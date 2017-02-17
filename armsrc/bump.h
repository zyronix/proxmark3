//-----------------------------------------------------------------------------
// Loek Sangers and Romke van Dijk, Jan 2016
//
// This code is licensed to you under the terms of the GNU GPL, version 2 or,
// at your option, any later version. See the LICENSE.txt file for the text of
// the license.
//-----------------------------------------------------------------------------
// Definitions internal to the bump commands.
//-----------------------------------------------------------------------------


extern int BumpActivateUID(uint64_t uid);
extern void BumpDefaultKeys(uint16_t arg0, uint64_t arg1, uint8_t arg2, uint8_t *datain);
extern void BumpReadBlock(uint8_t arg0, uint8_t arg1, uint64_t arg2, uint8_t *datain);
extern void BumpNested(uint32_t arg0, uint32_t arg1, uint32_t calibrate, uint8_t *datain);
extern void BumpAcquireEncryptedNonces(uint32_t arg0, uint32_t arg1, uint32_t flags, uint8_t *datain);
