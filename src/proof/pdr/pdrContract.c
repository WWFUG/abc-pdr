/**CFile****************************************************************

  FileName    [pdrContract.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Property driven reachability.]

  Synopsis    [Customiztation for Verifying Contract Property for CPUs.]

  Author      [Yu-Wei Fan]
  
  Affiliation [Princeton University]

  Date        [2025]

***********************************************************************/

#include "pdrInt.h"

ABC_NAMESPACE_IMPL_START

// ////////////////////////////////////////////////////////////////////////
// ///                        DECLARATIONS                              ///
// ////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    []

  Description [Log the unsafe concrete and generalized program to the pBlockedProgramFile. 
               Assume the previously reachability run has finished and the property is violated.
               Extract the program from the proof obligations accordingly.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/

int Pdr_ManLogUnsafeProgram(Pdr_Man_t* p, FILE * pFile){
    Pdr_Obl_t * pObl0, * pObl1;
    int i = 0, j=0, Lit;
    int nPis = Saig_ManPiNum(p->pAig);

    assert(pFile);

    pObl0 = p->pQueue; // the first proof obligation, PI assignments -> concrete unsafe program 
    pObl1 = pObl0->pNext; // the second proof obligation, state assignments -> generalized unsafe program

    fprintf(pFile, "%d-th Unsafe Program\n", p->nBlockedP);

    // derive concrete unsafe program
    fprintf(pFile, "Concrete one:\n");
    int totalBits = p->instLen * p->nInsts;
    char * pConcreteBits = (char *)malloc(totalBits + 1);
    memset(pConcreteBits, '0', totalBits);
    pConcreteBits[totalBits] = '\0';

    char * pGenBits = (char *)malloc(totalBits + 1);
    memset(pGenBits, 'x', totalBits);
    pGenBits[totalBits] = '\0';

    for ( i = pObl0->pState->nLits; i < pObl0->pState->nTotal; i++ )
    {
        Lit = pObl0->pState->Lits[i];
        int piId = Abc_Lit2Var(Lit);

        int imemIdx = Vec_IntEntry(p->vPIs2Imem, piId);
        // printf("imemIdx = %d, piId = %d, Val = %d\n", imemIdx, piId, 1 - Abc_LitIsCompl(Lit));
        if (imemIdx < 0) // skip if not mapped to imem
            continue;
        if (piId >= nPis)
            continue;

        pConcreteBits[imemIdx] = Abc_LitIsCompl(Lit) ? '0' : '1';
        pGenBits[imemIdx] = Abc_LitIsCompl(Lit) ? '0' : '1';
        // printf("%c\n", pConcreteBits[imemIdx]);
    }

    for (i = 0; i < p->nInsts; i++) {
        for (j = p->instLen; j > 0; j--) {
            fprintf(pFile, "%c", pConcreteBits[i * p->instLen + j-1 ]);
            // printf("imemIdx = %d, Val = %d\n", i * p->instLen + j-1, pConcreteBits[i * p->instLen + j-1 ] == '1' ? 1 : 0);
        }
        fprintf(pFile, "\n");
    }

    // derive generalized unsafe program
    fprintf(pFile, "Generalized one:\n");
    // Print the bit-vector grouped by instruction
    for (i = 0; i < p->nInsts; i++) {
        for (j = p->instLen; j > 0; j--) {  // REVERSED
            fprintf(pFile, "%c", pGenBits[i * p->instLen + j-1 ]);
        }
        fprintf(pFile, "\n");
    }

    free(pConcreteBits); // Clean up
    free(pGenBits); // Clean up

    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description [Return the instruction id of the register.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/

int Pdr_ManRegInstId(Pdr_Man_t* p, int regId){
    assert(regId >= 0 && regId < Vec_IntSize(p->vReg2Inst));
    return Vec_IntEntry(p->vReg2Inst, regId);
}

/**Function*************************************************************

  Synopsis    []

  Description [Return the instruction id of the PI.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/

int Pdr_ManPiInstId(Pdr_Man_t* p, int piId){
    assert(piId >= 0 && piId < Vec_IntSize(p->vPIs2Imem));
    int imemb = Vec_IntEntry(p->vPIs2Imem, piId);
    assert(imemb >= 0);
    // imemb is the index of the instruction memory, divided by instLen gives the instruction id
    return imemb / p->instLen; 
}

/**Function*************************************************************

  Synopsis    []

  Description [Return the position of the bit in its instruction of the register.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/

int Pdr_ManRegInstBit(Pdr_Man_t* p, int regId){
    assert(regId >= 0 && regId < Vec_IntSize(p->vReg2Inst));
    int pi = Vec_IntEntry(p->vReg2PI, regId);
    assert(pi >= 0 && pi < Vec_IntSize(p->vPIs2Imem));
    int imemb = Vec_IntEntry(p->vPIs2Imem, pi);
    return imemb % p->instLen; // the position of the bit in its instruction;
}

/**Function*************************************************************

  Synopsis    []

  Description [Return the position of the bit in its instruction of the PI.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/

int Pdr_ManPiInstBit(Pdr_Man_t* p, int piId){
    assert(piId >= 0 && piId < Vec_IntSize(p->vPIs2Imem));
    int imemb = Vec_IntEntry(p->vPIs2Imem, piId);
    assert(imemb >= 0);
    return imemb % p->instLen; // the position of the bit in its instruction
}

/**Function*************************************************************

  Synopsis    []

  Description [Return the position of the bit in its instruction of the PI.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/

int Pdr_ManIsRegInst(Pdr_Man_t* p, int regId){
    assert(regId >= 0 && regId < Vec_IntSize(p->vReg2Inst));
    int instId = Vec_IntEntry(p->vReg2Inst, regId);
    return (instId >= 0); // return 1 if it is a register instruction, 0 otherwise
}

/**Function*************************************************************

  Synopsis    []

  Description [Return the copy id of the register.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/

int Pdr_ManRegCopy(Pdr_Man_t* p, int regId){
    return Vec_IntEntry(p->vReg2Copy, regId) ; // return the copy id of the register
}