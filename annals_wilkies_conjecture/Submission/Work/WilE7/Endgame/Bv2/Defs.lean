/-
  Area E7 / the `CoreLT_succ` endgame, node **E2S** (module `Work.WilE7.Endgame.Bv2.Defs`).

  The *interface* of the `cellRefine_of_nodesBv2` assembly.  Because a Lean file may not exceed
  30 kB, the assembly is split over several modules; this one fixes the vocabulary they share:

  * the counting functions `PiL, SigL, Sig1L, LowL, LyL, SallL, NkL, BlkL, NgL` of the cardinality
    bookkeeping, and the degree polynomials `DqOf`, `DcandOf`;
  * `E2Env`, the bundle of all the constants produced by the five nodes (`hFC`, `hE5`, `h0`,
    `hE2`, plus the Σ/E1 boxes) together with their specifications.
-/
import Mathlib
import Submission.Work.WilE7.Endgame.Bv2.ExpB
import Submission.Work.WilE7.Endgame.CellRefineS
import Submission.Work.WilE7.Endgame.E2_pieces_of_family
import Submission.Work.WilE7.Endgame.E2_rank_strata
import Submission.Work.WilE7.Endgame.E2_frontier_strata
import Submission.Work.WilE7.Endgame.E2_sheets_of_stratum
import Submission.Work.WilE7.Endgame.E2Aux
import Submission.Work.WilE7.Endgame.sigmaFamily_len_unif
import Submission.Work.WilE7.CoreStep.CoreLTSuccNodes
import Submission.Work.WilE7.SheetData.gcase_cfs

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilE7.Endgame.Bv2

open WilkiesDesign WilkiesDesign.E
open Work.WilE7.MainDesign
open Work.WilE7.CoreStep (pPair pDim absPtUp absPtInv absReindex absLevelPairSet absPairSet
  pairPtUp projTop projTopSet projTopLin absPtLin AttainAt vertCoord)
open Work.CoreStep (frontierSet pairSubBaseFst pairFrontierBaseFst pairBase)

/-! ## §1. The counting functions -/

/-- The degree bound of the candidates. -/
def DqOf (Pp Pr Pf : Polynomial ℕ) : Polynomial ℕ :=
  Pp + Pr.comp Pp + Pf.comp Pp + Polynomial.X

/-- The degree bound of `Cand`, of the `Σ`/`E1` members and of the slices. -/
def DcandOf (Pp Pr Pf Bsum B1sum : Polynomial ℕ) : Polynomial ℕ :=
  DqOf Pp Pr Pf + Polynomial.C 3 * DqOf Pp Pr Pf + Polynomial.C 2
    + Bsum.comp (DqOf Pp Pr Pf) + B1sum.comp (DqOf Pp Pr Pf)

/-- A crude upper bound for the number of candidates: four lists, each of at most
`Np.eval ![D,k] * (Dcand.eval D + 1)` members. -/
def PiL (Np : MvPolynomial (Fin 2) ℕ) (Dcand : Polynomial ℕ) (D k : ℕ) : ℕ :=
  4 * (MvPolynomial.eval ![D, k] Np * (Dcand.eval D + 1))

/-- A bound for the length of the `Σ` family. -/
def SigL (Qsum : MvPolynomial (Fin 2) ℕ) (Np : MvPolynomial (Fin 2) ℕ)
    (Dq Dcand : Polynomial ℕ) (D k : ℕ) : ℕ :=
  MvPolynomial.eval ![Dq.eval D, PiL Np Dcand D k] Qsum

/-- A bound for the length of the `E1` family. -/
def Sig1L (Q1sum : MvPolynomial (Fin 3) ℕ) (Np : MvPolynomial (Fin 2) ℕ)
    (Dq Dcand : Polynomial ℕ) (D k : ℕ) : ℕ :=
  MvPolynomial.eval ![Dq.eval D, PiL Np Dcand D k, PiL Np Dcand D k] Q1sum

/-- A bound for the number of rank slices. -/
def LowL (K : ℕ) (Np : MvPolynomial (Fin 2) ℕ) (D k : ℕ) : ℕ :=
  K * MvPolynomial.eval ![D, k] Np

/-- A bound for the number of frontier (`Ly`) sets and for the number of rank strata. -/
def LyL (Np : MvPolynomial (Fin 2) ℕ) (Dcand : Polynomial ℕ) (D k : ℕ) : ℕ :=
  MvPolynomial.eval ![D, k] Np * (Dcand.eval D + 1)

/-- A bound for the length of the family `Σall`. -/
def SallL (Qsum : MvPolynomial (Fin 2) ℕ) (Q1sum : MvPolynomial (Fin 3) ℕ)
    (Np : MvPolynomial (Fin 2) ℕ) (Dq Dcand : Polynomial ℕ) (K D k : ℕ) : ℕ :=
  SigL Qsum Np Dq Dcand D k + Sig1L Q1sum Np Dq Dcand D k + LowL K Np D k
    + LyL Np Dcand D k

/-- A bound for the number of members of `X'`. -/
def NkL (Qsum : MvPolynomial (Fin 2) ℕ) (Q1sum : MvPolynomial (Fin 3) ℕ)
    (Np : MvPolynomial (Fin 2) ℕ) (Dq Dcand : Polynomial ℕ) (K D k : ℕ) : ℕ :=
  MvPolynomial.eval ![D, k] Np * SallL Qsum Q1sum Np Dq Dcand K D k

/-- A bound for the number of members of `Y'` other than the images of `Y`. -/
def BlkL (Qsum : MvPolynomial (Fin 2) ℕ) (Q1sum : MvPolynomial (Fin 3) ℕ)
    (Np : MvPolynomial (Fin 2) ℕ) (Dq Dcand : Polynomial ℕ) (K D k : ℕ) : ℕ :=
  (MvPolynomial.eval ![D, k] Np + MvPolynomial.eval ![D, k] Np) + LyL Np Dcand D k
    + LyL Np Dcand D k + SigL Qsum Np Dq Dcand D k + Sig1L Q1sum Np Dq Dcand D k
    + 2 * PiL Np Dcand D k + LowL K Np D k + LyL Np Dcand D k

/-- A bound for the number of new cells over one base cell. -/
def NgL (Psc : Polynomial ℕ) (Np : MvPolynomial (Fin 2) ℕ) (Dcand : Polynomial ℕ)
    (D k : ℕ) : ℕ :=
  2 * (PiL Np Dcand D k * Psc.eval D) + 3

/-- The degree bound of a stratum padded by `Fq` coordinates. -/
def padDegOf (Fq : ℕ) : Polynomial ℕ :=
  Polynomial.C (2 * Fq) + (1 + Polynomial.C (2 * Fq)) * Polynomial.X

end Work.WilE7.Endgame.Bv2
