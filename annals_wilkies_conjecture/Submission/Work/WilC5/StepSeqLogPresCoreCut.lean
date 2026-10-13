-- NOTE (WilC5 / S4OnePoint_general): a clash-free *copy* of `Submission/Work/WilC5/StepSeqLogPresCore.lean`
-- (proved by colleagues): every import in the `StepSeqLogClosure`/`StepSeqLogPres` chain is
-- redirected to the corresponding `…Cut` copy (in which the auxiliary definition `canonSyn` is
-- renamed), because the original `Work.WilC5.canonSyn` clashes with the identically named
-- definition of `Submission/Work/WilC5/StepKeyOfValProp.lean`, which is imported transitively by
-- `Submission/Work/WilC5/ExistsStepSeq.lean`; both are needed by the final assembly of vdDMM
-- Lemma 4.4 (`StepSeqTower.lean`).


import Mathlib
import Submission.Work.WilC5.S4StepNewSetup
import Submission.Work.WilC5.StepSeqDecomp
import Submission.Work.WilC5.StepSeqLogClosureCut
import Submission.Work.WilC5.StepSeqLogPresAuxCut
import Submission.Work.WilC5.StepSeqLogPresAux2Cut
import Submission.Work.WilC5.S4ExpG.ord_cut_aux
import Submission.Work.WilC5.S4ExpG.OrderEmbed
import Submission.Work.WilC5.leEL_iff_le
import Submission.Work.WilC5.logFun_one_add_rexp
import Submission.Work.WilC5.logFun_eq_of_rexp_eq
import Submission.Work.WilC5.S4ExpF.Bridge
import Submission.Work.WilC5.S4ExpF.logFun_zpow
import Submission.Work.WilC5.S4ExpF.logFun_eq_zero_of_not_pos
import Submission.Work.WilC5.StepNoNewAux.logFun_one_add_mem_dcl
import Submission.Work.WilC5.model_TR_of_dcl_closed
import Submission.Work.WilC5.LRcOps
import Submission.Work.WilC5.StepSeqLogPresWedgedCut

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

noncomputable section
open Classical

namespace Work.WilC5

open WilkiesDesign WilkiesDesign.CG WilkiesConjecture FirstOrder Language
open scoped FirstOrder

theorem StepSeqLogPresCore
    {K L : Type} [LEc.Structure K] [LEc.Structure L]
    [Field K] [LinearOrder K] [IsStrictOrderedRing K] [Ring.CompatibleRing K]
    [rexpL.Structure K] [(constantsOn ℝ).Structure K]
    [Field L] [LinearOrder L] [IsStrictOrderedRing L] [Ring.CompatibleRing L]
    [rexpL.Structure L] [(constantsOn ℝ).Structure L]
    (hK : K ⊨ TE) (hL : L ⊨ TE)
    (hMCr : ModelComplete TR) (hOM : OMinModels) (hVI : ValIneq)
    (haddK : ∀ x y : K, addE x y = x + y)
    (hmulK : ∀ x y : K, mulE x y = x * y)
    (honeK : (oneE : K) = 1)
    (hlenegK : ∀ x y : K, leE x y ↔ x ≤ y)
    (haddL : ∀ x y : L, addE x y = x + y)
    (hmulL : ∀ x y : L, mulE x y = x * y)
    (honeL : (oneE : L) = 1)
    (hlenegL : ∀ x y : L, leE x y ↔ x ≤ y)
    {B : LRc.Substructure K}
    (hBdcl : @WilC2.Dcl K (reductStruct K) (B : Set K) ⊆ (B : Set K))
    (hBlog : ∀ x ∈ (B : Set K), logFun x ∈ (B : Set K))
    (τ : LRc.Embedding ↥B L)
    (hτlog : ∀ b : ↥B, τ ⟨logFun (b : K), hBlog (b : K) b.2⟩ = logFun (τ b))
    (S : StepSeq B)
    (hind : ∀ (n : ℕ) (q : Fin n → ℤ),
      (∃ c ∈ (B : Set K), c ≠ 0 ∧ IsUnitVal (c * ∏ i : Fin n, S.xs (i : ℕ) ^ (q i))) → q = 0)
    {y0 : L}
    (hysrel : ∀ i : ℕ, logFun (StepSeq.ys B τ S y0 i) =
      (if S.pos i then (τ (S.beta i) : L) + StepSeq.ys B τ S y0 (i + 1)
       else (τ (S.beta i) : L) - StepSeq.ys B τ S y0 (i + 1)))
    {n : ℕ}
    (σ' : LRc.Embedding ↥(StepSeq.Fsub hK S (n + 1)) L)
    (hσ'B : ∀ b : ↥B, σ' ⟨(b : K), StepSeq.B_mem_Fsub hK S (n + 1) b.2⟩ = τ b)
    (hσ'xs : ∀ (i : ℕ) (hi : i < n + 1),
      σ' ⟨S.xs i, StepSeq.xs_mem_Fsub hK S hi⟩ = StepSeq.ys B τ S y0 i)
    {w : K} (hw : w ∈ StepSeq.Fset S n)
    (hwlog : logFun w ∈ StepSeq.Fset S (n + 1)) :
    σ' ⟨logFun w, (StepSeq.Fset_mem_Fsub hK S (n + 1)).mp hwlog⟩ =
      logFun (σ' ⟨w, (StepSeq.Fset_mem_Fsub hK S (n + 1)).mp
        (StepSeq.Fset_mono S (Nat.le_succ n) hw)⟩) := by

  classical
  have hzK : (zeroE : K) = 0 := S4ExpF.zeroE_eq_zero hK haddK
  have hnegK : ∀ x : K, negE x = -x := fun x => S4ExpF.negE_eq_neg hK haddK x
  have hzL : (zeroE : L) = 0 := S4ExpF.zeroE_eq_zero hL haddL
  have hnegL : ∀ x : L, negE x = -x := fun x => S4ExpF.negE_eq_neg hL haddL x
  letI : Ring.CompatibleRing K := SSLPAux.compatRingOfBridges haddK hmulK hnegK hzK honeK
  letI : Ring.CompatibleRing L := SSLPAux.compatRingOfBridges haddL hmulL hnegL hzL honeL
  letI : rexpL.Structure K := @lrcRexpReduct K (instStructureLRcOfLEc K)
  letI : rexpL.Structure L := @lrcRexpReduct L (instStructureLRcOfLEc L)
  letI : (constantsOn ℝ).Structure K := @lrcConstReduct K (instStructureLRcOfLEc K)
  letI : (constantsOn ℝ).Structure L := @lrcConstReduct L (instStructureLRcOfLEc L)
  have hstructK := StepSeq.canonStruct_eq_reduct (K := K)
  have hstructL : (reductStruct L : LRc.Structure L) = (LR.withConstantsStructure ℝ) := by
    ext m f y
    · rcases f with (g | c)
      · rcases g with (g | r)
        · rfl
        · cases r; show rexpFromExp (y 0) = _; rfl
      · rfl
    · nomatch f
  exact stepSeqLogPresWedged hstructK hstructL (fun x => rfl) hK hL hMCr hOM hVI haddK hmulK
    honeK hlenegK haddL hmulL honeL hlenegL hBdcl hBlog τ hτlog S hind hysrel σ' hσ'B hσ'xs hw
    hwlog

end Work.WilC5
