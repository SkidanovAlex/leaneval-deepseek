-- NOTE (WilC5 / S4OnePoint_general): a clash-free *copy* of `Submission/Work/WilC5/StepSeqLogPresWedged.lean`
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

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

noncomputable section
open Classical

namespace Work.WilC5

open WilkiesDesign WilkiesDesign.CG WilkiesConjecture FirstOrder Language
open scoped FirstOrder

theorem stepSeqLogPresWedged
    {K L : Type} [LEc.Structure K] [LEc.Structure L]
    [Field K] [LinearOrder K] [IsStrictOrderedRing K] [Ring.CompatibleRing K]
    [rexpL.Structure K] [(constantsOn ℝ).Structure K]
    [Field L] [LinearOrder L] [IsStrictOrderedRing L] [Ring.CompatibleRing L]
    [rexpL.Structure L] [(constantsOn ℝ).Structure L]
    (hstructK : (reductStruct K : LRc.Structure K) = LR.withConstantsStructure ℝ)
    (hstructL : (reductStruct L : LRc.Structure L) = LR.withConstantsStructure ℝ)
    (hrexpK : ∀ x : K, @Structure.funMap rexpL K _ 1 rexpFunc.rexp ![x] = rexpFromExp x)
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
  have hzK := S4ExpF.zeroE_eq_zero hK haddK
  have hnegK := fun x : K => S4ExpF.negE_eq_neg hK haddK x
  have hzL := S4ExpF.zeroE_eq_zero hL haddL
  have hnegL := fun x : L => S4ExpF.negE_eq_neg hL haddL x
  letI : Ring.CompatibleRing K := SSLPAux.compatRingOfBridges haddK hmulK hnegK hzK honeK
  letI : Ring.CompatibleRing L := SSLPAux.compatRingOfBridges haddL hmulL hnegL hzL honeL
  have hdclK : ∀ A : Set K, @WilC2.Dcl K (reductStruct K) A =
      @WilC2.Dcl K (LR.withConstantsStructure ℝ) A :=
    fun A => congrArg (fun i => @WilC2.Dcl K i A) hstructK
  let T : @LRc.Substructure K (reductStruct K) := StepSeq.Fsub hK S (n + 1)
  have hcoeT : (T : Set K) = StepSeq.Fset S (n + 1) := StepSeq.Fsub_coe hK S (n + 1)
  have hTdcl_red : @WilC2.Dcl K (reductStruct K) (T : Set K) ⊆ (T : Set K) :=
    StepSeq.Fsub_dcl hK S (n + 1)
  have hTdcl : @WilC2.Dcl K (LR.withConstantsStructure ℝ) (T : Set K) ⊆ (T : Set K) :=
    fun x hx => hTdcl_red ((hdclK (T : Set K)).symm ▸ hx)
  have hPT : (T : Set K) ⊆ @WilC2.Dcl K (LR.withConstantsStructure ℝ) (T : Set K) :=
    fun x hx => (hdclK (T : Set K)) ▸ (StepSeq.subset_dcl (A := (T : Set K)) hx)
  have hmemD : ∀ {x : K}, x ∈ (T : Set K) →
      x ∈ @WilC2.Dcl K (LR.withConstantsStructure ℝ) (T : Set K) := fun hx => hPT hx
  have hmemS : ∀ {x : K},
      x ∈ @WilC2.Dcl K (LR.withConstantsStructure ℝ) (T : Set K) → x ∈ (T : Set K) :=
    fun hx => hTdcl hx
  have h0T := hmemS (S4ExpF.dcl_zero_mem (T : Set K))
  have h1T := hmemS (S4ExpF.dcl_one_mem (T : Set K))
  have hIntT := fun z : ℤ => hmemS (S4ExpF.dcl_intCast_mem (T : Set K) z)
  have hNatT := fun m : ℕ => hmemS (S4ExpF.dcl_natCast_mem (T : Set K) m)
  have hBT := fun x (hx : x ∈ (B : Set K)) => hcoeT ▸ (StepSeq.B_subset_Fset S (n + 1) hx)
  have hxsT := fun (i : ℕ) (hi : i < n + 1) => hcoeT ▸ (StepSeq.xs_mem_Fset S hi)
  haveI hKTR : @Theory.Model LRc K (reductStruct K) TR := reduct_model_TR K hK
  haveI hLTR : @Theory.Model LRc L (reductStruct L) TR := reduct_model_TR L hL
  haveI hKTRc : @Theory.Model LRc K (LR.withConstantsStructure ℝ) TR :=
    hstructK ▸ reduct_model_TR K hK
  haveI hLTRc : @Theory.Model LRc L (LR.withConstantsStructure ℝ) TR :=
    hstructL ▸ reduct_model_TR L hL
  letI : Ring.CompatibleRing K := SSLPAux.compatRingOfBridges haddK hmulK hnegK hzK honeK
  letI : Ring.CompatibleRing L := SSLPAux.compatRingOfBridges haddL hmulL hnegL hzL honeL
  obtain ⟨hleT, hposT⟩ :=
    SSLPAux.orderEmbed_of_dcl_closed hK hL hMCr hOM haddK hmulK honeK hlenegK haddL hmulL honeL
      hlenegL hstructK hstructL hTdcl_red σ'
  have hembrexp := fun (y : ↥T) (h : rexpFromExp (y : K) ∈ (T : Set K)) =>
    SSLPAux.embRexpVal (T := T) σ' y h
  have hlogwT := hcoeT ▸ hwlog
  have hwT := hcoeT ▸ (StepSeq.Fset_mono S (Nat.le_succ n) hw)
  have hgoal1 : (⟨logFun w, (StepSeq.Fset_mem_Fsub hK S (n + 1)).mp hwlog⟩ : ↥T) =
      ⟨logFun w, hlogwT⟩ := Subtype.ext rfl
  have hgoal2 : (⟨w, (StepSeq.Fset_mem_Fsub hK S (n + 1)).mp
      (StepSeq.Fset_mono S (Nat.le_succ n) hw)⟩ : ↥T) = ⟨w, hwT⟩ := Subtype.ext rfl
  rw [hgoal1, hgoal2]
  haveI hKTE : K ⊨ TE := hK
  by_cases hwpos : (0 : K) < w
  · have hw0 : w ≠ 0 := ne_of_gt hwpos
    have hxs_pos : ∀ i : ℕ, (0 : K) < S.xs i :=
      fun i => (S4ExpF.leE_zero_iff hK haddK hlenegK (S.xs i)).mp (S.hpos i)
    obtain ⟨Q, hQ, N, z, hzB, hz0, ε, hε, hdec⟩ :=
      StepSeqDecomp hrexpK haddK hmulK honeK hlenegK hMCr hOM hVI B hBdcl
        (fun i : Fin n => S.xs (i : ℕ)) (fun i => ne_of_gt (hxs_pos (i : ℕ))) (hind n)
        (show w ∈ @WilC2.Dcl K (reductStruct K)
          ((B : Set K) ∪ Set.range (fun i : Fin n => S.xs (i : ℕ))) from hw) hw0
    have hxs_pos' := fun i : Fin n => hxs_pos (i : ℕ)
    have hprod_pos : 0 < ∏ i : Fin n, S.xs (i : ℕ) ^ (N i) :=
      Finset.prod_pos fun i _ => zpow_pos (hxs_pos' i) (N i)
    have hwQ_pos : 0 < w ^ Q := zpow_pos hwpos Q
    have hε_half : |ε| ≤ (2 : K)⁻¹ := by
      have h := hε 1
      rw [show (((1 : ℕ) : K) + 1) = 2 by norm_num] at h
      exact h
    have h1ε_pos : 0 < 1 + ε := by
      have hlow : -(2 : K)⁻¹ ≤ ε := (abs_le.mp hε_half).1
      have h2invlt : (2 : K)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by norm_num : (1 : K) < 2)
      linarith
    have hz_pos : 0 < z := by
      have hprod : 0 < (z * (∏ i : Fin n, S.xs (i : ℕ) ^ (N i))) * (1 + ε) := by
        rw [← hdec]; exact hwQ_pos
      have h1 : 0 < z * (∏ i : Fin n, S.xs (i : ℕ) ^ (N i)) :=
        (mul_pos_iff_of_pos_right h1ε_pos).mp hprod
      exact (mul_pos_iff_of_pos_right hprod_pos).mp h1
    have hzT := hBT z hzB
    have hxsT' := fun i : Fin n => hxsT (i : ℕ) (Nat.lt_succ_of_lt i.isLt)
    have hprodD : (∏ i : Fin n, S.xs (i : ℕ) ^ (N i)) ∈
        @WilC2.Dcl K (LR.withConstantsStructure ℝ) (T : Set K) :=
      dcl_prod_finset_mem (T : Set K) Finset.univ (fun i : Fin n => S.xs (i : ℕ) ^ (N i))
        (fun i _ => S4ExpF.dcl_zpow_mem (T : Set K) (hmemD (hxsT' i)) (ne_of_gt (hxs_pos' i))
          (N i))
    have hprodT := hmemS hprodD
    have hdenT : z * (∏ i : Fin n, S.xs (i : ℕ) ^ (N i)) ∈ (T : Set K) :=
      hmemS (S4ExpF.dcl_mul_mem (T : Set K) (hmemD hzT) hprodD)
    have hden0 : z * (∏ i : Fin n, S.xs (i : ℕ) ^ (N i)) ≠ 0 :=
      mul_ne_zero hz0 (ne_of_gt hprod_pos)
    have hwQT : w ^ Q ∈ (T : Set K) :=
      hmemS (S4ExpF.dcl_zpow_mem (T : Set K) (hmemD hwT) hw0 Q)
    have h1εT : 1 + ε ∈ (T : Set K) := by
      have h : w ^ Q * (z * (∏ i : Fin n, S.xs (i : ℕ) ^ (N i)))⁻¹ ∈ (T : Set K) :=
        hmemS (S4ExpF.dcl_mul_mem (T : Set K) (hmemD hwQT)
          (S4ExpF.dcl_inv_mem (T : Set K) (hmemD hdenT) hden0))
      have heq : w ^ Q * (z * (∏ i : Fin n, S.xs (i : ℕ) ^ (N i)))⁻¹ = 1 + ε := by
        rw [hdec, mul_comm (z * (∏ i : Fin n, S.xs (i : ℕ) ^ (N i))) (1 + ε)]
        exact mul_inv_cancel_right₀ hden0 (1 + ε)
      rwa [heq] at h
    have hεT : ε ∈ (T : Set K) := by
      have h : (1 + ε) + (-1) ∈ (T : Set K) :=
        hmemS (S4ExpF.dcl_add_mem (T : Set K) (hmemD h1εT)
          (S4ExpF.dcl_neg_mem (T : Set K) (hmemD h1T)))
      have heq : (1 + ε) + (-1) = ε := by ring
      rwa [heq] at h
    have hlogzT := hBT _ (hBlog z hzB)
    have hlogxsT : ∀ i : Fin n, logFun (S.xs (i : ℕ)) ∈ (T : Set K) := by
      intro i
      have hbT : (S.beta (i : ℕ) : K) ∈ (T : Set K) := hBT _ (S.beta (i : ℕ)).2
      have hx1T : S.xs ((i : ℕ) + 1) ∈ (T : Set K) := hxsT _ (by have := i.isLt; omega)
      by_cases hp : S.pos (i : ℕ)
      · rw [S.hrel (i : ℕ), if_pos hp, haddK]
        exact hmemS (S4ExpF.dcl_add_mem (T : Set K) (hmemD hbT) (hmemD hx1T))
      · rw [S.hrel (i : ℕ), if_neg hp]
        have hsub : subE (S.beta (i : ℕ) : K) (S.xs ((i : ℕ) + 1)) =
            (S.beta (i : ℕ) : K) + -(S.xs ((i : ℕ) + 1)) := by
          rw [S4ExpF.subE_eq_sub hK haddK, sub_eq_add_neg]
        rw [hsub]
        exact hmemS (S4ExpF.dcl_add_mem (T : Set K) (hmemD hbT)
          (S4ExpF.dcl_neg_mem (T : Set K) (hmemD hx1T)))
    have hδK : absLeOne (mulE (addE oneE oneE) ε) := by
      have hmulE : mulE (addE oneE oneE) ε = (2 : K) * ε := by rw [haddK, honeK, hmulK]; norm_num
      rw [hmulE, S4ExpF.absLeOne_iff_abs hK haddK honeK hlenegK, abs_mul]
      have h2abs : |(2 : K)| = 2 := abs_of_pos (by norm_num)
      rw [h2abs]
      calc (2 : K) * |ε| ≤ (2 : K) * (2 : K)⁻¹ :=
            mul_le_mul_of_nonneg_left hε_half (by norm_num)
        _ = 1 := mul_inv_cancel₀ (by norm_num)
    have hlogpeT : logFun (1 + ε) ∈ (T : Set K) := by
      have hδmem : addE oneE ε ∈ @WilC2.Dcl K (LR.withConstantsStructure ℝ) (T : Set K) := by
        rw [haddK, honeK]; exact hmemD h1εT
      have h := S4ExpF.logFun_one_add_mem_dcl hK hrexpK haddK honeK (T : Set K) hδmem hδK
      rw [haddK, honeK] at h
      exact hmemS h
    have hεTL := SSLPAux.isInfinitesimal_map_of_embedding (T := T) σ' haddK haddL hmulK hmulL honeK honeL
        hnegK hnegL hzK hzL hleT hIntT hNatT h1T
        (fun x hx y hy => hmemS (S4ExpF.dcl_add_mem (T : Set K) (hmemD hx) (hmemD hy)))
        (fun x hx => hmemS (S4ExpF.dcl_neg_mem (T : Set K) (hmemD hx)))
        (fun x hx hx0 => hmemS (S4ExpF.dcl_inv_mem (T : Set K) (hmemD hx) hx0)) hεT hε
    have hσwpos := (hposT ⟨w, hwT⟩).mp hwpos
    have hσzpos := (hposT ⟨z, hzT⟩).mp hz_pos
    have hσxs'_pos : ∀ i : Fin n, 0 < (σ' ⟨S.xs (i : ℕ), hxsT' i⟩ : L) :=
      fun i => (hposT ⟨S.xs (i : ℕ), hxsT' i⟩).mp (hxs_pos' i)
    have hσprodpos : 0 < (∏ i : Fin n, (σ' ⟨S.xs (i : ℕ), hxsT' i⟩ : L) ^ (N i)) :=
      Finset.prod_pos fun i _ => zpow_pos (hσxs'_pos i) (N i)
    have h1εLpos : 0 < 1 + (σ' ⟨ε, hεT⟩ : L) := by
      have h := hεTL 1
      rw [show (((1 : ℕ) : L) + 1) = 2 by norm_num] at h
      have hlow : -(2 : L)⁻¹ ≤ (σ' ⟨ε, hεT⟩ : L) := (abs_le.mp h).1
      have h2invlt : (2 : L)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by norm_num : (1 : L) < 2)
      linarith
    have hδL : absLeOne (mulE (addE oneE oneE) (σ' ⟨ε, hεT⟩)) := by
      have hmulE : mulE (addE oneE oneE) (σ' ⟨ε, hεT⟩) = (2 : L) * (σ' ⟨ε, hεT⟩) := by
        rw [haddL, honeL, hmulL]; norm_num
      rw [hmulE, S4ExpF.absLeOne_iff_abs hL haddL honeL hlenegL, abs_mul]
      have h2abs : |(2 : L)| = 2 := abs_of_pos (by norm_num)
      rw [h2abs]
      have hhalf : |(σ' ⟨ε, hεT⟩ : L)| ≤ (2 : L)⁻¹ := by
        have h := hεTL 1
        rw [show (((1 : ℕ) : L) + 1) = 2 by norm_num] at h
        exact h
      calc (2 : L) * |(σ' ⟨ε, hεT⟩ : L)| ≤ (2 : L) * (2 : L)⁻¹ :=
            mul_le_mul_of_nonneg_left hhalf (by norm_num)
        _ = 1 := mul_inv_cancel₀ (by norm_num)
    have hprodlogK := logFun_finset_prod_zpow hK haddK hmulK honeK hlenegK Finset.univ
        (fun i : Fin n => S.xs (i : ℕ)) N (fun i _ => hxs_pos' i)
    have hkeyK : (Q : K) * logFun w =
        logFun z + (∑ i : Fin n, (N i : K) * logFun (S.xs (i : ℕ))) + logFun (1 + ε) := by
      have h1 : logFun (w ^ Q) = (Q : K) * logFun w :=
        S4ExpF.logFun_zpow hK haddK hmulK honeK hlenegK w hwpos Q
      have h3 : logFun (z * (∏ i : Fin n, S.xs (i : ℕ) ^ (N i)) * (1 + ε)) =
          logFun (z * (∏ i : Fin n, S.xs (i : ℕ) ^ (N i))) + logFun (1 + ε) :=
        S4ExpF.logFun_mul_pos hK haddK hmulK hlenegK (mul_pos hz_pos hprod_pos) h1ε_pos
      have h4 : logFun (z * (∏ i : Fin n, S.xs (i : ℕ) ^ (N i))) =
          logFun z + logFun (∏ i : Fin n, S.xs (i : ℕ) ^ (N i)) :=
        S4ExpF.logFun_mul_pos hK haddK hmulK hlenegK hz_pos hprod_pos
      rw [← h1, hdec, h3, h4, hprodlogK]
    have hRzT : z * (∏ i : Fin n, S.xs (i : ℕ) ^ (N i)) * (1 + ε) ∈ (T : Set K) :=
      hmemS (S4ExpF.dcl_mul_mem (T : Set K) (hmemD hdenT) (hmemD h1εT))
    have hdecS : (⟨w ^ Q, hwQT⟩ : ↥T) =
        ⟨z * (∏ i : Fin n, S.xs (i : ℕ) ^ (N i)) * (1 + ε), hRzT⟩ := Subtype.ext hdec
    have he1 : σ' ⟨w ^ Q, hwQT⟩ = (σ' ⟨w, hwT⟩) ^ Q :=
      SSLPAux.embZPow (T := T) σ' haddK haddL hmulK hmulL honeK honeL hzK hzL ⟨w, hwT⟩ hw0
        (fun k => hmemS (S4ExpF.dcl_zpow_mem (T : Set K) (hmemD hwT) hw0 k)) Q
    have hep : σ' ⟨1 + ε, h1εT⟩ = 1 + (σ' ⟨ε, hεT⟩ : L) := by
      have h := SSLPAux.embAdd (T := T) σ' haddK haddL ⟨(1 : K), h1T⟩ ⟨ε, hεT⟩ h1εT
      rw [SSLPAux.embOne (T := T) σ' honeK honeL h1T] at h
      exact h
    have hprodimg : σ' ⟨∏ i : Fin n, S.xs (i : ℕ) ^ (N i), hprodT⟩ =
        ∏ i : Fin n, (σ' ⟨S.xs (i : ℕ), hxsT' i⟩ : L) ^ (N i) := by
      have hmem : ∀ (t : Finset (Fin n)) (z' : Fin n → ℤ),
          (∏ i ∈ t, (S.xs (i : ℕ)) ^ (z' i)) ∈ (T : Set K) :=
        fun t z' => hmemS (dcl_prod_finset_mem (T : Set K) t (fun i => S.xs (i : ℕ) ^ (z' i))
          (fun i _ => S4ExpF.dcl_zpow_mem (T : Set K) (hmemD (hxsT' i)) (ne_of_gt (hxs_pos' i))
            (z' i)))
      have h := SSLPAux.embProd (T := T) σ' haddK haddL hmulK hmulL honeK honeL hzK hzL
        Finset.univ (fun i : Fin n => ⟨S.xs (i : ℕ), hxsT' i⟩) N
        (fun i _ => ne_of_gt (hxs_pos' i)) hmem
      rw [show (⟨∏ i : Fin n, S.xs (i : ℕ) ^ (N i), hprodT⟩ : ↥T) =
          ⟨∏ i ∈ (Finset.univ : Finset (Fin n)),
              ((fun i : Fin n => (⟨S.xs (i : ℕ), hxsT' i⟩ : ↥T)) i : K) ^ (N i),
            hmem Finset.univ N⟩ from Subtype.ext rfl]
      exact h
    have hdecL : (σ' ⟨w, hwT⟩ : L) ^ Q =
        σ' ⟨z, hzT⟩ * (∏ i : Fin n, (σ' ⟨S.xs (i : ℕ), hxsT' i⟩ : L) ^ (N i))
          * (1 + (σ' ⟨ε, hεT⟩ : L)) := by
      calc (σ' ⟨w, hwT⟩ : L) ^ Q = σ' ⟨w ^ Q, hwQT⟩ := he1.symm
        _ = σ' ⟨z * (∏ i : Fin n, S.xs (i : ℕ) ^ (N i)) * (1 + ε), hRzT⟩ := by rw [hdecS]
        _ = σ' ⟨z * (∏ i : Fin n, S.xs (i : ℕ) ^ (N i)), hdenT⟩ * σ' ⟨1 + ε, h1εT⟩ :=
              SSLPAux.embMul (T := T) σ' hmulK hmulL
                ⟨z * (∏ i : Fin n, S.xs (i : ℕ) ^ (N i)), hdenT⟩ ⟨1 + ε, h1εT⟩ hRzT
        _ = (σ' ⟨z, hzT⟩ * σ' ⟨∏ i : Fin n, S.xs (i : ℕ) ^ (N i), hprodT⟩)
              * σ' ⟨1 + ε, h1εT⟩ := by
              rw [SSLPAux.embMul (T := T) σ' hmulK hmulL ⟨z, hzT⟩
                ⟨∏ i : Fin n, S.xs (i : ℕ) ^ (N i), hprodT⟩ hdenT]
        _ = σ' ⟨z, hzT⟩ * (∏ i : Fin n, (σ' ⟨S.xs (i : ℕ), hxsT' i⟩ : L) ^ (N i))
              * (1 + (σ' ⟨ε, hεT⟩ : L)) := by rw [hprodimg, hep]
    have hprodlogL := logFun_finset_prod_zpow hL haddL hmulL honeL hlenegL Finset.univ
        (fun i : Fin n => (σ' ⟨S.xs (i : ℕ), hxsT' i⟩ : L)) N (fun i _ => hσxs'_pos i)
    have hkeyL : (Q : L) * logFun (σ' ⟨w, hwT⟩) =
        logFun (σ' ⟨z, hzT⟩)
          + (∑ i : Fin n, (N i : L) * logFun (σ' ⟨S.xs (i : ℕ), hxsT' i⟩))
          + logFun (1 + (σ' ⟨ε, hεT⟩ : L)) := by
      have h1 : logFun ((σ' ⟨w, hwT⟩ : L) ^ Q) = (Q : L) * logFun (σ' ⟨w, hwT⟩) :=
        S4ExpF.logFun_zpow hL haddL hmulL honeL hlenegL (σ' ⟨w, hwT⟩) hσwpos Q
      have h3 : logFun (σ' ⟨z, hzT⟩ * (∏ i : Fin n, (σ' ⟨S.xs (i : ℕ), hxsT' i⟩ : L) ^ (N i))
            * (1 + (σ' ⟨ε, hεT⟩ : L))) =
          logFun (σ' ⟨z, hzT⟩ * (∏ i : Fin n, (σ' ⟨S.xs (i : ℕ), hxsT' i⟩ : L) ^ (N i)))
            + logFun (1 + (σ' ⟨ε, hεT⟩ : L)) :=
        S4ExpF.logFun_mul_pos hL haddL hmulL hlenegL (mul_pos hσzpos hσprodpos) h1εLpos
      have h4 : logFun (σ' ⟨z, hzT⟩ * (∏ i : Fin n, (σ' ⟨S.xs (i : ℕ), hxsT' i⟩ : L) ^ (N i))) =
          logFun (σ' ⟨z, hzT⟩)
            + logFun (∏ i : Fin n, (σ' ⟨S.xs (i : ℕ), hxsT' i⟩ : L) ^ (N i)) :=
        S4ExpF.logFun_mul_pos hL haddL hmulL hlenegL hσzpos hσprodpos
      rw [← h1, hdecL, h3, h4, hprodlogL]
    have hlogzmap : σ' ⟨logFun z, hlogzT⟩ = logFun (σ' ⟨z, hzT⟩) := by
      have hlogzB : logFun z ∈ (B : Set K) := hBlog z hzB
      have h1 : (⟨logFun z, hlogzT⟩ : ↥T) =
          ⟨logFun z, StepSeq.B_mem_Fsub hK S (n + 1) hlogzB⟩ := Subtype.ext rfl
      have h2 : (⟨z, hzT⟩ : ↥T) = ⟨z, StepSeq.B_mem_Fsub hK S (n + 1) hzB⟩ := Subtype.ext rfl
      have h3 : σ' ⟨logFun z, StepSeq.B_mem_Fsub hK S (n + 1) hlogzB⟩ =
          τ ⟨logFun z, hlogzB⟩ := hσ'B ⟨logFun z, hlogzB⟩
      have h4 : τ ⟨z, hzB⟩ = σ' ⟨z, StepSeq.B_mem_Fsub hK S (n + 1) hzB⟩ :=
        (hσ'B ⟨z, hzB⟩).symm
      have h5 : τ ⟨logFun z, hlogzB⟩ =
          τ (⟨logFun (↑(⟨z, hzB⟩ : ↥B)),
            hBlog (↑(⟨z, hzB⟩ : ↥B)) (⟨z, hzB⟩ : ↥B).2⟩ : ↥B) :=
        congrArg τ (Subtype.ext (by simp))
      calc σ' ⟨logFun z, hlogzT⟩
          = σ' ⟨logFun z, StepSeq.B_mem_Fsub hK S (n + 1) hlogzB⟩ := by rw [h1]
        _ = τ ⟨logFun z, hlogzB⟩ := h3
        _ = logFun (τ ⟨z, hzB⟩) := by rw [h5]; exact hτlog ⟨z, hzB⟩
        _ = logFun (σ' ⟨z, StepSeq.B_mem_Fsub hK S (n + 1) hzB⟩) := by rw [h4]
        _ = logFun (σ' ⟨z, hzT⟩) := by rw [← h2]
    have hlogxmap : ∀ i : Fin n, σ' ⟨logFun (S.xs (i : ℕ)), hlogxsT i⟩ =
        logFun (σ' ⟨S.xs (i : ℕ), hxsT' i⟩) := by
      intro i
      have hi1 : (i : ℕ) + 1 < n + 1 := Nat.succ_lt_succ i.isLt
      have hbT : (S.beta (i : ℕ) : K) ∈ (T : Set K) := hBT _ (S.beta (i : ℕ)).2
      have hx1T : S.xs ((i : ℕ) + 1) ∈ (T : Set K) := hxsT _ hi1
      have hσβ : σ' ⟨(S.beta (i : ℕ) : K), hbT⟩ = τ (S.beta (i : ℕ)) := by
        have h1 : (⟨(S.beta (i : ℕ) : K), hbT⟩ : ↥T) =
            ⟨(S.beta (i : ℕ) : K), StepSeq.B_mem_Fsub hK S (n + 1) (S.beta (i : ℕ)).2⟩ :=
          Subtype.ext rfl
        rw [h1]; exact hσ'B (S.beta (i : ℕ))
      have hσx1 : σ' ⟨S.xs ((i : ℕ) + 1), hx1T⟩ = StepSeq.ys B τ S y0 ((i : ℕ) + 1) := by
        have h1 : (⟨S.xs ((i : ℕ) + 1), hx1T⟩ : ↥T) =
            ⟨S.xs ((i : ℕ) + 1), StepSeq.xs_mem_Fsub hK S hi1⟩ := Subtype.ext rfl
        rw [h1]; exact hσ'xs ((i : ℕ) + 1) hi1
      have hσxi : σ' ⟨S.xs (i : ℕ), hxsT' i⟩ = StepSeq.ys B τ S y0 (i : ℕ) := by
        have h1 : (⟨S.xs (i : ℕ), hxsT' i⟩ : ↥T) =
            ⟨S.xs (i : ℕ), StepSeq.xs_mem_Fsub hK S (Nat.lt_succ_of_lt i.isLt)⟩ :=
          Subtype.ext rfl
        rw [h1]; exact hσ'xs (i : ℕ) (Nat.lt_succ_of_lt i.isLt)
      by_cases hp : S.pos (i : ℕ)
      · have hKlt : logFun (S.xs (i : ℕ)) = (S.beta (i : ℕ) : K) + S.xs ((i : ℕ) + 1) := by
          rw [S.hrel (i : ℕ), if_pos hp, haddK]
        have hLlt : logFun (σ' ⟨S.xs (i : ℕ), hxsT' i⟩) =
            (τ (S.beta (i : ℕ)) : L) + StepSeq.ys B τ S y0 ((i : ℕ) + 1) := by
          rw [hσxi, hysrel (i : ℕ), if_pos hp]
        calc σ' ⟨logFun (S.xs (i : ℕ)), hlogxsT i⟩
            = σ' ⟨(S.beta (i : ℕ) : K) + S.xs ((i : ℕ) + 1),
                SSLPAux.memAdd (T := T) haddK hbT hx1T⟩ := by
              rw [show (⟨logFun (S.xs (i : ℕ)), hlogxsT i⟩ : ↥T) =
                ⟨(S.beta (i : ℕ) : K) + S.xs ((i : ℕ) + 1),
                  SSLPAux.memAdd (T := T) haddK hbT hx1T⟩ from Subtype.ext hKlt]
          _ = σ' ⟨(S.beta (i : ℕ) : K), hbT⟩ + σ' ⟨S.xs ((i : ℕ) + 1), hx1T⟩ :=
              SSLPAux.embAdd (T := T) σ' haddK haddL ⟨(S.beta (i : ℕ) : K), hbT⟩
                ⟨S.xs ((i : ℕ) + 1), hx1T⟩ (SSLPAux.memAdd (T := T) haddK hbT hx1T)
          _ = (τ (S.beta (i : ℕ)) : L) + StepSeq.ys B τ S y0 ((i : ℕ) + 1) := by rw [hσβ, hσx1]
          _ = logFun (σ' ⟨S.xs (i : ℕ), hxsT' i⟩) := by rw [← hLlt]
      · have hKlt : logFun (S.xs (i : ℕ)) = (S.beta (i : ℕ) : K) - S.xs ((i : ℕ) + 1) := by
          rw [S.hrel (i : ℕ), if_neg hp, S4ExpF.subE_eq_sub hK haddK]
        have hLlt : logFun (σ' ⟨S.xs (i : ℕ), hxsT' i⟩) =
            (τ (S.beta (i : ℕ)) : L) - StepSeq.ys B τ S y0 ((i : ℕ) + 1) := by
          rw [hσxi, hysrel (i : ℕ), if_neg hp]
        calc σ' ⟨logFun (S.xs (i : ℕ)), hlogxsT i⟩
            = σ' ⟨(S.beta (i : ℕ) : K) - S.xs ((i : ℕ) + 1),
                SSLPAux.memSub (T := T) haddK hnegK hbT hx1T⟩ := by
              rw [show (⟨logFun (S.xs (i : ℕ)), hlogxsT i⟩ : ↥T) =
                ⟨(S.beta (i : ℕ) : K) - S.xs ((i : ℕ) + 1),
                  SSLPAux.memSub (T := T) haddK hnegK hbT hx1T⟩ from Subtype.ext hKlt]
          _ = σ' ⟨(S.beta (i : ℕ) : K), hbT⟩ - σ' ⟨S.xs ((i : ℕ) + 1), hx1T⟩ :=
              SSLPAux.embSub (T := T) σ' haddK haddL hnegK hnegL ⟨(S.beta (i : ℕ) : K), hbT⟩
                ⟨S.xs ((i : ℕ) + 1), hx1T⟩ (SSLPAux.memSub (T := T) haddK hnegK hbT hx1T)
          _ = (τ (S.beta (i : ℕ)) : L) - StepSeq.ys B τ S y0 ((i : ℕ) + 1) := by rw [hσβ, hσx1]
          _ = logFun (σ' ⟨S.xs (i : ℕ), hxsT' i⟩) := by rw [← hLlt]
    have hlogpemap : σ' ⟨logFun (1 + ε), hlogpeT⟩ = logFun (1 + (σ' ⟨ε, hεT⟩ : L)) := by
      have hrexp := logFun_one_add_rexp hK hδK
      rw [haddK, honeK] at hrexp
      have hrexpmem : rexpFromExp (logFun (1 + ε)) ∈ (T : Set K) := by
        rw [hrexp]; exact h1εT
      have h1 : (⟨rexpFromExp (logFun (1 + ε)), hrexpmem⟩ : ↥T) = ⟨1 + ε, h1εT⟩ :=
        Subtype.ext hrexp
      have h3 : rexpFromExp (σ' ⟨logFun (1 + ε), hlogpeT⟩) = 1 + (σ' ⟨ε, hεT⟩ : L) := by
        rw [← hembrexp ⟨logFun (1 + ε), hlogpeT⟩ hrexpmem, h1, hep]
      have h3' : rexpFromExp (σ' ⟨logFun (1 + ε), hlogpeT⟩) = addE oneE (σ' ⟨ε, hεT⟩) := by
        rw [haddL, honeL]; exact h3
      rw [logFun_eq_of_rexp_eq hL hδL h3']
      congr 1
      rw [haddL, honeL]
    have hNxT := fun i : Fin n => hmemS (S4ExpF.dcl_mul_mem (T : Set K) (hmemD (hIntT (N i)))
        (hmemD (hlogxsT i)))
    have hsummem : ∀ t : Finset (Fin n),
        (∑ i ∈ t, (N i : K) * logFun (S.xs (i : ℕ))) ∈ (T : Set K) := by
      intro t
      induction t using Finset.induction with
      | empty => simpa using h0T
      | insert a s ha ih =>
          rw [Finset.sum_insert ha]
          exact SSLPAux.memAdd (T := T) haddK (hNxT a) ih
    have hsumT := hsummem Finset.univ
    have hsumimg : σ' ⟨∑ i : Fin n, (N i : K) * logFun (S.xs (i : ℕ)), hsumT⟩ =
        ∑ i : Fin n, (N i : L) * logFun (σ' ⟨S.xs (i : ℕ), hxsT' i⟩) := by
      have h := SSLPAux.embSum (T := T) σ' haddK haddL hzK hzL Finset.univ
        (fun i : Fin n => ⟨(N i : K) * logFun (S.xs (i : ℕ)), hNxT i⟩)
        (fun t => hsummem t)
      rw [show (⟨∑ i : Fin n, (N i : K) * logFun (S.xs (i : ℕ)), hsumT⟩ : ↥T) =
          ⟨∑ i ∈ (Finset.univ : Finset (Fin n)),
              ((fun i : Fin n =>
                (⟨(N i : K) * logFun (S.xs (i : ℕ)), hNxT i⟩ : ↥T)) i : K),
            hsummem Finset.univ⟩ from Subtype.ext rfl]
      rw [h]
      apply Finset.sum_congr rfl
      intro i _
      rw [SSLPAux.embMul (T := T) σ' hmulK hmulL ⟨(N i : K), hIntT (N i)⟩
            ⟨logFun (S.xs (i : ℕ)), hlogxsT i⟩ (hNxT i),
          SSLPAux.embInt (T := T) σ' haddK haddL honeK honeL hnegK hnegL hzK hzL hIntT (N i),
          hlogxmap i]
    have hsum2T := hmemS (S4ExpF.dcl_add_mem (T : Set K) (hmemD hlogzT) (hmemD hsumT))
    have hLHSmem := hmemS (S4ExpF.dcl_mul_mem (T : Set K) (hmemD (hIntT Q)) (hmemD hlogwT))
    have hRHSmem := hmemS (S4ExpF.dcl_add_mem (T : Set K) (hmemD hsum2T) (hmemD hlogpeT))
    have hmapLHS : σ' ⟨(Q : K) * logFun w, hLHSmem⟩ = (Q : L) * σ' ⟨logFun w, hlogwT⟩ := by
      rw [SSLPAux.embMul (T := T) σ' hmulK hmulL ⟨(Q : K), hIntT Q⟩
            ⟨logFun w, hlogwT⟩ hLHSmem,
          SSLPAux.embInt (T := T) σ' haddK haddL honeK honeL hnegK hnegL hzK hzL hIntT Q]
    have hmapRHS : σ' ⟨logFun z + (∑ i : Fin n, (N i : K) * logFun (S.xs (i : ℕ)))
          + logFun (1 + ε), hRHSmem⟩ =
        logFun (σ' ⟨z, hzT⟩)
          + (∑ i : Fin n, (N i : L) * logFun (σ' ⟨S.xs (i : ℕ), hxsT' i⟩))
          + logFun (1 + (σ' ⟨ε, hεT⟩ : L)) := by
      rw [SSLPAux.embAdd (T := T) σ' haddK haddL
            ⟨logFun z + (∑ i : Fin n, (N i : K) * logFun (S.xs (i : ℕ))), hsum2T⟩
            ⟨logFun (1 + ε), hlogpeT⟩ hRHSmem,
          SSLPAux.embAdd (T := T) σ' haddK haddL ⟨logFun z, hlogzT⟩
            ⟨(∑ i : Fin n, (N i : K) * logFun (S.xs (i : ℕ))), hsumT⟩ hsum2T,
          hsumimg, hlogzmap, hlogpemap]
    have hconv : (⟨(Q : K) * logFun w, hLHSmem⟩ : ↥T) =
        ⟨logFun z + (∑ i : Fin n, (N i : K) * logFun (S.xs (i : ℕ))) + logFun (1 + ε),
          hRHSmem⟩ := Subtype.ext hkeyK
    have hA : (Q : L) * σ' ⟨logFun w, hlogwT⟩ =
        logFun (σ' ⟨z, hzT⟩)
          + (∑ i : Fin n, (N i : L) * logFun (σ' ⟨S.xs (i : ℕ), hxsT' i⟩))
          + logFun (1 + (σ' ⟨ε, hεT⟩ : L)) := by
      rw [← hmapLHS, hconv, hmapRHS]
    have hQeq : (Q : L) * σ' ⟨logFun w, hlogwT⟩ = (Q : L) * logFun (σ' ⟨w, hwT⟩) := by
      rw [hA, hkeyL]
    exact mul_left_cancel₀ (Int.cast_ne_zero.mpr (ne_of_gt hQ)) hQeq
  · have hlogw0 : logFun w = 0 :=
      S4ExpF.logFun_eq_zero_of_not_pos hK haddK honeK hlenegK w hwpos
    have h1 : (⟨logFun w, hlogwT⟩ : ↥T) = ⟨(0 : K), h0T⟩ := Subtype.ext hlogw0
    have h2 : (σ' ⟨w, hwT⟩ : L) ≤ 0 := by
      have h := (hleT ⟨w, hwT⟩ ⟨(0 : K), h0T⟩).mp (le_of_not_gt hwpos)
      rwa [SSLPAux.embZero (T := T) σ' hzK hzL h0T] at h
    have h3 : logFun (σ' ⟨w, hwT⟩) = 0 :=
      S4ExpF.logFun_eq_zero_of_not_pos hL haddL honeL hlenegL (σ' ⟨w, hwT⟩) (not_lt.mpr h2)
    rw [h1, SSLPAux.embZero (T := T) σ' hzK hzL h0T, h3]


end Work.WilC5
