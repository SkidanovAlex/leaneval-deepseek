import Mathlib
import Submission.Work.FIArea7.P231Defs
import Submission.Work.FIArea7.P231.LBilinStar_eq_epsSums
import Submission.Work.FIArea7.P231.card_strip_le
import Submission.Work.FIArea7.P231M.Defs
import Submission.Work.FIArea7.P231M.Aux1
import Submission.Work.FIArea7.P231M.EpsStepExplicit
import Submission.Work.FIArea7.P231M.multEpsExpansion
import Submission.Work.FIArea7.P231M.kstarBound
import Submission.Work.FIArea7.P231M.ReducedArith
import Submission.Work.FIArea7.norm_SChiK_le

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.FIArea7.P231M

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## The multiplier sign at `σ = 1` -/

lemma hilbertInf_zero_left (x : ℤ) : Work.FIArea7.HilbertInf x 0 = 1 := by
  rw [Work.FIArea7.HilbertInf, if_neg]; norm_num

lemma hilbertInf_one_zero : Work.FIArea7.HilbertInf 1 0 = 1 := hilbertInf_zero_left 1

lemma multEps_one (z : GaussianInt) : Work.FIArea7.MultEps 1 z = 1 := by
  unfold Work.FIArea7.MultEps
  have h1 : (1 : GaussianInt).re = 1 := rfl
  have h2 : (1 : GaussianInt).im = 0 := rfl
  rw [h1, h2, one_mul, zero_mul, neg_zero]
  by_cases hc : z.re > 0
  · rw [if_pos hc, hilbertInf_one_zero, hilbertInf_zero_left]
    norm_num
  · rw [if_neg hc, hilbertInf_one_zero, hilbertInf_zero_left]
    norm_num

lemma epsSummand_one_apply {σ : GaussianInt} {A B : GaussianInt → ℂ} {w z : GaussianInt}
    (h : σ = 1) :
    Work.FIArea7.epsSummand σ A B w z
      = (if Work.FIPlan.GaussCoprime w z then A w * B z * Work.FIArea7.JKSym (w * z) else 0) := by
  subst h
  rw [Work.FIArea7.epsSummand]
  by_cases hgc : Work.FIPlan.GaussCoprime w z
  · rw [if_pos hgc, if_pos hgc, multEps_one]
    simp
  · rw [if_neg hgc, if_neg hgc]

/-! ## The reduction -/

theorem reducedBound_of_prop214 (h : Work.FIArea7.Prop214) : Work.FIArea7.ReducedBound := by
  obtain ⟨Cstar, Astar, hCstar, hAstar, hKstar⟩ := Work.FIArea7.P231.kstarBound_of_prop214 h
  obtain ⟨Cexp, hCexp, hexp⟩ := Work.FIArea7.P231.multEpsExpansion
  obtain ⟨Ccard, hCcard, hcard⟩ := Work.FIArea7.P231.card_strip_le
  have hCw : ∀ (M : ℝ), 1 ≤ M → ∀ S : Finset GaussianInt,
      (∀ w ∈ S, (Work.FIPlan.gnorm w : ℝ) ≤ M) → ((S.card : ℝ) ≤ 25 * M) := card_gnorm_le25
  have hKb0 : 0 ≤ KbConst 25 Cexp Ccard Cstar := by
    rw [KbConst, KbadConst]
    have h1 : (0 : ℝ) ≤ (1 / 2) * Cexp * (1 + Real.log 4) ^ 4 := by positivity
    have h2 : (0 : ℝ) ≤ 2 * 25 * Ccard * (3 * Real.sqrt 2 + 6) := by positivity
    have h3 : (0 : ℝ) ≤ (1 / 2) * Cexp * (1 + Real.log 4) ^ 4 * Cstar := by positivity
    have h4 : (0 : ℝ) ≤ ((1 / 2) * Cexp * (1 + Real.log 4) ^ 4 + 1) * (2 * 25 * Ccard * (3 * Real.sqrt 2 + 6)) :=
      mul_nonneg (by linarith [h1]) h2
    linarith
  refine ⟨4 * (Cstar + 3 + KbConst 25 Cexp Ccard Cstar), Astar + 16, ?_, ?_, ?_⟩
  · linarith
  · linarith
  intro M N c k χ α β hc hM hN hχ hχmul hα hαc hβ hβc
  have hM1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  set P : ℝ := PP (M : ℝ) (N : ℝ) with hPdef
  set L : ℝ := LL (M : ℝ) (N : ℝ) with hLdef
  set Bound : ℝ := Cstar * P * L ^ Astar with hBounddef
  have hP0 : 0 ≤ P := by rw [hPdef]; exact PP_nonneg (by positivity) (by positivity)
  have hL1 : 1 ≤ L := by rw [hLdef]; exact LL_one_le hM1 hN1
  have hL0 : 0 < L := by rw [hLdef]; exact LL_pos hM1 hN1
  have hBound0 : 0 ≤ Bound := by rw [hBounddef]; positivity
  -- the K* input for the ε-step
  have hK : ∀ (Rw Rz : ℤ) (A B : GaussianInt → ℂ),
      (∀ w, ‖A w‖ ≤ 1) → (∀ z, ‖B z‖ ≤ 1) →
      (∀ w, A w ≠ 0 → Work.FIPlan.IsPrimary w ∧ IsCoprime w.re w.im ∧
        (Work.FIPlan.gnorm w : ℝ) ≤ (M : ℝ)) →
      (∀ z, B z ≠ 0 → Work.FIPlan.IsPrimary z ∧ (Work.FIPlan.gnorm z : ℝ) ≤ (N : ℝ)) →
      ‖Work.FIArea7.KBilinStar Rw Rz A B‖ ≤ Bound := by
    intro Rw Rz A B hA1 hB1 hAs hBs
    have hb := hKstar (M : ℝ) (N : ℝ) Rw Rz A B hM1 hN1 hA1 hB1 hAs hBs
    rw [hBounddef, hPdef, hLdef]
    simpa [PP, LL, mul_assoc] using hb
  have heps := Work.FIArea7.P231.epsStepUniformExplicit hM1 hN1 hBound0 hCexp hCcard
    (by norm_num : (0 : ℝ) < 25) hCw hK hexp hcard
  -- elementary coefficient bounds
  have hpsi : ∀ e : GaussianInt, ‖Work.FIArea7.grossenChar χ k e‖ ≤ 1 :=
    fun e => Work.FIArea7.norm_grossenChar_le_one χ k hχ e
  have hcoefA : ∀ (e w : GaussianInt), w ∈ primDisc M →
      ‖α (Work.FIPlan.gnorm w) * Work.FIArea7.grossenChar χ k w
        * ((Work.FIArea7.DirichletSym e w : ℤ) : ℂ)‖ ≤ 1 := by
    intro e w hw
    obtain ⟨hwP, hwc, hwgn⟩ := mem_primDisc.mp hw
    have hw0 : w ≠ 0 := Work.FIArea4.isPrimary_ne_zero hwP
    have hgn1 : 1 ≤ Work.FIPlan.gnorm w := Nat.one_le_iff_ne_zero.mpr (Work.FIArea4.gnorm_ne_zero hw0)
    have h1 : ‖α (Work.FIPlan.gnorm w)‖ ≤ 1 := hα _ (Finset.mem_Icc.mpr ⟨hgn1, hwgn⟩)
    have h2 : ‖Work.FIArea7.grossenChar χ k w‖ ≤ 1 := hpsi w
    have h3 : ‖(((Work.FIArea7.DirichletSym e w : ℤ)) : ℂ)‖ ≤ 1 := normDirichletSymLeOne e w
    rw [norm_mul, norm_mul]
    calc ‖α (Work.FIPlan.gnorm w)‖ * ‖Work.FIArea7.grossenChar χ k w‖
          * ‖(((Work.FIArea7.DirichletSym e w : ℤ)) : ℂ)‖
        ≤ 1 * 1 * 1 :=
          mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) (by positivity)) h3
            (norm_nonneg _) (by positivity)
      _ = 1 := by norm_num
  have hcoefB : ∀ (e z : GaussianInt), z ∈ Work.FIArea7.primaryDisc N →
      ‖β (Work.FIPlan.gnorm z) * Work.FIArea7.grossenChar χ k z
        * ((Work.FIArea7.DirichletSym e z : ℤ) : ℂ)‖ ≤ 1 := by
    intro e z hz
    obtain ⟨hzP, hzgn⟩ := Work.FIArea7.mem_primaryDisc.mp hz
    have hz0 : z ≠ 0 := Work.FIArea4.isPrimary_ne_zero hzP
    have hgn1 : 1 ≤ Work.FIPlan.gnorm z := Nat.one_le_iff_ne_zero.mpr (Work.FIArea4.gnorm_ne_zero hz0)
    have h1 : ‖β (Work.FIPlan.gnorm z)‖ ≤ 1 := hβ _ (Finset.mem_Icc.mpr ⟨hgn1, hzgn⟩)
    have h2 : ‖Work.FIArea7.grossenChar χ k z‖ ≤ 1 := hpsi z
    have h3 : ‖(((Work.FIArea7.DirichletSym e z : ℤ)) : ℂ)‖ ≤ 1 := normDirichletSymLeOne e z
    rw [norm_mul, norm_mul]
    calc ‖β (Work.FIPlan.gnorm z)‖ * ‖Work.FIArea7.grossenChar χ k z‖
          * ‖(((Work.FIArea7.DirichletSym e z : ℤ)) : ℂ)‖
        ≤ 1 * 1 * 1 :=
          mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) (by positivity)) h3
            (norm_nonneg _) (by positivity)
      _ = 1 := by norm_num
  -- bounds for the restricted coefficients
  have hbndA : ∀ (e : GaussianInt), ∀ w : GaussianInt,
      ‖restrPrim M (fun w => α (Work.FIPlan.gnorm w) * Work.FIArea7.grossenChar χ k w
        * ((Work.FIArea7.DirichletSym e w : ℤ) : ℂ)) w‖ ≤ 1 := by
    intro e w
    by_cases hw : w ∈ primDisc M
    · rw [restrPrim_apply_of_mem hw]; exact hcoefA e w hw
    · rw [restrPrim_apply_of_notMem hw]; norm_num
  have hbndB : ∀ (e : GaussianInt), ∀ z : GaussianInt,
      ‖restrDisc N (fun z => β (Work.FIPlan.gnorm z) * Work.FIArea7.grossenChar χ k z
        * ((Work.FIArea7.DirichletSym e z : ℤ) : ℂ)) z‖ ≤ 1 := by
    intro e z
    by_cases hz : z ∈ Work.FIArea7.primaryDisc N
    · rw [restrDisc_apply_of_mem hz]; exact hcoefB e z hz
    · rw [restrDisc_apply_of_notMem hz]; norm_num
  have hsupA : ∀ (e : GaussianInt), ∀ w : GaussianInt,
      restrPrim M (fun w => α (Work.FIPlan.gnorm w) * Work.FIArea7.grossenChar χ k w
        * ((Work.FIArea7.DirichletSym e w : ℤ) : ℂ)) w ≠ 0 →
      Work.FIPlan.IsPrimary w ∧ IsCoprime w.re w.im ∧ (Work.FIPlan.gnorm w : ℝ) ≤ (M : ℝ) := by
    intro e w hw
    have hw' : w ∈ primDisc M := by
      by_contra hcon
      exact hw (restrPrim_apply_of_notMem hcon)
    obtain ⟨h1, h2, h3⟩ := mem_primDisc.mp hw'
    exact ⟨h1, h2, by exact_mod_cast h3⟩
  have hsupB : ∀ (e : GaussianInt), ∀ z : GaussianInt,
      restrDisc N (fun z => β (Work.FIPlan.gnorm z) * Work.FIArea7.grossenChar χ k z
        * ((Work.FIArea7.DirichletSym e z : ℤ) : ℂ)) z ≠ 0 →
      Work.FIPlan.IsPrimary z ∧ (Work.FIPlan.gnorm z : ℝ) ≤ (N : ℝ) := by
    intro e z hz
    have hz' : z ∈ Work.FIArea7.primaryDisc N := by
      by_contra hcon
      exact hz (restrDisc_apply_of_notMem hcon)
    exact ⟨(Work.FIArea7.mem_primaryDisc.mp hz').1, by exact_mod_cast (Work.FIArea7.mem_primaryDisc.mp hz').2⟩
  -- abbreviations
  set D : ℝ := Work.FIArea7.P231.epsDen (M : ℝ) (N : ℝ) Bound
      + Work.FIArea7.P231.epsBound0 25 Cexp (M : ℝ) Ccard (N : ℝ) Bound with hDdef
  have hD0 : 0 ≤ D := by
    rw [hDdef]
    have h1 : 0 ≤ Work.FIArea7.P231.epsDen (M : ℝ) (N : ℝ) Bound := by
      rw [Work.FIArea7.P231.epsDen]
      have h3 : (0 : ℝ) ≤ Bound + (M : ℝ) * Real.sqrt (N : ℝ) + Real.sqrt ((M : ℝ) * (N : ℝ)) := by
        have h4 : (0 : ℝ) ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
        have h5 : (0 : ℝ) ≤ (M : ℝ) * Real.sqrt (N : ℝ) := by positivity
        have h6 : (0 : ℝ) ≤ Real.sqrt ((M : ℝ) * (N : ℝ)) := Real.sqrt_nonneg _
        linarith
      positivity
    have h2 : 0 ≤ Work.FIArea7.P231.epsBound0 25 Cexp (M : ℝ) Ccard (N : ℝ) Bound := by
      rw [Work.FIArea7.P231.epsBound0]
      have h7 : (0 : ℝ) ≤ Work.FIArea7.P231.epsKbad 25 (M : ℝ) Ccard (N : ℝ) := by
        rw [Work.FIArea7.P231.epsKbad, Work.FIArea7.P231.epsKz]; positivity
      have h6 : (0 : ℝ) ≤ Bound + Work.FIArea7.P231.epsKbad 25 (M : ℝ) Ccard (N : ℝ) := by
        linarith
      have h8 : (0 : ℝ) ≤ (1 / 2) * Cexp * (1 + Real.log 4) ^ 4
          * (Real.log ((M : ℝ) * (N : ℝ) + 2)) ^ 4 := by positivity
      have h9 : (0 : ℝ) ≤ (1 / 2) * Cexp * (1 + Real.log 4) ^ 4
          * (Real.log ((M : ℝ) * (N : ℝ) + 2)) ^ 4
          * (Bound + Work.FIArea7.P231.epsKbad 25 (M : ℝ) Ccard (N : ℝ)) := mul_nonneg h8 h6
      linarith
    linarith
  -- the main bound, term by term
  rw [Work.FIArea7.P231.LBilinStar_eq_epsSums hc hM hN k χ hχmul α β hαc hβc]
  have hterm : ∀ e ∈ Work.FIArea7.primaryPrimSet c,
      ‖Work.FIArea7.grossenChar χ k e * Work.FIArea7.JKSym e *
          (∑ w ∈ Work.FIArea7.primaryDisc M, ∑ z ∈ Work.FIArea7.primaryDisc N,
              Work.FIArea7.epsSummand e
                (fun w => α (Work.FIPlan.gnorm w) * Work.FIArea7.grossenChar χ k w
                  * ((Work.FIArea7.DirichletSym e w : ℤ) : ℂ))
                (fun z => β (Work.FIPlan.gnorm z) * Work.FIArea7.grossenChar χ k z
                  * ((Work.FIArea7.DirichletSym e z : ℤ) : ℂ)) w z)‖
        ≤ (if e = 1 then Bound else D) := by
    intro e he
    by_cases he1 : e = 1
    · -- the exceptional term `e = 1`
      subst he1
      rw [if_pos rfl]
      have hid : (∑ w ∈ Work.FIArea7.primaryDisc M, ∑ z ∈ Work.FIArea7.primaryDisc N,
              Work.FIArea7.epsSummand 1
                (fun w => α (Work.FIPlan.gnorm w) * Work.FIArea7.grossenChar χ k w
                  * ((Work.FIArea7.DirichletSym 1 w : ℤ) : ℂ))
                (fun z => β (Work.FIPlan.gnorm z) * Work.FIArea7.grossenChar χ k z
                  * ((Work.FIArea7.DirichletSym 1 z : ℤ) : ℂ)) w z)
          = Work.FIArea7.KBilinStar (M : ℤ) (N : ℤ)
              (restrPrim M (fun w => α (Work.FIPlan.gnorm w) * Work.FIArea7.grossenChar χ k w
                * ((Work.FIArea7.DirichletSym 1 w : ℤ) : ℂ)))
              (restrDisc N (fun z => β (Work.FIPlan.gnorm z) * Work.FIArea7.grossenChar χ k z
                * ((Work.FIArea7.DirichletSym 1 z : ℤ) : ℂ))) := by
        rw [← epsSumsGboxEqPrimaryDisc 1 M N
          (fun w => α (Work.FIPlan.gnorm w) * Work.FIArea7.grossenChar χ k w
            * ((Work.FIArea7.DirichletSym 1 w : ℤ) : ℂ))
          (fun z => β (Work.FIPlan.gnorm z) * Work.FIArea7.grossenChar χ k z
            * ((Work.FIArea7.DirichletSym 1 z : ℤ) : ℂ))]
        rw [Work.FIArea7.KBilinStar]
        refine Finset.sum_congr rfl (fun w _ => Finset.sum_congr rfl (fun z _ => ?_))
        rw [epsSummand_one_apply rfl]
      have h1 : ‖Work.FIArea7.grossenChar χ k 1‖ ≤ 1 := hpsi 1
      have h2 : ‖Work.FIArea7.JKSym 1‖ ≤ 1 := Work.FIArea7.norm_JKSym_le_one 1
      have h3 : ‖Work.FIArea7.grossenChar χ k 1‖ * ‖Work.FIArea7.JKSym 1‖ ≤ 1 :=
        mul_le_one₀ h1 (norm_nonneg _) h2
      have h4 : ‖Work.FIArea7.grossenChar χ k 1 * Work.FIArea7.JKSym 1 *
            (∑ w ∈ Work.FIArea7.primaryDisc M, ∑ z ∈ Work.FIArea7.primaryDisc N,
              Work.FIArea7.epsSummand 1
                (fun w => α (Work.FIPlan.gnorm w) * Work.FIArea7.grossenChar χ k w
                  * ((Work.FIArea7.DirichletSym 1 w : ℤ) : ℂ))
                (fun z => β (Work.FIPlan.gnorm z) * Work.FIArea7.grossenChar χ k z
                  * ((Work.FIArea7.DirichletSym 1 z : ℤ) : ℂ)) w z)‖
          ≤ ‖∑ w ∈ Work.FIArea7.primaryDisc M, ∑ z ∈ Work.FIArea7.primaryDisc N,
              Work.FIArea7.epsSummand 1
                (fun w => α (Work.FIPlan.gnorm w) * Work.FIArea7.grossenChar χ k w
                  * ((Work.FIArea7.DirichletSym 1 w : ℤ) : ℂ))
                (fun z => β (Work.FIPlan.gnorm z) * Work.FIArea7.grossenChar χ k z
                  * ((Work.FIArea7.DirichletSym 1 z : ℤ) : ℂ)) w z‖ := by
        rw [norm_mul, norm_mul]
        calc ‖Work.FIArea7.grossenChar χ k 1‖ * ‖Work.FIArea7.JKSym 1‖ *
              ‖∑ w ∈ Work.FIArea7.primaryDisc M, ∑ z ∈ Work.FIArea7.primaryDisc N,
                Work.FIArea7.epsSummand 1
                  (fun w => α (Work.FIPlan.gnorm w) * Work.FIArea7.grossenChar χ k w
                    * ((Work.FIArea7.DirichletSym 1 w : ℤ) : ℂ))
                  (fun z => β (Work.FIPlan.gnorm z) * Work.FIArea7.grossenChar χ k z
                    * ((Work.FIArea7.DirichletSym 1 z : ℤ) : ℂ)) w z‖
            ≤ 1 * ‖∑ w ∈ Work.FIArea7.primaryDisc M, ∑ z ∈ Work.FIArea7.primaryDisc N,
                Work.FIArea7.epsSummand 1
                  (fun w => α (Work.FIPlan.gnorm w) * Work.FIArea7.grossenChar χ k w
                    * ((Work.FIArea7.DirichletSym 1 w : ℤ) : ℂ))
                  (fun z => β (Work.FIPlan.gnorm z) * Work.FIArea7.grossenChar χ k z
                    * ((Work.FIArea7.DirichletSym 1 z : ℤ) : ℂ)) w z‖ :=
              mul_le_mul_of_nonneg_right h3 (norm_nonneg _)
          _ = _ := one_mul _
      refine le_trans h4 ?_
      rw [hid]
      exact hK (M : ℤ) (N : ℤ) _ _ (hbndA 1) (hbndB 1) (hsupA 1) (hsupB 1)
    · -- the generic term: the ε-step
      rw [if_neg he1]
      obtain ⟨heP, hegn, hec⟩ := Work.FIArea7.mem_primaryPrimSet.mp he
      have hei : e.im ≠ 0 := Work.FIArea7.P231.im_ne_zero_of_isPrimary_ne_one heP hec he1
      have hid := epsSumsGboxEqPrimaryDisc e M N
        (fun w => α (Work.FIPlan.gnorm w) * Work.FIArea7.grossenChar χ k w
          * ((Work.FIArea7.DirichletSym e w : ℤ) : ℂ))
        (fun z => β (Work.FIPlan.gnorm z) * Work.FIArea7.grossenChar χ k z
          * ((Work.FIArea7.DirichletSym e z : ℤ) : ℂ))
      have hb := heps e heP hec hei (M : ℤ) (N : ℤ)
        (restrPrim M (fun w => α (Work.FIPlan.gnorm w) * Work.FIArea7.grossenChar χ k w
          * ((Work.FIArea7.DirichletSym e w : ℤ) : ℂ)))
        (restrDisc N (fun z => β (Work.FIPlan.gnorm z) * Work.FIArea7.grossenChar χ k z
          * ((Work.FIArea7.DirichletSym e z : ℤ) : ℂ)))
        (hbndA e) (hbndB e) (hsupA e) (hsupB e)
      rw [hid] at hb
      have h3 : ‖Work.FIArea7.grossenChar χ k e‖ * ‖Work.FIArea7.JKSym e‖ ≤ 1 :=
        mul_le_one₀ (hpsi e) (norm_nonneg _) (Work.FIArea7.norm_JKSym_le_one e)
      rw [norm_mul, norm_mul]
      calc ‖Work.FIArea7.grossenChar χ k e‖ * ‖Work.FIArea7.JKSym e‖ *
            ‖∑ w ∈ Work.FIArea7.primaryDisc M, ∑ z ∈ Work.FIArea7.primaryDisc N,
              Work.FIArea7.epsSummand e
                (fun w => α (Work.FIPlan.gnorm w) * Work.FIArea7.grossenChar χ k w
                  * ((Work.FIArea7.DirichletSym e w : ℤ) : ℂ))
                (fun z => β (Work.FIPlan.gnorm z) * Work.FIArea7.grossenChar χ k z
                  * ((Work.FIArea7.DirichletSym e z : ℤ) : ℂ)) w z‖
          ≤ 1 * ‖∑ w ∈ Work.FIArea7.primaryDisc M, ∑ z ∈ Work.FIArea7.primaryDisc N,
              Work.FIArea7.epsSummand e
                (fun w => α (Work.FIPlan.gnorm w) * Work.FIArea7.grossenChar χ k w
                  * ((Work.FIArea7.DirichletSym e w : ℤ) : ℂ))
                (fun z => β (Work.FIPlan.gnorm z) * Work.FIArea7.grossenChar χ k z
                  * ((Work.FIArea7.DirichletSym e z : ℤ) : ℂ)) w z‖ :=
            mul_le_mul_of_nonneg_right h3 (norm_nonneg _)
        _ = _ := one_mul _
        _ ≤ D := by rw [hDdef]; exact hb
  -- sum the terms
  have hnormsum : ‖∑ e ∈ Work.FIArea7.primaryPrimSet c,
        Work.FIArea7.grossenChar χ k e * Work.FIArea7.JKSym e *
          (∑ w ∈ Work.FIArea7.primaryDisc M, ∑ z ∈ Work.FIArea7.primaryDisc N,
              Work.FIArea7.epsSummand e
                (fun w => α (Work.FIPlan.gnorm w) * Work.FIArea7.grossenChar χ k w
                  * ((Work.FIArea7.DirichletSym e w : ℤ) : ℂ))
                (fun z => β (Work.FIPlan.gnorm z) * Work.FIArea7.grossenChar χ k z
                  * ((Work.FIArea7.DirichletSym e z : ℤ) : ℂ)) w z)‖
      ≤ 2 * (((c.divisors.card : ℕ) : ℝ)) * (D + Bound) := by
    have hτ1 : (1 : ℝ) ≤ ((c.divisors.card : ℕ) : ℝ) := by
      have : 1 ≤ c.divisors.card := Finset.card_pos.mpr
        ⟨1, Nat.mem_divisors.mpr ⟨one_dvd c, by omega⟩⟩
      exact_mod_cast this
    calc ‖∑ e ∈ Work.FIArea7.primaryPrimSet c, _‖
        ≤ ∑ e ∈ Work.FIArea7.primaryPrimSet c, (if e = 1 then Bound else D) :=
          le_trans (norm_sum_le _ _) (Finset.sum_le_sum hterm)
      _ = (∑ e ∈ (Work.FIArea7.primaryPrimSet c).filter (fun e => e = 1), Bound)
            + ∑ e ∈ (Work.FIArea7.primaryPrimSet c).filter (fun e => ¬ (e = 1)), D := by
          rw [← Finset.sum_filter_add_sum_filter_not (s := Work.FIArea7.primaryPrimSet c)
            (p := fun e => e = 1) (f := fun e => if e = 1 then Bound else D)]
          congr 1
          · refine Finset.sum_congr rfl (fun e he => ?_)
            rw [if_pos (Finset.mem_filter.mp he).2]
          · refine Finset.sum_congr rfl (fun e he => ?_)
            rw [if_neg (Finset.mem_filter.mp he).2]
      _ ≤ 1 * Bound + (((c.divisors.card : ℕ) : ℝ)) * D := by
          have hc1 : (∑ e ∈ (Work.FIArea7.primaryPrimSet c).filter (fun e => e = 1), Bound)
              ≤ 1 * Bound := by
            have hsub : (Work.FIArea7.primaryPrimSet c).filter (fun e => e = 1)
                ⊆ ({1} : Finset GaussianInt) := by
              intro e he
              rw [Finset.mem_filter] at he
              rw [Finset.mem_singleton]
              exact he.2
            calc (∑ e ∈ (Work.FIArea7.primaryPrimSet c).filter (fun e => e = 1), Bound)
                ≤ ∑ _e ∈ ({1} : Finset GaussianInt), Bound :=
                  Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => hBound0)
              _ = 1 * Bound := by simp
          have hc2 : (∑ e ∈ (Work.FIArea7.primaryPrimSet c).filter (fun e => ¬ (e = 1)), D)
              ≤ (((c.divisors.card : ℕ) : ℝ)) * D := by
            calc (∑ _e ∈ (Work.FIArea7.primaryPrimSet c).filter (fun e => ¬ (e = 1)), D)
                ≤ ∑ _e ∈ Work.FIArea7.primaryPrimSet c, D :=
                  Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
                    (fun _ _ _ => hD0)
              _ = ((Work.FIArea7.primaryPrimSet c).card : ℝ) * D := by
                  rw [Finset.sum_const, nsmul_eq_mul]
              _ ≤ (((c.divisors.card : ℕ) : ℝ)) * D := by
                  refine mul_le_mul_of_nonneg_right ?_ hD0
                  exact_mod_cast primaryPrimSetCardLeTau c
          linarith
      _ ≤ 2 * (((c.divisors.card : ℕ) : ℝ)) * (D + Bound) := by
          have hb : Bound ≤ ((c.divisors.card : ℕ) : ℝ) * Bound :=
            le_mul_of_one_le_left hBound0 hτ1
          have hd : D ≤ ((c.divisors.card : ℕ) : ℝ) * D :=
            le_mul_of_one_le_left hD0 hτ1
          linarith
  refine le_trans hnormsum ?_
  have hX0 : 0 ≤ (Cstar + 3 + KbConst 25 Cexp Ccard Cstar) * P * L ^ (Astar + 16) := by positivity
  have hDX : D ≤ (Cstar + 3 + KbConst 25 Cexp Ccard Cstar) * P * L ^ (Astar + 16) := by
    rw [hDdef]
    exact reducedArith (by norm_num : (0 : ℝ) < 25) hCcard hCexp hCstar hAstar.le hM1 hN1
  have hBX : Bound ≤ (Cstar + 3 + KbConst 25 Cexp Ccard Cstar) * P * L ^ (Astar + 16) := by
    rw [hBounddef]
    have h1 : L ^ Astar ≤ L ^ (Astar + 16) := by
      have hthis : (1 : ℝ) ≤ L ^ (16 : ℝ) := Real.one_le_rpow hL1 (by norm_num)
      calc L ^ Astar = L ^ Astar * 1 := by ring
        _ ≤ L ^ Astar * L ^ (16 : ℝ) :=
            mul_le_mul_of_nonneg_left hthis (by positivity)
        _ = L ^ (Astar + 16) := (Real.rpow_add hL0 Astar 16).symm
    have h4 : Cstar * P * L ^ Astar ≤ Cstar * P * L ^ (Astar + 16) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h5 : Cstar * P * L ^ (Astar + 16)
        ≤ (Cstar + 3 + KbConst 25 Cexp Ccard Cstar) * P * L ^ (Astar + 16) := by
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      linarith
    exact le_trans h4 h5
  calc 2 * (((c.divisors.card : ℕ) : ℝ)) * (D + Bound)
      ≤ 2 * (((c.divisors.card : ℕ) : ℝ))
          * (2 * ((Cstar + 3 + KbConst 25 Cexp Ccard Cstar) * P * L ^ (Astar + 16))) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        linarith [hDX, hBX]
    _ = 4 * (Cstar + 3 + KbConst 25 Cexp Ccard Cstar) * (((c.divisors.card : ℕ) : ℝ))
          * P * L ^ (Astar + 16) := by ring
    _ = 4 * (Cstar + 3 + KbConst 25 Cexp Ccard Cstar) * ((c.divisors.card : ℕ) : ℝ)
          * ((M : ℝ) + (N : ℝ)) ^ ((1 : ℝ) / 12) * ((M : ℝ) * (N : ℝ)) ^ ((11 : ℝ) / 12)
          * (Real.log ((M : ℝ) * (N : ℝ) + 2)) ^ (Astar + 16) := by
        rw [hPdef, hLdef, PP, LL]
        ring

end

end Work.FIArea7.P231M
