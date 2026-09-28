import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.MDCommon
import Submission.Work.HP.MDEstimates.ell44_convenient
import Submission.Work.HP.quartic44
import Submission.Work.HP.MDEstimates.ballCount_R0_M
import Submission.Work.HP.MDEstimates.mu_div_det_real
import Submission.Work.HP.MDEstimates.detGam_lower
import Submission.Work.HP.MDEstimates.hiparts.HiDefs
import Submission.Work.HP.MDBasic.finite_sets
import Submission.Work.HP.MDBasic.mem_Gam_iff
import Submission.Work.HP.Sig2.omega_li
import Submission.Work.HP.Sig2.d3_lt_of_caseI
import Submission.Work.HP.Sig2.gam_rank_det
import Submission.Work.HP.Sig2.nu_indep
import Submission.Work.HP.MDEstimates.dmin_facts
import Submission.Work.HP.lam_basic
import Submission.Work.HP.Q44Child.gam_rank
import Submission.Work.HP.MDEstimates.hiparts.pairS0_hi_bound
import Submission.Work.HP.MDEstimates.hiparts.hi_cell_sum
import Submission.Work.HP.MDEstimates.hiparts.hi_cell_arith

set_option autoImplicit false
noncomputable section

open Finset
open scoped BigOperators

namespace Work.HP.MDEstimates

open Work.HP

/-! ## The index set of the `𝔡₃ > A^{1/20}` part of the case-`I` sum -/

/-- The set of the statement: pairs of `Ω_{4,4}(B)` with `μ > A`, in Case I and with
`𝔡₃ > A^{1/20}`. -/
private def SHiSet (A B : ℝ) : Set ((Fin 5 → ℤ) × (Fin 5 → ℤ)) :=
  {p | p ∈ Omega 4 4 B ∧
      ¬ (muXY 4 p.1 p.2 ≤ A) ∧
      ¬ (dmin 2 ({p.1, p.2} : Set (Fin 5 → ℤ)) * dmin 2 ({p.1, p.2} : Set (Fin 5 → ℤ)) ^ 2
          ≤ dmin 3 ({p.1, p.2} : Set (Fin 5 → ℤ)) * (eNorm p.1 * eNorm p.2)) ∧
      A ^ ((1 : ℝ) / 20) < dmin 3 ({p.1, p.2} : Set (Fin 5 → ℤ))}

private lemma SHiSet_subset_Omega (A B : ℝ) : SHiSet A B ⊆ Omega 4 4 B :=
  fun _ hp => hp.1

private lemma SHiSet_finite (A B : ℝ) : (SHiSet A B).Finite :=
  ((MDBasic.finite_sets 4 4 A B (fun _ => True)).2.2).subset (SHiSet_subset_Omega A B)

/-- A pair whose `λ₁(Γ_{x,y})` exceeds `A` carries no coefficient vector of norm at most `A`. -/
private lemma pairS0_eq_zero_of_lam_gt {A : ℝ} {x y : Fin 5 → ℤ}
    (h : A < lam (Gam 4 4 x y) 1) : pairS0 4 4 A (x, y) = 0 := by
  have hempty : ({a : Mon 4 4 → ℤ | a ∈ primSet 4 4 A (fun _ => True) ∧
      formEval 4 4 a x = 0 ∧ formEval 4 4 a y = 0} : Set (Mon 4 4 → ℤ)) = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.mpr ?_
    rintro a ⟨⟨hprim, hnorm, -⟩, h1, h2⟩
    have hne : a ≠ 0 := by
      intro h0
      rw [IsPrim] at hprim
      have hz : Finset.univ.gcd a = 0 := by
        rw [Finset.gcd_eq_zero_iff]
        intro i _
        rw [h0]
        rfl
      rw [hz] at hprim
      exact one_ne_zero hprim.symm
    have hmem : a ∈ Gam 4 4 x y := (MDBasic.mem_Gam_iff 4 4 x y a).mpr ⟨h1, h2⟩
    have := lam_one_le_eNorm (Gam 4 4 x y) hmem hne
    linarith
  unfold pairS0
  rw [hempty, Set.ncard_empty]
  norm_num

private lemma NN_four_four : (NN 4 4 : ℝ) = 70 := by
  rw [NN]
  exact_mod_cast Q44Child.card_Mon_four_four

private lemma NN_four_four_nat : NN 4 4 = 70 := Q44Child.card_Mon_four_four

theorem Sigma2_44_I_hi :
    ∃ K B₀ : ℝ, 0 < K ∧ ∀ A B : ℝ, B₀ ≤ B → B / Real.log B ≤ A → A ≤ B ^ 2 →
      (∑ᶠ p ∈ {p : (Fin 5 → ℤ) × (Fin 5 → ℤ) | p ∈ Omega 4 4 B ∧
          ¬ (muXY 4 p.1 p.2 ≤ A) ∧
          ¬ (dmin 2 ({p.1, p.2} : Set (Fin 5 → ℤ)) * dmin 2 ({p.1, p.2} : Set (Fin 5 → ℤ)) ^ 2
              ≤ dmin 3 ({p.1, p.2} : Set (Fin 5 → ℤ)) * (eNorm p.1 * eNorm p.2)) ∧
          A ^ ((1 : ℝ) / 20) < dmin 3 ({p.1, p.2} : Set (Fin 5 → ℤ))},
        pairS0 4 4 A p)
        ≤ K * A ^ ((NN 4 4 : ℝ) - 2 - (1 : ℝ) / 32) * B ^ 2 := by
  obtain ⟨Kar, Bar, hKarpos, har⟩ := hiparts.hi_cell_arith
  obtain ⟨Ksu, Bsu, hKsupos, hsu⟩ := hiparts.hi_cell_sum
  obtain ⟨Kp, hKppos, hpbound⟩ := hiparts.pairS0_hi_bound
  obtain ⟨Kl, hKlpos, hell⟩ := (show ∃ K : ℝ, 0 < K ∧ ∀ Z Δ M : ℝ, 1 ≤ Z → 1 ≤ Δ → 1 ≤ M → (ell44 1 Z Δ M : ℝ) ≤ K * Z ^ ((9 : ℝ) / 2) * Δ ^ 2 * (Z ^ ((3 : ℝ) / 2) + Δ ^ ((3 : ℝ) / 2)) * Real.log (2 * Δ) ^ 2 * min Δ (M ^ 53) from by obtain ⟨K, hK, h⟩ := quartic44; exact ⟨K, hK, fun Z Δ M hZ hΔ hM => (h Z Δ M 1 hZ hΔ hM le_rfl).1⟩)
  refine ⟨Kp * Ksu * Kl * Kar, max (max Bar Bsu) (Real.exp 10), by positivity, ?_⟩
  intro A B hB hAle hAge
  -- basic size hypotheses
  have hBar : Bar ≤ B := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hB
  have hBsu : Bsu ≤ B := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hB
  have hexpB : Real.exp 10 ≤ B := le_trans (le_max_right _ _) hB
  have hB1 : 1 ≤ B := le_trans (Real.one_le_exp (by norm_num)) hexpB
  have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one hB1
  have hexp10pos : 0 < Real.exp 10 := Real.exp_pos 10
  have hlogBpos : 0 < Real.log B := by
    have h1 : Real.log (Real.exp 10) ≤ Real.log B := Real.log_le_log hexp10pos hexpB
    rw [Real.log_exp] at h1
    linarith
  have hApos : 0 < A := lt_of_lt_of_le (div_pos hBpos hlogBpos) hAle
  have hA1 : 1 ≤ A := by
    have h1 : 1 ≤ B / Real.log B := by
      rw [le_div_iff₀ hlogBpos]
      have := Real.log_le_self hBpos.le
      linarith
    linarith [hAle]
  -- the finsum is over a finite set
  have hfin : (SHiSet A B).Finite := SHiSet_finite A B
  change (∑ᶠ p ∈ SHiSet A B, pairS0 4 4 A p)
      ≤ Kp * Ksu * Kl * Kar * A ^ ((NN 4 4 : ℝ) - 2 - (1 : ℝ) / 32) * B ^ 2
  rw [finsum_mem_eq_finite_toFinset_sum (fun p => pairS0 4 4 A p) hfin]
  -- the part with `λ₁ > A` contributes nothing
  set F : Finset ((Fin 5 → ℤ) × (Fin 5 → ℤ)) :=
    hfin.toFinset.filter (fun p => lam (Gam 4 4 p.1 p.2) 1 ≤ A) with hFdef
  have hsplit : (∑ p ∈ hfin.toFinset, pairS0 4 4 A p) = ∑ p ∈ F, pairS0 4 4 A p := by
    rw [hFdef, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    by_cases h : lam (Gam 4 4 p.1 p.2) 1 ≤ A
    · rw [if_pos h]
    · rw [if_neg h]
      exact pairS0_eq_zero_of_lam_gt (not_le.mp h)
  rw [hsplit]
  -- membership facts for `p ∈ F`
  have hmemS : ∀ p ∈ F, p ∈ SHiSet A B := by
    intro p hp
    rw [hFdef, Finset.mem_filter] at hp
    exact (Set.Finite.mem_toFinset hfin).mp hp.1
  have hlamA : ∀ p ∈ F, lam (Gam 4 4 p.1 p.2) 1 ≤ A := by
    intro p hp
    rw [hFdef, Finset.mem_filter] at hp
    exact hp.2
  -- the per-cell arithmetic hypothesis for `hi_cell_sum`
  have harith : ∀ Δ M : ℝ, A ^ ((1 : ℝ) / 20) ≤ Δ → Δ ≤ 48 * B ^ 2 / A → 1 ≤ M → M ≤ A →
      hiLZ B (2 * Δ) (2 * M) * hiMin A B Δ M
        ≤ Kar * A ^ ((68 : ℝ) - 1 / 32) * B ^ 2 * B ^ (-(1 / 1000 : ℝ)) :=
    fun Δ M h1 h2 h3 h4 => har A B Δ M hBar hAle hAge h1 h2 h3 h4
  -- the counting hypothesis, from the convenient `ℓ^{(1)}` bound
  have hcount : ∀ Δ M : ℝ, 1 ≤ Δ → 1 ≤ M →
      ((F.filter (fun p => dmin 3 ({p.1, p.2} : Set (Fin 5 → ℤ)) ≤ Δ ∧
        lam (Gam 4 4 p.1 p.2) 1 ≤ M)).card : ℝ) ≤ Kl * hiLZ B Δ M := by
    intro Δ M hΔ hM
    set Tset : Set ((Fin 5 → ℤ) × (Fin 5 → ℤ)) :=
      {p | LinearIndependent ℤ ![p.1, p.2] ∧ eNorm p.1 ≤ B ∧ eNorm p.2 ≤ B ∧
        dmin 3 ({p.1, p.2} : Set (Fin 5 → ℤ)) ≤ Δ ∧ lam (Gam 4 4 p.1 p.2) 1 ≤ M} with hTdef
    have hsub : (↑(F.filter (fun p => dmin 3 ({p.1, p.2} : Set (Fin 5 → ℤ)) ≤ Δ ∧
        lam (Gam 4 4 p.1 p.2) 1 ≤ M)) : Set ((Fin 5 → ℤ) × (Fin 5 → ℤ))) ⊆ Tset := by
      intro p hp
      rw [Finset.mem_coe, Finset.mem_filter] at hp
      obtain ⟨hpF, hd3, hl⟩ := hp
      have hpS := hmemS p hpF
      have hBexp1 : (1 : ℝ) / (((4 : ℕ) : ℝ) + 1 - ((4 : ℕ) : ℝ)) = 1 := by norm_num
      have he1 : eNorm p.1 ≤ B := by
        have h := hpS.1.1.2; rwa [hBexp1, Real.rpow_one] at h
      have he2 : eNorm p.2 ≤ B := by
        have h := hpS.1.2.1.2; rwa [hBexp1, Real.rpow_one] at h
      exact ⟨Sig2.li_of_mem_Omega 4 4 B p hpS.1, he1, he2, hd3, hl⟩
    have hfinT : Tset.Finite :=
      ((MDBasic.finite_eNorm_le (ι := Fin 5) B).prod
        (MDBasic.finite_eNorm_le (ι := Fin 5) B)).subset (fun p hp => ⟨hp.2.1, hp.2.2.1⟩)
    have h1 : ((F.filter (fun p => dmin 3 ({p.1, p.2} : Set (Fin 5 → ℤ)) ≤ Δ ∧
        lam (Gam 4 4 p.1 p.2) 1 ≤ M)).card : ℝ) ≤ (Tset.ncard : ℝ) := by
      rw [← Set.ncard_coe_finset]
      exact_mod_cast Set.ncard_le_ncard hsub hfinT
    have h2 : (Tset.ncard : ℝ) = (ell44 1 B Δ M : ℝ) := by
      rw [hTdef]
      rfl
    have h3 := hell B Δ M hB1 hΔ hM
    calc ((F.filter (fun p => dmin 3 ({p.1, p.2} : Set (Fin 5 → ℤ)) ≤ Δ ∧
          lam (Gam 4 4 p.1 p.2) 1 ≤ M)).card : ℝ)
        ≤ (Tset.ncard : ℝ) := h1
      _ = (ell44 1 B Δ M : ℝ) := h2
      _ ≤ Kl * hiLZ B Δ M := by
          refine le_trans h3 (le_of_eq ?_)
          rw [hiLZ]
          ring
  -- the cell-sum bound
  have hcell := hsu A B hBsu hAle hAge Kl Kar hKlpos hKarpos harith F
    (fun p => dmin 3 ({p.1, p.2} : Set (Fin 5 → ℤ)))
    (fun p => lam (Gam 4 4 p.1 p.2) 1)
    (fun p hp => le_of_lt (hmemS p hp).2.2.2)
    (by
      intro p hp
      have hpS := hmemS p hp
      have hLI := Sig2.li_of_mem_Omega 4 4 B p hpS.1
      obtain ⟨hd1, hd2, hd3, hd4⟩ := dmin_facts 4 (by norm_num)
      have hd2pos : 0 < dmin 2 ({p.1, p.2} : Set (Fin 5 → ℤ)) :=
        lt_of_lt_of_le zero_lt_one (hd1 p.1 p.2 hLI)
      have hd3pos : 0 < dmin 3 ({p.1, p.2} : Set (Fin 5 → ℤ)) :=
        lt_of_lt_of_le zero_lt_one (hd3 p.1 p.2 hLI)
      have hd2le : dmin 2 ({p.1, p.2} : Set (Fin 5 → ℤ)) ≤ eNorm p.1 * eNorm p.2 :=
        hd2 p.1 p.2 hLI
      have hlt := Sig2.d3_lt_of_caseI 4 p.1 p.2 A hd2pos hd3pos hd2le hApos
        (lt_of_not_ge hpS.2.1) hpS.2.2.1
      have hBexp1 : (1 : ℝ) / (((4 : ℕ) : ℝ) + 1 - ((4 : ℕ) : ℝ)) = 1 := by norm_num
      have he1 : eNorm p.1 ≤ B := by
        have h := hpS.1.1.2
        rwa [hBexp1, Real.rpow_one] at h
      have he2 : eNorm p.2 ≤ B := by
        have h := hpS.1.2.1.2
        rwa [hBexp1, Real.rpow_one] at h
      have he1n : 0 ≤ eNorm p.1 := eNorm_nonneg _
      have he2n : 0 ≤ eNorm p.2 := eNorm_nonneg _
      have hXY : eNorm p.1 * eNorm p.2 ≤ B ^ 2 := by
        calc eNorm p.1 * eNorm p.2 ≤ B * B := mul_le_mul he1 he2 he2n (le_trans he1n he1)
          _ = B ^ 2 := by ring
      have h48 : (3 : ℝ) * (((4 : ℕ) : ℝ)) ^ 2 = 48 := by norm_num
      rw [h48] at hlt
      calc dmin 3 ({p.1, p.2} : Set (Fin 5 → ℤ)) ≤ 48 * (eNorm p.1 * eNorm p.2) / A := le_of_lt hlt
        _ ≤ 48 * B ^ 2 / A := by
            apply div_le_div_of_nonneg_right _ hApos.le
            exact mul_le_mul_of_nonneg_left hXY (by norm_num))
    (by
      intro p hp
      have hpS := hmemS p hp
      have hnu := Sig2.nu_indep 4 4 (by norm_num) p.1 p.2 hpS.1.1.1 hpS.1.2.1.1
        hpS.1.2.2.1 hpS.1.2.2.2
      obtain ⟨hrk, -⟩ := Sig2.gam_rank_det 4 4 p.1 p.2 hnu
      have h68 : rk (Gam 4 4 p.1 p.2) = 68 := by rw [hrk, NN_four_four_nat]
      exact one_le_lam _ (le_refl 1) (by rw [h68]; norm_num))
    (fun p hp => hlamA p hp)
    hcount
  -- the pointwise bound and the conclusion
  have hpoint : ∀ p ∈ F, pairS0 4 4 A p
      ≤ Kp * hiMin A B (dmin 3 ({p.1, p.2} : Set (Fin 5 → ℤ))) (lam (Gam 4 4 p.1 p.2) 1) := by
    intro p hp
    have hpS := hmemS p hp
    exact hpbound A B hA1 p hpS.1 (lt_of_not_ge hpS.2.1) hpS.2.2.1 (hlamA p hp)
  have hsum : (∑ p ∈ F, pairS0 4 4 A p)
      ≤ Kp * (Ksu * Kl * Kar * A ^ ((68 : ℝ) - 1 / 32) * B ^ 2) := by
    calc (∑ p ∈ F, pairS0 4 4 A p)
        ≤ ∑ p ∈ F, Kp * hiMin A B (dmin 3 ({p.1, p.2} : Set (Fin 5 → ℤ)))
            (lam (Gam 4 4 p.1 p.2) 1) := Finset.sum_le_sum hpoint
      _ = Kp * ∑ p ∈ F, hiMin A B (dmin 3 ({p.1, p.2} : Set (Fin 5 → ℤ)))
            (lam (Gam 4 4 p.1 p.2) 1) := by rw [Finset.mul_sum]
      _ ≤ Kp * (Ksu * Kl * Kar * A ^ ((68 : ℝ) - 1 / 32) * B ^ 2) :=
          mul_le_mul_of_nonneg_left hcell hKppos.le
  refine le_trans hsum ?_
  rw [NN_four_four, show (70 : ℝ) - 2 - (1 : ℝ) / 32 = (68 : ℝ) - 1 / 32 by norm_num]
  exact le_of_eq (by ring)

end Work.HP.MDEstimates
