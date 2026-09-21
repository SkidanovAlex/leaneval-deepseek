import Mathlib
import Submission.Commons.Geometry.Ulam.even_profile_perturbation_from_smooth_bump

namespace Commons.Geometry.Ulam



open Filter Set
open scoped Topology ContDiff Pointwise RealInnerProductSpace

set_option autoImplicit false

private lemma exists_smooth_bump_for_target (τ : ℝ) (hτ0 : 0 < τ) (hτsmall : 2 * τ < 1) :
    ∃ c δ : ℝ, ∃ h : ℝ → ℝ,
      0 < c ∧ c < 1 ∧ 0 < δ ∧ 2 * δ < c ∧
      Function.support h ⊆ Set.Icc (c - 2 * δ) (c - δ) ∧
      Function.support h ⊆ Set.Icc (1 - 2 * τ) (1 - τ) ∧
      (∃ s : ℝ, 0 < s ∧ h s ≠ 0) ∧
      ContDiffOn ℝ (⊤ : ℕ∞) h Set.univ ∧
      ∃ η : ℝ, 0 < η ∧ ∀ s : ℝ, c - 2 * δ ≤ s → s < c - 2 * δ + η → h s = 0 := by
  let A : ℝ := 1 - 2 * τ
  let B : ℝ := 1 - τ
  let δ : ℝ := τ / 10
  let c : ℝ := 1 - (3 / 2) * τ
  let a : ℝ := c - 2 * δ
  let b : ℝ := c - δ
  let a1 : ℝ := a + (b - a) / 3
  let b1 : ℝ := b - (b - a) / 3
  let mid : ℝ := a + (b - a) / 2
  have hδ0 : 0 < δ := by dsimp [δ]; positivity
  have hc0 : 0 < c := by
    dsimp [c]
    nlinarith [hτsmall]
  have hc1 : c < 1 := by
    dsimp [c]
    nlinarith
  have h2δc : 2 * δ < c := by
    dsimp [δ, c]
    nlinarith [hτsmall]
  have hba : 0 < b - a := by
    dsimp [a, b, c, δ]
    nlinarith
  have hmid_in : mid ∈ Set.Ioo a1 b1 := by
    dsimp [mid, a1, b1, a, b, c, δ]
    constructor <;> nlinarith
  have hmid_pos : 0 < mid := by
    dsimp [mid, a, b, c, δ]
    nlinarith [hτsmall]
  have hIoo : Set.Ioo a1 b1 ∈ 𝓝 mid := by
    exact Ioo_mem_nhds hmid_in.1 hmid_in.2
  obtain ⟨h, htsupp, _hcomp, hdiff, _hrng, hx⟩ :=
    exists_contDiff_tsupport_subset (E := ℝ) (s := Set.Ioo a1 b1) (x := mid) (n := ⊤) hIoo
  have hsupp_c : Function.support h ⊆ Set.Icc a b := by
    intro s hs
    have hs_ts : s ∈ tsupport h := subset_tsupport h hs
    have hs_ioo : s ∈ Set.Ioo a1 b1 := htsupp hs_ts
    have hs1 : a1 < s := hs_ioo.1
    have hs2 : s < b1 := hs_ioo.2
    have hle1 : a ≤ s := by
      dsimp [a, a1, b, c, δ] at hs1 ⊢
      nlinarith
    have hle2 : s ≤ b := by
      dsimp [b, b1, a, c, δ] at hs2 ⊢
      nlinarith
    exact ⟨hle1, hle2⟩
  have hsupp_target : Function.support h ⊆ Set.Icc A B := by
    intro s hs
    have hs_c : s ∈ Set.Icc a b := hsupp_c hs
    have hsc1 : (1 - 3 / 2 * τ - 2 * (τ / 10)) ≤ s := hs_c.1
    have hsc2 : s ≤ 1 - 3 / 2 * τ - τ / 10 := hs_c.2
    have hle1 : A ≤ s := by
      dsimp [A]
      nlinarith
    have hle2 : s ≤ B := by
      dsimp [B]
      nlinarith
    exact ⟨hle1, hle2⟩
  refine ⟨c, δ, h, hc0, hc1, hδ0, h2δc, ?_, hsupp_target, ?_, ?_, ?_⟩
  · simpa [a, b] using hsupp_c
  · refine ⟨mid, hmid_pos, ?_⟩
    rw [hx]
    norm_num
  · have hdiff_on : ContDiffOn ℝ (⊤ : ℕ∞) h Set.univ := by
      exact hdiff.contDiffOn
    exact hdiff_on
  · refine ⟨(b - a) / 3, ?_, ?_⟩
    · exact div_pos hba (by norm_num)
    · intro s hs_left hs_right
      have hs_lt_a1 : s < a1 := by
        dsimp [a1, a, b]
        nlinarith
      have hs_not_support : s ∉ Function.support h := by
        intro hs_supp
        have hs_ts : s ∈ tsupport h := subset_tsupport h hs_supp
        have hs_ioo : s ∈ Set.Ioo a1 b1 := htsupp hs_ts
        exact not_lt_of_gt hs_ioo.1 hs_lt_a1
      simpa [Function.mem_support] using hs_not_support

lemma even_profile_perturbation_strict_of_tau_core_heavy_core (n : ℕ) (hn : 2 ≤ n) (τ : ℝ)
    (hτ0 : 0 < τ) (hτsmall : 2 * τ < 1) :
    ∃ h x y f : ℝ → ℝ,
      Function.support h ⊆ Set.Icc (1 - 2 * τ) (1 - τ) ∧
      (∃ s : ℝ, 0 < s ∧ h s ≠ 0) ∧
      ContDiffOn ℝ (⊤ : ℕ∞) h Set.univ ∧
      Function.support f ⊆ Set.Icc (-1 : ℝ) 1 ∧
      ContDiffOn ℝ (⊤ : ℕ∞) f (Set.Ioo (-1 : ℝ) 1) ∧
      StrictConcaveOn ℝ (Set.Icc (-1 : ℝ) 1) f ∧
      ContinuousOn f (Set.Icc (-1 : ℝ) 1) ∧
      f (-1) = 0 ∧ f 1 = 0 ∧
      (∀ t ∈ Set.Ioo (-1 : ℝ) 1, 0 < f t) ∧
      (∀ s : ℝ, 0 < s →
        0 < x s ∧ 0 < y s ∧
        (f (y s)) ^ 2 = (s * y s + h s) ^ 2 ∧
        (f (-x s)) ^ 2 = (s * (-x s) + h s) ^ 2) ∧
      (∃ t ∈ Set.Icc (-1 : ℝ) 1, f t ≠ f (-t)) ∧
      (∀ s : ℝ, 0 < s →
        (∫ t in (-x s)..(y s), (f t ^ 2 - (s * t + h s) ^ 2) ^ n) =
          (∫ t in (-(1 / Real.sqrt (1 + s ^ 2)))..(1 / Real.sqrt (1 + s ^ 2)),
            ((1 - t ^ 2) - (s * t) ^ 2) ^ n)) ∧
      (∀ s : ℝ, 0 < s →
        (∫ t in (-x s)..(y s), (f t ^ 2 - (s * t + h s) ^ 2) ^ (n - 1) * (t + deriv h s)) = 0) := by
  rcases exists_smooth_bump_for_target τ hτ0 hτsmall with
    ⟨c, δ, hbump, hc0, hc1, hδ0, hδsmall, hsupp_c, hsupp_target, hbump_ne, hbump_cont, hbump_flat⟩
  rcases even_profile_perturbation_from_smooth_bump n hn hc0 hc1 hδ0 hδsmall
    hbump hbump_cont hsupp_c hbump_ne hbump_flat with
    ⟨ε, hε0, x, y, f, hfsupp, hfcont, hfstrict, hfcontOn, hfl, hfr, hfpos, hxy,
      hnoteven, hI, hJ⟩
  let h : ℝ → ℝ := ε • hbump
  refine ⟨h, x, y, f, ?_, ?_, ?_, hfsupp, hfcont, hfstrict, hfcontOn, hfl, hfr,
    hfpos, ?_, hnoteven, ?_, ?_⟩
  · intro s hs
    have hs_prod : ε * hbump s ≠ 0 := by
      simpa [h, Function.mem_support, Pi.smul_apply, smul_eq_mul] using hs
    have hb_ne : hbump s ≠ 0 := by
      intro hb0
      apply hs_prod
      simp [hb0]
    exact hsupp_target (by simpa [Function.mem_support] using hb_ne)
  · rcases hbump_ne with ⟨s, hs0, hsne⟩
    refine ⟨s, hs0, ?_⟩
    dsimp [h]
    intro hzero
    have hprod : ε * hbump s = 0 := by
      simpa [Pi.smul_apply, smul_eq_mul] using hzero
    have hb0 : hbump s = 0 := by
      rcases mul_eq_zero.mp hprod with hε | hb
      · exact False.elim (ne_of_gt hε0 hε)
      · exact hb
    exact hsne hb0
  · dsimp [h]
    exact hbump_cont.const_smul ε
  · intro s hs
    have hxy_s := hxy s hs
    dsimp [h] at hxy_s ⊢
    exact hxy_s
  · intro s hs
    have hI_s := hI s hs
    dsimp [h] at hI_s ⊢
    exact hI_s
  · intro s hs
    have hJ_s := hJ s hs
    dsimp [h] at hJ_s ⊢
    exact hJ_s

end Commons.Geometry.Ulam


