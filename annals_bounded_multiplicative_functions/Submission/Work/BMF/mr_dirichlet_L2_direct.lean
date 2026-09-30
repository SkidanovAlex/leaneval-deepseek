import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.mv_sharp_dirichlet
import Submission.Work.BMF.mr_direct_defs
import Submission.Work.BMF.mr_core_defs
import Submission.Work.BMF.mr_core.main

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `Work.BMF.mr_dirichlet_L2_direct`

Target (Matomäki–Radziwiłł, Prop. 4.1 in the `k = 0` Dirichlet-polynomial form): for `1`-bounded
multiplicative `g` which is `B`-far in `𝔻` from every archimedean twist `n ↦ n^{iu}` on the window
`|u| ≤ C·Y/H`, one has for every `T ≥ Y/H`

`(Y/H)/T · ∫_{|t| ≤ 2T} ‖Σ_{Y ≤ n ≤ 3Y} g n · n^{-(1+it)}‖² ≤ ε`.

## Structure of the file

* `dirPolyD`, `dirPolyD_eq_mv`: the logarithmic Dirichlet polynomial and its rewriting with the
  `1/n` weights, so that the workspace's clean mean value theorem applies.
* `mr_direct_largeT`: the *easy* regime `T ≥ (2C/ε)·Y/H`, where the clean Montgomery–Vaughan /
  mean value bound `mv_sharp_dirichlet` suffices.
* `CoreInput`: the critical regime `Y/H ≤ T ≤ (2C/ε)·Y/H`, which is the genuine
  Matomäki–Radziwiłł content (Buchstab/Ramaré decomposition + Halász + large values).
* `mr_dirichlet_L2_direct`: the target, assembled from the two regimes.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.BMF

open MeasureTheory intervalIntegral
open scoped BigOperators
open BoundedMultiplicativeFunctions

noncomputable section

/-- Norms of the individual terms: `‖a n · n^{-(1+it)}‖ = ‖a n‖ / n` for `n ≥ 1`. -/
lemma norm_dirPolyD_term (a : ℕ → ℂ) {Y t : ℝ} (hY : 1 ≤ Y) {n : ℕ} (hn : n ∈ natIcc Y (3 * Y)) :
    ‖a n * (n : ℂ) ^ (-(1 + Complex.I * t))‖ = ‖a n‖ / (n : ℝ) := by
  have hn1 : 1 ≤ n := by
    rw [natIcc, Finset.mem_Icc] at hn
    exact le_trans (Nat.one_le_ceil_iff.mpr (by linarith)) hn.1
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  rw [norm_mul, Complex.norm_natCast_cpow_of_pos (by omega : 0 < n)]
  have hre : (-(1 + Complex.I * (t : ℂ))).re = -1 := by simp
  rw [hre, Real.rpow_neg_one, div_eq_mul_inv]

/-- Pointwise rewriting: `Σ a n · n^{-(1+it)} = Σ (a n / n) · n^{-it}` for `Y ≥ 1`. -/
lemma dirPolyD_eq_mv (a : ℕ → ℂ) {Y t : ℝ} (hY : 1 ≤ Y) :
    dirPolyD a Y t
      = ∑ n ∈ natIcc Y (3 * Y), (a n / (n : ℂ)) * (n : ℂ) ^ (-(Complex.I * t)) := by
  rw [dirPolyD]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn1 : 1 ≤ n := by
    rw [natIcc, Finset.mem_Icc] at hn
    exact le_trans (Nat.one_le_ceil_iff.mpr (by linarith)) hn.1
  have h0 : (n : ℂ) ≠ 0 := by
    simpa using (Nat.cast_ne_zero.mpr (by omega : n ≠ 0) : ((n : ℝ) : ℂ) ≠ 0)
  rw [show (-(1 + Complex.I * (t : ℂ))) = (-1 : ℂ) + (-(Complex.I * (t : ℂ))) by ring]
  rw [Complex.cpow_add _ _ h0, Complex.cpow_neg_one]
  ring

/-- **The easy regime.**  For `T ≥ (2C/ε)·(Y/H)` (with `H ≥ 2C/ε`) the clean mean value bound for
Dirichlet polynomials gives the required estimate.  `C` is the constant of
`mv_sharp_dirichlet`. -/
theorem mr_direct_largeT (C ε : ℝ) (hC : 0 < C) (hε : 0 < ε)
    (hmv : ∀ (a : ℕ → ℂ), (∀ n, ‖a n‖ ≤ 1 / (n : ℝ)) →
      ∀ (Y T : ℝ), 4 ≤ Y → 1 ≤ T →
        (∫ t in -(2 * T)..(2 * T),
            ‖∑ n ∈ natIcc Y (3 * Y), a n * (n : ℂ) ^ (-(Complex.I * (t : ℂ)))‖ ^ 2)
          ≤ C * (T + Y) / Y)
    (g : ℕ → ℂ) (hg : ∀ n, ‖g n‖ ≤ 1) (Y H T : ℝ)
    (hY : 4 ≤ Y) (hHpos : 0 < H) (hT : 1 ≤ T)
    (hTbig : 2 * C / ε * (Y / H) ≤ T) (hHbig : 2 * C / ε ≤ H) :
    (Y / H) / T * (∫ t in -(2 * T)..(2 * T), ‖dirPolyD g Y t‖ ^ 2) ≤ ε := by
  have hρpos : 0 < Y / H := div_pos (by linarith) hHpos
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  -- apply the mean value theorem to `a n = g n / n`
  have ha : ∀ n, ‖g n / (n : ℂ)‖ ≤ 1 / (n : ℝ) := by
    intro n
    rcases eq_or_ne n 0 with h | h
    · subst h; simp
    · have hnpos : (0 : ℝ) < (n : ℝ) := by positivity
      rw [norm_div, Complex.norm_natCast]
      exact div_le_div_of_nonneg_right (hg n) hnpos.le
  have hmv' := hmv (fun n => g n / (n : ℂ)) ha Y T hY hT
  have hcongr : (∫ t in -(2 * T)..(2 * T), ‖dirPolyD g Y t‖ ^ 2)
      = ∫ t in -(2 * T)..(2 * T),
          ‖∑ n ∈ natIcc Y (3 * Y), (g n / (n : ℂ)) * (n : ℂ) ^ (-(Complex.I * (t : ℂ)))‖ ^ 2 := by
    refine intervalIntegral.integral_congr fun t _ => ?_
    rw [dirPolyD_eq_mv g (by linarith : (1:ℝ) ≤ Y)]
  -- `(Y/H)/T · C(T+Y)/Y = C(Y/(HT) + 1/H)`
  have hkey : (Y / H) / T * (C * (T + Y) / Y) = C * (Y / (H * T) + 1 / H) := by
    field_simp
    ring
  have h1 : Y / (H * T) ≤ ε / (2 * C) := by
    have hYT : Y / H ≤ T * (ε / (2 * C)) := by
      have h := mul_le_mul_of_nonneg_right hTbig (show (0 : ℝ) ≤ ε / (2 * C) by positivity)
      rwa [show 2 * C / ε * (Y / H) * (ε / (2 * C)) = Y / H by field_simp] at h
    have hYT' : Y / (H * T) = (Y / H) / T := by field_simp
    rw [hYT', div_le_iff₀ hTpos]
    linarith
  have h2 : 1 / H ≤ ε / (2 * C) := by
    have h := mul_le_mul_of_nonneg_right hHbig (show (0 : ℝ) ≤ ε / (2 * C) by positivity)
    rw [show 2 * C / ε * (ε / (2 * C)) = 1 by field_simp] at h
    rw [div_le_iff₀ hHpos]
    simpa [mul_comm] using h
  have hsum : Y / (H * T) + 1 / H ≤ ε / (2 * C) + ε / (2 * C) := add_le_add h1 h2
  calc (Y / H) / T * (∫ t in -(2 * T)..(2 * T), ‖dirPolyD g Y t‖ ^ 2)
      = (Y / H) / T * (∫ t in -(2 * T)..(2 * T),
          ‖∑ n ∈ natIcc Y (3 * Y), (g n / (n : ℂ)) * (n : ℂ) ^ (-(Complex.I * (t : ℂ)))‖ ^ 2) := by
        rw [hcongr]
    _ ≤ (Y / H) / T * (C * (T + Y) / Y) := mul_le_mul_of_nonneg_left hmv' (by positivity)
    _ = C * (Y / (H * T) + 1 / H) := hkey
    _ ≤ C * (ε / (2 * C) + ε / (2 * C)) := mul_le_mul_of_nonneg_left hsum hC.le
    _ = ε := by field_simp; ring

end

end Work.BMF

namespace Work.BMF

open MeasureTheory intervalIntegral
open scoped BigOperators
open BoundedMultiplicativeFunctions

noncomputable section

/-- **Assembly.**  `CoreInput θ C₀` plus the clean mean value theorem for Dirichlet polynomials
(`mv_sharp_dirichlet`, used for `T ≥ (2C₀/ε)·Y/H`) give the full target. -/
theorem mr_dirichlet_L2_direct_of_core (θ C₀ : ℝ) (hθ₀ : 0 < θ) (hθ₁ : θ < 1)
    (hC₀pos : 0 < C₀)
    (hmv : ∀ (a : ℕ → ℂ), (∀ n, ‖a n‖ ≤ 1 / (n : ℝ)) →
      ∀ (Y T : ℝ), 4 ≤ Y → 1 ≤ T →
        (∫ t in -(2 * T)..(2 * T),
            ‖∑ n ∈ natIcc Y (3 * Y), a n * (n : ℂ) ^ (-(Complex.I * (t : ℂ)))‖ ^ 2)
          ≤ C₀ * (T + Y) / Y)
    (hcore : CoreInput θ C₀) :
    ∀ ε : ℝ, 0 < ε → ∃ B C X₀ : ℝ, 0 < B ∧ 0 < C ∧ 1 ≤ X₀ ∧
      ∀ (g : ℕ → ℂ), g 1 = 1 →
      (∀ m n : ℕ, m.Coprime n → g (m * n) = g m * g n) → (∀ n, ‖g n‖ ≤ 1) →
      ∀ (Y H : ℝ), X₀ ≤ Y → Y ^ θ ≤ H → H ≤ Y →
      (∀ u : ℝ, |u| ≤ C * Y / H →
        B ≤ BoundedMultiplicativeFunctions.𝔻 g (fun n ↦ (n : ℂ) ^ (Complex.I * u)) Y) →
      ∀ T : ℝ, Y / H ≤ T →
        (Y / H) / T * (∫ t in -(2 * T)..(2 * T), ‖dirPolyD g Y t‖ ^ 2) ≤ ε := by
  intro ε hε
  obtain ⟨B₁, C₁, X₁, hB₁, hC₁, hX₁, hcore'⟩ := hcore ε hε
  set a : ℝ := 2 * C₀ / ε + 1 with hadef
  have ha1 : 1 ≤ a := by
    rw [hadef]
    have h : 0 < 2 * C₀ / ε := by positivity
    linarith
  refine ⟨B₁, max C₁ 1, max X₁ (max 4 (a ^ (1 / θ) + 1)), hB₁,
    lt_of_lt_of_le one_pos (le_max_right _ _), ?_, ?_⟩
  · exact le_trans hX₁ (le_max_left _ _)
  intro g hg1 hgmul hgb Y H hY hYθ hHY hhyp T hρ
  have hX1 : X₁ ≤ Y := le_trans (le_max_left _ _) hY
  have h4 : 4 ≤ Y := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hY
  have hXbig : a ^ (1 / θ) + 1 ≤ Y := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hY
  have hYpos : 0 < Y := by linarith
  have hY1 : 1 ≤ Y := by linarith
  have hH1 : 1 ≤ H := le_trans (Real.one_le_rpow hY1 (le_of_lt hθ₀)) hYθ
  have hHpos : 0 < H := lt_of_lt_of_le zero_lt_one hH1
  have hρ1 : 1 ≤ Y / H := (one_le_div hHpos).mpr hHY
  have hρpos : 0 < Y / H := lt_of_lt_of_le zero_lt_one hρ1
  have hYbig : a ^ (1 / θ) ≤ Y := by linarith
  have hexpθ : a ≤ (a ^ (1 / θ)) ^ θ := by
    rw [← Real.rpow_mul (by positivity : (0 : ℝ) ≤ a), one_div,
      inv_mul_cancel₀ (ne_of_gt hθ₀), Real.rpow_one]
  have hstep : (a ^ (1 / θ)) ^ θ ≤ Y ^ θ :=
    Real.rpow_le_rpow (by positivity) hYbig (le_of_lt hθ₀)
  have hHbig : a ≤ H := le_trans (le_trans hexpθ hstep) hYθ
  have hHbig' : 2 * C₀ / ε ≤ H := by rw [hadef] at hHbig; linarith
  by_cases hT : T < 2 * C₀ / ε * (Y / H)
  · have hhyp' : ∀ u : ℝ, |u| ≤ C₁ * Y / H →
        B₁ ≤ BoundedMultiplicativeFunctions.𝔻 g (fun n ↦ (n : ℂ) ^ (Complex.I * u)) Y := by
      intro u hu
      refine hhyp u (le_trans hu ?_)
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left _ _) hYpos.le) hHpos.le
    have h1 := hcore' g hg1 hgmul hgb Y H T hX1 hYθ hHY hhyp' hρ hT.le
    linarith
  · push_neg at hT
    have h2 := mr_direct_largeT C₀ ε hC₀pos hε hmv g hgb Y H T h4 hHpos (le_trans hρ1 hρ) hT hHbig'
    simpa only [dirPolyD] using h2

end

end Work.BMF

namespace Work.BMF

open MeasureTheory intervalIntegral
open scoped BigOperators
open BoundedMultiplicativeFunctions

noncomputable section

/-- **Target.**  The Matomäki–Radziwiłł `k = 0` bound in the Dirichlet-polynomial form. -/
theorem mr_dirichlet_L2_direct (θ : ℝ) (hθ₀ : 0 < θ) (hθ₁ : θ < 1) :
    ∀ ε : ℝ, 0 < ε → ∃ B C X₀ : ℝ, 0 < B ∧ 0 < C ∧ 1 ≤ X₀ ∧
      ∀ (g : ℕ → ℂ), g 1 = 1 →
      (∀ m n : ℕ, m.Coprime n → g (m * n) = g m * g n) → (∀ n, ‖g n‖ ≤ 1) →
      ∀ (Y H : ℝ), X₀ ≤ Y → Y ^ θ ≤ H → H ≤ Y →
      (∀ u : ℝ, |u| ≤ C * Y / H →
        B ≤ BoundedMultiplicativeFunctions.𝔻 g (fun n ↦ (n : ℂ) ^ (Complex.I * u)) Y) →
      ∀ T : ℝ, Y / H ≤ T →
        (Y / H) / T * (∫ t in -(2 * T)..(2 * T),
          ‖∑ n ∈ Work.BMF.natIcc Y (3 * Y),
            g n * (n : ℂ) ^ (-(1 + Complex.I * t))‖ ^ 2) ≤ ε := by
  obtain ⟨C₀, hC₀pos, hmv⟩ := mv_sharp_dirichlet
  exact mr_dirichlet_L2_direct_of_core θ C₀ hθ₀ hθ₁ hC₀pos hmv
    (coreInput θ C₀ hC₀pos hθ₀ hθ₁)

end

end Work.BMF
