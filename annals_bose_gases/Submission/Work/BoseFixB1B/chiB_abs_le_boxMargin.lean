import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Submission.Work.BoseFixB1B.boxMarginDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1B.chiB_abs_le_boxMargin`

The window `χ_{B(u)} = chiB ℓ d u` vanishes at the boundary of the sliding box `B(u) = dlBox ℓ d u`
**at least linearly in the margin** `boxMargin ℓ d u`.  This is the estimate (F1) of
`boxMarginDefs.lean`, needed to compare the windowed slit function of the smooth approximants
`Ψ_δ` with that of the sharp fibre.

The proof is a two-step argument:

* `abs_chi_le_lin_margin` — `chi` (the corpus bump of `Submission.CubicChi`, supported in the
  closed ball of radius `1/2` and smooth) is Lipschitz, hence vanishes at least linearly in the
  distance to the boundary of its support ball.  The Lipschitz constant comes from
  `ContDiff.lipschitzWith_of_hasCompactSupport`; the linear bound itself is the elementary
  radial estimate `abs_le_lin_margin_of_lipschitz`.
* the box margin: on `dlBox ℓ d u` both the coordinate margins
  `A = ⨅_i (ℓ/2 - |x_i|)`, `B = ⨅_i (ℓd/2 - |(x - ℓd u)_i|)` are nonnegative and
  `A ≥ ℓ/2 - ‖x‖`, `B ≥ ℓd/2 - ‖x - ℓd u‖`, so `min A B` dominates
  `max 0 (ℓ/2 - ‖x‖)` resp. `max 0 (ℓd/2 - ‖x - ℓd u‖)`; a case split on `min` and the
  elementary combination lemma `abs_mul_le_of_margin_bounds` finish.
-/

noncomputable section

open scoped Topology ContDiff
open MeasureTheory Metric

namespace Work.BoseFixB1B

open Submission.BoseGases

set_option autoImplicit false

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-! ## The vanishing rate of `chi` at the boundary of its support -/

/-- `chi` vanishes on the closed exterior of the ball of radius `1/2` (its support ball). -/
lemma chi_eq_zero_of_half_le_norm (y : ℝ³) (h : 1 / 2 ≤ ‖y‖) : chi y = 0 := by
  have hb : chiBase y = 0 := by
    apply ContDiffBump.zero_of_le_dist
    simpa [chiBump, dist_eq_norm] using h
  simp [chi, hb]

/-- A Lipschitz function vanishing outside the ball of radius `1/2` decays at least linearly in
the distance to the boundary of that ball. -/
lemma abs_le_lin_margin_of_lipschitz {f : ℝ³ → ℝ}
    (hsupp : ∀ y : ℝ³, 1 / 2 ≤ ‖y‖ → f y = 0)
    (hLip : ∃ C : ℝ, 0 ≤ C ∧ ∀ a b : ℝ³, |f a - f b| ≤ C * ‖a - b‖) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ y : ℝ³, |f y| ≤ K * max 0 (1 / 2 - ‖y‖) := by
  obtain ⟨C, hC0, hC⟩ := hLip
  refine ⟨C, hC0, fun y => ?_⟩
  rcases le_total ‖y‖ (1 / 2 : ℝ) with h | h
  · rcases eq_or_lt_of_le (norm_nonneg y) with h0 | h0
    · -- `y = 0`: use any point of the sphere of radius `1/2`.
      rw [norm_eq_zero.mp h0.symm, norm_zero, sub_zero,
        max_eq_right (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      obtain ⟨z, hz⟩ : (Metric.sphere (0 : ℝ³) (1 / 2)).Nonempty := by
        rw [NormedSpace.sphere_nonempty]
        norm_num
      have hzn : ‖z‖ = 1 / 2 := by simpa [Metric.mem_sphere, dist_eq_norm] using hz
      have hvan : f z = 0 := hsupp z (le_of_eq hzn.symm)
      have h := hC 0 z
      rw [hvan, sub_zero, zero_sub, norm_neg, hzn] at h
      exact h
    · -- `0 < ‖y‖ ≤ 1/2`: project radially onto the sphere of radius `1/2`.
      have h2y : (0 : ℝ) < 2 * ‖y‖ := by linarith
      have h2ne : 2 * ‖y‖ ≠ 0 := ne_of_gt h2y
      have hmul : (2 * ‖y‖)⁻¹ * ‖y‖ = 1 / 2 := by
        calc (2 * ‖y‖)⁻¹ * ‖y‖ = (2 * ‖y‖)⁻¹ * (2 * ‖y‖) * (2 : ℝ)⁻¹ := by ring
          _ = (2 : ℝ)⁻¹ := by rw [inv_mul_cancel₀ h2ne, one_mul]
          _ = 1 / 2 := by norm_num
      have hzn : ‖(2 * ‖y‖)⁻¹ • y‖ = 1 / 2 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr h2y), hmul]
      have hvan : f ((2 * ‖y‖)⁻¹ • y) = 0 := hsupp _ (le_of_eq hzn.symm)
      have hge : (1 : ℝ) ≤ (2 * ‖y‖)⁻¹ := (one_le_inv₀ h2y).mpr (by linarith)
      have habs : |1 - (2 * ‖y‖)⁻¹| = (2 * ‖y‖)⁻¹ - 1 := by
        rw [abs_of_nonpos (by linarith : 1 - (2 * ‖y‖)⁻¹ ≤ 0)]
        ring
      have hsub : (1 - (2 * ‖y‖)⁻¹) • y = y - (2 * ‖y‖)⁻¹ • y := by
        rw [sub_smul, one_smul]
      have hdist : ‖y - (2 * ‖y‖)⁻¹ • y‖ = 1 / 2 - ‖y‖ := by
        rw [← hsub, norm_smul, Real.norm_eq_abs, habs, sub_mul, one_mul, hmul]
      have hle : |f y| ≤ C * (1 / 2 - ‖y‖) := by
        have h := hC y ((2 * ‖y‖)⁻¹ • y)
        rw [hvan, sub_zero, hdist] at h
        exact h
      rw [max_eq_right (by linarith : (0 : ℝ) ≤ 1 / 2 - ‖y‖)]
      exact hle
  · rw [hsupp y h, abs_zero, max_eq_left (by linarith : 1 / 2 - ‖y‖ ≤ 0), mul_zero]

/-- The corpus bump `chi` is Lipschitz (it is `C^∞` with compact support). -/
lemma exists_lipschitz_chi :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a b : ℝ³, |chi a - chi b| ≤ C * ‖a - b‖ := by
  obtain ⟨C, hC⟩ := ContDiff.lipschitzWith_of_hasCompactSupport chi_hasCompactSupport
    chi_contDiff (by simp : (∞ : WithTop ℕ∞) ≠ 0)
  refine ⟨(C : ℝ), C.coe_nonneg, fun a b => ?_⟩
  have h := hC.dist_le_mul a b
  rw [Real.dist_eq, dist_eq_norm] at h
  exact h

/-- **The linear margin bound for `chi`**: `chi` decays at least linearly in the distance to the
boundary of its support ball. -/
lemma abs_chi_le_lin_margin :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ y : ℝ³, |chi y| ≤ K * max 0 (1 / 2 - ‖y‖) :=
  abs_le_lin_margin_of_lipschitz chi_eq_zero_of_half_le_norm exists_lipschitz_chi

/-- Scaled form of `abs_chi_le_lin_margin`: `chiScale s x = chi (s⁻¹ • x)`. -/
lemma abs_chiScale_le_lin_margin {K : ℝ}
    (hK : ∀ y : ℝ³, |chi y| ≤ K * max 0 (1 / 2 - ‖y‖)) {s : ℝ} (hs : 0 < s) (x : ℝ³) :
    |chiScale s x| ≤ K * max 0 (1 / 2 - ‖x‖ / s) := by
  have h := hK (s⁻¹ • x)
  rw [chiScale]
  simpa [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hs, inv_mul_eq_div] using h

/-! ## Elementary auxiliary inequalities -/

/-- `max 0 a ≤ b` when `a ≤ b` and `b ≥ 0`. -/
lemma max_zero_le_of_le {a b : ℝ} (hb : 0 ≤ b) (h : a ≤ b) : max 0 a ≤ b := by
  rcases le_total a 0 with h' | h'
  · rw [max_eq_left h']; exact hb
  · rw [max_eq_right h']; exact h

/-- The abstract two-margin combination: if `|f|` is bounded both by `c₁·A` and by `S`, and `|g|`
both by `S` and by `c₂·B`, then `|f|·|g| ≤ S·(c₁+c₂)·min A B`. -/
lemma abs_mul_le_of_margin_bounds {f g A B c₁ c₂ S : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (hS : 0 ≤ S)
    (hf₁ : |f| ≤ c₁ * A) (hg₁ : |g| ≤ S) (hf₂ : |f| ≤ S) (hg₂ : |g| ≤ c₂ * B) :
    |f| * |g| ≤ S * (c₁ + c₂) * min A B := by
  rcases le_total A B with h | h
  · rw [min_eq_left h]
    calc |f| * |g| ≤ (c₁ * A) * S :=
          mul_le_mul hf₁ hg₁ (abs_nonneg g) (mul_nonneg hc₁ hA)
      _ ≤ S * (c₁ + c₂) * A := by nlinarith [mul_nonneg (mul_nonneg hS hc₂) hA]
  · rw [min_eq_right h]
    calc |f| * |g| ≤ S * (c₂ * B) :=
          mul_le_mul hf₂ hg₂ (abs_nonneg g) hS
      _ ≤ S * (c₁ + c₂) * B := by nlinarith [mul_nonneg (mul_nonneg hS hc₁) hB]

/-! ## The main estimate -/

theorem chiB_abs_le_boxMargin {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (u : EuclideanSpace ℝ (Fin 3)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : EuclideanSpace ℝ (Fin 3), x ∈ Submission.BoseGases.dlBox ℓ d u →
      |Submission.BoseGases.chiB ℓ d u x| ≤ C * Work.BoseFixB1B.boxMargin ℓ d u x := by
  obtain ⟨K, hK0, hK⟩ := abs_chi_le_lin_margin
  refine ⟨(Real.sqrt chiNormSq)⁻¹ * (K / ℓ + K / (ℓ * d)), ?_, ?_⟩
  · exact mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))
      (add_nonneg (div_nonneg hK0 (le_of_lt hℓ)) (div_nonneg hK0 (le_of_lt (mul_pos hℓ hd))))
  · intro x hx
    have hbm : boxMargin ℓ d u x
        = min (Finset.univ.inf' Finset.univ_nonempty (fun i : Fin 3 => ℓ / 2 - |x i|))
            (Finset.univ.inf' Finset.univ_nonempty
              (fun i : Fin 3 => ℓ * d / 2 - |(x - (ℓ * d) • u) i|)) := rfl
    rw [hbm]
    set z : ℝ³ := x - (ℓ * d) • u with hzdef
    set A : ℝ := Finset.univ.inf' Finset.univ_nonempty (fun i : Fin 3 => ℓ / 2 - |x i|) with hAdef
    set B : ℝ := Finset.univ.inf' Finset.univ_nonempty
      (fun i : Fin 3 => ℓ * d / 2 - |z i|) with hBdef
    have h0 : 0 ≤ min A B := by rw [← hbm]; exact boxMargin_nonneg_iff.mpr hx
    have hA0 : 0 ≤ A := le_trans h0 (min_le_left A B)
    have hB0 : 0 ≤ B := le_trans h0 (min_le_right A B)
    have hA : ℓ / 2 - ‖x‖ ≤ A := by
      rw [hAdef]
      refine Finset.le_inf' Finset.univ_nonempty (fun i : Fin 3 => ℓ / 2 - |x i|) (fun i _ => ?_)
      have hi : |x i| ≤ ‖x‖ := by
        have h := PiLp.norm_apply_le x i
        simpa [Real.norm_eq_abs] using h
      linarith
    have hB : ℓ * d / 2 - ‖z‖ ≤ B := by
      rw [hBdef]
      refine Finset.le_inf' Finset.univ_nonempty (fun i : Fin 3 => ℓ * d / 2 - |z i|)
        (fun i _ => ?_)
      have hi : |z i| ≤ ‖z‖ := by
        have h := PiLp.norm_apply_le z i
        simpa [Real.norm_eq_abs] using h
      linarith
    -- the two factors of `chiB`, each linearly controlled by its own margin
    have hmulA : max 0 (1 / 2 - ‖x‖ / ℓ) * ℓ ≤ A := by
      have hsplit : max 0 (1 / 2 - ‖x‖ / ℓ) * ℓ = max 0 (ℓ / 2 - ‖x‖) := by
        rw [max_mul_of_nonneg _ _ (le_of_lt hℓ), zero_mul]
        congr 1
        rw [sub_mul, div_mul_cancel₀ _ (ne_of_gt hℓ)]
        ring
      rw [hsplit]
      exact max_zero_le_of_le hA0 hA
    have hmulB : max 0 (1 / 2 - ‖z‖ / (ℓ * d)) * (ℓ * d) ≤ B := by
      have hld : (0 : ℝ) < ℓ * d := mul_pos hℓ hd
      have hsplit : max 0 (1 / 2 - ‖z‖ / (ℓ * d)) * (ℓ * d) = max 0 (ℓ * d / 2 - ‖z‖) := by
        rw [max_mul_of_nonneg _ _ (le_of_lt hld), zero_mul]
        congr 1
        rw [sub_mul, div_mul_cancel₀ _ (ne_of_gt hld)]
        ring
      rw [hsplit]
      exact max_zero_le_of_le hB0 hB
    have hF1 : |chiScale ℓ x| ≤ (K / ℓ) * A := by
      have h1 : |chiScale ℓ x| ≤ K * max 0 (1 / 2 - ‖x‖ / ℓ) :=
        abs_chiScale_le_lin_margin hK hℓ x
      calc |chiScale ℓ x| ≤ K * max 0 (1 / 2 - ‖x‖ / ℓ) := h1
        _ ≤ K * A / ℓ := by
            rw [le_div_iff₀ hℓ]
            calc K * max 0 (1 / 2 - ‖x‖ / ℓ) * ℓ = K * (max 0 (1 / 2 - ‖x‖ / ℓ) * ℓ) := by
                  ring
              _ ≤ K * A := mul_le_mul_of_nonneg_left hmulA hK0
        _ = (K / ℓ) * A := by ring
    have hF2 : |chiScale (ℓ * d) z| ≤ (K / (ℓ * d)) * B := by
      have hld : (0 : ℝ) < ℓ * d := mul_pos hℓ hd
      have h1 : |chiScale (ℓ * d) z| ≤ K * max 0 (1 / 2 - ‖z‖ / (ℓ * d)) :=
        abs_chiScale_le_lin_margin hK hld z
      calc |chiScale (ℓ * d) z| ≤ K * max 0 (1 / 2 - ‖z‖ / (ℓ * d)) := h1
        _ ≤ K * B / (ℓ * d) := by
            rw [le_div_iff₀ hld]
            calc K * max 0 (1 / 2 - ‖z‖ / (ℓ * d)) * (ℓ * d)
                = K * (max 0 (1 / 2 - ‖z‖ / (ℓ * d)) * (ℓ * d)) := by ring
              _ ≤ K * B := mul_le_mul_of_nonneg_left hmulB hK0
        _ = (K / (ℓ * d)) * B := by ring
    have hS0 : 0 ≤ (Real.sqrt chiNormSq)⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
    have hF1sup : |chiScale ℓ x| ≤ (Real.sqrt chiNormSq)⁻¹ := abs_chiScale_le ℓ x
    have hF2sup : |chiScale (ℓ * d) z| ≤ (Real.sqrt chiNormSq)⁻¹ := abs_chiScale_le (ℓ * d) z
    have hfin := abs_mul_le_of_margin_bounds (f := chiScale ℓ x) (g := chiScale (ℓ * d) z)
      (A := A) (B := B) (c₁ := K / ℓ) (c₂ := K / (ℓ * d))
      (S := (Real.sqrt chiNormSq)⁻¹) hA0 hB0
      (div_nonneg hK0 (le_of_lt hℓ)) (div_nonneg hK0 (le_of_lt (mul_pos hℓ hd))) hS0
      hF1 hF2sup hF1sup hF2
    rw [chiB, abs_mul]
    exact hfin

end Work.BoseFixB1B
