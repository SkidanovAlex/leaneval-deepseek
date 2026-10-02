import Mathlib
import Submission.Work.FatouCoord.Setup
import Submission.Work.FatouCoord.Petal.repelling_defs
import Submission.Work.FatouCoord.Estimate.wMap_iterate_deriv_bound
import Submission.Work.FatouCoord.Repelling.second_order_mod

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Lipschitz continuity of the defect `ζ ↦ defect f a w ζ`

The repelling coordinate of a parabolic germ is constructed as the fixed point of a contraction
on the left half-plane `{Re w < -R}` built from the *defect* `defect f a w ζ` of the corrected
ansatz `V₀ w = w + (1 - a) Λ w` (see `Petal/repelling_defs`).  The contraction estimates need
`ζ ↦ defect f a w ζ` to be Lipschitz with constant `O(1/‖w‖²)`, uniformly for `w` in a left
half-plane and `ζ` in the unit disc; this is the content of `defect_lipschitz` below.

The defect is the difference of the two terms

`defect f a w ζ = Φ (w + corr a w + ζ) - (1 - a) (Λ (w+1) - Λ w) - 1`,

where `Φ z = wMap f z - z`; the second and third terms do not involve `ζ`, so the `ζ`-Lipschitz
constant of `defect f a w ·` is that of `Φ` on the set of points `w + corr a w + ζ`.  Since
`‖deriv Φ z‖ = ‖deriv (wMap f) z - 1‖ ≤ Kderiv A' / ‖z‖²` on the region `‖z‖ ≥ 4`, `‖z‖ > 1/r`
(`Estimate.deriv_wMap_bound_aux`) and the points `w + corr a w + ζ` with `w` in a far left
half-plane and `‖ζ‖ ≤ 1` have modulus `≥ ‖w‖/2`, the mean value inequality on the segment
between two such points gives the constant `4 Kderiv A' / ‖w‖²`.

The only asymptotic input is `corr a w = (1 - a) Λ w = O(log ‖w‖)`, so that
`‖corr a w‖ ≤ ‖w‖/4` on a sufficiently far left half-plane; iterating the logarithm is
irrelevant since we may choose the half-plane as far left as we like.
-/

open scoped Topology
open Set Filter Metric Function

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace Work.FatouCoord.Repelling

open Work.FatouCoord

noncomputable section

variable {f h : ℂ → ℂ} {a : ℂ} {r A A' : ℝ} {z w : ℂ}

/-! ## Elementary estimates for the branch of the logarithm -/

/-- `‖log z‖ ≤ |log ‖z‖| + |arg z|`, directly from `log z = log ‖z‖ + (arg z) i`. -/
theorem norm_log_le_abs_log_norm_add_abs_arg (z : ℂ) :
    ‖Complex.log z‖ ≤ |Real.log ‖z‖| + |z.arg| := by
  rw [show Complex.log z = (Real.log ‖z‖ : ℂ) + (z.arg : ℂ) * Complex.I by
    rw [← Complex.re_add_im (Complex.log z), Complex.log_re, Complex.log_im]]
  calc ‖(Real.log ‖z‖ : ℂ) + (z.arg : ℂ) * Complex.I‖
      ≤ ‖(Real.log ‖z‖ : ℂ)‖ + ‖(z.arg : ℂ) * Complex.I‖ := norm_add_le _ _
    _ = |Real.log ‖z‖| + |z.arg| := by simp

/-- The logarithm grows at most like a square root: `|log t| ≤ 2 √t` for `t ≥ 1`. -/
theorem abs_log_le_two_sqrt {t : ℝ} (h1 : 1 ≤ t) : |Real.log t| ≤ 2 * Real.sqrt t := by
  have ht : 0 < t := lt_of_lt_of_le zero_lt_one h1
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  rw [abs_of_nonneg (Real.log_nonneg h1)]
  have hsq : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht.le
  have hlog : Real.log t = 2 * Real.log (Real.sqrt t) := by
    conv_lhs => rw [← hsq]
    rw [Real.log_mul (ne_of_gt hs) (ne_of_gt hs)]
    ring
  rw [hlog]
  have := Real.log_le_sub_one_of_pos hs
  linarith

/-- Size of the branch `Λ w = log (-w) + π i` on a far left half-plane:
`‖Λ w‖ ≤ 2 √‖w‖ + 2π` as soon as `1 ≤ ‖w‖`. -/
theorem norm_Lambda_le (w : ℂ) (h1 : 1 ≤ ‖w‖) :
    ‖Petal.Lambda w‖ ≤ 2 * Real.sqrt ‖w‖ + 2 * Real.pi := by
  have hlogw : ‖Complex.log (-w)‖ ≤ |Real.log ‖-w‖| + |(-w).arg| :=
    norm_log_le_abs_log_norm_add_abs_arg (-w)
  have harg : |(-w).arg| ≤ Real.pi :=
    abs_le.mpr ⟨le_of_lt (Complex.neg_pi_lt_arg _), Complex.arg_le_pi _⟩
  have hne : ‖-w‖ = ‖w‖ := norm_neg w
  have hlog2 : |Real.log ‖w‖| ≤ 2 * Real.sqrt ‖w‖ := abs_log_le_two_sqrt h1
  have h1' : ‖Petal.Lambda w‖ ≤ ‖Complex.log (-w)‖ + Real.pi := by
    rw [show Petal.Lambda w = Complex.log (-w) + (Real.pi : ℂ) * Complex.I from rfl]
    calc ‖Complex.log (-w) + (Real.pi : ℂ) * Complex.I‖
        ≤ ‖Complex.log (-w)‖ + ‖(Real.pi : ℂ) * Complex.I‖ := norm_add_le _ _
      _ = ‖Complex.log (-w)‖ + Real.pi := by
          rw [norm_mul, Complex.norm_I, mul_one]; simp
  have h2 : ‖Complex.log (-w)‖ ≤ 2 * Real.sqrt ‖w‖ + Real.pi := by
    have := hlogw; rw [hne] at this; linarith
  linarith

/-! ## Two elementary lemmas used in the mean value argument -/

/-- Splitting a convex combination of two points that both sit above a common `u`. -/
theorem smul_segment_add_eq (θ : ℝ) (u ζ ζ' : ℂ) :
    (1 - θ) • (u + ζ) + θ • (u + ζ') = u + ((1 - θ) • ζ + θ • ζ') := by
  apply Complex.ext <;>
    simp [Complex.add_re, Complex.add_im, Complex.smul_re, Complex.smul_im] <;> ring

/-- The derivative of `z ↦ f z - z` is `deriv f - 1`. -/
theorem deriv_sub_id {f : ℂ → ℂ} {z : ℂ} (hd : DifferentiableAt ℂ f z) :
    deriv (fun z : ℂ => f z - z) z = deriv f z - 1 := by
  have h2 : HasDerivAt (fun z : ℂ => f z - z) (deriv f z - 1) z :=
    hd.hasDerivAt.sub (hasDerivAt_id z)
  exact h2.deriv

/-! ## The main theorem -/

/-- **The defect is Lipschitz in `ζ`, with constant `O(1/‖w‖²)`.**  For a parabolic germ
`f z = z + z² h z` with `ParabolicBounds f h a r A A'` there are `R > 1/r` and `K ≥ 0` such
that for every `w` in the left half-plane `Re w < -R` the map `ζ ↦ defect f a w ζ` is
`K / ‖w‖²`-Lipschitz on the unit disc.  (One may take `K = 4 Kderiv A'`.) -/
theorem defect_lipschitz {f h : ℂ → ℂ} {a : ℂ} {r A A' : ℝ} (hb : ParabolicBounds f h a r A A') : ∃ R K : ℝ, 0 < R ∧ 1 / r < R ∧ 0 ≤ K ∧ ∀ w ζ ζ' : ℂ, w ∈ Work.FatouCoord.Petal.LeftHalfPlane R → ‖ζ‖ ≤ 1 → ‖ζ'‖ ≤ 1 → ‖Work.FatouCoord.Petal.defect f a w ζ - Work.FatouCoord.Petal.defect f a w ζ'‖ ≤ K / ‖w‖ ^ 2 * ‖ζ - ζ'‖ := by
  -- The level of the half-plane is chosen so that `‖corr a w‖ ≤ ‖w‖/4` and `‖w‖ ≥ 8` there.
  set S : ℝ := 8 * ‖(1 : ℂ) - a‖ + 8 * Real.pi * ‖(1 : ℂ) - a‖ + 1 with hSdef
  set M : ℝ := max (1 / r) (max (2 * (1 / r)) (max 8 (S ^ 2))) with hMdef
  have hM1 : 1 / r ≤ M := by rw [hMdef]; exact le_max_left _ _
  have hM2 : 2 * (1 / r) ≤ M := by
    rw [hMdef]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hM8 : (8 : ℝ) ≤ M := by
    rw [hMdef]
    exact le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)
  have hMS : S ^ 2 ≤ M := by
    rw [hMdef]
    exact le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)
  have hSnn : 0 ≤ S := by rw [hSdef]; positivity
  refine ⟨M + 1, 4 * Estimate.Kderiv A', ?_, ?_, ?_, ?_⟩
  · have h1 : 0 < 1 / r := one_div_pos.mpr hb.hr
    linarith
  · linarith
  · exact mul_nonneg (by norm_num) (Estimate.Kderiv_nonneg hb.hA')
  · intro w ζ ζ' hw hζ hζ'
    have hwre : w.re < -(M + 1) := hw
    have hMpos : 0 < M + 1 := by linarith [one_div_pos.mpr hb.hr]
    have hwn : M + 1 < ‖w‖ := by
      have hwr : w.re < 0 := by linarith
      have h1 : -w.re ≤ ‖w‖ := by
        have := Complex.abs_re_le_norm w
        rwa [abs_of_neg hwr] at this
      linarith
    have hw1 : 1 ≤ ‖w‖ := by linarith
    have hw8 : 8 ≤ ‖w‖ := by linarith
    have hw2r : 1 / r < ‖w‖ / 2 := by linarith
    have hsS : S ≤ Real.sqrt ‖w‖ := by
      rw [← Real.sqrt_sq hSnn]
      exact Real.sqrt_le_sqrt (by linarith)
    -- `corr` is small compared with `w`
    have hcorr : ‖Petal.corr a w‖ ≤ ‖w‖ / 4 := by
      have hL := norm_Lambda_le w hw1
      have hc1nn : 0 ≤ ‖(1 : ℂ) - a‖ := norm_nonneg _
      have hsq : Real.sqrt ‖w‖ * Real.sqrt ‖w‖ = ‖w‖ := Real.mul_self_sqrt (norm_nonneg w)
      have hsnn : 0 ≤ Real.sqrt ‖w‖ := Real.sqrt_nonneg _
      have hs1 : 1 ≤ Real.sqrt ‖w‖ := by
        have h0 : 0 ≤ 8 * ‖(1:ℂ) - a‖ + 8 * Real.pi * ‖(1:ℂ) - a‖ := by positivity
        have hS1 : 1 ≤ S := by rw [hSdef]; linarith
        linarith
      have hmain : ‖(1 : ℂ) - a‖ * (2 * Real.sqrt ‖w‖ + 2 * Real.pi) ≤ ‖w‖ / 4 := by
        have hA : (8 * ‖(1:ℂ) - a‖ + 8 * Real.pi * ‖(1:ℂ) - a‖) * Real.sqrt ‖w‖
            ≤ S * Real.sqrt ‖w‖ := by
          apply mul_le_mul_of_nonneg_right _ hsnn
          rw [hSdef]; linarith
        have hB : S * Real.sqrt ‖w‖ ≤ Real.sqrt ‖w‖ * Real.sqrt ‖w‖ :=
          mul_le_mul_of_nonneg_right hsS hsnn
        have hC : 8 * Real.pi * ‖(1:ℂ) - a‖ ≤ 8 * Real.pi * ‖(1:ℂ) - a‖ * Real.sqrt ‖w‖ := by
          have h0 : 0 ≤ 8 * Real.pi * ‖(1:ℂ) - a‖ := by positivity
          nlinarith [hs1]
        nlinarith [hA, hB, hC, hsq]
      calc ‖Petal.corr a w‖ = ‖(1 : ℂ) - a‖ * ‖Petal.Lambda w‖ := by
            rw [Petal.corr_apply, norm_mul]
        _ ≤ ‖(1 : ℂ) - a‖ * (2 * Real.sqrt ‖w‖ + 2 * Real.pi) :=
            mul_le_mul_of_nonneg_left hL hc1nn
        _ ≤ ‖w‖ / 4 := hmain
    have hwpos : 0 < ‖w‖ := by linarith
    set x : ℂ := w + Petal.corr a w + ζ with hxdef
    set y : ℂ := w + Petal.corr a w + ζ' with hydef
    have hw2 : 4 ≤ ‖w‖ / 2 := by linarith
    -- every point of the segment `[x,y]` is at distance `≥ ‖w‖/2` from the origin
    have hseg : ∀ z ∈ segment ℝ x y, ‖w‖ / 2 ≤ ‖z‖ := by
      intro z hz
      rw [segment_eq_image] at hz
      obtain ⟨θ, hθ, rfl⟩ := hz
      change ‖w‖ / 2 ≤ ‖(1 - θ) • x + θ • y‖
      have hsm : (1 - θ) • x + θ • y = (w + Petal.corr a w) + ((1 - θ) • ζ + θ • ζ') := by
        rw [hxdef, hydef, smul_segment_add_eq]
      rw [hsm]
      have hs1 : ‖(1 - θ) • ζ + θ • ζ'‖ ≤ 1 := by
        have h1 : ‖(1 - θ) • ζ + θ • ζ'‖ ≤ ‖(1 - θ) • ζ‖ + ‖θ • ζ'‖ := norm_add_le _ _
        have h2 : ‖(1 - θ) • ζ‖ = |1 - θ| * ‖ζ‖ := norm_smul _ _
        have h3 : ‖θ • ζ'‖ = |θ| * ‖ζ'‖ := norm_smul _ _
        have h4 : |1 - θ| = 1 - θ := abs_of_nonneg (by linarith [hθ.2])
        have h5 : |θ| = θ := abs_of_nonneg hθ.1
        rw [h2, h3, h4, h5] at h1
        have h6 : 0 ≤ 1 - θ := by linarith [hθ.2]
        have h7 : (1 - θ) * ‖ζ‖ ≤ (1 - θ) * 1 := mul_le_mul_of_nonneg_left hζ h6
        have h8 : θ * ‖ζ'‖ ≤ θ * 1 := mul_le_mul_of_nonneg_left hζ' hθ.1
        linarith
      have h1 : ‖w + Petal.corr a w‖ ≥ ‖w‖ - ‖Petal.corr a w‖ := by
        have h := norm_sub_le (w + Petal.corr a w) (Petal.corr a w)
        have h2 : (w + Petal.corr a w) - Petal.corr a w = w := by ring
        rw [h2] at h
        linarith
      have h3 : ‖(w + Petal.corr a w) + ((1 - θ) • ζ + θ • ζ')‖
          ≥ ‖w + Petal.corr a w‖ - ‖(1 - θ) • ζ + θ • ζ'‖ := by
        have h := norm_sub_le ((w + Petal.corr a w) + ((1 - θ) • ζ + θ • ζ'))
          ((1 - θ) • ζ + θ • ζ')
        have h2 : ((w + Petal.corr a w) + ((1 - θ) • ζ + θ • ζ')) - ((1 - θ) • ζ + θ • ζ')
            = w + Petal.corr a w := by ring
        rw [h2] at h
        linarith
      linarith
    have hdiff : ∀ z ∈ segment ℝ x y, DifferentiableAt ℂ (fun z => wMap f z - z) z := by
      intro z hz
      have hz4 : 4 ≤ ‖z‖ := le_trans hw2 (hseg z hz)
      have hzr : 1 / r < ‖z‖ := lt_of_lt_of_le hw2r (hseg z hz)
      exact (Estimate.differentiableAt_wMap hb hzr hz4).sub differentiableAt_id
    have hbnd : ∀ z ∈ segment ℝ x y,
        ‖deriv (fun z => wMap f z - z) z‖ ≤ 4 * Estimate.Kderiv A' / ‖w‖ ^ 2 := by
      intro z hz
      have hzn : ‖w‖ / 2 ≤ ‖z‖ := hseg z hz
      have hz4 : 4 ≤ ‖z‖ := le_trans hw2 hzn
      have hzr : 1 / r < ‖z‖ := lt_of_lt_of_le hw2r hzn
      have hsub : deriv (fun z => wMap f z - z) z = deriv (wMap f) z - 1 :=
        deriv_sub_id (Estimate.differentiableAt_wMap hb hzr hz4)
      rw [hsub]
      have hb' := Estimate.deriv_wMap_bound_aux hb hzr hz4
      have hK : 0 ≤ Estimate.Kderiv A' := Estimate.Kderiv_nonneg hb.hA'
      have hw2pos : 0 < ‖w‖ / 2 := by linarith
      have hsq2 : (‖w‖ / 2) ^ 2 ≤ ‖z‖ ^ 2 := by nlinarith [hzn]
      calc ‖deriv (wMap f) z - 1‖ ≤ Estimate.Kderiv A' / ‖z‖ ^ 2 := hb'
        _ ≤ Estimate.Kderiv A' / (‖w‖ / 2) ^ 2 :=
              div_le_div_of_nonneg_left hK (by positivity) hsq2
        _ = 4 * Estimate.Kderiv A' / ‖w‖ ^ 2 := by
              rw [div_pow]; field_simp; ring
    -- the mean value inequality on the segment
    have hmvt := Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℂ)
      (f := fun z => wMap f z - z) (s := segment ℝ x y) (x := x) (y := y)
      (C := 4 * Estimate.Kderiv A' / ‖w‖ ^ 2) hdiff hbnd (convex_segment x y)
      (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
    have hdefect : Petal.defect f a w ζ - Petal.defect f a w ζ'
        = (wMap f x - x) - (wMap f y - y) := by
      rw [Petal.defect_apply, Petal.defect_apply, ← hxdef, ← hydef]
      ring
    have hyx : y - x = ζ' - ζ := by rw [hydef, hxdef]; ring
    calc ‖Petal.defect f a w ζ - Petal.defect f a w ζ'‖
        = ‖(wMap f x - x) - (wMap f y - y)‖ := by rw [hdefect]
      _ = ‖(wMap f y - y) - (wMap f x - x)‖ := norm_sub_rev _ _
      _ ≤ (4 * Estimate.Kderiv A' / ‖w‖ ^ 2) * ‖y - x‖ := hmvt
      _ = 4 * Estimate.Kderiv A' / ‖w‖ ^ 2 * ‖ζ - ζ'‖ := by
            rw [hyx, norm_sub_rev]

end

end Work.FatouCoord.Repelling
