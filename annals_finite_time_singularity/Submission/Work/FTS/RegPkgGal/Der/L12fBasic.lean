/-
# `Work.FTS.RegPkgGal.Der.L12fBasic` — the elementary inputs of `jet_L12f`

This module collects the small analytic facts on which the proof of
`Work.FTS.RegPkgGal.Der.jet_L12f` (and the two auxiliary density lemmas
`L12fDensBound`, `L12fDensDiff`, `L12fDensContInt`) rests:

* `continuousOn_of_holder` — a Hölder modulus on a set gives continuity there (this is the
  only way the `Jet` data of the route produces the continuity hypotheses of dominated
  convergence);
* the pointwise bounds `0 ≤ K θ` and `K θ ≤ 3` for `θ ∈ Iθ` (`K θ = 3 sin θ cos²θ`);
* `L12dens_div` — the angular density of `L₁₂` as a divided integral;
* `setIntegral_abs_le_of_bound` — a pointwise bound on `Iθ` gives the angular `L¹` bound
  with mass `π/2`.

The first and the last are the analytic content of the (parked) module
`Work.FTS.RegPkgGal.R5.L12_transport_bound`, whose proofs are reproduced here so that the
`regPkg`-side lemmas can use them.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FM.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.Regularity.Defs
import Submission.Work.Coercivity.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.RegPkgGal.Der

set_option autoImplicit false

/-- **Hölder implies continuous.**  A function on `ℝ` with the modulus `N·|Δθ|^α` on a set `s`
(`N ≥ 0`, `α > 0`) is continuous on `s`. -/
theorem continuousOn_of_holder {f : ℝ → ℝ} {s : Set ℝ} {N α : ℝ} (hN : 0 ≤ N) (hα : 0 < α)
    (h : ∀ θ ∈ s, ∀ θ' ∈ s, |f θ - f θ'| ≤ N * |θ - θ'| ^ α) : ContinuousOn f s := by
  have hM : (0 : ℝ) < N + 1 := by linarith
  rw [Metric.continuousOn_iff]
  intro b hb ε hε
  have hpos : 0 < (ε / (N + 1)) ^ (1 / α) := Real.rpow_pos_of_pos (div_pos hε hM) _
  refine ⟨min 1 ((ε / (N + 1)) ^ (1 / α)), lt_min one_pos hpos, fun a ha hdist => ?_⟩
  have hab : |a - b| ≤ (ε / (N + 1)) ^ (1 / α) := by
    rw [Real.dist_eq] at hdist
    exact le_of_lt (lt_of_lt_of_le hdist (min_le_right _ _))
  have hpow : |a - b| ^ α ≤ ε / (N + 1) := by
    calc |a - b| ^ α ≤ ((ε / (N + 1)) ^ (1 / α)) ^ α :=
          Real.rpow_le_rpow (abs_nonneg _) hab hα.le
      _ = ε / (N + 1) := by
          rw [← Real.rpow_mul (le_of_lt (div_pos hε hM)),
            one_div_mul_cancel (ne_of_gt hα), Real.rpow_one]
  have key : |f a - f b| ≤ N * (ε / (N + 1)) :=
    le_trans (h a ha b hb) (mul_le_mul_of_nonneg_left hpow hN)
  have key2 : N * (ε / (N + 1)) < ε := by
    have hlt : N / (N + 1) < 1 := by
      rw [div_lt_one hM]; linarith
    calc N * (ε / (N + 1)) = (N / (N + 1)) * ε := by ring
      _ < 1 * ε := mul_lt_mul_of_pos_right hlt hε
      _ = ε := one_mul ε
  rw [Real.dist_eq]
  exact lt_of_le_of_lt key key2

/-- `K θ = 3 sin θ cos²θ ≥ 0` on `Iθ`. -/
theorem K_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Work.Spaces.K θ := by
  have hs : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
  simp only [Work.Spaces.K]
  positivity

/-- `K θ = 3 sin θ cos²θ ≤ 3` on `Iθ`. -/
theorem K_le_three_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : Work.Spaces.K θ ≤ 3 := by
  have hs : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
  have hs1 : Real.sin θ ≤ 1 := Real.sin_le_one θ
  have hc : Real.cos θ ^ 2 ≤ 1 := Real.cos_sq_le_one θ
  have hc0 : 0 ≤ Real.cos θ ^ 2 := sq_nonneg _
  simp only [Work.Spaces.K]
  nlinarith [mul_nonneg hs hc0]

/-- `|K θ| ≤ 3` on `Iθ`. -/
theorem abs_K_le_three {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : |Work.Spaces.K θ| ≤ 3 := by
  rw [abs_of_nonneg (K_nonneg_of_mem_Iθ hθ)]
  exact K_le_three_of_mem_Iθ hθ

/-- The angular density of `L₁₂` as a single divided integral. -/
theorem L12dens_div {f : ℝ → ℝ → ℝ} {s : ℝ} (hs : s ≠ 0) :
    Work.FM.L12dens Work.Spaces.K f s
      = (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * f s θ) / s := by
  rw [Work.FM.L12dens_eq hs]
  simp only [Work.Spaces.Iθ]

/-- **The angular `L¹` bound.**  A pointwise bound on `Iθ` bounds the angular integral, the total
angular mass being `π/2`. -/
theorem setIntegral_abs_le_of_bound {f : ℝ → ℝ} {c : ℝ}
    (h : ∀ θ ∈ Work.Spaces.Iθ, |f θ| ≤ c) :
    ∫ θ in Work.Spaces.Iθ, |f θ| ≤ c * (Real.pi / 2) := by
  have hInt : MeasureTheory.IntegrableOn (fun _ : ℝ => c) Work.Spaces.Iθ :=
    MeasureTheory.integrableOn_const (ne_of_lt Work.Spaces.volume_Iθ_lt_top)
  have hmono := MeasureTheory.integral_mono_of_nonneg
    (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
    (Filter.Eventually.of_forall fun θ => abs_nonneg _) hInt
    (by filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
        exact h θ hθ)
  have hconst : (∫ θ in Work.Spaces.Iθ, (fun _ : ℝ => c) θ) = c * (Real.pi / 2) := by
    rw [MeasureTheory.setIntegral_const, Work.Spaces.volume_real_Iθ, smul_eq_mul]
    ring
  exact le_trans hmono (le_of_eq hconst)

/-- The operator `L₁₂` of the fundamental model as a tail integral of its angular density. -/
theorem L12f_eq_tail (f : ℝ → ℝ → ℝ) (z : ℝ) :
    Work.Coercivity.L12f f z = ∫ s in Ioi z, Work.FM.L12dens Work.Spaces.K f s := rfl

end Work.FTS.RegPkgGal.Der
