import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Submission.Work.BoseRowsL.LatticeCoulomb.KernelDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseRowsL.LatticeCoulomb.reductionDefs`

Vocabulary for `Work.BoseRowsL.LatticeCoulomb.reduction_core`.

The lattice-Coulomb comparison pairs a **finite lattice sum** against a **ball integral** of the
same cos-cosine kernel `cos⟪k,x⟫cos⟪k,y⟫/(2‖k‖²)`.  Splitting the two variables of the "kernel"
in this way is what makes the comparison an *operator-norm* statement: the difference of the two
sides is `∫∫ f₁ x f₂ y K(x,y)` with `K(x,y) = cosCosSum x y − ℓ³(2π)⁻³ cosCosBall x y`, and
`K(x,y) = ½(kcal (x+y) + kcal (x−y))` (`kernel2_eq_half_kcal'`), so a sup bound on `kcal` on the
ball of radius `2r` bounds the whole difference by `M‖f₁‖₁‖f₂‖₁` for supported `fᵢ`.

* `cosCosSum T ℓ x y` — the lattice side `Σ_{n∈T} cos⟪k_n,x⟫cos⟪k_n,y⟫/(2‖k_n‖²)`,
  `k_n = ℓ⁻¹ • vec n`;
* `cosCosBall K x y` — the continuum side `∫_{p ∈ closedBall 0 K} cos⟪p,x⟫cos⟪p,y⟫/(2‖p‖²)`;
* `kernel2 T ℓ K x y` — their matched difference, the kernel of the target's left-hand side.
-/

noncomputable section

open MeasureTheory Metric
open scoped Real BigOperators Topology

namespace Work.BoseRowsL.LatticeCoulomb

set_option autoImplicit false

/-- The **lattice side** of the cos-cosine kernel:
`Σ_{n∈T} cos⟪ℓ⁻¹•vec n, x⟫·cos⟪ℓ⁻¹•vec n, y⟫ / (2‖ℓ⁻¹•vec n‖²)`.

The `n = 0` summand is `0` (`cos 0 · cos 0 / 0 = 0` in Lean's junk-value convention), which is
exactly what makes the `n = 0` term of the target's sum harmless. -/
noncomputable def cosCosSum (T : Finset (Fin 3 → ℤ)) (ℓ : ℝ) (x y : E3) : ℝ :=
  ∑ n ∈ T, Real.cos (inner ℝ (ℓ⁻¹ • Work.BoseB4.vec n) x)
      * Real.cos (inner ℝ (ℓ⁻¹ • Work.BoseB4.vec n) y) / (2 * ‖ℓ⁻¹ • Work.BoseB4.vec n‖ ^ 2)

/-- The **continuum side** of the cos-cosine kernel:
`∫_{p ∈ closedBall 0 K} cos⟪p,x⟫·cos⟪p,y⟫ / (2‖p‖²) dp`. -/
noncomputable def cosCosBall (K : ℝ) (x y : E3) : ℝ :=
  ∫ p in Metric.closedBall 0 K, Real.cos (inner ℝ p x) * Real.cos (inner ℝ p y) / (2 * ‖p‖ ^ 2)

/-- The **matched-difference kernel** of the target:
`kernel2 x y = (lattice side) − ℓ³(2π)⁻³ · (continuum side)`. -/
noncomputable def kernel2 (T : Finset (Fin 3 → ℤ)) (ℓ K : ℝ) (x y : E3) : ℝ :=
  cosCosSum T ℓ x y - ℓ ^ 3 * ((2 * Real.pi) ^ 3)⁻¹ * cosCosBall K x y

/-- `p ↦ (2‖p‖²)⁻¹` is integrable on any ball (`3 > 2`: the borderline case of the
3-dimensional radial power test).  This is the finiteness that makes the continuum side
`cosCosBall K x y` a genuine (non-junk) integral. -/
theorem integrableOn_inv_norm_sq (K : ℝ) :
    MeasureTheory.IntegrableOn (fun p : E3 => (2 * ‖p‖ ^ 2)⁻¹) (Metric.closedBall 0 K) := by
  set f : E3 → ℝ := fun p => (2 * ‖p‖ ^ 2)⁻¹ with hf
  have hmeas : AEStronglyMeasurable f (volume : Measure E3) := by
    rw [hf]
    exact (Measurable.inv (by fun_prop : Measurable (fun p : E3 => 2 * ‖p‖ ^ 2))).aestronglyMeasurable
  have hdecay : ∀ᵐ x ∂(volume : Measure E3).restrict (ball 0 (K + 1)),
      ‖f x‖ ≤ (1 : ℝ) * ‖x‖ ^ (-(2 : ℝ)) := by
    filter_upwards with x
    simp only [hf, Real.norm_eq_abs, one_mul]
    rcases eq_or_ne x 0 with hx | hx
    · subst hx
      simp [Real.zero_rpow (by norm_num : (-(2 : ℝ)) ≠ 0)]
    · have hpos : (0 : ℝ) < ‖x‖ ^ 2 := by positivity
      have h2 : (0 : ℝ) < 2 * ‖x‖ ^ 2 := by positivity
      rw [abs_of_pos (inv_pos.mpr h2), Real.rpow_neg (norm_nonneg x), Real.rpow_two]
      exact inv_anti₀ hpos (by linarith [sq_nonneg ‖x‖])
  have hball : IntegrableOn f (ball 0 (K + 1)) (volume : Measure E3) :=
    MeasureTheory.integrableOn_ball_of_norm_le_rpow (μ := (volume : Measure E3))
      (Module.finrank_pos (R := ℝ) (M := E3)) (C := 1) (α := 2) (r := K + 1)
      (by rw [finrank_euclideanSpace_fin]; norm_num) hdecay hmeas
  exact hball.mono_set (fun x hx => by
    rw [mem_ball_zero_iff]
    have h := mem_closedBall_zero_iff.mp hx
    linarith)

end Work.BoseRowsL.LatticeCoulomb
