/-
# `PkgK5.InterpTrace.cs_mK` — Cauchy–Schwarz for the weighted cut-off mass integrals

The four `m_k`-type integrals of the interpolation-trace package are

  `∫ z in cA k..cB k, χ k z * w z ^ 2 * G z θ`

(`χ k` the logarithmic cut-off of `Work.EllipticEst.Core.zLogCut`, `w z = (1+z)^2/z^2` the
radial weight).  Here we prove the elementary `L²`-Cauchy–Schwarz inequality that pairs the two
*squares* against the *product*: with the (nonnegative, on the support window) weight
`ρ z = χ k z · w z²`,

  `(∫ ρ ψ ∂_θψ)² ≤ (∫ ρ ψ²)(∫ ρ (∂_θψ)²)`.

The proof has three ingredients:

* `csQuad_aux` — the discriminant form of Cauchy–Schwarz for real numbers,
  `(∀ t, 0 ≤ A + 2Ct + Bt²) → 0 ≤ B → C² ≤ A·B` (the `B = 0` case is separate);
* `continuousOn_w_sq_aux` — `w²` is continuous on `(0,∞)`;
* `cs_interval_weighted_aux` — the weighted interval Cauchy–Schwarz
  `(∫_a^b ρ u v)² ≤ (∫_a^b ρ u²)(∫_a^b ρ v²)` for `ρ ≥ 0` on `(a,b]`, obtained by expanding
  `0 ≤ ∫_a^b ρ (u + t v)² = A + 2Ct + Bt²` and applying the discriminant lemma.

The three integrability hypotheses of the weighted inequality are discharged in the application
`cs_mK` from continuity on the compact window `[cA k, cB k] ⊂ (0,∞)` — the cut-off `χ k` is
`C^∞` on `(0,∞)` (`CutFam.sm`), `w²` is continuous there, and `ψ · θ`, `∂_θψ · θ` are the
`z`-slices of `ψ` resp. `Work.Spaces.pth ψ` at an interior angle `θ ∈ (0,π/2)`
(`SmoothOpen.curry_z`).

Everything here is `sorry`-free.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.EllSol.PkgK5.InterpTraceCore

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set

namespace Work.FTS.EllSol.PkgK5.InterpTrace

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-- **Cauchy–Schwarz, discriminant form.**  If the quadratic `t ↦ A + 2*C*t + B*t^2` is
nonnegative for every real `t` and `B ≥ 0`, then `C^2 ≤ A*B`.  (The degenerate case `B = 0`
is handled separately: a nonnegative *linear* function `t ↦ A + 2Ct` forces `C = 0`.) -/
private theorem csQuad_aux {A B C : ℝ} (h : ∀ t : ℝ, 0 ≤ A + 2 * C * t + B * t ^ 2)
    (hB : 0 ≤ B) : C ^ 2 ≤ A * B := by
  by_cases hB0 : B = 0
  · have hC : C = 0 := by
      by_contra hC0
      have h2C : (2 : ℝ) * C ≠ 0 := mul_ne_zero (by norm_num) hC0
      have hk := h (-(A + 1) / (2 * C))
      have hval : A + 2 * C * (-(A + 1) / (2 * C)) + B * (-(A + 1) / (2 * C)) ^ 2 = -1 := by
        rw [hB0]
        field_simp
        ring
      rw [hval] at hk
      norm_num at hk
    rw [hC, hB0]
    norm_num
  · have hBpos : 0 < B := lt_of_le_of_ne hB (Ne.symm hB0)
    have hkey := h (-(C / B))
    have hval : A + 2 * C * (-(C / B)) + B * (-(C / B)) ^ 2 = A - C ^ 2 / B := by
      field_simp
      ring
    rw [hval] at hkey
    have hle : C ^ 2 / B ≤ A := by linarith
    have heq : C ^ 2 = (C ^ 2 / B) * B := by
      field_simp
    rw [heq]
    exact mul_le_mul_of_nonneg_right hle hB

/-- The radial weight `w z = (1+z)^2/z^2` has a continuous square on `(0,∞)`. -/
private theorem continuousOn_w_sq_aux :
    ContinuousOn (fun z : ℝ => (Work.Spaces.w z) ^ 2) (Set.Ioi 0) := by
  have hw : ContinuousOn (Work.Spaces.w) (Set.Ioi 0) := by
    have h : Work.Spaces.w = fun z : ℝ => (1 + z) ^ 2 / z ^ 2 := rfl
    rw [h]
    exact ((continuousOn_const.add continuousOn_id).pow 2).div (continuousOn_id.pow 2)
      (fun z hz => pow_ne_zero 2 (ne_of_gt hz))
  exact hw.pow 2

/-- **Weighted Cauchy–Schwarz on an interval.**  For `a ≤ b`, a weight `ρ ≥ 0` on `(a,b]` and
`ρ u²`, `ρ v²`, `ρ u v` integrable on `(a,b]`,
`(∫_a^b ρ u v)² ≤ (∫_a^b ρ u²) * (∫_a^b ρ v²)`.

The proof integrates the pointwise identity
`ρ(u + t v)² = ρ u² + 2t·ρ u v + t²·ρ v²`, observes that the result is nonnegative (the weight is
nonnegative on `(a,b]`), and applies the discriminant lemma `csQuad_aux`. -/
private theorem cs_interval_weighted_aux {a b : ℝ} (hab : a ≤ b) {ρ u v : ℝ → ℝ}
    (hρ : ∀ x ∈ Set.Ioc a b, 0 ≤ ρ x)
    (h1 : IntegrableOn (fun x => ρ x * u x ^ 2) (Set.Ioc a b))
    (h2 : IntegrableOn (fun x => ρ x * v x ^ 2) (Set.Ioc a b))
    (h3 : IntegrableOn (fun x => ρ x * u x * v x) (Set.Ioc a b)) :
    (∫ x in a..b, ρ x * u x * v x) ^ 2 ≤
      (∫ x in a..b, ρ x * u x ^ 2) * (∫ x in a..b, ρ x * v x ^ 2) := by
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab,
    intervalIntegral.integral_of_le hab]
  have hB0 : 0 ≤ ∫ x in Set.Ioc a b, ρ x * v x ^ 2 :=
    integral_nonneg_of_ae (ae_restrict_of_forall_mem measurableSet_Ioc
      (fun x hx => mul_nonneg (hρ x hx) (sq_nonneg (v x))))
  refine csQuad_aux ?_ hB0
  intro t
  have hpoly : (∫ x in Set.Ioc a b, ρ x * (u x + t * v x) ^ 2)
      = (∫ x in Set.Ioc a b, ρ x * u x ^ 2)
        + 2 * (∫ x in Set.Ioc a b, ρ x * u x * v x) * t
        + (∫ x in Set.Ioc a b, ρ x * v x ^ 2) * t ^ 2 := by
    have hmid : Integrable (fun x => (2 * t) * (ρ x * u x * v x))
        (volume.restrict (Set.Ioc a b)) := h3.const_mul (2 * t)
    have hlast : Integrable (fun x => t ^ 2 * (ρ x * v x ^ 2))
        (volume.restrict (Set.Ioc a b)) := h2.const_mul (t ^ 2)
    have hsum : Integrable (fun x => ρ x * u x ^ 2 + (2 * t) * (ρ x * u x * v x))
        (volume.restrict (Set.Ioc a b)) := h1.add hmid
    rw [show (fun x => ρ x * (u x + t * v x) ^ 2)
        = (fun x => ρ x * u x ^ 2 + (2 * t) * (ρ x * u x * v x) + t ^ 2 * (ρ x * v x ^ 2))
        from funext (fun x => by ring)]
    rw [integral_add hsum hlast, integral_add h1 hmid, integral_const_mul, integral_const_mul]
    ring
  rw [← hpoly]
  exact integral_nonneg_of_ae (ae_restrict_of_forall_mem measurableSet_Ioc
    (fun x hx => mul_nonneg (hρ x hx) (sq_nonneg (u x + t * v x))))

theorem cs_mK {χ : ℕ → ℝ → ℝ} {K : ℝ} (hχ : Work.FTS.EllSol.PkgK5.CutFam χ K)
    (k : ℕ) {ψ : ℝ → ℝ → ℝ} (hψ : Work.FTS.EllipticEst.SmoothOpen ψ)
    {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    (∫ z in (Work.FTS.EllSol.PkgK5.cA k)..(Work.FTS.EllSol.PkgK5.cB k),
        χ k z * (Work.Spaces.w z) ^ 2 * ψ z θ * Work.Spaces.pth ψ z θ) ^ 2
      ≤ (∫ z in (Work.FTS.EllSol.PkgK5.cA k)..(Work.FTS.EllSol.PkgK5.cB k),
          χ k z * (Work.Spaces.w z) ^ 2 * ψ z θ ^ 2)
        * (∫ z in (Work.FTS.EllSol.PkgK5.cA k)..(Work.FTS.EllSol.PkgK5.cB k),
          χ k z * (Work.Spaces.w z) ^ 2 * (Work.Spaces.pth ψ z θ) ^ 2) := by
  have hab : Work.FTS.EllSol.PkgK5.cA k ≤ Work.FTS.EllSol.PkgK5.cB k :=
    Work.FTS.EllSol.PkgK5.cA_le_cB k
  set s : Set ℝ := Set.uIcc (Work.FTS.EllSol.PkgK5.cA k) (Work.FTS.EllSol.PkgK5.cB k) with hs
  have hsub : s ⊆ Set.Ioi 0 := by
    intro x hx
    rw [hs, Set.uIcc_of_le hab] at hx
    exact lt_of_lt_of_le (Work.FTS.EllSol.PkgK5.cA_pos k) hx.1
  have hχc : ContinuousOn (χ k) s := (hχ.sm k).continuousOn.mono hsub
  have hwc : ContinuousOn (fun x : ℝ => (Work.Spaces.w x) ^ 2) s :=
    continuousOn_w_sq_aux.mono hsub
  have hψc : ContinuousOn (fun x : ℝ => ψ x θ) s := (hψ.curry_z hθ).continuousOn.mono hsub
  have hpc : ContinuousOn (fun x : ℝ => Work.Spaces.pth ψ x θ) s :=
    ((hψ.pth).curry_z hθ).continuousOn.mono hsub
  have key : ∀ f : ℝ → ℝ, ContinuousOn f s →
      IntegrableOn f (Set.Ioc (Work.FTS.EllSol.PkgK5.cA k) (Work.FTS.EllSol.PkgK5.cB k)) :=
    fun f hf => (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hf.intervalIntegrable
  refine cs_interval_weighted_aux hab
    (ρ := fun z => χ k z * (Work.Spaces.w z) ^ 2) (u := fun z => ψ z θ)
    (v := fun z => Work.Spaces.pth ψ z θ) ?_ ?_ ?_ ?_
  · intro x hx
    exact mul_nonneg
      (hχ.bnd k x (lt_trans (Work.FTS.EllSol.PkgK5.cA_pos k) hx.1)).1 (sq_nonneg _)
  · exact key _ ((hχc.mul hwc).mul (hψc.pow 2))
  · exact key _ ((hχc.mul hwc).mul (hpc.pow 2))
  · exact key _ (((hχc.mul hwc).mul hψc).mul hpc)

end Work.FTS.EllSol.PkgK5.InterpTrace
