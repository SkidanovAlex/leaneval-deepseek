import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsLocalPStar

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

set_option linter.unusedVariables false

/-- **The boundary trace is locally integrable.**

We do not need the trace hypothesis `htr` at all: the boundary bound `hbd`, evaluated at the single
interior angle `θ₀ = π/3 ∈ (π/4, π/2)`, already gives

  `|lam z| ≤ |f z θ₀| + c * √(Ibd α f z)`,   `c := √(100/(γ-1) * sin(2θ₀)^{γ-1})`,

for a.e. `z > 0`; and since `SmoothOpen f` makes the slice `z ↦ f z θ₀` continuous on `(0,∞)`,
the first term is bounded by a constant on the compact interval `[a,b]`.  The second term is
integrable by hypothesis `hD`, so `lam` is dominated by an integrable function on `[a,b]`. -/
theorem LamLocInt {α : ℝ} (hα : α ∈ Set.Ioc 0 1) {f : ℝ → ℝ → ℝ} {lam : ℝ → ℝ}
    (hso : Work.FTS.EllipticEst.SmoothOpen f)
    (hlamm : Measurable lam)
    (htr : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
        Filter.Tendsto (fun θ => f z θ) (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)))
          (nhds (lam z)))
    (hbd : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
        ∀ θ ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2),
        (f z θ - lam z) ^ 2 ≤ 100 / (Work.Spaces.gam α - 1) * (Real.sin (2 * θ)) ^ (Work.Spaces.gam α - 1)
          * (∫ σ in Work.Spaces.Iθ,
              (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α) * (Work.Spaces.pth f z σ) ^ 2))
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hD : ∫⁻ u in Set.Icc a b, ENNReal.ofReal (Real.sqrt (∫ σ in Work.Spaces.Iθ,
        (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α) * (Work.Spaces.pth f u σ) ^ 2)) < ⊤) :
    ∫⁻ u in Set.Icc a b, ENNReal.ofReal |lam u| < ⊤ := by
  -- `γ - 1 = α/10 > 0`
  have hgam1 : 0 < Work.Spaces.gam α - 1 := by
    rw [Work.Spaces.gam]; linarith [hα.1]
  -- the interior angle `θ₀ = π/3` at which the boundary bound is evaluated
  set θ₀ : ℝ := Real.pi / 3 with hθ₀def
  have hθ₀ : θ₀ ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2) := by
    rw [hθ₀def]; constructor <;> linarith [Real.pi_pos]
  have hθ₀pos : θ₀ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
    rw [hθ₀def]; constructor <;> linarith [Real.pi_pos]
  have hsinθ₀ : 0 < Real.sin (2 * θ₀) := by
    have h2 : (2 : ℝ) * θ₀ = 2 * Real.pi / 3 := by rw [hθ₀def]; ring
    rw [h2]
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  -- the constant `c` of the boundary bound at `θ₀`
  set c : ℝ := Real.sqrt (100 / (Work.Spaces.gam α - 1)
    * (Real.sin (2 * θ₀)) ^ (Work.Spaces.gam α - 1)) with hcdef
  have hc_nonneg : 0 ≤ c := Real.sqrt_nonneg _
  have hc_sq : c ^ 2 = 100 / (Work.Spaces.gam α - 1)
      * (Real.sin (2 * θ₀)) ^ (Work.Spaces.gam α - 1) :=
    Real.sq_sqrt (mul_nonneg (by positivity) (Real.rpow_nonneg hsinθ₀.le _))
  -- the slice `z ↦ f z θ₀` is continuous on `(0,∞)`, hence bounded on `[a,b]`
  have hcontθ : ContinuousOn (fun u : ℝ => f u θ₀) (Set.Icc a b) :=
    (hso.curry_z hθ₀pos).continuousOn.mono (fun z hz => lt_of_lt_of_le ha hz.1)
  obtain ⟨x₀, -, hx₀max⟩ :=
    isCompact_Icc.exists_isMaxOn (⟨a, le_rfl, hab⟩ : (Set.Icc a b).Nonempty) hcontθ.abs
  have hMnb : 0 ≤ |f x₀ θ₀| := abs_nonneg _
  have hM : ∀ u ∈ Set.Icc a b, |f u θ₀| ≤ |f x₀ θ₀| := fun u hu => hx₀max hu
  -- the boundary bound, restricted to the interval `[a,b]`
  have hsub : Set.Icc a b ⊆ Set.Ioi (0 : ℝ) := fun z hz => lt_of_lt_of_le ha hz.1
  have hbdc : ∀ᵐ z ∂(volume.restrict (Set.Icc a b)),
      ∀ θ ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2),
        (f z θ - lam z) ^ 2 ≤ 100 / (Work.Spaces.gam α - 1)
          * (Real.sin (2 * θ)) ^ (Work.Spaces.gam α - 1)
          * (∫ σ in Work.Spaces.Iθ,
              (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α) * (Work.Spaces.pth f z σ) ^ 2) :=
    ae_restrict_of_ae_restrict_of_subset hsub hbd
  -- the a.e. pointwise domination of `lam` by an integrable function
  have hpoint : ∀ᵐ z ∂(volume.restrict (Set.Icc a b)),
      |lam z| ≤ |f x₀ θ₀| + c * Real.sqrt (∫ σ in Work.Spaces.Iθ,
        (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α) * (Work.Spaces.pth f z σ) ^ 2) := by
    refine (hbdc.and (ae_restrict_of_forall_mem measurableSet_Icc hM)).mono ?_
    rintro z ⟨hbz, hMz⟩
    have hbθ := hbz θ₀ hθ₀
    have hsq : (f z θ₀ - lam z) ^ 2 ≤ c ^ 2 * (∫ σ in Work.Spaces.Iθ,
        (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α) * (Work.Spaces.pth f z σ) ^ 2) := by
      rw [hc_sq]; exact hbθ
    have hsqrt : |f z θ₀ - lam z| ≤ c * Real.sqrt (∫ σ in Work.Spaces.Iθ,
        (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α) * (Work.Spaces.pth f z σ) ^ 2) := by
      have h1 := Real.sqrt_le_sqrt hsq
      rw [Real.sqrt_sq_eq_abs, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs,
        abs_of_nonneg hc_nonneg] at h1
      exact h1
    calc |lam z| = |(lam z - f z θ₀) + f z θ₀| := by rw [sub_add_cancel]
      _ ≤ |lam z - f z θ₀| + |f z θ₀| := abs_add_le _ _
      _ = |f z θ₀ - lam z| + |f z θ₀| := by rw [abs_sub_comm]
      _ ≤ c * Real.sqrt (∫ σ in Work.Spaces.Iθ,
            (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α) * (Work.Spaces.pth f z σ) ^ 2)
          + |f x₀ θ₀| := add_le_add hsqrt hMz
      _ = |f x₀ θ₀| + c * Real.sqrt (∫ σ in Work.Spaces.Iθ,
            (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α) * (Work.Spaces.pth f z σ) ^ 2) := by ring
  -- the dominating function is an (essentially) constant plus a multiple of the `hD`-integrand
  have hsplit : ∀ u : ℝ, ENNReal.ofReal (|f x₀ θ₀| + c * Real.sqrt (∫ σ in Work.Spaces.Iθ,
        (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α) * (Work.Spaces.pth f u σ) ^ 2))
      = ENNReal.ofReal |f x₀ θ₀|
        + ENNReal.ofReal c * ENNReal.ofReal (Real.sqrt (∫ σ in Work.Spaces.Iθ,
            (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α) * (Work.Spaces.pth f u σ) ^ 2)) := by
    intro u
    rw [ENNReal.ofReal_add (abs_nonneg _) (mul_nonneg hc_nonneg (Real.sqrt_nonneg _)),
      ENNReal.ofReal_mul hc_nonneg]
  refine lt_of_le_of_lt (lintegral_mono_ae (hpoint.mono fun z hz => ENNReal.ofReal_le_ofReal hz)) ?_
  rw [lintegral_congr hsplit]
  rw [lintegral_add_left' aemeasurable_const]
  rw [lintegral_const_mul' (ENNReal.ofReal c) _ ENNReal.ofReal_ne_top]
  rw [setLIntegral_const]
  exact ENNReal.add_lt_top.mpr
    ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_Icc_lt_top,
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top hD⟩

end Work.FTS.StrongEps.EpsLocalPStar
