import Mathlib
import Submission.Work.PlanarSC.not_hasArg_of_jordan_curve
import Submission.Work.HornSC.CellBoundaryJordan.hasArg_iff_arg_lift
import Submission.Work.HornSC.Tools

/-!
# The bounded component of a Jordan curve is detected by the drift of the argument lift

Let `γ : C(Circle, ℂ)` be an injective curve (a Jordan curve), `a ∉ range γ`, and let
`θ : ℝ → ℂ` be a continuous lift of the logarithm of `t ↦ γ (exp (2π i t)) - a` through `exp`,
whose drift is `m`: `θ (t + 1) = θ t + m · 2πi`.  Then `a` lies in a *bounded* component of the
complement of the curve exactly when the drift `m` is non-zero.

The two ingredients are

* `Commons.Topology.Winding.winding_zero_of_unbounded_component`: the curve does not wind around a
  point of the unbounded component of its complement, so there an argument lift is periodic;
* `Work.PlanarSC.not_hasArg_of_jordan_curve`: the winding number of a Jordan curve about a point of
  its bounded region is non-zero.

Since `HasArgPeriodic F` (an argument lift of the curve about `a`) is what these two facts control,
and by `hasArg_iff_arg_lift` it is equivalent to the periodicity of *any* lift `θ`, i.e. to `m = 0`,
the equivalence follows.
-/

namespace Work.HornSC.CellBoundaryJordan

open Set

open scoped Topology

theorem boundedComponentIn_iff_period_ne_zero {γ : C(Circle, ℂ)} (hγ : Function.Injective γ)
    {a : ℂ} (ha : a ∉ Set.range γ)
    {θ : ℝ → ℂ} (hθc : Continuous θ)
    (hθexp : ∀ t, Complex.exp (θ t) = γ (Circle.exp (2 * Real.pi * t)) - a)
    {m : ℤ} (hθper : ∀ t, θ (t + 1) = θ t + (m : ℂ) * (2 * Real.pi * Complex.I)) :
    Bornology.IsBounded (connectedComponentIn ((Set.range γ)ᶜ) a) ↔ m ≠ 0 := by
  -- `range (γ ∘ exp) = range γ`
  have hrange_f : Set.range (fun t : ℝ => γ (Circle.exp (2 * Real.pi * t))) = Set.range γ := by
    ext z
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨Circle.exp (2 * Real.pi * t), rfl⟩
    · rintro ⟨c, rfl⟩
      obtain ⟨t₀, ht₀⟩ := Circle.exp_surjective c
      refine ⟨t₀ / (2 * Real.pi), ?_⟩
      change γ (Circle.exp (2 * Real.pi * (t₀ / (2 * Real.pi)))) = γ c
      rw [show 2 * Real.pi * (t₀ / (2 * Real.pi)) = t₀ from
            (by rw [← mul_div_assoc, mul_div_cancel_left₀ _
              (ne_of_gt (by positivity : (0:ℝ) < 2 * Real.pi))]), ht₀]
  -- the closed curve `f` and the curve `F = f - a` about which we measure the winding
  set f : ℝ → ℂ := fun t => γ (Circle.exp (2 * Real.pi * t)) with hf
  set F : ℝ → ℂ := fun t => f t - a with hF
  have hfcont : Continuous f := by
    rw [hf]
    exact γ.continuous.comp (Circle.exp.continuous.comp (by fun_prop))
  have hfper : Function.Periodic f 1 := by
    intro t
    simp only [hf]
    have h : Circle.exp (2 * Real.pi * (t + 1)) = Circle.exp (2 * Real.pi * t) := by
      rw [show 2 * Real.pi * (t + 1) = 2 * Real.pi * t + 2 * Real.pi from by ring]
      exact Circle.periodic_exp (2 * Real.pi * t)
    rw [h]
  have hFcont : Continuous F := hfcont.sub continuous_const
  have hFper : ∀ t, F (t + 1) = F t := by
    intro t
    simp only [hF, hfper t]
  have hθexpF : ∀ t, Complex.exp (θ t) = F t := fun t => hθexp t
  have hFnz : ∀ t, F t ≠ 0 := by
    intro t h
    have h1 : Complex.exp (θ t) = 0 := by rw [hθexpF t, h]
    exact Complex.exp_ne_zero (θ t) h1
  -- `HasArgPeriodic F` is `HasArg F 0`
  have hHA : HasArgPeriodic F ↔ Commons.Topology.Winding.HasArg F 0 := by
    constructor
    · rintro ⟨φ, hc, hp, hrep⟩; exact ⟨φ, hc, hp, fun t => by simpa using hrep t⟩
    · rintro ⟨φ, hc, hp, hrep⟩; exact ⟨φ, hc, hp, fun t => by simpa using hrep t⟩
  -- the drift vanishes exactly when the lift is periodic
  have hmzero : HasArgPeriodic F ↔ m = 0 := by
    have hiff := hasArg_iff_arg_lift hFcont hFper hFnz hθc hθexpF
    constructor
    · intro hh
      have hp := hiff.mp hh
      have h2 : ((m : ℂ) * (2 * Real.pi * Complex.I)) = 0 := by
        have h3 : θ 0 + (m : ℂ) * (2 * Real.pi * Complex.I) = θ 0 + 0 := by
          rw [← hθper 0, hp 0, add_zero]
        exact add_left_cancel h3
      have hne : (2 * Real.pi * Complex.I : ℂ) ≠ 0 :=
        mul_ne_zero (mul_ne_zero (by norm_num)
          (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
      have hm0 : (m : ℂ) = 0 := (mul_eq_zero.mp h2).resolve_right hne
      exact_mod_cast hm0
    · intro hm
      refine hiff.mpr ?_
      intro t
      rw [hθper t, hm]
      simp
  constructor
  · -- bounded ⟹ the curve winds about `a`, hence the drift is non-zero
    intro hbdd
    have hnh := Work.PlanarSC.not_hasArg_of_jordan_curve hγ ha hbdd
    intro hm
    exact hnh (hHA.mp (hmzero.mpr hm))
  · -- non-zero drift ⟹ `a` is not in the unbounded component
    intro hm
    by_contra hnb
    have hp : a ∉ Set.range f := by
      rw [hf, hrange_f]; exact ha
    have hunb : ¬ Bornology.IsBounded (connectedComponentIn ((Set.range f)ᶜ) a) := by
      rw [hf, hrange_f]; exact hnb
    obtain ⟨φ, hφc, hφper, hφrep⟩ :=
      Commons.Topology.Winding.winding_zero_of_unbounded_component hfcont hfper hp hunb
    have hha : Commons.Topology.Winding.HasArg F 0 :=
      ⟨φ, hφc, hφper, fun t => by simpa [hF] using hφrep t⟩
    exact hm (hmzero.mp (hHA.mpr hha))

end Work.HornSC.CellBoundaryJordan
