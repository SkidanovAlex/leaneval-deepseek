import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Submission.Work.FTS.StrongEps.E5Aux2.MuHGlue

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E5Aux2.PT

open MeasureTheory Set Filter
open scoped Real Topology

/-!
# Convergence of the angular `L₁₂`-density of `F_* + wₙ`

The density of the model operator is the angular integral

`L12dens f x = ∫_θ K(θ) f(x,θ) / x`   (`θ` over `Iθ = [0,π/2]`),

with `K(θ) = 3 sin θ cos²θ`.  Here `f = F_* + wₙ`, where `F_* = Construction.Fstar α` is the
fixed profile — whose angular slice `θ ↦ F_*(x,θ)` is *continuous on the closed* interval
`Iθ` because the exponent `α/3` of `Γ(θ) = (sin θ cos²θ)^{α/3}` is positive — and `wₙ` is a
sequence dominated by the constant `C` on the open quadrant, converging pointwise there.

Since the complement of the open quadrant inside `Iθ` is the two-point null set
`{0,π/2}`, the pointwise convergence and the domination hold a.e.; the dominating function
`θ ↦ |K θ| (|F_*(x,θ)| + C)/x` is continuous on the compact `Iθ` (as `x ≠ 0`), hence
integrable, and the dominated convergence theorem gives the density limit at every `x > 0`.

Axioms: `[propext, Classical.choice, Quot.sound]`.
-/

/-- **Convergence of the `L₁₂`-density of `F_* + wₙ`.**  If the profiles `wₙ` are uniformly
bounded on the open quadrant `Qd = (0,∞) × (0,π/2)` and converge pointwise there to `W`, then
at every `x > 0` the angular densities of `F_* + wₙ` converge to that of `F_* + W`, by
dominated convergence in `θ` (the angular slices `θ ↦ wₙ x θ` being a.e.-strongly
measurable). -/
theorem L12densFstar_tendsto {α C : ℝ} (hα : α ∈ Set.Ioc 0 1) {w : ℕ → ℝ → ℝ → ℝ} {W : ℝ → ℝ → ℝ}
    (hbd : ∀ (n : ℕ) (z θ : ℝ), (z, θ) ∈ Work.Construction.Qd → |w n z θ| ≤ C)
    (hconv : ∀ (z θ : ℝ), (z, θ) ∈ Work.Construction.Qd →
      Filter.Tendsto (fun n : ℕ => w n z θ) Filter.atTop (nhds (W z θ)))
    {x : ℝ} (hx : 0 < x)
    (hmeas : ∀ n : ℕ, MeasureTheory.AEStronglyMeasurable (fun θ => w n x θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :
    Filter.Tendsto (fun n : ℕ => Work.Construction.L12dens
        (fun z θ => Work.Construction.Fstar α z θ + w n z θ) x) Filter.atTop
      (nhds (Work.Construction.L12dens (fun z θ => Work.Construction.Fstar α z θ + W z θ) x)) := by
  have hαpos : 0 < α := hα.1
  have hα3 : (0 : ℝ) ≤ α / 3 := div_nonneg hαpos.le (by norm_num)
  -- The angular slice of the reference profile `F_*` is continuous on the *closed* interval.
  have hGam : ContinuousOn (fun θ : ℝ => Work.Spaces.Gam α θ) Work.Spaces.Iθ := by
    have hbase : ContinuousOn (fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2) Work.Spaces.Iθ := by
      fun_prop
    exact hbase.rpow_const (fun _ _ => Or.inr hα3)
  have hcontF : ContinuousOn (fun θ : ℝ => Work.Construction.Fstar α x θ) Work.Spaces.Iθ := by
    simp only [Work.Construction.Fstar]
    exact (continuousOn_const.mul (hGam.div_const (Work.Spaces.c α))).mul continuousOn_const
  have hKcont : Continuous (fun θ : ℝ => Work.Spaces.K θ) := by
    unfold Work.Spaces.K
    fun_prop
  -- A.e. the angle lies in the open interval, where the hypotheses on `w` apply.
  have haeθ : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
    rw [MeasureTheory.ae_restrict_iff' (s := Work.Spaces.Iθ) measurableSet_Icc]
    filter_upwards [MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := (0 : ℝ))
      (b := Real.pi / 2)] with θ h
    exact fun hmem => h.mpr hmem
  -- Measurability of the integrand, from the a.e.-measurability of the slice of `wₙ`.
  have hmeas' : ∀ n : ℕ, MeasureTheory.AEStronglyMeasurable
      (fun θ : ℝ => Work.Spaces.K θ * (Work.Construction.Fstar α x θ + w n x θ) / x)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    intro n
    have hKae : MeasureTheory.AEStronglyMeasurable (fun θ : ℝ => Work.Spaces.K θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      hKcont.aestronglyMeasurable.mono_measure MeasureTheory.Measure.restrict_le_self
    have hFae : MeasureTheory.AEStronglyMeasurable
        (fun θ : ℝ => Work.Construction.Fstar α x θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      hcontF.aestronglyMeasurable measurableSet_Icc
    have hsum : MeasureTheory.AEStronglyMeasurable
        (fun θ : ℝ => Work.Construction.Fstar α x θ + w n x θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := hFae.add (hmeas n)
    have h1 : MeasureTheory.AEStronglyMeasurable
        (fun θ : ℝ => Work.Spaces.K θ * (Work.Construction.Fstar α x θ + w n x θ) * x⁻¹)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      (hKae.mul hsum).mul_const x⁻¹
    simpa only [div_eq_mul_inv] using h1
  -- Integrability of the dominating function: continuous on the compact `Iθ`.
  have hboundcont : ContinuousOn
      (fun θ : ℝ => |Work.Spaces.K θ| * (|Work.Construction.Fstar α x θ| + C) / x)
      Work.Spaces.Iθ :=
    ((hKcont.continuousOn.abs).mul ((hcontF.abs).add continuousOn_const)).div_const x
  have hboundInt : MeasureTheory.Integrable
      (fun θ : ℝ => |Work.Spaces.K θ| * (|Work.Construction.Fstar α x θ| + C) / x)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    ContinuousOn.integrableOn_compact isCompact_Icc hboundcont
  -- The domination, a.e. in `θ`.
  have hbound : ∀ n : ℕ, ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      ‖Work.Spaces.K θ * (Work.Construction.Fstar α x θ + w n x θ) / x‖
        ≤ |Work.Spaces.K θ| * (|Work.Construction.Fstar α x θ| + C) / x := by
    intro n
    filter_upwards [haeθ] with θ hθ
    have hw : |w n x θ| ≤ C := hbd n x θ ⟨hx, hθ⟩
    have h1 : |Work.Construction.Fstar α x θ + w n x θ|
        ≤ |Work.Construction.Fstar α x θ| + C :=
      le_trans (abs_add_le _ _) (add_le_add le_rfl hw)
    rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos hx]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h1 (abs_nonneg _)) hx.le
  -- The pointwise convergence, a.e. in `θ`.
  have hlim : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      Filter.Tendsto
        (fun n : ℕ => Work.Spaces.K θ * (Work.Construction.Fstar α x θ + w n x θ) / x)
        Filter.atTop
        (nhds (Work.Spaces.K θ * (Work.Construction.Fstar α x θ + W x θ) / x)) := by
    filter_upwards [haeθ] with θ hθ
    have h2 : Filter.Tendsto (fun n : ℕ => Work.Construction.Fstar α x θ + w n x θ)
        Filter.atTop (nhds (Work.Construction.Fstar α x θ + W x θ)) :=
      tendsto_const_nhds.add (hconv x θ ⟨hx, hθ⟩)
    have h3 := h2.div_const x
    have h4 : Filter.Tendsto
        (fun n : ℕ => Work.Spaces.K θ * ((Work.Construction.Fstar α x θ + w n x θ) / x))
        Filter.atTop
        (nhds (Work.Spaces.K θ * ((Work.Construction.Fstar α x θ + W x θ) / x))) :=
      tendsto_const_nhds.mul h3
    simpa only [mul_div_assoc] using h4
  have hmain := MeasureTheory.tendsto_integral_of_dominated_convergence
    (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
    (F := fun (n : ℕ) (θ : ℝ) =>
      Work.Spaces.K θ * (Work.Construction.Fstar α x θ + w n x θ) / x)
    (f := fun θ : ℝ => Work.Spaces.K θ * (Work.Construction.Fstar α x θ + W x θ) / x)
    (fun θ : ℝ => |Work.Spaces.K θ| * (|Work.Construction.Fstar α x θ| + C) / x)
    hmeas' hboundInt hbound hlim
  simpa only [Work.Construction.L12dens, Work.FM.L12dens, Work.Spaces.Iθ] using hmain

end Work.FTS.StrongEps.E5Aux2.PT
