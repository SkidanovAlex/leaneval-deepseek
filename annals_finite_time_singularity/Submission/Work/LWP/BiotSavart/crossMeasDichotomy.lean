/-
# `Work.LWP.BiotSavart.crossMeasDichotomy`

Two independent cross-product directions `z - ·` and `z' - ·` (with `z ≠ z'`) determine the
vector field `ω` almost everywhere, so if both `y ↦ ω y × (z - y)` and `y ↦ ω y × (z' - y)`
are ae strongly measurable then so is `ω` itself.

## The argument

Put `d = z' - z ≠ 0` and `a(y) = z - y`, and write `f y = WithLp.ofLp (ω y)` for `ω` viewed in
`Fin 3 → ℝ`, where the cross product lives.  Since `ω (z' - y) = ω (z - y) + ω d` (bilinearity
of `×`), the difference of the two hypotheses gives

  `y ↦ f y × d`  and  `y ↦ f y × a(y)`  are ae strongly measurable.

The first gives the component of `f y` orthogonal to `d`; the second yields the scalar
`f y · d` through the elementary identity `crossRecover` (a 2×2 Cramer solve).  Hence, off the
null set `{y | d × a(y) = 0}` (where `d` and `a(y)` are parallel, i.e. `y` lies on the line
through `z, z'` — see `volume_setOf_cross_eq_zero`), the field `f` agrees ae with an explicit
continuous function of the ae strongly measurable data, so it is ae strongly measurable.
-/
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.LWP.Defs
import Submission.Work.LWP.BiotSavart.crossRecover
import Submission.Work.LWP.BiotSavart.volume_setOf_cross_eq_zero

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.LWP.BiotSavart

open MeasureTheory

/-- The cross product of two ae strongly measurable `ℝ³`-valued functions is ae strongly
measurable. -/
theorem aestronglyMeasurable_crossProduct {α : Type*} {m : MeasurableSpace α} {μ : Measure α}
    {g h : α → Fin 3 → ℝ} (hg : AEStronglyMeasurable g μ) (hh : AEStronglyMeasurable h μ) :
    AEStronglyMeasurable (fun y => crossProduct (g y) (h y)) μ := by
  have hgm : ∀ i : Fin 3, AEMeasurable (fun y => (g y) i) μ :=
    fun i => ((continuous_apply i).comp_aestronglyMeasurable hg).aemeasurable
  have hhm : ∀ i : Fin 3, AEMeasurable (fun y => (h y) i) μ :=
    fun i => ((continuous_apply i).comp_aestronglyMeasurable hh).aemeasurable
  rw [aestronglyMeasurable_iff_aemeasurable]
  refine AEMeasurable.of_eval (fun i => ?_)
  fin_cases i <;>
    simp only [cross_apply, Fin.isValue, Fin.reduceFinMk, Matrix.cons_val_zero,
      Matrix.cons_val_one] <;>
    first
      | exact ((hgm 1).mul (hhm 2)).sub ((hgm 2).mul (hhm 1))
      | exact ((hgm 2).mul (hhm 0)).sub ((hgm 0).mul (hhm 2))
      | exact ((hgm 0).mul (hhm 1)).sub ((hgm 1).mul (hhm 0))

/-- The dot product of two ae strongly measurable `ℝ³`-valued functions is ae strongly
measurable. -/
theorem aestronglyMeasurable_dotProduct {α : Type*} {m : MeasurableSpace α} {μ : Measure α}
    {g h : α → Fin 3 → ℝ} (hg : AEStronglyMeasurable g μ) (hh : AEStronglyMeasurable h μ) :
    AEStronglyMeasurable (fun y => g y ⬝ᵥ h y) μ := by
  have hgc : ∀ i : Fin 3, AEStronglyMeasurable (fun y => (g y) i) μ :=
    fun i => (continuous_apply i).comp_aestronglyMeasurable hg
  have hhc : ∀ i : Fin 3, AEStronglyMeasurable (fun y => (h y) i) μ :=
    fun i => (continuous_apply i).comp_aestronglyMeasurable hh
  convert Finset.aestronglyMeasurable_sum (Finset.univ : Finset (Fin 3))
    (fun i _ => (hgc i).mul (hhc i)) using 1
  ext y
  simp only [dotProduct, Finset.sum_apply]
  rfl

theorem crossMeasDichotomy {ω : Work.LWP.R3 → Work.LWP.R3} {z z' : Work.LWP.R3} (hzz' : z ≠ z')
    (h₁ : MeasureTheory.AEStronglyMeasurable (fun y : Work.LWP.R3 => crossProduct (ω y) (z - y)) MeasureTheory.volume)
    (h₂ : MeasureTheory.AEStronglyMeasurable (fun y : Work.LWP.R3 => crossProduct (ω y) (z' - y)) MeasureTheory.volume) :
    MeasureTheory.AEStronglyMeasurable ω MeasureTheory.volume := by
  set f : Work.LWP.R3 → (Fin 3 → ℝ) := fun y => WithLp.ofLp (ω y) with hf
  set a : Work.LWP.R3 → (Fin 3 → ℝ) := fun y => WithLp.ofLp (z - y) with ha
  set D : (Fin 3 → ℝ) := WithLp.ofLp (z' - z) with hD
  have hDne : D ≠ 0 := by
    intro h
    have h1 : WithLp.ofLp (z' - z) = (0 : Fin 3 → ℝ) := hD ▸ h
    have h2 : WithLp.ofLp (z' - z) = WithLp.ofLp (0 : Work.LWP.R3) := by simpa using h1
    have h3 : z' - z = 0 := WithLp.ofLp_injective 2 h2
    exact hzz' (sub_eq_zero.mp h3).symm
  have hkey : ∀ y : Work.LWP.R3, WithLp.ofLp (z' - y) - WithLp.ofLp (z - y) = D := by
    intro y; rw [hD]; simp only [WithLp.ofLp_sub]; abel
  have hP1 : AEStronglyMeasurable (fun y => crossProduct (f y) (a y)) volume := h₁
  have hP2 : AEStronglyMeasurable (fun y => crossProduct (f y) D) volume := by
    have hd21 : AEStronglyMeasurable (fun y =>
        crossProduct (f y) (WithLp.ofLp (z' - y)) - crossProduct (f y) (WithLp.ofLp (z - y))) volume :=
      h₂.sub h₁
    refine hd21.congr ?_
    filter_upwards with y
    rw [← map_sub, hkey y]
  have ha_cont : Continuous a := by
    rw [ha]
    exact (EuclideanSpace.equiv (Fin 3) ℝ).continuous.comp (continuous_const.sub continuous_id)
  have hA_cont : Continuous (fun y : Work.LWP.R3 => D ⬝ᵥ (a y)) :=
    continuous_const.dotProduct ha_cont
  have hAA_cont : Continuous (fun y : Work.LWP.R3 => (a y) ⬝ᵥ (a y)) := ha_cont.dotProduct ha_cont
  have hG1 : AEStronglyMeasurable (fun y => crossProduct (crossProduct (f y) (a y)) D) volume :=
    (LinearMap.continuous_of_finiteDimensional
      (f := (LinearMap.flip crossProduct) D)).comp_aestronglyMeasurable hP1
  have hBf : AEStronglyMeasurable (fun y => (crossProduct (crossProduct (f y) (a y)) D) ⬝ᵥ (a y)) volume :=
    aestronglyMeasurable_dotProduct hG1 ha_cont.aestronglyMeasurable
  have hG2 : AEStronglyMeasurable (fun y => crossProduct (crossProduct (f y) D) (a y)) volume :=
    aestronglyMeasurable_crossProduct hP2 ha_cont.aestronglyMeasurable
  have hCf : AEStronglyMeasurable (fun y => (crossProduct (crossProduct (f y) D) (a y)) ⬝ᵥ D) volume :=
    aestronglyMeasurable_dotProduct hG2 continuous_const.aestronglyMeasurable
  set num : Work.LWP.R3 → ℝ := fun y =>
    ((crossProduct (crossProduct (f y) (a y)) D) ⬝ᵥ (a y)) * (D ⬝ᵥ D)
      + (D ⬝ᵥ (a y)) * ((crossProduct (crossProduct (f y) D) (a y)) ⬝ᵥ D) with hnum
  set den : Work.LWP.R3 → ℝ := fun y =>
    (D ⬝ᵥ D) * ((a y) ⬝ᵥ (a y)) - (D ⬝ᵥ (a y)) * (D ⬝ᵥ (a y)) with hden
  set rhs : Work.LWP.R3 → (Fin 3 → ℝ) := fun y =>
    (D ⬝ᵥ D)⁻¹ • crossProduct D (crossProduct (f y) D)
      + ((num y / den y) * (D ⬝ᵥ D)⁻¹) • D with hrhs
  have hnum_meas : AEStronglyMeasurable num volume := by
    rw [hnum]
    exact (hBf.mul continuous_const.aestronglyMeasurable).add
      (hA_cont.aestronglyMeasurable.mul hCf)
  have hden_meas : AEStronglyMeasurable den volume := by
    rw [hden]
    exact (continuous_const.aestronglyMeasurable.mul hAA_cont.aestronglyMeasurable).sub
      (hA_cont.aestronglyMeasurable.mul hA_cont.aestronglyMeasurable)
  have hcross1 : AEStronglyMeasurable (fun y => crossProduct D (crossProduct (f y) D)) volume :=
    (LinearMap.continuous_of_finiteDimensional (f := crossProduct D)).comp_aestronglyMeasurable hP2
  have hrhs_meas : AEStronglyMeasurable rhs volume := by
    rw [hrhs]
    exact (hcross1.const_smul (D ⬝ᵥ D)⁻¹).add
      (((hnum_meas.div₀ hden_meas).mul continuous_const.aestronglyMeasurable).smul_const D)
  have hgood : ∀ᵐ y ∂volume, crossProduct D (a y) ≠ 0 := by
    rw [ae_iff]
    have hset : {y : Work.LWP.R3 | ¬ (crossProduct D (a y) ≠ 0)} =
        {y : Work.LWP.R3 | crossProduct D (a y) = 0} := by
      ext y; simp
    rw [hset]
    exact volume_setOf_cross_eq_zero (z' - z) z (sub_ne_zero.mpr hzz'.symm)
  have hpt : f =ᵐ[volume] rhs := by
    filter_upwards [hgood] with y hy
    rw [hrhs, hnum, hden]
    exact crossRecover (f y) (a y) D hDne hy
  have hfAESM : AEStronglyMeasurable f volume := hrhs_meas.congr hpt.symm
  have hωeq : ω = fun y => WithLp.toLp 2 (f y) := by
    funext y; rw [hf]
  rw [hωeq]
  exact (EuclideanSpace.equiv (Fin 3) ℝ).symm.continuous.comp_aestronglyMeasurable hfAESM

end Work.LWP.BiotSavart
