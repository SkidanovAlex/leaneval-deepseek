/-
# `Work.FTS.PhiStar.StarPkgo2Aux.ZeroOffFields` — the fields vanish off the open quadrant

The star package of the lead (`VocabO2.StarCore`) produces a stream function `Ψ` whose
"fluid" part `Ψ − Θ` vanishes *off* the open quadrant `Q0 = (0,∞) × (0,π/2)`
(`Work.FTS.PhiStar.PhiTs_zeroOffW_off`).  The fields

`Rop α Ψ = (2 sinθ Ψ + α sinθ z ∂_zΨ + cosθ ∂_θΨ)/cosθ`,
`Vop Ψ = ∂_θΨ − tanθ Ψ`,
`Uop α Ψ = −3Ψ − α z ∂_zΨ`

(and the same multiplied by `(z+1)/z`, resp. divided by `s2 θ = sin 2θ`) are built from `Ψ`
**and its first derivatives**, which do *not* vanish on the boundary of the quadrant just
because `Ψ` does.  This module records that they vanish there anyway, i.e. the whole
five-fold `FieldIdents` list of the lead is `0` off `Q0`.

The reason is that `deriv` sees only the germ, and the germ of `Ψ` at a point outside the
open quadrant is very often the germ of the zero function:

* if `z ≤ 0` then the *whole* slice `θ' ↦ Ψ z θ'` vanishes (as `(z,θ') ∉ Q0` for every `θ'`),
  so `∂_θΨ z θ = 0`; and if `z < 0` also `∂_zΨ z θ = 0` (the `z`-slice is locally zero);
* if `z > 0` then `θ ∉ (0,π/2)`: for `θ < 0`, resp. `θ > π/2`, a whole neighbourhood of the
  point misses `Q0`, so both partial derivatives vanish; the only genuine boundary cases are

  – `θ = 0`: the `θ`-slice vanishes on `(-∞,0]`, which forces `deriv = 0` (`zof_deriv_Iic`);
  – `θ = π/2`: the `θ`-slice vanishes on `[π/2,∞)`, similarly (`zof_deriv_Ici`).

  (`z = 0` with `z > 0` being impossible, the `z`-slice vanishes on `(0,∞) ∋ z`, so `∂_zΨ` is
  the derivative of a function that is locally zero.)

The two one-sided facts are the elementary "a function vanishing on one half-line has zero
derivative at the junction" lemmas, proved here directly from the definition of `deriv` (as a
two-sided difference-quotient limit: the limit along the non-vanishing side is `0`, and if the
two-sided limit exists it must equal it; if it does not exist Lean's `deriv` is `0`).

Everything is elementary: no positivity, no smoothness and no support hypothesis on `Ψ` is
used beyond `zeroOff`.  Axioms: `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Group.AddTorsor
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.Construction.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.StarPkgo2Aux

set_option autoImplicit false

/-! ## A function vanishing on a half-line has zero derivative at the junction -/

/-- If `g` vanishes on `(-∞,a]`, then `deriv g a = 0`. -/
theorem zof_deriv_eq_zero_of_eqOn_Iic {g : ℝ → ℝ} {a : ℝ} (h : ∀ x : ℝ, x ≤ a → g x = 0) :
    deriv g a = 0 := by
  by_cases hd : DifferentiableAt ℝ g a
  · have ht : Tendsto (slope g a) (𝓝[Set.Iio a] a) (𝓝 (deriv g a)) :=
      hd.hasDerivAt.tendsto_slope.mono_left (nhdsWithin_mono a (fun z hz => ne_of_lt hz))
    have h0 : (fun z : ℝ => slope g a z) =ᶠ[𝓝[Set.Iio a] a] (fun _ => (0 : ℝ)) := by
      filter_upwards [self_mem_nhdsWithin] with z hz
      simp only [slope_def_field]
      rw [h z (le_of_lt hz), h a le_rfl]
      simp
    exact tendsto_nhds_unique (ht.congr' h0) tendsto_const_nhds
  · exact deriv_zero_of_not_differentiableAt hd

/-- If `g` vanishes on `[a,∞)`, then `deriv g a = 0`. -/
theorem zof_deriv_eq_zero_of_eqOn_Ici {g : ℝ → ℝ} {a : ℝ} (h : ∀ x : ℝ, a ≤ x → g x = 0) :
    deriv g a = 0 := by
  by_cases hd : DifferentiableAt ℝ g a
  · have ht : Tendsto (slope g a) (𝓝[Set.Ioi a] a) (𝓝 (deriv g a)) :=
      hd.hasDerivAt.tendsto_slope.mono_left (nhdsWithin_mono a (fun z hz => ne_of_gt hz))
    have h0 : (fun z : ℝ => slope g a z) =ᶠ[𝓝[Set.Ioi a] a] (fun _ => (0 : ℝ)) := by
      filter_upwards [self_mem_nhdsWithin] with z hz
      simp only [slope_def_field]
      rw [h z (le_of_lt hz), h a le_rfl]
      simp
    exact tendsto_nhds_unique (ht.congr' h0) tendsto_const_nhds
  · exact deriv_zero_of_not_differentiableAt hd

/-! ## The two partial derivatives of a function vanishing off `Q0` -/

/-- `∂_zΨ = 0` at every point off the open quadrant. -/
theorem zof_pz_eq_zero (Ψ : ℝ → ℝ → ℝ)
    (hZ : ∀ z θ : ℝ, (z, θ) ∉ Work.FTS.EllipticEst.Q0 → Ψ z θ = 0) :
    ∀ z θ : ℝ, (z, θ) ∉ Work.FTS.EllipticEst.Q0 → Work.Spaces.pz Ψ z θ = 0 := by
  intro z θ h
  rw [Work.Spaces.pz]
  rcases lt_trichotomy z 0 with hz | hz | hz
  · -- `z < 0`: the `z`-slice vanishes on the neighbourhood `(-∞,0)` of `z`
    have hfe : (fun z' : ℝ => Ψ z' θ) =ᶠ[𝓝 z] (fun _ => (0 : ℝ)) := by
      filter_upwards [isOpen_Iio.mem_nhds hz] with z' hz'
      exact hZ z' θ (fun hmem =>
        absurd (Work.FTS.EllipticEst.mem_Q0.mp hmem).1 (not_lt.mpr (le_of_lt hz')))
    rw [hfe.deriv_eq, deriv_const]
  · -- `z = 0`: the `z`-slice vanishes on `(-∞,0]`
    subst hz
    exact zof_deriv_eq_zero_of_eqOn_Iic (fun x hx => hZ x θ (fun hmem =>
      absurd (Work.FTS.EllipticEst.mem_Q0.mp hmem).1 (not_lt.mpr hx)))
  · -- `z > 0`: then `θ ∉ (0,π/2)`, so the *whole* `z`-slice of `Ψ` vanishes
    have hfun : (fun z' : ℝ => Ψ z' θ) = fun _ => (0 : ℝ) := by
      funext z'
      exact hZ z' θ (fun hmem =>
        h (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, (Work.FTS.EllipticEst.mem_Q0.mp hmem).2.1,
          (Work.FTS.EllipticEst.mem_Q0.mp hmem).2.2⟩))
    rw [hfun, deriv_const]

/-- `∂_θΨ = 0` at every point off the open quadrant. -/
theorem zof_pth_eq_zero (Ψ : ℝ → ℝ → ℝ)
    (hZ : ∀ z θ : ℝ, (z, θ) ∉ Work.FTS.EllipticEst.Q0 → Ψ z θ = 0) :
    ∀ z θ : ℝ, (z, θ) ∉ Work.FTS.EllipticEst.Q0 → Work.Spaces.pth Ψ z θ = 0 := by
  intro z θ h
  rw [Work.Spaces.pth]
  by_cases hz : z ≤ 0
  · -- `z ≤ 0`: the whole `θ`-slice vanishes
    have hfun : (fun θ' : ℝ => Ψ z θ') = fun _ => (0 : ℝ) := by
      funext θ'
      exact hZ z θ' (fun hmem =>
        absurd (Work.FTS.EllipticEst.mem_Q0.mp hmem).1 (not_lt.mpr hz))
    rw [hfun, deriv_const]
  · have hz' : (0 : ℝ) < z := not_le.mp hz
    rcases lt_trichotomy θ 0 with hθ | hθ | hθ
    · -- `θ < 0`: the `θ`-slice vanishes on the neighbourhood `(-∞,0)` of `θ`
      have hfe : (fun θ' : ℝ => Ψ z θ') =ᶠ[𝓝 θ] (fun _ => (0 : ℝ)) := by
        filter_upwards [isOpen_Iio.mem_nhds hθ] with θ' hθ'
        exact hZ z θ' (fun hmem =>
          absurd (Work.FTS.EllipticEst.mem_Q0.mp hmem).2.1 (not_lt.mpr (le_of_lt hθ')))
      rw [hfe.deriv_eq, deriv_const]
    · -- `θ = 0`: the `θ`-slice vanishes on `(-∞,0]`
      subst hθ
      exact zof_deriv_eq_zero_of_eqOn_Iic (fun y hy => hZ z y (fun hmem =>
        absurd (Work.FTS.EllipticEst.mem_Q0.mp hmem).2.1 (not_lt.mpr hy)))
    · -- `θ > 0`: with `z > 0` and `(z,θ) ∉ Q0` we get `π/2 ≤ θ`
      have hpi : Real.pi / 2 ≤ θ := by
        by_contra hcon
        exact h (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz', hθ, not_le.mp hcon⟩)
      rcases lt_trichotomy θ (Real.pi / 2) with h2 | h2 | h2
      · exact absurd hpi (not_le.mpr h2)
      · -- `θ = π/2`: the `θ`-slice vanishes on `[π/2,∞)`
        subst h2
        exact zof_deriv_eq_zero_of_eqOn_Ici (fun y hy => hZ z y (fun hmem =>
          absurd hy (not_le.mpr (Work.FTS.EllipticEst.mem_Q0.mp hmem).2.2)))
      · -- `θ > π/2`: the `θ`-slice vanishes on the neighbourhood `(π/2,∞)` of `θ`
        have hfe : (fun θ' : ℝ => Ψ z θ') =ᶠ[𝓝 θ] (fun _ => (0 : ℝ)) := by
          filter_upwards [isOpen_Ioi.mem_nhds h2] with θ' hθ'
          exact hZ z θ' (fun hmem =>
            absurd (Work.FTS.EllipticEst.mem_Q0.mp hmem).2.2 (not_lt.mpr (le_of_lt hθ')))
        rw [hfe.deriv_eq, deriv_const]

/-! ## The target -/

theorem ZeroOffFields (α : ℝ) (Ψ : ℝ → ℝ → ℝ)
    (hZ : ∀ z θ : ℝ, (z, θ) ∉ Work.FTS.EllipticEst.Q0 → Ψ z θ = 0) :
    (∀ z θ : ℝ, (z, θ) ∉ Work.FTS.EllipticEst.Q0 →
      (z + 1) / z * Work.Construction.Rop α Ψ z θ = 0) ∧
    (∀ z θ : ℝ, (z, θ) ∉ Work.FTS.EllipticEst.Q0 → Work.Construction.Vop Ψ z θ = 0) ∧
    (∀ z θ : ℝ, (z, θ) ∉ Work.FTS.EllipticEst.Q0 →
      (z + 1) / z * Work.Construction.Vop Ψ z θ = 0) ∧
    (∀ z θ : ℝ, (z, θ) ∉ Work.FTS.EllipticEst.Q0 →
      Work.Construction.Uop α Ψ z θ / Work.Construction.s2 θ = 0) ∧
    (∀ z θ : ℝ, (z, θ) ∉ Work.FTS.EllipticEst.Q0 →
      (z + 1) / z * (Work.Construction.Uop α Ψ z θ / Work.Construction.s2 θ) = 0) := by
  have hpz := zof_pz_eq_zero Ψ hZ
  have hpth := zof_pth_eq_zero Ψ hZ
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro z θ h
    have h1 := hZ z θ h
    have h2 := hpz z θ h
    have h3 := hpth z θ h
    simp only [Work.Construction.Rop, h1, h2, h3]
    ring
  · intro z θ h
    have h1 := hZ z θ h
    have h3 := hpth z θ h
    simp only [Work.Construction.Vop, h1, h3]
    ring
  · intro z θ h
    have h1 := hZ z θ h
    have h3 := hpth z θ h
    simp only [Work.Construction.Vop, h1, h3]
    ring
  · intro z θ h
    have h1 := hZ z θ h
    have h2 := hpz z θ h
    simp only [Work.Construction.Uop, h1, h2]
    ring
  · intro z θ h
    have h1 := hZ z θ h
    have h2 := hpz z θ h
    simp only [Work.Construction.Uop, h1, h2]
    ring

end Work.FTS.PhiStar.StarPkgo2Aux
