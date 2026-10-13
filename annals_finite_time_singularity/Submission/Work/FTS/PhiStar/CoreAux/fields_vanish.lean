import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.PhiStar.CoreAux.FieldsDefs
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS.PhiStar.Basic
import Submission.Work.FTS.PhiStar.CoreAux.iterate_deriv_eq_zero_of_eqOn_Iic
import Submission.Work.FTS.PhiStar.CoreAux.iterate_deriv_eq_zero_of_eqOn_Ici

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `FTS/PhiStar/CoreAux/fields_vanish.lean` — the fields vanish off the open quadrant

`PhiTs α Φs = Φ̃_*` is extended by `0` off the open quadrant `Q0 = (0,∞) × (0,π/2)`
(`StarCore.zeroOff`).  The transport coefficients `Rop, Vop, Uop` of `Work.Construction`
are built from `Ψ`, `∂_zΨ` and `∂_θΨ`; because the vanishing of `Φ̃_*` holds on a whole
half-plane in each variable, its *derivatives* vanish too at every point off `Q0`, and the
same then holds for every expression built from them.  Here we record that for all ten
fields consumed by `CoreAux/Assembly.lean` (`F0c_of_boundary`).

The analytic input is the "one-sided" fact for `deriv` in the sibling files
`CoreAux/iterate_deriv_eq_zero_of_eqOn_Iic.deriv_eq_zero_of_eqOn_Iic'` and
`CoreAux/iterate_deriv_eq_zero_of_eqOn_Ici.deriv_eq_zero_of_eqOn_Ici'`: a function vanishing
on `Iic a` (resp. `Ici a`) has derivative `0` at every point of that half-line (the right
half is needed at the edge `θ = π/2` of the quadrant).
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.CoreAux

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The off-quadrant condition -/

/-- The disjunction `z ≤ 0 ∨ θ ≤ 0 ∨ π/2 ≤ θ` puts the point outside the open quadrant. -/
theorem not_mem_Q0_of {z θ : ℝ} (h : z ≤ 0 ∨ θ ≤ 0 ∨ Real.pi / 2 ≤ θ) :
    ¬ ((z, θ) ∈ Work.FTS.EllipticEst.Q0) := by
  rw [Work.FTS.EllipticEst.Q0]
  simp only [Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo]
  rintro ⟨hz, hθ0, hθ1⟩
  rcases h with h | h | h
  · exact absurd hz (not_lt.mpr h)
  · exact absurd hθ0 (not_lt.mpr h)
  · exact absurd h (not_le.mpr hθ1)

/-! ## Derivatives of a function vanishing off the quadrant

The hypothesis is exactly the shape of the pointwise vanishing consumed by
`CoreAux/Assembly.lean`: `f` is `0` at every point of the closed complement of the open
quadrant, **slicewise** (the same `f`, not just its values).  Then `pz f` and `pth f`
vanish there as well: along the variable that is fixed, `f` is `0` on a half-line, and the
only possibly non-local point `z = 0` (resp. `θ = 0`) is handled by the `Iic` lemma. -/

/-- If `f` vanishes off the open quadrant then so does `pz f = ∂_z f`. -/
theorem pz_eq_zero_of_vanishing {f : ℝ → ℝ → ℝ}
    (hf : ∀ z θ : ℝ, (z ≤ 0 ∨ θ ≤ 0 ∨ Real.pi / 2 ≤ θ) → f z θ = 0) :
    ∀ z θ : ℝ, (z ≤ 0 ∨ θ ≤ 0 ∨ Real.pi / 2 ≤ θ) → Work.Spaces.pz f z θ = 0 := by
  intro z θ h
  simp only [Work.Spaces.pz]
  by_cases hθ : 0 < θ ∧ θ < Real.pi / 2
  · -- `0 < θ < π/2`, so the disjunction forces `z ≤ 0`: the `z`-slice vanishes on `Iic 0`
    have hz : z ≤ 0 := by
      rcases h with h | h | h
      · exact h
      · exact absurd hθ.1 (not_lt.mpr h)
      · exact absurd h (not_le.mpr hθ.2)
    exact deriv_eq_zero_of_eqOn_Iic' (f := fun z' => f z' θ)
      (fun y hy => hf y θ (Or.inl hy)) z hz
  · -- the whole `z`-slice vanishes
    have hzero : ∀ z' : ℝ, f z' θ = 0 := by
      intro z'
      rcases not_and_or.mp hθ with h1 | h2
      · exact hf z' θ (Or.inr (Or.inl (not_lt.mp h1)))
      · exact hf z' θ (Or.inr (Or.inr (not_lt.mp h2)))
    rw [show (fun z' => f z' θ) = fun _ => (0 : ℝ) from funext hzero]
    simp

/-- If `f` vanishes off the open quadrant then so does `pth f = ∂_θ f`. -/
theorem pth_eq_zero_of_vanishing {f : ℝ → ℝ → ℝ}
    (hf : ∀ z θ : ℝ, (z ≤ 0 ∨ θ ≤ 0 ∨ Real.pi / 2 ≤ θ) → f z θ = 0) :
    ∀ z θ : ℝ, (z ≤ 0 ∨ θ ≤ 0 ∨ Real.pi / 2 ≤ θ) → Work.Spaces.pth f z θ = 0 := by
  intro z θ h
  simp only [Work.Spaces.pth]
  by_cases hθ : θ ≤ 0
  · exact deriv_eq_zero_of_eqOn_Iic' (f := fun θ' => f z θ')
      (fun y hy => hf z y (Or.inr (Or.inl hy))) θ hθ
  · have hθ' : 0 < θ := not_le.mp hθ
    by_cases h2 : Real.pi / 2 ≤ θ
    · exact deriv_eq_zero_of_eqOn_Ici' (f := fun θ' => f z θ')
        (fun y hy => hf z y (Or.inr (Or.inr hy))) θ h2
    · -- `0 < θ < π/2`, so the disjunction forces `z ≤ 0`: the `θ`-slice vanishes entirely
      have h2' : θ < Real.pi / 2 := not_le.mp h2
      have hz : z ≤ 0 := by
        rcases h with h | h | h
        · exact h
        · exact absurd h (not_le.mpr hθ')
        · exact absurd h (not_le.mpr h2')
      have hzero : ∀ θ' : ℝ, f z θ' = 0 := fun θ' => hf z θ' (Or.inl hz)
      rw [show (fun θ' => f z θ') = fun _ => (0 : ℝ) from funext hzero]
      simp

/-! ## The ten fields -/

theorem fields_vanish {α Cs : ℝ} (hα : 0 < α) {Φs : Work.FTS.Galerkin.Fn} (hcore : Work.FTS.VocabO2.StarCore α Cs Φs) : (∀ z θ : ℝ, (z ≤ 0 ∨ θ ≤ 0 ∨ Real.pi / 2 ≤ θ) → (z + 1) / z * Work.Construction.Rop α (Work.FTS.VocabO2.PhiTs α Φs) z θ = 0) ∧ (∀ z θ : ℝ, (z ≤ 0 ∨ θ ≤ 0 ∨ Real.pi / 2 ≤ θ) → Work.Construction.Vop (Work.FTS.VocabO2.PhiTs α Φs) z θ = 0) ∧ (∀ z θ : ℝ, (z ≤ 0 ∨ θ ≤ 0 ∨ Real.pi / 2 ≤ θ) → (z + 1) / z * Work.Construction.Vop (Work.FTS.VocabO2.PhiTs α Φs) z θ = 0) ∧ (∀ z θ : ℝ, (z ≤ 0 ∨ θ ≤ 0 ∨ Real.pi / 2 ≤ θ) → Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs) z θ / Work.Construction.s2 θ = 0) ∧ (∀ z θ : ℝ, (z ≤ 0 ∨ θ ≤ 0 ∨ Real.pi / 2 ≤ θ) → (z + 1) / z * (Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs) z θ / Work.Construction.s2 θ) = 0) ∧ (∀ z θ : ℝ, (z ≤ 0 ∨ θ ≤ 0 ∨ Real.pi / 2 ≤ θ) → Work.Spaces.pth (fun z θ => (z + 1) / z * Work.Construction.Rop α (Work.FTS.VocabO2.PhiTs α Φs) z θ) z θ = 0) ∧ (∀ z θ : ℝ, (z ≤ 0 ∨ θ ≤ 0 ∨ Real.pi / 2 ≤ θ) → Work.Spaces.pth (Work.Construction.Vop (Work.FTS.VocabO2.PhiTs α Φs)) z θ = 0) ∧ (∀ z θ : ℝ, (z ≤ 0 ∨ θ ≤ 0 ∨ Real.pi / 2 ≤ θ) → Work.Spaces.pth (fun z θ => (z + 1) / z * Work.Construction.Vop (Work.FTS.VocabO2.PhiTs α Φs) z θ) z θ = 0) ∧ (∀ z θ : ℝ, (z ≤ 0 ∨ θ ≤ 0 ∨ Real.pi / 2 ≤ θ) → Work.Spaces.pth (fun z θ => Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs) z θ / Work.Construction.s2 θ) z θ = 0) ∧ (∀ z θ : ℝ, (z ≤ 0 ∨ θ ≤ 0 ∨ Real.pi / 2 ≤ θ) → Work.Spaces.pth (fun z θ => (z + 1) / z * (Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs) z θ / Work.Construction.s2 θ)) z θ = 0) := by
  set Ψ : ℝ → ℝ → ℝ := Work.FTS.VocabO2.PhiTs α Φs with hΨdef
  -- pointwise vanishing of `Ψ = Φ̃_*`
  have hΨ : ∀ z θ : ℝ, (z ≤ 0 ∨ θ ≤ 0 ∨ Real.pi / 2 ≤ θ) → Ψ z θ = 0 := by
    intro z θ h
    rw [hΨdef]
    exact hcore.zeroOff z θ (not_mem_Q0_of h)
  have hpz := pz_eq_zero_of_vanishing hΨ
  have hpth := pth_eq_zero_of_vanishing hΨ
  -- pointwise vanishing of the five basic fields
  have hR : ∀ z θ : ℝ, (z ≤ 0 ∨ θ ≤ 0 ∨ Real.pi / 2 ≤ θ) →
      (z + 1) / z * Work.Construction.Rop α Ψ z θ = 0 := by
    intro z θ h
    simp [Work.Construction.Rop, hΨ z θ h, hpz z θ h, hpth z θ h]
  have hV : ∀ z θ : ℝ, (z ≤ 0 ∨ θ ≤ 0 ∨ Real.pi / 2 ≤ θ) →
      Work.Construction.Vop Ψ z θ = 0 := by
    intro z θ h
    simp [Work.Construction.Vop, hΨ z θ h, hpth z θ h]
  have hVz : ∀ z θ : ℝ, (z ≤ 0 ∨ θ ≤ 0 ∨ Real.pi / 2 ≤ θ) →
      (z + 1) / z * Work.Construction.Vop Ψ z θ = 0 := by
    intro z θ h
    rw [hV z θ h, mul_zero]
  have hU : ∀ z θ : ℝ, (z ≤ 0 ∨ θ ≤ 0 ∨ Real.pi / 2 ≤ θ) →
      Work.Construction.Uop α Ψ z θ / Work.Construction.s2 θ = 0 := by
    intro z θ h
    have h1 : Work.Construction.Uop α Ψ z θ = 0 := by
      simp [Work.Construction.Uop, hΨ z θ h, hpz z θ h]
    rw [h1, zero_div]
  have hUz : ∀ z θ : ℝ, (z ≤ 0 ∨ θ ≤ 0 ∨ Real.pi / 2 ≤ θ) →
      (z + 1) / z * (Work.Construction.Uop α Ψ z θ / Work.Construction.s2 θ) = 0 := by
    intro z θ h
    rw [hU z θ h, mul_zero]
  exact ⟨hR, hV, hVz, hU, hUz,
    pth_eq_zero_of_vanishing hR, pth_eq_zero_of_vanishing hV,
    pth_eq_zero_of_vanishing hVz, pth_eq_zero_of_vanishing hU,
    pth_eq_zero_of_vanishing hUz⟩

end Work.FTS.PhiStar.CoreAux
