import Mathlib
import Submission.Work.Diff.EXT.ricCore
import Submission.Work.Diff.EXT.contMDiffAt_mvfderiv_gen
import Submission.Work.Diff.EXT.contMDiffAt_prod_inr_field

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `EXT`: spatial derivative of a jointly smooth family along a field smooth at the point

`Work.Diff.EXT.contMDiffAt_mvfderiv_along_field_at`: if `Φ : ℝ × M → F` is jointly `C^∞` near
`(t₀, x)` and the section `A` is `C^∞` at `x`, then `(t, y) ↦ d_y Φ(t, ·)(A y)` is jointly `C^∞`
near `(t₀, x)`.

This is the local form needed for the coordinate frame of a chart, which is smooth only on the
chart.  The proof reduces to the *product manifold* `ℝ × M`:

* `contMDiffAt_prod_inr_field` (`Diff/EXT/contMDiffAt_prod_inr_field`): the section
  `p ↦ (0, A p.2)` of `T(ℝ × M)` is `C^∞` at `(t₀, x)` whenever `A` is `C^∞` at `x`;
* `contMDiffAt_mvfderiv_gen` (`Diff/EXT/contMDiffAt_mvfderiv_gen`): the analogous "at a point",
  arbitrary-target version of the smoothness of a spatial derivative along a field;
* the remaining step is the eventual identification of `mvfderiv ((𝓘(ℝ,ℝ)).prod I) Φ p (0, A p.2)`
  with `mvfderiv I (fun y => Φ (p.1, y)) p.2 (A p.2)`: the total derivative of a two-variable
  function splits into its two partial derivatives (`mfderiv_prod_eq_add_apply`), and the partial
  derivative in the `t`-variable vanishes on `0`.
-/

set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.EXT

/-! ## The main lemma -/

/-- **The spatial derivative of a jointly smooth family, along a field smooth at the point, is
jointly smooth (local form).**  If `Φ : ℝ × M → F` is jointly `C^∞` near `(t₀, x)` and the section
`A` is `C^∞` at `x`, then `(t, y) ↦ d_y Φ(t, ·)(A y)` is jointly `C^∞` near `(t₀, x)`.  This is the
form needed for the coordinate frame of a chart, which is smooth only on the chart. -/
theorem contMDiffAt_mvfderiv_along_field_at
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {Φ : ℝ × M → F} {A : Π y : M, TangentSpace I y} {t₀ : ℝ} {x : M}
    (hΦ : JointSmoothAt I M Φ t₀ x) (hA : SmoothFieldAt I M A x) :
    JointSmoothAt I M (fun p : ℝ × M => mvfderiv I (fun y : M => Φ (p.1, y)) p.2 (A p.2)) t₀ x := by
  -- the vertical lift of `A` is a field on `ℝ × M` that is smooth at `(t₀, x)`
  have hB : ContMDiffAt ((𝓘(ℝ,ℝ)).prod I) ((𝓘(ℝ,ℝ)).prod I).tangent ∞
      (fun p : ℝ × M => (⟨p, (0, A p.2)⟩ : TangentBundle ((𝓘(ℝ,ℝ)).prod I) (ℝ × M)))
      (t₀, x) :=
    contMDiffAt_prod_inr_field (I := I) (M := M) (A := A) (t₀ := t₀) (x := x)
      (by simpa only [SmoothFieldAt] using hA)
  -- smoothness of the total derivative of `Φ` along that field
  have key := contMDiffAt_mvfderiv_gen (I := (𝓘(ℝ,ℝ)).prod I) (M := ℝ × M) (F := F)
    (f := Φ) (X := fun p : ℝ × M => ((0, A p.2) : TangentSpace ((𝓘(ℝ,ℝ)).prod I) p)) hΦ hB
  -- it agrees with the spatial derivative of the slice
  refine key.congr_of_eventuallyEq ?_
  have h2 : ∀ᶠ p in 𝓝 (t₀, x),
      ContMDiffAt ((𝓘(ℝ,ℝ)).prod I) 𝓘(ℝ,F) (1 : ℕ∞ω) Φ p :=
    (contMDiffAt_iff_contMDiffAt_nhds (n := (1 : ℕ∞ω)) (by decide)).mp
      (hΦ.of_le (show (1 : ℕ∞ω) ≤ ∞ from by norm_num))
  filter_upwards [h2] with p hp
  have hpd : MDifferentiableAt ((𝓘(ℝ,ℝ)).prod I) 𝓘(ℝ,F) Φ p := hp.mdifferentiableAt (by norm_num)
  have h := mfderiv_prod_eq_add_apply (I := 𝓘(ℝ,ℝ)) (M := ℝ) (I' := I) (M' := M)
    (I'' := 𝓘(ℝ,F)) (M'' := F) (f := Φ) (p := p) (v := ((0 : ℝ), A p.2)) hpd
  erw [h, map_zero, zero_add]
  rfl

end Work.Diff.EXT
