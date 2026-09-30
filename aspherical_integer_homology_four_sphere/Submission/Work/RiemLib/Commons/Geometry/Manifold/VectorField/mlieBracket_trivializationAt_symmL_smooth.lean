import Mathlib.Geometry.Manifold.VectorField.LieBracket

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open scoped Manifold ContDiff Bundle Topology
open Bundle Set VectorField

namespace Commons.Geometry.Manifold.VectorField

set_option backward.isDefEq.respectTransparency false in
/-- The two vector fields `q ↦ (trivializationAt E (TangentSpace I) x₀).symmL ℝ q v` and
`q ↦ (trivializationAt E (TangentSpace I) x₀).symmL ℝ q w` are the "constant" vector fields
`v` and `w` written in the chart at `x₀`; hence their Lie bracket vanishes everywhere on the
chart domain, in particular at `p ∈ (chartAt H x₀).source`.

The proof pulls everything back to the model space through the chart at `x₀`: the pullback of the
first field is the constant field `v`, so the pulled back bracket is the bracket of two constant
fields, which is zero, and pullback by the (invertible) derivative of the chart is injective. -/
theorem mlieBracket_trivializationAt_symmL_smooth
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    (x₀ : M) (v w : E) {p : M} (hp : p ∈ (chartAt H x₀).source) :
    VectorField.mlieBracket I
      (fun q : M => (trivializationAt E (TangentSpace I) x₀).symmL ℝ q v)
      (fun q : M => (trivializationAt E (TangentSpace I) x₀).symmL ℝ q w) p = 0 := by
  have hpt : p ∈ (extChartAt I x₀).source := by
    rwa [extChartAt_source]
  -- The constant fields `v` and `w` on the model space, as genuine vector fields on `E`.
  let Vc : Π (y : E), TangentSpace 𝓘(ℝ, E) y := fun _ => v
  let Wc : Π (y : E), TangentSpace 𝓘(ℝ, E) y := fun _ => w
  have hVc : MDiffAt (T% Vc) (extChartAt I x₀ p) :=
    ((contMDiffAt_vectorSpace_iff_contDiffAt (V := Vc) (x := extChartAt I x₀ p)
      (n := ∞)).mpr (contDiffAt_const (c := v))).mdifferentiableAt (by decide)
  have hWc : MDiffAt (T% Wc) (extChartAt I x₀ p) :=
    ((contMDiffAt_vectorSpace_iff_contDiffAt (V := Wc) (x := extChartAt I x₀ p)
      (n := ∞)).mpr (contDiffAt_const (c := w))).mdifferentiableAt (by decide)
  have hψ : CMDiffAt ∞ (extChartAt I x₀) p := contMDiffAt_extChartAt' hp
  have hle : minSmoothness ℝ 2 ≤ ∞ := by
    rw [minSmoothness_of_isRCLikeNormedField]
    exact ENat.LEInfty.out
  -- `minSmoothness` is irreducible, so the `LEInfty`-based instance cannot fire on it;
  -- provide the required low-smoothness manifold instance explicitly.
  have : IsManifold I (minSmoothness ℝ 2) M := IsManifold.of_le hle
  -- Naturality of the Lie bracket under the pullback by the chart at `x₀`.
  have hmp := mpullback_mlieBracket (𝕜 := ℝ) (I := I) (I' := 𝓘(ℝ, E))
      (f := fun q : M => extChartAt I x₀ q) (V := Vc) (W := Wc)
      (x₀ := p) hVc hWc hψ hle
  -- The Lie bracket of two constant fields is zero.
  have hconst : mlieBracket 𝓘(ℝ, E) Vc Wc = 0 := by
    funext y
    rw [← mlieBracketWithin_univ, mlieBracketWithin_eq_lieBracketWithin]
    simp [lieBracketWithin, Vc, Wc]
  -- On the chart domain, pulling back the field `symmL · v` by the chart gives the constant `v`,
  -- because `symmL` is the inverse of the derivative of the chart.
  have key : ∀ q ∈ (extChartAt I x₀).source,
      mpullback I 𝓘(ℝ, E) (fun q : M => extChartAt I x₀ q) Vc q
        = (trivializationAt E (TangentSpace I) x₀).symmL ℝ q v := by
    intro q hq
    have hqc : q ∈ (chartAt H x₀).source := by rw [extChartAt_source] at hq; exact hq
    have hqinv : (mfderiv% (extChartAt I x₀) q).IsInvertible :=
      isInvertible_mfderiv_extChartAt hq
    have hcomp := mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm' (x := x₀) hq
    have hinv : (mfderiv% (extChartAt I x₀) q).inverse v
        = (mfderiv[range I] (extChartAt I x₀).symm (extChartAt I x₀ q)) v := by
      refine (hqinv.inverse_apply_eq (x := (mfderiv[range I] (extChartAt I x₀).symm
        (extChartAt I x₀ q)) v) (y := v)).mpr ?_
      have h := (congrArg (fun h => h v) hcomp).symm
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at h
      exact h
    simp only [mpullback_apply, Vc]
    rw [TangentBundle.symmL_trivializationAt (I := I) hqc]
    exact hinv
  have keyw : ∀ q ∈ (extChartAt I x₀).source,
      mpullback I 𝓘(ℝ, E) (fun q : M => extChartAt I x₀ q) Wc q
        = (trivializationAt E (TangentSpace I) x₀).symmL ℝ q w := by
    intro q hq
    have hqc : q ∈ (chartAt H x₀).source := by rw [extChartAt_source] at hq; exact hq
    have hqinv : (mfderiv% (extChartAt I x₀) q).IsInvertible :=
      isInvertible_mfderiv_extChartAt hq
    have hcomp := mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm' (x := x₀) hq
    have hinv : (mfderiv% (extChartAt I x₀) q).inverse w
        = (mfderiv[range I] (extChartAt I x₀).symm (extChartAt I x₀ q)) w := by
      refine (hqinv.inverse_apply_eq (x := (mfderiv[range I] (extChartAt I x₀).symm
        (extChartAt I x₀ q)) w) (y := w)).mpr ?_
      have h := (congrArg (fun h => h w) hcomp).symm
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at h
      exact h
    simp only [mpullback_apply, Wc]
    rw [TangentBundle.symmL_trivializationAt (I := I) hqc]
    exact hinv
  have hVeq : mpullback I 𝓘(ℝ, E) (fun q : M => extChartAt I x₀ q) Vc
      =ᶠ[𝓝 p] (fun q : M => (trivializationAt E (TangentSpace I) x₀).symmL ℝ q v) :=
    Filter.eventually_of_mem ((isOpen_extChartAt_source x₀).mem_nhds hpt) key
  have hWeq : mpullback I 𝓘(ℝ, E) (fun q : M => extChartAt I x₀ q) Wc
      =ᶠ[𝓝 p] (fun q : M => (trivializationAt E (TangentSpace I) x₀).symmL ℝ q w) :=
    Filter.eventually_of_mem ((isOpen_extChartAt_source x₀).mem_nhds hpt) keyw
  rw [← hVeq.mlieBracket_vectorField_eq hWeq, ← hmp, hconst]
  simp [mpullback]

end Commons.Geometry.Manifold.VectorField