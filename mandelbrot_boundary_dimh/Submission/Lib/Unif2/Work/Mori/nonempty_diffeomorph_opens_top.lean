import Mathlib
import Submission.Lib.Unif2.Work.Mori.Defs

namespace Work.Mori

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

/-- **The canonical map onto the top open subset is smooth.**  For any charted space `M` and model
with corners `I`, the map `x ↦ ⟨x, ·⟩` from `M` to the open subtype `↥(⊤ : Opens M)` is `C^∞`.

This is stated for an *abstract* charted space, with the manifold and topological structures on `M`
as variables, on purpose: the composite `Subtype.val ∘ (x ↦ ⟨x, ·⟩)` is the identity, so the
statement is `ContMDiff.subtypeVal_comp_iff` + `contMDiff_id`.  For a concrete `M` such as `ℂ`,
where several propositionally-but-not-definitionally equal instances of `TopologicalSpace` /
`ChartedSpace` are in scope, the two copies of `M` occurring in `ContMDiff I I ∞ (Subtype.val ∘ f)`
(a map `M → M`) would be compared at instance transparency and fail to unify; with `M` abstract
there is a single instance variable in scope, so no diamond can appear, and the lemma can be
instantiated at any concrete `M` by unification. -/
lemma contMDiff_subtype_top {𝕜 E H M : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
    [TopologicalSpace M] [ChartedSpace H M] :
    ContMDiff I I ∞ (fun x : M => (⟨x, trivial⟩ : (⊤ : TopologicalSpace.Opens M))) := by
  rw [← ContMDiff.subtypeVal_comp_iff (U := (⊤ : TopologicalSpace.Opens M))
    (f := fun x : M => (⟨x, trivial⟩ : (⊤ : TopologicalSpace.Opens M)))]
  exact contMDiff_id

/-- **`⊤ : Opens ℂ` is `ℂ`.**  There is a biholomorphism (at the smoothness level `∞`, written out here
because the notation `≃ₘ⟮mℂ, mℂ⟯` is not in scope in this file) from the open subtype
`⊤ : TopologicalSpace.Opens ℂ` to `ℂ`, namely the identity: `fun z => (z : ℂ)` with inverse
`fun w => ⟨w, trivial⟩`.

Used to close the empty-polar-set case of the parabolic branch of uniformization: if the polar set
`Uᶜ` is empty then `U = ⊤` and `X ≃ₘ U` gives `X ≃ₘ ℂ`. -/
theorem nonempty_diffeomorph_opens_top :
    Nonempty (Diffeomorph (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (⊤ : TopologicalSpace.Opens ℂ) ℂ ((⊤ : ℕ∞) : WithTop ℕ∞)) := by
  let e : (⊤ : TopologicalSpace.Opens ℂ) ≃ ℂ :=
    { toFun := fun z => (z : ℂ),
      invFun := fun w => ⟨w, trivial⟩,
      left_inv := fun z => Subtype.ext rfl,
      right_inv := fun _ => rfl }
  refine ⟨Diffeomorph.mk e ?_ ?_⟩
  · exact contMDiff_subtype_val
  · exact contMDiff_subtype_top (M := ℂ) (I := modelWithCornersSelf ℂ ℂ)

end Work.Mori
