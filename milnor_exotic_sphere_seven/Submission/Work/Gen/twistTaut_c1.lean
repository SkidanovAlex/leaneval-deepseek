import Mathlib
import Submission.Work.Gen.chernRootDefs
import Submission.Work.Gen.tensorLine_c1_additive
import Submission.Work.Gen.DualLineCore
import Submission.Work.LerayHirsch.nonempty_bundleIso_twist_dual

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
# The first Chern class of `ℓ^* ⊗ π^*L`

`Work.Gen.twistTaut W L = ℓ^* ⊗ π^*L` is the twist of the tautological line bundle `ℓ` of the
projectivisation `P(W)` by the pullback of a complex line bundle `L` on the base.  Its first Chern
class is

  `c₁(ℓ^* ⊗ π^*L) = π^*c₁(L) - ζ`,

where `ζ = c₁(ℓ)` is the hyperplane class (`Work.LerayHirsch.zeta W`).

The proof deliberately avoids the "the dual line bundle has the negative Chern class" statement.
Instead it uses the *untwisting* isomorphism `ℓ ⊗ (ℓ^* ⊗ π^*L) ≅ π^*L` of
`Work.LerayHirsch.nonempty_bundleIso_twist_dual` (already proved in the tree; in particular it needs
no instance of the Whitney sum formula `c₂(L₁ ⊕ L₂) = c₁(L₁)⌣c₁(L₂)`): the two sides have the same
first Chern class, and the left-hand side is a tensor product of two *line* bundles once
`Work.LerayHirsch.twistCore` is identified with `Work.Gen.tensorLine`
(`nonempty_bundleIso_twistCore_tensorLine_rank_one` below), so the additivity of `c₁` on the tensor
product of line bundles (`Work.Gen.tensorLine_c1_additive`) and the naturality of `c₁` under the
projection (`Work.Thom.chernClass_comap`) finish it.
-/

namespace Work.Gen

/-- **The transition function of `twistCore` of two line bundles is that of `tensorLine`.**  For a
rank-one bundle the transition function is its scalar times the identity
(`Work.Gen.scl_smul_id`), and the two constructions differ only in how the two scalars are
multiplied together. -/
theorem twistCore_coordChange_eq_tensorLine {B : Type} [TopologicalSpace B] {ιA ιE : Type}
    (A : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ιA)
    (E : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ιE)
    (p q : ιA × ιE) (x : B) :
    (Work.LerayHirsch.twistCore A E).coordChange p q x
      = (Work.Gen.tensorLine A E).coordChange p q x := by
  rw [Work.LerayHirsch.twistCore_coordChange, Work.Gen.tensorLine_coordChange]
  conv_lhs => rw [Work.Gen.scl_smul_id (E.coordChange p.2 q.2 x)]
  rw [smul_smul]

/-- **`Work.LerayHirsch.twistCore` of two line bundles is `Work.Gen.tensorLine` up to a bundle
isomorphism.**  The two gluing data have the same base sets (over the same cover) and the same
transition functions, so the identity on fibres is a bundle isomorphism
(`Work.Whitney.nonempty_bundleIso_of_gauge_fibre` with the identity gauge).

Consequently `c₁(A ⊗ E) = c₁(A) + c₁(E)` for line bundles `A`, `E` by
`Work.Gen.tensorLine_c1_additive`. -/
theorem nonempty_bundleIso_twistCore_tensorLine_rank_one {B : Type} [TopologicalSpace B]
    {ιA ιE : Type}
    (A : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ιA)
    (E : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ιE) :
    Nonempty (Work.Thom.BundleIso (Work.LerayHirsch.twistCore A E) (Work.Gen.tensorLine A E)) := by
  refine Work.Whitney.nonempty_bundleIso_of_gauge_fibre (Work.LerayHirsch.twistCore A E)
    (Work.Gen.tensorLine A E) (ContinuousLinearEquiv.refl ℂ (EuclideanSpace ℂ (Fin 1)))
    (Equiv.refl (ιA × ιE)) ?_ ?_ ?_
  · intro i
    rw [Equiv.refl_apply, Work.Gen.tensorLine_baseSet, Work.LerayHirsch.twistCore_baseSet]
  · intro b
    rw [Equiv.refl_apply]
    show (Work.Gen.tensorLine A E).indexAt b = (Work.LerayHirsch.twistCore A E).indexAt b
    simp only [Work.Gen.tensorLine_indexAt, Work.LerayHirsch.twistCore_indexAt]
  · intro i b
    rw [Equiv.refl_apply]
    have hcc : (Work.Gen.tensorLine A E).coordChange ((Work.Gen.tensorLine A E).indexAt b) i b
        = (Work.LerayHirsch.twistCore A E).coordChange
            ((Work.LerayHirsch.twistCore A E).indexAt b) i b := by
      rw [twistCore_coordChange_eq_tensorLine A E ((Work.LerayHirsch.twistCore A E).indexAt b) i b]
      rfl
    rw [hcc]
    simp

/-- **The first Chern class of the twist** `ℓ^* ⊗ π^*L` over the projectivisation of `W`:
`c₁(ℓ^* ⊗ π^*L) = π^*c₁(L) - ζ`.

The untwisting isomorphism `ℓ ⊗ (ℓ^* ⊗ π^*L) ≅ π^*L` gives
`ζ + c₁(ℓ^* ⊗ π^*L) = π^*c₁(L)`; solve for `c₁(ℓ^* ⊗ π^*L)`. -/
theorem twistTaut_c1 {B : Type} [TopologicalSpace B] {ι : Type} [Fintype ι] {m : ℕ}
    (W : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) {ιL : Type} [Fintype ιL]
    (L : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ιL) :
    Work.Thom.chernClass 1 1 (twistTaut W L)
      = (Work.Thom.CohMap (Work.LerayHirsch.projMap W) ℤ 2).hom (Work.Thom.chernClass 1 1 L)
        - Work.LerayHirsch.zeta W := by
  -- the untwisting isomorphism `ℓ ⊗ (ℓ^* ⊗ π^*L) ≅ π^*L`
  obtain ⟨e1⟩ := Work.LerayHirsch.nonempty_bundleIso_twist_dual
    (Work.LerayHirsch.tautLine W) (Work.Thom.bundleComap L (Work.LerayHirsch.projMap W))
  have h1 : Work.Thom.chernClass 1 1 (Work.Thom.bundleComap L (Work.LerayHirsch.projMap W))
      = Work.Thom.chernClass 1 1
          (Work.LerayHirsch.twistCore (Work.LerayHirsch.tautLine W) (twistTaut W L)) :=
    (Work.Thom.chernClass_BundleIso _ _ e1).symm
  -- the twist of two rank-one bundles is their tensor product
  obtain ⟨e2⟩ := nonempty_bundleIso_twistCore_tensorLine_rank_one
    (Work.LerayHirsch.tautLine W) (twistTaut W L)
  have h2 : Work.Thom.chernClass 1 1
      (Work.LerayHirsch.twistCore (Work.LerayHirsch.tautLine W) (twistTaut W L))
      = Work.Thom.chernClass 1 1
          (Work.Gen.tensorLine (Work.LerayHirsch.tautLine W) (twistTaut W L)) :=
    Work.Thom.chernClass_BundleIso _ _ e2
  -- additivity of `c₁` on the tensor product of line bundles
  have h3 := Work.Gen.tensorLine_c1_additive
    (Work.LerayHirsch.tautLine W) (twistTaut W L)
  -- naturality of `c₁` under the projection
  have h4 := Work.Thom.chernClass_comap (Z := L) (f := Work.LerayHirsch.projMap W) (j := 1)
  -- `ζ` is the first Chern class of the tautological line bundle
  have h5 : Work.LerayHirsch.zeta W
      = Work.Thom.chernClass 1 1 (Work.LerayHirsch.tautLine W) := by
    rw [Work.LerayHirsch.zeta_def, Work.Thom.cohTransport_rfl]
  have key : Work.Thom.chernClass 1 1 (Work.Thom.bundleComap L (Work.LerayHirsch.projMap W))
      = Work.LerayHirsch.zeta W + Work.Thom.chernClass 1 1 (twistTaut W L) := by
    rw [h1, h2, h3, h5]
  exact eq_sub_iff_add_eq'.mpr (key.symm.trans h4)

end Work.Gen
