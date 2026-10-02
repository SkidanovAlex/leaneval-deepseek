import Submission.Work.Cohomology.Endgame.shiftCap
import Submission.Work.Cohomology.relMV_quasiIso

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The overlap case is degenerate: every simplex lying in `U ∩ V` is already small

`Work.Cohomology.smallInSubcomplex_inter_eq_range` : for any `U V : Set X`,

    smallInSubcomplex U V (U ∩ V) = Subfunctor.range (TopCat.toSSet.map (subtypeIncl X (U ∩ V))).

This is the load-bearing fact for the overlap half of the transgression route (NOTES §20): because
`IsSmall U V σ` unfolds to `Set.range σ ⊆ U ∨ Set.range σ ⊆ V` (`SmallChains.lean:43`), a simplex
whose image lies in `U ∩ V` is *automatically* small, so the small simplices lying in `U ∩ V` are
exactly the singular simplices of the subspace `U ∩ V`.  Consequently the comparison
`smallInLift U V (U ∩ V) : smallInSSet U V (U ∩ V) ⟶ TopCat.toSSet.obj (TopCat.of ↥(U ∩ V))`
(`relMV_quasiIso.lean:59`) is an *isomorphism* of simplicial sets, not merely the quasi-isomorphism
one would expect by analogy with `relMV_quasiIso`, and the induced `phi` of
`exists_capTopCanon_relCapHalf`'s overlap analogue is an isomorphism of chain complexes.

## Proof notes (both directions are two moves each)

* `≤`: a small simplex lying in `U ∩ V` is in the range of `Sing(U∩V) → Sing(X)` by
  `exists_map_inclUX_of_range_subset (U ∩ V) n σ h.2`.
* `≥`: for `σ = (toSSet.map (subtypeIncl X (U∩V))).app n a`, the two conjuncts of
  `IsSmallIn U V (U∩V) σ` follow from `TopCat.toSSetObjEquiv_map_apply` — which is *definitional*
  (`fun _ => rfl`), so no import of `Crux33.PairMap` is needed.  Caveat that cost a build: after
  `rintro y ⟨z, rfl⟩` the goal still contains the beta-redex `(fun z => …) z`, so a `show` (or
  `beta_reduce`) must precede the rewrite; `rw` alone reports "did not find the pattern".

## What is left for the overlap quasi-iso (NOTES §20)

1. `IsIso (smallInLift U V (U ∩ V))`.  Note the naive `rw [smallInSubcomplex_inter_eq_range]`
   **fails** on the motive (`Subfunctor.homOfLe`'s `≤`-proof depends on the subfunctor), so this has
   to be done by constructing the inverse (or via `Subfunctor.homOfLe` of the equality's two
   directions) and cancelling — not by rewriting the subfunctor.
2. then `phi := cokernel.desc …` with the zero condition from `smallInLift_comp`
   (`relMV_quasiIso.lean:66`) and `IsIso phi` by cancelling `cokernel.π`.
-/

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

variable {X : TopCat}

/-- Every simplex whose image lies in `U ∩ V` is automatically small for `(U,V)`, so the small
simplices lying in `U ∩ V` are exactly the range of `Sing(U ∩ V) ⟶ Sing(X)`. -/
theorem smallInSubcomplex_inter_eq_range (U V : Set X) :
    smallInSubcomplex U V (U ∩ V) =
      Subfunctor.range (TopCat.toSSet.map (subtypeIncl X (U ∩ V))) := by
  ext n σ
  rw [Subfunctor.range_obj]
  constructor
  · intro h
    exact exists_map_inclUX_of_range_subset (U ∩ V) n σ h.2
  · rintro ⟨a, rfl⟩
    have hsd : ∀ z : Convexity.StdSimplex ℝ (Fin (n.unop.len + 1)),
        TopCat.toSSetObjEquiv X n
            ((TopCat.toSSet.map (subtypeIncl X (U ∩ V))).app n a) z
          = subtypeIncl X (U ∩ V)
              (TopCat.toSSetObjEquiv (TopCat.of ↥(U ∩ V)) n a z) :=
      fun _ => rfl
    refine ⟨Or.inl ?_, ?_⟩
    · rintro y ⟨z, rfl⟩
      show TopCat.toSSetObjEquiv X n
          ((TopCat.toSSet.map (subtypeIncl X (U ∩ V))).app n a) z ∈ U
      rw [hsd z]
      exact (TopCat.toSSetObjEquiv (TopCat.of ↥(U ∩ V)) n a z).2.1
    · rintro y ⟨z, rfl⟩
      show TopCat.toSSetObjEquiv X n
          ((TopCat.toSSet.map (subtypeIncl X (U ∩ V))).app n a) z ∈ U ∩ V
      rw [hsd z]
      exact (TopCat.toSSetObjEquiv (TopCat.of ↥(U ∩ V)) n a z).2



/-- Since the small simplices lying in `U ∩ V` *are* the range of `Sing(U∩V) ⟶ Sing(X)`, the
inclusion of the former into the latter is an isomorphism. -/
theorem isIso_homOfLe_inter (U V : Set X) :
    IsIso (Subfunctor.homOfLe (smallInSubcomplex_le_range U V (U ∩ V))) := by
  have h := smallInSubcomplex_inter_eq_range U V
  refine ⟨Subfunctor.homOfLe (le_of_eq h.symm), ?_, ?_⟩
  · ext x
    rfl
  · ext x
    rfl

/-- **The overlap lift is an isomorphism**: `smallInLift U V (U∩V)` is the corestriction of the
small simplices lying in `U ∩ V` to the subspace `U ∩ V`, and by
`smallInSubcomplex_inter_eq_range` the two are the same subcomplex. -/
theorem isIso_smallInLift_inter (U V : Set X) : IsIso (smallInLift U V (U ∩ V)) := by
  rw [smallInLift]
  haveI := isIso_homOfLe_inter U V
  infer_instance

/-- The canonical identification of the two descriptions of `U ∩ V ∩ A`: as a subtype of `X`, and
as the part of the subspace `↥(U ∩ V)` lying in `A`.  This is the identification that Step 3 of
NOTES §20 needs in order to identify the composite
`subInclChain … ≫ chainComplexMap (smallInLift U V (U∩V)) ℤ` with the `inclChains`-factored form
(the two subtypes have the same elements but are *not* the same type). -/
def interSubHomeo (X : TopCat) (A U V : Set X) :
    TopCat.of ↥(U ∩ V ∩ A) ≅
      TopCat.of ↥((Subtype.val : ↥(U ∩ V) → X) ⁻¹' A) :=
  TopCat.isoOfHomeo
    { toFun := fun p => ⟨⟨(p : X), p.2.1.1, p.2.1.2⟩, p.2.2⟩
      invFun := fun q => ⟨(q.1 : X), ⟨⟨q.1.2.1, q.1.2.2⟩, q.2⟩⟩
      left_inv := fun p => by rfl
      right_inv := fun q => by rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }

@[simp] theorem interSubHomeo_hom_apply (X : TopCat) (A U V : Set X) (p : ↥(U ∩ V ∩ A)) :
    (((interSubHomeo X A U V).hom p : ↥(U ∩ V))) = ⟨(p : X), p.2.1.1, p.2.1.2⟩ := rfl

@[simp] theorem interSubHomeo_inv_apply (X : TopCat) (A U V : Set X)
    (q : ↥((Subtype.val : ↥(U ∩ V) → X) ⁻¹' A)) :
    (((interSubHomeo X A U V).inv q : X)) = (q.1 : X) := rfl

end

end Work.Cohomology
