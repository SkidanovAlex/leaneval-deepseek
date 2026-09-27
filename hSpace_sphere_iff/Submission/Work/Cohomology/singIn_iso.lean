import Mathlib
import Submission.Work.Cohomology.SingBridge
import Submission.Work.Cohomology.SingIn

/-!
# The singular simplices inside a subset

For a topological space `X` and a subset `W ⊆ X`, the subcomplex `singIn X W` of `Sing X`
consisting of the simplices whose image lies in `W` is isomorphic, as a simplicial set, to the
singular simplicial set `Sing W` of the subspace `W`.

The isomorphism is built explicitly on `n`-simplices: one direction corestricts a simplex of `X`
with image in `W` to a continuous map into `W`, and the other direction composes a continuous map
into `W` with the inclusion `W ↪ X`.  Both directions are natural transformations
(`phi0_naturality`, `psi0_naturality`) and they are mutually inverse
(`psi0_phi0`, `phi0_psi0`), so they assemble into an isomorphism of simplicial sets.
-/

open CategoryTheory Simplicial Opposite

namespace Work.Cohomology

noncomputable section

variable (X : TopCat.{0}) (W : Set X)

/-- The subcomplex `singIn X W`, as a simplicial set. -/
abbrev singInSSet : SSet.{0} := (Submission.Cohomology.singIn X W : SSet.{0})

/-- The singular simplicial set of the subspace `W`. -/
abbrev singW : SSet.{0} := TopCat.toSSet.obj (TopCat.of W)

/-- On `n`-simplices, corestrict a simplex of `X` whose image lies in `W` to a continuous map
into the subspace `W`. -/
def singInToSub (n : SimplexCategoryᵒᵖ) (σ : (singInSSet X W).obj n) : (singW X W).obj n :=
  (TopCat.toSSetObjEquivT (TopCat.of W) n).symm
    ⟨fun t => ⟨(TopCat.toSSetObjEquivT X n σ.val) t, σ.prop t⟩,
     Continuous.subtype_mk (TopCat.toSSetObjEquivT X n σ.val).continuous σ.prop⟩

/-- On `n`-simplices, compose a continuous map into the subspace `W` with the inclusion `W ↪ X`. -/
def subToSingIn (n : SimplexCategoryᵒᵖ) (τ : (singW X W).obj n) : (singInSSet X W).obj n :=
  ⟨(TopCat.toSSetObjEquivT X n).symm
      ⟨fun t => (TopCat.toSSetObjEquivT (TopCat.of W) n τ) t, by fun_prop⟩,
   fun t => by
     rw [Equiv.apply_symm_apply]
     exact ((TopCat.toSSetObjEquivT (TopCat.of W) n τ) t).2⟩

/-- The corestriction, read back through `toSSetObjEquivT`, has the expected underlying map. -/
lemma singInToSub_coe_apply (n : SimplexCategoryᵒᵖ) (σ : (singInSSet X W).obj n)
    (t : stdSimplex ℝ (Fin ((unop n).len + 1))) :
    ((TopCat.toSSetObjEquivT (TopCat.of W) n (singInToSub X W n σ)) t : ↑X) =
      (TopCat.toSSetObjEquivT X n σ.val) t :=
  (congrArg Subtype.val (by
    rw [singInToSub, Equiv.apply_symm_apply]
    rfl : (TopCat.toSSetObjEquivT (TopCat.of W) n (singInToSub X W n σ)) t =
      ⟨(TopCat.toSSetObjEquivT X n σ.val) t, σ.prop t⟩)).trans (Subtype.coe_mk _ _)

/-- The other direction, read back through `toSSetObjEquivT`, has the expected underlying map. -/
lemma subToSingIn_coe_apply (n : SimplexCategoryᵒᵖ) (τ : (singW X W).obj n)
    (t : stdSimplex ℝ (Fin ((unop n).len + 1))) :
    (TopCat.toSSetObjEquivT X n (subToSingIn X W n τ).val) t =
      ((TopCat.toSSetObjEquivT (TopCat.of W) n τ) t : ↑X) := by
  rw [subToSingIn, Equiv.apply_symm_apply]
  rfl

/-- Naturality of `toSSetObjEquivT` along a morphism of `SimplexCategoryᵒᵖ`. -/
lemma toSSetObjEquivT_map_apply {Y : TopCat.{0}} {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m)
    (x : (TopCat.toSSet.obj Y).obj n) (z : stdSimplex ℝ (Fin ((unop m).len + 1))) :
    (TopCat.toSSetObjEquivT Y m ((TopCat.toSSet.obj Y).map f x)) z
      = (TopCat.toSSetObjEquivT Y n x) (stdSimplex.map f.unop z) :=
  TopCat.toSSetObjEquivT_naturality_apply (X := Y) (f := f.unop) x z

/-- The underlying simplex of the image of `σ` under the subcomplex inclusion. -/
lemma singInSSet_map_val {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m)
    (σ : (singInSSet X W).obj n) :
    (((singInSSet X W).map f σ).val) = (TopCat.toSSet.obj X).map f σ.val := rfl

/-- The corestriction is natural in the simplex category. -/
lemma singInToSub_naturality {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m)
    (σ : (singInSSet X W).obj n) :
    singInToSub X W m ((singInSSet X W).map f σ)
      = (singW X W).map f (singInToSub X W n σ) := by
  apply (TopCat.toSSetObjEquivT (TopCat.of W) m).injective
  apply ContinuousMap.ext
  intro t
  apply Subtype.ext
  rw [singInToSub_coe_apply, toSSetObjEquivT_map_apply (Y := TopCat.of W) f
      (singInToSub X W n σ) t, singInToSub_coe_apply]
  rw [singInSSet_map_val]
  exact toSSetObjEquivT_map_apply (Y := X) f σ.val t

/-- The inclusion direction is natural in the simplex category. -/
lemma subToSingIn_naturality {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m)
    (τ : (singW X W).obj n) :
    subToSingIn X W m ((singW X W).map f τ)
      = (singInSSet X W).map f (subToSingIn X W n τ) := by
  apply Subtype.ext
  apply (TopCat.toSSetObjEquivT X m).injective
  apply ContinuousMap.ext
  intro t
  rw [subToSingIn_coe_apply, toSSetObjEquivT_map_apply (Y := TopCat.of W) f τ t,
    singInSSet_map_val, toSSetObjEquivT_map_apply (Y := X) f (subToSingIn X W n τ).val t,
    subToSingIn_coe_apply]

/-- The two directions are inverse; this is the `inv_hom_id` direction. -/
lemma subToSingIn_singInToSub (n : SimplexCategoryᵒᵖ) (σ : (singInSSet X W).obj n) :
    subToSingIn X W n (singInToSub X W n σ) = σ := by
  apply Subtype.ext
  apply (TopCat.toSSetObjEquivT X n).injective
  apply ContinuousMap.ext
  intro t
  rw [subToSingIn_coe_apply, singInToSub_coe_apply]

/-- The two directions are inverse; this is the `hom_inv_id` direction. -/
lemma singInToSub_subToSingIn (n : SimplexCategoryᵒᵖ) (τ : (singW X W).obj n) :
    singInToSub X W n (subToSingIn X W n τ) = τ := by
  apply (TopCat.toSSetObjEquivT (TopCat.of W) n).injective
  apply ContinuousMap.ext
  intro t
  apply Subtype.ext
  rw [singInToSub_coe_apply, subToSingIn_coe_apply]

/-- The simplices of `singIn X W` are the singular simplices of the subspace `W`. -/
def singInIso : (singInSSet X W) ≅ (singW X W) :=
  { hom :=
      { app := fun n => ↾(singInToSub X W n)
        naturality := by
          intro n m f
          ext σ
          exact singInToSub_naturality X W f σ }
    inv :=
      { app := fun n => ↾(subToSingIn X W n)
        naturality := by
          intro n m f
          ext τ
          exact subToSingIn_naturality X W f τ }
    hom_inv_id := by
      apply NatTrans.ext
      funext n
      ext σ
      simp only [NatTrans.comp_app, NatTrans.id_app]
      exact subToSingIn_singInToSub X W n σ
    inv_hom_id := by
      apply NatTrans.ext
      funext n
      ext τ
      simp only [NatTrans.comp_app, NatTrans.id_app]
      exact singInToSub_subToSingIn X W n τ }

/-- **The simplices of `singIn X W` are the singular simplices of the subspace `W`.**  For a
topological space `X` and a subset `W ⊆ X`, the subcomplex of `Sing X` consisting of the simplices
whose image lies in `W` is isomorphic to the singular simplicial set of `W` with the subspace
topology.

On `n`-simplices the isomorphism sends `σ` to the corestriction of `toSSetObjEquivT X (op ⦋n⦌) σ`
to `W`, using that its image lies in `W`; the inverse sends `τ` to the composite of `τ` with the
inclusion `W ↪ X`.  Continuity of the corestriction is `Continuous.subtype_mk`, and the two maps
are mutually inverse because a continuous map `Δⁿ → X` with image in `W` is the same thing as a
continuous map `Δⁿ → W`.  Naturality follows from `TopCat.toSSetObjEquivT_naturality_apply`, so the
two directions are natural transformations, and the pointwise inverses assemble into an
isomorphism of simplicial sets. -/
theorem singIn_iso (X : TopCat.{0}) (W : Set X) :
    Nonempty ((Submission.Cohomology.singIn X W : SSet.{0}) ≅ TopCat.toSSet.obj (TopCat.of W)) :=
  ⟨singInIso X W⟩

end

end Work.Cohomology
