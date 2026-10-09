import Mathlib
import Submission.Commons.RepresentationTheory.GroupCohomology.barComplex_res_comp_pi

/-!
# Group change on the bar complex

For `f : H →* G`, the natural map `(h₁,...,hₙ) ⊗ k[H] → (fh₁,...,fhₙ) ⊗ k[G]` is a morphism of
`H`-representations `barComplex k H n ⟶ res f (barComplex k G n)`.  This file records it together
with its evaluation on the standard generators and its compatibility with the differentials.
-/

open CategoryTheory Limits
open scoped MonoidAlgebra

namespace SSGRoute.PTExt

noncomputable section

variable (k : Type) [CommRing k] (G H : Type) [Group G] [Group H]

/-- The `n`-th component of the group-change map on bar complexes. -/
noncomputable def barChange (f : H →* G) (n : ℕ) :
    Rep.free k H (Fin n → H) ⟶ (Rep.resFunctor f).obj (Rep.free k G (Fin n → G)) :=
  Rep.freeLift (k := k) (G := H) (α := Fin n → H)
    (A := (Rep.resFunctor f).obj (Rep.free k G (Fin n → G)))
    (fun y : Fin n → H =>
      (Finsupp.single (fun i => f (y i)) (MonoidAlgebra.single (1 : G) (1 : k)) :
        Rep.free k G (Fin n → G)))

@[simp]
lemma barChange_apply (f : H →* G) (n : ℕ) (y : Fin n → H) (h : H) (r : k) :
    (barChange k G H f n).hom (Finsupp.single y (MonoidAlgebra.single h r)) =
      (Finsupp.single (fun i => f (y i)) (MonoidAlgebra.single (f h) r) :
        Rep.free k G (Fin n → G)) := by
  simp only [barChange, Rep.freeLift, Rep.hom_ofHom,
    Representation.freeLift_single_single, MonoidHom.comp_apply,
    Representation.free_single_single, mul_one, Finsupp.smul_single, MonoidAlgebra.smul_single']

lemma barChange_chain (f : H →* G) (n : ℕ) :
    barChange k G H f (n + 1) ≫ (Rep.resFunctor f).map (Rep.barComplex.d k G n) =
      Rep.barComplex.d k H n ≫ barChange k G H f n := by
  apply Rep.free_ext
  intro y
  rw [Rep.hom_comp, Rep.hom_comp]
  simp only [Representation.IntertwiningMap.comp_apply]
  rw [Rep.resMap_hom_apply]
  rw [barChange_apply, map_one]
  rw [Rep.barComplex.d_single, Rep.barComplex.d_single, map_add, map_sum]
  rw [barChange_apply, add_left_cancel_iff]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [barChange_apply, map_one]
  congr 1
  exact (Fin.comp_contractNth (· * ·) (· * ·) (fun x y => map_mul f x y) j y).symm

/-- Group change as a morphism of bar complexes. -/
noncomputable def barHom (f : H →* G) :
    (Rep.barComplex k H) ⟶
      ((Rep.resFunctor f).mapHomologicalComplex (ComplexShape.down ℕ)).obj (Rep.barComplex k G) where
  f n := barChange k G H f n
  comm' i j hij := by
    obtain rfl : i = j + 1 := hij.symm
    simp only [Functor.mapHomologicalComplex_obj_d, ChainComplex.of_d]
    exact barChange_chain k G H f j

/-- The identity `k ⟶ k` from the trivial `H`-module to the restriction of the trivial
`G`-module (the `G`- and `H`-trivial structures agree on `k`). -/
def unitChange (f : H →* G) : Rep.trivial k H k ⟶ (Rep.resFunctor f).obj (Rep.trivial k G k) :=
  Rep.ofHom ⟨LinearMap.id, fun _ => rfl⟩


open Commons.RepresentationTheory.GroupCohomology in
set_option maxHeartbeats 800000 in
/-- **Step 1 of `E0B_ROADMAP.md`.**  The group-change chain map `barHom` is compatible with the
augmentations of the bar resolutions of `H` and `G`.  This is the `hφ` hypothesis of
`mapExtAddHom_extMk` at `R = barResolution k G`, `R' = barResolution k H`, `φ = barHom k G H f`,
`g' = unitChange f`. -/
theorem barHom_augmentation (f : H →* G) :
    barHom k G H f ≫
        ((Rep.resFunctor f).mapHomologicalComplex (ComplexShape.down ℕ)).map
          (Rep.barResolution k G).π
        ≫ (HomologicalComplex.singleMapHomologicalComplex (Rep.resFunctor f)
              (ComplexShape.down ℕ) 0).hom.app (Rep.trivial k G k)
      = (Rep.barResolution k H).π ≫
          (ChainComplex.single₀ (Rep k H)).map (unitChange k G H f) := by
  apply HomologicalComplex.to_single_hom_ext (j := 0)
  simp only [HomologicalComplex.comp_f]
  rw [ChainComplex.single₀_map_f_zero]
  rw [singleMapHomologicalComplex_f_zero]
  simp only [Category.comp_id]
  apply Rep.free_ext
  intro x
  change (Rep.barResolution k G).π.f 0
      ((barChange k G H f 0) (Finsupp.single x (MonoidAlgebra.single (1 : H) (1 : k))))
    = unitChange k G H f
        ((Rep.barResolution k H).π.f 0 (Finsupp.single x (MonoidAlgebra.single (1 : H) (1 : k))))
  rw [barChange_apply]
  simp only [map_one]
  rw [barResolution_pi0_apply, unitChange]
  simp only [Rep.hom_ofHom, Representation.IntertwiningMap.coe_mk, LinearMap.id_apply]
  rw [barResolution_pi0_apply]
  rfl

end

end SSGRoute.PTExt
