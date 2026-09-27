import Mathlib
import Submission.Work.Cohomology.SmallSES
import Submission.Work.Homology.SimplexShim

namespace Work.Cohomology

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial
open Work.Cohomology

/-- The underlying singular simplex of the image of `a` under `smallLiftU`. -/
private lemma smallLiftU_val {X : TopCat} (U V : Set X) (n : SimplexCategoryᵒᵖ)
    (a : (TopCat.toSSet.obj (TopCat.of U)).obj n) :
    ((smallLiftU U V).app n a).val = (TopCat.toSSet.map (inclUX U)).app n a :=
  congrFun (congrArg (fun g => g.app n)
    (Subfunctor.lift_ι (TopCat.toSSet.map (inclUX U)) (range_inclUX_le U V))) a

/-- The underlying singular simplex of the image of `b` under `smallLiftV`. -/
private lemma smallLiftV_val {X : TopCat} (U V : Set X) (n : SimplexCategoryᵒᵖ)
    (b : (TopCat.toSSet.obj (TopCat.of V)).obj n) :
    ((smallLiftV U V).app n b).val = (TopCat.toSSet.map (inclVX V)).app n b :=
  congrFun (congrArg (fun g => g.app n)
    (Subfunctor.lift_ι (TopCat.toSSet.map (inclVX V)) (range_inclVX_le U V))) b

/-- If a simplex of `U` and a simplex of `V` have the same image under the two maps
`C_*(U) → C^{U,V}_*(X)` and `C_*(V) → C^{U,V}_*(X)`, then they both come from a simplex of
`U ∩ V`.  This is the pullback (fibre product) property of the pair of arms of the
Mayer–Vietoris short exact sequence. -/
theorem smallLift_pullback {X : TopCat} (U V : Set X) (n : SimplexCategoryᵒᵖ)
    (a : (TopCat.toSSet.obj (TopCat.of U)).obj n)
    (b : (TopCat.toSSet.obj (TopCat.of V)).obj n)
    (h : (smallLiftU U V).app n a = (smallLiftV U V).app n b) :
    ∃ c : (TopCat.toSSet.obj (TopCat.of ↥(U ∩ V))).obj n,
      (TopCat.toSSet.map (inclUVU U V)).app n c = a ∧
      (TopCat.toSSet.map (inclUVV U V)).app n c = b := by
  -- The two simplices have the same underlying singular simplex of `X`.
  have hval : (TopCat.toSSet.map (inclUX U)).app n a =
      (TopCat.toSSet.map (inclVX V)).app n b := by
    have h1 := congrArg Subtype.val h
    rw [smallLiftU_val, smallLiftV_val] at h1
    exact h1
  set A : C(stdSimplex ℝ (Fin (n.unop.len + 1)), TopCat.of U) :=
    Work.Homology.toSSetObjEquiv' (TopCat.of U) n a with hA
  set B : C(stdSimplex ℝ (Fin (n.unop.len + 1)), TopCat.of V) :=
    Work.Homology.toSSetObjEquiv' (TopCat.of V) n b with hB
  -- As continuous maps into `X`, `A` and `B` agree pointwise.
  have key : ∀ z, (A z).val = (B z).val := by
    intro z
    have h1 := toSSetObjEquiv_map_apply (inclUX U) n a z
    have h2 := toSSetObjEquiv_map_apply (inclVX V) n b z
    have h3 := congrArg (fun f : C(stdSimplex ℝ (Fin (n.unop.len + 1)), X) => f z)
      (congrArg (Work.Homology.toSSetObjEquiv' X n) hval)
    rw [h1, h2] at h3
    exact h3
  -- The common simplex factors through `U ∩ V`.
  set g : C(stdSimplex ℝ (Fin (n.unop.len + 1)), TopCat.of ↥(U ∩ V)) :=
    ⟨fun z => ⟨(A z).val, (A z).2, by rw [key z]; exact (B z).2⟩,
      Continuous.subtype_mk (continuous_subtype_val.comp A.continuous)
        (fun z => by
          change (A z).val ∈ U ∩ V
          exact ⟨(A z).2, by rw [key z]; exact (B z).2⟩)⟩ with hg
  refine ⟨(Work.Homology.toSSetObjEquiv' (TopCat.of ↥(U ∩ V)) n).symm g, ?_, ?_⟩
  · refine (Work.Homology.toSSetObjEquiv' (TopCat.of U) n).injective ?_
    rw [show Work.Homology.toSSetObjEquiv' (TopCat.of U) n a = A from hA.symm]
    apply ContinuousMap.ext
    intro z
    rw [toSSetObjEquiv_map_apply]
    rw [show Work.Homology.toSSetObjEquiv' (TopCat.of ↥(U ∩ V)) n
      ((Work.Homology.toSSetObjEquiv' (TopCat.of ↥(U ∩ V)) n).symm g) = g from
        Equiv.apply_symm_apply _ _]
    exact Subtype.ext rfl
  · refine (Work.Homology.toSSetObjEquiv' (TopCat.of V) n).injective ?_
    rw [show Work.Homology.toSSetObjEquiv' (TopCat.of V) n b = B from hB.symm]
    apply ContinuousMap.ext
    intro z
    rw [toSSetObjEquiv_map_apply]
    rw [show Work.Homology.toSSetObjEquiv' (TopCat.of ↥(U ∩ V)) n
      ((Work.Homology.toSSetObjEquiv' (TopCat.of ↥(U ∩ V)) n).symm g) = g from
        Equiv.apply_symm_apply _ _]
    exact Subtype.ext (key z)

end Work.Cohomology
