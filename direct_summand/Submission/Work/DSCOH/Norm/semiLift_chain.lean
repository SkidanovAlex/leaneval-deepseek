import Mathlib
import Submission.Work.DSCOH.Norm.SortSection
import Submission.Work.DSCOH.Norm.sign_sort_succAbove
import Submission.Work.DSCOH.Norm.semiProj_chain

/-!
Area DSCOH — the normalization comparison: `semiLift` is a chain map.

The signed sorting section `semiLift : semiT P U ⟶ (cechComplexFunctor U).obj P` (defined in
`Submission/Work/DSCOH/Norm/SortSection.lean`) commutes with the differentials:
`semiLift n ≫ d n (n+1) = semiD n ≫ semiLift (n+1)`.

Mathematically this is the "the stable sorting section is compatible with the Čech
differential" computation: deleting the `b`-th entry of a tuple and then signing is the same as
signing and then deleting the `σ⁻¹ b`-th entry of the sorted tuple, where `σ = Tuple.sort x`;
the sign comparison is `sortSign (del x b) = sortSign x * (-1)^(b + σ⁻¹ b)` and the
"restriction" morphisms agree because `Opens X` is a thin category.

All lemmas below are stated with the same (universe-polymorphic) binder style as the target
theorem so that they apply at the universe where `semiLift_chain` lives.
-/

namespace Work.DSCOH.Norm

open CategoryTheory Limits Opposite TopologicalSpace
open scoped BigOperators

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

/-! ## Scalar arithmetic -/

/-- The elementary scalar identity behind the sign comparison. -/
lemma negOne_pow_mul_shift (t : ℤ) (a c : ℕ) :
    (-1 : ℤ) ^ a * (t * (-1 : ℤ) ^ (a + c)) = (-1 : ℤ) ^ c * t := by
  rw [pow_add]
  have h1 : (-1 : ℤ) ^ a * (-1 : ℤ) ^ a = 1 := by rw [← mul_pow]; norm_num
  calc (-1 : ℤ) ^ a * (t * ((-1 : ℤ) ^ a * (-1 : ℤ) ^ c))
      = ((-1 : ℤ) ^ a * (-1 : ℤ) ^ a) * (t * (-1 : ℤ) ^ c) := by ring
    _ = 1 * (t * (-1 : ℤ) ^ c) := by rw [h1]
    _ = (-1 : ℤ) ^ c * t := by ring

/-! ## The sorting data of a deleted tuple -/

/-- `del` as a composition. -/
lemma del_eq_comp_aux {ι : Type*} [LinearOrder ι] {n : ℕ} (x : Fin (n + 2) → ι)
    (b : Fin (n + 2)) :
    del x b = x ∘ b.succAbove := rfl

/-- The stably sorted version of a tuple with the `b`-th entry deleted is the deletion at
position `σ⁻¹ b` of the stably sorted tuple, `σ = Tuple.sort x`. -/
lemma sortIdx_del_val_aux {ι : Type*} [LinearOrder ι] {n : ℕ} (x : Fin (n + 2) → ι)
    (b : Fin (n + 2)) :
    (sortIdx (del x b)).val = del (sortIdx x).val ((Tuple.sort x).symm b) := by
  rw [del_eq_comp_aux]
  funext i
  have h := congrFun (sort_comp_succAbove x b) i
  simp only [sortIdx, del_apply, Function.comp_apply] at h ⊢
  rw [h]

/-- The corresponding equality of `SemiIdx` elements. -/
lemma sortIdx_del_eq_aux {ι : Type*} [LinearOrder ι] {n : ℕ} (x : Fin (n + 2) → ι)
    (b : Fin (n + 2)) :
    sortIdx (del x b) =
      ⟨del (sortIdx x).val ((Tuple.sort x).symm b),
        monotone_del (sortIdx x).val ((Tuple.sort x).symm b) (sortIdx x).property⟩ :=
  Subtype.ext (sortIdx_del_val_aux x b)

/-- The sign attached to the stably sorted version of a tuple with the `b`-th entry deleted. -/
lemma sortSign_del_aux {ι : Type*} [LinearOrder ι] {n : ℕ} (x : Fin (n + 2) → ι)
    (b : Fin (n + 2)) :
    sortSign (del x b) =
      sortSign x * (-1 : ℤ) ^ ((b : ℕ) + (((Tuple.sort x).symm b : Fin (n + 2)) : ℕ)) := by
  have h := sign_sort_succAbove x b
  change ((Equiv.Perm.sign (Tuple.sort (del x b)) : ℤˣ) : ℤ) =
    ((Equiv.Perm.sign (Tuple.sort x) : ℤˣ) : ℤ) *
      (-1 : ℤ) ^ ((b : ℕ) + (((Tuple.sort x).symm b : Fin (n + 2)) : ℕ))
  rw [del_eq_comp_aux]
  exact h

/-! ## The component identity for the sorted deletion -/

/-- The `SemiIdx` version of `Work.DSCOH.Norm.pi_map_eq` (`projInclChain.lean`): two Čech
components whose tuples are equal, with restrictions starting at one and the same open, agree
because `Opens X` is a thin category. -/
lemma pi_map_eq_semi {X : Type*} [TopologicalSpace X] {A : Type*} [CommRing A]
    {ι : Type*} [Fintype ι] [LinearOrder ι]
    [CategoryTheory.Limits.HasProducts (ModuleCat A)]
    (P : CategoryTheory.Functor (Opposite (TopologicalSpace.Opens X)) (ModuleCat A))
    (U : ι → TopologicalSpace.Opens X) {n : ℕ} {z z' : SemiIdx ι n} (hz : z = z')
    {V : Opens X} (β : V ⟶ tupleOp U z.val) (β' : V ⟶ tupleOp U z'.val) :
    (CategoryTheory.Limits.Pi.π (fun w : SemiIdx ι n => tupleMod P U w.val) z :
        semiTerm P U n ⟶ tupleMod P U z.val) ≫ P.map β.op =
      (CategoryTheory.Limits.Pi.π (fun w : SemiIdx ι n => tupleMod P U w.val) z' :
        semiTerm P U n ⟶ tupleMod P U z'.val) ≫ P.map β'.op := by
  subst hz
  rw [Subsingleton.elim β β']

/-- **The component identity**: `sortRes` followed by `resDel` at the `b`-th entry equals
`resDel` at the sorted position `σ⁻¹ b` followed by `sortRes`.  Both sides restrict from
`tupleOp U x` to the open of the stably sorted deletion `(del x b) ∘ Tuple.sort (del x b)`, and
`Opens X` is a thin category. -/
theorem sortRes_resDel_aux {X : Type*} [TopologicalSpace X] {A : Type*} [CommRing A]
    {ι : Type*} [Fintype ι] [LinearOrder ι]
    [CategoryTheory.Limits.HasProducts (ModuleCat A)]
    (P : CategoryTheory.Functor (Opposite (TopologicalSpace.Opens X)) (ModuleCat A))
    (U : ι → TopologicalSpace.Opens X) {n : ℕ} (x : Fin (n + 2) → ι) (b : Fin (n + 2)) :
    (CategoryTheory.Limits.Pi.π (fun s : SemiIdx ι n => tupleMod P U s.val) (sortIdx (del x b)) :
        semiTerm P U n ⟶ tupleMod P U (sortIdx (del x b)).val) ≫
      sortRes P U (del x b) ≫ resDel P U x b =
    (CategoryTheory.Limits.Pi.π (fun s : SemiIdx ι n => tupleMod P U s.val)
        ⟨del (sortIdx x).val ((Tuple.sort x).symm b),
          monotone_del (sortIdx x).val ((Tuple.sort x).symm b) (sortIdx x).property⟩ :
        semiTerm P U n ⟶ tupleMod P U (del (sortIdx x).val ((Tuple.sort x).symm b))) ≫
      resDel P U (sortIdx x).val ((Tuple.sort x).symm b) ≫ sortRes P U x := by
  have hls : sortRes P U (del x b) ≫ resDel P U x b =
      P.map ((homOfLE (leOfHom (opDel U x b)) ≫ sortHom U (del x b)).op) := by
    rw [sortRes, resDel, ← P.map_comp, ← op_comp]
  have hrs : resDel P U (sortIdx x).val ((Tuple.sort x).symm b) ≫ sortRes P U x =
      P.map ((sortHom U x ≫
        homOfLE (leOfHom (opDel U (sortIdx x).val ((Tuple.sort x).symm b)))).op) := by
    rw [sortRes, resDel, ← P.map_comp, ← op_comp]
  rw [hls, hrs]
  exact pi_map_eq_semi P U (sortIdx_del_eq_aux x b) _ _

theorem semiLift_chain {X : Type*} [TopologicalSpace X] {A : Type*} [CommRing A]
    {ι : Type*} [Fintype ι] [LinearOrder ι]
    [CategoryTheory.Limits.HasProducts (ModuleCat A)]
    (P : CategoryTheory.Functor (Opposite (TopologicalSpace.Opens X)) (ModuleCat A))
    (U : ι → TopologicalSpace.Opens X) :
    ∀ n : ℕ, CategoryTheory.CategoryStruct.comp (Work.DSCOH.Norm.semiLift P U n)
        (((CategoryTheory.cechComplexFunctor U).obj P).d n (n + 1)) =
      CategoryTheory.CategoryStruct.comp (Work.DSCOH.Norm.semiD P U n)
        (Work.DSCOH.Norm.semiLift P U (n + 1)) := by
  intro n
  apply Pi.hom_ext (f := fun z : Fin (n + 2) → ι => tupleMod P U z)
  intro x
  have hL : (semiLift P U n ≫ ((cechComplexFunctor U).obj P).d n (n + 1)) ≫
        Pi.π (fun z : Fin (n + 2) → ι => tupleMod P U z) x
      = ∑ b : Fin (n + 2), (-1 : ℤ) ^ (b : ℕ) • (sortSign (del x b) •
          (Pi.π (fun s : SemiIdx ι n => tupleMod P U s.val) (sortIdx (del x b)) ≫
            sortRes P U (del x b) ≫ resDel P U x b)) := by
    conv_lhs => rw [Category.assoc]
    have hd : ((cechComplexFunctor U).obj P).d n (n + 1) ≫
          Pi.π (fun z : Fin (n + 2) → ι => tupleMod P U z) x
        = ∑ b : Fin (n + 2), (-1 : ℤ) ^ (b : ℕ) •
          (Pi.π (fun z : Fin (n + 1) → ι => tupleMod P U z) (del x b) ≫ resDel P U x b) := by
      rw [cechComplexFunctor_d_comp_gen P U n]
      exact Pi.lift_comp_π _ _
    rw [hd]
    simp only [Preadditive.comp_sum, Preadditive.comp_zsmul]
    refine Finset.sum_congr rfl fun b _ => ?_
    have hsl : semiLift P U n ≫ Pi.π (fun z : Fin (n + 1) → ι => tupleMod P U z) (del x b) =
        sortSign (del x b) • (Pi.π (fun s : SemiIdx ι n => tupleMod P U s.val)
          (sortIdx (del x b)) ≫ sortRes P U (del x b)) := by
      rw [semiLift]
      exact Pi.lift_comp_π _ _
    conv_lhs => rw [← Category.assoc]
    rw [hsl]
    simp only [Preadditive.zsmul_comp]
    rw [Category.assoc]
  have hR : (semiD P U n ≫ semiLift P U (n + 1)) ≫
        Pi.π (fun z : Fin (n + 2) → ι => tupleMod P U z) x
      = ∑ b : Fin (n + 2), (-1 : ℤ) ^ (b : ℕ) • (sortSign x •
          (Pi.π (fun s : SemiIdx ι n => tupleMod P U s.val)
              ⟨del (sortIdx x).val b, monotone_del (sortIdx x).val b (sortIdx x).property⟩ ≫
            resDel P U (sortIdx x).val b ≫ sortRes P U x)) := by
    conv_lhs => rw [Category.assoc]
    have hsl : semiLift P U (n + 1) ≫ Pi.π (fun z : Fin (n + 2) → ι => tupleMod P U z) x =
        sortSign x • (Pi.π (fun s : SemiIdx ι (n + 1) => tupleMod P U s.val)
          (sortIdx x) ≫ sortRes P U x) := by
      rw [semiLift]
      exact Pi.lift_comp_π _ _
    rw [hsl]
    simp only [Preadditive.comp_zsmul]
    conv_lhs => rw [← Category.assoc]
    have hsd : semiD P U n ≫
          Pi.π (fun s : SemiIdx ι (n + 1) => tupleMod P U s.val) (sortIdx x)
        = ∑ b : Fin (n + 2), (-1 : ℤ) ^ (b : ℕ) •
          (Pi.π (fun s : SemiIdx ι n => tupleMod P U s.val)
              ⟨del (sortIdx x).val b, monotone_del (sortIdx x).val b (sortIdx x).property⟩ ≫
            resDel P U (sortIdx x).val b) := by
      rw [semiD]
      exact Pi.lift_comp_π _ _
    rw [hsd]
    simp only [Preadditive.sum_comp, Preadditive.zsmul_comp, Finset.smul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [smul_comm, Category.assoc]
  rw [hL, hR]
  rw [show (∑ b : Fin (n + 2), (-1 : ℤ) ^ (b : ℕ) • (sortSign (del x b) •
          (Pi.π (fun s : SemiIdx ι n => tupleMod P U s.val) (sortIdx (del x b)) ≫
            sortRes P U (del x b) ≫ resDel P U x b)))
      = ∑ b : Fin (n + 2), (-1 : ℤ) ^ (b : ℕ) • (sortSign (del x b) •
          (Pi.π (fun s : SemiIdx ι n => tupleMod P U s.val)
              ⟨del (sortIdx x).val ((Tuple.sort x).symm b),
                monotone_del (sortIdx x).val ((Tuple.sort x).symm b)
                  (sortIdx x).property⟩ ≫
            resDel P U (sortIdx x).val ((Tuple.sort x).symm b) ≫ sortRes P U x))
      from Finset.sum_congr rfl fun b _ => by rw [sortRes_resDel_aux P U x b]]
  rw [show (∑ b : Fin (n + 2), (-1 : ℤ) ^ (b : ℕ) • (sortSign x •
          (Pi.π (fun s : SemiIdx ι n => tupleMod P U s.val)
              ⟨del (sortIdx x).val b, monotone_del (sortIdx x).val b
                (sortIdx x).property⟩ ≫
            resDel P U (sortIdx x).val b ≫ sortRes P U x)))
      = ∑ b : Fin (n + 2),
          (-1 : ℤ) ^ (((Tuple.sort x).symm b : Fin (n + 2)) : ℕ) • (sortSign x •
          (Pi.π (fun s : SemiIdx ι n => tupleMod P U s.val)
              ⟨del (sortIdx x).val ((Tuple.sort x).symm b),
                monotone_del (sortIdx x).val ((Tuple.sort x).symm b)
                  (sortIdx x).property⟩ ≫
            resDel P U (sortIdx x).val ((Tuple.sort x).symm b) ≫ sortRes P U x))
      from Fintype.sum_equiv (Tuple.sort x) _ _ (fun b => by rw [Equiv.symm_apply_apply])]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [smul_smul, smul_smul]
  rw [show (-1 : ℤ) ^ (b : ℕ) * sortSign (del x b) =
      (-1 : ℤ) ^ (((Tuple.sort x).symm b : Fin (n + 2)) : ℕ) * sortSign x from by
    rw [sortSign_del_aux x b]
    exact negOne_pow_mul_shift (sortSign x) (b : ℕ)
      (((Tuple.sort x).symm b : Fin (n + 2)) : ℕ)]

end Work.DSCOH.Norm
