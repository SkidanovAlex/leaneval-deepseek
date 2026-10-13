/-
Area DSCOH (curric-46) — the sorting homotopy `semiLift_homotopy`.

`Work.DSCOH.Norm.semiLift_homotopy` is the existence of a homotopy `h` (of cochain complexes,
`h n : X (n+1) ⟶ X n`) on Mathlib's unnormalized Čech complex of a finite family `U : ι → Opens X`
(`ι` linearly ordered) such that, in every degree,

* `d 0 1 ≫ h 0 + semiProj 0 ≫ semiLift 0 = 𝟙 (X 0)`, and
* `h n ≫ d n (n+1) + d (n+1) (n+2) ≫ h (n+1) + semiProj (n+1) ≫ semiLift (n+1) = 𝟙 (X (n+1))`.

This is Stacks Project, Tag 01FG, Lemma 20.23.6 (the first homotopy, Equation 20.23.6.1): the
"signed sorting" section `semiLift` of `semiProj` is homotopic to the identity of the unnormalized
Čech complex, via the explicit formula `h(s)_x = Σ_a (-1)^a sign(σ_a) s_{zA x a}`.

The homotopy is the sorting homotopy of `Submission.Work.DSCOH.Norm.FirstHomDefs` (the definitions
`zA`, `signA`, `readA`, `resA`, `dhTerm`, `hdTerm`).  The module category is pinned to
`ModuleCat.{max w u', v} A` (`u`, `v`, `w` the universes of `X`, `A`, `ι`, and `u'` a further
universe), which is exactly the universe at which the Čech complex, `semiProj`, `semiLift` and the
component terms live.

The verification of the two identities is the classical index computation:

* the `x`-components of `homAux k ≫ d k (k+1)` and `d (k+1) (k+2) ≫ homAux (k+1)` expand into the
  "delete then read" terms `hdTerm` and the "read then delete" terms `dhTerm`
  (`slh_homAux_d_comp`, `slh_d_homAux_comp`);
* the `dhTerm`-sum splits into a "matched" and a "leftover" part (`slh_sum_dhTerm_split`);
* the matched `dhTerm`s are matched, with opposite coefficients, against the `hdTerm`s
  (`Work.DSCOH.Norm.firstHom_matched`);
* the leftover `dhTerm`s telescope to `π_x - sortSign x • (π_{x ∘ sort x} ≫ sortRes x)`
  (`Work.DSCOH.Norm.firstHom_leftover`);
* the right hand side `(semiProj ≫ semiLift) ≫ π_x` is `sortSign x • (π_{x ∘ sort x} ≫ sortRes x)`
  (`slh_kappa_comp`).

The degree `0` identity is special: `d 0 1 ≫ h 0` vanishes (the two deletions of the repeated read
`zA x 0` of a `1`-tuple give the same term), while `semiProj 0 ≫ semiLift 0` is the identity
(every `1`-tuple is nondecreasing, so the sorting section is invertible in degree `0`); see
`slh_d_zero` and `slh_kappa_zero`.
-/
import Mathlib
import Submission.Work.DSCOH.Norm.FirstHomDefs
import Submission.Work.DSCOH.Norm.firstHom_leftover
import Submission.Work.DSCOH.Norm.firstHom_matched
import Submission.Work.DSCOH.Norm.SortSection
import Submission.Work.DSCOH.Norm.semiProj_chain

namespace Work.DSCOH.Norm

open CategoryTheory Limits Opposite TopologicalSpace
open scoped BigOperators

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

universe u v w u'

variable {X : Type u} [TopologicalSpace X] {A : Type v} [CommRing A]
variable {ι : Type w} [LinearOrder ι] [Fintype ι]
variable [HasProducts (ModuleCat.{max w u', v} A)]

/-! ## The sorting homotopy in the Čech spelling, and its component expansions -/

section Components

/-- The sorting homotopy of Stacks 01FG (20.23.6.1), with the source and target spelled as the
terms `((cechComplexFunctor U).obj P).X n` of Mathlib's unnormalized Čech complex: the
`x`-component is `Σ_a (-1)^a sign(σ_a) • (π_{zA x a} ≫ resA x a)`. -/
noncomputable def slhHom (P : (Opens X)ᵒᵖ ⥤ ModuleCat.{max w u', v} A) (U : ι → Opens X) (k : ℕ) :
    ((cechComplexFunctor U).obj P).X (k+1) ⟶ ((cechComplexFunctor U).obj P).X k :=
  Pi.lift fun x : Fin (k+1) → ι =>
    ∑ a : Fin (k+1), ((-1 : ℤ) ^ (a : ℕ) * signA x a) •
      (Pi.π (fun y : Fin (k+2) → ι => tupleMod P U y) (zA x a) ≫ resA P U x a)

lemma slhHom_comp (P : (Opens X)ᵒᵖ ⥤ ModuleCat.{max w u', v} A) (U : ι → Opens X) (k : ℕ)
    (x : Fin (k+1) → ι) :
    slhHom P U k ≫ Pi.π (fun y : Fin (k+1) → ι => tupleMod P U y) x =
      ∑ a : Fin (k+1), ((-1 : ℤ) ^ (a : ℕ) * signA x a) •
        (Pi.π (fun y : Fin (k+2) → ι => tupleMod P U y) (zA x a) ≫ resA P U x a) :=
  Pi.lift_comp_π _ _

/-- The `x`-component of the Čech differential, at the universe of `semiProj`/`semiLift`. -/
lemma slh_d_comp_pi (P : (Opens X)ᵒᵖ ⥤ ModuleCat.{max w u', v} A) (U : ι → Opens X) (m : ℕ)
    (x : Fin (m+2) → ι) :
    ((cechComplexFunctor U).obj P).d m (m+1) ≫
        Pi.π (fun y : Fin (m+2) → ι => tupleMod P U y) x
      = ∑ b : Fin (m+2), ((-1 : ℤ) ^ (b : ℕ)) •
          (Pi.π (fun y : Fin (m+1) → ι => tupleMod P U y) (del x b) ≫ resDel P U x b) := by
  have h := congrArg (fun t : ((cechComplexFunctor U).obj P).X m ⟶
      ((cechComplexFunctor U).obj P).X (m+1) =>
        t ≫ Pi.π (fun y : Fin (m+2) → ι => tupleMod P U y) x)
    (cechComplexFunctor_d_comp_gen P U m)
  rw [Pi.lift_comp_π] at h
  exact h

/-- The `x`-component of `slhHom k ≫ d k (k+1)`, expanded into the "delete then read" terms
`hdTerm`. -/
theorem slh_homAux_d_comp (P : (Opens X)ᵒᵖ ⥤ ModuleCat.{max w u', v} A) (U : ι → Opens X)
    (k : ℕ) (x : Fin (k+2) → ι) :
    (slhHom P U k ≫ ((cechComplexFunctor U).obj P).d k (k+1)) ≫
        Pi.π (fun y : Fin (k+2) → ι => tupleMod P U y) x
      = ∑ c : Fin (k+2), ∑ a : Fin (k+1), hdTerm P U x c a := by
  rw [Category.assoc]
  have h1 := slh_d_comp_pi P U k x
  rw [h1, CategoryTheory.Preadditive.comp_sum]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [CategoryTheory.Preadditive.comp_zsmul]
  have hstep : slhHom P U k ≫
      (Pi.π (fun y : Fin (k+1) → ι => tupleMod P U y) (del x c) ≫ resDel P U x c)
      = ∑ a : Fin (k+1), ((-1 : ℤ) ^ (a : ℕ) * signA (del x c) a) •
          (Pi.π (fun y : Fin (k+2) → ι => tupleMod P U y) (zA (del x c) a)
            ≫ resA P U (del x c) a ≫ resDel P U x c) := by
    rw [← Category.assoc, slhHom_comp, CategoryTheory.Preadditive.sum_comp]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [CategoryTheory.Preadditive.zsmul_comp, Category.assoc]
  rw [hstep, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [hdTerm, smul_smul,
    show (-1 : ℤ) ^ (c : ℕ) * ((-1 : ℤ) ^ (a : ℕ) * signA (del x c) a)
        = (-1 : ℤ) ^ ((c : ℕ) + (a : ℕ)) * signA (del x c) a by rw [pow_add]; ring]

/-- The `x`-component of `d (k+1) (k+2) ≫ slhHom (k+1)`, expanded into the "read then delete"
terms `dhTerm`. -/
theorem slh_d_homAux_comp (P : (Opens X)ᵒᵖ ⥤ ModuleCat.{max w u', v} A) (U : ι → Opens X)
    (k : ℕ) (x : Fin (k+2) → ι) :
    (((cechComplexFunctor U).obj P).d (k+1) (k+2) ≫ slhHom P U (k+1)) ≫
        Pi.π (fun y : Fin (k+2) → ι => tupleMod P U y) x
      = ∑ a : Fin (k+2), ∑ b : Fin (k+3), dhTerm P U x a b := by
  rw [Category.assoc]
  have hstep := slhHom_comp P U (k+1) x
  rw [hstep, CategoryTheory.Preadditive.comp_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [CategoryTheory.Preadditive.comp_zsmul]
  have h2 : ((cechComplexFunctor U).obj P).d (k+1) (k+2) ≫
      (Pi.π (fun y : Fin (k+3) → ι => tupleMod P U y) (zA x a) ≫ resA P U x a)
      = ∑ b : Fin (k+3), ((-1 : ℤ) ^ (b : ℕ)) •
          (Pi.π (fun y : Fin (k+2) → ι => tupleMod P U y) (del (zA x a) b)
            ≫ resDel P U (zA x a) b ≫ resA P U x a) := by
    have hd := slh_d_comp_pi P U (k+1) (zA x a)
    rw [← Category.assoc, hd, CategoryTheory.Preadditive.sum_comp]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [CategoryTheory.Preadditive.zsmul_comp, Category.assoc]
  rw [h2, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [dhTerm, smul_smul,
    show (-1 : ℤ) ^ (a : ℕ) * signA x a * (-1 : ℤ) ^ (b : ℕ)
        = (-1 : ℤ) ^ ((a : ℕ) + (b : ℕ)) * signA x a by rw [pow_add]; ring]

/-- The `x`-component of `semiProj (k+1) ≫ semiLift (k+1)`. -/
theorem slh_kappa_comp (P : (Opens X)ᵒᵖ ⥤ ModuleCat.{max w u', v} A) (U : ι → Opens X)
    (k : ℕ) (x : Fin (k+2) → ι) :
    (semiProj P U (k+1) ≫ semiLift P U (k+1)) ≫
        Pi.π (fun y : Fin (k+2) → ι => tupleMod P U y) x
      = sortSign x • (Pi.π (fun y : Fin (k+2) → ι => tupleMod P U y) (sortIdx x).val ≫
          sortRes P U x) := by
  rw [Category.assoc, semiLift_comp, CategoryTheory.Preadditive.comp_zsmul, ← Category.assoc,
    semiProj_comp_pi]

/-- **The splitting of the "read then delete" sum** into its leftover and matched parts. -/
theorem slh_sum_dhTerm_split (P : (Opens X)ᵒᵖ ⥤ ModuleCat.{max w u', v} A) (U : ι → Opens X)
    {k : ℕ} (x : Fin (k+2) → ι) :
    (∑ a : Fin (k+2), ∑ b : Fin (k+3), dhTerm P U x a b)
      = (∑ a : Fin (k+2), (dhTerm P U x a (Fin.castSucc a) + dhTerm P U x a (pos2A x a)))
        + (∑ a : Fin (k+2), ∑ b : Fin (k+3),
            if b = Fin.castSucc a ∨ b = pos2A x a then 0 else dhTerm P U x a b) := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  have hne : (Fin.castSucc a : Fin (k+3)) ≠ pos2A x a := by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_castSucc, pos2A] at hv
    omega
  rw [← Finset.sum_filter_add_sum_filter_not (s := (Finset.univ : Finset (Fin (k+3))))
      (p := fun b => b = Fin.castSucc a ∨ b = pos2A x a) (f := fun b => dhTerm P U x a b)]
  congr 1
  · have hf : (Finset.univ.filter (fun b : Fin (k+3) => b = Fin.castSucc a ∨ b = pos2A x a))
        = ({Fin.castSucc a, pos2A x a} : Finset (Fin (k+3))) := by
      ext b; simp [Finset.mem_insert, Finset.mem_singleton]
    rw [hf, Finset.sum_pair hne]
  · rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    by_cases h : b = Fin.castSucc a ∨ b = pos2A x a <;> simp [h]

/-- Two canonical `π ≫ P.map`-composites with equal source tuples agree: the category of open
subsets of `X` is thin. -/
lemma slh_pi_map_eq (P : (Opens X)ᵒᵖ ⥤ ModuleCat.{max w u', v} A) (U : ι → Opens X) {n : ℕ}
    {u₁ u₂ : Fin (n+1) → ι} (hu : u₁ = u₂) {W : (Opens X)ᵒᵖ}
    (α₁ : op (tupleOp U u₁) ⟶ W) (α₂ : op (tupleOp U u₂) ⟶ W) :
    Pi.π (fun y : Fin (n+1) → ι => tupleMod P U y) u₁ ≫ P.map α₁ =
      Pi.π (fun y : Fin (n+1) → ι => tupleMod P U y) u₂ ≫ P.map α₂ := by
  subst hu
  rw [Subsingleton.elim α₁ α₂]

end Components

/-! ## The degree `0` identities -/

section DegreeZero

variable (P : (Opens X)ᵒᵖ ⥤ ModuleCat.{max w u', v} A) (U : ι → Opens X)

/-- Every function out of `Fin 1` is nondecreasing. -/
lemma monotone_finOne (x : Fin 1 → ι) : Monotone x :=
  fun i j _ => le_of_eq (congrArg x (Fin.ext (by
    have h1 := i.isLt; have h2 := j.isLt; omega)))

/-- The sign of the sorting permutation of a `1`-tuple is `1`. -/
@[simp] lemma sortSign_finOne (x : Fin 1 → ι) : sortSign x = 1 :=
  sortSign_of_monotone x (monotone_finOne x)

/-- The sign `signA x a` of the `a`-th partial sorting permutation of a `1`-tuple is `1`. -/
@[simp] lemma signA_finOne (x : Fin 1 → ι) (a : Fin 1) : signA x a = 1 := by
  have h : sigmaAPerm x a = 1 := by
    apply Equiv.ext
    intro i
    show sigmaAPerm x a i = i
    apply Fin.ext
    have h1 := (sigmaAPerm x a i).isLt
    have h2 := i.isLt
    omega
  rw [signA, h]
  simp

/-- Sorting a `1`-tuple does nothing. -/
lemma comp_sort_self (x : Fin 1 → ι) : x ∘ Tuple.sort x = x := by
  rw [← sortIdx_val (x := x)]
  have h := sortIdx_of_monotone x (monotone_finOne x)
  exact congrArg (fun s : SemiIdx ι 0 => s.val) h

/-- The `x`-component of `sortRes` is the identity projection: sorting a `1`-tuple does nothing
and the canonical comparison is the comparison of a module with itself. -/
lemma slh_pi_sortRes (x : Fin 1 → ι) :
    Pi.π (fun y : Fin 1 → ι => tupleMod P U y) (x ∘ Tuple.sort x) ≫ sortRes P U x
      = Pi.π (fun y : Fin 1 → ι => tupleMod P U y) x := by
  have hsort : x ∘ Tuple.sort x = x := comp_sort_self x
  have hmap : P.map (𝟙 (op (tupleOp U x))) = 𝟙 (tupleMod P U x) := by
    rw [P.map_id]
    rfl
  have key := slh_pi_map_eq (u₁ := x ∘ Tuple.sort x) (u₂ := x) P U hsort
    (sortHom U x).op (𝟙 (op (tupleOp U x)))
  rw [hmap, Category.comp_id] at key
  change Pi.π (fun y : Fin 1 → ι => tupleMod P U y) (x ∘ Tuple.sort x) ≫
      P.map (sortHom U x).op = Pi.π (fun y : Fin 1 → ι => tupleMod P U y) x
  exact key

/-- In degree `0` the sorting section is a two-sided inverse of `semiProj`: every `1`-tuple is
nondecreasing, so `semiProj 0 ≫ semiLift 0 = 𝟙`. -/
theorem slh_kappa_zero :
    semiProj P U 0 ≫ semiLift P U 0 = 𝟙 (((cechComplexFunctor U).obj P).X 0) := by
  apply Pi.hom_ext (f := fun y : Fin 1 → ι => tupleMod P U y)
  intro x
  rw [Category.assoc, semiLift_comp, CategoryTheory.Preadditive.comp_zsmul, ← Category.assoc,
    semiProj_comp_pi, Category.id_comp]
  change sortSign x • (Pi.π (fun y : Fin 1 → ι => tupleMod P U y) (x ∘ Tuple.sort x) ≫
      sortRes P U x) = Pi.π (fun y : Fin 1 → ι => tupleMod P U y) x
  rw [sortSign_finOne x, one_smul]
  exact slh_pi_sortRes P U x

/-- The two deletions of the `0`-th read of a `1`-tuple give the same tuple. -/
lemma del_zA_zero_eq (x : Fin 1 → ι) :
    del (zA x 0) 0 = del (zA x 0) 1 := by
  have hy : zA x 0 = fun _ => x (readA x 0 0) := by
    funext p
    apply congrArg x
    apply Fin.ext
    have h1 := (readA x 0 p).isLt
    have h2 := (readA x 0 0).isLt
    omega
  funext a
  rw [del_apply, del_apply, hy]

/-- The two "read then delete then restrict" terms of the `0`-th read of a `1`-tuple are equal. -/
lemma slh_T_eq (x : Fin 1 → ι) :
    Pi.π (fun w : Fin 1 → ι => tupleMod P U w) (del (zA x 0) 0) ≫
        resDel P U (zA x 0) 0 ≫ resA P U x 0
      = Pi.π (fun w : Fin 1 → ι => tupleMod P U w) (del (zA x 0) 1) ≫
        resDel P U (zA x 0) 1 ≫ resA P U x 0 := by
  have hdel : del (zA x 0) 0 = del (zA x 0) 1 := del_zA_zero_eq x
  have h1 : resDel P U (zA x 0) 0 ≫ resA P U x 0
      = P.map ((opDel U (zA x 0) 0).op ≫ (opZ U x 0).op) := by
    rw [resDel_eq, resA, ← P.map_comp]
  have h2 : resDel P U (zA x 0) 1 ≫ resA P U x 0
      = P.map ((opDel U (zA x 0) 1).op ≫ (opZ U x 0).op) := by
    rw [resDel_eq, resA, ← P.map_comp]
  rw [h1, h2]
  exact slh_pi_map_eq P U hdel ((opDel U (zA x 0) 0).op ≫ (opZ U x 0).op)
    ((opDel U (zA x 0) 1).op ≫ (opZ U x 0).op)

/-- In degree `0` the composite `d 0 1 ≫ h 0` vanishes: the two summands of the differential at
the repeated read `zA x 0` are equal. -/
theorem slh_d_zero :
    ((cechComplexFunctor U).obj P).d 0 1 ≫ slhHom P U 0 = 0 := by
  apply Pi.hom_ext (f := fun y : Fin 1 → ι => tupleMod P U y)
  intro x
  rw [zero_comp]
  have h1 : slhHom P U 0 ≫ Pi.π (fun y : Fin 1 → ι => tupleMod P U y) x
      = Pi.π (fun y : Fin 2 → ι => tupleMod P U y) (zA x 0) ≫ resA P U x 0 := by
    rw [slhHom_comp, Fin.sum_univ_one]
    have hc : ((-1 : ℤ) ^ (((0 : Fin 1) : ℕ)) * signA x (0 : Fin 1)) = 1 := by
      rw [show (((0 : Fin 1) : ℕ)) = 0 from rfl, pow_zero, one_mul]
      exact signA_finOne x 0
    rw [hc, one_smul]
  have h2 : ((cechComplexFunctor U).obj P).d 0 1 ≫
      (Pi.π (fun y : Fin 2 → ι => tupleMod P U y) (zA x 0) ≫ resA P U x 0) = 0 := by
    rw [← Category.assoc]
    have hd := slh_d_comp_pi P U 0 (zA x 0)
    rw [hd, CategoryTheory.Preadditive.sum_comp, Fin.sum_univ_two,
      CategoryTheory.Preadditive.zsmul_comp, CategoryTheory.Preadditive.zsmul_comp, Category.assoc,
      Category.assoc]
    have hc0 : (-1 : ℤ) ^ (((0 : Fin 2) : ℕ)) = 1 := by simp
    have hc1 : (-1 : ℤ) ^ (((1 : Fin 2) : ℕ)) = -1 := by norm_num
    rw [hc0, hc1, one_zsmul, neg_one_zsmul, ← sub_eq_add_neg]
    exact sub_eq_zero.mpr (slh_T_eq P U x)
  calc (((cechComplexFunctor U).obj P).d 0 1 ≫ slhHom P U 0) ≫
        Pi.π (fun y : Fin 1 → ι => tupleMod P U y) x
      = ((cechComplexFunctor U).obj P).d 0 1 ≫
          (slhHom P U 0 ≫ Pi.π (fun y : Fin 1 → ι => tupleMod P U y) x) :=
        Category.assoc _ _ _
    _ = ((cechComplexFunctor U).obj P).d 0 1 ≫
          (Pi.π (fun y : Fin 2 → ι => tupleMod P U y) (zA x 0) ≫ resA P U x 0) := by
        rw [h1]
    _ = 0 := h2

end DegreeZero

/-! ## The main theorem -/

theorem semiLift_homotopy {X : Type*} [TopologicalSpace X] {A : Type*} [CommRing A]
    {ι : Type*} [Fintype ι] [LinearOrder ι]
    [CategoryTheory.Limits.HasProducts (ModuleCat A)]
    (P : CategoryTheory.Functor (Opposite (TopologicalSpace.Opens X)) (ModuleCat A))
    (U : ι → TopologicalSpace.Opens X) :
    ∃ h : ∀ n : ℕ, ((CategoryTheory.cechComplexFunctor U).obj P).X (n + 1) ⟶
        ((CategoryTheory.cechComplexFunctor U).obj P).X n,
      ((CategoryTheory.CategoryStruct.comp
            (((CategoryTheory.cechComplexFunctor U).obj P).d 0 1) (h 0) +
          CategoryTheory.CategoryStruct.comp (Work.DSCOH.Norm.semiProj P U 0)
            (Work.DSCOH.Norm.semiLift P U 0) =
        CategoryTheory.CategoryStruct.id (((CategoryTheory.cechComplexFunctor U).obj P).X 0))) ∧
      (∀ n : ℕ,
        CategoryTheory.CategoryStruct.comp (h n) (((CategoryTheory.cechComplexFunctor U).obj P).d n (n + 1)) +
            CategoryTheory.CategoryStruct.comp
              (((CategoryTheory.cechComplexFunctor U).obj P).d (n + 1) (n + 2)) (h (n + 1)) +
          CategoryTheory.CategoryStruct.comp (Work.DSCOH.Norm.semiProj P U (n + 1))
            (Work.DSCOH.Norm.semiLift P U (n + 1)) =
        CategoryTheory.CategoryStruct.id (((CategoryTheory.cechComplexFunctor U).obj P).X (n + 1))) := by
  refine ⟨fun n => slhHom P U n, ?_, ?_⟩
  · -- degree `0`: `d 0 1 ≫ h 0 = 0` and `semiProj 0 ≫ semiLift 0 = 𝟙`
    simp only []
    rw [slh_d_zero P U, slh_kappa_zero P U, zero_add]
  · -- degree `n+1`
    intro n
    apply Pi.hom_ext (f := fun y : Fin (n+2) → ι => tupleMod P U y)
    intro x
    rw [CategoryTheory.Preadditive.add_comp, CategoryTheory.Preadditive.add_comp,
      slh_homAux_d_comp P U n x, slh_d_homAux_comp P U n x, slh_kappa_comp P U n x,
      slh_sum_dhTerm_split P U x, Category.id_comp]
    -- the matched part cancels against the "delete then read" sum, the leftover part is the
    -- right hand side
    have hm : (∑ c : Fin (n+2), ∑ a' : Fin (n+1), hdTerm P U x c a')
        + (∑ a : Fin (n+2), ∑ b : Fin (n+3),
            if b = Fin.castSucc a ∨ b = pos2A x a then 0 else dhTerm P U x a b) = 0 :=
      (add_comm _ _).trans (firstHom_matched P U x)
    have hl := firstHom_leftover P U x
    simp only [sortIdx_val]
    rw [hl]
    calc (∑ c : Fin (n+2), ∑ a' : Fin (n+1), hdTerm P U x c a')
          + ((Pi.π (fun y : Fin (n+2) → ι => tupleMod P U y) x
                - sortSign x • (Pi.π (fun y : Fin (n+2) → ι => tupleMod P U y)
                    (x ∘ Tuple.sort x) ≫ sortRes P U x))
              + (∑ a : Fin (n+2), ∑ b : Fin (n+3),
                  if b = Fin.castSucc a ∨ b = pos2A x a then 0 else dhTerm P U x a b))
          + sortSign x • (Pi.π (fun y : Fin (n+2) → ι => tupleMod P U y) (x ∘ Tuple.sort x)
              ≫ sortRes P U x)
        = ((∑ c : Fin (n+2), ∑ a' : Fin (n+1), hdTerm P U x c a')
              + (∑ a : Fin (n+2), ∑ b : Fin (n+3),
                  if b = Fin.castSucc a ∨ b = pos2A x a then 0 else dhTerm P U x a b))
            + ((Pi.π (fun y : Fin (n+2) → ι => tupleMod P U y) x
                  - sortSign x • (Pi.π (fun y : Fin (n+2) → ι => tupleMod P U y)
                      (x ∘ Tuple.sort x) ≫ sortRes P U x))
              + sortSign x • (Pi.π (fun y : Fin (n+2) → ι => tupleMod P U y)
                  (x ∘ Tuple.sort x) ≫ sortRes P U x)) := by abel
      _ = 0 + Pi.π (fun y : Fin (n+2) → ι => tupleMod P U y) x := by
            rw [hm, sub_add_cancel]
      _ = Pi.π (fun y : Fin (n+2) → ι => tupleMod P U y) x := by simp

end Work.DSCOH.Norm
