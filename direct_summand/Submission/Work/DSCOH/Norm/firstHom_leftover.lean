/-
Area DSCOH (curric-46) — the normalization comparison: the *leftover* of the sorting homotopy.

This file completes the verification of the sorting homotopy of Stacks 01FG, Equation 20.23.6.1
(`Work.DSCOH.Norm.firstHom`, `Submission/Work/DSCOH/Norm/FirstHomDefs.lean`) by proving that the
terms of `d (k+1) (k+2) ≫ firstHom (k+1)` which "survive" the matching against
`firstHom k ≫ d k (k+1)` -- namely the two terms `dhTerm x a (a)` and `dhTerm x a (pos2A x a)` of
each slot `a`, whose read `zA x a` repeats its double point -- sum up to the component of
`𝟙 - semiProj ≫ semiLift`:

  `Σ_a (dhTerm x a (Fin.castSucc a) + dhTerm x a (pos2A x a)) = π_x - sortSign x • (π_{x∘σ} ≫ sortRes x)`.

The two surviving terms of the slot `a` cancel against the first surviving term of the slot `a+1`:
the tuples `del (zA x a) (pos2A x a)` and `del (zA x (a+1)) (a+1)` agree (deleting the second copy
of the double point of the `a`-th read is the same as deleting the first copy of the `(a+1)`-st
read), and the corresponding coefficients `(-1)^{a + pos2A x a} signA x a` and `- signA x (a+1)`
agree.  This telescopes, leaving the two end terms, which are exactly `π_x` and
`- sortSign x • (π_{x∘σ} ≫ sortRes x)`.
-/
import Mathlib
import Submission.Work.DSCOH.Norm.FirstHomDefs
import Submission.Work.DSCOH.Norm.SortSection
import Submission.Work.DSCOH.Norm.sortRes_resDel
import Submission.Work.DSCOH.Norm.TelIdx2.telIdx
import Submission.Work.DSCOH.Norm.TelSign.telescopeSign

namespace Work.DSCOH.Norm

open CategoryTheory Limits Opposite TopologicalSpace
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

universe u v w

variable {X : Type u} [TopologicalSpace X] {A : Type v} [CommRing A]
variable {ι : Type w} [LinearOrder ι] [Fintype ι] [HasProducts (ModuleCat A)]

/-! ## Elementary facts about the sorting data

The two "end point" computations of the sorting homotopy: the read at slot `0` duplicates the
smallest value in front of `x`, and the read at the last slot duplicates the largest value at the
end.  They are proved here (in the `Leftover` namespace) so that this module depends only on
`FirstHomDefs`. -/

namespace Leftover

/-- The increasing enumeration of the complement of `headVal x 0` (the empty set) is the
identity. -/
lemma tailEmb_zero {k : ℕ} (x : Fin (k+2) → ι) (m : Fin (k+2)) : tailEmb x 0 m = m := by
  rw [tailEmb]
  have hmem : ∀ m : Fin (k+2-0), m ∈ (headVal x (0 : Fin (k+2)))ᶜ := by
    intro m
    rw [Finset.mem_compl, headVal]
    simp
  have h := Finset.orderEmbOfFin_unique (compl_card x (0 : Fin (k+2))) hmem (strictMono_id)
  exact (congrFun h m).symm

/-- `sigmaA x 0` agrees with `Tuple.sort x` below `0` and is increasing on the whole of
`Fin (k+2)`, i.e. it is the identity. -/
lemma sigmaA_zero {k : ℕ} (x : Fin (k+2) → ι) : sigmaA x 0 = id := by
  funext j
  rw [sigmaA]
  rw [dite_eq_right (by simp : ¬ ((j : ℕ) < ((0 : Fin (k+2)) : ℕ))), id_eq]
  exact tailEmb_zero x _

lemma sigmaAPerm_zero {k : ℕ} (x : Fin (k+2) → ι) : sigmaAPerm x 0 = 1 := by
  apply Equiv.ext
  intro j
  rw [sigmaAPerm_apply, sigmaA_zero]
  rfl

lemma signA_zero {k : ℕ} (x : Fin (k+2) → ι) : signA x 0 = 1 := by
  rw [signA, sigmaAPerm_zero]
  simp

/-- Reading at slot `0` and forgetting the leading `σ(0)` is the identity: the read at slot `0`
reproduces `x` with the `0`-th smallest entry duplicated at the front. -/
lemma readA_zero {k : ℕ} (x : Fin (k+2) → ι) :
    readA x 0 ∘ (Fin.succAbove (0 : Fin (k+3))) = id := by
  rw [Fin.succAbove_zero]
  funext p
  rw [Function.comp_apply,
    readA_tail x 0 (p := Fin.succ p) (by simp), id_eq]
  exact tailEmb_zero x _

/-- The tuple of the first leftover term of the slot `0` is `x`. -/
lemma del_zA_zero {k : ℕ} (x : Fin (k+2) → ι) :
    del (zA x 0) (Fin.castSucc (0 : Fin (k+2))) = x := by
  haveI : NeZero (k+2) := ⟨by omega⟩
  have h0 : Fin.castSucc (0 : Fin (k+2)) = (0 : Fin (k+3)) := Fin.castSucc_zero
  rw [h0]
  funext j
  have h := congrFun (readA_zero x) j
  simp only [Function.comp_apply, id_eq] at h
  simpa only [del_apply, zA_apply] using congrArg x h

/-- At the last slot, the complement of the head values is the singleton of the largest value
`Tuple.sort x (Fin.last (k+1))`. -/
lemma compl_last {k : ℕ} (x : Fin (k+2) → ι) :
    (headVal x (Fin.last (k+1)))ᶜ = {Tuple.sort x (Fin.last (k+1))} := by
  refine Finset.eq_singleton_iff_unique_mem.mpr ⟨sortA_mem_compl x _, ?_⟩
  intro b hb
  by_contra hne
  have hsub : ({b, Tuple.sort x (Fin.last (k+1))} : Finset (Fin (k+2))) ⊆
      (headVal x (Fin.last (k+1)))ᶜ := by
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact hb
    · rw [Finset.mem_singleton] at hy; subst hy; exact sortA_mem_compl x _
  have h2 := Finset.card_le_card hsub
  rw [Finset.card_pair hne, compl_card, Fin.val_last] at h2
  omega

lemma rankA_last {k : ℕ} (x : Fin (k+2) → ι) : rankA x (Fin.last (k+1)) = 0 := by
  rw [rankA, compl_last, Finset.filter_singleton]
  simp

/-- The second position of the double point of the last read is the last position. -/
lemma pos2A_last {k : ℕ} (x : Fin (k+2) → ι) :
    pos2A x (Fin.last (k+1)) = Fin.last (k+2) := by
  rw [pos2A]
  apply Fin.ext
  simp [rankA_last, Fin.val_last]

lemma tailEmb_last_zero {k : ℕ} (x : Fin (k+2) → ι) :
    tailEmb x (Fin.last (k+1)) ⟨0, by rw [Fin.val_last]; omega⟩ =
      Tuple.sort x (Fin.last (k+1)) := by
  obtain ⟨_, huniq⟩ := Finset.eq_singleton_iff_unique_mem.mp (compl_last x)
  have h := Finset.orderEmbOfFin_mem (headVal x (Fin.last (k+1)))ᶜ (compl_card x _)
    (⟨0, by omega⟩ : Fin ((k+2) - (k+1)))
  rw [tailEmb]
  exact huniq _ h

/-- At the last slot `sigmaA` is `Tuple.sort` itself. -/
lemma sigmaA_last {k : ℕ} (x : Fin (k+2) → ι) :
    sigmaA x (Fin.last (k+1)) = Tuple.sort x := by
  funext j
  rw [sigmaA]
  split_ifs with hj
  · rfl
  · have hj' : j = Fin.last (k+1) := by
      apply Fin.ext
      have hj2 : ((j:ℕ) < k+2) := j.isLt
      have hj3 : ((Fin.last (k+1) : Fin (k+2)) : ℕ) = k+1 := Fin.val_last (k+1)
      have hj4 : ¬ ((j:ℕ) < ((Fin.last (k+1) : Fin (k+2)) : ℕ)) := hj
      omega
    subst hj'
    obtain ⟨_, huniq⟩ := Finset.eq_singleton_iff_unique_mem.mp (compl_last x)
    have h := Finset.orderEmbOfFin_mem (headVal x (Fin.last (k+1)))ᶜ (compl_card x _)
      (⟨↑(Fin.last (k+1)) - ↑(Fin.last (k+1)), by rw [Fin.val_last]; omega⟩ :
        Fin ((k+2) - (k+1)))
    rw [tailEmb]
    exact huniq _ h

lemma sigmaAPerm_last {k : ℕ} (x : Fin (k+2) → ι) :
    sigmaAPerm x (Fin.last (k+1)) = Tuple.sort x := by
  apply Equiv.ext
  intro j
  rw [sigmaAPerm_apply, sigmaA_last]

lemma signA_last {k : ℕ} (x : Fin (k+2) → ι) : signA x (Fin.last (k+1)) = sortSign x := by
  rw [signA, sortSign, sigmaAPerm_last]

/-- Reading at the last slot and deleting the second copy of the largest value gives the sorted
tuple. -/
lemma readA_last {k : ℕ} (x : Fin (k+2) → ι) :
    readA x (Fin.last (k+1)) ∘ (Fin.succAbove (pos2A x (Fin.last (k+1)))) = Tuple.sort x := by
  rw [pos2A_last, Fin.succAbove_last]
  funext p
  rw [Function.comp_apply]
  rw [readA_head x (Fin.last (k+1)) (p := Fin.castSucc p)
    (by have := p.isLt; simp only [Fin.val_castSucc, Fin.val_last]; omega)]
  exact congrArg (Tuple.sort x) (Fin.ext (by simp))

/-- The tuple of the second leftover term of the last slot is `x ∘ σ`. -/
lemma del_zA_last {k : ℕ} (x : Fin (k+2) → ι) :
    del (zA x (Fin.last (k+1))) (pos2A x (Fin.last (k+1))) = x ∘ Tuple.sort x := by
  funext j
  have h := congrFun (readA_last x) j
  simp only [Function.comp_apply] at h
  simpa only [del_apply, zA_apply, Function.comp_apply] using congrArg x h

/-- The `(Fin.last, pos2A last)`-coefficient of the "read then delete" term is `- sortSign x`. -/
lemma signA_last_coeff {k : ℕ} (x : Fin (k+2) → ι) :
    (-1 : ℤ) ^ ((Fin.last (k+1)).val + (pos2A x (Fin.last (k+1))).val) *
        signA x (Fin.last (k+1)) = - sortSign x := by
  have h2 : (-1 : ℤ) ^ ((Fin.last (k+1)).val + (pos2A x (Fin.last (k+1))).val) = -1 := by
    have h3 : (Fin.last (k+1)).val + (pos2A x (Fin.last (k+1))).val = 2*(k+1)+1 := by
      rw [pos2A_last, Fin.val_last, Fin.val_last]
      omega
    rw [h3]
    exact Odd.neg_one_pow ⟨k+1, rfl⟩
  rw [h2, signA_last]
  ring

end Leftover

/-- `Work.DSCOH.Norm.dhTerm` with the projection spelled as `piX` (whose source is the Čech term
`((cechComplexFunctor U).obj P).X (k+1)` rather than the propositionally equal product). -/
theorem dhTerm_piX_leftover {k : ℕ} (P : (Opens X)ᵒᵖ ⥤ ModuleCat A) (U : ι → Opens X)
    (x : Fin (k+2) → ι) (a : Fin (k+2)) (b : Fin (k+3)) :
    dhTerm P U x a b = ((-1 : ℤ) ^ ((a : ℕ) + (b : ℕ)) * signA x a) •
      (piX P U (k+1) (del (zA x a) b) ≫ resDel P U (zA x a) b ≫ resA P U x a) := rfl

/-! ## The index identity of the telescoping -/

/-- **The index identity of the telescoping.**  Deleting the second copy of the double point of the
`a`-th read of `x` (position `pos2A x a`) gives the same tuple as deleting the first copy of the
double point of the `(a+1)`-st read (position `a+1`).  This is `Work.DSCOH.Norm.telescopeIndex`
composed with `x`. -/
theorem del_zA_pos2A_eq_del_succ {k : ℕ} (x : Fin (k+2) → ι) (a : Fin (k+1)) :
    del (zA x (Fin.castSucc a)) (pos2A x (Fin.castSucc a))
      = del (zA x (Fin.succ a)) (Fin.castSucc (Fin.succ a)) := by
  funext j
  have h := congrFun (TelIdx2.telIdx x a) j
  simp only [Function.comp_apply] at h
  simpa only [del_apply, zA_apply] using congrArg x h

/-! ## Thinness of the canonical "delete an entry and restrict" morphisms

The category of open subsets of `X` is a preorder, so two morphisms of `(Opens X)ᵒᵖ` with the same
source and target are equal; consequently two composites "project at a tuple, delete an entry,
restrict" which have the same underlying tuple are equal, and can be compared through the canonical
identification `eqToHom` of the two (propositionally equal) source modules. -/

theorem resDel_resA_eqToHom {k : ℕ} (P : (Opens X)ᵒᵖ ⥤ ModuleCat A) (U : ι → Opens X)
    (x : Fin (k+2) → ι) {a a' : Fin (k+2)} {b b' : Fin (k+3)}
    (h : del (zA x a) b = del (zA x a') b') :
    resDel P U (zA x a) b ≫ resA P U x a =
      eqToHom (congrArg (fun t => tupleMod P U t) h) ≫
        (resDel P U (zA x a') b' ≫ resA P U x a') := by
  have hG : (eqToHom (congrArg (fun t : Fin (k+2) → ι => tupleMod P U t) h) :
      tupleMod P U (del (zA x a) b) ⟶ tupleMod P U (del (zA x a') b'))
      = P.map (eqToHom (congrArg
          (fun t : Fin (k+2) → ι => (op (tupleOp U t) : (Opens X)ᵒᵖ)) h)) := by
    rw [eqToHom_congrArg_comp (F := P.obj)
        (g := fun t : Fin (k+2) → ι => (op (tupleOp U t) : (Opens X)ᵒᵖ)) h,
      eqToHom_map]
  rw [hG, resDel_eq, resA, resDel_eq, resA]
  simp only [← P.map_comp]
  exact congrArg P.map (Subsingleton.elim _ _)

theorem resDel_resA_eqToHom_zero {k : ℕ} (P : (Opens X)ᵒᵖ ⥤ ModuleCat A) (U : ι → Opens X)
    (x : Fin (k+2) → ι) (a : Fin (k+2)) (b : Fin (k+3)) (h : del (zA x a) b = x) :
    resDel P U (zA x a) b ≫ resA P U x a
      = eqToHom (congrArg (fun t => tupleMod P U t) h) := by
  have hG : (eqToHom (congrArg (fun t : Fin (k+2) → ι => tupleMod P U t) h) :
      tupleMod P U (del (zA x a) b) ⟶ tupleMod P U x)
      = P.map (eqToHom (congrArg
          (fun t : Fin (k+2) → ι => (op (tupleOp U t) : (Opens X)ᵒᵖ)) h)) := by
    rw [eqToHom_congrArg_comp (F := P.obj)
        (g := fun t : Fin (k+2) → ι => (op (tupleOp U t) : (Opens X)ᵒᵖ)) h,
      eqToHom_map]
  rw [hG, resDel_eq, resA]
  simp only [← P.map_comp]
  exact congrArg P.map (Subsingleton.elim _ _)

theorem resDel_resA_eqToHom_sortRes {k : ℕ} (P : (Opens X)ᵒᵖ ⥤ ModuleCat A) (U : ι → Opens X)
    (x : Fin (k+2) → ι) (a : Fin (k+2)) (b : Fin (k+3))
    (h : del (zA x a) b = x ∘ Tuple.sort x) :
    resDel P U (zA x a) b ≫ resA P U x a
      = eqToHom (congrArg (fun t => tupleMod P U t) h) ≫ sortRes P U x := by
  have hG : (eqToHom (congrArg (fun t : Fin (k+2) → ι => tupleMod P U t) h) :
      tupleMod P U (del (zA x a) b) ⟶ tupleMod P U (x ∘ Tuple.sort x))
      = P.map (eqToHom (congrArg
          (fun t : Fin (k+2) → ι => (op (tupleOp U t) : (Opens X)ᵒᵖ)) h)) := by
    rw [eqToHom_congrArg_comp (F := P.obj)
        (g := fun t : Fin (k+2) → ι => (op (tupleOp U t) : (Opens X)ᵒᵖ)) h,
      eqToHom_map]
  have hsort : sortRes P U x = P.map (sortHom U x).op := rfl
  rw [hG, hsort, resDel_eq, resA]
  simp only [← P.map_comp]
  exact congrArg P.map (Subsingleton.elim _ _)

/-- The component form of `Work.DSCOH.Norm.pi_comp_eqToHom_congrArg` for the projection
`piX`, whose source is spelled as `((cechComplexFunctor U).obj P).X n`. -/
theorem piX_comp_eqToHom {k : ℕ} (P : (Opens X)ᵒᵖ ⥤ ModuleCat A) (U : ι → Opens X)
    {z z' : Fin (k+2) → ι} (h : z = z') :
    piX P U (k+1) z ≫ eqToHom (congrArg (fun t => tupleMod P U t) h) = piX P U (k+1) z' :=
  pi_comp_eqToHom_congrArg (fun t => tupleMod P U t) h

/-! ## The three term identities -/

/-- The first leftover term of the slot `0` is the `x`-th projection: its coefficient is `1` and it
deletes the leading entry of the `0`-th read, which reproduces `x`. -/
theorem dhTerm_zero {k : ℕ} (P : (Opens X)ᵒᵖ ⥤ ModuleCat A) (U : ι → Opens X)
    (x : Fin (k+2) → ι) :
    dhTerm P U x 0 (Fin.castSucc (0 : Fin (k+2))) = piX P U (k+1) x := by
  have hD : del (zA x (0 : Fin (k+2))) (Fin.castSucc (0 : Fin (k+2))) = x := Leftover.del_zA_zero x
  have hz : ((-1 : ℤ) ^
        (((0 : Fin (k+2)) : ℕ) + ((Fin.castSucc (0 : Fin (k+2)) : Fin (k+3)) : ℕ)))
      * signA x 0 = 1 := by
    have h1 : (((0 : Fin (k+2)) : ℕ) + ((Fin.castSucc (0 : Fin (k+2)) : Fin (k+3)) : ℕ)) = 0 := by
      simp
    rw [h1, Leftover.signA_zero]
    norm_num
  rw [dhTerm_piX_leftover, hz, one_smul,
    resDel_resA_eqToHom_zero P U x 0 (Fin.castSucc (0 : Fin (k+2))) hD,
    piX_comp_eqToHom (P := P) (U := U) hD]

/-- The second leftover term of the last slot is `- sortSign x • (π_{x∘σ} ≫ sortRes x)`. -/
theorem dhTerm_last {k : ℕ} (P : (Opens X)ᵒᵖ ⥤ ModuleCat A) (U : ι → Opens X)
    (x : Fin (k+2) → ι) :
    dhTerm P U x (Fin.last (k+1)) (pos2A x (Fin.last (k+1)))
      = - sortSign x • (piX P U (k+1) (x ∘ Tuple.sort x) ≫ sortRes P U x) := by
  have hD : del (zA x (Fin.last (k+1))) (pos2A x (Fin.last (k+1))) = x ∘ Tuple.sort x :=
    Leftover.del_zA_last x
  rw [dhTerm_piX_leftover, Leftover.signA_last_coeff x,
    resDel_resA_eqToHom_sortRes P U x (Fin.last (k+1)) (pos2A x (Fin.last (k+1))) hD,
    ← Category.assoc, piX_comp_eqToHom (P := P) (U := U) hD]

/-- **The cancellation of the leftover terms.**  The second leftover term of the slot `i` is the
negative of the first leftover term of the slot `i+1`: the two underlying tuples agree
(`Work.DSCOH.Norm.del_zA_pos2A_eq_del_succ`) and the two coefficients agree
(`Work.DSCOH.Norm.TelSign.telescopeSign`). -/
theorem dhTerm_cancel {k : ℕ} (P : (Opens X)ᵒᵖ ⥤ ModuleCat A) (U : ι → Opens X)
    (x : Fin (k+2) → ι) (i : Fin (k+1)) :
    dhTerm P U x (Fin.castSucc i) (pos2A x (Fin.castSucc i))
      = - dhTerm P U x (Fin.succ i) (Fin.castSucc (Fin.succ i)) := by
  have htu : del (zA x (Fin.castSucc i)) (pos2A x (Fin.castSucc i))
      = del (zA x (Fin.succ i)) (Fin.castSucc (Fin.succ i)) := del_zA_pos2A_eq_del_succ x i
  have hc : (-1 : ℤ) ^
        (((Fin.castSucc i : Fin (k+2)) : ℕ) + ((pos2A x (Fin.castSucc i) : Fin (k+3)) : ℕ))
      * signA x (Fin.castSucc i) = - signA x (Fin.succ i) :=
    TelSign.telescopeSign x i
  have hc' : (-1 : ℤ) ^
        (((Fin.succ i : Fin (k+2)) : ℕ) + ((Fin.castSucc (Fin.succ i) : Fin (k+3)) : ℕ)) = 1 := by
    have hmul : (((Fin.succ i : Fin (k+2)) : ℕ)
          + ((Fin.castSucc (Fin.succ i) : Fin (k+3)) : ℕ))
        = 2 * ((Fin.succ i : Fin (k+2)) : ℕ) := by
      simp [two_mul]
    rw [hmul, pow_mul]
    norm_num
  rw [dhTerm_piX_leftover, dhTerm_piX_leftover, hc, hc', one_mul, resDel_resA_eqToHom P U x htu,
    ← Category.assoc, piX_comp_eqToHom (P := P) (U := U) htu,
    neg_smul]

/-! ## The leftover identity -/

theorem firstHom_leftover {X : Type*} [TopologicalSpace X] {A : Type*} [CommRing A]
    {ι : Type*} [LinearOrder ι] [Fintype ι]
    [CategoryTheory.Limits.HasProducts (ModuleCat A)]
    (P : CategoryTheory.Functor (TopologicalSpace.Opens X)ᵒᵖ (ModuleCat A))
    (U : ι → TopologicalSpace.Opens X) {k : ℕ} (x : Fin (k+2) → ι) :
    (Finset.univ.sum (fun a : Fin (k+2) =>
        (Work.DSCOH.Norm.dhTerm P U x a (Fin.castSucc a)
          + Work.DSCOH.Norm.dhTerm P U x a (Work.DSCOH.Norm.pos2A x a))))
      = (CategoryTheory.Limits.Pi.π (fun y : Fin (k+2) → ι => Work.DSCOH.Norm.tupleMod P U y) x)
          - Work.DSCOH.Norm.sortSign x • (CategoryTheory.CategoryStruct.comp
              (CategoryTheory.Limits.Pi.π (fun y : Fin (k+2) → ι => Work.DSCOH.Norm.tupleMod P U y)
                (x ∘ Tuple.sort x))
              (Work.DSCOH.Norm.sortRes P U x)) := by
  -- replace the two explicit projections of the statement by the `piX` spelling
  change (Finset.univ.sum (fun a : Fin (k+2) =>
        (Work.DSCOH.Norm.dhTerm P U x a (Fin.castSucc a)
          + Work.DSCOH.Norm.dhTerm P U x a (Work.DSCOH.Norm.pos2A x a))))
      = Work.DSCOH.Norm.piX P U (k+1) x - Work.DSCOH.Norm.sortSign x •
          (Work.DSCOH.Norm.piX P U (k+1) (x ∘ Tuple.sort x) ≫ Work.DSCOH.Norm.sortRes P U x)
  -- split off the last slot, and split the sum into the two families of leftover terms
  rw [Fin.sum_univ_castSucc, Finset.sum_add_distrib]
  -- the `pos2A`-terms of the slots `i < k+2` cancel against the `castSucc`-terms of the next slots
  have hB : (Finset.univ.sum (fun i : Fin (k+1) =>
        dhTerm P U x (Fin.castSucc i) (pos2A x (Fin.castSucc i))))
      = - Finset.univ.sum (fun i : Fin (k+1) =>
        dhTerm P U x (Fin.succ i) (Fin.castSucc (Fin.succ i))) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => dhTerm_cancel P U x i
  rw [hB]
  -- evaluate the two sums of `castSucc`-terms by dropping the endpoints
  have hcast : (Finset.univ.sum (fun i : Fin (k+1) =>
        dhTerm P U x (Fin.castSucc i) (Fin.castSucc (Fin.castSucc i))))
      = (Finset.univ.sum (fun a : Fin (k+2) => dhTerm P U x a (Fin.castSucc a)))
        - dhTerm P U x (Fin.last (k+1)) (Fin.castSucc (Fin.last (k+1))) := by
    have h := Fin.sum_univ_castSucc (fun a : Fin (k+2) => dhTerm P U x a (Fin.castSucc a))
    rw [h]
    abel
  have hsucc : (Finset.univ.sum (fun i : Fin (k+1) =>
        dhTerm P U x (Fin.succ i) (Fin.castSucc (Fin.succ i))))
      = (Finset.univ.sum (fun a : Fin (k+2) => dhTerm P U x a (Fin.castSucc a)))
        - dhTerm P U x 0 (Fin.castSucc (0 : Fin (k+2))) := by
    have h := Fin.sum_univ_succ (fun a : Fin (k+2) => dhTerm P U x a (Fin.castSucc a))
    rw [h]
    abel
  rw [hcast, hsucc, dhTerm_zero P U x, dhTerm_last P U x, neg_smul]
  abel

end Work.DSCOH.Norm
