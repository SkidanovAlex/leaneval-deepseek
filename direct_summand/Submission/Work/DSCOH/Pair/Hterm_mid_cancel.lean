/-
Area DSCOH (curric-46) — the normalization comparison: cancellation of the two middle terms of
the second differential.

For a nondecreasing tuple `y : Fin (k+2) → ι` which is not strictly increasing, `a = frA y` is the
position of the first repeat of `y` and `frA2 y` is the last position carrying the repeated value
`frV y`; the positions `frA y, …, frA2 y` are exactly the block of entries equal to `frV y`.

The `c`-th term of the second differential, as a morphism into the `y`-component of the
semi-ordered complex, is

`Hterm y c = (-1)^(frA y + c) • (π_{del D c} ≫ (resDel D c ≫ isoDup))`,

where `D = dup y (frA y).castSucc` is `y` with a copy of `y (frA y)` inserted after position
`frA y`.  The present lemma is the middle piece of the second differential:

`Hterm y (frA y + 1) + Hterm y (frA y + 2) = 0`.

Maths: deleting the position `frA y + 1` (the inserted copy) or the position `frA y + 2` from `D`
both give the tuple `y` back (the latter because `y (frA y) = y (frA y + 1)`, so instead of
`y (frA y + 1)` the deleted tuple reads the preceding entry `y (frA y)`, which is the same value).
Hence the two read indices of the second differential coincide, and the corresponding canonical
composites of restrictions are equal (the hom-sets of `Opens X` are subsingletons); the two terms
therefore add up to `0` because their signs are opposite (`frA y + c` runs over `2 frA y + 1` and
`2 frA y + 2`).

The general statement behind the last step is isolated as `Hterm_add_eq_zero_of_del_eq`: whenever
the two deletion positions give the same read index and the two signs are opposite, the two
`Hterm`s cancel.  We also record the `Fintype`-free versions of the two bookkeeping lemmas of
`Work.DSCOH.Norm.HomoAssembly` (`tupleMod_map_eq` and `canonical_comp_eq`), which are only used
here for `ι` with no finiteness assumption.
-/
import Mathlib
import Submission.Work.DSCOH.Norm.HomoAssembly
import Submission.Work.DSCOH.Norm.HomoStruct
import Submission.Work.DSCOH.Struct.readH_eq

namespace Work.DSCOH.Pair

open CategoryTheory Limits Opposite TopologicalSpace
open Work.DSCOH.Norm

set_option backward.isDefEq.respectTransparency false

universe u v w

variable {X : Type u} [TopologicalSpace X] {A : Type v} [CommRing A]
variable {k : ℕ} {ι : Type w} [LinearOrder ι]

/-! ## Two bookkeeping lemmas of the comparison, without a finiteness assumption on `ι` -/

/-- Any two canonical maps (i.e. `P.map` of morphisms of opens with the same source and target)
between two sections of `P` over opens of tuples are equal: the hom-sets of `Opens X` are
subsingletons.  (`Fintype`-free version of `Work.DSCOH.Norm.tupleMod_map_eq`.) -/
private lemma pi_map_eq {P : (Opens X)ᵒᵖ ⥤ ModuleCat A} {V W : (Opens X)ᵒᵖ} (f g : V ⟶ W) :
    P.map f = P.map g := by
  rw [Subsingleton.elim f g]

/-- Two canonical composites whose read indices agree (up to the corresponding transport of the
index) are equal.  (`Fintype`-free version of `Work.DSCOH.Norm.canonical_comp_eq`.) -/
private lemma canonical_comp_eq_of_eq (P : (Opens X)ᵒᵖ ⥤ ModuleCat A) (U : ι → Opens X)
    {u₁ u₂ : SemiIdx ι k} (hu : u₁ = u₂) {W : (Opens X)ᵒᵖ}
    {α₁ : op (tupleOp U u₁.val) ⟶ W} {α₂ : op (tupleOp U u₂.val) ⟶ W} :
    P.map α₁ = eqToHom (congrArg (fun v : SemiIdx ι k => tupleMod P U v.val) hu) ≫ P.map α₂ := by
  rw [← eqToHom_map P (p := congrArg (fun v : SemiIdx ι k => op (tupleOp U v.val)) hu)]
  rw [← P.map_comp]
  exact pi_map_eq α₁ (eqToHom _ ≫ α₂)

/-- The signs of two consecutive second-differential terms are opposite:
`(-1)^(2n+1) + (-1)^(2n+2) = 0`. -/
private lemma negOne_pow_two_mul_add_one_add_two_mul_add_two (n : ℕ) :
    (-1 : ℤ) ^ (2 * n + 1) + (-1 : ℤ) ^ (2 * n + 2) = 0 := by
  have h : (-1 : ℤ) ^ (2 * n) = 1 := by
    rw [pow_mul]
    norm_num
  have h1 : (-1 : ℤ) ^ (2 * n + 1) = -1 := by
    rw [pow_succ (-1 : ℤ) (2 * n), h]
    norm_num
  have h2 : (-1 : ℤ) ^ (2 * n + 2) = 1 := by
    have : 2 * n + 2 = (2 * n + 1) + 1 := by omega
    rw [this, pow_succ (-1 : ℤ) (2 * n + 1), h1]
    norm_num
  rw [h1, h2]
  norm_num

/-! ## The general cancellation -/

/-- If two deletion positions `c`, `c'` give the same read index of the duplicated-first-repeat
tuple and the two signs `(-1)^(frA y + c)`, `(-1)^(frA y + c')` sum to zero, then the two
`Hterm`s cancel. -/
private lemma Hterm_add_eq_zero_of_del_eq [HasProducts (ModuleCat A)]
    (P : (Opens X)ᵒᵖ ⥤ ModuleCat A) (U : ι → Opens X)
    (y : SemiIdx ι (k + 1)) (hh : ¬ StrictMono y.val) {c c' : Fin (k + 3)}
    (hdel : del (dup y.val (frA y.val y.property hh).castSucc) c
          = del (dup y.val (frA y.val y.property hh).castSucc) c')
    (hsign : (-1 : ℤ) ^ ((frA y.val y.property hh : ℕ) + (c : ℕ))
           + (-1 : ℤ) ^ ((frA y.val y.property hh : ℕ) + (c' : ℕ)) = 0) :
    Hterm P U k y c + Hterm P U k y c' = 0 := by
  rw [Hterm, Hterm, dite_eq_right hh, dite_eq_right hh]
  set A0 : Fin (k + 1) := frA y.val y.property hh with hA0
  set D0 : Fin (k + 3) → ι := dup y.val A0.castSucc with hD0
  have hmc : Monotone (del D0 c) := monotone_del D0 c (monotone_dup y.property A0.castSucc)
  have hmc' : Monotone (del D0 c') := monotone_del D0 c' (monotone_dup y.property A0.castSucc)
  have hu : (⟨del D0 c, hmc⟩ : SemiIdx ι (k + 1)) = ⟨del D0 c', hmc'⟩ := Subtype.ext hdel
  have hY1 : resDel P U D0 c ≫ isoDup P U y.val A0.castSucc
      = P.map ((opDup U y.val A0.castSucc ≫ homOfLE (leOfHom (opDel U D0 c))).op) := by
    rw [resDel, isoDup, ← P.map_comp, ← op_comp]
  have hY2 : resDel P U D0 c' ≫ isoDup P U y.val A0.castSucc
      = P.map ((opDup U y.val A0.castSucc ≫ homOfLE (leOfHom (opDel U D0 c'))).op) := by
    rw [resDel, isoDup, ← P.map_comp, ← op_comp]
  have key : resDel P U D0 c ≫ isoDup P U y.val A0.castSucc
      = eqToHom (congrArg (fun v : SemiIdx ι (k + 1) => tupleMod P U v.val) hu)
        ≫ (resDel P U D0 c' ≫ isoDup P U y.val A0.castSucc) := by
    rw [hY1, hY2]
    exact canonical_comp_eq_of_eq P U hu
  have hX : Pi.π (fun w : SemiIdx ι (k + 1) => tupleMod P U w.val) ⟨del D0 c, hmc⟩
        ≫ (resDel P U D0 c ≫ isoDup P U y.val A0.castSucc)
      = Pi.π (fun w : SemiIdx ι (k + 1) => tupleMod P U w.val) ⟨del D0 c', hmc'⟩
        ≫ (resDel P U D0 c' ≫ isoDup P U y.val A0.castSucc) := by
    calc Pi.π (fun w : SemiIdx ι (k + 1) => tupleMod P U w.val) ⟨del D0 c, hmc⟩
            ≫ (resDel P U D0 c ≫ isoDup P U y.val A0.castSucc)
        = Pi.π (fun w : SemiIdx ι (k + 1) => tupleMod P U w.val) ⟨del D0 c, hmc⟩
            ≫ (eqToHom (congrArg (fun v : SemiIdx ι (k + 1) => tupleMod P U v.val) hu)
              ≫ (resDel P U D0 c' ≫ isoDup P U y.val A0.castSucc)) := by rw [key]
      _ = (Pi.π (fun w : SemiIdx ι (k + 1) => tupleMod P U w.val) ⟨del D0 c, hmc⟩
            ≫ eqToHom (congrArg (fun v : SemiIdx ι (k + 1) => tupleMod P U v.val) hu))
            ≫ (resDel P U D0 c' ≫ isoDup P U y.val A0.castSucc) := by rw [Category.assoc]
      _ = Pi.π (fun w : SemiIdx ι (k + 1) => tupleMod P U w.val) ⟨del D0 c', hmc'⟩
            ≫ (resDel P U D0 c' ≫ isoDup P U y.val A0.castSucc) := by
        rw [Pi.π_comp_eqToHom (f := fun v : SemiIdx ι (k + 1) => tupleMod P U v.val) hu]
  rw [hX, ← add_smul, hsign, zero_smul]

/-! ## The middle terms of the second differential -/

/-- The positions `frA y + 1` and `frA y + 2` lie at most one position past the last occurrence
`frA2 y` of the repeated value `frV y`: indeed `frA y + 1 ≤ frA2 y`, since `y` takes the value
`frV y` at the position `frA y + 1`. -/
private lemma frA_succ_le_frA2 (y : Fin (k + 2) → ι) (hy : Monotone y) (hh : ¬ StrictMono y) :
    (frA y hy hh : ℕ) + 1 ≤ (frA2 y hy hh : ℕ) := by
  have hmem : (frA y hy hh).succ
      ∈ Finset.univ.filter (fun i : Fin (k + 2) => y i = frV y hy hh) := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    show y (frA y hy hh).succ = y (frA y hy hh).castSucc
    exact (firstRepeat_spec y hy hh).symm
  have hle := Finset.le_max'
    (Finset.univ.filter (fun i : Fin (k + 2) => y i = frV y hy hh))
    (frA y hy hh).succ hmem
  show (frA y hy hh : ℕ) + 1
    ≤ ((Finset.univ.filter (fun i : Fin (k + 2) => y i = frV y hy hh)).max' _ : ℕ)
  have hle' : ((frA y hy hh).succ : ℕ)
      ≤ ((Finset.univ.filter (fun i : Fin (k + 2) => y i = frV y hy hh)).max' _ : ℕ) :=
    Fin.le_def.mp hle
  simpa [Fin.val_succ] using hle'

theorem Hterm_mid_cancel {k : Nat} {ι : Type*} [LinearOrder ι] {X : Type*}
    [TopologicalSpace X] {A : Type*} [CommRing A]
    [CategoryTheory.Limits.HasProducts (ModuleCat A)]
    (P : CategoryTheory.Functor (Opposite (TopologicalSpace.Opens X)) (ModuleCat A))
    (U : ι → TopologicalSpace.Opens X)
    (y : Work.DSCOH.Norm.SemiIdx ι (k + 1)) (hy : Monotone y.val) (hh : Not (StrictMono y.val)) :
    Work.DSCOH.Norm.Hterm P U k y
        (((Work.DSCOH.Norm.frA y.val hy hh).castSucc : Fin (k + 2)).succ)
      + Work.DSCOH.Norm.Hterm P U k y
        (⟨(Work.DSCOH.Norm.frA y.val hy hh : Nat) + 2, by
          have := (Work.DSCOH.Norm.frA y.val hy hh).isLt; omega⟩ : Fin (k + 3)) = 0 := by
  -- `frA` (and everything built from it) only depends on the tuple, not on the particular proof
  -- of monotonicity, so the read indices of `Hterm` may be taken with the subtype's proof.
  have hle : (frA y.val y.property hh : ℕ) + 1 ≤ (frA2 y.val y.property hh : ℕ) :=
    frA_succ_le_frA2 y.val y.property hh
  -- both deletion positions give back the tuple `y` itself
  have hdel1 : del (dup y.val (frA y.val y.property hh).castSucc)
      (((frA y.val y.property hh).castSucc : Fin (k + 2)).succ) = y.val :=
    Work.DSCOH.Struct.readH_eq y.val y.property hh _
      (by simp only [Fin.val_succ, Fin.val_castSucc]; omega)
      (by simp only [Fin.val_succ, Fin.val_castSucc]; omega)
  have hdel2 : del (dup y.val (frA y.val y.property hh).castSucc)
      (⟨(frA y.val y.property hh : ℕ) + 2, by
        have := (frA y.val y.property hh).isLt; omega⟩ : Fin (k + 3)) = y.val :=
    Work.DSCOH.Struct.readH_eq y.val y.property hh _
      (by show (frA y.val y.property hh : ℕ) ≤ (frA y.val y.property hh : ℕ) + 2; omega)
      (by show (frA y.val y.property hh : ℕ) + 2 ≤ (frA2 y.val y.property hh : ℕ) + 1; omega)
  -- the two signs are opposite: the exponents are `2 frA + 1` and `2 frA + 2`
  have hsign : (-1 : ℤ)
          ^ ((frA y.val y.property hh : ℕ)
            + ((((frA y.val y.property hh).castSucc : Fin (k + 2)).succ : Fin (k + 3)) : ℕ))
        + (-1 : ℤ)
          ^ ((frA y.val y.property hh : ℕ)
            + ((⟨(frA y.val y.property hh : ℕ) + 2, by
                have := (frA y.val y.property hh).isLt; omega⟩ : Fin (k + 3)) : ℕ)) = 0 := by
    have e1 : ((((frA y.val y.property hh).castSucc : Fin (k + 2)).succ : Fin (k + 3)) : ℕ)
        = (frA y.val y.property hh : ℕ) + 1 := by
      simp only [Fin.val_succ, Fin.val_castSucc]
    have e2 : ((⟨(frA y.val y.property hh : ℕ) + 2, by
        have := (frA y.val y.property hh).isLt; omega⟩ : Fin (k + 3)) : ℕ)
        = (frA y.val y.property hh : ℕ) + 2 := rfl
    rw [e1, e2]
    have e3 : (frA y.val y.property hh : ℕ) + ((frA y.val y.property hh : ℕ) + 1)
        = 2 * (frA y.val y.property hh : ℕ) + 1 := by ring
    have e4 : (frA y.val y.property hh : ℕ) + ((frA y.val y.property hh : ℕ) + 2)
        = 2 * (frA y.val y.property hh : ℕ) + 2 := by ring
    rw [e3, e4]
    exact negOne_pow_two_mul_add_one_add_two_mul_add_two _
  exact Hterm_add_eq_zero_of_del_eq P U y hh (hdel1.trans hdel2.symm) hsign

end Work.DSCOH.Pair
