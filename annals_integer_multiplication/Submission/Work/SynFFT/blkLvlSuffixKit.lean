import Mathlib
import Submission.Work.SynFFT.kit2
import Submission.Work.SynFFT.mrgBlkDefs
import Submission.Work.SynFFT.blkLvlDefs

/-!
# `Work.SynFFT.blkLvlSuffixKit`: shared vocabulary for the block-level suffix pass

The block level pass of the synthetic FFT ends with a list `Z` of *bunched* butterfly
outputs (`Z[i] = cons low_i high_i`); the suffix pass extracts the `low`s and the `high`s and
puts them next to each other:

`ofList Z :: int m :: rest  ↦  ofList ((Z.map vfst).take (m/2) ++ Z.map vsnd) :: int m :: rest`.

This file collects the vocabulary and the elementary list/size facts used by the three word
lemmas that the assembled proof (`blkLvlSuffix.lean`) chains together:

* `cnsP Lb x` — `x` is a `cons` of size `≤ Lb` (the predicate the `mapList` steps use, so that
  the per-element word has a *constant* cost);
* `vsz_vfst_le` / `vsz_vsnd_le` — extracting a component never increases the size;
* `forall₂_vfst` / `forall₂_vsnd` — a `Forall₂` with the graph of `vfst`/`vsnd` pins the image
  list (`mapStep`'s `hB`);
* `vsz_ofList_take_le` and `vsz_ofList_map_le_xblkLvlSuffixKit` — size bounds for `take`d and `map`ped lists;
* `fdivStep` and `int_fdiv_two` — the `IntLib.fdiv` step and `(m : ℤ).fdiv 2 = (m/2 : ℤ)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.SynFFT

open HvdH

/-- `x` is a `cons` value of size at most `Lb`.  This is the element predicate of the `mapList`
steps of the suffix pass: it carries the size bound into the per-element word, so that the word's
cost can be bounded by a *constant* (the `mapList` contract requires a cost independent of the
element). -/
def cnsP (Lb : ℕ) (x : Val) : Prop := (∃ a b : Val, x = .cons a b) ∧ vsz x ≤ Lb

lemma cnsP.cons {Lb : ℕ} {x : Val} (h : cnsP Lb x) : ∃ a b : Val, x = .cons a b := h.1

lemma cnsP.le {Lb : ℕ} {x : Val} (h : cnsP Lb x) : vsz x ≤ Lb := h.2

/-- Extracting the first component of a `cons` never increases the size. -/
lemma vsz_vfst_le (x : Val) : vsz (vfst x) ≤ vsz x := by
  cases x with
  | int z =>
    rw [show vfst (Val.int z) = Val.nil from rfl, MrgKit.vsz_int']
    show (1 : ℕ) ≤ isz z
    simp only [isz]
    omega
  | nil => exact le_rfl
  | cons a b =>
    rw [vfst_cons, MrgKit.vsz_cons']
    omega

/-- Extracting the second component of a `cons` never increases the size. -/
lemma vsz_vsnd_le (x : Val) : vsz (vsnd x) ≤ vsz x := by
  cases x with
  | int z =>
    rw [show vsnd (Val.int z) = Val.nil from rfl, MrgKit.vsz_int']
    show (1 : ℕ) ≤ isz z
    simp only [isz]
    omega
  | nil => exact le_rfl
  | cons a b =>
    rw [vsnd_cons, MrgKit.vsz_cons']
    omega

/-- `vfst` of a `cons` is its first component, and it is no bigger than the value. -/
lemma vfst_cons_le (a b : Val) : vsz a ≤ vsz (.cons a b) := by
  rw [MrgKit.vsz_cons']
  omega

/-- `vsnd` of a `cons` is its second component, and it is no bigger than the value. -/
lemma vsnd_cons_le (a b : Val) : vsz b ≤ vsz (.cons a b) := by
  rw [MrgKit.vsz_cons']
  omega

/-- A `Forall₂` with the graph of `vfst` pins the second list: it is the `map vfst` of the first. -/
lemma forall₂_vfst {xs ys : List Val} (h : List.Forall₂ (fun x y => y = vfst x) xs ys) :
    ys = xs.map vfst := by
  induction h with
  | nil => rfl
  | cons hxy _ ih => rw [hxy, ih]; rfl

/-- A `Forall₂` with the graph of `vsnd` pins the second list: it is the `map vsnd` of the first. -/
lemma forall₂_vsnd {xs ys : List Val} (h : List.Forall₂ (fun x y => y = vsnd x) xs ys) :
    ys = xs.map vsnd := by
  induction h with
  | nil => rfl
  | cons hxy _ ih => rw [hxy, ih]; rfl

/-- Taking entries of a list of values cannot increase the size of its encoding. -/
lemma vsz_ofList_take_le (xs : List Val) (s : ℕ) : vsz (ofList (xs.take s)) ≤ vsz (ofList xs) := by
  rw [MrgKit.vsz_ofList, MrgKit.vsz_ofList]
  have h1 : (xs.take s).length ≤ xs.length := by simp
  have h2 : ((xs.take s).map vsz).sum ≤ (xs.map vsz).sum := by
    have h := List.sum_take_add_sum_drop (xs.map vsz) s
    rw [← List.map_take, ← List.map_drop] at h
    omega
  omega

/-- Size of the encoding of a mapped list, from a pointwise bound on the images. -/
lemma vsz_ofList_map_le_xblkLvlSuffixKit (f : Val → Val) (xs : List Val) (L : ℕ)
    (h : ∀ x ∈ xs, vsz (f x) ≤ L) : vsz (ofList (xs.map f)) ≤ xs.length * (L + 1) + 1 := by
  rw [MrgKit.vsz_ofList]
  have hsum : ((xs.map f).map vsz).sum ≤ (xs.map f).length * L :=
    MrgKit.sum_le_of_forall vsz (xs.map f) L (by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
      exact h x hx)
  simp only [List.length_map] at hsum ⊢
  rw [Nat.mul_succ]
  omega

/-! ## The `IntLib.fdiv` step -/

theorem fdivStep {main : Cmd} {fdivP : Cmd} {Kf : ℕ}
    (h : BinOp main fdivP (fun _ b => 0 < b) Int.fdiv (fun a b => Kf * isz a * isz b))
    (a b : ℤ) (t : List Val) (hb : 0 < b) (D : ℕ) (hD : Kf * isz a * isz b ≤ D) :
    WordR main fdivP (fun vs => vs = .int a :: .int b :: t)
      (fun _ out => out = .int (a.fdiv b) :: t) (fun _ => D) := by
  unfold BinOp at h
  refine MrgKit.WordR_conseqC h ⟨a, b, t, rfl, hb⟩ ?_ hD
  intro out hout
  obtain ⟨a', b', t', h1, hout'⟩ := hout
  simp only [List.cons.injEq, Val.int.injEq] at h1
  obtain ⟨rfl, rfl, rfl⟩ := h1
  exact hout'

/-- `(m : ℤ).fdiv 2 = (m/2 : ℤ)`: halving a natural. -/
lemma int_fdiv_two (m : ℕ) : ((m : ℤ)).fdiv (2 : ℤ) = ((m / 2 : ℕ) : ℤ) := by
  simp [Int.fdiv_eq_ediv_of_nonneg]

/-- `isz (m : ℤ) ≤ 2 * (m + 1)`. -/
lemma isz_nat_le (m : ℕ) : isz (m : ℤ) ≤ 2 * (m + 1) := by
  have h1 : ((m : ℤ)).natAbs = m := by simp
  have h2 : m.size ≤ m := (Nat.size_le).mpr Nat.lt_two_pow_self
  simp only [isz, h1]
  omega

end Work.SynFFT
