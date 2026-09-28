import Mathlib
import Submission.Work.HP.Defs

/-!
# The two-coordinate slice of the Veronese monomials

For `1 ≤ n` the variables `X_0` and `X_1` of the Veronese embedding `ν_{d,n}` are singled out.
We define

* `c0 n`, `c1 n hn` : the two coordinates;
* `sliceVal d k i`, `sliceMon d n hn k` : the exponent vector of `X_0 ^ k * X_1 ^ (d - k)`;
* `IsSliceMono d n m` : the monomials supported in `{X_0, X_1}`;
* `slicePt n t` : the point `(t, 1, 0, …, 0)`;

and we prove the reindexing identity `∑_m f m = ∑_{k} f (sliceMon k)` for `f` vanishing outside
the slice, together with the evaluations of `veronese`, `dotR` and `rNorm` at the slice.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

noncomputable section

open Finset

namespace Work.HP.HP2

/-- The coordinate `0 : Fin (n + 1)`. -/
def c0 (n : ℕ) : Fin (n + 1) := ⟨0, Nat.succ_pos n⟩

/-- The coordinate `1 : Fin (n + 1)`, available when `1 ≤ n`. -/
def c1 (n : ℕ) (hn : 1 ≤ n) : Fin (n + 1) := ⟨1, by omega⟩

@[simp] lemma c0_val (n : ℕ) : ((c0 n : Fin (n + 1)) : ℕ) = 0 := rfl
@[simp] lemma c1_val (n : ℕ) (hn : 1 ≤ n) : ((c1 n hn : Fin (n + 1)) : ℕ) = 1 := rfl

lemma c0_ne_c1 (n : ℕ) (hn : 1 ≤ n) : c0 n ≠ c1 n hn := by
  intro h
  have h2 := congrArg (fun x : Fin (n + 1) => (x : ℕ)) h
  simp only [c0_val, c1_val] at h2
  exact one_ne_zero h2.symm

lemma eq_c0_of_val_eq_zero {n : ℕ} {i : Fin (n + 1)} (h : (i : ℕ) = 0) : i = c0 n :=
  Fin.ext (by simpa using h)

lemma eq_c1_of_val_eq_one {n : ℕ} (hn : 1 ≤ n) {i : Fin (n + 1)} (h : (i : ℕ) = 1) :
    i = c1 n hn := Fin.ext (by simpa using h)

lemma val_eq_zero_of_eq_c0 {n : ℕ} {i : Fin (n + 1)} (h : i = c0 n) : (i : ℕ) = 0 := by
  rw [h]; rfl

lemma val_eq_one_of_eq_c1 {n : ℕ} (hn : 1 ≤ n) {i : Fin (n + 1)} (h : i = c1 n hn) :
    (i : ℕ) = 1 := by rw [h]; rfl

/-- The exponent of `X_0` in the slice monomial `X_0 ^ k * X_1 ^ (d - k)` (at coordinate `i`). -/
def sliceVal (d : ℕ) {n : ℕ} (k : Fin (d + 1)) (i : Fin (n + 1)) : ℕ :=
  if (i : ℕ) = 0 then (k : ℕ) else if (i : ℕ) = 1 then d - (k : ℕ) else 0

lemma sliceVal_lt (d : ℕ) {n : ℕ} (k : Fin (d + 1)) (i : Fin (n + 1)) :
    sliceVal d k i < d + 1 := by
  unfold sliceVal
  split_ifs <;> omega

lemma sliceVal_c0 (d : ℕ) {n : ℕ} (k : Fin (d + 1)) : sliceVal d k (c0 n) = (k : ℕ) := by
  simp [sliceVal]

lemma sliceVal_c1 (d n : ℕ) (hn : 1 ≤ n) (k : Fin (d + 1)) :
    sliceVal d k (c1 n hn) = d - (k : ℕ) := by
  simp [sliceVal]

lemma sliceVal_other (d : ℕ) {n : ℕ} (k : Fin (d + 1)) {i : Fin (n + 1)}
    (h0 : (i : ℕ) ≠ 0) (h1 : (i : ℕ) ≠ 1) : sliceVal d k i = 0 := by
  simp [sliceVal, h0, h1]

lemma ite_val_zero_eq {M : Type*} {n : ℕ} (a b : M) (i : Fin (n + 1)) :
    (if (i : ℕ) = 0 then a else b) = (if i = c0 n then a else b) := by
  by_cases h : (i : ℕ) = 0
  · rw [if_pos h, if_pos (eq_c0_of_val_eq_zero h)]
  · rw [if_neg h, if_neg (fun hh => h (val_eq_zero_of_eq_c0 hh))]

lemma ite_val_one_eq {M : Type*} {n : ℕ} (hn : 1 ≤ n) (a b : M) (i : Fin (n + 1)) :
    (if (i : ℕ) = 1 then a else b) = (if i = c1 n hn then a else b) := by
  by_cases h : (i : ℕ) = 1
  · rw [if_pos h, if_pos (eq_c1_of_val_eq_one hn h)]
  · rw [if_neg h, if_neg (fun hh => h (val_eq_one_of_eq_c1 hn hh))]

lemma sum_ite_val_zero {M : Type*} [AddCommMonoid M] (N : ℕ) (a : M) :
    (∑ i : Fin (N + 1), (if (i : ℕ) = 0 then a else 0)) = a := by
  calc ∑ i : Fin (N + 1), (if (i : ℕ) = 0 then a else 0)
      = ∑ i : Fin (N + 1), (if i = c0 N then a else 0) :=
        Finset.sum_congr rfl (fun i _ => ite_val_zero_eq a 0 i)
    _ = a := Fintype.sum_ite_eq' (c0 N) (fun _ => a)

lemma sum_ite_val_one {M : Type*} [AddCommMonoid M] {N : ℕ} (hN : 1 ≤ N) (a : M) :
    (∑ i : Fin (N + 1), (if (i : ℕ) = 1 then a else 0)) = a := by
  calc ∑ i : Fin (N + 1), (if (i : ℕ) = 1 then a else 0)
      = ∑ i : Fin (N + 1), (if i = c1 N hN then a else 0) :=
        Finset.sum_congr rfl (fun i _ => ite_val_one_eq hN a 0 i)
    _ = a := Fintype.sum_ite_eq' (c1 N hN) (fun _ => a)

/-- The exponent vector of the monomial `X_0 ^ k * X_1 ^ (d - k)`. -/
def sliceMon (d n : ℕ) (hn : 1 ≤ n) (k : Fin (d + 1)) : Mon d n :=
  ⟨fun i => ⟨sliceVal d k i, sliceVal_lt d k i⟩, by
    change (∑ i : Fin (n + 1), sliceVal d k i) = d
    have hcomp : ∀ i : Fin (n + 1),
        sliceVal d k i = (if (i : ℕ) = 0 then (k : ℕ) else 0) +
          (if (i : ℕ) = 1 then d - (k : ℕ) else 0) := by
      intro i
      unfold sliceVal
      by_cases h0 : (i : ℕ) = 0
      · simp [h0]
      · by_cases h1 : (i : ℕ) = 1
        · simp [h0, h1]
        · simp [h0, h1]
    calc ∑ i : Fin (n + 1), sliceVal d k i
        = ∑ i : Fin (n + 1), ((if (i : ℕ) = 0 then (k : ℕ) else 0) +
            (if (i : ℕ) = 1 then d - (k : ℕ) else 0)) :=
          Finset.sum_congr rfl (fun i _ => hcomp i)
      _ = (∑ i : Fin (n + 1), (if (i : ℕ) = 0 then (k : ℕ) else 0)) +
            (∑ i : Fin (n + 1), (if (i : ℕ) = 1 then d - (k : ℕ) else 0)) :=
          Finset.sum_add_distrib
      _ = (k : ℕ) + (d - (k : ℕ)) := by
          rw [sum_ite_val_zero n (k : ℕ), sum_ite_val_one hn (d - (k : ℕ))]
      _ = d := by have hk := k.isLt; omega⟩

/-- The monomials of `Mon d n` supported in the first two variables. -/
def IsSliceMono (d n : ℕ) (m : Mon d n) : Prop :=
  ∀ i : Fin (n + 1), 2 ≤ (i : ℕ) → (m.1 i : ℕ) = 0

lemma sliceMon_val_c0 (d n : ℕ) (hn : 1 ≤ n) (k : Fin (d + 1)) :
    (sliceMon d n hn k).1 (c0 n) = k := by
  apply Fin.ext
  show sliceVal d k (c0 n) = (k : ℕ)
  exact sliceVal_c0 d k

lemma sliceMon_val_c1 (d n : ℕ) (hn : 1 ≤ n) (k : Fin (d + 1)) :
    ((sliceMon d n hn k).1 (c1 n hn) : ℕ) = d - (k : ℕ) :=
  sliceVal_c1 d n hn k

lemma sliceMon_val_other (d n : ℕ) (hn : 1 ≤ n) (k : Fin (d + 1)) {i : Fin (n + 1)}
    (h0 : (i : ℕ) ≠ 0) (h1 : (i : ℕ) ≠ 1) : ((sliceMon d n hn k).1 i : ℕ) = 0 :=
  sliceVal_other d k h0 h1

lemma sliceMon_injective (d n : ℕ) (hn : 1 ≤ n) : Function.Injective (sliceMon d n hn) := by
  intro k k' h
  have hh := congrArg (fun m : Mon d n => m.1 (c0 n)) h
  rw [sliceMon_val_c0, sliceMon_val_c0] at hh
  exact hh

lemma sliceMon_isSlice (d n : ℕ) (hn : 1 ≤ n) (k : Fin (d + 1)) :
    IsSliceMono d n (sliceMon d n hn k) := by
  intro i hi
  exact sliceMon_val_other d n hn k (by omega) (by omega)

lemma isSlice_sum_eq (d n : ℕ) (hn : 1 ≤ n) {m : Mon d n} (hm : IsSliceMono d n m) :
    ∑ i : Fin (n + 1), (m.1 i : ℕ) = (m.1 (c0 n) : ℕ) + (m.1 (c1 n hn) : ℕ) := by
  have h := Finset.sum_subset (Finset.subset_univ ({c0 n, c1 n hn} : Finset (Fin (n + 1))))
      (fun i _ hi => by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
        exact hm i (by
          have h0 : (i : ℕ) ≠ 0 := fun hh => hi.1 (eq_c0_of_val_eq_zero hh)
          have h1 : (i : ℕ) ≠ 1 := fun hh => hi.2 (eq_c1_of_val_eq_one hn hh)
          omega))
  rw [← h, Finset.sum_insert (by
    simp only [Finset.mem_singleton]; exact c0_ne_c1 n hn), Finset.sum_singleton]

lemma isSlice_add (d n : ℕ) (hn : 1 ≤ n) {m : Mon d n} (hm : IsSliceMono d n m) :
    (m.1 (c0 n) : ℕ) + (m.1 (c1 n hn) : ℕ) = d := by
  rw [← isSlice_sum_eq d n hn hm]
  exact m.2

lemma sliceMon_eq_of_isSlice (d n : ℕ) (hn : 1 ≤ n) {m : Mon d n} (hm : IsSliceMono d n m) :
    sliceMon d n hn (m.1 (c0 n)) = m := by
  apply Subtype.ext
  funext i
  apply Fin.ext
  show sliceVal d (m.1 (c0 n)) i = (m.1 i : ℕ)
  by_cases h0 : (i : ℕ) = 0
  · rw [eq_c0_of_val_eq_zero h0, sliceVal_c0]
  · by_cases h1 : (i : ℕ) = 1
    · rw [eq_c1_of_val_eq_one hn h1, sliceVal_c1 d n hn (m.1 (c0 n))]
      have hadd := isSlice_add d n hn hm
      omega
    · rw [sliceVal_other d (m.1 (c0 n)) h0 h1]
      exact (hm i (by omega)).symm

/-- Reindexing a sum over the slice monomials. -/
lemma sum_slice_reindex {M : Type*} [AddCommMonoid M] (d n : ℕ) (hn : 1 ≤ n)
    (f : Mon d n → M) (hf : ∀ m : Mon d n, ¬ IsSliceMono d n m → f m = 0) :
    ∑ m : Mon d n, f m = ∑ k : Fin (d + 1), f (sliceMon d n hn k) := by
  have hinj := sliceMon_injective d n hn
  have hmem : ∀ m : Mon d n, m ∈ (Finset.univ.image (sliceMon d n hn)) ↔ IsSliceMono d n m := by
    intro m
    constructor
    · intro hm
      obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hm
      exact sliceMon_isSlice d n hn k
    · intro hm
      exact Finset.mem_image.mpr
        ⟨m.1 (c0 n), Finset.mem_univ _, sliceMon_eq_of_isSlice d n hn hm⟩
  calc ∑ m : Mon d n, f m
      = ∑ m ∈ Finset.univ.image (sliceMon d n hn), f m := by
        rw [Finset.sum_subset (Finset.subset_univ _)
          (fun m _ hm => hf m (fun h => hm ((hmem m).mpr h)))]
    _ = ∑ k : Fin (d + 1), f (sliceMon d n hn k) :=
        Finset.sum_image (hinj.injOn)

/-- The point `(t, 1, 0, …, 0)`. -/
def slicePt (n : ℕ) (t : ℝ) : Fin (n + 1) → ℝ :=
  fun i => if (i : ℕ) = 0 then t else if (i : ℕ) = 1 then 1 else 0

lemma slicePt_c0 (n : ℕ) (t : ℝ) : slicePt n t (c0 n) = t := by simp [slicePt]
lemma slicePt_c1 (n : ℕ) (hn : 1 ≤ n) (t : ℝ) : slicePt n t (c1 n hn) = 1 := by simp [slicePt]
lemma slicePt_other (n : ℕ) (t : ℝ) {i : Fin (n + 1)} (h0 : (i : ℕ) ≠ 0) (h1 : (i : ℕ) ≠ 1) :
    slicePt n t i = 0 := by simp [slicePt, h0, h1]

lemma veronese_sliceMon (d n : ℕ) (hn : 1 ≤ n) (t : ℝ) (k : Fin (d + 1)) :
    veronese d n (slicePt n t) (sliceMon d n hn k) = t ^ (k : ℕ) := by
  rw [veronese]
  have hprod : ∀ i : Fin (n + 1),
      (slicePt n t i) ^ ((sliceMon d n hn k).1 i : ℕ) =
        (if i = c0 n then t ^ (k : ℕ) else 1) := by
    intro i
    by_cases h0 : (i : ℕ) = 0
    · rw [eq_c0_of_val_eq_zero h0, slicePt_c0 n t, sliceMon_val_c0 d n hn k]
      simp
    · by_cases h1 : (i : ℕ) = 1
      · rw [eq_c1_of_val_eq_one hn h1, slicePt_c1 n hn t, sliceMon_val_c1 d n hn k,
          ite_eq_right (fun hh => c0_ne_c1 n hn hh.symm)]
        simp
      · rw [ite_eq_right (fun hh => h0 (val_eq_zero_of_eq_c0 hh)),
          slicePt_other n t h0 h1, sliceMon_val_other d n hn k h0 h1]
        simp
  calc ∏ i : Fin (n + 1), (slicePt n t i) ^ ((sliceMon d n hn k).1 i : ℕ)
      = ∏ i : Fin (n + 1), (if i = c0 n then t ^ (k : ℕ) else 1) :=
        Finset.prod_congr rfl (fun i _ => hprod i)
    _ = t ^ (k : ℕ) := Fintype.prod_ite_eq' (c0 n) (fun _ => t ^ (k : ℕ))

lemma veronese_slice_other (d n : ℕ) (hn : 1 ≤ n) (t : ℝ) {m : Mon d n}
    (hm : ¬ IsSliceMono d n m) : veronese d n (slicePt n t) m = 0 := by
  rw [veronese]
  have hm' : ∃ i : Fin (n + 1), 2 ≤ (i : ℕ) ∧ (m.1 i : ℕ) ≠ 0 := by
    by_contra h
    exact hm (fun i hi => by
      by_contra hne
      exact h ⟨i, hi, hne⟩)
  obtain ⟨i, hi, hmi⟩ := hm'
  refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
  rw [slicePt_other n t (by omega) (by omega)]
  exact zero_pow hmi

lemma dotR_veronese_slice (d n : ℕ) (hn : 1 ≤ n) (t : ℝ) (b : Mon d n → ℝ) :
    dotR (veronese d n (slicePt n t)) b
      = ∑ k : Fin (d + 1), b (sliceMon d n hn k) * t ^ (k : ℕ) := by
  rw [dotR, sum_slice_reindex (M := ℝ) d n hn
    (fun m => veronese d n (slicePt n t) m * b m) (fun m hm => by
      rw [veronese_slice_other d n hn t hm, zero_mul])]
  apply Finset.sum_congr rfl
  intro k _
  rw [veronese_sliceMon, mul_comm]

lemma rNorm_veronese_slice (d n : ℕ) (hn : 1 ≤ n) (t : ℝ) :
    (rNorm (veronese d n (slicePt n t))) ^ 2
      = ∑ k : Fin (d + 1), (t ^ (k : ℕ)) ^ 2 := by
  have hnn : 0 ≤ ∑ m : Mon d n, (veronese d n (slicePt n t) m) ^ 2 :=
    Finset.sum_nonneg (fun m _ => sq_nonneg _)
  rw [rNorm, Real.sq_sqrt hnn]
  rw [sum_slice_reindex (M := ℝ) d n hn
    (fun m => (veronese d n (slicePt n t) m) ^ 2) (fun m hm => by
      rw [veronese_slice_other d n hn t hm, sq, mul_zero])]
  apply Finset.sum_congr rfl
  intro k _
  rw [veronese_sliceMon]

end Work.HP.HP2
