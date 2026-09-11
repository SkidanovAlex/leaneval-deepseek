import Mathlib.Probability.Distributions.SetBernoulli
import ChallengeDeps
import Submission.SelCore
import Submission.Deep
import Submission.Multi

/-!
# The multiset deep fragment argument (multiset analogue of `Sel.Deep.Sys`).

Members `S ∈ F` are multisets `X → ℕ` carrying a level function `lv S : X → ℕ`;
each element at level `j` contributes weight `wlev j = 100^{-j}` with multiplicity
`S x`.  The "level sub-multiset" `S_j` contains `x` with multiplicity `S x` iff
`lv S x = j`.  Counts `s_j := |S_j|`, `n_b := Σ_{j ≤ b} s_j`.  Level sums finite.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false
open Classical
open MeasureTheory ProbabilityTheory Measure unitInterval Finset
open scoped NNReal ENNReal BigOperators

namespace Submission

open _root_.SupremumOfSelectorProcesses

namespace Multi

open Sel.Deep

variable {X : Type*} [Fintype X]

/-- A "multi-system": a FINITE family `Fl` of multisets with a level function per member. -/
structure MSys (X : Type*) where
  τ : ℕ
  lv : (X → ℕ) → X → ℕ
  Fl : Finset (X → ℕ)

namespace MSys

/-- the family as a set -/
def F (N : MSys X) : Set (X → ℕ) := N.Fl

@[simp] lemma mem_F (N : MSys X) (S : X → ℕ) : S ∈ N.F ↔ S ∈ N.Fl := Iff.rfl

/-- levels are ≤ τ for every member -/
def LevelBounded (N : MSys X) : Prop := ∀ S ∈ N.F, ∀ x : X, N.lv S x ≤ N.τ

/-- the level-j sub-multiset of S -/
def levM (N : MSys X) (S : X → ℕ) (j : ℕ) : X → ℕ :=
  fun x => if N.lv S x = j then S x else 0

lemma levM_subM (N : MSys X) (S : X → ℕ) (j : ℕ) : subM (N.levM S j) S := by
  intro x; unfold levM; by_cases h : N.lv S x = j <;> simp [h]

lemma levM_pos_of_lv_eq (N : MSys X) (S : X → ℕ) (j : ℕ) {x : X} (h : N.lv S x = j) :
    N.levM S j x = S x := by
  simp [levM, h]

lemma levM_eq_zero_of_lv_ne (N : MSys X) (S : X → ℕ) (j : ℕ) {x : X} (h : N.lv S x ≠ j) :
    N.levM S j x = 0 := by
  simp [levM, h]

/-- |S_j|: the multiplicity of level-j elements of S -/
noncomputable def sCount (N : MSys X) (S : X → ℕ) (j : ℕ) : ℕ :=
  ∑ x : X, if N.lv S x = j then S x else 0

/-- count of level-j occurrences of S inside A: |A ∧ S_j| -/
noncomputable def countAt (N : MSys X) (S : X → ℕ) (A : X → ℕ) (j : ℕ) : ℕ :=
  ∑ x : X, if N.lv S x = j then min (A x) (S x) else 0

lemma countAt_eq_sizeM_minM (N : MSys X) (S A : X → ℕ) (j : ℕ) :
    N.countAt S A j = sizeM (minM A (N.levM S j)) := by
  unfold countAt sizeM minM levM
  apply Finset.sum_congr rfl
  intro x hx
  by_cases h : N.lv S x = j <;> simp [h]

lemma countAt_nonneg (N : MSys X) (S A : X → ℕ) (j : ℕ) : 0 ≤ (N.countAt S A j : ℝ) := by positivity

lemma countAt_mono_left {N : MSys X} {S : X → ℕ} (A A' : X → ℕ) (j : ℕ)
    (h : subM A A') : N.countAt S A j ≤ N.countAt S A' j := by
  unfold countAt
  exact Finset.sum_le_sum (by
    intro x hx
    by_cases hlv : N.lv S x = j
    · have hmin : min (A x) (S x) ≤ min (A' x) (S x) := min_le_min (h x) le_rfl
      simp [hlv, hmin]
    · simp [hlv])

lemma countAt_le_sCount (N : MSys X) (S A : X → ℕ) (j : ℕ) : N.countAt S A j ≤ N.sCount S j := by
  unfold countAt sCount
  exact Finset.sum_le_sum (by
    intro x hx
    by_cases hlv : N.lv S x = j
    · simp [hlv, Nat.min_le_right]
    · simp [hlv])

lemma sCount_eq_countAt_self (N : MSys X) (S : X → ℕ) (j : ℕ) :
    N.countAt S S j = N.sCount S j := by
  unfold countAt sCount
  apply Finset.sum_congr rfl
  intro x hx
  by_cases h : N.lv S x = j <;> simp [h]

/-- prefix count n_b = Σ_{j ≤ b} s_j -/
noncomputable def prefixCount (N : MSys X) (S : X → ℕ) (b : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (b + 1), N.sCount S j

/-- indicator sum at one level: Σ_{j ∈ range(τ+1)} [lv S x = j] = 1 -/
lemma sum_indicator_lv (N : MSys X) (S : X → ℕ) (x : X) (hτ : N.lv S x ≤ N.τ) :
    (∑ j ∈ Finset.range (N.τ + 1), if N.lv S x = j then 1 else 0) = 1 := by
  classical
  have hmem : N.lv S x ∈ Finset.range (N.τ + 1) := by simpa using hτ
  rw [Finset.sum_ite_eq]
  simp [hmem]

/-- Σ_{j ≤ τ} [lv S x = j] · S x = S x -/
lemma sum_indicator_lv_mul (N : MSys X) (S : X → ℕ) (x : X) (hτ : N.lv S x ≤ N.τ) :
    (∑ j ∈ Finset.range (N.τ + 1), if N.lv S x = j then S x else 0) = S x := by
  classical
  calc
    (∑ j ∈ Finset.range (N.τ + 1), if N.lv S x = j then S x else 0)
        = (∑ j ∈ Finset.range (N.τ + 1), if N.lv S x = j then 1 else 0) * S x := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro j hj
          by_cases h : N.lv S x = j <;> simp [h]
    _ = S x * (∑ j ∈ Finset.range (N.τ + 1), if N.lv S x = j then 1 else 0) := by ring
    _ = S x * 1 := by rw [sum_indicator_lv N S x hτ]
    _ = S x := by ring

/-- n_τ = |S| when all levels of S are ≤ τ -/
lemma prefixCount_eq_sizeM (N : MSys X) (S : X → ℕ) (hτ : ∀ x : X, N.lv S x ≤ N.τ) :
    N.prefixCount S N.τ = sizeM S := by
  unfold prefixCount sCount sizeM
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  exact sum_indicator_lv_mul N S x (hτ x)

/-- level count s_j ≤ prefix n_b for j ≤ b -/
lemma sCount_le_prefixCount (N : MSys X) (S : X → ℕ) (b : ℕ) {j : ℕ} (hj : j ≤ b) :
    N.sCount S j ≤ N.prefixCount S b := by
  unfold prefixCount
  exact Finset.single_le_sum (by intro k hk; exact Nat.zero_le _) (by simp [hj])

/-- prefixCount is monotone in b -/
lemma prefixCount_mono (N : MSys X) (S : X → ℕ) {b b' : ℕ} (h : b ≤ b') :
    N.prefixCount S b ≤ N.prefixCount S b' := by
  unfold prefixCount
  exact Finset.sum_le_sum_of_subset_of_nonneg (by intro j hj; simp at hj ⊢; omega) (by intro; simp)

lemma prefixCount_eq_zero_of_all_zero (N : MSys X) (S : X → ℕ) (b : ℕ)
    (h : ∀ j, j ≤ b → N.sCount S j = 0) : N.prefixCount S b = 0 := by
  unfold prefixCount
  rw [Finset.sum_eq_zero]
  intro j hj
  exact h j (by simpa using hj)

/-- weight (levels 0..τ of wlev j · |A∧S_j|): the λ^S-weighted total of A∧S -/
noncomputable def weightM (N : MSys X) (S A : X → ℕ) : ℝ :=
  ∑ j ∈ Finset.range (N.τ + 1), (N.countAt S A j : ℝ) * wlev j

/-- weight of the levels b+1..τ of A∧S -/
noncomputable def weightAboveM (N : MSys X) (S A : X → ℕ) (b : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc (b + 1) N.τ, (N.countAt S A j : ℝ) * wlev j

/-- total weight of S itself -/
noncomputable def totalWeightM (N : MSys X) (S : X → ℕ) : ℝ := N.weightM S S

/-- a member -/
lemma Fl_mem_F {N : MSys X} {S : X → ℕ} (hS : S ∈ N.Fl) : S ∈ N.F := by simpa using hS

lemma weightM_nonneg (N : MSys X) (S A : X → ℕ) : 0 ≤ N.weightM S A := by
  unfold weightM
  exact Finset.sum_nonneg (by intro j hj; exact mul_nonneg (by positivity) (wlev_nonneg j))

lemma weightAboveM_nonneg (N : MSys X) (S A : X → ℕ) (b : ℕ) : 0 ≤ N.weightAboveM S A b := by
  unfold weightAboveM
  exact Finset.sum_nonneg (by intro j hj; exact mul_nonneg (by positivity) (wlev_nonneg j))

/-- weightM is monotone in the second argument -/
lemma weightM_mono {N : MSys X} {S : X → ℕ} (A A' : X → ℕ) (h : subM A A') :
    N.weightM S A ≤ N.weightM S A' := by
  unfold weightM
  exact Finset.sum_le_sum (by
    intro j hj
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast countAt_mono_left (N := N) (S := S) A A' j h)
      (wlev_nonneg j))

/-- weightAboveM is monotone in the second argument -/
lemma weightAboveM_mono {N : MSys X} {S : X → ℕ} (A A' : X → ℕ) (b : ℕ) (h : subM A A') :
    N.weightAboveM S A b ≤ N.weightAboveM S A' b := by
  unfold weightAboveM
  exact Finset.sum_le_sum (by
    intro j hj
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast countAt_mono_left (N := N) (S := S) A A' j h)
      (wlev_nonneg j))

/-- weightAboveM at b ≥ τ is 0 -/
lemma weightAboveM_eq_zero_of_b_ge (N : MSys X) (S A : X → ℕ) (b : ℕ) (hb : N.τ ≤ b) :
    N.weightAboveM S A b = 0 := by
  unfold weightAboveM
  have hI : Finset.Icc (b + 1) N.τ = ∅ := Finset.Icc_eq_empty_iff.mpr (by omega)
  rw [hI]
  simp


/-- prefix of S at b as a multiset: ∨_{j≤b} S_j -/
noncomputable def prefixM (N : MSys X) (S : X → ℕ) (b : ℕ) : X → ℕ :=
  fun x => ∑ j ∈ Finset.range (b + 1), N.levM S j x

/-- pointwise value of the prefix -/
lemma prefixM_pointwise (N : MSys X) (S : X → ℕ) (b : ℕ) (x : X) :
    N.prefixM S b x = if N.lv S x ≤ b then S x else 0 := by
  classical
  unfold prefixM levM
  rw [Finset.sum_ite_eq]
  by_cases hb : N.lv S x ≤ b
  · have hmem : N.lv S x ∈ Finset.range (b + 1) := by simpa using hb
    simp [hb, hmem]
  · have hmem' : N.lv S x ∉ Finset.range (b + 1) := by
      intro hm
      have : N.lv S x ≤ b := by simpa using hm
      omega
    simp [hb, hmem']

/-- prefixM ≤ S -/
lemma prefixM_subM (N : MSys X) (S : X → ℕ) (b : ℕ) : subM (N.prefixM S b) S := by
  intro x
  rw [prefixM_pointwise]
  by_cases hb : N.lv S x ≤ b
  · simp [hb]
  · simp [hb]

/-- |prefixM S b| = prefixCount S b -/
lemma sizeM_prefixM (N : MSys X) (S : X → ℕ) (b : ℕ) : sizeM (N.prefixM S b) = N.prefixCount S b := by
  unfold sizeM prefixM prefixCount sCount levM
  rw [Finset.sum_comm]

/-- subM (prefixM S' b) Z iff each level piece is ⊆ Z -/
lemma subM_prefixM_iff (N : MSys X) (S' Z : X → ℕ) (b : ℕ) :
    subM (N.prefixM S' b) Z ↔ ∀ j, j ≤ b → subM (N.levM S' j) Z := by
  classical
  constructor
  · intro h j hj x
    by_cases hlv : N.lv S' x = j
    · have hxeq : N.levM S' j x = N.prefixM S' b x := by
        rw [levM_pos_of_lv_eq N S' j hlv]
        rw [prefixM_pointwise]
        simp [hlv, hj]
      rw [hxeq]
      exact h x
    · have hx0 : N.levM S' j x = 0 := levM_eq_zero_of_lv_ne N S' j hlv
      rw [hx0]
      exact Nat.zero_le (Z x)
  · intro h x
    rw [prefixM_pointwise]
    by_cases hb : N.lv S' x ≤ b
    · have hsub := h (N.lv S' x) hb x
      have hxeq : N.levM S' (N.lv S' x) x = S' x := by
        rw [levM_pos_of_lv_eq N S' (N.lv S' x) rfl]
      simpa [hb, hxeq] using hsub
    · simp [hb]


/-- weightAboveM depends only on the per-level counts -/
lemma weightAboveM_congr_of_countAt (N : MSys X) {S' A B : X → ℕ} {b : ℕ}
    (h : ∀ j, N.countAt S' A j = N.countAt S' B j) :
    N.weightAboveM S' A b = N.weightAboveM S' B b := by
  unfold weightAboveM
  apply Finset.sum_congr rfl
  intro j hj
  rw [h j]

/-- weightM depends only on the per-level counts -/
lemma weightM_congr_of_countAt (N : MSys X) {S' A B : X → ℕ}
    (h : ∀ j, N.countAt S' A j = N.countAt S' B j) :
    N.weightM S' A = N.weightM S' B := by
  unfold weightM
  apply Finset.sum_congr rfl
  intro j hj
  rw [h j]


/-- per-coordinate min with a decremented value -/
lemma min_sub_one_le (a s : ℕ) : min a s ≤ min (a - 1) s + 1 := by
  by_cases ha : a = 0
  · subst a; simp
  · by_cases h : a - 1 ≤ s
    · have hmin : min (a - 1) s = a - 1 := Nat.min_eq_left h
      have ha1 : 1 ≤ a := Nat.succ_le_of_lt (Nat.pos_of_ne_zero ha)
      calc
        min a s ≤ a := min_le_left a s
        _ = (a - 1) + 1 := by rw [Nat.sub_add_cancel ha1]
        _ = min (a - 1) s + 1 := by rw [hmin]
    · have hs : s < a - 1 := Nat.lt_of_not_ge h
      have hmin : min (a - 1) s = s := Nat.min_eq_right (le_of_lt hs)
      calc
        min a s = s := by
          have hsa : s ≤ a := by omega
          exact Nat.min_eq_right hsa
        _ ≤ s + 1 := by omega
        _ = min (a - 1) s + 1 := by rw [hmin]

/-- countAt changes by at most 1 when erasing one copy of x -/
lemma countAt_eraseOne_le (N : MSys X) (S' : X → ℕ) (j : ℕ) (x : X) (A : X → ℕ) :
    N.countAt S' A j ≤ N.countAt S' (eraseOne A x) j + 1 := by
  classical
  unfold countAt
  let f : X → ℕ := fun y => if N.lv S' y = j then min (A y) (S' y) else 0
  let g : X → ℕ := fun y => if N.lv S' y = j then min (eraseOne A x y) (S' y) else 0
  have hs1 : (∑ y : X, f y) = f x + (∑ y ∈ (Finset.univ.erase x), f y) := by
    exact sum_univ_singleton_add f x
  have hs2 : (∑ y : X, g y) = g x + (∑ y ∈ (Finset.univ.erase x), g y) := by
    exact sum_univ_singleton_add g x
  rw [hs1, hs2]
  have hrest : (∑ y ∈ (Finset.univ.erase x), f y) ≤ (∑ y ∈ (Finset.univ.erase x), g y) := by
    exact Finset.sum_le_sum (by
      intro y hy
      have hyx : y ≠ x := (Finset.mem_erase.mp hy).1
      have hE : eraseOne A x y = A y := eraseOne_other A (x := x) hyx
      simp [f, g, hE])
  by_cases hlv : N.lv S' x = j
  · have h1 : f x = min (A x) (S' x) := by simp [f, hlv]
    have h2 : g x = min (A x - 1) (S' x) := by simp [g, hlv, eraseOne]
    rw [h1, h2]
    have hm := min_sub_one_le (A x) (S' x)
    have hadd := Nat.add_le_add hm hrest
    omega
  · have h1 : f x = 0 := by simp [f, hlv]
    have h2 : g x = 0 := by simp [g, hlv, eraseOne]
    rw [h1, h2]
    omega

/-- countAt unchanged at levels ≠ level of x when erasing x -/
lemma countAt_eraseOne_eq_of_ne_level (N : MSys X) {S' A : X → ℕ} {j j0 : ℕ} (x : X)
    (hxlev : N.lv S' x = j0) (hne : j ≠ j0) :
    N.countAt S' A j = N.countAt S' (eraseOne A x) j := by
  classical
  unfold countAt eraseOne
  apply Finset.sum_congr rfl
  intro y hy
  by_cases hyx : y = x
  · subst y
    have hxne : ¬ N.lv S' x = j := by intro h; exact hne (by rw [← hxlev, h])
    simp [hxne]
  · simp [hyx]

/-- erasing one copy of x at level j0 lowers weightAboveM by at most wlev j0 -/
lemma weightAboveM_eraseOne_le (N : MSys X) {S' A : X → ℕ} {b j0 : ℕ} (x : X)
    (hxlev : N.lv S' x = j0) :
    N.weightAboveM S' A b ≤ N.weightAboveM S' (eraseOne A x) b + wlev j0 := by
  classical
  unfold weightAboveM
  let f : ℕ → ℝ := fun j => (N.countAt S' A j : ℝ) * wlev j
  let g : ℕ → ℝ := fun j => (N.countAt S' (eraseOne A x) j : ℝ) * wlev j
  let gg : ℕ → ℝ := fun j => g j + (if j = j0 then wlev j else 0)
  have hstep : (∑ j ∈ Finset.Icc (b + 1) N.τ, f j) ≤ (∑ j ∈ Finset.Icc (b + 1) N.τ, gg j) := by
    exact Finset.sum_le_sum (by
      intro j hj
      by_cases hjj0 : j = j0
      · subst j
        have hle : (N.countAt S' A j0 : ℝ) ≤ (N.countAt S' (eraseOne A x) j0 : ℝ) + 1 := by
          exact_mod_cast countAt_eraseOne_le N S' j0 x A
        have hmul := mul_le_mul_of_nonneg_right hle (wlev_nonneg j0)
        simpa [f, g, gg, add_mul, one_mul, add_comm, add_left_comm, add_assoc] using hmul
      · have hEq : N.countAt S' A j = N.countAt S' (eraseOne A x) j :=
          countAt_eraseOne_eq_of_ne_level N (S' := S') (A := A) (j := j) (j0 := j0) x hxlev hjj0
        simp [f, g, gg, hjj0, hEq])
  have hsumit : (∑ j ∈ Finset.Icc (b + 1) N.τ, (if j = j0 then wlev j else 0)) ≤ wlev j0 := by
    by_cases hmem : j0 ∈ Finset.Icc (b + 1) N.τ
    · have hval : (∑ j ∈ Finset.Icc (b + 1) N.τ, (if j = j0 then wlev j else 0)) = wlev j0 := by
        have hconv : (∑ j ∈ Finset.Icc (b + 1) N.τ, if j = j0 then wlev j else 0) =
            (∑ j ∈ Finset.Icc (b + 1) N.τ, if j0 = j then wlev j else 0) := by
              apply Finset.sum_congr rfl
              intro j hj
              by_cases h : j0 = j <;> simp [h, eq_comm]
        rw [hconv]
        rw [Finset.sum_ite_eq]
        simp [hmem]
      rw [hval]
    · have hval : (∑ j ∈ Finset.Icc (b + 1) N.τ, (if j = j0 then wlev j else 0)) = 0 := by
        have hconv : (∑ j ∈ Finset.Icc (b + 1) N.τ, if j = j0 then wlev j else 0) =
            (∑ j ∈ Finset.Icc (b + 1) N.τ, if j0 = j then wlev j else 0) := by
              apply Finset.sum_congr rfl
              intro j hj
              by_cases h : j0 = j <;> simp [h, eq_comm]
        rw [hconv]
        rw [Finset.sum_ite_eq]
        simp [hmem]
      rw [hval]
      exact wlev_nonneg j0
  have hgg : gg = fun j => g j + (if j = j0 then wlev j else 0) := by
    funext j
    rfl
  have hsplit : (∑ j ∈ Finset.Icc (b + 1) N.τ, gg j) = (∑ j ∈ Finset.Icc (b + 1) N.τ, g j) + (∑ j ∈ Finset.Icc (b + 1) N.τ, (if j = j0 then wlev j else 0)) := by
    rw [hgg, Finset.sum_add_distrib]
  have hreorg : (∑ j ∈ Finset.Icc (b + 1) N.τ, gg j) ≤ (∑ j ∈ Finset.Icc (b + 1) N.τ, g j) + wlev j0 := by
    rw [hsplit]
    simpa [add_comm, add_left_comm, add_assoc] using
      add_le_add_left hsumit (∑ j ∈ Finset.Icc (b + 1) N.τ, g j)
  exact le_trans hstep hreorg

end MSys

end Multi
end Submission
