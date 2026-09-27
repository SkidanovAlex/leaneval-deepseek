/-
Definitions and pointwise theory of the Hopf maximal function.

For a map `T : X → X` and a function `f : X → ℝ` we define
`hopfG f T n x = max_{0 ≤ k ≤ n} ∑_{j < k} f (T^[j] x)`
by the recursion `G 0 = 0`, `G (n+1) x = max 0 (f x + G n (T x))`.

The pointwise properties established here are the ones used in the proof of Hopf's
maximal ergodic inequality (`Work.EKLComp.hopf_maximal_inequality`).
-/
import Mathlib

open MeasureTheory

namespace Work.EKLComp

variable {X : Type*}

/-- The Hopf maximal function: `hopfG f T n x = max_{0 ≤ k ≤ n} ∑_{j<k} f (T^[j] x)`.
It is defined by the recursion `G 0 = 0`, `G (n+1) x = max 0 (f x + G n (T x))`. -/
noncomputable def hopfG (f : X → ℝ) (T : X → X) : ℕ → X → ℝ
  | 0 => fun _ => 0
  | n + 1 => fun x => max 0 (f x + hopfG f T n (T x))

@[simp] theorem hopfG_zero (f : X → ℝ) (T : X → X) (x : X) : hopfG f T 0 x = 0 := rfl

@[simp] theorem hopfG_zero_fun (f : X → ℝ) (T : X → X) : hopfG f T 0 = fun _ => 0 := rfl

@[simp] theorem hopfG_succ_apply (f : X → ℝ) (T : X → X) (n : ℕ) (x : X) :
    hopfG f T (n + 1) x = max 0 (f x + hopfG f T n (T x)) := rfl

theorem hopfG_succ (f : X → ℝ) (T : X → X) (n : ℕ) :
    hopfG f T (n + 1) = fun x => max 0 (f x + hopfG f T n (T x)) := rfl

theorem birkhoffSum_nonneg {g : X → ℝ} (hg : ∀ y, 0 ≤ g y) (T : X → X) (n : ℕ) (x : X) :
    0 ≤ birkhoffSum T g n x := Finset.sum_nonneg (fun _ _ => hg _)

theorem hopfG_nonneg (f : X → ℝ) (T : X → X) (n : ℕ) (x : X) : 0 ≤ hopfG f T n x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih => rw [hopfG_succ_apply]; exact le_max_left 0 _

theorem hopfG_le_succ (f : X → ℝ) (T : X → X) (n : ℕ) (x : X) :
    hopfG f T n x ≤ hopfG f T (n + 1) x := by
  induction n generalizing x with
  | zero => rw [hopfG_succ_apply]; exact le_max_left 0 _
  | succ n ih =>
    have h1 : hopfG f T (n + 1) x = max 0 (f x + hopfG f T n (T x)) := rfl
    have h2 : hopfG f T (n + 1 + 1) x = max 0 (f x + hopfG f T (n + 1) (T x)) := rfl
    rw [h1, h2]
    exact max_le_max le_rfl (add_le_add_right (ih (T x)) (f x))

theorem hopfG_monotone (f : X → ℝ) (T : X → X) : Monotone (hopfG f T) :=
  monotone_nat_of_le_succ (hopfG_le_succ f T)

theorem hopfG_le_abs (f : X → ℝ) (T : X → X) (n : ℕ) (x : X) :
    hopfG f T n x ≤ birkhoffSum T (fun y => |f y|) (n + 1) x := by
  induction n generalizing x with
  | zero => rw [hopfG_zero, birkhoffSum_one]; exact abs_nonneg _
  | succ n ih =>
    rw [hopfG_succ_apply]
    have hb : birkhoffSum T (fun y => |f y|) (n + 1 + 1) x
        = |f x| + birkhoffSum T (fun y => |f y|) (n + 1) (T x) := by
      rw [birkhoffSum_succ']; all_goals rfl
    rw [hb]
    exact max_le (add_nonneg (abs_nonneg _)
        (birkhoffSum_nonneg (fun y => abs_nonneg (f y)) T _ _))
      (add_le_add (le_abs_self (f x)) (ih (T x)))

/-- The main structural property of the Hopf maximal function: it is the running
maximum of the Birkhoff sums. -/
theorem hopfG_aux (f : X → ℝ) (T : X → X) (n : ℕ) :
    (∀ x k, k ≤ n → birkhoffSum T f k x ≤ hopfG f T n x) ∧
      (∀ x, hopfG f T n x = 0 ∨ ∃ k ≤ n, hopfG f T n x = birkhoffSum T f k x) := by
  induction n with
  | zero =>
    refine ⟨fun x k hk => ?_, fun x => Or.inl (by simp)⟩
    rw [Nat.le_zero.mp hk]
    simp
  | succ n ih =>
    obtain ⟨ih₁, ih₂⟩ := ih
    refine ⟨fun x k hk => ?_, fun x => ?_⟩
    · cases k with
      | zero => rw [birkhoffSum_zero]; exact hopfG_nonneg f T (n + 1) x
      | succ j =>
        have hj : j ≤ n := Nat.succ_le_succ_iff.mp hk
        rw [birkhoffSum_succ', hopfG_succ_apply]
        exact le_trans (add_le_add_right (ih₁ (T x) j hj) (f x)) (le_max_right 0 _)
    · by_cases h : hopfG f T (n + 1) x = 0
      · exact Or.inl h
      · refine Or.inr ?_
        have hpos_max : 0 < max 0 (f x + hopfG f T n (T x)) := by
          rw [← hopfG_succ_apply]
          exact lt_of_le_of_ne (hopfG_nonneg f T (n + 1) x) (Ne.symm h)
        have hpos : 0 < f x + hopfG f T n (T x) := by
          by_contra hc
          rw [not_lt] at hc
          rw [max_eq_left hc] at hpos_max
          exact (lt_irrefl 0) hpos_max
        have hmax : hopfG f T (n + 1) x = f x + hopfG f T n (T x) := by
          rw [hopfG_succ_apply, max_eq_right (le_of_lt hpos)]
        rcases ih₂ (T x) with h0 | ⟨k, hk, hk'⟩
        · refine ⟨1, by omega, ?_⟩
          rw [hmax, h0, add_zero, birkhoffSum_one]
        · refine ⟨k + 1, by omega, ?_⟩
          rw [hmax, hk', birkhoffSum_succ']; all_goals rfl

/-- Every Birkhoff sum up to `n` is bounded by the Hopf maximal function. -/
theorem birkhoffSum_le_hopfG (f : X → ℝ) (T : X → X) {n k : ℕ} (hk : k ≤ n) (x : X) :
    birkhoffSum T f k x ≤ hopfG f T n x := (hopfG_aux f T n).1 x k hk

/-- The Hopf maximal function is either `0` or one of the Birkhoff sums. -/
theorem hopfG_eq_zero_or_eq_birkhoffSum (f : X → ℝ) (T : X → X) (n : ℕ) (x : X) :
    hopfG f T n x = 0 ∨ ∃ k ≤ n, hopfG f T n x = birkhoffSum T f k x :=
  (hopfG_aux f T n).2 x

/-- The Hopf maximal function is positive exactly at the points where some Birkhoff
sum up to `n` is positive. -/
theorem hopfG_pos_iff (f : X → ℝ) (T : X → X) (n : ℕ) (x : X) :
    0 < hopfG f T n x ↔ ∃ k ≤ n, 0 < birkhoffSum T f k x := by
  constructor
  · intro h
    rcases hopfG_eq_zero_or_eq_birkhoffSum f T n x with h0 | ⟨k, hk, hk'⟩
    · rw [h0] at h; exact absurd h (lt_irrefl 0)
    · exact ⟨k, hk, by rw [← hk']; exact h⟩
  · rintro ⟨k, hk, hk'⟩
    exact lt_of_lt_of_le hk' (birkhoffSum_le_hopfG f T hk x)

/-- On the set where `hopfG f T (n+1)` is positive the recursion inverts. -/
theorem hopfG_succ_eq_of_pos (f : X → ℝ) (T : X → X) (n : ℕ) (x : X)
    (h : 0 < hopfG f T (n + 1) x) : f x + hopfG f T n (T x) = hopfG f T (n + 1) x := by
  have hm : 0 < max 0 (f x + hopfG f T n (T x)) := by rwa [hopfG_succ_apply] at h
  have hy : 0 < f x + hopfG f T n (T x) := by
    by_contra hc
    rw [not_lt] at hc
    rw [max_eq_left hc] at hm
    exact (lt_irrefl 0) hm
  rw [hopfG_succ_apply, max_eq_right (le_of_lt hy)]

/-- The inversion identity, in the form used for the integral computation. -/
theorem hopfG_sub_eq_of_pos (f : X → ℝ) (T : X → X) (n : ℕ) (x : X)
    (h : 0 < hopfG f T (n + 1) x) :
    f x = hopfG f T (n + 1) x - hopfG f T n (T x) := by
  have h1 := hopfG_succ_eq_of_pos f T n x h
  linarith

/-- `hopfG` vanishes off the set where it is positive. -/
theorem hopfG_eq_zero_of_not_pos (f : X → ℝ) (T : X → X) (n : ℕ) (x : X)
    (h : ¬ 0 < hopfG f T n x) : hopfG f T n x = 0 :=
  le_antisymm (not_lt.mp h) (hopfG_nonneg f T n x)

/-- The set where the `n`-th Hopf maximal function is positive. -/
def hopfA (f : X → ℝ) (T : X → X) (n : ℕ) : Set X := {x | 0 < hopfG f T n x}

theorem hopfA_eq (f : X → ℝ) (T : X → X) (n : ℕ) :
    hopfA f T n = {x | ∃ k ≤ n, 0 < birkhoffSum T f k x} := by
  ext x; exact hopfG_pos_iff f T n x

theorem hopfA_mono (f : X → ℝ) (T : X → X) : Monotone (hopfA f T) :=
  fun m n hmn x hx => lt_of_lt_of_le hx (hopfG_monotone f T hmn x)

theorem hopfA_subset_iff (f : X → ℝ) (T : X → X) {m n : ℕ} (hmn : m ≤ n) :
    hopfA f T m ⊆ hopfA f T n := hopfA_mono f T hmn

theorem iUnion_hopfA (f : X → ℝ) (T : X → X) :
    (⋃ n, hopfA f T n) = {x | ∃ k, 0 < birkhoffSum T f k x} := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_setOf_eq, hopfA_eq]
  constructor
  · rintro ⟨n, k, hk, h⟩; exact ⟨k, h⟩
  · rintro ⟨k, h⟩; exact ⟨k, k, le_rfl, h⟩

/-- The Birkhoff sum of a constant function. -/
theorem birkhoffSum_const (T : X → X) (c : ℝ) (n : ℕ) (x : X) :
    birkhoffSum T (fun _ => c) n x = n * c := by
  have h := birkhoffSum_of_comp_eq (f := T) (φ := fun _ : X => c) (by funext y; rfl) n
  simpa [nsmul_eq_mul] using congrFun h x

/-- Subtracting a constant from `f` subtracts `n * c` from the `n`-th Birkhoff sum. -/
theorem birkhoffSum_sub_const (T : X → X) (f : X → ℝ) (c : ℝ) (n : ℕ) (x : X) :
    birkhoffSum T (fun y => f y - c) n x = birkhoffSum T f n x - n * c := by
  rw [show (fun y : X => f y - c) = f - fun _ => c from rfl, birkhoffSum_sub]
  simp only [Pi.sub_apply, birkhoffSum_const]

end Work.EKLComp
