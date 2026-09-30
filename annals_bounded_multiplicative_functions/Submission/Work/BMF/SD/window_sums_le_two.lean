import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.SD.window_helpers

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Window sums over the geometric grid `P · (7/5)^j`

The grid `a_j = P · (7/5)^j` has *constant ratio* `7/5 < 2`, so a point `x ≥ P` belongs to at
most two of the closed windows `[a_j, a_{j+1}]` (consecutive windows overlap only in their
common endpoint `a_{j+1}`).  Consequently, if each window's primes are contained in a fixed
finite set `U`, every prime of `U` can be counted at most twice in the double sum

`∑_{j ∈ S} ∑_{p ∈ primesIn a_j a_{j+1}} f p`,

which gives the bound `≤ 2 · ∑_{p ∈ U} f p` for `f ≥ 0`.

The formal proof splits into:

* `window_index_le_succ` — two indices `i < j` whose windows share a prime satisfy `j ≤ i + 1`
  (the quantitative form of "windows `i` and `i+2` are disjoint");
* `card_le_two_of_lt_succ` — a finite set of naturals in which any two distinct elements differ
  by at most one has at most two elements;
* the interchange of summation (valid because each window is contained in `U`) and the
  pointwise multiplicity bound.
-/

namespace Work.BMF.SD

open Finset Real

/-- The window start is positive. -/
private lemma win_pos (P : ℝ) (hP : 0 < P) (j : ℕ) : 0 < P * (7 / 5 : ℝ) ^ j :=
  mul_pos hP (pow_pos (by norm_num) j)

/-- The window starts are monotone. -/
private lemma win_mono (P : ℝ) (hP : 0 < P) {i j : ℕ} (hij : i ≤ j) :
    P * (7 / 5 : ℝ) ^ i ≤ P * (7 / 5 : ℝ) ^ j :=
  mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) hij) hP.le

/-- The window starts are strictly increasing. -/
private lemma win_lt (P : ℝ) (hP : 0 < P) {i j : ℕ} (hij : i < j) :
    P * (7 / 5 : ℝ) ^ i < P * (7 / 5 : ℝ) ^ j :=
  mul_lt_mul_of_pos_left (pow_lt_pow_right₀ (by norm_num) hij) hP

/-- Two windows of the grid sharing a prime have consecutive indices: the windows
`[a_i, a_{i+1}]` and `[a_j, a_{j+1}]` overlap only at the point `a_{i+1}`, and the ratio
`7/5` is `> 1`. -/
private lemma window_index_le_succ (P : ℝ) (hP : 0 < P) {p i j : ℕ}
    (hi : p ∈ Work.BMF.primesIn (P * (7 / 5) ^ i) (P * (7 / 5) ^ (i + 1)))
    (hj : p ∈ Work.BMF.primesIn (P * (7 / 5) ^ j) (P * (7 / 5) ^ (j + 1)))
    (_hij : i < j) : j ≤ i + 1 := by
  have hiU : (p : ℝ) ≤ P * (7 / 5) ^ (i + 1) :=
    primesIn_upper (le_of_lt (win_pos P hP (i + 1))) hi
  have hjL : P * (7 / 5) ^ j ≤ (p : ℝ) := primesIn_lower (win_pos P hP j) hj
  by_contra h
  push Not at h
  have hle : P * (7 / 5) ^ (i + 2) ≤ P * (7 / 5) ^ j := win_mono P hP (by omega)
  have hlt : P * (7 / 5) ^ (i + 1) < P * (7 / 5) ^ (i + 2) := win_lt P hP (by omega)
  linarith

/-- A finite set of naturals in which any two distinct elements differ by at most one has at
most two elements. -/
private lemma card_le_two_of_lt_succ {T : Finset ℕ}
    (h : ∀ i ∈ T, ∀ j ∈ T, i < j → j ≤ i + 1) : T.card ≤ 2 := by
  rcases T.eq_empty_or_nonempty with he | hne
  · simp [he]
  · have hmem : T.min' hne ∈ T := Finset.min'_mem T hne
    have hsub : T ⊆ ({T.min' hne, T.min' hne + 1} : Finset ℕ) := by
      intro j hj
      rcases lt_trichotomy j (T.min' hne) with hlt | heq | hgt
      · exact absurd (Finset.min'_le T j hj) (not_le.mpr hlt)
      · simp [heq]
      · have h' := h (T.min' hne) hmem j hj hgt
        simp only [Finset.mem_insert, Finset.mem_singleton]
        omega
    calc T.card ≤ ({T.min' hne, T.min' hne + 1} : Finset ℕ).card := Finset.card_le_card hsub
      _ ≤ 2 := Finset.card_le_two

theorem window_sums_le_two (P : ℝ) (hP : 0 < P) (S U : Finset ℕ) (f : ℕ → ℝ)
    (hf : ∀ p, 0 ≤ f p)
    (hsub : ∀ j ∈ S, Work.BMF.primesIn (P * (7 / 5) ^ j) (P * (7 / 5) ^ (j + 1)) ⊆ U) :
    ∑ j ∈ S, ∑ p ∈ Work.BMF.primesIn (P * (7 / 5) ^ j) (P * (7 / 5) ^ (j + 1)), f p
      ≤ 2 * ∑ p ∈ U, f p := by
  classical
  set W : ℕ → Finset ℕ :=
    fun j => Work.BMF.primesIn (P * (7 / 5) ^ j) (P * (7 / 5) ^ (j + 1)) with hW
  -- each window sum may be viewed as a sum over `U` of the corresponding indicator
  have hstep : ∀ j ∈ S, ∑ p ∈ W j, f p = ∑ p ∈ U, (if p ∈ W j then f p else 0) := by
    intro j hj
    rw [← Finset.sum_subset (s₁ := W j) (s₂ := U) (f := fun q => if q ∈ W j then f q else 0)
      (hsub j hj) (fun x _ hx => by simp [hx])]
    exact Finset.sum_congr rfl (fun q hq => by simp [hq])
  -- pointwise multiplicity bound: at most two windows contain a given prime
  have hbound : ∀ p ∈ U, ∑ j ∈ S, (if p ∈ W j then f p else 0) ≤ 2 * f p := by
    intro p _
    have hcard : (S.filter (fun j => p ∈ W j)).card ≤ 2 := by
      apply card_le_two_of_lt_succ
      intro i hi j hj hij
      have hiW : p ∈ W i := (Finset.mem_filter.mp hi).2
      have hjW : p ∈ W j := (Finset.mem_filter.mp hj).2
      exact window_index_le_succ P hP hiW hjW hij
    calc ∑ j ∈ S, (if p ∈ W j then f p else 0)
        = ∑ j ∈ S.filter (fun j => p ∈ W j), f p :=
          (Finset.sum_filter (fun j => p ∈ W j) (fun _ => f p)).symm
      _ = (S.filter (fun j => p ∈ W j)).card * f p := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 2 * f p :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (hf p)
  calc ∑ j ∈ S, ∑ p ∈ W j, f p
      = ∑ j ∈ S, ∑ p ∈ U, (if p ∈ W j then f p else 0) :=
        Finset.sum_congr rfl (fun j hj => hstep j hj)
    _ = ∑ p ∈ U, ∑ j ∈ S, (if p ∈ W j then f p else 0) := Finset.sum_comm
    _ ≤ ∑ p ∈ U, 2 * f p := Finset.sum_le_sum (fun p hp => hbound p hp)
    _ = 2 * ∑ p ∈ U, f p := (Finset.mul_sum U f 2).symm

end Work.BMF.SD
