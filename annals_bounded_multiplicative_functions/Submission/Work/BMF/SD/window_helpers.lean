import Mathlib
import Submission.Work.BMF.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Elementary facts about `primesIn` and the geometric windows `P · (7/5)^j`

Vocabulary shared by the proof of `Work.BMF.SD.good_window_pairs` and its auxiliary lemmas:

* `primesIn_lower`, `primesIn_upper`, `primesIn_prime`, `primesIn_mono` — the interval members of
  `Work.BMF.primesIn a b = (Finset.Icc ⌈a⌉₊ ⌊b⌋₊).filter Nat.Prime` lie between `a` and `b`, are
  prime, and `primesIn` is monotone in both endpoints;
* the arithmetic of the geometric grid `a_j = P (7/5)^j`, whose consecutive ratio is exactly `7/5`
  (`5 * a_{j+1} = 7 * a_j`) and which is nondecreasing.
-/

namespace Work.BMF.SD

open Finset Real

/-- A prime of `primesIn a b` is at least `a`. -/
lemma primesIn_lower {a b : ℝ} (_ha : 0 < a) {p : ℕ} (hp : p ∈ Work.BMF.primesIn a b) :
    a ≤ (p : ℝ) := by
  rw [Work.BMF.primesIn, Work.BMF.natIcc, Finset.mem_filter, Finset.mem_Icc] at hp
  exact le_trans (Nat.le_ceil a) (by exact_mod_cast hp.1.1)

/-- A prime of `primesIn a b` is at most `b`. -/
lemma primesIn_upper {a b : ℝ} (hb : 0 ≤ b) {p : ℕ} (hp : p ∈ Work.BMF.primesIn a b) :
    (p : ℝ) ≤ b := by
  rw [Work.BMF.primesIn, Work.BMF.natIcc, Finset.mem_filter, Finset.mem_Icc] at hp
  exact le_trans (by exact_mod_cast hp.1.2) (Nat.floor_le hb)

/-- Every element of `primesIn a b` is prime. -/
lemma primesIn_prime {a b : ℝ} {p : ℕ} (hp : p ∈ Work.BMF.primesIn a b) : Nat.Prime p :=
  (Finset.mem_filter.mp hp).2

/-- Every element of `primesIn a b` is a positive natural number. -/
lemma primesIn_pos {a b : ℝ} {p : ℕ} (hp : p ∈ Work.BMF.primesIn a b) : 0 < p :=
  (primesIn_prime hp).pos

/-- `primesIn` is monotone in both endpoints. -/
lemma primesIn_mono {a a' b b' : ℝ} (ha : a' ≤ a) (hb : b ≤ b') :
    Work.BMF.primesIn a b ⊆ Work.BMF.primesIn a' b' := by
  intro p hp
  rw [Work.BMF.primesIn, Work.BMF.natIcc, Finset.mem_filter, Finset.mem_Icc] at hp ⊢
  exact ⟨⟨le_trans (Nat.ceil_mono ha) hp.1.1, le_trans hp.1.2 (Nat.floor_mono hb)⟩, hp.2⟩

/-- `primesIn` is monotone in the upper endpoint. -/
lemma primesIn_mono_b {a b b' : ℝ} (hb : b ≤ b') :
    Work.BMF.primesIn a b ⊆ Work.BMF.primesIn a b' :=
  primesIn_mono le_rfl hb

/-- The geometric grid ratio is `7/5`. -/
lemma seven_fifths_pow_pos (j : ℕ) : (0 : ℝ) < (7 / 5 : ℝ) ^ j := pow_pos (by norm_num) j

/-- The geometric grid is nondecreasing. -/
lemma one_le_seven_fifths_pow (j : ℕ) : (1 : ℝ) ≤ (7 / 5 : ℝ) ^ j :=
  one_le_pow₀ (show (1 : ℝ) ≤ 7 / 5 by norm_num)

/-- Consecutive window starts: `a_{j+1} = (7/5) · a_j`. -/
lemma seven_fifths_pow_succ (j : ℕ) : (7 / 5 : ℝ) ^ (j + 1) = (7 / 5 : ℝ) ^ j * (7 / 5) :=
  pow_succ _ _

end Work.BMF.SD
