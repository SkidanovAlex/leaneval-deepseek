import Mathlib
import Submission.Work.FIArea2.card_y_sols
import Submission.Work.FIArea2.sum_two_pow_padicValNat

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Counting solutions of `x ^ 2 = y ^ 2` in `ZMod (2 ^ n)`

We prove that the number of pairs `(x, y)` with `x ^ 2 = y ^ 2` in `(ZMod (2 ^ n)) ^ 2`
equals `n * 2 ^ n` for `n ≥ 1`.

The proof parameterises solutions by the difference `d = x - y`: for a fixed `d` the
solutions `y` of `(y + d) ^ 2 = y ^ 2` are either empty (`d` odd), everything (`d = 0`),
or a coset of `ker (2 * d * ·)` of size `2 ^ (v₂ d + 1)` (`d` even, `d ≠ 0`).
-/

namespace Work.FIArea2

open Finset

/-- The number of solutions `y` of `(y + d) ^ 2 = y ^ 2` in `ZMod (2 ^ n)`, as a
function of the value `m = d.val` of `d`. -/
def solF (n m : ℕ) : ℕ :=
  if m = 0 then 2 ^ n else if 2 ∣ m then 2 ^ (padicValNat 2 m + 1) else 0

/-- The equivalence `ZMod n ≃ Fin n` given by `ZMod.val`. -/
def zmodValEquiv (n : ℕ) [NeZero n] : ZMod n ≃ Fin n where
  toFun d := ⟨d.val, ZMod.val_lt d⟩
  invFun i := (i : ℕ)
  left_inv d := ZMod.natCast_zmod_val d
  right_inv i := by
    apply Fin.ext
    exact ZMod.val_natCast_of_lt i.isLt

/-- Reindexing a sum over `ZMod (2 ^ n)` as a sum over `Finset.range (2 ^ n)` via `ZMod.val`. -/
lemma sum_val_reindex (n : ℕ) (H : ℕ → ℕ) :
    (∑ d : ZMod (2 ^ n), H d.val) = ∑ i ∈ Finset.range (2 ^ n), H i := by
  rw [← Fin.sum_univ_eq_sum_range H (2 ^ n)]
  exact Fintype.sum_equiv (zmodValEquiv (2 ^ n))
    (fun d : ZMod (2 ^ n) => H d.val) (fun i : Fin (2 ^ n) => H i.val) (fun d => rfl)

/-- **Fiber decomposition.**  The solutions of `x ^ 2 = y ^ 2`, grouped by the difference
`d = x - y`, give a sum of the one-variable fiber counts. -/
lemma card_sq_eq_sq_eq_sum (n : ℕ) :
    (Finset.univ.filter (fun p : ZMod (2 ^ n) × ZMod (2 ^ n) => p.1 ^ 2 = p.2 ^ 2)).card
      = ∑ d : ZMod (2 ^ n),
          (Finset.univ.filter (fun y : ZMod (2 ^ n) => (y + d) ^ 2 = y ^ 2)).card := by
  have hmain := Finset.card_eq_sum_card_fiberwise
    (s := (Finset.univ.filter (fun p : ZMod (2 ^ n) × ZMod (2 ^ n) => p.1 ^ 2 = p.2 ^ 2)))
    (t := (Finset.univ : Finset (ZMod (2 ^ n))))
    (f := fun p : ZMod (2 ^ n) × ZMod (2 ^ n) => p.1 - p.2)
    (by intro x hx; exact Finset.mem_univ _)
  rw [hmain]
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.card_bij (fun (p : ZMod (2 ^ n) × ZMod (2 ^ n)) (_ : p ∈ _) => p.2)
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    obtain ⟨hp1, hp2⟩ := hp
    have hthis : p.1 = d + p.2 := by rw [sub_eq_iff_eq_add] at hp2; exact hp2
    rw [← hp1, hthis, add_comm]
  · intro p1 hp1 p2 hp2 heq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp1 hp2
    obtain ⟨_, hp1b⟩ := hp1
    obtain ⟨_, hp2b⟩ := hp2
    have e1 : p1.1 = d + p1.2 := by rw [sub_eq_iff_eq_add] at hp1b; exact hp1b
    have e2 : p2.1 = d + p2.2 := by rw [sub_eq_iff_eq_add] at hp2b; exact hp2b
    have h2 : p1.2 = p2.2 := heq
    ext <;> simp [e1, e2, h2]
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    refine ⟨(y + d, y), ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hy, by abel⟩

/-- Evaluation of the arithmetic sum coming from the fiber decomposition. -/
lemma sum_solF (n : ℕ) (hn : 1 ≤ n) :
    (∑ i ∈ Finset.range (2 ^ n), solF n i) = n * 2 ^ n := by
  have h0 : (0 : ℕ) ∈ Finset.range (2 ^ n) := by
    rw [Finset.mem_range]; positivity
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (2 ^ n)) (fun i => i = 0) (solF n)]
  have hA : (∑ i ∈ (Finset.range (2 ^ n)).filter (fun i => i = 0), solF n i) = 2 ^ n := by
    rw [Finset.sum_filter, Finset.sum_ite_eq' _ 0 (solF n), if_pos h0]
    simp [solF]
  have hB : (∑ i ∈ (Finset.range (2 ^ n)).filter (fun i => ¬ (i = 0)), solF n i)
      = (n - 1) * 2 ^ n := by
    rw [show (∑ i ∈ (Finset.range (2 ^ n)).filter (fun i => ¬ (i = 0)), solF n i)
          = ∑ i ∈ (Finset.range (2 ^ n)).filter (fun i => ¬ (i = 0)),
              (if 2 ∣ i then 2 ^ (padicValNat 2 i + 1) else 0) from by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mem_filter] at hi
        simp [solF, hi.2]]
    rw [← Finset.sum_filter]
    rw [Finset.filter_filter]
    have h := sum_two_pow_padicValNat n
    simp only [ne_eq] at h ⊢
    exact h
  rw [hA, hB]
  have hpred : n - 1 + 1 = n := Nat.succ_pred_eq_of_pos hn
  nlinarith [pow_pos (by norm_num : (0 : ℕ) < 2) n]

/-- The number of solutions of `(y + d) ^ 2 = y ^ 2` in `ZMod (2 ^ n)` is `solF n d.val`. -/
lemma card_y_sols_eq_solF (n : ℕ) (d : ZMod (2 ^ n)) :
    (Finset.univ.filter (fun y : ZMod (2 ^ n) => (y + d) ^ 2 = y ^ 2)).card = solF n d.val := by
  rw [card_y_sols n d]
  simp only [solF, ZMod.val_eq_zero]

theorem card_sq_eq_sq_two_pow (ν : ℕ) (hν : 1 ≤ ν) :
    ((Finset.univ : Finset (ZMod (2 ^ ν) × ZMod (2 ^ ν))).filter
        (fun p => p.1 ^ 2 = p.2 ^ 2)).card = ν * 2 ^ ν := by
  rw [card_sq_eq_sq_eq_sum ν]
  rw [show (∑ d : ZMod (2 ^ ν),
        (Finset.univ.filter (fun y : ZMod (2 ^ ν) => (y + d) ^ 2 = y ^ 2)).card)
      = ∑ d : ZMod (2 ^ ν), solF ν d.val from
    Finset.sum_congr rfl fun d _ => card_y_sols_eq_solF ν d]
  rw [sum_val_reindex ν (solF ν)]
  exact sum_solF ν hν

end Work.FIArea2
