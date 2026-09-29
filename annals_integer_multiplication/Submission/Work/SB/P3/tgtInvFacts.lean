import Mathlib
import Submission.Work.Layout.Shared
import Submission.Work.Layout.unslicesIdx

namespace Work.SB.P3

open Work.Layout

/-- Index arithmetic for the output layout maps `tgtIdx`/`invIdx2`: the map
`f ↦ tgtIdx n B (f/n) (f%n)` is a bijection of `range (A*B*n)` onto itself, with inverse
`t ↦ (invIdx2 n B t).1 * n + (invIdx2 n B t).2`.  All five facts (range, injectivity, range of
the inverse, and the two inverse laws) are direct consequences of `unslicesIdx`. -/
theorem tgtInvFacts (A n B : ℕ) (hn : 0 < n) (hB : 0 < B) :
    (∀ f, f < A * B * n → Work.Layout.tgtIdx n B (f / n) (f % n) < A * B * n) ∧
    (∀ f f', f < A * B * n → f' < A * B * n →
      Work.Layout.tgtIdx n B (f / n) (f % n) = Work.Layout.tgtIdx n B (f' / n) (f' % n) → f = f') ∧
    (∀ t, t < A * B * n → (Work.Layout.invIdx2 n B t).1 * n + (Work.Layout.invIdx2 n B t).2 < A * B * n) ∧
    (∀ t, t < A * B * n →
      Work.Layout.tgtIdx n B (((Work.Layout.invIdx2 n B t).1 * n + (Work.Layout.invIdx2 n B t).2) / n)
        (((Work.Layout.invIdx2 n B t).1 * n + (Work.Layout.invIdx2 n B t).2) % n) = t) ∧
    (∀ f, f < A * B * n →
      (Work.Layout.invIdx2 n B (Work.Layout.tgtIdx n B (f / n) (f % n))).1 * n +
        (Work.Layout.invIdx2 n B (Work.Layout.tgtIdx n B (f / n) (f % n))).2 = f) := by
  have hU := unslicesIdx A n B hn hB
  have hswap : A * n * B = A * B * n := by ring
  have hdiv : ∀ f, f < A * B * n → f / n < A * B := by
    intro f hf
    rw [Nat.div_lt_iff_lt_mul hn]
    exact hf
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro f hf
    rw [← hswap]
    exact hU.1 (f / n) (f % n) (hdiv f hf) (Nat.mod_lt f hn)
  · intro f f' hf hf' heq
    have h1 := hU.2.1 (f / n) (f % n) (hdiv f hf) (Nat.mod_lt f hn)
    have h2 := hU.2.1 (f' / n) (f' % n) (hdiv f' hf') (Nat.mod_lt f' hn)
    have hpair : (f / n, f % n) = (f' / n, f' % n) := by rw [← h1, ← h2, heq]
    have hfst : f / n = f' / n := congrArg Prod.fst hpair
    have hsnd : f % n = f' % n := congrArg Prod.snd hpair
    calc f = n * (f / n) + f % n := (Nat.div_add_mod f n).symm
      _ = n * (f' / n) + f' % n := by rw [hfst, hsnd]
      _ = f' := Nat.div_add_mod f' n
  · intro t ht
    obtain ⟨hs, hj⟩ := hU.2.2.2 t (by rw [hswap]; exact ht)
    calc (invIdx2 n B t).1 * n + (invIdx2 n B t).2
        < (invIdx2 n B t).1 * n + n := Nat.add_lt_add_left hj _
      _ = ((invIdx2 n B t).1 + 1) * n := by ring
      _ ≤ (A * B) * n := Nat.mul_le_mul_right n (Nat.succ_le_of_lt hs)
      _ = A * B * n := by ring
  · intro t ht
    obtain ⟨hs, hj⟩ := hU.2.2.2 t (by rw [hswap]; exact ht)
    have hdm : ((invIdx2 n B t).1 * n + (invIdx2 n B t).2) / n = (invIdx2 n B t).1 := by
      rw [Nat.mul_comm (invIdx2 n B t).1 n, Nat.mul_add_div hn, Nat.div_eq_of_lt hj,
        Nat.add_zero]
    have hdm' : ((invIdx2 n B t).1 * n + (invIdx2 n B t).2) % n = (invIdx2 n B t).2 := by
      rw [Nat.mul_comm (invIdx2 n B t).1 n, Nat.mul_add_mod, Nat.mod_eq_of_lt hj]
    rw [hdm, hdm']
    exact hU.2.2.1 t (by rw [hswap]; exact ht)
  · intro f hf
    have h := hU.2.1 (f / n) (f % n) (hdiv f hf) (Nat.mod_lt f hn)
    rw [h]
    show (f / n) * n + f % n = f
    rw [Nat.mul_comm (f / n) n]
    exact Nat.div_add_mod f n

end Work.SB.P3
