import Mathlib

-- v4.35 port: restore the v4.34 instance-unification behaviour (respectTransparency) in this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.KMTPlan.A6.ConcAux

/-- **Divisibility of `G` on a `p`-adic ball propagates to all congruent integers.**

If `G : ℤ[X]` is divisible by `p ^ k` at every representative `x < p ^ k` of the residue class of
`a` modulo `p ^ m` (i.e. on the ball of level `m` around `a` inside `ℤ/p^k`), then `p ^ k ∣ G.eval y`
for *every* integer `y ≡ a (mod p^m)` — not merely for the representatives in `[0, p^k)`.

The proof replaces `y` by its canonical representative `Y.val` modulo `p ^ k` (`Y` is the image of
`y` in `ZMod (p^k)`): since `p ^ m ∣ p ^ k` and `y ≡ Y.val (mod p^k)`, the two are congruent modulo
`p^m` as well, so the ball hypothesis applies at `Y`. Finally `y ≡ Y.val (mod p^k)` and
`(y - Y.val) ∣ G.eval y - G.eval Y.val` give the transfer of divisibility. -/
theorem dvd_eval_of_ball (G : Polynomial ℤ) (p k m : ℕ) [Fact p.Prime] (hm : m ≤ k)
    {a : ZMod (p ^ k)}
    (hball : ∀ x : ZMod (p ^ k), (p : ℤ) ^ m ∣ ((x.val : ℤ) - (a.val : ℤ)) → (p : ℤ) ^ k ∣ G.eval (x.val : ℤ))
    {y : ℤ} (hy : (p : ℤ) ^ m ∣ (y - (a.val : ℤ))) : (p : ℤ) ^ k ∣ G.eval y := by
  -- the canonical representative of `y` modulo `p ^ k`
  let Y : ZMod (p ^ k) := (y : ZMod (p ^ k))
  -- `Y.val` and `y` agree modulo `p ^ k`
  have hYs : ((Y.val : ℤ) : ZMod (p ^ k)) = (y : ZMod (p ^ k)) := by
    rw [Int.cast_natCast]
    exact ZMod.natCast_zmod_val Y
  have hGy : (p : ℤ) ^ k ∣ y - (Y.val : ℤ) := by
    have h := (ZMod.intCast_eq_intCast_iff_dvd_sub (Y.val : ℤ) y (p ^ k)).mp hYs
    simpa using h
  -- hence also modulo `p ^ m`, since `p ^ m ∣ p ^ k`
  have hmk : (p : ℤ) ^ m ∣ (p : ℤ) ^ k := pow_dvd_pow _ hm
  have hY0 : (p : ℤ) ^ m ∣ y - (Y.val : ℤ) := dvd_trans hmk hGy
  -- so `Y.val` lies in the ball of level `m` around `a`
  have hYA : (p : ℤ) ^ m ∣ (Y.val : ℤ) - (a.val : ℤ) := by
    have h := dvd_sub hy hY0
    have heq : (y - (a.val : ℤ)) - (y - (Y.val : ℤ)) = (Y.val : ℤ) - (a.val : ℤ) := by ring
    rwa [heq] at h
  -- the ball hypothesis applies at `Y`
  have hG := hball Y hYA
  -- and divisibility transfers from `Y.val` to `y`
  have hsub : (p : ℤ) ^ k ∣ G.eval y - G.eval (Y.val : ℤ) :=
    dvd_trans hGy (Polynomial.sub_dvd_eval_sub y (Y.val : ℤ) G)
  have hsum : (p : ℤ) ^ k ∣ G.eval y := by
    have h := dvd_add hsub hG
    simpa [sub_add_cancel] using h
  exact hsum

end Work.KMTPlan.A6.ConcAux
