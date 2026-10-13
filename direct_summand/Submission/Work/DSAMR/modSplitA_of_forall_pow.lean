import Mathlib
import Submission.Work.DSAMR.Defs
import Submission.Work.DSAM3.Api

namespace Work.DSAMR

universe u

/-- **The tower endgame.**

`Work.DSAM3.ModSplitA P ε ψ I c` (`Submission/Work/DSAM3/Basic.lean`) is the `A`-linear form of the
frozen `DSMap.Mix.ModSplit`: the existence of `t : P⁰ →ₗ[A] W ⧸ I` with `t ∘ d⁻¹ = 0` and
`t (ε 1) = mk I c`.  The achievable values form a submodule, and in particular
`Work.DSAM3.modSplitA_mul` (AM1) turns a splitting with value `c` into one with value `c * d` for
any `d ∈ W`.

If for **every** level `j` a splitting with value `ϖ j ^ L` exists (some fixed loss `L`), then every
value `ϖ k` is achieved: take `t := L` (so `p^L ≥ L`), `j := k + L`; multiplying the value
`ϖ (k+L) ^ L` by `ϖ (k+L) ^ (p^L - L)` gives `ϖ (k+L) ^ (p^L) = ϖ k` by the iterated tower
relation `Work.DSAMR.pow_tower` (`ϖ (k+t) ^ p^t = ϖ k`).  This is how the AMR node removes the
loss `L` produced by the truncation argument entirely.

Hints.  `Nat.lt_pow_self`/`Nat.le_self_pow` gives `L ≤ p^L` from `hp : 1 < p`; then
`pow_add` gives `ϖ j ^ (L + (p^L - L)) = ϖ j ^ (p^L)` and `Work.DSAMR.pow_tower ϖ p hϖ k L` closes
the value.  The `L = 0` case is covered by the same argument. -/
theorem modSplitA_of_forall_pow {A W : Type u} [CommRing A] [CommRing W] (ψ : A →+* W)
    (p : ℕ) (hp : 1 < p) (ϖ : ℕ → W) (hϖ : ∀ k, ϖ (k + 1) ^ p = ϖ k) (I : Ideal W)
    (P : CochainComplex (ModuleCat.{u} A) ℤ) (ε : ModuleCat.of A A ⟶ P.X 0) (L : ℕ)
    (h : ∀ j : ℕ, DSAM3.ModSplitA P ε ψ I (ϖ j ^ L)) :
    ∀ k : ℕ, DSAM3.ModSplitA P ε ψ I (ϖ k) := by
  intro k
  -- `L ≤ p ^ L`, from `hp : 1 < p`.
  have hL : L ≤ p ^ L := le_of_lt (Nat.lt_pow_self (n := L) (a := p) hp)
  -- The value `ϖ (k+L) ^ L` scaled by `ϖ (k+L) ^ (p^L - L)` is `ϖ k`.
  have hval : ϖ (k + L) ^ L * ϖ (k + L) ^ (p ^ L - L) = ϖ k := by
    rw [← pow_add, Nat.add_sub_of_le hL, pow_tower ϖ p hϖ k L]
  rw [← hval]
  exact DSAM3.modSplitA_mul P ε ψ I _ _ (h (k + L))

end Work.DSAMR
