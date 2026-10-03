/-
Copyright: work note for node N3 (`ORLyndon`).  Comments only -- this file exists so that the
delegated lemma `Work.ORLyndon.orderOf_presentRho_eps_ne_zero` can `depend_on` a module carrying the
proof plan, and so that the plan is readable by every colleague working in this directory.

# Plan: `orderOf (presentRho (u ^ l) u) = l` from non-vanishing exponent sums

`theorem orderOf_presentRho_eps_ne_zero {α : Type u} [DecidableEq α] (u : FreeGroup α) (l : ℕ)
  (hl : 1 ≤ l) (hsne : (relatorLetters u).Nonempty)
  (hne : ∀ x ∈ relatorLetters u, eps x u ≠ 0) :
  orderOf (presentRho (u ^ l) u) = l`

## Why this statement (and not the KMS route)

`Work.ORLyndon.orderOf_presentRho` (in `powDefs.lean`) derives the same conclusion from
`¬ IsProperPower u`, but it goes through `Work.OROneRel.kms_torsion_at`, whose chain contains the
`sorry` of `Submission/Work/OROneRel/magnus_step_root.lean` (the open Masters--Linton Case~2 step).
That is exactly the `sorryAx` we must avoid.  The statement above needs **no** KMS input: the
non-vanishing exponent sums alone force the order, by an abelianisation argument.  (It is *not*
weaker for the intended consumer: `Work.ORLyndon.EpsNeZeroDescent` supplies both
`2 ≤ relatorNorm u`, whence `(relatorLetters u).Nonempty`, and
`∀ x ∈ relatorLetters u, eps x u ≠ 0`.)

## The argument (short, elementary -- no roots, no gcd, no Bezout)

1. `hl : 1 ≤ l` and `presentRho_relator : presentRho r r = 1` give
   `(presentRho (u^l) u)^l = presentRho (u^l) (u^l) = 1`, hence `orderOf (presentRho (u^l) u) ∣ l`
   (`orderOf_dvd_iff_pow_eq_one`).

2. For the reverse divisibility pick `x₀ ∈ relatorLetters u` (`hsne`), put `d : ℤ := eps x₀ u`
   (so `d ≠ 0` by `hne`) and define the *character*
   `c : α → ℤ := fun x => if x = x₀ then 1 else 0`, i.e. the "coefficient functional" `δ_{x₀}`.
   Then `Σ_x c x * eps x u = eps x₀ u = d ≠ 0`.  (This is the point of the argument: *any* single
   letter with non-zero exponent sum already gives a non-zero character, so no greatest common
   divisor and no Bezout identity is needed.)

3. Let `N : ℕ := l * d.natAbs` (so `N ≠ 0`; `l * |d|` also works) and consider the homomorphism
   `f : FreeGroup α →* Multiplicative (ZMod N)`, `f x := Multiplicative.ofAdd ((c x : ℤ) : ZMod N)`.
   Its value on `u` is `Multiplicative.ofAdd (d : ZMod N)`: use `FreeGroup.lift_unique`/the
   defining property of `FreeGroup.lift` plus `eps` being the exponent sum
   (`Work.OROneRel.eps_eq_toAdd_sigma` converts `eps` into `Work.OROneRel.sigma`; or reprove
   `FreeGroup.lift (fun x => Multiplicative.ofAdd (eps x u)) u = Multiplicative.ofAdd d` directly
   from the definition `eps t r = wordEps t r.toWord` by induction on `toWord u`).

4. `(d : ZMod N) * l = (l * d : ℤ) = 0` in `ZMod N` (as `N = l * |d|` divides `l * d`), so
   `f (u^l) = (f u)^l = 1`.  Hence `f` kills the relator, so the universal property of
   `PresentedGroup` (`PresentedGroup.toGroup`, or `PresentedGroup.lift` followed by
   `MonoidHom.comp`) produces
   `φ : OneRelatorGroup (u^l) →* Multiplicative (ZMod N)` with `φ (presentRho (u^l) u)
     = Multiplicative.ofAdd (d : ZMod N)`.

5. `orderOf (Multiplicative.ofAdd (d : ZMod N)) = l`.  This is the only arithmetic step:
   in the additive group `ZMod N = ZMod (l * |d|)` the order of `d` is
   `N / gcd(d, N) = l * |d| / |d| = l`
   (`ZMod.addOrderOf_coe`, `ZMod.natCast_self`, or `orderOf_dvd_iff_natCast_eq_zero` plus
   `Nat.gcd_eq_left`-style bookkeeping; note `gcd (d) (l * |d|) = |d|`).

6. `orderOf (φ x) ∣ orderOf x` (`orderOf_map_dvd`), so `l ∣ orderOf (presentRho (u^l) u)`;
   with (1) this gives `orderOf (presentRho (u^l) u) = l` via `Nat.dvd_antisymm`.

## Interface notes

* `eps x u` is `Word`-level (`Work.OROneRel.eps t r = wordEps t r.toWord`), and for
  `x ∉ relatorLetters u` it is `0`; this is why only the letters of `u` matter.
* `relatorLetters` is a `Set`, so to speak of its elements one uses `hne` directly; the finiteness
  is not needed anywhere in the argument above.  (In particular `Finset`/`Finsupp` machinery and
  `Int.gcd` are *not* required -- this is the reason the statement is cheap.)
* `presentRho (u^l) u` is the class of the root `u` in `⟨α | u^l⟩`, and
  `Work.ORLyndon.annChain`'s residual `EpsNeZeroDescent` asks for exactly this order statement in
  the case where every exponent sum is non-zero.
-/
import Mathlib
import Submission.Work.ORLyndon.Lyndon
import Submission.Work.OROneRel.MagnusRewrite
import Submission.Work.OROneRel.Basic

set_option autoImplicit false

namespace Work.ORLyndon

end Work.ORLyndon
