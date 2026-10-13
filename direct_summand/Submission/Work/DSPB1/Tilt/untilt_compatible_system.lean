import Mathlib
import Submission.Work.DSMap.Map

/-!
# DSPB1 — every compatible system of `p`-power roots in a `p`-adically complete ring is an untilt

This file proves `Work.DSPB1.Tilt.untilt_compatible_system`:

> if `C` is a commutative ring in which `p` is a non-unit and which is complete for the
> `p`-adic topology, and `κ : ℕ → C` is a *compatible system*, i.e. `κ (k + 1) ^ p = κ k`
> for all `k`, then there is an element `ϖf` of the tilt `PreTilt C p = Perfection (C ⧸ (p)) p`
> whose Teichmüller untilt `PreTilt.untilt ϖf` is *exactly* `κ 0`.

Note what is *not* assumed: `C` need not be `p`-torsion-free, and the roots `κ n` need not have
anything to do with a pseudo-uniformizer.  The point is that the compatible system
`n ↦ κ n mod p` is *already* an element of `Perfection (C ⧸ (p)) p` — its compatibility is
`hκ` — and the Teichmüller limit of any of its lifts is `κ 0`: the lift `κ n` of the `n`-th
coefficient has `p^n`-th power *exactly* `κ 0` (`compat_pow_iterate`), so the defining
approximation condition of `Perfection.teichmuller_spec` is met with no error term at all.

This is the `PreTilt`-level statement of `Work.DSPB1.varpiTilt_untilt` (the ϖ-flatness `PB1`),
with the concrete system `n ↦ ϖ_n` replaced by an arbitrary one.

## Contents

* `Work.DSPB1.Tilt.compat_pow_iterate` — the tower property `κ (k + n) ^ p ^ n = κ k`;
* `Work.DSPB1.Tilt.untilt_compatible_system` — the requested statement.
-/

namespace Work.DSPB1.Tilt

/-- The tower property of a compatible system of `p`-power roots: `κ (k + n)` is a `p ^ n`-th
root of `κ k`.  Obtained by iterating the defining relation `κ (k + 1) ^ p = κ k`. -/
theorem compat_pow_iterate {C : Type*} [CommRing C] (κ : ℕ → C) (p : ℕ)
    (hκ : ∀ k, κ (k + 1) ^ p = κ k) (k n : ℕ) : κ (k + n) ^ p ^ n = κ k := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc κ (k + (n + 1)) ^ p ^ (n + 1)
        = (κ (k + n + 1) ^ p) ^ p ^ n := by rw [Nat.add_succ, pow_succ', pow_mul]
      _ = κ (k + n) ^ p ^ n := by rw [hκ (k + n)]
      _ = κ k := ih

/-- **A compatible system of `p`-power roots is an untilt.**  The compatible system
`ϖf := (n ↦ κ n mod p)` is an element of `PreTilt C p`, and `PreTilt.untilt ϖf = κ 0` because
the lift `κ n` of its `n`-th coefficient satisfies `κ n ^ p ^ n = κ 0` on the nose
(`compat_pow_iterate`), which is the approximation condition of `Perfection.teichmuller_spec`. -/
theorem untilt_compatible_system {p : ℕ} [Fact p.Prime] {C : Type*} [CommRing C]
    [Fact ¬IsUnit (p : C)] [Pc : IsAdicComplete (Ideal.span {(p : C)}) C]
    (κ : ℕ → C) (hκ : ∀ k, κ (k + 1) ^ p = κ k) :
    ∃ ϖf : PreTilt C p, PreTilt.untilt ϖf = κ 0 := by
  -- `Pc`, the completeness instance required by `PreTilt.untilt`, is already an instance
  -- binder of the statement, so nothing has to be introduced here.
  refine ⟨⟨fun n => Ideal.Quotient.mk (Ideal.span {(p : C)}) (κ n), fun n => ?_⟩, ?_⟩
  · -- compatibility in `C ⧸ (p)`: `(κ (n+1) mod p) ^ p = κ n mod p`
    rw [← map_pow, hκ n]
  · -- the untilt is computed through `Perfection.teichmuller_spec`
    refine Perfection.teichmuller_spec fun n => ⟨κ n, rfl, ?_⟩
    rw [show κ n ^ p ^ n = κ 0 from by simpa using compat_pow_iterate κ p hκ 0 n]

end Work.DSPB1.Tilt
