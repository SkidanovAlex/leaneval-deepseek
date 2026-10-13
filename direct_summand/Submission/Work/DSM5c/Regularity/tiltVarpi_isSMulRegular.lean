import Mathlib
import Submission.Work.DSM5c.Charts
import Submission.Work.DSPB2.Main

/-!
# DSM5c — `ϖ♭` is a non-zero-divisor on the tilt

This file proves `Work.DSM5c.Regularity.tiltVarpi_isSMulRegular`: in the tilt
`PreTilt W p = Perfection (W ⧸ (p)) p` of a ring `W` carrying a `DSMap.PerfectoidData p W`,
multiplication by the tilted pseudo-uniformizer `ϖ♭ = Work.DSM5c.tiltVarpi Q` is injective.

## The mathematics

Multiplication on `Perfection (W ⧸ (p)) p` is *coordinatewise*, so the hypothesis
`ϖ♭ * x = 0` says that for every `n`

  `(ϖ_n mod p) * (x_n) = 0`  in `W ⧸ (p)`,

and the compatibility of `x` says `x_n = (x_{n+1}) ^ p`.  Hence it suffices to prove the
following completely elementary statement about the *quotient* `W ⧸ (p)` (`p` prime, `W`
`p`-torsion-free with `ϖ_0 ^ p = p · v`, `v` a unit):

  **if `z ∈ W ⧸ (p)` and `(ϖ_n mod p) · z = 0`, then `z ^ p = 0`.**

Indeed `ϖ_0 ^ p = p v` forces `(ϖ_0 mod p) ^ p = 0` while `ϖ_0 ∉ (p)`, so `W ⧸ (p)` is *not*
reduced and `ϖ_n mod p` is a non-zero nilpotent — in particular a zero divisor.  But an
annihilator of `ϖ_n mod p` is much more special: descending along the tower
`ϖ_{k+1} ^ p = ϖ_k` (`(ϖ_k mod p) · z = (ϖ_{k+1} mod p) ^ (p-1) · ((ϖ_{k+1} mod p) · z)`)
reduces to `n = 0`, and then, lifting `z` to `Z ∈ W` with `ϖ_0 Z = p c`, multiplying by
`ϖ_0 ^ (p-1)` and cancelling the (regular) element `p` gives `v Z = c ϖ_0 ^ (p-1)`, so that
modulo `p`

  `z = (v⁻¹ c) · (ϖ_0 mod p) ^ (p - 1)`,

whence `z ^ p = (v⁻¹ c) ^ p · ((ϖ_0 mod p) ^ p) ^ (p - 1) = 0`.

The consequences are immediate: applying this to `z = x_{n+1}` yields `x_n = (x_{n+1}) ^ p = 0`
for every `n`, and `Perfection.ext` (here `Work.DSM5c.tilt_ext`) finishes.  Neither
`frobSurj`, `frobInj`, `complete` nor any unit-cancellation beyond `IsSMulRegular` is used.
-/

namespace Work.DSM5c.Regularity

open Work.DSM5c

variable {p : ℕ} [Fact p.Prime] {W : Type*} [CommRing W]

/-- **The key computation on the quotient.**  If `z ∈ W ⧸ (p)` is annihilated by the image of a
pseudo-uniformizer root `ϖ n`, then `z ^ p = 0`.  (So multiplication by `ϖ_n mod p` behaves like a
non-zero-divisor *up to `p`-th powers*.) -/
theorem pow_p_eq_zero_of_quot_varpi_mul_eq_zero (Q : DSMap.PerfectoidData p W) (n : ℕ)
    (z : ModP W p) (hz : Ideal.Quotient.mk (Ideal.span {(p : W)}) (Q.ϖ n) * z = 0) :
    z ^ p = 0 := by
  obtain ⟨hp1, hp1ne⟩ : p - 1 + 1 = p ∧ p - 1 ≠ 0 := by
    have h := (Fact.out : p.Prime).two_le
    omega
  -- Descend from `n` to `0` along the tower `ϖ_{k+1} ^ p = ϖ_k`.
  have descend : ∀ n : ℕ, ∀ z : ModP W p,
      Ideal.Quotient.mk (Ideal.span {(p : W)}) (Q.ϖ n) * z = 0 →
      Ideal.Quotient.mk (Ideal.span {(p : W)}) (Q.ϖ 0) * z = 0 := by
    intro n
    induction n with
    | zero => intro z hz; exact hz
    | succ n ih =>
      intro z hz
      refine ih z ?_
      have hpow : Q.ϖ n = Q.ϖ (n + 1) ^ (p - 1) * Q.ϖ (n + 1) := by
        conv_lhs => rw [← Q.root n]
        rw [congrArg (fun k => Q.ϖ (n + 1) ^ k) hp1.symm, pow_succ]
      rw [hpow, map_mul, mul_assoc, hz, mul_zero]
  have hz0 := descend n z hz
  -- Lift `z` to `W` and exploit `ϖ_0 ^ p = p * v`.
  obtain ⟨Z, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨v, hv⟩ := Q.unit
  have hmkp : Ideal.Quotient.mk (Ideal.span {(p : W)}) (p : W) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.mem_span_singleton.mpr (dvd_refl (p : W)))
  -- `u := ϖ_0 mod p` is `p`-nilpotent.
  have hu : Ideal.Quotient.mk (Ideal.span {(p : W)}) (Q.ϖ 0) ^ p = 0 := by
    rw [← map_pow, hv, map_mul, hmkp, zero_mul]
  have hup : Ideal.Quotient.mk (Ideal.span {(p : W)}) (Q.ϖ 0) ^ ((p - 1) * p) = 0 := by
    rw [Nat.mul_comm, pow_mul, hu, zero_pow hp1ne]
  -- `ϖ_0 * Z = p * c`
  have hmem : Q.ϖ 0 * Z ∈ Ideal.span {(p : W)} := by
    have h0 : Ideal.Quotient.mk (Ideal.span {(p : W)}) (Q.ϖ 0 * Z) = 0 := by
      rw [map_mul]; exact hz0
    exact Ideal.Quotient.eq_zero_iff_mem.mp h0
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hmem
  -- Multiply `hc` by `ϖ_0 ^ (p-1)` and cancel `p`.
  have hmain : (↑v : W) * Z = c * Q.ϖ 0 ^ (p - 1) := by
    apply Q.torsionFree
    simp only [smul_eq_mul]
    calc (p : W) * ((↑v : W) * Z)
        = ((p : W) * ↑v) * Z := by rw [mul_assoc]
      _ = Q.ϖ 0 ^ p * Z := by rw [← hv]
      _ = (Q.ϖ 0 ^ (p - 1) * Q.ϖ 0) * Z := by
            rw [congrArg (fun k => Q.ϖ 0 ^ k) hp1.symm, pow_succ]
      _ = Q.ϖ 0 ^ (p - 1) * (Q.ϖ 0 * Z) := by rw [mul_assoc]
      _ = Q.ϖ 0 ^ (p - 1) * ((p : W) * c) := by rw [hc]
      _ = (p : W) * (c * Q.ϖ 0 ^ (p - 1)) := by ring
  have hZ : Z = (↑(v⁻¹) : W) * (c * Q.ϖ 0 ^ (p - 1)) := by
    rw [← hmain]
    exact (Units.inv_mul_cancel_left v Z).symm
  have hzeq : Ideal.Quotient.mk (Ideal.span {(p : W)}) Z =
      Ideal.Quotient.mk (Ideal.span {(p : W)}) (↑(v⁻¹) : W) *
        (Ideal.Quotient.mk (Ideal.span {(p : W)}) c *
          Ideal.Quotient.mk (Ideal.span {(p : W)}) (Q.ϖ 0) ^ (p - 1)) := by
    rw [hZ, map_mul, map_mul, map_pow]
  rw [hzeq, mul_pow, mul_pow, ← pow_mul, hup, mul_zero, mul_zero]

/-- **`ϖ♭` is a non-zero-divisor on the tilt** (`Regularity`): if `x` is annihilated by
`Work.DSM5c.tiltVarpi Q` in `PreTilt W p = Perfection (W ⧸ (p)) p`, then `x = 0`. -/
theorem tiltVarpi_isSMulRegular {p : ℕ} [Fact p.Prime] {W : Type*} [CommRing W]
    (Q : DSMap.PerfectoidData p W) [Fact ¬IsUnit (p : W)] (x : PreTilt W p)
    (hx : Work.DSM5c.tiltVarpi Q * x = 0) : x = 0 := by
  have hcoeff : ∀ n : ℕ,
      Ideal.Quotient.mk (Ideal.span {(p : W)}) (Q.ϖ n) * PreTilt.coeff n x = 0 := by
    intro n
    have h := congrArg (PreTilt.coeff n) hx
    simpa only [map_mul, Work.DSM5c.coeff_tiltVarpi, map_zero] using h
  refine Work.DSM5c.tilt_ext fun n => ?_
  rw [map_zero, ← PreTilt.coeff_pow_p x n]
  exact pow_p_eq_zero_of_quot_varpi_mul_eq_zero Q (n + 1) _ (hcoeff (n + 1))

end Work.DSM5c.Regularity
