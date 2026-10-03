import Mathlib
import Submission.Work.FIPlan.Interface

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The automatic coprimality `(|z₁|², |Δ(z₁,z₂)|) = 1`

`Submission/Work/FIArea2/Cnt_eq_Nsol.lean` needs the hypothesis `Nat.Coprime (gnorm z₁) (absDelta z₁ z₂)`
in order to invert `|z₁|²` modulo `|Δ|` (`ZMod.isUnit_iff_coprime`).  This file proves that this
hypothesis is **automatic**: it holds for every coprime pair `(z₁,z₂)` with `z₁` primitive.

## The argument

Everything happens in `ℤ[i] = Zsqrtd (-1)`.  The key identity is

  `2i · Δ = z̄₁z₂ − z₁z̄₂`,   where `Δ = Im(z̄₁z₂)`,   `i = ⟨0,1⟩`   (`Delta_mul_two_I`).

Now let `q ∈ ℤ[i]` be a prime element dividing both `z₁z̄₁ = |z₁|²` and `Δ`.

* `q ∣ z₁z̄₁` and `q` prime give `q ∣ z₁` or `q ∣ z̄₁`.
* If `q ∣ z₁`: then `q ∣ z₁z̄₂`, while `q ∣ 2iΔ = z̄₁z₂ − z₁z̄₂` gives `q ∣ z̄₁z₂`; primality yields
  `q ∣ z̄₁` (contradicting `(z₁,z̄₁) = 1`) or `q ∣ z₂` (contradicting `(z₁,z₂) = 1`).
* If `q ∣ z̄₁`: symmetrically `q ∣ z̄₁z₂` and `q ∣ z₁z̄₂`, so `q ∣ z₁` (contradiction with
  `(z₁,z̄₁) = 1`) or `q ∣ z̄₂` (contradiction with `(z̄₁,z̄₂) = 1`, the conjugate of `(z₁,z₂) = 1`).

Hence no prime element of `ℤ[i]` divides both, and since `ℤ[i]` is a PID this is `IsCoprime` in
`ℤ[i]` (`isCoprime_of_prime_dvd`).  Both elements being rational integers, taking real parts of a
Bézout relation gives coprimality in `ℤ`, and `Int.isCoprime_iff_nat_coprime` finishes.

Note that no prime splitting / quadratic reciprocity is involved: the argument is uniform in the
prime, so it needs no case distinction between `2`, `p ≡ 3 (mod 4)` and `p ≡ 1 (mod 4)`. -/

namespace Work.FIArea2

open Work.FIPlan

/-- **The determinant identity `2i·Δ(z₁,z₂) = z̄₁z₂ − z₁z̄₂`** in `ℤ[i]`, where
`Δ(z₁,z₂) = Im(z̄₁z₂)`.  This is the identity that converts the divisibility `q ∣ Δ` of a rational
integer into a divisibility of a product of Gaussian integers. -/
theorem Delta_mul_two_I (z1 z2 : GaussianInt) :
    (Delta z1 z2 : GaussianInt) * (2 * (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt))
      = star z1 * z2 - z1 * star z2 := by
  ext <;> simp [Delta]
  all_goals ring

/-- **Coprimality in `ℤ` (and in `ℤ[i]`) of `|z₁|²` and `Δ(z₁,z₂)`** for a coprime pair whose
first member is primitive: `IsCoprime (gnorm z₁) (Δ(z₁,z₂))` inside `ℤ`.  This is the strengthening
of `coprime_gnorm_absDelta` before passing to `natAbs`. -/
theorem isCoprime_gnorm_Delta {z1 z2 : GaussianInt} (h12 : GaussCoprime z1 z2)
    (h1 : IsCoprime z1 (star z1)) : IsCoprime (gnorm z1 : ℤ) (Delta z1 z2) := by
  -- `z₁ ≠ 0`, since `(z₁,z̄₁) = 1` rules out `z₁ = 0 = z̄₁`.
  have hz1 : z1 ≠ 0 := by
    rcases h1.ne_zero_or_ne_zero with h | h
    · exact h
    · exact fun h0 => h (by rw [h0]; simp)
  -- `(z₁,z₂) = 1` transports to `(z̄₁,z̄₂) = 1`.
  have h12s : IsCoprime (star z1) (star z2) := h12.map (starRingEnd GaussianInt)
  -- Coprimality of `z₁z̄₁` and `Δ` in `ℤ[i]`.
  have hcop : IsCoprime (z1 * star z1) ((Delta z1 z2 : ℤ) : GaussianInt) := by
    refine isCoprime_of_prime_dvd ?_ ?_
    · rintro ⟨hx, -⟩
      rcases mul_eq_zero.mp hx with h | h
      · exact hz1 h
      · exact hz1 (by simpa using congrArg star h)
    · intro q hq hqN hqD
      -- `2iΔ = z̄₁z₂ − z₁z̄₂`, so `q` divides that difference as well.
      have hA : q ∣ star z1 * z2 - z1 * star z2 := by
        rw [← Delta_mul_two_I z1 z2]
        exact dvd_mul_of_dvd_left hqD _
      rcases hq.dvd_or_dvd hqN with hq1 | hqs1
      · -- Case `q ∣ z₁`: `q ∣ z₁z̄₂` and `q ∣ z̄₁z₂`.
        have hC : q ∣ star z1 * z2 := by
          have h := dvd_add hA (dvd_mul_of_dvd_left hq1 (star z2))
          simpa using h
        rcases hq.dvd_or_dvd hC with h | h
        · exact hq.not_isUnit (h1.isUnit_of_dvd' hq1 h)
        · exact hq.not_isUnit (h12.isUnit_of_dvd' hq1 h)
      · -- Case `q ∣ z̄₁`: `q ∣ z̄₁z₂` and `q ∣ z₁z̄₂`.
        have hC : q ∣ z1 * star z2 := by
          have h := dvd_sub hA (dvd_mul_of_dvd_left hqs1 z2)
          simpa using h
        rcases hq.dvd_or_dvd hC with h | h
        · exact hq.not_isUnit (h1.isUnit_of_dvd' h hqs1)
        · exact hq.not_isUnit (h12s.isUnit_of_dvd' hqs1 h)
  -- `z₁z̄₁ = |z₁|²` as a Gaussian integer.
  have hcop' : IsCoprime ((Zsqrtd.norm z1 : ℤ) : GaussianInt)
      ((Delta z1 z2 : ℤ) : GaussianInt) := by
    rw [Zsqrtd.norm_eq_mul_conj]
    exact hcop
  -- Read off the real parts of a Bézout relation: the imaginary part of `2i` is irrelevant.
  obtain ⟨x, y, hxy⟩ := hcop'
  have hreal : x.re * Zsqrtd.norm z1 + y.re * (Delta z1 z2) = 1 := by
    have h := congrArg Zsqrtd.re hxy
    simp only [Zsqrtd.re_add, Zsqrtd.re_mul, Zsqrtd.re_intCast, Zsqrtd.im_intCast] at h
    ring_nf at h ⊢
    exact h
  exact ⟨x.re, y.re, by simpa [gnorm] using hreal⟩

/-- **The automatic coprimality of `|z₁|²` and `|Δ|`**: if `z₁, z₂` are coprime and `z₁` is
primitive (`(z₁,z̄₁) = 1`), then no rational prime divides both `|z₁|²` and `|Im(z̄₁z₂)|`.  This is
the hypothesis `(|z₁|²,|Δ|) = 1` that `Cnt_eq_Nsol` needs in order to invert `|z₁|²` modulo `|Δ|`;
it holds for every pair that occurs (brute-forced on all `5284` primary/coprime/primitive pairs with
`z₁ ≡ z₂ (mod 8)` and `|Δ| ≤ 200`, and on all pairs with coordinates in `[−12,12]`).

Sketch: let `p | |z₁|²`.  For `p = 2` or `p ≡ 3 (mod 4)`, `p` is a Gaussian prime dividing `z₁` and
`z̄₁`, contradicting `(z₁,z̄₁) = 1`.  For `p ≡ 1 (mod 4)` write `p = ππ̄`; `p | z₁z̄₁` gives
`π | z₁` or `π̄ | z₁` (not both), and if `p | Δ` then `π | Δ`, i.e. `π | z̄₁z₂`, forcing `π | z̄₁`
(impossible) or `π | z₂` (contradicting `(z₁,z₂) = 1`). -/
theorem coprime_gnorm_absDelta {z1 z2 : GaussianInt}
    (h12 : Work.FIPlan.GaussCoprime z1 z2) (h1 : IsCoprime z1 (star z1)) :
    Nat.Coprime (Work.FIPlan.gnorm z1) (Work.FIPlan.absDelta z1 z2) := by
  rw [absDelta]
  exact Int.isCoprime_iff_nat_coprime.mp
    (by simpa [gnorm] using isCoprime_gnorm_Delta h12 h1)

end Work.FIArea2
