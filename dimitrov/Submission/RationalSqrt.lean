import Mathlib
import Submission.Powers

/-!
# Rational formal power series with a polynomial square is a polynomial

Given an integer sequence `a : ℕ → ℤ` whose convolution square is the
coefficient sequence of a polynomial `G : ℤ[X]`:

    (∑ i ∈ range (k+1), a i * a (k - i)) = G.coeff k        for all k,

and which is *rational* in the formal-power-series sense:

    ∃ p q : ℤ[X], q ≠ 0 ∧
      (∑ i ∈ range (k+1), q.coeff i * a (k - i)) = p.coeff k   for all k

(i.e. `q · (∑ a_k X^k) = p` coefficientwise), we prove that `G` is a perfect
square in `ℤ[X]`:

    ∃ g : ℤ[X], G = g ^ 2

This is the last purely algebraic ingredient of the analytic engine of the
proof of Dimitrov's theorem: Pólya–Bertrandias rationality will give the
`SeriesRational a` hypothesis for the sequence `a` produced by
`Submission.PowRev.powRev_sqrt_integral` (whose convolution square is
`G := R₂ * R₄`), and this lemma turns it into the perfect-square conclusion
needed by `Submission.SquareReflect` / `Submission.SquarePoly` /
`Submission.RootOfUnity`.

## Proof plan

Let `F := ∑_k a_k X^k` be the associated formal power series (over `ℤ`,
conceptually; all arguments are coefficientwise).

1. **`F * F = G` as series.**  The hypothesis `hconv` says exactly that
   `(F * F).coeff k = G.coeff k` for every `k`; both hypotheses are converted
   into identities of power series by reindexing the antidiagonal sums of
   `PowerSeries.coeff_mul` into the range sums (`Finset.Nat.sum_antidiagonal_eq_sum_range_succ`).

2. **Rationality gives a recurrence-free identity.**  From `hrat` we get
   `(q · F) = p` as series.  Squaring and using `F * F = G`: the commutativity
   of `ℤ[[X]]` gives `q² · F² = q² · G = p²` coefficientwise.  Both `q² * G`
   and `p²` are polynomials, and polynomials embed injectively into power
   series (`coe_inj`), so we conclude the polynomial identity
   `(q ^ 2) * G = p ^ 2` in `ℤ[X]` — call this `hmain`.

3. **Euclid in the UFD `ℤ[X]`.**  From `hmain`, `q ^ 2 ∣ p ^ 2`; in a UFD
   domain `a ^ 2 ∣ b ^ 2` implies `a ∣ b` (`dvd_of_sq_dvd_sq`, proved by
   prime-factor induction via `UniqueFactorizationMonoid.induction_on_prime`).
   Write `p = q * s` with `s : ℤ[X]`.

4. **Conclude.**  Substitute `p = q * s` into `(q^2) * G = p^2`, cancel the
   nonzero `q ^ 2` (`mul_left_cancel₀`, `ℤ[X]` is a domain), and get
   `G = s ^ 2`.
-/

noncomputable section

open Polynomial
open scoped Polynomial

namespace Submission.RationalSqrt

/-- A sequence `a` is (formally) rational: some nonzero `q : ℤ[X]` makes
`q · (∑ a_k X^k)` a polynomial `p` (coefficientwise identity for all `k`). -/
def SeriesRational (a : ℕ → ℤ) : Prop :=
  ∃ (p q : ℤ[X]), q ≠ 0 ∧
    ∀ k : ℕ, (∑ i ∈ Finset.range (k + 1), q.coeff i * a (k - i)) = p.coeff k

/-- In a unique-factorization domain, `a ^ 2 ∣ b ^ 2` implies `a ∣ b`.
Proved by induction on the factorization of `a` into primes: a prime `p`
dividing `a` divides `b` (Euclid), the leftover `p`-factor is cancelled from
the squared divisibility, and the induction hypothesis is applied to the rest. -/
lemma dvd_of_sq_dvd_sq {α : Type*} [CommRing α] [IsDomain α] [UniqueFactorizationMonoid α]
    {a b : α} (h : a ^ 2 ∣ b ^ 2) : a ∣ b := by
  classical
  let Q : α → Prop := fun x => ∀ z : α, x ^ 2 ∣ z ^ 2 → x ∣ z
  have hmain : Q a := by
    refine UniqueFactorizationMonoid.induction_on_prime a ?h0 ?hu ?hstep
    · -- zero: `0 ^ 2 = 0` divides `z ^ 2`, so `z ^ 2 = 0`, hence `z = 0`, and `0 ∣ 0`.
      intro z hz
      rcases hz with ⟨c, hc⟩
      have hz2 : z ^ 2 = 0 := by simpa using hc
      have hz0 : z = 0 := by
        have hor := eq_zero_or_eq_zero_of_mul_eq_zero (a := z) (b := z) (by simpa [pow_two] using hz2)
        rcases hor with hz0 | hz0
        · exact hz0
        · exact hz0
      refine ⟨0, ?_⟩
      simp [hz0]
    · -- units divide everything.
      intro x hx z hz
      exact dvd_trans (isUnit_iff_dvd_one.mp hx) (one_dvd z)
    · -- `p * y` step: `p` is prime; from `(p*y)^2 ∣ z^2` get `p ∣ z`, write
      -- `z = p*z₁`, cancel `p^2`, apply the induction hypothesis to `y ∣ z₁`.
      intro y p hy0 hp ih z hz
      have hpne0 : p ≠ 0 := hp.ne_zero
      have hp_z : p ∣ z := by
        apply hp.dvd_of_dvd_pow
        rcases hz with ⟨c, hc⟩
        refine ⟨p * y ^ 2 * c, ?_⟩
        rw [hc]
        ring
      rcases hp_z with ⟨z₁, hz₁ : z = p * z₁⟩
      have hy_z1 : y ^ 2 ∣ z₁ ^ 2 := by
        rcases hz with ⟨c, hc⟩
        refine ⟨c, ?_⟩
        apply mul_left_cancel₀ (pow_ne_zero 2 hpne0)
        calc
          p ^ 2 * z₁ ^ 2 = (p * z₁) ^ 2 := by ring
          _ = z ^ 2 := by rw [hz₁]
          _ = (p * y) ^ 2 * c := by rw [hc]
          _ = p ^ 2 * (y ^ 2 * c) := by ring
      have hy_z1' : y ∣ z₁ := ih z₁ hy_z1
      rcases hy_z1' with ⟨d, hd : z₁ = y * d⟩
      refine ⟨d, ?_⟩
      calc
        z = p * z₁ := hz₁
        _ = p * (y * d) := by rw [hd]
        _ = (p * y) * d := by ring
  exact hmain b h

/-- If the convolution square of the rational integer sequence `a` is the
coefficient sequence of `G`, then `G` is a perfect square in `ℤ[X]`. -/
theorem square_of_rational_conv_square (a : ℕ → ℤ) (G : ℤ[X])
    (hconv : ∀ k : ℕ, (∑ i ∈ Finset.range (k + 1), a i * a (k - i)) = G.coeff k)
    (hrat : SeriesRational a) : ∃ g : ℤ[X], G = g ^ 2 := by
  classical
  rcases hrat with ⟨p, q, hq0, hratcoeff⟩
  -- `F` is the formal power series `∑ a_k X^k`.
  let F : PowerSeries ℤ := PowerSeries.mk (fun k => a k)
  -- Step 1: `F * F = G` as power series (coefficientwise `hconv`).
  have hFF : F * F = (G : PowerSeries ℤ) := by
    apply PowerSeries.ext
    intro k
    simp [F, PowerSeries.coeff_mul]
    exact (Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => a i * a j) k).trans (hconv k)
  -- Step 1': `q · F = p` as power series (coefficientwise `hrat`).
  have hqF : (q : PowerSeries ℤ) * F = (p : PowerSeries ℤ) := by
    apply PowerSeries.ext
    intro k
    simp [F, PowerSeries.coeff_mul]
    exact (Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => q.coeff i * a j) k).trans
      (hratcoeff k)
  -- Step 2: `q² · G = p²` as power series.
  have hsq : ((q : PowerSeries ℤ) ^ 2) * (G : PowerSeries ℤ) = ((p : PowerSeries ℤ) ^ 2) := by
    calc
      ((q : PowerSeries ℤ) ^ 2) * (G : PowerSeries ℤ)
          = ((q : PowerSeries ℤ) ^ 2) * (F * F) := by rw [hFF]
      _ = ((q : PowerSeries ℤ) * F) * ((q : PowerSeries ℤ) * F) := by ring
      _ = (p : PowerSeries ℤ) * (p : PowerSeries ℤ) := by rw [hqF]
      _ = ((p : PowerSeries ℤ) ^ 2) := by ring
  -- ... as polynomials (polynomials embed injectively into power series).
  have hmain : q ^ 2 * G = p ^ 2 := by
    apply coe_inj.mp
    simpa [pow_two, coe_pow, coe_mul] using hsq
  -- Step 3: `q ^ 2 ∣ p ^ 2`, hence `q ∣ p` in the UFD `ℤ[X]`.
  have hq2dvd : q ^ 2 ∣ p ^ 2 := by
    refine ⟨G, ?_⟩
    exact hmain.symm
  have hqp : q ∣ p := dvd_of_sq_dvd_sq hq2dvd
  rcases hqp with ⟨s, hp : p = q * s⟩
  -- Step 4: substitute and cancel the nonzero `q ^ 2`.
  refine ⟨s, ?_⟩
  apply mul_left_cancel₀ (pow_ne_zero 2 hq0)
  calc
    q ^ 2 * G = p ^ 2 := hmain
    _ = (q * s) ^ 2 := by rw [hp]
    _ = q ^ 2 * s ^ 2 := by ring

end Submission.RationalSqrt

end
