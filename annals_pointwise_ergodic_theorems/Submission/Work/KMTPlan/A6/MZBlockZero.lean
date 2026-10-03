import Mathlib
import Submission.Work.A7.ModelApproxCore_M0_defs

/-!
# The arithmetic symbol `m_Ẑ` vanishes at a non-trivial `q`-torsion phase

`Work.KMTAreas.A7.mZ P Q α₁ α₂ = Q⁻¹ ∑_{n < Q} e(n α₁) e(P(n) α₂)` is the average of the
arithmetic exponential sum over `ℤ/Qℤ`.  If

* `q ∣ Q`,
* `Q • α₁ = 0` while `q • α₁ ≠ 0`,
* `q • α₂ = 0`,

then the sum over the `Q/q` blocks of length `q` is a geometric series in the non-trivial
character value `ω = e(q α₁)`, whose `Q/q`-th power is `e(Q α₁) = 1`; hence it vanishes.

The two ingredients are the multiplicativity of `fourier` in its index (`fourier_add`,
`fourier_mul_natCast`), the triviality criterion `fourier n α = 1 ↔ n • α = 0`
(injectivity of `AddCircle.toCircle`), and the integrality fact
`q ∣ P(x+q) - P(x)` (`Polynomial.sub_dvd_eval_sub`).
-/

namespace Work.KMTPlan.A6

open scoped BigOperators

/-- On the circle `ℝ/ℤ`, `fourier n α = 1` exactly when `n • α = 0`. -/
private lemma mzFourierEqOneIff (n : ℤ) (α : Work.Analysis.IonescuWainger.Circle) :
    fourier (T := 1) n α = 1 ↔ n • α = 0 := by
  rw [fourier_apply]
  constructor
  · intro h
    have h2 : AddCircle.toCircle (n • α) = (1 : Circle) := Subtype.coe_injective (by simpa using h)
    exact AddCircle.injective_toCircle one_ne_zero (by simpa [AddCircle.toCircle_zero] using h2)
  · intro h
    rw [h, AddCircle.toCircle_zero]
    rfl

/-- `fourier` is multiplicative in its integral index; in particular a shift of the index by `q`
multiplies the value by `fourier q α`. -/
private lemma mzFourierAddCast (n q : ℕ) (α : Work.Analysis.IonescuWainger.Circle) :
    fourier (T := 1) (((n + q : ℕ) : ℤ)) α
      = fourier (T := 1) (n : ℤ) α * fourier (T := 1) (q : ℤ) α := by
  rw [show (((n + q : ℕ) : ℤ)) = (n : ℤ) + (q : ℤ) by push_cast; ring]
  exact fourier_add

/-- `q ∣ P(x+q) - P(x)` for an integer polynomial `P`, so for a `q`-torsion frequency `α` the
value `fourier (P(x)) α` is `q`-periodic in `x`. -/
private lemma mzFourierEvalShift (P : Polynomial ℤ) (q : ℕ)
    (α : Work.Analysis.IonescuWainger.Circle) (hα : q • α = 0) (n : ℕ) :
    fourier (T := 1) (P.eval (((n + q : ℕ) : ℤ))) α = fourier (T := 1) (P.eval (n : ℤ)) α := by
  rw [fourier_apply, fourier_apply]
  congr 1
  have hcast : ((n + q : ℕ) : ℤ) = (n : ℤ) + (q : ℤ) := by push_cast; ring
  rw [hcast]
  obtain ⟨c, hc⟩ := Polynomial.sub_dvd_eval_sub ((n : ℤ) + (q : ℤ)) (n : ℤ) P
  have hc' : P.eval ((n : ℤ) + (q : ℤ)) - P.eval (n : ℤ) = (q : ℤ) * c := by
    simpa using hc
  have hval : P.eval ((n : ℤ) + (q : ℤ)) = P.eval (n : ℤ) + (q : ℤ) * c := by linarith
  have hq' : (q : ℤ) • α = 0 := by rw [natCast_zsmul]; exact hα
  have hc0 : ((q : ℤ) * c) • α = 0 := by
    rw [mul_comm, mul_zsmul, hq', smul_zero]
  rw [hval, add_zsmul, hc0, add_zero]

/-- `fourier (m * n) α = (fourier m α) ^ n` for a natural multiplier `n`. -/
private lemma mzFourierMulNatCast (m : ℤ) (n : ℕ) (α : Work.Analysis.IonescuWainger.Circle) :
    fourier (T := 1) (m * (n : ℤ)) α = fourier (T := 1) m α ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.cast_succ, mul_add, mul_one, fourier_add, ih, pow_succ]

/-- Splitting the range `{0, …, M*q-1}` into `M` blocks of length `q`. -/
private lemma mzSumRangeMulRange (f : ℕ → ℂ) (M q : ℕ) :
    ∑ n ∈ Finset.range (M * q), f n
      = ∑ i ∈ Finset.range M, ∑ j ∈ Finset.range q, f (i * q + j) := by
  induction M with
  | zero => simp
  | succ M ih => rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]

/-- A finite geometric sum with a non-trivial `M`-th root of unity vanishes. -/
private lemma mzGeomSumRangeZero {ω : ℂ} {M : ℕ} (hωM : ω ^ M = 1) (hω : ω ≠ 1) :
    ∑ i ∈ Finset.range M, ω ^ i = 0 := by
  have h := geom_sum_mul ω M
  rw [hωM, sub_self] at h
  rcases mul_eq_zero.mp h with h' | h'
  · exact h'
  · exact absurd h' (sub_ne_zero.mpr hω)

theorem MZBlockZero (P : Polynomial ℤ) (Q q : ℕ) (hq : 0 < q) (hdvd : q ∣ Q)
    (α₁ α₂ : Work.Analysis.IonescuWainger.Circle) (hα₁ : q • α₁ ≠ 0) (hα₂ : q • α₂ = 0)
    (hQ : Q • α₁ = 0) :
    Work.KMTAreas.A7.mZ P Q α₁ α₂ = 0 := by
  have _hq := hq
  set f : ℕ → ℂ := fun n => fourier (T := 1) (n : ℤ) α₁ * fourier (T := 1) (P.eval (n : ℤ)) α₂
    with hf
  set ω : ℂ := fourier (T := 1) (q : ℤ) α₁ with hω
  have hf' : ∀ n : ℕ,
      f n = fourier (T := 1) (n : ℤ) α₁ * fourier (T := 1) (P.eval (n : ℤ)) α₂ := by
    intro n; rw [hf]
  -- the summand is multiplied by `ω` when its index is shifted by `q`
  have hshift : ∀ n : ℕ, f (n + q) = ω * f n := by
    intro n
    rw [hf', hf', hω, mzFourierAddCast n q α₁, mzFourierEvalShift P q α₂ hα₂ n]
    ring
  -- iterating the shift
  have hpow : ∀ i j : ℕ, f (i * q + j) = ω ^ i * f j := by
    intro i
    induction i with
    | zero => intro j; simp
    | succ i ih =>
        intro j
        have h1 : (i + 1) * q + j = (i * q + j) + q := by ring
        rw [h1, hshift, ih, pow_succ]
        ring
  -- `ω` is a `Q/q`-th root of unity …
  have hωM : ω ^ (Q / q) = 1 := by
    rw [hω, ← mzFourierMulNatCast (q : ℤ) (Q / q) α₁]
    rw [show (q : ℤ) * (((Q / q : ℕ)) : ℤ) = (Q : ℤ) by
      push_cast; rw [mul_comm]; exact_mod_cast Nat.div_mul_cancel hdvd]
    exact (mzFourierEqOneIff (Q : ℤ) α₁).mpr (by rw [natCast_zsmul]; exact hQ)
  -- … and it is not `1`
  have hωneq : ω ≠ 1 := by
    intro h
    rw [hω] at h
    have h2 := (mzFourierEqOneIff (q : ℤ) α₁).mp h
    rw [natCast_zsmul] at h2
    exact hα₁ h2
  have hgeo : ∑ i ∈ Finset.range (Q / q), ω ^ i = 0 := mzGeomSumRangeZero hωM hωneq
  -- the block decomposition turns the sum into a geometric series
  have hsum : ∑ n ∈ Finset.range Q, f n = 0 := by
    have hQeq : Q = Q / q * q := by rw [Nat.div_mul_cancel hdvd]
    rw [hQeq, mzSumRangeMulRange f (Q / q) q]
    have hstep : ∀ i ∈ Finset.range (Q / q),
        (∑ j ∈ Finset.range q, f (i * q + j)) = ω ^ i * (∑ j ∈ Finset.range q, f j) := by
      intro i _
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j _ => hpow i j)
    rw [Finset.sum_congr rfl hstep, ← Finset.sum_mul, hgeo, zero_mul]
  rw [Work.KMTAreas.A7.mZ]
  rw [show (∑ n ∈ Finset.range Q,
      fourier (T := 1) (n : ℤ) α₁ * fourier (T := 1) (P.eval (n : ℤ)) α₂)
      = ∑ n ∈ Finset.range Q, f n from by rw [hf]]
  rw [hsum, mul_zero]

end Work.KMTPlan.A6
