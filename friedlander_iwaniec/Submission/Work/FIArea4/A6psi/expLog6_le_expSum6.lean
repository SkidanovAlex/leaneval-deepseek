/-
# Area 4 (round 6): the log-sine Fourier step `S15expLog6 ≤ (log N+1)² · M`

The round-6 analogue of `Work.FIArea4.S15expLog_le_expSum`: the exponential sum `S15expLog6`,
which carries the logarithmic weight `logFac6`, is dominated by `(log N + 1)²` times a uniform
bound `M` for the *separated* sums `S15expSum6 ℓ`.

The proof is the paper's FI (15.5)–(15.7) step, verbatim as in the frozen chain:

* on the support of `β` every pair lies in the polar box with `|Δ| ≥ 2`, so the two arguments
  satisfy `1/N ≤ |α₂ - α₁| ≤ 1` (`Work.FIArea4.S15red.logFac_arg_bounds`);
* there, `logFac6 z₁ z₂ = log 4 + logFac z₁ z₂`
  (`Work.FIArea7.fi_logFac6_eq_logFac_add_log4`) and `logFac z₁ z₂ = -log(|sin(α₂-α₁)|/2)`
  (`Work.FIArea4.logFac_sin`);
* the mollified log-sine Fourier expansion `Work.FIArea4.S15red.logFac_expansion` expands
  `-log(|sin θ|/2)` on that range with `Σ_ℓ ‖c ℓ‖ ≤ C(log N + 1)²`;
* summing the expansion against `S15theta ℓ = e^{iℓ(α₂-α₁)}` and exchanging the finite and
  infinite sums gives `S15expLog6 = log 4 · S15expSum6 0 + Σ_ℓ c ℓ · S15expSum6 ℓ`.
-/
import Mathlib
import Submission.Work.FIArea4.A6psi.Defs
import Submission.Work.FIArea4.S15red.logFac_expansion
import Submission.Work.FIArea4.S15red.logFac_arg_bounds
import Submission.Work.FIArea4.A6supp6
import Submission.Work.FIArea4.logFac_sin
import Submission.Work.FIArea7.logFac6_eq_sum_freq

namespace Work.FIArea4.A6psi

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 1. The two summands, as curried functions -/

/-- The summand of `S15expLog6` (the `logFac6`-weighted exponential sum), as a curried function. -/
def S15expTerm6 (X j : ℕ) (β : GaussianInt → ℂ) (u t : ℝ)
    (z1 z2 : GaussianInt) (d : ℕ) : ℂ :=
  S15coef6 β ((z1, z2), d) * ((Work.FITop4.logFac6 z1 z2 : ℝ) : ℂ) *
    S15phase X j u t ((z1, z2), d)

/-- The summand of `S15expSum6` (the separated sum with the angular character), as a curried
function. -/
def S15sepTerm6 (X j : ℕ) (β : GaussianInt → ℂ) (ℓ : ℤ) (u t : ℝ)
    (z1 z2 : GaussianInt) (d : ℕ) : ℂ :=
  S15coef6 β ((z1, z2), d) * S15theta ℓ z1 z2 * S15phase X j u t ((z1, z2), d)

lemma S15expTerm6_eq_zero_of {X j : ℕ} {β : GaussianInt → ℂ} {u t : ℝ}
    {z1 z2 : GaussianInt} {d : ℕ} (h : β z1 = 0 ∨ β z2 = 0) :
    S15expTerm6 X j β u t z1 z2 d = 0 := by
  rcases h with h | h
  · rw [S15expTerm6, S15coef6, h]; ring
  · rw [S15expTerm6, S15coef6, h, star_zero]; ring

lemma S15sepTerm6_eq_zero_of {X j : ℕ} {β : GaussianInt → ℂ} {ℓ : ℤ} {u t : ℝ}
    {z1 z2 : GaussianInt} {d : ℕ} (h : β z1 = 0 ∨ β z2 = 0) :
    S15sepTerm6 X j β ℓ u t z1 z2 d = 0 := by
  rcases h with h | h
  · rw [S15sepTerm6, S15coef6, h]; ring
  · rw [S15sepTerm6, S15coef6, h, star_zero]; ring

/-- `S15expLog6` as a sum over the support `A6supp` of `β`. -/
lemma S15expLog6_eq_sum_supp (Pa : Work.FITop.Params) (X j : ℕ) (β : GaussianInt → ℂ)
    (u t : ℝ) :
    S15expLog6 Pa X j β u t
      = ∑ i ∈ Work.FIArea4.A6supp Pa X j β, S15expTerm6 X j β u t i.1.1 i.1.2 i.2 := by
  rw [show S15expLog6 Pa X j β u t
      = ∑ i ∈ Work.FIArea4.S15ixSet Pa X j, S15expTerm6 X j β u t i.1.1 i.1.2 i.2 from rfl]
  exact Work.FIArea4.A6sum_S15ixSet_eq_sum_supp Pa X j β (S15expTerm6 X j β u t)
    (fun z1 z2 d h => S15expTerm6_eq_zero_of h)

/-- `S15expSum6` as a sum over the support `A6supp` of `β`. -/
lemma S15expSum6_eq_sum_supp_finset (Pa : Work.FITop.Params) (X j : ℕ) (β : GaussianInt → ℂ)
    (ℓ : ℤ) (u t : ℝ) :
    S15expSum6 Pa X j β ℓ u t
      = ∑ i ∈ Work.FIArea4.A6supp Pa X j β, S15sepTerm6 X j β ℓ u t i.1.1 i.1.2 i.2 := by
  rw [show S15expSum6 Pa X j β ℓ u t
      = ∑ i ∈ Work.FIArea4.S15ixSet Pa X j, S15sepTerm6 X j β ℓ u t i.1.1 i.1.2 i.2 from rfl]
  exact Work.FIArea4.A6sum_S15ixSet_eq_sum_supp Pa X j β (S15sepTerm6 X j β ℓ u t)
    (fun z1 z2 d h => S15sepTerm6_eq_zero_of h)

/-! ## 2. The per-pair log-sine expansion of `logFac6` -/

/-- **The per-pair log-sine expansion.**  For a triple of the support (both points in the polar
box, `|Δ| ≥ 2`, hence `|α₂ - α₁| ∈ [1/N, 1]`), the round-6 logarithmic factor `logFac6` is the
log-sine series of FI (15.5)–(15.7), up to the additive constant `log 4`. -/
lemma S15logFac6_eq_tsum {Pa : Work.FITop.Params} {φ : ℝ} {β : GaussianInt → ℂ}
    (hβ : IsPrimBoxCoeff Pa φ β) {X j : ℕ} (hX : 1 ≤ X) {i : S15Id}
    (hi : i ∈ Work.FIArea4.A6supp Pa X j β) (c : ℤ → ℂ)
    (hcexp : ∀ α : ℝ, 1 / (Pa.N : ℝ) ≤ |α| → |α| ≤ 1 →
        (-(Real.log (|Real.sin α| / 2)) : ℂ)
          = ∑' ℓ : ℤ, c ℓ * Complex.exp (Complex.I * (ℓ : ℂ) * (α : ℂ))) :
    (Work.FITop4.logFac6 i.1.1 i.1.2 : ℂ)
      = (Real.log 4 : ℂ) + ∑' ℓ : ℤ, c ℓ * S15theta ℓ i.1.1 i.1.2 := by
  rw [Work.FIArea4.A6supp, Finset.mem_filter] at hi
  obtain ⟨hix, hb1, hb2⟩ := hi
  rw [Work.FIArea4.S15ixSet, Finset.mem_filter] at hix
  obtain ⟨-, hcop, hXlt, hdvd, hΔpos⟩ := hix
  have hd1 : 1 ≤ i.2 := le_of_lt (lt_of_le_of_lt hX hXlt)
  have hΔ2 : 2 ≤ Work.FIPlan.absDelta i.1.1 i.1.2 := by
    have h4 : 4 * i.2 ≤ Work.FIPlan.absDelta i.1.1 i.1.2 := Nat.le_of_dvd hΔpos hdvd
    omega
  have hP1 : Work.FITop3.InPolarBox Pa φ i.1.1 := hβ.inPolarBox hb1
  have hP2 : Work.FITop3.InPolarBox Pa φ i.1.2 := hβ.inPolarBox hb2
  have hΔne : Work.FIPlan.absDelta i.1.1 i.1.2 ≠ 0 := by omega
  have hΔneZ : Work.FIPlan.Delta i.1.1 i.1.2 ≠ 0 := by
    intro h
    exact hΔne (by rw [Work.FIPlan.absDelta, h]; rfl)
  have harg := Work.FIArea4.S15red.logFac_arg_bounds Pa φ hP1 hP2 hΔ2
  rw [Work.FIArea7.fi_logFac6_eq_logFac_add_log4 i.1.1 i.1.2 hΔneZ]
  rw [Work.FIArea4.logFac_sin i.1.1 i.1.2 hΔne]
  push_cast
  rw [hcexp (Complex.arg i.1.2.toComplex - Complex.arg i.1.1.toComplex) harg.1 harg.2]
  have hts : (∑' ℓ : ℤ, c ℓ * Complex.exp (Complex.I * (ℓ : ℂ)
        * (((Complex.arg i.1.2.toComplex - Complex.arg i.1.1.toComplex : ℝ)) : ℂ)))
      = ∑' ℓ : ℤ, c ℓ * S15theta ℓ i.1.1 i.1.2 :=
    tsum_congr (fun ℓ => by rw [S15theta])
  rw [hts]
  ring

/-! ## 3. The transfer -/

theorem expLog6_le_expSum6 :
    ∃ C : ℝ, 0 < C ∧ ∀ (Pa : Work.FITop.Params) (X j : ℕ) (φ : ℝ) (β : GaussianInt → ℂ)
      (u t M : ℝ),
      Work.FIArea4.IsPrimBoxCoeff Pa φ β → 1 ≤ X →
      (∀ ℓ : ℤ, ‖Work.FIArea4.A6psi.S15expSum6 Pa X j β ℓ u t‖ ≤ M) →
      ‖Work.FIArea4.A6psi.S15expLog6 Pa X j β u t‖ ≤ C * (Real.log Pa.N + 1) ^ 2 * M := by
  obtain ⟨C₀, hC₀pos, hlogfac⟩ := Work.FIArea4.S15red.logFac_expansion
  have hlog4pos : 0 < Real.log 4 := Real.log_pos (by norm_num)
  refine ⟨Real.log 4 + C₀, by linarith, ?_⟩
  intro Pa X j φ β u t M hβ hX hM
  obtain ⟨c, hcsum, hcnorm, hcbd, hcexp⟩ := hlogfac Pa
  have hMnn : 0 ≤ M := le_trans (norm_nonneg _) (hM 0)
  have hper : ∀ i ∈ Work.FIArea4.A6supp Pa X j β,
      S15expTerm6 X j β u t i.1.1 i.1.2 i.2
        = (Real.log 4 : ℂ) * S15sepTerm6 X j β 0 u t i.1.1 i.1.2 i.2
          + ∑' ℓ : ℤ, c ℓ * S15sepTerm6 X j β ℓ u t i.1.1 i.1.2 i.2 := by
    intro i hi
    have key := S15logFac6_eq_tsum hβ hX hi c hcexp
    have hsm := Work.FIArea4.A6summable_S15theta c hcnorm i.1.1 i.1.2
    have htheta0 : S15theta 0 i.1.1 i.1.2 = 1 := by rw [S15theta]; simp
    calc S15expTerm6 X j β u t i.1.1 i.1.2 i.2
        = S15coef6 β i * ((Real.log 4 : ℂ)
              + ∑' ℓ : ℤ, c ℓ * S15theta ℓ i.1.1 i.1.2) * S15phase X j u t i := by
          rw [S15expTerm6, key]
      _ = (Real.log 4 : ℂ) * (S15coef6 β i * S15phase X j u t i)
            + (S15coef6 β i * S15phase X j u t i)
              * (∑' ℓ : ℤ, c ℓ * S15theta ℓ i.1.1 i.1.2) := by ring
      _ = (Real.log 4 : ℂ) * S15sepTerm6 X j β 0 u t i.1.1 i.1.2 i.2
            + ∑' ℓ : ℤ, c ℓ * S15sepTerm6 X j β ℓ u t i.1.1 i.1.2 i.2 := by
          rw [show S15sepTerm6 X j β 0 u t i.1.1 i.1.2 i.2
              = S15coef6 β i * S15phase X j u t i by rw [S15sepTerm6, htheta0]; ring]
          congr 1
          rw [← Summable.tsum_mul_left (S15coef6 β i * S15phase X j u t i) hsm]
          exact tsum_congr (fun ℓ => by rw [S15sepTerm6]; ring)
  have hsumm : ∀ i ∈ Work.FIArea4.A6supp Pa X j β,
      Summable (fun ℓ : ℤ => c ℓ * S15sepTerm6 X j β ℓ u t i.1.1 i.1.2 i.2) := by
    intro i hi
    have h1 : Summable (fun ℓ : ℤ =>
        (S15coef6 β i * S15phase X j u t i) * (c ℓ * S15theta ℓ i.1.1 i.1.2)) :=
      (Work.FIArea4.A6summable_S15theta c hcnorm i.1.1 i.1.2).mul_left _
    simpa only [S15sepTerm6, mul_assoc, mul_comm, mul_left_comm] using h1
  have hmain : S15expLog6 Pa X j β u t
      = (Real.log 4 : ℂ) * S15expSum6 Pa X j β 0 u t
        + ∑' ℓ : ℤ, c ℓ * S15expSum6 Pa X j β ℓ u t := by
    calc S15expLog6 Pa X j β u t
        = ∑ i ∈ Work.FIArea4.A6supp Pa X j β, S15expTerm6 X j β u t i.1.1 i.1.2 i.2 :=
          S15expLog6_eq_sum_supp Pa X j β u t
      _ = ∑ i ∈ Work.FIArea4.A6supp Pa X j β,
            ((Real.log 4 : ℂ) * S15sepTerm6 X j β 0 u t i.1.1 i.1.2 i.2
              + ∑' ℓ : ℤ, c ℓ * S15sepTerm6 X j β ℓ u t i.1.1 i.1.2 i.2) :=
          Finset.sum_congr rfl hper
      _ = (Real.log 4 : ℂ)
            * (∑ i ∈ Work.FIArea4.A6supp Pa X j β,
                S15sepTerm6 X j β 0 u t i.1.1 i.1.2 i.2)
          + ∑ i ∈ Work.FIArea4.A6supp Pa X j β,
              ∑' ℓ : ℤ, c ℓ * S15sepTerm6 X j β ℓ u t i.1.1 i.1.2 i.2 := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ = (Real.log 4 : ℂ) * S15expSum6 Pa X j β 0 u t
          + ∑' ℓ : ℤ, ∑ i ∈ Work.FIArea4.A6supp Pa X j β,
              c ℓ * S15sepTerm6 X j β ℓ u t i.1.1 i.1.2 i.2 := by
          have hswap : (∑ i ∈ Work.FIArea4.A6supp Pa X j β,
              ∑' ℓ : ℤ, c ℓ * S15sepTerm6 X j β ℓ u t i.1.1 i.1.2 i.2)
            = ∑' ℓ : ℤ, ∑ i ∈ Work.FIArea4.A6supp Pa X j β,
              c ℓ * S15sepTerm6 X j β ℓ u t i.1.1 i.1.2 i.2 :=
            (Summable.tsum_finsetSum (fun i hi => hsumm i hi)).symm
          rw [hswap, S15expSum6_eq_sum_supp_finset Pa X j β 0 u t]
      _ = (Real.log 4 : ℂ) * S15expSum6 Pa X j β 0 u t
          + ∑' ℓ : ℤ, c ℓ * S15expSum6 Pa X j β ℓ u t := by
          congr 1
          refine tsum_congr (fun ℓ => ?_)
          rw [S15expSum6_eq_sum_supp_finset Pa X j β ℓ u t, Finset.mul_sum]
  rw [hmain]
  have hsmn : Summable (fun ℓ : ℤ => c ℓ * S15expSum6 Pa X j β ℓ u t) :=
    Summable.of_norm_bounded (hcnorm.mul_right M) (fun ℓ => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hM ℓ) (norm_nonneg _))
  have hnorm4 : ‖(Real.log 4 : ℂ)‖ = Real.log 4 := by
    rw [Complex.norm_def, Complex.normSq_ofReal, Real.sqrt_mul_self hlog4pos.le]
  have h0 : ‖(Real.log 4 : ℂ) * S15expSum6 Pa X j β 0 u t‖ ≤ Real.log 4 * M := by
    rw [norm_mul, hnorm4]
    exact mul_le_mul_of_nonneg_left (hM 0) hlog4pos.le
  have h1 : ‖∑' ℓ : ℤ, c ℓ * S15expSum6 Pa X j β ℓ u t‖ ≤ (∑' ℓ : ℤ, ‖c ℓ‖) * M := by
    calc ‖∑' ℓ : ℤ, c ℓ * S15expSum6 Pa X j β ℓ u t‖
        ≤ ∑' ℓ : ℤ, ‖c ℓ * S15expSum6 Pa X j β ℓ u t‖ := norm_tsum_le_tsum_norm hsmn.norm
      _ ≤ ∑' ℓ : ℤ, ‖c ℓ‖ * M := Summable.tsum_le_tsum (fun ℓ => by
            rw [norm_mul]
            exact mul_le_mul_of_nonneg_left (hM ℓ) (norm_nonneg _))
            hsmn.norm (hcnorm.mul_right M)
      _ = (∑' ℓ : ℤ, ‖c ℓ‖) * M := tsum_mul_right
  have hL2 : (1 : ℝ) ≤ (Real.log Pa.N + 1) ^ 2 := by
    have h := Real.log_nonneg Pa.hN1
    nlinarith
  have hkey : Real.log 4 * M ≤ Real.log 4 * M * (Real.log Pa.N + 1) ^ 2 := by
    have h2 : (0 : ℝ) ≤ Real.log 4 * M := mul_nonneg hlog4pos.le hMnn
    have h3 := mul_le_mul_of_nonneg_left hL2 h2
    simpa using h3
  calc ‖(Real.log 4 : ℂ) * S15expSum6 Pa X j β 0 u t
        + ∑' ℓ : ℤ, c ℓ * S15expSum6 Pa X j β ℓ u t‖
      ≤ ‖(Real.log 4 : ℂ) * S15expSum6 Pa X j β 0 u t‖
          + ‖∑' ℓ : ℤ, c ℓ * S15expSum6 Pa X j β ℓ u t‖ := norm_add_le _ _
    _ ≤ Real.log 4 * M + (∑' ℓ : ℤ, ‖c ℓ‖) * M := add_le_add h0 h1
    _ ≤ Real.log 4 * M + C₀ * (Real.log Pa.N + 1) ^ 2 * M :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_right hcbd hMnn)
    _ ≤ (Real.log 4 + C₀) * (Real.log Pa.N + 1) ^ 2 * M := by nlinarith [hkey]

end

end Work.FIArea4.A6psi
