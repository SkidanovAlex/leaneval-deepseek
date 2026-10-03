import Mathlib
import Submission.Work.FIArea3.BoxDefs
import Submission.Work.FIArea3.gcd_cast_eq_sum_totient_ite

namespace Work.FIArea3

open Finset
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

/-- Divisibility transfer: for `e : ℕ` and `a : ℤ`, `(e : ℤ) ∣ a ↔ e ∣ a.natAbs`. -/
private lemma int_dvd_iff_natAbs (e : ℕ) (a : ℤ) : (e : ℤ) ∣ a ↔ e ∣ a.natAbs := by
  rw [← Int.natAbs_dvd_natAbs (a := (e : ℤ)) (b := a), Int.natAbs_natCast]

/-- The pointwise divisor-sum representation of `gcd(gcd z.re z.im, d)`:
`gcd(a,d) = ∑_{e ∣ d} φ(e)·[e ∣ a]` with `a = gcd(|re|,|im|)`. -/
private lemma gcd_gcd_cast_eq_sum_totient_ite (z : GaussianInt) (d : ℕ) (hd : 1 ≤ d) :
    ((Nat.gcd (Nat.gcd z.re.natAbs z.im.natAbs) d : ℕ) : ℝ)
      = ∑ e ∈ d.divisors,
          (if e ∣ Nat.gcd z.re.natAbs z.im.natAbs then (Nat.totient e : ℝ) else 0) := by
  rw [Nat.gcd_comm (Nat.gcd z.re.natAbs z.im.natAbs) d]
  exact gcd_cast_eq_sum_totient_ite d (Nat.gcd z.re.natAbs z.im.natAbs) hd

/-- The arithmetic core: for `1 ≤ e ≤ d` and `u ≥ 0`,
`φ(e)·(10u/e + 1)² ≤ 100u² + 20u + d`.  Indeed `φ(e) ≤ e`, `e·(10u/e+1)² = 100u²/e + 20u + e`,
and `100u²/e ≤ 100u²` for `e ≥ 1`. -/
private lemma totient_mul_sq_div_le (u : ℝ) (hu : 0 ≤ u) (e d : ℕ) (he : 1 ≤ e) (hed : e ≤ d) :
    (Nat.totient e : ℝ) * (10 * (u / (e : ℝ)) + 1) ^ 2
      ≤ 100 * u ^ 2 + 20 * u + (d : ℝ) := by
  have he0 : (0 : ℝ) < (e : ℝ) := by exact_mod_cast he
  have hne : (e : ℝ) ≠ 0 := ne_of_gt he0
  have hte : (Nat.totient e : ℝ) ≤ (e : ℝ) := by exact_mod_cast Nat.totient_le e
  have hsq : (0 : ℝ) ≤ (10 * (u / (e : ℝ)) + 1) ^ 2 := sq_nonneg _
  have h1 : (Nat.totient e : ℝ) * (10 * (u / (e : ℝ)) + 1) ^ 2
      ≤ (e : ℝ) * (10 * (u / (e : ℝ)) + 1) ^ 2 :=
    mul_le_mul_of_nonneg_right hte hsq
  have h2 : (e : ℝ) * (10 * (u / (e : ℝ)) + 1) ^ 2
      = 100 * u ^ 2 / (e : ℝ) + 20 * u + (e : ℝ) := by
    field_simp
    ring
  have h3 : 100 * u ^ 2 / (e : ℝ) ≤ 100 * u ^ 2 := by
    have hstep : 100 * u ^ 2 / (e : ℝ) ≤ 100 * u ^ 2 / 1 :=
      div_le_div_of_nonneg_left (by positivity : (0:ℝ) ≤ 100 * u ^ 2) one_pos
        (by exact_mod_cast he)
    simpa using hstep
  have h4 : (e : ℝ) ≤ (d : ℝ) := by exact_mod_cast hed
  linarith

/-- **The `gcd`-weighted count of the polar box.** For `d ≥ 1`, assuming the scaled counts `#{z ∈ polar box : g ∣ z.re ∧ g ∣ z.im} ≤ (10θ√N/g + 1)²` (supplied by `Work.FIArea3.scaled_polarBox_count`), one has `∑_{z ∈ box} gcd(gcd(z.re, z.im), d) ≤ (100(θ√N)² + 20θ√N + d)·τ(d)`.  Proof: `gcd(a,d) = ∑_{e ∈ d.divisors} φ(e)·[e ∣ a]` (from `Nat.sum_totient`), swap the sums, bound `#{z ∈ box : e ∣ gcd(z.re,z.im)} ≤ #{z ∈ box : e ∣ z.re ∧ e ∣ z.im} ≤ (10u/e+1)²`, and use `φ(e)/e² ≤ 1`, `φ(e)/e ≤ 1`, `φ(e) ≤ e`, with `∑_{e ∣ d} 1 = τ(d)` and `∑_{e ∣ d} e ≤ d·τ(d)`. -/
theorem sum_gcd_polarBox_le (Pa : Work.FITop.Params) (φ : ℝ) (d : ℕ) (hd : 1 ≤ d)
    (hcount : ∀ g : ℕ, 1 ≤ g →
      (((Work.FIArea3.polarBoxFinset Pa φ).filter
          (fun z => (g : ℤ) ∣ z.re ∧ (g : ℤ) ∣ z.im)).card : ℝ)
        ≤ (10 * ((Pa.θ * Real.sqrt Pa.N) / (g : ℝ)) + 1) ^ (2 : ℕ)) :
    (∑ z ∈ Work.FIArea3.polarBoxFinset Pa φ,
        ((Nat.gcd (Nat.gcd z.re.natAbs z.im.natAbs) d : ℕ) : ℝ))
      ≤ (100 * (Pa.θ * Real.sqrt Pa.N) ^ 2 + 20 * (Pa.θ * Real.sqrt Pa.N) + (d : ℝ))
          * ((d.divisors.card : ℕ) : ℝ) := by
  classical
  have hd0 : 0 < d := hd
  have hu0 : (0 : ℝ) ≤ Pa.θ * Real.sqrt Pa.N :=
    mul_nonneg Pa.hθ0.le (Real.sqrt_nonneg _)
  have hinner : ∀ e ∈ d.divisors,
      (∑ z ∈ polarBoxFinset Pa φ,
          (if e ∣ Nat.gcd z.re.natAbs z.im.natAbs then (Nat.totient e : ℝ) else 0))
        ≤ 100 * (Pa.θ * Real.sqrt Pa.N) ^ 2 + 20 * (Pa.θ * Real.sqrt Pa.N) + (d : ℝ) := by
    intro e he
    have hedvd : e ∣ d := (Nat.mem_divisors.mp he).1
    have he1 : 1 ≤ e := Nat.pos_of_dvd_of_pos hedvd hd0
    have hed : e ≤ d := Nat.le_of_dvd hd0 hedvd
    have hsum : (∑ z ∈ polarBoxFinset Pa φ,
          (if e ∣ Nat.gcd z.re.natAbs z.im.natAbs then (Nat.totient e : ℝ) else 0))
        = (((polarBoxFinset Pa φ).filter
              (fun z => e ∣ Nat.gcd z.re.natAbs z.im.natAbs)).card : ℝ)
            * (Nat.totient e : ℝ) := by
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    rw [hsum]
    have hsub : ((polarBoxFinset Pa φ).filter
          (fun z => e ∣ Nat.gcd z.re.natAbs z.im.natAbs))
        ⊆ ((polarBoxFinset Pa φ).filter (fun z => (e : ℤ) ∣ z.re ∧ (e : ℤ) ∣ z.im)) := by
      intro z hz
      rw [Finset.mem_filter] at hz ⊢
      exact ⟨hz.1,
        (int_dvd_iff_natAbs e z.re).mpr (hz.2.trans (Nat.gcd_dvd_left _ _)),
        (int_dvd_iff_natAbs e z.im).mpr (hz.2.trans (Nat.gcd_dvd_right _ _))⟩
    have hcard : (((polarBoxFinset Pa φ).filter
          (fun z => e ∣ Nat.gcd z.re.natAbs z.im.natAbs)).card : ℝ)
        ≤ (10 * ((Pa.θ * Real.sqrt Pa.N) / (e : ℝ)) + 1) ^ 2 :=
      le_trans (Nat.cast_le.mpr (Finset.card_le_card hsub)) (hcount e he1)
    calc (((polarBoxFinset Pa φ).filter
              (fun z => e ∣ Nat.gcd z.re.natAbs z.im.natAbs)).card : ℝ) * (Nat.totient e : ℝ)
        ≤ (10 * ((Pa.θ * Real.sqrt Pa.N) / (e : ℝ)) + 1) ^ 2 * (Nat.totient e : ℝ) :=
          mul_le_mul_of_nonneg_right hcard (Nat.cast_nonneg _)
      _ = (Nat.totient e : ℝ) * (10 * ((Pa.θ * Real.sqrt Pa.N) / (e : ℝ)) + 1) ^ 2 := by ring
      _ ≤ 100 * (Pa.θ * Real.sqrt Pa.N) ^ 2 + 20 * (Pa.θ * Real.sqrt Pa.N) + (d : ℝ) :=
          totient_mul_sq_div_le _ hu0 e d he1 hed
  calc (∑ z ∈ polarBoxFinset Pa φ,
        ((Nat.gcd (Nat.gcd z.re.natAbs z.im.natAbs) d : ℕ) : ℝ))
      = ∑ z ∈ polarBoxFinset Pa φ, ∑ e ∈ d.divisors,
          (if e ∣ Nat.gcd z.re.natAbs z.im.natAbs then (Nat.totient e : ℝ) else 0) :=
        Finset.sum_congr rfl fun z _ => gcd_gcd_cast_eq_sum_totient_ite z d hd
    _ = ∑ e ∈ d.divisors, ∑ z ∈ polarBoxFinset Pa φ,
          (if e ∣ Nat.gcd z.re.natAbs z.im.natAbs then (Nat.totient e : ℝ) else 0) :=
        Finset.sum_comm
    _ ≤ ∑ _e ∈ d.divisors,
          (100 * (Pa.θ * Real.sqrt Pa.N) ^ 2 + 20 * (Pa.θ * Real.sqrt Pa.N) + (d : ℝ)) :=
        Finset.sum_le_sum hinner
    _ = (100 * (Pa.θ * Real.sqrt Pa.N) ^ 2 + 20 * (Pa.θ * Real.sqrt Pa.N) + (d : ℝ))
          * ((d.divisors.card : ℕ) : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        ring

end

end Work.FIArea3
