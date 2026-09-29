import Mathlib
import Submission.Work.Resample.buDefs
import Submission.Work.ResMath.quad_ineq

namespace Work.Resample

open HvdH

/-- `buBeta s t n` is `s` times the paper's `β_n = tn/s - ⌊tn/s + 1/2⌋`
(`Work.ResMath.betaI`), after coercion to `ℝ`. -/
lemma buBeta_cast (s t : ℕ) (hs : 0 < s) (n : ℤ) :
    ((buBeta s t n : ℤ) : ℝ) = (s : ℝ) * Work.ResMath.betaI s t n := by
  have hs' : (s : ℝ) ≠ 0 := by positivity
  simp only [buBeta, Work.ResMath.betaI, HvdH.rnd]
  push_cast
  field_simp

/-- The integer numerator `buN s t ℓ h` of the exponent of the one-dimensional `B̃` weight equals
`s²` times the difference of the squares of the two working exponents `t h/s + β_ℓ` and
`β_{ℓ+h}`; since `t/s > 1` and `h ≠ 0`, that difference is positive (Lemma 4.6 of the paper,
`Work.ResMath.quad_ineq`), so `buN` is a positive integer. -/
theorem buNIdent (s t : ℕ) (hs : 0 < s) (hst : s < t) (ℓ h : ℤ) (hh : h ≠ 0) :
    ((Work.Resample.buN s t ℓ h : ℤ) : ℝ) =
        (s : ℝ) ^ 2 * (((t : ℝ) * (h : ℝ) / s + Work.ResMath.betaI s t ℓ) ^ 2
          - (Work.ResMath.betaI s t (ℓ + h)) ^ 2)
      ∧ 0 ≤ Work.Resample.buN s t ℓ h := by
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hid : ((buN s t ℓ h : ℤ) : ℝ) =
        (s : ℝ) ^ 2 * (((t : ℝ) * (h : ℝ) / s + Work.ResMath.betaI s t ℓ) ^ 2
          - (Work.ResMath.betaI s t (ℓ + h)) ^ 2) := by
    have h1 : ((buBeta s t ℓ : ℤ) : ℝ) = (s : ℝ) * Work.ResMath.betaI s t ℓ :=
      buBeta_cast s t hs ℓ
    have h2 : ((buBeta s t (ℓ + h) : ℤ) : ℝ) = (s : ℝ) * Work.ResMath.betaI s t (ℓ + h) :=
      buBeta_cast s t hs (ℓ + h)
    simp only [buN]
    push_cast
    rw [h1, h2]
    have e1 : (t : ℝ) * (h : ℝ) + (s : ℝ) * Work.ResMath.betaI s t ℓ
        = (s : ℝ) * ((t : ℝ) * (h : ℝ) / s + Work.ResMath.betaI s t ℓ) := by
      field_simp
    rw [e1]
    ring
  refine ⟨hid, ?_⟩
  -- positivity of the difference of squares, from Lemma 4.6 (`Work.ResMath.quad_ineq`)
  have hpos : 0 < ((t : ℝ) * (h : ℝ) / s + Work.ResMath.betaI s t ℓ) ^ 2
          - (Work.ResMath.betaI s t (ℓ + h)) ^ 2 := by
    have hstR : (s : ℝ) < t := by exact_mod_cast hst
    have hτ : 1 < (t : ℝ) / s := by rw [lt_div_iff₀ hsR]; simpa using hstR
    have hm : (1 : ℝ) ≤ |(h : ℝ)| := by
      have h1 : (1 : ℤ) ≤ |h| := Int.one_le_abs hh
      rw [← Int.cast_abs]; exact_mod_cast h1
    -- reduce the integer index `ℓ` modulo `s`, so that `Work.ResMath.quad_ineq` applies
    set n : ℤ := ℓ % s with hn
    have hn0 : 0 ≤ n := Int.emod_nonneg _ (by positivity)
    have hβ1 : Work.ResMath.betaI s t n = Work.ResMath.betaI s t ℓ := by
      rw [hn]
      conv_rhs => rw [← Int.emod_add_mul_ediv ℓ (s : ℤ)]
      exact (Work.ResMath.betaI_dvd_shift s t hs (ℓ % s) (ℓ / s)).symm
    have hβ2 : Work.ResMath.betaI s t (n + h) = Work.ResMath.betaI s t (ℓ + h) := by
      have hde : ℓ % s = ℓ - ℓ / s * s := by
        linarith [Int.emod_add_mul_ediv ℓ (s : ℤ)]
      have hsplit : ℓ - ℓ / s * s + h = (ℓ + h) + s * (-(ℓ / s)) := by ring
      rw [hn, hde, hsplit]
      exact Work.ResMath.betaI_dvd_shift s t hs (ℓ + h) (-(ℓ / s))
    have hntg : (n.toNat : ℤ) = n := Int.toNat_of_nonneg hn0
    have hns : n < (s : ℤ) := Int.emod_lt_of_pos _ (by positivity)
    have hfin_lt : n.toNat < s := by
      have h : (n.toNat : ℤ) < (s : ℤ) := by rw [hntg]; exact hns
      exact_mod_cast h
    have hfin : ((⟨n.toNat, hfin_lt⟩ : Fin s) : ℤ) = n := by
      simp [hntg]
    have hq := Work.ResMath.quad_ineq s t hs hst ⟨n.toNat, hfin_lt⟩ h hh
    rw [hfin, hβ1, hβ2] at hq
    have hleft : 0 < 2 * ((t : ℝ) / s - 1) * (|(h : ℝ)| - 1 / 2) ^ 2 := by
      have h1 : (0 : ℝ) < |(h : ℝ)| - 1 / 2 := by linarith
      have h2 : (0 : ℝ) < 2 * ((t : ℝ) / s - 1) := by linarith
      exact mul_pos h2 (pow_pos h1 2)
    linarith
  have hcast : (0 : ℝ) < ((buN s t ℓ h : ℤ) : ℝ) := by
    rw [hid]
    exact mul_pos (pow_pos hsR 2) hpos
  exact le_of_lt (by exact_mod_cast hcast : (0 : ℤ) < buN s t ℓ h)

end Work.Resample

