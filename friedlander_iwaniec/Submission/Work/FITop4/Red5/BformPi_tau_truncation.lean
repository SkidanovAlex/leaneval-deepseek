/-
# `Submission.Work.FITop4.Red5.BformPi_tau_truncation`

The `τ`-truncation (4.10) of the `Π`-restricted bilinear form: dropping the inner terms with
`τ(n) > τ` (`n.divisors.card > τ`) loses at most
`c·τ⁻¹·Ã(x)·(log x)^{131072}`, under the paper's (4.11)
`τ ≥ (log x)^{A+124} ≥ (log x)^{124}`.

The proof splits the two-sided comparison into two lemmas, both proved by colleagues:

* `BformPi_trunc_le`  — the *exact* error term `BformPi ≤ BformPiTau + τ⁻¹·Σ_{l ≤ x} ã_l τ(l)³`,
  by the triangle inequality, `|γ(n;C)| ≤ τ(n)`, and the divisor-pair reindexing
  `Work.FITop.TauMulReindex` (`Σ_m Σ_{n : mn ≤ x} g(mn) ≤ Σ_{l≤x} τ(l) g(l)`);
* `AseqTauCubBound` — the polylogarithmic bound `Σ_{l ≤ x} ã_l τ(l)³ ≤ C·Ã(x)(log x)^{131072}`
  (from `Work.FITop.AseqTauEightBound`).

The only arithmetic left here is `τ ≥ (log x)^{124} > 0`, which turns the exact error into the
paper's `c·τ⁻¹·Ã(x)·(log x)^{131072}`.
-/
import Mathlib
import Submission.Work.FITop4.Defs4
import Submission.Work.FITop4.Red5.Vocab
import Submission.Work.FITop.AseqTauEightBound
import Submission.Work.FITop4.Red5.Aseq_tau_sq_le
import Submission.Work.FITop4.Red5.AseqTauCubBound
import Submission.Work.FITop4.Red5.BformPi_trunc_le

set_option autoImplicit false

namespace Work.FITop4.Red5

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

theorem BformPi_tau_truncation :
    ∃ c x₀ : ℕ, 0 < c ∧ ∀ (x N Pz : ℕ) (C τ : ℝ), x₀ ≤ x → 1 ≤ N → 1 ≤ C →
      (Real.log (x : ℝ)) ^ (124 : ℕ) ≤ τ →
      Work.FITop.BformPi x N C Pz ≤ BformPiTau x N Pz C τ
        + c * τ⁻¹ * AcountAtil x * (Real.log (x : ℝ)) ^ (131072 : ℕ) := by
  obtain ⟨Cp, Xp, hCp, hp⟩ := AseqTauCubBound
  refine ⟨Cp, max Xp 3, hCp, ?_⟩
  intro x N Pz C τ hx _hN _hC hlog
  have hx3 : 3 ≤ x := le_trans (le_max_right Xp 3) hx
  have hxXp : Xp ≤ x := le_trans (le_max_left Xp 3) hx
  have hxR : (1 : ℝ) < (x : ℝ) := by
    have h : (3 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx3
    linarith
  have hlogpos : 0 < Real.log (x : ℝ) := Real.log_pos hxR
  have hτpos : 0 < τ := lt_of_lt_of_le (pow_pos hlogpos 124) hlog
  have hτinv : 0 ≤ τ⁻¹ := inv_nonneg.mpr hτpos.le
  have htrunc := BformPi_trunc_le x N Pz C τ hτpos
  have hsum := hp x hxXp
  calc Work.FITop.BformPi x N C Pz
      ≤ BformPiTau x N Pz C τ
          + τ⁻¹ * (∑ l ∈ Finset.Icc 1 x,
              Work.FITop.atilFIa l * ((l.divisors.card : ℝ) ^ 3)) := htrunc
    _ ≤ BformPiTau x N Pz C τ
          + τ⁻¹ * ((Cp : ℝ) * Work.FITop.AcountAtil x
              * (Real.log (x : ℝ)) ^ (131072 : ℕ)) := by
          exact add_le_add_right (mul_le_mul_of_nonneg_left hsum hτinv) _
    _ = BformPiTau x N Pz C τ
          + Cp * τ⁻¹ * Work.FITop.AcountAtil x
              * (Real.log (x : ℝ)) ^ (131072 : ℕ) := by ring

end

end Work.FITop4.Red5
