import Mathlib
import Submission.Work.Holonomy3.assembly_defs
import Submission.Work.Holonomy3.sieve_err_bound

namespace Work.Holonomy3

/-- **Auxiliary comparison of the assembly errors with the sieved sum.**

With `errC`, `errE` the two error terms of the assembly (which use `Dint = Ds + 1`), the quantity
`(2/(ds·(Ds+1)))·(errC + errE + |lnu0|)` is dominated by the sum of the ten terms appearing in the
expansion `Work.Holonomy3.sieveErr_expand` of `sieveErr` with the sieve parameter `Ds` (the sum
*before* the last summand `m·η`).

The proof is the term-by-term comparison obtained from `Ds ≤ Ds + 1`: each of the `1/x` and `log`
terms of the errors is at most the corresponding term with `Ds` in the denominator, the quadratic
`G₀`-term and the `ε`-terms agree, and the `U₀`-term absorbs `|lnu0| ≤ ds·U0`. -/
lemma sieve_err_compare_aux {m l ds Ds : ℕ} {ε G0 B U0 M errC errE lnu0 : ℝ}
    (hm : 0 < m) (hds : 0 < ds) (hDs : 1 ≤ Ds)
    (hε0 : 0 ≤ ε) (hG0 : 0 ≤ G0) (hB : 0 ≤ B) (hU0 : 0 ≤ U0) (hM : 1 ≤ M)
    (hlnu0 : |lnu0| ≤ (ds : ℝ) * U0)
    (herrC : errC = ε * ds * Ds + ds * Real.log ((Ds : ℝ) + 1) + ds * Real.log (m : ℝ)
      + ds * Real.log M + Real.log 2
      + (((Ds : ℝ) + 1) / (2 * ds)) * (8 * ((l : ℝ) + 1) ^ 2 * ((ds : ℝ) + 1) + ds) * G0
      + ((Ds : ℝ) + 1) * (ε + 2 / ((Ds : ℝ) + 1) + 1 / ds) * ds * G0)
    (herrE : errE = (m : ℝ) * ds * ((Ds : ℝ) + 1) * B
      * (3 * ε + 1 / ((Ds : ℝ) + 1) + 16 * ((l : ℝ) + 1) / ds)) :
    (2 / ((ds : ℝ) * ((Ds : ℝ) + 1))) * (errC + errE + |lnu0|) ≤
      2 * ε + 2 * Real.log ((Ds : ℝ) + 1) / (Ds : ℝ) + 2 * Real.log (m : ℝ) / (Ds : ℝ)
      + 2 * Real.log M / (Ds : ℝ) + 2 * Real.log 2 / ((ds : ℝ) * (Ds : ℝ))
      + (8 * ((l : ℝ) + 1) ^ 2 * ((ds : ℝ) + 1) + (ds : ℝ)) * G0 / (ds : ℝ) ^ 2
      + 2 * G0 * (ε + 2 / (Ds : ℝ) + 1 / (ds : ℝ))
      + 2 * ((m : ℝ) * B) * (3 * ε + 1 / (Ds : ℝ) + 16 * ((l : ℝ) + 1) / (ds : ℝ))
      + 2 * U0 / (Ds : ℝ) := by
  rw [herrC, herrE]
  have hdsR : (0 : ℝ) < (ds : ℝ) := by exact_mod_cast hds
  have hDsR : (0 : ℝ) < (Ds : ℝ) := by exact_mod_cast hDs
  have hlogδ : 0 ≤ Real.log ((Ds : ℝ) + 1) := Real.log_nonneg (by linarith)
  have hlogm : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg (by exact_mod_cast hm)
  have hlogM : 0 ≤ Real.log M := Real.log_nonneg (by exact_mod_cast hM)
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hA2 : 0 ≤ 8 * ((l : ℝ) + 1) ^ 2 * ((ds : ℝ) + 1) + (ds : ℝ) := by positivity
  have hDle : (Ds : ℝ) ≤ (Ds : ℝ) + 1 := by linarith
  field_simp
  ring_nf
  -- after clearing denominators the residual is a sum of nonnegative monomials
  have hres : (0 : ℝ) ≤ 2 * ↑Ds * ↑ds ^ 2 * ε + 2 * ↑Ds * ↑ds ^ 2 * U0 + 2 * ↑ds * Real.log 2
      + 2 * ↑ds ^ 2 * Real.log (1 + (↑Ds : ℝ)) + 2 * ↑ds ^ 2 * Real.log ↑m
      + 2 * ↑ds ^ 2 * Real.log M + 4 * ↑ds ^ 2 * G0 + 2 * ↑ds ^ 2 * ↑m * B
      + 2 * ↑ds ^ 2 * U0 - 2 * ↑Ds * ↑ds * |lnu0| := by
    have h1 : (0 : ℝ) ≤ 2 * ↑Ds * ↑ds ^ 2 * ε := by positivity
    have h2 : (0 : ℝ) ≤ 2 * ↑Ds * ↑ds * (↑ds * U0 - |lnu0|) := by
      have h0 : (0 : ℝ) ≤ (↑ds : ℝ) * U0 - |lnu0| := by linarith [hlnu0]
      positivity
    have h3 : (0 : ℝ) ≤ 2 * ↑ds * Real.log 2 := by positivity
    have h4 : (0 : ℝ) ≤ 2 * ↑ds ^ 2 * Real.log (1 + (↑Ds : ℝ)) := by
      have hh : (0 : ℝ) ≤ Real.log (1 + (↑Ds : ℝ)) := Real.log_nonneg (by linarith)
      positivity
    have h5 : (0 : ℝ) ≤ 2 * ↑ds ^ 2 * Real.log ↑m := by positivity
    have h6 : (0 : ℝ) ≤ 2 * ↑ds ^ 2 * Real.log M := by positivity
    have h7 : (0 : ℝ) ≤ 4 * ↑ds ^ 2 * G0 := by positivity
    have h8 : (0 : ℝ) ≤ 2 * ↑ds ^ 2 * ↑m * B := by positivity
    have h9 : (0 : ℝ) ≤ 2 * ↑ds ^ 2 * U0 := by positivity
    linarith
  nlinarith only [hres]

/-- **The comparison of the assembly error with the sieved error.**

If the sieve error `sieveErr m l ds Ds G0 B 0 M U0 ε (η₁/(16m))` (built with the sieve parameter
`Ds`) is at most `η₁`, then the assembly error
`(2/(ds·(Ds+1)))·(errC + errE + |lnu0|) + m·(η₁/(16m))`
(which uses `Dint = Ds + 1`) is also at most `η₁`.

Indeed the last summand of `sieveErr` contributes `(2/(ds·Ds))·(m·ds·Ds/2)·(η₁/(16m)) = η₁/16`
after cancelling, exactly matching the `m·(η₁/(16m)) = η₁/16` on the left, while the remaining
nine terms dominate `(2/(ds·(Ds+1)))·(errC + errE + |lnu0|)` by
`Work.Holonomy3.sieve_err_compare_aux`. -/
theorem sieve_err_compare {m l ds Ds : ℕ} {ε G0 B U0 M η₁ errC errE lnu0 : ℝ}
    (hm : 0 < m) (hds : 0 < ds) (hDs : 1 ≤ Ds)
    (hε0 : 0 ≤ ε) (hG0 : 0 ≤ G0) (hB : 0 ≤ B) (hU0 : 0 ≤ U0) (hM : 1 ≤ M)
    (hlnu0 : |lnu0| ≤ (ds : ℝ) * U0)
    (herrC : errC = ε * ds * Ds + ds * Real.log ((Ds : ℝ) + 1) + ds * Real.log (m : ℝ)
      + ds * Real.log M + Real.log 2
      + (((Ds : ℝ) + 1) / (2 * ds)) * (8 * ((l : ℝ) + 1) ^ 2 * ((ds : ℝ) + 1) + ds) * G0
      + ((Ds : ℝ) + 1) * (ε + 2 / ((Ds : ℝ) + 1) + 1 / ds) * ds * G0)
    (herrE : errE = (m : ℝ) * ds * ((Ds : ℝ) + 1) * B
      * (3 * ε + 1 / ((Ds : ℝ) + 1) + 16 * ((l : ℝ) + 1) / ds))
    (hErrs : sieveErr m l ds Ds G0 B 0 M U0 ε (η₁ / (16 * (m : ℝ))) ≤ η₁) :
    (2 / ((ds : ℝ) * ((Ds : ℝ) + 1))) * (errC + errE + |lnu0|)
      + (m : ℝ) * (η₁ / (16 * (m : ℝ))) ≤ η₁ := by
  have hDs0 : 0 < Ds := by omega
  -- the expansion of the sieve error, with the last summand evaluated
  have hE := sieveErr_expand (m := m) (l := l) (d := ds) (D := Ds) (G₀ := G0) (B := B)
    (C₀ := 0) (M' := M) (U₀ := U0) (ε := ε) (η := η₁ / (16 * (m : ℝ))) hds hDs0
  have hη : (m : ℝ) * (η₁ / (16 * (m : ℝ))) = η₁ / 16 := by
    have hmne : ((m : ℝ)) ≠ 0 := by positivity
    field_simp
  -- the sieve sum (without the `m·η` summand, which equals `η₁/16`)
  have hErrs' : 2 * ε + 2 * Real.log ((Ds : ℝ) + 1) / (Ds : ℝ)
      + 2 * Real.log (m : ℝ) / (Ds : ℝ)
      + 2 * Real.log M / (Ds : ℝ) + 2 * Real.log 2 / ((ds : ℝ) * (Ds : ℝ))
      + (8 * ((l : ℝ) + 1) ^ 2 * ((ds : ℝ) + 1) + (ds : ℝ)) * G0 / (ds : ℝ) ^ 2
      + 2 * G0 * (ε + 2 / (Ds : ℝ) + 1 / (ds : ℝ))
      + 2 * ((m : ℝ) * B) * (3 * ε + 1 / (Ds : ℝ) + 16 * ((l : ℝ) + 1) / (ds : ℝ))
      + 2 * U0 / (Ds : ℝ) + η₁ / 16 ≤ η₁ := by
    have h := hErrs
    rw [hE, hη] at h
    simpa only [zero_add] using h
  have hA := sieve_err_compare_aux hm hds hDs hε0 hG0 hB hU0 hM hlnu0 herrC herrE
  clear hE hErrs herrC herrE
  rw [hη]
  linarith [hErrs', hA]

end Work.Holonomy3
