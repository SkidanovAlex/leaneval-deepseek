import Mathlib
import Submission.Work.ChenPlan.LinearSieve.JR2.Defs
import Submission.Work.ChenPlan.LinearSieve.RI.identity_minus
import Submission.Work.ChenPlan.LinearSieve.RI.lamMinus_sieve_lower
import Submission.Work.ChenPlan.LinearSieve.RI.lamMinus_multSum_le
import Submission.Work.ChenPlan.LinearSieve.RI.lamMinus_error_le
import Submission.Work.ChenPlan.LinearSieve.RIMain.LayerAux
import Submission.Work.ChenPlan.LinearSieve.Assembly.sum_layers_le
import Submission.Work.ChenPlan.LinearSieve.JR2.sum_T_le_riPsi

namespace Work.ChenPlan.LinearSieve.JR2

open Finset
open scoped BigOperators
open Work.NumberTheory.Chen.APSwitchUpper

/-- **The outer assembly of the sharp `λ⁻` (lower) sieve.**  Given the `λ⁻` layer-sum bound
`hsumT` (proved by `sum_T_le_riPsi` from `LayerSharpBound`), the rest of the sharp lower sieve
follows: the Rosser–Iwaniec identity `Gm A Z D = VfR A Z - Σ_{even n} T_n(D,Z)`
(`RI.identity_minus`), the minorant property `RI.lamMinus_multSum_le` and the remainder bound
`RI.lamMinus_error_le` (which needs `Z ≤ D`, i.e. `s ≥ 2`). -/
theorem sharp_sieve_lower_of_sum_T (C ρ : ℝ) (_hC : 0 ≤ C) (_hρ : 0 ≤ ρ) (_hρ1 : ρ ≤ 99/100)
    (hsumT : ∀ (A : BoundingSieve) (ε Z D : ℝ), 0 ≤ ε → ε ≤ 1/100 → 2 ≤ Z → 1 ≤ D →
      SharpNorm A Z ε → 2 ≤ Real.log D / Real.log Z →
      ∑ n ∈ (Finset.range (Nat.log 2 ⌈D⌉₊ + 3)).filter (fun n : ℕ => Even n ∧ n ≠ 0),
          T A n D Z
        ≤ VfR A Z * (riPsi (Real.log D / Real.log Z)
            + ε * (C * 10100) * errH (Real.log D / Real.log Z))) :
    SharpSieveLower C ρ (C * 10100) := by
  classical
  intro hLayer A ε Z D hε0 hε1 hZ hD hSharp hX hs
  have hZ1 : (1 : ℝ) < Z := by linarith
  have hlogZ : 0 < Real.log Z := Real.log_pos hZ1
  have hD0 : (0 : ℝ) < D := by linarith
  have hDnn : (0 : ℝ) ≤ D := le_of_lt hD0
  have hlogD : 2 * Real.log Z ≤ Real.log D := by
    have h := (le_div_iff₀ hlogZ).mp hs
    linarith
  have hZsq : Z ^ 2 ≤ D := by
    have hlog : Real.log (Z ^ 2) ≤ Real.log D := by
      rw [Real.log_pow]; push_cast; linarith
    exact (Real.log_le_log_iff (by positivity) hD0).mp hlog
  have hZD : Z ≤ D := by nlinarith
  have hTb := hsumT A ε Z D hε0 hε1 hZ hD hSharp hs
  have hlamProd : ∀ d ∈ (Pz A Z).divisors,
      lamMinus A.prodPrimes D d
        = (if rdMinus D d then ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0) := by
    intro d hd
    obtain ⟨hdd, -⟩ := Nat.mem_divisors.mp hd
    have hdvd : d ∣ A.prodPrimes := hdd.trans (RI.Pz_dvd_prodPrimes A Z)
    rw [lamMinus]
    by_cases h : rdMinus D d
    · rw [if_pos ⟨hdvd, h⟩, if_pos h]
    · rw [if_neg (fun hc => h hc.2), if_neg h]
  have hGmEq : (∑ d ∈ (Pz A Z).divisors, lamMinus A.prodPrimes D d * A.nu d) = RI.Gm A Z D := by
    rw [RI.Gm]
    exact Finset.sum_congr rfl (fun d hd => by rw [hlamProd d hd])
  have hid := RI.identity_minus A (D := D) (z := Z) hD
  have hGm : VfR A Z * (1 - riPsi (Real.log D / Real.log Z)
        - ε * (C * 10100) * errH (Real.log D / Real.log Z)) ≤ RI.Gm A Z D := by
    rw [← hGmEq, hid]
    have hkey : VfR A Z * (1 - riPsi (Real.log D / Real.log Z)
          - ε * (C * 10100) * errH (Real.log D / Real.log Z))
        = VfR A Z - VfR A Z * (riPsi (Real.log D / Real.log Z)
            + ε * (C * 10100) * errH (Real.log D / Real.log Z)) := by ring
    rw [hkey]
    linarith [hTb]
  have hlamPz : ∀ d ∈ (Pz A Z).divisors,
      lamMinus (Pz A Z) D d
        = (if rdMinus D d then ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0) := by
    intro d hd
    obtain ⟨hdd, -⟩ := Nat.mem_divisors.mp hd
    rw [lamMinus]
    by_cases h : rdMinus D d
    · rw [if_pos ⟨hdd, h⟩, if_pos h]
    · rw [if_neg (fun hc => h hc.2), if_neg h]
  have herr : -(Submission.ChenPlan.remSum A D)
      ≤ ∑ d ∈ (Pz A Z).divisors, lamMinus (Pz A Z) D d * A.rem d := by
    have h := RI.lamMinus_error_le A hDnn hZ hZD
    have h2 := (abs_le.mp h).1
    linarith
  have hminor := RI.lamMinus_multSum_le A Z D hDnn
  have hsplit : (∑ d ∈ (Pz A Z).divisors, lamMinus (Pz A Z) D d * A.multSum d)
      = A.totalMass * RI.Gm A Z D
        + ∑ d ∈ (Pz A Z).divisors, lamMinus (Pz A Z) D d * A.rem d := by
    have hterm : ∀ d ∈ (Pz A Z).divisors, lamMinus (Pz A Z) D d * A.multSum d
        = (if rdMinus D d then ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0)
            * (A.nu d * A.totalMass)
          + (if rdMinus D d then ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0) * A.rem d := by
      intro d hd
      rw [hlamPz d hd, BoundingSieve.multSum_eq_main_err]
      ring
    calc ∑ d ∈ (Pz A Z).divisors, lamMinus (Pz A Z) D d * A.multSum d
        = ∑ d ∈ (Pz A Z).divisors,
            ((if rdMinus D d then ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0)
                * (A.nu d * A.totalMass)
              + (if rdMinus D d then ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0) * A.rem d) :=
          Finset.sum_congr rfl hterm
      _ = (∑ d ∈ (Pz A Z).divisors,
              (if rdMinus D d then ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0)
                * (A.nu d * A.totalMass))
            + ∑ d ∈ (Pz A Z).divisors,
                (if rdMinus D d then ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0) * A.rem d :=
          Finset.sum_add_distrib
      _ = A.totalMass * RI.Gm A Z D
            + ∑ d ∈ (Pz A Z).divisors, lamMinus (Pz A Z) D d * A.rem d := by
          congr 1
          · rw [RI.Gm, Finset.mul_sum]
            exact Finset.sum_congr rfl (fun d _ => by ring)
          · exact Finset.sum_congr rfl (fun d hd => by rw [hlamPz d hd])
  have hstep : A.totalMass * VfR A Z
        * (1 - riPsi (Real.log D / Real.log Z)
            - ε * (C * 10100) * errH (Real.log D / Real.log Z))
      ≤ A.totalMass * RI.Gm A Z D := by
    have h := mul_le_mul_of_nonneg_left hGm hX
    rw [mul_assoc] at h
    linarith [h]
  linarith [hstep, herr, hminor, hsplit]

/-- **The sharp-normalised `λ⁻` (lower) sieve**, from the per-layer bound `LayerSharpBound C ρ`
(defined in `JR2/Defs.lean`; see `JR2/NOTES.md`).

NOTE: `Submission/Work/ChenPlan/LinearSieve/Assembly/sieve_of_main.lean` does NOT compile under
the v5/v6 interface change — do NOT import it (it also defines the helper
`lamMinus_multSum_le_siftedSumR`, which you must reprove here or obtain from
`RI/lamMinus_sieve_lower.lean`).  Working ingredients: `RI/lamMinus_sieve_lower.lean`
(the `λ⁻` minorant property / `IsLowerMoebiusOn`), `RI/identity_minus.lean`
(`RI.Gm A z E = VfR A z - Σ_{n even ≥ 2} T_n`), `RI/basic.lean` (`T`), `APSwitchUpper/prof.lean`
(`profC`, `riPsi`), `RIMain/LayerAux.lean`.

Assembly: `Σ_{d ∣ Pz} λ⁻(d)·multSum d ≤ siftedSumR A Z` (minorant property), the `λ⁻` remainder
part is `≥ -remSum A D` (`|λ⁻| ≤ 1`, and `rdMinus`-support forces `d < D` when `Z² ≤ D`, cf. the
broken blueprint's `RI.support_lt` case split), then `Gm = VfR Z - Σ_{n even ≥ 2} T_n` and the
per-layer bound with `Σ_{n even ≥ 2} profC (n-1) s ≤ riPsi s`; `Σ_{n ≥ 1}(n+1)ρ^{n-1} ≤ 10100`
for `ρ ≤ 99/100`. -/
theorem sharp_sieve_lower (C ρ : ℝ) (hC : 0 ≤ C) (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 99/100) :
    Work.ChenPlan.LinearSieve.JR2.SharpSieveLower C ρ (C * 10100) := by
  intro hLayer
  exact sharp_sieve_lower_of_sum_T C ρ hC hρ hρ1
    (fun A ε Z D hε0 hε1 hZ hD hSharp hs =>
      sum_T_le_riPsi (C := C) (ρ := ρ) hC hρ hρ1 hLayer A
        (ε := ε) (Z := Z) (D := D) hε0 hε1 hZ hD hSharp hs)
    hLayer

end Work.ChenPlan.LinearSieve.JR2
