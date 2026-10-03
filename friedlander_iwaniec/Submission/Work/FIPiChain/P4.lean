/-
# `Submission.Work.FIPiChain.P4` --- the FI endgame at a *free* scale `B`, from the integrated windows

This is node **P4** of the lead design (`Submission/Work/FIFinal/PIREMOVAL_LEAD.md`, §3): the
FIChain endgame re-run at a free sieve exponent `B ≥ 2`, consuming

* the integrated `(B′)`-window `Work.FIChain.BprimeWindowInt` (node P1,
  `Work.FIPiChain.P1Aw.BprimeWindowInt_ge`, produced by the areas' `Prop41StatementPiBig`), and
* the **`z`-integrated** `ρ`-window `Work.FIChain.RhoWindowInt2` at the chain's level
  `⌊(zc x B)^{1-etac}⌋` with top `e·sc x B·zc x B` (node P2,
  `Work.FIPiChain.P2Rho.RhoWindowInt2_ge`),

in place of the frozen pointwise contract `Work.FIChain.Prop41Stmt` that the pinned chain
(`Submission/Work/FIChain/PrimeSumSignedChain.lean`) uses.

The two halves are

* `Work.FIPiChain.Chain.PrimeSumSignedChain_B.primeSumSignedChain` --- the endgame
  (`Submission/Work/FIChain/PrimeSumSignedChain.lean` with `Bstar ↦ B` and the `(B′)`-window supplied
  by `hBp`);
* `Work.FIPiChain.Chain.S3fixed_signed_B.S3fixed_signed_Bstar` --- the `§8` `S₃` input
  (`Submission/Work/FIChain/S3fixed_signed_Bstar.lean` with `Bstar ↦ B`), whose `ρ`-side is fed by
  the three delegated nodes of P3 at the `ρ`-window of `hρ`:
  `Work.FIPiChain.S3minusC_dyadic_le` (the pointwise dyadic domination),
  `Work.FIPiChain.Grho_sum_measurable_bdd` (measurability, integrability and a bound of the
  `Grho`-sum) and `Work.FIPiChain.Grho_sum_zavg_le` (its `z`-average, from the integrated window).

The sieve gap is the proved `Work.FIChain.rosserLambda_FIgtil_r2`, as in
`Work.FIChain.PrimeSumSigned_of_prop41`.
-/
import Mathlib
import Submission.Work.FIPiChain.Defs
import Submission.Work.FIPiChain.HasB
import Submission.Work.FIPiChain.Chain.PrimeSumSignedChain_B
import Submission.Work.FIPiChain.Chain.S3fixed_signed_B
import Submission.Work.FIPiChain.P3S3.S3minusC_dyadic_le
import Submission.Work.FIPiChain.P3S3.Grho_sum_measurable_bdd
import Submission.Work.FIPiChain.P3S3.Grho_sum_zavg_le
import Submission.Work.FIChain.FIChainSieveGap_discharged
import Submission.Work.FIChain.scale_factsC

set_option autoImplicit false
set_option maxHeartbeats 3200000

namespace Work.FIPiChain

open Finset Filter
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- **The FI endgame at a free scale `B ≥ 2`, from the two integrated windows.**  This is
`Work.FIChain.primeSum_bound_of_prop41`'s conclusion with the frozen contract replaced by the two
`Π`-free *integrated* windows of the areas: the `(B′)`-window
`Work.FIChain.BprimeWindowInt` (P1) and the `z`-integrated `ρ`-window `Work.FIChain.RhoWindowInt2`
at the chain's level (P2), both at the same free exponent `B`. -/
theorem primeSum_bound_of_windowsInt (B : ℝ) (hB : 2 ≤ B)
    (hBp : ∃ K : ℝ, ∃ x₀ : ℕ, 0 < K ∧ ∀ x : ℕ, x₀ ≤ x →
      Work.FIChain.BprimeWindowInt Work.FIChain.atilc x Work.FIChain.wc
        (K * Work.FIChain.AcountAtilC x * (Real.log (x : ℝ)) ^ (-(4 : ℤ)))
        (Work.FIChain.Yc x B / (Work.FIChain.Deltac x : ℝ))
        (Work.FIChain.sc x B * (Real.exp 1 * Work.FIChain.Yc x B)))
    (hρ : ∃ K : ℝ, ∃ x₀ : ℕ, 0 < K ∧ ∀ x : ℕ, x₀ ≤ x →
      Work.FIChain.RhoWindowInt2 Work.FIChain.atilc x Work.FIChain.wc
        (K * Work.FIChain.AcountAtilC x * (Real.log (x : ℝ)) ^ (-(4 : ℤ)))
        (((⌊(Work.FIChain.zc x B) ^ (1 - Work.FIChain.etac)⌋₊ : ℕ) : ℝ))
        (Work.FIChain.zc x B) (Real.exp 1 * (Work.FIChain.sc x B * Work.FIChain.zc x B))) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in Filter.atTop,
      |(∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, Real.log (p : ℝ) * Submission.ASP.FIa p)
          - (4 / Real.pi) * Submission.ASP.Acount Submission.ASP.FIa (N : ℝ)|
        ≤ C * Work.FIChain.AcountAtilC N
            * (Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ)) := by
  classical
  have hBpos : (0 : ℝ) < B := by linarith
  letI : HasBc := HasBc.of B hB
  have hBpCopy := hBp
  obtain ⟨Kbp, xbp, hKbp, hBwin⟩ := hBpCopy
  obtain ⟨Krho, xrho, hKrho, hrho⟩ := hρ
  obtain ⟨Ksie, hKsie, hsieve⟩ := Work.FIChain.FIChainSieveGap_proved
  -- ## the `ρ`-side facts at the scale `B` (node P3, instantiated at the window of `hρ`)
  have hdyad : ∀ᶠ x : ℕ in Filter.atTop, ∀ lam' : ℕ → ℝ, (∀ ν : ℕ, |lam' ν| ≤ 1) →
      ∀ z ∈ Set.Icc (Work.FIChain.zc x HasBc.val) (Real.exp 1 * Work.FIChain.zc x HasBc.val),
      ∀ y : ℝ,
      |Work.FIChain.S3minusC Work.FIChain.atilc lam' x z (Work.FIChain.sc x HasBc.val * y)
          (Work.FIChain.sc x HasBc.val * z)
          (((⌊(Work.FIChain.zc x HasBc.val) ^ (1 - Work.FIChain.etac)⌋₊ : ℕ) : ℝ))|
        ≤ ∑ j ∈ Finset.range (Work.FIChain.Jc x HasBc.val),
            Grho x (((⌊(Work.FIChain.zc x HasBc.val) ^ (1 - Work.FIChain.etac)⌋₊ : ℕ) : ℝ))
              ((2 : ℝ) ^ j * z) := by
    filter_upwards [Work.FIChain.scale_factsC B hBpos] with x hsc
    obtain ⟨-, -, -, -, -, -, -, -, -, hZ1, -, -, -, -, -, -⟩ := hsc
    have hzc1 : (1 : ℝ) ≤ Work.FIChain.zc x B := by
      rw [Work.FIChain.zc]
      exact_mod_cast hZ1
    have hCrp : (1 : ℝ) ≤ (Work.FIChain.zc x B) ^ (1 - Work.FIChain.etac) := by
      calc (1 : ℝ) = (1 : ℝ) ^ (1 - Work.FIChain.etac) := (Real.one_rpow _).symm
        _ ≤ (Work.FIChain.zc x B) ^ (1 - Work.FIChain.etac) :=
            Real.rpow_le_rpow zero_le_one hzc1 (by norm_num [Work.FIChain.etac])
    have hC1 : (1 : ℝ) ≤ ((⌊(Work.FIChain.zc x B) ^ (1 - Work.FIChain.etac)⌋₊ : ℕ) : ℝ) := by
      exact_mod_cast (Nat.one_le_floor_iff _).mpr hCrp
    intro lam' hlam' z hz y
    have hzpos : 0 < z := lt_of_lt_of_le (lt_of_lt_of_le zero_lt_one hzc1) hz.1
    have hmain := P3S3.S3minusC_dyadic_le x B lam' z (Work.FIChain.sc x B * y)
      (((⌊(Work.FIChain.zc x B) ^ (1 - Work.FIChain.etac)⌋₊ : ℕ) : ℝ)) hC1 hlam' hzpos
    exact hmain
  have hWmeas : ∀ᶠ x : ℕ in Filter.atTop, Measurable (fun z : ℝ =>
      ∑ j ∈ Finset.range (Work.FIChain.Jc x HasBc.val),
        Grho x (((⌊(Work.FIChain.zc x HasBc.val) ^ (1 - Work.FIChain.etac)⌋₊ : ℕ) : ℝ))
          ((2 : ℝ) ^ j * z)) := by
    filter_upwards [Work.FIChain.scale_factsC B hBpos, Filter.eventually_ge_atTop 1] with x hsc hx1
    obtain ⟨-, -, -, -, -, -, -, -, -, hZ1, -, -, -, -, -, -⟩ := hsc
    have hzc1 : (1 : ℝ) ≤ Work.FIChain.zc x B := by
      rw [Work.FIChain.zc]
      exact_mod_cast hZ1
    exact (P3S3.Grho_sum_measurable_bdd x B hx1 hzc1).1
  have hWint : ∀ᶠ x : ℕ in Filter.atTop, IntervalIntegrable (fun z : ℝ =>
      (∑ j ∈ Finset.range (Work.FIChain.Jc x HasBc.val),
        Grho x (((⌊(Work.FIChain.zc x HasBc.val) ^ (1 - Work.FIChain.etac)⌋₊ : ℕ) : ℝ))
          ((2 : ℝ) ^ j * z)) / z)
      MeasureTheory.volume (Work.FIChain.zc x HasBc.val)
        (Real.exp 1 * Work.FIChain.zc x HasBc.val) := by
    filter_upwards [Work.FIChain.scale_factsC B hBpos, Filter.eventually_ge_atTop 1] with x hsc hx1
    obtain ⟨-, -, -, -, -, -, -, -, -, hZ1, -, -, -, -, -, -⟩ := hsc
    have hzc1 : (1 : ℝ) ≤ Work.FIChain.zc x B := by
      rw [Work.FIChain.zc]
      exact_mod_cast hZ1
    exact (P3S3.Grho_sum_measurable_bdd x B hx1 hzc1).2.1
  have hWbdd : ∀ᶠ x : ℕ in Filter.atTop, ∃ V : ℝ,
      ∀ z ∈ Set.Icc (Work.FIChain.zc x HasBc.val) (Real.exp 1 * Work.FIChain.zc x HasBc.val),
        (∑ j ∈ Finset.range (Work.FIChain.Jc x HasBc.val),
          Grho x (((⌊(Work.FIChain.zc x HasBc.val) ^ (1 - Work.FIChain.etac)⌋₊ : ℕ) : ℝ))
            ((2 : ℝ) ^ j * z)) ≤ V := by
    filter_upwards [Work.FIChain.scale_factsC B hBpos, Filter.eventually_ge_atTop 1] with x hsc hx1
    obtain ⟨-, -, -, -, -, -, -, -, -, hZ1, -, -, -, -, -, -⟩ := hsc
    have hzc1 : (1 : ℝ) ≤ Work.FIChain.zc x B := by
      rw [Work.FIChain.zc]
      exact_mod_cast hZ1
    exact (P3S3.Grho_sum_measurable_bdd x B hx1 hzc1).2.2
  have hWzavg : ∀ᶠ x : ℕ in Filter.atTop,
      (∫ z in Work.FIChain.zc x HasBc.val..(Real.exp 1 * Work.FIChain.zc x HasBc.val),
        (∑ j ∈ Finset.range (Work.FIChain.Jc x HasBc.val),
          Grho x (((⌊(Work.FIChain.zc x HasBc.val) ^ (1 - Work.FIChain.etac)⌋₊ : ℕ) : ℝ))
            ((2 : ℝ) ^ j * z)) / z)
        ≤ (Work.FIChain.Jc x HasBc.val : ℝ)
            * (Krho * Work.FIChain.AcountAtilC x * (Real.log (x : ℝ)) ^ (-(4 : ℤ))) := by
    filter_upwards [Work.FIChain.scale_factsC B hBpos, Filter.eventually_ge_atTop xrho]
      with x hsc hxr
    obtain ⟨-, -, -, -, -, -, -, -, -, hZ1, -, -, -, -, -, -⟩ := hsc
    have hzc1 : (1 : ℝ) ≤ Work.FIChain.zc x B := by
      rw [Work.FIChain.zc]
      exact_mod_cast hZ1
    have hEρnn : 0 ≤ Krho * Work.FIChain.AcountAtilC x * (Real.log (x : ℝ)) ^ (-(4 : ℤ)) :=
      mul_nonneg (mul_nonneg hKrho.le (Work.FITop.AcountAtil_nonneg' x)) (by positivity)
    exact P3S3.Grho_sum_zavg_le x B _ hzc1 hEρnn (hrho x hxr)
  -- ## the two halves
  obtain ⟨K3, x₀, hK3pos, hS3raw⟩ :=
    S3fixed_signed_Bstar Kbp hKbp xbp hBwin Ksie hKsie hsieve Krho hKrho.le
      hdyad hWmeas hWint hWbdd hWzavg
  exact primeSumSignedChain hBp Ksie hKsie hsieve
    ⟨K3, hK3pos, Filter.eventually_atTop.mpr ⟨x₀, hS3raw⟩⟩

end

end Work.FIPiChain
