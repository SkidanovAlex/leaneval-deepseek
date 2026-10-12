import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.boxQInd_self_boxPInd
import Submission.Work.BoseFixB1S.commutatorPairingB1
import Submission.Work.BoseFixB1S.intAbsCS
import Submission.Work.BoseFixB1S.n0FunOp_collapseB1
import Submission.Work.BoseFixB1S.n0LossPPairing
import Submission.Work.BoseFixB1S.n0PairingSumNice
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace Work.BoseFixB1S

open Submission.BoseGases

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-- **The per-slot `√`-split.**  For a single slot `i`, with `Θ₊ = √(n₀+1) + √c`,
`Θ₋ = √(n₀+1) − √c`, `L = n₀ + 1 − c`, `Qᵢ = boxQInd V A i Φ`, `Pᵢ = boxPInd V A i Φ`,

`∫ QᵢΦ·fib(xᵢ)·(L(PᵢΦ)) = ∫ (Θ₊(QᵢΦ))·fib(xᵢ)·(Θ₋(PᵢΦ))
    + ∫ ((Θ₊(fib(·ᵢ)·QᵢΦ)) − fib(xᵢ)·(Θ₊(QᵢΦ)))·(Θ₋(PᵢΦ))`.

The proof is the completion of squares (`n0FunOp_collapseB1`) followed by self-adjointness of
`Θ₊` (`n0FunOp_selfAdjointB1`), then the pointwise split `a·b = (fib·c)·b + (a−fib·c)·b`. -/
private theorem boxZpSplitB1_slot {N : ℕ} {ℓ V c : ℝ} (hℓ : 0 < ℓ) (hV : 0 < V)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hVeq : V = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ) (hc : 0 ≤ c)
    {fib : EuclideanSpace ℝ (Fin 3) → ℝ} (hfm : Measurable fib) (hfib0 : ∀ z, 0 ≤ fib z)
    {Cf : ℝ} (hfibb : ∀ z ∈ Submission.BoseGases.acube ℓ, |fib z| ≤ Cf)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ) (i : Fin N) :
    (∫ x in Submission.BoseGases.abox N ℓ,
        (Work.UBBInputs8.boxQInd V A i Φ x) * fib (x i)
          * (Work.BoseFixB1S.n0FunOp V A (fun r : ℝ => r + 1 - c)
              (Work.UBBInputs8.boxPInd V A i Φ)) x)
      = (∫ x in Submission.BoseGases.abox N ℓ,
            (Work.BoseFixB1S.n0FunOp V A (fun r : ℝ => Real.sqrt (r + 1) + Real.sqrt c)
                (Work.UBBInputs8.boxQInd V A i Φ)) x * fib (x i)
              * (Work.BoseFixB1S.n0FunOp V A (fun r : ℝ => Real.sqrt (r + 1) - Real.sqrt c)
                  (Work.UBBInputs8.boxPInd V A i Φ)) x)
        + (∫ x in Submission.BoseGases.abox N ℓ,
            ((Work.BoseFixB1S.n0FunOp V A (fun r : ℝ => Real.sqrt (r + 1) + Real.sqrt c)
                (fun y : Submission.BoseGases.X N =>
                  fib (y i) * Work.UBBInputs8.boxQInd V A i Φ y)) x
              - fib (x i) * (Work.BoseFixB1S.n0FunOp V A
                  (fun r : ℝ => Real.sqrt (r + 1) + Real.sqrt c)
                  (Work.UBBInputs8.boxQInd V A i Φ)) x)
              * (Work.BoseFixB1S.n0FunOp V A (fun r : ℝ => Real.sqrt (r + 1) - Real.sqrt c)
                  (Work.UBBInputs8.boxPInd V A i Φ)) x) := by
  classical
  have hCfib : 0 ≤ Cf := Cfib_nonneg hℓ hfibb
  have hΦG : GoodState ℓ Φ := goodState_of_continuous hℓ hΦc
  -- the spectral coefficient bounds at `{0,…,N}`
  have hcard : ∀ S : Finset (Fin N), (S.card : ℝ) ≤ (N : ℝ) := by
    intro S
    have h2 : S.card ≤ N := by simpa using Finset.card_le_univ S
    exact_mod_cast h2
  have hbP : ∀ S : Finset (Fin N),
      |(fun r : ℝ => Real.sqrt (r + 1) + Real.sqrt c) (S.card : ℝ)|
        ≤ Real.sqrt ((N : ℝ) + 1) + Real.sqrt c := by
    intro S
    have h1 : (S.card : ℝ) ≤ (N : ℝ) := hcard S
    have h2 : Real.sqrt ((S.card : ℝ) + 1) ≤ Real.sqrt ((N : ℝ) + 1) :=
      Real.sqrt_le_sqrt (by linarith)
    have h3 : (0 : ℝ) ≤ Real.sqrt ((S.card : ℝ) + 1) := Real.sqrt_nonneg _
    have h4 : (0 : ℝ) ≤ Real.sqrt c := Real.sqrt_nonneg _
    rw [abs_of_nonneg (add_nonneg h3 h4)]
    linarith
  have hbM : ∀ S : Finset (Fin N),
      |(fun r : ℝ => Real.sqrt (r + 1) - Real.sqrt c) (S.card : ℝ)|
        ≤ Real.sqrt ((N : ℝ) + 1) + Real.sqrt c := by
    intro S
    have h1 : (S.card : ℝ) ≤ (N : ℝ) := hcard S
    have h2 : Real.sqrt ((S.card : ℝ) + 1) ≤ Real.sqrt ((N : ℝ) + 1) :=
      Real.sqrt_le_sqrt (by linarith)
    have h3 : (0 : ℝ) ≤ Real.sqrt ((S.card : ℝ) + 1) := Real.sqrt_nonneg _
    have h4 : (0 : ℝ) ≤ Real.sqrt c := Real.sqrt_nonneg _
    calc |(fun r : ℝ => Real.sqrt (r + 1) - Real.sqrt c) (S.card : ℝ)|
        = |Real.sqrt ((S.card : ℝ) + 1) - Real.sqrt c| := rfl
      _ ≤ |Real.sqrt ((S.card : ℝ) + 1)| + |Real.sqrt c| := abs_sub _ _
      _ = Real.sqrt ((S.card : ℝ) + 1) + Real.sqrt c := by
          rw [abs_of_nonneg h3, abs_of_nonneg h4]
      _ ≤ Real.sqrt ((N : ℝ) + 1) + Real.sqrt c := by linarith
  -- abbreviations matching the `set gP/gM/gC/Ps/Qs/Xi/W` of the assembly
  set gP : ℝ → ℝ := fun r : ℝ => Real.sqrt (r + 1) + Real.sqrt c with hgP
  set gM : ℝ → ℝ := fun r : ℝ => Real.sqrt (r + 1) - Real.sqrt c with hgM
  set gC : ℝ → ℝ := fun r : ℝ => r + 1 - c with hgC
  set Ps : Submission.BoseGases.X N → ℝ := Work.UBBInputs8.boxPInd V A i Φ with hPs
  set Qs : Submission.BoseGases.X N → ℝ := Work.UBBInputs8.boxQInd V A i Φ with hQs
  set Xi : Submission.BoseGases.X N → ℝ := fun y => n0FunOp V A gM Ps y with hXi
  set W : Submission.BoseGases.X N → ℝ := fun y => fib (y i) * Qs y with hW
  have hPG : GoodState ℓ Ps := by
    simpa only [hPs] using goodState_boxPInd hℓ hV hA hVeq hAc i hΦG
  have hQG : GoodState ℓ Qs := by
    simpa only [hQs] using goodState_boxQInd hℓ hV hA hVeq hAc i hΦG
  have hbP' : ∀ S : Finset (Fin N),
      |gP (S.card : ℝ)| ≤ Real.sqrt ((N : ℝ) + 1) + Real.sqrt c :=
    fun S => by simpa only [hgP] using hbP S
  have hbM' : ∀ S : Finset (Fin N),
      |gM (S.card : ℝ)| ≤ Real.sqrt ((N : ℝ) + 1) + Real.sqrt c :=
    fun S => by simpa only [hgM] using hbM S
  have hXiG : GoodState ℓ Xi := by
    simpa only [hXi] using
      goodState_n0FunOp (N := N) hℓ hV hA hVeq hAc gM hbM' hPG
  have hWG : GoodState ℓ W := by
    simpa only [hW] using goodState_fib_mul (fib := fib) hfm i hCfib hfibb hQG
  have hθWG : GoodState ℓ (n0FunOp V A gP W) :=
    goodState_n0FunOp (N := N) hℓ hV hA hVeq hAc gP hbP' hWG
  have hθQG : GoodState ℓ (n0FunOp V A gP Qs) :=
    goodState_n0FunOp (N := N) hℓ hV hA hVeq hAc gP hbP' hQG
  have hfibθQG : GoodState ℓ (fun y => fib (y i) * (n0FunOp V A gP Qs) y) :=
    goodState_fib_mul (fib := fib) hfm i hCfib hfibb hθQG
  have hdefG : GoodState ℓ
      (fun y => (n0FunOp V A gP W) y - fib (y i) * (n0FunOp V A gP Qs) y) :=
    goodState_sub hθWG hfibθQG
  -- the collapsing identity of the completed square
  have hcoll : (fun x => n0FunOp V A gP Xi x)
      =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)]
      fun x => n0FunOp V A gC Ps x :=
    n0FunOp_collapseB1 hℓ hV hc hA hVeq hAc hPG
  -- ## the chain of integral identities
  have h1 : (∫ x in Submission.BoseGases.abox N ℓ,
        Qs x * fib (x i) * (n0FunOp V A gC Ps) x)
      = ∫ x in Submission.BoseGases.abox N ℓ,
        Qs x * fib (x i) * (n0FunOp V A gP Xi) x := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [hcoll] with x hx
    rw [← hx]
  have h2 : (∫ x in Submission.BoseGases.abox N ℓ,
        Qs x * fib (x i) * (n0FunOp V A gP Xi) x)
      = ∫ x in Submission.BoseGases.abox N ℓ, (n0FunOp V A gP Xi) x * W x := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    simp only [hW]
    ring
  have h3 : (∫ x in Submission.BoseGases.abox N ℓ, (n0FunOp V A gP Xi) x * W x)
      = ∫ x in Submission.BoseGases.abox N ℓ, Xi x * (n0FunOp V A gP W) x :=
    n0FunOp_selfAdjointB1 hℓ hV hA hVeq hAc gP hXiG hWG
  have h4 : (∫ x in Submission.BoseGases.abox N ℓ, Xi x * (n0FunOp V A gP W) x)
      = ∫ x in Submission.BoseGases.abox N ℓ, (n0FunOp V A gP W) x * Xi x := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    ring
  have h5 : (∫ x in Submission.BoseGases.abox N ℓ, (n0FunOp V A gP W) x * Xi x)
      = (∫ x in Submission.BoseGases.abox N ℓ,
            fib (x i) * (n0FunOp V A gP Qs) x * Xi x)
        + (∫ x in Submission.BoseGases.abox N ℓ,
            ((n0FunOp V A gP W) x - fib (x i) * (n0FunOp V A gP Qs) x) * Xi x) := by
    have hI1 : MeasureTheory.Integrable
        (fun x => fib (x i) * (n0FunOp V A gP Qs) x * Xi x)
        (MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)) :=
      integrableOn_mul_goodState hℓ hfibθQG hXiG
    have hI2 : MeasureTheory.Integrable
        (fun x => ((n0FunOp V A gP W) x - fib (x i) * (n0FunOp V A gP Qs) x) * Xi x)
        (MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)) :=
      integrableOn_mul_goodState hℓ hdefG hXiG
    have hpt : ∀ x : Submission.BoseGases.X N,
        (n0FunOp V A gP W) x * Xi x
          = fib (x i) * (n0FunOp V A gP Qs) x * Xi x
            + ((n0FunOp V A gP W) x - fib (x i) * (n0FunOp V A gP Qs) x) * Xi x :=
      fun x => by ring
    simp only [hpt]
    exact MeasureTheory.integral_add hI1 hI2
  have h6 : (∫ x in Submission.BoseGases.abox N ℓ,
        fib (x i) * (n0FunOp V A gP Qs) x * Xi x)
      = ∫ x in Submission.BoseGases.abox N ℓ,
        (n0FunOp V A gP Qs) x * fib (x i) * (n0FunOp V A gM Ps) x := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    simp only [hXi]
    ring
  have hmain := h1.trans (h2.trans (h3.trans (h4.trans (h5.trans (by rw [h6])))))
  simpa only [hQs, hPs, hgC, hgP, hgM, hXi, hW] using hmain

/-- **The `√`-split of the fibre-weighted FS cross pairing.**  With `Θ₊ = √(n₀+1) + √c`,
`Θ₋ = √(n₀+1) − √c`, `L = n₀ + 1 − c` (all `n₀`-functional calculus, `n0FunOp`), the FS box
projections `Qᵢ = boxQInd V A i Φ`, `Pᵢ = boxPInd V A i Φ` and a fibre `fib`, the fibre-weighted
cross pairing splits as

  `Σᵢ∫ QᵢΦ·fib(xᵢ)·(L(PᵢΦ)) = Σᵢ∫ (Θ₊(QᵢΦ))·fib(xᵢ)·(Θ₋(PᵢΦ))
      + Σᵢ∫ ((Θ₊(fib(·ᵢ)·QᵢΦ)) − fib(xᵢ)·(Θ₊(QᵢΦ)))·(Θ₋(PᵢΦ))`.

The first step is the completion of squares `L(p) = Θ₊(Θ₋p)` (`n0FunOp_collapseB1`) followed by
self-adjointness of `Θ₊ = n0FunOp …` on `L²(abox N ℓ)` (`n0FunOp_selfAdjointB1`), which moves `Θ₊`
onto the factor `fib(·ᵢ)·QᵢΦ`; the second step is the pointwise linearity
`a·b = (fib(xᵢ)·c)·b + (a − fib(xᵢ)·c)·b` with `a = Θ₊(fib(·ᵢ)·QᵢΦ)`, `c = Θ₊(QᵢΦ)`,
`b = Θ₋(PᵢΦ)`, summed with `integral_add`/`Finset.sum_add_distrib`.  It separates the
fibre-weighted AM–GM partner (`boxSharpPairingAMGMB1`) from the oscillation defect
(`commutatorPairingOscB1`).  All functions involved are measurable, bounded on the finite-measure
box `abox N ℓ` (hence integrable there).

WARNING for the prover: do NOT import `Submission.Work.BoseFixB1S.fsPCorpusAuxB1`,
`fsCompletionPairingB1`, `fsPCorpusB1`, `fsCompletionCoreB1` or `crossEngineB1Fix` — those modules
redeclare `Work.BoseFixB1S.goodState_n0FunOp`, and the caller must also import the
`commutatorPairingB1` cone (`commutatorPairingOscB1`, `boxSharpPairingAMGMB1`), which is
incompatible with them.  Everything needed here is in the `commutatorPairingB1` cone. -/
theorem boxZpSplitB1 {N : ℕ} {ℓ V c : ℝ} (hℓ : 0 < ℓ) (hV : 0 < V)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hVeq : V = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ) (hc : 0 ≤ c)
    {fib : EuclideanSpace ℝ (Fin 3) → ℝ} (hfm : Measurable fib) (hfib0 : ∀ z, 0 ≤ fib z)
    {Cf : ℝ} (hfibb : ∀ z ∈ Submission.BoseGases.acube ℓ, |fib z| ≤ Cf)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ) :
    (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
        (Work.UBBInputs8.boxQInd V A i Φ x) * fib (x i)
          * (Work.BoseFixB1S.n0FunOp V A (fun r : ℝ => r + 1 - c)
              (Work.UBBInputs8.boxPInd V A i Φ)) x)
      = (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
            (Work.BoseFixB1S.n0FunOp V A (fun r : ℝ => Real.sqrt (r + 1) + Real.sqrt c)
                (Work.UBBInputs8.boxQInd V A i Φ)) x * fib (x i)
              * (Work.BoseFixB1S.n0FunOp V A (fun r : ℝ => Real.sqrt (r + 1) - Real.sqrt c)
                  (Work.UBBInputs8.boxPInd V A i Φ)) x)
        + (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
            ((Work.BoseFixB1S.n0FunOp V A (fun r : ℝ => Real.sqrt (r + 1) + Real.sqrt c)
                (fun y : Submission.BoseGases.X N =>
                  fib (y i) * Work.UBBInputs8.boxQInd V A i Φ y)) x
              - fib (x i) * (Work.BoseFixB1S.n0FunOp V A
                  (fun r : ℝ => Real.sqrt (r + 1) + Real.sqrt c)
                  (Work.UBBInputs8.boxQInd V A i Φ)) x)
              * (Work.BoseFixB1S.n0FunOp V A (fun r : ℝ => Real.sqrt (r + 1) - Real.sqrt c)
                  (Work.UBBInputs8.boxPInd V A i Φ)) x) := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl
    (fun i _ => boxZpSplitB1_slot hℓ hV hA hVeq hAc hc hfm hfib0 hfibb hΦc i)

end Work.BoseFixB1S
