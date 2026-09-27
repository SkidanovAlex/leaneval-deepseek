import Submission.Work.EKLC6Core.Sigma
import Submission.Work.EKLC6Core.Hcond_mono

/-!
# `EKLC6Core.EntSig` — entropy dominates the σ-algebra conditional entropy (Pisa 7.40, first half)

This is L3 of `PLAN.md`: for a `T`-decreasing σ-algebra `A`, the Kolmogorov–Sinai entropy of `T`
is at least `H_μ(A | T^{-1}A)`.  The proof is the finite-sub-partition argument: for a finite
partition `P` with `partSigma P ≤ A`, the past of `P` is contained in `comap T A`, so
`Hcond μ P (comap T A) ≤ hPart μ T P ≤ ent μ T`; taking the supremum over `P` gives the claim.
`(E5)` of `P_EntropyBasics` (`hPart = Hcond` against the past) is taken as a hypothesis so that
this lemma is independent of component C3.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract

/-- **L3 of `PLAN.md`** (Pisa 7.40, first half): the entropy dominates `H_μ(A | T^{-1}A)` for a
`T`-decreasing `A`. -/
theorem ent_ge_HcondSig {X : Type*} [mX : MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] (T : X → X)
    (hE5 : ∀ P : @FinPart X mX, @hPart X mX μ T P =
      @Hcond X mX μ P (⨆ n : ℕ, MeasurableSpace.comap (T^[n+1]) (@partSigma X mX P)))
    (A : MeasurableSpace X) (hdec : MeasurableSpace.comap T A ≤ A) :
    @HcondSig X mX μ A (MeasurableSpace.comap T A) ≤ @ent X mX μ T := by
  change (⨆ (P : {P : @FinPart X mX // @partSigma X mX P ≤ A}),
      ENNReal.ofReal (@Hcond X mX μ P.1 (MeasurableSpace.comap T A))) ≤ @ent X mX μ T
  refine iSup_le fun P => ?_
  have h1 : @Hcond X mX μ P.1 (MeasurableSpace.comap T A) ≤ @hPart X mX μ T P.1 := by
    have h0 := @Hcond_mono X mX μ inferInstance P.1
      (⨆ n : ℕ, MeasurableSpace.comap (T^[n+1]) (@partSigma X mX P.1))
      (MeasurableSpace.comap T A) (@past_le_comap X mX T A hdec P.1 P.2)
    rwa [← hE5 P.1] at h0
  exact le_trans (ENNReal.ofReal_le_ofReal h1)
    (le_iSup (fun Q : @FinPart X mX => ENNReal.ofReal (@hPart X mX μ T Q)) P.1)

end Work.EKLC6Core

end
