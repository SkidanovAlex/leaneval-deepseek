import Submission.Work.EKLC6Core.EntSig
import Submission.Work.EKLC6Core.Hcond_le_hPart

/-!
# `EKLC6Core.ent_ge_HcondSig_le` — Pisa 7.40 (first half) from the `≤` half of Walters 4.14

`Work.EKLC6Core.ent_ge_HcondSig` proves `HcondSig μ A (comap T A) ≤ ent μ T` for a `T`-decreasing
`A` from the *equality* `hE5` of Walters 4.14 (`hPart = Hcond (· | past)`).  For the assembly of
`ent_ge_growth` only the `≤` half is needed, and that half is available unconditionally as
`Work.EKLC6Core.Hcond_le_hPart`.  This file records the resulting statement, which makes the
final assembly depend only on `Hcond_le_hPart` (already proved) instead of on the (harder)
equality `hE5`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract

/-- **Pisa 7.40, first half.**  For a `T`-decreasing σ-algebra `A`,
`H_μ(A | T^{-1}A) ≤ h_μ(T)`. -/
theorem ent_ge_HcondSig_le {X : Type*} [mX : MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] (T : X → X) (hmp : MeasurePreserving T μ μ)
    (A : MeasurableSpace X) (hdec : MeasurableSpace.comap T A ≤ A) :
    @HcondSig X mX μ A (MeasurableSpace.comap T A) ≤ @ent X mX μ T := by
  change (⨆ (P : {P : @FinPart X mX // @partSigma X mX P ≤ A}),
      ENNReal.ofReal (@Hcond X mX μ P.1 (MeasurableSpace.comap T A))) ≤ @ent X mX μ T
  refine iSup_le fun P => ?_
  have h1 : @Hcond X mX μ P.1 (MeasurableSpace.comap T A) ≤ @hPart X mX μ T P.1 := by
    have h0 := @Hcond_mono X mX μ inferInstance P.1
      (⨆ n : ℕ, MeasurableSpace.comap (T^[n+1]) (@partSigma X mX P.1))
      (MeasurableSpace.comap T A) (@past_le_comap X mX T A hdec P.1 P.2)
    exact le_trans h0 (@Hcond_le_hPart X mX μ inferInstance T hmp P.1)
  exact le_trans (ENNReal.ofReal_le_ofReal h1)
    (le_iSup (fun Q : @FinPart X mX => ENNReal.ofReal (@hPart X mX μ T Q)) P.1)

end Work.EKLC6Core

end
