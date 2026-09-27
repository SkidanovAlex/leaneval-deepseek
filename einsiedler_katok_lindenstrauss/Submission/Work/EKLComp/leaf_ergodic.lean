import Mathlib
import Submission.Work.EKLComp.prove_X3
import Submission.Work.EKLRelCross.leafwise_ergodic

/-!
# `Work.EKLComp.leaf_ergodic` — clause (U8) of the frozen contract

For an `A`-ergodic probability `μ` on `X₃ = SL₃(ℝ)/SL₃(ℤ)`, a horospherical subgroup `U` contracted
by a measure-preserving `α^{t₀}`, and a system `ν` of leafwise measures on a co-null set `X'`,

  either `μ` has a conull `U`-cross-section, or `ν x` has no atom at the identity a.e.

This is exactly clause (U8) of `Work.EKLContract.P_Leafwise`.  The mathematics is carried out in
`Submission/Work/EKLRelCross/leafwise_ergodic.lean`, where the statement is proved from the
background component `P_X3` (used for the topological standing assumptions of Pisa §5–6: `T₂`,
Polish, and Luzin's theorem).  That component is unconditional for `SL₃(ℝ)/SL₃(ℤ)` — it is proved
in `Submission/Work/EKLComp/prove_X3.lean` — so we can discharge the hypothesis here.
-/

namespace Work.EKLComp

theorem leaf_ergodic (μ : MeasureTheory.Measure Work.EKLContract.X3) [MeasureTheory.IsProbabilityMeasure μ]
    (U : Subgroup Work.EKLContract.SL3) (hU : Work.EKLContract.IsHoro U) (t0 : Fin 3 → ℝ)
    (hmp : MeasureTheory.MeasurePreserving (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t0 • x) μ μ)
    (hcontr : ∀ u ∈ U, Filter.Tendsto (fun n : ℕ => Work.EKLContract.aDiag t0 ^ n * u * (Work.EKLContract.aDiag t0 ^ n)⁻¹) Filter.atTop (nhds 1))
    (ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3) (X' : Set Work.EKLContract.X3) (hL : Work.EKLContract.IsLeafwise μ U ν X') :
    Work.EKLContract.IsAErgodic μ → Work.EKLContract.CrossSection μ U ∨ ∀ᵐ x ∂μ, ν x {1} = 0 :=
  Work.EKLRelCross.leafwise_ergodic prove_X3 μ U hU t0 hmp hcontr ν X' hL

end Work.EKLComp
