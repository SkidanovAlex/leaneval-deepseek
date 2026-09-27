import Mathlib
import Submission.Work.EKLComp.prove_X3
import Submission.Work.EKLRelCross.leafwise_entropy_cs

/-!
# `Work.EKLComp.leaf_entropy_cs` — clause (U9) of the frozen contract

The frozen component `Work.EKLContract.P_Leafwise` contains the clause

> **(U9), EKL §2.1 (9).**  For an `A`-ergodic probability `μ` on `X₃ = SL₃(ℝ)/SL₃(ℤ)`, a
> one-dimensional root group `U = U_ij` contracted by a measure-preserving `α^{t₀}`, and a
> system `ν` of leafwise measures on a co-null set `X'`:
> if it is *not* the case that `ν x` is right-`u_ij(s)`-invariant for a.e. `x` **and every**
> nonzero `s`, then `μ` is invariant under `U_ij`.

Contrapositively (which is how the argument runs): a single nonzero period `s₀` of the leafwise
measures on a set of positive measure, combined with the `A`-covariance of the system and the
ergodicity of `μ`, forces `ν x` to be Haar a.e., and then Pisa 6.27 / clause (U4) gives
`U`-invariance of `μ`.

This file only assembles the mathematics, which is carried out in
`Submission/Work/EKLRelCross/leafwise_entropy_cs.lean` out of the pieces

* `Work.EKLRelCross.plaque_identity_base` — the `condexp` field evaluated at the base point of
  an orbit plaque (the local product structure of `μ` along `U`-plaques),
* `Work.EKLRelCross.plaque_ratio` — the resulting plaque-mass ratio,
* `Work.EKLRelCross.ae_covariance` — clause (U7) / EKL (4), the `A`-covariance,
* `Work.EKLRelCross.ae_translation_invariant_of_period` — the EKL (9) period argument,
* `Work.EKLRelCross.isUInvariant_of_ae_translation` — (U4) / Pisa 6.27.

The argument uses the topological background component `P_X3` of the frozen contract (T₂,
Polish, Mahler compactness, local injectivity of orbit maps), which is unconditional for
`SL₃(ℝ)/SL₃(ℤ)` and is proved in `Submission/Work/EKLComp/prove_X3.lean`; it is discharged here
by `Work.EKLComp.prove_X3`.  (The frozen statement bounds neither the `A`-invariance of `μ` nor
the topology of `X₃`, so this component has to be supplied by the caller -- exactly as in
`leaf_ergodic`.)
-/

open MeasureTheory Filter Topology
open scoped ENNReal

set_option linter.style.haveILetI false

noncomputable section

namespace Work.EKLComp

theorem leaf_entropy_cs (μ : MeasureTheory.Measure Work.EKLContract.X3) [MeasureTheory.IsProbabilityMeasure μ]
    (U : Subgroup Work.EKLContract.SL3) (hU : Work.EKLContract.IsHoro U) (t0 : Fin 3 → ℝ)
    (hmp : MeasureTheory.MeasurePreserving (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t0 • x) μ μ)
    (hcontr : ∀ u ∈ U, Filter.Tendsto (fun n : ℕ => Work.EKLContract.aDiag t0 ^ n * u * (Work.EKLContract.aDiag t0 ^ n)⁻¹) Filter.atTop (nhds 1))
    (ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3) (X' : Set Work.EKLContract.X3) (hL : Work.EKLContract.IsLeafwise μ U ν X') :
    Work.EKLContract.IsAErgodic μ → ∀ (i j : Fin 3) (hij : i ≠ j), U = Work.EKLContract.Uij hij →
        ¬ (∀ᵐ x ∂μ, ∀ s : ℝ, s ≠ 0 → (ν x).map (fun g => g * Work.EKLContract.uij hij s) ≠ ν x) →
        Work.EKLContract.IsUInvariant μ U :=
  Work.EKLRelCross.leafwise_entropy_cs prove_X3 μ U hU t0 hmp hcontr ν X' hL

end Work.EKLComp
