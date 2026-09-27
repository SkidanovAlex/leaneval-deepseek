import Mathlib
import Submission.Work.EKLContract.All
import Submission.Work.EKLRelCross.Instances
import Submission.Work.EKLRelCross.LeafBasic
import Submission.Work.EKLRelCross.entropy_cs_interface
import Submission.Work.EKLRelCross.plaque_identity_base
import Submission.Work.EKLRelCross.plaque_ratio
import Submission.Work.EKLRelCross.ae_covariance
import Submission.Work.EKLRelCross.ae_translation_invariant_of_period
import Submission.Work.EKLRelCross.isUInvariant_of_ae_translation

/-!
# EKL (9) / clause (U9) of `P_Leafwise`: from a nontrivial period to `U`-invariance

The frozen contract `Work.EKLContract.P_Leafwise` (clause (U9), EKL §2.1 (9)) says: if for a
set of positive measure of points `x` the leafwise measure `ν x` is invariant under right
translation by some *nonzero* `u_ij(s)`, then `μ` is invariant under `U_ij`.

This file assembles the proof from pieces, following `ROUTE_LEAD.md` §C5 ("(U9) EKL (9) proof
… Then (U4)"):

* `plaque_identity_base` — the `condexp` field of `IsLeafwise` evaluated at the base point of an
  orbit plaque: the local product structure of `μ` along the `U`-plaques (this is what makes the
  interface's `ν` computable in terms of `μ`);
* `plaque_ratio` — its corollary: plaque masses transform by the ratio of the `ν x₀`-masses of
  the box and its right translate;
* `ae_covariance` — clause (U7) of `P_Leafwise` (EKL (4)) on a conull set, from `μ`'s
  `A`-invariance;
* `ae_translation_invariant_of_period` — the EKL (9) argument itself: a nonzero period on a
  positive-measure set forces, via the `A`-covariance and the ergodicity of `μ`, that `ν x` is
  invariant under right translation by *every* element of `U`, for a.e. `x`;
* `isUInvariant_of_ae_translation` — the (U4) direction (Pisa 6.27): a.e. Haar leafwise measures
  imply that `μ` is invariant under `U`.
-/

namespace Work.EKLRelCross

open MeasureTheory Filter Topology
open scoped ENNReal
open Work.EKLContract

theorem leafwise_entropy_cs (h2 : Work.EKLContract.P_X3) (μ : MeasureTheory.Measure Work.EKLContract.X3) [MeasureTheory.IsProbabilityMeasure μ]
    (U : Subgroup Work.EKLContract.SL3) (hU : Work.EKLContract.IsHoro U) (t0 : Fin 3 → ℝ)
    (ht0 : MeasureTheory.MeasurePreserving (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t0 • x) μ μ)
    (hcontr : ∀ u ∈ U, Filter.Tendsto (fun n : ℕ => Work.EKLContract.aDiag t0 ^ n * u * (Work.EKLContract.aDiag t0 ^ n)⁻¹) Filter.atTop (nhds 1))
    (ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3) (X' : Set Work.EKLContract.X3) (hL : Work.EKLContract.IsLeafwise μ U ν X') :
    Work.EKLContract.IsAErgodic μ → ∀ (i j : Fin 3) (hij : i ≠ j), U = Work.EKLContract.Uij hij →
        ¬ (∀ᵐ x ∂μ, ∀ s : ℝ, s ≠ 0 → (ν x).map (fun g => g * Work.EKLContract.uij hij s) ≠ ν x) →
        Work.EKLContract.IsUInvariant μ U := by
  intro hErg i j hij hUeq hroot
  -- the local product structure at base points, and the plaque-mass ratio
  have hP1 : PlaqueId μ U ν :=
    plaque_identity_base h2 μ U hU t0 ht0 hcontr ν X' hL
  have hP1' : PlaqueRatio μ U ν :=
    plaque_ratio h2 μ U hU t0 ht0 hcontr ν X' hL hP1
  -- the A-covariance (U7), clause of the frozen `P_Leafwise`
  have hCov : Covariance μ U ν X' :=
    ae_covariance h2 μ U hU t0 ht0 hcontr ν X' hL hErg.1 hP1'
  -- EKL (9): a nonzero period on a positive-measure set makes `ν x` Haar a.e.
  have hAe : AeHaar μ U ν :=
    ae_translation_invariant_of_period h2 μ U hU t0 ht0 hcontr ν X' hL hErg hCov i j hij hUeq hroot
  -- (U4): a.e. Haar leafwise measures imply U-invariance of μ
  exact isUInvariant_of_ae_translation h2 μ U hU t0 ht0 hcontr ν X' hL hAe

end Work.EKLRelCross
