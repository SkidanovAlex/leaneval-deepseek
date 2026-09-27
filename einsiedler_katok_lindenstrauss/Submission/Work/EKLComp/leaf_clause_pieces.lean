import Submission.Work.EKLC7.LeafwiseHoro
import Submission.Work.EKLC7.nu_equivariant
import Submission.Work.EKLCompSetup.exists_of
import Submission.Work.EKLRelCross.leafwise_propor
import Submission.Work.EKLRelCross.leafwise_luzin
import Submission.Work.EKLRelCross.leafwise_crossSection
import Submission.Work.EKLRelCross.atomic_trivial_of_covariant
import Submission.Work.EKLC6Core.trivial_ae_dichotomy
import Submission.Work.EKLRelCross.ae_translation_invariant_of_period
import Submission.Work.EKLRelCross.isUInvariant_of_ae_translation

/-!
# Clause-level pieces of the leafwise layer for `U_01`

Component C8 consumes the leafwise-measure input only through the clauses (U5), (U6), (U7),
(U8), (U9) at the distinguished root group `U_01`; the clause (U4) of `P_Leafwise` is *not*
used (see `Work.EKLCompSetup.exists_of_layer`).  This module proves all of them except (U7),
from the libraries of the other components:

* existence of the leafwise system (Pisa Thm 6.3): `Work.EKLC7.P_LeafwiseEx`, proved here as
  `leafwiseEx` from the flower construction `Work.EKLC7.FlowerFamExists`/`LeafNuFields`/
  `LeafNuCondExp`/`measurable_nu`/`OrbitCoord` and the equivariance clause
  `Work.EKLC7.nu_equivariant`;
* (U5) = `Work.EKLRelCross.leafwise_propor`;
* (U6) = Luzin = `Work.EKLRelCross.leafwise_luzin`;
* (U8) = the ergodic dichotomy `CrossSection μ U_01 ∨ ν x {1} = 0` a.e., assembled from (U7),
  `Work.EKLC6Core.trivial_ae_dichotomy`, `Work.EKLRelCross.atomic_trivial_of_covariant` (whose
  Luzin input is (U6)) and `Work.EKLRelCross.crossSection_of_ae_dirac`
  (Pisa 6.25 / EKL §2.1(8));
* (U9) = EKL (9): from (U7) together with `Work.EKLRelCross.ae_translation_invariant_of_period`
  (a nonzero period forces a.e. Haar leafwise measures) and
  `Work.EKLRelCross.isUInvariant_of_ae_translation` (Pisa 6.27: a.e. Haar leafwise measures
  force `U`-invariance).

The clause (U7) (EKL (4) = Pisa 7.16) is the one input taken from outside this module; it is
used by `leaf_layer01` as a hypothesis.
-/

open MeasureTheory Filter Topology
open scoped ENNReal Matrix
open Work.EKLContract Work.EKLComp

noncomputable section

namespace Work.EKLComp

/-- **(Pisa Thm 6.3 / EKL §2.1(1)–(3))** Existence of a system of leafwise measures for every
horospherical subgroup. -/
theorem leafwiseEx : Work.EKLC7.P_LeafwiseEx :=
  Work.EKLC7.LeafwiseHoro_of_equivariant
    (fun U μ hμ hU F coord hcoordm hcsub X' hX' =>
      @Work.EKLC7.nu_equivariant U μ F hμ hU coord hcoordm hcsub X' hX')

/-- Existence of the leafwise system at the distinguished root group `U_01`. -/
theorem leafwise_exists01 {μ : Measure X3} [IsProbabilityMeasure μ] (hA : IsAInvariant μ) :
    ∃ (ν₀ : X3 → Measure SL3) (X' : Set X3), IsLeafwise μ (Uij h01) ν₀ X' :=
  leafwiseEx μ hA (Uij h01) Work.EKLCompSetup.isHoro_Uij_h01

/-- **(U5) at `U_01`** (EKL (8)): a leafwise measure proportional to one of its right translates
is equal to it. -/
theorem u5clause01 (hX3 : P_X3) {μ : Measure X3} [IsProbabilityMeasure μ]
    (hErg : IsAErgodic μ) (ν : X3 → Measure SL3) (X' : Set X3)
    (hL : IsLeafwise μ (Uij h01) ν X') : U5clause μ ν :=
  Work.EKLRelCross.leafwise_propor hX3 μ (Uij h01) Work.EKLCompSetup.isHoro_Uij_h01
    Work.EKLCompSetup.t0 (hErg.1 Work.EKLCompSetup.t0)
    Work.EKLCompSetup.tendsto_conj_Uij_h01 ν X' hL

/-- **(U6) at `U_01`** (Luzin, EKL p. 14 / Federer 2.3.5): a compact subset of `X'` on which
`x ↦ ∫ f dν x` is continuous for every test function, of `μ`-measure as close to `1` as
desired. -/
theorem u6clause01 (hX3 : P_X3) {μ : Measure X3} [IsProbabilityMeasure μ]
    (hErg : IsAErgodic μ) (ν : X3 → Measure SL3) (X' : Set X3)
    (hL : IsLeafwise μ (Uij h01) ν X') : U6clause μ ν X' :=
  Work.EKLRelCross.leafwise_luzin hX3 μ (Uij h01) Work.EKLCompSetup.isHoro_Uij_h01
    Work.EKLCompSetup.t0 (hErg.1 Work.EKLCompSetup.t0)
    Work.EKLCompSetup.tendsto_conj_Uij_h01 ν X' hL

/-- **(U8) at `U_01`** (ergodic dichotomy, EKL §2.1(8)): either `U_01` is a `μ`-cross-section,
or the leafwise measures have no atom at the identity a.e. -/
theorem u8clause01 (hX3 : P_X3) {μ : Measure X3} [IsProbabilityMeasure μ]
    (hErg : IsAErgodic μ) (ν : X3 → Measure SL3) (X' : Set X3)
    (hL : IsLeafwise μ (Uij h01) ν X') (hU7 : U7clause μ ν X') :
    CrossSection μ (Uij h01) ∨ ∀ᵐ x ∂μ, ν x {1} = 0 := by
  obtain ⟨X'', -, -, hX''conull, hcov⟩ := hU7
  have hcov' : Work.EKLC6Core.ACovariant ν X'' := hcov
  have hU := Work.EKLCompSetup.isHoro_Uij_h01
  have ht0 := hErg.1 Work.EKLCompSetup.t0
  have hc := Work.EKLCompSetup.tendsto_conj_Uij_h01
  by_cases htriv : ∀ᵐ x ∂μ, ν x = Measure.dirac 1
  · exact Or.inl (Work.EKLRelCross.crossSection_of_ae_dirac hL htriv)
  · refine Or.inr ?_
    have hnontriv : ∀ᵐ x ∂μ, ν x ≠ Measure.dirac 1 := by
      rcases Work.EKLC6Core.trivial_ae_dichotomy hL hU hcov' hX''conull hErg with h | h
      · exact absurd h htriv
      · exact h
    have hatomic : ∀ᵐ x ∂μ, ν x {1} > 0 → ν x = Measure.dirac 1 :=
      Work.EKLRelCross.atomic_trivial_of_covariant hX3 μ (Uij h01) hU
        Work.EKLCompSetup.t0 ht0 hc ν X' X'' hL hcov' hX''conull
        (Work.EKLRelCross.leafwise_luzin hX3 μ (Uij h01) hU
          Work.EKLCompSetup.t0 ht0 hc ν X' hL) hErg
    filter_upwards [hnontriv, hatomic] with x hne hatomic_x
    exact le_antisymm (le_of_not_gt fun hp => hne (hatomic_x hp)) zero_le

/-- **(U9) at `U_01`** (EKL (9)): from (U7) and the period argument. -/
theorem u9clause01 (hX3 : P_X3) {μ : Measure X3} [IsProbabilityMeasure μ]
    (hErg : IsAErgodic μ) (ν : X3 → Measure SL3) (X' : Set X3)
    (hL : IsLeafwise μ (Uij h01) ν X') (hU7 : U7clause μ ν X') : U9clause μ ν := by
  intro hErg' hroot
  have hCov : Work.EKLRelCross.Covariance μ (Uij h01) ν X' := hU7
  have hAe : Work.EKLRelCross.AeHaar μ (Uij h01) ν :=
    Work.EKLRelCross.ae_translation_invariant_of_period hX3 μ (Uij h01)
      Work.EKLCompSetup.isHoro_Uij_h01 Work.EKLCompSetup.t0 (hErg.1 Work.EKLCompSetup.t0)
      Work.EKLCompSetup.tendsto_conj_Uij_h01 ν X' hL hErg' hCov 0 1 h01 rfl hroot
  exact Work.EKLRelCross.isUInvariant_of_ae_translation hX3 μ (Uij h01)
    Work.EKLCompSetup.isHoro_Uij_h01 Work.EKLCompSetup.t0 (hErg.1 Work.EKLCompSetup.t0)
    Work.EKLCompSetup.tendsto_conj_Uij_h01 ν X' hL hAe

/-- **The leafwise layer at `U_01`, clause level**, from a leafwise system with the clause (U7).
The clauses (U5), (U6), (U8) and (U9) at `U_01` are then produced here. -/
theorem leaf_layer01 (hX3 : P_X3) {μ : Measure X3} [IsProbabilityMeasure μ]
    (hErg : IsAErgodic μ) (ν : X3 → Measure SL3) (X' : Set X3)
    (hL : IsLeafwise μ (Uij h01) ν X') (hU7 : U7clause μ ν X') :
    ∃ (ν' : X3 → Measure SL3) (Y : Set X3),
      IsLeafwise μ (Uij h01) ν' Y ∧ U5clause μ ν' ∧ U6clause μ ν' Y ∧ U7clause μ ν' Y ∧
      (IsAErgodic μ → CrossSection μ (Uij h01) ∨ ∀ᵐ x ∂μ, ν' x {1} = 0) ∧
      U9clause μ ν' :=
  ⟨ν, X', hL, u5clause01 hX3 hErg ν X' hL, u6clause01 hX3 hErg ν X' hL, hU7,
    fun _ => u8clause01 hX3 hErg ν X' hL hU7, u9clause01 hX3 hErg ν X' hL hU7⟩

end Work.EKLComp
