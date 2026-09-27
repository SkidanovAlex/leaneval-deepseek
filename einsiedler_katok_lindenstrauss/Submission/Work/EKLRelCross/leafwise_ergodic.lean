import Mathlib
import Submission.Work.EKLContract.All
import Submission.Work.EKLRelCross.Instances
import Submission.Work.EKLRelCross.LeafBasic
import Submission.Work.EKLC6Core.Covariant
import Submission.Work.EKLC6Core.goodSet_subset_dirac
import Submission.Work.EKLC6Core.trivial_ae_dichotomy
import Submission.Work.EKLRelCross.leafwise_luzin
import Submission.Work.EKLRelCross.acovariant_of_isLeafwise
import Submission.Work.EKLRelCross.atomic_trivial_of_covariant

/-!
# (U8) of the frozen contract: the ergodic dichotomy of a leafwise system

`Work.EKLRelCross.leafwise_ergodic` is clause (U8) of `Work.EKLContract.P_Leafwise` (EKL §2.1,
p. 13): for an `A`-ergodic probability `μ` on `X₃`, a horospherical subgroup `U` contracted by a
measure-preserving `α^{t₀}` and a system `ν` of leafwise measures on a conull set `X'`,

  either `μ` has a conull `U`-cross-section, or `ν x` has no atom at the identity a.e.

The mathematical content splits into three pieces, of which this file supplies the third (and the
assembly):

* (U7) `A`-covariance of the leafwise system (`leafwise_acovariant`, EKL (4) / Pisa 7.16): the
  leafwise measures transform by conjugation along the diagonal flow.  Pisa 7.16 proves it by
  applying the `condexp` axiom of `IsLeafwise` to a flower and to its image under `α^t`; it is
  *not* a field of `IsLeafwise`.
* (U6) Luzin continuity (`leafwise_luzin`, EKL p. 14 / Federer 2.3.5): on a compact set of large
  measure, `x ↦ ∫ f dν x` is continuous.
* the *atomic case* (`atomic_trivial_of_covariant`, EKL p. 13, proved by a child): if `ν x` has
  positive mass at `1`, then `ν x = δ₁` a.e.; the proof combines (U7) with Poincaré recurrence
  of `α^{t₀}` and the Luzin continuity to force the masses `ν (α^{-n}x)` of shrinking boxes (and
  hence `ν x` itself) to concentrate at the identity.

The assembly then runs the standard argument: by (U7) the set `{ν x = δ₁}` is `A`-invariant, so
`trivial_ae_dichotomy` (`EKLC6Core`, coming from (U7)) splits the space into the trivial-a.e. case
and the non-trivial-a.e. case.  In the first case `goodSet ν X'` (the measurable set on which all
the test functions of `EKLC6Core.goodSet_subset_dirac` vanish) is conull and the *equivariance*
field of `IsLeafwise` alone yields the cross-section `B = goodSet ν X'`: if `x` and `u • x` both
lie in `B` then `ν x = ν (u • x) = δ₁` and the equivariance relation `ν x = c • (ν (u•x)).map (· * u)`
evaluated at `{1}` gives `1 = c * δ₁ {u⁻¹}`, whence `u = 1`.  In the second case the atomic case
upgrades `ν x ≠ δ₁` to `ν x {1} = 0`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

namespace Work.EKLRelCross

open Work.EKLContract

/-! ## The trivial-a.e. case: `ν x = δ₁` a.e. gives a cross-section -/

/-- **Cross-section from triviality.**  If the leafwise measures are the Dirac mass at the
identity almost everywhere, then `goodSet ν X'` — a Borel conull set — is a `U`-cross-section:
its cross-section property uses only the equivariance field of `IsLeafwise`. -/
theorem crossSection_of_trivial_ae (h2 : P_X3) (μ : Measure X3) [IsProbabilityMeasure μ]
    (U : Subgroup SL3) (hU : IsHoro U) (t0 : Fin 3 → ℝ)
    (ht0 : MeasurePreserving (fun x : X3 => aDiag t0 • x) μ μ)
    (hcontr : ∀ u ∈ U, Tendsto (fun n : ℕ => aDiag t0 ^ n * u * (aDiag t0 ^ n)⁻¹) atTop (𝓝 1))
    (ν : X3 → Measure SL3) (X' : Set X3) (hL : IsLeafwise μ U ν X')
    (hT : μ (Work.EKLC6Core.goodSet ν X') = 1) :
    CrossSection μ U := by
  have hGmeas : MeasurableSet (Work.EKLC6Core.goodSet ν X') :=
    Work.EKLC6Core.measurableSet_goodSet hL
  refine ⟨Work.EKLC6Core.goodSet ν X', hGmeas, ?_, ?_⟩
  · rw [MeasureTheory.measure_compl hGmeas (measure_ne_top μ _), hT, measure_univ, tsub_self]
  · intro x hx u hu hux
    have hxX' : x ∈ X' := hx.1
    have hyX' : u • x ∈ X' := hux.1
    have hdx : ν x = Measure.dirac 1 := Work.EKLC6Core.goodSet_subset_dirac hL hx
    have hdy : ν (u • x) = Measure.dirac 1 := Work.EKLC6Core.goodSet_subset_dirac hL hux
    obtain ⟨c, hc0, hct, hceq⟩ := hL.equivariant x hxX' u hu hyX'
    -- evaluate the equivariance relation at the singleton `{1}`
    have hval : (1 : ENNReal) = c * (((ν (u • x)).map (fun g : SL3 => g * u)) {1}) := by
      have h := congrArg (fun ρ : Measure SL3 => ρ {1}) hceq
      rw [Measure.smul_apply, smul_eq_mul, hdx,
        Measure.dirac_apply_of_mem (Set.mem_singleton (1 : SL3))] at h
      exact h
    have hmap : ((ν (u • x)).map (fun g : SL3 => g * u)) {1} = (ν (u • x)) {u⁻¹} := by
      rw [Measure.map_apply (by fun_prop) (measurableSet_singleton (1 : SL3))]
      congr 1
      ext g
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      exact ⟨fun h => eq_inv_of_mul_eq_one_left h, fun h => by rw [h, inv_mul_cancel]⟩
    rw [hmap, hdy] at hval
    by_cases hu1 : u = 1
    · exact hu1
    · exfalso
      have hinv : (1 : SL3) ∉ ({u⁻¹} : Set SL3) := fun h => hu1 (inv_eq_one.mp h.symm)
      rw [Measure.dirac_apply, Set.indicator_of_notMem hinv, mul_zero] at hval
      exact one_ne_zero hval

/-! ## The assembly -/

theorem leafwise_ergodic (h2 : Work.EKLContract.P_X3) (μ : MeasureTheory.Measure Work.EKLContract.X3) [MeasureTheory.IsProbabilityMeasure μ]
    (U : Subgroup Work.EKLContract.SL3) (hU : Work.EKLContract.IsHoro U) (t0 : Fin 3 → ℝ)
    (ht0 : MeasureTheory.MeasurePreserving (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t0 • x) μ μ)
    (hcontr : ∀ u ∈ U, Filter.Tendsto (fun n : ℕ => Work.EKLContract.aDiag t0 ^ n * u * (Work.EKLContract.aDiag t0 ^ n)⁻¹) Filter.atTop (nhds 1))
    (ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3) (X' : Set Work.EKLContract.X3) (hL : Work.EKLContract.IsLeafwise μ U ν X') :
    Work.EKLContract.IsAErgodic μ → Work.EKLContract.CrossSection μ U ∨ ∀ᵐ x ∂μ, ν x {1} = 0 := by
  intro hErg
  -- (U7): the `A`-covariance of the leafwise system on a conull set
  obtain ⟨X'', hX''sub, hX''meas, hX''conull, hcov⟩ :=
    acovariant_of_isLeafwise h2 μ U hU t0 ht0 hcontr ν X' hL hErg.1
  have hcov' : Work.EKLC6Core.ACovariant ν X'' := hcov
  by_cases hT : μ (Work.EKLC6Core.goodSet ν X') = 1
  · exact Or.inl (crossSection_of_trivial_ae h2 μ U hU t0 ht0 hcontr ν X' hL hT)
  · refine Or.inr ?_
    rcases Work.EKLC6Core.trivial_ae_dichotomy hL hU hcov' hX''conull hErg with htriv | hnontriv
    · -- `ν x = δ₁` a.e. makes `goodSet ν X'` conull, contradicting `hT`
      exfalso
      apply hT
      have hbad : μ ({x : X3 | ν x ≠ Measure.dirac 1} ∪ X'ᶜ) = 0 :=
        measure_union_null (MeasureTheory.ae_iff.mp htriv) hL.conull
      have hsub : (Work.EKLC6Core.goodSet ν X')ᶜ ⊆ {x : X3 | ν x ≠ Measure.dirac 1} ∪ X'ᶜ := by
        intro x hx
        by_cases hxX' : x ∈ X'
        · exact Or.inl fun hdirac => hx (Work.EKLC6Core.mem_goodSet_of_dirac hxX' hdirac)
        · exact Or.inr hxX'
      have hG : μ (Work.EKLC6Core.goodSet ν X')ᶜ = 0 :=
        le_antisymm ((measure_mono hsub).trans_eq hbad) bot_le
      have hGmeas : MeasurableSet (Work.EKLC6Core.goodSet ν X') :=
        Work.EKLC6Core.measurableSet_goodSet hL
      have hadd := MeasureTheory.measure_add_measure_compl (μ := μ) hGmeas
      rw [measure_univ, hG, add_zero] at hadd
      exact hadd
    · -- `ν x ≠ δ₁` a.e.; the atomic case forces `ν x {1} = 0`
      filter_upwards [hnontriv,
        atomic_trivial_of_covariant h2 μ U hU t0 ht0 hcontr ν X' X'' hL hcov' hX''conull
          (leafwise_luzin h2 μ U hU t0 ht0 hcontr ν X' hL) hErg]
        with x hxne hxat
      by_contra hne
      exact hxne (hxat (lt_of_le_of_ne (zero_le : (0 : ENNReal) ≤ ν x {1}) (Ne.symm hne)))

end Work.EKLRelCross
