import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBox.tKinAmbAEMeasurable
import Submission.Work.BoseKinLoc.Compare.compare_box_energy_v2
import Submission.Work.BoseKinLoc.Kinetic.fibre_lift_general
import Submission.Work.BoseKinLoc.Sector.fsT_bound_all
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixGlue.Kinetic.integrable_kinForm`

**The localised kinetic word `u ↦ 𝒯_u` of a box state is integrable in the translation
parameter.**  For `N` particles, `ℓ > 0`, `d > 0`, `L > 0`, and a smooth state `Φ` of the
centred box `abox N L`,

    `u ↦ kinForm N ℓ d s ε_T b u Φ = Σ_i ℓ⁻³ ∫_x 1_{Λ(u)}(x_i)·fsT ℓ d s ε_T b u (fibre_i Φ x)`

is Bochner integrable on `ℝ³` (`Λ(u) = ℓu + [−ℓ/2,ℓ/2]³`, `fsT` = FS `eq:DefT`'s `𝒯_u`).

## Structure of the argument

The word is the `N`-body lift `Σᵢ𝒯_u^{(i)}` of the one-body word, and the whole `u`-dependence
is the position of the sliding box:

* *support.*  Off the support-adapted localisation cover `coverBoxU ℓ L` — the cube of side
  `(L+ℓ)/ℓ` consisting of the `u` whose box `Λ(u)` meets the centred one-particle box
  `acube L` — every slot fibre `fibre_i Φ x` vanishes on `Λ(u)` (its `i`-th slot would leave
  `abox N L`, where `Φ` is supported), so `fsT … u (fibre_i Φ x) = 0`
  (`Work.BoseKinLoc.Word.fsT_eq_zero_of_lamBox_const`) and the word vanishes
  (`Work.BoseKinLoc.Compare.kinForm_eq_zero_of_not_mem_coverBoxU`).  Hence
  `Function.support` of the word is contained in `coverBoxU ℓ L`, which is measurable
  (`Work.BoseKinLoc.Compare.measurableSet_coverBoxU`) of volume `(L+ℓ)³/ℓ³`
  (`Work.BoseKinLoc.Compare.volume_coverBoxU`), in particular of finite measure.

* *measurability.*  `Work.BoseBox.kinForm_aemeasurable_of_pos`: peeling each slot with
  `slotForm_eq_fibre_integral` turns it into the integral in `r` of `fsT` along the fibre
  family, whose joint `(u,r)`-a.e. strong measurability is
  `Work.BoseBox.fsT_fibre_aemeasurable` (the four pieces of `fsT`), and
  `AEStronglyMeasurable.integral_prod_right'` integrates it out.

* *bound.*  `Work.BoseKinLoc.Compare.exists_bound_kinForm`: `‖kinForm … u Φ‖` is bounded
  uniformly in `u` by a constant depending only on `(ℓ,d,s,ε_T,b)` and the (finite) `H¹` data of
  the slot fibres of `Φ`, via the one-body bound `Kinetic.fsT_H1_bound_all` and the
  integrability of the fibre data (`integral_fibre_sq`, `dSpace_fibre_eq`).

`IntegrableOn.of_bound` then gives the restricted integral over the cover, and the support
condition upgrades it to the global `Integrable`.
-/

namespace Work.BoseFixGlue.Kinetic

open MeasureTheory

theorem integrable_kinForm {N : ℕ} {ℓ L d s εT b : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (hL : 0 < L)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (hsupp : tsupport Φ ⊆ Submission.BoseGases.abox N L) :
    MeasureTheory.Integrable
      (fun u : EuclideanSpace ℝ (Fin 3) => Work.BoseKinLoc.kinForm N ℓ d s εT b u Φ) := by
  classical
  have hL0 : (0 : ℝ) ≤ L := le_of_lt hL
  -- the state is compactly supported (the centred box is compact for `L > 0`)
  have hcs : HasCompactSupport Φ :=
    IsCompact.of_isClosed_subset (Work.BoseKinLoc.Kinetic.abox_compact_of_nonneg N hL0)
      (isClosed_tsupport Φ) hsupp
  -- ## a.e. strong measurability of the word in the translation parameter
  have hmeas : MeasureTheory.AEStronglyMeasurable
      (fun u : EuclideanSpace ℝ (Fin 3) => Work.BoseKinLoc.kinForm N ℓ d s εT b u Φ)
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))) :=
    Work.BoseBox.kinForm_aemeasurable_of_pos hℓ hΦ hcs
  -- ## the word vanishes off the support-adapted cover
  have hvan : ∀ u : EuclideanSpace ℝ (Fin 3),
      u ∉ Work.BoseKinLoc.Compare.coverBoxU ℓ L →
        Work.BoseKinLoc.kinForm N ℓ d s εT b u Φ = 0 :=
    fun u hu => Work.BoseKinLoc.Compare.kinForm_eq_zero_of_not_mem_coverBoxU hℓ hsupp hu
  have hsupp_f : Function.support
      (fun u : EuclideanSpace ℝ (Fin 3) => Work.BoseKinLoc.kinForm N ℓ d s εT b u Φ)
      ⊆ Work.BoseKinLoc.Compare.coverBoxU ℓ L := by
    intro u hu
    by_contra huc
    exact hu (hvan u huc)
  -- ## the cover has finite measure
  have hfin : (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))
      (Work.BoseKinLoc.Compare.coverBoxU ℓ L) < ⊤ := by
    rw [Work.BoseKinLoc.Compare.volume_coverBoxU hℓ hL0]
    exact ENNReal.ofReal_lt_top
  -- ## it suffices to integrate over the cover
  refine (MeasureTheory.integrableOn_iff_integrable_of_support_subset hsupp_f).mp ?_
  rcases N with _ | n
  · -- `N = 0`: the word is an empty sum
    have hzero : (fun u : EuclideanSpace ℝ (Fin 3) =>
        Work.BoseKinLoc.kinForm 0 ℓ d s εT b u Φ) = fun _ => (0 : ℝ) := by
      funext u
      simp [Work.BoseKinLoc.kinForm]
    rw [hzero]
    exact MeasureTheory.integrableOn_zero
  · -- `N = n + 1`: the uniform bound on the cover
    obtain ⟨W, _hW0, hW⟩ :=
      Work.BoseKinLoc.Compare.exists_bound_kinForm (n := n) (ℓ := ℓ) (L := L) (d := d)
        (s := s) (εT := εT) (b := b) hℓ hL hd hΦ hsupp
    refine MeasureTheory.IntegrableOn.of_bound hfin ?_ W ?_
    · exact hmeas.mono_measure MeasureTheory.Measure.restrict_le_self
    · exact Filter.Eventually.of_forall fun u => hW u

end Work.BoseFixGlue.Kinetic
