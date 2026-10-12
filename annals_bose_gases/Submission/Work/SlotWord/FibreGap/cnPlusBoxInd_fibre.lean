import Mathlib.Tactic.Have
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.SlotWord.integrableOn_boxQInd_sq_of_boundedOn
import Submission.Work.SlotWord.integral_slotFibre_cnPlusBoxInd
import Submission.Work.SlotWord.slotSplit_integral_fibre
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.SlotWord.FibreGap.cnPlusBoxInd_fibre`

**The fibre factorisation of the box excited count** — the `cnPlusBoxInd`-half of (R1)(a) of
`Submission/Work/PerSector/README.md` §6: the FS-faithful excited count of the *slot piece*
`slotPiece B S Φ = 1_{slotSet B S}·Φ` equals the `y`-integral, over the outside configurations
`y ∈ slotOutside L B S`, of the `|S|`-particle excited count of the *fibre*
`slotFibreState S e (slotPiece B S Φ) y`, transported to `X |S|` along a bijection
`e : SlotIn N S ≃ Fin |S|`.

The proof is the standard one for this identity: splitting the configuration space along
`slotSet B S`, the change of variables `x ↔ (ζ, y)` and Fubini (`slotSplit_integral_fibre`), the
pointwise collapse of the `N`-particle projections onto the `|S|`-particle ones
(`integral_slotFibre_cnPlusBoxInd`), and the boundedness of the projected squares on the box
(`integrableOn_boxQInd_sq_of_boundedOn`).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.SlotWord.FibreGap

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases
open BoseGases
open Work.PerSector
open Work.UBBInputs8
open Work.SmallBoxSliding
open Work.UBB

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

variable {N : ℕ}

theorem cnPlusBoxInd_fibre {N : ℕ} (L d : ℝ) (hL : 0 < L) (hd : 0 < d)
    (u : EuclideanSpace ℝ (Fin 3)) (S : Finset (Fin N)) (Φ : Submission.BoseGases.X N → ℝ)
    (hΦ : Continuous Φ) (e : Work.PerSector.SlotIn N S ≃ Fin S.card) :
    Work.UBBInputs8.cnPlusBoxInd L (Submission.BoseGases.dlBox L d u)
        (Work.SmallBoxSliding.boxMass L d u)
        (Work.PerSector.slotPiece (Submission.BoseGases.dlBox L d u) S Φ)
      = ∫ y in Work.PerSector.slotOutside L (Submission.BoseGases.dlBox L d u) S,
          Work.UBBInputs8.cnPlusBoxInd L (Submission.BoseGases.dlBox L d u)
            (Work.SmallBoxSliding.boxMass L d u)
            (Work.PerSector.slotFibreState S e
              (Work.PerSector.slotPiece (Submission.BoseGases.dlBox L d u) S Φ) y) := by
  classical
  have hA : MeasurableSet (dlBox L d u) := measurableSet_dlBox L d u
  have hAL : dlBox L d u ⊆ acube L := fun x hx => hx.1
  have hvol : boxMass L d u = (volume : Measure ℝ³).real (dlBox L d u) :=
    boxMass_eq_measureReal L d u
  -- a bound for `Φ` on the big box
  obtain ⟨C₀, hC₀⟩ := (Work.UBBInputs9.B.abox_isCompact N L).exists_bound_of_continuousOn
    hΦ.continuousOn
  set C : ℝ := max C₀ 0 with hCdef
  have hC0 : 0 ≤ C := le_max_right _ _
  have hC : ∀ x ∈ abox N L, |Φ x| ≤ C := by
    intro x hx
    rw [← Real.norm_eq_abs]
    exact le_trans (hC₀ x hx) (le_max_left _ _)
  -- the state and its slot piece are bounded on the big box
  have hspan : Measurable (slotPiece (dlBox L d u) S Φ) :=
    slotPiece_measurable _ hA S hΦ.measurable
  have hbound_span : ∀ x ∈ abox N L, |slotPiece (dlBox L d u) S Φ x| ≤ C := by
    intro x hx
    rw [slotPiece]
    by_cases hxs : x ∈ slotSet (dlBox L d u) S
    · rw [Set.indicator_of_mem hxs]; exact hC x hx
    · rw [Set.indicator_of_notMem hxs, abs_zero]; exact hC0
  -- integrability of each projected square on the big box
  have hIntj : ∀ j : Fin N, IntegrableOn (fun x => (boxQInd (boxMass L d u)
      (dlBox L d u) j (slotPiece (dlBox L d u) S Φ) x)^2) (abox N L) :=
    fun j => integrableOn_boxQInd_sq_of_boundedOn hA hAL hvol hspan hC0 hbound_span j
  -- the integrand of the excited count
  set G : X N → ℝ := fun x => ∑ j : Fin N, (boxQInd (boxMass L d u) (dlBox L d u) j
      (slotPiece (dlBox L d u) S Φ) x)^2 with hG
  have hIntG : IntegrableOn G (abox N L) := by
    rw [hG]
    exact integrable_finsetSum Finset.univ (fun j _ => hIntj j)
  -- `G` is supported on the slot set
  have hsuppG : ∀ x : X N, G x ≠ 0 → x ∈ slotSet (dlBox L d u) S := by
    intro x hx
    rw [hG] at hx
    by_contra hxnot
    apply hx
    refine Finset.sum_eq_zero (fun j _ => ?_)
    have hshift : x ∉ slotShiftSet (dlBox L d u) S j :=
      fun hmem => hxnot (slotShiftSet_subset_slotSet S j hmem)
    rw [boxQInd_slotPiece_eq_zero_of_notMem_slotShiftSet hA j S hshift]; ring
  -- the splitting of the configuration space
  have hsplit := slotSplit_integral_fibre (N := N) L S e hAL hIntG hsuppG
  have hSout : MeasurableSet (slotOutside L (dlBox L d u) S) :=
    Work.PerSector.Work.PerSector.slotBox_measurable ((acube_measurable L).inter hA.compl)
  -- the pointwise fibre identity at every outside configuration
  have hfig : ∀ y ∈ slotOutside L (dlBox L d u) S,
      (∫ ζ in abox S.card L, G (slotComb S (fun k : SlotIn N S => ζ (e k)) y))
        = cnPlusBoxInd L (dlBox L d u) (boxMass L d u)
            (slotFibreState S e (slotPiece (dlBox L d u) S Φ) y) := by
    intro y hy
    have hyo := mem_slotOutside_iff.mp hy
    have hyc : ∀ j : SlotOut N S, y j ∈ acube L := hyo.1
    -- the transport map `ζ ↦ slotComb S (ζ ∘ e) y` is measurable
    have hT : Measurable (fun ζ : X S.card =>
        slotComb S (fun k : SlotIn N S => ζ (e k)) y) := by
      rw [measurable_pi_iff]
      intro k
      by_cases hk : k ∈ S
      · have hthis : (fun ζ : X S.card =>
            slotComb S (fun k' : SlotIn N S => ζ (e k')) y k) = fun ζ => ζ (e ⟨k, hk⟩) := by
          funext ζ; rw [slotComb_apply, dif_pos hk]
        rw [hthis]
        exact measurable_pi_apply _
      · have hthis : (fun ζ : X S.card =>
            slotComb S (fun k' : SlotIn N S => ζ (e k')) y k) = fun _ => y ⟨k, hk⟩ := by
          funext ζ; rw [slotComb_apply, dif_neg hk]
        rw [hthis]
        exact measurable_const
    have hmeas : Measurable (slotFibreState S e (slotPiece (dlBox L d u) S Φ) y) := by
      rw [show slotFibreState S e (slotPiece (dlBox L d u) S Φ) y
          = fun ζ : X S.card => slotPiece (dlBox L d u) S Φ
              (slotComb S (fun k : SlotIn N S => ζ (e k)) y) from rfl]
      exact hspan.comp hT
    -- the fibre is bounded on the small box
    have hbound : ∀ ζ ∈ abox S.card L,
        |slotFibreState S e (slotPiece (dlBox L d u) S Φ) y ζ| ≤ C := by
      intro ζ hζ
      rw [slotFibreState_apply]
      refine hbound_span _ (fun k => ?_)
      rw [slotComb_apply]
      by_cases hk : k ∈ S
      · rw [dif_pos hk]; exact hζ _
      · rw [dif_neg hk]; exact hyc _
    rw [hG]
    exact integral_slotFibre_cnPlusBoxInd L hA hAL (boxMass L d u) S Φ e y
      (fun i => integrableOn_boxQInd_sq_of_boundedOn hA hAL hvol hmeas hC0 hbound i)
  rw [cnPlusBoxInd]
  rw [← integral_finsetSum Finset.univ (fun j _ => hIntj j)]
  change ∫ x in abox N L, G x = ∫ y in slotOutside L (dlBox L d u) S,
      cnPlusBoxInd L (dlBox L d u) (boxMass L d u)
        (slotFibreState S e (slotPiece (dlBox L d u) S Φ) y)
  rw [hsplit]
  refine integral_congr_ae ((MeasureTheory.ae_restrict_iff' hSout).mpr
    (Filter.Eventually.of_forall (fun y hy => hfig y hy)))

end Work.SlotWord.FibreGap
