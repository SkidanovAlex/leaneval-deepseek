import Mathlib.Order.CompletePartialOrder
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.boxM1Info
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `χ_{B(u)}` vanishes when the sliding small box `B(u)` is a null set

`Submission.BoseGases.chiSmallB M ℓ d u x = χ(x/ℓ)·χ_M(x/(ℓd) − u)` is the two-factor
sliding cutoff of the localised potential kernels, whose support is contained in the
`u`-indexed small box `B(u) = dlBox ℓ d u = acube ℓ ∩ ((ℓd)•u + acube (ℓd))`.

Here we prove the degeneracy statement needed when the geometry of `B(u)` collapses
(the two cubes touch only along a lower-dimensional face): if the box is a null set then
the cutoff is identically zero.

The argument is cleaner than the sharp-support route used for the corpus bump `chiB`
(`Work.UBBInputs8.A.chiB_eq_zero_of_volume_dlBox_eq_zero`): the corpus bump is a
`ContDiffBump` with `rOut = 1/2`, whose *sharp* support (`chiScale ℓ x ≠ 0 → ‖x‖ < ℓ/2`)
is available, whereas here the second factor is the explicit cosine bump `chiSmall M`,
whose sharp support at `|z_j| = 1/2` would be a separate computation.  We avoid it
entirely by using continuity:

* `χ_{B(u)}` is continuous (`chiScale_continuous`, `chiSmall_continuous`), hence its
  support is **open**;
* its support is contained in `B(u)` (`chiSmallB_support_big_box` +
  `chiSmallB_support_small_box_dist`, coordinatewise, via `mem_acube_iff`).

So if `χ_{B(u)}(x) ≠ 0` then a whole ball around `x` lies in `B(u)`; that ball has
positive Lebesgue measure (`Metric.measure_ball_pos`) and `measure_mono` bounds the
volume of `B(u)` below by it — contradicting `volume B(u) = 0`.
-/

noncomputable section

open MeasureTheory Metric
open scoped Topology Real

namespace Work.BoseFixB1S

set_option autoImplicit false

/-- The support of the sliding cutoff is contained in the sliding small box: if
`χ_{B(u)}(x) ≠ 0` then `x ∈ dlBox ℓ d u`. -/
lemma chiSmallB_support_subset_dlBox {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ)
    (hd : 0 < d) (u : EuclideanSpace ℝ (Fin 3)) :
    Function.support (Submission.BoseGases.chiSmallB M ℓ d u) ⊆
      Submission.BoseGases.dlBox ℓ d u := by
  intro x hx
  rw [Function.mem_support] at hx
  rw [Submission.BoseGases.mem_dlBox_iff]
  refine ⟨?_, ?_⟩
  · rw [Submission.BoseGases.mem_acube_iff]
    intro m
    have hb := abs_le.mp (Submission.BoseGases.chiSmallB_support_big_box hM hℓ hx m)
    exact Set.mem_Icc.mpr ⟨by linarith [hb.1], hb.2⟩
  · rw [Submission.BoseGases.mem_acube_iff]
    intro m
    have hb := abs_le.mp (Submission.BoseGases.chiSmallB_support_small_box_dist hM hℓ hd hx m)
    exact Set.mem_Icc.mpr ⟨by linarith [hb.1], hb.2⟩

/-- The sliding cutoff `χ_{B(u)} = χ(·/ℓ)·χ_M(·/(ℓd) − u)` is continuous. -/
lemma chiSmallB_continuous {M : ℕ} (hM : 1 ≤ M) (ℓ d : ℝ) (u : EuclideanSpace ℝ (Fin 3)) :
    Continuous (Submission.BoseGases.chiSmallB M ℓ d u) := by
  show Continuous (fun x : EuclideanSpace ℝ (Fin 3) =>
    Submission.BoseGases.chiScale ℓ x * Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u))
  exact (Submission.BoseGases.chiScale_continuous ℓ).mul
    ((Submission.BoseGases.chiSmall_continuous hM).comp (by fun_prop))

theorem chiSmallB_eq_zero_of_volume_dlBox_eq_zero {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ}
    (hℓ : 0 < ℓ) (hd : 0 < d) (u : EuclideanSpace ℝ (Fin 3))
    (h : (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))
          (Submission.BoseGases.dlBox ℓ d u) = 0) :
    Submission.BoseGases.chiSmallB M ℓ d u = 0 := by
  have hsub := chiSmallB_support_subset_dlBox (M := M) hM hℓ hd u
  have hcont := chiSmallB_continuous (M := M) hM ℓ d u
  have hopen : IsOpen (Function.support (Submission.BoseGases.chiSmallB M ℓ d u)) := by
    have heq : Function.support (Submission.BoseGases.chiSmallB M ℓ d u) =
        (Submission.BoseGases.chiSmallB M ℓ d u) ⁻¹' ({0}ᶜ : Set ℝ) := by
      ext y
      simp [Function.mem_support]
    rw [heq]
    exact isOpen_compl_singleton.preimage hcont
  funext x
  by_contra hx
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hopen x hx
  have hpos : 0 < (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))
      (Submission.BoseGases.dlBox ℓ d u) :=
    lt_of_lt_of_le
      (Metric.measure_ball_pos
        (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))) x hr)
      (measure_mono (hball.trans hsub))
  rw [h] at hpos
  exact lt_irrefl 0 hpos

end Work.BoseFixB1S
