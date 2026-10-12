import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Submission.Work.SlotWord.chiSmallB_support_mem_dlBox
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `chiMass ≤ (chiSupAbs · chiSmallDecay M)² · boxMass`

The sliding small-box cutoff

    χ_{B(u)}(x) = χ(x/ℓ) · χ_M(x/(ℓd) − u)

is the product of the corpus bump at the big-box scale (bounded by its absolute
sup `chiSupAbs` — its formula is hidden behind `Classical.choice`, so no
boundary decay of it is available, see `ChiSmall.chiSupAbs`) and the explicit
cosine-`M`-th-power bump at the small-box scale (bounded by `chiSmallDecay M`).
Hence `|χ_{B(u)}| ≤ chiSupAbs · chiSmallDecay M` **everywhere**, and — this is
the point of the statement — `χ_{B(u)}` is supported in the sliding box
`B(u) = dlBox ℓ d u` (`SlotWord.chiSmallB_support_mem_dlBox`, from the two
factorwise support containments).  Therefore

    chiMass M ℓ d u = ∫_x χ_{B(u)}(x)² dx ≤ C² · |B(u)| = C² · boxMass ℓ d u ,

with `C = chiSupAbs · chiSmallDecay M`: the `χ`-mass is dominated by the
constant `C²` times the *true* box volume.  This is the comparison that lets
every `χ_{B(u)}²`-weighted quantity of the sliding chapter be paid by the
box counting measure (the `boxMass` bookkeeping of
`SmallBoxSliding.boxMass_integral_u`, `∫_u boxMass ℓ d u = ℓ³`).

The proof is pointwise + monotonicity of the integral:
* `|χ_{B(u)}(x)| ≤ C` for every `x` (use `chiScale_abs_le_sup`,
  `chiSmall_decay_coord_le_decay`);
* if `χ_{B(u)}(x) ≠ 0` then `x ∈ B(u)`, where `boxInd ℓ d u x = 1`; otherwise
  the left-hand side is `0`. Either way
  `χ_{B(u)}(x)² ≤ C² · boxInd ℓ d u x`;
* `boxInd ℓ d u` is the indicator of a measurable set of finite volume
  (`measurableSet_dlBox`, `volume_dlBox_lt_top`), hence integrable, so
  `integral_mono_of_nonneg` applies and
  `∫_x C² · boxInd ℓ d u x = C² · boxMass ℓ d u`.
-/

open MeasureTheory
open scoped ENNReal Topology

namespace Work.BoseFixB1S

open Submission.BoseGases

theorem chiMass_le_const_mul_boxMass {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (u : EuclideanSpace ℝ (Fin 3)) :
    Work.SmallBoxSliding.chiMass M ℓ d u
      ≤ (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M) ^ 2
          * Work.SmallBoxSliding.boxMass ℓ d u := by
  set C : ℝ := Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M
  have hCnn : 0 ≤ C := mul_nonneg Submission.BoseGases.chiSupAbs_nonneg
      (Submission.BoseGases.chiSmallDecay_nonneg M)
  -- the pointwise absolute bound on the cutoff
  have hbd : ∀ x : EuclideanSpace ℝ (Fin 3),
      |Submission.BoseGases.chiSmallB M ℓ d u x| ≤ C := by
    intro x
    have h1 : |Submission.BoseGases.chiScale ℓ x| ≤ Submission.BoseGases.chiSupAbs :=
      Submission.BoseGases.chiScale_abs_le_sup ℓ x
    have h2 : |Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u)| ≤
        Submission.BoseGases.chiSmallDecay M :=
      Submission.BoseGases.chiSmall_decay_coord_le_decay hM _
    rw [show Submission.BoseGases.chiSmallB M ℓ d u x
        = Submission.BoseGases.chiScale ℓ x *
          Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u) from rfl, abs_mul]
    exact mul_le_mul h1 h2 (abs_nonneg _) Submission.BoseGases.chiSupAbs_nonneg
  have hboxnn : ∀ x : EuclideanSpace ℝ (Fin 3), 0 ≤ Work.SmallBoxSliding.boxInd ℓ d u x := by
    intro x
    by_cases hx : x ∈ Submission.BoseGases.dlBox ℓ d u
    · rw [Work.SmallBoxSliding.boxInd, Set.indicator_of_mem hx]; norm_num
    · rw [Work.SmallBoxSliding.boxInd, Set.indicator_of_notMem hx]
  -- pointwise domination by `C² · boxInd`
  have hpt : ∀ x : EuclideanSpace ℝ (Fin 3),
      (Submission.BoseGases.chiSmallB M ℓ d u x) ^ 2
        ≤ C ^ 2 * Work.SmallBoxSliding.boxInd ℓ d u x := by
    intro x
    by_cases hx : Submission.BoseGases.chiSmallB M ℓ d u x = 0
    · rw [hx, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
      exact mul_nonneg (sq_nonneg C) (hboxnn x)
    · have hmem : x ∈ Submission.BoseGases.dlBox ℓ d u :=
        Work.SlotWord.chiSmallB_support_mem_dlBox hM hℓ hd hx
      have hbi : Work.SmallBoxSliding.boxInd ℓ d u x = 1 := by
        rw [Work.SmallBoxSliding.boxInd, Set.indicator_of_mem hmem]
      rw [hbi, mul_one]
      calc (Submission.BoseGases.chiSmallB M ℓ d u x) ^ 2
          = |Submission.BoseGases.chiSmallB M ℓ d u x| ^ 2 := (sq_abs _).symm
        _ ≤ C ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hbd x) 2
  -- the indicator is integrable: a measurable set of finite volume
  have hboxint : Integrable (Work.SmallBoxSliding.boxInd ℓ d u) := by
    show Integrable ((Submission.BoseGases.dlBox ℓ d u).indicator (fun _ => (1 : ℝ)))
    rw [MeasureTheory.integrable_indicator_iff
      (Work.SmallBoxSliding.measurableSet_dlBox ℓ d u)]
    refine MeasureTheory.integrableOn_const (C := (1 : ℝ)) ?_ ?_
    · exact (Work.SmallBoxSliding.volume_dlBox_lt_top hℓ d u).ne
    · simp
  have hintg : Integrable (fun x : EuclideanSpace ℝ (Fin 3) =>
      C ^ 2 * Work.SmallBoxSliding.boxInd ℓ d u x) := hboxint.const_mul (C ^ 2)
  rw [Work.SmallBoxSliding.chiMass_def]
  calc (∫ x, (Submission.BoseGases.chiSmallB M ℓ d u x) ^ 2)
      ≤ ∫ x, C ^ 2 * Work.SmallBoxSliding.boxInd ℓ d u x :=
        MeasureTheory.integral_mono_of_nonneg
          (Filter.Eventually.of_forall (fun x => sq_nonneg _)) hintg
          (Filter.Eventually.of_forall hpt)
    _ = C ^ 2 * Work.SmallBoxSliding.boxMass ℓ d u := by
        rw [Work.SmallBoxSliding.boxMass, MeasureTheory.integral_const_mul]

end Work.BoseFixB1S
