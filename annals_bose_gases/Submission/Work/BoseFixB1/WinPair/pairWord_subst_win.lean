import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.BoseFixB1.WinPair.WinChiFacts
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.WinPair.pairWord_subst_win` — the relative-coordinate substitution for a
general window

    ∫_{acube s}∫_{acube s} χ_B(y)W(y−z)χ_B(z)Q(y,z)
      = ∫_u W(u)·(∫_z χ_B(z+u)χ_B(z)Q(z+u,z)) ,   χ_B = winChi s χ .

This is the general-window form of the corpus's `Submission.BoseGases.pairWord_subst`
(`Submission/Work/SmallBoxPairRelDecomp.lean`, proved there for the single window `chiScale ℓ`).
The only property of the window used is that it vanishes off the box (`winChi_support`), which
holding for every `χ` (with no positivity assumption on `s`) is exactly why `winChi` was
introduced; the rest is translation invariance, the pointwise extension of a set integral, and
one Fubini whose integrability is the hypothesis `hInt`.
-/

noncomputable section

open MeasureTheory Metric
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1.WinPair

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

theorem pairWord_subst_win {s : ℝ} {χ : EuclideanSpace ℝ (Fin 3) → ℝ}
    {W : EuclideanSpace ℝ (Fin 3) → ℝ}
    {Q : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ}
    (hInt : MeasureTheory.Integrable (Function.uncurry (fun y u : EuclideanSpace ℝ (Fin 3) =>
      Work.BoseFixB1.winChi s χ y * W u * Work.BoseFixB1.winChi s χ (y - u) * Q y (y - u)))
      (MeasureTheory.volume.prod MeasureTheory.volume)) :
    (∫ y in Submission.BoseGases.acube s, ∫ z in Submission.BoseGases.acube s,
        Work.BoseFixB1.winChi s χ y * W (y - z) * Work.BoseFixB1.winChi s χ z * Q y z)
      = ∫ u, W u * (∫ z, Work.BoseFixB1.winChi s χ (z + u) * Work.BoseFixB1.winChi s χ z
          * Q (z + u) z) := by
  have hzero : ∀ z : E3, z ∉ Submission.BoseGases.acube s → Work.BoseFixB1.winChi s χ z = 0 := by
    intro z hz
    by_contra hne
    exact hz (Work.BoseFixB1.winChi_support hne)
  have hb : ∀ y : E3,
      (∫ z in Submission.BoseGases.acube s,
          Work.BoseFixB1.winChi s χ y * W (y - z) * Work.BoseFixB1.winChi s χ z * Q y z)
        = ∫ z, Work.BoseFixB1.winChi s χ y * W (y - z) * Work.BoseFixB1.winChi s χ z * Q y z := by
    intro y
    refine setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => ?_)
    rw [hzero z hz]
    ring
  have hc : ∀ y : E3,
      (∫ z, Work.BoseFixB1.winChi s χ y * W (y - z) * Work.BoseFixB1.winChi s χ z * Q y z)
        = ∫ u, Work.BoseFixB1.winChi s χ y * W u * Work.BoseFixB1.winChi s χ (y - u)
            * Q y (y - u) := by
    intro y
    refine (integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)).trans
      (integral_sub_left_eq_self
        (fun w : E3 => Work.BoseFixB1.winChi s χ y * W w
          * Work.BoseFixB1.winChi s χ (y - w) * Q y (y - w)) volume y)
    simp only [show y - (y - z) = z from by abel]
  have hd : ∀ y : E3,
      (∫ u, Work.BoseFixB1.winChi s χ y * W u * Work.BoseFixB1.winChi s χ (y - u)
          * Q y (y - u))
        = Work.BoseFixB1.winChi s χ y
            * ∫ u, W u * Work.BoseFixB1.winChi s χ (y - u) * Q y (y - u) := by
    intro y
    rw [show (∫ u, Work.BoseFixB1.winChi s χ y * W u * Work.BoseFixB1.winChi s χ (y - u)
          * Q y (y - u))
        = ∫ u, Work.BoseFixB1.winChi s χ y
            * (W u * Work.BoseFixB1.winChi s χ (y - u) * Q y (y - u)) from by
      apply integral_congr_ae
      filter_upwards with u
      ring]
    rw [MeasureTheory.integral_const_mul]
  have he : (∫ y in Submission.BoseGases.acube s, Work.BoseFixB1.winChi s χ y
        * ∫ u, W u * Work.BoseFixB1.winChi s χ (y - u) * Q y (y - u))
      = ∫ y, Work.BoseFixB1.winChi s χ y
          * ∫ u, W u * Work.BoseFixB1.winChi s χ (y - u) * Q y (y - u) := by
    refine setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => ?_)
    rw [hzero y hy, zero_mul]
  have hf : (∫ y, Work.BoseFixB1.winChi s χ y
        * ∫ u, W u * Work.BoseFixB1.winChi s χ (y - u) * Q y (y - u))
      = ∫ y, ∫ u, Work.BoseFixB1.winChi s χ y * W u * Work.BoseFixB1.winChi s χ (y - u)
          * Q y (y - u) := by
    apply integral_congr_ae
    filter_upwards with y
    rw [show (∫ u, Work.BoseFixB1.winChi s χ y * W u * Work.BoseFixB1.winChi s χ (y - u)
          * Q y (y - u))
        = ∫ u, Work.BoseFixB1.winChi s χ y
            * (W u * Work.BoseFixB1.winChi s χ (y - u) * Q y (y - u)) from by
      apply integral_congr_ae
      filter_upwards with u
      ring]
    rw [MeasureTheory.integral_const_mul]
  have hg : (∫ y, ∫ u, Work.BoseFixB1.winChi s χ y * W u * Work.BoseFixB1.winChi s χ (y - u)
          * Q y (y - u))
      = ∫ u, ∫ y, Work.BoseFixB1.winChi s χ y * W u * Work.BoseFixB1.winChi s χ (y - u)
          * Q y (y - u) :=
    integral_integral_swap (f := fun y u : E3 =>
      Work.BoseFixB1.winChi s χ y * W u * Work.BoseFixB1.winChi s χ (y - u) * Q y (y - u)) hInt
  have hh : (∫ u, ∫ y, Work.BoseFixB1.winChi s χ y * W u * Work.BoseFixB1.winChi s χ (y - u)
          * Q y (y - u))
      = ∫ u, W u * ∫ z, Work.BoseFixB1.winChi s χ (z + u) * Work.BoseFixB1.winChi s χ z
          * Q (z + u) z := by
    apply integral_congr_ae
    filter_upwards with u
    rw [show (∫ y, Work.BoseFixB1.winChi s χ y * W u * Work.BoseFixB1.winChi s χ (y - u)
          * Q y (y - u))
        = ∫ y, W u * (Work.BoseFixB1.winChi s χ y * Work.BoseFixB1.winChi s χ (y - u)
            * Q y (y - u)) from by
      apply integral_congr_ae
      filter_upwards with y
      ring]
    rw [MeasureTheory.integral_const_mul]
    congr 1
    -- translation: `y = z + u`
    have hshift := MeasureTheory.integral_add_left_eq_self (μ := (volume : Measure E3))
      (fun w : E3 => Work.BoseFixB1.winChi s χ w * Work.BoseFixB1.winChi s χ (w - u)
        * Q w (w - u)) u
    have h1 : (∫ z, Work.BoseFixB1.winChi s χ (u + z) * Work.BoseFixB1.winChi s χ (u + z - u)
          * Q (u + z) (u + z - u))
        = ∫ z, Work.BoseFixB1.winChi s χ z * Work.BoseFixB1.winChi s χ (z - u) * Q z (z - u) :=
      hshift
    have h2 : (∫ z, Work.BoseFixB1.winChi s χ (u + z) * Work.BoseFixB1.winChi s χ (u + z - u)
          * Q (u + z) (u + z - u))
        = ∫ z, Work.BoseFixB1.winChi s χ (z + u) * Work.BoseFixB1.winChi s χ z * Q (z + u) z := by
      apply integral_congr_ae
      filter_upwards with z
      rw [show u + z = z + u from by abel]
      rw [show z + u - u = z from by abel]
    rw [← h2, h1]
  calc (∫ y in Submission.BoseGases.acube s, ∫ z in Submission.BoseGases.acube s,
          Work.BoseFixB1.winChi s χ y * W (y - z) * Work.BoseFixB1.winChi s χ z * Q y z)
      = ∫ y in Submission.BoseGases.acube s,
          ∫ z, Work.BoseFixB1.winChi s χ y * W (y - z) * Work.BoseFixB1.winChi s χ z * Q y z :=
        integral_congr_ae (Filter.Eventually.of_forall hb)
    _ = ∫ y in Submission.BoseGases.acube s, Work.BoseFixB1.winChi s χ y
          * ∫ u, W u * Work.BoseFixB1.winChi s χ (y - u) * Q y (y - u) :=
        integral_congr_ae (Filter.Eventually.of_forall (fun y => (hc y).trans (hd y)))
    _ = ∫ y, Work.BoseFixB1.winChi s χ y
          * ∫ u, W u * Work.BoseFixB1.winChi s χ (y - u) * Q y (y - u) := he
    _ = ∫ y, ∫ u, Work.BoseFixB1.winChi s χ y * W u * Work.BoseFixB1.winChi s χ (y - u)
          * Q y (y - u) := hf
    _ = ∫ u, ∫ y, Work.BoseFixB1.winChi s χ y * W u * Work.BoseFixB1.winChi s χ (y - u)
          * Q y (y - u) := hg
    _ = ∫ u, W u * ∫ z, Work.BoseFixB1.winChi s χ (z + u) * Work.BoseFixB1.winChi s χ z
          * Q (z + u) z := hh

end Work.BoseFixB1.WinPair
