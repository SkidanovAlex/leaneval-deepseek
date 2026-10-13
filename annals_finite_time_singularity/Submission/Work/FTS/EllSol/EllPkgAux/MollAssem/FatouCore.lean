/-
# `Work.FTS.EllSol.EllPkgAux.MollAssem.FatouCore` — the Fatou core of the assembly

`mollFatouCore` is the Fatou (lower-semicontinuity) argument relating `∫_Iz mixIntS G` to the
values `∫_Iz mixIntS (zmoll G δ ε)` of the doubly-mollified approximants, with the *slice
honesty* of the diagonal approximants supplied as an explicit hypothesis (it is derived from
`StripAdm` in the assembly file).

The two Fatou steps (in `θ` at fixed `z > 0`, then in `z`) are performed with
`MollAssem.fatou_lintegral_le_liminf`; the `IntegrableOn` hypotheses of the statement convert
the Bochner integrals into the corresponding `lintegral`s at the two ends.

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.Interval.Basic
import Submission.Work.FTS.EllSol.EllPkgAux.MollAssem.Defs
import Submission.Work.FTS.EllSol.EllPkgAux.MollBase
import Submission.Work.FTS.EllSol.EllPkgAux.MollFatouAux
import Submission.Work.EllipticEst.Core.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.EllPkgAux

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace MollAssem

/-! ## The Fatou assembly -/

/-- The Fatou assembly, with the slice honesty of the diagonal approximants as an explicit
hypothesis. -/
theorem mollFatouCore (G : ℝ → ℝ → ℝ) (hT : TraceClass G) (hF : FourInts G)
    (hint : ∀ δ ε : ℝ, Params δ ε → MeasureTheory.IntegrableOn
      (fun z : ℝ => Work.EllipticEst.Core.mixIntS (Work.FTS.EllSol.PkgK5.K5c.zmoll G δ ε) z)
      Work.Spaces.Iz)
    (hconv : ∀ z : ℝ, 0 < z → ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      Filter.Tendsto (fun n : ℕ => (Work.Spaces.Dz (Work.Spaces.pth
        (Work.FTS.EllSol.PkgK5.K5c.zmoll G (tseq n) (tseq n))) z θ) ^ 2
          * Work.FTS.EllipticEst.thEta θ) Filter.atTop
        (nhds ((Work.Spaces.Dz (Work.Spaces.pth G) z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)))
    (hhon : ∀ (n : ℕ) (z : ℝ), 0 < z → MeasureTheory.AEStronglyMeasurable
      (fun θ : ℝ => (Work.Spaces.Dz (Work.Spaces.pth
        (Work.FTS.EllSol.PkgK5.K5c.zmoll G (tseq n) (tseq n))) z θ) ^ 2
          * Work.FTS.EllipticEst.thEta θ) (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hhonest : ∀ (n : ℕ) (z : ℝ), 0 < z → MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Work.Spaces.Dz (Work.Spaces.pth
        (Work.FTS.EllSol.PkgK5.K5c.zmoll G (tseq n) (tseq n))) z θ) ^ 2
          * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ) :
    ∀ η : ℝ, 0 < η → ∃ δ ε : ℝ, Params δ ε ∧
      (∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.mixIntS G z)
        ≤ (∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.mixIntS
            (Work.FTS.EllSol.PkgK5.K5c.zmoll G δ ε) z) + η := by
  intro η hη
  -- Step 1: for every `z > 0`, Fatou in `θ` compares the angular slices.
  have key1 : ∀ z : ℝ, 0 < z → ENNReal.ofReal (Work.EllipticEst.Core.mixIntS G z)
      ≤ Filter.liminf (fun n : ℕ => ENNReal.ofReal (Work.EllipticEst.Core.mixIntS
          (Work.FTS.EllSol.PkgK5.K5c.zmoll G (tseq n) (tseq n)) z)) Filter.atTop := by
    intro z hz
    set c : ℝ := (Work.Spaces.w z) ^ 2 with hc
    set u : ℝ → ℝ := fun θ => (Work.Spaces.Dz (Work.Spaces.pth G) z θ) ^ 2
      * Work.FTS.EllipticEst.thEta θ with hu
    set un : ℕ → ℝ → ℝ := fun n θ => (Work.Spaces.Dz (Work.Spaces.pth
      (Work.FTS.EllSol.PkgK5.K5c.zmoll G (tseq n) (tseq n))) z θ) ^ 2
        * Work.FTS.EllipticEst.thEta θ with hun
    have hun' : ∀ n θ, un n θ = (Work.Spaces.Dz (Work.Spaces.pth
        (Work.FTS.EllSol.PkgK5.K5c.zmoll G (tseq n) (tseq n))) z θ) ^ 2
          * Work.FTS.EllipticEst.thEta θ := fun n θ => rfl
    have hcnn : 0 ≤ c := by rw [hc]; exact sq_nonneg _
    have hunn : ∀ n, 0 ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ] un n := by
      intro n
      refine ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
      rw [hun' n θ]
      exact mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hθ)
    have hunn' : 0 ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ] u := by
      refine ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
      exact mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hθ)
    have hFatouθ : (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (c * u θ))
        ≤ Filter.liminf (fun n : ℕ => ∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal (c * un n θ)) Filter.atTop := by
      refine fatou_lintegral_le_liminf
        (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
        (G := fun n θ => c * un n θ) (f := fun θ => c * u θ) ?_ ?_
      · intro n
        exact aemeasurable_ofReal_of_aestronglyMeasurable
          ((hhon n z hz).const_mul c)
      · filter_upwards [hconv z hz] with θ hθ
        exact le_of_eq (ENNReal.tendsto_ofReal (hθ.const_mul c)).liminf_eq.symm
    -- The left-hand end: the honest `θ`-integral is below the `θ`-lower integral.
    have hLHS : ENNReal.ofReal (c * (∫ θ in Work.Spaces.Iθ, u θ))
        ≤ ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (c * u θ) := by
      by_cases hintg : Integrable u (MeasureTheory.volume.restrict Work.Spaces.Iθ)
      · rw [ENNReal.ofReal_mul hcnn,
          MeasureTheory.ofReal_integral_eq_lintegral_ofReal hintg hunn']
        rw [show (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (c * u θ))
            = ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal c * ENNReal.ofReal (u θ) from
          lintegral_congr (fun θ => ENNReal.ofReal_mul hcnn)]
        exact le_of_eq (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
      · rw [MeasureTheory.integral_undef hintg, mul_zero, ENNReal.ofReal_zero]
        exact zero_le
    -- The right-hand end: honesty of the approximant's `θ`-slices.
    have hRHS : ∀ n : ℕ, (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (c * un n θ))
        = ENNReal.ofReal (c * (∫ θ in Work.Spaces.Iθ, un n θ)) := by
      intro n
      have hintn : Integrable (un n) (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
        hhonest n z hz
      rw [show (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (c * un n θ))
            = ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal c * ENNReal.ofReal (un n θ) from
          lintegral_congr (fun θ => ENNReal.ofReal_mul hcnn),
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hintn (hunn n)]
      exact (ENNReal.ofReal_mul hcnn).symm
    have hlim_eq : Filter.liminf (fun n : ℕ => ENNReal.ofReal (Work.EllipticEst.Core.mixIntS
          (Work.FTS.EllSol.PkgK5.K5c.zmoll G (tseq n) (tseq n)) z)) Filter.atTop
        = Filter.liminf (fun n : ℕ => ENNReal.ofReal
            (c * (∫ θ in Work.Spaces.Iθ, un n θ))) Filter.atTop :=
      Filter.liminf_congr (Filter.Eventually.of_forall (fun n => by
        rw [show Work.EllipticEst.Core.mixIntS
            (Work.FTS.EllSol.PkgK5.K5c.zmoll G (tseq n) (tseq n)) z
            = c * (∫ θ in Work.Spaces.Iθ, un n θ) from rfl]))
    have hMG : Work.EllipticEst.Core.mixIntS G z = c * (∫ θ in Work.Spaces.Iθ, u θ) := rfl
    rw [hMG, hlim_eq]
    exact hLHS.trans (hFatouθ.trans (le_of_eq (Filter.liminf_congr
      (Filter.Eventually.of_forall hRHS))))
  -- Step 2: the pointwise bound holds a.e. on `Iz` (only `z = 0` is not covered).
  have key2 : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      ENNReal.ofReal (Work.EllipticEst.Core.mixIntS G z)
        ≤ Filter.liminf (fun n : ℕ => ENNReal.ofReal (Work.EllipticEst.Core.mixIntS
            (Work.FTS.EllSol.PkgK5.K5c.zmoll G (tseq n) (tseq n)) z)) Filter.atTop := by
    rw [MeasureTheory.ae_restrict_iff' (s := Work.Spaces.Iz) measurableSet_Ici]
    refine Filter.Eventually.of_forall (fun z hz => ?_)
    by_cases hz0 : 0 < z
    · exact key1 z hz0
    · have hz_eq : z = 0 := le_antisymm (not_lt.mp hz0) hz
      subst hz_eq
      rw [show Work.EllipticEst.Core.mixIntS G 0 = 0 from ?_]
      · rw [ENNReal.ofReal_zero]; exact zero_le
      · rw [Work.EllipticEst.Core.mixIntS]
        have hw0 : Work.Spaces.w (0 : ℝ) = 0 := by rw [Work.Spaces.w]; norm_num
        rw [hw0]
        ring
  -- Step 3: Fatou in `z`.
  have hzmeas : ∀ n : ℕ, AEMeasurable (fun z : ℝ => ENNReal.ofReal
      (Work.EllipticEst.Core.mixIntS (Work.FTS.EllSol.PkgK5.K5c.zmoll G
        (tseq n) (tseq n)) z)) (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    fun n => aemeasurable_ofReal_of_aestronglyMeasurable
      ((hint _ _ (params_tseq n)).integrable).aestronglyMeasurable
  have hzFatou := fatou_lintegral_le_liminf
    (μ := MeasureTheory.volume.restrict Work.Spaces.Iz) hzmeas key2
  have hLconvert : (∫⁻ z, ENNReal.ofReal (Work.EllipticEst.Core.mixIntS G z)
        ∂(MeasureTheory.volume.restrict Work.Spaces.Iz))
      = ENNReal.ofReal (∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.mixIntS G z) :=
    (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hF.1
      (ae_of_all _ (fun z => mixIntS_nonneg_mfa G z))).symm
  have hRconvert : ∀ n : ℕ, (∫⁻ z, ENNReal.ofReal (Work.EllipticEst.Core.mixIntS
        (Work.FTS.EllSol.PkgK5.K5c.zmoll G (tseq n) (tseq n)) z)
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iz))
      = ENNReal.ofReal (∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.mixIntS
          (Work.FTS.EllSol.PkgK5.K5c.zmoll G (tseq n) (tseq n)) z) := by
    intro n
    exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal
      ((hint _ _ (params_tseq n)).integrable)
      (ae_of_all _ (fun z => mixIntS_nonneg_mfa _ z))).symm
  have key3 : ENNReal.ofReal (∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.mixIntS G z)
      ≤ Filter.liminf (fun n : ℕ => ENNReal.ofReal (∫ z in Work.Spaces.Iz,
          Work.EllipticEst.Core.mixIntS (Work.FTS.EllSol.PkgK5.K5c.zmoll G
            (tseq n) (tseq n)) z)) Filter.atTop := by
    rw [← hLconvert, ← Filter.liminf_congr (Filter.Eventually.of_forall hRconvert)]
    exact hzFatou
  -- Step 4: extract a single index `n`.
  by_cases hsmall : (∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.mixIntS G z) ≤ η
  · refine ⟨tseq 0, tseq 0, params_tseq 0, ?_⟩
    have hb0 : 0 ≤ ∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.mixIntS
        (Work.FTS.EllSol.PkgK5.K5c.zmoll G (tseq 0) (tseq 0)) z :=
      MeasureTheory.integral_nonneg_of_ae (ae_of_all _ (fun z => mixIntS_nonneg_mfa _ z))
    linarith
  · have hsmall' : η < (∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.mixIntS G z) :=
      not_le.mp hsmall
    by_contra hcon
    have hb : ∀ n : ℕ, (∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.mixIntS
          (Work.FTS.EllSol.PkgK5.K5c.zmoll G (tseq n) (tseq n)) z)
        ≤ (∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.mixIntS G z) - η := by
      intro n
      have h : ¬ ((∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.mixIntS G z)
          ≤ (∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.mixIntS
              (Work.FTS.EllSol.PkgK5.K5c.zmoll G (tseq n) (tseq n)) z) + η) :=
        fun hh => hcon ⟨tseq n, tseq n, params_tseq n, hh⟩
      linarith [not_le.mp h]
    have hlimle : Filter.liminf (fun n : ℕ => ENNReal.ofReal (∫ z in Work.Spaces.Iz,
          Work.EllipticEst.Core.mixIntS (Work.FTS.EllSol.PkgK5.K5c.zmoll G
            (tseq n) (tseq n)) z)) Filter.atTop
        ≤ ENNReal.ofReal ((∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.mixIntS G z) - η) :=
      Filter.liminf_le_of_frequently_le' (Filter.Frequently.of_forall
        (fun n => ENNReal.ofReal_le_ofReal (hb n)))
    have hfinal := key3.trans hlimle
    have hpos : 0 ≤ (∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.mixIntS G z) - η := by
      linarith
    have hfin := (ENNReal.ofReal_le_ofReal_iff hpos).mp hfinal
    linarith

end MollAssem

end Work.FTS.EllSol.EllPkgAux
