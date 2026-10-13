/-
# `|f|²_{ℋ¹} = E_{z,θ}¹(f)` in the interior class `SmoothQuad`

`Work.Coercivity.Eztheta1_eq_HkSq_one` proves `Eztheta1 α f = HkSq α 1 f` from
`HkMem α 1 f` and the (analytic) class `Work.Coercivity.HkSq`… precisely: from
`Spaces.SmoothNbhd f`.  This file re-proves the same identity in the interior class
`Work.FTS.LocData.SmoothQuad`, which is what the coercivity of `Lhat` uses
(`RegQ α 2 f` gives `SmoothQuad f`, `HkMem α 2 f`, `BdryTraces α 2 f`).

The proof is that of `Eztheta1_eq_HkSq_one`:

* the `ℋ¹`-integrand splits pointwise into the three squares `U0² + U1² + U2²`
  (`Work.Coercivity.hkIntegrand_one_split`, an unconditional algebraic identity);
* each of the three is an honest iterated integral (`I2Mem`), by domination with the
  (integrable) `ℋ¹`-integrand; here the *a.e. strong measurability* of the summands comes
  from their continuity on the open quadrant (`SmoothQuad`), in the same way as
  `Work.FTS.LocData.continuousOn_HkIntegrand_smoothQuad`;
* the iterated integral of the sum splits (`Work.Coercivity.iterated_integral_add3`), and
  each `L²Sq` is identified with the corresponding energy (`Work.Coercivity.L2Sq_U0_eq_EfEta`,
  `_U1_eq_EDz`, `_U2_eq_EDth`).
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.CoercivityFix.Coer1.Defs
import Submission.Work.Coercivity.Eztheta1_eq_HkSq_one

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Coer1

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- The open quadrant on which the `ℋ¹`-weights are continuous. -/
abbrev Qd : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)

/-- The piece `u ↦ u · w/sin(2θ)^{η/2}` is continuous on the open quadrant. -/
theorem continuousOn_wdiv : ContinuousOn (fun p : ℝ × ℝ =>
    Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2)) Qd := by
  have hsinpos : ∀ p ∈ Qd, 0 < Real.sin (2 * p.2) :=
    fun p hp =>
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hp.2.1]) (by linarith [hp.2.2, Real.pi_pos])
  have hw : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1) Qd := by
    have hfun : (fun p : ℝ × ℝ => Work.Spaces.w p.1)
        = fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2 := by
      funext p; rfl
    rw [hfun]
    refine ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
      (continuousOn_fst.pow 2) (fun p hp => pow_ne_zero 2 (ne_of_gt hp.1))
  have hsinpow : ContinuousOn (fun p : ℝ × ℝ =>
      (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2)) Qd :=
    ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn)
      |>.rpow_const (fun p hp => Or.inl (ne_of_gt (hsinpos p hp)))
  exact hw.div hsinpow (fun p hp => ne_of_gt (Real.rpow_pos_of_pos (hsinpos p hp) _))

/-- A function `A` whose square is dominated by the `ℋ^k`-integrand and which is continuous on
the open quadrant has an a.e. strongly measurable square. -/
theorem continuousOn_sq_of_cont {A : Fn}
    (hcont : ContinuousOn (fun p : ℝ × ℝ => A p.1 p.2) Qd) :
    ContinuousOn (fun p : ℝ × ℝ => (A p.1 p.2) ^ 2) Qd := hcont.pow 2

/-- The three summands of the `ℋ¹`-integrand are continuous on the open quadrant as soon as
`f` is `C^∞` there.  (The pieces of this proof are those of
`Work.FTS.LocData.continuousOn_HkIntegrand_smoothQuad`.) -/
theorem continuousOn_summands (α : ℝ) {f : Fn} (hsq : Work.FTS.LocData.SmoothQuad f) :
    ContinuousOn (fun p : ℝ × ℝ => (Work.Coercivity.U0 f p.1 p.2) ^ 2) Qd ∧
    ContinuousOn (fun p : ℝ × ℝ => (Work.Coercivity.U1 f p.1 p.2) ^ 2) Qd ∧
    ContinuousOn (fun p : ℝ × ℝ => (Work.Coercivity.U2 α f p.1 p.2) ^ 2) Qd := by
  have hq : ∀ p ∈ Qd, p ∈ Work.Spaces.quadU := by
    intro p hp
    simp only [Qd, Work.Spaces.quadU, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo] at hp ⊢
    exact ⟨by linarith [hp.1], hp.2.1, hp.2.2⟩
  have hsinpos : ∀ p ∈ Qd, 0 < Real.sin (2 * p.2) :=
    fun p hp =>
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hp.2.1]) (by linarith [hp.2.2, Real.pi_pos])
  have hw : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1) Qd := by
    have hfun : (fun p : ℝ × ℝ => Work.Spaces.w p.1)
        = fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2 := by
      funext p; rfl
    rw [hfun]
    refine ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
      (continuousOn_fst.pow 2) (fun p hp => pow_ne_zero 2 (ne_of_gt hp.1))
  have hsinpow : ∀ c : ℝ, ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ c) Qd :=
    fun c => ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn)
      |>.rpow_const (fun p hp => Or.inl (ne_of_gt (hsinpos p hp)))
  have hWt : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2) Qd := by
    have hfun : (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2)
        = fun p : ℝ × ℝ => Work.Spaces.w p.1
            * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2)) := by
      funext p; rfl
    rw [hfun]
    exact hw.mul (hsinpow _)
  have hwdiv : ContinuousOn (fun p : ℝ × ℝ =>
      Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2)) Qd :=
    hw.div (hsinpow _) (fun p hp => ne_of_gt (Real.rpow_pos_of_pos (hsinpos p hp) _))
  have hDzC : ∀ i : ℕ, ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.DzIter i f p.1 p.2) Qd :=
    fun i => ((Work.FTS.LocData.contDiffOn_DzIter (Work.FTS.LocData.isOpen_quadU) hsq i
      ).continuousOn).mono hq
  have hmC : ∀ j i : ℕ, ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.mixed j i f p.1 p.2) Qd :=
    fun j i => ((Work.FTS.LocData.contDiffOn_mixed (Work.FTS.LocData.isOpen_quadU) hsq j i
      ).continuousOn).mono hq
  refine ⟨?_, ?_, ?_⟩
  · have hfun : (fun p : ℝ × ℝ => (Work.Coercivity.U0 f p.1 p.2) ^ 2)
        = fun p : ℝ × ℝ => (Work.Spaces.DzIter 0 f p.1 p.2
            * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
      funext p; rfl
    rw [hfun]
    exact ((hDzC 0).mul hwdiv).pow 2
  · have hfun : (fun p : ℝ × ℝ => (Work.Coercivity.U1 f p.1 p.2) ^ 2)
        = fun p : ℝ × ℝ => (Work.Spaces.DzIter 1 f p.1 p.2
            * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
      funext p; rfl
    rw [hfun]
    exact ((hDzC 1).mul hwdiv).pow 2
  · have hfun : (fun p : ℝ × ℝ => (Work.Coercivity.U2 α f p.1 p.2) ^ 2)
        = fun p : ℝ × ℝ => (Work.Spaces.mixed 0 1 f p.1 p.2 * Work.Spaces.Wt α p.1 p.2) ^ 2 := by
      funext p; rfl
    rw [hfun]
    exact ((hmC 0 1).mul hWt).pow 2

/-- The weighted `D_z`-summand of the `ℋ^k`-integrand is continuous on the open quadrant. -/
theorem continuousOn_Dz_wdiv {f : Fn} (hsq : Work.FTS.LocData.SmoothQuad f) (i : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.DzIter i f p.1 p.2
      * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))) ^ 2) Qd := by
  have hq : ∀ p ∈ Qd, p ∈ Work.Spaces.quadU := by
    intro p hp
    simp only [Qd, Work.Spaces.quadU, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo] at hp ⊢
    exact ⟨by linarith [hp.1], hp.2.1, hp.2.2⟩
  have hDzC : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.DzIter i f p.1 p.2) Qd :=
    ((Work.FTS.LocData.contDiffOn_DzIter (Work.FTS.LocData.isOpen_quadU) hsq i
      ).continuousOn).mono hq
  exact (hDzC.mul continuousOn_wdiv).pow 2

/-- The mixed summand of the `ℋ^k`-integrand is continuous on the open quadrant. -/
theorem continuousOn_mixed_Wt (α : ℝ) {f : Fn} (hsq : Work.FTS.LocData.SmoothQuad f)
    (j i : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ =>
      (Work.Spaces.mixed j i f p.1 p.2 * Work.Spaces.Wt α p.1 p.2) ^ 2) Qd := by
  have hq : ∀ p ∈ Qd, p ∈ Work.Spaces.quadU := by
    intro p hp
    simp only [Qd, Work.Spaces.quadU, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo] at hp ⊢
    exact ⟨by linarith [hp.1], hp.2.1, hp.2.2⟩
  have hsinpos : ∀ p ∈ Qd, 0 < Real.sin (2 * p.2) :=
    fun p hp =>
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hp.2.1]) (by linarith [hp.2.2, Real.pi_pos])
  have hw : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1) Qd := by
    have hfun : (fun p : ℝ × ℝ => Work.Spaces.w p.1)
        = fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2 := by
      funext p; rfl
    rw [hfun]
    refine ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
      (continuousOn_fst.pow 2) (fun p hp => pow_ne_zero 2 (ne_of_gt hp.1))
  have hsinpow : ContinuousOn (fun p : ℝ × ℝ =>
      (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2))) Qd :=
    ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn)
      |>.rpow_const (fun p hp => Or.inl (ne_of_gt (hsinpos p hp)))
  have hWt : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2) Qd := by
    have hfun : (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2)
        = fun p : ℝ × ℝ => Work.Spaces.w p.1
            * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2)) := by
      funext p; rfl
    rw [hfun]
    exact hw.mul hsinpow
  have hmC : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.mixed j i f p.1 p.2) Qd :=
    ((Work.FTS.LocData.contDiffOn_mixed (Work.FTS.LocData.isOpen_quadU) hsq j i).continuousOn
      ).mono hq
  exact (hmC.mul hWt).pow 2

/-- Domination of a square of a continuous function by the `ℋ^k`-integrand gives the honesty
of its iterated integral. -/
theorem i2Mem_sq_of_le (α : ℝ) (k : ℕ) {f A : Fn} (hm : Work.Spaces.HkMem α k f)
    (hcont : ContinuousOn (fun p : ℝ × ℝ => (A p.1 p.2) ^ 2) Qd)
    (hle : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      (A z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α k f z θ) :
    Work.Coercivity.I2Mem (fun z θ => (A z θ) ^ 2) := by
  constructor
  · intro z hz
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hz0
    · subst h0
      refine MeasureTheory.IntegrableOn.congr_fun integrableOn_zero (fun θ hθ => ?_)
        measurableSet_Icc
      have h1 := hle 0 (le_refl (0 : ℝ)) θ hθ
      rw [Work.Spaces.HkIntegrand_zero_z] at h1
      exact (le_antisymm h1 (sq_nonneg _)).symm
    · have hsl : ContinuousOn (fun θ : ℝ => (A z θ) ^ 2) (Set.Ioo 0 (π / 2)) :=
        hcont.comp (continuous_const.prodMk continuous_id).continuousOn
          (fun θ hθ => ⟨hz0, hθ⟩)
      have haesm : MeasureTheory.AEStronglyMeasurable (fun θ : ℝ => (A z θ) ^ 2)
          (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
        have h1 : MeasureTheory.AEStronglyMeasurable (fun θ : ℝ => (A z θ) ^ 2)
            (MeasureTheory.volume.restrict (Set.Ioo 0 (π / 2))) :=
          hsl.aestronglyMeasurable measurableSet_Ioo
        have hset : MeasureTheory.volume.restrict Work.Spaces.Iθ
            = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) :=
          (MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc).symm
        rwa [hset]
      refine MeasureTheory.Integrable.mono' (hm.1 z hz) haesm ?_
      filter_upwards [MeasureTheory.ae_restrict_mem
        (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)] with θ hθ
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact hle z hz θ hθ
  · have hjoint : MeasureTheory.AEStronglyMeasurable
        (fun p : ℝ × ℝ => (A p.1 p.2) ^ 2)
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
      Work.Spaces.aesm_of_continuousOn_Qd _ hcont
    refine MeasureTheory.Integrable.mono' hm.2 hjoint.integral_prod_right' ?_
    filter_upwards [MeasureTheory.ae_restrict_mem
      (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici)] with z hz
    rw [Real.norm_of_nonneg (integral_nonneg fun θ => sq_nonneg _)]
    exact integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun θ => sq_nonneg _)
      (hm.1 z hz)
      (MeasureTheory.ae_restrict_of_forall_mem
        (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc) fun θ hθ => hle z hz θ hθ)

/-- **`|f|²_{ℋ¹} = E_{z,θ}¹(f)` in the interior class**: the `ℋ¹`-energy of the paper,
`E_{z,θ}¹(f) = EDz f + EfEta f + EDth α f`, is the squared `ℋ¹`-norm of `f`. -/
theorem HkSq_one_eq (α : ℝ) {f : Fn} (hsq : Work.FTS.LocData.SmoothQuad f)
    (hm : Work.Spaces.HkMem α 1 f) :
    Work.Spaces.HkSq α 1 f
      = Work.Coercivity.EDz f + Work.Coercivity.EfEta f + Work.Coercivity.EDth α f := by
  obtain ⟨hU0c, hU1c, hU2c⟩ := continuousOn_summands α hsq
  have hL0 : Work.Coercivity.I2Mem (fun z θ => (Work.Coercivity.U0 f z θ) ^ 2) :=
    i2Mem_sq_of_le α 1 hm hU0c
      (fun z _ θ _ => Work.Spaces.sq_le_HkIntegrand_z α 1 f z θ 0 (by norm_num))
  have hL1 : Work.Coercivity.I2Mem (fun z θ => (Work.Coercivity.U1 f z θ) ^ 2) :=
    i2Mem_sq_of_le α 1 hm hU1c
      (fun z _ θ _ => Work.Spaces.sq_le_HkIntegrand_z α 1 f z θ 1 (by norm_num))
  have hL2 : Work.Coercivity.I2Mem (fun z θ => (Work.Coercivity.U2 α f z θ) ^ 2) :=
    i2Mem_sq_of_le α 1 hm hU2c
      (fun z _ θ _ => Work.Spaces.sq_le_HkIntegrand_mixed α 1 f z θ 1 0 (by norm_num)
        (by norm_num))
  have hsplit : Work.Spaces.HkSq α 1 f
      = Work.Spaces.L2Sq (Work.Coercivity.U0 f) + Work.Spaces.L2Sq (Work.Coercivity.U1 f)
        + Work.Spaces.L2Sq (Work.Coercivity.U2 α f) := by
    rw [Work.Spaces.HkSq]
    have h1 : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 f z θ)
        = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
            ((Work.Coercivity.U0 f z θ) ^ 2 + (Work.Coercivity.U1 f z θ) ^ 2
              + (Work.Coercivity.U2 α f z θ) ^ 2) := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici fun z _ => ?_
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun θ _ => ?_
      exact Work.Coercivity.hkIntegrand_one_split α f z θ
    rw [h1]
    have hadd := Work.Coercivity.iterated_integral_add3
      (A := fun z θ => (Work.Coercivity.U0 f z θ) ^ 2)
      (B := fun z θ => (Work.Coercivity.U1 f z θ) ^ 2)
      (C := fun z θ => (Work.Coercivity.U2 α f z θ) ^ 2) hL0 hL1 hL2
    rw [hadd]
    simp only [Work.Spaces.L2Sq]
  rw [hsplit, Work.Coercivity.L2Sq_U0_eq_EfEta, Work.Coercivity.L2Sq_U1_eq_EDz,
    Work.Coercivity.L2Sq_U2_eq_EDth]
  ring

end Work.FTS.CoercivityFix.Coer1
