import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Coercivity.Defs
import Submission.Work.Coercivity.Basic
import Submission.Work.Coercivity.H1IPAddDefs
import Submission.Work.Coercivity.EzDefs
import Submission.Work.Coercivity.I2Mem_mul_of_ae
import Submission.Work.Coercivity.wip_add_of_PairHonest
import Submission.Work.Coercivity.H1IP_homog
import Submission.Work.Coercivity.H1IP_nonneg
import Submission.Work.Coercivity.Xeta_mul_eq
import Submission.Work.Coercivity.XetaDz_mul_eq
import Submission.Work.Coercivity.XgamDth_mul_eq
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.Spaces.aesm_slice_of_continuousOn_Qd
import Submission.Work.FTS.LocData.SmoothChain
import Submission.Work.FTS.CoercivityFix.StepAssembly.H1IP_congr_qd

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `H1IP_core_Q`: the four algebraic clauses of the `ℋ¹` inner product on `RegQ α 1`

The inner product

  `H1IP α f g = 10·(D_zf,D_zg)_{w²/sin^η} + 10¹⁰·(f,g)_{w²/sin^η} + 10¹⁷·(f,g)_{w²}
                 + 10²¹·(D_θf,D_θg)_{w²/sin^γ}`

is a sum of four weight pairings `wip ρ A B = ∫_z ∫_θ A·B·ρ`.  The Bochner integral is
total, so `wip` is not additive for *arbitrary* profiles (the junk value `0` of a
non-integrable integrand destroys the identity — `Work.Coercivity.H1IP_add_fails`); but for
profiles of the class `RegQ α 1` (genuine `C^∞` on the open quadrant, `HkMem α 1`, and the
integration-by-parts boundary traces) every pairing integrand is *honest*, because it is
dominated by the (integrable) `ℋ¹`-integrand of the two arguments and is a.e. strongly
measurable (continuity on the open quadrant).  Hence:

* `H1IP` is additive and homogeneous in its first argument on `RegQ α 1` (the four
  `PairHonest` lemmas below, followed by `H1IP_add_Q`);
* `H1IP` is symmetric for **all** profiles (`H1IP_comm`: the integrands are literally equal
  pointwise, so no honesty is needed);
* the diagonal is nonnegative for **all** profiles (`H1IP_nonneg`).

This is the `RegQ` (interior, non-analytic) replacement of the analytic-class additivity
proved in `Work.Coercivity.H1IP_isHkIP`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Assembly

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## Symmetry of `wip` and of `H1IP` -/

theorem wip_comm (ρ A B : ℝ → ℝ → ℝ) :
    Work.Coercivity.wip ρ A B = Work.Coercivity.wip ρ B A := by
  simp only [Work.Coercivity.wip]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun z _ => ?_)
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
  ring

theorem H1IP_comm (α : ℝ) (f g : ℝ → ℝ → ℝ) :
    Work.Coercivity.H1IP α f g = Work.Coercivity.H1IP α g f := by
  simp only [Work.Coercivity.H1IP, wip_comm]

/-! ## The open quadrant, and continuity of the blocks -/

/-- The open quadrant `(0,∞) × (0,π/2)`, definitionally `Work.Construction.Qd`. -/
abbrev Qo : Set (ℝ × ℝ) := Work.Construction.Qd

theorem Qo_subset_quadU : Qo ⊆ Work.Spaces.quadU :=
  Set.prod_mono (Set.Ioi_subset_Ioi (by norm_num : (-1 : ℝ) ≤ 0)) subset_rfl

theorem continuousOn_w_Qo : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1) Qo := by
  have hfun : (fun p : ℝ × ℝ => Work.Spaces.w p.1)
      = fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2 := by
    funext p; rfl
  rw [hfun]
  exact ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
    (continuousOn_fst.pow 2) (fun p hp => pow_ne_zero 2 (ne_of_gt (Set.mem_Ioi.mp hp.1)))

theorem continuousOn_sinpow_Qo (c : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ c) Qo := by
  have hsin : Continuous (fun p : ℝ × ℝ => Real.sin (2 * p.2)) :=
    Real.continuous_sin.comp (continuous_const.mul continuous_snd)
  refine hsin.continuousOn.rpow_const ?_
  intro p hp
  have h1 : 0 < p.2 := (Set.mem_Ioo.mp hp.2).1
  have h2 : p.2 < π / 2 := (Set.mem_Ioo.mp hp.2).2
  exact Or.inl (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])))

theorem continuousOn_lamEta : ContinuousOn (Function.uncurry Work.Coercivity.lamEta) Qo := by
  have hfun : Function.uncurry Work.Coercivity.lamEta
      = fun p : ℝ × ℝ =>
          Work.Spaces.w p.1 ^ 2 * (Real.sin (2 * p.2)) ^ (-Work.Spaces.eta) := by
    funext p; rcases p with ⟨z, θ⟩; rfl
  rw [hfun]
  exact (continuousOn_w_Qo.pow 2).mul (continuousOn_sinpow_Qo _)

theorem continuousOn_lamGam (α : ℝ) :
    ContinuousOn (Function.uncurry (Work.Coercivity.lamGam α)) Qo := by
  have hfun : Function.uncurry (Work.Coercivity.lamGam α)
      = fun p : ℝ × ℝ =>
          Work.Spaces.w p.1 ^ 2 * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α)) := by
    funext p; rcases p with ⟨z, θ⟩; rfl
  rw [hfun]
  exact (continuousOn_w_Qo.pow 2).mul (continuousOn_sinpow_Qo _)

theorem continuousOn_lamW : ContinuousOn (Function.uncurry Work.Coercivity.lamW) Qo := by
  have hfun : Function.uncurry Work.Coercivity.lamW = fun p : ℝ × ℝ => Work.Spaces.w p.1 ^ 2 := by
    funext p; rcases p with ⟨z, θ⟩; rfl
  rw [hfun]
  exact continuousOn_w_Qo.pow 2

theorem continuousOn_smoothQuad {f : ℝ → ℝ → ℝ} (h : Work.FTS.LocData.SmoothQuad f) :
    ContinuousOn (Function.uncurry f) Qo :=
  h.continuousOn.mono Qo_subset_quadU

theorem continuousOn_Dz_smoothQuad {f : ℝ → ℝ → ℝ} (h : Work.FTS.LocData.SmoothQuad f) :
    ContinuousOn (Function.uncurry (Work.Spaces.Dz f)) Qo :=
  ((Work.FTS.LocData.contDiffOn_Dz Work.Spaces.isOpen_quadU h).continuousOn).mono Qo_subset_quadU

theorem continuousOn_Dth_smoothQuad {f : ℝ → ℝ → ℝ} (h : Work.FTS.LocData.SmoothQuad f) :
    ContinuousOn (Function.uncurry (Work.Spaces.Dth f)) Qo :=
  ((Work.FTS.LocData.contDiffOn_Dth Work.Spaces.isOpen_quadU h).continuousOn).mono Qo_subset_quadU

/-! ## Domination of the pairing integrands by the `ℋ¹`-integrand -/

/-- The elementary AM–GM bound `|a|·|b| ≤ (a² + b²)/2`. -/
theorem abs_mul_abs_le_half (a b : ℝ) : |a| * |b| ≤ (a ^ 2 + b ^ 2) / 2 := by
  have h := two_mul_le_add_sq |a| |b|
  rw [sq_abs, sq_abs] at h
  linarith

/-- For `0 < t ≤ 1` and any `a`, dividing by `t` does not decrease the square. -/
theorem sq_le_div_sq {a t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) : a ^ 2 ≤ (a / t) ^ 2 := by
  have ht2 : 0 < t ^ 2 := pow_pos ht0 2
  have ht2le : t ^ 2 ≤ 1 := by nlinarith [ht0, ht1]
  rw [div_pow, le_div_iff₀ ht2]
  simpa using mul_le_mul_of_nonneg_left ht2le (sq_nonneg a)

/-- The `D_z⁰`-block `Xeta f = f·w/√(sin 2θ^η)` is dominated by the `ℋ¹`-integrand. -/
theorem sq_Xeta_le_HkIntegrand (α : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    (Work.Coercivity.Xeta f z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 1 f z θ := by
  have h := Work.Spaces.sq_le_HkIntegrand_z α 1 f z θ 0 (by norm_num)
  simpa only [Work.Coercivity.Xeta, Work.Coercivity.U0, Work.Spaces.DzIter_zero] using h

/-- The `D_z¹`-block `XetaDz f = D_zf·w/√(sin 2θ^η)` is dominated by the `ℋ¹`-integrand. -/
theorem sq_XetaDz_le_HkIntegrand (α : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    (Work.Coercivity.XetaDz f z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 1 f z θ := by
  have h := Work.Spaces.sq_le_HkIntegrand_z α 1 f z θ 1 (by norm_num)
  simpa only [Work.Coercivity.XetaDz, Work.Coercivity.U1, Work.Spaces.DzIter_succ,
    Work.Spaces.DzIter_zero] using h

/-- The `D_θ`-block `XgamDth α f = D_θf·W` is dominated by the `ℋ¹`-integrand. -/
theorem sq_XgamDth_le_HkIntegrand (α : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    (Work.Coercivity.XgamDth α f z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 1 f z θ := by
  have h := Work.Spaces.sq_le_HkIntegrand_mixed α 1 f z θ 1 0 (by norm_num) (by norm_num)
  simpa only [Work.Coercivity.XgamDth, Work.Coercivity.U2, Work.Spaces.mixed_zero_left,
    Work.Spaces.DthIter_succ, Work.Spaces.DthIter_zero] using h

/-- The plain `w²`-block `Xw f = f·w` is dominated by the `ℋ¹`-integrand **off the two
(null) endpoints** `θ = 0`, `θ = π/2`: there the `D_z⁰`-summand of the integrand is
`Xw f / √(sin 2θ^η)` and `0 < sin 2θ ≤ 1`. -/
theorem sq_Xw_le_HkIntegrand_ae (α : ℝ) (f : ℝ → ℝ → ℝ) (z : ℝ) :
    ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      (Work.Coercivity.Xw f z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 1 f z θ := by
  have hmeas : MeasureTheory.volume.restrict (Set.Ioo 0 (π / 2))
      = MeasureTheory.volume.restrict Work.Spaces.Iθ :=
    MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc
  rw [← hmeas]
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
  have hs0 : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have ht0 : 0 < (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) := Real.rpow_pos_of_pos hs0 _
  have ht1 : (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) ≤ 1 := by
    calc (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)
        ≤ (1 : ℝ) ^ (Work.Spaces.eta / 2) := Real.rpow_le_rpow (le_of_lt hs0) hs1
          (div_nonneg (le_of_lt Work.Spaces.eta_pos) (by norm_num))
      _ = 1 := by simp
  have hkey : (f z θ * Work.Spaces.w z) ^ 2
      ≤ ((f z θ * Work.Spaces.w z) / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2 :=
    sq_le_div_sq ht0 ht1
  have hterm : (Work.Coercivity.Xw f z θ) ^ 2
      ≤ (Work.Spaces.DzIter 0 f z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
    simp only [Work.Coercivity.Xw, Work.Spaces.DzIter_zero]
    rw [← mul_div_assoc]
    exact hkey
  exact le_trans hterm (Work.Spaces.sq_le_HkIntegrand_z α 1 f z θ 0 (by norm_num))

/-- Honesty of the "average" domination `(HkIntegrand α 1 a + HkIntegrand α 1 b)/2` used for
all four pairings: it is the arithmetic mean of two integrable functions. -/
theorem I2Mem_HkPairDom (α : ℝ) {a b : ℝ → ℝ → ℝ} (ha : Work.Spaces.HkMem α 1 a)
    (hb : Work.Spaces.HkMem α 1 b) :
    Work.Coercivity.I2Mem (fun z θ => (Work.Spaces.HkIntegrand α 1 a z θ
      + Work.Spaces.HkIntegrand α 1 b z θ) / 2) := by
  refine ⟨fun z hz => (ha.1 z hz |>.add (hb.1 z hz)).div_const 2, ?_⟩
  refine (ha.2.div_const 2 |>.add (hb.2.div_const 2)).congr ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
  simp only [Pi.add_apply]
  rw [MeasureTheory.integral_div, MeasureTheory.integral_add (ha.1 z hz) (hb.1 z hz)]
  ring

/-- **Domination criterion for honesty.**  If an integrand `F` is continuous on the open
quadrant, vanishes on the slice `z = 0`, and is dominated (a.e. in `θ`) by an honest
integrand `D`, then its iterated integral over the quadrant is honest. -/
theorem I2Mem_of_dominated {F D : ℝ → ℝ → ℝ}
    (hD : Work.Coercivity.I2Mem D)
    (hFc : ContinuousOn (Function.uncurry F) Qo)
    (hF0 : ∀ θ, F 0 θ = 0)
    (hle : ∀ z ∈ Work.Spaces.Iz, ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      |F z θ| ≤ D z θ) :
    Work.Coercivity.I2Mem F := by
  have haesm : MeasureTheory.AEStronglyMeasurable (Function.uncurry F)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _ hFc
  refine ⟨fun z hz => ?_, ?_⟩
  · rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hpos
    · subst h0
      have hz0 : (fun θ : ℝ => F 0 θ) = fun _ : ℝ => (0 : ℝ) := by
        funext θ; exact hF0 θ
      rw [hz0]
      exact MeasureTheory.integrableOn_zero
    · exact MeasureTheory.Integrable.mono' (hD.1 z hz)
        (Work.Spaces.aesm_slice_of_continuousOn_Qd _ hFc hpos)
        (by filter_upwards [hle z hz] with θ hθ; rwa [Real.norm_eq_abs])
  · refine MeasureTheory.Integrable.mono' hD.2 haesm.integral_prod_right' ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
    rw [Real.norm_eq_abs]
    calc |∫ θ in Work.Spaces.Iθ, F z θ| ≤ ∫ θ in Work.Spaces.Iθ, |F z θ| := by
          simpa only [Real.norm_eq_abs] using
            (MeasureTheory.norm_integral_le_integral_norm (fun θ : ℝ => F z θ)
              (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ))
      _ ≤ ∫ θ in Work.Spaces.Iθ, D z θ :=
          MeasureTheory.integral_mono_of_nonneg (Filter.Eventually.of_forall
            (fun θ => abs_nonneg _)) (hD.1 z hz) (hle z hz)

/-! ## The four honest pairings of `H1IP` -/

theorem PairHonest_eta_Q (α : ℝ) {a b : ℝ → ℝ → ℝ}
    (hqa : Work.FTS.LocData.SmoothQuad a) (hqb : Work.FTS.LocData.SmoothQuad b)
    (hma : Work.Spaces.HkMem α 1 a) (hmb : Work.Spaces.HkMem α 1 b) :
    Work.Coercivity.PairHonest Work.Coercivity.lamEta a b := by
  refine I2Mem_of_dominated (I2Mem_HkPairDom α hma hmb) ?_ ?_ ?_
  · have hfun : Function.uncurry (fun z θ => a z θ * b z θ * Work.Coercivity.lamEta z θ)
        = fun p : ℝ × ℝ => Function.uncurry a p * Function.uncurry b p
            * Function.uncurry Work.Coercivity.lamEta p := by
      funext p; rcases p with ⟨z, θ⟩; rfl
    rw [hfun]
    exact ((continuousOn_smoothQuad hqa).mul (continuousOn_smoothQuad hqb)).mul continuousOn_lamEta
  · intro θ
    simp [Work.Coercivity.lamEta, Work.Spaces.w]
  · intro z _
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    rw [← Work.Coercivity.Xeta_mul_eq a b z θ hθ]
    calc |Work.Coercivity.Xeta a z θ * Work.Coercivity.Xeta b z θ|
        = |Work.Coercivity.Xeta a z θ| * |Work.Coercivity.Xeta b z θ| := abs_mul _ _
      _ ≤ ((Work.Coercivity.Xeta a z θ) ^ 2 + (Work.Coercivity.Xeta b z θ) ^ 2) / 2 :=
          abs_mul_abs_le_half _ _
      _ ≤ (Work.Spaces.HkIntegrand α 1 a z θ + Work.Spaces.HkIntegrand α 1 b z θ) / 2 := by
          have h1 := sq_Xeta_le_HkIntegrand α a z θ
          have h2 := sq_Xeta_le_HkIntegrand α b z θ
          linarith

theorem PairHonest_etaDz_Q (α : ℝ) {a b : ℝ → ℝ → ℝ}
    (hqa : Work.FTS.LocData.SmoothQuad a) (hqb : Work.FTS.LocData.SmoothQuad b)
    (hma : Work.Spaces.HkMem α 1 a) (hmb : Work.Spaces.HkMem α 1 b) :
    Work.Coercivity.PairHonest Work.Coercivity.lamEta
      (Work.Spaces.Dz a) (Work.Spaces.Dz b) := by
  refine I2Mem_of_dominated (I2Mem_HkPairDom α hma hmb) ?_ ?_ ?_
  · have hfun : Function.uncurry (fun z θ =>
        Work.Spaces.Dz a z θ * Work.Spaces.Dz b z θ * Work.Coercivity.lamEta z θ)
        = fun p : ℝ × ℝ => Function.uncurry (Work.Spaces.Dz a) p
            * Function.uncurry (Work.Spaces.Dz b) p
            * Function.uncurry Work.Coercivity.lamEta p := by
      funext p; rcases p with ⟨z, θ⟩; rfl
    rw [hfun]
    exact ((continuousOn_Dz_smoothQuad hqa).mul (continuousOn_Dz_smoothQuad hqb)).mul
      continuousOn_lamEta
  · intro θ
    simp [Work.Coercivity.lamEta, Work.Spaces.w]
  · intro z _
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    rw [← Work.Coercivity.XetaDz_mul_eq a b z θ hθ]
    calc |Work.Coercivity.XetaDz a z θ * Work.Coercivity.XetaDz b z θ|
        = |Work.Coercivity.XetaDz a z θ| * |Work.Coercivity.XetaDz b z θ| := abs_mul _ _
      _ ≤ ((Work.Coercivity.XetaDz a z θ) ^ 2 + (Work.Coercivity.XetaDz b z θ) ^ 2) / 2 :=
          abs_mul_abs_le_half _ _
      _ ≤ (Work.Spaces.HkIntegrand α 1 a z θ + Work.Spaces.HkIntegrand α 1 b z θ) / 2 := by
          have h1 := sq_XetaDz_le_HkIntegrand α a z θ
          have h2 := sq_XetaDz_le_HkIntegrand α b z θ
          linarith

theorem PairHonest_gam_Q (α : ℝ) {a b : ℝ → ℝ → ℝ}
    (hqa : Work.FTS.LocData.SmoothQuad a) (hqb : Work.FTS.LocData.SmoothQuad b)
    (hma : Work.Spaces.HkMem α 1 a) (hmb : Work.Spaces.HkMem α 1 b) :
    Work.Coercivity.PairHonest (Work.Coercivity.lamGam α)
      (Work.Spaces.Dth a) (Work.Spaces.Dth b) := by
  refine I2Mem_of_dominated (I2Mem_HkPairDom α hma hmb) ?_ ?_ ?_
  · have hfun : Function.uncurry (fun z θ =>
        Work.Spaces.Dth a z θ * Work.Spaces.Dth b z θ * Work.Coercivity.lamGam α z θ)
        = fun p : ℝ × ℝ => Function.uncurry (Work.Spaces.Dth a) p
            * Function.uncurry (Work.Spaces.Dth b) p
            * Function.uncurry (Work.Coercivity.lamGam α) p := by
      funext p; rcases p with ⟨z, θ⟩; rfl
    rw [hfun]
    exact ((continuousOn_Dth_smoothQuad hqa).mul (continuousOn_Dth_smoothQuad hqb)).mul
      (continuousOn_lamGam α)
  · intro θ
    simp [Work.Coercivity.lamGam, Work.Spaces.w]
  · intro z _
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    rw [← Work.Coercivity.XgamDth_mul_eq α a b z θ hθ]
    calc |Work.Coercivity.XgamDth α a z θ * Work.Coercivity.XgamDth α b z θ|
        = |Work.Coercivity.XgamDth α a z θ| * |Work.Coercivity.XgamDth α b z θ| := abs_mul _ _
      _ ≤ ((Work.Coercivity.XgamDth α a z θ) ^ 2
            + (Work.Coercivity.XgamDth α b z θ) ^ 2) / 2 := abs_mul_abs_le_half _ _
      _ ≤ (Work.Spaces.HkIntegrand α 1 a z θ + Work.Spaces.HkIntegrand α 1 b z θ) / 2 := by
          have h1 := sq_XgamDth_le_HkIntegrand α a z θ
          have h2 := sq_XgamDth_le_HkIntegrand α b z θ
          linarith

theorem PairHonest_w_Q (α : ℝ) {a b : ℝ → ℝ → ℝ}
    (hqa : Work.FTS.LocData.SmoothQuad a) (hqb : Work.FTS.LocData.SmoothQuad b)
    (hma : Work.Spaces.HkMem α 1 a) (hmb : Work.Spaces.HkMem α 1 b) :
    Work.Coercivity.PairHonest Work.Coercivity.lamW a b := by
  refine I2Mem_of_dominated (I2Mem_HkPairDom α hma hmb) ?_ ?_ ?_
  · have hfun : Function.uncurry (fun z θ => a z θ * b z θ * Work.Coercivity.lamW z θ)
        = fun p : ℝ × ℝ => Function.uncurry a p * Function.uncurry b p
            * Function.uncurry Work.Coercivity.lamW p := by
      funext p; rcases p with ⟨z, θ⟩; rfl
    rw [hfun]
    exact ((continuousOn_smoothQuad hqa).mul (continuousOn_smoothQuad hqb)).mul continuousOn_lamW
  · intro θ
    simp [Work.Coercivity.lamW, Work.Spaces.w]
  · intro z _
    filter_upwards [sq_Xw_le_HkIntegrand_ae α a z, sq_Xw_le_HkIntegrand_ae α b z]
      with θ h1 h2
    have hXw : Work.Coercivity.Xw a z θ * Work.Coercivity.Xw b z θ
        = a z θ * b z θ * Work.Coercivity.lamW z θ := by
      simp only [Work.Coercivity.Xw, Work.Coercivity.lamW]; ring
    rw [← hXw]
    calc |Work.Coercivity.Xw a z θ * Work.Coercivity.Xw b z θ|
        = |Work.Coercivity.Xw a z θ| * |Work.Coercivity.Xw b z θ| := abs_mul _ _
      _ ≤ ((Work.Coercivity.Xw a z θ) ^ 2 + (Work.Coercivity.Xw b z θ) ^ 2) / 2 :=
          abs_mul_abs_le_half _ _
      _ ≤ (Work.Spaces.HkIntegrand α 1 a z θ + Work.Spaces.HkIntegrand α 1 b z θ) / 2 := by
          linarith

/-! ## Derivative linearity on the open quadrant -/

theorem Dz_add_Qo {a₁ a₂ : ℝ → ℝ → ℝ} (h1 : Work.FTS.LocData.SmoothQuad a₁)
    (h2 : Work.FTS.LocData.SmoothQuad a₂) :
    ∀ z θ, (z, θ) ∈ Qo →
      Work.Spaces.Dz (a₁ + a₂) z θ = Work.Spaces.Dz a₁ z θ + Work.Spaces.Dz a₂ z θ := by
  intro z θ hzθ
  have hz : z ∈ Set.Ioi (-1 : ℝ) := Set.mem_Ioi.mpr (by linarith [Set.mem_Ioi.mp hzθ.1])
  have hθ : θ ∈ Set.Ioo 0 (π / 2) := hzθ.2
  have hd : ∀ a : ℝ → ℝ → ℝ, Work.FTS.LocData.SmoothQuad a →
      DifferentiableAt ℝ (fun z' => a z' θ) z := fun a ha =>
    (Work.FTS.LocData.SmoothQuad.differentiableAt_slice_mixed ha 0 0 hz hθ)
  simp only [Work.Spaces.Dz, Work.Spaces.pz]
  rw [show (fun z' => (a₁ + a₂) z' θ) = (fun z' => a₁ z' θ) + (fun z' => a₂ z' θ) from rfl,
    deriv_add (hd a₁ h1) (hd a₂ h2)]
  ring

theorem Dth_add_Qo {a₁ a₂ : ℝ → ℝ → ℝ} (h1 : Work.FTS.LocData.SmoothQuad a₁)
    (h2 : Work.FTS.LocData.SmoothQuad a₂) :
    ∀ z θ, (z, θ) ∈ Qo →
      Work.Spaces.Dth (a₁ + a₂) z θ = Work.Spaces.Dth a₁ z θ + Work.Spaces.Dth a₂ z θ := by
  intro z θ hzθ
  have hz : z ∈ Set.Ioi (-1 : ℝ) := Set.mem_Ioi.mpr (by linarith [Set.mem_Ioi.mp hzθ.1])
  have hθ : θ ∈ Set.Ioo 0 (π / 2) := hzθ.2
  have hd : ∀ a : ℝ → ℝ → ℝ, Work.FTS.LocData.SmoothQuad a →
      DifferentiableAt ℝ (fun θ' => a z θ') θ := fun a ha =>
    (Work.FTS.LocData.SmoothQuad.differentiableAt_slice_DthIter ha 0 hz hθ)
  simp only [Work.Spaces.Dth, Work.Spaces.pth]
  rw [show (fun θ' => (a₁ + a₂) z θ') = (fun θ' => a₁ z θ') + (fun θ' => a₂ z θ') from rfl,
    deriv_add (hd a₁ h1) (hd a₂ h2)]
  ring

/-! ## Additivity of `H1IP` on `RegQ α 1` -/

theorem H1IP_add_Q (α : ℝ) {a₁ a₂ b : ℝ → ℝ → ℝ}
    (h1 : Work.FTS.Nonlin.RegQ α 1 a₁) (h2 : Work.FTS.Nonlin.RegQ α 1 a₂)
    (hb : Work.FTS.Nonlin.RegQ α 1 b) :
    Work.Coercivity.H1IP α (a₁ + a₂) b
      = Work.Coercivity.H1IP α a₁ b + Work.Coercivity.H1IP α a₂ b := by
  simp only [Work.FTS.Nonlin.RegQ] at h1 h2 hb
  obtain ⟨hq1, hm1, _⟩ := h1
  obtain ⟨hq2, hm2, _⟩ := h2
  obtain ⟨hqb, hmb, _⟩ := hb
  have hA : Work.Coercivity.wip Work.Coercivity.lamEta (Work.Spaces.Dz (a₁ + a₂))
        (Work.Spaces.Dz b)
      = Work.Coercivity.wip Work.Coercivity.lamEta (Work.Spaces.Dz a₁) (Work.Spaces.Dz b)
        + Work.Coercivity.wip Work.Coercivity.lamEta (Work.Spaces.Dz a₂) (Work.Spaces.Dz b) := by
    rw [Work.FTS.CoercivityFix.StepAssembly.wip_congr_Qd (A := Work.Spaces.Dz (a₁ + a₂))
      (A' := Work.Spaces.Dz a₁ + Work.Spaces.Dz a₂)
      (fun z θ hzθ => Dz_add_Qo hq1 hq2 z θ hzθ)]
    exact Work.Coercivity.wip_add_of_PairHonest Work.Coercivity.lamEta (Work.Spaces.Dz a₁)
      (Work.Spaces.Dz a₂) (Work.Spaces.Dz b)
      (PairHonest_etaDz_Q α hq1 hqb hm1 hmb) (PairHonest_etaDz_Q α hq2 hqb hm2 hmb)
  have hB : Work.Coercivity.wip Work.Coercivity.lamEta (a₁ + a₂) b
      = Work.Coercivity.wip Work.Coercivity.lamEta a₁ b
        + Work.Coercivity.wip Work.Coercivity.lamEta a₂ b :=
    Work.Coercivity.wip_add_of_PairHonest Work.Coercivity.lamEta a₁ a₂ b
      (PairHonest_eta_Q α hq1 hqb hm1 hmb) (PairHonest_eta_Q α hq2 hqb hm2 hmb)
  have hC : Work.Coercivity.wip Work.Coercivity.lamW (a₁ + a₂) b
      = Work.Coercivity.wip Work.Coercivity.lamW a₁ b
        + Work.Coercivity.wip Work.Coercivity.lamW a₂ b :=
    Work.Coercivity.wip_add_of_PairHonest Work.Coercivity.lamW a₁ a₂ b
      (PairHonest_w_Q α hq1 hqb hm1 hmb) (PairHonest_w_Q α hq2 hqb hm2 hmb)
  have hD : Work.Coercivity.wip (Work.Coercivity.lamGam α) (Work.Spaces.Dth (a₁ + a₂))
        (Work.Spaces.Dth b)
      = Work.Coercivity.wip (Work.Coercivity.lamGam α) (Work.Spaces.Dth a₁)
          (Work.Spaces.Dth b)
        + Work.Coercivity.wip (Work.Coercivity.lamGam α) (Work.Spaces.Dth a₂)
          (Work.Spaces.Dth b) := by
    rw [Work.FTS.CoercivityFix.StepAssembly.wip_congr_Qd (A := Work.Spaces.Dth (a₁ + a₂))
      (A' := Work.Spaces.Dth a₁ + Work.Spaces.Dth a₂)
      (fun z θ hzθ => Dth_add_Qo hq1 hq2 z θ hzθ)]
    exact Work.Coercivity.wip_add_of_PairHonest (Work.Coercivity.lamGam α) (Work.Spaces.Dth a₁)
      (Work.Spaces.Dth a₂) (Work.Spaces.Dth b)
      (PairHonest_gam_Q α hq1 hqb hm1 hmb) (PairHonest_gam_Q α hq2 hqb hm2 hmb)
  have hEtaW : (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
      = Work.Coercivity.lamEta := rfl
  have hGamW : (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      = Work.Coercivity.lamGam α := rfl
  have hWtW : (fun z _ => Work.Spaces.w z ^ 2) = Work.Coercivity.lamW := rfl
  simp only [Work.Coercivity.H1IP]
  rw [hEtaW, hGamW, hWtW, hA, hB, hC, hD]
  ring

theorem H1IP_core_Q (α : ℝ) (hα : 0 < α) :
    (∀ f₁ f₂ g : ℝ → ℝ → ℝ, Work.FTS.Nonlin.RegQ α 1 f₁ → Work.FTS.Nonlin.RegQ α 1 f₂ →
      Work.FTS.Nonlin.RegQ α 1 g →
      Work.Coercivity.H1IP α (f₁ + f₂) g
        = Work.Coercivity.H1IP α f₁ g + Work.Coercivity.H1IP α f₂ g) ∧
    (∀ (c : ℝ) (f g : ℝ → ℝ → ℝ), Work.FTS.Nonlin.RegQ α 1 f → Work.FTS.Nonlin.RegQ α 1 g →
      Work.Coercivity.H1IP α (fun z θ => c * f z θ) g
        = c * Work.Coercivity.H1IP α f g) ∧
    (∀ f g : ℝ → ℝ → ℝ, Work.Coercivity.H1IP α f g = Work.Coercivity.H1IP α g f) ∧
    (∀ f : ℝ → ℝ → ℝ, 0 ≤ Work.Coercivity.H1IP α f f) :=
  ⟨fun f₁ f₂ g h₁ h₂ hg => H1IP_add_Q α h₁ h₂ hg,
   fun c f g _ _ => Work.Coercivity.H1IP_homog α c f g,
   fun f g => H1IP_comm α f g,
   fun f => Work.Coercivity.H1IP_nonneg α f⟩

end Work.FTS.CoercivityFix.Assembly
