import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.intSlotLeHkSq
import Submission.Work.FTS.StrongPersist.N6Trans.Hon.HkProdOpen
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.aesm_of_continuousOn_Qd

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Pair6Aux.T6Gen

open MeasureTheory Set Filter
open scoped Real Topology

/-! ## Auxiliary facts for the weighted mixed slot `(D_z^j D_θ f · W)²`

The two pieces of bookkeeping needed to turn the abstract "single slot" machinery
(`Work.Spaces.sq_le_HkIntegrand_mixed`, `intSlotLeHkSq`) into the statement below:

* the slot `(D_z^jD_θ f · W)²` is continuous on the open quadrant, so its `z`-marginal is
  a.e. strongly measurable and is dominated by the (integrable) marginal of `HkIntegrand`;
* the square of the weight factorises as `(w · s^{-γ/2})² = w² · s^{-γ}`, which identifies
  the slot's integral with the `θw = s^{-γ}` instance of `intSlotLeHkSq`. -/

/-- `sin(2θ) ≥ 0` on `[0,π/2]`. -/
private lemma sin_two_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- The weight `W = w · sin(2θ)^{-γ/2}` is continuous on the open quadrant. -/
private lemma continuousOn_Wt_Q0 (α : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2) Work.FTS.EllipticEst.Q0 := by
  have hsinpos : ∀ p ∈ Work.FTS.EllipticEst.Q0, 0 < Real.sin (2 * p.2) := by
    intro p hp
    obtain ⟨-, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hfun : (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2)
      = fun p : ℝ × ℝ =>
          Work.Spaces.w p.1 * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2)) := by
    funext p; rfl
  rw [hfun]
  have hw : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1) Work.FTS.EllipticEst.Q0 := by
    have hfun2 : (fun p : ℝ × ℝ => Work.Spaces.w p.1)
        = fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2 := by
      funext p; rfl
    rw [hfun2]
    exact ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
      (continuousOn_fst.pow 2)
      (fun p hp => pow_ne_zero 2 (ne_of_gt (Work.FTS.EllipticEst.mem_Q0.mp hp).1))
  exact hw.mul
    (((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
      (fun p hp => Or.inl (ne_of_gt (hsinpos p hp))))

/-- The squared weighted mixed slot `(D_z^jD_θ f · W)²` is continuous on the open quadrant. -/
private lemma contOn_mixed_sq {f : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen f)
    (j : ℕ) (α : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ =>
      (Work.Spaces.mixed j 1 f p.1 p.2 * Work.Spaces.Wt α p.1 p.2) ^ 2)
      Work.FTS.EllipticEst.Q0 :=
  ((((hsm.mixed j 1).forall 0).continuousOn.mul (continuousOn_Wt_Q0 α)) |>.pow 2)

/-- The `z`-marginal of a weighted mixed slot is a.e. strongly measurable. -/
private lemma aesm_mixed_slot (α : ℝ) {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (j : ℕ) :
    MeasureTheory.AEStronglyMeasurable
      (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.mixed j 1 f z θ * Work.Spaces.Wt α z θ) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
  (Work.Spaces.aesm_of_continuousOn_Qd _
    (contOn_mixed_sq hsm j α)).integral_prod_right'
    (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ)

/-- The square of the weight factorises: `(w · s^{-γ/2})² = w² · s^{-γ}` for `s ≥ 0`. -/
private lemma Wt_sq_eq (α z θ : ℝ) (hs : 0 ≤ Real.sin (2 * θ)) :
    (Work.Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
  rw [Work.Spaces.Wt, Work.Spaces.wTheta, mul_pow]
  rw [show ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ 2
        = ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ ((2 : ℝ)) from
      (Real.rpow_natCast ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) 2).symm]
  rw [← Real.rpow_mul hs]
  rw [show (-(Work.Spaces.gam α / 2)) * (2 : ℝ) = -(Work.Spaces.gam α) by ring]

/-- The weighted mixed slot, in the `θw = s^{-γ}` form used by `intSlotLeHkSq`. -/
private lemma mixed_slot_sq_eq (α : ℝ) (f : ℝ → ℝ → ℝ) (j : ℕ) (z θ : ℝ)
    (hs : 0 ≤ Real.sin (2 * θ)) :
    (Work.Spaces.mixed j 1 f z θ * Work.Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        * (Work.Spaces.mixed j 1 f z θ) ^ 2 := by
  rw [mul_pow, Wt_sq_eq α z θ hs]
  ring

theorem mixedSlotL2 : ∀ α ∈ Set.Ioc 0 1, ∀ (f : ℝ → ℝ → ℝ) (j : ℕ),
    Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 6 f → j ≤ 5 →
      MeasureTheory.Integrable (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.mixed j 1 f z θ * Work.Spaces.Wt α z θ) ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iz) ∧
      (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.mixed j 1 f z θ * Work.Spaces.Wt α z θ) ^ 2)
        ≤ Work.Spaces.HkSq α 6 f := by
  intro α _hα f j hsm hmem hj
  constructor
  · -- Integrability of the `z`-marginal, by domination by the `ℋ⁶`-integrand.
    refine MeasureTheory.Integrable.mono' hmem.2 (aesm_mixed_slot α hsm j) ?_
    refine MeasureTheory.ae_restrict_of_forall_mem
      (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici) fun z hz => ?_
    have hAn : ‖∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.mixed j 1 f z θ * Work.Spaces.Wt α z θ) ^ 2‖
        = ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.mixed j 1 f z θ * Work.Spaces.Wt α z θ) ^ 2 :=
      Real.norm_of_nonneg (MeasureTheory.integral_nonneg fun θ => sq_nonneg _)
    have hle : (∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.mixed j 1 f z θ * Work.Spaces.Wt α z θ) ^ 2)
        ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 f z θ :=
      MeasureTheory.integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun θ => sq_nonneg _) (hmem.1 z hz)
        (Filter.Eventually.of_forall fun θ =>
          Work.Spaces.sq_le_HkIntegrand_mixed α 6 f z θ 1 j le_rfl (by omega))
    rw [hAn]
    exact hle
  · -- The value of the integral, via the `θw = sin(2θ)^{-γ}` slot of `intSlotLeHkSq`.
    have hEq : (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.mixed j 1 f z θ * Work.Spaces.Wt α z θ) ^ 2)
        =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iz]
          (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
              * (Work.Spaces.mixed j 1 f z θ) ^ 2) := by
      filter_upwards [MeasureTheory.ae_restrict_mem
        (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici)] with z _
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [MeasureTheory.ae_restrict_mem
        (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)] with θ hθ
      exact mixed_slot_sq_eq α f j z θ (sin_two_nonneg_Iθ hθ)
    calc (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.mixed j 1 f z θ * Work.Spaces.Wt α z θ) ^ 2)
        = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
              * (Work.Spaces.mixed j 1 f z θ) ^ 2 :=
          MeasureTheory.integral_congr_ae hEq
      _ ≤ Work.Spaces.HkSq α 6 f :=
          (intSlotLeHkSq α hmem).2 j 1 le_rfl (by omega)
            (fun θ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
            (fun θ hθ => Real.rpow_nonneg
              (sin_two_nonneg_Iθ ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩) _)
            (fun _ _ => le_refl _)

end Work.FTS.StrongPersist.H6Pair6Aux.T6Gen
