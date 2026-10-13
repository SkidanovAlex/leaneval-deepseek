/-
# The `γ ≤ η` case of the wrong-weight layer lemma

`wrongLayerInt α f b t (2t) = ∫_z w(z)^2 ∫_{θ∈(t,2t)} sin(2θ)^{-γ} (D_z^b f z θ)^2 dθ dz`
with `γ = gam α`, and on the layer `sin(2θ) ≤ 4t`; hence, when `γ ≤ η = 99/100`,

  `sin(2θ)^{-γ} = sin(2θ)^{-η} · sin(2θ)^{η-γ} ≤ (4t)^{η-γ} sin(2θ)^{-η}`,

and the right-hand side is (up to the factor `(4t)^{η-γ}`) exactly the `D_z^b`-summand of
`HkIntegrand α 4 f`, i.e. `(D_z^b f · w / sin(2θ)^{η/2})^2`.  This gives

  `wrongLayerInt α f b t (2t) ≤ (4t)^{η-γ} · HkSq α 4 f`,

which tends to `0` for `t → 0⁺`.  The comparison of the iterated integrals is done with
`Work.FTS.GalBasis.cc.Subcut.HkSq_le_of_ae_dominated` (an a.e. pointwise bound plus the
integrability of the dominating function is enough).
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.GalBasis.cc.ShrinkDefs
import Submission.Work.FTS.GalBasis.cc.wwBasic
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.GalBasis.cc.Subcut.HkSq_le_of_ae_dominated

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalBasis.cc

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Elementary rewritings of the weights -/

/-- `Wt α z θ ^ 2 = w z ^ 2 * sin(2θ)^{-γ}` on the open quadrant. -/
lemma Wt_sq_eq (α : ℝ) {z θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < π / 2) :
    (Work.Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
  rw [Work.Spaces.Wt, Work.Spaces.wTheta, mul_pow]
  have hs : 0 < Real.sin (2 * θ) := sin_two_pos hθ0 hθ1
  have h : (Real.sin (2 * θ) ^ (-(Work.Spaces.gam α / 2))) ^ 2
      = (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
    rw [← Real.rpow_two, ← Real.rpow_mul (le_of_lt hs)]
    congr 1
    ring
  rw [h]

/-- The `D_z^b`-summand of `HkIntegrand`, rewritten with the `η`-weight:
`(D_z^b f · w / sin(2θ)^{η/2})^2 = w z ^ 2 * (D_z^b f)^2 * sin(2θ)^{-η}`. -/
lemma slot_eq (b : ℕ) {f : ℝ → ℝ → ℝ} {z θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < π / 2) :
    (Work.Spaces.DzIter b f z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      = (Work.Spaces.w z) ^ 2 * (Work.Spaces.DzIter b f z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
  have hs : 0 < Real.sin (2 * θ) := sin_two_pos hθ0 hθ1
  have hT : ((Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
      = (Real.sin (2 * θ)) ^ (Work.Spaces.eta) := by
    rw [← Real.rpow_two, ← Real.rpow_mul (le_of_lt hs)]
    congr 1
    ring
  rw [div_eq_mul_inv, mul_pow]
  rw [show ((Work.Spaces.w z) * ((Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))⁻¹) ^ 2
      = (Work.Spaces.w z) ^ 2 * (((Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2)⁻¹ from by
    rw [mul_pow, inv_pow]]
  rw [hT, ← Real.rpow_neg (le_of_lt hs)]
  ring

/-- On the layer `(t, 2t)` (with `t > 0`), `sin(2θ) ≤ 4t`. -/
lemma sin_two_le_layer {θ t : ℝ} (hθ : θ ∈ Set.Ioc t (2 * t)) (ht : 0 < t) :
    Real.sin (2 * θ) ≤ 4 * t := by
  have h1 : Real.sin (2 * θ) ≤ 2 * θ := Real.sin_le (by linarith [hθ.1, ht])
  linarith [h1, hθ.2]

/-- On the layer, if `γ ≤ η`, then `sin(2θ)^{-γ} ≤ (4t)^{η-γ} · sin(2θ)^{-η}`. -/
lemma rpow_layer_le {γ : ℝ} (hγ : γ ≤ Work.Spaces.eta) {θ t : ℝ}
    (hθ : θ ∈ Set.Ioc t (2 * t)) (ht : 0 < t) (h2t : 2 * t ≤ Real.pi / 4) :
    (Real.sin (2 * θ)) ^ (-γ)
      ≤ (4 * t) ^ (Work.Spaces.eta - γ) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
  have hθ0 : 0 < θ := by linarith [hθ.1, ht]
  have hθπ : θ < π / 2 := by linarith [hθ.2, h2t, Real.pi_pos]
  have hs : 0 < Real.sin (2 * θ) := sin_two_pos hθ0 hθπ
  have hs4 : Real.sin (2 * θ) ≤ 4 * t := sin_two_le_layer hθ ht
  have hexp : (0:ℝ) ≤ Work.Spaces.eta - γ := by linarith
  have h1 : (Real.sin (2 * θ)) ^ (-γ)
      = (Real.sin (2 * θ)) ^ (Work.Spaces.eta - γ)
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
    rw [← Real.rpow_add hs]
    congr 1
    ring
  rw [h1]
  exact mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow (le_of_lt hs) hs4 hexp)
    (Real.rpow_nonneg (le_of_lt hs) _)

/-! ## The pointwise bound on the layer -/

/-- **Pointwise bound on the layer.**  For `θ ∈ (t,2t)`, `gam α ≤ η`, `2t ≤ π/4` and `b ≤ 3`:
`(D_z^b f z θ · Wt α z θ)^2 ≤ (4t)^{η-γ} · HkIntegrand α 4 f z θ`. -/
lemma layer_pointwise {α : ℝ} {b : ℕ} {f : ℝ → ℝ → ℝ} (hb4 : b ≤ 3)
    (hγ : Work.Spaces.gam α ≤ Work.Spaces.eta)
    {t θ z : ℝ} (ht : 0 < t) (h2t : 2 * t ≤ Real.pi / 4) (hθ : θ ∈ Set.Ioc t (2 * t)) :
    (Work.Spaces.DzIter b f z θ * Work.Spaces.Wt α z θ) ^ 2
      ≤ (4 * t) ^ (Work.Spaces.eta - Work.Spaces.gam α) * Work.Spaces.HkIntegrand α 4 f z θ := by
  have hθ0 : 0 < θ := by linarith [hθ.1, ht]
  have hθπ : θ < π / 2 := by linarith [hθ.2, h2t, Real.pi_pos]
  have hcmp := rpow_layer_le hγ hθ ht h2t
  have hcoe2 : (0:ℝ) ≤ (4 * t) ^ (Work.Spaces.eta - Work.Spaces.gam α) :=
    Real.rpow_nonneg (by linarith) _
  rw [mul_pow, Wt_sq_eq α hθ0 hθπ]
  calc (Work.Spaces.DzIter b f z θ) ^ 2
        * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      ≤ (Work.Spaces.DzIter b f z θ) ^ 2
        * ((Work.Spaces.w z) ^ 2
          * ((4 * t) ^ (Work.Spaces.eta - Work.Spaces.gam α)
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcmp (sq_nonneg _)) (sq_nonneg _)
    _ = (4 * t) ^ (Work.Spaces.eta - Work.Spaces.gam α)
        * ((Work.Spaces.DzIter b f z θ) ^ 2
          * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))) := by ring
    _ = (4 * t) ^ (Work.Spaces.eta - Work.Spaces.gam α)
        * (Work.Spaces.DzIter b f z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
        rw [slot_eq (f := f) b hθ0 hθπ]
        ring
    _ ≤ (4 * t) ^ (Work.Spaces.eta - Work.Spaces.gam α) * Work.Spaces.HkIntegrand α 4 f z θ :=
        mul_le_mul_of_nonneg_left (Work.Spaces.sq_le_HkIntegrand_z α 4 f z θ b (by omega)) hcoe2

/-! ## The `γ ≤ η` layer bound -/

/-- **The `γ ≤ η` layer bound.**  For `gam α ≤ η`, `0 < t`, `2t ≤ π/4` and `b ≤ 3`,
`wrongLayerInt α f b t (2t) ≤ (4t)^{η-γ} · HkSq α 4 f`. -/
lemma eta_layer_bound {α : ℝ} {f : Fn} (hsm : Work.FTS.EllipticEst.SmoothOpen f)
    (hmem : Work.Spaces.HkMem α 4 f) {b : ℕ} (hb4 : b ≤ 3)
    (hγ : Work.Spaces.gam α ≤ Work.Spaces.eta)
    {t : ℝ} (ht : 0 < t) (h2t : 2 * t ≤ Real.pi / 4) :
    wrongLayerInt α f b t (2 * t)
      ≤ (4 * t) ^ (Work.Spaces.eta - Work.Spaces.gam α) * Work.Spaces.HkSq α 4 f := by
  have hcoe : (0:ℝ) ≤ (4 * t) ^ (Work.Spaces.eta - Work.Spaces.gam α) :=
    Real.rpow_nonneg (by linarith) _
  have hmain := Subcut.HkSq_le_of_ae_dominated
    (g := fun z θ => (Work.Spaces.DzIter b f z θ * Work.Spaces.Wt α z θ) ^ 2
      * (Set.Ioc t (2 * t)).indicator (fun _ => (1 : ℝ)) θ)
    (ψ := fun z θ => (4 * t) ^ (Work.Spaces.eta - Work.Spaces.gam α)
      * Work.Spaces.HkIntegrand α 4 f z θ)
    (fun z θ => mul_nonneg (sq_nonneg _) (by
      by_cases hθ : θ ∈ Set.Ioc t (2 * t)
      · simp [Set.indicator_of_mem hθ]
      · simp [Set.indicator_of_notMem hθ]))
    (fun z θ => mul_nonneg hcoe (Work.Spaces.HkIntegrand_nonneg α 4 f z θ))
    (by
      have hcont : ContinuousOn
          (fun q : ℝ × ℝ => (4 * t) ^ (Work.Spaces.eta - Work.Spaces.gam α)
            * Work.Spaces.HkIntegrand α 4 f q.1 q.2)
          (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
        continuousOn_const.mul (hsm.continuousOn_HkIntegrand α 4)
      exact Work.Spaces.aesm_of_continuousOn_Qd _ hcont)
    (Filter.Eventually.of_forall fun p => by
      by_cases hp : p.2 ∈ Set.Ioc t (2 * t)
      · simp only [Set.indicator_of_mem hp, mul_one]
        exact layer_pointwise hb4 hγ ht h2t hp
      · simp only [Set.indicator_of_notMem hp, mul_zero]
        exact mul_nonneg hcoe (Work.Spaces.HkIntegrand_nonneg α 4 f p.1 p.2))
    (by
      filter_upwards [MeasureTheory.ae_restrict_mem (by rw [Work.Spaces.Iz]; exact measurableSet_Ici)]
        with z hz
      exact (hmem.1 z hz).const_mul _)
    (by
      have hfun : (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
            (4 * t) ^ (Work.Spaces.eta - Work.Spaces.gam α)
              * Work.Spaces.HkIntegrand α 4 f z θ)
          = fun z : ℝ => (4 * t) ^ (Work.Spaces.eta - Work.Spaces.gam α)
              * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ) := by
        funext z
        exact MeasureTheory.integral_const_mul _ _
      rw [hfun]
      exact hmem.2.const_mul _)
  -- identify the left-hand side with `wrongLayerInt`
  have hL : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.DzIter b f z θ * Work.Spaces.Wt α z θ) ^ 2
          * (Set.Ioc t (2 * t)).indicator (fun _ => (1 : ℝ)) θ)
      = wrongLayerInt α f b t (2 * t) := by
    rw [wrongLayerInt]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    show (∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.DzIter b f z θ * Work.Spaces.Wt α z θ) ^ 2
            * (Set.Ioc t (2 * t)).indicator (fun _ => (1 : ℝ)) θ)
      = ∫ θ in t..(2 * t), (Work.Spaces.DzIter b f z θ * Work.Spaces.Wt α z θ) ^ 2
    have hθ2t : t ≤ 2 * t := by linarith
    have hsub : Set.Ioc t (2 * t) ⊆ Work.Spaces.Iθ := fun x hx =>
      ⟨by linarith [hx.1, ht], by linarith [hx.2, h2t, Real.pi_pos]⟩
    rw [show (∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.DzIter b f z θ * Work.Spaces.Wt α z θ) ^ 2
            * (Set.Ioc t (2 * t)).indicator (fun _ => (1 : ℝ)) θ)
        = ∫ θ in Work.Spaces.Iθ,
            (Set.Ioc t (2 * t)).indicator
              (fun θ => (Work.Spaces.DzIter b f z θ * Work.Spaces.Wt α z θ) ^ 2) θ from
      MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => by
        by_cases hθ : θ ∈ Set.Ioc t (2 * t)
        · simp only [Set.indicator_of_mem hθ, mul_one]
        · simp only [Set.indicator_of_notMem hθ, mul_zero])]
    rw [MeasureTheory.setIntegral_indicator measurableSet_Ioc]
    rw [show Work.Spaces.Iθ ∩ Set.Ioc t (2 * t) = Set.Ioc t (2 * t) from
      Set.inter_eq_right.mpr hsub]
    exact (intervalIntegral.integral_of_le hθ2t).symm
  -- identify the right-hand side with `(4t)^{η-γ} * HkSq`
  have hR : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        (4 * t) ^ (Work.Spaces.eta - Work.Spaces.gam α)
          * Work.Spaces.HkIntegrand α 4 f z θ)
      = (4 * t) ^ (Work.Spaces.eta - Work.Spaces.gam α) * Work.Spaces.HkSq α 4 f := by
    rw [Work.Spaces.HkSq]
    rw [show (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          (4 * t) ^ (Work.Spaces.eta - Work.Spaces.gam α)
            * Work.Spaces.HkIntegrand α 4 f z θ)
        = ∫ z in Work.Spaces.Iz,
            ((4 * t) ^ (Work.Spaces.eta - Work.Spaces.gam α)
              * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ) from
      MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z =>
        MeasureTheory.integral_const_mul _ _)]
    exact MeasureTheory.integral_const_mul _ _
  rw [← hL, ← hR]
  exact hmain

/-! ## The sequence form of the `γ ≤ η` bound -/

/-- `(4/(N+1))^p → 0` for `p > 0`. -/
lemma tendsto_rpow_div_nat (p : ℝ) (hp : 0 < p) :
    Tendsto (fun N : ℕ => (4 / ((N : ℝ) + 1)) ^ p) Filter.atTop (nhds 0) := by
  have hbase : Tendsto (fun N : ℕ => ((N : ℝ) + 1)) Filter.atTop Filter.atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have hpow : Tendsto (fun N : ℕ => (((N : ℝ) + 1)) ^ p) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop hp).comp hbase
  have hinv : Tendsto (fun N : ℕ => ((((N : ℝ) + 1)) ^ p)⁻¹) Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hpow
  have h4 : Tendsto (fun N : ℕ => (4:ℝ) ^ p * ((((N : ℝ) + 1)) ^ p)⁻¹) Filter.atTop (nhds 0) := by
    have h := (tendsto_const_nhds (x := (4:ℝ) ^ p)).mul hinv
    simpa using h
  refine h4.congr' (Filter.Eventually.of_forall fun N => ?_)
  show (4:ℝ) ^ p * (((↑N : ℝ) + 1) ^ p)⁻¹ = (4 / ((↑N : ℝ) + 1)) ^ p
  rw [div_eq_mul_inv, Real.mul_rpow (by norm_num) (by positivity),
    Real.inv_rpow (by positivity)]

/-- `wrongLayerInt α f b t (2t) ≥ 0`. -/
lemma wrongLayerInt_nonneg {α : ℝ} {f : Fn} (b : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ wrongLayerInt α f b t (2 * t) := by
  rw [wrongLayerInt]
  exact integral_nonneg fun z => intervalIntegral.integral_nonneg (by linarith)
    fun θ _ => sq_nonneg _

/-- **The `γ < η` case of the first conjunct**, in sequence form. -/
theorem eta_case_tendsto {α : ℝ} {f : Fn} (hsm : Work.FTS.EllipticEst.SmoothOpen f)
    (hmem : Work.Spaces.HkMem α 4 f) {b : ℕ} (hb4 : b ≤ 3)
    (hγ : Work.Spaces.gam α < Work.Spaces.eta) :
    Filter.Tendsto
      (fun N : ℕ => wrongLayerInt α f b (1 / ((N : ℝ) + 1)) (2 / ((N : ℝ) + 1)))
      Filter.atTop (nhds 0) := by
  have hp : 0 < Work.Spaces.eta - Work.Spaces.gam α := by linarith
  have hHk : Tendsto
      (fun N : ℕ => (4 / ((N : ℝ) + 1)) ^ (Work.Spaces.eta - Work.Spaces.gam α)
        * Work.Spaces.HkSq α 4 f)
      Filter.atTop (nhds 0) := by
    have h4 := (tendsto_rpow_div_nat (Work.Spaces.eta - Work.Spaces.gam α) hp).mul
      (tendsto_const_nhds (x := Work.Spaces.HkSq α 4 f))
    simpa using h4
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hHk ?_ ?_
  · filter_upwards with N
    have h2t' : (2:ℝ) * (1 / ((N : ℝ) + 1)) = 2 / ((N : ℝ) + 1) := by ring
    rw [← h2t']
    exact wrongLayerInt_nonneg b (div_nonneg zero_le_one (by positivity))
  · filter_upwards [Filter.eventually_ge_atTop 8] with N hN
    have ht : 0 < 1 / ((N : ℝ) + 1) := by positivity
    have hN8 : (8:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
    have h2t : 2 * (1 / ((N : ℝ) + 1)) ≤ Real.pi / 4 := by
      have hN9 : (9:ℝ) ≤ (N:ℝ) + 1 := by linarith
      rw [show 2 * (1 / ((N:ℝ)+1)) = 2 / ((N:ℝ)+1) by ring]
      have h1 : 2 / ((N:ℝ)+1) ≤ 2/9 :=
        div_le_div_of_nonneg_left (by norm_num) (by norm_num) hN9
      have h2 : (2:ℝ)/9 ≤ Real.pi/4 := by nlinarith [Real.pi_gt_three]
      linarith
    have h := eta_layer_bound hsm hmem hb4 hγ.le ht h2t
    rw [show (4 * (1 / ((N : ℝ) + 1))) = 4 / ((N : ℝ) + 1) by ring,
      show (2 * (1 / ((N : ℝ) + 1))) = 2 / ((N : ℝ) + 1) by ring] at h
    exact h

end Work.FTS.GalBasis.cc
