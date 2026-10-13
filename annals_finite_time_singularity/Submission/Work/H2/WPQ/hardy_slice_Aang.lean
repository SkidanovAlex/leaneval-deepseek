import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.Interval.Basic
import Submission.Work.FTS.H2.WPQ.Interior
import Submission.Work.FTS.H2.WPQ.Defs
import Submission.Work.FTS.Vocab
import Submission.Work.FTS.H2.STBasic
import Submission.Work.Spaces.HardyZ
import Submission.Work.Spaces.bt_aux
import Submission.Work.Spaces.MixedMulDefs
import Submission.Work.H2.WPQ.Dth_DzIter_comm_smoothQuad
import Submission.Work.H2.WPQ.aesm_slice_mixed_Wt_sq

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.H2.WPQ

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## `rpow` algebra on the angular interval -/

/-- `(x ^ a) ^ 2 = x ^ (2 * a)` for `x > 0`. -/
private lemma rpow_sq_pos {x a : ℝ} (hx : 0 < x) : (x ^ a) ^ 2 = x ^ (2 * a) := by
  rw [pow_two, ← Real.rpow_add hx]
  congr 1
  ring

/-- `x ^ a * x ^ b = 1` when `a + b = 0` and `x > 0`. -/
private lemma rpow_mul_rpow_eq_one {x a b : ℝ} (hx : 0 < x) (hab : a + b = 0) :
    x ^ a * x ^ b = 1 := by
  rw [← Real.rpow_add hx, hab, Real.rpow_zero]

private lemma sin_two_nonneg_Iθ' {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-! ## The angular Hardy inequality with a one-sided limit at `0`

This is the interior replacement for the private `core` of `Work.Spaces.HardyTheta`: the value
`u 0 = 0` is replaced by the one-sided limit hypothesis `u → 0` at `0⁺`.  The proof passes
through the intervals `[ε,θ]` and lets `ε → 0⁺`, so that neither continuity nor integrability
of `u'` at the endpoint `0` is ever needed. -/

/-- **The angular Hardy inequality with a one-sided limit at `0`.**  For `0 < α ≤ 1`, for
`0 < θ < π/2`, a function `u` differentiable on `(0,θ]` with derivative `u'` continuous there,
with `(u')² sin(2σ)^{2-γ}` integrable on `Iθ = [0,π/2]` (`γ = gam α = 1 + α/10`) and with
`u → 0` as `σ → 0⁺`:

  `(u θ)² ≤ (100/(γ-1)) · ∫_{Iθ} (u' σ)² sin(2σ)^{2-γ}`. -/
theorem angular_hardy_limit {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {u u' : ℝ → ℝ} {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (π / 2))
    (hderiv : ∀ σ ∈ Set.Ioc 0 θ, HasDerivAt u (u' σ) σ)
    (hu'c : ContinuousOn u' (Set.Ioc 0 θ))
    (hint : IntegrableOn (fun σ => (u' σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α))
      Work.Spaces.Iθ)
    (h0 : Tendsto u (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    (u θ) ^ 2 ≤ (100 / (Work.Spaces.gam α - 1))
      * ∫ σ in Work.Spaces.Iθ, (u' σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α) := by
  have hγ1 : 0 < Work.Spaces.gam α - 1 := by rw [Work.Spaces.gam_sub_one]; linarith
  have hγ2 : Work.Spaces.gam α ≤ 2 := by rw [Work.Spaces.gam]; linarith
  have hπ : 0 < π := Real.pi_pos
  have hθ0 : 0 < θ := hθ.1
  have hθ1 : θ < π / 2 := hθ.2
  set A : ℝ := ∫ σ in Work.Spaces.Iθ,
    (u' σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α) with hA
  have hA0 : 0 ≤ A := by
    rw [hA]
    exact setIntegral_nonneg measurableSet_Icc fun σ hσ =>
      mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg_Iθ' hσ) _)
  have hsinint : ∫ σ in Work.Spaces.Iθ, (Real.sin (2 * σ)) ^ (Work.Spaces.gam α - 2)
      ≤ 100 / (Work.Spaces.gam α - 1) := by
    have hp1 : (-1 : ℝ) < Work.Spaces.gam α - 2 := by linarith
    have hp0 : Work.Spaces.gam α - 2 ≤ 0 := by linarith
    have h := (Work.Spaces.sin_two_rpow (Work.Spaces.gam α - 2) hp1 hp0).2
    have he : (Work.Spaces.gam α - 2) + 1 = Work.Spaces.gam α - 1 := by ring
    rwa [he] at h
  -- The bound for each `ε ∈ (0,θ)`.
  have hkey : ∀ ε ∈ Set.Ioo 0 θ,
      |u θ - u ε| ≤ Real.sqrt A * Real.sqrt (100 / (Work.Spaces.gam α - 1)) := by
    intro ε hε
    have hεpos : 0 < ε := hε.1
    have hεθ : ε ≤ θ := hε.2.le
    have hsinpos : ∀ σ ∈ Set.Icc ε θ, 0 < Real.sin (2 * σ) := by
      intro σ hσ
      exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hσ.1])
        (by linarith [hσ.2, hθ1, hπ])
    have hsub : Set.Icc ε θ ⊆ Set.Ioc 0 θ := fun x hx => ⟨by linarith [hx.1], hx.2⟩
    have hcontu : ContinuousOn u (Set.Icc ε θ) := fun x hx =>
      ((hderiv x (hsub hx)).continuousAt).continuousWithinAt
    have hderiv' : ∀ x ∈ Set.Ioo ε θ, HasDerivAt u (u' x) x := fun x hx =>
      hderiv x (hsub ⟨le_of_lt hx.1, le_of_lt hx.2⟩)
    have hui : IntervalIntegrable u' volume ε θ := by
      have hc : ContinuousOn u' (Set.uIcc ε θ) := by
        rw [Set.uIcc_of_le hεθ]
        exact hu'c.mono hsub
      exact hc.intervalIntegrable
    have hFTC : ∫ σ in ε..θ, u' σ = u θ - u ε :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hεθ hcontu hderiv' hui
    -- Cauchy--Schwarz on `[ε,θ]` against the splitting of the singular weight.
    have hFc : ContinuousOn
        (fun σ => u' σ * (Real.sin (2 * σ)) ^ ((2 - Work.Spaces.gam α) / 2)) (Set.uIcc ε θ) := by
      rw [Set.uIcc_of_le hεθ]
      refine (hu'c.mono hsub).mul ?_
      exact ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn).rpow_const
        (fun σ hσ => Or.inl (ne_of_gt (hsinpos σ hσ)))
    have hGc : ContinuousOn (fun σ => (Real.sin (2 * σ)) ^ ((Work.Spaces.gam α - 2) / 2))
        (Set.uIcc ε θ) := by
      rw [Set.uIcc_of_le hεθ]
      exact ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn).rpow_const
        (fun σ hσ => Or.inl (ne_of_gt (hsinpos σ hσ)))
    have hcs := Work.Spaces.hardyZ_interval_integral_mul_le_sqrt ε θ hεθ hFc hGc
    -- Identify the three interval integrals.
    have e1 : ∫ x in ε..θ, (u' x * (Real.sin (2 * x)) ^ ((2 - Work.Spaces.gam α) / 2))
          * (Real.sin (2 * x)) ^ ((Work.Spaces.gam α - 2) / 2) = ∫ x in ε..θ, u' x := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le hεθ] at hx
      dsimp only
      have hsum : (2 - Work.Spaces.gam α) / 2 + (Work.Spaces.gam α - 2) / 2 = 0 := by ring
      rw [mul_assoc, rpow_mul_rpow_eq_one (hsinpos x hx) hsum, mul_one]
    have e2 : ∫ x in ε..θ, (u' x * (Real.sin (2 * x)) ^ ((2 - Work.Spaces.gam α) / 2)) ^ 2
        = ∫ x in ε..θ, (u' x) ^ 2 * (Real.sin (2 * x)) ^ (2 - Work.Spaces.gam α) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le hεθ] at hx
      dsimp only
      rw [mul_pow, rpow_sq_pos (hsinpos x hx)]
      congr 1
      ring
    have e3 : ∫ x in ε..θ, ((Real.sin (2 * x)) ^ ((Work.Spaces.gam α - 2) / 2)) ^ 2
        = ∫ x in ε..θ, (Real.sin (2 * x)) ^ (Work.Spaces.gam α - 2) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le hεθ] at hx
      dsimp only
      rw [rpow_sq_pos (hsinpos x hx)]
      congr 1
      ring
    -- The two bounds.
    have hsubIoc : Set.Ioc ε θ ⊆ Work.Spaces.Iθ := fun x hx =>
      ⟨le_of_lt (lt_trans hεpos hx.1), le_trans hx.2 hθ1.le⟩
    have eA : ∫ x in ε..θ, (u' x) ^ 2 * (Real.sin (2 * x)) ^ (2 - Work.Spaces.gam α) ≤ A := by
      rw [hA, intervalIntegral.integral_of_le hεθ]
      refine setIntegral_mono_set hint ?_ ?_
      · exact ae_restrict_of_forall_mem measurableSet_Icc fun σ hσ =>
          mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg_Iθ' hσ) _)
      · exact Eventually.of_forall fun x hx => hsubIoc hx
    have eB : ∫ x in ε..θ, (Real.sin (2 * x)) ^ (Work.Spaces.gam α - 2)
        ≤ 100 / (Work.Spaces.gam α - 1) := by
      have hp1 : (-1 : ℝ) < Work.Spaces.gam α - 2 := by linarith
      have hp0 : Work.Spaces.gam α - 2 ≤ 0 := by linarith
      rw [intervalIntegral.integral_of_le hεθ]
      refine le_trans (setIntegral_mono_set (Work.Spaces.sin_two_rpow _ hp1 hp0).1 ?_ ?_) hsinint
      · exact ae_restrict_of_forall_mem measurableSet_Icc fun σ hσ =>
          Real.rpow_nonneg (sin_two_nonneg_Iθ' hσ) _
      · exact Eventually.of_forall fun x hx => hsubIoc hx
    calc |u θ - u ε| = |∫ σ in ε..θ, u' σ| := by rw [hFTC]
      _ = |∫ x in ε..θ, (u' x * (Real.sin (2 * x)) ^ ((2 - Work.Spaces.gam α) / 2))
            * (Real.sin (2 * x)) ^ ((Work.Spaces.gam α - 2) / 2)| := by rw [e1]
      _ ≤ Real.sqrt (∫ x in ε..θ,
              (u' x * (Real.sin (2 * x)) ^ ((2 - Work.Spaces.gam α) / 2)) ^ 2)
            * Real.sqrt (∫ x in ε..θ,
                ((Real.sin (2 * x)) ^ ((Work.Spaces.gam α - 2) / 2)) ^ 2) := hcs
      _ = Real.sqrt (∫ x in ε..θ, (u' x) ^ 2 * (Real.sin (2 * x)) ^ (2 - Work.Spaces.gam α))
            * Real.sqrt (∫ x in ε..θ, (Real.sin (2 * x)) ^ (Work.Spaces.gam α - 2)) := by
          rw [e2, e3]
      _ ≤ Real.sqrt A * Real.sqrt (100 / (Work.Spaces.gam α - 1)) :=
          mul_le_mul (Real.sqrt_le_sqrt eA) (Real.sqrt_le_sqrt eB)
            (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  -- Let `ε → 0⁺`.
  have hlim : Tendsto (fun ε => |u θ - u ε|) (𝓝[>] (0 : ℝ)) (𝓝 |u θ|) := by
    have h1 : Tendsto (fun ε => u θ - u ε) (𝓝[>] (0 : ℝ)) (𝓝 (u θ - 0)) :=
      tendsto_const_nhds.sub h0
    simpa using h1.abs
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      |u θ - u ε| ≤ Real.sqrt A * Real.sqrt (100 / (Work.Spaces.gam α - 1)) :=
    Filter.eventually_of_mem ((nhdsGT_basis (0 : ℝ)).mem_of_mem hθ0)
      fun ε hε => hkey ε hε
  have hle : |u θ| ≤ Real.sqrt A * Real.sqrt (100 / (Work.Spaces.gam α - 1)) :=
    le_of_tendsto hlim hev
  have hsq : (u θ) ^ 2 ≤ A * (100 / (Work.Spaces.gam α - 1)) := by
    have h2 := pow_le_pow_left₀ (abs_nonneg (u θ)) hle 2
    rw [sq_abs, mul_pow, Real.sq_sqrt hA0, Real.sq_sqrt (by positivity)] at h2
    exact h2
  calc (u θ) ^ 2 ≤ A * (100 / (Work.Spaces.gam α - 1)) := hsq
    _ = (100 / (Work.Spaces.gam α - 1))
        * ∫ σ in Work.Spaces.Iθ, (u' σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α) := by
        rw [hA]; ring

/-! ## The integrability of the weighted `θ`-derivative of the `z`-slice -/

/-- For `g` smooth on the open quadrant and of class `ℋ⁴`, for `0 < α`, `z > 0` and `d ≤ 3`,
the angular function `σ ↦ (∂_θ (D_z^d g)(z,σ))² sin(2σ)^{2-γ}` is integrable on `Iθ`. -/
theorem integrableOn_pth_DzIter_sq_sin {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {g : ℝ → ℝ → ℝ}
    (hg : Work.FTS.LocData.SmoothQuad g) (hgm : Work.Spaces.HkMem α 4 g)
    {d : ℕ} (hd : d ≤ 3) {z : ℝ} (hzpos : 0 < z) :
    IntegrableOn (fun σ => (Work.Spaces.pth (Work.Spaces.DzIter d g) z σ) ^ 2
      * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)) Work.Spaces.Iθ := by
  have hzI : z ∈ Work.Spaces.Iz := Set.mem_Ici.mpr hzpos.le
  have hwne : (Work.Spaces.w z) ^ 2 ≠ 0 := by
    have h1 : Work.Spaces.w z ≠ 0 := by rw [Work.Spaces.w]; positivity
    exact pow_ne_zero 2 h1
  -- The weighted mixed slot is integrable, by domination with the `ℋ⁴`-integrand.
  have hmixed : IntegrableOn
      (fun σ => (Work.Spaces.mixed d 1 g z σ * Work.Spaces.Wt α z σ) ^ 2) Work.Spaces.Iθ := by
    refine (hgm.1 z hzI).mono' (aesm_slice_mixed_Wt_sq α g hg d 1 hzpos) ?_
    refine ae_restrict_of_forall_mem measurableSet_Icc fun σ _ => ?_
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact Work.Spaces.sq_le_HkIntegrand_mixed α 4 g z σ 1 d le_rfl (by omega)
  -- On the open quadrant the two integrands differ by the factor `(w z)²`.
  have hpt : ∀ σ ∈ Set.Ioo 0 (π / 2),
      (Work.Spaces.mixed d 1 g z σ * Work.Spaces.Wt α z σ) ^ 2 / (Work.Spaces.w z) ^ 2
        = (Work.Spaces.pth (Work.Spaces.DzIter d g) z σ) ^ 2
            * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α) := by
    intro σ hσ
    have hθI : σ ∈ Work.Spaces.Iθ := ⟨hσ.1.le, hσ.2.le⟩
    have hcomm : Work.Spaces.mixed d 1 g z σ
        = Real.sin (2 * σ) * Work.Spaces.pth (Work.Spaces.DzIter d g) z σ := by
      rw [← Dth_DzIter_comm_smoothQuad hg d hzI hσ]
      rfl
    rw [div_eq_iff hwne,
      ← Work.Spaces.bt_mixed_weight_gen α z σ hα hα1 hθI
        (Work.Spaces.pth (Work.Spaces.DzIter d g) z σ)
        (Work.Spaces.mixed d 1 g z σ) hcomm]
    ring
  have hae : (fun σ => (Work.Spaces.mixed d 1 g z σ * Work.Spaces.Wt α z σ) ^ 2
        / (Work.Spaces.w z) ^ 2)
      =ᵐ[volume.restrict Work.Spaces.Iθ]
      (fun σ => (Work.Spaces.pth (Work.Spaces.DzIter d g) z σ) ^ 2
        * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)) := by
    have h1 : ∀ᵐ σ ∂volume.restrict (Set.Ioo 0 (π / 2)),
        (Work.Spaces.mixed d 1 g z σ * Work.Spaces.Wt α z σ) ^ 2 / (Work.Spaces.w z) ^ 2
          = (Work.Spaces.pth (Work.Spaces.DzIter d g) z σ) ^ 2
              * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α) :=
      ae_restrict_of_forall_mem measurableSet_Ioo hpt
    rwa [MeasureTheory.restrict_Ioo_eq_restrict_Icc] at h1
  exact MeasureTheory.IntegrableOn.congr_fun_ae
    (hmixed.div_const ((Work.Spaces.w z) ^ 2)) hae

/-! ## The one-sided angular limit of `D_z^d g` -/

/-- The `BdryTraces` clause of order `(a,b) = (0,d)` turns into the one-sided limit
`D_z^d g(z,θ) → 0` as `θ → 0⁺`, for every `z > 0`. -/
theorem tendsto_DzIter_zero_of_BdryTraces {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {g : ℝ → ℝ → ℝ} (hbd : Work.FTS.Nonlin.BdryTraces α 4 g)
    {d : ℕ} (hd : d ≤ 3) {z : ℝ} (hzpos : 0 < z) :
    Tendsto (fun θ => Work.Spaces.DzIter d g z θ) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hγ1 : 1 < Work.Spaces.gam α := Work.Spaces.one_lt_gam hα
  obtain ⟨-, hclause⟩ := hbd 0 d (by omega)
  have hb : Tendsto (fun θ => (Real.sin (2 * θ)) ^ (1 - Work.Spaces.gam α)
      * (Work.Spaces.mixed d 0 g z θ) ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    (hclause z (Set.mem_Ioi.mpr hzpos)).1
  have hb' : Tendsto (fun θ => (Real.sin (2 * θ)) ^ (1 - Work.Spaces.gam α)
      * (Work.Spaces.DzIter d g z θ) ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using hb
  have hg : Tendsto (fun θ => (Real.sin (2 * θ)) ^ (Work.Spaces.gam α - 1))
      (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    Work.FTS.H2.tendsto_sin_rpow_zero_right (Work.Spaces.gam α - 1) (by linarith)
  have hprod : Tendsto (fun θ => (Real.sin (2 * θ)) ^ (1 - Work.Spaces.gam α)
      * (Work.Spaces.DzIter d g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (Work.Spaces.gam α - 1))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using hb'.mul hg
  have hsq : Tendsto (fun θ => (Work.Spaces.DzIter d g z θ) ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    refine hprod.congr' ?_
    filter_upwards [(nhdsGT_basis (0 : ℝ)).mem_of_mem
      (show (0 : ℝ) < π / 2 by positivity)] with θ hθ
    have hs : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
    have hsum : (1 - Work.Spaces.gam α) + (Work.Spaces.gam α - 1) = 0 := by ring
    rw [mul_comm (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)) _,
      mul_assoc, rpow_mul_rpow_eq_one hs hsum, mul_one]
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hsqrt : Tendsto (fun θ => Real.sqrt ((Work.Spaces.DzIter d g z θ) ^ 2))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa [Function.comp_def] using (Real.continuous_sqrt.tendsto 0).comp hsq
  simpa [Real.sqrt_sq_eq_abs, Real.norm_eq_abs] using hsqrt

/-! ## The interior identity between `Aang` and the `Btil`-integrand -/

/-- On the open quadrant, the `ℋ⁴`-weight `W` absorbs the angular derivative: the squared
mixed slot equals `w²` times the squared `θ`-derivative of `D_z^d g` against
`sin(2θ)^{2-γ}`. -/
theorem mixed_Wt_sq_eq_wsq_pth_sq {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {g : ℝ → ℝ → ℝ}
    (hg : Work.FTS.LocData.SmoothQuad g) {d : ℕ} {z : ℝ} (hzI : z ∈ Work.Spaces.Iz)
    {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    (Work.Spaces.mixed d 1 g z θ * Work.Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.w z) ^ 2 * ((Work.Spaces.pth (Work.Spaces.DzIter d g) z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) := by
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.1.le, hθ.2.le⟩
  have hcomm : Work.Spaces.mixed d 1 g z θ
      = Real.sin (2 * θ) * Work.Spaces.pth (Work.Spaces.DzIter d g) z θ := by
    rw [← Dth_DzIter_comm_smoothQuad hg d hzI hθ]
    rfl
  rw [← Work.Spaces.bt_mixed_weight_gen α z θ hα hα1 hθI
    (Work.Spaces.pth (Work.Spaces.DzIter d g) z θ) (Work.Spaces.mixed d 1 g z θ) hcomm]
  ring

/-- **The `Btil`-form of `Aang`**: `Aang α g d z = w(z)² · ∫_θ (∂_θ D_z^d g)² sin(2θ)^{2-γ}`. -/
theorem Aang_eq_wsq_integral {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {g : ℝ → ℝ → ℝ}
    (hg : Work.FTS.LocData.SmoothQuad g) {d : ℕ} {z : ℝ} (hzI : z ∈ Work.Spaces.Iz) :
    Work.FTS.H2.WPQ.Aang α g d z = (Work.Spaces.w z) ^ 2
      * ∫ σ in Work.Spaces.Iθ, (Work.Spaces.pth (Work.Spaces.DzIter d g) z σ) ^ 2
          * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α) := by
  rw [Work.FTS.H2.WPQ.Aang]
  have hae : (fun σ => (Work.Spaces.mixed d 1 g z σ * Work.Spaces.Wt α z σ) ^ 2)
      =ᵐ[volume.restrict Work.Spaces.Iθ]
      (fun σ => (Work.Spaces.w z) ^ 2 * ((Work.Spaces.pth (Work.Spaces.DzIter d g) z σ) ^ 2
        * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α))) := by
    have h1 : ∀ᵐ σ ∂volume.restrict (Set.Ioo 0 (π / 2)),
        (Work.Spaces.mixed d 1 g z σ * Work.Spaces.Wt α z σ) ^ 2
          = (Work.Spaces.w z) ^ 2 * ((Work.Spaces.pth (Work.Spaces.DzIter d g) z σ) ^ 2
              * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)) :=
      ae_restrict_of_forall_mem measurableSet_Ioo
        (fun σ hσ => mixed_Wt_sq_eq_wsq_pth_sq hα hα1 hg hzI hσ)
    rwa [MeasureTheory.restrict_Ioo_eq_restrict_Icc] at h1
  rw [MeasureTheory.integral_congr_ae hae, MeasureTheory.integral_const_mul]

/-- **The angular-Hardy sup bound for `D_z^d g`, in the interior class `RegQ`.**  For
`0 < α ≤ 1`, `g` smooth on the open quadrant with `g ∈ ℋ⁴` (`HkMem α 4 g`) and with the
`BdryTraces` at order `4` (which in particular makes `D_z^d g(z,θ) → 0` as `θ → 0⁺` for every
`z > 0` and `d ≤ 3`),

`(D_z^d g(z,θ) · w(z))² ≤ 100/(γ-1) · Aang α g d z`,  for `z > 0`, `0 < θ < π/2`,

where `Aang α g d z = ∫_θ (D_z^d D_θ g(z,θ)·W(z,θ))²` (`Work.FTS.H2.WPQ.Aang`, the squared
weighted angular `L²`-norm of the mixed slot).

This is the interior counterpart of `Work.Spaces.hardy_slice` (which needs `SmoothNbhd g` and
`VanishTheta g` to have `D_z^d g z 0 = 0` on the nose and phrases the conclusion with
`Work.Spaces.Btil α g d z = ∫_θ (∂_θ D_z^d g)² sin(2θ)^{2-γ}`; note `Aang = w²·Btil`).  Route:
the angular Hardy inequality applied to `D_z^d g` at fixed `z` against the weight
`sin(2σ)^{2-γ}`.  The analytic-class version is `Work.Spaces.HardyTheta` (hypotheses
`SmoothNbhd`, `g z 0 = 0`), and the interior version with a limit hypothesis has to be redone
(e.g. by the fundamental calculus identity on `[ε,θ]` and `ε → 0⁺`, using
`Work.Spaces.sin_two_rpow` for the bound `∫ sin(2σ)^{γ-2} ≤ 100/(γ-1)` and
`Work.Spaces.hardyZ_interval_integral_mul_le_sqrt` for the local Cauchy–Schwarz step) — the
hypothesis `h0 : Tendsto (D_z^d g z ·) (nhdsWithin 0 (Ioi 0)) (nhds 0)` here comes from
`BdryTraces α 4 g` (its `a = 0`, `b = d` clause says `sin(2θ)^{1-γ}(D_z^d g)² → 0`, and since
`γ > 1` the factor `sin(2θ)^{γ-1} → 0` forces `D_z^d g → 0`).  The identification
`(∂_θ (D_z^d g))² sin(2θ)^{2-γ} = (D_z^d D_θ g · W)²/w²` on the quadrant comes from the
commutation `D_θ D_z^d = D_z^d D_θ` (for the interior class: `Work.Spaces.Dz_Dth_comm` applied
to the `z`-slice, or `Work.Spaces.Dth_DzIter_comm_eqOn` for the analytic class) together with
the weight algebra `Wt² = w² sin(2θ)^{-γ}`, and the integrability of the resulting integrand
comes from `HkMem α 4 g` by domination with `Work.Spaces.sq_le_HkIntegrand_mixed`.  Note
`Work.Spaces.hardy_slice` is a good template for the whole argument. -/
theorem hardy_slice_Aang {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {g : ℝ → ℝ → ℝ} (hg : Work.FTS.LocData.SmoothQuad g) (hgm : Work.Spaces.HkMem α 4 g)
    (hbd : Work.FTS.Nonlin.BdryTraces α 4 g) {d : ℕ} (hd : d ≤ 3)
    {z θ : ℝ} (hz : z ∈ Work.Spaces.Iz) (hzpos : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    (Work.Spaces.DzIter d g z θ * Work.Spaces.w z) ^ 2
      ≤ (100 / (Work.Spaces.gam α - 1)) * Work.FTS.H2.WPQ.Aang α g d z := by
  have hγ1 : 0 < Work.Spaces.gam α - 1 := by rw [Work.Spaces.gam_sub_one]; linarith
  have hz1 : z ∈ Set.Ioi (-1 : ℝ) := Set.mem_Ioi.mpr (by linarith)
  -- The `θ`-slice of `D_z^d g` is differentiable on `(0,θ]` with derivative `∂_θ D_z^d g`.
  have hderiv : ∀ σ ∈ Set.Ioc 0 θ,
      HasDerivAt (fun σ' => Work.Spaces.DzIter d g z σ')
        (Work.Spaces.pth (Work.Spaces.DzIter d g) z σ) σ := by
    intro σ hσ
    have hσ' : σ ∈ Set.Ioo 0 (π / 2) := ⟨hσ.1, lt_of_le_of_lt hσ.2 hθ.2⟩
    have hslice : ContDiffOn ℝ Work.Stability.smoothOrder
        (fun σ' => Work.Spaces.DzIter d g z σ') (Set.Ioo 0 (π / 2)) :=
      (hg.DzIter d).curry_θ hz1
    have hdiff : DifferentiableAt ℝ (fun σ' => Work.Spaces.DzIter d g z σ') σ :=
      (hslice.differentiableOn Work.FTS.LocData.smoothOrder_ne_zero).differentiableAt
        (isOpen_Ioo.mem_nhds hσ')
    exact hdiff.hasDerivAt
  -- Continuity of `∂_θ D_z^d g` on `(0,θ]`.
  have hu'c : ContinuousOn (fun σ => Work.Spaces.pth (Work.Spaces.DzIter d g) z σ)
      (Set.Ioc 0 θ) := by
    have hquad : ContDiffOn ℝ Work.Stability.smoothOrder
        (Function.uncurry (Work.Spaces.pth (Work.Spaces.DzIter d g))) Work.Spaces.quadU :=
      Work.FTS.LocData.contDiffOn_pth Work.Spaces.isOpen_quadU (hg.DzIter d)
    have hslice : ContDiffOn ℝ Work.Stability.smoothOrder
        (fun σ => Work.Spaces.pth (Work.Spaces.DzIter d g) z σ) (Set.Ioo 0 (π / 2)) :=
      Work.FTS.LocData.contDiffOn_slice_θ hquad hz1
    exact hslice.continuousOn.mono (fun σ hσ => ⟨hσ.1, lt_of_le_of_lt hσ.2 hθ.2⟩)
  have hint := integrableOn_pth_DzIter_sq_sin hα hα1 hg hgm hd hzpos
  have hlim := tendsto_DzIter_zero_of_BdryTraces hα hα1 hbd hd hzpos
  have hHardy := angular_hardy_limit hα hα1 hθ hderiv hu'c hint hlim
  have hAA := Aang_eq_wsq_integral hα hα1 hg (d := d) hz
  have hw2 : (0 : ℝ) ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
  calc (Work.Spaces.DzIter d g z θ * Work.Spaces.w z) ^ 2
      = (Work.Spaces.DzIter d g z θ) ^ 2 * (Work.Spaces.w z) ^ 2 := by ring
    _ ≤ ((100 / (Work.Spaces.gam α - 1))
          * ∫ σ in Work.Spaces.Iθ, (Work.Spaces.pth (Work.Spaces.DzIter d g) z σ) ^ 2
              * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)) * (Work.Spaces.w z) ^ 2 :=
        mul_le_mul_of_nonneg_right hHardy hw2
    _ = (100 / (Work.Spaces.gam α - 1))
        * ((Work.Spaces.w z) ^ 2
          * ∫ σ in Work.Spaces.Iθ, (Work.Spaces.pth (Work.Spaces.DzIter d g) z σ) ^ 2
              * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)) := by ring
    _ = (100 / (Work.Spaces.gam α - 1)) * Work.FTS.H2.WPQ.Aang α g d z := by rw [← hAA]

end Work.H2.WPQ
