import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.mixed_comm
import Submission.Work.FTS.H2.IBPWeight
import Submission.Work.FTS.H2.mixed_sin_bound
import Submission.Work.FTS.H2.IbpHardEta
import Submission.Work.FTS.H2.T2SliceAux
import Submission.Work.Coercivity.sliceEtaAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## Weight algebra at the angular endpoints

For `s ≥ 0` and exponents `q` avoiding the critical values, the powers of `s` combine as in
the exponential notation (both sides vanish at `s = 0`, which is why only the non-vanishing
of the exponents has to be assumed). -/

/-- `s^{1-q}·s² = s^{3-q}` for `s ≥ 0` and `q ≠ 3`. -/
private lemma rpow_one_sub_mul_sq (s q : ℝ) (hs : 0 ≤ s) (hq : q ≠ 3) :
    s ^ (1 - q) * s ^ 2 = s ^ (3 - q) := by
  have h2 : s ^ (2 : ℝ) = s ^ 2 := Real.rpow_natCast s 2
  have hne : (1 - q) + 2 ≠ 0 := by intro h; exact hq (by linarith)
  rw [← h2, ← Real.rpow_add' (x := s) (y := 1 - q) (z := (2 : ℝ)) hs hne]
  rw [show (1 - q) + 2 = 3 - q by ring]

/-- `s^{-q}·s² = s^{2-q}` for `s ≥ 0` and `q ≠ 2`. -/
private lemma rpow_neg_mul_sq (s q : ℝ) (hs : 0 ≤ s) (hq : q ≠ 2) :
    s ^ (-q) * s ^ 2 = s ^ (2 - q) := by
  have h2 : s ^ (2 : ℝ) = s ^ 2 := Real.rpow_natCast s 2
  have hne : (-q) + 2 ≠ 0 := by intro h; exact hq (by linarith)
  rw [← h2, ← Real.rpow_add' (x := s) (y := -q) (z := (2 : ℝ)) hs hne]
  rw [show (-q) + 2 = 2 - q by ring]

/-! ## The pointwise algebra of the factorization `w = sin(2θ)·u`

The three identities below rewrite the two integrands of the integration by parts for a block
`w = D_z^j D_θ^{i'+1} g` which carries the factor `sin(2θ)` (so that `w = sin(2θ)·u` with
`u = D_z^j ∂_θ D_θ^{i'} g`), the singular weight `sin(2θ)^{-q}` being absorbed by two powers
of `sin(2θ)` coming from the two factors `w`. -/

/-- The boundary-term identity: `s^{1-q}·f·(s·u)² = s^{3-q}·f·u²`. -/
private lemma rpow_one_sub_mul_sq_factor (s q u f : ℝ) (hs : 0 ≤ s) (hq : q ≠ 3) :
    s ^ (1 - q) * (f * (s * u) ^ 2) = s ^ (3 - q) * (f * u ^ 2) := by
  have hsq := rpow_one_sub_mul_sq s q hs hq
  have h1 : s ^ (1 - q) * (f * (s * u) ^ 2) = (s ^ (1 - q) * s ^ 2) * (f * u ^ 2) := by
    rw [mul_pow]; ring
  rw [h1, hsq]

/-- The `hK`-integrand identity: `(s·u)²·K·s^{-q} = s^{2-q}·(u²·K)`. -/
private lemma sq_mul_rpow_neg_factor (s q u K : ℝ) (hs : 0 ≤ s) (hq : q ≠ 2) :
    (s * u) ^ 2 * K * s ^ (-q) = s ^ (2 - q) * (u ^ 2 * K) := by
  have hsq := rpow_neg_mul_sq s q hs hq
  have h1 : (s * u) ^ 2 * K * s ^ (-q) = (s ^ (-q) * s ^ 2) * (u ^ 2 * K) := by
    rw [mul_pow]; ring
  rw [h1, hsq]

/-- The `hint`-integrand identity:
`s^{-q}·(f·(s·p)·(s·u) + (s·u)²·K) = s^{2-q}·(f·p·u + u²·K)`. -/
private lemma rpow_neg_sum_factor (s q u f p K : ℝ) (hs : 0 ≤ s) (hq : q ≠ 2) :
    s ^ (-q) * (f * (s * p) * (s * u) + (s * u) ^ 2 * K)
      = s ^ (2 - q) * (f * p * u + u ^ 2 * K) := by
  have hsq := rpow_neg_mul_sq s q hs hq
  have h1 : s ^ (-q) * (f * (s * p) * (s * u) + (s * u) ^ 2 * K)
      = (s ^ (-q) * s ^ 2) * (f * p * u + u ^ 2 * K) := by
    rw [mul_pow]; ring
  rw [h1, hsq]

/-- The angular integration by parts for a mixed slot `D_z^j D_θ^i g` with `i ≥ 1` and the weight
`sin(2θ)^{-γ}`, `γ = gam α ∈ (1,2)`: for `z > 0`,
`∫_θ f·D_θ(D_z^jD_θ^i g)·D_z^jD_θ^i g·sin(2θ)^{-γ}
   = -∫_θ (D_z^jD_θ^i g)²·(D_θf/2 + (1-γ)cos(2θ)f)·sin(2θ)^{-γ}`.
Route: for `i ≥ 1` write `i = k+1` and use the pointwise factorization
`D_z^jD_θ^{k+1}g (z,θ) = sin(2θ)·D_z^j(∂_θD_θ^kg)(z,θ)` (`Work.Spaces.DthIter_succ` and the fact
that `D_z` only differentiates in `z`: `deriv_const_mul_field`), then apply
`Work.FTS.H2.IbpHardMixed` (the same statement for `v = sin(2θ)·u`) with
`u := D_z^j(∂_θD_θ^kg)` (smooth by `Work.Spaces.SmoothNbhd.pth`,
`Work.Spaces.smoothNbhd_DthIter`, `Work.Spaces.smoothNbhd_DzIter`) and rewrite the two
integrands with the factorization. Note: this is a repackaging of `IbpHardMixed` into exactly
the shape needed by the `T1Hard` assembly, which works with the blocks `mixed j i g` directly;
if the module `Submission/Work/FTS/H2/IbpHardMixed` is not yet present in the workspace (it is
being proved in parallel), prove the statement directly from `Work.FTS.H2.ibp_hard` by the same
route. -/
theorem IbpHardMixedBlock (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (f g : ℝ → ℝ → ℝ)
    (hsmf : Work.Spaces.SmoothNbhd f) (hsmg : Work.Spaces.SmoothNbhd g)
    (j i : ℕ) (hi : 1 ≤ i) {z : ℝ} (hz : 0 < z) :
    ∫ θ in Work.Spaces.Iθ, f z θ * Work.Spaces.Dth (Work.Spaces.mixed j i g) z θ
        * Work.Spaces.mixed j i g z θ * (Real.sin (2 * θ)) ^ (-Work.Spaces.gam α)
      = -∫ θ in Work.Spaces.Iθ, (Work.Spaces.mixed j i g z θ) ^ 2
          * (Work.Spaces.Dth f z θ / 2
            + (1 - Work.Spaces.gam α) * Real.cos (2 * θ) * f z θ)
          * (Real.sin (2 * θ)) ^ (-Work.Spaces.gam α) := by
  obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
  -- the two functions exposed by the factorization `w = sin(2θ)·u`
  set u : ℝ → ℝ → ℝ :=
    Work.Spaces.DzIter j (Work.Spaces.pth (Work.Spaces.DthIter i' g)) with hu
  set w : ℝ → ℝ → ℝ := Work.Spaces.mixed j (i' + 1) g with hw
  have hgam1 : 1 < Work.Spaces.gam α := Work.Spaces.one_lt_gam hα
  have hgam2 : Work.Spaces.gam α < 2 := by rw [Work.Spaces.gam]; linarith
  have hgam0 : 0 < Work.Spaces.gam α := lt_trans one_pos hgam1
  have hgam_ne_two : Work.Spaces.gam α ≠ 2 := by linarith
  have hgam_ne_three : Work.Spaces.gam α ≠ 3 := by linarith
  have hexp2 : (0 : ℝ) ≤ 2 - Work.Spaces.gam α := by linarith
  have hexp3 : (0 : ℝ) ≤ 3 - Work.Spaces.gam α := by linarith
  have hne3 : (3 : ℝ) - Work.Spaces.gam α ≠ 0 := by linarith
  -- the factorization and the smoothness of both factors
  have hfac : ∀ a b : ℝ, w a b = Real.sin (2 * b) * u a b := by
    intro a b
    rw [hw, hu]
    exact mixed_eq_sin_mul g j i' a b
  have hsmw : Work.Spaces.SmoothNbhd w := by
    rw [hw]
    exact Work.Spaces.smoothNbhd_mixed hsmg j (i' + 1)
  have hsmu : Work.Spaces.SmoothNbhd u := by
    rw [hu]
    exact Work.Spaces.smoothNbhd_DzIter
      (Work.Spaces.SmoothNbhd.pth (Work.Spaces.smoothNbhd_DthIter hsmg i')) j
  -- continuity of the angular slices occurring below
  have hmem0 : (0 : ℝ) ∈ Set.Ioo (-1) (π / 2 + 1) :=
    ⟨by norm_num, by linarith [Real.pi_pos]⟩
  have hmemp : (π / 2) ∈ Set.Ioo (-1) (π / 2 + 1) :=
    ⟨by linarith [Real.pi_pos], by linarith⟩
  have hcont_f : ContinuousOn (fun θ => f z θ) Work.Spaces.Iθ :=
    Work.Coercivity.slice_continuousOn f hsmf hz
  have hcont_pthf : ContinuousOn (fun θ => Work.Spaces.pth f z θ) Work.Spaces.Iθ :=
    Work.Coercivity.slice_pth_continuousOn f hsmf hz
  have hcont_u : ContinuousOn (fun θ => u z θ) Work.Spaces.Iθ :=
    Work.Coercivity.slice_continuousOn u hsmu hz
  have hcont_pthw : ContinuousOn (fun θ => Work.Spaces.pth w z θ) Work.Spaces.Iθ :=
    Work.Coercivity.slice_pth_continuousOn w hsmw hz
  have hcont_sin : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) Work.Spaces.Iθ :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
  have hcont_cos : ContinuousOn (fun θ : ℝ => Real.cos (2 * θ)) Work.Spaces.Iθ :=
    (Real.continuous_cos.comp (continuous_const.mul continuous_id)).continuousOn
  have hcont_Dthf : ContinuousOn (fun θ => Work.Spaces.Dth f z θ) Work.Spaces.Iθ :=
    hcont_sin.mul hcont_pthf
  have hcont_K : ContinuousOn (fun θ => Work.Spaces.Dth f z θ / 2
      + (1 - Work.Spaces.gam α) * Real.cos (2 * θ) * f z θ) Work.Spaces.Iθ :=
    (hcont_Dthf.div_const 2).add ((continuousOn_const.mul hcont_cos).mul hcont_f)
  have hcont_sinpow : ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
      Work.Spaces.Iθ :=
    (sin_two_rpow_continuous (2 - Work.Spaces.gam α) hexp2).continuousOn
  -- the pointwise rewritings of the integrands
  have hpt_van : ∀ θ ∈ Work.Spaces.Iθ,
      (Real.sin (2 * θ)) ^ (1 - Work.Spaces.gam α) * (f z θ * (w z θ) ^ 2)
        = (Real.sin (2 * θ)) ^ (3 - Work.Spaces.gam α) * (f z θ * (u z θ) ^ 2) := by
    intro θ hθ
    have hs : 0 ≤ Real.sin (2 * θ) := Work.Spaces.sin_two_nonneg_of_Iθ hθ
    rw [hfac z θ]
    exact rpow_one_sub_mul_sq_factor (Real.sin (2 * θ)) (Work.Spaces.gam α) (u z θ) (f z θ)
      hs hgam_ne_three
  have hpt_K : ∀ θ ∈ Work.Spaces.Iθ,
      (w z θ) ^ 2 * (Work.Spaces.Dth f z θ / 2
          + (1 - Work.Spaces.gam α) * Real.cos (2 * θ) * f z θ)
        * (Real.sin (2 * θ)) ^ (-Work.Spaces.gam α)
        = (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
          * ((u z θ) ^ 2 * (Work.Spaces.Dth f z θ / 2
              + (1 - Work.Spaces.gam α) * Real.cos (2 * θ) * f z θ)) := by
    intro θ hθ
    have hs : 0 ≤ Real.sin (2 * θ) := Work.Spaces.sin_two_nonneg_of_Iθ hθ
    rw [hfac z θ]
    exact sq_mul_rpow_neg_factor (Real.sin (2 * θ)) (Work.Spaces.gam α) (u z θ)
      (Work.Spaces.Dth f z θ / 2 + (1 - Work.Spaces.gam α) * Real.cos (2 * θ) * f z θ)
      hs hgam_ne_two
  have hpt_H : ∀ θ ∈ Work.Spaces.Iθ,
      (Real.sin (2 * θ)) ^ (-Work.Spaces.gam α)
        * (f z θ * Work.Spaces.Dth w z θ * w z θ
          + (w z θ) ^ 2 * (Work.Spaces.Dth f z θ / 2
              + (1 - Work.Spaces.gam α) * Real.cos (2 * θ) * f z θ))
        = (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
          * (f z θ * Work.Spaces.pth w z θ * u z θ
            + (u z θ) ^ 2 * (Work.Spaces.Dth f z θ / 2
              + (1 - Work.Spaces.gam α) * Real.cos (2 * θ) * f z θ)) := by
    intro θ hθ
    have hs : 0 ≤ Real.sin (2 * θ) := Work.Spaces.sin_two_nonneg_of_Iθ hθ
    rw [show Work.Spaces.Dth w z θ = Real.sin (2 * θ) * Work.Spaces.pth w z θ from rfl,
      hfac z θ]
    exact rpow_neg_sum_factor (Real.sin (2 * θ)) (Work.Spaces.gam α) (u z θ) (f z θ)
      (Work.Spaces.pth w z θ)
      (Work.Spaces.Dth f z θ / 2 + (1 - Work.Spaces.gam α) * Real.cos (2 * θ) * f z θ)
      hs hgam_ne_two
  -- the boundary terms vanish: near the endpoints the first factor is `sin(2θ)^{3-γ} → 0`
  have hLeftIθ : ∀ᶠ θ in 𝓝[>] (0 : ℝ), θ ∈ Work.Spaces.Iθ := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds (show (0 : ℝ) < π / 2 by positivity))] with θ hθ1 hθ2
    exact ⟨le_of_lt hθ1, le_of_lt hθ2⟩
  have hRightIθ : ∀ᶠ θ in 𝓝[<] (π / 2), θ ∈ Work.Spaces.Iθ := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Ioi_mem_nhds (show (0 : ℝ) < π / 2 by positivity))] with θ hθ1 hθ2
    exact ⟨le_of_lt hθ2, le_of_lt hθ1⟩
  have hvan : Filter.Tendsto (fun θ : ℝ => (Real.sin (2 * θ)) ^ (1 - Work.Spaces.gam α)
      * (f z θ * (w z θ) ^ 2)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hcont : ContinuousAt (fun θ : ℝ => (Real.sin (2 * θ)) ^ (3 - Work.Spaces.gam α)
        * (f z θ * (u z θ) ^ 2)) 0 :=
      ((sin_two_rpow_continuous (3 - Work.Spaces.gam α) hexp3).continuousAt).mul
        ((slice_continuousAt f hsmf hz hmem0).mul ((slice_continuousAt u hsmu hz hmem0).pow 2))
    have hval : (Real.sin (2 * (0 : ℝ))) ^ (3 - Work.Spaces.gam α)
        * (f z 0 * (u z 0) ^ 2) = 0 := by
      have hsin0 : Real.sin (2 * (0 : ℝ)) = 0 := by
        rw [show (2 : ℝ) * 0 = 0 by ring, Real.sin_zero]
      rw [hsin0, Real.zero_rpow hne3]; ring
    have hF : Filter.Tendsto (fun θ : ℝ => (Real.sin (2 * θ)) ^ (3 - Work.Spaces.gam α)
        * (f z θ * (u z θ) ^ 2)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have h' : Filter.Tendsto (fun θ : ℝ => (Real.sin (2 * θ)) ^ (3 - Work.Spaces.gam α)
          * (f z θ * (u z θ) ^ 2)) (𝓝 (0 : ℝ)) (𝓝 0) := by
        simpa only [hval] using hcont.tendsto
      exact h'.mono_left nhdsWithin_le_nhds
    have hev : (fun θ : ℝ => (Real.sin (2 * θ)) ^ (3 - Work.Spaces.gam α)
          * (f z θ * (u z θ) ^ 2))
        =ᶠ[𝓝[>] (0 : ℝ)]
          (fun θ : ℝ => (Real.sin (2 * θ)) ^ (1 - Work.Spaces.gam α)
            * (f z θ * (w z θ) ^ 2)) := by
      filter_upwards [hLeftIθ] with θ hθ
      exact (hpt_van θ hθ).symm
    exact Filter.Tendsto.congr' hev hF
  have hvan2 : Filter.Tendsto (fun θ : ℝ => (Real.sin (2 * θ)) ^ (1 - Work.Spaces.gam α)
      * (f z θ * (w z θ) ^ 2)) (𝓝[<] (π / 2)) (𝓝 0) := by
    have hcont : ContinuousAt (fun θ : ℝ => (Real.sin (2 * θ)) ^ (3 - Work.Spaces.gam α)
        * (f z θ * (u z θ) ^ 2)) (π / 2) :=
      ((sin_two_rpow_continuous (3 - Work.Spaces.gam α) hexp3).continuousAt).mul
        ((slice_continuousAt f hsmf hz hmemp).mul ((slice_continuousAt u hsmu hz hmemp).pow 2))
    have hval : (Real.sin (2 * (π / 2))) ^ (3 - Work.Spaces.gam α)
        * (f z (π / 2) * (u z (π / 2)) ^ 2) = 0 := by
      have hsinp : Real.sin (2 * (π / 2)) = 0 := by
        rw [show (2 : ℝ) * (π / 2) = π by ring, Real.sin_pi]
      rw [hsinp, Real.zero_rpow hne3]; ring
    have hF : Filter.Tendsto (fun θ : ℝ => (Real.sin (2 * θ)) ^ (3 - Work.Spaces.gam α)
        * (f z θ * (u z θ) ^ 2)) (𝓝[<] (π / 2)) (𝓝 0) := by
      have h' : Filter.Tendsto (fun θ : ℝ => (Real.sin (2 * θ)) ^ (3 - Work.Spaces.gam α)
          * (f z θ * (u z θ) ^ 2)) (𝓝 (π / 2)) (𝓝 0) := by
        simpa only [hval] using hcont.tendsto
      exact h'.mono_left nhdsWithin_le_nhds
    have hev : (fun θ : ℝ => (Real.sin (2 * θ)) ^ (3 - Work.Spaces.gam α)
          * (f z θ * (u z θ) ^ 2))
        =ᶠ[𝓝[<] (π / 2)]
          (fun θ : ℝ => (Real.sin (2 * θ)) ^ (1 - Work.Spaces.gam α)
            * (f z θ * (w z θ) ^ 2)) := by
      filter_upwards [hRightIθ] with θ hθ
      exact (hpt_van θ hθ).symm
    exact Filter.Tendsto.congr' hev hF
  -- the two interval-integrability hypotheses
  have hKcont : ContinuousOn (fun θ => (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
      * ((u z θ) ^ 2 * (Work.Spaces.Dth f z θ / 2
          + (1 - Work.Spaces.gam α) * Real.cos (2 * θ) * f z θ))) Work.Spaces.Iθ :=
    hcont_sinpow.mul ((hcont_u.pow 2).mul hcont_K)
  have hHcont : ContinuousOn (fun θ => (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
      * (f z θ * Work.Spaces.pth w z θ * u z θ
        + (u z θ) ^ 2 * (Work.Spaces.Dth f z θ / 2
          + (1 - Work.Spaces.gam α) * Real.cos (2 * θ) * f z θ))) Work.Spaces.Iθ :=
    hcont_sinpow.mul (((hcont_f.mul hcont_pthw).mul hcont_u).add
      ((hcont_u.pow 2).mul hcont_K))
  have hpi : (0 : ℝ) ≤ π / 2 := by positivity
  have hK : IntervalIntegrable (fun θ : ℝ => (w z θ) ^ 2 * (Work.Spaces.Dth f z θ / 2
      + (1 - Work.Spaces.gam α) * Real.cos (2 * θ) * f z θ)
      * (Real.sin (2 * θ)) ^ (-Work.Spaces.gam α)) volume 0 (π / 2) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hpi]
    exact ((ContinuousOn.integrableOn_compact isCompact_Icc hKcont).mono_set
        Set.Ioc_subset_Icc_self).congr_fun
      (fun θ hθ => (hpt_K θ (Set.Ioc_subset_Icc_self hθ)).symm) measurableSet_Ioc
  have hint : IntervalIntegrable (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-Work.Spaces.gam α)
      * (f z θ * Work.Spaces.Dth w z θ * w z θ
        + (w z θ) ^ 2 * (Work.Spaces.Dth f z θ / 2
            + (1 - Work.Spaces.gam α) * Real.cos (2 * θ) * f z θ))) volume 0 (π / 2) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hpi]
    exact ((ContinuousOn.integrableOn_compact isCompact_Icc hHcont).mono_set
        Set.Ioc_subset_Icc_self).congr_fun
      (fun θ hθ => (hpt_H θ (Set.Ioc_subset_Icc_self hθ)).symm) measurableSet_Ioc
  exact ibp_hard (Work.Spaces.gam α) f w hsmf hsmw hgam0 hgam2 hz hvan hvan2 hint hK

end Work.FTS.H2
