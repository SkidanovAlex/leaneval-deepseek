import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# `Work.LandLeaves.sqrtReduction`

The **square-root reduction** of a holomorphic germ `f` tangent to the identity:
if `f` is injective and holomorphic on the unit ball with `f 0 = 0` and `deriv f 0 = 1`, then
`z ↦ f (z ^ 2)` has a holomorphic square root `φ (z) = z * u (z ^ 2)` on the unit ball, and
`F = 1 / φ` is holomorphic and injective on the punctured unit disc, with the asymptotic
expansion
`F z = 1 / z - (iteratedDeriv 2 f 0) / 4 * z + O (‖z‖ ^ 2)`.

The construction is the classical one used in the proof of the Bieberbach bound: `f (w) / w` is
holomorphic and zero free on the ball, hence has a holomorphic square root `u` there
(`u (w) ^ 2 = f (w) / w`), and `φ (z) = z * u (z ^ 2)` is the odd square root of `z ↦ f (z ^ 2)`.
Injectivity of `φ` (and hence of `1 / φ`) follows from injectivity of `f` on the ball, and the
coefficient of `z` in `1 / φ (z)` is `-f''(0) / 4` because `u` and `f` are related by
`u (z ^ 2) ^ 2 * z ^ 2 = f (z ^ 2)`.
-/

namespace Work.LandLeaves

open Complex Metric Set Filter
open scoped Topology

noncomputable section

/-- The holomorphic extension `h` of the difference quotient `z ↦ f z / z`: for a holomorphic
`f` on the unit ball with `f 0 = 0`, the quotient extends holomorphically across `0`; if moreover
`deriv f 0 = 1` the extension takes the value `1` at `0`, is zero free on the ball and satisfies
`h z * z = f z` there. -/
theorem sqrtReduction_quotient (f : ℂ → ℂ) (hd : DifferentiableOn ℂ f (Metric.ball 0 1))
    (hf : Set.InjOn f (Metric.ball 0 1)) (h0 : f 0 = 0) (h1 : deriv f 0 = 1) :
    ∃ h : ℂ → ℂ, DifferentiableOn ℂ h (Metric.ball 0 1) ∧ h 0 = 1 ∧
      (∀ z ∈ Metric.ball 0 1, h z ≠ 0) ∧ ∀ z ∈ Metric.ball 0 1, h z * z = f z := by
  have hmem : Metric.ball (0 : ℂ) 1 ∈ 𝓝 (0 : ℂ) :=
    Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self one_pos)
  set h : ℂ → ℂ := fun z => if z = 0 then 1 else f z / z with hh
  have hh0 : h 0 = 1 := by simp [hh]
  have hdiff : DifferentiableOn ℂ h (Metric.ball 0 1) := by
    rw [← Complex.differentiableOn_compl_singleton_and_continuousAt_iff
      (s := Metric.ball 0 1) hmem]
    constructor
    · intro x hx
      have hx0 : x ≠ 0 := hx.2
      have hxd : DifferentiableAt ℂ f x :=
        hd.differentiableAt (Metric.isOpen_ball.mem_nhds hx.1)
      have hz : DifferentiableAt ℂ (fun z => f z / z) x :=
        hxd.div differentiableAt_id (by simpa using hx0)
      refine (hz.congr_of_eventuallyEq ?_).differentiableWithinAt
      filter_upwards [isOpen_ne.mem_nhds hx0] with z hz
      simp [hh, hz]
    · rw [continuousAt_iff_punctured_nhds]
      have hslope : Tendsto (slope f 0) (𝓝[≠] (0 : ℂ)) (𝓝 1) := by
        have := (hd.differentiableAt hmem).hasDerivAt
        rw [h1] at this
        exact this.tendsto_slope
      rw [hh0]
      refine hslope.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with z hz
      have hz' : z ≠ 0 := hz
      simp [hh, slope, h0, hz', div_eq_mul_inv, mul_comm]
  refine ⟨h, hdiff, hh0, ?_, ?_⟩
  · intro z hz
    rcases eq_or_ne z 0 with rfl | hz0
    · rw [hh0]; norm_num
    · simp only [hh, ite_eq_right hz0]
      exact div_ne_zero
        (fun hfz => hz0 (hf hz (Metric.mem_ball_self one_pos) (by rw [hfz, h0]))) hz0
  · intro z hz
    rcases eq_or_ne z 0 with rfl | hz0
    · simp [hh0, h0]
    · simp only [hh, ite_eq_right hz0]
      field_simp

/-- A holomorphic zero free function on the unit ball with `h 0 = 1` has a holomorphic square
root `u` with `u 0 = 1`. The proof uses the primitive of `h' / (2 h)` (the ball is a disc, hence
a holomorphic function has a primitive there) and compares `u ^ 2` with `h`. -/
theorem sqrtReduction_holoSqrt (h : ℂ → ℂ) (hd : DifferentiableOn ℂ h (Metric.ball 0 1))
    (h0 : h 0 = 1) (hne : ∀ z ∈ Metric.ball 0 1, h z ≠ 0) :
    ∃ u : ℂ → ℂ, DifferentiableOn ℂ u (Metric.ball 0 1) ∧ u 0 = 1 ∧
      ∀ z ∈ Metric.ball 0 1, u z ^ 2 = h z := by
  have hmem : Metric.ball (0 : ℂ) 1 ∈ 𝓝 (0 : ℂ) :=
    Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self one_pos)
  set k : ℂ → ℂ := fun z => deriv h z / (2 * h z) with hk
  have hkdiff : DifferentiableOn ℂ k (Metric.ball 0 1) := by
    refine (hd.deriv Metric.isOpen_ball).div (hd.const_mul 2) ?_
    intro z hz
    exact mul_ne_zero two_ne_zero (hne z hz)
  obtain ⟨K, hK0, hK⟩ := hkdiff.isExactOn_ball.with_val_at 0 0
  set u : ℂ → ℂ := fun z => Complex.exp (K z) with hu
  have hudiff : DifferentiableOn ℂ u (Metric.ball 0 1) := fun z hz =>
    ((hK z hz).cexp).differentiableAt.differentiableWithinAt
  have hu0 : u 0 = 1 := by simp [hu, hK0]
  refine ⟨u, hudiff, hu0, ?_⟩
  set Q : ℂ → ℂ := fun z => u z ^ 2 / h z with hQ
  have hQdiff : DifferentiableOn ℂ Q (Metric.ball 0 1) := (hudiff.pow 2).div hd hne
  have key : ∀ (A B D : ℂ), D ≠ 0 → (2 * A * (A * (B / (2 * D))) * D - A ^ 2 * B) / D ^ 2 = 0 := by
    intro A B D hD
    field_simp
    ring
  have hQderiv : ∀ x ∈ Metric.ball 0 1, deriv Q x = 0 := by
    intro x hx
    have hxh : DifferentiableAt ℂ h x := hd.differentiableAt (Metric.isOpen_ball.mem_nhds hx)
    have hu' : HasDerivAt u (u x * k x) x := (hK x hx).cexp
    have hnum : HasDerivAt (fun w => u w ^ 2) (2 * u x ^ (2 - 1) * (u x * k x)) x := hu'.pow 2
    have hd1 := (hnum.div hxh.hasDerivAt (hne x hx)).deriv
    change deriv ((fun w => u w ^ 2) / h) x = 0
    rw [hd1]
    have hkx : k x = deriv h x / (2 * h x) := rfl
    have hpow : u x ^ (2 - 1) = u x := by norm_num
    rw [hkx, hpow]
    exact key (u x) (deriv h x) (h x) (hne x hx)
  have hQcons : Set.EqOn Q (fun _ => (1 : ℂ)) (Metric.ball 0 1) :=
    IsOpen.eqOn_of_deriv_eq Metric.isOpen_ball (convex_ball (0 : ℂ) 1).isPreconnected
      hQdiff (differentiableOn_const 1)
      (fun x hx => by rw [deriv_const]; exact hQderiv x hx)
      (Metric.mem_ball_self one_pos) (by simp [hQ, hu0, h0])
  intro z hz
  have h1 : u z ^ 2 / h z = 1 := hQcons hz
  rwa [div_eq_one_iff_eq (hne z hz)] at h1

/-- Asymptotic expansion of `1 / (z * u (z ^ 2))`: if `u` is analytic at `0` with `u 0 = 1` and
`u (w) ^ 2 * w = f w` on the unit ball, then
`1 / (z * u (z ^ 2)) = 1 / z - (iteratedDeriv 2 f 0) / 4 * z + O (‖z‖ ^ 2)`. -/
theorem sqrtReduction_approx (f u : ℂ → ℂ) (hu : AnalyticAt ℂ u 0) (hf : AnalyticAt ℂ f 0)
    (hu0 : u 0 = 1) (hf0 : f 0 = 0) (hf1 : deriv f 0 = 1)
    (hueq : ∀ w ∈ Metric.ball 0 1, u w ^ 2 * w = f w) :
    ∃ C δ : ℝ, 0 < δ ∧ ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < δ →
      ‖(z * u (z ^ 2))⁻¹ - (1 / z + (-(iteratedDeriv 2 f 0) / 4) * z)‖ ≤ C * ‖z‖ ^ 2 := by
  obtain ⟨F3, hF3_an, hF3⟩ := hf.exists_eq_sum_add_pow_mul 3
  obtain ⟨G, hG_an, hG⟩ := hu.exists_eq_sum_add_pow_mul 2
  have hf_exp : ∀ z, f z = z + (z ^ 2 / 2) * iteratedDeriv 2 f 0 + z ^ 3 * F3 z := by
    intro z
    have h := hF3 z
    simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
    simp only [Nat.factorial_zero, Nat.factorial_one, Nat.factorial_two,
      iteratedDeriv_zero, iteratedDeriv_one, smul_eq_mul, pow_zero, pow_one, zero_add] at h
    rw [hf0, hf1, mul_one] at h
    simpa using h
  have hu_exp : ∀ z, u z = 1 + z * deriv u 0 + z ^ 2 * G z := by
    intro z
    have h := hG z
    simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
    simp only [Nat.factorial_zero, Nat.factorial_one,
      iteratedDeriv_zero, iteratedDeriv_one, smul_eq_mul, pow_zero, pow_one, zero_add] at h
    rw [hu0] at h
    simpa using h
  -- the linear coefficient of `u` is `f''(0) / 4`
  set D2 : ℂ := iteratedDeriv 2 f 0 with hD2
  set α : ℂ := deriv u 0 with hα
  have hαD : deriv u 0 = iteratedDeriv 2 f 0 / 4 := by
    have hf_exp' : ∀ z, f z = z + (z ^ 2 / 2) * D2 + z ^ 3 * F3 z := by
      intro z; rw [hD2]; exact hf_exp z
    have hu_exp' : ∀ z, u z = 1 + z * α + z ^ 2 * G z := by
      intro z; rw [hα]; exact hu_exp z
    set V : ℂ → ℂ := fun z =>
      (D2 / 2 + z ^ 2 * F3 (z ^ 2)) - (2 * α + 2 * (z ^ 2 * G (z ^ 2)) + z ^ 2 * (α + z ^ 2 * G (z ^ 2)) ^ 2)
      with hV
    have hVcont : ContinuousAt V 0 := by
      change ContinuousAt (fun z : ℂ => (D2 / 2 + z ^ 2 * F3 (z ^ 2)) -
        (2 * α + 2 * (z ^ 2 * G (z ^ 2)) + z ^ 2 * (α + z ^ 2 * G (z ^ 2)) ^ 2)) 0
      have h1 : ContinuousAt (fun z : ℂ => F3 (z ^ 2)) 0 :=
        ContinuousAt.comp (x := (0 : ℂ)) (f := fun z : ℂ => z ^ 2) (g := F3)
          (by simpa using hF3_an.continuousAt) (continuousAt_id.pow 2)
      have h2 : ContinuousAt (fun z : ℂ => G (z ^ 2)) 0 :=
        ContinuousAt.comp (x := (0 : ℂ)) (f := fun z : ℂ => z ^ 2) (g := G)
          (by simpa using hG_an.continuousAt) (continuousAt_id.pow 2)
      have hz2 : ContinuousAt (fun z : ℂ => z ^ 2) 0 := continuousAt_id.pow 2
      have hA : ContinuousAt (fun z : ℂ => z ^ 2 * F3 (z ^ 2)) 0 := hz2.mul h1
      have hB : ContinuousAt (fun z : ℂ => z ^ 2 * G (z ^ 2)) 0 := hz2.mul h2
      have hD : ContinuousAt (fun z : ℂ => α + z ^ 2 * G (z ^ 2)) 0 := continuousAt_const.add hB
      have hF : ContinuousAt (fun z : ℂ => z ^ 2 * (α + z ^ 2 * G (z ^ 2)) ^ 2) 0 :=
        hz2.mul (hD.pow 2)
      exact (continuousAt_const.add hA).sub ((continuousAt_const.add (hB.const_mul 2)).add hF)
    have hVzero : ∀ z, 0 < ‖z‖ → ‖z‖ < 1 → V z = 0 := by
      intro z hz0 hz1
      have hz2 : z ^ 2 ∈ Metric.ball 0 1 := by
        rw [Metric.mem_ball, dist_zero_right, norm_pow]
        calc ‖z‖ ^ 2 < 1 ^ 2 := by nlinarith [norm_nonneg z]
          _ = 1 := by norm_num
      have hXne : z ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mp (ne_of_gt hz0))
      have h1 := hueq (z ^ 2) hz2
      have e1 : f (z ^ 2) = z ^ 2 + ((z ^ 2) ^ 2 / 2) * D2 + (z ^ 2) ^ 3 * F3 (z ^ 2) :=
        hf_exp' (z ^ 2)
      have e2 : u (z ^ 2) = 1 + z ^ 2 * α + (z ^ 2) ^ 2 * G (z ^ 2) := hu_exp' (z ^ 2)
      have hc : (1 + z ^ 2 * α + (z ^ 2) ^ 2 * G (z ^ 2)) ^ 2
          = 1 + ((z ^ 2) / 2) * D2 + (z ^ 2) ^ 2 * F3 (z ^ 2) := by
        have h1' : (1 + z ^ 2 * α + (z ^ 2) ^ 2 * G (z ^ 2)) ^ 2 * z ^ 2
            = (1 + ((z ^ 2) / 2) * D2 + (z ^ 2) ^ 2 * F3 (z ^ 2)) * z ^ 2 := by
          have hh1 := h1
          rw [e2, e1] at hh1
          rw [hh1]; ring
        exact mul_right_cancel₀ hXne h1'
      have hz2V : z ^ 2 * V z = 0 := by
        have h1 : z ^ 2 * V z = (1 + ((z ^ 2) / 2) * D2 + (z ^ 2) ^ 2 * F3 (z ^ 2))
            - (1 + z ^ 2 * α + (z ^ 2) ^ 2 * G (z ^ 2)) ^ 2 := by
          rw [hV]; ring
        rw [h1, hc, sub_self]
      exact (mul_eq_zero.mp hz2V).resolve_left hXne
    have hV0 : V 0 = 0 := by
      have hb : Metric.ball (0 : ℂ) 1 ∈ 𝓝[≠] (0 : ℂ) :=
        mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds 0 one_pos)
      have h1 : (fun _ : ℂ => (0 : ℂ)) =ᶠ[𝓝[≠] (0 : ℂ)] V := by
        filter_upwards [self_mem_nhdsWithin, hb] with z hzne hz
        have hz1 : ‖z‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hz
        exact (hVzero z (by simpa [norm_pos_iff] using hzne) hz1).symm
      have h2 : Tendsto V (𝓝[≠] (0 : ℂ)) (𝓝 0) := Tendsto.congr' h1 tendsto_const_nhds
      have h3 : Tendsto V (𝓝[≠] (0 : ℂ)) (𝓝 (V 0)) :=
        hVcont.tendsto.mono_left nhdsWithin_le_nhds
      exact (tendsto_nhds_unique h2 h3).symm
    have hV0' : D2 / 2 - 2 * α = 0 := by
      have h := hV0
      rw [hV] at h
      simpa using h
    rw [hD2, hα] at hV0'
    linear_combination (-1 / 2) * hV0'
  -- a bound for `G` near `0`
  set M : ℝ := ‖G 0‖ + 1 with hMdef
  have hMpos : 0 < M := by rw [hMdef]; positivity
  obtain ⟨ρ, hρpos, hρ⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ∀ w : ℂ, ‖w‖ < ρ → ‖G w‖ ≤ M := by
    have hpre : G ⁻¹' (Metric.ball (G 0) 1) ∈ 𝓝 (0 : ℂ) := by
      have := hG_an.continuousAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self one_pos))
      rwa [Filter.mem_map] at this
    rw [Metric.mem_nhds_iff] at hpre
    obtain ⟨ρ, hρpos, hρ⟩ := hpre
    refine ⟨ρ, hρpos, fun w hw => ?_⟩
    have h1 : G w ∈ Metric.ball (G 0) 1 := hρ (by rw [Metric.mem_ball, dist_zero_right]; exact hw)
    rw [Metric.mem_ball, dist_eq_norm] at h1
    have h2 := norm_add_le (G 0) (G w - G 0)
    rw [add_sub_cancel] at h2
    rw [hMdef]
    linarith
  set K : ℝ := ‖deriv u 0‖ + M with hKdef
  have hKnonneg : 0 ≤ K := by rw [hKdef]; linarith [norm_nonneg (deriv u 0), hMpos]
  set δ : ℝ := min 1 (min ρ (1 / (2 * (K + 1)))) with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]
    exact lt_min one_pos (lt_min hρpos (by positivity))
  refine ⟨2 * (‖deriv u 0‖ * K + M), δ, hδpos, ?_⟩
  intro z hz0 hzδ
  have hz0' : z ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt hz0)
  have hz1 : ‖z‖ < 1 := lt_of_lt_of_le hzδ (min_le_left _ _)
  have hzρ : ‖z‖ < ρ := lt_of_lt_of_le hzδ (le_trans (min_le_right _ _) (min_le_left _ _))
  have hδle : δ ≤ 1 / (2 * (K + 1)) := le_trans (min_le_right _ _) (min_le_right _ _)
  have hGz : ‖G (z ^ 2)‖ ≤ M := by
    apply hρ
    rw [norm_pow]
    calc ‖z‖ ^ 2 ≤ ‖z‖ := by nlinarith [norm_nonneg z, hz1]
      _ < ρ := hzρ
  have hzsq : ‖z‖ ^ 2 < 1 / (2 * (K + 1)) := by
    have h2 : 0 < K + 1 := by linarith
    nlinarith [norm_nonneg z, hz1, hzδ, hδle, h2]
  set W : ℂ := z ^ 2 * deriv u 0 + (z ^ 2) ^ 2 * G (z ^ 2) with hWdef
  have hWb : ‖W‖ ≤ K * ‖z‖ ^ 2 := by
    have h4 : (‖z‖ ^ 2) ^ 2 ≤ ‖z‖ ^ 2 := by
      have h1 : ‖z‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg z, hz1]
      calc (‖z‖ ^ 2) ^ 2 = ‖z‖ ^ 2 * ‖z‖ ^ 2 := by ring
        _ ≤ ‖z‖ ^ 2 := mul_le_of_le_one_right (sq_nonneg _) h1
    calc ‖W‖ = ‖z ^ 2 * deriv u 0 + (z ^ 2) ^ 2 * G (z ^ 2)‖ := by rw [hWdef]
      _ ≤ ‖z ^ 2 * deriv u 0‖ + ‖(z ^ 2) ^ 2 * G (z ^ 2)‖ := norm_add_le _ _
      _ = ‖z‖ ^ 2 * ‖deriv u 0‖ + (‖z‖ ^ 2) ^ 2 * ‖G (z ^ 2)‖ := by
            simp only [norm_mul, norm_pow]
      _ ≤ ‖z‖ ^ 2 * ‖deriv u 0‖ + ‖z‖ ^ 2 * M :=
            add_le_add le_rfl (mul_le_mul h4 hGz (norm_nonneg _) (sq_nonneg _))
      _ = K * ‖z‖ ^ 2 := by rw [hKdef]; ring
  have hWlt : ‖W‖ < 1 / 2 := by
    have h2 : K * ‖z‖ ^ 2 < K * (1 / (2 * (K + 1))) := by
      have hc : 0 < K := by rw [hKdef]; linarith [norm_nonneg (deriv u 0), hMpos]
      nlinarith [hzsq, hc]
    have h3 : K * (1 / (2 * (K + 1))) < 1 / 2 := by
      rw [mul_one_div, div_lt_iff₀ (by linarith : (0 : ℝ) < 2 * (K + 1))]
      nlinarith [hKnonneg]
    linarith [hWb, h2, h3]
  have h1W : (1 : ℝ) / 2 ≤ ‖1 + W‖ := by
    have h := norm_add_le (1 + W) (-W)
    have h1 : 1 + W + -W = 1 := by ring
    rw [h1, norm_one, norm_neg] at h
    linarith
  have hWne : 1 + W ≠ 0 := by
    intro h
    rw [h, norm_zero] at h1W
    norm_num at h1W
  have huW : u (z ^ 2) = 1 + W := by rw [hu_exp (z ^ 2), hWdef]; ring
  have hid : (z * u (z ^ 2))⁻¹ - (1 / z + (-(iteratedDeriv 2 f 0) / 4) * z)
      = z * (deriv u 0 * W - z ^ 2 * G (z ^ 2)) * (1 + W)⁻¹ := by
    have hc : (-(iteratedDeriv 2 f 0) / 4) = -(deriv u 0) := by rw [hαD]; ring
    have key : z * (1 + W) * ((z * (1 + W))⁻¹ - (z⁻¹ + (-(deriv u 0)) * z))
        = z * (1 + W) * (z * (deriv u 0 * W - z ^ 2 * G (z ^ 2)) * (1 + W)⁻¹) := by
      field_simp [hz0', hWne]
      ring
    have hcan : (z * (1 + W))⁻¹ - (z⁻¹ + (-(deriv u 0)) * z)
        = z * (deriv u 0 * W - z ^ 2 * G (z ^ 2)) * (1 + W)⁻¹ :=
      mul_left_cancel₀ (mul_ne_zero hz0' hWne) key
    rw [hc, huW]
    simpa using hcan
  have hnum : ‖deriv u 0 * W - z ^ 2 * G (z ^ 2)‖ ≤ (‖deriv u 0‖ * K + M) * ‖z‖ ^ 2 := by
    calc ‖deriv u 0 * W - z ^ 2 * G (z ^ 2)‖ ≤ ‖deriv u 0 * W‖ + ‖z ^ 2 * G (z ^ 2)‖ :=
          norm_sub_le _ _
      _ = ‖deriv u 0‖ * ‖W‖ + ‖z‖ ^ 2 * ‖G (z ^ 2)‖ := by simp only [norm_mul, norm_pow]
      _ ≤ ‖deriv u 0‖ * (K * ‖z‖ ^ 2) + ‖z‖ ^ 2 * M :=
            add_le_add (mul_le_mul_of_nonneg_left hWb (norm_nonneg _))
              (mul_le_mul_of_nonneg_left hGz (sq_nonneg _))
      _ = (‖deriv u 0‖ * K + M) * ‖z‖ ^ 2 := by ring
  have hinv : ‖(1 + W)⁻¹‖ ≤ 2 := by
    rw [norm_inv]
    have hpos : (0 : ℝ) < ‖1 + W‖ := by linarith
    have hmul : ‖1 + W‖ * (‖1 + W‖)⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hpos)
    nlinarith [h1W, hmul, hpos]
  rw [hid, norm_mul, norm_mul]
  calc ‖z‖ * ‖deriv u 0 * W - z ^ 2 * G (z ^ 2)‖ * ‖(1 + W)⁻¹‖
      ≤ ‖z‖ * ((‖deriv u 0‖ * K + M) * ‖z‖ ^ 2) * 2 := by gcongr
    _ = 2 * (‖deriv u 0‖ * K + M) * ‖z‖ ^ 3 := by ring
    _ ≤ 2 * (‖deriv u 0‖ * K + M) * ‖z‖ ^ 2 := by
        have h3 : ‖z‖ ^ 3 ≤ ‖z‖ ^ 2 := by nlinarith [norm_nonneg z, hz1]
        have hc0 : (0 : ℝ) ≤ 2 * (‖deriv u 0‖ * K + M) := by
          nlinarith [norm_nonneg (deriv u 0), hKnonneg, hMpos]
        nlinarith [h3, hc0]

/-- **The square-root reduction.** For a holomorphic injection `f` on the unit ball with
`f 0 = 0` and `deriv f 0 = 1`, there is a holomorphic injection `F` on the punctured unit disc
with `F z = 1 / z - (iteratedDeriv 2 f 0) / 4 * z + O (‖z‖ ^ 2)`. -/
theorem sqrtReduction (f : ℂ → ℂ) (hd : DifferentiableOn ℂ f (Metric.ball 0 1))
    (hf : Set.InjOn f (Metric.ball 0 1)) (h0 : f 0 = 0) (h1 : deriv f 0 = 1) :
    ∃ F : ℂ → ℂ, DifferentiableOn ℂ F {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < 1} ∧
      Set.InjOn F {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < 1} ∧
      ∃ C δ : ℝ, 0 < δ ∧ ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < δ →
        ‖F z - (1 / z + (-(iteratedDeriv 2 f 0) / 4) * z)‖ ≤ C * ‖z‖ ^ 2 := by
  obtain ⟨h, hdh, hh0, hhne, hhmul⟩ := sqrtReduction_quotient f hd hf h0 h1
  obtain ⟨u, hdu, hu0, hueq⟩ := sqrtReduction_holoSqrt h hdh hh0 hhne
  have hune : ∀ z ∈ Metric.ball 0 1, u z ≠ 0 := by
    intro z hz hzu
    have h1 := hueq z hz
    rw [hzu] at h1
    simp at h1
    exact hhne z hz h1.symm
  have sqmem : ∀ z : ℂ, ‖z‖ < 1 → z ^ 2 ∈ Metric.ball 0 1 := by
    intro z hz
    rw [Metric.mem_ball, dist_zero_right, norm_pow]
    calc ‖z‖ ^ 2 < 1 ^ 2 := by nlinarith [norm_nonneg z]
      _ = 1 := by norm_num
  have hmem : Metric.ball (0 : ℂ) 1 ∈ 𝓝 (0 : ℂ) :=
    Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self one_pos)
  refine ⟨fun z => (z * u (z ^ 2))⁻¹, ?_, ?_, ?_⟩
  · intro z hz
    have hz0 : z ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt hz.1)
    have hz2 : z ^ 2 ∈ Metric.ball 0 1 := sqmem z hz.2
    have huz : DifferentiableAt ℂ u (z ^ 2) :=
      hdu.differentiableAt (Metric.isOpen_ball.mem_nhds hz2)
    have hzu : DifferentiableAt ℂ (fun w => w * u (w ^ 2)) z :=
      differentiableAt_id.mul (huz.comp z (differentiableAt_id.pow 2))
    have hne : z * u (z ^ 2) ≠ 0 := mul_ne_zero hz0 (hune (z ^ 2) hz2)
    exact (hzu.inv hne).differentiableWithinAt
  · intro a ha b hb hab
    have ha0 : a ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt ha.1)
    have ha2 : a ^ 2 ∈ Metric.ball 0 1 := sqmem a ha.2
    have hb2 : b ^ 2 ∈ Metric.ball 0 1 := sqmem b hb.2
    have hphi : a * u (a ^ 2) = b * u (b ^ 2) := inv_inj.mp hab
    have hfa : (a * u (a ^ 2)) ^ 2 = f (a ^ 2) := by
      calc (a * u (a ^ 2)) ^ 2 = a ^ 2 * (u (a ^ 2)) ^ 2 := by ring
        _ = a ^ 2 * h (a ^ 2) := by rw [hueq (a ^ 2) ha2]
        _ = f (a ^ 2) := by rw [mul_comm, hhmul (a ^ 2) ha2]
    have hfb : (b * u (b ^ 2)) ^ 2 = f (b ^ 2) := by
      calc (b * u (b ^ 2)) ^ 2 = b ^ 2 * (u (b ^ 2)) ^ 2 := by ring
        _ = b ^ 2 * h (b ^ 2) := by rw [hueq (b ^ 2) hb2]
        _ = f (b ^ 2) := by rw [mul_comm, hhmul (b ^ 2) hb2]
    have hsq : a ^ 2 = b ^ 2 := hf ha2 hb2 (by rw [← hfa, ← hfb, hphi])
    have hfac : (a - b) * (a + b) = 0 := by
      have : (a - b) * (a + b) = a ^ 2 - b ^ 2 := by ring
      rw [this, hsq, sub_self]
    rcases mul_eq_zero.mp hfac with h' | h'
    · exact sub_eq_zero.mp h'
    · exfalso
      have hba : b = -a := eq_neg_of_add_eq_zero_right h'
      have hne : a * u (a ^ 2) ≠ 0 := mul_ne_zero ha0 (hune (a ^ 2) ha2)
      have hneg : a * u (a ^ 2) = -(a * u (a ^ 2)) := by
        have h2 := hphi
        rw [hba, neg_sq, neg_mul] at h2
        exact h2
      have hzero : a * u (a ^ 2) = 0 := by
        have h2 : a * u (a ^ 2) + a * u (a ^ 2) = 0 := by
          nth_rewrite 2 [hneg]; ring
        rw [← two_mul] at h2
        exact (mul_eq_zero.mp h2).resolve_left (by norm_num)
      exact hne hzero
  · have hu_an : AnalyticAt ℂ u 0 := hdu.analyticAt hmem
    have hf_an : AnalyticAt ℂ f 0 := hd.analyticAt hmem
    have hueq' : ∀ w ∈ Metric.ball 0 1, u w ^ 2 * w = f w := by
      intro w hw
      rw [hueq w hw, hhmul w hw]
    exact sqrtReduction_approx f u hu_an hf_an hu0 h0 h1 hueq'

end

end Work.LandLeaves
