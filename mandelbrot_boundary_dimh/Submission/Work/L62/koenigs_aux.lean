import Mathlib

/-!
# Auxiliary lemmas for the Koenigs linearisation

Standalone input facts for `Work.L62.koenigs`.
-/

namespace Work.L62

open Complex Set Metric Filter Topology

noncomputable section

/-! ## Auxiliary lemmas -/

/-- **Contraction radius from the derivative.**  If `f` is complex differentiable at `0` with
`f 0 = 0` and derivative `lam` of norm `< q`, then `f` maps a small ball into the ball of radius
`q * r`. -/
lemma norm_le_of_hasDerivAt {f : ℂ → ℂ} {lam : ℂ} (hd : HasDerivAt f lam 0) (h0 : f 0 = 0)
    {q : ℝ} (hq : ‖lam‖ < q) : ∃ r : ℝ, 0 < r ∧ ∀ z : ℂ, ‖z‖ ≤ r → ‖f z‖ ≤ q * ‖z‖ := by
  have hε : 0 < q - ‖lam‖ := sub_pos.mpr hq
  have hlit : (fun z : ℂ => f z - f 0 - (z - 0) • lam) =o[𝓝 (0 : ℂ)] fun z : ℂ => z - 0 := by
    rw [← hasDerivAt_iff_isLittleO]; exact hd
  have hb := hlit.bound hε
  rw [Metric.eventually_nhds_iff] at hb
  obtain ⟨e, he0, hb⟩ := hb
  refine ⟨e / 2, by positivity, fun z hz => ?_⟩
  have hze : dist z 0 < e := by rw [dist_eq_norm, sub_zero]; linarith
  have h1 : ‖f z - f 0 - (z - 0) • lam‖ ≤ (q - ‖lam‖) * ‖z - 0‖ := hb hze
  simp only [h0, sub_zero, smul_eq_mul] at h1
  have h4 : ‖z * lam‖ = ‖z‖ * ‖lam‖ := by rw [norm_mul, mul_comm]
  calc ‖f z‖ = ‖(f z - z * lam) + z * lam‖ := by ring_nf
    _ ≤ ‖f z - z * lam‖ + ‖z * lam‖ := norm_add_le _ _
    _ ≤ (q - ‖lam‖) * ‖z‖ + ‖z‖ * ‖lam‖ := add_le_add h1 (le_of_eq h4)
    _ = q * ‖z‖ := by ring

/-- **Iterate contraction.**  If `‖f z‖ ≤ q ‖z‖` on the closed ball of radius `r`, with
`0 ≤ q ≤ 1`, then `‖f^[n] z‖ ≤ q^n ‖z‖` for `‖z‖ ≤ r`. -/
lemma norm_iterate_le {f : ℂ → ℂ} {q r : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (h : ∀ z : ℂ, ‖z‖ ≤ r → ‖f z‖ ≤ q * ‖z‖) (n : ℕ) (z : ℂ) (hz : ‖z‖ ≤ r) :
    ‖f^[n] z‖ ≤ q ^ n * ‖z‖ := by
  induction n generalizing z with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    have hmem : ‖f^[n] z‖ ≤ r := by
      have h1 := ih z hz
      have h2 : q ^ n ≤ 1 := pow_le_one₀ hq0 hq1
      nlinarith [norm_nonneg z, norm_nonneg (f^[n] z), h1, h2, hz]
    calc ‖f (f^[n] z)‖ ≤ q * ‖f^[n] z‖ := h _ hmem
      _ ≤ q * (q ^ n * ‖z‖) := mul_le_mul_of_nonneg_left (ih z hz) hq0
      _ = q ^ (n + 1) * ‖z‖ := by ring

/-- **Second order Taylor estimate.**  If `f` is holomorphic on a neighbourhood of `0` with
`f 0 = 0` and `deriv f 0 = lam`, then `f z - lam * z = O(‖z‖²)`.  (Holomorphy of `f` on an open
set is essential: for a merely real-differentiable `f` this is false.) -/
lemma quad_bound {U : Set ℂ} (hUo : IsOpen U) (hU : U ∈ nhds (0 : ℂ))
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) (h0 : f 0 = 0) {lam : ℂ}
    (hderiv : deriv f 0 = lam) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ z in nhds (0 : ℂ), ‖f z - lam * z‖ ≤ C * ‖z‖ ^ 2 := by
  obtain ⟨p, hfps⟩ := hf.analyticAt hU
  have hp1 : (p 1) (fun _ : Fin 1 => (1 : ℂ)) = lam := by
    rw [← hderiv]
    exact (hfps.deriv).symm
  have hp1' : ∀ w : ℂ, (p 1) (fun _ : Fin 1 => w) = lam * w := by
    intro w
    have h := ContinuousMultilinearMap.map_smul_univ (p 1) (fun _ : Fin 1 => w)
      (fun _ : Fin 1 => (1 : ℂ))
    have h2 : (p 1) (fun _ : Fin 1 => w) = w * lam := by simpa [hp1] using h
    rw [h2, mul_comm]
  have hbig := hfps.isBigO_sub_partialSum_pow 2
  have hmain : (fun z : ℂ => f z - lam * z) =O[𝓝 (0 : ℂ)] fun z : ℂ => ‖z‖ ^ 2 := by
    refine hbig.congr' ?_ (Filter.EventuallyEq.rfl)
    filter_upwards with z
    rw [FormalMultilinearSeries.partialSum, Finset.sum_range_succ, Finset.sum_range_one,
      hfps.coeff_zero (fun _ : Fin 0 => z), hp1' z, h0, zero_add, zero_add]
  obtain ⟨c, hc⟩ := hmain.bound
  refine ⟨max c 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  filter_upwards [hc] with z hz
  have hz' : ‖(fun z : ℂ => ‖z‖ ^ 2) z‖ = ‖z‖ ^ 2 := Real.norm_of_nonneg (sq_nonneg ‖z‖)
  rw [hz'] at hz
  calc ‖f z - lam * z‖ ≤ c * ‖z‖ ^ 2 := hz
    _ ≤ max c 1 * ‖z‖ ^ 2 := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)

end

end Work.L62
