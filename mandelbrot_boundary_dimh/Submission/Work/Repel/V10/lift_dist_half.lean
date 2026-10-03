import Mathlib
import Submission.Work.Repel.V10.chain_v9_src

/-!
# `Work.Repel.lift_dist_half` : the explicit lift of a cell source stays in its round box

`V.lift j k n u = w_c + n + log (φ₁ u / φ₁ (u_c + k)) / (2πi)` is the explicit lift of a level-1
source `u ∈ W j + k` into the `n`-th period (`chain_v9_src`).  This file proves that it lies in the
round box `ball (w_c + n) (1/2)` used to cut out the source region `SrcC`:

  `‖lift j k n u - (w_c + n)‖ < 1/2`.

Equivalently (`‖log z / (2πi)‖ = ‖log z‖ / 2π`), `‖log (φ₁ u / φ₁ (u_c + k))‖ < π`.  Both
`u` and `u_c + k` lie in the fibre `W j + k`, which has diameter `< 1/2` (`IsChain.bounded`) and
is mapped by `φ₁` into the disc where `τ₀ ∘ φ₁ = -1/φ₁·` is within `η₁/40` of the identity
(`PertData.φ_star_close`).  Hence `φ₁ u / φ₁ (u_c + k) - 1` has modulus `≲ 1/η₁ ≪ 1/2`, and the
complex logarithm of a point in the `1/2`-ball around `1` has modulus at most `3/4 < π`
(`Complex.norm_log_one_add_half_le_self`).
-/

namespace Work.Repel

open MandelDim Complex Set Metric Filter Topology

noncomputable section

namespace V10

variable (V : V10)

/-- `Sm1 = Dsm (sgn η₁)` is contained in `Dsm η₁ ∪ Dsm (-η₁)`, the region where the `φ*`
asymptotics of `PertData` are stated. -/
theorem Sm1_sub_Dsm_union : V.Sm1 ⊆ Dsm V.η₁ ∪ Dsm (-V.η₁) := by
  intro z hz
  rw [V10.Sm1] at hz
  split at hz
  · exact Or.inl hz
  · exact Or.inr hz

/-- A point of `Sm1` has modulus at least `3η₁/4`. -/
theorem norm_ge_of_mem_Sm1 {u : ℂ} (hu : u ∈ V.Sm1) : 3 * V.η₁ / 4 ≤ ‖u‖ := by
  rw [Sm1] at hu
  split at hu
  · exact (norm_bounds_of_mem_Dsm V.hη₁pos hu).1
  · exact (norm_bounds_of_mem_Dsm_neg V.hη₁pos hu).1

/-- `τ₀ ∘ φ₁` is within `η₁/40` of the identity on `Sm1`. -/
theorem star_close_of_mem_Sm1 {u : ℂ} (hu : u ∈ V.Sm1) :
    ‖MandelDim.tau0 (V.P₁.φ u) - u‖ ≤ V.η₁ / 40 := by
  have h := V.P₁.φ_star_close u (Sm1_sub_Dsm_union V hu)
  rwa [abs_of_pos V.hη₁pos] at h

/-- The fibre `W j + k` has diameter `< 1/2`, so any two of its points are at distance `< 1/2`. -/
theorem fib_dist_lt_half {j : ℕ} {k : ℤ} {u v : ℂ} (hu : u ∈ V.fib j k) (hv : v ∈ V.fib j k) :
    ‖u - v‖ < 1 / 2 := by
  obtain ⟨u₀, hu₀, rfl⟩ := hu
  obtain ⟨v₀, hv₀, rfl⟩ := hv
  have h1 : dist u₀ v₀ ≤ Metric.diam (V.W j) :=
    Metric.dist_le_diam_of_mem (V.hIsChain.bounded j).1 hu₀ hv₀
  have h2 : dist (u₀ + ((k : ℤ) : ℂ)) (v₀ + ((k : ℤ) : ℂ)) = dist u₀ v₀ :=
    dist_add_right u₀ v₀ _
  rw [← dist_eq_norm, h2]
  linarith [(V.hIsChain.bounded j).2]

/-- The ratio of `φ₁` at two points of a fibre stays in the disc of radius `1/2` around `1`. -/
theorem phi_div_sub_one_le {j : ℕ} {k : ℤ} (hSm : V.fib j k ⊆ V.Sm1)
    {u v : ℂ} (hu : u ∈ V.fib j k) (hv : v ∈ V.fib j k) :
    ‖V.P₁.φ u / V.P₁.φ v - 1‖ ≤ 1 / 2 := by
  have ha : V.P₁.φ u ≠ 0 := phi_ne_zero_of_mem_fib V hSm hu
  have huSm : u ∈ V.Sm1 := hSm hu
  have hvSm : v ∈ V.Sm1 := hSm hv
  have hclu := star_close_of_mem_Sm1 V huSm
  have hclv := star_close_of_mem_Sm1 V hvSm
  have hnu := norm_ge_of_mem_Sm1 V huSm
  have huv : ‖u - v‖ < 1 / 2 := fib_dist_lt_half V hu hv
  -- `φ₁ x` is at distance `≤ η₁/40` from `-1/x`
  have hAu : ‖(V.P₁.φ u)⁻¹ + u‖ ≤ V.η₁ / 40 := by
    have h := hclu
    rw [MandelDim.tau0] at h
    have he : -1 / V.P₁.φ u - u = -((V.P₁.φ u)⁻¹ + u) := by
      rw [div_eq_mul_inv]; ring
    rw [he, norm_neg] at h
    exact h
  have hAv : ‖(V.P₁.φ v)⁻¹ + v‖ ≤ V.η₁ / 40 := by
    have h := hclv
    rw [MandelDim.tau0] at h
    have he : -1 / V.P₁.φ v - v = -((V.P₁.φ v)⁻¹ + v) := by
      rw [div_eq_mul_inv]; ring
    rw [he, norm_neg] at h
    exact h
  have hAnorm : 29 * V.η₁ / 40 ≤ ‖(V.P₁.φ u)⁻¹‖ := by
    have h1 : ‖u‖ ≤ ‖(V.P₁.φ u)⁻¹‖ + ‖(V.P₁.φ u)⁻¹ + u‖ := by
      calc ‖u‖ = ‖((V.P₁.φ u)⁻¹ + u) - (V.P₁.φ u)⁻¹‖ := by congr 1; ring
        _ ≤ ‖(V.P₁.φ u)⁻¹ + u‖ + ‖(V.P₁.φ u)⁻¹‖ := norm_sub_le _ _
        _ = ‖(V.P₁.φ u)⁻¹‖ + ‖(V.P₁.φ u)⁻¹ + u‖ := by ring
    linarith
  have hApos : 0 < ‖(V.P₁.φ u)⁻¹‖ := by linarith [hAnorm, V.hη₁pos]
  have hB1 : ‖((V.P₁.φ v)⁻¹ + v) - (v - u) - ((V.P₁.φ u)⁻¹ + u)‖
      ≤ ‖((V.P₁.φ v)⁻¹ + v) - (v - u)‖ + ‖(V.P₁.φ u)⁻¹ + u‖ := norm_sub_le _ _
  have hB2 : ‖((V.P₁.φ v)⁻¹ + v) - (v - u)‖ ≤ ‖(V.P₁.φ v)⁻¹ + v‖ + ‖v - u‖ :=
    norm_sub_le _ _
  have hvu : ‖v - u‖ = ‖u - v‖ := norm_sub_rev v u
  have hBdiff : ‖(V.P₁.φ v)⁻¹ - (V.P₁.φ u)⁻¹‖ ≤ V.η₁ / 20 + 1 / 2 := by
    have hsplit : (V.P₁.φ v)⁻¹ - (V.P₁.φ u)⁻¹
        = ((V.P₁.φ v)⁻¹ + v) - (v - u) - ((V.P₁.φ u)⁻¹ + u) := by ring
    rw [hsplit]
    linarith [hB1, hB2, hAv, hAu, hvu, huv]
  have hkey : V.P₁.φ u / V.P₁.φ v - 1
      = ((V.P₁.φ v)⁻¹ - (V.P₁.φ u)⁻¹) / (V.P₁.φ u)⁻¹ := by
    rw [div_eq_mul_inv, div_eq_mul_inv, inv_inv, sub_mul, inv_mul_cancel₀ ha]
    ring
  rw [hkey, norm_div]
  have hCnonneg : (0 : ℝ) ≤ V.η₁ / 20 + 1 / 2 := by linarith [V.hη₁pos]
  have hdpos : (0 : ℝ) < 29 * V.η₁ / 40 := by linarith [V.hη₁pos]
  refine le_trans (div_le_div₀ hCnonneg hBdiff hdpos hAnorm) ?_
  rw [div_le_iff₀ hdpos]
  have h64 : (64 : ℝ) ≤ V.η₁ := by nlinarith [V.hsize, V.hC₀]
  nlinarith [h64]

/-- `log (φ₁ u / φ₁ v)` has modulus `< π` for `u, v` in a common fibre. -/
theorem phi_div_log_lt_pi {j : ℕ} {k : ℤ} (hSm : V.fib j k ⊆ V.Sm1)
    {u v : ℂ} (hu : u ∈ V.fib j k) (hv : v ∈ V.fib j k) :
    ‖Complex.log (V.P₁.φ u / V.P₁.φ v)‖ < Real.pi := by
  have h1 : ‖V.P₁.φ u / V.P₁.φ v - 1‖ ≤ 1 / 2 := phi_div_sub_one_le V hSm hu hv
  have h2 : ‖Complex.log (1 + (V.P₁.φ u / V.P₁.φ v - 1))‖
      ≤ 3 / 2 * ‖V.P₁.φ u / V.P₁.φ v - 1‖ := norm_log_one_add_half_le_self h1
  have h3 : (1 : ℂ) + (V.P₁.φ u / V.P₁.φ v - 1) = V.P₁.φ u / V.P₁.φ v := by ring
  rw [h3] at h2
  linarith [h2, h1, Real.pi_gt_three]

end V10

/-- **The explicit lift lies in the round box of its period.** -/
theorem lift_dist_half (V : Work.Repel.V10) {j : ℕ} {k n : ℤ} (hSm : V.fib j k ⊆ V.Sm1)
    {u : ℂ} (hu : u ∈ V.fib j k) :
    ‖V.lift j k n u - (V.wc j k + ((n : ℤ) : ℂ))‖ < 1 / 2 := by
  have hv : V.uc j + ((k : ℤ) : ℂ) ∈ V.fib j k := V.uc_fib j k
  have hlog : ‖Complex.log (V.P₁.φ u / V.P₁.φ (V.uc j + ((k : ℤ) : ℂ)))‖ < Real.pi :=
    V10.phi_div_log_lt_pi V hSm hu hv
  rw [V10.lift]
  have hdiff : V.wc j k + ((n : ℤ) : ℂ) +
        Complex.log (V.P₁.φ u / V.P₁.φ (V.uc j + ((k : ℤ) : ℂ))) / (2 * Real.pi * Complex.I) -
        (V.wc j k + ((n : ℤ) : ℂ))
      = Complex.log (V.P₁.φ u / V.P₁.φ (V.uc j + ((k : ℤ) : ℂ))) /
        (2 * Real.pi * Complex.I) := by
    ring
  rw [hdiff, norm_div]
  have hnrm : ‖(2 * Real.pi * Complex.I : ℂ)‖ = 2 * Real.pi := by
    rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [hnrm, div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi)]
  nlinarith [hlog]

end

end Work.Repel
