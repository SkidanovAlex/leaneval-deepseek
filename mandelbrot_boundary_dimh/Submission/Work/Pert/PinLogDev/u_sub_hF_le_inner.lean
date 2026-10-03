import Mathlib
import Submission.Work.Pert.PinLogDev.u_sub_hF_le
import Submission.Work.Interfaces.Parabolic

/-!
# `Work.Pert.PinLogDev.u_sub_hF_le_inner`

Variant of `Work.Pert.PinLogDev.u_sub_hF_le` on the *inner* disk `‖z‖ ≤ ρ/2`.

For the two model germs

  `f z = z + z (z - σ) (u z)`,      `f₀ z = z + z² (hF z)`

which are `δ`-close on `closedBall 0 ρ` (`NearOn`), the difference of the model functions is

  `z² (u z - hF z) = (f z - f₀ z) + σ z (u z)`.

The right-hand side is the restriction to `ball 0 ρ` of a function `G` holomorphic on `ball 0 ρ`
(it is a combination of `f - f₀` and `σ z u z`), which is bounded by `M = δ + 2‖σ‖ρ` there
(`NearOn` on `closedBall 0 ρ ⊆ L` for `f - f₀`, and `‖u‖ ≤ 2`, `‖z‖ < ρ` for the second term).
Moreover `G 0 = 0` and, since `G w = w² (u w - hF w)` with `‖u‖ ≤ 2`, `‖hF‖ ≤ 2`,

  `‖G w‖ ≤ 4 ‖w‖²`

near the origin: `G` vanishes to order two.  The Schwarz lemma with order-two vanishing
(`norm_le_mul_ratio_sq_of_holo` below) then gives `‖G z‖ ≤ M (‖z‖/ρ)²` for *every* `z ∈ ball 0 ρ`,
and dividing by `‖z‖²` (legal for `z ≠ 0`) yields the uniform bound `‖u z - hF z‖ ≤ M/ρ²` on the
whole inner disk — no separate argument is needed for points close to the origin, which is what
makes the statement with `‖z‖ ≤ ρ/2` (rather than `ρ/2 ≤ ‖z‖`) true.  At `z = 0` the claim is the
hypothesis `‖u 0 - hF 0‖ ≤ η`.

Finally `M/ρ² = δ/ρ² + (2rr/ρ)(‖σ‖/rr) ≤ C (δ/ρ² + ‖σ‖/rr + η)` with `C = max 1 (2rr/ρ)`.

The only analytic input is the Schwarz lemma; all the rest is arithmetic, and `f₀ 0 = 0`,
`ContinuousAt hF 0` and the `η`-hypothesis are not needed for `z ≠ 0`.
-/

namespace Work.Pert.PinLogDev

open MandelDim Complex Metric Filter

noncomputable section

/-- **Schwarz lemma, order-two vanishing.**  If `g : ℂ → ℂ` is holomorphic on `ball 0 R`
(`R > 0`), is bounded by `M` there, satisfies `g 0 = 0` and `‖g w‖ ≤ K ‖w‖²` on `ball 0 R`
(with `K ≥ 0`), then `‖g z‖ ≤ M (‖z‖/R)²` for every `z ∈ ball 0 R`. -/
theorem norm_le_mul_ratio_sq_of_holo {g : ℂ → ℂ} {R M K : ℝ} (hR : 0 < R) (hK0 : 0 ≤ K)
    (hd : DifferentiableOn ℂ g (Metric.ball (0 : ℂ) R))
    (hmaps : Set.MapsTo g (Metric.ball (0 : ℂ) R) (Metric.closedBall (0 : ℂ) M))
    (h0 : g 0 = 0) (hK : ∀ w ∈ Metric.ball (0 : ℂ) R, ‖g w‖ ≤ K * ‖w‖ ^ 2) {z : ℂ}
    (hz : z ∈ Metric.ball (0 : ℂ) R) : ‖g z‖ ≤ M * (‖z‖ / R) ^ 2 := by
  -- `g` vanishes to order two at the origin, expressed as a little-o statement
  have hlit : (fun w => g w - g 0) =o[nhds (0 : ℂ)] (fun w => ‖w - 0‖ ^ 1) := by
    rw [Asymptotics.isLittleO_iff]
    intro ε hε
    have hden : 0 < K + 1 := by linarith
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hR,
      Metric.ball_mem_nhds (0 : ℂ) (show 0 < ε / (K + 1) by positivity)] with w hw hwK
    have hwK' : ‖w‖ < ε / (K + 1) := by simpa [dist_eq_norm] using hwK
    rcases eq_or_ne w 0 with rfl | hwne
    · simp [h0]
    · have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hwne
      have hKle : K * ‖w‖ ≤ ε := by
        have h1 : K * ‖w‖ ≤ K * (ε / (K + 1)) := mul_le_mul_of_nonneg_left (le_of_lt hwK') hK0
        have h2 : K * (ε / (K + 1)) ≤ ε := by
          rw [mul_div_assoc', div_le_iff₀ hden]
          nlinarith [hε.le, hK0]
        linarith
      calc ‖g w - g 0‖ = ‖g w‖ := by rw [h0, sub_zero]
        _ ≤ K * ‖w‖ ^ 2 := hK w hw
        _ = (K * ‖w‖) * ‖w‖ := by ring
        _ ≤ ε * ‖w‖ := mul_le_mul_of_nonneg_right hKle hwpos.le
        _ = ε * ‖(fun w => ‖w - 0‖ ^ 1) w‖ := by simp
  have hmaps' : Set.MapsTo g (Metric.ball (0 : ℂ) R) (Metric.closedBall (g 0) M) := by
    simpa [h0] using hmaps
  have hmain := Complex.dist_le_mul_div_pow_of_mapsTo_ball_of_isLittleO (f := g) (c := (0 : ℂ))
    (z := z) (R₁ := R) (R₂ := M) (n := 1) hd hmaps' hlit hz
  calc ‖g z‖ = dist (g z) (g 0) := by rw [dist_eq_norm, h0, sub_zero]
    _ ≤ M * (dist z 0 / R) ^ (1 + 1) := hmain
    _ = M * (‖z‖ / R) ^ 2 := by rw [dist_eq_norm, sub_zero]

theorem u_sub_hF_le_inner (rr ρ : ℝ) (hrr : 0 < rr) (hρ : 0 < ρ) (hρrr : ρ ≤ rr) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {f₀ f : ℂ → ℂ} {Df L : Set ℂ} {δ : ℝ} {σ : ℂ} {u hF : ℂ → ℂ} {η : ℝ},
      MandelDim.NearOn f₀ f Df L δ → Metric.closedBall (0 : ℂ) ρ ⊆ L →
      DifferentiableOn ℂ f₀ (Metric.ball (0 : ℂ) rr) →
      DifferentiableOn ℂ u (Metric.ball (0 : ℂ) rr) →
      (∀ z ∈ Metric.ball (0 : ℂ) rr, ‖u z‖ ≤ 2) →
      ContinuousAt hF 0 → (∀ z ∈ Metric.ball (0 : ℂ) ρ, ‖hF z‖ ≤ 2) →
      (∀ z ∈ Metric.ball (0 : ℂ) rr, f₀ z = z + z ^ 2 * hF z) →
      (∀ z ∈ Metric.ball (0 : ℂ) rr, f z = z + z * (z - σ) * u z) →
      f₀ 0 = 0 → 0 ≤ η → ‖u 0 - hF 0‖ ≤ η →
      ∀ z ∈ Metric.ball (0 : ℂ) ρ, ‖z‖ ≤ ρ / 2 →
        ‖u z - hF z‖ ≤ C * (δ / ρ ^ 2 + ‖σ‖ / rr + η) := by
  refine ⟨max 1 (2 * rr / ρ), le_trans zero_le_one (le_max_left _ _), ?_⟩
  intro f₀ f Df L δ σ u hF η hnear hL hf0d hud hu2 hhFc hhF hf₀ hf hf₀0 hη hη0 z hz hz2
  set C : ℝ := max 1 (2 * rr / ρ) with hCdef
  set M : ℝ := δ + 2 * ‖σ‖ * ρ with hMdef
  have hCpos : 0 ≤ C := le_trans zero_le_one (le_max_left _ _)
  have h0L : (0 : ℂ) ∈ L := hL (Metric.mem_closedBall.mpr (by simpa using hρ.le))
  have hδpos : 0 < δ := by
    have h := hnear.2.2.2 0 h0L
    have h' := norm_nonneg (f 0 - f₀ 0)
    linarith
  -- the defect function `G`
  set G : ℂ → ℂ := fun w => (f w - f₀ w) + σ * w * u w with hGdef
  have hGdiff : DifferentiableOn ℂ G (Metric.ball (0 : ℂ) ρ) := by
    rw [hGdef]
    refine DifferentiableOn.add (DifferentiableOn.sub ?_ ?_) ?_
    · exact hnear.2.2.1.mono (fun w hw => hnear.2.1 (hL (Metric.ball_subset_closedBall hw)))
    · exact hf0d.mono (Metric.ball_subset_ball hρrr)
    · exact DifferentiableOn.mul
        (DifferentiableOn.mul (differentiableOn_const σ) differentiableOn_id)
        (hud.mono (Metric.ball_subset_ball hρrr))
  have hG0 : G 0 = 0 := by
    have h1 : f 0 = 0 := by
      have h := hf 0 (by simp [Metric.mem_ball, hrr])
      simpa using h
    show (f 0 - f₀ 0) + σ * 0 * u 0 = 0
    rw [h1, hf₀0]
    ring
  have hGeq : ∀ w ∈ Metric.ball (0 : ℂ) rr, G w = w ^ 2 * (u w - hF w) := by
    intro w hw
    have h1 := hf w hw
    have h2 := hf₀ w hw
    show (f w - f₀ w) + σ * w * u w = w ^ 2 * (u w - hF w)
    rw [h1, h2]
    ring
  have hGM : ∀ w ∈ Metric.ball (0 : ℂ) ρ, ‖G w‖ ≤ M := by
    intro w hw
    have hwrr : w ∈ Metric.ball (0 : ℂ) rr := Metric.ball_subset_ball hρrr hw
    have hwL : w ∈ L := hL (Metric.ball_subset_closedBall hw)
    have hclose : ‖f w - f₀ w‖ ≤ δ := le_of_lt (hnear.2.2.2 w hwL)
    have hu := hu2 w hwrr
    have hwρ : ‖w‖ ≤ ρ := by
      have h := Metric.mem_ball.mp hw
      rw [dist_eq_norm, sub_zero] at h
      exact le_of_lt h
    have hσ : ‖σ * w * u w‖ ≤ 2 * ‖σ‖ * ρ := by
      rw [norm_mul, norm_mul]
      calc ‖σ‖ * ‖w‖ * ‖u w‖ ≤ ‖σ‖ * ρ * 2 :=
            mul_le_mul (mul_le_mul_of_nonneg_left hwρ (norm_nonneg σ)) hu (norm_nonneg _)
              (by positivity)
        _ = 2 * ‖σ‖ * ρ := by ring
    calc ‖G w‖ = ‖(f w - f₀ w) + σ * w * u w‖ := by rw [hGdef]
      _ ≤ ‖f w - f₀ w‖ + ‖σ * w * u w‖ := norm_add_le _ _
      _ ≤ M := by rw [hMdef]; linarith
  have hGmaps : Set.MapsTo G (Metric.ball (0 : ℂ) ρ) (Metric.closedBall (0 : ℂ) M) := by
    intro w hw
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    exact hGM w hw
  -- `G` vanishes to order two at the origin
  have hquad : ∀ w ∈ Metric.ball (0 : ℂ) ρ, ‖G w‖ ≤ 4 * ‖w‖ ^ 2 := by
    intro w hw
    have hwrr : w ∈ Metric.ball (0 : ℂ) rr := Metric.ball_subset_ball hρrr hw
    have hu := hu2 w hwrr
    have hh := hhF w hw
    have h4 : ‖u w - hF w‖ ≤ 4 := by
      calc ‖u w - hF w‖ ≤ ‖u w‖ + ‖hF w‖ := norm_sub_le _ _
        _ ≤ 4 := by linarith
    rw [hGeq w hwrr, norm_mul, norm_pow]
    calc ‖w‖ ^ 2 * ‖u w - hF w‖ ≤ ‖w‖ ^ 2 * 4 :=
          mul_le_mul_of_nonneg_left h4 (sq_nonneg ‖w‖)
      _ = 4 * ‖w‖ ^ 2 := by ring
  have hsch : ∀ z ∈ Metric.ball (0 : ℂ) ρ, ‖G z‖ ≤ M * (‖z‖ / ρ) ^ 2 := by
    intro z hz'
    exact norm_le_mul_ratio_sq_of_holo hρ (by norm_num) hGdiff hGmaps hG0 hquad hz'
  -- arithmetic in the two constants
  have harith : M / ρ ^ 2 ≤ C * (δ / ρ ^ 2 + ‖σ‖ / rr + η) := by
    have h1 : (0 : ℝ) ≤ δ / ρ ^ 2 := by positivity
    have h2 : (0 : ℝ) ≤ ‖σ‖ / rr := by positivity
    have hC1 : (1 : ℝ) ≤ C := le_max_left _ _
    have hC2 : 2 * rr / ρ ≤ C := le_max_right _ _
    have hMeq : M / ρ ^ 2 = δ / ρ ^ 2 + (2 * rr / ρ) * (‖σ‖ / rr) := by
      rw [hMdef]
      field_simp
    rw [hMeq]
    calc δ / ρ ^ 2 + (2 * rr / ρ) * (‖σ‖ / rr)
        ≤ C * (δ / ρ ^ 2) + C * (‖σ‖ / rr) :=
          add_le_add (by simpa using mul_le_mul_of_nonneg_right hC1 h1)
            (mul_le_mul_of_nonneg_right hC2 h2)
      _ = C * (δ / ρ ^ 2 + ‖σ‖ / rr) := by ring
      _ ≤ C * (δ / ρ ^ 2 + ‖σ‖ / rr + η) :=
          mul_le_mul_of_nonneg_left (by linarith) hCpos
  rcases eq_or_ne z 0 with rfl | hz0
  · -- `z = 0`: the hypothesis on `η`
    have h1 : (1 : ℝ) ≤ C := le_max_left _ _
    have hstuff : (0 : ℝ) ≤ δ / ρ ^ 2 + ‖σ‖ / rr := by positivity
    have h2 : η ≤ C * (δ / ρ ^ 2 + ‖σ‖ / rr + η) := by
      calc η = 1 * η := by ring
        _ ≤ C * η := mul_le_mul_of_nonneg_right h1 hη
        _ ≤ C * (δ / ρ ^ 2 + ‖σ‖ / rr + η) :=
            mul_le_mul_of_nonneg_left (by linarith) hCpos
    linarith
  · have hzrr : z ∈ Metric.ball (0 : ℂ) rr := Metric.ball_subset_ball hρrr hz
    have hgn : ‖G z‖ = ‖z‖ ^ 2 * ‖u z - hF z‖ := by
      rw [hGeq z hzrr, norm_mul, norm_pow]
    have hzpos : 0 < ‖z‖ ^ 2 := by positivity
    have hkey : ‖u z - hF z‖ ≤ M / ρ ^ 2 := by
      have h2 : ‖z‖ ^ 2 * ‖u z - hF z‖ ≤ ‖z‖ ^ 2 * (M / ρ ^ 2) := by
        calc ‖z‖ ^ 2 * ‖u z - hF z‖ = ‖G z‖ := hgn.symm
          _ ≤ M * (‖z‖ / ρ) ^ 2 := hsch z hz
          _ = ‖z‖ ^ 2 * (M / ρ ^ 2) := by rw [div_pow]; ring
      exact le_of_mul_le_mul_left h2 hzpos
    linarith

end

end Work.Pert.PinLogDev
