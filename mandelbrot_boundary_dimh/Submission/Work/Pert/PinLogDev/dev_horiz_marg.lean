import Mathlib
import Submission.Work.Pert.dev_base_v3
import Submission.Work.Pert.Pin3.dev_deriv_le_pt
import Submission.Work.Pert.Pin3.dev_seg_const
import Submission.Work.Interfaces.FatouNarrow

namespace Work.Pert.PinLogDev

theorem dev_horiz_marg {F Φ : ℂ → ℂ} {Ξ : ℝ} {α : ℂ} {Rde C₂ : ℝ} {a Y : ℝ}
    (hRde : 0 < Rde) (ha : a ≤ 0)
    (hDE : ∀ (Φ' v : ℂ → ℂ) (z' : ℂ) (R : ℝ), Rde ≤ R →
      DifferentiableOn ℂ Φ' (Metric.ball z' R) → Set.InjOn Φ' (Metric.ball z' R) →
      DifferentiableOn ℂ v (Metric.ball z' R) → (∀ z ∈ Metric.ball z' R, ‖v z - 1‖ < 1 / 4) →
      (∀ z ∈ Metric.ball z' R, z + v z ∈ Metric.ball z' R → Φ' (z + v z) = Φ' z + 1) →
      ‖deriv Φ' z' - 1 / v z'‖ ≤ C₂ / R)
    (hNT : MandelDim.NearTranslationL1 F (Work.Pert.Qm Ξ α))
    (hΦ : MandelDim.IsFatouCoordOn F Φ (Work.Pert.Qm Ξ α))
    (hhor : ∀ x ∈ Set.Icc a 0,
      Real.sqrt 2 * Rde ≤ Work.Pert.margA Ξ α ((x : ℂ) + (Y : ℂ) * Complex.I) ∧
      Real.sqrt 2 * Rde ≤ Work.Pert.margB Ξ α ((x : ℂ) + (Y : ℂ) * Complex.I)) :
    ‖(Φ ((Y : ℂ) * Complex.I) - (Y : ℂ) * Complex.I)
        - (Φ ((a : ℂ) + (Y : ℂ) * Complex.I) - ((a : ℂ) + (Y : ℂ) * Complex.I))‖
      ≤ (C₂ / Rde + 1 / 31) * |a| := by
  obtain ⟨hNTon, -⟩ := hNT
  obtain ⟨hFdiff, hFclose'⟩ := hNTon
  obtain ⟨hΦdiff, hΦinj, hΦrel⟩ := hΦ
  -- `F` is within `1/32` of `z ↦ z + 1` on the gate.
  have hFclose : ∀ z ∈ Qm Ξ α, ‖F z - (z + 1)‖ ≤ 1 / 32 := fun z hz => (hFclose' z hz).1
  -- The margin hypothesis along the horizontal segment gives a `Qm`-ball at every point of it.
  have hball_of : ∀ x ∈ Set.Icc a 0, Metric.ball (((x : ℂ) + (Y : ℂ) * Complex.I)) Rde ⊆ Qm Ξ α := by
    intro x hx
    obtain ⟨hA, hB⟩ := hhor x hx
    exact Work.Pert.ball_subset_Qm_of_marg_le (le_of_lt hRde) (le_min hA hB)
  have hb0 : Metric.ball ((Y : ℂ) * Complex.I) Rde ⊆ Qm Ξ α := by
    have h := hball_of 0 ⟨ha, le_refl 0⟩
    simpa using h
  -- The derivative estimate at one point of the gate forces `C₂ ≥ 0`.
  have hdiv : 0 ≤ C₂ / Rde := by
    have hvc : ∀ w ∈ Metric.ball ((Y : ℂ) * Complex.I) Rde,
        ‖(fun w : ℂ => F w - w) w - 1‖ < 1 / 4 := by
      intro w hw
      have h := hFclose w (hb0 hw)
      have h1 : F w - w - 1 = F w - (w + 1) := by ring
      rw [h1]; linarith
    have hvr : ∀ w ∈ Metric.ball ((Y : ℂ) * Complex.I) Rde,
        w + (fun w : ℂ => F w - w) w ∈ Metric.ball ((Y : ℂ) * Complex.I) Rde →
        Φ (w + (fun w : ℂ => F w - w) w) = Φ w + 1 := by
      intro w hw hwb
      have hwv : w + (F w - w) = F w := by ring
      rw [hwv] at hwb ⊢
      exact hΦrel w (hb0 hw) (hb0 hwb)
    have hres := hDE Φ (fun w : ℂ => F w - w) ((Y : ℂ) * Complex.I) Rde le_rfl
      (hΦdiff.mono hb0) (hΦinj.mono hb0) ((hFdiff.mono hb0).sub differentiableOn_id) hvc hvr
    exact le_trans (norm_nonneg _) hres
  have hΛ0 : 0 ≤ C₂ / Rde + 1 / 31 := by
    have hC2 : 0 ≤ C₂ := by
      have := (le_div_iff₀ hRde).mp hdiv
      simpa using this
    have : 0 ≤ C₂ / Rde := div_nonneg hC2 (le_of_lt hRde)
    linarith
  -- Pointwise derivative defect bound on the segment.
  have hbound : ∀ x ∈ Set.Icc a 0,
      ‖deriv Φ (((x : ℂ) + (Y : ℂ) * Complex.I)) - 1‖ ≤ C₂ / Rde + 1 / 31 := by
    intro x hx
    have hb := hball_of x hx
    have hzQ : ((x : ℂ) + (Y : ℂ) * Complex.I) ∈ Qm Ξ α := hb (Metric.mem_ball_self hRde)
    have hd := Work.Pert.Pin3.dev_deriv_le_pt (Ξ := Ξ) (β := α)
      hDE hFdiff hFclose hΦdiff hΦinj hΦrel
      (z := ((x : ℂ) + (Y : ℂ) * Complex.I)) (R := Rde) hRde le_rfl hb
    have hδ : ‖F (((x : ℂ) + (Y : ℂ) * Complex.I)) - ((((x : ℂ) + (Y : ℂ) * Complex.I)) + 1)‖
        ≤ 1 / 32 := hFclose _ hzQ
    have hstep : 32 / 31 * ‖F (((x : ℂ) + (Y : ℂ) * Complex.I))
          - ((((x : ℂ) + (Y : ℂ) * Complex.I)) + 1)‖ ≤ 1 / 31 := by
      have h2 := mul_le_mul_of_nonneg_left hδ (by norm_num : (0 : ℝ) ≤ 32 / 31)
      have h3 : (32 / 31 : ℝ) * (1 / 32) = 1 / 31 := by norm_num
      linarith
    linarith [hd, hstep]
  -- The segment `[a, 0]` at height `Y`, parametrised.
  have hz_id : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (a : ℂ) + (Y : ℂ) * Complex.I + t • ((Y : ℂ) * Complex.I - ((a : ℂ) + (Y : ℂ) * Complex.I))
        = (((a * (1 - t) : ℝ) : ℂ) + (Y : ℂ) * Complex.I) := by
    intro t ht
    rw [Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_one]
    ring
  have hxmem : ∀ t ∈ Set.Icc (0 : ℝ) 1, a * (1 - t) ∈ Set.Icc a 0 := by
    intro t ht
    refine ⟨?_, ?_⟩
    · have h1 : a * (1 - t) = a - a * t := by ring
      rw [h1]
      nlinarith [mul_nonpos_of_nonpos_of_nonneg ha ht.1]
    · nlinarith [mul_nonpos_of_nonpos_of_nonneg ha (by linarith [ht.2] : (0 : ℝ) ≤ 1 - t)]
  have hmain := Work.Pert.Pin3.dev_seg_const (Φ := Φ) (p := (a : ℂ) + (Y : ℂ) * Complex.I)
    (q := (Y : ℂ) * Complex.I) (Λ := C₂ / Rde + 1 / 31) hΛ0
    (by
      intro t ht
      rw [hz_id t ht]
      exact hΦdiff.differentiableAt
        (Filter.mem_of_superset (Metric.ball_mem_nhds _ hRde) (hball_of _ (hxmem t ht))))
    (by
      intro t ht
      rw [hz_id t ht]
      exact hbound _ (hxmem t ht))
  have hn : ‖((Y : ℂ) * Complex.I) - ((a : ℂ) + (Y : ℂ) * Complex.I)‖ = |a| := by
    have h : (Y : ℂ) * Complex.I - ((a : ℂ) + (Y : ℂ) * Complex.I) = -(a : ℂ) := by ring
    rw [h, norm_neg]
    have h2 : ‖(a : ℂ)‖ ^ 2 = a ^ 2 := by rw [Complex.sq_norm, Complex.normSq_ofReal]; ring
    have h3 := congrArg Real.sqrt h2
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq_eq_abs] at h3
  rwa [hn] at hmain

end Work.Pert.PinLogDev
