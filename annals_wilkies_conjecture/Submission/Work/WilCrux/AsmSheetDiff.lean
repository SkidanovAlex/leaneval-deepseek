import Mathlib
import Submission.Work.WilCrux.C1AsmDefs

set_option autoImplicit false
noncomputable section
open Classical
open scoped Topology
open Filter

namespace Work.WilCrux

/-- `famFun` reads a family member through the two coordinate blocks. -/
theorem famFun_parProj_fibProj {a b : ℕ} (G : (Fin a → ℝ) → (Fin b → ℝ) → ℝ)
    (v : Fin (a + b) → ℝ) :
    Work.WilG4c.famFun G v = G (parProj a b v) (fibProj a b v) := rfl

/-- **The fibre-direction estimate at a sheet point.**

For `w` in the open set `Q6`, the map `δ ↦ G (w + parProj δ) (fibProj δ) - G (w + parProj δ) 0`
is `o(‖δ‖)` at `δ = 0`, with respect to the linear functional `fderiv ℝ (G w) 0` on the fibre
block.  This is the elementary estimate underlying the differentiability of `famFun G` at the
sheet point `Fin.append w 0`. -/
theorem fiberSheet_eventually {a b : ℕ} (G : (Fin a → ℝ) → (Fin b → ℝ) → ℝ)
    (Q6 : Set (Fin a → ℝ)) (hQ6 : IsOpen Q6) (r0 : ℝ) (hr0 : 0 < r0)
    (hsl : ∀ w ∈ Q6, ContDiffOn ℝ 1 (G w) (Metric.ball 0 r0))
    (hz : ∀ w₀ ∈ Q6, ∀ ε > 0, ∃ η > 0, ∀ (w : Fin a → ℝ) (z : Fin b → ℝ),
      dist w w₀ < η → z ≠ 0 → ‖z‖ < η → ‖fderiv ℝ (G w) z - fderiv ℝ (G w) 0‖ < ε)
    (hb : ∀ w ∈ Q6, ContinuousWithinAt (fun w' => fderiv ℝ (G w') 0) Q6 w)
    {w : Fin a → ℝ} (hw : w ∈ Q6) :
    (fun δ : Fin (a + b) → ℝ =>
        G (w + parProj a b δ) (fibProj a b δ) - G (w + parProj a b δ) 0
          - (fderiv ℝ (G w) 0) (fibProj a b δ)) =o[𝓝 0] (fun δ => δ) := by
  refine Asymptotics.IsLittleO.of_bound (fun c hc => ?_)
  -- the modulus `c/4` for both the slice-derivative continuity and the continuity of `b`
  obtain ⟨η1, hη1pos, hη1⟩ := hz w hw (c / 4) (by linarith)
  obtain ⟨η2, hη2pos, hη2⟩ :=
    (Metric.continuousWithinAt_iff.mp (hb w hw)) (c / 4) (by linarith)
  obtain ⟨η3, hη3pos, hη3⟩ := Metric.mem_nhds_iff.mp (hQ6.mem_nhds hw)
  let η : ℝ := min (min η1 η2) (min η3 r0)
  have hηpos : 0 < η := lt_min (lt_min hη1pos hη2pos) (lt_min hη3pos hr0)
  have hη1' : η ≤ η1 := le_trans (min_le_left _ _) (min_le_left _ _)
  have hη2' : η ≤ η2 := le_trans (min_le_left _ _) (min_le_right _ _)
  have hη3' : η ≤ η3 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hηr0 : η ≤ r0 := le_trans (min_le_right _ _) (min_le_right _ _)
  refine Filter.eventually_of_mem (Metric.ball_mem_nhds 0 hηpos) (fun δ hδ => ?_)
  have hδn : ‖δ‖ < η := by simpa [Metric.mem_ball, dist_eq_norm, sub_zero] using hδ
  have hhn : ‖parProj a b δ‖ < η := lt_of_le_of_lt (norm_parProj_le a b δ) hδn
  have hzn : ‖fibProj a b δ‖ < η := lt_of_le_of_lt (norm_fibProj_le a b δ) hδn
  have hwm : w + parProj a b δ ∈ Q6 := by
    apply hη3
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
    exact lt_of_lt_of_le hhn hη3'
  have hdist1 : dist (w + parProj a b δ) w < η1 := by
    rw [dist_eq_norm, add_sub_cancel_left]
    exact lt_of_lt_of_le hhn hη1'
  have hdist2 : dist (w + parProj a b δ) w < η2 := by
    rw [dist_eq_norm, add_sub_cancel_left]
    exact lt_of_lt_of_le hhn hη2'
  -- differentiability of the slice `G (w + h)` on the segment `[0, fibProj δ]`
  have hdiff : ∀ x ∈ segment ℝ 0 (fibProj a b δ),
      DifferentiableAt ℝ (G (w + parProj a b δ)) x := by
    intro x hx
    rw [segment_eq_image_lineMap] at hx
    obtain ⟨t, ht, ht_eq⟩ := hx
    rw [← ht_eq]
    have hnorm : ‖AffineMap.lineMap (0 : Fin b → ℝ) (fibProj a b δ) t‖ < r0 := by
      rw [AffineMap.lineMap_apply_module]
      simp only [smul_zero, zero_add]
      rw [norm_smul_of_nonneg ht.1]
      calc t * ‖fibProj a b δ‖ ≤ 1 * ‖fibProj a b δ‖ :=
            mul_le_mul_of_nonneg_right ht.2 (norm_nonneg _)
        _ = ‖fibProj a b δ‖ := one_mul _
        _ < r0 := lt_of_lt_of_le hzn hηr0
    have hmem : AffineMap.lineMap (0 : Fin b → ℝ) (fibProj a b δ) t ∈ Metric.ball 0 r0 := by
      rw [Metric.mem_ball, dist_eq_norm, sub_zero]
      exact hnorm
    exact ((hsl (w + parProj a b δ) hwm).contDiffAt
      (Metric.isOpen_ball.mem_nhds hmem)).differentiableAt (by norm_num)
  -- the derivative bound on the segment
  have hbound : ∀ x ∈ segment ℝ 0 (fibProj a b δ),
      ‖fderiv ℝ (G (w + parProj a b δ)) x - fderiv ℝ (G w) 0‖ ≤ c / 2 := by
    intro x hx
    rw [segment_eq_image_lineMap] at hx
    obtain ⟨t, ht, ht_eq⟩ := hx
    have hxnorm : ‖x‖ < η1 := by
      rw [← ht_eq, AffineMap.lineMap_apply_module]
      simp only [smul_zero, zero_add]
      rw [norm_smul_of_nonneg ht.1]
      calc t * ‖fibProj a b δ‖ ≤ 1 * ‖fibProj a b δ‖ :=
            mul_le_mul_of_nonneg_right ht.2 (norm_nonneg _)
        _ = ‖fibProj a b δ‖ := one_mul _
        _ < η1 := lt_of_lt_of_le hzn hη1'
    have hbnd : ‖fderiv ℝ (G (w + parProj a b δ)) 0 - fderiv ℝ (G w) 0‖ < c / 4 := by
      have h := hη2 (show w + parProj a b δ ∈ Q6 from hwm) hdist2
      simpa [dist_eq_norm] using h
    by_cases hx0 : x = 0
    · rw [hx0]
      have : ‖fderiv ℝ (G (w + parProj a b δ)) 0 - fderiv ℝ (G w) 0‖ ≤ c / 4 := le_of_lt hbnd
      linarith
    · have h1 : ‖fderiv ℝ (G (w + parProj a b δ)) x
            - fderiv ℝ (G (w + parProj a b δ)) 0‖ < c / 4 :=
        hη1 (w + parProj a b δ) x hdist1 hx0 hxnorm
      have hstep := dist_triangle (fderiv ℝ (G (w + parProj a b δ)) x)
        (fderiv ℝ (G (w + parProj a b δ)) 0) (fderiv ℝ (G w) 0)
      rw [dist_eq_norm, dist_eq_norm, dist_eq_norm] at hstep
      linarith
  have hmain := Convex.norm_image_sub_le_of_norm_fderiv_le'
      (s := segment ℝ 0 (fibProj a b δ)) (φ := fderiv ℝ (G w) 0) (C := c / 2)
      hdiff hbound (convex_segment _ _) (left_mem_segment ℝ 0 _) (right_mem_segment ℝ 0 _)
  rw [sub_zero] at hmain
  calc ‖G (w + parProj a b δ) (fibProj a b δ) - G (w + parProj a b δ) 0
          - (fderiv ℝ (G w) 0) (fibProj a b δ)‖
      ≤ (c / 2) * ‖fibProj a b δ‖ := hmain
    _ ≤ (c / 2) * ‖δ‖ := mul_le_mul_of_nonneg_left (norm_fibProj_le a b δ) (by linarith)
    _ ≤ c * ‖δ‖ := mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)

theorem AsmSheetDiff {a b : ℕ} (G : (Fin a → ℝ) → (Fin b → ℝ) → ℝ)
    (Q6 : Set (Fin a → ℝ)) (hQ6 : IsOpen Q6) (r0 : ℝ) (hr0 : 0 < r0)
    (hsl : ∀ w ∈ Q6, ContDiffOn ℝ 1 (G w) (Metric.ball 0 r0))
    (ha : ContDiffOn ℝ 1 (fun w => G w 0) Q6)
    (hz : ∀ w₀ ∈ Q6, ∀ ε > 0, ∃ η > 0, ∀ (w : Fin a → ℝ) (z : Fin b → ℝ),
      dist w w₀ < η → z ≠ 0 → ‖z‖ < η → ‖fderiv ℝ (G w) z - fderiv ℝ (G w) 0‖ < ε)
    (hb : ∀ w ∈ Q6, ContinuousWithinAt (fun w' => fderiv ℝ (G w') 0) Q6 w) :
    ∀ w ∈ Q6, HasFDerivAt (Work.WilG4c.famFun G)
      (pairCLM a b (fderiv ℝ (fun w' => G w' 0) w) (fderiv ℝ (G w) 0))
      (Fin.append w 0) := by
  intro w hw
  set φ : (Fin a → ℝ) →L[ℝ] ℝ := fderiv ℝ (fun w' => G w' 0) w with hφ
  set ψ : (Fin b → ℝ) →L[ℝ] ℝ := fderiv ℝ (G w) 0 with hψ
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  -- the parameter-direction part
  have hG0 : HasFDerivAt (fun w' => G w' 0) φ w := by
    rw [hφ]
    exact ((ha.contDiffAt (hQ6.mem_nhds hw)).differentiableAt (by norm_num)).hasFDerivAt
  have hAff : HasFDerivAt (fun δ : Fin (a + b) → ℝ => w + parProj a b δ) (parProj a b) 0 :=
    (ContinuousLinearMap.hasFDerivAt (parProj a b)).const_add w
  have hG0' : HasFDerivAt (fun w' => G w' 0) φ
      ((fun δ : Fin (a + b) → ℝ => w + parProj a b δ) 0) := by
    simpa using hG0
  have hcomp : HasFDerivAt
      ((fun w' => G w' 0) ∘ (fun δ : Fin (a + b) → ℝ => w + parProj a b δ))
      (φ ∘SL (parProj a b)) 0 := hG0'.comp 0 hAff
  have hb1 : (fun δ : Fin (a + b) → ℝ =>
      G (w + parProj a b δ) 0 - G w 0 - φ (parProj a b δ)) =o[𝓝 0] (fun δ => δ) := by
    have h := hasFDerivAt_iff_isLittleO_nhds_zero.mp hcomp
    simpa [Function.comp_apply, zero_add, map_zero, add_zero] using h
  have hb2 := fiberSheet_eventually G Q6 hQ6 r0 hr0 hsl hz hb hw
  have hsum := hb1.add hb2
  refine Asymptotics.IsLittleO.congr hsum ?_ (fun δ => rfl)
  intro δ
  show (G (w + parProj a b δ) 0 - G w 0 - φ (parProj a b δ))
      + (G (w + parProj a b δ) (fibProj a b δ) - G (w + parProj a b δ) 0
          - ψ (fibProj a b δ))
    = Work.WilG4c.famFun G (Fin.append w 0 + δ) - Work.WilG4c.famFun G (Fin.append w 0)
        - pairCLM a b φ ψ δ
  simp only [famFun_parProj_fibProj, pairCLM_apply, ContinuousLinearMap.map_add,
    parProj_append, fibProj_append, zero_add]
  ring

end Work.WilCrux
