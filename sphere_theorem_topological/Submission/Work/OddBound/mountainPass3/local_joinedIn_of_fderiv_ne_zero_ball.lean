import Mathlib

namespace Work.OddBound.mountainPass3

open scoped ContDiff Topology

/-- **Local path connectedness of a sublevel set at a regular point, localised to a ball.**

This is the version of `Work.OddBound.mountainPass.port.local_joinedIn_ball_of_fderiv_ne_zero`
in which `F` is only assumed to be `C¹` on `Metric.ball c R` (rather than globally), which is
what is needed when `F` is a chart expression.

With `L = f'(c) ≠ 0`, a unit vector `v` with `L v = lam > 0` and `kap = lam / (4 * (1 + ‖L‖/lam))`,
the linearised function `φ = F - Λ - L(· - c)` satisfies `‖φ p - φ q‖ ≤ kap ‖p - q‖` on a ball
around `c` (mean value inequality, using `C¹` on `Metric.ball c R`), so that along the direction
`-v` the function `F` decreases by at least `(lam - kap)` per unit of length.  Two points `x`, `y`
of the sublevel set close to `c` are joined through the "deep" points `x₀` and `y₀` obtained by
moving a distance `> ρ` in the direction `-v`; the two deep points have the same `L`-level up to
`(1 + B)ρ`, so the segment joining them also stays strictly below `Λ`. -/
theorem local_joinedIn_ball_of_contDiffOn_fderiv_ne_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : E → ℝ} {c : E} {R : ℝ} (hR : 0 < R)
    (hF : ContDiffOn ℝ 1 F (Metric.ball c R)) {Λ : ℝ} (_hc : F c = Λ)
    (hFc : fderiv ℝ F c ≠ 0) :
    ∃ ρ > 0, ∀ x y : E, dist x c < ρ → dist y c < ρ → F x < Λ → F y < Λ →
      JoinedIn ({w : E | F w < Λ} ∩ Metric.ball c R) x y := by
  classical
  set L : E →L[ℝ] ℝ := fderiv ℝ F c with hL
  have hLne : L ≠ 0 := by rw [hL]; exact hFc
  have hLpos : 0 < ‖L‖ := norm_pos_iff.mpr hLne
  obtain ⟨v, hvnorm, hvpos⟩ : ∃ v : E, ‖v‖ = 1 ∧ 0 < L v := by
    obtain ⟨w, hw⟩ : ∃ w : E, L w ≠ 0 := by
      by_contra h
      rw [not_exists] at h
      exact hLne (ContinuousLinearMap.ext fun u => by simpa using h u)
    have hw0 : w ≠ 0 := fun h0 => hw (by simp [h0])
    have hwn : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw0
    rcases lt_or_gt_of_ne hw with hneg | hpos
    · refine ⟨‖w‖⁻¹ • (-w), ?_, ?_⟩
      · rw [norm_smul, norm_neg, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg w)),
          inv_mul_cancel₀ hwn]
      · rw [map_smul, map_neg, smul_eq_mul]
        exact mul_pos (inv_pos.mpr (norm_pos_iff.mpr hw0)) (neg_pos.mpr hneg)
    · refine ⟨‖w‖⁻¹ • w, ?_, ?_⟩
      · rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg w)), inv_mul_cancel₀ hwn]
      · rw [map_smul, smul_eq_mul]
        exact mul_pos (inv_pos.mpr (norm_pos_iff.mpr hw0)) hpos
  set lam : ℝ := L v with hlam
  have hlampos : 0 < lam := by rw [hlam]; exact hvpos
  set B : ℝ := ‖L‖ / lam with hB
  have hBpos : 0 < B := div_pos hLpos hlampos
  have hBnn : 0 ≤ B := hBpos.le
  set kap : ℝ := lam / (4 * (1 + B)) with hkap
  have hkappos : 0 < kap := by rw [hkap]; positivity
  set A : ℝ := 2 * (1 + B) with hA
  have hApos : 0 < A := by rw [hA]; linarith
  have hAge1 : 1 ≤ A := by rw [hA]; linarith
  have hkapA : kap * A = lam / 2 := by
    rw [hkap, hA]
    field_simp
    ring
  have hkaplt : kap < lam / 2 := by
    have h1 : kap * 2 < kap * A := mul_lt_mul_of_pos_left (by rw [hA]; linarith) hkappos
    rw [hkapA] at h1
    linarith
  have hlamkappos : 0 < lam - kap := by linarith
  -- the derivative is continuous at `c`, since `F` is `C¹` on the ball
  have hcontOn : ContinuousOn (fderiv ℝ F) (Metric.ball c R) :=
    hF.continuousOn_fderiv_of_isOpen Metric.isOpen_ball (by norm_num)
  have hcmem : c ∈ Metric.ball c R := Metric.mem_ball_self hR
  have hcont : ContinuousAt (fderiv ℝ F) c :=
    hcontOn.continuousAt (Metric.isOpen_ball.mem_nhds hcmem)
  obtain ⟨δ₀, hδ₀pos, hδ₀⟩ := (Metric.continuousAt_iff.mp hcont) kap hkappos
  -- shrink `δ` so that the closed ball is contained in `Metric.ball c R`
  set δ : ℝ := min (δ₀ / 2) (R / 2) with hδdef
  have hδpos : 0 < δ := lt_min (by linarith) (by linarith)
  have hsub : Metric.closedBall c δ ⊆ Metric.ball c R := by
    intro η hη
    rw [Metric.mem_closedBall, dist_eq_norm] at hη
    rw [Metric.mem_ball, dist_eq_norm]
    have h2 : δ ≤ R / 2 := min_le_right _ _
    linarith
  have hδ : ∀ η : E, ‖η - c‖ ≤ δ → ‖fderiv ℝ F η - L‖ ≤ kap := by
    intro η hη
    have h1 : dist η c < δ₀ := by
      rw [dist_eq_norm]
      have h2 : ‖η - c‖ ≤ δ₀ / 2 := le_trans hη (min_le_left _ _)
      linarith
    have h2 : dist (fderiv ℝ F η) (fderiv ℝ F c) < kap := hδ₀ h1
    rw [dist_eq_norm] at h2
    exact le_of_lt (by simpa [← hL] using h2)
  have hdiff : ∀ η ∈ Metric.closedBall c δ, DifferentiableAt ℝ F η := by
    intro η hη
    exact (hF.differentiableOn (n := 1) (by norm_num)).differentiableAt
      (Metric.isOpen_ball.mem_nhds (hsub hη))
  have hMVT : ∀ η ∈ Metric.closedBall c δ, ∀ η' ∈ Metric.closedBall c δ,
      ‖F η' - F η - L (η' - η)‖ ≤ kap * ‖η' - η‖ := by
    intro η hη η' hη'
    exact Convex.norm_image_sub_le_of_norm_fderiv_le' (s := Metric.closedBall c δ) (φ := L)
      (C := kap) hdiff (fun ξ hξ => hδ ξ (by rwa [Metric.mem_closedBall, dist_eq_norm] at hξ))
      (convex_closedBall c δ) hη hη'
  set ρ : ℝ := min δ R / (2 * A) with hρ
  have hρpos : 0 < ρ := by rw [hρ]; exact div_pos (lt_min hδpos hR) (by linarith)
  have hAρ_eq : A * ρ = min δ R / 2 := by
    rw [hρ, ← mul_div_assoc, mul_comm 2 A, mul_div_mul_left _ _ hApos.ne']
  have hAρ_le_δ : A * ρ ≤ δ := by rw [hAρ_eq]; linarith [min_le_left δ R]
  have hAρ_lt_R : A * ρ < R := by rw [hAρ_eq]; linarith [min_le_right δ R]
  have hρ_le : ρ ≤ A * ρ := by
    have h := mul_le_mul_of_nonneg_left hAge1 hρpos.le
    rw [mul_one] at h
    linarith
  refine ⟨ρ, hρpos, ?_⟩
  intro x y hxc hyc hFx hFy
  rw [dist_eq_norm] at hxc hyc
  have hx_d : ‖x - c‖ ≤ A * ρ := le_trans hxc.le hρ_le
  have hy_d : ‖y - c‖ ≤ A * ρ := le_trans hyc.le hρ_le
  -- ## moving in the direction `-v` strictly decreases `F`
  have hvert : ∀ η : E, ‖η - c‖ ≤ A * ρ → ∀ τ : ℝ, 0 ≤ τ → ‖η - τ • v - c‖ ≤ A * ρ →
      F (η - τ • v) ≤ F η - (lam - kap) * τ := by
    intro η hη τ hτ hτη
    have h1 : η ∈ Metric.closedBall c δ := by
      rw [Metric.mem_closedBall, dist_eq_norm]; linarith
    have h2 : η - τ • v ∈ Metric.closedBall c δ := by
      rw [Metric.mem_closedBall, dist_eq_norm]; linarith
    have h := hMVT η h1 (η - τ • v) h2
    have e : η - τ • v - η = -(τ • v) := by abel
    have e2 : L (η - τ • v - η) = -(τ * lam) := by
      rw [e, map_neg, map_smul, smul_eq_mul, ← hlam]
    have e3 : ‖η - τ • v - η‖ = τ := by
      rw [e, norm_neg, norm_smul, hvnorm, mul_one, Real.norm_eq_abs, abs_of_nonneg hτ]
    rw [e2, e3, Real.norm_eq_abs] at h
    have h3 : F (η - τ • v) - F η - -(τ * lam) ≤ kap * τ := (abs_le.mp h).2
    linarith
  -- ## along a direction in the kernel of `L` the value of `F` changes little
  have hdeep : ∀ η η' : E, ‖η - c‖ ≤ A * ρ → ‖η' - c‖ ≤ A * ρ → L (η' - η) = 0 →
      F η' ≤ F η + kap * ‖η' - η‖ := by
    intro η η' hη hη' hker
    have h1 : η ∈ Metric.closedBall c δ := by
      rw [Metric.mem_closedBall, dist_eq_norm]; linarith
    have h2 : η' ∈ Metric.closedBall c δ := by
      rw [Metric.mem_closedBall, dist_eq_norm]; linarith
    have h := hMVT η h1 η' h2
    rw [hker, sub_zero, Real.norm_eq_abs] at h
    have h3 : F η' - F η ≤ kap * ‖η' - η‖ := (abs_le.mp h).2
    linarith
  have hvdist : ∀ η : E, ‖η - c‖ < ρ → ∀ T τ : ℝ, 0 ≤ τ → τ ≤ T → T ≤ (2 * B + 1) * ρ →
      ‖η - τ • v - c‖ ≤ A * ρ := by
    intro η hη T τ hτ0 hτT hT
    have e : η - τ • v - c = (η - c) - τ • v := by abel
    rw [e]
    calc ‖(η - c) - τ • v‖ ≤ ‖η - c‖ + ‖τ • v‖ := norm_sub_le _ _
      _ = ‖η - c‖ + τ := by rw [norm_smul, hvnorm, mul_one, Real.norm_eq_abs, abs_of_nonneg hτ0]
      _ ≤ ρ + T := by linarith
      _ ≤ ρ + (2 * B + 1) * ρ := by linarith
      _ = A * ρ := by rw [hA]; ring
  -- ## every point close to `c` has a "deep" point in direction `-v`
  set S : ℝ := (B + 1) * ρ with hS
  have hdata : ∀ η : E, ‖η - c‖ < ρ → ∃ (T : ℝ) (η₀ u : E),
      ρ < T ∧ T ≤ (2 * B + 1) * ρ ∧ η₀ = η - T • v ∧ η₀ = c + u - S • v ∧
      L u = 0 ∧ ‖u‖ < (1 + B) * ρ ∧ ‖η₀ - c‖ ≤ A * ρ ∧ F η₀ ≤ F η - (lam - kap) * T := by
    intro η hη
    have hSnn : 0 ≤ S := by rw [hS]; exact mul_nonneg (by linarith) hρpos.le
    set t : ℝ := L (η - c) / lam with ht
    set u : E := η - c - t • v with hu
    set T : ℝ := t + S with hT
    set η₀ : E := η - T • v with hη₀
    have hBt : |t| < B * ρ := by
      have hLxz : |L (η - c)| ≤ ‖L‖ * ‖η - c‖ := by
        simpa [Real.norm_eq_abs] using L.le_opNorm (η - c)
      have hBlam : B * lam = ‖L‖ := by rw [hB, div_mul_cancel₀ _ hlampos.ne']
      have hBρlam : (B * ρ) * lam = ‖L‖ * ρ := by rw [← hBlam]; ring
      have key : |t| * lam < (B * ρ) * lam := by
        calc |t| * lam = |L (η - c)| := by
              rw [ht, abs_div, abs_of_pos hlampos, div_mul_cancel₀ _ hlampos.ne']
          _ ≤ ‖L‖ * ‖η - c‖ := hLxz
          _ < ‖L‖ * ρ := mul_lt_mul_of_pos_left hη hLpos
          _ = (B * ρ) * lam := by rw [hBρlam]
      exact lt_of_mul_lt_mul_right key hlampos.le
    have hTgt : ρ < T := by
      have h1 : -(B * ρ) < t := (abs_lt.mp hBt).1
      rw [hT, hS]; linarith
    have hTle : T ≤ (2 * B + 1) * ρ := by
      have h1 : t < B * ρ := (abs_lt.mp hBt).2
      rw [hT, hS]; linarith
    have hTnn : 0 ≤ T := le_of_lt (lt_trans hρpos hTgt)
    have huL : L u = 0 := by
      rw [hu, map_sub, map_smul, smul_eq_mul, ← hlam, ht, div_mul_cancel₀ _ hlampos.ne',
        sub_self]
    have hub : ‖u‖ < (1 + B) * ρ := by
      rw [hu]
      calc ‖η - c - t • v‖ ≤ ‖η - c‖ + ‖t • v‖ := norm_sub_le _ _
        _ = ‖η - c‖ + |t| := by rw [norm_smul, hvnorm, mul_one, Real.norm_eq_abs]
        _ < ρ + B * ρ := by linarith
        _ = (1 + B) * ρ := by ring
    have heq : η₀ = c + u - S • v := by
      rw [hη₀, hu, hT, add_smul]
      abel
    have hd : ‖η₀ - c‖ ≤ A * ρ := by
      have e : η₀ - c = u - S • v := by rw [heq]; abel
      rw [e]
      calc ‖u - S • v‖ ≤ ‖u‖ + ‖S • v‖ := norm_sub_le _ _
        _ = ‖u‖ + S := by rw [norm_smul, hvnorm, mul_one, Real.norm_eq_abs, abs_of_nonneg hSnn]
        _ ≤ (1 + B) * ρ + S := by linarith
        _ = A * ρ := by rw [hA, hS]; ring
    have hFη : F η₀ ≤ F η - (lam - kap) * T := by
      have h1 : ‖η - T • v - c‖ ≤ A * ρ := hvdist η hη T T hTnn le_rfl hTle
      have h2 := hvert η (le_trans hη.le hρ_le) T hTnn h1
      simpa [hη₀] using h2
    exact ⟨T, η₀, u, hTgt, hTle, rfl, heq, huL, hub, hd, hFη⟩
  obtain ⟨Tx, x₀, ux, hTxgt, hTxle, hx₀def, hx₀eq, hLux, huxb, hx₀d, hx₀F⟩ := hdata x hxc
  obtain ⟨Ty, y₀, uy, hTygt, hTyle, hy₀def, hy₀eq, hLuy, huyb, hy₀d, hy₀F⟩ := hdata y hyc
  have hLd : L (y₀ - x₀) = 0 := by
    have e : y₀ - x₀ = uy - ux := by rw [hy₀eq, hx₀eq]; abel
    rw [e, map_sub, hLuy, hLux, sub_self]
  have hdb : ‖y₀ - x₀‖ < 2 * (1 + B) * ρ := by
    have e : y₀ - x₀ = uy - ux := by rw [hy₀eq, hx₀eq]; abel
    rw [e]
    calc ‖uy - ux‖ ≤ ‖uy‖ + ‖ux‖ := norm_sub_le _ _
      _ < (1 + B) * ρ + (1 + B) * ρ := by linarith
      _ = 2 * (1 + B) * ρ := by ring
  have hpiece1 : JoinedIn ({w : E | F w < Λ} ∩ Metric.ball c R) x x₀ := by
    refine ⟨Path.segment x x₀, fun t => ?_⟩
    rw [Path.segment_apply, AffineMap.lineMap_apply_module, Set.mem_inter_iff, Set.mem_ofPred_eq]
    set s : ℝ := (t : ℝ) with hs
    have hs0 : 0 ≤ s := t.2.1
    have hs1 : s ≤ 1 := t.2.2
    have hTnn : 0 ≤ Tx := le_of_lt (lt_trans hρpos hTxgt)
    have hpt : (1 - s) • x + s • x₀ = x - (s * Tx) • v := by
      rw [hx₀def]
      module
    have hdist : ‖x - (s * Tx) • v - c‖ ≤ A * ρ :=
      hvdist x hxc Tx (s * Tx) (mul_nonneg hs0 hTnn)
        (mul_le_of_le_one_left hTnn hs1) hTxle
    constructor
    · rw [hpt]
      have h := hvert x hx_d (s * Tx) (mul_nonneg hs0 hTnn) hdist
      have h2 : F x - (lam - kap) * (s * Tx) ≤ F x := by
        have : 0 ≤ (lam - kap) * (s * Tx) := mul_nonneg hlamkappos.le (mul_nonneg hs0 hTnn)
        linarith
      linarith
    · rw [Metric.mem_ball, dist_eq_norm, hpt]
      linarith [hdist, hAρ_lt_R]
  have hpiece2 : JoinedIn ({w : E | F w < Λ} ∩ Metric.ball c R) x₀ y₀ := by
    refine ⟨Path.segment x₀ y₀, fun t => ?_⟩
    rw [Path.segment_apply, AffineMap.lineMap_apply_module, Set.mem_inter_iff, Set.mem_ofPred_eq]
    set s : ℝ := (t : ℝ) with hs
    have hs0 : 0 ≤ s := t.2.1
    have hs1 : s ≤ 1 := t.2.2
    have hpt : (1 - s) • x₀ + s • y₀ = x₀ + s • (y₀ - x₀) := by module
    have hdist : ‖x₀ + s • (y₀ - x₀) - c‖ ≤ A * ρ := by
      have e : x₀ + s • (y₀ - x₀) - c = (1 - s) • (x₀ - c) + s • (y₀ - c) := by module
      rw [e]
      calc ‖(1 - s) • (x₀ - c) + s • (y₀ - c)‖
          ≤ ‖(1 - s) • (x₀ - c)‖ + ‖s • (y₀ - c)‖ := norm_add_le _ _
        _ = (1 - s) * ‖x₀ - c‖ + s * ‖y₀ - c‖ := by
            rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
              abs_of_nonneg (by linarith), abs_of_nonneg hs0]
        _ ≤ (1 - s) * (A * ρ) + s * (A * ρ) :=
            add_le_add (mul_le_mul_of_nonneg_left hx₀d (by linarith))
              (mul_le_mul_of_nonneg_left hy₀d hs0)
        _ = A * ρ := by ring
    constructor
    · rw [hpt]
      have hker : L (x₀ + s • (y₀ - x₀) - x₀) = 0 := by
        rw [add_sub_cancel_left, map_smul, smul_eq_mul, hLd, mul_zero]
      have h := hdeep x₀ (x₀ + s • (y₀ - x₀)) hx₀d hdist hker
      have hnorm : ‖x₀ + s • (y₀ - x₀) - x₀‖ = s * ‖y₀ - x₀‖ := by
        rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs0]
      rw [hnorm] at h
      have hb1 : kap * (s * ‖y₀ - x₀‖) ≤ (lam / 2) * ρ := by
        have h3 : s * ‖y₀ - x₀‖ ≤ A * ρ := by
          have h4 : ‖y₀ - x₀‖ ≤ A * ρ := by rw [hA]; exact hdb.le
          have h5 : s * ‖y₀ - x₀‖ ≤ 1 * (A * ρ) :=
            mul_le_mul hs1 h4 (norm_nonneg _) zero_le_one
          rwa [one_mul] at h5
        calc kap * (s * ‖y₀ - x₀‖) ≤ kap * (A * ρ) := mul_le_mul_of_nonneg_left h3 hkappos.le
          _ = (lam / 2) * ρ := by rw [← mul_assoc, hkapA]
      have hb2 : F x₀ ≤ F x - (lam - kap) * ρ := by
        have h4 : (lam - kap) * ρ ≤ (lam - kap) * Tx :=
          mul_le_mul_of_nonneg_left hTxgt.le hlamkappos.le
        linarith
      have hb3 : F x - (lam - kap) * ρ + (lam / 2) * ρ < Λ := by
        have h5 : (lam / 2) * ρ < (lam - kap) * ρ :=
          mul_lt_mul_of_pos_right (by linarith) hρpos
        linarith
      linarith
    · rw [Metric.mem_ball, dist_eq_norm, hpt]
      linarith [hdist, hAρ_lt_R]
  have hpiece3 : JoinedIn ({w : E | F w < Λ} ∩ Metric.ball c R) y₀ y := by
    refine ⟨Path.segment y₀ y, fun t => ?_⟩
    rw [Path.segment_apply, AffineMap.lineMap_apply_module, Set.mem_inter_iff, Set.mem_ofPred_eq]
    set s : ℝ := (t : ℝ) with hs
    have hs0 : 0 ≤ s := t.2.1
    have hs1 : s ≤ 1 := t.2.2
    have hTnn : 0 ≤ Ty := le_of_lt (lt_trans hρpos hTygt)
    have hpt : (1 - s) • y₀ + s • y = y - ((1 - s) * Ty) • v := by
      rw [hy₀def]
      module
    have hτ0 : 0 ≤ (1 - s) * Ty := mul_nonneg (by linarith) hTnn
    have hτle : (1 - s) * Ty ≤ Ty := by
      have h : (1 - s) ≤ 1 := by linarith
      simpa using mul_le_of_le_one_left hTnn h
    have hdist : ‖y - ((1 - s) * Ty) • v - c‖ ≤ A * ρ :=
      hvdist y hyc Ty ((1 - s) * Ty) hτ0 hτle hTyle
    constructor
    · rw [hpt]
      have h := hvert y hy_d ((1 - s) * Ty) hτ0 hdist
      have h2 : F y - (lam - kap) * ((1 - s) * Ty) ≤ F y := by
        have : 0 ≤ (lam - kap) * ((1 - s) * Ty) := mul_nonneg hlamkappos.le hτ0
        linarith
      linarith
    · rw [Metric.mem_ball, dist_eq_norm, hpt]
      linarith [hdist, hAρ_lt_R]
  exact (hpiece1.trans hpiece2).trans hpiece3

/-- **Local connectedness of a sublevel set near a regular point of a `C¹` function.**

Let `f : E → ℝ` be `C¹` on `Metric.ball u R` (with `0 < R`) and suppose `f'(u) ≠ 0`, so that `u`
is a regular point of `f`.  Then for all `x`, `y` close enough to `u` with `f x < f u` and
`f y < f u` there is a path from `x` to `y` which stays strictly in the sublevel set `{f < f u}`
and inside the ball `Metric.ball u R`.

The path is the concatenation of three segments: from `x` straight in the direction in which `f`
decreases, then across (in the kernel direction of `f'(u)`), then back to `y`. -/
theorem local_joinedIn_of_fderiv_ne_zero_ball {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : E → ℝ} {u : E} {R : ℝ} (hR : 0 < R)
    (hf : ContDiffOn ℝ 1 f (Metric.ball u R)) (hgz : fderiv ℝ f u ≠ 0) :
    ∃ ρ > 0, ∀ x y : E, dist x u < ρ → dist y u < ρ → f x < f u → f y < f u →
      ∃ γ : ℝ → E, ContinuousOn γ unitInterval ∧ γ 0 = x ∧ γ 1 = y ∧
        (∀ t ∈ unitInterval, f (γ t) < f u) ∧ (∀ t ∈ unitInterval, dist (γ t) u < R) := by
  obtain ⟨ρ, hρ, hJ⟩ :=
    local_joinedIn_ball_of_contDiffOn_fderiv_ne_zero hR hf rfl hgz
  refine ⟨ρ, hρ, ?_⟩
  intro x y hx hy hfx hfy
  obtain ⟨γ, hγ⟩ := hJ x y hx hy hfx hfy
  refine ⟨fun t : ℝ => γ (Set.projIcc 0 1 (by norm_num) t), ?_, ?_, ?_, ?_, ?_⟩
  · exact (γ.continuous.comp continuous_projIcc).continuousOn
  · show γ (Set.projIcc 0 1 _ (0 : ℝ)) = x
    rw [show Set.projIcc 0 1 (by norm_num : (0 : ℝ) ≤ 1) (0 : ℝ) = (0 : ↥unitInterval) from
      Set.projIcc_of_mem _ (by norm_num : (0 : ℝ) ∈ Set.Icc 0 1)]
    exact γ.source
  · show γ (Set.projIcc 0 1 _ (1 : ℝ)) = y
    rw [show Set.projIcc 0 1 (by norm_num : (0 : ℝ) ≤ 1) (1 : ℝ) = (1 : ↥unitInterval) from
      Set.projIcc_of_mem _ (by norm_num : (1 : ℝ) ∈ Set.Icc 0 1)]
    exact γ.target
  · intro t ht
    have h1 := hγ (Set.projIcc 0 1 (by norm_num : (0 : ℝ) ≤ 1) t)
    exact h1.1
  · intro t ht
    have h1 := hγ (Set.projIcc 0 1 (by norm_num : (0 : ℝ) ≤ 1) t)
    exact h1.2

end Work.OddBound.mountainPass3
