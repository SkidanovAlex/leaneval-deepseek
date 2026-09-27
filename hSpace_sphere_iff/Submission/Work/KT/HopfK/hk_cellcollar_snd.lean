import Mathlib
import Submission.Work.KT.HopfK.Basic

namespace Work.KT.HopfK

/-- On the boundary sphere of the ball, the cell evaluation `evalD` coincides with the base
evaluation `evalT` at the image point under the attaching map: both amount to the relation
`g ∘ f = h` defining the mapping cone. -/
private lemma evalD_eq_evalT_of_norm_eq_one (m : ℕ) (f : C(Sph (Eu m × Eu m), Tgt m))
    (w : Ball (Eu m × Eu m)) (hw : ‖(w : Eu m × Eu m)‖ = 1) :
    evalD m f w = evalT m f (f ⟨(w : Eu m × Eu m), mem_sphere_zero_iff_norm.mpr hw⟩) := by
  ext x
  have hx := x.2 w hw
  show (x : C(Tgt m, ℂ) × C(Ball (Eu m × Eu m), ℂ)).2 w = _
  rw [show (evalT m f (f ⟨(w : Eu m × Eu m), mem_sphere_zero_iff_norm.mpr hw⟩)) x
      = ((x : C(Tgt m, ℂ) × C(Ball (Eu m × Eu m), ℂ)).1)
        (f ⟨(w : Eu m × Eu m), mem_sphere_zero_iff_norm.mpr hw⟩) from rfl]
  exact hx

/-- The height of the Hopf construction at a point of norm `≤ 1` whose second coordinate has
norm `≥ √3/2` is `≥ -1/2`, i.e. the image lies in the upper cap `capTplus`. -/
private lemma hopfSnd_ge_neg_half (m : ℕ) (w : Eu m × Eu m) (hw : ‖w‖ ≤ 1)
    (hw2 : Real.sqrt 3 / 2 ≤ ‖w.2‖) : -(1 / 2 : ℝ) ≤ hopfSnd m w := by
  have h2 : (3 : ℝ) / 4 ≤ ‖w.2‖ ^ 2 := by
    have h3 : ((Real.sqrt 3) / 2) ^ 2 = 3 / 4 := by
      rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]; norm_num
    calc (3 : ℝ) / 4 = ((Real.sqrt 3) / 2) ^ 2 := h3.symm
      _ ≤ ‖w.2‖ ^ 2 := (sq_le_sq₀ (by positivity) (norm_nonneg _)).mpr hw2
  have h1 : ‖w.1‖ ^ 2 ≤ 1 := by
    have h := norm_fst_le w
    nlinarith [norm_nonneg w.1, norm_nonneg w, h, hw]
  have hB : Real.sqrt (max (‖w.1‖ ^ 2 - ‖w.2‖ ^ 2) 0) ≤ (1 : ℝ) / 2 := by
    have hmax : max (‖w.1‖ ^ 2 - ‖w.2‖ ^ 2) 0 ≤ ((1 : ℝ) / 2) ^ 2 := by
      rw [show ((1 : ℝ) / 2) ^ 2 = 1 / 4 by norm_num]
      apply max_le _ (by norm_num)
      linarith
    have hle := Real.sqrt_le_sqrt hmax
    rwa [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1 / 2)] at hle
  have hA : 0 ≤ Real.sqrt (max (‖w.2‖ ^ 2 - ‖w.1‖ ^ 2) 0) := Real.sqrt_nonneg _
  unfold hopfSnd
  linarith

theorem hk_cellcollar_snd (m : ℕ) (μ : C(Sph (Eu m) × Sph (Eu m), Sph (Eu m))) (n r : ℕ) (δ : ℝ)
    (hδ : Real.sqrt 3 / 2 ≤ 1 - δ)
    (p : Matrix (Fin n) (Fin n) (coneAlg (hopfKMap m μ)))
    (hpb : ∀ t : Tgt m, t ∈ capTplus m → p.map (evalT m (hopfKMap m μ) t) = diagIdemMat r n)
    (hcollar : ∀ z : Ball (Eu m × Eu m), 1 / 2 ≤ ‖(z : Eu m × Eu m)‖ →
      p.map (evalD m (hopfKMap m μ) z) = p.map (evalD m (hopfKMap m μ) (normPtBall z))) :
    ∀ z : Ball (Eu m × Eu m), 1 - δ ≤ ‖(z : Eu m × Eu m).2‖ →
      p.map (evalD m (hopfKMap m μ) z) = diagIdemMat r n := by
  intro z hz
  -- `1 - δ ≥ √3/2` gives that `z` is far enough from the origin for the collar to apply.
  have hzle : ‖(z : Eu m × Eu m)‖ ≤ 1 := by
    have h := Metric.mem_closedBall.mp z.2
    rwa [dist_eq_norm, sub_zero] at h
  have hz2 : Real.sqrt 3 / 2 ≤ ‖(z : Eu m × Eu m).2‖ := le_trans hδ hz
  have hhalf : (1 : ℝ) / 2 ≤ ‖(z : Eu m × Eu m)‖ := by
    have h1 : ‖(z : Eu m × Eu m).2‖ ≤ ‖(z : Eu m × Eu m)‖ := norm_snd_le _
    have h3 : (1 : ℝ) / 2 ≤ Real.sqrt 3 / 2 := by
      have h4 : (1 : ℝ) ≤ Real.sqrt 3 := by
        have hs := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ 3 by norm_num)
        rwa [Real.sqrt_one] at hs
      linarith
    linarith
  have hzpos : 0 < ‖(z : Eu m × Eu m)‖ := by linarith
  have hz0 : z ≠ 0 := by
    intro h
    have hc : (z : Eu m × Eu m) = 0 := by rw [h]; rfl
    rw [hc, norm_zero] at hhalf
    norm_num at hhalf
  -- normalise `z` to the boundary sphere and read off the point of the target.
  let w : Ball (Eu m × Eu m) := normPtBall z
  have hwb : ‖(w : Eu m × Eu m)‖ = 1 := normPtBall_mem_sphere hz0
  let ws : Sph (Eu m × Eu m) := ⟨(w : Eu m × Eu m), mem_sphere_zero_iff_norm.mpr hwb⟩
  -- the normalised point still has second coordinate of norm `≥ √3/2`.
  have hw2 : Real.sqrt 3 / 2 ≤ ‖(ws : Eu m × Eu m).2‖ := by
    have hinv : 1 ≤ (‖(z : Eu m × Eu m)‖)⁻¹ := (one_le_inv₀ hzpos).mpr hzle
    show Real.sqrt 3 / 2 ≤ ‖(w : Eu m × Eu m).2‖
    rw [show (w : Eu m × Eu m) = ‖(z : Eu m × Eu m)‖⁻¹ • (z : Eu m × Eu m) from
      normPtBall_coe z]
    rw [Prod.smul_snd, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
    calc Real.sqrt 3 / 2 ≤ ‖(z : Eu m × Eu m).2‖ := hz2
      _ = 1 * ‖(z : Eu m × Eu m).2‖ := (one_mul _).symm
      _ ≤ (‖(z : Eu m × Eu m)‖)⁻¹ * ‖(z : Eu m × Eu m).2‖ :=
          mul_le_mul_of_nonneg_right hinv (norm_nonneg _)
  -- hence the image point lies in the upper cap.
  have hcap : hopfKMap m μ ws ∈ capTplus m := by
    show tgtHeight m (hopfKMap m μ ws) ≥ -(1 / 2)
    rw [tgtHeight_hopfKMap]
    exact hopfSnd_ge_neg_half m (ws : Eu m × Eu m) (le_of_eq hwb) hw2
  -- the collar moves `z` to its radial projection, where the cell part is the base part.
  have hcol : p.map (evalD m (hopfKMap m μ) z) = p.map (evalD m (hopfKMap m μ) w) :=
    hcollar z hhalf
  have heq : evalD m (hopfKMap m μ) w = evalT m (hopfKMap m μ) (hopfKMap m μ ws) :=
    evalD_eq_evalT_of_norm_eq_one m (hopfKMap m μ) w hwb
  have hpb' := hpb (hopfKMap m μ ws) hcap
  calc p.map (evalD m (hopfKMap m μ) z) = p.map (evalD m (hopfKMap m μ) w) := hcol
    _ = p.map (evalT m (hopfKMap m μ) (hopfKMap m μ ws)) := by rw [heq]
    _ = diagIdemMat r n := hpb'

end Work.KT.HopfK
