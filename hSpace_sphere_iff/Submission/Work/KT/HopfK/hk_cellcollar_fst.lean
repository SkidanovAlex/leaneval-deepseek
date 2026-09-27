import Mathlib
import Submission.Work.KT.HopfK.Basic

namespace Work.KT.HopfK

open Work.KT

/-! ## Two elementary helpers -/

/-- On the boundary of the ball, evaluation of the cell component of the mapping cone agrees with
evaluation of the base component at the image point of `f`. -/
lemma evalD_eq_evalT_at_bdry (m : ℕ) (f : C(Sph (Eu m × Eu m), Tgt m))
    (z : Ball (Eu m × Eu m)) (hz : z ∈ bdry (Eu m × Eu m)) (a : coneAlg f) :
    evalD m f z a = evalT m f (f ⟨(z : Eu m × Eu m), mem_sphere_zero_iff_norm.mpr hz⟩) a := by
  show ((a : C(Tgt m, ℂ) × C(Ball (Eu m × Eu m), ℂ)).2) z =
       ((a : C(Tgt m, ℂ) × C(Ball (Eu m × Eu m), ℂ)).1) _
  exact a.2 z hz

/-- A unit vector whose first component has norm at least `√3/2` is carried by the Hopf
construction into the lower cap `capTminus`. -/
lemma hopfSnd_le_half_of_norm_one (m : ℕ) (u : Eu m × Eu m) (hu : ‖u‖ = 1)
    (hu1 : Real.sqrt 3 / 2 ≤ ‖u.1‖) : hopfSnd m u ≤ 1 / 2 := by
  have hu' : max ‖u.1‖ ‖u.2‖ = 1 := by rw [Prod.norm_def] at hu; exact hu
  rcases le_total ‖u.1‖ ‖u.2‖ with h | h
  · rw [hopfSnd_of_le m h]
    have hu2 : ‖u.2‖ = 1 := by rw [max_eq_right h] at hu'; exact hu'
    rw [hu2, one_pow]
    have hs3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    have hu1sq : (3 : ℝ) / 4 ≤ ‖u.1‖ ^ 2 := by nlinarith [hu1, hs3, Real.sqrt_nonneg 3]
    have hle : 1 - ‖u.1‖ ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by nlinarith
    calc Real.sqrt (1 - ‖u.1‖ ^ 2) ≤ Real.sqrt ((1 / 2 : ℝ) ^ 2) := Real.sqrt_le_sqrt hle
      _ = 1 / 2 := Real.sqrt_sq (by norm_num)
  · rw [hopfSnd_of_ge m h]
    have := Real.sqrt_nonneg (‖u.1‖ ^ 2 - ‖u.2‖ ^ 2)
    linarith

/-! ## The cell-collar consequence of the lower cap condition -/

theorem hk_cellcollar_fst (m : ℕ) (μ : C(Sph (Eu m) × Sph (Eu m), Sph (Eu m))) (n r : ℕ) (δ : ℝ)
    (hδ : Real.sqrt 3 / 2 ≤ 1 - δ)
    (q : Matrix (Fin n) (Fin n) (coneAlg (hopfKMap m μ)))
    (hqb : ∀ t : Tgt m, t ∈ capTminus m → q.map (evalT m (hopfKMap m μ) t) = diagIdemMat r n)
    (hcollar : ∀ z : Ball (Eu m × Eu m), 1 / 2 ≤ ‖(z : Eu m × Eu m)‖ →
      q.map (evalD m (hopfKMap m μ) z) = q.map (evalD m (hopfKMap m μ) (normPtBall z))) :
    ∀ z : Ball (Eu m × Eu m), 1 - δ ≤ ‖(z : Eu m × Eu m).1‖ →
      q.map (evalD m (hopfKMap m μ) z) = diagIdemMat r n := by
  intro z hz
  have hz1 : Real.sqrt 3 / 2 ≤ ‖(z : Eu m × Eu m).1‖ := le_trans hδ hz
  have h1h : (1 : ℝ) / 2 ≤ Real.sqrt 3 / 2 := by
    have h3 : (1 : ℝ) ≤ Real.sqrt 3 := by
      rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
    linarith
  have hznorm_ge : 1 / 2 ≤ ‖(z : Eu m × Eu m)‖ := by
    rw [Prod.norm_def]
    exact le_trans (le_trans h1h hz1) (le_max_left _ _)
  have hz_norm_le : ‖(z : Eu m × Eu m)‖ ≤ 1 := mem_closedBall_zero_iff.mp z.2
  have hz_norm_pos : 0 < ‖(z : Eu m × Eu m)‖ := lt_of_lt_of_le (by norm_num) hznorm_ge
  have hz_ne : z ≠ 0 := by
    intro hz0
    rw [show (z : Eu m × Eu m) = 0 from by rw [hz0]; rfl, norm_zero] at hz_norm_pos
    exact lt_irrefl 0 hz_norm_pos
  have hbdry : normPtBall z ∈ bdry (Eu m × Eu m) := normPtBall_mem_sphere hz_ne
  -- the normalised point, as a unit vector
  have hcnorm : ‖((normPtBall z : Ball (Eu m × Eu m)) : Eu m × Eu m)‖ = 1 := hbdry
  have hcu1 : Real.sqrt 3 / 2 ≤
      ‖(((normPtBall z : Ball (Eu m × Eu m)) : Eu m × Eu m)).1‖ := by
    rw [normPtBall_coe, Prod.smul_fst, norm_smul,
      Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
    have hinv : (1 : ℝ) ≤ ‖(z : Eu m × Eu m)‖⁻¹ := by
      rw [one_le_inv₀ hz_norm_pos]; exact hz_norm_le
    calc Real.sqrt 3 / 2 ≤ ‖(z : Eu m × Eu m).1‖ := hz1
      _ = 1 * ‖(z : Eu m × Eu m).1‖ := (one_mul _).symm
      _ ≤ ‖(z : Eu m × Eu m)‖⁻¹ * ‖(z : Eu m × Eu m).1‖ :=
          mul_le_mul_of_nonneg_right hinv (norm_nonneg _)
  -- the radial collar
  rw [hcollar z hznorm_ge]
  -- the corresponding base point lies in the lower cap
  let pt : Sph (Eu m × Eu m) :=
    ⟨(normPtBall z : Eu m × Eu m), mem_sphere_zero_iff_norm.mpr hbdry⟩
  let t : Tgt m := hopfKMap m μ pt
  have htmem : t ∈ capTminus m := by
    show tgtHeight m (hopfKMap m μ pt) ≤ 1 / 2
    rw [tgtHeight_hopfKMap]
    exact hopfSnd_le_half_of_norm_one m _ hcnorm hcu1
  -- `evalD` at the normalised point is `evalT` at the image point
  have hED : q.map (evalD m (hopfKMap m μ) (normPtBall z)) =
      q.map (evalT m (hopfKMap m μ) t) := by
    apply Matrix.ext
    intro i j
    simp only [Matrix.map_apply]
    exact evalD_eq_evalT_at_bdry m (hopfKMap m μ) (normPtBall z) hbdry (q i j)
  rw [hED]
  exact hqb t htmem

end Work.KT.HopfK
