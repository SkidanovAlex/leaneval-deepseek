import Submission.Work.Stems.Hur2.PsiCont

/-!
# The filling of a *based* cube is `x₀` off the inner square

If `p : Ω^(Fin 2) X x₀` is based then its four edges are the constant cube at `x₀`, so by
`K₁_const` the four sectors of `PsiCube x₀ p.1` are constant `x₀`: the filling only depends on `p`
on the middle quarter-square.  This is the input to (Z) (`p ~ Ψ(p)` for based `p`).
-/

open scoped unitInterval Topology

namespace Work.Stems.Hur2

open Work.Stems.Cubical

noncomputable section

variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]

/-- The top edge of a based 2-cube is the constant cube at `x₀`. -/
theorem comp_faceCM_11_eq_const {x₀ : X} (p : GenLoop (Fin 2) X x₀) :
    p.1.comp (faceCM (1 : Fin 2) (1 : unitInterval)) = ContinuousMap.const (IC 1) x₀ := by
  ext w
  rw [ContinuousMap.comp_apply, ContinuousMap.const_apply]
  refine p.2 _ ?_
  rw [Cube.boundary]
  exact ⟨1, Or.inr (by rw [faceCM_pair2_11, pair2_one])⟩

/-- The right edge of a based 2-cube is the constant cube at `x₀`. -/
theorem comp_faceCM_01_eq_const {x₀ : X} (p : GenLoop (Fin 2) X x₀) :
    p.1.comp (faceCM (0 : Fin 2) (1 : unitInterval)) = ContinuousMap.const (IC 1) x₀ := by
  ext w
  rw [ContinuousMap.comp_apply, ContinuousMap.const_apply]
  refine p.2 _ ?_
  rw [Cube.boundary]
  exact ⟨0, Or.inr (by rw [faceCM_pair2_01, pair2_zero])⟩

/-- The bottom edge of a based 2-cube is the constant cube at `x₀`. -/
theorem comp_faceCM_10_eq_const {x₀ : X} (p : GenLoop (Fin 2) X x₀) :
    p.1.comp (faceCM (1 : Fin 2) (0 : unitInterval)) = ContinuousMap.const (IC 1) x₀ := by
  ext w
  rw [ContinuousMap.comp_apply, ContinuousMap.const_apply]
  refine p.2 _ ?_
  rw [Cube.boundary]
  exact ⟨1, Or.inl (by rw [faceCM_pair2_10, pair2_one])⟩

/-- The left edge of a based 2-cube is the constant cube at `x₀`. -/
theorem comp_faceCM_00_eq_const {x₀ : X} (p : GenLoop (Fin 2) X x₀) :
    p.1.comp (faceCM (0 : Fin 2) (0 : unitInterval)) = ContinuousMap.const (IC 1) x₀ := by
  ext w
  rw [ContinuousMap.comp_apply, ContinuousMap.const_apply]
  refine p.2 _ ?_
  rw [Cube.boundary]
  exact ⟨0, Or.inl (by rw [faceCM_pair2_00, pair2_zero])⟩

/-- **Off the inner square the filling of a based cube is `x₀`.** -/
theorem psiFun_apply_of_not_mem_inner {x₀ : X} (p : GenLoop (Fin 2) X x₀) {t : IC 2}
    (h : t ∉ innerSet) : psiFun x₀ p.1 t = x₀ := by
  rcases mem_regions t with ht | ht | ht | ht | ht
  · rw [psiFun_eq_topVal ht, topVal, comp_faceCM_11_eq_const, K₁_const]
    rfl
  · rw [psiFun_eq_rightVal' ht, rightVal, comp_faceCM_01_eq_const, K₁_const]
    rfl
  · rw [psiFun_eq_botVal' ht, botVal, comp_faceCM_10_eq_const, K₁_const]
    rfl
  · rw [psiFun_eq_leftVal' ht, leftVal, comp_faceCM_00_eq_const, K₁_const]
    rfl
  · exact absurd ht h

/-- **On the inner square the filling of a based cube is `p` rescaled.** -/
theorem psiFun_apply_of_mem_inner {x₀ : X} (p : GenLoop (Fin 2) X x₀) {t : IC 2}
    (h : t ∈ innerSet) :
    psiFun x₀ p.1 t = p.1 (pair2 (clamp (2 * (t 0 : ℝ) - 1/2)) (clamp (2 * (t 1 : ℝ) - 1/2))) :=
  psiFun_eq_innerVal' h

/-- The square-radius of a point: `max (|2a - 1|) (|2b - 1|)`. -/
def sqRad (t : IC 2) : ℝ := max |2 * (t 0 : ℝ) - 1| |2 * (t 1 : ℝ) - 1|

@[simp] theorem sqRad_apply (t : IC 2) :
    sqRad t = max |2 * (t 0 : ℝ) - 1| |2 * (t 1 : ℝ) - 1| := rfl

theorem sqRad_nonneg (t : IC 2) : 0 ≤ sqRad t := le_max_of_le_left (abs_nonneg _)

/-- The inner square is exactly the set where the square-radius is at most `1/2`. -/
theorem sqRad_le_half_iff (t : IC 2) : sqRad t ≤ 1/2 ↔ t ∈ innerSet := by
  have h0 : (0 : ℝ) ≤ (t 0 : ℝ) := (t 0).2.1
  have h1 : (t 0 : ℝ) ≤ 1 := (t 0).2.2
  have h2 : (0 : ℝ) ≤ (t 1 : ℝ) := (t 1).2.1
  have h3 : (t 1 : ℝ) ≤ 1 := (t 1).2.2
  constructor
  · intro h
    have ha : |2 * (t 0 : ℝ) - 1| ≤ 1/2 := le_trans (le_max_left _ _) h
    have hb : |2 * (t 1 : ℝ) - 1| ≤ 1/2 := le_trans (le_max_right _ _) h
    rw [abs_le] at ha hb
    exact ⟨by linarith [ha.1], by linarith [ha.2], by linarith [hb.1], by linarith [hb.2]⟩
  · rintro ⟨ha, ha', hb, hb'⟩
    refine max_le ?_ ?_
    · rw [abs_le]; exact ⟨by linarith, by linarith⟩
    · rw [abs_le]; exact ⟨by linarith, by linarith⟩

/-- On the boundary of the square the square-radius is `1`. -/
theorem sqRad_eq_one_of_mem_boundary {t : IC 2} (ht : t ∈ Cube.boundary (Fin 2)) :
    sqRad t = 1 := by
  have h0 : (0 : ℝ) ≤ (t 0 : ℝ) := (t 0).2.1
  have h1 : (t 0 : ℝ) ≤ 1 := (t 0).2.2
  have h2 : (0 : ℝ) ≤ (t 1 : ℝ) := (t 1).2.1
  have h3 : (t 1 : ℝ) ≤ 1 := (t 1).2.2
  rw [Cube.boundary] at ht
  obtain ⟨i, hi | hi⟩ := ht
  · fin_cases i
    · have hu : (t 0 : unitInterval) = 0 := hi
      have hr : ((t 0 : unitInterval) : ℝ) = 0 := by rw [hu]; rfl
      rw [sqRad, show (2 * (t 0 : ℝ) - 1) = -1 by rw [hr]; norm_num, abs_neg, abs_one]
      exact max_eq_left (by rw [abs_le]; exact ⟨by linarith, by linarith⟩)
    · have hu : (t 1 : unitInterval) = 0 := hi
      have hr : ((t 1 : unitInterval) : ℝ) = 0 := by rw [hu]; rfl
      rw [sqRad, show (2 * (t 1 : ℝ) - 1) = -1 by rw [hr]; norm_num, abs_neg, abs_one]
      exact max_eq_right (by rw [abs_le]; exact ⟨by linarith, by linarith⟩)
  · fin_cases i
    · have hu : (t 0 : unitInterval) = 1 := hi
      have hr : ((t 0 : unitInterval) : ℝ) = 1 := by rw [hu]; rfl
      rw [sqRad, show (2 * (t 0 : ℝ) - 1) = 1 by rw [hr]; norm_num, abs_one]
      exact max_eq_left (by rw [abs_le]; exact ⟨by linarith, by linarith⟩)
    · have hu : (t 1 : unitInterval) = 1 := hi
      have hr : ((t 1 : unitInterval) : ℝ) = 1 := by rw [hu]; rfl
      rw [sqRad, show (2 * (t 1 : ℝ) - 1) = 1 by rw [hr]; norm_num, abs_one]
      exact max_eq_right (by rw [abs_le]; exact ⟨by linarith, by linarith⟩)

end

end Work.Stems.Hur2
