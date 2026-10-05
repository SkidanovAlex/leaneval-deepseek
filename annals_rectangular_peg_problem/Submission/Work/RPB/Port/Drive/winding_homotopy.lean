import Mathlib
import Submission.Work.RPB.Port.Drive.WindingNumber
import Submission.Work.RPB.Port.Drive.degree_homotopic

namespace Work.RPB.Port.Drive

/-- Scaling a vector by `s ∈ [0,1]` does not increase its norm. -/
lemma norm_smul_le_of_mem_Icc {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) (v : E) : ‖s • v‖ ≤ ‖v‖ := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1]
  calc s * ‖v‖ ≤ 1 * ‖v‖ := mul_le_mul_of_nonneg_right hs.2 (norm_nonneg v)
    _ = ‖v‖ := one_mul _

/-- If `b` is strictly shorter than `a`, then `a - s • b` does not vanish for `s ∈ [0,1]`. -/
lemma sub_smul_ne_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b : E} (h : ‖b‖ < ‖a‖) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) : a - s • b ≠ 0 := by
  intro hzero
  have h1 : ‖a‖ ≤ ‖a - s • b‖ + ‖s • b‖ := by
    have h2 := norm_add_le (a - s • b) (s • b)
    rwa [sub_add_cancel] at h2
  have h3 : ‖s • b‖ ≤ ‖b‖ := norm_smul_le_of_mem_Icc hs b
  rw [hzero, norm_zero, zero_add] at h1
  linarith

/-- **The winding number is unchanged by a homotopy of the curve avoiding the point.**

If `p'` is at strictly smaller distance from `p` than from every point of the curve, then
`winding γ hγ hp' = winding γ hγ hp`: the straight-line homotopy
`(t, s) ↦ γ t - (p + s • (p' - p))` never vanishes, because
`‖γ t - (p + s • (p' - p))‖ ≥ ‖γ t - p‖ - ‖p' - p‖ > 0`, so it induces a free homotopy of the
direction maps `dirCurve γ hγ p hp` and `dirCurve γ hγ p' hp'`, and the degrees agree by
`Work.RPB.Port.Drive.degree_homotopic`.

The hypothesis is the pointwise form of "`p'` is closer to `p` than the distance from `p` to the
curve"; for `p ∉ range γ` with `γ` continuous it holds on a genuine ball around `p` (the distance
function attains a positive minimum on the compact circle), which is exactly the local constancy of
`p ↦ winding γ hγ hp` and the first step towards "the winding is constant on the connected components
of the complement of `γ`". -/
theorem winding_homotopy (γ : UnitAddCircle → ℝ × ℝ) (hγ : Continuous γ) {p p' : ℝ × ℝ}
    (hp : p ∉ Set.range γ) (hp' : p' ∉ Set.range γ)
    (h : ∀ t : UnitAddCircle, dist p' p < dist (γ t) p) :
    winding γ hγ hp' = winding γ hγ hp := by
  have hdist : ∀ t : UnitAddCircle, ‖p' - p‖ < ‖γ t - p‖ := by
    intro t
    have h1 := h t
    rwa [dist_eq_norm, dist_eq_norm] at h1
  -- the straight-line interpolation of the base point from `p` to `p'`
  let P : unitInterval → ℝ × ℝ := fun s => p + (s : ℝ) • (p' - p)
  have hPcont : Continuous P := by
    unfold P
    fun_prop
  let q : unitInterval × UnitAddCircle → ℝ × ℝ := fun x => γ x.2 - P x.1
  have hqcont : Continuous q := (hγ.comp continuous_snd).sub (hPcont.comp continuous_fst)
  -- the moving base point never meets the curve
  have hqne : ∀ x : unitInterval × UnitAddCircle, q x ≠ 0 := by
    rintro ⟨s, t⟩
    show γ t - (p + (s : ℝ) • (p' - p)) ≠ 0
    rw [sub_add_eq_sub_sub]
    exact sub_smul_ne_zero (hdist t) s.2
  let F : unitInterval × UnitAddCircle → UnitAddCircle :=
    fun x => Work.RPB.Port.Collision.dirC (q x)
  have hFcont : Continuous F := by
    have hcomp : ContinuousOn (Work.RPB.Port.Collision.dirC ∘ q) Set.univ :=
      Work.RPB.Port.Configuration.continuousOn_dirC.comp hqcont.continuousOn
        (fun x _ => hqne x)
    exact continuousOn_univ.mp hcomp
  -- the induced free homotopy of the direction maps
  have hhom : (⟨dirCurve γ hγ p hp, continuous_dirCurve γ hγ p hp⟩ :
        C(UnitAddCircle, UnitAddCircle)).Homotopic
      ⟨dirCurve γ hγ p' hp', continuous_dirCurve γ hγ p' hp'⟩ := by
    refine ⟨ContinuousMap.Homotopy.mk ⟨F, hFcont⟩ ?_ ?_⟩
    · intro t
      change F ((0 : unitInterval), t) = dirCurve γ hγ p hp t
      have h1 : F ((0 : unitInterval), t) = Work.RPB.Port.Collision.dirC (γ t - p) := by
        show Work.RPB.Port.Collision.dirC (γ t - (p + ((0 : unitInterval) : ℝ) • (p' - p))) = _
        simp
      rw [h1]
      rfl
    · intro t
      change F ((1 : unitInterval), t) = dirCurve γ hγ p' hp' t
      have h1 : F ((1 : unitInterval), t) = Work.RPB.Port.Collision.dirC (γ t - p') := by
        show Work.RPB.Port.Collision.dirC (γ t - (p + ((1 : unitInterval) : ℝ) • (p' - p))) = _
        simp
      rw [h1]
      rfl
  have hdeg := degree_homotopic hhom
  show winding γ hγ hp' = winding γ hγ hp
  rw [winding, winding]
  exact hdeg.symm

end Work.RPB.Port.Drive
