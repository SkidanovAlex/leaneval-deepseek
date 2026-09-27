import Mathlib
import Submission.Work.Mostow.QIDefs
import Submission.Work.Mostow.geomFiniteDefs
import Submission.Work.Mostow.hptOf_level
import Submission.Work.Mostow.hptOf_yc
import Submission.Work.Mostow.levYcFormula

/-!
# A parabolic fixed point of `Sph 2` acts trivially on the flat coordinates of its horospheres

An isometry `δ` of `ℍ²` that preserves every horosphere centred at `ξ ∈ Sph 2` acts on the flat
coordinate `yc ξ ·` of each horosphere by an affine isometry `y ↦ A y + v`.  The statement proved
here is that if `δ` is *parabolic* and `A` is an isometry of `ξ^⊥`, then in fact `A = id` on
`ξ^⊥`.

The point of the hypothesis `n = 2` is that `ξ^⊥` is then **one-dimensional**, so the linear
isometry `A|ξ^⊥` is `±id`; if it were `-id`, the affine map `y ↦ -y + v` would have the fixed
point `v/2`, whence `δ` would fix the point `hptOf ξ (v/2) 1` of `ℍ²`, contradicting parabolicity.
In higher dimensions `A|ξ^⊥` may be a non-trivial rotation and the statement is false (the
corresponding isometry is not parabolic in the classical sense, only in the weak sense of
`IsParabolic`).

The one-dimensionality of `ξ^⊥ ⊂ E 2` is `perp_sphere_two_span` below, obtained from
`Submodule.finrank_add_finrank_orthogonal` and `finrank_span_singleton`.
-/

namespace Work.Mostow

open Submission.Mostow

/-- In `E 2`, the orthogonal complement of a point `ξ` of the unit sphere is spanned by one
non-zero vector: there is `w ≠ 0` with `⟪w,ξ⟫ = 0` such that every `y` orthogonal to `ξ` is a
multiple of `w`. -/
lemma perp_sphere_two_span (ξ : E 2) (hξ : ξ ∈ Sph 2) :
    ∃ w : E 2, inner ℝ w ξ = 0 ∧ w ≠ 0 ∧
      ∀ y : E 2, inner ℝ y ξ = 0 → ∃ c : ℝ, c • w = y := by
  have hξn : ‖ξ‖ = 1 := by simpa [Sph, Metric.mem_sphere, dist_eq_norm] using hξ
  have hξ0 : ξ ≠ 0 := by
    intro h
    rw [h] at hξn
    simp at hξn
  -- `ξ^⊥` is one-dimensional in `E 2`
  have hfr : Module.finrank ℝ ↥((ℝ ∙ ξ)ᗮ) = 1 := by
    have h := Submodule.finrank_add_finrank_orthogonal (𝕜 := ℝ) (K := (ℝ ∙ ξ : Submodule ℝ (E 2)))
    have h1 : Module.finrank ℝ ↥(ℝ ∙ ξ : Submodule ℝ (E 2)) = 1 := finrank_span_singleton hξ0
    have h2 : Module.finrank ℝ (E 2) = 2 := by rw [finrank_euclideanSpace, Fintype.card_fin]
    omega
  obtain ⟨w, hwne, hw⟩ := (finrank_eq_one_iff' (K := ℝ) (V := ↥((ℝ ∙ ξ)ᗮ))).mp hfr
  refine ⟨(w : E 2), Submodule.mem_orthogonal_singleton_iff_inner_left.mp w.2, ?_, ?_⟩
  · intro h
    exact hwne (Subtype.ext h)
  · intro y hy
    obtain ⟨c, hc⟩ := hw ⟨y, Submodule.mem_orthogonal_singleton_iff_inner_left.mpr hy⟩
    exact ⟨c, by simpa using congrArg Subtype.val hc⟩

theorem flatLin_id_of_parabolic_two (hA : Submission.Mostow.POActionProp 2)
    (hI : Submission.Mostow.HypIsometryProp 2) (ξ : Submission.Mostow.E 2)
    (hξ : ξ ∈ Submission.Mostow.Sph 2) (δ : LeanEval.Geometry.MostowRigidity.PO 2 1)
    (hpar : Submission.Mostow.IsParabolic δ) (hfix : Submission.Mostow.bd δ ξ = ξ)
    (A : Submission.Mostow.E 2 →ₗ[ℝ] Submission.Mostow.E 2) (v : Submission.Mostow.E 2)
    (hvperp : inner ℝ v ξ = 0)
    (hperp : ∀ y : Submission.Mostow.E 2, inner ℝ y ξ = 0 → inner ℝ (A y) ξ = 0)
    (hnorm : ∀ y : Submission.Mostow.E 2, inner ℝ y ξ = 0 → ‖A y‖ = ‖y‖)
    (hact : ∀ (y : Submission.Mostow.E 2) (D : ℝ), inner ℝ y ξ = 0 → 0 < D →
      Work.Mostow.lev ξ (δ • Work.Mostow.hptOf ξ y D) = D ∧
      Work.Mostow.yc ξ (δ • Work.Mostow.hptOf ξ y D) = A y + v) :
    ∀ y : Submission.Mostow.E 2, inner ℝ y ξ = 0 → A y = y := by
  obtain ⟨w, hwξ, hw0, hwspan⟩ := perp_sphere_two_span ξ hξ
  -- `A` maps `w` to `±w`
  obtain ⟨s, hs⟩ := hwspan (A w) (hperp w hwξ)
  have hsabs : |s| = 1 := by
    have h : ‖s • w‖ = ‖w‖ := by rw [hs, hnorm w hwξ]
    rw [norm_smul, Real.norm_eq_abs] at h
    have hwne : ‖w‖ ≠ 0 := by rw [norm_ne_zero_iff]; exact hw0
    have h2 : |s| * ‖w‖ = 1 * ‖w‖ := by rw [one_mul]; exact h
    exact mul_right_cancel₀ hwne h2
  rcases (abs_eq zero_le_one).mp hsabs with h1 | hm1
  · -- `A w = w`: then `A` is the identity on the line spanned by `w`
    intro y hy
    obtain ⟨c, hc⟩ := hwspan y hy
    rw [← hc, map_smul, ← hs, h1, one_smul]
  · -- `A w = - w`: then `δ` fixes `hptOf ξ (v/2) 1`, contradicting parabolicity
    exfalso
    have hAneg : ∀ y : E 2, inner ℝ y ξ = 0 → A y = -y := by
      intro y hy
      obtain ⟨c, hc⟩ := hwspan y hy
      rw [← hc, map_smul, ← hs, hm1]
      simp
    set y0 : E 2 := (1/2 : ℝ) • v with hy0def
    have hy0 : inner ℝ y0 ξ = 0 := by
      rw [hy0def, real_inner_smul_left, hvperp, mul_zero]
    have hAy0 : A y0 + v = y0 := by
      rw [hAneg y0 hy0, hy0def]
      module
    have hpt := hact y0 1 hy0 (by norm_num)
    have hfixpt : δ • Work.Mostow.hptOf ξ y0 1 = Work.Mostow.hptOf ξ y0 1 := by
      have h1 := Work.Mostow.hptOf_yc ξ hξ 1 (by norm_num)
        (δ • Work.Mostow.hptOf ξ y0 1) hpt.1
      rw [hpt.2, hAy0] at h1
      exact h1.symm
    exact hpar.1 (Work.Mostow.hptOf ξ y0 1) hfixpt

end Work.Mostow
