import Mathlib
import Submission.Work.Surf.transfer_defs
import Submission.Work.Surf.raySet_persist_one_dim

/-!
# Persistence of the face ray-meeting data under a small `C¹` perturbation

`Work.Surf.Trans.face_persist`: for a `C¹` map `F : 𝔼² → 𝔼²`, a non-zero `v` and a face `i` of the unit
square, if the set `FaceRaySet F v i` of parameters at which `F` meets the open ray `ℝ_{>0} • v` on the
`i`-th face is finite, contained in the *interior* `(0,1)` of the face, transverse (the derivative of
`t ↦ det2 (F (facePt i t)) v` does not vanish there) and *separated* in the sense of the hypothesis
`hsep` (every point of the face at which `F` is close to the ray lies near a genuine ray-meeting
point), then every `C¹` map `G` which is `δ`-close to `F` in the `C¹`-sense for a suitable `δ > 0` has
the same properties: `FaceRaySet G v i` is finite, contained in `(0,1)`, and transverse.

The one-dimensional engine is `Work.Surf.raySet_persist_one_dim` (a variant of
`Work.Surf.zeroSet_persist_one_dim` in which the "anti-ray" gap hypothesis is replaced by the
separation hypothesis `hsep`, and whose conclusion includes the transversality of the perturbed
ray-meeting points).  It is applied to the functions
`t ↦ faceDet F v i t = det2 (F (facePt i t)) v` and `t ↦ faceInn F v i t = ⟪F (facePt i t), v⟫`; the
`C¹`-closeness of `G` to `F` on the square `sqBox` transfers to a `C⁰`-closeness of these functions
and of the derivative of `faceDet` on `[0,1]`, with the factor `‖v‖` (`abs_faceDet_sub_le`,
`abs_faceInn_sub_le`, `abs_deriv_faceDet_sub_le`), which is why the explicit bound
`δ = δ₀ / (‖v‖ + 1)` appears.
-/

namespace Work.Surf.Trans

open Set Metric
open scoped Topology

noncomputable section


/-- The parametrisation of a face of the unit square is `C¹`. -/
lemma contDiff_facePt (i : Fin 4) : ContDiff ℝ 1 (facePt i) := by
  rw [contDiff_one_iff_deriv]
  refine ⟨fun t => (hasDerivAt_facePt i t).differentiableAt, ?_⟩
  have h : deriv (facePt i) = fun _ : ℝ => faceDirN i := by
    funext t; exact (hasDerivAt_facePt i t).deriv
  rw [h]; exact continuous_const

/-- The determinant against `v` along a face of a `C¹` map is `C¹`. -/
lemma contDiff_faceDet (H : E2 → E2) (hH : ContDiff ℝ 1 H) (v : E2) (i : Fin 4) :
    ContDiff ℝ 1 (faceDet H v i) := by
  have h1 : ContDiff ℝ 1 (fun t : ℝ => det2CLM v (H (facePt i t))) :=
    (det2CLM v).contDiff.comp (hH.comp (contDiff_facePt i))
  show ContDiff ℝ 1 (fun t : ℝ => Work.Drive.det2 (H (facePt i t)) v)
  simpa only [det2CLM_apply] using h1

theorem face_persist (F : E2 → E2) (hF : ContDiff ℝ 1 F) {v : E2} (hv : v ≠ 0) (i : Fin 4)
    (hSfin : (FaceRaySet F v i).Finite)
    (hSint : FaceRaySet F v i ⊆ Set.Ioo 0 1)
    (htrans : ∀ p ∈ FaceRaySet F v i, deriv (faceDet F v i) p ≠ 0)
    (hsep : ∀ ε > 0, ∃ δA > 0, ∀ t ∈ Set.Icc 0 1, |Work.Drive.det2 (F (facePt i t)) v| ≤ δA →
      -δA ≤ inner ℝ (F (facePt i t)) v → ∃ p ∈ FaceRaySet F v i, |t - p| < ε) :
    ∃ δ > 0, ∀ G : E2 → E2, ContDiff ℝ 1 G →
      (∀ x ∈ sqBox, ‖G x - F x‖ < δ) → (∀ x ∈ sqBox, ‖fderiv ℝ G x - fderiv ℝ F x‖ < δ) →
      (FaceRaySet G v i).Finite ∧ FaceRaySet G v i ⊆ Set.Ioo 0 1 ∧
        ∀ t ∈ FaceRaySet G v i, deriv (faceDet G v i) t ≠ 0 := by
  classical
  have hS_eq_F : FaceRaySet F v i =
      {t : ℝ | t ∈ Set.Icc (0 : ℝ) 1 ∧ faceDet F v i t = 0 ∧ 0 < faceInn F v i t} := by
    rw [FaceRaySet_eq F hv i]; rfl
  have hfin : ({t : ℝ | t ∈ Set.Icc (0 : ℝ) 1 ∧ faceDet F v i t = 0 ∧
      0 < faceInn F v i t}).Finite := by
    rw [← hS_eq_F]; exact hSfin
  have hint : ({t : ℝ | t ∈ Set.Icc (0 : ℝ) 1 ∧ faceDet F v i t = 0 ∧ 0 < faceInn F v i t}) ⊆
      Set.Ioo (0 : ℝ) 1 := by
    rw [← hS_eq_F]; exact hSint
  have htrans' : ∀ t ∈ Set.Icc (0 : ℝ) 1, faceDet F v i t = 0 → 0 < faceInn F v i t →
      deriv (faceDet F v i) t ≠ 0 := by
    intro t ht h1 h2
    exact htrans t (by rw [hS_eq_F]; exact ⟨ht, h1, h2⟩)
  have hsep' : ∀ ε > 0, ∃ δA > 0, ∀ t ∈ Set.Icc (0 : ℝ) 1, |faceDet F v i t| ≤ δA →
      -δA ≤ faceInn F v i t →
      ∃ p ∈ {t : ℝ | t ∈ Set.Icc (0 : ℝ) 1 ∧ faceDet F v i t = 0 ∧ 0 < faceInn F v i t},
        |t - p| < ε := by
    intro ε hε
    obtain ⟨δA, hδApos, hδA⟩ := hsep ε hε
    refine ⟨δA, hδApos, ?_⟩
    intro t ht h1 h2
    obtain ⟨p, hp, hpt⟩ := hδA t ht h1 h2
    exact ⟨p, by rw [← hS_eq_F]; exact hp, hpt⟩
  obtain ⟨δ₀, hδ₀pos, hδ₀⟩ := Work.Surf.raySet_persist_one_dim (faceDet F v i)
    (contDiff_faceDet F hF v i) (faceInn F v i) hfin hint htrans' hsep'
  refine ⟨δ₀ / (‖v‖ + 1), by positivity, ?_⟩
  intro G hG hG0 hG1
  have hcpos : (0 : ℝ) < ‖v‖ + 1 := by positivity
  have hδle : δ₀ / (‖v‖ + 1) * ‖v‖ ≤ δ₀ := by
    have h1 : ‖v‖ / (‖v‖ + 1) ≤ 1 := by
      rw [div_le_one hcpos]; linarith [norm_nonneg v]
    calc δ₀ / (‖v‖ + 1) * ‖v‖ = δ₀ * (‖v‖ / (‖v‖ + 1)) := by ring
      _ ≤ δ₀ * 1 := mul_le_mul_of_nonneg_left h1 hδ₀pos.le
      _ = δ₀ := mul_one _
  have hb1 : ∀ t ∈ Set.Icc (0 : ℝ) 1, |faceDet G v i t - faceDet F v i t| ≤ δ₀ := by
    intro t ht
    have hx : facePt i t ∈ sqBox := (facePt_mem_sqBox i t).mpr ht
    calc |faceDet G v i t - faceDet F v i t|
        ≤ ‖G (facePt i t) - F (facePt i t)‖ * ‖v‖ := abs_faceDet_sub_le G F v i t
      _ ≤ (δ₀ / (‖v‖ + 1)) * ‖v‖ :=
          mul_le_mul_of_nonneg_right (le_of_lt (hG0 (facePt i t) hx)) (norm_nonneg v)
      _ ≤ δ₀ := hδle
  have hb2 : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      |deriv (faceDet G v i) t - deriv (faceDet F v i) t| ≤ δ₀ := by
    intro t ht
    have hx : facePt i t ∈ sqBox := (facePt_mem_sqBox i t).mpr ht
    calc |deriv (faceDet G v i) t - deriv (faceDet F v i) t|
        ≤ ‖fderiv ℝ G (facePt i t) - fderiv ℝ F (facePt i t)‖ * ‖v‖ :=
          abs_deriv_faceDet_sub_le G F hG hF v i t
      _ ≤ (δ₀ / (‖v‖ + 1)) * ‖v‖ :=
          mul_le_mul_of_nonneg_right (le_of_lt (hG1 (facePt i t) hx)) (norm_nonneg v)
      _ ≤ δ₀ := hδle
  have hb3 : ∀ t ∈ Set.Icc (0 : ℝ) 1, |faceInn G v i t - faceInn F v i t| ≤ δ₀ := by
    intro t ht
    have hx : facePt i t ∈ sqBox := (facePt_mem_sqBox i t).mpr ht
    calc |faceInn G v i t - faceInn F v i t|
        ≤ ‖G (facePt i t) - F (facePt i t)‖ * ‖v‖ := abs_faceInn_sub_le G F v i t
      _ ≤ (δ₀ / (‖v‖ + 1)) * ‖v‖ :=
          mul_le_mul_of_nonneg_right (le_of_lt (hG0 (facePt i t) hx)) (norm_nonneg v)
      _ ≤ δ₀ := hδle
  obtain ⟨h1, h2, h3⟩ := hδ₀ (faceDet G v i) (faceInn G v i) (contDiff_faceDet G hG v i)
    hb1 hb2 hb3
  have hS_eq_G : FaceRaySet G v i =
      {t : ℝ | t ∈ Set.Icc (0 : ℝ) 1 ∧ faceDet G v i t = 0 ∧ 0 < faceInn G v i t} := by
    rw [FaceRaySet_eq G hv i]; rfl
  exact ⟨by rw [hS_eq_G]; exact h1, by rw [hS_eq_G]; exact h2, by rw [hS_eq_G]; exact h3⟩

end

end Work.Surf.Trans

