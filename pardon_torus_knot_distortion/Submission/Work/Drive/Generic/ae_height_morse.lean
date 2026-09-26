import Mathlib
import Submission.Work.Drive.Generic.HeightDefs
import Submission.Work.Drive.Generic.contDiff_gaussParam
import Submission.Work.Drive.Generic.fderiv_gaussParam
import Submission.Work.Drive.Generic.fderiv_height_eq_zero_iff
import Submission.Work.Drive.Generic.fderiv_fderiv_height_eq
import Submission.Work.Drive.Generic.inner_fderiv_normal_d1
import Submission.Work.Drive.Generic.inner_fderiv_normal_d2
import Submission.Work.Drive.Generic.normal_ne_zero

/-! Guidance from the project lead (the requester):

LEAD'S DESIGN (P1(i) of the sideways sweep: the tilted wall direction v must make the height x_v = ⟪v, ·⟫ Morse on the torus surface).
Classical Gauss-map argument, entirely in Mathlib terms; no periodicity needed.
1. Let N(p) = ∂₁Φ(p) × ∂₂Φ(p) (a cross product in ℝ³; nonzero by himm). p is critical for h_v = ⟪v, Φ⟫ iff ⟪v, ∂ᵢΦ(p)⟫ = 0 for i = 1, 2
   iff v = t·N(p) for some t ∈ ℝ.
2. Define G : (ℝ × ℝ) × ℝ → ℝ³, G(p, t) = t·N(p) (C², since Φ is C³). At a critical point with v = t·N(p) and t ≠ 0, the Hessian of h_v is
   t·⟪N(p), ∂ᵢ∂ⱼΦ(p)⟫ (the second fundamental form times t), and det dG(p,t) = t²·(nonzero factor)·det Hess (compute dG: ∂_t G = N, ∂ᵢG = t ∂ᵢN,
   and ⟪∂ᵢN, ∂ⱼΦ⟫ = −⟪N, ∂ᵢ∂ⱼΦ⟫ by differentiating ⟪N, ∂ⱼΦ⟫ = 0). So v is a critical VALUE of G whenever h_v has a degenerate critical point
   (v ≠ 0). For v = 0, a single point, which is null.
3. Sard in equal dimension is in Mathlib: MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero (applied to G on the set where
   det dG = 0). Transfer (ℝ × ℝ) × ℝ ≃ ℝ³ by a linear equiv for the Haar measure. Hence the set of bad v is null.
Hints: state the key identity ⟪∂ᵢN, ∂ⱼΦ⟫ = −⟪N, ∂ᵢ∂ⱼΦ⟫ as its own lemma; use fderiv of the cross product via bilinearity (crossProduct is
bilinear on Fin 3 → ℝ; EuclideanSpace ℝ (Fin 3) is WithLp, so convert with the WithLp equiv). Delegate the determinant computation and the
Sard application separately.
-/

namespace Work.Drive.Generic

open scoped Matrix RealInnerProductSpace
open MeasureTheory

/-! ## Proof of the Morse property for almost every height

The argument (Gauss map, no compactness or periodicity needed).

* A direction `v` is *critical* at `p` when `v` is orthogonal to both partial derivatives
  `∂₁Φ(p), ∂₂Φ(p)`, i.e. when `v` is a multiple of the normal vector `N(p) = ∂₁Φ ⨯ ∂₂Φ`; this is
  `fderiv_height_eq_zero_iff` together with `exists_smul_normal_of_crit`.
* At such a `p`, writing `v = t · N(p)` with `t ≠ 0`, the Hessian of the height
  `q ↦ ⟪v, Φ q⟫` is `t` times the second fundamental form
  `(w, w') ↦ ⟪N(p), D²Φ(p)(w, w')⟫` (`fderiv_fderiv_height_eq`).
* If that form is degenerate, say `w ≠ 0` with `⟪N(p), D²Φ(p)(w, ·)⟫ = 0`, then the identity
  `⟪∂ᵢN, ∂ⱼΦ⟫ = -⟪N, ∂ᵢ∂ⱼΦ⟫` (`inner_fderiv_normal_d1`, `inner_fderiv_normal_d2`) shows that
  `dN_p(w)` is orthogonal to the tangent plane, hence a multiple `c · N(p)` of the normal; thus
  `(w, -t c)` lies in the kernel of the differential at `(p, t)` of the parametrisation
  `G(z) = z 2 • N(z 0, z 1)`, so `det dG(p,t) = 0`.
* Hence every bad direction other than `0` is a critical value of `G`, and by Sard's theorem
  (`addHaar_image_eq_zero_of_det_fderivWithin_eq_zero`, in dimension `3`) the set of critical
  values is null; `0` is a point. So the bad set is null.
-/

variable {Φ : ℝ × ℝ → E3}

/-- If `v ≠ 0` is a critical direction of the height `q ↦ ⟪v, Φ q⟫` at `p`, then `v` is a nonzero
multiple of the normal `N(p)`. -/
lemma exists_smul_normal_of_crit (hΦ : ContDiff ℝ 3 Φ)
    (himm : ∀ p, Function.Injective (fderiv ℝ Φ p)) {v : E3} {p : ℝ × ℝ}
    (hcrit : fderiv ℝ (fun q => inner ℝ v (Φ q)) p = 0) (hv : v ≠ 0) :
    ∃ t : ℝ, t ≠ 0 ∧ v = t • normal Φ p := by
  obtain ⟨h1, h2⟩ := (fderiv_height_eq_zero_iff hΦ v p).mp hcrit
  have hN := normal_ne_zero hΦ himm p
  have hcross : crossE v (normal Φ p) = 0 := by
    rw [normal, crossE_crossE]
    have h1' : inner ℝ (d1 Φ p) v = 0 := by rw [real_inner_comm]; exact h1
    have h2' : inner ℝ (d2 Φ p) v = 0 := by rw [real_inner_comm]; exact h2
    rw [h2, h1']
    simp
  obtain ⟨t, ht⟩ := exists_smul_of_crossE_eq_zero hcross hN
  refine ⟨t, ?_, ht⟩
  rintro rfl
  exact hv (by simpa using ht)

/-- If the second fundamental form `(w, w') ↦ ⟪N(p), D²Φ(p)(w,w')⟫` is degenerate in the direction
`w`, then `dN_p(w)` is a multiple of the normal `N(p)`. -/
lemma exists_smul_normal_fderiv_eq_zero (hΦ : ContDiff ℝ 3 Φ)
    (himm : ∀ p, Function.Injective (fderiv ℝ Φ p)) {p : ℝ × ℝ} {w : ℝ × ℝ}
    (hdeg : ∀ w' : ℝ × ℝ, inner ℝ (normal Φ p) (D2 Φ p w w') = 0) :
    ∃ c : ℝ, fderiv ℝ (normal Φ) p w = c • normal Φ p := by
  have h1 : inner ℝ (fderiv ℝ (normal Φ) p w) (d1 Φ p) = 0 := by
    rw [inner_fderiv_normal_d1 hΦ p w, hdeg (1, 0), neg_zero]
  have h2 : inner ℝ (fderiv ℝ (normal Φ) p w) (d2 Φ p) = 0 := by
    rw [inner_fderiv_normal_d2 hΦ p w, hdeg (0, 1), neg_zero]
  have hcross : crossE (fderiv ℝ (normal Φ) p w) (normal Φ p) = 0 := by
    rw [normal, crossE_crossE]
    have h1' : inner ℝ (d1 Φ p) (fderiv ℝ (normal Φ) p w) = 0 := by
      rw [real_inner_comm]; exact h1
    rw [h2, h1']
    simp
  exact exists_smul_of_crossE_eq_zero hcross (normal_ne_zero hΦ himm p)

/-- A degenerate critical point of a height with direction `v = t • N(p)`, `t ≠ 0`, makes the
parametrisation `G` of the critical directions singular at `(p, t)`. -/
lemma det_fderiv_gaussParam_toE3_eq_zero (hΦ : ContDiff ℝ 3 Φ)
    (himm : ∀ p, Function.Injective (fderiv ℝ Φ p)) {p : ℝ × ℝ} {t : ℝ} (_ht : t ≠ 0)
    {w : ℝ × ℝ} (hw : w ≠ 0)
    (hdeg : ∀ w' : ℝ × ℝ, inner ℝ (normal Φ p) (D2 Φ p w w') = 0) :
    (fderiv ℝ (gaussParam Φ) (toE3 p t)).det = 0 := by
  obtain ⟨c, hc⟩ := exists_smul_normal_fderiv_eq_zero hΦ himm hdeg
  set y : E3 := toE3 w (-(t * c)) with hydef
  have hy0 : y 0 = w.1 := rfl
  have hy1 : y 1 = w.2 := rfl
  have hy2 : y 2 = -(t * c) := rfl
  have hyne : y ≠ 0 := by
    intro h
    apply hw
    refine Prod.ext ?_ ?_
    · show w.1 = (0 : ℝ × ℝ).1
      rw [← hy0, h]; simp
    · show w.2 = (0 : ℝ × ℝ).2
      rw [← hy1, h]; simp
  have hyw : (y 0, y 1) = w := by simp [hy0, hy1]
  have hfy : fderiv ℝ (gaussParam Φ) (toE3 p t) y = 0 := by
    rw [fderiv_gaussParam hΦ (toE3 p t) y]
    simp only [toE3_apply_zero, toE3_apply_one, toE3_apply_two, hy2, hyw, Prod.mk.eta]
    rw [hc, smul_smul, neg_smul]
    exact neg_add_cancel _
  rw [show (fderiv ℝ (gaussParam Φ) (toE3 p t)).det =
      LinearMap.det (fderiv ℝ (gaussParam Φ) (toE3 p t)).toLinearMap by simp,
    LinearMap.det_eq_zero_iff_ker_ne_bot]
  intro hbot
  exact hyne ((Submodule.eq_bot_iff _).mp hbot y (LinearMap.mem_ker.mpr hfy))

/-- Every bad direction is `0` or a critical value of the Gauss parametrisation `G`. -/
lemma badSet_subset (hΦ : ContDiff ℝ 3 Φ)
    (himm : ∀ p, Function.Injective (fderiv ℝ Φ p)) :
    badSet Φ ⊆ {0} ∪ gaussParam Φ '' critSet Φ := by
  rintro v hv
  simp only [badSet, Set.mem_ofPred_eq] at hv
  push Not at hv
  obtain ⟨p, hcrit, hdeg⟩ := hv
  by_cases h0 : v = 0
  · exact Or.inl h0
  · right
    obtain ⟨t, ht, hvt⟩ := exists_smul_normal_of_crit hΦ himm hcrit h0
    refine ⟨toE3 p t, ?_, ?_⟩
    · simp only [critSet, Set.mem_ofPred_eq]
      obtain ⟨w, hwA, hw⟩ := hdeg
      have hdeg' : ∀ w' : ℝ × ℝ, inner ℝ (normal Φ p) (D2 Φ p w w') = 0 := by
        intro w'
        have h1 : fderiv ℝ (fderiv ℝ (fun q => inner ℝ v (Φ q))) p w w' = 0 := hwA w'
        rw [fderiv_fderiv_height_eq hΦ v p w w'] at h1
        rw [hvt] at h1
        rw [inner_smul_left] at h1
        simpa using (mul_eq_zero.mp h1).resolve_left ht
      exact det_fderiv_gaussParam_toE3_eq_zero hΦ himm ht hw hdeg'
    · rw [gaussParam_toE3, hvt]

/-- The bad set has measure zero. -/
lemma volume_badSet_eq_zero (hΦ : ContDiff ℝ 3 Φ)
    (himm : ∀ p, Function.Injective (fderiv ℝ Φ p)) :
    volume (badSet Φ) = 0 := by
  have hdiff : Differentiable ℝ (gaussParam Φ) :=
    (contDiff_gaussParam hΦ).differentiable (by norm_num)
  have hS : volume (gaussParam Φ '' critSet Φ) = 0 := by
    refine addHaar_image_eq_zero_of_det_fderivWithin_eq_zero (μ := volume) (f := gaussParam Φ)
      (f' := fun z => fderiv ℝ (gaussParam Φ) z) (s := critSet Φ) ?_ ?_
    · intro z hz
      exact (hdiff z).hasFDerivAt.hasFDerivWithinAt
    · intro z hz
      exact hz
  refine le_antisymm ?_ bot_le
  calc volume (badSet Φ) ≤ volume ({0} ∪ gaussParam Φ '' critSet Φ) :=
        measure_mono (badSet_subset hΦ himm)
    _ ≤ volume ({0} : Set E3) + volume (gaussParam Φ '' critSet Φ) := measure_union_le _ _
    _ = 0 := by rw [hS, measure_singleton, add_zero]

/-- For a `C³` immersion `Φ` of the plane into `ℝ³`, almost every vector `v` gives a height `⟪v, Φ ·⟫`
all of whose critical points are nondegenerate. -/
theorem ae_height_morse {Φ : ℝ × ℝ → EuclideanSpace ℝ (Fin 3)} (hΦ : ContDiff ℝ 3 Φ)
    (himm : ∀ p, Function.Injective (fderiv ℝ Φ p)) :
    ∀ᵐ v ∂(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))),
      ∀ p : ℝ × ℝ, fderiv ℝ (fun q => inner ℝ v (Φ q)) p = 0 →
        ∀ w : ℝ × ℝ, (∀ w' : ℝ × ℝ, fderiv ℝ (fderiv ℝ (fun q => inner ℝ v (Φ q))) p w w' = 0) → w = 0 := by
  rw [MeasureTheory.ae_iff]
  exact volume_badSet_eq_zero hΦ himm

end Work.Drive.Generic
