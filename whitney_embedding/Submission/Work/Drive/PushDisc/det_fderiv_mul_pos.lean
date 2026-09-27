import Mathlib
import Submission.Work.Drive.PushDisc.asymSignDefs

namespace Work.Drive.PushDisc

open scoped ContDiff

/-- **The sign of the Jacobian determinant of a global smooth chart is the same at every pair of
points.**  If `Θ : Mdl k → ℝ^{2(k+1)}` and `Φ` are mutually inverse `C^∞` maps and `J` is a linear
isomorphism, then the determinants of the two composed derivatives

    d(J ∘ Θ) ξ = (LinearMap.comp J.toLinearMap (fderiv ℝ Θ ξ).toLinearMap).det

have the same sign, so their product is positive.  (`dΘ ξ` is injective because
`dΦ (Θ ξ) ∘ dΘ ξ = id`, hence its determinant never vanishes; the determinant is continuous and
`Mdl k` is preconnected, so it cannot change sign.) -/
theorem det_fderiv_mul_pos {k : ℕ}
    (Θ : Work.Drive.Whitney.Mdl k → EuclideanSpace ℝ (Fin (2 * (k + 1))))
    (Φ : EuclideanSpace ℝ (Fin (2 * (k + 1))) → Work.Drive.Whitney.Mdl k)
    (J : EuclideanSpace ℝ (Fin (2 * (k + 1))) ≃ₗ[ℝ] Work.Drive.Whitney.Mdl k)
    (hΘ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Θ)
    (hΦ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (hΘΦ : ∀ y, Θ (Φ y) = y) (hΦΘ : ∀ ξ, Φ (Θ ξ) = ξ) (ξ₁ ξ₂ : Work.Drive.Whitney.Mdl k) :
    0 < (LinearMap.comp J.toLinearMap (fderiv ℝ Θ ξ₁).toLinearMap).det
      * (LinearMap.comp J.toLinearMap (fderiv ℝ Θ ξ₂).toLinearMap).det := by
  have _hsurj : Function.Surjective Θ := fun y => ⟨Φ y, hΘΦ y⟩
  have htop : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  have hdΘ : Differentiable ℝ Θ := hΘ.differentiable htop
  have hdΦ : Differentiable ℝ Φ := hΦ.differentiable htop
  -- Step 1: the chain rule `dΦ (Θ ξ) ∘ dΘ ξ = id`.
  have hchain : ∀ ξ : Work.Drive.Whitney.Mdl k,
      (fderiv ℝ Φ (Θ ξ)).comp (fderiv ℝ Θ ξ)
        = ContinuousLinearMap.id ℝ (Work.Drive.Whitney.Mdl k) := by
    intro ξ
    have h : fderiv ℝ (fun x => Φ (Θ x)) ξ
        = (fderiv ℝ Φ (Θ ξ)).comp (fderiv ℝ Θ ξ) :=
      fderiv_comp (𝕜 := ℝ) (f := Θ) (g := Φ) ξ (hdΦ (Θ ξ)) (hdΘ ξ)
    rw [show (fun x => Φ (Θ x)) = id from funext hΦΘ, fderiv_id] at h
    exact h.symm
  -- Step 2: consequently `dΘ ξ` is injective.
  have hinjD : ∀ ξ : Work.Drive.Whitney.Mdl k,
      Function.Injective (fderiv ℝ Θ ξ).toLinearMap := by
    intro ξ a b hab
    have hab' : (fderiv ℝ Θ ξ) a = (fderiv ℝ Θ ξ) b := hab
    have h1 : (fderiv ℝ Φ (Θ ξ)) ((fderiv ℝ Θ ξ) (a - b)) = a - b := by
      rw [← ContinuousLinearMap.comp_apply, hchain ξ]
      rfl
    have h2 : (fderiv ℝ Θ ξ) (a - b) = 0 := by
      rw [map_sub, hab', sub_self]
    rw [h2] at h1
    simp only [map_zero] at h1
    exact sub_eq_zero.mp h1.symm
  have hK : Function.Injective
      (J.toLinearMap : EuclideanSpace ℝ (Fin (2 * (k + 1))) →ₗ[ℝ] Work.Drive.Whitney.Mdl k) := by
    simpa [LinearEquiv.coe_toLinearMap] using J.injective
  -- Step 3: the determinant of `dΘ ξ ∘ J` never vanishes.
  have hdet_ne : ∀ ξ : Work.Drive.Whitney.Mdl k,
      ((fderiv ℝ Θ ξ).toLinearMap.comp J.toLinearMap).det ≠ 0 := by
    intro ξ h0
    rw [LinearMap.det_eq_zero_iff_ker_ne_bot] at h0
    apply h0
    rw [LinearMap.ker_eq_bot']
    intro v hv
    have hinj : Function.Injective ((fderiv ℝ Θ ξ).toLinearMap.comp J.toLinearMap) := by
      simpa only [LinearMap.coe_comp] using (hinjD ξ).comp hK
    exact hinj (hv.trans (map_zero _).symm)
  -- Step 4: `ξ ↦ det (dΘ ξ ∘ J)` is continuous.
  have hcont : Continuous fun ξ : Work.Drive.Whitney.Mdl k =>
      ((fderiv ℝ Θ ξ).toLinearMap.comp J.toLinearMap).det := by
    let L : EuclideanSpace ℝ (Fin (2 * (k + 1))) →L[ℝ] Work.Drive.Whitney.Mdl k :=
      LinearMap.toContinuousLinearMap
        (J : EuclideanSpace ℝ (Fin (2 * (k + 1))) →ₗ[ℝ] Work.Drive.Whitney.Mdl k)
    have hcL : Continuous fun ξ : Work.Drive.Whitney.Mdl k => (fderiv ℝ Θ ξ).comp L := by
      have hcf : Continuous (fderiv ℝ Θ) := hΘ.continuous_fderiv (by simp)
      have h1 : Continuous fun ξ : Work.Drive.Whitney.Mdl k =>
          (ContinuousLinearMap.compL ℝ (EuclideanSpace ℝ (Fin (2 * (k + 1))))
            (Work.Drive.Whitney.Mdl k) (EuclideanSpace ℝ (Fin (2 * (k + 1)))))
              (fderiv ℝ Θ ξ) :=
        (ContinuousLinearMap.compL ℝ (EuclideanSpace ℝ (Fin (2 * (k + 1))))
          (Work.Drive.Whitney.Mdl k) (EuclideanSpace ℝ (Fin (2 * (k + 1))))).continuous.comp hcf
      have h2 : Continuous fun ξ : Work.Drive.Whitney.Mdl k =>
          (ContinuousLinearMap.compL ℝ (EuclideanSpace ℝ (Fin (2 * (k + 1))))
            (Work.Drive.Whitney.Mdl k) (EuclideanSpace ℝ (Fin (2 * (k + 1)))))
              (fderiv ℝ Θ ξ) L :=
        Continuous.clm_apply h1 continuous_const
      simpa only [ContinuousLinearMap.compL_apply] using h2
    have hcd := ContinuousLinearMap.continuous_det.comp hcL
    have hcoe : ∀ ξ : Work.Drive.Whitney.Mdl k,
        ((fderiv ℝ Θ ξ).comp L).det
          = ((fderiv ℝ Θ ξ).toLinearMap.comp J.toLinearMap).det := by
      intro ξ
      simp only [ContinuousLinearMap.det, ContinuousLinearMap.toLinearMap_comp]
      simp only [L, LinearMap.coe_toContinuousLinearMap]
    exact hcd.congr hcoe
  -- Step 5: `Mdl k` is preconnected, so the two determinant values have the same sign.
  have hmain : 0 < ((fderiv ℝ Θ ξ₁).toLinearMap.comp J.toLinearMap).det
      * ((fderiv ℝ Θ ξ₂).toLinearMap.comp J.toLinearMap).det := by
    by_contra hcon
    have hcon : ((fderiv ℝ Θ ξ₁).toLinearMap.comp J.toLinearMap).det
        * ((fderiv ℝ Θ ξ₂).toLinearMap.comp J.toLinearMap).det ≤ 0 := not_lt.mp hcon
    have h1 := hdet_ne ξ₁
    have h2 := hdet_ne ξ₂
    have hcases :
        (0 < ((fderiv ℝ Θ ξ₁).toLinearMap.comp J.toLinearMap).det
          ∧ ((fderiv ℝ Θ ξ₂).toLinearMap.comp J.toLinearMap).det < 0)
        ∨ (((fderiv ℝ Θ ξ₁).toLinearMap.comp J.toLinearMap).det < 0
          ∧ 0 < ((fderiv ℝ Θ ξ₂).toLinearMap.comp J.toLinearMap).det) := by
      rw [mul_nonpos_iff] at hcon
      rcases hcon with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · exact Or.inl ⟨lt_of_le_of_ne ha (Ne.symm h1), lt_of_le_of_ne hb h2⟩
      · exact Or.inr ⟨lt_of_le_of_ne ha h1, lt_of_le_of_ne hb (Ne.symm h2)⟩
    have hpc : IsPreconnected (Set.range fun ξ : Work.Drive.Whitney.Mdl k =>
        ((fderiv ℝ Θ ξ).toLinearMap.comp J.toLinearMap).det) := by
      have h := (convex_univ (𝕜 := ℝ) (E := Work.Drive.Whitney.Mdl k)).isPreconnected.image
        (fun ξ => ((fderiv ℝ Θ ξ).toLinearMap.comp J.toLinearMap).det) hcont.continuousOn
      simpa [Set.image_univ] using h
    have hord := hpc.ordConnected
    rcases hcases with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · obtain ⟨ξ, hξ⟩ := hord.out ⟨ξ₂, rfl⟩ ⟨ξ₁, rfl⟩ ⟨le_of_lt hb, le_of_lt ha⟩
      exact hdet_ne ξ hξ
    · obtain ⟨ξ, hξ⟩ := hord.out ⟨ξ₁, rfl⟩ ⟨ξ₂, rfl⟩ ⟨le_of_lt ha, le_of_lt hb⟩
      exact hdet_ne ξ hξ
  -- Step 6: replace `J ∘ dΘ` by its conjugate `dΘ ∘ J`.
  have hconj : ∀ ξ : Work.Drive.Whitney.Mdl k,
      LinearMap.det (LinearMap.comp J.toLinearMap (fderiv ℝ Θ ξ).toLinearMap)
        = LinearMap.det ((fderiv ℝ Θ ξ).toLinearMap.comp J.toLinearMap) := by
    intro ξ
    have h := LinearMap.det_conj
      (f := LinearMap.comp J.toLinearMap (fderiv ℝ Θ ξ).toLinearMap) (e := J.symm)
    rw [← h]
    congr 1
    refine LinearMap.ext fun v => ?_
    simp [LinearMap.comp_apply]
  rw [hconj ξ₁, hconj ξ₂]
  exact hmain

end Work.Drive.PushDisc
