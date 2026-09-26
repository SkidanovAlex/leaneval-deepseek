import Mathlib
import Submission.Work.Drive.Final.AnyEventDefs
import Submission.Work.Drive.Final.eventGates
import Submission.Work.Drive.Final.cornerRegionChart_pathConnected
import Submission.Work.Drive.Final.fderiv_boxNorm_par_active
import Submission.Work.Drive.Final.cornerLevelPieceDown
import Submission.Work.Smooth.Morse.Surface.isOpenInCarrier_image_of_isOpen
import Submission.Work.BoxShrink.Pinch.Basic

set_option maxHeartbeats 2000000

namespace Work.Drive.Final

open LeanEval.KnotTheory.PardonDistortion Set

noncomputable section

theorem cornerGates {ψ : Submission.Diffeo} {K : LeanEval.KnotTheory.PardonDistortion.Knot} {s R : ℝ}
    {c : LeanEval.KnotTheory.PardonDistortion.R3}
    {σ : Equiv.Perm (Fin 3)} {u : ℝ} {v : LeanEval.KnotTheory.PardonDistortion.R3} {h : ℝ}
    {ℓ : LeanEval.KnotTheory.PardonDistortion.R3 →L[ℝ] ℝ} {exc : Finset ℝ}
    {lam0 lam1 : ℝ}
    (hG : Work.Drive.Final.GoodSweepData3 ψ K s c σ u v h R ℓ exc lam0 lam1)
    {p : ℝ × ℝ} (hp : Work.Drive.Final.IsCornerEvent ψ s c σ u v h p) :
    ∃ (E U₁ U₂ : Set LeanEval.KnotTheory.PardonDistortion.R3), IsOpen E ∧
      Work.BoxShrink.Pinch.par ψ p ∈ E ∧
      (U₁ = ∅ ∨ IsPathConnected U₁) ∧ (U₂ = ∅ ∨ IsPathConnected U₂) ∧
      (Work.Drive.EpsFormSphere.openTiltedSweepRegion (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ
          (Work.Drive.Final.eventValue ψ ℓ p) ∩ E = U₁ ∪ U₂) := by

  classical
  obtain ⟨hDP2, hEF, hBelt, hSBCR, hGT, hFRC, hCross, hOffK, hOne, hSC⟩ := hG
  obtain ⟨hGSD, hBoxGen, hℓsingle, hNoEventFace, hFaceND, hTripleReg⟩ := hDP2
  obtain ⟨hTilt, hAbove, hBelow, hOffK0, hKnotGP⟩ := hGSD
  have hh : 0 < h := hTilt.2.2.2.2.2.1
  have hcarrier : Work.BoxShrink.Pinch.par ψ p ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier :=
    Work.BoxShrink.Pinch.par_mem_carrier ψ p
  have hslab' : |inner ℝ v (Work.BoxShrink.Pinch.par ψ p) - (inner ℝ v c + u)| = h := by
    simpa [Work.Drive.Final.slabFn_apply] using hp.2.2
  have hbelt : |(Work.BoxShrink.Pinch.par ψ p) (σ 2) - c (σ 2)| < Submission.boxSide 2 * s :=
    hBelt _ hcarrier hp.1 (le_of_eq hp.2.2)
  have hs : 0 < s := by
    have h1 := Submission.boxSide_pos 2
    nlinarith [abs_nonneg ((Work.BoxShrink.Pinch.par ψ p) (σ 2) - c (σ 2)), hbelt, h1]
  have hbelt' : |(Work.BoxShrink.Pinch.par ψ p) (σ 2) - c (σ 2)| / Submission.boxSide 2 < s := by
    rw [div_lt_iff₀ (Submission.boxSide_pos 2)]
    simpa [mul_comm] using hbelt
  have hle : ∀ m : Fin 3, |(Work.BoxShrink.Pinch.par ψ p) (σ m) - c (σ m)|
      / Submission.boxSide m ≤ s := by
    intro m
    have h := hp.2.1
    rw [Submission.boxNorm] at h
    fin_cases m
    · calc |_| / Submission.boxSide 0 ≤ max (|(Work.BoxShrink.Pinch.par ψ p) (σ 0) - c (σ 0)| / Submission.boxSide 0)
            (|(Work.BoxShrink.Pinch.par ψ p) (σ 1) - c (σ 1)| / Submission.boxSide 1) := le_max_left _ _
        _ ≤ max (max _ _) (|(Work.BoxShrink.Pinch.par ψ p) (σ 2) - c (σ 2)| / Submission.boxSide 2) :=
            le_max_left _ _
        _ = s := h
    · calc |_| / Submission.boxSide 1 ≤ max (|(Work.BoxShrink.Pinch.par ψ p) (σ 0) - c (σ 0)| / Submission.boxSide 0)
            (|(Work.BoxShrink.Pinch.par ψ p) (σ 1) - c (σ 1)| / Submission.boxSide 1) := le_max_right _ _
        _ ≤ max (max _ _) (|(Work.BoxShrink.Pinch.par ψ p) (σ 2) - c (σ 2)| / Submission.boxSide 2) :=
            le_max_left _ _
        _ = s := h
    · calc |_| / Submission.boxSide 2 ≤ max (max _ _) (|(Work.BoxShrink.Pinch.par ψ p) (σ 2) - c (σ 2)| / Submission.boxSide 2) :=
            le_max_right _ _
        _ = s := h
  obtain ⟨k, hk⟩ : ∃ k : Fin 3, |(Work.BoxShrink.Pinch.par ψ p) (σ k) - c (σ k)| / Submission.boxSide k = s := by
    have h := hp.2.1
    rw [Submission.boxNorm] at h
    rcases (max_eq_iff.mp h) with ⟨h1, _⟩ | ⟨h2, _⟩
    · rcases (max_eq_iff.mp h1) with ⟨h1', _⟩ | ⟨h1', _⟩
      · exact ⟨0, h1'⟩
      · exact ⟨1, h1'⟩
    · exact ⟨2, h2⟩
  have hk2 : k = 2 → False := by
    intro hk2
    rw [hk2] at hk
    linarith [hbelt']
  have hkabs : |(Work.BoxShrink.Pinch.par ψ p) (σ k) - c (σ k)| = Submission.boxSide k * s := by
    rw [div_eq_iff (ne_of_gt (Submission.boxSide_pos k))] at hk
    linarith [hk]
  have hk_ne : k ≠ 2 := fun h2 => hk2 h2
  have huniq : ∀ j : Fin 3, j ≠ k → |(Work.BoxShrink.Pinch.par ψ p) (σ j) - c (σ j)| < Submission.boxSide j * s := by
    intro j hj
    by_cases hj2 : j = 2
    · rw [hj2]; exact hbelt
    · have hne : |(Work.BoxShrink.Pinch.par ψ p) (σ j) - c (σ j)| ≠ Submission.boxSide j * s := by
        intro heq
        have := hEF _ hcarrier hp.2.1 ⟨k, j, Ne.symm hj, hkabs, heq⟩
        rw [hslab'] at this
        exact absurd this (lt_irrefl h)
      have hlej := hle j
      rw [div_le_iff₀ (Submission.boxSide_pos j)] at hlej
      rw [mul_comm] at hlej
      exact lt_of_le_of_ne hlej hne
  -- ### signs
  obtain ⟨ε, hε, hεi⟩ : ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧
      (Work.BoxShrink.Pinch.par ψ p) (σ k) - c (σ k) = ε * (Submission.boxSide k * s) := by
    rcases (abs_eq (le_of_lt (mul_pos (Submission.boxSide_pos k) hs))).mp hkabs with hh' | hh'
    · exact ⟨1, Or.inl rfl, by rw [hh', one_mul]⟩
    · exact ⟨-1, Or.inr rfl, by rw [hh']; ring⟩
  have hεsq : ε * ε = 1 := by rcases hε with hh' | hh' <;> rw [hh'] <;> norm_num
  have hεabs : |ε| = 1 := by rcases hε with hh' | hh' <;> rw [hh'] <;> norm_num
  obtain ⟨η, hη, hηx⟩ : ∃ η : ℝ, (η = 1 ∨ η = -1) ∧
      Work.Drive.Final.slabFn c u v (Work.BoxShrink.Pinch.par ψ p) = η * h := by
    rcases (abs_eq (le_of_lt hh)).mp hp.2.2 with hh' | hh'
    · exact ⟨1, Or.inl rfl, by rw [hh', one_mul]⟩
    · exact ⟨-1, Or.inr rfl, by rw [hh']; ring⟩
  have hηsq : η * η = 1 := by rcases hη with hh' | hh' <;> rw [hh'] <;> norm_num
  have hηabs : |η| = 1 := by rcases hη with hh' | hh' <;> rw [hh'] <;> norm_num
  -- ### the two chart functionals
  set A : ℝ := Submission.boxSide k * s with hAdef
  set uFn : ℝ × ℝ → ℝ := fun q => ε * ((Work.BoxShrink.Pinch.par ψ q) (σ k) - c (σ k)) - A with huFndef
  set vFn : ℝ × ℝ → ℝ := fun q => η * Work.Drive.Final.slabFn c u v (Work.BoxShrink.Pinch.par ψ q) - h with hvFndef
  have hxA : (Work.BoxShrink.Pinch.par ψ p) (σ k) - c (σ k) = ε * A := by rw [hAdef]; exact hεi
  have hup : uFn p = 0 := by
    have h1 : uFn p = ε * ((Work.BoxShrink.Pinch.par ψ p) (σ k) - c (σ k)) - A := by rw [huFndef]
    rw [h1, hxA, ← mul_assoc, hεsq, one_mul, sub_self]
  have hvp : vFn p = 0 := by
    have h1 : vFn p = η * Work.Drive.Final.slabFn c u v (Work.BoxShrink.Pinch.par ψ p) - h := by rw [hvFndef]
    rw [h1, hηx, ← mul_assoc, hηsq, one_mul, sub_self]
  have hukey : ∀ q : ℝ × ℝ, uFn q = ε * ((Work.BoxShrink.Pinch.par ψ q) (σ k) - c (σ k)) - Submission.boxSide k * s := by
    intro q
    have h1 : uFn q = ε * ((Work.BoxShrink.Pinch.par ψ q) (σ k) - c (σ k)) - A := by rw [huFndef]
    rw [h1, hAdef]
  have hvkey : ∀ q : ℝ × ℝ, vFn q = η * (inner ℝ v (Work.BoxShrink.Pinch.par ψ q) - (inner ℝ v c + u)) - h := by
    intro q
    have h1 : vFn q = η * Work.Drive.Final.slabFn c u v (Work.BoxShrink.Pinch.par ψ q) - h := by rw [hvFndef]
    rw [h1, Work.Drive.Final.slabFn_apply]
  -- ### continuity/smoothness
  have hcoord_cd : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : ℝ × ℝ => (Work.BoxShrink.Pinch.par ψ q) (σ k)) p :=
    ((EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) (σ k)).contDiff.contDiffAt.comp p
      (Work.BoxShrink.Pinch.par_contDiff ψ).contDiffAt)
  have hinner_cd : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) p :=
    ((innerSL ℝ v).contDiff.contDiffAt.comp p (Work.BoxShrink.Pinch.par_contDiff ψ).contDiffAt)
  have hu_cd : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) uFn p := by
    rw [huFndef]
    exact ((contDiffAt_const (c := ε)).mul (hcoord_cd.sub contDiffAt_const)).sub contDiffAt_const
  have hv_cd : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) vFn p := by
    rw [hvFndef]
    simp only [Work.Drive.Final.slabFn_apply]
    exact ((contDiffAt_const (c := η)).mul
      ((hinner_cd.sub (contDiffAt_const (c := inner ℝ v c + u))))).sub
      (contDiffAt_const (c := h))
  have hΘ_cd : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : ℝ × ℝ => (uFn q, vFn q)) p :=
    hu_cd.prodMk hv_cd
  -- ### derivatives
  have hu_deriv : fderiv ℝ uFn p = ε • fderiv ℝ (fun q : ℝ × ℝ => (Work.BoxShrink.Pinch.par ψ q) (σ k)) p := by
    rw [huFndef]
    have hdiff : DifferentiableAt ℝ (fun q : ℝ × ℝ => (Work.BoxShrink.Pinch.par ψ q) (σ k) - c (σ k)) p :=
      (hcoord_cd.differentiableAt (by simp)).sub_const _
    rw [fderiv_sub_const, fderiv_const_mul hdiff ε, fderiv_sub_const]
  have hv_deriv : fderiv ℝ vFn p =
      η • fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) p := by
    rw [hvFndef]
    simp only [Work.Drive.Final.slabFn_apply]
    have hdiff : DifferentiableAt ℝ (fun q : ℝ × ℝ =>
        inner ℝ v (Work.BoxShrink.Pinch.par ψ q) - (inner ℝ v c + u)) p :=
      (hinner_cd.differentiableAt (by simp)).sub_const _
    rw [fderiv_sub_const, fderiv_const_mul hdiff η, fderiv_sub_const]
  -- ### the pair used by SlabBoxCrossReg
  have hp_deriv : fderiv ℝ (fun q : ℝ × ℝ =>
      ((Work.BoxShrink.Pinch.par ψ q) (σ k), inner ℝ v (Work.BoxShrink.Pinch.par ψ q))) p
      = (fderiv ℝ (fun q : ℝ × ℝ => (Work.BoxShrink.Pinch.par ψ q) (σ k)) p).prod
        (fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) p) := by
    have h1 : HasFDerivAt (fun q : ℝ × ℝ => (Work.BoxShrink.Pinch.par ψ q) (σ k))
        (fderiv ℝ (fun q : ℝ × ℝ => (Work.BoxShrink.Pinch.par ψ q) (σ k)) p) p :=
      (hcoord_cd.differentiableAt (by simp)).hasFDerivAt
    have h2 : HasFDerivAt (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q))
        (fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) p) p :=
      (hinner_cd.differentiableAt (by simp)).hasFDerivAt
    exact (h1.prodMk h2).fderiv
  have hSBCRapp := hSBCR k hk_ne ε hε η hη p (by linarith [hεi]) (by
    rw [Work.Drive.Final.slabFn_apply] at hηx
    linarith [hηx])
  have hTinv' : ((fderiv ℝ (fun q : ℝ × ℝ => (Work.BoxShrink.Pinch.par ψ q) (σ k)) p).prod
      (fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) p)).IsInvertible := by
    rw [← hp_deriv]; exact hSBCRapp
  -- ### the chart
  let Llin : (ℝ × ℝ) ≃ₗ[ℝ] (ℝ × ℝ) :=
    { toFun := fun ξ => (ε * ξ.1, η * ξ.2)
      invFun := fun ξ => (ε * ξ.1, η * ξ.2)
      left_inv := by
        intro ξ
        exact Prod.ext (by show ε * (ε * ξ.1) = ξ.1; rw [← mul_assoc, hεsq, one_mul])
          (by show η * (η * ξ.2) = ξ.2; rw [← mul_assoc, hηsq, one_mul])
      right_inv := by
        intro ξ
        exact Prod.ext (by show ε * (ε * ξ.1) = ξ.1; rw [← mul_assoc, hεsq, one_mul])
          (by show η * (η * ξ.2) = ξ.2; rw [← mul_assoc, hηsq, one_mul])
      map_add' := by
        intro a b
        exact Prod.ext (by show ε * (a.1 + b.1) = ε * a.1 + ε * b.1; ring)
          (by show η * (a.2 + b.2) = η * a.2 + η * b.2; ring)
      map_smul' := by
        intro a b
        exact Prod.ext (by show ε * (a * b.1) = a * (ε * b.1); ring)
          (by show η * (a * b.2) = a * (η * b.2); ring) }
  let L : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ) := Llin.toContinuousLinearEquiv
  have hLkey : ∀ w : ℝ × ℝ, (L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))
      ((fderiv ℝ (fun q : ℝ × ℝ => (Work.BoxShrink.Pinch.par ψ q) (σ k)) p) w,
       (fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) p) w)
      = ((ε • fderiv ℝ (fun q : ℝ × ℝ => (Work.BoxShrink.Pinch.par ψ q) (σ k)) p).prod
         (η • fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) p)) w := by
    intro w
    simp only [ContinuousLinearMap.prod_apply, ContinuousLinearMap.smul_apply, L, Llin,
      LinearEquiv.coe_toContinuousLinearEquiv]
    rfl
  have hInv : (fderiv ℝ (fun q : ℝ × ℝ => (uFn q, vFn q)) p).IsInvertible := by
    have h1 : HasFDerivAt (fun q : ℝ × ℝ => (uFn q, vFn q))
        ((fderiv ℝ uFn p).prod (fderiv ℝ vFn p)) p :=
      (hu_cd.differentiableAt (by simp)).hasFDerivAt.prodMk
        (hv_cd.differentiableAt (by simp)).hasFDerivAt
    have h2 : fderiv ℝ (fun q : ℝ × ℝ => (uFn q, vFn q)) p
        = (L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)).comp
          ((fderiv ℝ (fun q : ℝ × ℝ => (Work.BoxShrink.Pinch.par ψ q) (σ k)) p).prod
            (fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) p)) := by
      rw [h1.fderiv, hu_deriv, hv_deriv]
      exact ContinuousLinearMap.ext fun w => hLkey w
    rw [h2]
    exact ContinuousLinearMap.IsInvertible.comp ⟨L, rfl⟩ hTinv'
  obtain ⟨Ae, hAe⟩ : ∃ Ae : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ),
      Ae = fderiv ℝ (fun q : ℝ × ℝ => (uFn q, vFn q)) p := hInv
  have hAe' : fderiv ℝ (fun q : ℝ × ℝ => (uFn q, vFn q)) p = (Ae : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) := hAe.symm
  have hAtt : HasFDerivAt (fun q : ℝ × ℝ => (uFn q, vFn q)) (Ae : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) p := by
    have h2 : HasFDerivAt (fun q : ℝ × ℝ => (uFn q, vFn q))
        (fderiv ℝ (fun q : ℝ × ℝ => (uFn q, vFn q)) p) p :=
      (hΘ_cd.differentiableAt (by simp)).hasFDerivAt
    rwa [hAe'] at h2
  let Θc : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ) :=
    ContDiffAt.toOpenPartialHomeomorph (f := fun q : ℝ × ℝ => (uFn q, vFn q)) (f' := Ae) hΘ_cd hAtt (by simp)
  have hcoe : (Θc : ℝ × ℝ → ℝ × ℝ) = fun q => (uFn q, vFn q) :=
    ContDiffAt.toOpenPartialHomeomorph_coe _ _ _
  have hpsrc : p ∈ Θc.source := ContDiffAt.mem_toOpenPartialHomeomorph_source _ _ _
  have hfunp : (uFn p, vFn p) = (0 : ℝ × ℝ) := Prod.ext hup hvp
  have hfunp' : (fun q : ℝ × ℝ => (uFn q, vFn q)) p = (0 : ℝ × ℝ) := hfunp
  have h0tgt : (0 : ℝ × ℝ) ∈ Θc.target := by
    have h := ContDiffAt.image_mem_toOpenPartialHomeomorph_target (f := fun q : ℝ × ℝ => (uFn q, vFn q))
      (f' := Ae) hΘ_cd hAtt (by simp)
    rw [hfunp] at h
    exact h
  have hsymm0 : Θc.symm 0 = p := by
    have h := Θc.left_inv hpsrc
    rw [hcoe] at h
    rw [hfunp'] at h
    exact h
  have hΘp : Θc p = 0 := by
    show (fun q : ℝ × ℝ => (uFn q, vFn q)) p = 0
    simp [hup, hvp]
  -- ### the level function in the chart
  have hsymm_cd : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun ξ : ℝ × ℝ => Θc.symm ξ) 0 := by
    refine Θc.contDiffAt_symm (f₀' := Ae) h0tgt ?_ ?_
    · rw [hsymm0, hcoe]; exact hAtt
    · rw [hsymm0, hcoe]; exact hΘ_cd
  set W : ℝ × ℝ → ℝ :=
    fun ξ => ℓ (Work.BoxShrink.Pinch.par ψ (Θc.symm ξ)) - Work.Drive.Final.eventValue ψ ℓ p
    with hWdef
  have hWfun : W = fun ξ : ℝ × ℝ =>
      ℓ (Work.BoxShrink.Pinch.par ψ (Θc.symm ξ)) - Work.Drive.Final.eventValue ψ ℓ p := hWdef
  have hW0 : W 0 = 0 := by
    show ℓ (Work.BoxShrink.Pinch.par ψ (Θc.symm 0)) - Work.Drive.Final.eventValue ψ ℓ p = 0
    rw [hsymm0, Work.Drive.Final.eventValue, sub_self]
  have hW_cd : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W 0 := by
    rw [hWfun]
    have h2 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun ξ : ℝ × ℝ => ℓ (Work.BoxShrink.Pinch.par ψ (Θc.symm ξ))) 0 :=
      ℓ.contDiff.contDiffAt.comp 0
        ((Work.BoxShrink.Pinch.par_contDiff ψ).contDiffAt.comp 0 hsymm_cd)
    exact h2.sub contDiffAt_const
  have hW_diff : DifferentiableAt ℝ W 0 := hW_cd.differentiableAt (by simp)
  -- the chain rule: `fderiv (l . par) p = fderiv W 0 . fderiv Theta p`
  have hprodh : HasFDerivAt (fun q : ℝ × ℝ => (uFn q, vFn q))
      ((fderiv ℝ uFn p).prod (fderiv ℝ vFn p)) p :=
    (hu_cd.differentiableAt (by simp)).hasFDerivAt.prodMk
      (hv_cd.differentiableAt (by simp)).hasFDerivAt
  have hpr : fderiv ℝ (fun q : ℝ × ℝ => (uFn q, vFn q)) p
      = (fderiv ℝ uFn p).prod (fderiv ℝ vFn p) := hprodh.fderiv
  have heq : (W ∘ fun q : ℝ × ℝ => (uFn q, vFn q)) =ᶠ[nhds p]
      (fun q : ℝ × ℝ => ℓ (Work.BoxShrink.Pinch.par ψ q) - Work.Drive.Final.eventValue ψ ℓ p) := by
    filter_upwards [Θc.open_source.mem_nhds hpsrc] with q hq
    have h2 : Θc.symm ((fun q : ℝ × ℝ => (uFn q, vFn q)) q) = q := by
      rw [← hcoe]
      exact Θc.left_inv hq
    show ℓ (Work.BoxShrink.Pinch.par ψ (Θc.symm ((fun q : ℝ × ℝ => (uFn q, vFn q)) q))) -
      Work.Drive.Final.eventValue ψ ℓ p = ℓ (Work.BoxShrink.Pinch.par ψ q) -
      Work.Drive.Final.eventValue ψ ℓ p
    rw [h2]
  have hchain : fderiv ℝ (fun q : ℝ × ℝ => ℓ (Work.BoxShrink.Pinch.par ψ q)) p
      = (fderiv ℝ W 0).comp (fderiv ℝ (fun q : ℝ × ℝ => (uFn q, vFn q)) p) := by
    have hshift : fderiv ℝ (fun q : ℝ × ℝ => ℓ (Work.BoxShrink.Pinch.par ψ q)
        - Work.Drive.Final.eventValue ψ ℓ p) p
        = fderiv ℝ (fun q : ℝ × ℝ => ℓ (Work.BoxShrink.Pinch.par ψ q)) p :=
      fderiv_sub_const _
    rw [← hshift, ← heq.fderiv_eq]
    rw [fderiv_comp p (by rw [hfunp]; exact hW_diff) (hΘ_cd.differentiableAt (by simp)), hfunp]
  -- ### the derivative of the box norm composed with the parametrisation
  have hbn_deriv : fderiv ℝ (fun q : ℝ × ℝ => Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q)) p
      = (1 / Submission.boxSide k) • fderiv ℝ uFn p := by
    rw [Work.Drive.Final.fderiv_boxNorm_par_active ψ c σ s hε hs hεi huniq, hu_deriv]
    refine ContinuousLinearMap.ext fun w => ?_
    simp only [smul_apply, smul_eq_mul]
    ring_nf
  have hγne : ∀ t : ℝ, fderiv ℝ (fun q : ℝ × ℝ => ℓ (Work.BoxShrink.Pinch.par ψ q)) p ≠
      t • fderiv ℝ (fun q : ℝ × ℝ => Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q)) p :=
    fun t => (hGT p hp.2.1 (le_of_eq hp.2.2)).2 t
  -- ### the second partial derivative of `W` at `0` is nonzero
  have hWderiv_ne : fderiv ℝ W 0 (0, 1) ≠ 0 := by
    intro hzero
    have hrepr : ∃ cc : ℝ, fderiv ℝ W 0 = cc • ContinuousLinearMap.fst ℝ ℝ ℝ := by
      refine ⟨fderiv ℝ W 0 (1, 0), ?_⟩
      refine ContinuousLinearMap.ext fun w => ?_
      have hdecomp : w = w.1 • ((1 : ℝ), (0 : ℝ)) + w.2 • ((0 : ℝ), (1 : ℝ)) := by
        ext <;> simp
      have hkey : (fderiv ℝ W 0) w
          = w.1 * (fderiv ℝ W 0) (1, 0) + w.2 * (fderiv ℝ W 0) (0, 1) := by
        conv_lhs => rw [hdecomp]
        rw [map_add, map_smul, map_smul]
        simp only [smul_eq_mul]
      rw [hkey, hzero]
      simp only [mul_zero, add_zero]
      rw [smul_apply, show (ContinuousLinearMap.fst ℝ ℝ ℝ) w = w.1 from rfl]
      ring
    obtain ⟨cc, hcc⟩ := hrepr
    have hgamma : fderiv ℝ (fun q : ℝ × ℝ => ℓ (Work.BoxShrink.Pinch.par ψ q)) p
        = cc • fderiv ℝ uFn p := by
      rw [hchain]
      refine ContinuousLinearMap.ext fun w => ?_
      have h1 : ((fderiv ℝ W 0).comp (fderiv ℝ (fun q : ℝ × ℝ => (uFn q, vFn q)) p)) w
          = (fderiv ℝ W 0) (((fderiv ℝ uFn p).prod (fderiv ℝ vFn p)) w) := by
        rw [ContinuousLinearMap.comp_apply, hpr]
      rw [h1, ContinuousLinearMap.prod_apply, hcc]
      simp
    have hbn' : fderiv ℝ (fun q : ℝ × ℝ => Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q)) p
        = (1 / Submission.boxSide k) • fderiv ℝ uFn p := hbn_deriv
    rcases eq_or_ne (fderiv ℝ uFn p) 0 with hz | hnz
    · have h0 : fderiv ℝ (fun q : ℝ × ℝ => ℓ (Work.BoxShrink.Pinch.par ψ q)) p = 0 := by
        rw [hgamma, hz, smul_zero]
      exact (hγne 0) (by rw [h0]; simp)
    · have hbne : Submission.boxSide k ≠ 0 := ne_of_gt (Submission.boxSide_pos k)
      have h := hγne (cc * Submission.boxSide k)
      rw [hbn', hgamma] at h
      apply h
      rw [smul_smul, mul_one_div, mul_div_assoc, div_self hbne, mul_one]

  -- ### the local description of the box and of the slab
  have hdesc : ∀ᶠ q in nhds p,
      (Work.BoxShrink.Pinch.par ψ q ∈ Submission.PBox s c σ ↔ uFn q < 0) ∧
      (Work.BoxShrink.Pinch.par ψ q ∈
          Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h ↔ vFn q ≤ 0) := by
    have hcontk : Continuous (fun q : ℝ × ℝ =>
        ε * ((Work.BoxShrink.Pinch.par ψ q) (σ k) - c (σ k))) :=
      (continuous_const.mul (((EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) (σ k)).continuous.comp
        (Work.BoxShrink.Pinch.par_continuous ψ)).sub continuous_const))
    have hcontη : Continuous (fun q : ℝ × ℝ =>
        η * (inner ℝ v (Work.BoxShrink.Pinch.par ψ q) - (inner ℝ v c + u))) :=
      (continuous_const.mul ((continuous_const.inner (Work.BoxShrink.Pinch.par_continuous ψ)).sub
        continuous_const))
    have hslack : ∀ᶠ q in nhds p, ∀ m : Fin 3, m ≠ k →
        |(Work.BoxShrink.Pinch.par ψ q) (σ m) - c (σ m)| < Submission.boxSide m * s := by
      rw [Filter.eventually_all]
      intro m
      by_cases hm : m = k
      · exact Filter.Eventually.of_forall fun q hq => absurd hm hq
      · have hcont : Continuous (fun q : ℝ × ℝ =>
            |(Work.BoxShrink.Pinch.par ψ q) (σ m) - c (σ m)|) :=
          (((EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) (σ m)).continuous.comp
            (Work.BoxShrink.Pinch.par_continuous ψ)).sub continuous_const).abs
        filter_upwards [(isOpen_lt hcont continuous_const).mem_nhds (by simpa using huniq m hm)]
          with q hq
        intro _
        exact hq
    have hsigε : ∀ᶠ q in nhds p, -(Submission.boxSide k * s) <
        ε * ((Work.BoxShrink.Pinch.par ψ q) (σ k) - c (σ k)) :=
      (isOpen_lt continuous_const hcontk).mem_nhds (by
        show -(Submission.boxSide k * s) < ε * ((Work.BoxShrink.Pinch.par ψ p) (σ k) - c (σ k))
        rw [hxA, hAdef, ← mul_assoc, hεsq, one_mul]
        have := Submission.boxSide_pos k
        nlinarith [hs])
    have hsigη : ∀ᶠ q in nhds p, -h < η *
        (inner ℝ v (Work.BoxShrink.Pinch.par ψ q) - (inner ℝ v c + u)) :=
      (isOpen_lt continuous_const hcontη).mem_nhds (by
        show -h < η * (inner ℝ v (Work.BoxShrink.Pinch.par ψ p) - (inner ℝ v c + u))
        have h1 : inner ℝ v (Work.BoxShrink.Pinch.par ψ p) - (inner ℝ v c + u)
            = Work.Drive.Final.slabFn c u v (Work.BoxShrink.Pinch.par ψ p) := by
          rw [Work.Drive.Final.slabFn_apply]
        rw [h1, hηx, ← mul_assoc, hηsq, one_mul]
        linarith)
    filter_upwards [hslack, hsigε, hsigη] with q hsl hsε hsη
    refine ⟨?_, ?_⟩
    · rw [Submission.mem_PBox, hukey q]
      constructor
      · intro hbox
        have h1 : |ε * ((Work.BoxShrink.Pinch.par ψ q) (σ k) - c (σ k))| < Submission.boxSide k * s := by
          rw [abs_mul, hεabs, one_mul]
          exact hbox k
        exact sub_neg.mpr (abs_lt.mp h1).2
      · intro hlt m
        by_cases hm : m = k
        · rw [hm]
          have h2 : ε * ((Work.BoxShrink.Pinch.par ψ q) (σ k) - c (σ k))
              < Submission.boxSide k * s := sub_neg.mp hlt
          have h1 : |ε * ((Work.BoxShrink.Pinch.par ψ q) (σ k) - c (σ k))|
              < Submission.boxSide k * s := abs_lt.mpr ⟨hsε, h2⟩
          rwa [abs_mul, hεabs, one_mul] at h1
        · exact hsl m hm
    · rw [Work.Drive.EpsForm.tiltedSlabClosed, Set.mem_ofPred_eq, hvkey q]
      have h1 : |η * (inner ℝ v (Work.BoxShrink.Pinch.par ψ q) - (inner ℝ v c + u))|
          = |inner ℝ v (Work.BoxShrink.Pinch.par ψ q) - (inner ℝ v c + u)| := by
        rw [abs_mul, hηabs, one_mul]
      constructor
      · intro h
        rw [← h1] at h
        linarith [(abs_le.mp h).2]
      · intro h
        rw [← h1, abs_le]
        exact ⟨le_of_lt hsη, by linarith⟩


  -- ### smallness data
  obtain ⟨ρW, hρW, hW1_on⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ContDiffOn ℝ 1 W (Metric.ball (0:ℝ×ℝ) ρ) := by
    have h1 : ContDiffAt ℝ (1 : WithTop ℕ∞) W 0 := hW_cd.of_le (by simp)
    obtain ⟨u, hu, hucd⟩ : ∃ u ∈ nhds (0:ℝ×ℝ), ContDiffOn ℝ (1:ℕ) W u := by
      have hh := (contDiffWithinAt_iff_contDiffOn_nhds (𝕜 := ℝ) (f := W) (x := (0:ℝ×ℝ))
        (s := Set.univ) (n := (1:ℕ)) (by simp)).mp h1
      simpa using hh
    obtain ⟨ρ, hρ, hsub⟩ := Metric.mem_nhds_iff.mp hu
    exact ⟨ρ, hρ, hucd.mono hsub⟩
  set M : ℝ := ‖fderiv ℝ W 0‖ + 1 with hMdef
  have hMpos : 0 < M := by rw [hMdef]; positivity
  obtain ⟨ρM, hρM, hMbound⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ∀ ξ : ℝ × ℝ, ‖ξ‖ < ρ → ‖fderiv ℝ W ξ‖ ≤ M := by
    have hcont : ContinuousAt (fderiv ℝ W) 0 := hW_cd.continuousAt_fderiv (by simp)
    obtain ⟨ρ, hρ, hρ'⟩ := Metric.continuousAt_iff.mp hcont 1 (by norm_num)
    refine ⟨ρ, hρ, fun ξ hξ => ?_⟩
    have h1 : dist (fderiv ℝ W ξ) (fderiv ℝ W 0) < 1 := hρ' (by simpa using hξ)
    rw [dist_eq_norm] at h1
    have h2 : ‖fderiv ℝ W ξ‖ ≤ ‖fderiv ℝ W ξ - fderiv ℝ W 0‖ + ‖fderiv ℝ W 0‖ := by
      have h3 := norm_add_le (fderiv ℝ W ξ - fderiv ℝ W 0) (fderiv ℝ W 0)
      simpa using h3
    rw [hMdef]
    linarith
  obtain ⟨ρsign, hρsign, hsign⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ∀ ξ : ℝ × ℝ, ‖ξ‖ < ρ →
      |fderiv ℝ W ξ (0, 1) - fderiv ℝ W 0 (0, 1)| < |fderiv ℝ W 0 (0, 1)| / 2 := by
    have hcont : ContinuousAt (fderiv ℝ W) 0 := hW_cd.continuousAt_fderiv (by simp)
    obtain ⟨ρ, hρ, hρ'⟩ := Metric.continuousAt_iff.mp hcont (|fderiv ℝ W 0 (0,1)| / 2)
      (by positivity)
    refine ⟨ρ, hρ, fun ξ hξ => ?_⟩
    have h1 : dist (fderiv ℝ W ξ) (fderiv ℝ W 0) < |fderiv ℝ W 0 (0,1)| / 2 :=
      hρ' (by simpa using hξ)
    have h2 : |fderiv ℝ W ξ (0,1) - fderiv ℝ W 0 (0,1)| ≤ dist (fderiv ℝ W ξ) (fderiv ℝ W 0) := by
      rw [dist_eq_norm]
      calc |fderiv ℝ W ξ (0,1) - fderiv ℝ W 0 (0,1)|
          = |(fderiv ℝ W ξ - fderiv ℝ W 0) (0,1)| := by rw [sub_apply]
        _ = ‖(fderiv ℝ W ξ - fderiv ℝ W 0) (0,1)‖ := by rw [Real.norm_eq_abs]
        _ ≤ ‖fderiv ℝ W ξ - fderiv ℝ W 0‖ * ‖((0:ℝ), (1:ℝ))‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ = ‖fderiv ℝ W ξ - fderiv ℝ W 0‖ := by simp
    linarith
  obtain ⟨ρd, hρd, hρd'⟩ : ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball p ρ ⊆
      {q : ℝ × ℝ | (Work.BoxShrink.Pinch.par ψ q ∈ Submission.PBox s c σ ↔ uFn q < 0) ∧
        (Work.BoxShrink.Pinch.par ψ q ∈
            Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h ↔ vFn q ≤ 0)} :=
    Metric.mem_nhds_iff.mp hdesc
  obtain ⟨ρt, hρt, hρt'⟩ : ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball (0:ℝ×ℝ) ρ ⊆ Θc.target :=
    Metric.mem_nhds_iff.mp (Θc.open_target.mem_nhds h0tgt)
  have hsymm_cont : ContinuousAt (fun ξ : ℝ × ℝ => Θc.symm ξ) 0 := hsymm_cd.continuousAt
  obtain ⟨ρs, hρs, hρs'⟩ : ∃ ρ : ℝ, 0 < ρ ∧
      ∀ ξ : ℝ × ℝ, ‖ξ‖ < ρ → Θc.symm ξ ∈ Metric.ball p ρd := by
    obtain ⟨ρ, hρ, hρ'⟩ := Metric.continuousAt_iff.mp hsymm_cont ρd hρd
    refine ⟨ρ, hρ, fun ξ hξ => ?_⟩
    have h := hρ' (by simpa [dist_eq_norm] using hξ)
    rw [hsymm0] at h
    rwa [Metric.mem_ball]
  -- ### the two box half-widths
  set dd : ℝ := min (min ρM ρsign) (min ρW (min ρd (min ρt ρs))) with hdddef
  set d : ℝ := dd / 2 with hddef
  have hddpos : 0 < dd := by
    rw [hdddef]
    exact lt_min (lt_min hρM hρsign) (lt_min hρW (lt_min hρd (lt_min hρt hρs)))
  have hd : 0 < d := by rw [hddef]; linarith
  have hdd : d ≤ dd := by rw [hddef]; linarith
  have hdρM : d ≤ ρM := le_trans hdd (le_trans (min_le_left _ _) (min_le_left _ _))
  have hdρsign : d ≤ ρsign := le_trans hdd (le_trans (min_le_left _ _) (min_le_right _ _))
  have hdρW : d ≤ ρW := le_trans hdd (le_trans (min_le_right _ _) (min_le_left _ _))
  have hdρd : d ≤ ρd :=
    le_trans hdd (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hdρt : d ≤ ρt :=
    le_trans hdd (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (min_le_left _ _))))
  have hdρs : d ≤ ρs :=
    le_trans hdd (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (min_le_right _ _))))
  set e : ℝ := min (d / 2) (|fderiv ℝ W 0 (0,1)| * d / (8 * M)) with hedef
  have he : 0 < e := by
    rw [hedef]
    exact lt_min (by linarith) (by positivity)
  have hed : e ≤ d := by
    rw [hedef]
    exact le_trans (min_le_left _ _) (by linarith)
  have heM : M * e < |fderiv ℝ W 0 (0,1)| * d / 4 := by
    have h1 : e ≤ |fderiv ℝ W 0 (0,1)| * d / (8 * M) := by rw [hedef]; exact min_le_right _ _
    have h2 : M * e ≤ M * (|fderiv ℝ W 0 (0,1)| * d / (8 * M)) :=
      mul_le_mul_of_nonneg_left h1 (le_of_lt hMpos)
    have h3 : M * (|fderiv ℝ W 0 (0,1)| * d / (8 * M)) = |fderiv ℝ W 0 (0,1)| * d / 8 := by
      field_simp
    rw [h3] at h2
    have h4 : 0 < |fderiv ℝ W 0 (0,1)| * d :=
      mul_pos (abs_pos.mpr hWderiv_ne) hd
    linarith
  set Bx : Set (ℝ × ℝ) := Set.Ioo (-e) e ×ˢ Set.Ioo (-d) d with hBxdef
  have hBx_norm : ∀ ξ : ℝ × ℝ, ξ ∈ Bx → ‖ξ‖ < d := by
    intro ξ hξ
    rw [hBxdef, Set.mem_prod, Set.mem_Ioo, Set.mem_Ioo] at hξ
    have h1 : |ξ.1| < d := by
      rw [abs_lt]
      exact ⟨by linarith [hξ.1.1, hed], by linarith [hξ.1.2, hed]⟩
    have h2 : |ξ.2| < d := abs_lt.mpr hξ.2
    rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
    exact max_lt h1 h2
  have hBx_tgt : ∀ ξ ∈ Bx, ξ ∈ Metric.ball (0:ℝ×ℝ) ρt := fun ξ hξ =>
    Metric.mem_ball.mpr (by rw [dist_zero_right]; exact lt_of_lt_of_le (hBx_norm ξ hξ) hdρt)
  -- ### the open set of the parameter plane
  set O : Set (ℝ × ℝ) := Θc.symm '' Bx with hOdef
  have hOopen : IsOpen O := by
    rw [hOdef]
    refine Θc.isOpen_image_symm_of_subset_target (isOpen_Ioo.prod isOpen_Ioo) ?_
    intro ξ hξ
    exact hρt' (hBx_tgt ξ hξ)
  have hpO : p ∈ O := by
    rw [hOdef]
    refine ⟨0, ?_, hsymm0⟩
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
      · simp only [Prod.fst_zero, Prod.snd_zero]
        linarith
  have hdescO : ∀ q ∈ O,
      (Work.BoxShrink.Pinch.par ψ q ∈ Submission.PBox s c σ ↔ uFn q < 0) ∧
      (Work.BoxShrink.Pinch.par ψ q ∈
          Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h ↔ vFn q ≤ 0) := by
    intro q hq
    rw [hOdef] at hq
    obtain ⟨ξ, hξ, hξeq⟩ := hq
    refine hρd' ?_
    rw [← hξeq]
    exact hρs' ξ (lt_of_lt_of_le (hBx_norm ξ hξ) hdρs)
  have hopenIn : Work.SurgeryInvariance.IsOpenInCarrier (Work.Drive.EpsSphere.torusOf ψ)
      (Work.BoxShrink.Pinch.par ψ '' O) := by
    have h := Work.Smooth.Morse.Surface.isOpenInCarrier_image_of_isOpen ψ hOopen
    simpa only [Work.Drive.EpsSphere.torusOf, Work.Smooth.Morse.torus,
      Work.BoxShrink.Pinch.par_def, Work.Smooth.Morse.param_def] using h
  obtain ⟨E, hEopen, hEeq⟩ := (isOpen_induced_iff.mp hopenIn :
    ∃ W : Set R3, IsOpen W ∧ Subtype.val ⁻¹' W = Subtype.val ⁻¹' (Work.BoxShrink.Pinch.par ψ '' O))
  have hEcarrier : ∀ y : R3, y ∈ (Work.Smooth.Morse.torus ψ).carrier →
      (y ∈ E ↔ y ∈ Work.BoxShrink.Pinch.par ψ '' O) := by
    intro y hy
    have h1 : (⟨y, hy⟩ : (Work.Smooth.Morse.torus ψ).carrier) ∈ Subtype.val ⁻¹' E ↔
        (⟨y, hy⟩ : (Work.Smooth.Morse.torus ψ).carrier) ∈
          Subtype.val ⁻¹' (Work.BoxShrink.Pinch.par ψ '' O) := by
      rw [hEeq]
    rwa [Set.mem_preimage, Set.mem_preimage] at h1
  -- ### the two chart pieces
  set F : ℝ × ℝ → R3 := fun ξ => Work.BoxShrink.Pinch.par ψ (Θc.symm ξ) with hFdef
  have hF_contOn : ContinuousOn F Bx := by
    rw [hFdef]
    refine (Work.BoxShrink.Pinch.par_continuous ψ).comp_continuousOn ?_
    refine Θc.continuousOn_symm.mono ?_
    intro ξ hξ
    exact hρt' (hBx_tgt ξ hξ)
  set S₁ : Set (ℝ × ℝ) := {ξ : ℝ × ℝ | ξ ∈ Bx ∧ ξ.1 < 0 ∧ 0 < ξ.2} with hS₁def
  set S₂ : Set (ℝ × ℝ) := {ξ : ℝ × ℝ | ξ ∈ Bx ∧ ξ.1 < 0 ∧ 0 < W ξ} with hS₂def
  set S : Set (ℝ × ℝ) := {ξ : ℝ × ℝ | ξ ∈ Bx ∧ ξ.1 < 0 ∧ (0 < ξ.2 ∨ 0 < W ξ)} with hSdef
  have hS_split : S = S₁ ∪ S₂ := by
    rw [hSdef, hS₁def, hS₂def]
    ext ξ
    simp only [Set.mem_union, Set.mem_ofPred_eq]
    tauto
  -- ### the identity of the region
  have hregion : Work.Drive.EpsFormSphere.openTiltedSweepRegion (Work.Drive.EpsSphere.torusOf ψ)
      s c σ u v h ℓ (Work.Drive.Final.eventValue ψ ℓ p) ∩ E = F '' S := by
    ext y
    constructor
    · rintro ⟨hyreg, hyE⟩
      rw [Work.Drive.Final.mem_openTiltedSweepRegion_iff] at hyreg
      obtain ⟨hyc, hybox, hcond⟩ := hyreg
      obtain ⟨q, hqO, hqeq⟩ := (hEcarrier y hyc).mp hyE
      have hqsrc : q ∈ Θc.source := by
        rw [hOdef] at hqO
        obtain ⟨ξ, hξ, hξeq⟩ := hqO
        rw [← hξeq]
        exact Θc.map_target (hρt' (hBx_tgt ξ hξ))
      have hΘq : Θc q = (uFn q, vFn q) := by simpa using congrFun hcoe q
      have hdescq := hdescO q hqO
      have h1 : uFn q < 0 := hdescq.1.mp (by rw [hqeq]; exact hybox)
      have h2 : 0 < vFn q ∨ Work.Drive.Final.eventValue ψ ℓ p < ℓ y := by
        rcases hcond with hcond | hcond | hcond
        · left
          rw [← hqeq] at hcond
          have hgo : ¬ (Work.BoxShrink.Pinch.par ψ q ∈
              Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h) := by
            rw [Work.Drive.EpsForm.tiltedSlabClosed, Set.mem_ofPred_eq]
            intro hc
            have hcl := (abs_le.mp hc).2
            linarith
          by_contra hcon
          exact hgo (hdescq.2.mpr (le_of_not_gt hcon))
        · left
          rw [← hqeq] at hcond
          have hgo : ¬ (Work.BoxShrink.Pinch.par ψ q ∈
              Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h) := by
            rw [Work.Drive.EpsForm.tiltedSlabClosed, Set.mem_ofPred_eq]
            intro hc
            have hcl := (abs_le.mp hc).1
            linarith
          by_contra hcon
          exact hgo (hdescq.2.mpr (le_of_not_gt hcon))
        · right
          exact hcond
      refine ⟨Θc q, ?_, ?_⟩
      · rw [hSdef]
        refine ⟨?_, ?_, ?_⟩
        · rw [hOdef] at hqO
          obtain ⟨ξ, hξ, hξeq⟩ := hqO
          have htgt : ξ ∈ Θc.target := hρt' (hBx_tgt ξ hξ)
          rw [← hξeq, Θc.right_inv htgt]
          exact hξ
        · rw [hΘq]; exact h1
        · rcases h2 with h2 | h2
          · exact Or.inl (by rw [hΘq]; exact h2)
          · refine Or.inr ?_
            have hWq : W (Θc q) = ℓ y - Work.Drive.Final.eventValue ψ ℓ p := by
              show ℓ (Work.BoxShrink.Pinch.par ψ (Θc.symm (Θc q))) -
                Work.Drive.Final.eventValue ψ ℓ p = ℓ y - Work.Drive.Final.eventValue ψ ℓ p
              rw [Θc.left_inv hqsrc, hqeq]
            rw [hWq]
            linarith
      · rw [hFdef]
        show Work.BoxShrink.Pinch.par ψ (Θc.symm (Θc q)) = y
        rw [Θc.left_inv hqsrc, hqeq]
    · rintro ⟨ξ, hξS, hξeq⟩
      rw [hFdef] at hξeq
      rw [hSdef] at hξS
      obtain ⟨hξbox, hξneg, hξcond⟩ := hξS
      have htgt : ξ ∈ Θc.target := hρt' (hBx_tgt ξ hξbox)
      have hq : Θc.symm ξ ∈ Θc.source := Θc.map_target htgt
      have hΘq : Θc (Θc.symm ξ) = ξ := Θc.right_inv htgt
      have hqO : Θc.symm ξ ∈ O := ⟨ξ, hξbox, rfl⟩
      have hdescq := hdescO (Θc.symm ξ) hqO
      have hu : uFn (Θc.symm ξ) = ξ.1 := by
        have h := congrArg Prod.fst hΘq
        simpa [hcoe] using h
      have hv : vFn (Θc.symm ξ) = ξ.2 := by
        have h := congrArg Prod.snd hΘq
        simpa [hcoe] using h
      have hWy : W ξ = ℓ y - Work.Drive.Final.eventValue ψ ℓ p := by
        show ℓ (Work.BoxShrink.Pinch.par ψ (Θc.symm ξ)) -
          Work.Drive.Final.eventValue ψ ℓ p = ℓ y - Work.Drive.Final.eventValue ψ ℓ p
        rw [← hξeq]
      refine ⟨?_, ?_⟩
      · rw [Work.Drive.Final.mem_openTiltedSweepRegion_iff]
        refine ⟨?_, ?_, ?_⟩
        · rw [← hξeq]
          exact Work.BoxShrink.Pinch.par_mem_carrier ψ _
        · rw [← hξeq]
          exact hdescq.1.mpr (by rw [hu]; exact hξneg)
        · rcases hξcond with hξc | hξc
          · have hgo : ¬ (Work.BoxShrink.Pinch.par ψ (Θc.symm ξ) ∈
                Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h) := by
              intro hc
              have hcl := hdescq.2.mp hc
              rw [hv] at hcl
              linarith
            rw [Work.Drive.EpsForm.tiltedSlabClosed, Set.mem_ofPred_eq] at hgo
            rw [not_le] at hgo
            rcases lt_abs.mp hgo with hgo | hgo
            · exact Or.inl (by rw [← hξeq]; linarith)
            · exact Or.inr (Or.inl (by rw [← hξeq]; linarith))
          · refine Or.inr (Or.inr ?_)
            rw [hWy] at hξc
            linarith
      · rw [hEcarrier y (by rw [← hξeq]; exact Work.BoxShrink.Pinch.par_mem_carrier ψ _)]
        exact ⟨Θc.symm ξ, hqO, hξeq⟩
  -- ### the two cases on the sign of the second partial derivative
  by_cases hsign0 : 0 < fderiv ℝ W 0 (0, 1)
  · -- UP
    have hderpos : ∀ ξ : ℝ × ℝ, ξ ∈ Bx → 0 < fderiv ℝ W ξ (0, 1) := by
      intro ξ hξ
      have h1 : ‖ξ‖ < ρsign := lt_of_lt_of_le (hBx_norm ξ hξ) hdρsign
      have h2 := hsign ξ h1
      rw [abs_of_pos hsign0] at h2
      linarith [(abs_lt.mp h2).1]
    have hmono : ∀ x y y' : ℝ, x ∈ Set.Ioo (-e) e → y ∈ Set.Ioo (-d) d → y' ∈ Set.Ioo y d →
        0 < W (x, y) → 0 < W (x, y') := by
      intro x y y' hx hy hy' hposy
      have hstrict : StrictMonoOn (fun t : ℝ => W (x, t)) (Set.Ioo (-d) d) := by
        refine strictMonoOn_of_deriv_pos (convex_Ioo _ _) ?_ ?_
        · intro t ht
          have hmem : (x, t) ∈ Bx := by
            rw [hBxdef, Set.mem_prod, Set.mem_Ioo, Set.mem_Ioo]
            exact ⟨hx, ht⟩
          have hmemW : (x, t) ∈ Metric.ball (0:ℝ×ℝ) ρW :=
            Metric.mem_ball.mpr (by rw [dist_zero_right]; exact lt_of_lt_of_le (hBx_norm _ hmem) hdρW)
          have hct : ContinuousAt W (x, t) :=
            hW1_on.continuousOn.continuousAt (Metric.isOpen_ball.mem_nhds hmemW)
          exact (hct.comp (continuous_const.prodMk continuous_id).continuousAt).continuousWithinAt
        · intro t ht
          rw [interior_Ioo] at ht
          have hmem : (x, t) ∈ Bx := by
            rw [hBxdef, Set.mem_prod, Set.mem_Ioo, Set.mem_Ioo]
            exact ⟨hx, ht⟩
          have hmemW : (x, t) ∈ Metric.ball (0:ℝ×ℝ) ρW :=
            Metric.mem_ball.mpr (by rw [dist_zero_right]; exact lt_of_lt_of_le (hBx_norm _ hmem) hdρW)
          have hdiff : DifferentiableAt ℝ W (x, t) :=
            hW1_on.differentiableOn_one.differentiableAt (Metric.isOpen_ball.mem_nhds hmemW)
          have hderiv : deriv (fun s : ℝ => W (x, s)) t = fderiv ℝ W (x, t) (0, 1) := by
            have hcurve : HasDerivAt (fun s : ℝ => ((x, s) : ℝ × ℝ)) ((0:ℝ), (1:ℝ)) t :=
              (hasDerivAt_const (x := t) x).prodMk (hasDerivAt_id t)
            exact (hdiff.hasFDerivAt.comp_hasDerivAt t hcurve).deriv
          rw [hderiv]
          exact hderpos (x, t) hmem
      exact lt_trans hposy (hstrict hy ⟨by linarith [hy.1, hy'.1], hy'.2⟩ hy'.1)
    have hSpc : IsPathConnected S := by
      have h := Work.Drive.Final.cornerRegionChart_pathConnected W he hd hmono
      rw [hSdef, hBxdef]
      exact h
    have hFSpc : IsPathConnected (F '' S) :=
      hSpc.image' (hF_contOn.mono (fun ξ hξ => (hSdef ▸ hξ).1))
    refine ⟨E, F '' S, ∅, hEopen, ?_, Or.inr hFSpc, Or.inl rfl, ?_⟩
    · rw [hEcarrier (Work.BoxShrink.Pinch.par ψ p) (Work.BoxShrink.Pinch.par_mem_carrier ψ p)]
      exact ⟨p, hpO, rfl⟩
    · rw [hregion, Set.union_empty]
  · -- DOWN
    have hneg : fderiv ℝ W 0 (0, 1) < 0 := lt_of_le_of_ne (le_of_not_gt hsign0) hWderiv_ne
    have hmono2 : ∀ ξ : ℝ × ℝ, ξ ∈ Bx → fderiv ℝ W ξ (0, 1) ≤ fderiv ℝ W 0 (0, 1) / 2 := by
      intro ξ hξ
      have h1 : ‖ξ‖ < ρsign := lt_of_lt_of_le (hBx_norm ξ hξ) hdρsign
      have h2 := hsign ξ h1
      rw [abs_of_neg hneg] at h2
      linarith [(abs_lt.mp h2).2]
    have hdiffB : ∀ ξ : ℝ × ℝ, ξ ∈ Set.Ioo (-e) e ×ˢ Set.Ioo (-d) d → DifferentiableAt ℝ W ξ := by
      intro ξ hξ
      have hmemW : ξ ∈ Metric.ball (0:ℝ×ℝ) ρW :=
        Metric.mem_ball.mpr (by rw [dist_zero_right]; exact lt_of_lt_of_le (hBx_norm ξ hξ) hdρW)
      exact hW1_on.differentiableOn_one.differentiableAt (Metric.isOpen_ball.mem_nhds hmemW)
    have hboundB : ∀ ξ : ℝ × ℝ, ξ ∈ Set.Ioo (-e) e ×ˢ Set.Ioo (-d) d → ‖fderiv ℝ W ξ‖ ≤ M := by
      intro ξ hξ
      exact hMbound ξ (lt_of_lt_of_le (hBx_norm ξ hξ) hdρM)
    have hS₂pc : IsPathConnected S₂ := by
      have h := Work.Drive.Final.cornerLevelPieceDown W he hd hneg hMpos hW0 heM hdiffB hboundB
        (fun ξ hξ => hmono2 ξ hξ)
      rw [hS₂def, hBxdef]
      exact h
    have hS₁pc : IsPathConnected S₁ := by
      have hS₁eq : S₁ = Set.Ioo (-e) 0 ×ˢ Set.Ioo (0:ℝ) d := by
        rw [hS₁def, hBxdef]
        ext ξ
        simp only [Set.mem_prod, Set.mem_Ioo, Set.mem_ofPred_eq]
        constructor
        · rintro ⟨⟨⟨h1, h2⟩, h3, h4⟩, h5, h6⟩
          exact ⟨⟨h1, h5⟩, ⟨h6, h4⟩⟩
        · rintro ⟨⟨h1, h5⟩, ⟨h6, h4⟩⟩
          exact ⟨⟨⟨h1, by linarith⟩, by linarith, h4⟩, h5, h6⟩
      rw [hS₁eq]
      exact ((convex_Ioo _ _).prod (convex_Ioo _ _)).isPathConnected
        ⟨(-e/2, d/2), ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩⟩
    refine ⟨E, F '' S₁, F '' S₂, hEopen, ?_, Or.inr ?_, Or.inr ?_, ?_⟩
    · rw [hEcarrier (Work.BoxShrink.Pinch.par ψ p) (Work.BoxShrink.Pinch.par_mem_carrier ψ p)]
      exact ⟨p, hpO, rfl⟩
    · exact hS₁pc.image' (hF_contOn.mono (fun ξ hξ => (hS₁def ▸ hξ).1))
    · exact hS₂pc.image' (hF_contOn.mono (fun ξ hξ => (hS₂def ▸ hξ).1))
    · rw [hregion, hS_split, Set.image_union]

end

end Work.Drive.Final
