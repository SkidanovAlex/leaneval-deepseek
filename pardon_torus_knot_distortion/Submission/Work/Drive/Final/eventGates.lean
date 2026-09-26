import Mathlib
import Submission.Work.Drive.Final.GoodSweepData
import Submission.Work.Drive.Mono.fibreRegion_pathConnected
import Submission.Work.Drive.Mono.Band.BadFaceDefs
import Submission.Work.Smooth.Morse.Surface.isOpenInCarrier_image_of_isOpen
import Submission.Work.Drive.Final.gateNoFace
import Submission.Work.Drive.Final.gateFace
import Submission.Work.Drive.Final.morseLemmaProd
import Submission.Work.Drive.Final.exists_faceMonotoneData
import Submission.Work.Drive.Final.exists_paramDir_inner_ne_zero
import Submission.Work.Drive.Final.exists_mem_doubleCone_of_fderivFst

/-!
# The gates of the tilted sweep at an event

`Work.Drive.Final.eventGates`: at an event `p` of the tilted sweep, the region of the sweep at the
event's level is, inside a suitable open set `E` around `par ψ p`, the union of **two** sets each of
which is empty or path connected.

The proof is local.  By clause (iii) of `Work.Drive.Final.TiltedGenericity` the sweep height is
Morse at `p`, so `Work.Drive.Final.morseLemmaProd` gives a chart `φ` of the parameter plane centred
at `p` in which the height is the normal form `s₁ x² + s₂ y²` (`sᵢ = ±1`).  Two cases:

* *the event is in the interior of the slab*: near `par ψ p` the slab condition is inactive, and the
  region is `{ℓ > ℓ p}` — the superlevel set of the normal form, which is the punctured disc
  (`s₁ = s₂ = 1`), two convex cones (`s₁ s₂ = -1`) or empty (`s₁ = s₂ = -1`):
  `Work.Drive.Final.gateNoFace`;
* *the event is on a slab face*: a linear change of coordinates in the chart puts the active face
  functional in the form `ξ ↦ ξ₁ + o(‖ξ‖)`, so the region is the union of a "half disc" (the face
  side) and the superlevel set of the normal form.  Every straight line in the first coordinate
  stays in the face side (`Work.Drive.Final.exists_faceMonotoneData`), the cones meet the face side
  (`Work.Drive.Final.exists_mem_doubleCone_of_fderivFst`), and `Work.Drive.Final.gateFace` splits the
  union into two path connected pieces.

The open set `E` is produced by the openness of the chart image in the surface
(`Work.Smooth.Morse.Surface.isOpenInCarrier_image_of_isOpen`).
-/

namespace Work.Drive.Final

open LeanEval.KnotTheory.PardonDistortion Set
open Work.BoxShrink.Pinch

noncomputable section

/-- An elementary arithmetic rewriting of the complement of the removed set of the tilted sweep. -/
theorem not_abs_le_and (A B h lam : ℝ) :
    ¬(|A| ≤ h ∧ B ≤ lam) ↔ (0 < A - h ∨ 0 < -A - h ∨ lam < B) := by
  rw [not_and_or, not_le, not_le, lt_abs]
  constructor
  · rintro (h1 | h1)
    · rcases h1 with h1 | h1
      · exact Or.inl (by linarith)
      · exact Or.inr (Or.inl (by linarith))
    · exact Or.inr (Or.inr h1)
  · rintro (h1 | h1 | h1)
    · exact Or.inl (Or.inl (by linarith))
    · exact Or.inl (Or.inr (by linarith))
    · exact Or.inr h1

/-- **Membership in the open region of the tilted sweep**, in terms of the two face functionals
`y ↦ ⟪v,y⟫ - (⟪v,c⟫ + u) - h` and `y ↦ -(⟪v,y⟫ - (⟪v,c⟫ + u)) - h`. -/
theorem mem_openTiltedSweepRegion_iff {ψ : Submission.Diffeo} {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {u : ℝ} {v : R3} {h : ℝ} {ℓ : R3 →L[ℝ] ℝ} {lam : ℝ} {y : R3} :
    y ∈ Work.Drive.EpsFormSphere.openTiltedSweepRegion (Work.Drive.EpsSphere.torusOf ψ)
        s c σ u v h ℓ lam ↔
      y ∈ (Work.Smooth.Morse.torus ψ).carrier ∧ y ∈ Submission.PBox s c σ ∧
        (0 < inner ℝ v y - (inner ℝ v c + u) - h ∨
         0 < -(inner ℝ v y - (inner ℝ v c + u)) - h ∨ lam < ℓ y) := by
  simp only [Work.Drive.EpsFormSphere.openTiltedSweepRegion, Work.Drive.EpsForm.tiltedSlabClosed,
    Work.Drive.EpsSphere.torusOf, Set.mem_inter_iff, Set.mem_sdiff, Set.mem_ofPred_eq]
  rw [not_abs_le_and]

/-- **The region of the sweep does not change when `(v, u)` is replaced by `(-v, -u)`** (the two
faces of the tilted slab are exchanged). -/
theorem openTiltedSweepRegion_neg (ψ : Submission.Diffeo) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) (v : R3) (h : ℝ) (ℓ : R3 →L[ℝ] ℝ) (lam : ℝ) :
    Work.Drive.EpsFormSphere.openTiltedSweepRegion (Work.Drive.EpsSphere.torusOf ψ)
        s c σ (-u) (-v) h ℓ lam =
      Work.Drive.EpsFormSphere.openTiltedSweepRegion (Work.Drive.EpsSphere.torusOf ψ)
        s c σ u v h ℓ lam := by
  ext y
  rw [mem_openTiltedSweepRegion_iff, mem_openTiltedSweepRegion_iff]
  have h1 : inner ℝ (-v) y - (inner ℝ (-v) c + (-u)) = -(inner ℝ v y - (inner ℝ v c + u)) := by
    simp only [inner_neg_left]
    ring
  rw [h1, neg_neg]
  tauto

/-- The square `(-δ,δ) × (-δ,δ)` of the parameter plane. -/
def sq (δ : ℝ) : Set (ℝ × ℝ) := Set.Ioo (-δ) δ ×ˢ Set.Ioo (-δ) δ

theorem isOpen_sq (δ : ℝ) : IsOpen (sq δ) := isOpen_Ioo.prod isOpen_Ioo

theorem mem_sq {δ : ℝ} {ξ : ℝ × ℝ} : ξ ∈ sq δ ↔ ξ.1 ∈ Set.Ioo (-δ) δ ∧ ξ.2 ∈ Set.Ioo (-δ) δ :=
  Iff.rfl

/-- A neighbourhood of `0` in `ℝ²` contains a square around `0`. -/
theorem exists_sq_subset {F : Set (ℝ × ℝ)} (hF : F ∈ nhds (0 : ℝ × ℝ)) :
    ∃ δ : ℝ, 0 < δ ∧ sq δ ⊆ F := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hF
  refine ⟨r / 2, by linarith, ?_⟩
  intro ξ hξ
  apply hball
  have h1 : |ξ.1| < r / 2 := abs_lt.mpr ⟨by linarith [hξ.1.1], hξ.1.2⟩
  have h2 : |ξ.2| < r / 2 := abs_lt.mpr ⟨by linarith [hξ.2.1], hξ.2.2⟩
  rw [Metric.mem_ball, dist_zero_right, Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
  exact lt_of_le_of_lt (max_le (le_of_lt h1) (le_of_lt h2)) (by linarith)

/-- **The face case of `eventGates`**: the event lies on the `+` face of the tilted slab
(`⟪v,·⟫ = ⟪v,c⟫ + u + h` at `par ψ p`). -/
theorem faceCaseGates (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ)
    (v : R3) (h : ℝ) (ℓ : R3 →L[ℝ] ℝ) (p : ℝ × ℝ)
    (φ : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ))
    {s₁ s₂ : ℝ} (hs₁ : s₁ = 1 ∨ s₁ = -1) (hs₂ : s₂ = 1 ∨ s₂ = -1)
    (hpsrc : p ∈ φ.source) (hφ0 : φ p = 0)
    (hφsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (φ : ℝ × ℝ → ℝ × ℝ) φ.source)
    (hφsymm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (φ.symm : ℝ × ℝ → ℝ × ℝ) φ.target)
    (hquad : ∀ y ∈ φ.source, Work.Drive.EpsForm.sweepHeight ψ ℓ y
      = Work.Drive.EpsForm.sweepHeight ψ ℓ p + s₁ * (φ y).1 ^ 2 + s₂ * (φ y).2 ^ 2)
    (hbox : par ψ p ∈ Submission.PBox s c σ) (hh : 0 < h)
    (hVp0 : inner ℝ v (par ψ p) - (inner ℝ v c + u) - h = 0)
    (hFne : fderiv ℝ (fun w : ℝ × ℝ => inner ℝ v (par ψ (φ.symm w)) - (inner ℝ v c + u) - h) 0
      ≠ 0) :
    ∃ E U₁ U₂ : Set R3, IsOpen E ∧ par ψ p ∈ E ∧ (U₁ = ∅ ∨ IsPathConnected U₁) ∧
      (U₂ = ∅ ∨ IsPathConnected U₂) ∧
      (Work.Drive.EpsFormSphere.openTiltedSweepRegion (Work.Drive.EpsSphere.torusOf ψ)
        s c σ u v h ℓ (eventValue ψ ℓ p) ∩ E = U₁ ∪ U₂) := by
  classical
  have htop : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  -- ### the chart map and its basic properties
  set Φ : ℝ × ℝ → R3 := fun w => par ψ (φ.symm w) with hΦ
  have htarget : (0 : ℝ × ℝ) ∈ φ.target := by rw [← hφ0]; exact φ.map_source hpsrc
  have hsymm0 : φ.symm 0 = p := by rw [← hφ0]; exact φ.left_inv hpsrc
  have hΦ0 : Φ 0 = par ψ p := by rw [hΦ]; simp [hsymm0]
  have hsymm_smooth : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w : ℝ × ℝ => φ.symm w) 0 :=
    hφsymm.contDiffAt (φ.open_target.mem_nhds htarget)
  have hΦ_smooth : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ 0 := by
    have hh := (Work.BoxShrink.Pinch.par_contDiff ψ).comp_contDiffAt 0 hsymm_smooth
    rw [hΦ]
    exact hh
  have hΦ_contOn : ContinuousOn Φ φ.target :=
    (par_continuous ψ).comp_continuousOn hφsymm.continuousOn
  -- ### the functional `F` and the adapted linear map `T`
  set F : (ℝ × ℝ) →L[ℝ] ℝ :=
    fderiv ℝ (fun w : ℝ × ℝ => inner ℝ v (Φ w) - (inner ℝ v c + u) - h) 0 with hF
  have hFne' : F ≠ 0 := hFne
  obtain ⟨w₀, hw₀⟩ : ∃ w : ℝ × ℝ, F w ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hFne' (ContinuousLinearMap.ext hcon)
  set uu : ℝ × ℝ := (F w₀)⁻¹ • w₀ with huu
  have hFuu : F uu = 1 := by
    rw [huu, map_smul, smul_eq_mul]
    exact inv_mul_cancel₀ hw₀
  have he1 : F (1, 0) ≠ 0 ∨ F (0, 1) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    refine hFne' (ContinuousLinearMap.ext fun w => ?_)
    have hw : w = w.1 • ((1, 0) : ℝ × ℝ) + w.2 • ((0, 1) : ℝ × ℝ) := by ext <;> simp
    rw [hw, map_add, map_smul, map_smul, hcon.1, hcon.2]
    simp
  set zz : ℝ × ℝ := (F (0, 1), -(F (1, 0))) with hzz
  have hFzz : F zz = 0 := by
    have hdecomp : zz = F (0, 1) • ((1, 0) : ℝ × ℝ) + (-(F (1, 0))) • ((0, 1) : ℝ × ℝ) := by
      rw [hzz]; ext <;> simp
    rw [hdecomp, map_add, map_smul, map_smul]
    simp only [smul_eq_mul]
    ring
  have hzzne : zz ≠ 0 := by
    rintro hcon
    rw [hzz] at hcon
    have h1 : F (0, 1) = 0 := by simpa using congrArg Prod.fst hcon
    have h2 : F (1, 0) = 0 := by simpa using congrArg Prod.snd hcon
    exact he1.elim (fun hA => hA h2) (fun hB => hB h1)
  set T : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight uu + (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight zz
    with hT
  have hTapply : ∀ a : ℝ × ℝ, T a = a.1 • uu + a.2 • zz := by
    intro a; simp [hT]
  have hTF : ∀ a : ℝ × ℝ, F (T a) = a.1 := by
    intro a
    rw [hTapply, map_add]
    rw [map_smul, hFuu]
    rw [map_smul, hFzz]
    simp
  have hTinj : Function.Injective T := by
    intro a b hab
    have h1 : a.1 = b.1 := by rw [← hTF a, ← hTF b, hab]
    have h2 : a.2 = b.2 := by
      have h3 : a.2 • zz = b.2 • zz := by
        have h4 : a.1 • uu + a.2 • zz = b.1 • uu + b.2 • zz := by
          rw [← hTapply, ← hTapply]; exact hab
        rw [h1] at h4
        exact add_left_cancel h4
      have h5 : (a.2 - b.2) • zz = 0 := by rw [sub_smul, h3, sub_self]
      exact sub_eq_zero.mp ((smul_eq_zero.mp h5).resolve_right hzzne)
    exact Prod.ext h1 h2
  have hTsurj : Function.Surjective T :=
    ((LinearMap.injective_iff_surjective_of_finrank_eq_finrank (K := ℝ)
      (V := ℝ × ℝ) (V₂ := ℝ × ℝ) rfl).mp hTinj)
  -- ### the new chart map and the face function
  set Φt : ℝ × ℝ → R3 := fun ξ => Φ (T ξ) with hΦt
  have hΦt0 : Φt 0 = par ψ p := by rw [hΦt]; simp [hΦ0]
  have hΦt_smooth : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φt 0 := by
    have hTsm : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun ξ : ℝ × ℝ => T ξ) 0 :=
      (ContinuousLinearMap.contDiff T).contDiffAt
    have hΦ_smooth' : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ (T 0) := by
      rw [ContinuousLinearMap.map_zero]; exact hΦ_smooth
    have h2 := hΦ_smooth'.comp 0 hTsm
    rw [hΦt]
    exact h2
  -- ### the face function in the new chart
  set V : ℝ × ℝ → ℝ := fun ξ => inner ℝ v (Φt ξ) - (inner ℝ v c + u) - h with hV
  have hV0 : V 0 = 0 := by
    rw [hV]
    simp only [hΦt, ContinuousLinearMap.map_zero, hΦ0]
    exact hVp0
  have hV_smooth : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V 0 := by
    have h1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun ξ : ℝ × ℝ => inner ℝ v (Φt ξ)) 0 :=
      (innerSL ℝ v).contDiff.contDiffAt.comp 0 hΦt_smooth
    have h2 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun ξ : ℝ × ℝ => inner ℝ v (Φt ξ) - (inner ℝ v c + u) - h) 0 :=
      (h1.sub contDiffAt_const).sub contDiffAt_const
    simpa only [hV] using h2
  have hV_deriv : fderiv ℝ V 0 = ContinuousLinearMap.fst ℝ ℝ ℝ := by
    have hVeq : V = (fun w : ℝ × ℝ => inner ℝ v (Φ w) - (inner ℝ v c + u) - h) ∘ T := by
      funext ξ; rw [hV, hΦt]; rfl
    have hdiff : DifferentiableAt ℝ
        (fun w : ℝ × ℝ => inner ℝ v (Φ w) - (inner ℝ v c + u) - h) (T 0) := by
      have hΦ_smooth' : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ (T 0) := by
        rw [ContinuousLinearMap.map_zero]; exact hΦ_smooth
      have h1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun w : ℝ × ℝ => inner ℝ v (Φ w)) (T 0) :=
        (innerSL ℝ v).contDiff.contDiffAt.comp (T 0) hΦ_smooth'
      have h2 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun w : ℝ × ℝ => inner ℝ v (Φ w) - (inner ℝ v c + u) - h) (T 0) :=
        (h1.sub contDiffAt_const).sub contDiffAt_const
      exact ContDiffAt.differentiableAt h2 htop
    rw [hVeq, fderiv_comp 0 hdiff (ContinuousLinearMap.differentiableAt T)]
    rw [ContinuousLinearMap.fderiv]
    rw [ContinuousLinearMap.map_zero]
    rw [← hF]
    refine ContinuousLinearMap.ext fun ξ => ?_
    rw [ContinuousLinearMap.comp_apply, hTF]
    rfl
  -- ### the monotonicity data
  obtain ⟨δ₀, hδ₀pos, hmonoData⟩ := exists_faceMonotoneData V hV0 hV_smooth hV_deriv
  have hVg0 : -(inner ℝ v (par ψ p) - (inner ℝ v c + u)) - h < 0 := by linarith [hVp0, hh]
  have hev : ∀ᶠ ξ in nhds (0 : ℝ × ℝ), T ξ ∈ φ.target ∧ Φt ξ ∈ Submission.PBox s c σ ∧
      -(inner ℝ v (Φt ξ) - (inner ℝ v c + u)) - h < 0 := by
    have h1 : ∀ᶠ ξ in nhds (0 : ℝ × ℝ), T ξ ∈ φ.target :=
      T.continuous.continuousAt.preimage_mem_nhds
        (φ.open_target.mem_nhds (by simpa using htarget))
    have h2 : ∀ᶠ ξ in nhds (0 : ℝ × ℝ), Φt ξ ∈ Submission.PBox s c σ :=
      hΦt_smooth.continuousAt.preimage_mem_nhds
        ((Work.Topology.SphereSlicing.isOpen_PBox s c σ).mem_nhds (by rw [hΦt0]; exact hbox))
    have h3 : ∀ᶠ ξ in nhds (0 : ℝ × ℝ),
        -(inner ℝ v (Φt ξ) - (inner ℝ v c + u)) - h < 0 := by
      have hcont : Continuous (fun y : R3 => -(inner ℝ v y - (inner ℝ v c + u)) - h) := by
        fun_prop
      exact hΦt_smooth.continuousAt.preimage_mem_nhds
        ((isOpen_lt hcont continuous_const).mem_nhds (by rw [hΦt0]; exact hVg0))
    filter_upwards [h1, h2, h3] with ξ h1 h2 h3
    exact ⟨h1, h2, h3⟩
  obtain ⟨δ', hδ'pos, hδ'sub⟩ := exists_sq_subset hev
  set δ : ℝ := min δ' δ₀ with hδdef
  have hδpos : 0 < δ := lt_min hδ'pos hδ₀pos
  have hδδ' : δ ≤ δ' := min_le_left _ _
  have hδδ₀ : δ ≤ δ₀ := min_le_right _ _
  have hsqmono : sq δ ⊆ sq δ' := by
    intro ξ hξ
    rw [mem_sq] at hξ ⊢
    exact ⟨⟨by linarith [hξ.1.1, hδδ', hδ'pos], by linarith [hξ.1.2, hδδ']⟩,
      ⟨by linarith [hξ.2.1, hδδ', hδ'pos], by linarith [hξ.2.2, hδδ']⟩⟩
  obtain ⟨xstar, hxstar, hmono, htall⟩ := hmonoData δ hδpos hδδ₀
  have hTtarget : ∀ ξ ∈ sq δ, T ξ ∈ φ.target := fun ξ hξ => (hδ'sub (hsqmono hξ)).1
  have hPBox : ∀ ξ ∈ sq δ, Φt ξ ∈ Submission.PBox s c σ :=
    fun ξ hξ => (hδ'sub (hsqmono hξ)).2.1
  have hVneg : ∀ ξ ∈ sq δ, -(inner ℝ v (Φt ξ) - (inner ℝ v c + u)) - h < 0 :=
    fun ξ hξ => (hδ'sub (hsqmono hξ)).2.2
  -- ### the height in the new chart
  have hheight : ∀ ξ ∈ sq δ,
      ℓ (Φt ξ) = eventValue ψ ℓ p + s₁ * (T ξ).1 ^ 2 + s₂ * (T ξ).2 ^ 2 := by
    intro ξ hξ
    have h2 : φ.symm (T ξ) ∈ φ.source := φ.map_target (hTtarget ξ hξ)
    have h3 := hquad (φ.symm (T ξ)) h2
    rw [φ.right_inv (hTtarget ξ hξ)] at h3
    have h4 : Work.Drive.EpsForm.sweepHeight ψ ℓ p = eventValue ψ ℓ p := rfl
    rw [h4] at h3
    have h5 : Work.Drive.EpsForm.sweepHeight ψ ℓ (φ.symm (T ξ)) = ℓ (Φt ξ) := by
      rw [hΦt]
      rfl
    rw [← h5]
    exact h3
  -- ### the two cones meet the face side
  have hV_hasFDeriv : HasFDerivAt V (ContinuousLinearMap.fst ℝ ℝ ℝ) 0 := by
    have h1 := (ContDiffAt.differentiableAt hV_smooth htop).hasFDerivAt
    rwa [hV_deriv] at h1
  have hmeet1 : s₁ = 1 → s₂ = -1 → ∃ ξ ∈ sq δ, 0 < V ξ ∧ |(T ξ).2| < |(T ξ).1| := by
    intro _ _
    obtain ⟨ξ₀, hξ₀pos, hVξ₀, hcone⟩ := exists_mem_doubleCone_of_fderivFst V hV0 hV_hasFDeriv T hTinj
    have hξ₀ne : ξ₀ ≠ 0 := by rintro h; rw [h] at hξ₀pos; simp at hξ₀pos
    have hc : 0 < ξ₀.1 / (2 * ‖ξ₀‖) := by positivity
    have hbound := hV_hasFDeriv.isLittleO.bound hc
    rw [Metric.eventually_nhds_iff] at hbound
    obtain ⟨η, hη, hηb⟩ := hbound
    set t : ℝ := min (η / (2 * (‖ξ₀‖ + 1))) (min 1 (δ / (2 * (‖ξ₀‖ + 1)))) / 2 with ht
    have hminpos : 0 < min (η / (2 * (‖ξ₀‖ + 1))) (min 1 (δ / (2 * (‖ξ₀‖ + 1)))) :=
      lt_min (by positivity) (lt_min (by norm_num) (by positivity))
    have htpos : 0 < t := by rw [ht]; positivity
    have ht_le_η : t ≤ η / (2 * (‖ξ₀‖ + 1)) := by
      rw [ht]
      exact le_trans (div_le_self (le_of_lt hminpos) (by norm_num)) (min_le_left _ _)
    have ht_le_δ : t ≤ δ / (2 * (‖ξ₀‖ + 1)) := by
      rw [ht]
      exact le_trans (div_le_self (le_of_lt hminpos) (by norm_num))
        (le_trans (min_le_right _ _) (min_le_right _ _))
    have ht_le_one : t ≤ 1 := by
      rw [ht]
      exact le_trans (div_le_self (le_of_lt hminpos) (by norm_num))
        (le_trans (min_le_right _ _) (min_le_left _ _))
    have hden : 0 < 2 * (‖ξ₀‖ + 1) := by positivity
    have htη : t * ‖ξ₀‖ < η := by
      have h2 : t * ‖ξ₀‖ ≤ (η / (2 * (‖ξ₀‖ + 1))) * (‖ξ₀‖ + 1) := by
        apply mul_le_mul ht_le_η (by linarith) (norm_nonneg _) (by positivity)
      have h3 : (η / (2 * (‖ξ₀‖ + 1))) * (‖ξ₀‖ + 1) = η / 2 := by
        field_simp
      rw [h3] at h2
      linarith
    have htδ : t * ‖ξ₀‖ < δ := by
      have h2 : t * ‖ξ₀‖ ≤ (δ / (2 * (‖ξ₀‖ + 1))) * (‖ξ₀‖ + 1) := by
        apply mul_le_mul ht_le_δ (by linarith) (norm_nonneg _) (by positivity)
      have h3 : (δ / (2 * (‖ξ₀‖ + 1))) * (‖ξ₀‖ + 1) = δ / 2 := by
        field_simp
      rw [h3] at h2
      linarith
    have hnormt : ‖t • ξ₀‖ = t * ‖ξ₀‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos htpos]
    have hb := hηb (by rw [dist_zero_right]; exact lt_of_eq_of_lt hnormt htη)
    rw [sub_zero] at hb
    have hVt : 0 < V (t • ξ₀) := by
      have hfst : ContinuousLinearMap.fst ℝ ℝ ℝ (t • ξ₀) = t * ξ₀.1 := rfl
      rw [hV0, hfst] at hb
      have hnorm : ‖t • ξ₀‖ = t * ‖ξ₀‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos htpos]
      rw [hnorm] at hb
      have hcval : (ξ₀.1 / (2 * ‖ξ₀‖)) * (t * ‖ξ₀‖) = t * ξ₀.1 / 2 := by
        field_simp
      rw [hcval, Real.norm_eq_abs] at hb
      have htξ : 0 < t * ξ₀.1 := mul_pos htpos hξ₀pos
      have := (abs_le.mp hb).1
      linarith
    refine ⟨t • ξ₀, ?_, hVt, ?_⟩
    · rw [mem_sq]
      have hch1 : |(t • ξ₀).1| ≤ t * ‖ξ₀‖ := by
        rw [Prod.smul_fst, smul_eq_mul, abs_mul, abs_of_pos htpos]
        exact mul_le_mul_of_nonneg_left
          (by rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]; exact le_max_left _ _)
          (le_of_lt htpos)
      have hch2 : |(t • ξ₀).2| ≤ t * ‖ξ₀‖ := by
        rw [Prod.smul_snd, smul_eq_mul, abs_mul, abs_of_pos htpos]
        exact mul_le_mul_of_nonneg_left
          (by rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]; exact le_max_right _ _)
          (le_of_lt htpos)
      have h1 : |(t • ξ₀).1| < δ := lt_of_le_of_lt hch1 htδ
      have h2 : |(t • ξ₀).2| < δ := lt_of_le_of_lt hch2 htδ
      exact ⟨⟨(abs_lt.mp h1).1, (abs_lt.mp h1).2⟩, ⟨(abs_lt.mp h2).1, (abs_lt.mp h2).2⟩⟩
    · rw [map_smul]
      simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, abs_mul, abs_of_pos htpos]
      exact mul_lt_mul_of_pos_left hcone htpos
  have hmeet2 : s₁ = -1 → s₂ = 1 → ∃ ξ ∈ sq δ, 0 < V ξ ∧ |(T ξ).1| < |(T ξ).2| := by
    intro _ _
    set Tsw : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
      (ContinuousLinearMap.prod ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp T)
        ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp T)) with hTsw
    have hTsw_apply : ∀ ξ : ℝ × ℝ, Tsw ξ = ((T ξ).2, (T ξ).1) := by
      intro ξ; simp [hTsw]
    have hTsw_inj : Function.Injective Tsw := by
      intro a b hab
      have h1 : (T a).2 = (T b).2 := by
        have := congrArg Prod.fst hab
        simpa only [hTsw_apply] using this
      have h2 : (T a).1 = (T b).1 := by
        have := congrArg Prod.snd hab
        simpa only [hTsw_apply] using this
      exact hTinj (by ext <;> assumption)
    obtain ⟨ξ₀, hξ₀pos, hVξ₀, hcone⟩ :=
      exists_mem_doubleCone_of_fderivFst V hV0 hV_hasFDeriv Tsw hTsw_inj
    have hcone' : |(T ξ₀).1| < |(T ξ₀).2| := by
      rw [hTsw_apply] at hcone
      simpa using hcone
    have hξ₀ne : ξ₀ ≠ 0 := by rintro h; rw [h] at hξ₀pos; simp at hξ₀pos
    have hc : 0 < ξ₀.1 / (2 * ‖ξ₀‖) := by positivity
    have hbound := hV_hasFDeriv.isLittleO.bound hc
    rw [Metric.eventually_nhds_iff] at hbound
    obtain ⟨η, hη, hηb⟩ := hbound
    set t : ℝ := min (η / (2 * (‖ξ₀‖ + 1))) (min 1 (δ / (2 * (‖ξ₀‖ + 1)))) / 2 with ht
    have hminpos : 0 < min (η / (2 * (‖ξ₀‖ + 1))) (min 1 (δ / (2 * (‖ξ₀‖ + 1)))) :=
      lt_min (by positivity) (lt_min (by norm_num) (by positivity))
    have htpos : 0 < t := by rw [ht]; positivity
    have ht_le_η : t ≤ η / (2 * (‖ξ₀‖ + 1)) := by
      rw [ht]
      exact le_trans (div_le_self (le_of_lt hminpos) (by norm_num)) (min_le_left _ _)
    have ht_le_δ : t ≤ δ / (2 * (‖ξ₀‖ + 1)) := by
      rw [ht]
      exact le_trans (div_le_self (le_of_lt hminpos) (by norm_num))
        (le_trans (min_le_right _ _) (min_le_right _ _))
    have htη : t * ‖ξ₀‖ < η := by
      have h2 : t * ‖ξ₀‖ ≤ (η / (2 * (‖ξ₀‖ + 1))) * (‖ξ₀‖ + 1) := by
        apply mul_le_mul ht_le_η (by linarith) (norm_nonneg _) (by positivity)
      have h3 : (η / (2 * (‖ξ₀‖ + 1))) * (‖ξ₀‖ + 1) = η / 2 := by
        field_simp
      rw [h3] at h2
      linarith
    have htδ : t * ‖ξ₀‖ < δ := by
      have h2 : t * ‖ξ₀‖ ≤ (δ / (2 * (‖ξ₀‖ + 1))) * (‖ξ₀‖ + 1) := by
        apply mul_le_mul ht_le_δ (by linarith) (norm_nonneg _) (by positivity)
      have h3 : (δ / (2 * (‖ξ₀‖ + 1))) * (‖ξ₀‖ + 1) = δ / 2 := by
        field_simp
      rw [h3] at h2
      linarith
    have hnormt : ‖t • ξ₀‖ = t * ‖ξ₀‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos htpos]
    have hb := hηb (by rw [dist_zero_right]; exact lt_of_eq_of_lt hnormt htη)
    rw [sub_zero] at hb
    have hVt : 0 < V (t • ξ₀) := by
      have hfst : ContinuousLinearMap.fst ℝ ℝ ℝ (t • ξ₀) = t * ξ₀.1 := rfl
      rw [hV0, hfst] at hb
      have hnorm : ‖t • ξ₀‖ = t * ‖ξ₀‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos htpos]
      rw [hnorm] at hb
      have hcval : (ξ₀.1 / (2 * ‖ξ₀‖)) * (t * ‖ξ₀‖) = t * ξ₀.1 / 2 := by
        field_simp
      rw [hcval, Real.norm_eq_abs] at hb
      have htξ : 0 < t * ξ₀.1 := mul_pos htpos hξ₀pos
      have := (abs_le.mp hb).1
      linarith
    refine ⟨t • ξ₀, ?_, hVt, ?_⟩
    · rw [mem_sq]
      have hch1 : |(t • ξ₀).1| ≤ t * ‖ξ₀‖ := by
        rw [Prod.smul_fst, smul_eq_mul, abs_mul, abs_of_pos htpos]
        exact mul_le_mul_of_nonneg_left
          (by rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]; exact le_max_left _ _)
          (le_of_lt htpos)
      have hch2 : |(t • ξ₀).2| ≤ t * ‖ξ₀‖ := by
        rw [Prod.smul_snd, smul_eq_mul, abs_mul, abs_of_pos htpos]
        exact mul_le_mul_of_nonneg_left
          (by rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]; exact le_max_right _ _)
          (le_of_lt htpos)
      have h1 : |(t • ξ₀).1| < δ := lt_of_le_of_lt hch1 htδ
      have h2 : |(t • ξ₀).2| < δ := lt_of_le_of_lt hch2 htδ
      exact ⟨⟨(abs_lt.mp h1).1, (abs_lt.mp h1).2⟩, ⟨(abs_lt.mp h2).1, (abs_lt.mp h2).2⟩⟩
    · rw [map_smul]
      simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, abs_mul, abs_of_pos htpos]
      exact mul_lt_mul_of_pos_left hcone htpos
  -- ### the gate decomposition in the chart
  obtain ⟨S₁, S₂, hS₁, hS₂, hS⟩ :=
    gateFace δ hδpos xstar hxstar V hV0 hmono htall T hTinj s₁ s₂ hs₁ hs₂ hmeet1 hmeet2
  have hS₁U : S₁ ⊆ sq δ := by
    intro x hx
    have hx' : x ∈ Set.Ioo (-δ) δ ×ˢ Set.Ioo (-δ) δ ∩
        ({ξ | 0 < V ξ} ∪ {ξ | 0 < s₁ * (T ξ).1 ^ 2 + s₂ * (T ξ).2 ^ 2}) := by
      rw [← hS]; exact Or.inl hx
    exact hx'.1
  have hS₂U : S₂ ⊆ sq δ := by
    intro x hx
    have hx' : x ∈ Set.Ioo (-δ) δ ×ˢ Set.Ioo (-δ) δ ∩
        ({ξ | 0 < V ξ} ∪ {ξ | 0 < s₁ * (T ξ).1 ^ 2 + s₂ * (T ξ).2 ^ 2}) := by
      rw [← hS]; exact Or.inr hx
    exact hx'.1
  have hΦt_contOn : ContinuousOn Φt (Set.Ioo (-δ) δ ×ˢ Set.Ioo (-δ) δ) := by
    have h1 : ContinuousOn Φ (T '' (Set.Ioo (-δ) δ ×ˢ Set.Ioo (-δ) δ)) :=
      hΦ_contOn.mono (by rintro _ ⟨ξ, hξ, rfl⟩; exact hTtarget ξ hξ)
    have h2 : ContinuousOn (fun ξ : ℝ × ℝ => T ξ) (Set.Ioo (-δ) δ ×ˢ Set.Ioo (-δ) δ) :=
      T.continuous.continuousOn
    have h3 := h1.comp h2 (fun ξ hξ => ⟨ξ, hξ, rfl⟩)
    rw [hΦt]
    exact h3
  -- ### the open set `E` on the surface
  have hTimg_open : IsOpen (T '' sq δ) := by
    have hbij : Function.Bijective T := ⟨hTinj, hTsurj⟩
    let e : (ℝ × ℝ) ≃ₗ[ℝ] (ℝ × ℝ) :=
      LinearEquiv.ofBijective (T : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ)) hbij
    have hcoe : (e : ℝ × ℝ → ℝ × ℝ) = T := by
      funext ξ
      exact LinearEquiv.ofBijective_apply (T : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ)) (hf := hbij) ξ
    have hcont : Continuous (e.symm : (ℝ × ℝ) → (ℝ × ℝ)) :=
      e.symm.toLinearMap.continuous_of_finiteDimensional
    have h1 : IsOpen ((e.symm : (ℝ × ℝ) → (ℝ × ℝ)) ⁻¹' sq δ) :=
      hcont.isOpen_preimage _ (isOpen_sq δ)
    have h2 : (T '' sq δ) = (e.symm : (ℝ × ℝ) → (ℝ × ℝ)) ⁻¹' sq δ := by
      ext w
      constructor
      · rintro ⟨ξ, hξ, rfl⟩
        rw [Set.mem_preimage, ← hcoe, LinearEquiv.symm_apply_apply]
        exact hξ
      · intro hw
        rw [Set.mem_preimage] at hw
        exact ⟨e.symm w, hw, by rw [← hcoe, LinearEquiv.apply_symm_apply]⟩
    rwa [h2]
  have hTimg_target : T '' sq δ ⊆ φ.target := by
    rintro _ ⟨ξ, hξ, rfl⟩
    exact hTtarget ξ hξ
  have hparam_open : IsOpen (φ.symm '' (T '' sq δ)) :=
    φ.isOpen_image_symm_of_subset_target hTimg_open hTimg_target
  have hmain : Work.SurgeryInvariance.IsOpenInCarrier (Work.Drive.EpsSphere.torusOf ψ)
      (par ψ '' (φ.symm '' (T '' sq δ))) := by
    simpa only [Work.Drive.EpsSphere.torusOf, Work.Smooth.Morse.torus,
      Work.BoxShrink.Pinch.par_def, Work.Smooth.Morse.param_def] using
      (Work.Smooth.Morse.Surface.isOpenInCarrier_image_of_isOpen ψ hparam_open)
  have hopen : Work.SurgeryInvariance.IsOpenInCarrier (Work.Drive.EpsSphere.torusOf ψ)
      (Φt '' sq δ) := by
    have himg : Φt '' sq δ = par ψ '' (φ.symm '' (T '' sq δ)) := by
      rw [hΦt, hΦ]
      show (par ψ ∘ ⇑φ.symm ∘ T) '' sq δ = par ψ '' (⇑φ.symm '' T '' sq δ)
      rw [Set.image_comp, Set.image_comp]
    rwa [himg]
  obtain ⟨E, hEopen, hEeq⟩ := (isOpen_induced_iff.mp hopen :
    ∃ W : Set R3, IsOpen W ∧ Subtype.val ⁻¹' W = Subtype.val ⁻¹' (Φt '' sq δ))
  have hEcarrier : ∀ y : R3, y ∈ (Work.Smooth.Morse.torus ψ).carrier →
      (y ∈ E ↔ y ∈ Φt '' sq δ) := by
    intro y hy
    have h1 : (⟨y, hy⟩ : (Work.Smooth.Morse.torus ψ).carrier) ∈ Subtype.val ⁻¹' E ↔
        (⟨y, hy⟩ : (Work.Smooth.Morse.torus ψ).carrier) ∈ Subtype.val ⁻¹' (Φt '' sq δ) := by
      rw [hEeq]
    rwa [Set.mem_preimage, Set.mem_preimage] at h1
  -- ### the equality
  refine ⟨E, Φt '' S₁, Φt '' S₂, hEopen, ?_, ?_, ?_, ?_⟩
  · rw [hEcarrier (par ψ p) (par_mem_carrier ψ p)]
    refine ⟨0, ?_, hΦt0⟩
    rw [mem_sq]
    have h0 : ((0 : ℝ × ℝ).1 : ℝ) = 0 := rfl
    have h02 : ((0 : ℝ × ℝ).2 : ℝ) = 0 := rfl
    rw [h0, h02]
    exact ⟨⟨by linarith [hδpos], hδpos⟩, ⟨by linarith [hδpos], hδpos⟩⟩
  · rcases hS₁ with h | h
    · exact Or.inl (by rw [h]; exact Set.image_empty _)
    · exact Or.inr (h.image' (hΦt_contOn.mono hS₁U))
  · rcases hS₂ with h | h
    · exact Or.inl (by rw [h]; exact Set.image_empty _)
    · exact Or.inr (h.image' (hΦt_contOn.mono hS₂U))
  · ext y
    constructor
    · rintro ⟨hyreg, hyE⟩
      rw [mem_openTiltedSweepRegion_iff] at hyreg
      obtain ⟨hyc, hybox, hcond⟩ := hyreg
      obtain ⟨ξ, hξU, hξeq⟩ := (hEcarrier y hyc).mp hyE
      rw [← hξeq] at hcond ⊢
      have hξS : ξ ∈ S₁ ∪ S₂ := by
        rw [hS]
        refine ⟨hξU, ?_⟩
        rcases hcond with h | h | h
        · exact Or.inl h
        · exact absurd h (not_lt.mpr (le_of_lt (hVneg ξ hξU)))
        · refine Or.inr ?_
          show 0 < s₁ * (T ξ).1 ^ 2 + s₂ * (T ξ).2 ^ 2
          have hh2 := hheight ξ hξU
          linarith
      rcases hξS with h | h
      · exact Or.inl ⟨ξ, h, rfl⟩
      · exact Or.inr ⟨ξ, h, rfl⟩
    · rintro (⟨ξ, hξS, hξeq⟩ | ⟨ξ, hξS, hξeq⟩)
      · refine ⟨?_, ?_⟩
        · rw [← hξeq, mem_openTiltedSweepRegion_iff]
          refine ⟨par_mem_carrier ψ _, hPBox ξ (hS₁U hξS), ?_⟩
          have h : ξ ∈ Set.Ioo (-δ) δ ×ˢ Set.Ioo (-δ) δ ∩
              ({ξ | 0 < V ξ} ∪ {ξ | 0 < s₁ * (T ξ).1 ^ 2 + s₂ * (T ξ).2 ^ 2}) := by
            rw [← hS]; exact Or.inl hξS
          rcases h.2 with h | h
          · refine Or.inl ?_; show 0 < V ξ; rw [hV]; exact h
          · refine Or.inr (Or.inr ?_)
            have h' : 0 < s₁ * (T ξ).1 ^ 2 + s₂ * (T ξ).2 ^ 2 := h
            have hh2 := hheight ξ (hS₁U hξS)
            linarith
        · rw [hEcarrier y (by rw [← hξeq]; exact par_mem_carrier ψ _)]
          exact ⟨ξ, hS₁U hξS, hξeq⟩
      · refine ⟨?_, ?_⟩
        · rw [← hξeq, mem_openTiltedSweepRegion_iff]
          refine ⟨par_mem_carrier ψ _, hPBox ξ (hS₂U hξS), ?_⟩
          have h : ξ ∈ Set.Ioo (-δ) δ ×ˢ Set.Ioo (-δ) δ ∩
              ({ξ | 0 < V ξ} ∪ {ξ | 0 < s₁ * (T ξ).1 ^ 2 + s₂ * (T ξ).2 ^ 2}) := by
            rw [← hS]; exact Or.inr hξS
          rcases h.2 with h | h
          · refine Or.inl ?_; show 0 < V ξ; rw [hV]; exact h
          · refine Or.inr (Or.inr ?_)
            have h' : 0 < s₁ * (T ξ).1 ^ 2 + s₂ * (T ξ).2 ^ 2 := h
            have hh2 := hheight ξ (hS₂U hξS)
            linarith
        · rw [hEcarrier y (by rw [← hξeq]; exact par_mem_carrier ψ _)]
          exact ⟨ξ, hS₂U hξS, hξeq⟩

/-- **The chart-derivative of the first face functional does not vanish at an event.** -/
theorem chartFaceDeriv_ne_zero {ψ : Submission.Diffeo} {ℓ : R3 →L[ℝ] ℝ} {v : R3} {p : ℝ × ℝ}
    (φ : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ)) (hpsrc : p ∈ φ.source) (hφ0 : φ p = 0)
    (hφsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (φ : ℝ × ℝ → ℝ × ℝ) φ.source)
    (hφsymm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (φ.symm : ℝ × ℝ → ℝ × ℝ) φ.target)
    (hℓ : ℓ ≠ 0) (hv : v ≠ 0) (hℓv : ℓ v = 0)
    (hcrit : fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) p = 0) :
    fderiv ℝ (fun w : ℝ × ℝ => inner ℝ v (par ψ (φ.symm w))) 0 ≠ 0 := by
  have htop : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  have htarget : (0 : ℝ × ℝ) ∈ φ.target := by rw [← hφ0]; exact φ.map_source hpsrc
  have hsymm0 : φ.symm 0 = p := by rw [← hφ0]; exact φ.left_inv hpsrc
  have hsymm_diff : DifferentiableAt ℝ (fun w : ℝ × ℝ => φ.symm w) 0 :=
    (hφsymm.contDiffAt (φ.open_target.mem_nhds htarget)).differentiableAt htop
  have hsymm_diff' : DifferentiableAt ℝ (fun w : ℝ × ℝ => φ.symm w) (φ p) := by
    rw [hφ0]; exact hsymm_diff
  have hφ_diff : DifferentiableAt ℝ (fun w : ℝ × ℝ => φ w) p :=
    (hφsm.contDiffAt (φ.open_source.mem_nhds hpsrc)).differentiableAt htop
  have hφ_diff' : DifferentiableAt ℝ (fun w : ℝ × ℝ => φ w) (φ.symm 0) := by
    rw [hsymm0]; exact hφ_diff
  have hpar_diff : DifferentiableAt ℝ (par ψ) p :=
    ((Work.BoxShrink.Pinch.par_contDiff ψ).differentiable (by simp)).differentiableAt
  have hker : ∀ w : ℝ × ℝ, ℓ (fderiv ℝ (par ψ) p w) = 0 := by
    intro w
    have h1 : fderiv ℝ (fun q : ℝ × ℝ => ℓ (par ψ q)) p = 0 := hcrit
    have h2 : fderiv ℝ (fun q : ℝ × ℝ => ℓ (par ψ q)) p = ℓ.comp (fderiv ℝ (par ψ) p) := by
      show fderiv ℝ (⇑ℓ ∘ par ψ) p = ℓ.comp (fderiv ℝ (par ψ) p)
      rw [fderiv_comp p (ContinuousLinearMap.differentiableAt ℓ) hpar_diff,
        ContinuousLinearMap.fderiv]
    rw [h2] at h1
    exact congrArg (fun (T : (ℝ × ℝ) →L[ℝ] ℝ) => T w) h1
  obtain ⟨w₀, hw₀⟩ := exists_paramDir_inner_ne_zero (fderiv ℝ (par ψ) p)
    (Work.Drive.Mono.Band.par_immersion ψ p) ℓ v hℓ hv hℓv hker
  have hAB : (fderiv ℝ (fun w : ℝ × ℝ => φ w) p).comp
      (fderiv ℝ (fun w : ℝ × ℝ => φ.symm w) 0) = 1 := by
    have heq : ((fun w : ℝ × ℝ => φ w) ∘ (fun w : ℝ × ℝ => φ.symm w))
        =ᶠ[nhds (0 : ℝ × ℝ)] (fun w => w) := by
      filter_upwards [φ.open_target.mem_nhds htarget] with w hw
      exact φ.right_inv hw
    have h1 : fderiv ℝ ((fun w : ℝ × ℝ => φ w) ∘ (fun w : ℝ × ℝ => φ.symm w)) 0 = 1 := by
      rw [heq.fderiv_eq]
      exact fderiv_id
    rw [fderiv_comp 0 hφ_diff' hsymm_diff, hsymm0] at h1
    exact h1
  have hBA : (fderiv ℝ (fun w : ℝ × ℝ => φ.symm w) 0).comp
      (fderiv ℝ (fun w : ℝ × ℝ => φ w) p) = 1 := by
    have heq : ((fun w : ℝ × ℝ => φ.symm w) ∘ (fun w : ℝ × ℝ => φ w))
        =ᶠ[nhds p] (fun w => w) := by
      filter_upwards [φ.open_source.mem_nhds hpsrc] with w hw
      exact φ.left_inv hw
    have h1 : fderiv ℝ ((fun w : ℝ × ℝ => φ.symm w) ∘ (fun w : ℝ × ℝ => φ w)) p = 1 := by
      rw [heq.fderiv_eq]
      exact fderiv_id
    rw [fderiv_comp p hsymm_diff' hφ_diff, hφ0] at h1
    exact h1
  have hmain : fderiv ℝ (fun w : ℝ × ℝ => inner ℝ v (par ψ (φ.symm w))) 0
      = ((innerSL ℝ v).comp (fderiv ℝ (par ψ) p)).comp
        (fderiv ℝ (fun w : ℝ × ℝ => φ.symm w) 0) := by
    have heqfun : (fun w : ℝ × ℝ => inner ℝ v (par ψ (φ.symm w)))
        = ((fun z : ℝ × ℝ => inner ℝ v (par ψ z)) ∘ (fun w : ℝ × ℝ => φ.symm w)) := rfl
    rw [heqfun]
    have houter : DifferentiableAt ℝ (fun z : ℝ × ℝ => inner ℝ v (par ψ z)) (φ.symm 0) := by
      rw [hsymm0]
      exact DifferentiableAt.comp p (ContinuousLinearMap.differentiableAt (innerSL ℝ v)) hpar_diff
    rw [fderiv_comp 0 houter hsymm_diff, hsymm0]
    have heqfun2 : (fun z : ℝ × ℝ => inner ℝ v (par ψ z)) = (⇑(innerSL ℝ v) ∘ par ψ) := rfl
    rw [heqfun2]
    rw [fderiv_comp p (ContinuousLinearMap.differentiableAt (innerSL ℝ v)) hpar_diff,
      ContinuousLinearMap.fderiv]
  intro hzero
  rw [hmain] at hzero
  have h1 : ∀ w : ℝ × ℝ,
      inner ℝ v ((fderiv ℝ (par ψ) p) ((fderiv ℝ (fun u : ℝ × ℝ => φ.symm u) 0) w)) = 0 := by
    intro w
    have h2 := congrArg (fun (S : (ℝ × ℝ) →L[ℝ] ℝ) => S w) hzero
    simpa only [ContinuousLinearMap.comp_apply, innerSL_apply_apply,
      ContinuousLinearMap.zero_apply] using h2
  refine hw₀ ?_
  have h3 := h1 ((fderiv ℝ (fun w : ℝ × ℝ => φ w) p) w₀)
  have h4 : ((fderiv ℝ (fun w : ℝ × ℝ => φ.symm w) 0)
      ((fderiv ℝ (fun w : ℝ × ℝ => φ w) p) w₀)) = w₀ := by
    have h5 := congrArg (fun (S : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) => S w₀) hBA
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
      one_apply_eq_self] using h5
  rw [h4] at h3
  exact h3

/-- **The interior case of the local gates**: both faces of the slab are inactive at the event, so
the region at the event's level is the superlevel set of the Morse normal form. -/
theorem interiorCaseGates (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
    (u : ℝ) (v : R3) (h : ℝ) (ℓ : R3 →L[ℝ] ℝ) (p : ℝ × ℝ)
    (φ : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ))
    {s₁ s₂ : ℝ} (hs₁ : s₁ = 1 ∨ s₁ = -1) (hs₂ : s₂ = 1 ∨ s₂ = -1)
    (hpsrc : p ∈ φ.source) (hφ0 : φ p = 0)
    (hφsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (φ : ℝ × ℝ → ℝ × ℝ) φ.source)
    (hφsymm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (φ.symm : ℝ × ℝ → ℝ × ℝ) φ.target)
    (hquad : ∀ y ∈ φ.source, Work.Drive.EpsForm.sweepHeight ψ ℓ y
      = Work.Drive.EpsForm.sweepHeight ψ ℓ p + s₁ * (φ y).1 ^ 2 + s₂ * (φ y).2 ^ 2)
    (hbox : par ψ p ∈ Submission.PBox s c σ)
    (hVp : inner ℝ v (par ψ p) - (inner ℝ v c + u) - h < 0)
    (hVm : -(inner ℝ v (par ψ p) - (inner ℝ v c + u)) - h < 0) :
    ∃ E U₁ U₂ : Set R3, IsOpen E ∧ par ψ p ∈ E ∧ (U₁ = ∅ ∨ IsPathConnected U₁) ∧
      (U₂ = ∅ ∨ IsPathConnected U₂) ∧
      (Work.Drive.EpsFormSphere.openTiltedSweepRegion (Work.Drive.EpsSphere.torusOf ψ)
        s c σ u v h ℓ (eventValue ψ ℓ p) ∩ E = U₁ ∪ U₂) := by
  classical
  have htop : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  set Φ : ℝ × ℝ → R3 := fun w => par ψ (φ.symm w) with hΦ
  have htarget : (0 : ℝ × ℝ) ∈ φ.target := by rw [← hφ0]; exact φ.map_source hpsrc
  have hsymm0 : φ.symm 0 = p := by rw [← hφ0]; exact φ.left_inv hpsrc
  have hΦ0 : Φ 0 = par ψ p := by rw [hΦ]; simp [hsymm0]
  have hsymm_smooth : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w : ℝ × ℝ => φ.symm w) 0 :=
    hφsymm.contDiffAt (φ.open_target.mem_nhds htarget)
  have hΦ_smooth : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ 0 := by
    have hh := (Work.BoxShrink.Pinch.par_contDiff ψ).comp_contDiffAt 0 hsymm_smooth
    rw [hΦ]
    exact hh
  have hΦ_contOn : ContinuousOn Φ φ.target :=
    (par_continuous ψ).comp_continuousOn hφsymm.continuousOn
  have hev : ∀ᶠ ξ in nhds (0 : ℝ × ℝ), ξ ∈ φ.target ∧ Φ ξ ∈ Submission.PBox s c σ ∧
      (inner ℝ v (Φ ξ) - (inner ℝ v c + u) - h < 0) ∧
      (-(inner ℝ v (Φ ξ) - (inner ℝ v c + u)) - h < 0) := by
    have h1 : ∀ᶠ ξ in nhds (0 : ℝ × ℝ), ξ ∈ φ.target := φ.open_target.mem_nhds htarget
    have h2 : ∀ᶠ ξ in nhds (0 : ℝ × ℝ), Φ ξ ∈ Submission.PBox s c σ :=
      hΦ_smooth.continuousAt.preimage_mem_nhds
        ((Work.Topology.SphereSlicing.isOpen_PBox s c σ).mem_nhds (by rw [hΦ0]; exact hbox))
    have h3 : ∀ᶠ ξ in nhds (0 : ℝ × ℝ), inner ℝ v (Φ ξ) - (inner ℝ v c + u) - h < 0 := by
      have hcont : Continuous (fun y : R3 => inner ℝ v y - (inner ℝ v c + u) - h) := by fun_prop
      exact hΦ_smooth.continuousAt.preimage_mem_nhds
        ((isOpen_lt hcont continuous_const).mem_nhds (by rw [hΦ0]; exact hVp))
    have h4 : ∀ᶠ ξ in nhds (0 : ℝ × ℝ), -(inner ℝ v (Φ ξ) - (inner ℝ v c + u)) - h < 0 := by
      have hcont : Continuous (fun y : R3 => -(inner ℝ v y - (inner ℝ v c + u)) - h) := by fun_prop
      exact hΦ_smooth.continuousAt.preimage_mem_nhds
        ((isOpen_lt hcont continuous_const).mem_nhds (by rw [hΦ0]; exact hVm))
    filter_upwards [h1, h2, h3, h4] with ξ h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  obtain ⟨δ, hδpos, hδsub⟩ := exists_sq_subset hev
  have htargetδ : ∀ ξ ∈ sq δ, ξ ∈ φ.target := fun ξ hξ => (hδsub hξ).1
  have hPBoxδ : ∀ ξ ∈ sq δ, Φ ξ ∈ Submission.PBox s c σ := fun ξ hξ => (hδsub hξ).2.1
  have hVpδ : ∀ ξ ∈ sq δ, inner ℝ v (Φ ξ) - (inner ℝ v c + u) - h < 0 :=
    fun ξ hξ => (hδsub hξ).2.2.1
  have hVmδ : ∀ ξ ∈ sq δ, -(inner ℝ v (Φ ξ) - (inner ℝ v c + u)) - h < 0 :=
    fun ξ hξ => (hδsub hξ).2.2.2
  have hheight : ∀ ξ ∈ sq δ, ℓ (Φ ξ) = eventValue ψ ℓ p + s₁ * ξ.1 ^ 2 + s₂ * ξ.2 ^ 2 := by
    intro ξ hξ
    have h2 : φ.symm ξ ∈ φ.source := φ.map_target (htargetδ ξ hξ)
    have h3 := hquad (φ.symm ξ) h2
    rw [φ.right_inv (htargetδ ξ hξ)] at h3
    have h4 : Work.Drive.EpsForm.sweepHeight ψ ℓ p = eventValue ψ ℓ p := rfl
    rw [h4] at h3
    have h5 : Work.Drive.EpsForm.sweepHeight ψ ℓ (φ.symm ξ) = ℓ (Φ ξ) := by
      rw [hΦ]; rfl
    rw [← h5]
    exact h3
  obtain ⟨S₁, S₂, hS₁, hS₂, hS⟩ := gateNoFace δ hδpos (ContinuousLinearMap.id ℝ (ℝ × ℝ))
    (fun _ _ h => h) s₁ s₂ hs₁ hs₂
  simp only [ContinuousLinearMap.id_apply, one_apply_eq_self] at hS
  have hS₁U : S₁ ⊆ sq δ := by
    intro x hx
    have hx' : x ∈ Set.Ioo (-δ) δ ×ˢ Set.Ioo (-δ) δ ∩
        {ξ : ℝ × ℝ | 0 < s₁ * ξ.1 ^ 2 + s₂ * ξ.2 ^ 2} := by
      rw [← hS]; exact Or.inl hx
    exact hx'.1
  have hS₂U : S₂ ⊆ sq δ := by
    intro x hx
    have hx' : x ∈ Set.Ioo (-δ) δ ×ˢ Set.Ioo (-δ) δ ∩
        {ξ : ℝ × ℝ | 0 < s₁ * ξ.1 ^ 2 + s₂ * ξ.2 ^ 2} := by
      rw [← hS]; exact Or.inr hx
    exact hx'.1
  have hΦ_contOn' : ContinuousOn Φ (Set.Ioo (-δ) δ ×ˢ Set.Ioo (-δ) δ) :=
    hΦ_contOn.mono (fun ξ hξ => htargetδ ξ hξ)
  have hparam_open : IsOpen (φ.symm '' sq δ) :=
    φ.isOpen_image_symm_of_subset_target (isOpen_sq δ)
      (fun ξ hξ => htargetδ ξ (by rw [mem_sq]; exact hξ))
  have hopen : Work.SurgeryInvariance.IsOpenInCarrier (Work.Drive.EpsSphere.torusOf ψ)
      (Φ '' sq δ) := by
    have h := Work.Smooth.Morse.Surface.isOpenInCarrier_image_of_isOpen ψ hparam_open
    have himg : Φ '' sq δ = par ψ '' (φ.symm '' sq δ) := by
      rw [hΦ]
      show (par ψ ∘ ⇑φ.symm) '' sq δ = par ψ '' (⇑φ.symm '' sq δ)
      rw [Set.image_comp]
    have h' : Work.SurgeryInvariance.IsOpenInCarrier (Work.Drive.EpsSphere.torusOf ψ)
        (par ψ '' (φ.symm '' sq δ)) := by
      simpa only [Work.Drive.EpsSphere.torusOf, Work.Smooth.Morse.torus,
        Work.BoxShrink.Pinch.par_def, Work.Smooth.Morse.param_def] using h
    rwa [himg]
  obtain ⟨E, hEopen, hEeq⟩ := (isOpen_induced_iff.mp hopen :
    ∃ W : Set R3, IsOpen W ∧ Subtype.val ⁻¹' W = Subtype.val ⁻¹' (Φ '' sq δ))
  have hEcarrier : ∀ y : R3, y ∈ (Work.Smooth.Morse.torus ψ).carrier →
      (y ∈ E ↔ y ∈ Φ '' sq δ) := by
    intro y hy
    have h1 : (⟨y, hy⟩ : (Work.Smooth.Morse.torus ψ).carrier) ∈ Subtype.val ⁻¹' E ↔
        (⟨y, hy⟩ : (Work.Smooth.Morse.torus ψ).carrier) ∈ Subtype.val ⁻¹' (Φ '' sq δ) := by
      rw [hEeq]
    rwa [Set.mem_preimage, Set.mem_preimage] at h1
  refine ⟨E, Φ '' S₁, Φ '' S₂, hEopen, ?_, ?_, ?_, ?_⟩
  · rw [hEcarrier (par ψ p) (par_mem_carrier ψ p)]
    refine ⟨0, ?_, hΦ0⟩
    rw [mem_sq]
    have h0 : ((0 : ℝ × ℝ).1 : ℝ) = 0 := rfl
    have h02 : ((0 : ℝ × ℝ).2 : ℝ) = 0 := rfl
    rw [h0, h02]
    exact ⟨⟨by linarith [hδpos], hδpos⟩, ⟨by linarith [hδpos], hδpos⟩⟩
  · rcases hS₁ with h | h
    · exact Or.inl (by rw [h]; exact Set.image_empty _)
    · exact Or.inr (h.image' (hΦ_contOn'.mono hS₁U))
  · rcases hS₂ with h | h
    · exact Or.inl (by rw [h]; exact Set.image_empty _)
    · exact Or.inr (h.image' (hΦ_contOn'.mono hS₂U))
  · ext y
    constructor
    · rintro ⟨hyreg, hyE⟩
      rw [mem_openTiltedSweepRegion_iff] at hyreg
      obtain ⟨hyc, hybox, hcond⟩ := hyreg
      obtain ⟨ξ, hξU, hξeq⟩ := (hEcarrier y hyc).mp hyE
      rw [← hξeq] at hcond ⊢
      have hξS : ξ ∈ S₁ ∪ S₂ := by
        rw [hS]
        rcases hcond with h | h | h
        · exact absurd h (not_lt.mpr (le_of_lt (hVpδ ξ hξU)))
        · exact absurd h (not_lt.mpr (le_of_lt (hVmδ ξ hξU)))
        · refine ⟨hξU, ?_⟩
          show 0 < s₁ * ξ.1 ^ 2 + s₂ * ξ.2 ^ 2
          have hh2 := hheight ξ hξU
          linarith
      rcases hξS with h | h
      · exact Or.inl ⟨ξ, h, rfl⟩
      · exact Or.inr ⟨ξ, h, rfl⟩
    · rintro (⟨ξ, hξS, hξeq⟩ | ⟨ξ, hξS, hξeq⟩)
      · refine ⟨?_, ?_⟩
        · rw [← hξeq, mem_openTiltedSweepRegion_iff]
          refine ⟨par_mem_carrier ψ _, hPBoxδ ξ (hS₁U hξS), ?_⟩
          have h : ξ ∈ Set.Ioo (-δ) δ ×ˢ Set.Ioo (-δ) δ ∩
              {ξ : ℝ × ℝ | 0 < s₁ * ξ.1 ^ 2 + s₂ * ξ.2 ^ 2} := by
            rw [← hS]; exact Or.inl hξS
          have h' : 0 < s₁ * ξ.1 ^ 2 + s₂ * ξ.2 ^ 2 := by simpa using h.2
          have hh2 := hheight ξ (hS₁U hξS)
          refine Or.inr (Or.inr ?_)
          linarith
        · rw [hEcarrier y (by rw [← hξeq]; exact par_mem_carrier ψ _)]
          exact ⟨ξ, hS₁U hξS, hξeq⟩
      · refine ⟨?_, ?_⟩
        · rw [← hξeq, mem_openTiltedSweepRegion_iff]
          refine ⟨par_mem_carrier ψ _, hPBoxδ ξ (hS₂U hξS), ?_⟩
          have h : ξ ∈ Set.Ioo (-δ) δ ×ˢ Set.Ioo (-δ) δ ∩
              {ξ : ℝ × ℝ | 0 < s₁ * ξ.1 ^ 2 + s₂ * ξ.2 ^ 2} := by
            rw [← hS]; exact Or.inr hξS
          have h' : 0 < s₁ * ξ.1 ^ 2 + s₂ * ξ.2 ^ 2 := by simpa using h.2
          have hh2 := hheight ξ (hS₂U hξS)
          refine Or.inr (Or.inr ?_)
          linarith
        · rw [hEcarrier y (by rw [← hξeq]; exact par_mem_carrier ψ _)]
          exact ⟨ξ, hS₂U hξS, hξeq⟩

theorem eventGates (ψ : Submission.Diffeo) (K : LeanEval.KnotTheory.PardonDistortion.Knot) (s : ℝ) (c : LeanEval.KnotTheory.PardonDistortion.R3) (σ : Equiv.Perm (Fin 3))
    (u : ℝ) (v : LeanEval.KnotTheory.PardonDistortion.R3) (h R : ℝ) (ℓ : LeanEval.KnotTheory.PardonDistortion.R3 →L[ℝ] ℝ) (exc : Finset ℝ) (lam0 lam1 : ℝ)
    (hG : Work.Drive.Final.GoodSweepData ψ K s c σ u v h R ℓ exc lam0 lam1)
    {p : ℝ × ℝ} (hp : Work.Drive.Final.IsEvent ψ s c σ u v h ℓ p) :
    ∃ (E U₁ U₂ : Set LeanEval.KnotTheory.PardonDistortion.R3),
      IsOpen E ∧ Work.BoxShrink.Pinch.par ψ p ∈ E ∧
      (U₁ = ∅ ∨ IsPathConnected U₁) ∧ (U₂ = ∅ ∨ IsPathConnected U₂) ∧
      (Work.Drive.EpsFormSphere.openTiltedSweepRegion (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ
          (Work.Drive.Final.eventValue ψ ℓ p) ∩ E = U₁ ∪ U₂) := by
  classical
  have hℓne : ℓ ≠ 0 := hG.1.2.2.1
  have hℓv : ℓ v = 0 := hG.1.2.2.2.1
  have hvne : v ≠ 0 := by
    have hv1 : ‖v‖ = 1 := hG.1.2.1
    intro h0
    rw [h0, norm_zero] at hv1
    norm_num at hv1
  have hh : 0 < h := hG.1.2.2.2.2.2.1
  have hbox : par ψ p ∈ Submission.PBox s c σ := hp.1
  have hslab : |inner ℝ v (par ψ p) - (inner ℝ v c + u)| ≤ h := hp.2.1
  have hcrit : fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) p = 0 := hp.2.2
  have hnondeg : Function.Injective
      (fderiv ℝ (fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ)) p) :=
    (hG.1.1.2.2.1 p hp.1 hp.2.1 hp.2.2).1
  have hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Work.Drive.EpsForm.sweepHeight ψ ℓ) := by
    have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : R3 => ℓ y) := ℓ.contDiff
    exact Work.Smooth.Morse.pullback_contDiff ψ h1
  obtain ⟨φ, s₁, s₂, hpsrc, hφ0, hφsm, hφsymm, hs₁, hs₂, hquad⟩ :=
    morseLemmaProd (Work.Drive.EpsForm.sweepHeight ψ ℓ) p hsm hcrit hnondeg
  have hFne : fderiv ℝ (fun w : ℝ × ℝ => inner ℝ v (par ψ (φ.symm w))) 0 ≠ 0 :=
    chartFaceDeriv_ne_zero φ hpsrc hφ0 hφsm hφsymm hℓne hvne hℓv hcrit
  have hFneC : fderiv ℝ
      (fun w : ℝ × ℝ => inner ℝ v (par ψ (φ.symm w)) - (inner ℝ v c + u) - h) 0 ≠ 0 := by
    have heq : (fun w : ℝ × ℝ => inner ℝ v (par ψ (φ.symm w)) - (inner ℝ v c + u) - h)
        =ᶠ[nhds (0 : ℝ × ℝ)]
        (fun w : ℝ × ℝ => inner ℝ v (par ψ (φ.symm w)) - ((inner ℝ v c + u) + h)) := by
      filter_upwards with w
      ring
    rw [heq.fderiv_eq, fderiv_sub_const]
    exact hFne
  have hVp : inner ℝ v (par ψ p) - (inner ℝ v c + u) - h ≤ 0 := by
    have := (abs_le.mp hslab).2; linarith
  have hVm : -(inner ℝ v (par ψ p) - (inner ℝ v c + u)) - h ≤ 0 := by
    have := (abs_le.mp hslab).1; linarith
  rcases lt_or_eq_of_le hVp with hVplt | hVpeq
  · rcases lt_or_eq_of_le hVm with hVmlt | hVmeq
    · exact interiorCaseGates ψ s c σ u v h ℓ p φ hs₁ hs₂ hpsrc hφ0 hφsm hφsymm hquad hbox
        hVplt hVmlt
    · have hVp0' : inner ℝ (-v) (par ψ p) - (inner ℝ (-v) c + (-u)) - h = 0 := by
        simp only [inner_neg_left]
        ring_nf
        linarith [hVmeq]
      have hFne' : fderiv ℝ (fun w : ℝ × ℝ => inner ℝ (-v) (par ψ (φ.symm w))
          - (inner ℝ (-v) c + (-u)) - h) 0 ≠ 0 := by
        have heq : (fun w : ℝ × ℝ => inner ℝ (-v) (par ψ (φ.symm w))
              - (inner ℝ (-v) c + (-u)) - h)
            =ᶠ[nhds (0 : ℝ × ℝ)]
            fun w => -(inner ℝ v (par ψ (φ.symm w)) - (inner ℝ v c + u) - h) - 2 * h := by
          filter_upwards with w
          rw [inner_neg_left, inner_neg_left]
          ring
        rw [heq.fderiv_eq, fderiv_sub_const]
        intro hcon
        apply hFneC
        have h2 : fderiv ℝ (fun w : ℝ × ℝ =>
              -(inner ℝ v (par ψ (φ.symm w)) - (inner ℝ v c + u) - h)) 0
            = -fderiv ℝ (fun w : ℝ × ℝ =>
              inner ℝ v (par ψ (φ.symm w)) - (inner ℝ v c + u) - h) 0 := fderiv_neg
        rw [h2] at hcon
        exact neg_eq_zero.mp hcon
      obtain ⟨E, U₁, U₂, hE, hmem, hU₁, hU₂, heq⟩ :=
        faceCaseGates ψ s c σ (-u) (-v) h ℓ p φ hs₁ hs₂ hpsrc hφ0 hφsm hφsymm hquad hbox hh
          hVp0' hFne'
      exact ⟨E, U₁, U₂, hE, hmem, hU₁, hU₂, by
        rw [openTiltedSweepRegion_neg] at heq
        exact heq⟩
  · exact faceCaseGates ψ s c σ u v h ℓ p φ hs₁ hs₂ hpsrc hφ0 hφsm hφsymm hquad hbox hh
      hVpeq hFneC

end

end Work.Drive.Final
