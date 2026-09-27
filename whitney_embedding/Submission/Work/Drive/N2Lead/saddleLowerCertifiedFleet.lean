import Mathlib
import Submission.Work.Drive.N2C.defs
import Submission.Work.Drive.N2Lead.saddlePacket
import Submission.Work.Drive.N2Lead.isCertifiedAt_of_starRegions
import Submission.Work.Drive.N2Lead.polarCurve_rows

/-!
# §4.2: the lower certificate of the saddle packet, in fleet form

The statement is `Work.Drive.N2Lead.saddleLowerCertifiedFleet`; the proof feeds the star-regions
engine `Work.Drive.N2Lead.isCertifiedAt_of_starRegions` with the regions `ball 0 17` (the marked
component of the anchor level, drawn by the polar curve `t ↦ cE3 (r (Θ t) · exp (i Θ t))`) and
`ball (proj2 (farPos n j)) 2` (the parked round circles `farCurve n j`, of norm `≥ 19`).

This file is self-contained: the elementary rows of the two kinds of curves (their planar
projections, derivatives and non-radiality) are proved here.
-/

namespace Work.Drive.N2Lead

open scoped Manifold ContDiff Topology
open Set Filter

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
  [IsManifold (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞) M]

section Rows

/-- The squared norm of the planar projection, from the two coordinates. -/
lemma norm_proj2_sq (v : Work.Drive.N2Lead.E3) :
    ‖Work.Drive.N2Lead.proj2 v‖ ^ 2 = (v 0) ^ 2 + (v 1) ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [Work.Drive.N2Lead.proj2]
  ring

/-- The planar projection of the parking spot `(-20, 20 + 5j, 1)`. -/
lemma proj2_farPos (n : ℕ) (j : Fin n) :
    Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.farPos n j)
      = (⟨(-20 : ℝ), 20 + 5 * ((j : ℕ) : ℝ)⟩ : ℂ) := by
  apply Complex.ext <;> simp [Work.Drive.N2Lead.proj2, Work.Drive.N2Lead.farPos_apply]

/-- The planar projection of the far circle: a round circle of radius `1` about the parking spot. -/
lemma proj2_farCurve (n : ℕ) (j : Fin n) (t : ℝ) :
    Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.farCurve n j t)
      = Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.farPos n j)
        + Work.Drive.N2Lead.proj2 (Work.Drive.N2.ang t) := by
  rw [Work.Drive.N2Lead.farCurve_eq, Work.Drive.N2Lead.proj2_add]

/-- The planar projection of the round picture is `exp (i 2πt)`. -/
lemma proj2_ang (t : ℝ) :
    Work.Drive.N2Lead.proj2 (Work.Drive.N2.ang t)
      = Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I) := by
  rw [Work.Drive.N2.ang, Work.Drive.N2Lead.proj2_roundPic, Complex.exp_ofReal_mul_I]
  apply Complex.ext
  · rw [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im]
    simp
  · rw [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im]
    simp

lemma norm_proj2_ang (t : ℝ) : ‖Work.Drive.N2Lead.proj2 (Work.Drive.N2.ang t)‖ = 1 := by
  rw [proj2_ang, Complex.norm_exp]
  norm_num

lemma norm_proj2_farPos_ge (n : ℕ) (j : Fin n) :
    19 ≤ ‖Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.farPos n j)‖ := by
  have h : (‖Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.farPos n j)‖) ^ 2
      = (20 : ℝ) ^ 2 + (20 + 5 * ((j : ℕ) : ℝ)) ^ 2 := by
    rw [norm_proj2_sq]
    simp [Work.Drive.N2Lead.farPos_apply]
  nlinarith [norm_nonneg (Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.farPos n j)),
    sq_nonneg (20 + 5 * ((j : ℕ) : ℝ))]


end Rows

section Deriv

/-- The derivative of `t ↦ 2πt`. -/
lemma hasDerivAt_two_pi_mul (t : ℝ) :
    HasDerivAt (fun u : ℝ => 2 * Real.pi * u) (2 * Real.pi) t := by
  simpa using (hasDerivAt_id t).const_mul (2 * Real.pi)

/-- **The derivative of the planar projection of the round picture**: the velocity of the round
circle is the rotation of the position by `π/2`, scaled by `2π`. -/
lemma hasDerivAt_proj2_ang (t : ℝ) :
    HasDerivAt (fun u : ℝ => Work.Drive.N2Lead.proj2 (Work.Drive.N2.ang u))
      ((2 * Real.pi : ℂ) * Complex.I * Work.Drive.N2Lead.proj2 (Work.Drive.N2.ang t)) t := by
  have h1 : HasDerivAt (fun u : ℝ => ((2 * Real.pi * u : ℝ) : ℂ))
      ((2 * Real.pi : ℝ) : ℂ) t :=
    Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_two_pi_mul t)
  have hlin : HasDerivAt (fun u : ℝ => ((2 * Real.pi * u : ℝ) : ℂ) * Complex.I)
      (((2 * Real.pi : ℝ) : ℂ) * Complex.I) t := h1.mul_const Complex.I
  have hexp : HasDerivAt (fun u : ℝ => Complex.exp (((2 * Real.pi * u : ℝ) : ℂ) * Complex.I))
      (Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I)
        * (((2 * Real.pi : ℝ) : ℂ) * Complex.I)) t :=
    (Complex.hasDerivAt_exp _).comp t hlin
  have hfun : (fun u : ℝ => Work.Drive.N2Lead.proj2 (Work.Drive.N2.ang u))
      = (fun u : ℝ => Complex.exp (((2 * Real.pi * u : ℝ) : ℂ) * Complex.I)) :=
    funext fun u => proj2_ang u
  rw [hfun, proj2_ang t]
  refine hexp.congr_deriv ?_
  push_cast
  ring

/-- The derivative of the planar projection of a far circle. -/
lemma hasDerivAt_proj2_farCurve (n : ℕ) (j : Fin n) (t : ℝ) :
    HasDerivAt (fun u : ℝ => Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.farCurve n j u))
      ((2 * Real.pi : ℂ) * Complex.I * Work.Drive.N2Lead.proj2 (Work.Drive.N2.ang t)) t := by
  have hfun : (fun u : ℝ => Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.farCurve n j u))
      = (fun u : ℝ => Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.farPos n j)
          + Work.Drive.N2Lead.proj2 (Work.Drive.N2.ang u)) := by
    funext u
    rw [proj2_farCurve]
  rw [hfun]
  exact (hasDerivAt_proj2_ang t).const_add _

/-- **The derivative of the packet's polar curve.** -/
lemma hasDerivAt_polar {r Θ : ℝ → ℝ} (hr : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) r)
    (hΘ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Θ) (t : ℝ) :
    HasDerivAt (fun u : ℝ => (r (Θ u) : ℂ) * Complex.exp (((Θ u : ℝ) : ℂ) * Complex.I))
      ((Complex.ofReal (deriv r (Θ t)) + Complex.I * (r (Θ t) : ℂ))
        * Complex.ofReal (deriv Θ t) * Complex.exp (((Θ t : ℝ) : ℂ) * Complex.I)) t := by
  have hdr : HasDerivAt r (deriv r (Θ t)) (Θ t) :=
    (hr.contDiffAt.differentiableAt (by simp)).hasDerivAt
  have hdΘ : HasDerivAt Θ (deriv Θ t) t :=
    (hΘ.contDiffAt.differentiableAt (by simp)).hasDerivAt
  have hcomp : HasDerivAt (fun u : ℝ => r (Θ u)) (deriv r (Θ t) * deriv Θ t) t :=
    hdr.comp t hdΘ
  have hcast : HasDerivAt (fun u : ℝ => ((r (Θ u) : ℝ) : ℂ))
      (Complex.ofReal (deriv r (Θ t) * deriv Θ t)) t :=
    Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t hcomp
  have hcastΘ : HasDerivAt (fun u : ℝ => ((Θ u : ℝ) : ℂ)) (Complex.ofReal (deriv Θ t)) t :=
    Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t hdΘ
  have harg : HasDerivAt (fun u : ℝ => ((Θ u : ℝ) : ℂ) * Complex.I)
      (Complex.ofReal (deriv Θ t) * Complex.I) t := hcastΘ.mul_const Complex.I
  have hexp : HasDerivAt (fun u : ℝ => Complex.exp (((Θ u : ℝ) : ℂ) * Complex.I))
      (Complex.exp (((Θ t : ℝ) : ℂ) * Complex.I)
        * (Complex.ofReal (deriv Θ t) * Complex.I)) t :=
    (Complex.hasDerivAt_exp _).comp t harg
  have hprod := hcast.mul hexp
  refine hprod.congr_deriv ?_
  push_cast
  ring

/-- **The basis form of the derivative of the polar curve.** -/
lemma deriv_polar {r Θ : ℝ → ℝ} (hr : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) r)
    (hΘ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Θ) (t : ℝ) :
    deriv (fun u : ℝ => (r (Θ u) : ℂ) * Complex.exp (((Θ u : ℝ) : ℂ) * Complex.I)) t
      = (Complex.ofReal (deriv r (Θ t)) + Complex.I * (r (Θ t) : ℂ))
        * Complex.ofReal (deriv Θ t) * Complex.exp (((Θ t : ℝ) : ℂ) * Complex.I) :=
  (hasDerivAt_polar hr hΘ t).deriv

/-- **The polar curve has no radial derivative**: its velocity is never a real multiple of its
position (the angular rate `Θ'` is nonzero). -/
lemma polar_deriv_not_radial {r Θ : ℝ → ℝ} (hr : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) r)
    (hrpos : ∀ φ : ℝ, 0 < r φ) (hΘ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Θ)
    (hΘderiv : ∀ t : ℝ, deriv Θ t ≠ 0) (t : ℝ) :
    ¬ ∃ s : ℝ, deriv (fun u : ℝ => (r (Θ u) : ℂ) * Complex.exp (((Θ u : ℝ) : ℂ) * Complex.I)) t
      = s • ((r (Θ t) : ℂ) * Complex.exp (((Θ t : ℝ) : ℂ) * Complex.I)) := by
  rintro ⟨s, hs⟩
  rw [deriv_polar hr hΘ t] at hs
  set E : ℂ := Complex.exp (((Θ t : ℝ) : ℂ) * Complex.I) with hEdef
  have hE : E ≠ 0 := Complex.exp_ne_zero _
  have h2 : (Complex.ofReal (deriv r (Θ t)) + Complex.I * (r (Θ t) : ℂ))
      * Complex.ofReal (deriv Θ t) = (s : ℂ) * (r (Θ t) : ℂ) := by
    refine mul_right_cancel₀ hE ?_
    simpa [E, smul_eq_mul, mul_assoc] using hs
  have him := congrArg Complex.im h2
  simp only [Complex.mul_im, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, zero_mul, mul_zero, add_zero] at him
  have hrp : 0 < r (Θ t) := hrpos _
  have hd : deriv Θ t = 0 := by
    have hmul : r (Θ t) * deriv Θ t = 0 := by linarith [him]
    exact (mul_eq_zero.mp hmul).resolve_left (ne_of_gt hrp)
  exact hΘderiv t hd

/-- **The far circle has no radial derivative** (about its own centre): the velocity is the rotation
of the radius vector. -/
lemma farCurve_deriv_not_radial (n : ℕ) (j : Fin n) (t : ℝ) :
    ¬ ∃ s : ℝ, deriv (fun u : ℝ => Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.farCurve n j u)) t
      = s • (Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.farCurve n j t)
        - Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.farPos n j)) := by
  rintro ⟨s, hs⟩
  rw [(hasDerivAt_proj2_farCurve n j t).deriv, proj2_farCurve n j t, add_sub_cancel_left] at hs
  have hZ : Work.Drive.N2Lead.proj2 (Work.Drive.N2.ang t) ≠ 0 := by
    intro h
    have h1 := norm_proj2_ang t
    rw [h] at h1
    simp at h1
  have hs' : ((2 * Real.pi : ℂ) * Complex.I) * Work.Drive.N2Lead.proj2 (Work.Drive.N2.ang t)
      = (s : ℂ) * Work.Drive.N2Lead.proj2 (Work.Drive.N2.ang t) := by
    simpa [smul_eq_mul] using hs
  have h2 : ((2 * Real.pi : ℂ) * Complex.I) = (s : ℂ) := mul_right_cancel₀ hZ hs'
  have him := congrArg Complex.im h2
  simp only [Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_zero, add_zero, sub_zero] at him
  norm_num at him

end Deriv

section Aux

/-- From `(r : ℂ) * exp (iθ) = (s : ℂ)` with `r, s > 0`: the exponential factor is `1`. -/
lemma exp_eq_one_of_mul_eq_pos {r s θ : ℝ} (hr : 0 < r) (hs : 0 < s)
    (h : (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) = (s : ℂ)) :
    Complex.exp ((θ : ℂ) * Complex.I) = 1 := by
  have h1 : ‖(r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖ = r := by
    rw [norm_mul, Complex.norm_exp]
    simp [Complex.ofReal_re, Real.norm_eq_abs, abs_of_pos hr]
  have h2 : ‖(s : ℂ)‖ = s := by
    simp [Real.norm_eq_abs, abs_of_pos hs]
  have hrs : r = s := by rw [← h1, h, h2]
  refine mul_left_cancel₀ (show (r : ℂ) ≠ 0 by exact_mod_cast (ne_of_gt hr)) ?_
  rw [h, mul_one, hrs]

/-- `exp (iθ) = 1` iff `θ` is an integer multiple of `2π`. -/
lemma exp_eq_one_iff_int_mul (θ : ℝ) :
    Complex.exp ((θ : ℂ) * Complex.I) = 1 ↔ ∃ m : ℤ, θ = m * (2 * Real.pi) := by
  constructor
  · intro h
    rw [Complex.exp_ofReal_mul_I] at h
    have hre := congrArg Complex.re h
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, sub_zero, add_zero] at hre
    norm_num at hre
    obtain ⟨m, hm⟩ := (Real.cos_eq_one_iff θ).mp hre
    exact ⟨m, hm.symm⟩
  · rintro ⟨m, rfl⟩
    refine Complex.exp_eq_one_iff.mpr ⟨m, ?_⟩
    push_cast
    ring

/-- `r (m · 2π) = r 0` for an integer `m`, from `2π`-periodicity. -/
lemma periodic_two_pi_int_mul {r : ℝ → ℝ} (hrper : ∀ φ : ℝ, r (φ + 2 * Real.pi) = r φ)
    (m : ℤ) : r ((m : ℝ) * (2 * Real.pi)) = r 0 := by
  have h : Function.Periodic r (2 * Real.pi) := hrper
  have h2 := h.int_mul m 0
  simpa using h2

end Aux
section Transport

open Work.Drive.N2Lead (proj2 farPos farCurve)

variable {f : M → ℝ} {u : ℝ}

/-- Real scalar multiplication of `ℂ` is complex multiplication by the coercion. -/
lemma real_smul_eq_mul (c : ℝ) (z : ℂ) : c • z = Complex.ofReal c * z := by
  rw [Algebra.smul_def]; rfl

/-- Division of a real scalar becomes division of the coerced scalar. -/
lemma smul_div_eq (c r : ℝ) (z : ℂ) (hr : r ≠ 0) : (c / r) • z = (c • z) / (r : ℂ) := by
  rw [real_smul_eq_mul, real_smul_eq_mul, Complex.ofReal_div]
  field_simp


lemma im_proj2_ang (t : ℝ) :
    (proj2 (Work.Drive.N2.ang t)).im = Real.sin (2 * Real.pi * t) := by
  rw [Work.Drive.N2.ang, Work.Drive.N2Lead.proj2_roundPic]

lemma re_proj2_ang (t : ℝ) :
    (proj2 (Work.Drive.N2.ang t)).re = Real.cos (2 * Real.pi * t) := by
  rw [Work.Drive.N2.ang, Work.Drive.N2Lead.proj2_roundPic]

lemma im_proj2_farCurve (n : ℕ) (j : Fin n) (t : ℝ) :
    (proj2 (farCurve n j t)).im = (20 + 5 * ((j : ℕ) : ℝ)) + Real.sin (2 * Real.pi * t) := by
  rw [proj2_farCurve, proj2_farPos, Complex.add_im, im_proj2_ang]

lemma norm_proj2_farCurve_ge (n : ℕ) (j : Fin n) (t : ℝ) :
    19 ≤ ‖proj2 (farCurve n j t)‖ := by
  have h1 := Complex.abs_im_le_norm (proj2 (farCurve n j t))
  rw [im_proj2_farCurve] at h1
  have h2 : -1 ≤ Real.sin (2 * Real.pi * t) := Real.neg_one_le_sin _
  have h3 : (0 : ℝ) ≤ ((j : ℕ) : ℝ) := Nat.cast_nonneg _
  have h4 := abs_le.mp h1
  nlinarith [h4.1]

lemma proj2_farCurve_sub (n : ℕ) (j : Fin n) (t : ℝ) :
    proj2 (farCurve n j t) - proj2 (farPos n j) = proj2 (Work.Drive.N2.ang t) := by
  rw [proj2_farCurve, add_sub_cancel_left]

/-- **The chain rule on a level curve**: the derivative of the picture along the level, in terms of
the parametrisation of the component. -/
lemma mfderiv_levelCurve_eq_deriv {W : M → Work.Drive.N2Lead.E3} {n : ℕ}
    (L : Work.Drive.N2C.LevelCurves f u n) {w : Fin n → ℝ → ℂ}
    (hWsm : ∀ y : M, f y = u → ContMDiffAt (𝓡 2) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) W y)
    (hw : ∀ (j : Fin n) (t : ℝ), proj2 (W (L.γ j t)) = w j t)
    (j : Fin n) (s t₀ : ℝ) :
    mfderiv (𝓡 2) 𝓘(ℝ,ℂ) (fun z : M => proj2 (W z)) (L.γ j s)
        (mfderiv 𝓘(ℝ,ℝ) (𝓡 2) (L.γ j) s t₀)
      = deriv (w j) s * (t₀ : ℂ) := by
  have hg : MDifferentiableAt (𝓡 2) 𝓘(ℝ,ℂ) (fun z : M => proj2 (W z)) (L.γ j s) :=
    Work.Drive.N2Lead.proj2CLM.mdifferentiableAt.comp _
      ((hWsm _ (L.val j s)).mdifferentiableAt (by simp))
  have hf : MDifferentiableAt 𝓘(ℝ,ℝ) (𝓡 2) (L.γ j) s :=
    (L.sm j).contMDiffAt.mdifferentiableAt (by simp)
  have hchain := mfderiv_comp_apply (I := 𝓘(ℝ,ℝ)) (I' := 𝓡 2) (I'' := 𝓘(ℝ,ℂ)) s
    (f := L.γ j) (g := fun z : M => proj2 (W z)) hg hf t₀
  have hcomp : ((fun z : M => proj2 (W z)) ∘ L.γ j) = fun u : ℝ => proj2 (W (L.γ j u)) := rfl
  rw [hcomp] at hchain
  rw [← hchain]
  have hfun : (fun u : ℝ => proj2 (W (L.γ j u))) = w j := funext fun u => hw j u
  rw [hfun]
  rw [mfderiv_eq_fderiv]
  calc (fderiv ℝ (w j) s) t₀ = (fderiv ℝ (w j) s) (t₀ • (1 : ℝ)) := by rw [smul_eq_mul, mul_one]
    _ = t₀ • (fderiv ℝ (w j) s) 1 := by rw [map_smul]
    _ = t₀ • deriv (w j) s := by rw [fderiv_apply_one_eq_deriv]
    _ = deriv (w j) s * (t₀ : ℂ) := by
      rw [Algebra.smul_def]
      exact mul_comm _ _

/-- The polar curve has no radial derivative even after multiplying the velocity by a nonzero real
factor. -/
lemma polar_deriv_mul_not_radial {r Θ : ℝ → ℝ} (hr : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) r)
    (hrpos : ∀ φ : ℝ, 0 < r φ) (hΘ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Θ)
    (hΘderiv : ∀ t : ℝ, deriv Θ t ≠ 0) (t t₀ : ℝ) (ht : t₀ ≠ 0) :
    ¬ ∃ c : ℝ, deriv (fun u : ℝ => (r (Θ u) : ℂ) * Complex.exp (((Θ u : ℝ) : ℂ) * Complex.I)) t
        * (t₀ : ℂ)
      = c • ((r (Θ t) : ℂ) * Complex.exp (((Θ t : ℝ) : ℂ) * Complex.I)) := by
  rintro ⟨c, hc⟩
  refine polar_deriv_not_radial hr hrpos hΘ hΘderiv t ⟨c / t₀, ?_⟩
  have ht₀ : ((t₀ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ht
  have hsm : (c / t₀) • ((r (Θ t) : ℂ) * Complex.exp (((Θ t : ℝ) : ℂ) * Complex.I))
      = (c • ((r (Θ t) : ℂ) * Complex.exp (((Θ t : ℝ) : ℂ) * Complex.I))) / (t₀ : ℂ) :=
    smul_div_eq c t₀ _ ht
  rw [hsm]
  rw [eq_div_iff ht₀]
  exact hc

/-- The far circle has no radial derivative about its own centre, even after multiplying the
velocity by a nonzero real factor. -/
lemma farCurve_deriv_mul_not_radial (n : ℕ) (j : Fin n) (t t₀ : ℝ) (ht : t₀ ≠ 0) :
    ¬ ∃ c : ℝ, deriv (fun u : ℝ => proj2 (farCurve n j u)) t * (t₀ : ℂ)
      = c • (proj2 (farCurve n j t) - proj2 (farPos n j)) := by
  rintro ⟨c, hc⟩
  refine farCurve_deriv_not_radial n j t ⟨c / t₀, ?_⟩
  have ht₀ : ((t₀ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ht
  have hsm : (c / t₀) • (proj2 (farCurve n j t) - proj2 (farPos n j))
      = (c • (proj2 (farCurve n j t) - proj2 (farPos n j))) / (t₀ : ℂ) :=
    smul_div_eq c t₀ _ ht
  rw [hsm]
  rw [eq_div_iff ht₀]
  exact hc

end Transport

section MainFleet

open Work.Drive.N2Lead (proj2 farPos farCurve)

/-- The imaginary part of a far circle minus a parking spot's projection. -/
lemma im_proj2_farCurve_sub_farPos (n : ℕ) (j k : Fin n) (t : ℝ) :
    (proj2 (farCurve n j t) - proj2 (farPos n k)).im
      = 5 * (((j : ℕ) : ℝ) - ((k : ℕ) : ℝ)) + Real.sin (2 * Real.pi * t) := by
  simp only [proj2_farCurve, proj2_farPos, Complex.add_im, Complex.sub_im, im_proj2_ang]
  ring

end MainFleet


section FleetAux

open Work.Drive.N2Lead (proj2 farPos farCurve)

/-- The planar projection of the planar inclusion `cE3` is the identity. -/
lemma proj2_cE3 (z : ℂ) : proj2 (Work.Drive.N2.cE3 z) = z := by
  apply Complex.ext <;> simp [Work.Drive.N2Lead.proj2]

/-- `|a| - |b| ≤ |a + b|`. -/
lemma abs_sub_abs_le_abs_add (a b : ℝ) : |a| - |b| ≤ |a + b| := by
  have h : |a| ≤ |a + b| + |b| := by
    calc |a| = |(a + b) + (-b)| := by ring_nf
      _ ≤ |a + b| + |-b| := abs_add_le _ _
      _ = |a + b| + |b| := by rw [abs_neg]
  linarith

/-- Two distinct natural numbers differ by at least `1`, so `|5 (j - k)| ≥ 5`. -/
lemma five_le_abs_five_mul_sub {j k : ℕ} (h : j ≠ k) :
    (5 : ℝ) ≤ |5 * ((j : ℝ) - (k : ℝ))| := by
  have hne : ((j : ℝ)) ≠ ((k : ℝ)) := by
    intro hh
    exact h (Nat.cast_injective hh)
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 5)]
  have h2 : (1 : ℝ) ≤ |((j : ℝ) - (k : ℝ))| := by
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have h1 : ((j : ℝ)) + 1 ≤ ((k : ℝ)) := by
        have h3 : j < k := by exact_mod_cast hlt
        exact_mod_cast (by omega : j + 1 ≤ k)
      rw [abs_of_neg (by linarith)]
      linarith
    · have h1 : ((k : ℝ)) + 1 ≤ ((j : ℝ)) := by
        have h3 : k < j := by exact_mod_cast hlt
        exact_mod_cast (by omega : k + 1 ≤ j)
      rw [abs_of_pos (by linarith)]
      linarith
  linarith

/-- The distance between two distinct parking spots' planar projections is at least `5`. -/
lemma dist_proj2_farPos_ge {n : ℕ} {j k : Fin n} (h : j ≠ k) :
    (5 : ℝ) ≤ dist (proj2 (farPos n j)) (proj2 (farPos n k)) := by
  rw [dist_eq_norm]
  have him : (proj2 (farPos n j) - proj2 (farPos n k)).im
      = 5 * (((j : ℕ) : ℝ) - ((k : ℕ) : ℝ)) := by
    simp only [proj2_farPos, Complex.sub_im]
    ring
  have h1 := Complex.abs_im_le_norm (proj2 (farPos n j) - proj2 (farPos n k))
  rw [him] at h1
  exact le_trans (five_le_abs_five_mul_sub (fun hh => h (Fin.ext hh))) h1

/-- The real part of the planar projection of a far circle. -/
lemma re_proj2_farCurve (n : ℕ) (j : Fin n) (t : ℝ) :
    (proj2 (farCurve n j t)).re = -20 + Real.cos (2 * Real.pi * t) := by
  simp only [proj2_farCurve, proj2_farPos, Complex.add_re, re_proj2_ang]

/-- The imaginary part of the planar projection of a parking spot. -/
lemma im_proj2_farPos (n : ℕ) (j : Fin n) :
    (proj2 (farPos n j)).im = 20 + 5 * ((j : ℕ) : ℝ) := by
  rw [proj2_farPos]

/-- The real part of the planar projection of a parking spot. -/
lemma re_proj2_farPos (n : ℕ) (j : Fin n) :
    (proj2 (farPos n j)).re = -20 := by
  rw [proj2_farPos]

end FleetAux

section FleetRegions

open Work.Drive.N2Lead (proj2 farPos farCurve)

/-- The region family of the lower certificate: the marked component `i` gets the disc `ball 0 17`,
every other component `k` the disc of radius `2` about the planar projection of its parking spot. -/
noncomputable def saddleRegions (n : ℕ) (i : Fin n) : Fin n → Set ℂ :=
  fun k => if k = i then Metric.ball 0 17
    else Metric.ball (proj2 (farPos n k)) 2

/-- The centres of the region family. -/
noncomputable def saddleCentres (n : ℕ) (i : Fin n) : Fin n → ℂ :=
  fun k => if k = i then 0 else proj2 (farPos n k)

lemma mem_saddleRegions_iff {n : ℕ} (i k : Fin n) (z : ℂ) :
    z ∈ saddleRegions n i k ↔
      (k = i ∧ z ∈ Metric.ball 0 17)
        ∨ (k ≠ i ∧ z ∈ Metric.ball (proj2 (farPos n k)) 2) := by
  by_cases hk : k = i
  · simp [saddleRegions, hk]
  · simp [saddleRegions, hk]

lemma mem_saddleCentres_iff {n : ℕ} (i k : Fin n) (z : ℂ) :
    saddleCentres n i k = z ↔
      (k = i ∧ (0 : ℂ) = z) ∨ (k ≠ i ∧ proj2 (farPos n k) = z) := by
  by_cases hk : k = i
  · simp [saddleCentres, hk]
  · simp [saddleCentres, hk]

lemma saddleCentres_self (n : ℕ) (i : Fin n) : saddleCentres n i i = 0 := by
  rw [saddleCentres, if_pos rfl]

lemma saddleCentres_of_ne {n : ℕ} {i k : Fin n} (h : k ≠ i) :
    saddleCentres n i k = proj2 (farPos n k) := by
  rw [saddleCentres, if_neg h]

lemma isOpen_convex_saddleRegions (n : ℕ) (i : Fin n) :
    ∀ k : Fin n, IsOpen (saddleRegions n i k) ∧ Convex ℝ (saddleRegions n i k) := by
  intro k
  by_cases hk : k = i
  · rw [saddleRegions, if_pos hk]
    exact ⟨Metric.isOpen_ball, convex_ball _ _⟩
  · rw [saddleRegions, if_neg hk]
    exact ⟨Metric.isOpen_ball, convex_ball _ _⟩

lemma closedBall_subset_saddleRegions (n : ℕ) (i : Fin n) :
    ∀ k : Fin n, Metric.closedBall (saddleCentres n i k) 1 ⊆ saddleRegions n i k := by
  intro k
  by_cases hk : k = i
  · rw [saddleRegions, saddleCentres, if_pos hk, if_pos hk]
    intro z hz
    have h := Metric.mem_closedBall.mp hz
    rw [dist_eq_norm, sub_zero] at h
    rw [Metric.mem_ball, dist_eq_norm, sub_zero]
    linarith
  · rw [saddleRegions, saddleCentres, if_neg hk, if_neg hk]
    intro z hz
    rw [Metric.mem_ball]
    exact lt_of_le_of_lt (Metric.mem_closedBall.mp hz) (by norm_num)

lemma pairwiseDisjoint_saddleRegions (n : ℕ) (i : Fin n) :
    Pairwise fun k l : Fin n => Disjoint (saddleRegions n i k) (saddleRegions n i l) := by
  intro k l hkl
  rw [Set.disjoint_left]
  intro z hzk hzl
  rw [mem_saddleRegions_iff] at hzk hzl
  have hfar_ge : 19 ≤ ‖proj2 (farPos n l)‖ := norm_proj2_farPos_ge n l
  have hfar_ge' : 19 ≤ ‖proj2 (farPos n k)‖ := norm_proj2_farPos_ge n k
  have htri : ∀ a b : ℂ, ‖a‖ - ‖b‖ ≤ ‖a - b‖ := by
    intro a b
    have h := norm_add_le (a - b) b
    rw [sub_add_cancel] at h
    linarith
  rcases hzk with ⟨hk, hzk⟩ | ⟨hk, hzk⟩
  · rcases hzl with ⟨hl, hzl⟩ | ⟨hl, hzl⟩
    · exact hkl (hk.trans hl.symm)
    · have h1 : ‖z‖ < 17 := by simpa [Metric.mem_ball, dist_zero_right] using hzk
      have h2 : ‖z - proj2 (farPos n l)‖ < 2 := by
        simpa [Metric.mem_ball, dist_eq_norm] using hzl
      have h3 := htri (proj2 (farPos n l)) z
      rw [norm_sub_rev] at h3
      linarith
  · rcases hzl with ⟨hl, hzl⟩ | ⟨hl, hzl⟩
    · have h1 : ‖z‖ < 17 := by simpa [Metric.mem_ball, dist_zero_right] using hzl
      have h2 : ‖z - proj2 (farPos n k)‖ < 2 := by
        simpa [Metric.mem_ball, dist_eq_norm] using hzk
      have h3 := htri (proj2 (farPos n k)) z
      rw [norm_sub_rev] at h3
      linarith
    · have h1 : ‖z - proj2 (farPos n k)‖ < 2 := by
        simpa [Metric.mem_ball, dist_eq_norm] using hzk
      have h2 : ‖z - proj2 (farPos n l)‖ < 2 := by
        simpa [Metric.mem_ball, dist_eq_norm] using hzl
      have h4 : dist (proj2 (farPos n k)) (proj2 (farPos n l))
          ≤ ‖z - proj2 (farPos n k)‖ + ‖z - proj2 (farPos n l)‖ := by
        rw [dist_eq_norm]
        calc ‖proj2 (farPos n k) - proj2 (farPos n l)‖
            = ‖(proj2 (farPos n k) - z) + (z - proj2 (farPos n l))‖ := by ring_nf
          _ ≤ ‖proj2 (farPos n k) - z‖ + ‖z - proj2 (farPos n l)‖ := norm_add_le _ _
          _ = ‖z - proj2 (farPos n k)‖ + ‖z - proj2 (farPos n l)‖ := by rw [norm_sub_rev]
      have h5 := dist_proj2_farPos_ge (n := n) (j := k) (k := l) hkl
      linarith

end FleetRegions



/-- **§4.2: the lower certificate of the saddle packet.**  With a `LevelCurves` parametrisation `L`
of the regular anchor level `f = a`, a picture `A` of that level with its injectivity and
`ker df`-immersivity rows, whose values on the marked component are the polar curve
`t ↦ cE3 (r (Θ t) * exp (i Θ t))` of a positive smooth `2π`-periodic profile `r` along a strictly
increasing angle function `Θ` with `Θ (t+1) = Θ t + 2π` and radius bound `r ≤ R < 17`, and whose
values on every other component are the parked round circles `farCurve n j` (centred at
`farPos n j = (-20, 20 + 5j, 1)`, radius `1`), the picture `A` is certified at `a`
(`Work.Drive.N2C.IsCertifiedAt f a A`). -/
theorem saddleLowerCertifiedFleet {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    {f : M → ℝ} {a : ℝ} {n : ℕ} (L : Work.Drive.N2C.LevelCurves f a n)
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hreg : ∀ x : M, f x = a → ¬ Work.Drive.Morse.IsCritical f x)
    {A : M → EuclideanSpace ℝ (Fin 3)}
    (hAsm : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))) ((⊤ : ℕ∞) : WithTop ℕ∞) A)
    (hAinj : ∀ x y : M, f x = a → f y = a → A x = A y → x = y)
    (hAimm : ∀ x : M, f x = a →
      ∀ v : TangentSpace (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) x,
      mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) (modelWithCornersSelf ℝ ℝ) f x v = 0 →
      mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))) A x v = 0 → v = 0)
    {i : Fin n} {r Θ : ℝ → ℝ} {R : ℝ}
    (hc : ∀ t : ℝ, A (L.γ i t) =
      Work.Drive.N2.cE3 (r (Θ t) * Complex.exp (((Θ t : ℝ) : ℂ) * Complex.I)))
    (hfarA : ∀ j : Fin n, j ≠ i → ∀ t : ℝ, A (L.γ j t) = Work.Drive.N2Lead.farCurve n j t)
    (hr : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) r) (hrpos : ∀ φ : ℝ, 0 < r φ)
    (hrper : ∀ φ : ℝ, r (φ + 2 * Real.pi) = r φ) (hrR : ∀ φ : ℝ, r φ ≤ R) (hR : R < 17)
    (hΘ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Θ) (hΘmono : StrictMono Θ)
    (hΘderiv : ∀ t : ℝ, deriv Θ t ≠ 0)
    (hΘper : ∀ t : ℝ, Θ (t + 1) = Θ t + 2 * Real.pi) :
    Work.Drive.N2C.IsCertifiedAt f a A := by
  classical
  have hRpos : 0 < R := lt_of_lt_of_le (hrpos 0) (hrR 0)
  -- ## the planar projections of the marked curve and of the far curves
  have hproj_i : ∀ t : ℝ, proj2 (A (L.γ i t))
      = (r (Θ t) : ℂ) * Complex.exp (((Θ t : ℝ) : ℂ) * Complex.I) := by
    intro t
    rw [hc t, proj2_cE3]
  have hproj_j : ∀ (j : Fin n), j ≠ i → ∀ t : ℝ,
      proj2 (A (L.γ j t)) = proj2 (farCurve n j t) := by
    intro j hj t
    rw [hfarA j hj t]
  have hPolNorm : ∀ u : ℝ,
      ‖(r (Θ u) : ℂ) * Complex.exp (((Θ u : ℝ) : ℂ) * Complex.I)‖ = r (Θ u) := by
    intro u
    rw [norm_mul]
    have h1 : ‖Complex.exp (((Θ u : ℝ) : ℂ) * Complex.I)‖ = 1 := by
      rw [Complex.norm_exp]; simp
    rw [h1, mul_one]
    simp [abs_of_pos (hrpos (Θ u))]
  have hPnorm : ∀ u : ℝ, ‖proj2 (A (L.γ i u))‖ = r (Θ u) := by
    intro u
    rw [hproj_i u]
    exact hPolNorm u
  -- the component projections, as functions of the parameter
  let w : Fin n → ℝ → ℂ := fun j t => proj2 (A (L.γ j t))
  have hwi : w i = fun t : ℝ => (r (Θ t) : ℂ) * Complex.exp (((Θ t : ℝ) : ℂ) * Complex.I) :=
    funext fun t => hproj_i t
  have hwj : ∀ (j : Fin n), j ≠ i → w j = fun t : ℝ => proj2 (farCurve n j t) :=
    fun j hj => funext fun t => hproj_j j hj t
  -- ## the constant family in the isotopy parameter is a level isotopy
  have hiso : Work.Drive.N2C.IsLevelIsotopy f a (fun _ : ℝ => A) := by
    refine ⟨?_, ?_, ?_⟩
    · intro s y hy
      exact (hAsm.contMDiffAt).comp (s, y) contMDiffAt_snd
    · intro s x y hx hy h
      exact hAinj x y hx hy h
    · intro s y hy v hvf hvA
      exact hAimm y hy v hvf hvA
  -- ## the chain rule along the level
  have hmfderiv : ∀ (j : Fin n) (s : ℝ) (v : TangentSpace (𝓡 2) (L.γ j s)),
      mfderiv (𝓡 2) 𝓘(ℝ,ℝ) f (L.γ j s) v = 0 → v ≠ 0 →
      ∃ t₀ : ℝ, t₀ ≠ 0 ∧ mfderiv (𝓡 2) 𝓘(ℝ,ℂ) (fun z : M => proj2 (A z)) (L.γ j s) v
          = deriv (w j) s * (t₀ : ℂ) := by
    intro j s v hv hv0
    obtain ⟨t₀, ht₀⟩ := L.ker j s v hv
    have ht₀ne : t₀ ≠ 0 := by
      intro h0
      apply hv0
      rw [← ht₀, h0]
      exact map_zero _
    exact ⟨t₀, ht₀ne, by
      rw [← ht₀]
      exact mfderiv_levelCurve_eq_deriv L (fun y hy => hAsm.contMDiffAt)
        (fun j t => rfl) j s t₀⟩
  -- ## which region a point of the level occupies
  have hregion_id : ∀ (j : Fin n) (s : ℝ) (k : Fin n),
      proj2 (A (L.γ j s)) ∈ saddleRegions n i k → k = j := by
    intro j s k hk
    rw [mem_saddleRegions_iff] at hk
    rcases hk with ⟨hki, hk⟩ | ⟨hki, hk⟩
    · by_contra hkj
      rw [Metric.mem_ball, dist_zero_right] at hk
      have hji : j ≠ i := fun h => hkj (hki.trans h.symm)
      rw [hproj_j j hji s] at hk
      have h1 := norm_proj2_farCurve_ge n j s
      linarith
    · rw [Metric.mem_ball, dist_eq_norm] at hk
      by_cases hji : j = i
      · exfalso
        rw [hji] at hk
        rw [hproj_i s] at hk
        have h2 : ‖proj2 (farPos n k)‖
            ≤ ‖(r (Θ s) : ℂ) * Complex.exp (((Θ s : ℝ) : ℂ) * Complex.I)‖
              + ‖(r (Θ s) : ℂ) * Complex.exp (((Θ s : ℝ) : ℂ) * Complex.I)
                - proj2 (farPos n k)‖ := by
          calc ‖proj2 (farPos n k)‖
              = ‖(r (Θ s) : ℂ) * Complex.exp (((Θ s : ℝ) : ℂ) * Complex.I)
                  - ((r (Θ s) : ℂ) * Complex.exp (((Θ s : ℝ) : ℂ) * Complex.I)
                    - proj2 (farPos n k))‖ := by congr 1; ring
            _ ≤ _ := norm_sub_le _ _
        rw [hPolNorm s] at h2
        have h4 := norm_proj2_farPos_ge n k
        linarith [hrR (Θ s), hR, hk, h2, h4]
      · by_contra hkj
        rw [hproj_j j hji s] at hk
        have h1 : (proj2 (farCurve n j s) - proj2 (farPos n k)).im
            = 5 * (((j : ℕ) : ℝ) - ((k : ℕ) : ℝ)) + Real.sin (2 * Real.pi * s) :=
          im_proj2_farCurve_sub_farPos n j k s
        have habs : |(proj2 (farCurve n j s) - proj2 (farPos n k)).im| ≤
            ‖proj2 (farCurve n j s) - proj2 (farPos n k)‖ := Complex.abs_im_le_norm _
        rw [h1] at habs
        have h5 : (5 : ℝ) ≤ |5 * (((j : ℕ) : ℝ) - ((k : ℕ) : ℝ))| :=
          five_le_abs_five_mul_sub (fun hc => hkj (Fin.ext hc).symm)
        have h6 : |Real.sin (2 * Real.pi * s)| ≤ 1 :=
          abs_le.mpr ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩
        have h7 : (4 : ℝ)
            ≤ |5 * (((j : ℕ) : ℝ) - ((k : ℕ) : ℝ)) + Real.sin (2 * Real.pi * s)| := by
          have := abs_sub_abs_le_abs_add (5 * (((j : ℕ) : ℝ) - ((k : ℕ) : ℝ)))
            (Real.sin (2 * Real.pi * s))
          linarith
        linarith
  -- ## every point of the level is in a region
  have hin : ∀ y : M, f y = a → ∃ k : Fin n, proj2 (A y) ∈ saddleRegions n i k := by
    intro y hy
    obtain ⟨j, s, rfl⟩ := L.cover y hy
    by_cases hji : j = i
    · rw [hji]
      refine ⟨i, ?_⟩
      rw [mem_saddleRegions_iff]
      refine Or.inl ⟨rfl, ?_⟩
      rw [Metric.mem_ball, dist_zero_right, hproj_i s, hPolNorm s]
      linarith [hrR (Θ s), hR]
    · refine ⟨j, ?_⟩
      rw [mem_saddleRegions_iff]
      refine Or.inr ⟨hji, ?_⟩
      rw [Metric.mem_ball, dist_eq_norm, hproj_j j hji s, proj2_farCurve_sub, norm_proj2_ang]
      norm_num
  -- ## the radial-rate rows
  have hrate : ∀ (y : M) (k : Fin n), f y = a → proj2 (A y) ∈ saddleRegions n i k →
      proj2 (A y) ≠ saddleCentres n i k ∧
      ∀ v : TangentSpace (𝓡 2) y, mfderiv (𝓡 2) 𝓘(ℝ,ℝ) f y v = 0 → v ≠ 0 →
        ¬ (∃ t : ℝ, mfderiv (𝓡 2) 𝓘(ℝ,ℂ) (fun z : M => proj2 (A z)) y v
            = t • (proj2 (A y) - saddleCentres n i k)) := by
    intro y k hy hk
    obtain ⟨j, s, rfl⟩ := L.cover y hy
    have hkj : k = j := hregion_id j s k hk
    rw [hkj]
    by_cases hji : j = i
    · rw [hji]
      have hctr : saddleCentres n i i = 0 := saddleCentres_self n i
      rw [hctr]
      refine ⟨?_, ?_⟩
      · rw [hproj_i s]
        intro h0
        have h := hPolNorm s
        rw [h0, norm_zero] at h
        linarith [hrpos (Θ s)]
      · intro v hv hv0 hcon
        obtain ⟨t₀, ht₀ne, hD⟩ := hmfderiv i s v hv hv0
        obtain ⟨c, hc'⟩ := hcon
        rw [hD, sub_zero] at hc'
        refine polar_deriv_mul_not_radial hr hrpos hΘ hΘderiv s t₀ ht₀ne ⟨c, ?_⟩
        rw [show deriv (fun u : ℝ => (r (Θ u) : ℂ) * Complex.exp (((Θ u : ℝ) : ℂ) * Complex.I)) s
              = deriv (w i) s from by rw [hwi]]
        rw [← hproj_i s]
        exact hc'
    · have hctr : saddleCentres n i j = proj2 (farPos n j) := saddleCentres_of_ne hji
      rw [hctr]
      refine ⟨?_, ?_⟩
      · rw [hproj_j j hji s]
        intro h0
        have h1 : ‖proj2 (farCurve n j s) - proj2 (farPos n j)‖ = 1 := by
          rw [proj2_farCurve_sub, norm_proj2_ang]
        rw [h0, sub_self, norm_zero] at h1
        norm_num at h1
      · intro v hv hv0 hcon
        obtain ⟨t₀, ht₀ne, hD⟩ := hmfderiv j s v hv hv0
        obtain ⟨c, hc'⟩ := hcon
        rw [hD] at hc'
        refine farCurve_deriv_mul_not_radial n j s t₀ ht₀ne ⟨c, ?_⟩
        rw [show deriv (fun u : ℝ => proj2 (farCurve n j u)) s = deriv (w j) s
              from by rw [hwj j hji]]
        rw [← hproj_j j hji s]
        exact hc'
  -- ## one ray is hit at most once
  have hhit : ∀ k : Fin n, ∃ e : ℂ, e ≠ 0 ∧ ∀ x y : M, f x = a → f y = a →
      (∃ s : ℝ, 0 < s ∧ proj2 (A x) = saddleCentres n i k + s • e) →
      (∃ s : ℝ, 0 < s ∧ proj2 (A y) = saddleCentres n i k + s • e) → x = y := by
    intro k
    refine ⟨1, one_ne_zero, ?_⟩
    intro x y hx hy hxray hyray
    obtain ⟨s, hs, hxs⟩ := hxray
    obtain ⟨s', hs', hys⟩ := hyray
    obtain ⟨j, t, rfl⟩ := L.cover x hx
    obtain ⟨j', t', rfl⟩ := L.cover y hy
    by_cases hki : k = i
    · -- the ray is the positive real axis
      rw [hki, saddleCentres_self, zero_add] at hxs hys
      have key : ∀ (m : Fin n) (u σ : ℝ), 0 < σ →
          proj2 (A (L.γ m u)) = σ • (1 : ℂ) → m = i ∧ ∃ c : ℤ, Θ u = c * (2 * Real.pi) := by
        intro m u σ hσ h
        have hm : m = i := by
          by_contra hmi
          rw [hproj_j m hmi u] at h
          have h1 := congrArg Complex.im h
          rw [im_proj2_farCurve] at h1
          have h2 : (σ • (1 : ℂ)).im = 0 := by simp [Complex.real_smul]
          rw [h2] at h1
          have h3 := Real.neg_one_le_sin (2 * Real.pi * u)
          have h4 : (0 : ℝ) ≤ ((m : ℕ) : ℝ) := Nat.cast_nonneg _
          nlinarith
        refine ⟨hm, ?_⟩
        rw [hm, hproj_i u] at h
        have h' : (r (Θ u) : ℂ) * Complex.exp (((Θ u : ℝ) : ℂ) * Complex.I) = (σ : ℂ) := by
          rw [h, Complex.real_smul, mul_one]
        exact (exp_eq_one_iff_int_mul (Θ u)).mp (exp_eq_one_of_mul_eq_pos (hrpos (Θ u)) hσ h')
      obtain ⟨hji, m, hm⟩ := key j t s hs hxs
      obtain ⟨hj'i, m', hm'⟩ := key j' t' s' hs' hys
      rw [hji, hj'i]
      have hshift := add_int_mul_period (θ := Θ) (m := 1)
        (fun u => by rw [hΘper u]; norm_num) t' (m - m')
      have hs_eq : Θ (t' + ((m - m' : ℤ) : ℝ)) = Θ t := by
        rw [hshift, hm', hm]
        push_cast
        ring
      have hst : t' + ((m - m' : ℤ) : ℝ) = t := hΘmono.injective hs_eq
      have hp : Function.Periodic (L.γ i) 1 := L.per i
      have hper : L.γ i (t' + ((m - m' : ℤ) : ℝ)) = L.γ i t' := by
        simpa using hp.int_mul (m - m') t'
      rw [← hst, hper]
    · -- the ray is the horizontal half-line from the parking spot
      have hctr : saddleCentres n i k = proj2 (farPos n k) := saddleCentres_of_ne hki
      rw [hctr] at hxs hys
      have hRay_im : ∀ σ : ℝ, (proj2 (farPos n k) + σ • (1 : ℂ)).im = 20 + 5 * ((k : ℕ) : ℝ) := by
        intro σ
        rw [Complex.add_im, im_proj2_farPos]
        simp [Complex.real_smul]
      have hRay_re : ∀ σ : ℝ, (proj2 (farPos n k) + σ • (1 : ℂ)).re = -20 + σ := by
        intro σ
        rw [Complex.add_re, re_proj2_farPos]
        simp [Complex.real_smul]
      have key : ∀ (m : Fin n) (u σ : ℝ), 0 < σ →
          proj2 (A (L.γ m u)) = proj2 (farPos n k) + σ • (1 : ℂ) → m = k ∧ ∃ c : ℤ, u = c := by
        intro m u σ hσ h
        have hmk : m = k := by
          by_contra hmk
          by_cases hmi : m = i
          · rw [hmi, hproj_i u] at h
            have h1 : |((r (Θ u) : ℂ) * Complex.exp (((Θ u : ℝ) : ℂ) * Complex.I)).im| ≤ R := by
              refine le_trans (Complex.abs_im_le_norm _) ?_
              rw [hPolNorm u]
              exact hrR (Θ u)
            have h3 : ((r (Θ u) : ℂ) * Complex.exp (((Θ u : ℝ) : ℂ) * Complex.I)).im ≤ R :=
              (abs_le.mp h1).2
            have him := congrArg Complex.im h
            rw [hRay_im σ] at him
            have h4 : (0 : ℝ) ≤ ((k : ℕ) : ℝ) := Nat.cast_nonneg _
            rw [him] at h3
            linarith
          · rw [hproj_j m hmi u] at h
            have him := congrArg Complex.im h
            rw [im_proj2_farCurve, hRay_im σ] at him
            have hsin : Real.sin (2 * Real.pi * u) = 5 * (((k : ℕ) : ℝ) - ((m : ℕ) : ℝ)) := by
              linarith
            have h6 : |Real.sin (2 * Real.pi * u)| ≤ 1 :=
              abs_le.mpr ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩
            rw [hsin] at h6
            have h7 : (5 : ℝ) ≤ |5 * (((k : ℕ) : ℝ) - ((m : ℕ) : ℝ))| :=
              five_le_abs_five_mul_sub (fun hc => hmk (Fin.ext hc).symm)
            linarith
        refine ⟨hmk, ?_⟩
        rw [hmk, hproj_j k hki u] at h
        have hsin0 : Real.sin (2 * Real.pi * u) = 0 := by
          have him := congrArg Complex.im h
          rw [im_proj2_farCurve, hRay_im σ] at him
          linarith
        have hcos : Real.cos (2 * Real.pi * u) = 1 := by
          have hre := congrArg Complex.re h
          rw [re_proj2_farCurve, hRay_re σ] at hre
          have hs2 : Real.cos (2 * Real.pi * u) = σ := by linarith
          have hsq := Real.cos_sq_add_sin_sq (2 * Real.pi * u)
          rw [hsin0] at hsq
          nlinarith [hs2, hσ]
        obtain ⟨c, hc⟩ := (Real.cos_eq_one_iff (2 * Real.pi * u)).mp hcos
        refine ⟨c, ?_⟩
        have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
        have h2 : (c : ℝ) * (2 * Real.pi) = u * (2 * Real.pi) := by linarith [hc]
        exact (mul_right_cancel₀ hpi h2).symm
      obtain ⟨hjk, mm, ha⟩ := key j t s hs hxs
      obtain ⟨hj'k, mm', ha'⟩ := key j' t' s' hs' hys
      rw [hjk, hj'k]
      have hst : t = t' + ((mm - mm' : ℤ) : ℝ) := by
        have h2 : ((mm : ℝ)) - ((mm' : ℝ)) = t - t' := by linarith [ha, ha']
        have h3 : t = t' + (((mm : ℝ)) - ((mm' : ℝ))) := by linarith
        rw [h3]
        push_cast
        ring
      have hp : Function.Periodic (L.γ k) 1 := L.per k
      have hper : L.γ k (t' + ((mm - mm' : ℤ) : ℝ)) = L.γ k t' := by
        simpa using hp.int_mul (mm - mm') t'
      rw [hst, hper]
  exact isCertifiedAt_of_starRegions (f := f) (u := a) (g := A) hf hreg hiso
    (saddleRegions n i) (saddleCentres n i) (fun _ => 1)
    (isOpen_convex_saddleRegions n i) (fun _ => one_pos)
    (closedBall_subset_saddleRegions n i) (pairwiseDisjoint_saddleRegions n i) hin hrate hhit


end

end Work.Drive.N2Lead
