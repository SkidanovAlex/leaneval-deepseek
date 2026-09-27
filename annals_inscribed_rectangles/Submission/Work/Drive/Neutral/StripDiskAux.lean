import Mathlib
import Submission.Work.Drive.planePt
import Submission.Work.Drive.stripChartSmooth
import Submission.Work.Drive.Neutral.stripTauData

/-!
# Auxiliary lemmas for the strip disk presentation

Two things:

* `Work.Drive.Neutral.contMDiffAt_cappingVecPoint` — the capping point given by a radius and a nonzero
  *physical* vector `Eucl 3` is smooth (generalises `Work.Drive.contMDiffAt_planePt`);
* the radial profile `Work.Drive.stripDiskPsi`/`rhoHat`/`tauHat` and the `τ`-coordinate used by
  `Work.Drive.exists_contMDiff_stripDiskPresentation`.
-/

namespace Work.Drive.Neutral

open Manifold
open scoped Manifold ContDiff

noncomputable section

/-! ## 1. The vector presentation of a capping point -/

open Classical in
/-- **Smoothness of the capping point with prescribed radius and physical vector.** -/
theorem contMDiffAt_cappingVecPoint {k : ℕ}
    (r : EuclideanSpace ℝ (Fin k) → ℝ) (V : EuclideanSpace ℝ (Fin k) → Eucl 3)
    (x₀ : EuclideanSpace ℝ (Fin k))
    (hr : ∀ w, 0 < r w) (hV : ∀ w, V w ≠ 0)
    (hrs : ContMDiffAt (𝓡 k) 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) r x₀)
    (hVs : ContMDiffAt (𝓡 k) 𝓘(ℝ, Eucl 3) ((⊤ : ℕ∞) : WithTop ℕ∞) V x₀) :
    letI := cappingCharted
    ContMDiffAt (𝓡 k) 𝓘(ℝ, EuclideanSpace ℝ (Fin 4)) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun w => cappingSpaceHomeoProj.symm
        (⟨r w, hr w⟩, Projectivization.mk ℝ (V w) (hV w))) x₀ := by
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 3))
      (Projectivization ℝ (EuclideanSpace ℝ (Fin 4))) := projCharted 3
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 1)) (Set.Ioi (0:ℝ)) :=
    Homeomorph.chartedSpace expHomeo
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (Set.Ioi (0:ℝ) × Projectivization ℝ (EuclideanSpace ℝ (Fin 4))) :=
    halfLineProjectiveCharted
  let F : EuclideanSpace ℝ (Fin k) → CappingSpace := fun w =>
    cappingSpaceHomeoProj.symm (⟨r w, hr w⟩, Projectivization.mk ℝ (V w) (hV w))
  let g : EuclideanSpace ℝ (Fin k) →
      Set.Ioi (0:ℝ) × Projectivization ℝ (EuclideanSpace ℝ (Fin 4)) :=
    fun w => cappingSpaceHomeoProj (F w)
  have hg : ∀ w, g w = (⟨r w, hr w⟩, Projectivization.mk ℝ (V w) (hV w)) := fun w =>
    cappingSpaceHomeoProj.apply_symm_apply _
  have hchart : (letI := cappingCharted
        ContMDiffAt (𝓡 k) 𝓘(ℝ, EuclideanSpace ℝ (Fin 4)) ((⊤ : ℕ∞) : WithTop ℕ∞) F x₀) ↔
      ContMDiffAt (𝓡 k) (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
        ((⊤ : ℕ∞) : WithTop ℕ∞) g x₀ :=
    chartedStructure_contMDiffWithinAt (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin 4))
      (H := EuclideanSpace ℝ (Fin 4)) (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      (E' := EuclideanSpace ℝ (Fin k)) (H' := EuclideanSpace ℝ (Fin k)) (𝓡 k)
      (M := Set.Ioi (0:ℝ) × Projectivization ℝ (EuclideanSpace ℝ (Fin 4)))
      (M' := CappingSpace) (n := ((⊤ : ℕ∞) : WithTop ℕ∞))
      cappingSpaceHomeoProj.symm F Set.univ x₀
  have hfirst : ContMDiffAt (𝓡 k) (𝓡 1) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun w => expHomeo.symm (g w).1) x₀ := by
    have hcomp : (fun w => expHomeo.symm (g w).1)
        = fun w => expHomeo.symm ⟨r w, hr w⟩ := by
      funext w
      rw [hg w]
    rw [hcomp]
    exact contMDiffAt_expHomeo_symm hr x₀ hrs
  have hsecond : ContMDiffAt (𝓡 k) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun w => (g w).2) x₀ := by
    have hcomp : (fun w => (g w).2)
        = fun w => Projectivization.mk ℝ (V w) (hV w) := by
      funext w
      rw [hg w]
    rw [hcomp]
    exact contMDiffAt_projMk V hV x₀ hVs
  exact hchart.mpr ((contMDiffAt_halfLineProjective_iff g x₀).mpr ⟨hfirst, hsecond⟩)

/-! ## 2. The radial profile -/

section Profile

/-- Lower splice weight: `0` below `1/4 - d`, `1` above `1/4`. -/
def psiL (d t : ℝ) : ℝ := Real.smoothTransition ((t - (1 / 4 - d)) / d)

/-- Lower-spliced profile: `1/4` below `1/4 - d`, `t` above `1/4`. -/
def psiLo (d t : ℝ) : ℝ := 1 / 4 + (t - 1 / 4) * psiL d t

/-- Upper splice weight: `1` below `1`, `0` above `1 + d`. -/
def psiUL (d t : ℝ) : ℝ := Real.smoothTransition (((1 + d) - t) / d)

/-- The clamped profile: equals `psiLo` up to `1` and is `1` from `1 + d` on. -/
def psiP (d t : ℝ) : ℝ := 1 + (psiLo d t - 1) * psiUL d t

/-- The radial profile `psi = sqrt (psiP)`. -/
def psi (d t : ℝ) : ℝ := Real.sqrt (psiP d t)

lemma psiL_nonneg (d t : ℝ) : 0 ≤ psiL d t := Real.smoothTransition.nonneg _

lemma psiL_le_one (d t : ℝ) : psiL d t ≤ 1 := Real.smoothTransition.le_one _

lemma contDiff_psiL (d : ℝ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (psiL d) := by
  have h : psiL d = fun t : ℝ => Real.smoothTransition ((t - (1 / 4 - d)) / d) := rfl
  rw [h]; fun_prop

lemma psiL_eq_one {d t : ℝ} (hd : 0 < d) (h : 1 / 4 ≤ t) : psiL d t = 1 :=
  Real.smoothTransition.one_of_one_le (by rw [le_div_iff₀ hd]; linarith)

lemma psiL_eq_zero {d t : ℝ} (hd : 0 < d) (h : t ≤ 1 / 4 - d) : psiL d t = 0 :=
  Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hd.le)

lemma contDiff_psiLo (d : ℝ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (psiLo d) := by
  have h : psiLo d = fun t : ℝ => 1 / 4 + (t - 1 / 4) * psiL d t := rfl
  rw [h]
  exact contDiff_const.add ((contDiff_id.sub contDiff_const).mul (contDiff_psiL d))

lemma psiLo_eq_quarter {d t : ℝ} (hd : 0 < d) (h : t ≤ 1 / 4 - d) : psiLo d t = 1 / 4 := by
  rw [psiLo, psiL_eq_zero hd h, mul_zero, add_zero]

lemma psiLo_eq_self {d t : ℝ} (hd : 0 < d) (h : 1 / 4 ≤ t) : psiLo d t = t := by
  rw [psiLo, psiL_eq_one hd h, mul_one]; ring

lemma psiLo_ge {d t : ℝ} (hd : 0 < d) (hd' : d < 1 / 4) : 1 / 4 - d ≤ psiLo d t := by
  have hlam0 : 0 ≤ psiL d t := psiL_nonneg d t
  have hlam1 : psiL d t ≤ 1 := psiL_le_one d t
  rcases lt_or_ge t (1 / 4 - d) with h | h
  · rw [psiLo_eq_quarter hd h.le]; linarith
  · rcases lt_or_ge t (1 / 4) with h2 | h2
    · have hkey : psiLo d t = 1 / 4 - (1 / 4 - t) * psiL d t := by rw [psiLo]; ring
      have hb : (1 / 4 - t) * psiL d t ≤ (1 / 4 - t) * 1 :=
        mul_le_mul_of_nonneg_left hlam1 (by linarith)
      rw [hkey]; linarith
    · rw [psiLo_eq_self hd h2]; linarith

lemma psiLo_le_one {d t : ℝ} (hd : 0 < d) (h : t ≤ 1) : psiLo d t ≤ 1 := by
  have hlam1 : psiL d t ≤ 1 := psiL_le_one d t
  rcases lt_or_ge t (1 / 4) with h2 | h2
  · have hkey : psiLo d t = 1 / 4 + (t - 1 / 4) * psiL d t := rfl
    have hb : (t - 1 / 4) * psiL d t ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) (psiL_nonneg d t)
    rw [hkey]; linarith
  · rw [psiLo_eq_self hd h2]; linarith

lemma psiUL_nonneg (d t : ℝ) : 0 ≤ psiUL d t := Real.smoothTransition.nonneg _

lemma psiUL_le_one (d t : ℝ) : psiUL d t ≤ 1 := Real.smoothTransition.le_one _

lemma contDiff_psiUL (d : ℝ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (psiUL d) := by
  have h : psiUL d = fun t : ℝ => Real.smoothTransition (((1 + d) - t) / d) := rfl
  rw [h]; fun_prop

lemma psiUL_eq_one {d t : ℝ} (hd : 0 < d) (h : t ≤ 1) : psiUL d t = 1 :=
  Real.smoothTransition.one_of_one_le (by rw [le_div_iff₀ hd]; linarith)

lemma psiUL_eq_zero {d t : ℝ} (hd : 0 < d) (h : 1 + d ≤ t) : psiUL d t = 0 :=
  Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hd.le)

lemma contDiff_psiP (d : ℝ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (psiP d) := by
  have h : psiP d = fun t : ℝ => 1 + (psiLo d t - 1) * psiUL d t := rfl
  rw [h]
  exact contDiff_const.add (((contDiff_psiLo d).sub contDiff_const).mul (contDiff_psiUL d))

lemma psiP_eq_self {d t : ℝ} (hd : 0 < d) (h : t ≤ 1) : psiP d t = psiLo d t := by
  rw [psiP, psiUL_eq_one hd h, mul_one, add_sub_cancel]

lemma psiP_eq_quarter {d t : ℝ} (hd : 0 < d) (hd' : d < 1 / 4) (h : t ≤ 1 / 4 - d) :
    psiP d t = 1 / 4 := by
  rw [psiP_eq_self hd (by linarith), psiLo_eq_quarter hd h]

lemma psiP_eq_one {d t : ℝ} (hd : 0 < d) (h : 1 + d ≤ t) : psiP d t = 1 := by
  rw [psiP, psiUL_eq_zero hd h, mul_zero, add_zero]

lemma psiP_ge {d : ℝ} (hd : 0 < d) (hd' : d < 1 / 4) (t : ℝ) : 1 / 4 - d ≤ psiP d t := by
  have hlo := psiLo_ge hd hd' (t := t)
  have hkey : psiP d t = 1 + (psiLo d t - 1) * psiUL d t := rfl
  rcases lt_or_ge (psiLo d t) 1 with h | h
  · have h0 : psiLo d t - 1 < 0 := by linarith
    have h1 : psiUL d t ≤ 1 := psiUL_le_one d t
    have hb : (psiLo d t - 1) * psiUL d t ≥ (psiLo d t - 1) * 1 :=
      mul_le_mul_of_nonpos_left h1 h0.le
    rw [hkey]; linarith
  · have h0 : 0 ≤ psiLo d t - 1 := by linarith
    have h1 : 0 ≤ psiUL d t := psiUL_nonneg d t
    have hb : 0 ≤ (psiLo d t - 1) * psiUL d t := mul_nonneg h0 h1
    rw [hkey]; linarith

lemma psiP_le {d : ℝ} (hd : 0 < d) (hd' : d < 1 / 4) (t : ℝ) : psiP d t ≤ 1 + d := by
  rcases lt_or_ge t 1 with h1 | h1
  · rw [psiP_eq_self hd h1.le]
    have := psiLo_le_one hd h1.le
    linarith
  · have hlo : psiLo d t = t := psiLo_eq_self hd (by linarith)
    have hkey : psiP d t = 1 + (t - 1) * psiUL d t := by rw [psiP, hlo]
    rw [hkey]
    rcases lt_or_ge t (1 + d) with h2 | h2
    · have h1' : psiUL d t ≤ 1 := psiUL_le_one d t
      have h2' : 0 ≤ t - 1 := by linarith
      nlinarith
    · have h2' : psiUL d t = 0 := psiUL_eq_zero hd h2
      rw [h2', mul_zero, add_zero]; linarith

lemma psiP_pos {d : ℝ} (hd : 0 < d) (hd' : d < 1 / 4) (t : ℝ) : 0 < psiP d t :=
  lt_of_lt_of_le (by linarith : (0:ℝ) < 1 / 4 - d) (psiP_ge hd hd' t)

lemma contDiff_psi {d : ℝ} (hd : 0 < d) (hd' : d < 1 / 4) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (psi d) :=
  (contDiff_psiP d).sqrt (fun t => ne_of_gt (psiP_pos hd hd' t))

lemma psi_eq_sqrt {d t : ℝ} (hd : 0 < d) (h : 1 / 4 ≤ t) (h2 : t ≤ 1) :
    psi d t = Real.sqrt t := by
  rw [psi, psiP_eq_self hd h2, psiLo_eq_self hd h]

lemma psi_lower {d : ℝ} (hd : 0 < d) (hd' : d < 1 / 4) (t : ℝ) :
    Real.sqrt (1 / 4 - d) ≤ psi d t := Real.sqrt_le_sqrt (psiP_ge hd hd' t)

lemma psi_upper {d : ℝ} (hd : 0 < d) (hd' : d < 1 / 4) (t : ℝ) :
    psi d t ≤ Real.sqrt (1 + d) := Real.sqrt_le_sqrt (psiP_le hd hd' t)

/-- The radial coordinate `rhoHat z = psi (normSq z)`. -/
def rhoHat (d : ℝ) (z : ℂ) : ℝ := psi d (Complex.normSq z)

/-- The `tau`-coordinate `(pi^2 / 2) * (rhoHat - 1/2)`. -/
def tauHat (d : ℝ) (z : ℂ) : ℝ := Real.pi ^ 2 / 2 * (rhoHat d z - 1 / 2)

/-- The direction-like variable `w = z / rhoHat`. -/
def wDir (d : ℝ) (z : ℂ) : ℂ := z / (rhoHat d z : ℂ)

lemma rhoHat_pos {d : ℝ} (hd : 0 < d) (hd' : d < 1 / 4) (z : ℂ) : 0 < rhoHat d z :=
  Real.sqrt_pos.mpr (psiP_pos hd hd' _)

lemma contDiff_normSqAux : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℂ => Complex.normSq z) := by
  have hfun : (fun z : ℂ => Complex.normSq z)
      = fun z : ℂ => z.re * z.re + z.im * z.im := by
    funext z; rw [Complex.normSq_apply]
  rw [hfun]
  exact ((Complex.reCLM.contDiff.mul Complex.reCLM.contDiff).add
    (Complex.imCLM.contDiff.mul Complex.imCLM.contDiff))

lemma contDiff_rhoHat {d : ℝ} (hd : 0 < d) (hd' : d < 1 / 4) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (rhoHat d) :=
  (contDiff_psi hd hd').comp contDiff_normSqAux

lemma normSq_ge {z : ℂ} (h : 1 / 2 ≤ ‖z‖) : 1 / 4 ≤ Complex.normSq z := by
  rw [Complex.normSq_eq_norm_sq]; nlinarith

lemma normSq_le {z : ℂ} (h : ‖z‖ ≤ 1) : Complex.normSq z ≤ 1 := by
  rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg z]

lemma rhoHat_eq_norm {d : ℝ} (hd : 0 < d) {z : ℂ} (h : 1 / 2 ≤ ‖z‖) (h2 : ‖z‖ ≤ 1) :
    rhoHat d z = ‖z‖ := by
  rw [rhoHat, psi_eq_sqrt hd (normSq_ge h) (normSq_le h2), Complex.normSq_eq_norm_sq,
    Real.sqrt_sq (norm_nonneg z)]

lemma rhoHat_lower {d : ℝ} (hd : 0 < d) (hd' : d < 1 / 4) (z : ℂ) :
    Real.sqrt (1 / 4 - d) ≤ rhoHat d z := psi_lower hd hd' _

lemma rhoHat_upper {d : ℝ} (hd : 0 < d) (hd' : d < 1 / 4) (z : ℂ) :
    rhoHat d z ≤ Real.sqrt (1 + d) := psi_upper hd hd' _

lemma tauHat_eq {d : ℝ} (hd : 0 < d) {z : ℂ} (h : 1 / 2 ≤ ‖z‖) (h2 : ‖z‖ ≤ 1) :
    tauHat d z = Real.pi ^ 2 * (‖z‖ - 1 / 2) / 2 := by
  rw [tauHat, rhoHat_eq_norm hd h h2]; ring

lemma contDiff_tauHat {d : ℝ} (hd : 0 < d) (hd' : d < 1 / 4) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (tauHat d) := by
  have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℂ => rhoHat d z - 1 / 2) :=
    (contDiff_rhoHat hd hd').sub contDiff_const
  have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : ℂ => (Real.pi ^ 2 / 2 : ℝ) * (rhoHat d z - 1 / 2)) :=
    (contDiff_const : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun _ : ℂ => (Real.pi ^ 2 / 2 : ℝ))).mul h1
  have h3 : tauHat d = fun z : ℂ => (Real.pi ^ 2 / 2 : ℝ) * (rhoHat d z - 1 / 2) := rfl
  rw [h3]
  exact h2

lemma contDiff_wDir {d : ℝ} (hd : 0 < d) (hd' : d < 1 / 4) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (wDir d) := by
  have hden : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℂ => ((rhoHat d z : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_rhoHat hd hd')
  have hne : ∀ z : ℂ, ((rhoHat d z : ℝ) : ℂ) ≠ 0 := fun z =>
    Complex.ofReal_ne_zero.mpr (ne_of_gt (rhoHat_pos hd hd' z))
  have hid : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℂ => z) := contDiff_id
  have hinv : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : ℂ => (((rhoHat d z : ℝ) : ℂ))⁻¹) := hden.inv hne
  have h3 : wDir d = fun z : ℂ => z * (((rhoHat d z : ℝ) : ℂ))⁻¹ := by
    funext z; rw [wDir, div_eq_mul_inv]
  rw [h3]
  exact hid.mul hinv

lemma wDir_eq {d : ℝ} (hd : 0 < d) {z : ℂ} (h : 1 / 2 ≤ ‖z‖) (h2 : ‖z‖ ≤ 1) :
    wDir d z = z / (‖z‖ : ℂ) := by
  rw [wDir, rhoHat_eq_norm hd h h2]

lemma norm_wDir {d : ℝ} (hd : 0 < d) {z : ℂ} (h : 1 / 2 ≤ ‖z‖) (h2 : ‖z‖ ≤ 1) :
    ‖wDir d z‖ = 1 := by
  have hz : ‖z‖ ≠ 0 := by linarith
  rw [wDir_eq hd h h2, norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg z),
    div_self hz]

end Profile

/-! ## 3. The chord data of the pair `{x e^{is}, x e^{-is}}` -/

section ChordData

/-- The point of `Circle = Submonoid.unitSphere ℂ` with the given nonzero complex representative. -/
def toCirc (y : ℂ) (hy : y ≠ 0) : Circle :=
  ⟨y / ‖y‖, by
    have h : ‖y / ‖y‖‖ = 1 := by
      rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg y)]
      exact div_self (norm_ne_zero_iff.mpr hy)
    simpa [Submonoid.unitSphere] using h⟩

variable (γ : Circle → ℝ × ℝ)

/-- Clamping weight for the chord opening: `1` for `|s| ≤ π/2`, `0` for `|s| ≥ π - 1`. -/
def sKappa (s : ℝ) : ℝ :=
  Real.smoothTransition (((Real.pi - 1) ^ 2 - s ^ 2) / ((Real.pi - 1) ^ 2 - (Real.pi / 2) ^ 2))

lemma contDiff_sKappa : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) sKappa := by
  have h : sKappa = fun s : ℝ =>
      Real.smoothTransition (((Real.pi - 1) ^ 2 - s ^ 2) / ((Real.pi - 1) ^ 2 - (Real.pi / 2) ^ 2)) :=
    rfl
  rw [h]; fun_prop

/-- The odd, smooth, bounded model function `s ↦ s/√(1+s²)` (bounded by `1`). -/
def sSig (s : ℝ) : ℝ := s / Real.sqrt (1 + s ^ 2)

lemma contDiff_sSig : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) sSig := by
  have h : sSig = fun s : ℝ => s / Real.sqrt (1 + s ^ 2) := rfl
  rw [h]
  have hden : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun s : ℝ => Real.sqrt (1 + s ^ 2)) :=
    (contDiff_const.add (contDiff_id.pow 2)).sqrt (fun s => by positivity)
  exact contDiff_id.div hden (fun s => by positivity)

lemma sSig_odd (s : ℝ) : sSig (-s) = -sSig s := by
  simp only [sSig]
  ring

lemma abs_sSig_lt_one (s : ℝ) : |sSig s| < 1 := by
  have h1 : (0:ℝ) < Real.sqrt (1 + s ^ 2) := Real.sqrt_pos.mpr (by positivity)
  rw [sSig, abs_div, abs_of_nonneg h1.le, div_lt_one h1]
  rw [Real.lt_sqrt (abs_nonneg s)]
  nlinarith [sq_abs s]

lemma abs_sSig_le_one (s : ℝ) : |sSig s| ≤ 1 := (abs_sSig_lt_one s).le

lemma sKappa_nonneg (s : ℝ) : 0 ≤ sKappa s := Real.smoothTransition.nonneg _

lemma sKappa_le_one (s : ℝ) : sKappa s ≤ 1 := Real.smoothTransition.le_one _

lemma sKappa_denom_pos : (0:ℝ) < (Real.pi - 1) ^ 2 - (Real.pi / 2) ^ 2 := by
  nlinarith [Real.pi_gt_three]

lemma sKappa_eq_one {s : ℝ} (h : |s| ≤ Real.pi / 2) : sKappa s = 1 := by
  refine Real.smoothTransition.one_of_one_le ?_
  rw [le_div_iff₀ sKappa_denom_pos]
  have h2 : s ^ 2 ≤ (Real.pi / 2) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h 2
  linarith

lemma sKappa_eq_zero {s : ℝ} (h : Real.pi - 1 ≤ |s|) : sKappa s = 0 := by
  refine Real.smoothTransition.zero_of_nonpos ?_
  rw [div_nonpos_iff]
  right
  constructor
  · have h2 : (Real.pi - 1) ^ 2 ≤ s ^ 2 := by
      nlinarith [h, abs_nonneg s, sq_abs s, Real.pi_gt_three]
    linarith
  · exact sKappa_denom_pos.le

/-- **The clamped chord opening**: smooth, odd, equal to `s` for `|s| ≤ π/2` and bounded by `π - 1`.
This is what keeps the two chord endpoints distinct for *all* openings, so that the divided difference
(hence the halving of the doubled direction) is smooth and nowhere zero. -/
def sClamp (s : ℝ) : ℝ :=
  s * sKappa s + (Real.pi - 1) * (1 - sKappa s) * sSig s

lemma contDiff_sClamp : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) sClamp := by
  have h : sClamp = fun s : ℝ =>
      s * sKappa s + (Real.pi - 1) * (1 - sKappa s) * sSig s := rfl
  rw [h]
  exact ((contDiff_id.mul contDiff_sKappa).add
    ((contDiff_const.mul (contDiff_const.sub contDiff_sKappa)).mul contDiff_sSig))

lemma sClamp_odd (s : ℝ) : sClamp (-s) = -sClamp s := by
  have h1 : sKappa (-s) = sKappa s := by simp only [sKappa, neg_sq]
  rw [sClamp, sClamp, h1, sSig_odd]
  ring

lemma sClamp_eq_self {s : ℝ} (h : |s| ≤ Real.pi / 2) : sClamp s = s := by
  rw [sClamp, sKappa_eq_one h]
  ring

lemma abs_sClamp_le {s : ℝ} : |sClamp s| ≤ Real.pi - 1 := by
  have hπ : (0:ℝ) < Real.pi - 1 := by linarith [Real.pi_gt_three]
  have htanh : |sSig s| ≤ 1 := abs_sSig_le_one s
  rcases lt_or_ge (Real.pi - 1) |s| with h | h
  · rw [sClamp, sKappa_eq_zero h.le]
    simp only [mul_zero, sub_zero, zero_add, one_mul]
    have : |(Real.pi - 1) * sSig s| ≤ Real.pi - 1 := by
      rw [abs_mul, abs_of_nonneg hπ.le]
      calc (Real.pi - 1) * |sSig s| ≤ (Real.pi - 1) * 1 :=
            mul_le_mul_of_nonneg_left htanh hπ.le
        _ = Real.pi - 1 := by ring
    simpa only [mul_one] using this
  · have h1 : sClamp s = sKappa s * s + (1 - sKappa s) * ((Real.pi - 1) * sSig s) := by
      rw [sClamp]; ring
    rw [h1]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg (sKappa_nonneg s),
      abs_of_nonneg (by linarith [sKappa_le_one s] : (0:ℝ) ≤ 1 - sKappa s)]
    have hA : sKappa s * |s| ≤ sKappa s * (Real.pi - 1) :=
      mul_le_mul_of_nonneg_left h (sKappa_nonneg s)
    have hB : (1 - sKappa s) * |(Real.pi - 1) * sSig s| ≤ (1 - sKappa s) * (Real.pi - 1) := by
      have h2 : |(Real.pi - 1) * sSig s| ≤ Real.pi - 1 := by
        rw [abs_mul, abs_of_nonneg hπ.le]
        calc (Real.pi - 1) * |sSig s| ≤ (Real.pi - 1) * 1 :=
              mul_le_mul_of_nonneg_left htanh hπ.le
          _ = Real.pi - 1 := by ring
      exact mul_le_mul_of_nonneg_left h2 (by linarith [sKappa_le_one s])
    have : sKappa s * (Real.pi - 1) + (1 - sKappa s) * (Real.pi - 1) = Real.pi - 1 := by ring
    linarith

/-- The complexified curve point at the clamped circle parameter of `x * exp (s * I)`, i.e.
`symmC (γ ((x/‖x‖) e^{i sClamp s}))`; a junk value at `x = 0` (where it is never used). -/
def curvePtAt (x : ℂ) (s : ℝ) : ℂ :=
  if hx : x = 0 then 0
  else symmC (γ (toCirc (x * Complex.exp ((sClamp s) * Complex.I))
    (mul_ne_zero hx (Complex.exp_ne_zero _))))

/-- The `+` endpoint of the chord with midpoint parameter `x` (as a complex number) and half opening
`s`. -/
def endPlus (x : ℂ) (s : ℝ) : ℂ := curvePtAt γ x s

/-- The `-` endpoint. -/
def endMinus (x : ℂ) (s : ℝ) : ℂ := curvePtAt γ x (-s)

/-- The complexified midpoint of the chord. -/
def dataMid (x : ℂ) (s : ℝ) : ℂ := (endPlus γ x s + endMinus γ x s) / 2

/-- The complexified chord vector. -/
def dataChord (x : ℂ) (s : ℝ) : ℂ := endPlus γ x s - endMinus γ x s

/-- The capping radius of the chord. -/
def dataR (x : ℂ) (s : ℝ) : ℝ :=
  Real.sqrt (Complex.normSq (dataMid γ x s) + Complex.normSq (dataChord γ x s))

/-- The disk coordinate of the chord. -/
def dataD (x : ℂ) (s : ℝ) : ℂ := dataMid γ x s / (dataR γ x s : ℂ)

end ChordData

/-! ## 4. The blends -/

section Blend

/-- The bump in `x`: a smooth function of `normSq x`, `0` for `|x| ≤ 1/2` and `1` for
`|x| ≥ √(1/4 + 1/(4k))`. -/
def muX (k : ℕ) (x : ℂ) : ℝ := Real.smoothTransition ((Complex.normSq x - 1 / 4) * (4 * k))

/-- The anchor vector `(0,1) ∈ ℂ² ≅ Eucl 3`. -/
def anchorV : Eucl 3 := ofComplex 0 1

variable (γ : Circle → ℝ × ℝ)

/-- The physical (unit) vector of the chord data at `(x,s)`, given a halving `W` of the doubled
chord direction. -/
def dataVOf (W : ℂ × ℝ → ℂ) (x : ℂ) (s : ℝ) : Eucl 3 :=
  confProjVecOf (W (x, s) / (‖W (x, s)‖ : ℂ)) (dataD γ x s)

/-- The blended physical vector, with the anchor `(0,1)` off the unit circle. -/
def dataVbOf (k : ℕ) (W : ℂ × ℝ → ℂ) (x : ℂ) (s : ℝ) : Eucl 3 :=
  (muX k x) • dataVOf γ W x s + (1 - muX k x) • anchorV

/-- The blended capping radius. -/
def dataRbOf (k : ℕ) (x : ℂ) (s : ℝ) : ℝ :=
  muX k x * dataR γ x s + (1 - muX k x) * 1

end Blend

end

end Work.Drive.Neutral