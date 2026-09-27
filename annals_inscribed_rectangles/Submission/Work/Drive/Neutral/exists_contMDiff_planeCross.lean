import Mathlib
import Submission.Work.Drive.planePt
import Submission.Work.Drive.stripChartSmooth
import Submission.Work.Drive.Neutral.stripTauData
import Submission.Work.Drive.Neutral.stripTauChart
import Submission.Work.Drive.cappedPlaneFamily
import Submission.Work.Drive.seeleyDescent_ext
import Submission.Work.Drive.contDiffOn_even_comp_sqrt_local
import Submission.Work.Drive.Neutral.exists_contMDiff_stripPlane
import Submission.Work.Drive.unit_mul_sq_div

/-!
# The plane cross of the seam

Given a smooth embedded plane curve `γ` avoiding the origin and a parameter `σ₀` of the gluing curve,
this file produces a **globally** `C^∞` map `F` of the plane into the capping space which

* on the half-strip `{0 < q 1 < ε}` is the strip chart `stripChart γ hγne 0` of the chord
  `(q 0 + √(q 1), q 0 - √(q 1))` (the configuration side of the seam), and
* on the half-strip `{-ε < q 1 < 0}` is a point of the **cap** solid torus.

The construction: the symmetric chord data `(symmMid, symmWC)` is even in the opening parameter `s`,
so by Seeley's even-`√` descent it extends to globally smooth data `M, W` on `ℝ²` with
`M (σ, s) = symmC (symmMid γ σ √s)`, `W (σ, s) = symmWC γ σ √s` for `s ≥ 0`.  The corresponding
capping data is
`A = ‖M‖² + 4 τ ‖W‖²`, `R = √A`, `D = M / R` (so `‖D‖² = ‖M‖²/A`), and the disk coordinate `D`
crosses the unit circle exactly when `τ` changes sign: `‖D‖ < 1` for `τ > 0` (configuration) and
`‖D‖ > 1` for `τ < 0` (cap).  The single formula `planePt` (`Submission/Work/Drive/planePt.lean`)
then presents both sides, and its smoothness across the seam is `contMDiffAt_planePt`.

The halving of the `S¹`-coordinate is `W / ‖W‖`, whose square is the squared chord direction; it is
anchored at the base point and normalised so that it is unit-valued everywhere.
-/

namespace Work.Drive.Neutral

open Manifold
open scoped Manifold ContDiff Topology

noncomputable section

variable {γ : Circle → ℝ × ℝ}

/-! ## Elementary helpers -/

/-- **Proof irrelevance for the non-vanishing argument of `planePt`.** -/
lemma planePt_congr_hv {u : ℂ} {r : ℝ} (hr : 0 < r) {d : ℂ} (hu : ‖u‖ = 1)
    (hv₁ hv₂ : confProjVecOf u d ≠ 0) :
    planePt u r hr d hu hv₁ = planePt u r hr d hu hv₂ := by
  have h : Projectivization.mk ℝ (confProjVecOf u d) hv₁
      = Projectivization.mk ℝ (confProjVecOf u d) hv₂ :=
    (Projectivization.mk_eq_mk_iff ℝ _ _ hv₁ hv₂).mpr ⟨1, one_smul ℝ _⟩
  simp only [planePt, h]

/-- **The cap clause for `planePt`, in the form used below.**  For unit `u`, positive `r` and
`1 ≤ ‖d‖ ≤ √2` the plane point is a point of the cap solid torus. -/
theorem exists_capPiece_planePt' {u : ℂ} {r : ℝ} (hr : 0 < r) {d : ℂ} (hu : ‖u‖ = 1)
    (hd1 : 1 ≤ ‖d‖) (hd2 : ‖d‖ ≤ Real.sqrt 2)
    (hv : confProjVecOf u d ≠ 0) :
    ∃ c : CapPiece, planePt u r hr d hu hv = Quotient.mk'' (Sum.inr c) := by
  obtain ⟨c, hc⟩ := exists_capPiece_planePt hr hu hd1 hd2
  refine ⟨c, ?_⟩
  rw [← planePt_congr_hv hr hu hv (confProjVecOf_ne_zero_of_le_sqrt2 hu hd2)]
  exact hc

/-- **Newton–Leibniz for the symmetric family**: the chord is `2 s` times the divided difference. -/
lemma symmChordC_eq_smul_symmWC
    (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) γ) (σ s : ℝ) :
    symmChordC γ σ s = (((2 * s : ℝ)) : ℂ) * symmWC γ σ s := by
  have hsub : γ (Circle.exp (σ + s)) - γ (Circle.exp (σ - s))
      = ((2 * s : ℝ)) • secantW (curve γ) (σ + s, σ - s) := by
    have h' := sub_eq_smul_secantW (contDiff_curve γ hγ) (σ + s) (σ - s)
    rwa [show σ + s - (σ - s) = 2 * s from by ring] at h'
  rw [symmChordC, chordC_eq_symmC, hsub, symmC_smul, symmWC]

/-- The complexification of the symmetric midpoint is the numerator of `symmD`. -/
lemma symmC_symmMid_eq (γ : Circle → ℝ × ℝ) (σ s : ℝ) :
    symmC (symmMid γ σ s)
      = (((symmMid γ σ s).1 : ℂ) + ((symmMid γ σ s).2 : ℂ) * Complex.I) := by
  refine Complex.ext ?_ ?_ <;> simp [symmC]

/-- The three algebraic identities for the symmetric chord data. -/
theorem symmData_norm_identities'
    (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) γ) (σ s : ℝ) :
    symmA γ σ s = ‖symmC (symmMid γ σ s)‖ ^ 2 + 4 * s ^ 2 * ‖symmWC γ σ s‖ ^ 2 ∧
    symmD γ σ s = symmC (symmMid γ σ s) / (((symmR γ σ s : ℝ)) : ℂ) ∧
    (symmWC γ σ s / (((‖symmWC γ σ s‖ : ℝ)) : ℂ)) ^ 2 = symmE γ σ s := by
  have hchord := symmChordC_eq_smul_symmWC hγ σ s
  have hnormC : ‖symmC (symmMid γ σ s)‖ ^ 2
      = (symmMid γ σ s).1 ^ 2 + (symmMid γ σ s).2 ^ 2 := by
    rw [norm_symmC]
    simp only [Submission.Geometry.eucNorm, Submission.Geometry.eucDot_self]
    rw [Real.sq_sqrt (by positivity)]
  have hchordN : Complex.normSq (symmChordC γ σ s) = 4 * s ^ 2 * ‖symmWC γ σ s‖ ^ 2 := by
    rw [Complex.normSq_eq_norm_sq, hchord, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      mul_pow, sq_abs]
    ring
  have hD : symmD γ σ s = symmC (symmMid γ σ s) / (((symmR γ σ s : ℝ)) : ℂ) := by
    rw [symmD, symmC_symmMid_eq]
  have hE : (symmWC γ σ s / (((‖symmWC γ σ s‖ : ℝ)) : ℂ)) ^ 2 = symmE γ σ s := by
    rw [symmE, div_eq_mul_inv, one_div, Complex.ofReal_inv]
  exact ⟨by rw [symmA, hchordN, hnormC], hD, hE⟩

/-! ## The descended capping data -/

/-- The squared capping radius of the descended symmetric data: the squared norm of the (complexified)
midpoint plus `4 τ` times the squared norm of the divided difference. -/
def dA (M W : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℝ := ‖M p‖ ^ 2 + 4 * p.2 * ‖W p‖ ^ 2

/-- The capping radius of the descended symmetric data. -/
def dR (M W : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℝ := Real.sqrt (dA M W p)

/-- The disk coordinate of the descended symmetric data. -/
def dD (M W : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℂ := M p / (((dR M W p : ℝ)) : ℂ)

/-- The squared unit chord direction of the descended symmetric data. -/
def dE (W : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℂ := (W p / (((‖W p‖ : ℝ)) : ℂ)) ^ 2

lemma contDiffAt_dA {M W : ℝ × ℝ → ℂ} (hM : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) M)
    (hW : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W) (p : ℝ × ℝ) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (dA M W) p := by
  have hMre : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : ℝ × ℝ => (M q).re) p :=
    (Complex.reCLM.contDiff.contDiffAt).comp p hM.contDiffAt
  have hMim : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : ℝ × ℝ => (M q).im) p :=
    (Complex.imCLM.contDiff.contDiffAt).comp p hM.contDiffAt
  have h1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : ℝ × ℝ => ‖M q‖ ^ 2) p := by
    have h := (hMre.mul hMre).add (hMim.mul hMim)
    refine h.congr_of_eventuallyEq ?_
    filter_upwards with q
    rw [Complex.sq_norm, Complex.normSq_apply]
  have hWre : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : ℝ × ℝ => (W q).re) p :=
    (Complex.reCLM.contDiff.contDiffAt).comp p hW.contDiffAt
  have hWim : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : ℝ × ℝ => (W q).im) p :=
    (Complex.imCLM.contDiff.contDiffAt).comp p hW.contDiffAt
  have h2 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : ℝ × ℝ => ‖W q‖ ^ 2) p := by
    have h := (hWre.mul hWre).add (hWim.mul hWim)
    refine h.congr_of_eventuallyEq ?_
    filter_upwards with q
    rw [Complex.sq_norm, Complex.normSq_apply]
  have h3 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : ℝ × ℝ => 4 * q.2 * ‖W q‖ ^ 2) p :=
    (contDiffAt_const.mul contDiffAt_snd).mul h2
  exact h1.add h3

lemma contDiffAt_dR {M W : ℝ × ℝ → ℂ} (hM : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) M)
    (hW : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W) {p : ℝ × ℝ} (hp : 0 < dA M W p) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (dR M W) p :=
  (Real.contDiffAt_sqrt (ne_of_gt hp)).comp p (contDiffAt_dA hM hW p)

lemma contDiffAt_dD {M W : ℝ × ℝ → ℂ} (hM : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) M)
    (hW : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W) {p : ℝ × ℝ} (hp : 0 < dA M W p) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (dD M W) p := by
  have hR : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (dR M W) p := contDiffAt_dR hM hW hp
  have hden : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : ℝ × ℝ => (((dR M W q : ℝ)) : ℂ)) p :=
    (Complex.ofRealCLM.contDiff.contDiffAt).comp p hR
  have hne : (((dR M W p : ℝ)) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]
    exact ne_of_gt (Real.sqrt_pos.mpr hp)
  have h : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => M p / (((dR M W p : ℝ)) : ℂ)) p := by
    have := hM.contDiffAt.mul (hden.inv hne)
    simpa only [div_eq_mul_inv, Pi.inv_apply] using this
  exact h

lemma contDiffAt_dE {W : ℝ × ℝ → ℂ} (hW : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W)
    {p : ℝ × ℝ} (hp : W p ≠ 0) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (dE W) p := by
  have hnorm : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : ℝ × ℝ => ‖W q‖) p :=
    ContDiffAt.norm ℝ hW.contDiffAt hp
  have hden : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : ℝ × ℝ => (((‖W q‖ : ℝ)) : ℂ)) p :=
    (Complex.ofRealCLM.contDiff.contDiffAt).comp p hnorm
  have hne : (((‖W p‖ : ℝ)) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]
    exact norm_ne_zero_iff.mpr hp
  have h : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => (W p / (((‖W p‖ : ℝ)) : ℂ)) ^ 2) p := by
    have := (hW.contDiffAt.mul (hden.inv hne)).pow 2
    simpa only [div_eq_mul_inv, Pi.inv_apply] using this
  exact h

lemma contDiffOn_dR {M W : ℝ × ℝ → ℂ} (hM : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) M)
    (hW : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W) {U : Set (ℝ × ℝ)}
    (hU : ∀ p ∈ U, 0 < dA M W p) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (dR M W) U :=
  fun p hp => (contDiffAt_dR hM hW (hU p hp)).contDiffWithinAt

lemma contDiffOn_dD {M W : ℝ × ℝ → ℂ} (hM : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) M)
    (hW : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W) {U : Set (ℝ × ℝ)}
    (hU : ∀ p ∈ U, 0 < dA M W p) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (dD M W) U :=
  fun p hp => (contDiffAt_dD hM hW (hU p hp)).contDiffWithinAt

lemma contDiffOn_dE {W : ℝ × ℝ → ℂ} (hW : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W)
    {U : Set (ℝ × ℝ)} (hU : ∀ p ∈ U, W p ≠ 0) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (dE W) U :=
  fun p hp => (contDiffAt_dE hW (hU p hp)).contDiffWithinAt

/-- The norm of the descended disk coordinate. -/
lemma norm_dD_sq {M W : ℝ × ℝ → ℂ} {p : ℝ × ℝ} (h : 0 < dA M W p) :
    ‖dD M W p‖ ^ 2 = ‖M p‖ ^ 2 / dA M W p := by
  have hRpos : 0 < dR M W p := Real.sqrt_pos.mpr h
  rw [dD, dR, norm_div, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), div_pow,
    Real.sq_sqrt h.le]

/-- **The disk coordinate is inside the unit disk on the configuration side** (`τ ≥ 0`). -/
lemma norm_dD_le_one {M W : ℝ × ℝ → ℂ} {p : ℝ × ℝ} (h : 0 < dA M W p) (hτ : 0 ≤ p.2) :
    ‖dD M W p‖ ≤ 1 := by
  have hle : ‖M p‖ ^ 2 ≤ dA M W p := by
    simp only [dA]
    nlinarith [sq_nonneg ‖M p‖, sq_nonneg ‖W p‖, hτ]
  have h1 : ‖dD M W p‖ ^ 2 ≤ 1 := by
    rw [norm_dD_sq h, div_le_one h]
    exact hle
  rw [← Real.sqrt_sq (norm_nonneg (dD M W p))]
  exact Real.sqrt_le_one.mpr h1

/-- **The disk coordinate is outside the unit disk on the cap side** (`τ < 0`). -/
lemma norm_dD_ge_one {M W : ℝ × ℝ → ℂ} {p : ℝ × ℝ} (h : 0 < dA M W p) (hτ : p.2 < 0) :
    1 ≤ ‖dD M W p‖ := by
  have hle : dA M W p ≤ ‖M p‖ ^ 2 := by
    simp only [dA]
    nlinarith [sq_nonneg ‖W p‖, hτ]
  have h1 : (1 : ℝ) ≤ ‖dD M W p‖ ^ 2 := by
    rw [norm_dD_sq h, one_le_div h]
    exact hle
  have h2 := Real.sqrt_le_sqrt h1
  rw [Real.sqrt_sq (norm_nonneg (dD M W p))] at h2
  simpa [Real.sqrt_one] using h2

/-- **The uniform bound on the descended disk coordinate.**  Where the good condition
`12 |τ| ‖W‖² < ‖M‖²` holds (`τ < 0` close to the seam) the squared norm is at most `3/2`. -/
lemma norm_dD_le_sqrt {M W : ℝ × ℝ → ℂ} {p : ℝ × ℝ} (h : 0 < dA M W p)
    (hτ : 12 * |p.2| * ‖W p‖ ^ 2 < ‖M p‖ ^ 2) :
    ‖dD M W p‖ ≤ Real.sqrt (3 / 2) := by
  have hkey : (3 / 2 : ℝ) * dA M W p
      = (3 / 2) * ‖M p‖ ^ 2 + 6 * p.2 * ‖W p‖ ^ 2 := by
    simp only [dA]; ring
  have h2 : ‖dD M W p‖ ^ 2 ≤ 3 / 2 := by
    rw [norm_dD_sq h, div_le_iff₀ h, hkey]
    by_cases hp : 0 ≤ p.2
    · nlinarith [sq_nonneg ‖M p‖, sq_nonneg ‖W p‖, hp]
    · have hlt : p.2 < 0 := lt_of_not_ge hp
      have hp2 : p.2 = -|p.2| := by
        rw [abs_of_neg hlt]; ring
      nlinarith [hτ, hp2, sq_nonneg ‖M p‖, sq_nonneg ‖W p‖]
  have := Real.sqrt_le_sqrt h2
  rwa [Real.sqrt_sq (norm_nonneg (dD M W p))] at this

/-- A unit complex number raised to the square (the descended chord direction) is unit. -/
lemma norm_dE {W : ℝ × ℝ → ℂ} {p : ℝ × ℝ} (h : W p ≠ 0) : ‖dE W p‖ = 1 := by
  rw [dE, norm_pow, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg _), div_self (norm_ne_zero_iff.mpr h), one_pow]

end

/-! ## The plane cross -/

open Manifold in
open scoped Manifold ContDiff in
theorem exists_contMDiff_planeCross (γ : Circle → ℝ × ℝ)
    (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    (hγne : ∀ x : Circle, γ x ≠ 0) (σ₀ : ℝ) :
    ∃ (ε : ℝ) (F : EuclideanSpace ℝ (Fin 2) → CappingSpace), 0 < ε ∧
      (letI := cappingCharted
       ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) F) ∧
      (∀ q : EuclideanSpace ℝ (Fin 2), |q 0 - σ₀| < ε → 0 < q 1 → q 1 < ε →
        F q = stripChart γ hγne 0 (mk2 (q 0 + Real.sqrt (q 1)) (q 0 - Real.sqrt (q 1)))) ∧
      (∀ q : EuclideanSpace ℝ (Fin 2), |q 0 - σ₀| < ε → -ε < q 1 → q 1 < 0 →
        ∃ c : CapPiece, F q = Quotient.mk'' (Sum.inr c)) := by
  letI := cappingCharted
  -- ## 1. The even descent of the symmetric chord data
  obtain ⟨M, hMcd, hMval⟩ := seeleyDescent_ext
    (contDiff_symmC.comp (contDiff_symmMid hγ))
    (fun x t => by
      show symmC (symmMid γ x (-t)) = symmC (symmMid γ x t)
      rw [symmMid_neg])
  obtain ⟨W, hWcd, hWval⟩ := seeleyDescent_ext (contDiff_symmWC hγ)
    (fun x t => symmWC_neg hγ x t)
  -- ## 2. The value of the data at the seam point
  have hmid00 : symmMid γ σ₀ 0 = γ (Circle.exp σ₀) := by
    simp only [symmMid, curve, add_zero, sub_zero]
    exact add_self_div_two_prod _
  have hM0 : M (σ₀, 0) ≠ 0 := by
    rw [hMval σ₀ 0 le_rfl, Real.sqrt_zero]
    show symmC (symmMid γ σ₀ 0) ≠ 0
    rw [hmid00]
    intro h
    exact hγne _ (symmC_eq_zero_iff.mp h)
  have hW0 : W (σ₀, 0) ≠ 0 := by
    rw [hWval σ₀ 0 le_rfl, Real.sqrt_zero, symmWC_zero hγ σ₀]
    intro h
    exact curve_deriv_ne_zero γ hγ σ₀ (symmC_eq_zero_iff.mp h)
  -- ## 3. The anchor halving
  set u₀ : ℂ := W (σ₀, 0) / (((‖W (σ₀, 0)‖ : ℝ)) : ℂ) with hu₀def
  have hu₀ : ‖u₀‖ = 1 := by
    rw [hu₀def, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
      div_self (norm_ne_zero_iff.mpr hW0)]
  have hu₀sq : u₀ ^ 2 = dE W (σ₀, 0) := by
    rw [hu₀def]; rfl
  have hu₀ne : u₀ ^ 2 ≠ 0 := by
    intro h
    have h2 : ‖u₀ ^ 2‖ = 0 := by rw [h, norm_zero]
    rw [norm_pow, hu₀] at h2
    norm_num at h2
  -- ## 4. The side conditions, with the uniformity radii
  have hEv1 : ∀ᶠ p in nhds (σ₀, 0), 0 < dA M W p := by
    have hcont : ContinuousAt (dA M W) (σ₀, 0) := (contDiffAt_dA hMcd hWcd _).continuousAt
    have hval : 0 < dA M W (σ₀, 0) := by
      have h : dA M W (σ₀, 0) = ‖M (σ₀, 0)‖ ^ 2 := by simp [dA]
      rw [h]
      exact sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hM0)
    exact hcont.preimage_mem_nhds ((isOpen_lt continuous_const continuous_id).mem_nhds hval)
  have hEv2 : ∀ᶠ p in nhds (σ₀, 0), W p ≠ 0 :=
    hWcd.continuous.continuousAt.preimage_mem_nhds (isOpen_ne.mem_nhds hW0)
  have hEv3 : ∀ᶠ p in nhds (σ₀, 0), ‖dE W p - dE W (σ₀, 0)‖ < 1 / 8 := by
    have hcont : ContinuousAt (fun p : ℝ × ℝ => ‖dE W p - dE W (σ₀, 0)‖) (σ₀, 0) :=
      ((contDiffAt_dE hWcd hW0).continuousAt.sub continuousAt_const).norm
    have hval : ‖dE W (σ₀, 0) - dE W (σ₀, 0)‖ < 1 / 8 := by
      rw [sub_self, norm_zero]; norm_num
    exact hcont.preimage_mem_nhds ((isOpen_lt continuous_id continuous_const).mem_nhds hval)
  have hEv4 : ∀ᶠ p in nhds (σ₀, 0), 12 * |p.2| * ‖W p‖ ^ 2 < ‖M p‖ ^ 2 := by
    have hcont : ContinuousAt
        (fun p : ℝ × ℝ => 12 * |p.2| * ‖W p‖ ^ 2 - ‖M p‖ ^ 2) (σ₀, 0) :=
      (((continuous_const.mul (continuous_abs.comp continuous_snd)).mul
        (hWcd.continuous.norm.pow 2)).sub (hMcd.continuous.norm.pow 2)).continuousAt
    have hval : 12 * |(0 : ℝ)| * ‖W (σ₀, 0)‖ ^ 2 - ‖M (σ₀, 0)‖ ^ 2 < 0 := by
      simp only [abs_zero, mul_zero, zero_mul, zero_sub, neg_lt_zero]
      exact sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hM0)
    filter_upwards [hcont.preimage_mem_nhds
      ((isOpen_lt continuous_id continuous_const).mem_nhds hval)] with p hp
    have hp' : 12 * |p.2| * ‖W p‖ ^ 2 - ‖M p‖ ^ 2 < 0 := hp
    linarith
  have hEv : ∀ᶠ p in nhds (σ₀, 0),
      0 < dA M W p ∧ W p ≠ 0 ∧ ‖dE W p - dE W (σ₀, 0)‖ < 1 / 8 ∧
        12 * |p.2| * ‖W p‖ ^ 2 < ‖M p‖ ^ 2 := by
    filter_upwards [hEv1, hEv2, hEv3, hEv4] with p h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  obtain ⟨δ, hδpos, hδ⟩ := Metric.eventually_nhds_iff.mp hEv
  -- ## 5. The bump and the interpolated data
  let bump : ContDiffBump ((σ₀, 0) : ℝ × ℝ) := ⟨δ / 8, δ / 4, by linarith, by linarith⟩
  have hbump_rIn : bump.rIn = δ / 8 := rfl
  have hbump_rOut : bump.rOut = δ / 4 := rfl
  have hbump_cd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (bump : ℝ × ℝ → ℝ) :=
    ContDiffBump.contDiff bump
  have hbump_tsupp : tsupport (bump : ℝ × ℝ → ℝ) ⊆ Metric.ball (σ₀, 0) δ := by
    intro p hp
    have h1 : p ∈ closure (Metric.ball (σ₀, 0) bump.rOut) := by
      rw [← ContDiffBump.support_eq bump]
      exact hp
    rw [hbump_rOut, closure_ball _ (by linarith : δ / 4 ≠ 0)] at h1
    rw [Metric.mem_closedBall] at h1
    rw [Metric.mem_ball]
    linarith
  set χ : ℝ × ℝ → ℝ := (bump : ℝ × ℝ → ℝ) with hχdef
  have hχcd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ := by
    rw [hχdef]; exact hbump_cd
  have hχ_nonneg : ∀ p, 0 ≤ χ p := fun p => by rw [hχdef]; exact ContDiffBump.nonneg bump
  have hχ_le_one : ∀ p, χ p ≤ 1 := fun p => by rw [hχdef]; exact ContDiffBump.le_one bump
  have hχ_one_near : ∀ p, dist p (σ₀, 0) ≤ δ / 8 → χ p = 1 := by
    intro p hp
    rw [hχdef]
    refine ContDiffBump.one_of_mem_closedBall bump ?_
    rw [Metric.mem_closedBall, hbump_rIn]
    exact hp
  have hχ_ball : tsupport χ ⊆ Metric.ball (σ₀, 0) δ := by
    rw [hχdef]; exact hbump_tsupp
  have hUball : ∀ p ∈ Metric.ball (σ₀, 0) δ, 0 < dA M W p :=
    fun p hp => (hδ (Metric.mem_ball.mp hp)).1
  have hUballW : ∀ p ∈ Metric.ball (σ₀, 0) δ, W p ≠ 0 :=
    fun p hp => (hδ (Metric.mem_ball.mp hp)).2.1
  have hUballE : ∀ p ∈ Metric.ball (σ₀, 0) δ, ‖dE W p - dE W (σ₀, 0)‖ < 1 / 8 :=
    fun p hp => (hδ (Metric.mem_ball.mp hp)).2.2.1
  have hUballM : ∀ p ∈ Metric.ball (σ₀, 0) δ, 12 * |p.2| * ‖W p‖ ^ 2 < ‖M p‖ ^ 2 :=
    fun p hp => (hδ (Metric.mem_ball.mp hp)).2.2.2
  have hχ_tsupp_ball : ∀ p ∈ tsupport χ, dist p (σ₀, 0) < δ := fun p hp =>
    Metric.mem_ball.mp (hχ_ball hp)
  -- the global data
  let rb : ℝ × ℝ → ℝ := fun p => χ p • dR M W p + (1 - χ p) * 1
  let db : ℝ × ℝ → ℂ := fun p => χ p • dD M W p
  let zb : ℝ × ℝ → ℂ := fun p => χ p • dE W p + (1 - χ p) • u₀ ^ 2
  have hrb_cd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) rb := by
    have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => χ p • dR M W p) :=
      contDiff_smul_of_contDiffOn_of_tsupport_subset Metric.isOpen_ball
        (contDiffOn_dR hMcd hWcd hUball) hχcd hχ_ball
    have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => (1 - χ p) * 1) :=
      (contDiff_const.sub hχcd).mul contDiff_const
    exact h1.add h2
  have hdb_cd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) db :=
    contDiff_smul_of_contDiffOn_of_tsupport_subset Metric.isOpen_ball
      (contDiffOn_dD hMcd hWcd hUball) hχcd hχ_ball
  have hzb_cd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) zb := by
    have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => χ p • dE W p) :=
      contDiff_smul_of_contDiffOn_of_tsupport_subset Metric.isOpen_ball
        (contDiffOn_dE hWcd hUballW) hχcd hχ_ball
    have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => (1 - χ p) • u₀ ^ 2) :=
      (contDiff_const.sub hχcd).smul contDiff_const
    exact h1.add h2
  -- ## 6. The side conditions of the global data
  have hrb_pos : ∀ p, 0 < rb p := by
    intro p
    by_cases hp : χ p = 0
    · show 0 < χ p • dR M W p + (1 - χ p) * 1
      rw [hp]; norm_num
    · have hmem : p ∈ tsupport χ := subset_closure (Function.mem_support.mpr hp)
      have hA := hUball p (hχ_ball hmem)
      have hR : 0 < dR M W p := Real.sqrt_pos.mpr hA
      have h0 := hχ_nonneg p
      have h1 := hχ_le_one p
      show 0 < χ p • dR M W p + (1 - χ p) * 1
      rw [smul_eq_mul]
      rcases eq_or_lt_of_le h0 with h0' | h0'
      · rw [← h0', zero_mul]; norm_num
      · nlinarith [mul_pos h0' hR]
  have hzb_near : ∀ p, ‖zb p - u₀ ^ 2‖ ≤ 1 / 8 := by
    intro p
    by_cases hp : χ p = 0
    · show ‖χ p • dE W p + (1 - χ p) • u₀ ^ 2 - u₀ ^ 2‖ ≤ 1 / 8
      rw [hp]; norm_num
    · have hmem : p ∈ tsupport χ := subset_closure (Function.mem_support.mpr hp)
      have hgood := hUballE p (hχ_ball hmem)
      have hgood' : ‖dE W p - u₀ ^ 2‖ < 1 / 8 := by rwa [hu₀sq]
      have h0 := hχ_nonneg p
      have h1 := hχ_le_one p
      have hkey : zb p - u₀ ^ 2 = χ p • (dE W p - u₀ ^ 2) := by
        simp only [zb]
        module
      rw [hkey, norm_smul, Real.norm_of_nonneg h0]
      calc χ p * ‖dE W p - u₀ ^ 2‖ ≤ 1 * (1 / 8) :=
            mul_le_mul h1 hgood'.le (norm_nonneg _) (by norm_num)
        _ = 1 / 8 := by norm_num
  have hZ_near : ∀ p, ‖zb p / u₀ ^ 2 - 1‖ ≤ 1 / 8 := by
    intro p
    have h1 := hzb_near p
    have h2 : ‖u₀ ^ 2‖ = 1 := by rw [norm_pow, hu₀]; norm_num
    have hkey : (zb p - u₀ ^ 2) / u₀ ^ 2 = zb p / u₀ ^ 2 - 1 := by
      rw [sub_div, div_self hu₀ne]
    rw [← hkey, norm_div, h2, div_one]
    exact h1
  have hone : ∀ p, 1 + zb p / u₀ ^ 2 ≠ 0 := by
    intro p h
    have hZ := hZ_near p
    have h2 : zb p / u₀ ^ 2 = -1 := ((neg_eq_iff_add_eq_zero).mpr h).symm
    rw [h2] at hZ
    norm_num at hZ
  have hnorm_one : ∀ p, 1 / 2 ≤ ‖1 + zb p / u₀ ^ 2‖ := by
    intro p
    have hZ := hZ_near p
    have hsplit : (2 : ℂ) = (1 + zb p / u₀ ^ 2) + (1 - zb p / u₀ ^ 2) := by ring
    have h3 : ‖(1 : ℂ) - zb p / u₀ ^ 2‖ ≤ 1 / 8 := by
      rw [← neg_sub, norm_neg]
      exact hZ
    have h4 : (2 : ℝ) ≤ ‖1 + zb p / u₀ ^ 2‖ + ‖(1 : ℂ) - zb p / u₀ ^ 2‖ := by
      calc (2 : ℝ) = ‖(2 : ℂ)‖ := by norm_num
        _ = ‖(1 + zb p / u₀ ^ 2) + (1 - zb p / u₀ ^ 2)‖ := by rw [hsplit]
        _ ≤ _ := norm_add_le _ _
    linarith
  -- ## 7. The unit halving
  let ub : ℝ × ℝ → ℂ :=
    fun p => u₀ * (1 + zb p / u₀ ^ 2) * (((‖1 + zb p / u₀ ^ 2‖ : ℝ)) : ℂ)⁻¹
  have hub_cd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ub := by
    have hZcd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × ℝ => 1 + zb p / u₀ ^ 2) :=
      contDiff_const.add (hzb_cd.div_const _)
    have hnorm := ContDiff.norm ℝ hZcd hone
    have hnorm' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × ℝ => (((‖1 + zb p / u₀ ^ 2‖ : ℝ)) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp hnorm
    have hinv : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × ℝ => (((‖1 + zb p / u₀ ^ 2‖ : ℝ)) : ℂ)⁻¹) :=
      hnorm'.inv (fun p => by
        rw [Complex.ofReal_ne_zero]
        intro h
        have := hnorm_one p
        rw [h] at this
        norm_num at this)
    exact (contDiff_const.mul hZcd).mul hinv
  have hub_unit : ∀ p, ‖ub p‖ = 1 := by
    intro p
    have hne : ‖1 + zb p / u₀ ^ 2‖ ≠ 0 := by
      intro h
      have := hnorm_one p
      rw [h] at this
      norm_num at this
    show ‖u₀ * (1 + zb p / u₀ ^ 2) * (((‖1 + zb p / u₀ ^ 2‖ : ℝ)) : ℂ)⁻¹‖ = 1
    calc ‖u₀ * (1 + zb p / u₀ ^ 2) * (((‖1 + zb p / u₀ ^ 2‖ : ℝ)) : ℂ)⁻¹‖
          = ‖u₀‖ * ‖1 + zb p / u₀ ^ 2‖ * ‖(((‖1 + zb p / u₀ ^ 2‖ : ℝ)) : ℂ)⁻¹‖ := by
          rw [norm_mul, norm_mul]
      _ = 1 * ‖1 + zb p / u₀ ^ 2‖ * (‖1 + zb p / u₀ ^ 2‖)⁻¹ := by
          rw [hu₀, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      _ = 1 := by rw [one_mul, mul_inv_cancel₀ hne]
  -- ## 8. The plane map
  let r : EuclideanSpace ℝ (Fin 2) → ℝ := fun q => rb (q 0, q 1)
  let d : EuclideanSpace ℝ (Fin 2) → ℂ := fun q => db (q 0, q 1)
  let u : EuclideanSpace ℝ (Fin 2) → ℂ := fun q => ub (q 0, q 1)
  have hr : ∀ q, 0 < r q := fun q => hrb_pos _
  have hu : ∀ q, ‖u q‖ = 1 := fun q => hub_unit _
  have hd_bound : ∀ q, ‖d q‖ ≤ Real.sqrt (3 / 2) := by
    intro q
    by_cases hχ : χ (q 0, q 1) = 0
    · show ‖χ (q 0, q 1) • dD M W (q 0, q 1)‖ ≤ Real.sqrt (3 / 2)
      rw [hχ, zero_smul, norm_zero]
      exact Real.sqrt_nonneg _
    · have hmem : (q 0, q 1) ∈ tsupport χ := subset_closure (Function.mem_support.mpr hχ)
      have hgood := hδ (hχ_tsupp_ball _ hmem)
      have hD := norm_dD_le_sqrt hgood.1 hgood.2.2.2
      show ‖χ (q 0, q 1) • dD M W (q 0, q 1)‖ ≤ Real.sqrt (3 / 2)
      rw [norm_smul, Real.norm_of_nonneg (hχ_nonneg _)]
      calc χ (q 0, q 1) * ‖dD M W (q 0, q 1)‖ ≤ 1 * Real.sqrt (3 / 2) :=
            mul_le_mul (hχ_le_one _) hD (norm_nonneg _) (by norm_num)
        _ = Real.sqrt (3 / 2) := one_mul _
  have hne : ∀ q, 1 - ‖d q‖ ^ 2 / 2 ≠ 0 := by
    intro q h
    have h1 : ‖d q‖ ≤ Real.sqrt (3 / 2) := hd_bound q
    have h2 : ‖d q‖ ^ 2 ≤ 3 / 2 := by
      have h3 := mul_self_le_mul_self (norm_nonneg (d q)) h1
      have h4 : Real.sqrt (3 / 2) * Real.sqrt (3 / 2) = 3 / 2 := by
        rw [← sq, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3 / 2)]
      calc ‖d q‖ ^ 2 = ‖d q‖ * ‖d q‖ := by ring
        _ ≤ Real.sqrt (3 / 2) * Real.sqrt (3 / 2) := h3
        _ = 3 / 2 := h4
    linarith
  let hv : ∀ q, confProjVecOf (u q) (d q) ≠ 0 :=
    fun q => confProjVecOf_ne_zero_of_norm_eq_one (hu q) (d q)
  let F : EuclideanSpace ℝ (Fin 2) → CappingSpace :=
    fun q => planePt (u q) (r q) (hr q) (d q) (hu q) (hv q)
  have hpair : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin 2) => (q 0, q 1)) := by fun_prop
  have hF_cd : ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) F := by
    intro q
    exact contMDiffAt_planePt r u d q hr hu (hne q) hv
      (contMDiffAt_iff_contDiffAt.mpr (hrb_cd.comp hpair).contDiffAt)
      (contMDiffAt_iff_contDiffAt.mpr (hub_cd.comp hpair).contDiffAt)
      (contMDiffAt_iff_contDiffAt.mpr (hdb_cd.comp hpair).contDiffAt)
  -- ## 9. The plane cross
  refine ⟨min (δ / 8) (1 / 2), F, lt_min (by linarith) (by norm_num), hF_cd, ?_, ?_⟩
  · -- ### the configuration side
    intro q hq0 hq1pos hq1lt
    set s : ℝ := Real.sqrt (q 1) with hs
    have hspos : 0 < s := by rw [hs]; exact Real.sqrt_pos.mpr hq1pos
    have hs2 : s ^ 2 = q 1 := by rw [hs]; exact Real.sq_sqrt hq1pos.le
    have hδ8pos : 0 < δ / 8 := by linarith
    have hq0abs : |q 0 - σ₀| < δ / 8 := lt_of_lt_of_le hq0 (min_le_left _ _)
    have hq1abs : |q 1| < δ / 8 := by
      rw [abs_of_pos hq1pos]
      exact lt_of_lt_of_le hq1lt (min_le_left _ _)
    have hdist8 : dist (q 0, q 1) (σ₀, 0) ≤ δ / 8 := by
      rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, sub_zero]
      exact max_le hq0abs.le hq1abs.le
    have hdistδ : dist (q 0, q 1) (σ₀, 0) < δ := by linarith
    have hχq : χ (q 0, q 1) = 1 := hχ_one_near _ hdist8
    have hgood := hδ hdistδ
    have hspi : s < Real.pi / 2 := by
      rw [hs, Real.sqrt_lt' (by positivity : (0 : ℝ) < Real.pi / 2)]
      have h1 : q 1 < 1 / 2 := lt_of_lt_of_le hq1lt (min_le_right _ _)
      nlinarith [Real.pi_gt_three]
    have hspi' : |s| < Real.pi / 2 := by rw [abs_of_pos hspos]; exact hspi
    have hsπ : s < Real.pi := by linarith [hspi, Real.pi_pos]
    -- the descended data at the point
    have hMv : M (q 0, q 1) = symmC (symmMid γ (q 0) s) := by
      have h := hMval (q 0) (q 1) hq1pos.le
      rw [← hs] at h
      exact h
    have hWv : W (q 0, q 1) = symmWC γ (q 0) s := by
      have h := hWval (q 0) (q 1) hq1pos.le
      rw [← hs] at h
      exact h
    have hAeq : dA M W (q 0, q 1) = symmA γ (q 0) s := by
      have h1 : ‖M (q 0, q 1)‖ ^ 2 = ‖symmC (symmMid γ (q 0) s)‖ ^ 2 := by rw [hMv]
      have h2 : ‖W (q 0, q 1)‖ ^ 2 = ‖symmWC γ (q 0) s‖ ^ 2 := by rw [hWv]
      simp only [dA]
      rw [h1, h2, ← hs2, ← (symmData_norm_identities' hγ (q 0) s).1]
    have hReq : dR M W (q 0, q 1) = symmR γ (q 0) s := by
      simp only [dR, symmR]
      rw [hAeq]
    have hDeq : dD M W (q 0, q 1) = symmD γ (q 0) s := by
      simp only [dD, symmD]
      rw [hMv, hReq, symmC_symmMid_eq]
    have hEeq : dE W (q 0, q 1) = symmE γ (q 0) s := by
      simp only [dE]
      rw [hWv, ← (symmData_norm_identities' hγ (q 0) s).2.2]
    -- the radius, the disk coordinate and the halving
    have hrq : r q = (stripData γ (mk2 (q 0 + s) (q 0 - s))).1 := by
      show χ (q 0, q 1) • dR M W (q 0, q 1) + (1 - χ (q 0, q 1)) * 1 = _
      rw [hχq, one_smul, sub_self, zero_mul, add_zero, hReq, symmR_eq_stripR, stripData_fst]
    have hdq : d q = (stripData γ (mk2 (q 0 + s) (q 0 - s))).2.1 := by
      show χ (q 0, q 1) • dD M W (q 0, q 1) = _
      rw [hχq, one_smul, hDeq, symmD_eq_stripD, stripData_snd]
    have hzq : zb (q 0, q 1) = dE W (q 0, q 1) := by
      show χ (q 0, q 1) • dE W (q 0, q 1) + (1 - χ (q 0, q 1)) • u₀ ^ 2 = _
      rw [hχq, one_smul, sub_self, zero_smul, add_zero]
    have hz1 : ‖zb (q 0, q 1)‖ = 1 := by
      rw [hzq, hEeq]
      exact symmE_norm γ (q 0) s (symmWC_ne_zero_of_lt hγ hspi')
    have hZ1 : ‖zb (q 0, q 1) / u₀ ^ 2‖ = 1 := by
      rw [norm_div, hz1, norm_pow, hu₀]
      norm_num
    have hsq2 : u q ^ 2 = zb (q 0, q 1) := by
      have hsq := (unit_mul_sq_div u₀ (zb (q 0, q 1) / u₀ ^ 2) hu₀ hZ1 (hone _)).1
      show ub (q 0, q 1) ^ 2 = zb (q 0, q 1)
      rw [show ub (q 0, q 1)
          = u₀ * (1 + zb (q 0, q 1) / u₀ ^ 2)
              * (((‖1 + zb (q 0, q 1) / u₀ ^ 2‖ : ℝ)) : ℂ)⁻¹ from rfl, hsq]
      calc u₀ ^ 2 * (zb (q 0, q 1) / u₀ ^ 2)
          = u₀ ^ 2 * (u₀ ^ 2)⁻¹ * zb (q 0, q 1) := by rw [div_eq_mul_inv]; ring
        _ = zb (q 0, q 1) := by rw [mul_inv_cancel₀ hu₀ne, one_mul]
    -- the value
    have hd_le : ‖d q‖ ≤ 1 := by
      show ‖χ (q 0, q 1) • dD M W (q 0, q 1)‖ ≤ 1
      rw [hχq, one_smul]
      exact norm_dD_le_one hgood.1 hq1pos.le
    have hL : F q = Quotient.mk'' (Sum.inl (⟨(r q, d q, circOf (u q ^ 2)
        (by rw [norm_pow, hu q]; norm_num)), hr q, hd_le⟩ : ConfigPiece)) := by
      show planePt (u q) (r q) (hr q) (d q) (hu q) (hv q) = _
      rw [← planePt_congr_hv (hr q) (hu q) (hv q) (confProjVecOf_ne_zero (hu q) hd_le)]
      exact planePt_eq_confPiece (hr q) hd_le (hu q)
    have hR : stripChart γ hγne 0 (mk2 (q 0 + s) (q 0 - s))
        = Quotient.mk'' (Sum.inl (⟨((stripData γ (mk2 (q 0 + s) (q 0 - s))).1,
            (stripData γ (mk2 (q 0 + s) (q 0 - s))).2.1,
            (stripData γ (mk2 (q 0 + s) (q 0 - s))).2.2 + 0),
            stripData_pos hγne _, confOf_snd_norm_le_one _⟩ : ConfigPiece)) :=
      stripChart_eq_mk γ hγne 0 _
    have hne' : Circle.exp ((mk2 (q 0 + s) (q 0 - s)) 0)
        ≠ Circle.exp ((mk2 (q 0 + s) (q 0 - s)) 1) := by
      simp only [mk2_apply_zero, mk2_apply_one]
      exact circle_exp_add_ne_sub hspos hsπ
    have hpair_eq : ((mk2 (q 0 + s) (q 0 - s)) 0, (mk2 (q 0 + s) (q 0 - s)) 1)
        = (q 0 + s, q 0 - s) :=
      Prod.ext (mk2_apply_zero (q 0 + s) (q 0 - s)) (mk2_apply_one (q 0 + s) (q 0 - s))
    have hchain : u q ^ 2 = (stripHalf γ (mk2 (q 0 + s) (q 0 - s))) ^ 2 := by
      rw [hsq2, hzq, hEeq,
        symmE_eq_chordUnitDir_sq hγ (q 0) s (ne_of_gt hspos) (symmWC_ne_zero_of_lt hγ hspi')]
      have h1 : stripHalf γ (mk2 (q 0 + s) (q 0 - s))
          = chordUnitDir γ (q 0 + s, q 0 - s) :=
        (stripHalf_of_ne (γ := γ) hne').trans (congrArg (chordUnitDir γ) hpair_eq)
      rw [h1]
    rw [hL, hR, mk_inl_inj]
    refine Subtype.ext (Prod.ext ?_ (Prod.ext ?_ ?_))
    · show r q = (stripData γ (mk2 (q 0 + s) (q 0 - s))).1
      exact hrq
    · show d q = (stripData γ (mk2 (q 0 + s) (q 0 - s))).2.1
      exact hdq
    · rw [add_zero, ← circOf_stripHalf_sq hγ (mk2 (q 0 + s) (q 0 - s))]
      exact circOf_congr (by rw [norm_pow, hu q]; norm_num)
        (by rw [norm_pow, stripHalf_norm hγ (mk2 (q 0 + s) (q 0 - s))]; norm_num) hchain
  · -- ### the cap side
    intro q hq0 hqneg hq1lt
    have hδ8pos : 0 < δ / 8 := by linarith
    have hq0abs : |q 0 - σ₀| < δ / 8 := lt_of_lt_of_le hq0 (min_le_left _ _)
    have hq1lt0 : q 1 < 0 := hq1lt
    have hq1abs : |q 1| < δ / 8 := by
      rw [abs_of_neg hq1lt0]
      exact lt_of_lt_of_le (by linarith : -q 1 < min (δ / 8) (1 / 2)) (min_le_left _ _)
    have hdist8 : dist (q 0, q 1) (σ₀, 0) ≤ δ / 8 := by
      rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, sub_zero]
      exact max_le hq0abs.le hq1abs.le
    have hdistδ : dist (q 0, q 1) (σ₀, 0) < δ := by linarith
    have hχq : χ (q 0, q 1) = 1 := hχ_one_near _ hdist8
    have hgood := hδ hdistδ
    have hd_eq : d q = dD M W (q 0, q 1) := by
      show χ (q 0, q 1) • dD M W (q 0, q 1) = _
      rw [hχq, one_smul]
    have hge : 1 ≤ ‖d q‖ := by
      rw [hd_eq]
      exact norm_dD_ge_one hgood.1 hq1lt0
    have hle : ‖d q‖ ≤ Real.sqrt 2 := by
      rw [hd_eq]
      have h := norm_dD_le_sqrt hgood.1 hgood.2.2.2
      have h2 : Real.sqrt (3 / 2) ≤ Real.sqrt 2 := Real.sqrt_le_sqrt (by norm_num)
      linarith
    exact exists_capPiece_planePt' (hr q) (hu q) hge hle (hv q)

end Work.Drive.Neutral
