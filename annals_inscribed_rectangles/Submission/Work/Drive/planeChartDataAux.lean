import Mathlib
import Submission.Work.Drive.Interfaces
import Submission.Work.Drive.Neutral.dataChord_spec
import Submission.Work.Drive.cappingProjCoords
import Submission.Work.Drive.capLift_reflect
import Submission.Work.Drive.capSide_capPiece
import Submission.Work.Drive.planeProfiles
import Submission.Work.Drive.bandData
import Submission.Work.Drive.Neutral.dataR_dataD_spec
import Submission.Work.Drive.Neutral.stripDiskChordNe
import Submission.Work.Drive.directionStabilization

namespace Work.Drive

open scoped ContDiff

noncomputable section

/-!
# The auxiliary data of the plane chart of `Work.Drive.exists_planeChartData`

`Work.Drive.exists_planeChartData` produces a smooth positive radius `r` and a smooth nowhere
vanishing sphere lift `V` out of the band data `(M, W)` and the profiles `x`, `τ`.  The lift is
assembled from two *parametrisations* of the same sphere, glued along the seam circle `‖z‖ = 1/2`:

* the **configuration form** `confProjVecOf u D` (`u` a unit complex number, `D` the disk
  coordinate), which is the honest chord lift on the annulus `1/2 < ‖z‖ ≤ 1`;
* the **cap form** `capProjVecOf w dc` (`‖w‖ = 1`, `‖dc‖ ≤ 1`), which is the form required inside the
  disk `‖z‖ < 1/2`.

The change of coordinates between the two is the *reflection*

> `D ↦ dc = √2 · (D/‖D‖) · √(1 - ‖D‖²/2)`,  `u ↦ w = u · conj D/‖D‖`,

with `‖dc‖ = √(2 - ‖D‖²)`: `capProjVecOf w dc = confProjVecOf u D` (this is
`Work.Drive.capLift_reflect`), the cap coordinate `dc` being in the unit disk exactly when
`1 ≤ ‖D‖ ≤ √2` — which is the region where the band inequality `4|τ|‖W‖² < ‖M‖²` holds.

This file only fixes the *notation* (the total functions `pcA`, `pcU`, `pcD`, `pcW`, `pcDc` of the
band data, and the radial cut-off `pcCut`), so that the several lemmas that the assembly needs can
be stated uniformly.  All of them are junk where the band data degenerate; every statement about
them carries the region on which the data are honest.
-/

/-- The band quantity `A = ‖M (x z, τ z)‖² + τ z * ‖W (x z, τ z)‖²`, written with
`Complex.normSq` so that it is a smooth function of `z` wherever the data are. -/
def pcA (M W : ℂ × ℝ → ℂ) (x : ℂ → ℂ) (τ : ℂ → ℝ) (z : ℂ) : ℝ :=
  Complex.normSq (M (x z, τ z)) + τ z * Complex.normSq (W (x z, τ z))

/-- The unit direction `u = W/‖W‖` of the halving datum. -/
def pcU (W : ℂ × ℝ → ℂ) (x : ℂ → ℂ) (τ : ℂ → ℝ) (z : ℂ) : ℂ :=
  W (x z, τ z) / ((Real.sqrt (Complex.normSq (W (x z, τ z))) : ℝ) : ℂ)

/-- The disk coordinate `D = M/√A` of the chord. -/
def pcD (M W : ℂ × ℝ → ℂ) (x : ℂ → ℂ) (τ : ℂ → ℝ) (z : ℂ) : ℂ :=
  M (x z, τ z) / ((Real.sqrt (pcA M W x τ z) : ℝ) : ℂ)

/-- The reflected cap direction `w = u · conj D/‖D‖` (a unit complex number where `D ≠ 0`). -/
def pcW (M W : ℂ × ℝ → ℂ) (x : ℂ → ℂ) (τ : ℂ → ℝ) (z : ℂ) : ℂ :=
  pcU W x τ z * star (pcD M W x τ z) / ((Real.sqrt (Complex.normSq (pcD M W x τ z)) : ℝ) : ℂ)

/-- The reflected cap disk coordinate `dc = √2 · (D/‖D‖) · √(1 - ‖D‖²/2)`, of norm `√(2 - ‖D‖²)`. -/
def pcDc (M W : ℂ × ℝ → ℂ) (x : ℂ → ℂ) (τ : ℂ → ℝ) (z : ℂ) : ℂ :=
  ((Real.sqrt 2 : ℝ) : ℂ) * (pcD M W x τ z / ((Real.sqrt (Complex.normSq (pcD M W x τ z)) : ℝ) : ℂ))
    * ((Real.sqrt (1 - Complex.normSq (pcD M W x τ z) / 2) : ℝ) : ℂ)

/-- The smooth radial cut-off `0` on `{‖z‖² ≤ a}` and `1` on `{b ≤ ‖z‖²}` (assumed `a < b`).
Written through `Complex.normSq` so that it is smooth on *all* of `ℂ` without any hypothesis. -/
def pcCut (a b : ℝ) (z : ℂ) : ℝ := Real.smoothTransition ((Complex.normSq z - a) / (b - a))

@[simp] lemma pcCut_apply (a b : ℝ) (z : ℂ) :
    pcCut a b z = Real.smoothTransition ((Complex.normSq z - a) / (b - a)) := rfl

lemma contDiff_pcCut (a b : ℝ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (pcCut a b) :=
  Real.smoothTransition.contDiff.comp
    ((Neutral.contDiff_complexNormSq.sub contDiff_const).div_const _)

lemma pcCut_eq_zero {a b : ℝ} (hab : a < b) {z : ℂ} (h : Complex.normSq z ≤ a) :
    pcCut a b z = 0 :=
  Real.smoothTransition.zero_of_nonpos
    (div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith))

lemma pcCut_eq_one {a b : ℝ} (hab : a < b) {z : ℂ} (h : b ≤ Complex.normSq z) :
    pcCut a b z = 1 :=
  Real.smoothTransition.one_of_one_le
    (one_le_div (by linarith) |>.mpr (by linarith))

lemma pcCut_nonneg (a b : ℝ) (z : ℂ) : 0 ≤ pcCut a b z := Real.smoothTransition.nonneg _
lemma pcCut_le_one (a b : ℝ) (z : ℂ) : pcCut a b z ≤ 1 := Real.smoothTransition.le_one _

end

section DataLemmas

variable {M W : ℂ × ℝ → ℂ} {x : ℂ → ℂ} {τ : ℂ → ℝ} {c : ℝ}

/-- `√(normSq w) = ‖w‖`. -/
lemma sqrt_normSq (w : ℂ) : Real.sqrt (Complex.normSq w) = ‖w‖ := by
  rw [Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg w)]

lemma pcU_apply (z : ℂ) :
    pcU W x τ z = W (x z, τ z) / ((‖W (x z, τ z)‖ : ℝ) : ℂ) := by
  rw [pcU, sqrt_normSq]

lemma pcD_apply (z : ℂ) :
    pcD M W x τ z = M (x z, τ z) / ((Real.sqrt (pcA M W x τ z) : ℝ) : ℂ) := rfl

lemma pcW_apply (z : ℂ) :
    pcW M W x τ z = pcU W x τ z * star (pcD M W x τ z)
      / ((Real.sqrt (Complex.normSq (pcD M W x τ z)) : ℝ) : ℂ) := rfl

lemma pcDc_apply (z : ℂ) :
    pcDc M W x τ z = ((Real.sqrt 2 : ℝ) : ℂ)
      * (pcD M W x τ z / ((Real.sqrt (Complex.normSq (pcD M W x τ z)) : ℝ) : ℂ))
      * ((Real.sqrt (1 - Complex.normSq (pcD M W x τ z) / 2) : ℝ) : ℂ) := rfl

lemma normSq_pcD {z : ℂ} (hA : 0 ≤ pcA M W x τ z) :
    Complex.normSq (pcD M W x τ z)
      = Complex.normSq (M (x z, τ z)) / pcA M W x τ z := by
  rw [pcD, Complex.normSq_div, Complex.normSq_ofReal, ← sq, Real.sq_sqrt hA]

lemma pcD_mul_sqrt {z : ℂ} (hA : 0 < pcA M W x τ z) :
    pcD M W x τ z * ((Real.sqrt (pcA M W x τ z) : ℝ) : ℂ) = M (x z, τ z) := by
  rw [pcD, div_mul_cancel₀ _
    (Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr hA)))]

/-- On the negative band the quantity `A = ‖M‖² + τ‖W‖²` is positive (strict band inequality). -/
lemma pcA_pos_of_neg
    (hband : ∀ x : ℂ, ∀ τ : ℝ, 1 / 4 ≤ ‖x‖ → ‖x‖ ≤ 2 → -c ≤ τ → τ < 0 →
      4 * |τ| * ‖W (x, τ)‖ ^ 2 < ‖M (x, τ)‖ ^ 2)
    (hWne : ∀ x : ℂ, ∀ τ : ℝ, 1 / 4 ≤ ‖x‖ → ‖x‖ ≤ 2 → -c ≤ τ → τ < 0 → W (x, τ) ≠ 0)
    {z : ℂ} (hx1 : 1 / 4 ≤ ‖x z‖) (hx2 : ‖x z‖ ≤ 2) (hc : -c ≤ τ z) (hτ : τ z < 0) :
    0 < pcA M W x τ z := by
  have hb := hband (x z) (τ z) hx1 hx2 hc hτ
  have h1 : (0 : ℝ) ≤ |τ z| * ‖W (x z, τ z)‖ ^ 2 :=
    mul_nonneg (abs_nonneg _) (sq_nonneg _)
  have h3 : ‖M (x z, τ z)‖ ^ 2 + τ z * ‖W (x z, τ z)‖ ^ 2
      = ‖M (x z, τ z)‖ ^ 2 - |τ z| * ‖W (x z, τ z)‖ ^ 2 := by
    rw [abs_of_neg hτ]; ring
  rw [pcA, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, h3]
  linarith

/-- On the negative band the disk coordinate has norm at least one. -/
lemma one_le_normSq_pcD_of_neg
    (hband : ∀ x : ℂ, ∀ τ : ℝ, 1 / 4 ≤ ‖x‖ → ‖x‖ ≤ 2 → -c ≤ τ → τ < 0 →
      4 * |τ| * ‖W (x, τ)‖ ^ 2 < ‖M (x, τ)‖ ^ 2)
    (hWne : ∀ x : ℂ, ∀ τ : ℝ, 1 / 4 ≤ ‖x‖ → ‖x‖ ≤ 2 → -c ≤ τ → τ < 0 → W (x, τ) ≠ 0)
    {z : ℂ} (hx1 : 1 / 4 ≤ ‖x z‖) (hx2 : ‖x z‖ ≤ 2) (hc : -c ≤ τ z) (hτ : τ z < 0) :
    1 ≤ Complex.normSq (pcD M W x τ z) := by
  have hA := pcA_pos_of_neg (M := M) (W := W) (x := x) (τ := τ) hband hWne hx1 hx2 hc hτ
  rw [normSq_pcD hA.le, le_div_iff₀ hA, one_mul, pcA,
    Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
  have h2 : τ z * ‖W (x z, τ z)‖ ^ 2 ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hτ.le (sq_nonneg _)
  linarith

/-- On the negative band the disk coordinate has norm at most `√2`. -/
lemma normSq_pcD_le_two_of_neg
    (hband : ∀ x : ℂ, ∀ τ : ℝ, 1 / 4 ≤ ‖x‖ → ‖x‖ ≤ 2 → -c ≤ τ → τ < 0 →
      4 * |τ| * ‖W (x, τ)‖ ^ 2 < ‖M (x, τ)‖ ^ 2)
    (hWne : ∀ x : ℂ, ∀ τ : ℝ, 1 / 4 ≤ ‖x‖ → ‖x‖ ≤ 2 → -c ≤ τ → τ < 0 → W (x, τ) ≠ 0)
    {z : ℂ} (hx1 : 1 / 4 ≤ ‖x z‖) (hx2 : ‖x z‖ ≤ 2) (hc : -c ≤ τ z) (hτ : τ z < 0) :
    Complex.normSq (pcD M W x τ z) ≤ 2 := by
  have hb := hband (x z) (τ z) hx1 hx2 hc hτ
  have hA := pcA_pos_of_neg (M := M) (W := W) (x := x) (τ := τ) hband hWne hx1 hx2 hc hτ
  have h1 : (0 : ℝ) ≤ |τ z| * ‖W (x z, τ z)‖ ^ 2 :=
    mul_nonneg (abs_nonneg _) (sq_nonneg _)
  rw [normSq_pcD hA.le, div_le_iff₀ hA, pcA,
    Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
  rw [show τ z * ‖W (x z, τ z)‖ ^ 2 = -(|τ z| * ‖W (x z, τ z)‖ ^ 2) by
    rw [abs_of_neg hτ]; ring]
  nlinarith [hb, h1]

/-- At `τ = 0` the quantity `A` is the squared norm of `M`. -/
lemma pcA_apply_zero {z : ℂ} (hτ : τ z = 0) :
    pcA M W x τ z = Complex.normSq (M (x z, τ z)) := by
  rw [pcA, hτ, zero_mul, add_zero]

lemma pcA_pos_of_zero (hM0 : ∀ x : ℂ, 1 / 4 ≤ ‖x‖ → ‖x‖ ≤ 1 → M (x, 0) ≠ 0)
    {z : ℂ} (hx1 : 1 / 4 ≤ ‖x z‖) (hx2 : ‖x z‖ ≤ 1) (hτ : τ z = 0) :
    0 < pcA M W x τ z := by
  rw [pcA_apply_zero hτ, Complex.normSq_pos, hτ]
  exact hM0 (x z) hx1 hx2

lemma normSq_pcD_of_zero {z : ℂ} (hτ : τ z = 0) (hM : M (x z, τ z) ≠ 0) :
    Complex.normSq (pcD M W x τ z) = 1 := by
  have hA : pcA M W x τ z = Complex.normSq (M (x z, τ z)) := pcA_apply_zero hτ
  rw [pcD, hA, sqrt_normSq, Complex.normSq_div, Complex.normSq_ofReal, ← sq,
    Complex.normSq_eq_norm_sq, div_self (pow_ne_zero 2 (norm_ne_zero_iff.mpr hM))]

/-- On the seam (`τ = 0`) the reflected cap direction is the direction datum of the two data. -/
lemma pcW_eq_dirDatum {z : ℂ} (hτ : τ z = 0) (hM : M (x z, τ z) ≠ 0)
    (hW : W (x z, τ z) ≠ 0) :
    pcW M W x τ z = dirDatum M W (x z, τ z) := by
  have hA : pcA M W x τ z = Complex.normSq (M (x z, τ z)) := pcA_apply_zero hτ
  have hD : pcD M W x τ z = M (x z, τ z) / ((‖M (x z, τ z)‖ : ℝ) : ℂ) := by
    rw [pcD, hA, sqrt_normSq]
  have hnormD : Complex.normSq (pcD M W x τ z) = 1 := normSq_pcD_of_zero hτ hM
  rw [pcW, hnormD, pcU_apply, hD, Real.sqrt_one, Complex.ofReal_one, div_one, dirDatum]

end DataLemmas

section Smoothness

variable {M W : ℂ × ℝ → ℂ} {x : ℂ → ℂ} {τ : ℂ → ℝ}

/-- The complex conjugate is smooth. -/
lemma contDiff_star_complex : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (star : ℂ → ℂ) := by
  rw [Complex.star_def]
  exact (Complex.conjCLE : ℂ →L[ℝ] ℂ).contDiff

lemma contDiffAt_star_comp {a : ℂ → ℂ} {z : ℂ}
    (ha : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) a z) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => star (a z)) z :=
  contDiff_star_complex.contDiffAt.comp z ha

/-- `ofComplex` of two smooth complex functions is smooth (componentwise smoothness). -/
lemma pc_contDiffAt_ofComplex {a b : ℂ → ℂ} {z : ℂ}
    (ha : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) a z)
    (hb : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) b z) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => ofComplex (a z) (b z)) z := by
  rw [contDiffAt_piLp]
  intro i
  fin_cases i <;> simp only [ofComplex, PiLp.toLp_apply]
  · exact (Complex.reCLM.contDiff.contDiffAt).comp z ha
  · exact (Complex.imCLM.contDiff.contDiffAt).comp z ha
  · exact (Complex.reCLM.contDiff.contDiffAt).comp z hb
  · exact (Complex.imCLM.contDiff.contDiffAt).comp z hb

/-- A `Eucl 3`-valued function is smooth at a point as soon as its two complex coordinates are. -/
lemma contDiffAt_of_components {F : ℂ → Eucl 3} {z : ℂ}
    (h1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => c₁ (F z)) z)
    (h2 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => c₂ (F z)) z) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F z := by
  have h : F = fun z => ofComplex (c₁ (F z)) (c₂ (F z)) := by
    funext z; exact (ofComplex_c₁_c₂ (F z)).symm
  rw [h]
  exact pc_contDiffAt_ofComplex h1 h2

lemma contDiffAt_normSq_comp {g : ℂ → ℂ} {z : ℂ}
    (hg : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g z) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => Complex.normSq (g z)) z :=
  Neutral.contDiff_complexNormSq.contDiffAt.comp z hg

lemma contDiffAt_sqrt_comp {φ : ℂ → ℝ} {z : ℂ}
    (hφ : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ z) (h : φ z ≠ 0) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => Real.sqrt (φ z)) z :=
  (Real.contDiffAt_sqrt h).comp z hφ

lemma contDiffAt_ofReal_comp {φ : ℂ → ℝ} {z : ℂ}
    (hφ : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ z) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => ((φ z : ℝ) : ℂ)) z :=
  Complex.ofRealCLM.contDiff.contDiffAt.comp z hφ

/-- A smooth function of the band point `z ↦ (x z, τ z)` is smooth. -/
lemma contDiff_band_apply {g : ℂ × ℝ → ℂ} (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g)
    (hxsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) x)
    (hτsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) τ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℂ => g (x z, τ z)) :=
  hg.comp (hxsm.prodMk hτsm)

lemma contDiffAt_band_apply {g : ℂ × ℝ → ℂ} (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g)
    (hxsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) x)
    (hτsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) τ) (z : ℂ) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℂ => g (x z, τ z)) z :=
  (contDiff_band_apply hg hxsm hτsm).contDiffAt

lemma contDiff_pcA (hMsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) M)
    (hWsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W)
    (hxsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) x)
    (hτsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) τ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (pcA M W x τ) :=
  (Neutral.contDiff_complexNormSq.comp (contDiff_band_apply hMsm hxsm hτsm)).add
    (hτsm.mul (Neutral.contDiff_complexNormSq.comp (contDiff_band_apply hWsm hxsm hτsm)))

lemma contDiffAt_pcA (hMsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) M)
    (hWsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W)
    (hxsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) x)
    (hτsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) τ) (z : ℂ) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (pcA M W x τ) z :=
  (contDiff_pcA hMsm hWsm hxsm hτsm).contDiffAt

/-- The configuration sphere point of two smooth data is smooth where the disk coordinate is not at
the boundary `‖d‖ = √2`. -/
lemma pc_contDiffAt_confProjVecOf {u d : ℂ → ℂ} {z : ℂ}
    (hu : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u z)
    (hd : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) d z)
    (h2 : Complex.normSq (d z) ≠ 2) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => confProjVecOf (u z) (d z)) z := by
  simp only [confProjVecOf]
  refine pc_contDiffAt_ofComplex (hu.mul ?_) ?_
  · refine contDiffAt_ofReal_comp (contDiffAt_sqrt_comp ?_ ?_)
    · simp only [← Complex.normSq_eq_norm_sq]
      exact (contDiffAt_const (c := (1 : ℝ))).sub ((contDiffAt_normSq_comp hd).div_const 2)
    · rw [← Complex.normSq_eq_norm_sq]
      intro h
      exact h2 (by linarith)
  · exact ((contDiffAt_star_comp hu).mul hd).mul
      (contDiffAt_const (c := (((Real.sqrt 2 : ℝ) : ℂ))⁻¹))

/-- The cap sphere point of two smooth data is smooth where the disk coordinate is not at the
boundary `‖d‖ = √2`. -/
lemma pc_contDiffAt_capProjVecOf {w dc : ℂ → ℂ} {z : ℂ}
    (hw : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w z)
    (hdc : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) dc z)
    (h2 : Complex.normSq (dc z) ≠ 2) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => capProjVecOf (w z) (dc z)) z := by
  simp only [capProjVecOf]
  refine pc_contDiffAt_ofComplex ?_ ?_
  · exact (hdc.mul hw).mul (contDiffAt_const (c := (((Real.sqrt 2 : ℝ) : ℂ))⁻¹))
  · refine (contDiffAt_star_comp hw).mul ?_
    refine contDiffAt_ofReal_comp (contDiffAt_sqrt_comp ?_ ?_)
    · simp only [← Complex.normSq_eq_norm_sq]
      exact (contDiffAt_const (c := (1 : ℝ))).sub ((contDiffAt_normSq_comp hdc).div_const 2)
    · rw [← Complex.normSq_eq_norm_sq]
      intro h
      exact h2 (by linarith)

lemma contDiffAt_pcU (hWsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W)
    (hxsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) x)
    (hτsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) τ) {z : ℂ} (hW : W (x z, τ z) ≠ 0) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (pcU W x τ) z := by
  have hN : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℂ => W (x z, τ z)) z :=
    contDiffAt_band_apply hWsm hxsm hτsm z
  change ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
    (fun z : ℂ => W (x z, τ z) / ((Real.sqrt (Complex.normSq (W (x z, τ z))) : ℝ) : ℂ)) z
  refine hN.mul ?_
  refine (contDiffAt_ofReal_comp (contDiffAt_sqrt_comp (contDiffAt_normSq_comp hN) ?_)).inv ?_
  · exact (Complex.normSq_pos.mpr hW).ne'
  · exact Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (Complex.normSq_pos.mpr hW)))

lemma contDiffAt_pcD (hMsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) M)
    (hWsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W)
    (hxsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) x)
    (hτsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) τ) {z : ℂ} (hA : 0 < pcA M W x τ z) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (pcD M W x τ) z := by
  have hN : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℂ => M (x z, τ z)) z :=
    contDiffAt_band_apply hMsm hxsm hτsm z
  change ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
    (fun z : ℂ => M (x z, τ z) / ((Real.sqrt (pcA M W x τ z) : ℝ) : ℂ)) z
  refine hN.mul ?_
  refine (contDiffAt_ofReal_comp
    ((Real.contDiffAt_sqrt (ne_of_gt hA)).comp z (contDiffAt_pcA hMsm hWsm hxsm hτsm z))).inv ?_
  exact Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr hA))

lemma contDiffAt_pcW (hMsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) M)
    (hWsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W)
    (hxsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) x)
    (hτsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) τ) {z : ℂ}
    (hA : 0 < pcA M W x τ z) (hW : W (x z, τ z) ≠ 0) (hD : pcD M W x τ z ≠ 0) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (pcW M W x τ) z := by
  have hDsm : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (pcD M W x τ) z :=
    contDiffAt_pcD hMsm hWsm hxsm hτsm hA
  change ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
    (fun z : ℂ => pcU W x τ z * star (pcD M W x τ z)
      / ((Real.sqrt (Complex.normSq (pcD M W x τ z)) : ℝ) : ℂ)) z
  refine ((contDiffAt_pcU hWsm hxsm hτsm hW).mul (contDiffAt_star_comp hDsm)).mul ?_
  exact (contDiffAt_ofReal_comp
    (contDiffAt_sqrt_comp (contDiffAt_normSq_comp hDsm) (Complex.normSq_pos.mpr hD).ne')).inv
    (Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (Complex.normSq_pos.mpr hD))))

lemma contDiffAt_pcDc (hMsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) M)
    (hWsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W)
    (hxsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) x)
    (hτsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) τ) {z : ℂ}
    (hA : 0 < pcA M W x τ z) (hD : pcD M W x τ z ≠ 0)
    (h2 : Complex.normSq (pcD M W x τ z) ≠ 2) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (pcDc M W x τ) z := by
  have hDsm : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (pcD M W x τ) z :=
    contDiffAt_pcD hMsm hWsm hxsm hτsm hA
  have h1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : ℂ => pcD M W x τ z / ((Real.sqrt (Complex.normSq (pcD M W x τ z)) : ℝ) : ℂ)) z :=
    hDsm.mul ((contDiffAt_ofReal_comp
      (contDiffAt_sqrt_comp (contDiffAt_normSq_comp hDsm) (Complex.normSq_pos.mpr hD).ne')).inv
      (Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (Complex.normSq_pos.mpr hD)))))
  change ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
    (fun z : ℂ => ((Real.sqrt 2 : ℝ) : ℂ)
      * (pcD M W x τ z / ((Real.sqrt (Complex.normSq (pcD M W x τ z)) : ℝ) : ℂ))
      * ((Real.sqrt (1 - Complex.normSq (pcD M W x τ z) / 2) : ℝ) : ℂ)) z
  refine (contDiffAt_const.mul h1).mul ?_
  refine contDiffAt_ofReal_comp (contDiffAt_sqrt_comp ?_ ?_)
  · exact (contDiffAt_const (c := (1 : ℝ))).sub ((contDiffAt_normSq_comp hDsm).div_const 2)
  · intro h; exact h2 (by linarith)

end Smoothness

section CutDown

/-- The descending radial cut-off `1` on `{‖z‖² ≤ a}` and `0` on `{b ≤ ‖z‖²}` (assumed `a < b`). -/
noncomputable def pcCutDown (a b : ℝ) (z : ℂ) : ℝ := Real.smoothTransition ((b - Complex.normSq z) / (b - a))

@[simp] lemma pcCutDown_apply (a b : ℝ) (z : ℂ) :
    pcCutDown a b z = Real.smoothTransition ((b - Complex.normSq z) / (b - a)) := rfl

lemma contDiff_pcCutDown (a b : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (pcCutDown a b) :=
  Real.smoothTransition.contDiff.comp
    (((contDiff_const.sub Neutral.contDiff_complexNormSq)).div_const _)

lemma pcCutDown_eq_one {a b : ℝ} (hab : a < b) {z : ℂ} (h : Complex.normSq z ≤ a) :
    pcCutDown a b z = 1 :=
  Real.smoothTransition.one_of_one_le
    (one_le_div (by linarith) |>.mpr (by linarith))

lemma pcCutDown_eq_zero {a b : ℝ} (hab : a < b) {z : ℂ} (h : b ≤ Complex.normSq z) :
    pcCutDown a b z = 0 :=
  Real.smoothTransition.zero_of_nonpos
    (div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith))

lemma pcCutDown_nonneg (a b : ℝ) (z : ℂ) : 0 ≤ pcCutDown a b z :=
  Real.smoothTransition.nonneg _

lemma pcCutDown_le_one (a b : ℝ) (z : ℂ) : pcCutDown a b z ≤ 1 :=
  Real.smoothTransition.le_one _

end CutDown

section Norms

variable {M W : ℂ × ℝ → ℂ} {x : ℂ → ℂ} {τ : ℂ → ℝ}

lemma norm_pcU {z : ℂ} (hW : W (x z, τ z) ≠ 0) : ‖pcU W x τ z‖ = 1 := by
  rw [pcU_apply, norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _),
    div_self (norm_ne_zero_iff.mpr hW)]

lemma norm_pcW {z : ℂ} (hW : W (x z, τ z) ≠ 0) (hD : pcD M W x τ z ≠ 0) :
    ‖pcW M W x τ z‖ = 1 := by
  have hUn : ‖pcU W x τ z‖ = 1 := norm_pcU hW
  rw [pcW, norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
    sqrt_normSq, norm_star, hUn, one_mul]
  exact div_self (norm_ne_zero_iff.mpr hD)

lemma pcU_ne_zero {z : ℂ} (hW : W (x z, τ z) ≠ 0) : pcU W x τ z ≠ 0 := by
  intro h
  have := norm_pcU (W := W) (x := x) (τ := τ) hW
  rw [h, norm_zero] at this
  norm_num at this

lemma pcW_ne_zero {z : ℂ} (hW : W (x z, τ z) ≠ 0) (hD : pcD M W x τ z ≠ 0) :
    pcW M W x τ z ≠ 0 := by
  intro h
  have := norm_pcW hW hD
  rw [h, norm_zero] at this
  norm_num at this

/-- The squared norm of the reflected cap coordinate is `2 - ‖D‖²`. -/
lemma normSq_pcDc {z : ℂ} (hD : pcD M W x τ z ≠ 0)
    (h2 : Complex.normSq (pcD M W x τ z) ≤ 2) :
    Complex.normSq (pcDc M W x τ z) = 2 - Complex.normSq (pcD M W x τ z) := by
  have hs : (0 : ℝ) ≤ 1 - Complex.normSq (pcD M W x τ z) / 2 := by linarith
  have hdn : Complex.normSq (pcD M W x τ z) ≠ 0 := (Complex.normSq_pos.mpr hD).ne'
  rw [pcDc, Complex.normSq_mul, Complex.normSq_mul, Complex.normSq_div, Complex.normSq_ofReal,
    Complex.normSq_ofReal, Complex.normSq_ofReal, sqrt_normSq,
    Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.mul_self_sqrt hs, ← sq,
    ← Complex.normSq_eq_norm_sq, div_self hdn]
  ring

lemma norm_pcDc_le_one {z : ℂ} (hD : pcD M W x τ z ≠ 0)
    (h1 : 1 ≤ Complex.normSq (pcD M W x τ z)) (h2 : Complex.normSq (pcD M W x τ z) ≤ 2) :
    ‖pcDc M W x τ z‖ ≤ 1 := by
  have h := normSq_pcDc (M := M) (W := W) (x := x) (τ := τ) hD h2
  rw [Complex.normSq_eq_norm_sq] at h
  rw [← Real.sqrt_sq (norm_nonneg (pcDc M W x τ z))]
  exact Real.sqrt_le_one.mpr (by linarith)

/-- The reflection identity of `Work.Drive.capLift_reflect` for the band data. -/
lemma capProjVecOf_pcW_pcDc {z : ℂ} (hu : ‖pcU W x τ z‖ = 1) (hD : pcD M W x τ z ≠ 0)
    (h2 : Complex.normSq (pcD M W x τ z) ≤ 2) :
    capProjVecOf (pcW M W x τ z) (pcDc M W x τ z)
      = confProjVecOf (pcU W x τ z) (pcD M W x τ z) := by
  have hw : pcW M W x τ z
      = pcU W x τ z * star (pcD M W x τ z) / ((‖pcD M W x τ z‖ : ℝ) : ℂ) := by
    rw [pcW, sqrt_normSq]
  have hdc : pcDc M W x τ z = ((Real.sqrt 2 : ℝ) : ℂ)
      * (pcD M W x τ z / ((‖pcD M W x τ z‖ : ℝ) : ℂ))
      * ((Real.sqrt (1 - ‖pcD M W x τ z‖ ^ 2 / 2) : ℝ) : ℂ) := by
    rw [pcDc, sqrt_normSq, Complex.normSq_eq_norm_sq]
  rw [hw, hdc]
  refine capLift_reflect hu hD ?_
  rw [← sqrt_normSq (pcD M W x τ z)]
  exact Real.sqrt_le_sqrt h2

end Norms

section Regions

variable {M W : ℂ × ℝ → ℂ} {x : ℂ → ℂ} {τ : ℂ → ℝ} {c : ℝ}

/-- On the disk half `‖z‖ ≤ 1/2` (where `τ z ≤ 0`) the band data are honest. -/
lemma pcA_pos_of_disc
    (hband : ∀ x : ℂ, ∀ τ : ℝ, 1 / 4 ≤ ‖x‖ → ‖x‖ ≤ 2 → -c ≤ τ → τ < 0 →
      4 * |τ| * ‖W (x, τ)‖ ^ 2 < ‖M (x, τ)‖ ^ 2)
    (hWne : ∀ x : ℂ, ∀ τ : ℝ, 1 / 4 ≤ ‖x‖ → ‖x‖ ≤ 2 → -c ≤ τ → τ < 0 → W (x, τ) ≠ 0)
    (hM0 : ∀ x : ℂ, 1 / 4 ≤ ‖x‖ → ‖x‖ ≤ 1 → M (x, 0) ≠ 0)
    {z : ℂ} (hx1 : 1 / 4 ≤ ‖x z‖) (hx2 : ‖x z‖ ≤ 1) (hτ2 : -c ≤ τ z) (hτ3 : τ z ≤ 0) :
    0 < pcA M W x τ z := by
  rcases lt_or_eq_of_le hτ3 with h | h
  · exact pcA_pos_of_neg hband hWne hx1 (by linarith) hτ2 h
  · exact pcA_pos_of_zero (M := M) (W := W) (x := x) (τ := τ) hM0 hx1 hx2 h

lemma W_ne_zero_of_disc
    (hWne : ∀ x : ℂ, ∀ τ : ℝ, 1 / 4 ≤ ‖x‖ → ‖x‖ ≤ 2 → -c ≤ τ → τ < 0 → W (x, τ) ≠ 0)
    (hW0 : ∀ x : ℂ, 1 / 4 ≤ ‖x‖ → ‖x‖ ≤ 1 → W (x, 0) ≠ 0)
    {z : ℂ} (hx1 : 1 / 4 ≤ ‖x z‖) (hx2 : ‖x z‖ ≤ 1) (hτ2 : -c ≤ τ z) (hτ3 : τ z ≤ 0) :
    W (x z, τ z) ≠ 0 := by
  rcases lt_or_eq_of_le hτ3 with h | h
  · exact hWne (x z) (τ z) hx1 (by linarith) hτ2 h
  · rw [h]; exact hW0 (x z) hx1 hx2

lemma one_le_normSq_pcD_of_disc
    (hband : ∀ x : ℂ, ∀ τ : ℝ, 1 / 4 ≤ ‖x‖ → ‖x‖ ≤ 2 → -c ≤ τ → τ < 0 →
      4 * |τ| * ‖W (x, τ)‖ ^ 2 < ‖M (x, τ)‖ ^ 2)
    (hWne : ∀ x : ℂ, ∀ τ : ℝ, 1 / 4 ≤ ‖x‖ → ‖x‖ ≤ 2 → -c ≤ τ → τ < 0 → W (x, τ) ≠ 0)
    (hM0 : ∀ x : ℂ, 1 / 4 ≤ ‖x‖ → ‖x‖ ≤ 1 → M (x, 0) ≠ 0)
    {z : ℂ} (hx1 : 1 / 4 ≤ ‖x z‖) (hx2 : ‖x z‖ ≤ 1) (hτ2 : -c ≤ τ z) (hτ3 : τ z ≤ 0) :
    1 ≤ Complex.normSq (pcD M W x τ z) := by
  rcases lt_or_eq_of_le hτ3 with h | h
  · exact one_le_normSq_pcD_of_neg hband hWne hx1 (by linarith) hτ2 h
  · exact le_of_eq (normSq_pcD_of_zero (M := M) (W := W) (x := x) (τ := τ) h
      (by rw [h]; exact hM0 (x z) hx1 hx2)).symm

lemma normSq_pcD_le_two_of_disc
    (hband : ∀ x : ℂ, ∀ τ : ℝ, 1 / 4 ≤ ‖x‖ → ‖x‖ ≤ 2 → -c ≤ τ → τ < 0 →
      4 * |τ| * ‖W (x, τ)‖ ^ 2 < ‖M (x, τ)‖ ^ 2)
    (hWne : ∀ x : ℂ, ∀ τ : ℝ, 1 / 4 ≤ ‖x‖ → ‖x‖ ≤ 2 → -c ≤ τ → τ < 0 → W (x, τ) ≠ 0)
    (hM0 : ∀ x : ℂ, 1 / 4 ≤ ‖x‖ → ‖x‖ ≤ 1 → M (x, 0) ≠ 0)
    {z : ℂ} (hx1 : 1 / 4 ≤ ‖x z‖) (hx2 : ‖x z‖ ≤ 1) (hτ2 : -c ≤ τ z) (hτ3 : τ z ≤ 0) :
    Complex.normSq (pcD M W x τ z) ≤ 2 := by
  rcases lt_or_eq_of_le hτ3 with h | h
  · exact normSq_pcD_le_two_of_neg hband hWne hx1 (by linarith) hτ2 h
  · rw [normSq_pcD_of_zero (M := M) (W := W) (x := x) (τ := τ) h
      (by rw [h]; exact hM0 (x z) hx1 hx2)]
    norm_num

lemma pcD_ne_zero_of_disc
    (hband : ∀ x : ℂ, ∀ τ : ℝ, 1 / 4 ≤ ‖x‖ → ‖x‖ ≤ 2 → -c ≤ τ → τ < 0 →
      4 * |τ| * ‖W (x, τ)‖ ^ 2 < ‖M (x, τ)‖ ^ 2)
    (hWne : ∀ x : ℂ, ∀ τ : ℝ, 1 / 4 ≤ ‖x‖ → ‖x‖ ≤ 2 → -c ≤ τ → τ < 0 → W (x, τ) ≠ 0)
    (hM0 : ∀ x : ℂ, 1 / 4 ≤ ‖x‖ → ‖x‖ ≤ 1 → M (x, 0) ≠ 0)
    {z : ℂ} (hx1 : 1 / 4 ≤ ‖x z‖) (hx2 : ‖x z‖ ≤ 1) (hτ2 : -c ≤ τ z) (hτ3 : τ z ≤ 0) :
    pcD M W x τ z ≠ 0 := by
  intro h
  have h1 := one_le_normSq_pcD_of_disc hband hWne hM0 hx1 hx2 hτ2 hτ3
  rw [h, Complex.normSq_zero] at h1
  norm_num at h1

/-! ## The honest half `‖z‖ ≥ 1/2` -/

lemma W_ne_zero_of_honest {γ : Circle → ℝ × ℝ}
    (hγ : Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    (hWval : ∀ x : ℂ, ∀ τ : ℝ, 0 ≤ τ → ‖x‖ = 1 → W (x, τ) = Neutral.dchW γ (x, Real.sqrt τ))
    {z : ℂ} (hxu : ‖x z‖ = 1) (hτ0 : 0 ≤ τ z) : W (x z, τ z) ≠ 0 := by
  rw [hWval (x z) (τ z) hτ0 hxu]
  exact (Neutral.stripDiskChordNe γ hγ).2 (x z) (by rw [← norm_ne_zero_iff, hxu]; norm_num)
    (Real.sqrt (τ z))

lemma pcA_eq_dataR_sq {γ : Circle → ℝ × ℝ}
    (hγ : Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    (hMval : ∀ x : ℂ, ∀ τ : ℝ, 0 ≤ τ → ‖x‖ = 1 → M (x, τ) = Neutral.dataMid γ x (Real.sqrt τ))
    (hWval : ∀ x : ℂ, ∀ τ : ℝ, 0 ≤ τ → ‖x‖ = 1 → W (x, τ) = Neutral.dchW γ (x, Real.sqrt τ))
    {z : ℂ} (hxu : ‖x z‖ = 1) (hτ0 : 0 ≤ τ z) :
    pcA M W x τ z = Neutral.dataR γ (x z) (Real.sqrt (τ z)) ^ 2 := by
  have hxne : x z ≠ 0 := by rw [← norm_ne_zero_iff, hxu]; norm_num
  have hsmul := Neutral.dchW_smul γ hγ hxne (Real.sqrt (τ z))
  have hchord : Neutral.dataChord γ (x z) (Real.sqrt (τ z))
      = ((Real.sqrt (τ z) : ℝ) : ℂ) * Neutral.dchW γ (x z, Real.sqrt (τ z)) := by
    rw [← hsmul, Complex.real_smul]
  have hnn : (0 : ℝ) ≤ Complex.normSq (Neutral.dataMid γ (x z) (Real.sqrt (τ z)))
      + Complex.normSq (Neutral.dataChord γ (x z) (Real.sqrt (τ z))) :=
    add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)
  rw [pcA, hMval (x z) (τ z) hτ0 hxu, hWval (x z) (τ z) hτ0 hxu, Neutral.dataR,
    Real.sq_sqrt hnn, hchord, Complex.normSq_mul, Complex.normSq_ofReal, Real.mul_self_sqrt hτ0]

lemma dataR_pos_of_honest {γ : Circle → ℝ × ℝ} (hγne : ∀ x : Circle, γ x ≠ 0)
    {z : ℂ} (hxu : ‖x z‖ = 1) : 0 < Neutral.dataR γ (x z) (Real.sqrt (τ z)) :=
  Neutral.dataR_pos γ hγne (by rw [← norm_ne_zero_iff, hxu]; norm_num) _

lemma pcA_pos_of_honest {γ : Circle → ℝ × ℝ}
    (hγ : Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    (hγne : ∀ x : Circle, γ x ≠ 0)
    (hMval : ∀ x : ℂ, ∀ τ : ℝ, 0 ≤ τ → ‖x‖ = 1 → M (x, τ) = Neutral.dataMid γ x (Real.sqrt τ))
    (hWval : ∀ x : ℂ, ∀ τ : ℝ, 0 ≤ τ → ‖x‖ = 1 → W (x, τ) = Neutral.dchW γ (x, Real.sqrt τ))
    {z : ℂ} (hxu : ‖x z‖ = 1) (hτ0 : 0 ≤ τ z) : 0 < pcA M W x τ z := by
  rw [pcA_eq_dataR_sq hγ hMval hWval hxu hτ0]
  exact pow_pos (dataR_pos_of_honest (τ := τ) hγne hxu) 2

lemma pcD_eq_dataD_of_honest {γ : Circle → ℝ × ℝ}
    (hγ : Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    (hγne : ∀ x : Circle, γ x ≠ 0)
    (hMval : ∀ x : ℂ, ∀ τ : ℝ, 0 ≤ τ → ‖x‖ = 1 → M (x, τ) = Neutral.dataMid γ x (Real.sqrt τ))
    (hWval : ∀ x : ℂ, ∀ τ : ℝ, 0 ≤ τ → ‖x‖ = 1 → W (x, τ) = Neutral.dchW γ (x, Real.sqrt τ))
    {z : ℂ} (hxu : ‖x z‖ = 1) (hτ0 : 0 ≤ τ z) :
    pcD M W x τ z = Neutral.dataD γ (x z) (Real.sqrt (τ z)) := by
  have hA := pcA_eq_dataR_sq (M := M) (W := W) (x := x) (τ := τ) hγ hMval hWval hxu hτ0
  have hR := dataR_pos_of_honest (τ := τ) hγne hxu
  rw [pcD, hA, Real.sqrt_sq hR.le, hMval (x z) (τ z) hτ0 hxu, Neutral.dataD]

lemma normSq_pcD_le_one_of_honest {γ : Circle → ℝ × ℝ}
    (hγ : Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    (hγne : ∀ x : Circle, γ x ≠ 0)
    (hMval : ∀ x : ℂ, ∀ τ : ℝ, 0 ≤ τ → ‖x‖ = 1 → M (x, τ) = Neutral.dataMid γ x (Real.sqrt τ))
    (hWval : ∀ x : ℂ, ∀ τ : ℝ, 0 ≤ τ → ‖x‖ = 1 → W (x, τ) = Neutral.dchW γ (x, Real.sqrt τ))
    {z : ℂ} (hxu : ‖x z‖ = 1) (hτ0 : 0 ≤ τ z) :
    Complex.normSq (pcD M W x τ z) ≤ 1 := by
  have hxne : x z ≠ 0 := by rw [← norm_ne_zero_iff, hxu]; norm_num
  rw [pcD_eq_dataD_of_honest hγ hγne hMval hWval hxu hτ0, Complex.normSq_eq_norm_sq]
  exact pow_le_one₀ (norm_nonneg _) (Neutral.dataD_norm_le_one γ hγne hxne (Real.sqrt (τ z)))

end Regions

section Structure

variable {M W : ℂ × ℝ → ℂ} {x : ℂ → ℂ} {τ : ℂ → ℝ} {c : ℝ}

/-- The strict form of `normSq (pcD) ≤ 2` on the negative band. -/
lemma normSq_pcD_lt_two_of_neg
    (hband : ∀ x : ℂ, ∀ τ : ℝ, 1 / 4 ≤ ‖x‖ → ‖x‖ ≤ 2 → -c ≤ τ → τ < 0 →
      4 * |τ| * ‖W (x, τ)‖ ^ 2 < ‖M (x, τ)‖ ^ 2)
    (hWne : ∀ x : ℂ, ∀ τ : ℝ, 1 / 4 ≤ ‖x‖ → ‖x‖ ≤ 2 → -c ≤ τ → τ < 0 → W (x, τ) ≠ 0)
    {z : ℂ} (hx1 : 1 / 4 ≤ ‖x z‖) (hx2 : ‖x z‖ ≤ 2) (hc : -c ≤ τ z) (hτ : τ z < 0) :
    Complex.normSq (pcD M W x τ z) < 2 := by
  have hA := pcA_pos_of_neg (M := M) (W := W) (x := x) (τ := τ) hband hWne hx1 hx2 hc hτ
  have hb := hband (x z) (τ z) hx1 hx2 hc hτ
  have hb' : 4 * |τ z| * Complex.normSq (W (x z, τ z)) < Complex.normSq (M (x z, τ z)) := by
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]; exact hb
  have h1 : (0 : ℝ) ≤ |τ z| * Complex.normSq (W (x z, τ z)) :=
    mul_nonneg (abs_nonneg _) (Complex.normSq_nonneg _)
  have h2 : τ z * Complex.normSq (W (x z, τ z))
      = -(|τ z| * Complex.normSq (W (x z, τ z))) := by
    rw [abs_of_neg hτ]; ring
  rw [normSq_pcD hA.le, div_lt_iff₀ hA, pcA, h2]
  nlinarith [hb', h1]

/-- The band data at a point of the disk half `‖z‖ ≤ 1/2`. -/
structure PcDisc (M W : ℂ × ℝ → ℂ) (x : ℂ → ℂ) (τ : ℂ → ℝ) (z : ℂ) : Prop where
  pos : 0 < pcA M W x τ z
  Wne : W (x z, τ z) ≠ 0
  Dne : pcD M W x τ z ≠ 0
  Dge : 1 ≤ Complex.normSq (pcD M W x τ z)
  Dlt : Complex.normSq (pcD M W x τ z) < 2

/-- The band data at a point of the honest half `1/2 ≤ ‖z‖`. -/
structure PcHon (M W : ℂ × ℝ → ℂ) (x : ℂ → ℂ) (τ : ℂ → ℝ) (z : ℂ) : Prop where
  pos : 0 < pcA M W x τ z
  Wne : W (x z, τ z) ≠ 0
  Dle : Complex.normSq (pcD M W x τ z) ≤ 1
  Dlt : Complex.normSq (pcD M W x τ z) < 2

lemma PcDisc.of_disc
    (hband : ∀ x : ℂ, ∀ τ : ℝ, 1 / 4 ≤ ‖x‖ → ‖x‖ ≤ 2 → -c ≤ τ → τ < 0 →
      4 * |τ| * ‖W (x, τ)‖ ^ 2 < ‖M (x, τ)‖ ^ 2)
    (hWne : ∀ x : ℂ, ∀ τ : ℝ, 1 / 4 ≤ ‖x‖ → ‖x‖ ≤ 2 → -c ≤ τ → τ < 0 → W (x, τ) ≠ 0)
    (hM0 : ∀ x : ℂ, 1 / 4 ≤ ‖x‖ → ‖x‖ ≤ 1 → M (x, 0) ≠ 0)
    (hW0 : ∀ x : ℂ, 1 / 4 ≤ ‖x‖ → ‖x‖ ≤ 1 → W (x, 0) ≠ 0)
    {z : ℂ} (hx1 : 1 / 4 ≤ ‖x z‖) (hx2 : ‖x z‖ ≤ 1) (hτ2 : -c ≤ τ z) (hτ3 : τ z ≤ 0) :
    PcDisc M W x τ z := by
  have hx2' : ‖x z‖ ≤ 2 := by linarith
  rcases lt_or_eq_of_le hτ3 with h | h
  · exact ⟨pcA_pos_of_neg hband hWne hx1 hx2' hτ2 h,
      hWne (x z) (τ z) hx1 hx2' hτ2 h,
      pcD_ne_zero_of_disc hband hWne hM0 hx1 hx2 hτ2 hτ3,
      one_le_normSq_pcD_of_neg hband hWne hx1 hx2' hτ2 h,
      normSq_pcD_lt_two_of_neg hband hWne hx1 hx2' hτ2 h⟩
  · have hMne : M (x z, τ z) ≠ 0 := by rw [h]; exact hM0 (x z) hx1 hx2
    have hWne0 : W (x z, τ z) ≠ 0 := by rw [h]; exact hW0 (x z) hx1 hx2
    have hD1 : Complex.normSq (pcD M W x τ z) = 1 := normSq_pcD_of_zero h hMne
    refine ⟨?_, hWne0, ?_, ?_, ?_⟩
    · rw [pcA_apply_zero h, Complex.normSq_pos]; exact hMne
    · intro hzero
      rw [hzero, Complex.normSq_zero] at hD1
      norm_num at hD1
    · exact le_of_eq hD1.symm
    · rw [hD1]; norm_num

lemma PcHon.of_honest {γ : Circle → ℝ × ℝ}
    (hγ : Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    (hγne : ∀ x : Circle, γ x ≠ 0)
    (hMval : ∀ x : ℂ, ∀ τ : ℝ, 0 ≤ τ → ‖x‖ = 1 → M (x, τ) = Neutral.dataMid γ x (Real.sqrt τ))
    (hWval : ∀ x : ℂ, ∀ τ : ℝ, 0 ≤ τ → ‖x‖ = 1 → W (x, τ) = Neutral.dchW γ (x, Real.sqrt τ))
    {z : ℂ} (hxu : ‖x z‖ = 1) (hτ0 : 0 ≤ τ z) : PcHon M W x τ z :=
  ⟨pcA_pos_of_honest hγ hγne hMval hWval hxu hτ0,
    W_ne_zero_of_honest hγ hWval hxu hτ0,
    normSq_pcD_le_one_of_honest hγ hγne hMval hWval hxu hτ0,
    lt_of_le_of_lt (normSq_pcD_le_one_of_honest hγ hγne hMval hWval hxu hτ0) (by norm_num)⟩

namespace PcDisc

variable {M W : ℂ × ℝ → ℂ} {x : ℂ → ℂ} {τ : ℂ → ℝ} {z : ℂ}

lemma normU (h : PcDisc M W x τ z) : ‖pcU W x τ z‖ = 1 := norm_pcU h.Wne

lemma normW' (h : PcDisc M W x τ z) : ‖pcW M W x τ z‖ = 1 := norm_pcW h.Wne h.Dne

lemma Wne' (h : PcDisc M W x τ z) : pcW M W x τ z ≠ 0 := pcW_ne_zero h.Wne h.Dne

lemma dc_le (h : PcDisc M W x τ z) : ‖pcDc M W x τ z‖ ≤ 1 :=
  norm_pcDc_le_one h.Dne h.Dge h.Dlt.le

lemma Dlt_two (h : PcDisc M W x τ z) : Complex.normSq (pcD M W x τ z) ≠ 2 := ne_of_lt h.Dlt

lemma dc_normSq_eq (h : PcDisc M W x τ z) :
    Complex.normSq (pcDc M W x τ z) = 2 - Complex.normSq (pcD M W x τ z) :=
  normSq_pcDc h.Dne h.Dlt.le

lemma reflect (h : PcDisc M W x τ z) :
    capProjVecOf (pcW M W x τ z) (pcDc M W x τ z)
      = confProjVecOf (pcU W x τ z) (pcD M W x τ z) :=
  capProjVecOf_pcW_pcDc h.normU h.Dne h.Dlt.le

lemma dD (hMsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) M)
    (hWsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W)
    (hxsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) x)
    (hτsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) τ) (h : PcDisc M W x τ z) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (pcD M W x τ) z :=
  contDiffAt_pcD hMsm hWsm hxsm hτsm h.pos

lemma dU (hWsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W)
    (hxsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) x)
    (hτsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) τ) (h : PcDisc M W x τ z) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (pcU W x τ) z :=
  contDiffAt_pcU hWsm hxsm hτsm h.Wne

lemma dW (hMsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) M)
    (hWsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W)
    (hxsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) x)
    (hτsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) τ) (h : PcDisc M W x τ z) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (pcW M W x τ) z :=
  contDiffAt_pcW hMsm hWsm hxsm hτsm h.pos h.Wne h.Dne

lemma dDc (hMsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) M)
    (hWsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W)
    (hxsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) x)
    (hτsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) τ) (h : PcDisc M W x τ z) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (pcDc M W x τ) z :=
  contDiffAt_pcDc hMsm hWsm hxsm hτsm h.pos h.Dne h.Dlt_two

end PcDisc

namespace PcHon

variable {M W : ℂ × ℝ → ℂ} {x : ℂ → ℂ} {τ : ℂ → ℝ} {z : ℂ}

lemma normU (h : PcHon M W x τ z) : ‖pcU W x τ z‖ = 1 := norm_pcU h.Wne

lemma Dlt_two (h : PcHon M W x τ z) : Complex.normSq (pcD M W x τ z) ≠ 2 :=
  ne_of_lt (lt_of_le_of_lt h.Dle (by norm_num))

lemma dD (hMsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) M)
    (hWsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W)
    (hxsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) x)
    (hτsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) τ) (h : PcHon M W x τ z) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (pcD M W x τ) z :=
  contDiffAt_pcD hMsm hWsm hxsm hτsm h.pos

lemma dU (hWsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W)
    (hxsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) x)
    (hτsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) τ) (h : PcHon M W x τ z) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (pcU W x τ) z :=
  contDiffAt_pcU hWsm hxsm hτsm h.Wne

lemma dConf (hMsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) M)
    (hWsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W)
    (hxsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) x)
    (hτsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) τ) (h : PcHon M W x τ z) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z => confProjVecOf (pcU W x τ z) (pcD M W x τ z)) z :=
  pc_contDiffAt_confProjVecOf (h.dU hWsm hxsm hτsm) (h.dD hMsm hWsm hxsm hτsm) h.Dlt_two

end PcHon

end Structure

section Seam

variable {M W : ℂ × ℝ → ℂ} {x : ℂ → ℂ} {τ : ℂ → ℝ}

/-- `star (exp (i θ)) = exp (-i θ)`. -/
lemma star_exp_mul_I (θ : ℝ) :
    star (Complex.exp (((θ : ℝ) : ℂ) * Complex.I))
      = Complex.exp ((((-θ : ℝ)) : ℂ) * Complex.I) := by
  change (starRingEnd ℂ) (Complex.exp (((θ : ℝ) : ℂ) * Complex.I))
    = Complex.exp ((((-θ : ℝ)) : ℂ) * Complex.I)
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_neg]
  ring

/-- **The direction datum at the seam, in the band notation.**  On the circle of radius `1/2` the
reflected direction `pcW` is the direction datum `dirDatum` evaluated at `τ = 0`. -/
lemma pcW_at_seam
    (hx1 : ∀ z : ℂ, 1 / 2 ≤ ‖z‖ → x z = z / ((‖z‖ : ℝ) : ℂ))
    (hτ1 : ∀ z : ℂ, 1 / 2 ≤ ‖z‖ → τ z = Real.pi ^ 2 / 2 * (‖z‖ - 1 / 2))
    (hM0 : ∀ x : ℂ, 1 / 4 ≤ ‖x‖ → ‖x‖ ≤ 1 → M (x, 0) ≠ 0)
    (hW0 : ∀ x : ℂ, 1 / 4 ≤ ‖x‖ → ‖x‖ ≤ 1 → W (x, 0) ≠ 0)
    (σ : ℝ) :
    pcW M W x τ (((1 / 2 : ℝ) : ℂ) * Complex.exp (((σ : ℂ) * Complex.I)))
      = dirDatum M W (Complex.exp (((σ : ℂ) * Complex.I)), 0) := by
  set z : ℂ := ((1 / 2 : ℝ) : ℂ) * Complex.exp (((σ : ℂ) * Complex.I)) with hz
  have hre : (((σ : ℂ) * Complex.I).re) = 0 := by simp [Complex.mul_re, Complex.mul_im]
  have hnorm : ‖z‖ = 1 / 2 := by
    rw [hz, norm_mul, Complex.norm_real, Complex.norm_exp, hre, Real.exp_zero]
    norm_num
  have hexp1 : ‖Complex.exp (((σ : ℂ) * Complex.I))‖ = 1 := by
    rw [Complex.norm_exp, hre, Real.exp_zero]
  have hx : x z = Complex.exp (((σ : ℂ) * Complex.I)) := by
    rw [hx1 z (le_of_eq hnorm.symm), hnorm, hz]
    field_simp
  have hτ : τ z = 0 := by
    rw [hτ1 z (le_of_eq hnorm.symm), hnorm]; ring
  have hM : M (x z, τ z) ≠ 0 := by
    rw [hx, hτ]
    exact hM0 _ (by norm_num [hexp1]) (by norm_num [hexp1])
  have hW : W (x z, τ z) ≠ 0 := by
    rw [hx, hτ]
    exact hW0 _ (by norm_num [hexp1]) (by norm_num [hexp1])
  rw [pcW_eq_dirDatum (M := M) (W := W) (x := x) (τ := τ) hτ hM hW, hx, hτ]

end Seam

section Final

lemma pcCut_eq_one_iff {a b : ℝ} (hab : a < b) (z : ℂ) :
    pcCut a b z = 1 ↔ b ≤ Complex.normSq z := by
  rw [pcCut_apply, Real.smoothTransition.eq_one_iff_one_le, one_le_div (by linarith)]
  constructor <;> intro h <;> linarith

lemma pcCut_pos_iff {a b : ℝ} (hab : a < b) (z : ℂ) :
    0 < pcCut a b z ↔ a < Complex.normSq z := by
  have hsT : ∀ y : ℝ, 0 < Real.smoothTransition y ↔ 0 < y := fun y =>
    ⟨fun h => not_le.mp (fun hy => by
        rw [Real.smoothTransition.zero_of_nonpos hy] at h; exact lt_irrefl 0 h),
      Real.smoothTransition.pos_of_pos⟩
  rw [pcCut_apply, hsT, div_pos_iff]
  constructor
  · rintro (⟨h1, -⟩ | ⟨h1, h2⟩) <;> linarith
  · intro h; exact Or.inl ⟨by linarith, by linarith⟩

lemma lt_norm_of_normSq_lt {a : ℝ} (ha : 0 ≤ a) {z : ℂ} (h : a ^ 2 < Complex.normSq z) :
    a < ‖z‖ := by
  have h' : a ^ 2 < ‖z‖ ^ 2 := by rwa [Complex.normSq_eq_norm_sq] at h
  have h2 := sq_lt_sq.mp h'
  simpa [abs_of_nonneg ha, abs_of_nonneg (norm_nonneg z)] using h2

lemma normSq_lt_of_lt_norm {a : ℝ} (ha : 0 ≤ a) {z : ℂ} (h : ‖z‖ < a) :
    Complex.normSq z < a ^ 2 := by
  rw [Complex.normSq_eq_norm_sq]
  nlinarith [h, norm_nonneg z, ha]

/-- A configuration sphere point with a nonzero direction never vanishes. -/
lemma confProjVecOf_ne_zero_of_ne {u d : ℂ} (hu : u ≠ 0) : confProjVecOf u d ≠ 0 := by
  intro h
  have h2 : c₂ (confProjVecOf u d) = 0 := by rw [h]; simp [c₂]
  rw [c₂_confProjVecOf, div_eq_zero_iff] at h2
  have hd : d = 0 := by
    rcases h2 with h2 | h2
    · rcases mul_eq_zero.mp h2 with h3 | h3
      · exact absurd h3 (star_ne_zero.mpr hu)
      · exact h3
    · exact absurd h2
        (Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (by norm_num))))
  have h1 : c₁ (confProjVecOf u d) = 0 := by rw [h]; simp [c₁]
  rw [c₁_confProjVecOf, hd] at h1
  simp at h1
  exact hu h1

end Final

lemma le_norm_of_normSq_le {a : ℝ} (ha : 0 ≤ a) {z : ℂ} (h : a ^ 2 ≤ Complex.normSq z) :
    a ≤ ‖z‖ := by
  rw [Complex.normSq_eq_norm_sq] at h
  nlinarith [norm_nonneg z, ha]

end Work.Drive
