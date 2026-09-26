import Mathlib
import Submission.Work.CKFinal.LineDecay.Defs
import Submission.Work.CKFinal.LineDecay.shift_helpers
import Submission.Work.CKFinal.LineDecay.Khat_second_residue
import Submission.Work.CKFinal.LineDecay.F1Half.Basic

/-!
# The contour shift for the `K̂`-ray `Re = -1/2` : shared definitions

This file collects the objects of the contour shift of the `K̂` analogues of the identities
`Work.CKFinal.LineDecay.shift_f1_neg_half` / `shift_f1_half`.  The integrand is

  `f1hat ℓ d τ r z = K̂^{(d)}(τ, z - 1) · e^{iπr²z}`,

its poles in the closed half strip `{0 ≤ Re ≤ 1, 1 ≤ Im}` are the points `poleAtTauAddOne τ`
(when `Re τ = -1/2`) and `poleAtTau τ` (when `Re τ = 1/2`), and the tail integrands are
`A0hat` (ray `Re = 0`) and `Amhat` (ray `Re = -1`).
-/

noncomputable section

namespace Work.CKFinal.LineDecay

open UpperHalfPlane MeasureTheory Filter Topology
open scoped Topology

/-- The closed half-strip `{0 ≤ Re ≤ 1, 1 ≤ Im}` of `ℂ`, the domain of the contour shift. -/
def halfStripClosed : Set ℂ := {z : ℂ | 0 ≤ z.re ∧ z.re ≤ 1 ∧ 1 ≤ z.im}

/-- The pole `z = τ` of the shifted integrand `f1hat` when `Re τ = 1/2`
(the second variable `z - 1 = τ - 1` is then on the orbit of `τ`). -/
def poleAtTau (τ : UpperHalfPlane) : ℂ := (τ : ℂ)

/-- The pole `z = τ + 1` of the shifted integrand `f1hat` when `Re τ = -1/2`
(the second variable `z - 1 = τ` is then the diagonal point). -/
def poleAtTauAddOne (τ : UpperHalfPlane) : ℂ := (((1 : ℝ) +ᵥ τ : UpperHalfPlane) : ℂ)

lemma poleAtTau_re (τ : UpperHalfPlane) : (poleAtTau τ).re = τ.re := rfl

lemma poleAtTau_im (τ : UpperHalfPlane) : (poleAtTau τ).im = τ.im := rfl

lemma poleAtTauAddOne_re (τ : UpperHalfPlane) :
    (poleAtTauAddOne τ).re = τ.re + 1 := by
  rw [poleAtTauAddOne, UpperHalfPlane.coe_vadd, Complex.add_re, Complex.ofReal_re,
    UpperHalfPlane.coe_re]
  ring

lemma poleAtTauAddOne_im (τ : UpperHalfPlane) :
    (poleAtTauAddOne τ).im = τ.im := by
  rw [poleAtTauAddOne, UpperHalfPlane.coe_vadd, Complex.add_im, Complex.ofReal_im,
    UpperHalfPlane.coe_im]
  ring

/-- The shifted contour integrand `f̂₁(z) = K̂^{(d)}(τ, z - 1)·e^{iπr²z}`. -/
def f1hat (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (τ : UpperHalfPlane) (r : ℝ) : ℂ → ℂ :=
  fun z => Work.Kernels.Khat ℓ d τ (UpperHalfPlane.ofComplex (z - 1))
    * Work.Asymptotics.kerExp r z

/-- The tail integrand of the `K̂(τ, ·)` ray. -/
def A0hat (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (τ : UpperHalfPlane) (r : ℝ) : ℝ → ℂ :=
  fun t => Work.CKFinal.Kax (Work.Kernels.Khat ℓ d) τ 0 t * Work.Asymptotics.gaussWeight r t

/-- The tail integrand of the `K̂(τ, ·-1)` ray. -/
def Amhat (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (τ : UpperHalfPlane) (r : ℝ) : ℝ → ℂ :=
  fun t => Work.CKFinal.Kax (Work.Kernels.Khat ℓ d) τ (-1) t * Work.Asymptotics.gaussWeight r t

/-! ## The divisor is avoided on the half-strip, away from the pole -/

/-- For `τ.re = -1/2`, `Im τ ≥ 12` and `z` in the closed half-strip `{0 ≤ Re ≤ 1, Im ≥ 1}`
with `z ≠ τ + 1`, the point `z - 1` is not in the `SL(2,ℤ)`-orbit of `τ`. -/
theorem ofComplex_sub_one_clean_neg (τ : UpperHalfPlane) (hre : τ.re = -1 / 2)
    (him : 12 ≤ τ.im) :
    ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 → 1 ≤ z.im → z ≠ poleAtTauAddOne τ →
      Work.Kernels.jInvariantFun τ ≠
        Work.Kernels.jInvariantFun (UpperHalfPlane.ofComplex (z - 1)) := by
  intro z h0 h1 h2 hne hjeq
  have hwimpos : 0 < (z - 1).im := by simp [Complex.sub_im]; linarith
  have hwim : 1 ≤ (z - 1).im := by simp [Complex.sub_im]; linarith
  have hwre : -1 ≤ (z - 1).re := by simp [Complex.sub_re]; linarith
  have hwre1 : (z - 1).re ≤ 1 := by simp [Complex.sub_re]; linarith
  have hcoe : ((UpperHalfPlane.ofComplex (z - 1) : UpperHalfPlane) : ℂ) = z - 1 := by
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos hwimpos]
  have hc := ofComplex_mem_orbit τ (Or.inr hre) him hwim hwre hwre1 hjeq
  rcases hc with h | h | h
  · -- `z - 1 = τ`, i.e. `z = τ + 1`
    have hc1 : ((UpperHalfPlane.ofComplex (z - 1) : UpperHalfPlane) : ℂ) = (τ : ℂ) := by
      rw [h]
    have hz : (z - 1) = (τ : ℂ) := hcoe.symm.trans hc1
    have hzz : z = (τ : ℂ) + 1 := by
      have h' := congrArg (fun w : ℂ => w + 1) hz
      simpa using h'
    have hz0 : poleAtTauAddOne τ = (τ : ℂ) + 1 := by
      rw [poleAtTauAddOne, UpperHalfPlane.coe_vadd]; push_cast; ring
    exact hne (by rw [hzz, hz0])
  · -- `z - 1 = τ - 1`, whose real part is `τ.re - 1 = -3/2 < -1`
    have hc2 : ((UpperHalfPlane.ofComplex (z - 1) : UpperHalfPlane) : ℂ)
        = ((((-1 : ℝ) +ᵥ τ : UpperHalfPlane)) : ℂ) := by rw [h]
    have hz : (z - 1) = (τ : ℂ) - 1 := by
      rw [hcoe.symm.trans hc2, UpperHalfPlane.coe_vadd]
      push_cast; ring
    have hre' : (z - 1).re = τ.re - 1 := by rw [hz]; simp
    have hle : (z - 1).re ≤ 0 := by simp [Complex.sub_re]; linarith
    linarith [hre', hle, hre]
  · -- `z - 1 = τ + 1`, i.e. `z = τ + 2`, whose real part is `τ.re + 2 = 3/2 > 1`
    have hc3 : ((UpperHalfPlane.ofComplex (z - 1) : UpperHalfPlane) : ℂ)
        = ((((1 : ℝ) +ᵥ τ : UpperHalfPlane)) : ℂ) := by rw [h]
    have hz : (z - 1) = (τ : ℂ) + 1 := by
      rw [hcoe.symm.trans hc3, UpperHalfPlane.coe_vadd]
      push_cast; ring
    have hzz : z = (τ : ℂ) + 2 := by
      have h' := congrArg (fun w : ℂ => w + 1) hz
      have h2 : z = z - 1 + 1 := by ring
      rw [h2, h']; ring
    have hre' : z.re = τ.re + 2 := by rw [hzz]; simp
    linarith [hre', h1, hre]

/-- For `τ.re = 1/2`, `Im τ ≥ 12` and `z` in the closed half-strip `{0 ≤ Re ≤ 1, Im ≥ 1}`
with `z ≠ τ`, the point `z - 1` is not in the `SL(2,ℤ)`-orbit of `τ`. -/
theorem ofComplex_sub_one_clean_pos (τ : UpperHalfPlane) (hre : τ.re = 1 / 2)
    (him : 12 ≤ τ.im) :
    ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 → 1 ≤ z.im → z ≠ poleAtTau τ →
      Work.Kernels.jInvariantFun τ ≠
        Work.Kernels.jInvariantFun (UpperHalfPlane.ofComplex (z - 1)) := by
  intro z h0 h1 h2 hne
  exact ofComplex_sub_one_clean τ hre him z h0 h1 h2 (by simpa [poleAtTau] using hne)

end Work.CKFinal.LineDecay
