import Mathlib
import Submission.Work.Drive.chordStrictWideDescent
import Submission.Work.Drive.planeChartDataAux

/-!
# The strip data of the descent

`Work.Drive.descent_strip_injective` is a statement about the pair `(pcA, pcDc)` evaluated at the
points `x = e^{iα}` (constant in `z`) and `τ = τ` (constant), at `z = 0`.  This file fixes the
shorthand for those evaluations:

* `dstripU α = e^{iα}`;
* `dstripA M W α τ = ‖M (e^{iα}, τ)‖² + τ ‖W (e^{iα}, τ)‖² = pcA M W (const (dstripU α)) (const τ) 0`;
* `dstripD M W α τ = M (e^{iα}, τ) / √(dstripA M W α τ) = pcD …`;
* `dstripDc M W α τ = √2 (D/‖D‖) √(1 - ‖D‖²/2)  = pcDc …`;
* `dstripG M W (α, τ) = (M (e^{iα}, τ), dstripA M W α τ)`, the map whose injectivity on a thin strip
  is the content of the statement (the pair `(dstripA, dstripDc)` is a function of `dstripG`, and
  `(dstripA, dstripDc)` determines `dstripG` back — see
  `Work.Drive.dstripG_eq_of_dstripA_dstripDc_eq`).

The bridge lemmas `pcA_dstripU`, `pcD_dstripU`, `pcDc_dstripU` are `rfl`.
-/

namespace Work.Drive

open scoped ContDiff

noncomputable section

/-- The unit complex number `e^{iα}`. -/
def dstripU (α : ℝ) : ℂ := Complex.exp ((α : ℂ) * Complex.I)

lemma dstripU_add_two_pi (α : ℝ) : dstripU (α + 2 * Real.pi) = dstripU α := by
  rw [dstripU, dstripU,
    show (((α + 2 * Real.pi : ℝ) : ℂ) * Complex.I)
      = (α : ℂ) * Complex.I + (2 * Real.pi : ℂ) * Complex.I by push_cast; ring,
    Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

lemma norm_dstripU (α : ℝ) : ‖dstripU α‖ = 1 := by
  rw [dstripU, Complex.norm_exp]
  simp

lemma dstripU_ne_zero (α : ℝ) : dstripU α ≠ 0 := by
  rw [dstripU]; exact Complex.exp_ne_zero _

lemma contDiff_dstripU : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) dstripU := by
  have h : dstripU = fun α : ℝ => Complex.exp ((α : ℂ) * Complex.I) := rfl
  rw [h]
  exact (Complex.ofRealCLM.contDiff.mul contDiff_const).cexp

/-- `pcA` at the strip point. -/
def dstripA (M W : ℂ × ℝ → ℂ) (α τ : ℝ) : ℝ :=
  Complex.normSq (M (dstripU α, τ)) + τ * Complex.normSq (W (dstripU α, τ))

/-- `pcD` at the strip point. -/
def dstripD (M W : ℂ × ℝ → ℂ) (α τ : ℝ) : ℂ :=
  M (dstripU α, τ) / ((Real.sqrt (dstripA M W α τ) : ℝ) : ℂ)

/-- `pcDc` at the strip point. -/
def dstripDc (M W : ℂ × ℝ → ℂ) (α τ : ℝ) : ℂ :=
  ((Real.sqrt 2 : ℝ) : ℂ)
    * (dstripD M W α τ / ((Real.sqrt (Complex.normSq (dstripD M W α τ)) : ℝ) : ℂ))
    * ((Real.sqrt (1 - Complex.normSq (dstripD M W α τ) / 2) : ℝ) : ℂ)

/-- The map of the strip: first the band datum `M`, then the band quantity `A`. -/
def dstripG (M W : ℂ × ℝ → ℂ) (p : ℝ × ℝ) : ℂ × ℝ :=
  (M (dstripU p.1, p.2), dstripA M W p.1 p.2)

@[simp] lemma pcA_dstripU (M W : ℂ × ℝ → ℂ) (α τ : ℝ) :
    pcA M W (fun _ : ℂ => dstripU α) (fun _ : ℂ => τ) 0 = dstripA M W α τ := rfl

@[simp] lemma pcD_dstripU (M W : ℂ × ℝ → ℂ) (α τ : ℝ) :
    pcD M W (fun _ : ℂ => dstripU α) (fun _ : ℂ => τ) 0 = dstripD M W α τ := rfl

@[simp] lemma pcDc_dstripU (M W : ℂ × ℝ → ℂ) (α τ : ℝ) :
    pcDc M W (fun _ : ℂ => dstripU α) (fun _ : ℂ => τ) 0 = dstripDc M W α τ := rfl

lemma dstripG_periodic (M W : ℂ × ℝ → ℂ) (α τ : ℝ) :
    dstripG M W (α + 2 * Real.pi, τ) = dstripG M W (α, τ) := by
  have h := dstripU_add_two_pi α
  simp only [dstripG, Prod.mk.injEq, h, dstripA, true_and]

lemma contDiff_dstripG {M W : ℂ × ℝ → ℂ}
    (hMsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) M)
    (hWsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (dstripG M W) := by
  have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => M (dstripU p.1, p.2)) :=
    hMsm.comp ((contDiff_dstripU.comp contDiff_fst).prodMk contDiff_snd)
  have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => dstripA M W p.1 p.2) := by
    have hMn : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × ℝ => Complex.normSq (M (dstripU p.1, p.2))) :=
      Neutral.contDiff_complexNormSq.comp h1
    have hWn : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × ℝ => Complex.normSq (W (dstripU p.1, p.2))) :=
      Neutral.contDiff_complexNormSq.comp
        (hWsm.comp ((contDiff_dstripU.comp contDiff_fst).prodMk contDiff_snd))
    exact hMn.add (contDiff_snd.mul hWn)
  have hfun : dstripG M W = fun p : ℝ × ℝ =>
      ((fun p : ℝ × ℝ => M (dstripU p.1, p.2)) p,
        (fun p : ℝ × ℝ => dstripA M W p.1 p.2) p) := rfl
  rw [hfun]
  exact h1.prodMk h2

end

end Work.Drive
