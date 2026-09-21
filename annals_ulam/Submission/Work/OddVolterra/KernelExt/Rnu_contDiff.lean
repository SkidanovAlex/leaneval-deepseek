import Mathlib
import Submission.Work.OddVolterra.KernelExt.Defs

/-!
# Smoothness of the manifest Bell numerator `Rnu`

`Work.OddVolterra.KernelExt.Rnu ν h init m` is the polynomial
`(d/ds)^m[Z^ν · init] · Z^{m-ν}` attached to `Z = Zrad h`, defined by the recursion

`R_0 = init`,  `R_{m+1} = Z · ∂_s R_m + (ν - m) · (∂_s Z) · R_m`.

Since `ContDiff ℝ (⊤ : ℕ∞)` is closed under products, scalars, and — crucially — under
`fderiv` (a `C^∞` function has a `C^∞` derivative, *as a function of the base point*),
the recursion preserves smoothness: `Rnu ν h init m` is `C^∞` whenever `h` and `init` are.
-/

open scoped Topology ContDiff

namespace Work.OddVolterra.KernelExt

open Work.OddVolterra Work.OddVolterra.KernelExt

/-- A `C^∞` function on `ℝ × ℝ × ℝ` has a `C^∞` *directional* derivative in the first
coordinate, as a function of the base point. -/
theorem contDiff_fderiv_fst {F : ℝ × ℝ × ℝ → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
    ContDiff ℝ (⊤ : ℕ∞) fun p => (fderiv ℝ F p) (1, 0, 0) :=
  (hF.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

/-- `Zrad h` is smooth when `h` is. -/
theorem contDiff_Zrad {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) : ContDiff ℝ (⊤ : ℕ∞) (Zrad h) := by
  unfold Zrad line
  fun_prop

/-- **Smoothness of the recursive Bell numerator.** -/
theorem Rnu_contDiff (ν : ℝ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    {init : ℝ × ℝ × ℝ → ℝ} (hinit : ContDiff ℝ (⊤ : ℕ∞) init) (m : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (Work.OddVolterra.KernelExt.Rnu ν h init m) := by
  induction m with
  | zero => simpa [Rnu] using hinit
  | succ m ih =>
    rw [Rnu]
    have hZ := contDiff_Zrad hh
    have hdZ := contDiff_fderiv_fst hZ
    have hdR := contDiff_fderiv_fst ih
    fun_prop

end Work.OddVolterra.KernelExt
