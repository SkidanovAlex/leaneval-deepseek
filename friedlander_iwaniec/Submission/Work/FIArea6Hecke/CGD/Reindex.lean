import Mathlib
import Submission.Work.FIArea6Hecke.ConductorGaussSumDefs

set_option autoImplicit false

namespace Work.FIArea6Hecke.CGD

open scoped BigOperators

/-- The box sum over `[0,N)²` is the nested sum over the two coordinates. -/
lemma boxSum_eq_double (N : ℕ) (f : GaussianInt → ℂ) :
    Work.FIArea6Hecke.R.boxSum N f =
      ∑ a ∈ Finset.range N, ∑ b ∈ Finset.range N, f (⟨(a : ℤ), (b : ℤ)⟩ : GaussianInt) := by
  unfold Work.FIArea6Hecke.R.boxSum Work.FIArea6Hecke.R.gbox
  rw [Finset.sum_image]
  · rw [Finset.product_eq_sprod, Finset.sum_product]
  · intro x _ y _ hxy
    exact Prod.ext (Int.ofNat.inj (congrArg Zsqrtd.re hxy))
      (Int.ofNat.inj (congrArg Zsqrtd.im hxy))

/-- `ekern M ξ` at the box point `⟨a,b⟩` is the exponential appearing in `condGaussSum`. -/
lemma ekern_box (M : GaussianInt) (ξ : GaussianInt) (a b : ℕ) :
    Work.FIArea6Hecke.R.ekern M ξ (⟨(a : ℤ), (b : ℤ)⟩ : GaussianInt) =
      Complex.exp (2 * Real.pi * Complex.I *
        (((((a : ℤ) * ξ.re + (b : ℤ) * ξ.im : ℤ)) : ℂ) / ((Work.FIPlan.gnorm M : ℕ) : ℂ))) := by
  rw [Work.FIArea6Hecke.R.ekern, Work.FIArea6Hecke.R.gdot]
  congr 1
  push_cast
  ring

theorem Reindex (M : GaussianInt) (chi : GaussianInt → ℂ) (ξ : GaussianInt) :
    Work.FIArea6Hecke.R.condGaussSum M chi ξ =
      Work.FIArea6Hecke.R.boxSum (Work.FIPlan.gnorm M)
        (fun s => chi s * Work.FIArea6Hecke.R.ekern M ξ s) := by
  rw [boxSum_eq_double]
  rw [Work.FIArea6Hecke.R.condGaussSum]
  apply Finset.sum_congr rfl
  intro a _ha
  apply Finset.sum_congr rfl
  intro b _hb
  rw [ekern_box M ξ a b]

end Work.FIArea6Hecke.CGD
