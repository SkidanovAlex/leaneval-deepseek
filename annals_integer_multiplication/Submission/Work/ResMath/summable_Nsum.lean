import Mathlib
import Submission.Work.ResMath.resE_defs
import Submission.Work.ResMath.summable_exp_neg_affine_sq

namespace Work.ResMath

open HvdH

/-- For fixed `j : Fin s`, the `q`-series defining the `(ℓ,j)` entry of `Nmat` is summable:
the summand is a constant times a Gaussian `exp (-(π α²) (t q + x)²)` in `q`. -/
lemma summable_Nsum_fiber (s t α : ℕ) (hs : 0 < s) (hst : s < t) (hα : 0 < α)
    (ℓ j : Fin s) (u : Fin s → ℂ) :
    Summable fun q : ℤ => Nsum s t α ℓ u j q := by
  have ht : 0 < t := by omega
  have ha : (0 : ℝ) < Real.pi * (α : ℝ) ^ 2 := by
    have : (0 : ℝ) < (α : ℝ) := by exact_mod_cast hα
    positivity
  set x : ℝ := (t : ℝ) * ((j : ℤ) - (ℓ : ℤ)) / (s : ℝ) + betaI s t (ℓ : ℤ) with hx
  set K : ℂ := ((Real.exp (Real.pi * (α : ℝ) ^ 2 * (betaR s t (j : ℕ)) ^ 2) : ℝ) : ℂ) * u j with hK
  have hbase : Summable fun q : ℤ =>
      ((Real.exp (-(Real.pi * (α : ℝ) ^ 2) * ((t : ℝ) * (q : ℝ) + x) ^ 2) : ℝ) : ℂ) :=
    (Complex.summable_ofReal).mpr (summable_exp_neg_affine_sq (Real.pi * (α : ℝ) ^ 2) x ha ht)
  have hKsum : Summable fun q : ℤ =>
      ((Real.exp (-(Real.pi * (α : ℝ) ^ 2) * ((t : ℝ) * (q : ℝ) + x) ^ 2) : ℝ) : ℂ) * K :=
    hbase.mul_right K
  refine hKsum.congr (fun q => ?_)
  have hA : Real.exp (-(Real.pi * (α : ℝ) ^ 2) * ((t : ℝ) * (q : ℝ) + x) ^ 2)
      = Real.exp (-(Real.pi * (α : ℝ) ^ 2
          * ((t : ℝ) * (q : ℝ) + (t : ℝ) * ((j : ℤ) - (ℓ : ℤ)) / (s : ℝ) + betaI s t (ℓ : ℤ)) ^ 2)) := by
    rw [hx]; congr 1; ring
  rw [Nsum, hK]
  conv_rhs => rw [mul_assoc]
  rw [hA]

/-- `Nsum` is summable over `Fin s × ℤ`. -/
theorem summable_Nsum (s t α : ℕ) (hs : 0 < s) (hst : s < t) (hα : 0 < α) (ℓ : Fin s) (u : Fin s → ℂ) :
    Summable fun p : Fin s × ℤ => Nsum s t α ℓ u p.1 p.2 := by
  have hprod : Summable fun p : Fin s × ℤ => ‖Nsum s t α ℓ u p.1 p.2‖ :=
    (summable_prod_of_nonneg (fun p => norm_nonneg _)).mpr
      ⟨fun j => (summable_Nsum_fiber s t α hs hst hα ℓ j u).norm, Summable.of_finite⟩
  exact hprod.of_norm

end Work.ResMath
