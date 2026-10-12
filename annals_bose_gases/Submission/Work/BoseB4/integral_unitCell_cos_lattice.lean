import Mathlib.Tactic.Have
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Submission.Work.BoseB4.cos_lattice_1d
import Submission.Work.BoseB4.exists_boxData
import Submission.Work.BoseB4.ofLp_unitCell_integral
import Submission.Work.BoseB4.prod_integral_unitCube
import Submission.Work.BoseB4.setIntegral_re
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB4.integral_unitCell_cos_lattice`

Lattice orthogonality of plane waves on FS's unit cell `[-1/2,1/2]³`: for `n : Fin 3 → ℤ`,

```
∫_{unitCell} cos ⟪2π n, x⟫ dx = if n = 0 then 1 else 0 .
```

This is the standard "Kronecker delta" for the characters `x ↦ e^{2πi n·x}` of the unit
torus: the integral factorises into a product of one-dimensional integrals of
`t ↦ e^{2πi nᵢ t}` over `[-1/2,1/2]`, each of which vanishes unless `nᵢ = 0`.

## The proof, in three steps

* `cos_lattice_1d` (delegated): `∫_{-1/2}^{1/2} e^{2πi m t} dt = δ_{m,0}` for `m : ℤ`.
* `prod_integral_unitCube` (delegated): the integral of a product `∏ᵢ hᵢ(yᵢ)` over the
  coordinate box `∏ᵢ [-1/2,1/2]` is the product of the one-dimensional integrals
  (`Measure.pi` + `MeasureTheory.integral_fintype_prod_eq_prod`).
* `ofLp_unitCell_integral` (delegated): transport of a set integral over the unit cell in
  `EuclideanSpace ℝ (Fin 3)` to the coordinate box in `Fin 3 → ℝ` along the
  volume-preserving `WithLp.ofLp`.

The real cosine is written as the real part of `exp (i ⟪·,x⟫)` (`re_exp_mul_I`), the
exponential of the inner product is turned into the product of the coordinate
exponentials (`prod_exp_eq`, via `Complex.exp_sum`), and the real part is pulled out of
the integral with `MeasureTheory.integral_re` (`setIntegral_re`).
-/

noncomputable section

open scoped BigOperators Pointwise
open MeasureTheory Classical

namespace Work.BoseB4

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- The real inner product of `WithLp.toLp 2 a` with `x` is `∑ i, a i * x i`. -/
private lemma inner_toLp_apply (a : Fin 3 → ℝ) (x : ℝ³) :
    inner ℝ (WithLp.toLp 2 a) x = ∑ i, a i * x.ofLp i := by
  rw [PiLp.inner_apply]
  simp [mul_comm]

/-- `cos θ` is the real part of `exp (i θ)`. -/
private lemma re_exp_mul_I (r : ℝ) :
    (Complex.exp (Complex.I * (r : ℂ))).re = Real.cos r := by
  rw [mul_comm, Complex.exp_mul_I, Complex.add_re, Complex.mul_I_re, ← Complex.ofReal_sin,
    Complex.ofReal_im, neg_zero, add_zero, ← Complex.ofReal_cos, Complex.ofReal_re]

/-- `exp` of a sum is the product of the exponentials: the additivity that makes the
plane waves factorise over the coordinates. -/
private lemma prod_exp_eq (a : Fin 3 → ℝ) (y : Fin 3 → ℝ) :
    (∏ i, Complex.exp (Complex.I * (a i * y i)))
      = Complex.exp (Complex.I * (∑ i, a i * y i)) := by
  rw [← Complex.exp_sum Finset.univ (fun i => Complex.I * ((a i : ℂ) * (y i : ℂ)))]
  congr 1
  push_cast
  rw [← Finset.mul_sum]

/-- **The orthogonality integral on the unit cell, in frequency coordinates.**  For every
frequency vector `a : Fin 3 → ℝ`,

```
∫_{unitCell} cos ⟪a,x⟫ dx = Re ∏ᵢ ∫_{-1/2}^{1/2} e^{i aᵢ t} dt .
```

The right-hand side keeps `aᵢ` rather than `2π aᵢ`, so that the lemma is stated for an
arbitrary frequency vector; the target specialises `aᵢ = 2π nᵢ`. -/
private lemma integral_unitCell_cos (a : Fin 3 → ℝ) :
    ∫ x in unitCell, Real.cos (inner ℝ (WithLp.toLp 2 a) x)
      = (∏ i, ∫ t in Set.Icc (-(1/2) : ℝ) (1/2),
          Complex.exp (Complex.I * (a i * t))).re := by
  have hcont : Continuous (fun x : ℝ³ =>
      Complex.exp (Complex.I * (inner ℝ (WithLp.toLp 2 a) x))) := by fun_prop
  have hFint : IntegrableOn (fun x : ℝ³ =>
      Complex.exp (Complex.I * (inner ℝ (WithLp.toLp 2 a) x))) unitCell volume :=
    hcont.continuousOn.integrableOn_compact isCompact_unitCell
  calc ∫ x in unitCell, Real.cos (inner ℝ (WithLp.toLp 2 a) x)
      = ∫ x in unitCell, (Complex.exp (Complex.I * (inner ℝ (WithLp.toLp 2 a) x))).re := by
          apply setIntegral_congr_fun isClosed_unitCell.measurableSet
          intro x _
          exact (re_exp_mul_I _).symm
    _ = (∫ x in unitCell, Complex.exp (Complex.I * (inner ℝ (WithLp.toLp 2 a) x))).re :=
          setIntegral_re isClosed_unitCell.measurableSet _ hFint
    _ = (∫ y in Set.pi Set.univ (fun _ : Fin 3 => Set.Icc (-(1/2) : ℝ) (1/2)),
            (∏ i, Complex.exp (Complex.I * (a i * y i)))).re := by
          congr 1
          calc ∫ x in unitCell, Complex.exp (Complex.I * (inner ℝ (WithLp.toLp 2 a) x))
              = ∫ x in unitCell, Complex.exp (Complex.I * (∑ i, a i * x.ofLp i)) := by
                apply setIntegral_congr_fun isClosed_unitCell.measurableSet
                intro x _
                simp only [inner_toLp_apply]
            _ = ∫ y in Set.pi Set.univ (fun _ : Fin 3 => Set.Icc (-(1/2) : ℝ) (1/2)),
                  Complex.exp (Complex.I * (∑ i, a i * y i)) := by
                rw [show unitCell = {x : ℝ³ | ∀ i, |x i| ≤ (1/2 : ℝ)} from rfl]
                exact ofLp_unitCell_integral (F := fun y : Fin 3 → ℝ =>
                  Complex.exp (Complex.I * (∑ i, a i * y i)))
            _ = ∫ y in Set.pi Set.univ (fun _ : Fin 3 => Set.Icc (-(1/2) : ℝ) (1/2)),
                  (∏ i, Complex.exp (Complex.I * (a i * y i))) := by
                apply setIntegral_congr_fun
                  (MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Icc))
                intro y _
                exact (prod_exp_eq a y).symm
    _ = (∏ i, ∫ t in Set.Icc (-(1/2) : ℝ) (1/2),
            Complex.exp (Complex.I * (a i * t))).re := by
          congr 1
          exact prod_integral_unitCube (fun i t => Complex.exp (Complex.I * (a i * t)))

/-- **Lattice orthogonality of the plane waves on the unit cell.**  For a lattice vector
`n : Fin 3 → ℤ`, the integral of `cos ⟪2π n, x⟫` over the unit cell is the Kronecker
delta `δ_{n,0}`. -/
theorem integral_unitCell_cos_lattice (n : Fin 3 → ℤ) :
    ∫ x in Work.BoseB4.unitCell,
        Real.cos (inner ℝ (WithLp.toLp 2 (fun i : Fin 3 => 2 * Real.pi * (n i : ℝ))) x)
      = if n = 0 then 1 else 0 := by
  rw [integral_unitCell_cos (fun i : Fin 3 => 2 * Real.pi * (n i : ℝ))]
  -- Evaluate the one-dimensional factors.
  have hprod1 : (∏ i : Fin 3, (∫ t in Set.Icc (-(1/2) : ℝ) (1/2),
        Complex.exp (Complex.I * (((2 * Real.pi * (n i : ℝ) : ℝ) : ℂ) * (t : ℂ)))))
      = ∏ i : Fin 3, (if n i = 0 then (1 : ℂ) else 0) := by
    apply Finset.prod_congr rfl
    intro i _
    have hpoint : ∀ t : ℝ,
        Complex.exp (Complex.I * (((2 * Real.pi * (n i : ℝ) : ℝ) : ℂ) * (t : ℂ)))
          = Complex.exp (Complex.I * ((2 * Real.pi * (n i : ℝ)) * t)) := by
      intro t
      congr 1
      push_cast
      ring
    rw [setIntegral_congr_fun measurableSet_Icc (fun t _ => hpoint t)]
    exact cos_lattice_1d (n i)
  rw [hprod1]
  -- Rewrite the complex product of `0`/`1` factors through `ℂ.ofReal`.
  have hprod : (∏ i : Fin 3, (if n i = 0 then (1 : ℂ) else 0))
      = Complex.ofReal (∏ i : Fin 3, (if n i = 0 then (1 : ℝ) else 0)) := by
    rw [Complex.ofReal_prod]
    apply Finset.prod_congr rfl
    intro i _
    by_cases h : n i = 0 <;> simp [h]
  rw [hprod, Complex.ofReal_re]
  -- The product of the `0`/`1` factors is `1` exactly when all coordinates vanish.
  have hlast : (∏ i : Fin 3, (if n i = 0 then (1 : ℝ) else 0))
      = (if n = 0 then (1 : ℝ) else 0) := by
    by_cases hn : n = 0
    · subst hn; simp
    · rw [if_neg hn]
      obtain ⟨i, hi⟩ : ∃ i : Fin 3, n i ≠ 0 := by
        by_contra h; push Not at h; exact hn (funext h)
      exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)
  rw [hlast]

end Work.BoseB4
