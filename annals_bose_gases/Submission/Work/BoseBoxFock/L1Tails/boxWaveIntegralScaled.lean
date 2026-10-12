import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Submission.Work.BoseBoxFock.L1Tails.latDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock.L1Tails

open MeasureTheory
open scoped BigOperators Pointwise

/-! ## The `ℂ`-valued unit-cell orthogonality (local, `private` helpers)

The helpers below rebuild — in this file, under `private` names — the `ℂ`-valued factorisation of
the unit-cell integral that the (private) `Work.BoseB4.integral_unitCell_cos` performs for the
*real* part.  They are `private` so that this module can be imported side by side with
`Submission.Work.BoseBoxFock.L1Tails.boxWave_integral` (which carries public versions of the same
two statements) without a duplicate-declaration clash.
-/

/-- The real inner product of a coordinate vector `WithLp.toLp 2 a` with `y` is the coordinate
sum `∑ i, a i * y i`. -/
private lemma inner_toLp_eq_sum_wave (a : Fin 3 → ℝ) (y : EuclideanSpace ℝ (Fin 3)) :
    inner ℝ (WithLp.toLp 2 a) y = ∑ i, a i * y.ofLp i := by
  rw [PiLp.inner_apply]
  simp [mul_comm]

/-- The coordinate plane waves factorise: `∏ᵢ e^{i aᵢ zᵢ} = e^{i ∑ᵢ aᵢ zᵢ}`. -/
private lemma prod_exp_eq_exp_sum_wave (a : Fin 3 → ℝ) (z : Fin 3 → ℝ) :
    (∏ i, Complex.exp (Complex.I * ((a i * z i : ℝ) : ℂ)))
      = Complex.exp (Complex.I * ((∑ i, a i * z i : ℝ) : ℂ)) := by
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.mul_sum]

/-- **The complex unit-cell orthogonality, in frequency coordinates.**  For every frequency vector
`a : Fin 3 → ℝ`, the integral of `e^{i⟪a,x⟫}` over the unit cell `[-1/2,1/2]³` factorises into
the product of the one-dimensional integrals of the coordinate exponentials. -/
private lemma integral_unitCell_exp_wave (a : Fin 3 → ℝ) :
    ∫ y in Work.BoseB4.unitCell,
        Complex.exp (Complex.I * ((inner ℝ (WithLp.toLp 2 a) y : ℝ) : ℂ))
      = ∏ i, ∫ t in Set.Icc (-(1/2) : ℝ) (1/2),
          Complex.exp (Complex.I * ((a i * t : ℝ) : ℂ)) := by
  calc ∫ y in Work.BoseB4.unitCell,
        Complex.exp (Complex.I * ((inner ℝ (WithLp.toLp 2 a) y : ℝ) : ℂ))
      = ∫ y in Work.BoseB4.unitCell,
          Complex.exp (Complex.I * ((∑ i, a i * y.ofLp i : ℝ) : ℂ)) := by
        apply setIntegral_congr_fun Work.BoseB4.isClosed_unitCell.measurableSet
        intro y _
        simp only [inner_toLp_eq_sum_wave]
    _ = ∫ z in Set.pi Set.univ (fun _ : Fin 3 => Set.Icc (-(1/2) : ℝ) (1/2)),
          Complex.exp (Complex.I * ((∑ i, a i * z i : ℝ) : ℂ)) := by
        rw [show Work.BoseB4.unitCell
            = {y : EuclideanSpace ℝ (Fin 3) | ∀ i, |y.ofLp i| ≤ (1/2 : ℝ)} from rfl]
        exact Work.BoseB4.ofLp_unitCell_integral (F := fun z : Fin 3 → ℝ =>
          Complex.exp (Complex.I * ((∑ i, a i * z i : ℝ) : ℂ)))
    _ = ∫ z in Set.pi Set.univ (fun _ : Fin 3 => Set.Icc (-(1/2) : ℝ) (1/2)),
          ∏ i, Complex.exp (Complex.I * ((a i * z i : ℝ) : ℂ)) := by
        apply setIntegral_congr_fun
          (MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Icc))
        intro z _
        simp only [prod_exp_eq_exp_sum_wave]
    _ = ∏ i, ∫ t in Set.Icc (-(1/2) : ℝ) (1/2),
          Complex.exp (Complex.I * ((a i * t : ℝ) : ℂ)) :=
        Work.BoseB4.prod_integral_unitCube
          (fun i t => Complex.exp (Complex.I * ((a i * t : ℝ) : ℂ)))

/-- **The complex unit-cell orthogonality at lattice momenta:**
`∫_{unitCell} e^{i⟪vec k,x⟫} dx = δ_{k,0}`. -/
private lemma integral_unitCell_exp_lattice_wave (k : Fin 3 → ℤ) :
    ∫ y in Work.BoseB4.unitCell,
        Complex.exp (Complex.I * ((inner ℝ (Work.BoseB4.vec k) y : ℝ) : ℂ))
      = if k = 0 then 1 else 0 := by
  rw [show Work.BoseB4.vec k
      = WithLp.toLp 2 (fun i : Fin 3 => 2 * Real.pi * (k i : ℝ)) from rfl]
  rw [integral_unitCell_exp_wave (fun i : Fin 3 => 2 * Real.pi * (k i : ℝ))]
  have hfac : ∀ i : Fin 3,
      (∫ t in Set.Icc (-(1/2) : ℝ) (1/2),
          Complex.exp (Complex.I * (((2 * Real.pi * (k i : ℝ)) * t : ℝ) : ℂ)))
        = (if k i = 0 then (1 : ℂ) else 0) := by
    intro i
    have hpoint : ∀ t : ℝ,
        Complex.exp (Complex.I * (((2 * Real.pi * (k i : ℝ)) * t : ℝ) : ℂ))
          = Complex.exp (Complex.I * ((2 * Real.pi * (k i : ℝ)) * (t : ℂ))) := by
      intro t
      congr 1
      push_cast
      ring
    rw [setIntegral_congr_fun measurableSet_Icc (fun t _ => hpoint t)]
    exact Work.BoseB4.cos_lattice_1d (k i)
  rw [Finset.prod_congr rfl (fun i _ => hfac i)]
  by_cases hk : k = 0
  · subst hk; simp
  · rw [if_neg hk]
    obtain ⟨i, hi⟩ : ∃ i : Fin 3, k i ≠ 0 := by
      by_contra h
      push Not at h
      exact hk (funext h)
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

/-- Lattice orthogonality of the plane waves over the box `boxL ℓ = ℓ • unitCell = [-ℓ/2,ℓ/2]³`:
`∫_{boxL ℓ} e^{i⟪κ_k,x⟫} dx = ℓ³` if `k = 0` and `0` otherwise, where `κ_k = kappaL ℓ k = ℓ⁻¹ • vec k`
and `latWave v x = exp (I * (inner ℝ v x))`.

This is the scaled-box version of the PROVED `Work.BoseB4.integral_unitCell_cos_lattice`.  It is the
`(P1)` input of `boxLatPoly_normSq` and `boxLatPoly_deriv_normSq` of the `L¹`-weight tail chapter.
(NB: `Submission/Work/BoseBoxFock/L1Tails/boxWave_integral.lean` states the same lemma, but it is
still `sorry` there and `boxLatPoly_normSq` must not depend on it.)

Proof hints: `boxL ℓ = ℓ • unitCell` by `rfl` (both are `Work.BoseB4.unitCell`), so
`MeasureTheory.Measure.setIntegral_comp_smul_of_pos` (`R := ℓ`, `s := unitCell`, `E := E3`, with
`finrank_euclideanSpace_fin`) gives `∫_{boxL ℓ} f = ℓ ^ 3 • ∫_{unitCell} f (ℓ • ·)`.  Then
`f (ℓ • x) = exp (I * ⟪vec k, x⟫)` (`real_inner_smul_left`, `kappaL_eq`, `smul_smul`,
`inv_smul_smul₀`), and the unit-cell integral factorises as in the proof of the (private)
`Work.BoseB4.integral_unitCell_cos` but without the `.re` step: use the general-value
`Work.BoseB4.ofLp_unitCell_integral` (it works for any normed space, in particular `ℂ`) and
`Work.BoseB4.prod_integral_unitCube` for the product of the one-dimensional factors, and evaluate
each factor with the PROVED `Work.BoseB4.cos_lattice_1d`.  (The ℂ-valued version of
`integral_unitCell_cos` must be rebuilt: it needs `PiLp.inner_apply` and `Complex.exp_sum`.) -/
theorem boxWaveIntegralScaled {ℓ : ℝ} (hℓ : 0 < ℓ) (k : Fin 3 → ℤ) :
    ∫ x in Work.BoseK15.corpusBox.boxL ℓ,
        Work.BoseBoxFock.L1Tails.latWave (Work.BoseBoxFock.kappaL ℓ k) x
      = if k = 0 then ((ℓ ^ 3 : ℝ) : ℂ) else 0 := by
  have hℓ0 : ℓ ≠ 0 := ne_of_gt hℓ
  -- The change of variables `x = ℓ y`: `boxL ℓ = ℓ • unitCell` definitionally.
  have hsc := MeasureTheory.Measure.setIntegral_comp_smul_of_pos (μ := volume)
    (f := latWave (kappaL ℓ k)) (s := Work.BoseB4.unitCell) hℓ
  rw [finrank_euclideanSpace_fin] at hsc
  have hmul : ℓ ^ 3 • (∫ y in Work.BoseB4.unitCell, latWave (kappaL ℓ k) (ℓ • y))
      = ∫ x in ℓ • Work.BoseB4.unitCell, latWave (kappaL ℓ k) x := by
    rw [hsc, smul_smul, mul_inv_cancel₀ (pow_ne_zero 3 hℓ0), one_smul]
  rw [show Work.BoseK15.corpusBox.boxL ℓ = ℓ • Work.BoseB4.unitCell from rfl]
  calc ∫ x in ℓ • Work.BoseB4.unitCell, latWave (kappaL ℓ k) x
      = ℓ ^ 3 • ∫ y in Work.BoseB4.unitCell, latWave (kappaL ℓ k) (ℓ • y) := hmul.symm
    -- `⟪ℓ⁻¹ • vec k, ℓ • y⟫ = ⟪vec k, y⟫`: the integrand is the lattice character of `unitCell`.
    _ = ℓ ^ 3 • ∫ y in Work.BoseB4.unitCell,
          Complex.exp (Complex.I * ((inner ℝ (Work.BoseB4.vec k) y : ℝ) : ℂ)) := by
        congr 1
        apply setIntegral_congr_fun Work.BoseB4.isClosed_unitCell.measurableSet
        intro y _
        simp only [latWave, kappaL_eq]
        congr 1
        rw [real_inner_smul_left, real_inner_smul_right, ← mul_assoc, inv_mul_cancel₀ hℓ0, one_mul]
    _ = ℓ ^ 3 • (if k = 0 then 1 else 0) := by
        rw [integral_unitCell_exp_lattice_wave k]
    _ = ((ℓ ^ 3 : ℝ) : ℂ) * (if k = 0 then 1 else 0) := by rw [Complex.real_smul]
    _ = if k = 0 then ((ℓ ^ 3 : ℝ) : ℂ) else 0 := by
        by_cases hk : k = 0 <;> simp [hk]

end Work.BoseBoxFock.L1Tails
