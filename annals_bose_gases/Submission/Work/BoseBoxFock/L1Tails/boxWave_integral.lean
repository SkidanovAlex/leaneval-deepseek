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

/-!
# `Work.BoseBoxFock.L1Tails.boxWave_integral` — lattice orthogonality of the plane waves

The box `boxL ℓ = ℓ • cell = [-ℓ/2, ℓ/2]³` of the corpus `Work.BoseK15.corpusBox` is a
fundamental domain of the dual lattice `κ_k = kappaL ℓ k = ℓ⁻¹ • vec k` (`vec k = (2π kᵢ)`), so
the plane waves `latWave κ x = e^{i⟪κ,x⟫}` satisfy the Kronecker orthogonality

    `∫_{boxL ℓ} e^{i⟪κ_k,x⟫} dx = ℓ³ · δ_{k,0}`,   (`k : Fin 3 → ℤ`)

the `(P1)` input of the `L¹`-weight tail chapter (the Dirichlet bound of `latticeDirichlet` /
`boxLatPoly_normSq`).

## Proof

The change of variables `x = ℓ y` (`Measure.setIntegral_comp_smul_of_pos`, `finrank ℝ E3 = 3`,
`boxL ℓ = ℓ • unitCell` definitionally) gives `ℓ³ ∫_{unitCell} e^{i⟪vec k,y⟫} dy`, and
`⟪ℓ⁻¹ • vec k, ℓ • y⟫ = ⟪vec k, y⟫` (`kappaL_eq`, `real_inner_smul_left/right`).  It remains to
evaluate the **complex** unit-cell integral, which factorises over the coordinates
(`ofLp_unitCell_integral` + `prod_integral_unitCube` + `Complex.exp_sum`) into
`∏ᵢ ∫_{-1/2}^{1/2} e^{2π i kᵢ t} dt = ∏ᵢ δ_{kᵢ,0}`, evaluated by `cos_lattice_1d`.

(The real-part version of the unit cell integral is `Work.BoseB4.integral_unitCell_cos_lattice`;
its helper lemmas are `private` there, so the ℂ-valued factorisation is redone here.)
-/

noncomputable section

open MeasureTheory
open scoped BigOperators Pointwise

namespace Work.BoseBoxFock.L1Tails

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The real inner product of a coordinate vector `WithLp.toLp 2 a` with `x` is the coordinate
sum `∑ i, a i * x i`. -/
private lemma inner_toLp_eq_sum (a : Fin 3 → ℝ) (y : E3) :
    inner ℝ (WithLp.toLp 2 a) y = ∑ i, a i * y.ofLp i := by
  rw [PiLp.inner_apply]
  simp [mul_comm]

/-- The coordinate plane wave factorises: `∏ᵢ e^{i aᵢ zᵢ} = e^{i ∑ᵢ aᵢ zᵢ}`. -/
private lemma prod_exp_eq_exp_sum (a : Fin 3 → ℝ) (z : Fin 3 → ℝ) :
    (∏ i, Complex.exp (Complex.I * ((a i * z i : ℝ) : ℂ)))
      = Complex.exp (Complex.I * ((∑ i, a i * z i : ℝ) : ℂ)) := by
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.mul_sum]

/-- **The complex unit-cell orthogonality, in frequency coordinates.**  For every frequency vector
`a : Fin 3 → ℝ`, the integral of `e^{i⟪a,x⟫}` over the unit cell `[-1/2,1/2]³` factorises into
the product of the one-dimensional integrals of the coordinate exponentials. -/
lemma integral_unitCell_exp (a : Fin 3 → ℝ) :
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
        simp only [inner_toLp_eq_sum]
    _ = ∫ z in Set.pi Set.univ (fun _ : Fin 3 => Set.Icc (-(1/2) : ℝ) (1/2)),
          Complex.exp (Complex.I * ((∑ i, a i * z i : ℝ) : ℂ)) := by
        rw [show Work.BoseB4.unitCell
            = {y : E3 | ∀ i, |y.ofLp i| ≤ (1/2 : ℝ)} from rfl]
        exact Work.BoseB4.ofLp_unitCell_integral (F := fun z : Fin 3 → ℝ =>
          Complex.exp (Complex.I * ((∑ i, a i * z i : ℝ) : ℂ)))
    _ = ∫ z in Set.pi Set.univ (fun _ : Fin 3 => Set.Icc (-(1/2) : ℝ) (1/2)),
          ∏ i, Complex.exp (Complex.I * ((a i * z i : ℝ) : ℂ)) := by
        apply setIntegral_congr_fun
          (MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Icc))
        intro z _
        simp only [prod_exp_eq_exp_sum]
    _ = ∏ i, ∫ t in Set.Icc (-(1/2) : ℝ) (1/2),
          Complex.exp (Complex.I * ((a i * t : ℝ) : ℂ)) :=
        Work.BoseB4.prod_integral_unitCube
          (fun i t => Complex.exp (Complex.I * ((a i * t : ℝ) : ℂ)))

/-- **The complex unit-cell orthogonality at lattice momenta:**
`∫_{unitCell} e^{i⟪vec k,x⟫} dx = δ_{k,0}`. -/
lemma integral_unitCell_exp_lattice (k : Fin 3 → ℤ) :
    ∫ y in Work.BoseB4.unitCell,
        Complex.exp (Complex.I * ((inner ℝ (Work.BoseB4.vec k) y : ℝ) : ℂ))
      = if k = 0 then 1 else 0 := by
  rw [show Work.BoseB4.vec k
      = WithLp.toLp 2 (fun i : Fin 3 => 2 * Real.pi * (k i : ℝ)) from rfl]
  rw [integral_unitCell_exp (fun i : Fin 3 => 2 * Real.pi * (k i : ℝ))]
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

/-- **Lattice orthogonality of the plane waves on the box `boxL ℓ = [-ℓ/2,ℓ/2]³`.**  For `ℓ > 0`
and a lattice label `k : Fin 3 → ℤ`, the integral of the character
`latWave (kappaL ℓ k) x = e^{i⟪κ_k,x⟫}`, `κ_k = ℓ⁻¹ • vec k`, over the box is `ℓ³` if `k = 0`
and `0` otherwise. -/
theorem boxWave_integral {ℓ : ℝ} (hℓ : 0 < ℓ) (k : Fin 3 → ℤ) :
    ∫ x in Work.BoseK15.corpusBox.boxL ℓ, Work.BoseBoxFock.L1Tails.latWave (Work.BoseBoxFock.kappaL ℓ k) x
      = if k = 0 then ((ℓ ^ 3 : ℝ) : ℂ) else 0 := by
  have hℓ0 : ℓ ≠ 0 := ne_of_gt hℓ
  -- The change of variables `x = ℓ y`: `boxL ℓ = ℓ • unitCell`.
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
        rw [integral_unitCell_exp_lattice k]
    _ = ((ℓ ^ 3 : ℝ) : ℂ) * (if k = 0 then 1 else 0) := by rw [Complex.real_smul]
    _ = if k = 0 then ((ℓ ^ 3 : ℝ) : ℂ) else 0 := by
        by_cases hk : k = 0 <;> simp [hk]

end Work.BoseBoxFock.L1Tails
