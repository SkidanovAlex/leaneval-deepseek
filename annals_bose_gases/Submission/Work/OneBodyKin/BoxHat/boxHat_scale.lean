import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Submission.Work.OneBodyKin.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The scaling law of the box Fourier profile `boxHat`

The box Fourier profile of `Submission.Work.OneBodyKin.Defs` is

  `boxHat ℓ q = ∫_{acube ℓ} cos⟪q,z⟫ dz`,

the (real) Fourier transform of the indicator of the centred cube `acube ℓ` of side `ℓ`.  Since
`acube ℓ = ℓ • acube 1` and `z ↦ ℓ • z` multiplies Lebesgue measure by `ℓ ^ 3` (`finrank ℝ ℝ³ = 3`),
the profile obeys the scaling law

  `boxHat ℓ q = ℓ ^ 3 * boxHat 1 (ℓ • q)`   (`ℓ > 0`),

proved here by the change of variables `z = ℓ • w` for the Bochner integral
(`MeasureTheory.Measure.setIntegral_comp_smul_of_pos`), together with the identity
`⟪q, ℓ • w⟫ = ⟪ℓ • q, w⟫` (`real_inner_smul_right`, `real_inner_smul_left`).

This is the change of variables used when comparing the symbol at scale `ℓ` with the
scale-free symbol at scale `1` (`SymBoundOne` in `OneBodyKin/Defs.lean`).
-/

open scoped Pointwise

namespace Work.OneBodyKin.BoxHat

open MeasureTheory

set_option maxHeartbeats 800000

/-- **Scaling of the centred cube.** For `ℓ > 0` the centred cube of side `ℓ` is the `ℓ`-dilate of
the unit centred cube, `ℓ • acube 1 = acube ℓ`. -/
lemma smul_acube_one {ℓ : ℝ} (hℓ : 0 < ℓ) :
    ℓ • Submission.BoseGases.acube 1 = Submission.BoseGases.acube ℓ := by
  ext y
  rw [Set.mem_smul_set]
  constructor
  · rintro ⟨x, hx, rfl⟩
    intro m
    have hxm := Set.mem_Icc.mp (hx m)
    rw [Set.mem_Icc]
    simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
    constructor <;> nlinarith [hxm.1, hxm.2, hℓ]
  · intro hy
    refine ⟨ℓ⁻¹ • y, ?_, ?_⟩
    · intro m
      have hym := Set.mem_Icc.mp (hy m)
      rw [Set.mem_Icc]
      simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
      have hinv : 0 < ℓ⁻¹ := inv_pos.2 hℓ
      have hmul : ℓ⁻¹ * ℓ = 1 := inv_mul_cancel₀ hℓ.ne'
      constructor <;> nlinarith [hym.1, hym.2, hℓ, hinv, hmul]
    · rw [smul_inv_smul₀ hℓ.ne']

/-- **The scaling law of the box profile**: `boxHat ℓ q = ℓ³ · boxHat 1 (ℓ • q)` for `ℓ > 0`. -/
theorem boxHat_scale {ℓ : ℝ} (hℓ : 0 < ℓ) (q : EuclideanSpace ℝ (Fin 3)) :
    Work.OneBodyKin.boxHat ℓ q = ℓ ^ 3 * Work.OneBodyKin.boxHat 1 (ℓ • q) := by
  -- The change of variables `z = ℓ • w` in the defining integral.
  have key : (∫ w in Submission.BoseGases.acube 1, Real.cos (inner ℝ q (ℓ • w)))
      = (ℓ ^ 3)⁻¹ * ∫ z in Submission.BoseGases.acube ℓ, Real.cos (inner ℝ q z) := by
    have h := MeasureTheory.Measure.setIntegral_comp_smul_of_pos
      (μ := (volume : Measure (EuclideanSpace ℝ (Fin 3))))
      (f := fun y : EuclideanSpace ℝ (Fin 3) => Real.cos (inner ℝ q y))
      (R := ℓ) (s := Submission.BoseGases.acube 1) hℓ
    rw [finrank_euclideanSpace_fin, smul_acube_one hℓ, smul_eq_mul] at h
    exact h
  -- `⟪q, ℓ • w⟫ = ⟪ℓ • q, w⟫`, so the two integrands over `acube 1` agree.
  have hcongr : (∫ w in Submission.BoseGases.acube 1, Real.cos (inner ℝ q (ℓ • w)))
      = ∫ w in Submission.BoseGases.acube 1, Real.cos (inner ℝ (ℓ • q) w) := by
    refine MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.acube_measurable 1) ?_
    intro w _
    show Real.cos (inner ℝ q (ℓ • w)) = Real.cos (inner ℝ (ℓ • q) w)
    congr 1
    rw [real_inner_smul_right, real_inner_smul_left]
  have hkey : (∫ w in Submission.BoseGases.acube 1, Real.cos (inner ℝ (ℓ • q) w))
      = (ℓ ^ 3)⁻¹ * ∫ z in Submission.BoseGases.acube ℓ, Real.cos (inner ℝ q z) :=
    hcongr ▸ key
  unfold Work.OneBodyKin.boxHat
  rw [hkey, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero 3 hℓ.ne'), one_mul]

end Work.OneBodyKin.BoxHat
