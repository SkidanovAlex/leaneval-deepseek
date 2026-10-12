import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Submission.Work.BoseB4.integral_unitCell_cos_lattice
import Submission.Work.BoseB4.realIP_thetaExp_qVec
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB4.thetaExp_lattice` — the θ-mode orthogonality at lattice momenta

The θ-modes `ã_s = ℓ^{-3/2}a(Q(e^{isx}θ))` are orthonormal exactly when the
momenta run over the dual lattice `(2π/ℓ)ℤ³`.  For a `BoxData` whose cell *is* the
unit cube (the geometric content of FS's `χ_Λ = χ(x/ℓ)` on `Λ = [−ℓ/2,ℓ/2]³`),
and for the lattice momentum `s = ℓ⁻¹ • 2π n` (`n : Fin 3 → ℤ`),

    `⟨e^{isx}θ, θ⟩ = ℓ³ δ_{s,0}`,

i.e. `0` for `s ≠ 0` (the hypothesis `horthC` of
`Work.BoseB4.exists_gram_jointKernel`) and `ℓ³` for `s = 0` (which is `‖θ‖²`,
`Work.BoseB4.realIP_thetaFun_thetaFun`).  The proof is the change of variables
`x = ℓy` followed by the unit-cube Fourier orthogonality
`Work.BoseB4.integral_unitCell_cos_lattice`.

The general pair `⟨e^{isx}θ, e^{itx}θ⟩ = ℓ³δ_{st}` follows by the same argument
from `conj_thetaExp_mul_thetaExp_re` below; only the coordinate bookkeeping
`2π m − 2π n = 2π(m − n)` of the dual lattice is not packaged here.
-/

noncomputable section

open scoped BigOperators Pointwise
open MeasureTheory Classical

namespace Work.BoseB4

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- The dual-lattice momentum vector `2π n` of the unit cube. -/
noncomputable def vec (n : Fin 3 → ℤ) : ℝ³ :=
  WithLp.toLp 2 (fun i : Fin 3 => 2 * Real.pi * (n i : ℝ))

namespace BoxData

variable (B : BoxData)

/-- The integrand of `realIP (thetaExp ℓ s) (thetaExp ℓ t)`: the indicator of the
box times `cos⟪t−s,x⟫`. -/
lemma conj_thetaExp_mul_thetaExp_re (ℓ : ℝ) (s t : ℝ³) (x : ℝ³) :
    ((starRingEnd ℂ) (B.thetaExp ℓ s x) * B.thetaExp ℓ t x).re
      = Set.indicator (B.boxL ℓ) (fun x : ℝ³ => Real.cos (inner ℝ (t - s) x)) x := by
  by_cases hx : x ∈ B.boxL ℓ
  · rw [Set.indicator_of_mem hx]
    have h := modeVec_integrand_re (1 : ℝ) (inner ℝ s x) (inner ℝ t x)
    simp only [BoxData.thetaExp_apply, BoxData.thetaFun_apply, if_pos hx, one_pow, mul_one,
      Complex.ofReal_one] at h ⊢
    rw [h, inner_sub_left, one_mul]
  · have hθ : B.thetaFun ℓ x = 0 := by
      simp only [BoxData.thetaFun_apply, hx, if_false]
    rw [Set.indicator_of_notMem hx]
    simp only [BoxData.thetaExp_apply, hθ, mul_zero, map_zero, Complex.zero_re]

end BoxData

/-- **The θ-mode/condensate orthogonality at lattice momenta.**  For a `BoxData` on
FS's unit cube and the dual-lattice momentum `s = ℓ⁻¹ • 2πn`, the overlap of the
θ-mode with the condensate is `ℓ³` when `s = 0` and `0` otherwise — the identity
that makes the θ-modes orthonormal (the hypothesis `horthC` of
`Work.BoseB4.exists_gram_jointKernel`). -/
theorem realIP_thetaExp_thetaFun_of_cell (B : BoxData) (hcell : B.cell = unitCell)
    {ℓ : ℝ} (hℓ : 0 < ℓ) (n : Fin 3 → ℤ) :
    B.realIP (B.thetaExp ℓ (ℓ⁻¹ • vec n)) (B.thetaFun ℓ)
      = if n = 0 then ℓ ^ 3 else 0 := by
  have hℓ0 : ℓ ≠ 0 := ne_of_gt hℓ
  rw [BoxData.realIP_apply,
    show (fun x : ℝ³ => ((starRingEnd ℂ) (B.thetaExp ℓ (ℓ⁻¹ • vec n) x) * B.thetaFun ℓ x).re)
        = fun x : ℝ³ =>
            Set.indicator (B.boxL ℓ) (fun x : ℝ³ => Real.cos (inner ℝ (ℓ⁻¹ • vec n) x)) x from
      funext fun x => B.conj_thetaExp_mul_thetaFun_re ℓ (ℓ⁻¹ • vec n) x,
    MeasureTheory.integral_indicator (B.boxL_measurableSet ℓ), BoxData.boxL, hcell]
  have hsc := MeasureTheory.Measure.setIntegral_comp_smul_of_pos (μ := volume)
    (f := fun x : ℝ³ => Real.cos (inner ℝ (ℓ⁻¹ • vec n) x)) (s := unitCell) hℓ
  rw [finrank_euclideanSpace_fin] at hsc
  calc ∫ x in ℓ • unitCell, Real.cos (inner ℝ (ℓ⁻¹ • vec n) x)
      = ℓ ^ 3 * ∫ x in unitCell, Real.cos (inner ℝ (ℓ⁻¹ • vec n) (ℓ • x)) := by
        rw [hsc, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero 3 hℓ0), one_mul]
    _ = ℓ ^ 3 * ∫ x in unitCell, Real.cos (inner ℝ (vec n) x) := by
        congr 1
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        show Real.cos (inner ℝ (ℓ⁻¹ • vec n) (ℓ • x)) = Real.cos (inner ℝ (vec n) x)
        congr 1
        rw [real_inner_smul_right, real_inner_smul_left, ← mul_assoc, mul_inv_cancel₀ hℓ0,
          one_mul]
    _ = ℓ ^ 3 * (if n = 0 then 1 else 0) := by
        simp only [vec]
        rw [integral_unitCell_cos_lattice n]
    _ = if n = 0 then ℓ ^ 3 else 0 := by
        by_cases hn : n = 0
        · rw [if_pos hn, if_pos hn, mul_one]
        · rw [if_neg hn, if_neg hn, mul_zero]

end Work.BoseB4
