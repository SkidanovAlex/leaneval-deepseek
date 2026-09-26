import Mathlib
import Submission.Work.Lattice.poissonBasics
import Submission.Work.Lattice.integral_eq_tsum_intVec

namespace Work.Lattice

open MeasureTheory Set
open scoped Pointwise

theorem summable_integral_norm_schwartz_add_intVec {n : ℕ}
    (g : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ) :
    Summable fun v : Fin n → ℤ =>
      ∫ x in Work.Lattice.unitCube n, ‖g (WithLp.toLp 2 (x + Work.Lattice.intVecToReal v))‖ := by
  classical
  have hint : Integrable (fun y : Fin n → ℝ => ‖g (WithLp.toLp 2 y)‖)
      (volume : Measure (Fin n → ℝ)) := by
    have hmp := PiLp.volume_preserving_toLp (Fin n)
    have hg : Integrable (g : EuclideanSpace ℝ (Fin n) → ℂ) volume :=
      SchwartzMap.integrable (μ := volume) g
    exact ((hmp.integrable_comp (g.continuous.aestronglyMeasurable)).2 hg).norm
  have hfd : IsAddFundamentalDomain (intVec n) (unitCube n) (volume : Measure (Fin n → ℝ)) :=
    isAddFundamentalDomain_unitCube n
  have key : (∑' w : intVec n, ∫⁻ x in unitCube n,
        ENNReal.ofReal ‖g (WithLp.toLp 2 (w +ᵥ x))‖)
      = ENNReal.ofReal (∫ y, ‖g (WithLp.toLp 2 y)‖) := by
    rw [← hfd.lintegral_eq_tsum'' (fun y => ENNReal.ofReal ‖g (WithLp.toLp 2 y)‖)]
    exact (ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun y => norm_nonneg _)).symm
  have summand : ∀ v : Fin n → ℤ,
      (∫⁻ x in unitCube n, ENNReal.ofReal ‖g (WithLp.toLp 2 (x + intVecToReal v))‖)
        = ENNReal.ofReal (∫ x in unitCube n, ‖g (WithLp.toLp 2 (x + intVecToReal v))‖) := by
    intro v
    exact (ofReal_integral_eq_lintegral_ofReal
      ((hint.comp_add_right (intVecToReal v)).integrableOn)
      (ae_of_all _ fun y => norm_nonneg _)).symm
  have hA : (∑' v : Fin n → ℤ, ∫⁻ x in unitCube n,
        ENNReal.ofReal ‖g (WithLp.toLp 2 ((intVecEquiv n v) +ᵥ x))‖)
      = ENNReal.ofReal (∫ y, ‖g (WithLp.toLp 2 y)‖) :=
    (Equiv.tsum_eq (intVecEquiv n) (fun w : intVec n => ∫⁻ x in unitCube n,
        ENNReal.ofReal ‖g (WithLp.toLp 2 (w +ᵥ x))‖)).trans key
  have h1 : (∑' v : Fin n → ℤ,
        ENNReal.ofReal (∫ x in unitCube n, ‖g (WithLp.toLp 2 (x + intVecToReal v))‖))
      = ENNReal.ofReal (∫ y, ‖g (WithLp.toLp 2 y)‖) := by
    have h2 : (∑' v : Fin n → ℤ,
          ENNReal.ofReal (∫ x in unitCube n, ‖g (WithLp.toLp 2 (x + intVecToReal v))‖))
        = ∑' v : Fin n → ℤ, ∫⁻ x in unitCube n,
            ENNReal.ofReal ‖g (WithLp.toLp 2 ((intVecEquiv n v) +ᵥ x))‖ := by
      refine tsum_congr fun v => ?_
      simp only [intVecEquiv_vadd]
      exact (summand v).symm
    rw [h2]; exact hA
  have hne : (∑' v : Fin n → ℤ,
        ENNReal.ofReal (∫ x in unitCube n, ‖g (WithLp.toLp 2 (x + intVecToReal v))‖))
        ≠ (⊤ : ENNReal) := by
    rw [h1]; exact ENNReal.ofReal_ne_top
  have hnn : Summable fun v : Fin n → ℤ =>
      ((Real.toNNReal (∫ x in unitCube n, ‖g (WithLp.toLp 2 (x + intVecToReal v))‖) : NNReal) : ℝ) := by
    apply ENNReal.tsum_coe_ne_top_iff_summable_coe.mp
    simpa only [ENNReal.ofReal] using hne
  refine hnn.congr fun v => ?_
  rw [Real.coe_toNNReal']
  exact max_eq_left (integral_nonneg fun x => norm_nonneg _)

end Work.Lattice
