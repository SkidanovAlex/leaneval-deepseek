import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.moment_ibp

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov

open MeasureTheory Set Filter
open scoped Topology

theorem ibpZZ (σ φ : ℝ → ℝ) (hσ : ContDiffOn ℝ 2 σ (Set.Ioi 0)) (hφ : ContDiffOn ℝ 2 φ (Set.Ioi 0)) (hi1 : MeasureTheory.IntegrableOn (fun z => z ^ 2 * σ z * φ z * deriv (deriv φ) z) (Set.Ioi 0)) (hi2 : MeasureTheory.IntegrableOn (fun z => deriv (fun z => z ^ 2 * σ z) z * φ z * deriv φ z) (Set.Ioi 0)) (hi3 : MeasureTheory.IntegrableOn (fun z => σ z * (z * deriv φ z) ^ 2) (Set.Ioi 0)) (hi4 : MeasureTheory.IntegrableOn (fun z => deriv (deriv (fun z => z ^ 2 * σ z)) z * (φ z) ^ 2) (Set.Ioi 0)) (h0 : Filter.Tendsto (fun z => z ^ 2 * σ z * φ z * deriv φ z) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0)) (hT : Filter.Tendsto (fun z => z ^ 2 * σ z * φ z * deriv φ z) Filter.atTop (nhds 0)) (hb0 : Filter.Tendsto (fun z => deriv (fun z => z ^ 2 * σ z) z * (φ z) ^ 2) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0)) (hbT : Filter.Tendsto (fun z => deriv (fun z => z ^ 2 * σ z) z * (φ z) ^ 2) Filter.atTop (nhds 0)) : (∫ z in Set.Ioi 0, σ z * z ^ 2 * deriv (deriv φ) z * φ z) = (1 / 2) * (∫ z in Set.Ioi 0, deriv (deriv (fun z => z ^ 2 * σ z)) z * (φ z) ^ 2) - (∫ z in Set.Ioi 0, σ z * (z * deriv φ z) ^ 2) := by
  -- ### Differentiability of the weight `w = z²σ` and of `φ`
  have hw2 : ContDiffOn ℝ 2 (fun z : ℝ => z ^ 2 * σ z) (Set.Ioi 0) :=
    ContDiffOn.mul (by fun_prop) hσ
  have hw1 : ContDiffOn ℝ 1 (deriv (fun z : ℝ => z ^ 2 * σ z)) (Set.Ioi 0) :=
    hw2.deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hF : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun z : ℝ => z ^ 2 * σ z) (deriv (fun z : ℝ => z ^ 2 * σ z) z) z := by
    intro z hz
    exact (hw2.differentiableOn (by norm_num)).hasDerivAt (isOpen_Ioi.mem_nhds hz)
  have hF' : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (deriv (fun z : ℝ => z ^ 2 * σ z))
        (deriv (deriv (fun z : ℝ => z ^ 2 * σ z)) z) z := by
    intro z hz
    exact (hw1.differentiableOn (by norm_num)).hasDerivAt (isOpen_Ioi.mem_nhds hz)
  have hφd : ∀ z ∈ Set.Ioi (0 : ℝ), HasDerivAt φ (deriv φ z) z := by
    intro z hz
    exact (hφ.differentiableOn (by norm_num)).hasDerivAt (isOpen_Ioi.mem_nhds hz)
  have hφd' : ∀ z ∈ Set.Ioi (0 : ℝ), HasDerivAt (deriv φ) (deriv (deriv φ) z) z := by
    have h1 : ContDiffOn ℝ 1 (deriv φ) (Set.Ioi 0) := hφ.deriv_of_isOpen isOpen_Ioi (by norm_num)
    intro z hz
    exact (h1.differentiableOn (by norm_num)).hasDerivAt (isOpen_Ioi.mem_nhds hz)
  have hH : ∀ z ∈ Set.Ioi (0 : ℝ), HasDerivAt (fun z => (φ z) ^ 2) (2 * φ z * deriv φ z) z := by
    intro z hz
    convert (hφd z hz).pow 2 using 1
    simp [pow_one, mul_assoc]
  have hH' : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun z => 2 * φ z * deriv φ z)
        (2 * (deriv φ z * deriv φ z + φ z * deriv (deriv φ) z)) z := by
    intro z hz
    convert ((hφd z hz).mul (hφd' z hz)).const_mul 2 using 1; simp [mul_assoc]
  -- ### Integrability and boundary conditions
  have hI1 : IntegrableOn
      (fun z => (z ^ 2 * σ z) * (2 * (deriv φ z * deriv φ z + φ z * deriv (deriv φ) z)))
      (Set.Ioi 0) := by
    have hA : IntegrableOn (fun z => 2 * (σ z * (z * deriv φ z) ^ 2)) (Set.Ioi 0) := hi3.const_mul 2
    have hB : IntegrableOn (fun z => 2 * (z ^ 2 * σ z * φ z * deriv (deriv φ) z)) (Set.Ioi 0) :=
      hi1.const_mul 2
    refine (hA.add hB).congr_fun ?_ measurableSet_Ioi
    intro z _
    simp only [Pi.add_apply]; ring
  have hI2 : IntegrableOn (fun z => deriv (fun z => z ^ 2 * σ z) z * (2 * φ z * deriv φ z))
      (Set.Ioi 0) := by
    have hB : IntegrableOn (fun z => 2 * (deriv (fun z => z ^ 2 * σ z) z * φ z * deriv φ z))
        (Set.Ioi 0) := hi2.const_mul 2
    refine hB.congr_fun ?_ measurableSet_Ioi
    intro z _
    ring
  have h0' : Tendsto (fun z => 2 * (z ^ 2 * σ z * φ z * deriv φ z))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    simpa using h0.const_mul 2
  have hT' : Tendsto (fun z => 2 * (z ^ 2 * σ z * φ z * deriv φ z)) atTop (nhds 0) := by
    simpa using hT.const_mul 2
  have hb1 : Tendsto (fun z => (fun z : ℝ => z ^ 2 * σ z) z * (fun z : ℝ => 2 * φ z * deriv φ z) z)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) :=
    h0'.congr' (Eventually.of_forall (fun z => by ring))
  have hb2 : Tendsto (fun z => (fun z : ℝ => z ^ 2 * σ z) z * (fun z : ℝ => 2 * φ z * deriv φ z) z)
      atTop (nhds 0) :=
    hT'.congr' (Eventually.of_forall (fun z => by ring))
  -- ### The integration by parts `∫ w·(φ²)'' = ∫ w''·φ²`
  obtain ⟨e1, _⟩ := Work.FTS.EllipticEst.moment_ibp
      (fun z : ℝ => z ^ 2 * σ z) (deriv (fun z : ℝ => z ^ 2 * σ z))
      (deriv (deriv (fun z : ℝ => z ^ 2 * σ z)))
      (fun _ : ℝ => (0 : ℝ)) (fun _ : ℝ => (0 : ℝ))
      (fun z : ℝ => (φ z) ^ 2) (fun z : ℝ => 2 * φ z * deriv φ z)
      (fun z : ℝ => 2 * (deriv φ z * deriv φ z + φ z * deriv (deriv φ) z))
      hF hF' (fun z _ => by simpa using hasDerivAt_const (c := (0 : ℝ)) z)
      hH hH' hI1 hI2 hi4 (by simp) (by simp)
      hb1 hb2 hb0 hbT (by simp) (by simp)
  have hkey : (∫ z in Set.Ioi 0,
        (z ^ 2 * σ z) * (2 * (deriv φ z * deriv φ z + φ z * deriv (deriv φ) z)))
      = ∫ z in Set.Ioi 0, deriv (deriv (fun z : ℝ => z ^ 2 * σ z)) z * (φ z) ^ 2 := by
    simpa only [] using e1
  -- ### Splitting the left-hand side of the identity into the two pieces of the statement
  have hA : IntegrableOn (fun z => 2 * (σ z * (z * deriv φ z) ^ 2)) (Set.Ioi 0) := hi3.const_mul 2
  have hB : IntegrableOn (fun z => 2 * (z ^ 2 * σ z * φ z * deriv (deriv φ) z)) (Set.Ioi 0) :=
    hi1.const_mul 2
  have hfun : (∫ z in Set.Ioi 0,
        (z ^ 2 * σ z) * (2 * (deriv φ z * deriv φ z + φ z * deriv (deriv φ) z)))
      = ∫ z in Set.Ioi 0,
          2 * (σ z * (z * deriv φ z) ^ 2) + 2 * (z ^ 2 * σ z * φ z * deriv (deriv φ) z) :=
    setIntegral_congr_fun measurableSet_Ioi (fun z _ => by ring)
  have hsplit : (∫ z in Set.Ioi 0,
        2 * (σ z * (z * deriv φ z) ^ 2) + 2 * (z ^ 2 * σ z * φ z * deriv (deriv φ) z))
      = 2 * (∫ z in Set.Ioi 0, σ z * (z * deriv φ z) ^ 2)
        + 2 * (∫ z in Set.Ioi 0, z ^ 2 * σ z * φ z * deriv (deriv φ) z) := by
    rw [integral_add hA hB, integral_const_mul, integral_const_mul]
  have hsum : 2 * (∫ z in Set.Ioi 0, σ z * (z * deriv φ z) ^ 2)
        + 2 * (∫ z in Set.Ioi 0, z ^ 2 * σ z * φ z * deriv (deriv φ) z)
      = ∫ z in Set.Ioi 0, deriv (deriv (fun z : ℝ => z ^ 2 * σ z)) z * (φ z) ^ 2 :=
    hsplit.symm.trans (hfun.symm.trans hkey)
  -- ### Conclusion
  have htarget : (∫ z in Set.Ioi 0, σ z * z ^ 2 * deriv (deriv φ) z * φ z)
      = ∫ z in Set.Ioi 0, z ^ 2 * σ z * φ z * deriv (deriv φ) z :=
    setIntegral_congr_fun measurableSet_Ioi (fun z _ => by ring)
  rw [htarget]
  linarith [hsum]

end Work.FTS.EllipticEst.remov
