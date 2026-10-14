import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.NormNum.RealSqrt
import Submission.Work.FTS.Galerkin.Inhabit.regPkg_zero
import Submission.Work.FTS.StrongPersist.L3Rhs.N0gCoupled
import Submission.Work.FTS.StrongPersist.L3Rhs.N0gLocal
import Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.leibnizRem6
import Submission.Work.FTS.TransportS.GalSide
import Submission.Work.FTS_RegExport.RXT.velVanish2Star

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.L3Rhs

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## Merging the two halves -/

/-- **`ℋ³`-membership and the `ℋ³`-square bound for a difference** of two `C³` data with honest
`ℋ³`-integrands: `0 + u - v = u - v`, so this is `L3Aux.HkMem_HkSq_add3_le` with the zero
datum. -/
theorem hkMem_hkSq_sub_le {α : ℝ} {u v : Fn}
    (hu : ContDiffOn ℝ 3 (Function.uncurry u) Work.FTS.EllipticEst.Q0)
    (hv : ContDiffOn ℝ 3 (Function.uncurry v) Work.FTS.EllipticEst.Q0)
    (hmu : Work.Spaces.HkMem α 3 u) (hmv : Work.Spaces.HkMem α 3 v) :
    Work.Spaces.HkMem α 3 (fun z θ => u z θ - v z θ) ∧
      Work.Spaces.HkSq α 3 (fun z θ => u z θ - v z θ)
        ≤ 4 * (Work.Spaces.HkSq α 3 u + Work.Spaces.HkSq α 3 v) := by
  have h0 : ContDiffOn ℝ 3 (Function.uncurry (fun _ _ : ℝ => (0 : ℝ)))
      Work.FTS.EllipticEst.Q0 := contDiffOn_const
  obtain ⟨hm, hb⟩ := Work.FTS.StrongPersist.L3Aux.HkMem_HkSq_add3_le α 3 (by norm_num)
    (f := fun _ _ : ℝ => (0 : ℝ)) (g := u) (h := v) h0 hu hv
    (Work.FTS.Galerkin.Inhabit.HkMem_zeroF α 3) hmu hmv
  have heq : (fun z θ : ℝ => (0 : ℝ) + u z θ - v z θ) = fun z θ => u z θ - v z θ := by
    funext z θ; ring
  rw [heq] at hm hb
  have hz : Work.Spaces.HkSq α 3 (fun _ _ : ℝ => (0 : ℝ)) = 0 :=
    Work.FTS.Galerkin.HkSq_zero_fun α 3
  rw [hz, zero_add] at hb
  exact ⟨hm, hb⟩

/-- `√(a+b) ≤ √a + √b` for `a, b ≥ 0`. -/
private theorem sqrt_add_le' {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  have h1 : Real.sqrt (a + b) ^ 2 = a + b := Real.sq_sqrt (by linarith)
  have h2 : (Real.sqrt a + Real.sqrt b) ^ 2
      = a + b + 2 * Real.sqrt a * Real.sqrt b := by
    rw [add_sq, Real.sq_sqrt ha, Real.sq_sqrt hb]; ring
  have h3 : 0 ≤ Real.sqrt a := Real.sqrt_nonneg a
  have h4 : 0 ≤ Real.sqrt b := Real.sqrt_nonneg b
  have h5 : 0 ≤ Real.sqrt (a + b) := Real.sqrt_nonneg _
  nlinarith [h1, h2, h3, h4, h5, mul_nonneg h3 h4]

/-- The square-root form of the merging: the `ℋ³`-norm of the difference is at most twice the
sum of the two `ℋ³`-norms. -/
theorem hkNorm_sub_le {α : ℝ} {u v : Fn}
    (hu : ContDiffOn ℝ 3 (Function.uncurry u) Work.FTS.EllipticEst.Q0)
    (hv : ContDiffOn ℝ 3 (Function.uncurry v) Work.FTS.EllipticEst.Q0)
    (hmu : Work.Spaces.HkMem α 3 u) (hmv : Work.Spaces.HkMem α 3 v) :
    Work.Spaces.HkNorm α 3 (fun z θ => u z θ - v z θ)
      ≤ 2 * (Work.Spaces.HkNorm α 3 u + Work.Spaces.HkNorm α 3 v) := by
  have hsub := hkMem_hkSq_sub_le hu hv hmu hmv
  have hA : 0 ≤ Work.Spaces.HkSq α 3 u := Work.Spaces.HkSq_nonneg α 3 u
  have hB : 0 ≤ Work.Spaces.HkSq α 3 v := Work.Spaces.HkSq_nonneg α 3 v
  have h4 : Work.Spaces.HkSq α 3 (fun z θ => u z θ - v z θ)
      ≤ 4 * (Work.Spaces.HkSq α 3 u + Work.Spaces.HkSq α 3 v) := hsub.2
  have h45 : 0 ≤ 4 * (Work.Spaces.HkSq α 3 u + Work.Spaces.HkSq α 3 v) := by linarith
  have hsq : Work.Spaces.HkSq α 3 (fun z θ => u z θ - v z θ)
      ≤ 4 * Work.Spaces.HkSq α 3 u + 4 * Work.Spaces.HkSq α 3 v := by linarith
  calc Work.Spaces.HkNorm α 3 (fun z θ => u z θ - v z θ)
      = Real.sqrt (Work.Spaces.HkSq α 3 (fun z θ => u z θ - v z θ)) := rfl
    _ ≤ Real.sqrt (4 * Work.Spaces.HkSq α 3 u + 4 * Work.Spaces.HkSq α 3 v) :=
        Real.sqrt_le_sqrt hsq
    _ ≤ Real.sqrt (4 * Work.Spaces.HkSq α 3 u) + Real.sqrt (4 * Work.Spaces.HkSq α 3 v) :=
        sqrt_add_le' (by linarith) (by linarith)
    _ = 2 * Real.sqrt (Work.Spaces.HkSq α 3 u) + 2 * Real.sqrt (Work.Spaces.HkSq α 3 v) := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4),
          Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
        norm_num
    _ = 2 * (Work.Spaces.HkNorm α 3 u + Work.Spaces.HkNorm α 3 v) := by
        simp only [Work.Spaces.HkNorm]
        ring

/-! ## The assembly -/

/-- **The block estimate, from its two halves.** -/
theorem L3RhsN0gBlock_of
    (hcoup : ∃ C Cpow α₂ : ℝ, 0 < C ∧ 0 ≤ Cpow ∧ 0 < α₂ ∧
      ∀ α ∈ Set.Ioc 0 α₂, ∀ (f : Fn) (M : ℝ),
        H6Adm α f → Work.FTS.Nonlin.Xn α f ≤ M →
        Work.Spaces.HkMem α 3 (fun z θ => Mf f z θ * Bf α f z θ) ∧
        Work.Spaces.HkNorm α 3 (fun z θ => Mf f z θ * Bf α f z θ)
          ≤ C * α ^ (-Cpow) * (1 + M) ^ 4 * (1 + Xn6 α f) ^ 2)
    (hloc : ∃ C α₂ : ℝ, 0 < C ∧ 0 < α₂ ∧
      ∀ α ∈ Set.Ioc 0 α₂, ∀ (f : Fn) (M : ℝ),
        H6Adm α f → Work.FTS.Nonlin.Xn α f ≤ M →
        Work.Spaces.HkMem α 3 (Wf α f) ∧
        Work.Spaces.HkNorm α 3 (Wf α f) ≤ C * (1 + M)) :
    ∃ C Cpow α₂ : ℝ, 0 < C ∧ 0 ≤ Cpow ∧ 0 < α₂ ∧
      ∀ α ∈ Set.Ioc 0 α₂, ∀ (f : Fn) (M : ℝ),
        H6Adm α f → Work.FTS.Nonlin.Xn α f ≤ M →
        ContDiffOn ℝ 3 (Function.uncurry (N0gSum α f)) Work.FTS.EllipticEst.Q0 ∧
        Work.Spaces.HkMem α 3 (N0gSum α f) ∧
        Work.Spaces.HkNorm α 3 (N0gSum α f)
          ≤ C * α ^ (-Cpow) * (1 + M) ^ 4 * (1 + Xn6 α f) ^ 2 := by
  obtain ⟨C1, Cpow, a1, hC1, hCp, ha1, H1⟩ := hcoup
  obtain ⟨C2, a2, hC2, ha2, H2⟩ := hloc
  refine ⟨2 * (C1 + C2), Cpow, min a1 (min a2 1), by positivity, hCp,
    lt_min ha1 (lt_min ha2 one_pos), ?_⟩
  intro α hα f M hf hM
  have hαpos : 0 < α := hα.1
  have hα1 : α ≤ 1 := le_trans hα.2 (le_trans (min_le_right _ _) (min_le_right _ _))
  have hαa1 : α ≤ a1 := le_trans hα.2 (min_le_left _ _)
  have hαa2 : α ≤ a2 := le_trans hα.2 (le_trans (min_le_right _ _) (min_le_left _ _))
  obtain ⟨hm1, hb1⟩ := H1 α ⟨hαpos, hαa1⟩ f M hf hM
  obtain ⟨hm2, hb2⟩ := H2 α ⟨hαpos, hαa2⟩ f M hf hM
  have hcd1 : ContDiffOn ℝ 3 (Function.uncurry (fun z θ => Mf f z θ * Bf α f z θ))
      Work.FTS.EllipticEst.Q0 := contDiffOn_three_Mf_mul_Bf hαpos hα1 hf
  have hcd2 : ContDiffOn ℝ 3 (Function.uncurry (Wf α f)) Work.FTS.EllipticEst.Q0 :=
    contDiffOn_three_Wf hαpos hα1 hf.reg.1
  have hsub := hkMem_hkSq_sub_le hcd1 hcd2 hm1 hm2
  have hnorm := hkNorm_sub_le hcd1 hcd2 hm1 hm2
  have hMnn : 0 ≤ M := le_trans (Real.sqrt_nonneg _) hM
  have hXn6nn : 0 ≤ Xn6 α f := Xn6_nonneg α f
  have hXpow : (1 : ℝ) ≤ α ^ (-Cpow) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hαpos hα1 (by linarith)
  have hY4 : (1 : ℝ) ≤ (1 + M) ^ 4 := by
    calc (1 : ℝ) = 1 ^ 4 := by norm_num
      _ ≤ (1 + M) ^ 4 := pow_le_pow_left₀ (by norm_num) (by linarith) 4
  have hY4' : (1 + M) ≤ (1 + M) ^ 4 := by
    calc (1 + M) = (1 + M) ^ 1 := (pow_one _).symm
      _ ≤ (1 + M) ^ 4 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have hZ2 : (1 : ℝ) ≤ (1 + Xn6 α f) ^ 2 := by
    calc (1 : ℝ) = 1 ^ 2 := by norm_num
      _ ≤ (1 + Xn6 α f) ^ 2 := pow_le_pow_left₀ (by norm_num) (by linarith) 2
  have hC1nn : 0 ≤ C1 := le_of_lt hC1
  have hC2nn : 0 ≤ C2 := le_of_lt hC2
  have hQnn : 0 ≤ α ^ (-Cpow) * (1 + M) ^ 4 * (1 + Xn6 α f) ^ 2 := by positivity
  -- the local half, upgraded to the common shape
  have h1 : Work.Spaces.HkNorm α 3 (Wf α f)
      ≤ C2 * α ^ (-Cpow) * (1 + M) ^ 4 * (1 + Xn6 α f) ^ 2 := by
    refine le_trans hb2 ?_
    have hA : 0 ≤ C2 * α ^ (-Cpow) * (1 + M) ^ 4 := by positivity
    calc C2 * (1 + M)
        ≤ C2 * (1 + M) ^ 4 := mul_le_mul_of_nonneg_left hY4' hC2nn
      _ ≤ C2 * α ^ (-Cpow) * (1 + M) ^ 4 :=
          mul_le_mul_of_nonneg_right (by simpa using mul_le_mul_of_nonneg_left hXpow hC2nn)
            (by positivity)
      _ ≤ C2 * α ^ (-Cpow) * (1 + M) ^ 4 * (1 + Xn6 α f) ^ 2 := by
          simpa using mul_le_mul_of_nonneg_left hZ2 hA
  refine ⟨contDiffOn_three_N0gSum hαpos hα1 hf, ?_, ?_⟩
  · rw [N0gSum_eq α f]; exact hsub.1
  · rw [N0gSum_eq α f]
    refine le_trans hnorm ?_
    calc 2 * (Work.Spaces.HkNorm α 3 (fun z θ => Mf f z θ * Bf α f z θ)
          + Work.Spaces.HkNorm α 3 (Wf α f))
        ≤ 2 * (C1 * α ^ (-Cpow) * (1 + M) ^ 4 * (1 + Xn6 α f) ^ 2
            + C2 * α ^ (-Cpow) * (1 + M) ^ 4 * (1 + Xn6 α f) ^ 2) :=
          mul_le_mul_of_nonneg_left (add_le_add hb1 h1) (by norm_num)
      _ = 2 * (C1 + C2) * α ^ (-Cpow) * (1 + M) ^ 4 * (1 + Xn6 α f) ^ 2 := by ring

/-! ## The target -/

theorem L3RhsN0gBlock : ∃ C Cpow α₂ : ℝ, 0 < C ∧ 0 ≤ Cpow ∧ 0 < α₂ ∧
    ∀ α ∈ Set.Ioc 0 α₂, ∀ (f : Work.FTS.Galerkin.Fn) (M : ℝ),
      Work.FTS.StrongPersist.H6Adm α f → Work.FTS.Nonlin.Xn α f ≤ M →
      ContDiffOn ℝ 3 (Function.uncurry (Work.FTS.StrongPersist.L3Rhs.N0gSum α f)) Work.FTS.EllipticEst.Q0 ∧
      Work.Spaces.HkMem α 3 (Work.FTS.StrongPersist.L3Rhs.N0gSum α f) ∧
      Work.Spaces.HkNorm α 3 (Work.FTS.StrongPersist.L3Rhs.N0gSum α f)
        ≤ C * α ^ (-Cpow) * (1 + M) ^ 4 * (1 + Work.FTS.StrongPersist.Xn6 α f) ^ 2 := by
  exact L3RhsN0gBlock_of N0gCoupled N0gLocal

end Work.FTS.StrongPersist.L3Rhs
