import Mathlib
import Submission.Work.ORVonNeumann.Rep.HilbertBasis
import Submission.Work.ORVonNeumann.Rep.GroupVonNeumann
import Submission.Work.ORVonNeumann.Rep.delta1_separating

namespace Work.Rep

open Work.ORVonNeumann

variable {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
  [MeasurableMul G]

/-- `δ₁` is the basis vector `δ_g` at `g = 1`. -/
theorem deltaG_one : Work.ORVonNeumann.Rep.deltaG (1 : G) = delta1 G := by
  rw [← Work.ORVonNeumann.Rep.rightRegOp_inv_delta1 (G := G) (1 : G), inv_one,
    Work.ORVonNeumann.Rep.rightRegOp_one_apply]

/-- An element `T` of the group von Neumann algebra `N(G)` commutes with the right regular
representation, so `T δ_g = ρ(g⁻¹) (T δ₁)`. -/
theorem N_apply_deltaG (T : groupVonNeumann G) (g : G) :
    (T : boundedEnd G) (Work.ORVonNeumann.Rep.deltaG g)
      = Work.ORVonNeumann.Rep.rightRegOp g⁻¹ ((T : boundedEnd G) (delta1 G)) := by
  have hcomm := (mem_groupVonNeumann_iff (G := G) (T : boundedEnd G)).mp T.2 g⁻¹
  have h2 : (T : boundedEnd G) (Work.ORVonNeumann.Rep.rightRegOp g⁻¹ (delta1 G))
      = Work.ORVonNeumann.Rep.rightRegOp g⁻¹ ((T : boundedEnd G) (delta1 G)) := by
    have h := congrArg (fun S : boundedEnd G => S (delta1 G)) hcomm
    rwa [mul_apply_eq_comp, mul_apply_eq_comp] at h
  rw [← Work.ORVonNeumann.Rep.rightRegOp_inv_delta1 (G := G) g]
  exact h2

/-- The matrix coefficient `⟪δ₁, T δ_g⟫` of an element `T` of `N(G)` equals
`⟪δ_{g⁻¹}, T δ₁⟫`. -/
theorem inner_delta1_N_apply_deltaG (T : groupVonNeumann G) (g : G) :
    inner ℂ (delta1 G) ((T : boundedEnd G) (Work.ORVonNeumann.Rep.deltaG g))
      = inner ℂ (Work.ORVonNeumann.Rep.deltaG g⁻¹) ((T : boundedEnd G) (delta1 G)) := by
  rw [N_apply_deltaG (G := G) T g]
  rw [← Work.ORVonNeumann.Rep.rightRegOp_star g, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right]
  rw [← deltaG_one, Work.ORVonNeumann.Rep.rightRegOp_deltaG, one_mul]

/-- **The trace computed in the basis `{δ_g}`.**  For `a b ∈ N(G)`,
`τ (a b) = ∑' g, ⟪δ_g, b δ₁⟫ * ⟪δ_{g⁻¹}, a δ₁⟫`. -/
theorem tau_mul_eq_tsum (a b : groupVonNeumann G) :
    inner ℂ (delta1 G) (((a * b : groupVonNeumann G) : boundedEnd G) (delta1 G))
      = ∑' g : G, inner ℂ (Work.ORVonNeumann.Rep.deltaG g) ((b : boundedEnd G) (delta1 G))
          * inner ℂ (Work.ORVonNeumann.Rep.deltaG g⁻¹) ((a : boundedEnd G) (delta1 G)) := by
  have hcoe : (((a * b : groupVonNeumann G) : boundedEnd G) (delta1 G))
      = (a : boundedEnd G) ((b : boundedEnd G) (delta1 G)) := by
    rw [Subalgebra.coe_mul, mul_apply_eq_comp]
  rw [hcoe]
  have hb : HasSum (fun g : G =>
      inner ℂ (Work.ORVonNeumann.Rep.deltaG g) ((b : boundedEnd G) (delta1 G))
        • Work.ORVonNeumann.Rep.deltaG g) ((b : boundedEnd G) (delta1 G)) :=
    Work.ORVonNeumann.Rep.hasSum_expansion _
  have h3 : HasSum (fun g : G => inner ℂ (delta1 G)
        (inner ℂ (Work.ORVonNeumann.Rep.deltaG g) ((b : boundedEnd G) (delta1 G))
          • (a : boundedEnd G) (Work.ORVonNeumann.Rep.deltaG g)))
      (inner ℂ (delta1 G) ((a : boundedEnd G) ((b : boundedEnd G) (delta1 G)))) := by
    have ha := hb.map (a : boundedEnd G) (a : boundedEnd G).continuous
    have ha' : HasSum (fun g : G =>
        inner ℂ (Work.ORVonNeumann.Rep.deltaG g) ((b : boundedEnd G) (delta1 G))
          • (a : boundedEnd G) (Work.ORVonNeumann.Rep.deltaG g))
        ((a : boundedEnd G) ((b : boundedEnd G) (delta1 G))) := by
      simpa only [Function.comp_def, ContinuousLinearMap.map_smul] using ha
    have h4 := ha'.map (innerSL ℂ (delta1 G)) (innerSL ℂ (delta1 G)).continuous
    simpa only [Function.comp_def, innerSL_apply_apply] using h4
  rw [← h3.tsum_eq]
  refine tsum_congr (fun g => ?_)
  rw [inner_smul_right, inner_delta1_N_apply_deltaG (G := G) a g]

theorem tau_tracial {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G] [MeasurableMul G] (a b : ↥(Work.ORVonNeumann.groupVonNeumann G)) : inner ℂ (Work.ORVonNeumann.delta1 G) (((a * b : ↥(Work.ORVonNeumann.groupVonNeumann G)) : Work.ORVonNeumann.boundedEnd G) (Work.ORVonNeumann.delta1 G)) = inner ℂ (Work.ORVonNeumann.delta1 G) (((b * a : ↥(Work.ORVonNeumann.groupVonNeumann G)) : Work.ORVonNeumann.boundedEnd G) (Work.ORVonNeumann.delta1 G)) := by
  rw [tau_mul_eq_tsum (G := G) a b, tau_mul_eq_tsum (G := G) b a]
  rw [← Equiv.tsum_eq (Equiv.inv G) (fun g : G =>
    inner ℂ (Work.ORVonNeumann.Rep.deltaG g) ((b : boundedEnd G) (delta1 G))
      * inner ℂ (Work.ORVonNeumann.Rep.deltaG g⁻¹) ((a : boundedEnd G) (delta1 G)))]
  refine tsum_congr (fun g => ?_)
  rw [Equiv.inv_apply, inv_inv, mul_comm]

end Work.Rep
