import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped ContDiff
open Filter

namespace Work.FTS.EllSol.PkgK5.InterpTrace

theorem sqrt_m_calc {m A B P : ℝ → ℝ}
    (hm : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), HasDerivAt m (2 * P θ) θ)
    (hP : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), HasDerivAt P (A θ + B θ) θ)
    (hAB : ContinuousOn (fun θ => A θ + B θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    (hpos : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), 0 < m θ)
    (hCS : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), P θ ^ 2 ≤ m θ * A θ) :
    ContDiffOn ℝ 2 (fun θ => Real.sqrt (m θ)) (Set.Ioo (0 : ℝ) (Real.pi / 2)) ∧
      (∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        (deriv (fun θ' => Real.sqrt (m θ')) θ) ^ 2 ≤ A θ) ∧
      (∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        (deriv (fun θ' => Real.sqrt (m θ')) θ) ^ 2
          + Real.sqrt (m θ) * deriv (deriv (fun θ' => Real.sqrt (m θ'))) θ = A θ + B θ) := by
  have hs : IsOpen (Set.Ioo (0 : ℝ) (Real.pi / 2)) := isOpen_Ioo
  -- `P` is `C¹` on the interval, with `deriv P = A + B` there
  have hdiffP : DifferentiableOn ℝ P (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    fun θ hθ => (hP θ hθ).differentiableAt.differentiableWithinAt
  have hderivP : Set.EqOn (deriv P) (fun θ => A θ + B θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    fun θ hθ => (hP θ hθ).deriv
  have hcont_derivP : ContinuousOn (deriv P) (Set.Ioo (0 : ℝ) (Real.pi / 2)) := hAB.congr hderivP
  have hC1P : ContDiffOn ℝ 1 P (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    have h := (contDiffOn_succ_iff_deriv_of_isOpen (𝕜 := ℝ) (f := P)
      (s := Set.Ioo (0 : ℝ) (Real.pi / 2)) (n := (0 : ℕ∞ω)) hs)
    simp only [zero_add] at h
    rw [h]
    exact ⟨hdiffP, fun hc => absurd hc (by simp), by rwa [contDiffOn_zero]⟩
  -- `m` is `C²`, because `deriv m = 2 * P` and `P` is `C¹`
  have hdiffm : DifferentiableOn ℝ m (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    fun θ hθ => (hm θ hθ).differentiableAt.differentiableWithinAt
  have hC1_2P : ContDiffOn ℝ 1 (fun θ => 2 * P θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    have h := hC1P.const_smul (2 : ℝ)
    simpa only [smul_eq_mul] using h
  have hC1_derivm : ContDiffOn ℝ 1 (deriv m) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hC1_2P.congr (fun θ hθ => (hm θ hθ).deriv)
  have hC2m : ContDiffOn ℝ 2 m (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    have h := (contDiffOn_succ_iff_deriv_of_isOpen (𝕜 := ℝ) (f := m)
      (s := Set.Ioo (0 : ℝ) (Real.pi / 2)) (n := (1 : ℕ∞ω)) hs)
    rw [show (2 : ℕ∞ω) = (1 : ℕ∞ω) + 1 from rfl]
    rw [h]
    exact ⟨hdiffm, fun hc => absurd hc (by simp), hC1_derivm⟩
  -- hence `√(m ·)` is `C²` (as `m > 0` on the interval)
  have hC2sqrt : ContDiffOn ℝ 2 (fun θ => Real.sqrt (m θ)) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hC2m.sqrt (fun θ hθ => (hpos θ hθ).ne')
  have hsqrt_ne : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), Real.sqrt (m θ) ≠ 0 :=
    fun θ hθ => (Real.sqrt_pos.mpr (hpos θ hθ)).ne'
  have hsqrt_sq : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), (Real.sqrt (m θ)) ^ 2 = m θ :=
    fun θ hθ => Real.sq_sqrt (le_of_lt (hpos θ hθ))
  -- first and second derivatives of `√(m ·)`
  have hderiv1 : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (fun θ' => Real.sqrt (m θ')) (P θ / Real.sqrt (m θ)) θ := by
    intro θ hθ
    have h := (hm θ hθ).sqrt (hpos θ hθ).ne'
    convert h using 1
    field_simp
  have hderiv2 : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (fun y => P y / Real.sqrt (m y))
        (((A θ + B θ) * Real.sqrt (m θ) - P θ * (P θ / Real.sqrt (m θ)))
          / (Real.sqrt (m θ)) ^ 2) θ := by
    intro θ hθ
    have hd := (hP θ hθ).fun_div (hderiv1 θ hθ) (hsqrt_ne θ hθ)
    convert hd using 1
  refine ⟨hC2sqrt, ?_, ?_⟩
  · intro θ hθ
    rw [(hderiv1 θ hθ).deriv]
    rw [div_pow, hsqrt_sq θ hθ]
    rw [div_le_iff₀ (hpos θ hθ)]
    nlinarith [hCS θ hθ]
  · intro θ hθ
    have h1 := hderiv1 θ hθ
    have h2 := hderiv2 θ hθ
    have heq : (deriv (fun θ' => Real.sqrt (m θ'))) =ᶠ[nhds θ]
        (fun y => P y / Real.sqrt (m y)) := by
      filter_upwards [hs.mem_nhds hθ] with y hy
      exact (hderiv1 y hy).deriv
    have hd2 : deriv (deriv (fun θ' => Real.sqrt (m θ'))) θ =
        (((A θ + B θ) * Real.sqrt (m θ) - P θ * (P θ / Real.sqrt (m θ)))
          / (Real.sqrt (m θ)) ^ 2) := by
      rw [Filter.EventuallyEq.deriv_eq heq]
      exact h2.deriv
    rw [h1.deriv, hd2]
    have hu : Real.sqrt (m θ) ≠ 0 := hsqrt_ne θ hθ
    field_simp
    ring

end Work.FTS.EllSol.PkgK5.InterpTrace
