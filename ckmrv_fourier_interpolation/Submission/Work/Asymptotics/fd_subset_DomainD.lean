import Mathlib
import Submission.Work.Asymptotics.DomainD

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle Topology

namespace Work.Asymptotics

/-- **Mathlib's standard fundamental domain `fd` for `SL(2,ℤ)` lies in the CKMRV
`Γ(2)`-fundamental domain `𝒟`.**  For `|Re z| ≤ 1/2` and `‖z‖ ≥ 1` one has
`‖z ∓ 1/2‖² = ‖z‖² ∓ Re z + 1/4 ≥ 3/4 > 1/4`, so both disc conditions hold. -/
theorem fd_subset_DomainD : ModularGroup.fd ⊆ DomainD := by
  intro z hz
  obtain ⟨hnormSq, hre⟩ := hz
  have hnsq : Complex.normSq (z : ℂ) = z.re ^ 2 + z.im ^ 2 := by
    rw [Complex.normSq_apply, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
    ring
  have hx1 : z.re ≤ 1 / 2 := (abs_le.mp hre).2
  have hx0 : -(1 / 2 : ℝ) ≤ z.re := (abs_le.mp hre).1
  have key : ∀ c : ℝ, c = 1 / 2 ∨ c = -(1 / 2) →
      (1 / 4 : ℝ) < Complex.normSq ((z : ℂ) - (c : ℂ)) := by
    intro c hc
    have hns : Complex.normSq ((z : ℂ) - (c : ℂ)) = (z.re - c) ^ 2 + z.im ^ 2 := by
      rw [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
        Complex.ofReal_im, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
      ring
    rw [hns]
    rcases hc with hc | hc <;> rw [hc] <;> nlinarith [hnormSq, hnsq, sq_nonneg z.im]
  have norm_le : ∀ c : ℝ, c = 1 / 2 ∨ c = -(1 / 2) →
      (1 / 2 : ℝ) < ‖((z : ℂ) - (c : ℂ))‖ := by
    intro c hc
    have h := key c hc
    have hsq : (1 / 4 : ℝ) < ‖((z : ℂ) - (c : ℂ))‖ ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq]; exact h
    have hsq' : ((1 : ℝ) / 2) ^ 2 < ‖((z : ℂ) - (c : ℂ))‖ ^ 2 := by
      rw [show ((1 : ℝ) / 2) ^ 2 = (1 / 4 : ℝ) by norm_num]; exact hsq
    have hnn : (0 : ℝ) ≤ ‖((z : ℂ) - (c : ℂ))‖ := norm_nonneg _
    calc (1 / 2 : ℝ) < Real.sqrt (‖((z : ℂ) - (c : ℂ))‖ ^ 2) :=
          Real.lt_sqrt_of_sq_lt hsq'
      _ = ‖((z : ℂ) - (c : ℂ))‖ := Real.sqrt_sq hnn
  refine ⟨by linarith, by linarith, ?_, ?_⟩
  · convert norm_le (1 / 2) (Or.inl rfl) using 2
    push_cast
    ring
  · have h := norm_le (-(1 / 2)) (Or.inr rfl)
    convert h using 2
    push_cast
    ring

end Work.Asymptotics
