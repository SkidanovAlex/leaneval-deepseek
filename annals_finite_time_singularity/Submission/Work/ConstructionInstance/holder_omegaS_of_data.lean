import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Topology.MetricSpace.Holder
import Submission.Work.ConstructionInstance.Defs
import Submission.Work.ConstructionInstance.Basic
import Submission.Work.ConstructionInstance.AuxOmegaStar
import Submission.Work.ConstructionInstance.omegaStar_eq_Aom
import Submission.Work.ConstructionInstance.holder_omegaStar
import Submission.Work.ConstructionInstance.holder_smul_eTheta
import Submission.Work.ConstructionInstance.isOddVorticity_omegaS
import Submission.Work.ConstructionInstance.gComp_abs_le
import Submission.Work.ConstructionInstance.holder_of_half_odd
import Submission.Work.ConstructionInstance.holder_gComp

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

namespace Work.ConstructionInstance

/-- The self-similar vorticity `omegaS (3α) g` is `α`-Hölder, from the *explicit* conditions on
the perturbation `g`: smoothness near the closed quadrant, vanishing at `z = 0` and on the angular
boundaries, and the three uniform bounds — angular vanishing `|g| ≤ Cv·Γ(α,θ)`, radial modulus
`|g(z,θ)-g(z',θ)| ≤ Lg|z-z'|^α`, angular modulus `|g(z,θ)-g(z,θ')| ≤ Lθ|θ-θ'|^α`.  The `F_*` part
is handled by `Defs.Fstar_abs_le` and the explicit form of `Γ`. -/
theorem holder_omegaS_of_data {α : ℝ} (hα : 0 < α) (hα13 : α ≤ 1/3) {g : ℝ → ℝ → ℝ}
    {Cv Lg Lθ : ℝ} (hCv : 0 ≤ Cv) (hLg : 0 ≤ Lg) (hLθ : 0 ≤ Lθ)
    (hvt : Work.Spaces.VanishTheta g)
    (hquad0 : ∀ θ : ℝ, g 0 θ = 0)
    (hquad1 : ∀ θ : ℝ, Work.Spaces.pz g 0 θ = 0)
    (hvan : ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
      |g z θ| ≤ Cv * Work.ConstructionInstance.Gamma α θ)
    (hzk : ∀ z z' θ : ℝ, 0 ≤ z → 0 ≤ z' → θ ∈ Work.Spaces.Iθ →
      |g z θ - g z' θ| ≤ Lg * |z - z'| ^ α)
    (hzth : ∀ z θ θ' : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → θ' ∈ Work.Spaces.Iθ →
      |g z θ - g z θ'| ≤ Lθ * |θ - θ'| ^ α)
    (hsm : ContDiffOn ℝ 2 (Function.uncurry g)
      (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (Real.pi / 2 + 1))) :
    Holder ⟨α, hα.le⟩ (Work.ConstructionInstance.omegaS (3 * α) g) := by
  have hα1 : α ≤ 1 := by linarith
  set ĝ : R3 → ℝ := fun x => g (Work.Cyl.rho x ^ (3 * α)) (|Work.Cyl.theta x|) with hĝ
  have hĝ_holder : Holder ⟨α, hα.le⟩ ĝ :=
    holder_gComp hα hα13 hCv hLg hLθ hvt hquad0 hquad1 hvan hzk hzth hsm
  obtain ⟨Ca, hCa0, hCa⟩ :=
    gComp_abs_le hα hα13 hCv hLg hLθ hvt hquad0 hquad1 hvan hzk hzth hsm
  have hE_holder : Holder ⟨α, hα.le⟩ (fun x : R3 => ĝ x • Work.Cyl.eTheta x) :=
    holder_smul_eTheta hα hα1 hCa0 hĝ_holder hCa
  obtain ⟨Cω, hCω⟩ := holder_omegaStar (β := α) hα hα1
  have hS_holder : Holder ⟨α, hα.le⟩
      (fun x : R3 => (3 * α / Work.Spaces.c (3 * α)) • omegaStar α x) :=
    ⟨Cω * ‖(3 * α / Work.Spaces.c (3 * α))‖₊, HolderWith.smul _ hCω⟩
  have hΦ_holder : Holder ⟨α, hα.le⟩
      (fun x : R3 => (3 * α / Work.Spaces.c (3 * α)) • omegaStar α x
        + ĝ x • Work.Cyl.eTheta x) := by
    obtain ⟨C₁, h₁⟩ := hS_holder
    obtain ⟨C₂, h₂⟩ := hE_holder
    exact ⟨C₁ + C₂, HolderWith.add h₁ h₂⟩
  have hhalf : ∀ x : R3, 0 ≤ x 2 → omegaS (3 * α) g x
      = (3 * α / Work.Spaces.c (3 * α)) • omegaStar α x + ĝ x • Work.Cyl.eTheta x := by
    intro x hx
    have hθ : 0 ≤ Work.Cyl.theta x := theta_nonneg_of_axial_nonneg hx
    have hAom : Aom α x = A0 α x := by
      rw [Aom, cSign, ite_eq_left hx, one_mul]
    have hGF : Gamma α (Work.Cyl.theta x) * Work.FM.Fstar (Work.Cyl.rho x ^ (3 * α))
        = A0 α x := by
      rw [← hAom, Gamma_mul_Fstar_eq_Aom α hα x]
    have hF : Work.Construction.Fstar (3 * α) (Work.Cyl.rho x ^ (3 * α)) (Work.Cyl.theta x)
        = (3 * α / Work.Spaces.c (3 * α)) * A0 α x := by
      have hGam : Work.Spaces.Gam (3 * α) (Work.Cyl.theta x) = Gamma α (Work.Cyl.theta x) := by
        rw [Work.Spaces.Gam, Gamma, show (3 * α) / 3 = α by ring]
      rw [Work.Construction.Fstar, hGam]
      conv_rhs => rw [← hGF]
      ring
    have hĝx : ĝ x = g (Work.Cyl.rho x ^ (3 * α)) (Work.Cyl.theta x) := by
      rw [hĝ]; simp only; rw [abs_of_nonneg hθ]
    rw [omegaS_apply', profile_of_nonneg hθ, hF, hĝx, omegaStar_apply,
      Gamma_mul_Fstar_eq_Aom α hα x, hAom, smul_smul, ← add_smul]
  have hplane : ∀ x : R3, x 2 = 0 →
      (3 * α / Work.Spaces.c (3 * α)) • omegaStar α x + ĝ x • Work.Cyl.eTheta x = 0 := by
    intro x hx
    have hθ0 : Work.Cyl.theta x = 0 := by
      rw [Work.Cyl.theta, Work.Cyl.axial, hx]; simp
    have hA0 : A0 α x = 0 := by
      simp [A0, hx, Real.zero_rpow (ne_of_gt hα)]
    have hAom : Aom α x = 0 := by
      rw [Aom, cSign, ite_eq_left (le_of_eq hx.symm), one_mul, hA0]
    have hĝ0 : ĝ x = 0 := by
      rw [hĝ]; simp only; rw [hθ0, abs_zero]; exact hvt.1 _
    rw [omegaStar_apply, Gamma_mul_Fstar_eq_Aom α hα x, hAom, hĝ0]
    simp
  have hodd : ∀ x : R3, omegaS (3 * α) g (Work.Cyl.reflZ x) = - omegaS (3 * α) g x := by
    intro x
    have hrho : Work.Cyl.rho (Work.Cyl.reflZ x) = Work.Cyl.rho x := by
      simp [Work.Cyl.rho, Work.Cyl.radSq, Work.Cyl.axial, Work.Cyl.reflZ]
    have hth : Work.Cyl.theta (Work.Cyl.reflZ x) = - Work.Cyl.theta x := by
      simp [Work.Cyl.theta, Work.Cyl.radial, Work.Cyl.radSq, Work.Cyl.axial, Work.Cyl.reflZ,
        neg_div, Real.arctan_neg]
    have he : Work.Cyl.eTheta (Work.Cyl.reflZ x) = Work.Cyl.eTheta x := by
      simp [Work.Cyl.eTheta, Work.Cyl.radial, Work.Cyl.radSq, Work.Cyl.angularVec, Work.Cyl.reflZ]
    rw [omegaS_apply', omegaS_apply', hrho, hth, he,
      profile_odd (by positivity : (3:ℝ) * α ≠ 0) (fun z => hvt.1 z), neg_smul]
  exact holder_of_half_odd (ω := omegaS (3 * α) g)
    (Φ := fun x : R3 => (3 * α / Work.Spaces.c (3 * α)) • omegaStar α x
      + ĝ x • Work.Cyl.eTheta x) hα hΦ_holder hhalf hodd hplane

end Work.ConstructionInstance
