import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS_EllLimOK.RulingELF
import Submission.Work.FTS_EllLimOK.ProducerH.H2.Basic
import Submission.Work.FTS_EllLimOK.ProducerH.H2.bounds_rates_z
import Submission.Work.FTS_EllLimOK.ProducerH.H2.bounds_rates_theta

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK.ProducerH.H2

set_option autoImplicit false

/-- **The full box bound of the L3 producer.**  The fourteen bounds of `bounds_rates` split into
the `∂_z`-clauses (`bounds_rates_z`, from the radial rate `psiDz_rate` divided by `z ≥ a₀`) and the
`∂_θ`-clauses (`bounds_rates_theta`, from the value at the midpoint `θ = π/4` together with the
interpolation inequality and the plain second angular derivatives).  The two constants are simply
added. -/
theorem bounds_rates {α Ce : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    (hE : Work.FTS_EllLimOK.ProducerH.H2.Ctx α Ce E) {a₀ b₀ : ℝ} (ha₀ : 0 < a₀) (hab : a₀ ≤ b₀)
    {K β : ℝ} (hK : 0 < K) (hβ : 0 < β)
    (hmod : ∀ g : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α g → ∀ z ∈ Set.Icc a₀ b₀,
      ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        |deriv (deriv (fun θ' => (E g) z θ')) θ|
          ≤ K * Work.FTS.StrongGlobal.Xn6 α g * (min θ (Real.pi / 2 - θ)) ^ β) :
    ∃ C : ℝ, 0 < C ∧ ∀ g : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α g →
      ∀ z ∈ Set.Icc a₀ b₀, ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        |Work.Spaces.pz (E g) z θ| ≤ C * Work.FTS.StrongGlobal.Xn6 α g ∧
        |Work.Spaces.pth (E g) z θ| ≤ C * Work.FTS.StrongGlobal.Xn6 α g ∧
        |Work.Spaces.pz (Work.Spaces.pz (E g)) z θ| ≤ C * Work.FTS.StrongGlobal.Xn6 α g ∧
        |Work.Spaces.pth (Work.Spaces.pz (E g)) z θ| ≤ C * Work.FTS.StrongGlobal.Xn6 α g ∧
        |Work.Spaces.pz (Work.Spaces.pth (E g)) z θ| ≤ C * Work.FTS.StrongGlobal.Xn6 α g ∧
        |Work.Spaces.pth (Work.Spaces.pth (E g)) z θ| ≤ C * Work.FTS.StrongGlobal.Xn6 α g ∧
        |Work.Spaces.pth (Work.Spaces.pz (Work.Spaces.pz (E g))) z θ| ≤ C * Work.FTS.StrongGlobal.Xn6 α g ∧
        |Work.Spaces.pth (Work.Spaces.pth (Work.Spaces.pz (E g))) z θ| ≤ C * Work.FTS.StrongGlobal.Xn6 α g ∧
        |Work.Spaces.pz (E g) z θ| ≤ C * Work.FTS.StrongGlobal.Xn6 α g * θ ∧
        |Work.Spaces.pz (Work.Spaces.pz (E g)) z θ| ≤ C * Work.FTS.StrongGlobal.Xn6 α g * θ ∧
        |Work.Spaces.pz (E g) z θ| ≤ C * Work.FTS.StrongGlobal.Xn6 α g * (Real.pi / 2 - θ) ∧
        |Work.Spaces.pz (Work.Spaces.pz (E g)) z θ| ≤ C * Work.FTS.StrongGlobal.Xn6 α g * (Real.pi / 2 - θ) ∧
        |Work.Spaces.pth (Work.Spaces.pth (E g)) z θ| ≤ C * Work.FTS.StrongGlobal.Xn6 α g * θ ^ β ∧
        |Work.Spaces.pth (Work.Spaces.pth (E g)) z θ|
          ≤ C * Work.FTS.StrongGlobal.Xn6 α g * (Real.pi / 2 - θ) ^ β := by
  obtain ⟨Cz, _hCzpos, hCz⟩ := bounds_rates_z hα hα4 hE ha₀ hab
  obtain ⟨Ct, _hCtpos, hCt⟩ := bounds_rates_theta hα hα4 hE ha₀ hab hK hβ hmod
  refine ⟨Cz + Ct, by positivity, ?_⟩
  intro g hg z hz θ hθ
  obtain ⟨h1, h3, h9, h10, h11, h12⟩ := hCz g hg z hz θ hθ
  obtain ⟨h2, h4, h5, h6, h7, h8, h13, h14⟩ := hCt g hg z hz θ hθ
  have hX0 : 0 ≤ Work.FTS.StrongGlobal.Xn6 α g := Xn6_nonneg α g
  have hgen : ∀ a f : ℝ, 0 ≤ f → a ≤ Cz * Work.FTS.StrongGlobal.Xn6 α g * f →
      a ≤ (Cz + Ct) * Work.FTS.StrongGlobal.Xn6 α g * f := by
    intro a f hf ha
    calc a ≤ Cz * Work.FTS.StrongGlobal.Xn6 α g * f := ha
      _ ≤ (Cz + Ct) * Work.FTS.StrongGlobal.Xn6 α g * f := by
          apply mul_le_mul_of_nonneg_right _ hf
          exact mul_le_mul_of_nonneg_right (by linarith) hX0
  have hgenT : ∀ a f : ℝ, 0 ≤ f → a ≤ Ct * Work.FTS.StrongGlobal.Xn6 α g * f →
      a ≤ (Cz + Ct) * Work.FTS.StrongGlobal.Xn6 α g * f := by
    intro a f hf ha
    calc a ≤ Ct * Work.FTS.StrongGlobal.Xn6 α g * f := ha
      _ ≤ (Cz + Ct) * Work.FTS.StrongGlobal.Xn6 α g * f := by
          apply mul_le_mul_of_nonneg_right _ hf
          exact mul_le_mul_of_nonneg_right (by linarith) hX0
  have hgen1 : ∀ a : ℝ, a ≤ Cz * Work.FTS.StrongGlobal.Xn6 α g →
      a ≤ (Cz + Ct) * Work.FTS.StrongGlobal.Xn6 α g := fun a ha =>
    le_trans ha (mul_le_mul_of_nonneg_right (by linarith) hX0)
  have hgenT1 : ∀ a : ℝ, a ≤ Ct * Work.FTS.StrongGlobal.Xn6 α g →
      a ≤ (Cz + Ct) * Work.FTS.StrongGlobal.Xn6 α g := fun a ha =>
    le_trans ha (mul_le_mul_of_nonneg_right (by linarith) hX0)
  have hθ0 : 0 ≤ θ := hθ.1.le
  have hπ0 : 0 ≤ Real.pi / 2 - θ := by linarith [hθ.2]
  exact ⟨hgen1 _ h1,
    hgenT1 _ h2,
    hgen1 _ h3,
    hgenT1 _ h4,
    hgenT1 _ h5,
    hgenT1 _ h6,
    hgenT1 _ h7,
    hgenT1 _ h8,
    hgen _ θ hθ0 h9,
    hgen _ θ hθ0 h10,
    hgen _ (Real.pi / 2 - θ) hπ0 h11,
    hgen _ (Real.pi / 2 - θ) hπ0 h12,
    hgenT _ (θ ^ β) (Real.rpow_nonneg hθ0 β) h13,
    hgenT _ ((Real.pi / 2 - θ) ^ β) (Real.rpow_nonneg hπ0 β) h14⟩

end Work.FTS_EllLimOK.ProducerH.H2
