import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.PhiStar.Gegenbauer.eFam_complete
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.FlatWAux.PsiExpAux

open MeasureTheory Set Filter

noncomputable section

set_option autoImplicit false

/-! ## Uniqueness of a `C⁰` function from its `eFam`-moments

The Dirichlet eigenfunctions `eFam n θ = cos θ · C^{(3/2)}_{2n+1}(sin θ)` of `Work.Elliptic.Lzero`
are complete with respect to the weight `cos θ dθ` on `Iθ = [0, π/2]`
(`Work.FTS.PhiStar.Gegenbauer.eFam_complete`): a function orthogonal to every `eFam n` vanishes
a.e.  Consequently two continuous functions with the same `eFam`-moments coincide.

The proof is soft.  Put `g := w - v`; then `g` is continuous on the compact `Iθ`, so it is a.e.
strongly measurable, `g ^ 2 * cos` is integrable on `Iθ`, and each `g * eFam n * cos` (as well as
the two pieces `w * eFam n * cos`, `v * eFam n * cos`) is integrable there.  Linearity of the
integral turns the agreement of the moments into `∫_{Iθ} g · eFam n · cos = 0` for every `n`, and
completeness gives `g =ᵐ 0`.  Since `g` is continuous and `Iθ ⊆ closure (interior Iθ)`
(`Iθ = [0, π/2]`, so `interior Iθ = (0, π/2)` and it is dense in `Iθ`), the a.e. equality upgrades
to the pointwise equality `g = 0` on `Iθ` (`Measure.eqOn_of_ae_eq`), in particular on `Ioo 0 π/2`.
-/

/-- `eFam m` is continuous on `ℝ`. -/
theorem continuous_eFam_psi (m : ℕ) :
    Continuous (fun θ : ℝ => Work.FTS.PhiStar.Gegenbauer.eFam m θ) :=
  Real.continuous_cos.mul
    (((Work.FTS.PhiStar.Gegenbauer.contDiff_gC (2 * m + 1)).continuous).comp
      Real.continuous_sin)

theorem MomentEqOn (v w : ℝ → ℝ)
    (hv : ContinuousOn v (Set.Icc 0 (Real.pi / 2)))
    (hw : ContinuousOn w (Set.Icc 0 (Real.pi / 2)))
    (hmom : ∀ n : ℕ, (∫ θ in Work.Spaces.Iθ, w θ * Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ)
        = ∫ θ in Work.Spaces.Iθ, v θ * Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), w θ = v θ := by
  -- `g := w - v` is continuous on `Iθ`
  have hgcont : ContinuousOn (fun θ : ℝ => w θ - v θ) Work.Spaces.Iθ := hw.sub hv
  -- hence a.e. strongly measurable there
  have haesm : AEStronglyMeasurable (fun θ : ℝ => w θ - v θ)
      (volume.restrict Work.Spaces.Iθ) :=
    hgcont.aestronglyMeasurable measurableSet_Icc
  -- and `g ^ 2 * cos` is integrable on the compact `Iθ`
  have hint : IntegrableOn (fun θ : ℝ => (w θ - v θ) ^ 2 * Real.cos θ) Work.Spaces.Iθ :=
    ContinuousOn.integrableOn_compact isCompact_Icc
      ((hgcont.pow 2).mul Real.continuous_cos.continuousOn)
  -- the two pieces of a moment are integrable on `Iθ` (continuity on a compact set)
  have hintw : ∀ n : ℕ,
      Integrable (fun θ : ℝ => w θ * Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ)
        (volume.restrict Work.Spaces.Iθ) := fun n =>
    ContinuousOn.integrableOn_compact isCompact_Icc
      ((hw.mul (continuous_eFam_psi n).continuousOn).mul Real.continuous_cos.continuousOn)
  have hintv : ∀ n : ℕ,
      Integrable (fun θ : ℝ => v θ * Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ)
        (volume.restrict Work.Spaces.Iθ) := fun n =>
    ContinuousOn.integrableOn_compact isCompact_Icc
      ((hv.mul (continuous_eFam_psi n).continuousOn).mul Real.continuous_cos.continuousOn)
  -- the moments of `g` vanish, by linearity of the integral
  have hmom0 : ∀ n : ℕ,
      ∫ θ in Work.Spaces.Iθ,
          (w θ - v θ) * Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ = 0 := by
    intro n
    have hsplit : (∫ θ in Work.Spaces.Iθ,
          (w θ - v θ) * Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ)
        = ∫ θ in Work.Spaces.Iθ,
            (w θ * Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ
              - v θ * Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ) :=
      setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)
    rw [hsplit, integral_sub (hintw n) (hintv n), hmom n, sub_self]
  -- completeness of the Dirichlet eigenbasis
  have hae := Work.FTS.PhiStar.Gegenbauer.eFam_complete (fun θ : ℝ => w θ - v θ)
    haesm hint hmom0
  -- a.e. equality of continuous functions upgrades to equality on the closed interval
  have hsub : Work.Spaces.Iθ ⊆ closure (interior Work.Spaces.Iθ) := by
    have hne : (0 : ℝ) ≠ Real.pi / 2 := by positivity
    change Set.Icc (0 : ℝ) (Real.pi / 2)
      ⊆ closure (interior (Set.Icc (0 : ℝ) (Real.pi / 2)))
    intro θ hθ
    rw [closure_interior_Icc hne]
    exact hθ
  have heqon : EqOn (fun θ : ℝ => w θ - v θ) (fun _ : ℝ => (0 : ℝ)) Work.Spaces.Iθ :=
    Measure.eqOn_of_ae_eq hae hgcont continuousOn_const hsub
  intro θ hθ
  have h0 : w θ - v θ = 0 := heqon (Set.Ioo_subset_Icc_self hθ)
  exact sub_eq_zero.mp h0

end

end Work.FTS.PhiStar.FlatWAux.PsiExpAux
