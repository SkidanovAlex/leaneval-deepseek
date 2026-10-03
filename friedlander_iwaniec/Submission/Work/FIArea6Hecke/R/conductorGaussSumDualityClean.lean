import Mathlib
import Submission.Work.FIArea6Hecke.R.ConductorThetaDefs
import Submission.Work.FIArea6Hecke.R.StrictConductorDefs
import Submission.Work.FIArea6Hecke.R2.Defs
import Submission.Work.FIArea6Hecke.R2.Support
import Submission.Work.FIArea6Hecke.R2.CrsMinIsCRS
import Submission.Work.FIArea6Hecke.R2.BoxSumKappa
import Submission.Work.FIArea6Hecke.R2.GsUnitK
import Submission.Work.FIArea6Hecke.R2.GsNonunitK
import Submission.Work.FIArea6Hecke.R2.Nonvanishing
import Submission.Work.FIArea6Hecke.CGD.Reindex
import Submission.Work.FIArea6Hecke.CGD.ChiUnits

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.FIArea6Hecke.R

open scoped BigOperators

noncomputable section

/-- `star (gconjInt γ) = γ`: the conjugate Gaussian integer is the complex conjugate. -/
lemma star_gconjInt (γ : GaussianInt) : star (gconjInt γ) = γ := by
  ext <;> simp [gconjInt]

theorem conductorGaussSumDualityClean (M : GaussianInt) (hM : M ≠ 0)
    (hg : 2 ≤ Work.FIPlan.gnorm M) (chi₀ : GaussianInt → ℂ)
    (hchi : Work.FIArea6Hecke.R.IsCharModStrict M chi₀)
    (hprim : Work.FIArea6Hecke.R.IsPrimitiveCharAt M chi₀)
    (hnt : ∃ z : GaussianInt, Work.FIArea6Hecke.R.IsUnitMod M z ∧ chi₀ z ≠ 1) :
    ∃ τ : ℂ, τ ≠ 0 ∧
      (∀ ξ : GaussianInt, ¬ (M ∣ ξ) → Work.FIArea6Hecke.R.condGaussSum M chi₀ ξ = 0) ∧
      (∀ γ : GaussianInt, Work.FIArea6Hecke.R.condGaussSum M chi₀ (M * γ) =
        ((Work.FIPlan.gnorm M : ℕ) : ℂ) * τ * star (chi₀ (Work.FIArea6Hecke.R.gconjInt γ))) := by
  classical
  -- the canonical complete residue system mod `M` and the two Gauss-sum inputs
  set S : Finset GaussianInt := Work.FIArea6Hecke.R2.crsMin M with hSdef
  have hS : IsCRS M S := Work.FIArea6Hecke.R2.CrsMinIsCRS M hM
  have hGs1 : Gs M chi₀ S 1 ≠ 0 :=
    Work.FIArea6Hecke.R2.Gs_one_ne_zero M hM hg S hS chi₀ hchi hprim hnt
  have hkap : ((Work.FIArea6Hecke.R2.kappa M : ℕ) : ℂ) ≠ 0 := by
    have hpos : 0 < Work.FIArea6Hecke.R2.kappa M := by
      rw [Work.FIArea6Hecke.R2.kappa, Finset.card_pos]
      refine ⟨0, ?_⟩
      rw [Work.FIArea6Hecke.R2.boxK, Finset.mem_filter]
      refine ⟨?_, dvd_zero M⟩
      rw [Work.FIArea6Hecke.R.gbox]
      refine Finset.mem_image.mpr ⟨(0, 0), ?_, ?_⟩
      · exact Finset.mem_product.mpr
          ⟨Finset.mem_range.mpr (Work.FIArea6Hecke.R2.gnorm_pos hM),
            Finset.mem_range.mpr (Work.FIArea6Hecke.R2.gnorm_pos hM)⟩
      · ext <;> simp
    exact_mod_cast Nat.pos_iff_ne_zero.mp hpos
  have hN : ((Work.FIPlan.gnorm M : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (Work.FIArea6Hecke.R2.gnorm_ne_zero hM : (Work.FIPlan.gnorm M : ℕ) ≠ 0)
  -- the box sum of the `M`-periodic weight `chi₀ · ekern M (M*γ)` equals `kappa M` times `Gs`
  have hbox : ∀ γ : GaussianInt,
      condGaussSum M chi₀ (M * γ)
        = ((Work.FIArea6Hecke.R2.kappa M : ℕ) : ℂ) * Gs M chi₀ S (gconjInt γ) := by
    intro γ
    have hper : ∀ z w : GaussianInt, M ∣ (z - w) →
        chi₀ z * ekern M (M * γ) z = chi₀ w * ekern M (M * γ) w := by
      intro z w hzw
      have h1 : chi₀ z = chi₀ w := hchi.2.2.2.1 z w hzw
      have h2 : ekern M (M * γ) z = ekern M (M * γ) w := by
        have hdecomp : z = w + (z - w) := by ring
        rw [hdecomp, Work.FIArea6Hecke.R2.ekern_add_of_dvd M (M * γ) w (z - w) hM
          (dvd_mul_right M γ) hzw]
      rw [h1, h2]
    rw [Work.FIArea6Hecke.CGD.Reindex M chi₀ (M * γ),
      Work.FIArea6Hecke.R2.BoxSumKappa M hM S hS
        (fun s => chi₀ s * ekern M (M * γ) s) hper]
    congr 1
    rw [Gs]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    rw [star_gconjInt]
  -- the value of `condGaussSum M chi₀ M`
  have hM1 : condGaussSum M chi₀ M
      = ((Work.FIArea6Hecke.R2.kappa M : ℕ) : ℂ) * Gs M chi₀ S 1 := by
    have hg1 : gconjInt (1 : GaussianInt) = 1 := by ext <;> simp [gconjInt]
    simpa [hg1] using hbox 1
  refine ⟨condGaussSum M chi₀ M / ((Work.FIPlan.gnorm M : ℕ) : ℂ), ?_, ?_, ?_⟩
  · -- `τ ≠ 0`
    have hne : condGaussSum M chi₀ M ≠ 0 := by
      rw [hM1]; exact mul_ne_zero hkap hGs1
    exact div_ne_zero hne hN
  · -- vanishing off the support
    intro ξ hξ
    exact Work.FIArea6Hecke.R2.condGaussSum_eq_zero_of_not_dvd M ξ hM chi₀ hchi hξ
  · -- the duality
    intro γ
    rw [hbox γ]
    by_cases hγ : IsUnitMod M (gconjInt γ)
    · rw [Work.FIArea6Hecke.R2.GsUnitK M hM hg S hS chi₀ hchi (gconjInt γ) hγ, hM1]
      field_simp
    · rw [Work.FIArea6Hecke.R2.GsNonunitK M hM hg S hS chi₀ hchi hprim hnt (gconjInt γ) hγ,
        hchi.2.2.2.2 (gconjInt γ) hγ, star_zero, mul_zero, mul_zero]

end

end Work.FIArea6Hecke.R
