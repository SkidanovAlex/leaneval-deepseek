import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BSKinetic.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The shifted (translation-normalised) one-body big-box state

The one-body big-box kinetic form `Work.BSKinetic.bsOneBody ℓ F u ψ` is

    `(2π)⁻³ ∫_p F(‖p‖)·‖kinFT (χ_u · Q_{Λ(u)}ψ)‖²`,

with the moving window `bsWin ℓ u x = χ((x − ℓu)/ℓ)` and the box mean-free part
`bsQ ℓ u ψ = ψ − bsMean ℓ u ψ`.  Both the window and the state hence depend on the parameter `u`
in a non-linear way, which is awkward for continuity estimates.

The trick used here is to **transport the state back to the origin**: since

    `bsWin ℓ u (z + ℓ•u) = chiScale ℓ z`,  `bsQ ℓ u ψ (z + ℓ•u) = ψ (z + ℓ•u) − bsMean ℓ u ψ`,

the localised state `(bsWin ℓ u · bsQ ℓ u ψ)(z + ℓ•u)` is the *shifted state*

    `bsShift ℓ ψ u z = chiScale ℓ z · (ψ (z + ℓ•u) − bsMean ℓ u ψ)`,

whose support is contained in the **fixed** box `acube ℓ` for every `u`.  Since translating a
function only multiplies its `kinFT` by a complex number of modulus one, the kinetic form is
unchanged: `bsOneBody ℓ F u ψ = (2π)⁻³·bsW F (bsShift ℓ ψ u)` (`bsOneBody_eq_bsW_shift`).

This is the state class on which the continuity, `L²` and `H¹` estimates of the family
`u ↦ bsShift ℓ ψ u` are formulated (`bsShift_L2_tendsto`, `bsShift_H1_tendsto`,
`bsShift_H1_bounded`), together with the weighted Plancherel bound `bsW_le_L2_Dir`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BSKinetic.Decomp

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

set_option autoImplicit false

/-! ## 1. The shifted state -/

/-- **The shifted big-box one-body state**: the moving-box localised mean-free state, transported
so that its window sits at the origin, `z ↦ χ(z)·(ψ(z + ℓ•u) − ⨍_{acube ℓ}ψ(ℓ•u + ·))`. -/
noncomputable def bsShift (ℓ : ℝ) (ψ : ℝ³ → ℝ) (u : ℝ³) : ℝ³ → ℝ :=
  fun z => chiScale ℓ z * (ψ (z + ℓ • u) - bsMean ℓ u ψ)

@[simp] lemma bsShift_apply (ℓ : ℝ) (ψ : ℝ³ → ℝ) (u z : ℝ³) :
    bsShift ℓ ψ u z = chiScale ℓ z * (ψ (z + ℓ • u) - bsMean ℓ u ψ) := rfl

/-! ## 2. The `p`-space transform and the weighted norm² -/

/-- The `p`-convention Fourier transform of the complexification of a real one-body state. -/
noncomputable def bsPsi (h : ℝ³ → ℝ) (p : ℝ³) : ℂ :=
  kinFT (fun z : ℝ³ => (h z : ℂ)) p

/-- The `F`-weighted `L²` norm² of the `p`-transform of a real one-body state,
`∫_p F(‖p‖)·‖bsPsi h p‖²` (the `p`-space quadratic form of the symbol `F(√−Δ)`). -/
noncomputable def bsW (F : ℝ → ℝ) (h : ℝ³ → ℝ) : ℝ :=
  ∫ p : ℝ³, F ‖p‖ * ‖bsPsi h p‖ ^ 2

/-- The `L²` mass `∫_z (h z)²` of a one-body state. -/
noncomputable def bsL2 (h : ℝ³ → ℝ) : ℝ := ∫ z : ℝ³, (h z) ^ 2

/-- The Dirichlet word `Σ_k ∫_z (∂_k h z)²` of a one-body state. -/
noncomputable def bsDir (h : ℝ³ → ℝ) : ℝ :=
  ∑ k : Fin 3, ∫ z : ℝ³, (fderiv ℝ h z (kcStdBasis k)) ^ 2


/-! ## 3. Integrability and additivity of `bsPsi` (shared with the sibling modules) -/

lemma norm_exp_phase (p z : ℝ³) :
    ‖Complex.exp (-(Complex.I * (inner ℝ p z : ℂ)))‖ = 1 := by
  rw [Complex.norm_exp]
  simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]

lemma integrable_ofReal_state {h : ℝ³ → ℝ} (hd : ContDiff ℝ (⊤ : ENat) h)
    (hc : HasCompactSupport h) : Integrable (fun z : ℝ³ => (h z : ℂ)) :=
  (Complex.continuous_ofReal.comp hd.continuous).integrable_of_hasCompactSupport
    (hc.comp_left (by simp : ((0 : ℝ) : ℂ) = 0))

lemma integrable_phase_mul {h : ℝ³ → ℝ} (hd : ContDiff ℝ (⊤ : ENat) h)
    (hc : HasCompactSupport h) (p : ℝ³) :
    Integrable (fun z : ℝ³ =>
      Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) * (h z : ℂ)) := by
  have h1 : Integrable (fun z : ℝ³ =>
      (h z : ℂ) * Complex.exp (-(Complex.I * (inner ℝ p z : ℂ)))) :=
    (integrable_ofReal_state hd hc).mul_bdd (by fun_prop)
      (Eventually.of_forall (fun z => le_of_eq (norm_exp_phase p z)))
  exact h1.congr (Eventually.of_forall (fun z => mul_comm _ _))

lemma bsPsi_sub {h₁ h₂ : ℝ³ → ℝ}
    (h₁d : ContDiff ℝ (⊤ : ENat) h₁) (h₁c : HasCompactSupport h₁)
    (h₂d : ContDiff ℝ (⊤ : ENat) h₂) (h₂c : HasCompactSupport h₂) (p : ℝ³) :
    bsPsi (fun z => h₁ z - h₂ z) p = bsPsi h₁ p - bsPsi h₂ p := by
  rw [bsPsi, bsPsi, bsPsi, kinFT, kinFT, kinFT]
  have hpt : ∀ z : ℝ³, Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) * (((h₁ z - h₂ z : ℝ) : ℂ))
      = Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) * ((h₁ z : ℝ) : ℂ)
        - Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) * ((h₂ z : ℝ) : ℂ) := by
    intro z; push_cast; ring
  rw [show (∫ z : ℝ³, Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) * (((h₁ z - h₂ z : ℝ) : ℂ)))
      = ∫ z : ℝ³, (Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) * ((h₁ z : ℝ) : ℂ)
        - Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) * ((h₂ z : ℝ) : ℂ)) from
      integral_congr_ae (Eventually.of_forall hpt)]
  rw [integral_sub (integrable_phase_mul h₁d h₁c p) (integrable_phase_mul h₂d h₂c p)]

/-! ## 4.  Regularity of the shifted state -/

lemma contDiff_bsShift {ℓ : ℝ} (hℓ' : 0 < ℓ) {ψ : ℝ³ → ℝ} (hψ : ContDiff ℝ (⊤ : ENat) ψ)
    (u : ℝ³) : ContDiff ℝ (⊤ : ENat) (bsShift ℓ ψ u) := by
  have hχ : ContDiff ℝ (⊤ : ENat) (chiScale ℓ) := chiScale_contDiff (ne_of_gt hℓ')
  have hshift : ContDiff ℝ (⊤ : ENat) (fun z : ℝ³ => ψ (z + ℓ • u)) :=
    hψ.comp (by fun_prop)
  have hconst : ContDiff ℝ (⊤ : ENat) (fun _ : ℝ³ => bsMean ℓ u ψ) := contDiff_const
  exact hχ.mul (hshift.sub hconst)

lemma hasCompactSupport_bsShift {ℓ : ℝ} (hℓ : ℓ ≠ 0) {ψ : ℝ³ → ℝ} (u : ℝ³) :
    HasCompactSupport (bsShift ℓ ψ u) := by
  have h : bsShift ℓ ψ u = chiScale ℓ * fun z : ℝ³ => (ψ (z + ℓ • u) - bsMean ℓ u ψ) := rfl
  rw [h]
  exact (chiScale_hasCompactSupport hℓ).mul_right


end Work.BSKinetic.Decomp
