import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BSKinetic.Decomp.integrable_fsKinCoeff_mul_bsPsi_sq
import Submission.Work.BoseFixB2.Defs
import Submission.Work.BoseKinLoc.Kinetic.momForm_le_box
import Submission.Work.BoseKinLoc.Kinetic.neuFracTrialDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB2.Polar.fsT_parallelogram` — FS `eq:DefT`'s word is a quadratic form

The one-body localised kinetic word of Fournais–Solovej `eq:DefT`,

`fsT ℓ d s εT b u ψ = neuWord + gapWord + momWord + mainWord`,

is a **quadratic form** in the one-body state `ψ`; this file records the resulting
*parallelogram identity*

`fsT u (f + g) + fsT u (f − g) = 2·fsT u f + 2·fsT u g`,

which is the analytic input of the polarisation used by §6 (`lem:LocMatrices`) of the paper.

## The four summands

Each of the four summands of `fsT_eq_sum` is the diagonal of a *symmetric bilinear* form, so each
satisfies the parallelogram identity separately:

* `gapWord = bℓ⁻²·gapBare`, `gapBare ℓ u ψ = ∫_{Λ(u)}(Q_uψ)²`: `Q_u` is linear in `ψ`
  (`Qfree_add`, `Qfree_sub`, from the linearity of the box mean), so the identity is the pointwise
  identity `(x+y)² + (x−y)² = 2x² + 2y²` plus additivity of the box integral
  (`gapBare_parallelogram`, on top of the generic `mul_parallelogram`).
* `mainWord` is a combination of two `bsOneBody ℓ (fsKinCoeff c) u` words; the `p`-integral
  defining `bsOneBody` is honest (its integrand is integrable, being the symbol `[‖p‖−c]₊²`
  times the squared Fourier transform of a smooth compactly supported state), and the identity
  reduces to the parallelogram law in `ℂ` for the two Fourier transforms.
* `momWord = bε_T(dℓ)⁻²·momForm` is of the same shape, with the bounded symbol `momProj ≤ 1`.
* `neuWord = ½ε_T(dℓ)⁻²·neuFrac ℓ a2 u (Q_uψ)` with `a2 = (dℓ)⁻²`: here `neuFrac` is the `sInf`
  of the Dirichlet trial functional `T(φ,g) = ∫_Λφ² − 2a₂∫_Λφg + a₂(Σ_k∫_Λ(∂_kg)² + a₂∫_Λg²)`
  over the smooth compactly supported trials `g`.  The trial functional is the diagonal of a
  symmetric bilinear form in the *pair* `(φ,g)` (`trialVal_quadric`), and the trial class is a
  linear space stable under `g ↦ ±g` and halving; hence the `sInf`s obey the parallelogram
  identity (`neuFrac_parallelogram_aux`), by a two-sided `sInf` argument
  (`csInf_add` and `le_csInf`) that never needs a minimiser:
  * the elements of `trialSet(f+g) + trialSet(f−g)` are `2T(f,·) + 2T(g,·) ≥ 2V(f) + 2V(g)`;
  * the double of an element of `trialSet f + trialSet g` is `T(f+g,·) + T(f−g,·) ≥ V(f+g) + V(f−g)`.
-/

noncomputable section

open MeasureTheory
open scoped Pointwise

namespace Work.BoseFixB2.Polar

open Work.BoseKinLoc Work.BSKinetic

namespace FsTAux

/-! ## 1. A bilinear parallelogram identity for box integrals

For continuous `a, b, c, d` on a compact box `Λ`, the integral of the product is a bilinear form,
so it satisfies the polarisation of the parallelogram identity.  This single identity covers all
the "sum of squares" and "cross term" manipulations below. -/

lemma mul_parallelogram {Λ : Set (EuclideanSpace ℝ (Fin 3))} (hΛ : IsCompact Λ)
    {a b c d : EuclideanSpace ℝ (Fin 3) → ℝ}
    (ha : Continuous a) (hb : Continuous b) (hc : Continuous c) (hd : Continuous d) :
    (∫ z in Λ, (a z + b z) * (c z + d z)) + (∫ z in Λ, (a z - b z) * (c z - d z))
      = 2 * (∫ z in Λ, a z * c z) + 2 * (∫ z in Λ, b z * d z) := by
  have hI1 : IntegrableOn (fun z => (a z + b z) * (c z + d z)) Λ volume :=
    ((ha.add hb).mul (hc.add hd)).continuousOn.integrableOn_compact hΛ
  have hI2 : IntegrableOn (fun z => (a z - b z) * (c z - d z)) Λ volume :=
    ((ha.sub hb).mul (hc.sub hd)).continuousOn.integrableOn_compact hΛ
  have hI3 : IntegrableOn (fun z => a z * c z) Λ volume :=
    (ha.mul hc).continuousOn.integrableOn_compact hΛ
  have hI4 : IntegrableOn (fun z => b z * d z) Λ volume :=
    (hb.mul hd).continuousOn.integrableOn_compact hΛ
  have e1 : (∫ z in Λ, (a z + b z) * (c z + d z)) + (∫ z in Λ, (a z - b z) * (c z - d z))
      = ∫ z in Λ, ((a z + b z) * (c z + d z) + (a z - b z) * (c z - d z)) :=
    (MeasureTheory.integral_add hI1 hI2).symm
  have e2 : 2 * (∫ z in Λ, a z * c z) + 2 * (∫ z in Λ, b z * d z)
      = ∫ z in Λ, (2 * (a z * c z) + 2 * (b z * d z)) := by
    rw [← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_const_mul,
      ← MeasureTheory.integral_add (hI3.const_mul 2) (hI4.const_mul 2)]
  rw [e1, e2]
  apply MeasureTheory.setIntegral_congr_fun hΛ.measurableSet
  intro z _
  ring

/-- The same identity for a finite family of pairs of continuous functions (used for the
`Fin 3`-sum over the directions of the gradient). -/
lemma sum_mul_parallelogram {ι : Type*} [Fintype ι]
    {Λ : Set (EuclideanSpace ℝ (Fin 3))} (hΛ : IsCompact Λ)
    {A B : ι → EuclideanSpace ℝ (Fin 3) → ℝ}
    (hA : ∀ i, Continuous (A i)) (hB : ∀ i, Continuous (B i)) :
    (∑ i, ∫ z in Λ, (A i z + B i z) * (A i z + B i z))
      + (∑ i, ∫ z in Λ, (A i z - B i z) * (A i z - B i z))
      = 2 * (∑ i, ∫ z in Λ, A i z * A i z) + 2 * (∑ i, ∫ z in Λ, B i z * B i z) := by
  have hpt : ∀ i : ι, (∫ z in Λ, (A i z + B i z) * (A i z + B i z))
      + (∫ z in Λ, (A i z - B i z) * (A i z - B i z))
      = 2 * (∫ z in Λ, A i z * A i z) + 2 * (∫ z in Λ, B i z * B i z) :=
    fun i => mul_parallelogram hΛ (hA i) (hB i) (hA i) (hB i)
  rw [← Finset.sum_add_distrib, Finset.sum_congr rfl (fun i _ => hpt i), Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum]

/-! ## 2. Admissible trials of the Dirichlet functional -/

/-- The trial class of `neuFrac`: globally smooth functions with compact support. -/
def Adm (g : EuclideanSpace ℝ (Fin 3) → ℝ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) g ∧ HasCompactSupport g

namespace Adm

lemma add {g h : EuclideanSpace ℝ (Fin 3) → ℝ} (hg : Adm g) (hh : Adm h) :
    Adm (fun z => g z + h z) :=
  ⟨hg.1.add hh.1, hg.2.add hh.2⟩

lemma sub {g h : EuclideanSpace ℝ (Fin 3) → ℝ} (hg : Adm g) (hh : Adm h) :
    Adm (fun z => g z - h z) :=
  ⟨hg.1.sub hh.1, hg.2.sub hh.2⟩

lemma smul (c : ℝ) {g : EuclideanSpace ℝ (Fin 3) → ℝ} (hg : Adm g) :
    Adm (fun z => c * g z) :=
  ⟨contDiff_const.mul hg.1, HasCompactSupport.mul_left hg.2⟩

lemma div_two {g : EuclideanSpace ℝ (Fin 3) → ℝ} (hg : Adm g) :
    Adm (fun z => g z / 2) := by
  have h := smul (2⁻¹) hg
  have heq : (fun z : EuclideanSpace ℝ (Fin 3) => 2⁻¹ * g z) = fun z => g z / 2 := by
    funext z; rw [div_eq_inv_mul]
  rwa [heq] at h

end Adm

/-! ## 3. The trial functional of `neuFrac` is the diagonal of a symmetric bilinear form -/

/-- **The quadric identity for the Dirichlet trial functional.**  For continuous states `φ₁, φ₂`
and admissible trials `g₁, g₂`,

`T(φ₁+φ₂, g₁+g₂) + T(φ₁−φ₂, g₁−g₂) = 2T(φ₁,g₁) + 2T(φ₂,g₂)`,

where `T = Work.BoseKinLoc.Kinetic.trialVal`.  This is the statement that `T` is the diagonal of
the symmetric bilinear form `(φ,g) ↦ ∫_Λφφ' − a₂∫_Λ(φg' + φ'g) + a₂(⟨∇g,∇g'⟩ + a₂∫_Λgg')`. -/
lemma trialVal_quadric {ℓ a2 : ℝ} (hℓ : 0 < ℓ) (u : EuclideanSpace ℝ (Fin 3))
    {φ₁ φ₂ g₁ g₂ : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hφ₁ : Continuous φ₁) (hφ₂ : Continuous φ₂) (hg₁ : Adm g₁) (hg₂ : Adm g₂) :
    Kinetic.trialVal ℓ a2 u (fun z => φ₁ z + φ₂ z) (fun z => g₁ z + g₂ z)
      + Kinetic.trialVal ℓ a2 u (fun z => φ₁ z - φ₂ z) (fun z => g₁ z - g₂ z)
      = 2 * Kinetic.trialVal ℓ a2 u φ₁ g₁ + 2 * Kinetic.trialVal ℓ a2 u φ₂ g₂ := by
  have hΛ : IsCompact (lamBox ℓ u) := Gap.isCompact_lamBox hℓ u
  have hms : MeasurableSet (lamBox ℓ u) := hΛ.measurableSet
  have hgtop : (((⊤ : ℕ∞) : WithTop ℕ∞)) ≠ 0 := by simp
  -- the square masses of the states
  have hA : (∫ z in lamBox ℓ u, (φ₁ z + φ₂ z) ^ 2)
        + (∫ z in lamBox ℓ u, (φ₁ z - φ₂ z) ^ 2)
      = 2 * (∫ z in lamBox ℓ u, (φ₁ z) ^ 2)
        + 2 * (∫ z in lamBox ℓ u, (φ₂ z) ^ 2) := by
    have h := mul_parallelogram (Λ := lamBox ℓ u) hΛ hφ₁ hφ₂ hφ₁ hφ₂
    simpa only [pow_two] using h
  -- the cross terms
  have hB : (∫ z in lamBox ℓ u, (φ₁ z + φ₂ z) * (g₁ z + g₂ z))
        + (∫ z in lamBox ℓ u, (φ₁ z - φ₂ z) * (g₁ z - g₂ z))
      = 2 * (∫ z in lamBox ℓ u, φ₁ z * g₁ z)
        + 2 * (∫ z in lamBox ℓ u, φ₂ z * g₂ z) :=
    mul_parallelogram hΛ hφ₁ hφ₂ hg₁.1.continuous hg₂.1.continuous
  -- the gradient energies of the trials
  have hC : (∑ k : Fin 3, ∫ z in lamBox ℓ u,
        (fderiv ℝ (fun z => g₁ z + g₂ z) z) (Submission.BoseGases.kcStdBasis k) ^ 2)
      + (∑ k : Fin 3, ∫ z in lamBox ℓ u,
        (fderiv ℝ (fun z => g₁ z - g₂ z) z) (Submission.BoseGases.kcStdBasis k) ^ 2)
      = 2 * (∑ k : Fin 3, ∫ z in lamBox ℓ u,
          (fderiv ℝ g₁ z) (Submission.BoseGases.kcStdBasis k) ^ 2)
        + 2 * (∑ k : Fin 3, ∫ z in lamBox ℓ u,
          (fderiv ℝ g₂ z) (Submission.BoseGases.kcStdBasis k) ^ 2) := by
    have hpt : ∀ k : Fin 3,
        (∫ z in lamBox ℓ u,
            (fderiv ℝ (fun z => g₁ z + g₂ z) z) (Submission.BoseGases.kcStdBasis k) ^ 2)
          + (∫ z in lamBox ℓ u,
            (fderiv ℝ (fun z => g₁ z - g₂ z) z) (Submission.BoseGases.kcStdBasis k) ^ 2)
        = 2 * (∫ z in lamBox ℓ u,
            (fderiv ℝ g₁ z) (Submission.BoseGases.kcStdBasis k) ^ 2)
          + 2 * (∫ z in lamBox ℓ u,
            (fderiv ℝ g₂ z) (Submission.BoseGases.kcStdBasis k) ^ 2) := by
      intro k
      have hc₁ : Continuous
          (fun z => (fderiv ℝ g₁ z) (Submission.BoseGases.kcStdBasis k)) :=
        (hg₁.1.continuous_fderiv hgtop).clm_apply continuous_const
      have hc₂ : Continuous
          (fun z => (fderiv ℝ g₂ z) (Submission.BoseGases.kcStdBasis k)) :=
        (hg₂.1.continuous_fderiv hgtop).clm_apply continuous_const
      have e1 : (∫ z in lamBox ℓ u,
            (fderiv ℝ (fun z => g₁ z + g₂ z) z) (Submission.BoseGases.kcStdBasis k) ^ 2)
          = ∫ z in lamBox ℓ u,
            ((fderiv ℝ g₁ z) (Submission.BoseGases.kcStdBasis k)
              + (fderiv ℝ g₂ z) (Submission.BoseGases.kcStdBasis k)) ^ 2 := by
        apply MeasureTheory.setIntegral_congr_fun hms
        intro z _
        show (fderiv ℝ (fun z => g₁ z + g₂ z) z) (Submission.BoseGases.kcStdBasis k) ^ 2
          = ((fderiv ℝ g₁ z) (Submission.BoseGases.kcStdBasis k)
              + (fderiv ℝ g₂ z) (Submission.BoseGases.kcStdBasis k)) ^ 2
        have hfeq : (fun z : EuclideanSpace ℝ (Fin 3) => g₁ z + g₂ z) = g₁ + g₂ := by
          funext z; rfl
        rw [hfeq, fderiv_add ((hg₁.1.differentiable hgtop).differentiableAt)
          ((hg₂.1.differentiable hgtop).differentiableAt), ContinuousLinearMap.add_apply]
      have e2 : (∫ z in lamBox ℓ u,
            (fderiv ℝ (fun z => g₁ z - g₂ z) z) (Submission.BoseGases.kcStdBasis k) ^ 2)
          = ∫ z in lamBox ℓ u,
            ((fderiv ℝ g₁ z) (Submission.BoseGases.kcStdBasis k)
              - (fderiv ℝ g₂ z) (Submission.BoseGases.kcStdBasis k)) ^ 2 := by
        apply MeasureTheory.setIntegral_congr_fun hms
        intro z _
        show (fderiv ℝ (fun z => g₁ z - g₂ z) z) (Submission.BoseGases.kcStdBasis k) ^ 2
          = ((fderiv ℝ g₁ z) (Submission.BoseGases.kcStdBasis k)
              - (fderiv ℝ g₂ z) (Submission.BoseGases.kcStdBasis k)) ^ 2
        have hfeq : (fun z : EuclideanSpace ℝ (Fin 3) => g₁ z - g₂ z) = g₁ - g₂ := by
          funext z; rfl
        rw [hfeq, fderiv_sub ((hg₁.1.differentiable hgtop).differentiableAt)
          ((hg₂.1.differentiable hgtop).differentiableAt), ContinuousLinearMap.sub_apply]
      rw [e1, e2]
      have h := mul_parallelogram (Λ := lamBox ℓ u) hΛ hc₁ hc₂ hc₁ hc₂
      simpa only [pow_two] using h
    calc (∑ k : Fin 3, ∫ z in lamBox ℓ u,
            (fderiv ℝ (fun z => g₁ z + g₂ z) z) (Submission.BoseGases.kcStdBasis k) ^ 2)
          + (∑ k : Fin 3, ∫ z in lamBox ℓ u,
            (fderiv ℝ (fun z => g₁ z - g₂ z) z) (Submission.BoseGases.kcStdBasis k) ^ 2)
        = ∑ k : Fin 3, ((∫ z in lamBox ℓ u,
              (fderiv ℝ (fun z => g₁ z + g₂ z) z) (Submission.BoseGases.kcStdBasis k) ^ 2)
            + (∫ z in lamBox ℓ u,
              (fderiv ℝ (fun z => g₁ z - g₂ z) z) (Submission.BoseGases.kcStdBasis k) ^ 2)) :=
          (Finset.sum_add_distrib).symm
      _ = ∑ k : Fin 3, (2 * (∫ z in lamBox ℓ u,
              (fderiv ℝ g₁ z) (Submission.BoseGases.kcStdBasis k) ^ 2)
            + 2 * (∫ z in lamBox ℓ u,
              (fderiv ℝ g₂ z) (Submission.BoseGases.kcStdBasis k) ^ 2)) :=
          Finset.sum_congr rfl (fun k _ => hpt k)
      _ = 2 * (∑ k : Fin 3, ∫ z in lamBox ℓ u,
              (fderiv ℝ g₁ z) (Submission.BoseGases.kcStdBasis k) ^ 2)
            + 2 * (∑ k : Fin 3, ∫ z in lamBox ℓ u,
              (fderiv ℝ g₂ z) (Submission.BoseGases.kcStdBasis k) ^ 2) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  -- the square masses of the trials
  have hD : (∫ z in lamBox ℓ u, (g₁ z + g₂ z) ^ 2)
        + (∫ z in lamBox ℓ u, (g₁ z - g₂ z) ^ 2)
      = 2 * (∫ z in lamBox ℓ u, (g₁ z) ^ 2)
        + 2 * (∫ z in lamBox ℓ u, (g₂ z) ^ 2) := by
    have h := mul_parallelogram (Λ := lamBox ℓ u) hΛ hg₁.1.continuous hg₂.1.continuous
      hg₁.1.continuous hg₂.1.continuous
    simpa only [pow_two] using h
  rw [Kinetic.trialVal, Kinetic.trialVal, Kinetic.trialVal, Kinetic.trialVal]
  beta_reduce
  linear_combination (norm := ring) hA - (2 * a2) * hB + a2 * hC + (a2 ^ 2) * hD

/-- **The quadric identity in the "halved" form** used for the lower bound on the sum of the two
trial sets: `T(φ₁+φ₂, e) + T(φ₁−φ₂, h) = 2T(φ₁, (e+h)/2) + 2T(φ₂, (e−h)/2)`. -/
lemma trialVal_quadric_halved {ℓ a2 : ℝ} (hℓ : 0 < ℓ) (u : EuclideanSpace ℝ (Fin 3))
    {φ₁ φ₂ e h : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hφ₁ : Continuous φ₁) (hφ₂ : Continuous φ₂) (he : Adm e) (hh : Adm h) :
    Kinetic.trialVal ℓ a2 u (fun z => φ₁ z + φ₂ z) e
      + Kinetic.trialVal ℓ a2 u (fun z => φ₁ z - φ₂ z) h
      = 2 * Kinetic.trialVal ℓ a2 u φ₁ (fun z => (e z + h z) / 2)
        + 2 * Kinetic.trialVal ℓ a2 u φ₂ (fun z => (e z - h z) / 2) := by
  have hq := trialVal_quadric (a2 := a2) hℓ u hφ₁ hφ₂
    (Adm.div_two (Adm.add he hh)) (Adm.div_two (Adm.sub he hh))
  have heq1 : (fun z : EuclideanSpace ℝ (Fin 3) => (e z + h z) / 2 + (e z - h z) / 2) = e := by
    funext z; ring
  have heq2 : (fun z : EuclideanSpace ℝ (Fin 3) => (e z + h z) / 2 - (e z - h z) / 2) = h := by
    funext z; ring
  rw [heq1, heq2] at hq
  exact hq

/-! ## 4. The parallelogram identity for `neuFrac` -/

/-- **`neuFrac` is a quadratic form**: it satisfies the parallelogram identity.  The proof never
uses a minimiser of the trial functional, only that
* the trial functional is the diagonal of a symmetric bilinear form (`trialVal_quadric`),
* the trial class is closed under `+`, `−` and halving (`Adm`),
* `sInf (A + B) = sInf A + sInf B` (`csInf_add`), the trial sets being nonempty (`0` is an
  admissible trial) and bounded below (`bddBelow_trialSet_of_integrableOn'`). -/
theorem neuFrac_parallelogram_aux {ℓ a2 : ℝ} (hℓ : 0 < ℓ) (ha2 : 0 < a2)
    (u : EuclideanSpace ℝ (Fin 3)) {f g : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    neuFrac ℓ a2 u (fun z => f z + g z) + neuFrac ℓ a2 u (fun z => f z - g z)
      = 2 * neuFrac ℓ a2 u f + 2 * neuFrac ℓ a2 u g := by
  have hΛ : IsCompact (lamBox ℓ u) := Gap.isCompact_lamBox hℓ u
  have hFc : Continuous (fun z => f z + g z) := hf.continuous.add hg.continuous
  have hGc : Continuous (fun z => f z - g z) := hf.continuous.sub hg.continuous
  have hneF : (Kinetic.trialSet ℓ a2 u (fun z => f z + g z)).Nonempty :=
    ⟨_, Kinetic.zero_mem_trialSet ℓ a2 u (fun z => f z + g z)⟩
  have hneG : (Kinetic.trialSet ℓ a2 u (fun z => f z - g z)).Nonempty :=
    ⟨_, Kinetic.zero_mem_trialSet ℓ a2 u (fun z => f z - g z)⟩
  have hnef : (Kinetic.trialSet ℓ a2 u f).Nonempty :=
    ⟨_, Kinetic.zero_mem_trialSet ℓ a2 u f⟩
  have hneg : (Kinetic.trialSet ℓ a2 u g).Nonempty :=
    ⟨_, Kinetic.zero_mem_trialSet ℓ a2 u g⟩
  have hbddF : BddBelow (Kinetic.trialSet ℓ a2 u (fun z => f z + g z)) :=
    Kinetic.bddBelow_trialSet_of_integrableOn' ha2.le u
      ((hFc.pow 2).continuousOn.integrableOn_compact hΛ)
  have hbddG : BddBelow (Kinetic.trialSet ℓ a2 u (fun z => f z - g z)) :=
    Kinetic.bddBelow_trialSet_of_integrableOn' ha2.le u
      ((hGc.pow 2).continuousOn.integrableOn_compact hΛ)
  have hbddf : BddBelow (Kinetic.trialSet ℓ a2 u f) :=
    Kinetic.bddBelow_trialSet_of_integrableOn' ha2.le u
      ((hf.continuous.pow 2).continuousOn.integrableOn_compact hΛ)
  have hbddg : BddBelow (Kinetic.trialSet ℓ a2 u g) :=
    Kinetic.bddBelow_trialSet_of_integrableOn' ha2.le u
      ((hg.continuous.pow 2).continuousOn.integrableOn_compact hΛ)
  -- `f + g` and `f - g` for brevity
  have h1 : 2 * neuFrac ℓ a2 u f + 2 * neuFrac ℓ a2 u g
      ≤ neuFrac ℓ a2 u (fun z => f z + g z) + neuFrac ℓ a2 u (fun z => f z - g z) := by
    rw [Kinetic.neuFrac_eq_sInf_trialSet ℓ a2 u f,
      Kinetic.neuFrac_eq_sInf_trialSet ℓ a2 u g,
      Kinetic.neuFrac_eq_sInf_trialSet ℓ a2 u (fun z => f z + g z),
      Kinetic.neuFrac_eq_sInf_trialSet ℓ a2 u (fun z => f z - g z)]
    rw [← csInf_add hneF hbddF hneG hbddG]
    refine le_csInf (hneF.add hneG) ?_
    intro c hc
    obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_add.mp hc
    rw [← hab]
    obtain ⟨e, he, hec, heq⟩ := ha
    obtain ⟨h, hh, hhc, hhq⟩ := hb
    rw [heq, hhq]
    rw [trialVal_quadric_halved (a2 := a2) hℓ u hf.continuous hg.continuous
      ⟨he, hec⟩ ⟨hh, hhc⟩]
    have hle1 : sInf (Kinetic.trialSet ℓ a2 u f)
        ≤ Kinetic.trialVal ℓ a2 u f (fun z => (e z + h z) / 2) :=
      csInf_le hbddf ⟨fun z => (e z + h z) / 2, (Adm.div_two (Adm.add ⟨he, hec⟩ ⟨hh, hhc⟩)).1,
        (Adm.div_two (Adm.add ⟨he, hec⟩ ⟨hh, hhc⟩)).2, rfl⟩
    have hle2 : sInf (Kinetic.trialSet ℓ a2 u g)
        ≤ Kinetic.trialVal ℓ a2 u g (fun z => (e z - h z) / 2) :=
      csInf_le hbddg ⟨fun z => (e z - h z) / 2, (Adm.div_two (Adm.sub ⟨he, hec⟩ ⟨hh, hhc⟩)).1,
        (Adm.div_two (Adm.sub ⟨he, hec⟩ ⟨hh, hhc⟩)).2, rfl⟩
    linarith
  have h2 : neuFrac ℓ a2 u (fun z => f z + g z) + neuFrac ℓ a2 u (fun z => f z - g z)
      ≤ 2 * neuFrac ℓ a2 u f + 2 * neuFrac ℓ a2 u g := by
    rw [Kinetic.neuFrac_eq_sInf_trialSet ℓ a2 u f,
      Kinetic.neuFrac_eq_sInf_trialSet ℓ a2 u g,
      Kinetic.neuFrac_eq_sInf_trialSet ℓ a2 u (fun z => f z + g z),
      Kinetic.neuFrac_eq_sInf_trialSet ℓ a2 u (fun z => f z - g z)]
    have hle : (sInf (Kinetic.trialSet ℓ a2 u (fun z => f z + g z))
          + sInf (Kinetic.trialSet ℓ a2 u (fun z => f z - g z))) / 2
        ≤ sInf (Kinetic.trialSet ℓ a2 u f + Kinetic.trialSet ℓ a2 u g) := by
      refine le_csInf (hnef.add hneg) ?_
      intro c hc
      obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_add.mp hc
      rw [← hab]
      obtain ⟨p, hp, hpc, hpq⟩ := ha
      obtain ⟨q, hq, hqc, hqq⟩ := hb
      rw [hpq, hqq]
      have hkey : sInf (Kinetic.trialSet ℓ a2 u (fun z => f z + g z))
          + sInf (Kinetic.trialSet ℓ a2 u (fun z => f z - g z))
          ≤ 2 * Kinetic.trialVal ℓ a2 u f p + 2 * Kinetic.trialVal ℓ a2 u g q := by
        rw [← trialVal_quadric (a2 := a2) hℓ u hf.continuous hg.continuous
          ⟨hp, hpc⟩ ⟨hq, hqc⟩]
        exact add_le_add
          (csInf_le hbddF ⟨fun z => p z + q z, (Adm.add ⟨hp, hpc⟩ ⟨hq, hqc⟩).1,
            (Adm.add ⟨hp, hpc⟩ ⟨hq, hqc⟩).2, rfl⟩)
          (csInf_le hbddG ⟨fun z => p z - q z, (Adm.sub ⟨hp, hpc⟩ ⟨hq, hqc⟩).1,
            (Adm.sub ⟨hp, hpc⟩ ⟨hq, hqc⟩).2, rfl⟩)
      linarith
    rw [csInf_add hnef hbddf hneg hbddg] at hle
    linarith
  linarith

/-! ## 5. Linearity of the box mean and of the mean-free projection -/

/-- The moving-box mean is additive in the state. -/
lemma bsMean_add {ℓ : ℝ} (hℓ : 0 < ℓ) (u : EuclideanSpace ℝ (Fin 3))
    {ψ₁ ψ₂ : EuclideanSpace ℝ (Fin 3) → ℝ} (h₁ : Continuous ψ₁) (h₂ : Continuous ψ₂) :
    bsMean ℓ u (fun z => ψ₁ z + ψ₂ z) = bsMean ℓ u ψ₁ + bsMean ℓ u ψ₂ := by
  have hK : IsCompact (Submission.BoseGases.acube ℓ) := Submission.BoseGases.acube_compact hℓ
  have hI₁ : IntegrableOn (fun z : EuclideanSpace ℝ (Fin 3) => ψ₁ (ℓ • u + z))
      (Submission.BoseGases.acube ℓ) volume :=
    (h₁.comp (continuous_const.add continuous_id)).continuousOn.integrableOn_compact hK
  have hI₂ : IntegrableOn (fun z : EuclideanSpace ℝ (Fin 3) => ψ₂ (ℓ • u + z))
      (Submission.BoseGases.acube ℓ) volume :=
    (h₂.comp (continuous_const.add continuous_id)).continuousOn.integrableOn_compact hK
  unfold bsMean
  beta_reduce
  rw [MeasureTheory.integral_add hI₁ hI₂, mul_add]

/-- The moving-box mean is subtractive in the state. -/
lemma bsMean_sub {ℓ : ℝ} (hℓ : 0 < ℓ) (u : EuclideanSpace ℝ (Fin 3))
    {ψ₁ ψ₂ : EuclideanSpace ℝ (Fin 3) → ℝ} (h₁ : Continuous ψ₁) (h₂ : Continuous ψ₂) :
    bsMean ℓ u (fun z => ψ₁ z - ψ₂ z) = bsMean ℓ u ψ₁ - bsMean ℓ u ψ₂ := by
  have hK : IsCompact (Submission.BoseGases.acube ℓ) := Submission.BoseGases.acube_compact hℓ
  have hI₁ : IntegrableOn (fun z : EuclideanSpace ℝ (Fin 3) => ψ₁ (ℓ • u + z))
      (Submission.BoseGases.acube ℓ) volume :=
    (h₁.comp (continuous_const.add continuous_id)).continuousOn.integrableOn_compact hK
  have hI₂ : IntegrableOn (fun z : EuclideanSpace ℝ (Fin 3) => ψ₂ (ℓ • u + z))
      (Submission.BoseGases.acube ℓ) volume :=
    (h₂.comp (continuous_const.add continuous_id)).continuousOn.integrableOn_compact hK
  unfold bsMean
  beta_reduce
  rw [MeasureTheory.integral_sub hI₁ hI₂, mul_sub]

/-- The mean-free projection `Q_{Λ(u)}` is additive in the state. -/
lemma bsQ_add {ℓ : ℝ} (hℓ : 0 < ℓ) (u : EuclideanSpace ℝ (Fin 3))
    {ψ₁ ψ₂ : EuclideanSpace ℝ (Fin 3) → ℝ} (h₁ : Continuous ψ₁) (h₂ : Continuous ψ₂) :
    bsQ ℓ u (fun z => ψ₁ z + ψ₂ z) = fun z => bsQ ℓ u ψ₁ z + bsQ ℓ u ψ₂ z := by
  funext z
  simp only [bsQ]
  rw [bsMean_add hℓ u h₁ h₂]
  ring

/-- The mean-free projection `Q_{Λ(u)}` is subtractive in the state. -/
lemma bsQ_sub {ℓ : ℝ} (hℓ : 0 < ℓ) (u : EuclideanSpace ℝ (Fin 3))
    {ψ₁ ψ₂ : EuclideanSpace ℝ (Fin 3) → ℝ} (h₁ : Continuous ψ₁) (h₂ : Continuous ψ₂) :
    bsQ ℓ u (fun z => ψ₁ z - ψ₂ z) = fun z => bsQ ℓ u ψ₁ z - bsQ ℓ u ψ₂ z := by
  funext z
  simp only [bsQ]
  rw [bsMean_sub hℓ u h₁ h₂]
  ring

/-- `Qfree` (the chapter's name for `bsQ`) is additive in the state. -/
lemma Qfree_add {ℓ : ℝ} (hℓ : 0 < ℓ) (u : EuclideanSpace ℝ (Fin 3))
    {ψ₁ ψ₂ : EuclideanSpace ℝ (Fin 3) → ℝ} (h₁ : Continuous ψ₁) (h₂ : Continuous ψ₂) :
    Qfree ℓ u (fun z => ψ₁ z + ψ₂ z) = fun z => Qfree ℓ u ψ₁ z + Qfree ℓ u ψ₂ z :=
  bsQ_add hℓ u h₁ h₂

/-- `Qfree` is subtractive in the state. -/
lemma Qfree_sub {ℓ : ℝ} (hℓ : 0 < ℓ) (u : EuclideanSpace ℝ (Fin 3))
    {ψ₁ ψ₂ : EuclideanSpace ℝ (Fin 3) → ℝ} (h₁ : Continuous ψ₁) (h₂ : Continuous ψ₂) :
    Qfree ℓ u (fun z => ψ₁ z - ψ₂ z) = fun z => Qfree ℓ u ψ₁ z - Qfree ℓ u ψ₂ z :=
  bsQ_sub hℓ u h₁ h₂

/-! ## 6. The `p`-spectral words are quadratic forms

Both `momForm` and `bsOneBody` are of the form `(2π)⁻³∫_p F(‖p‖)·‖kinFT W_ψ(p)‖²` with a
windowed state `W_ψ`; the parallelogram identity is the pointwise parallelogram law in `ℂ` for
the two Fourier transforms, transported through the `p`-integral.  The two inputs are
linearity of `kinFT` on integrable states and integrability of the four `p`-integrands. -/

/-- `kinFT` is additive on integrable states: the `p`-integrand is integrable as soon as the
state is, since the exponential factor has modulus one. -/
lemma kinFT_add {A B : EuclideanSpace ℝ (Fin 3) → ℂ}
    (hA : Integrable A) (hB : Integrable B) (p : EuclideanSpace ℝ (Fin 3)) :
    Submission.BoseGases.kinFT (fun z => A z + B z) p
      = Submission.BoseGases.kinFT A p + Submission.BoseGases.kinFT B p := by
  have hbdd : ∀ y : EuclideanSpace ℝ (Fin 3),
      ‖Complex.exp (-(Complex.I * (inner ℝ p y : ℂ)))‖ ≤ 1 := by
    intro y
    rw [Complex.norm_exp]
    have hre : (-(Complex.I * (inner ℝ p y : ℂ))).re = 0 := by
      simp [Complex.mul_re, Complex.I_re, Complex.I_im]
    rw [hre]
    simp
  have hA' : Integrable (fun y : EuclideanSpace ℝ (Fin 3) =>
      Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))) * A y) := by
    have h := hA.mul_bdd (g := fun y : EuclideanSpace ℝ (Fin 3) =>
      Complex.exp (-(Complex.I * (inner ℝ p y : ℂ)))) (by fun_prop)
      (Filter.Eventually.of_forall hbdd)
    refine h.congr (Filter.Eventually.of_forall (fun y => ?_))
    simp only [Pi.mul_apply]
    ring
  have hB' : Integrable (fun y : EuclideanSpace ℝ (Fin 3) =>
      Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))) * B y) := by
    have h := hB.mul_bdd (g := fun y : EuclideanSpace ℝ (Fin 3) =>
      Complex.exp (-(Complex.I * (inner ℝ p y : ℂ)))) (by fun_prop)
      (Filter.Eventually.of_forall hbdd)
    refine h.congr (Filter.Eventually.of_forall (fun y => ?_))
    simp only [Pi.mul_apply]
    ring
  unfold Submission.BoseGases.kinFT
  rw [← MeasureTheory.integral_add hA' hB']
  apply MeasureTheory.integral_congr_ae
  filter_upwards with y
  ring

/-- `kinFT` is subtractive on integrable states. -/
lemma kinFT_sub {A B : EuclideanSpace ℝ (Fin 3) → ℂ}
    (hA : Integrable A) (hB : Integrable B) (p : EuclideanSpace ℝ (Fin 3)) :
    Submission.BoseGases.kinFT (fun z => A z - B z) p
      = Submission.BoseGases.kinFT A p - Submission.BoseGases.kinFT B p := by
  have hbdd : ∀ y : EuclideanSpace ℝ (Fin 3),
      ‖Complex.exp (-(Complex.I * (inner ℝ p y : ℂ)))‖ ≤ 1 := by
    intro y
    rw [Complex.norm_exp]
    have hre : (-(Complex.I * (inner ℝ p y : ℂ))).re = 0 := by
      simp [Complex.mul_re, Complex.I_re, Complex.I_im]
    rw [hre]
    simp
  have hA' : Integrable (fun y : EuclideanSpace ℝ (Fin 3) =>
      Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))) * A y) := by
    have h := hA.mul_bdd (g := fun y : EuclideanSpace ℝ (Fin 3) =>
      Complex.exp (-(Complex.I * (inner ℝ p y : ℂ)))) (by fun_prop)
      (Filter.Eventually.of_forall hbdd)
    refine h.congr (Filter.Eventually.of_forall (fun y => ?_))
    simp only [Pi.mul_apply]
    ring
  have hB' : Integrable (fun y : EuclideanSpace ℝ (Fin 3) =>
      Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))) * B y) := by
    have h := hB.mul_bdd (g := fun y : EuclideanSpace ℝ (Fin 3) =>
      Complex.exp (-(Complex.I * (inner ℝ p y : ℂ)))) (by fun_prop)
      (Filter.Eventually.of_forall hbdd)
    refine h.congr (Filter.Eventually.of_forall (fun y => ?_))
    simp only [Pi.mul_apply]
    ring
  unfold Submission.BoseGases.kinFT
  rw [← MeasureTheory.integral_sub hA' hB']
  apply MeasureTheory.integral_congr_ae
  filter_upwards with y
  ring

/-- The `p`-integrand of `momForm` is integrable: the cut-off `momProj ≤ 1` is discarded and
Plancherel (`kinFT_sq_of_memLp`) applied to the localised box state. -/
lemma integrable_momProj_boxState {ℓ d : ℝ} (hℓ : 0 < ℓ) (u : EuclideanSpace ℝ (Fin 3))
    {ψ : EuclideanSpace ℝ (Fin 3) → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    Integrable (fun p : EuclideanSpace ℝ (Fin 3) => momProj ℓ d p *
      ‖Submission.BoseGases.kinFT (Kinetic.boxState ℓ u ψ) p‖ ^ 2) := by
  obtain ⟨h1, h2⟩ := Kinetic.boxState_memLp hℓ u hψ
  obtain ⟨hint, -⟩ := Kinetic.kinFT_sq_of_memLp h1 h2
  have hmeas : Measurable (fun p : EuclideanSpace ℝ (Fin 3) => momProj ℓ d p) := by
    unfold momProj
    exact Measurable.ite (measurableSet_lt measurable_const continuous_norm.measurable)
      measurable_const measurable_const
  refine hint.mono' (hmeas.aestronglyMeasurable.mul hint.aestronglyMeasurable) ?_
  refine Filter.Eventually.of_forall (fun p => ?_)
  rw [Real.norm_of_nonneg (mul_nonneg (Kinetic.momProj_nonneg ℓ d p) (sq_nonneg _))]
  exact mul_le_of_le_one_left (sq_nonneg _) (Kinetic.momProj_le_one ℓ d p)

/-- **`momForm ℓ d u` is a quadratic form** (parallelogram identity). -/
lemma momForm_parallelogram_aux {ℓ d : ℝ} (hℓ : 0 < ℓ) (u : EuclideanSpace ℝ (Fin 3))
    {f g : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    momForm ℓ d u (fun z => f z + g z) + momForm ℓ d u (fun z => f z - g z)
      = 2 * momForm ℓ d u f + 2 * momForm ℓ d u g := by
  -- the pointwise splitting of the windowed box states
  have hsplit_add : Kinetic.boxState ℓ u (fun z => f z + g z)
      = fun z => Kinetic.boxState ℓ u f z + Kinetic.boxState ℓ u g z := by
    funext z
    simp only [Kinetic.boxState]
    rw [show Qfree ℓ u (fun z => f z + g z) z = Qfree ℓ u f z + Qfree ℓ u g z from
      congrFun (Qfree_add hℓ u hf.continuous hg.continuous) z]
    push_cast
    ring
  have hsplit_sub : Kinetic.boxState ℓ u (fun z => f z - g z)
      = fun z => Kinetic.boxState ℓ u f z - Kinetic.boxState ℓ u g z := by
    funext z
    simp only [Kinetic.boxState]
    rw [show Qfree ℓ u (fun z => f z - g z) z = Qfree ℓ u f z - Qfree ℓ u g z from
      congrFun (Qfree_sub hℓ u hf.continuous hg.continuous) z]
    push_cast
    ring
  -- integrability of the two localised states
  have hIntf : Integrable (Kinetic.boxState ℓ u f) := by
    obtain ⟨h1, -⟩ := Kinetic.boxState_memLp hℓ u hf
    exact MeasureTheory.memLp_one_iff_integrable.mp h1
  have hIntg : Integrable (Kinetic.boxState ℓ u g) := by
    obtain ⟨h1, -⟩ := Kinetic.boxState_memLp hℓ u hg
    exact MeasureTheory.memLp_one_iff_integrable.mp h1
  -- the Fourier transforms split
  have hKadd : ∀ p, Submission.BoseGases.kinFT (Kinetic.boxState ℓ u (fun z => f z + g z)) p
      = Submission.BoseGases.kinFT (Kinetic.boxState ℓ u f) p
        + Submission.BoseGases.kinFT (Kinetic.boxState ℓ u g) p := by
    intro p
    rw [hsplit_add]
    exact kinFT_add hIntf hIntg p
  have hKsub : ∀ p, Submission.BoseGases.kinFT (Kinetic.boxState ℓ u (fun z => f z - g z)) p
      = Submission.BoseGases.kinFT (Kinetic.boxState ℓ u f) p
        - Submission.BoseGases.kinFT (Kinetic.boxState ℓ u g) p := by
    intro p
    rw [hsplit_sub]
    exact kinFT_sub hIntf hIntg p
  -- integrability of the four `p`-integrands
  have hintp := integrable_momProj_boxState (d := d) hℓ u (hf.add hg)
  have hintm := integrable_momProj_boxState (d := d) hℓ u (hf.sub hg)
  have hintf := integrable_momProj_boxState (d := d) hℓ u hf
  have hintg := integrable_momProj_boxState (d := d) hℓ u hg
  -- the `p`-integral identity
  have key : (∫ p : EuclideanSpace ℝ (Fin 3), momProj ℓ d p *
        ‖Submission.BoseGases.kinFT (Kinetic.boxState ℓ u (fun z => f z + g z)) p‖ ^ 2)
      + (∫ p : EuclideanSpace ℝ (Fin 3), momProj ℓ d p *
        ‖Submission.BoseGases.kinFT (Kinetic.boxState ℓ u (fun z => f z - g z)) p‖ ^ 2)
      = 2 * (∫ p : EuclideanSpace ℝ (Fin 3), momProj ℓ d p *
          ‖Submission.BoseGases.kinFT (Kinetic.boxState ℓ u f) p‖ ^ 2)
        + 2 * (∫ p : EuclideanSpace ℝ (Fin 3), momProj ℓ d p *
          ‖Submission.BoseGases.kinFT (Kinetic.boxState ℓ u g) p‖ ^ 2) := by
    rw [← MeasureTheory.integral_add hintp hintm,
      ← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_const_mul,
      ← MeasureTheory.integral_add (hintf.const_mul 2) (hintg.const_mul 2)]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with p
    rw [hKadd p, hKsub p]
    have hpar := parallelogram_law_with_norm ℝ
      (Submission.BoseGases.kinFT (Kinetic.boxState ℓ u f) p)
      (Submission.BoseGases.kinFT (Kinetic.boxState ℓ u g) p)
    linear_combination (norm := ring) momProj ℓ d p * hpar
  rw [Kinetic.momForm_eq_boxState ℓ d u (fun z => f z + g z),
    Kinetic.momForm_eq_boxState ℓ d u (fun z => f z - g z),
    Kinetic.momForm_eq_boxState ℓ d u f,
    Kinetic.momForm_eq_boxState ℓ d u g]
  linear_combination ((2 * Real.pi) ^ 3)⁻¹ * key

/-- The `p`-integrand of `bsOneBody ℓ (fsKinCoeff c)` is integrable for smooth compactly
supported states (`integrable_fsKinCoeff_mul_bsPsi_sq`, the symbol `[‖p‖−c]₊²` being dominated
by `2(1+c²)(1+‖p‖²)`). -/
lemma integrable_fsKinCoeff_kinFT_sq {c : ℝ} {h : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hd : ContDiff ℝ (⊤ : ℕ∞) h) (hc : HasCompactSupport h) :
    Integrable (fun p : EuclideanSpace ℝ (Fin 3) => Submission.BoseGases.fsKinCoeff c ‖p‖ *
      ‖Submission.BoseGases.kinFT (fun z => (h z : ℂ)) p‖ ^ 2) :=
  Work.BSKinetic.Decomp.integrable_fsKinCoeff_mul_bsPsi_sq hd hc

/-- **`bsOneBody ℓ (fsKinCoeff c) u` is a quadratic form** (parallelogram identity). -/
lemma bsOneBody_parallelogram_aux {ℓ c : ℝ} (hℓ : 0 < ℓ) (u : EuclideanSpace ℝ (Fin 3))
    {f g : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    bsOneBody ℓ (Submission.BoseGases.fsKinCoeff c) u (fun z => f z + g z)
      + bsOneBody ℓ (Submission.BoseGases.fsKinCoeff c) u (fun z => f z - g z)
      = 2 * bsOneBody ℓ (Submission.BoseGases.fsKinCoeff c) u f
        + 2 * bsOneBody ℓ (Submission.BoseGases.fsKinCoeff c) u g := by
  have hℓ' : ℓ ≠ 0 := ne_of_gt hℓ
  have hWin : ContDiff ℝ (⊤ : ℕ∞) (bsWin ℓ u) := by
    have h' : bsWin ℓ u = fun z : EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.chiScale ℓ (z - ℓ • u) := rfl
    rw [h']
    exact (Submission.BoseGases.chiScale_contDiff hℓ').comp
      (contDiff_id.sub contDiff_const)
  have hWcs : HasCompactSupport (bsWin ℓ u) := bsWin_hasCompactSupport hℓ u
  have hcd : ∀ {ψ : EuclideanSpace ℝ (Fin 3) → ℝ}, ContDiff ℝ (⊤ : ℕ∞) ψ →
      ContDiff ℝ (⊤ : ℕ∞) (fun z => bsWin ℓ u z * bsQ ℓ u ψ z) := by
    intro ψ hψ
    have hQ : ContDiff ℝ (⊤ : ℕ∞) (bsQ ℓ u ψ) := by
      have h' : bsQ ℓ u ψ = fun z => ψ z - bsMean ℓ u ψ := rfl
      rw [h']; exact hψ.sub contDiff_const
    exact hWin.mul hQ
  have hcs : ∀ ψ : EuclideanSpace ℝ (Fin 3) → ℝ,
      HasCompactSupport (fun z => bsWin ℓ u z * bsQ ℓ u ψ z) :=
    fun _ => HasCompactSupport.mul_right hWcs
  have hint : ∀ {ψ : EuclideanSpace ℝ (Fin 3) → ℝ}, ContDiff ℝ (⊤ : ℕ∞) ψ →
      Integrable (fun z : EuclideanSpace ℝ (Fin 3) =>
        ((bsWin ℓ u z * bsQ ℓ u ψ z : ℝ) : ℂ)) := by
    intro ψ hψ
    exact (Complex.continuous_ofReal.comp (hcd hψ).continuous).integrable_of_hasCompactSupport
      ((hcs ψ).comp_left (by simp))
  have hcast : ∀ ψ : EuclideanSpace ℝ (Fin 3) → ℝ,
      (fun z : EuclideanSpace ℝ (Fin 3) => (bsWin ℓ u z : ℂ) * (bsQ ℓ u ψ z : ℂ))
        = fun z => ((bsWin ℓ u z * bsQ ℓ u ψ z : ℝ) : ℂ) := by
    intro ψ
    funext z
    rw [Complex.ofReal_mul]
  -- the pointwise splitting of the windowed states
  have hsplit_add : (fun z : EuclideanSpace ℝ (Fin 3) =>
        ((bsWin ℓ u z * bsQ ℓ u (fun z => f z + g z) z : ℝ) : ℂ))
      = fun z => ((bsWin ℓ u z * bsQ ℓ u f z : ℝ) : ℂ)
          + ((bsWin ℓ u z * bsQ ℓ u g z : ℝ) : ℂ) := by
    funext z
    rw [congrFun (bsQ_add hℓ u hf.continuous hg.continuous) z]
    push_cast
    ring
  have hsplit_sub : (fun z : EuclideanSpace ℝ (Fin 3) =>
        ((bsWin ℓ u z * bsQ ℓ u (fun z => f z - g z) z : ℝ) : ℂ))
      = fun z => ((bsWin ℓ u z * bsQ ℓ u f z : ℝ) : ℂ)
          - ((bsWin ℓ u z * bsQ ℓ u g z : ℝ) : ℂ) := by
    funext z
    rw [congrFun (bsQ_sub hℓ u hf.continuous hg.continuous) z]
    push_cast
    ring
  -- the Fourier transforms split
  have hKadd : ∀ p, Submission.BoseGases.kinFT (fun z =>
        ((bsWin ℓ u z * bsQ ℓ u (fun z => f z + g z) z : ℝ) : ℂ)) p
      = Submission.BoseGases.kinFT
          (fun z => ((bsWin ℓ u z * bsQ ℓ u f z : ℝ) : ℂ)) p
        + Submission.BoseGases.kinFT
          (fun z => ((bsWin ℓ u z * bsQ ℓ u g z : ℝ) : ℂ)) p := by
    intro p
    rw [hsplit_add]
    exact kinFT_add (hint hf) (hint hg) p
  have hKsub : ∀ p, Submission.BoseGases.kinFT (fun z =>
        ((bsWin ℓ u z * bsQ ℓ u (fun z => f z - g z) z : ℝ) : ℂ)) p
      = Submission.BoseGases.kinFT
          (fun z => ((bsWin ℓ u z * bsQ ℓ u f z : ℝ) : ℂ)) p
        - Submission.BoseGases.kinFT
          (fun z => ((bsWin ℓ u z * bsQ ℓ u g z : ℝ) : ℂ)) p := by
    intro p
    rw [hsplit_sub]
    exact kinFT_sub (hint hf) (hint hg) p
  -- integrability of the four `p`-integrands
  have hintp := integrable_fsKinCoeff_kinFT_sq (c := c)
    (hcd (hf.add hg)) (hcs (fun z => f z + g z))
  have hintm := integrable_fsKinCoeff_kinFT_sq (c := c)
    (hcd (hf.sub hg)) (hcs (fun z => f z - g z))
  have hintf := integrable_fsKinCoeff_kinFT_sq (c := c) (hcd hf) (hcs f)
  have hintg := integrable_fsKinCoeff_kinFT_sq (c := c) (hcd hg) (hcs g)
  -- the `p`-integral identity
  have key : (∫ p : EuclideanSpace ℝ (Fin 3), Submission.BoseGases.fsKinCoeff c ‖p‖ *
        ‖Submission.BoseGases.kinFT (fun z =>
          ((bsWin ℓ u z * bsQ ℓ u (fun z => f z + g z) z : ℝ) : ℂ)) p‖ ^ 2)
      + (∫ p : EuclideanSpace ℝ (Fin 3), Submission.BoseGases.fsKinCoeff c ‖p‖ *
        ‖Submission.BoseGases.kinFT (fun z =>
          ((bsWin ℓ u z * bsQ ℓ u (fun z => f z - g z) z : ℝ) : ℂ)) p‖ ^ 2)
      = 2 * (∫ p : EuclideanSpace ℝ (Fin 3), Submission.BoseGases.fsKinCoeff c ‖p‖ *
          ‖Submission.BoseGases.kinFT (fun z =>
            ((bsWin ℓ u z * bsQ ℓ u f z : ℝ) : ℂ)) p‖ ^ 2)
        + 2 * (∫ p : EuclideanSpace ℝ (Fin 3), Submission.BoseGases.fsKinCoeff c ‖p‖ *
          ‖Submission.BoseGases.kinFT (fun z =>
            ((bsWin ℓ u z * bsQ ℓ u g z : ℝ) : ℂ)) p‖ ^ 2) := by
    rw [← MeasureTheory.integral_add hintp hintm,
      ← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_const_mul,
      ← MeasureTheory.integral_add (hintf.const_mul 2) (hintg.const_mul 2)]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with p
    rw [hKadd p, hKsub p]
    have hpar := parallelogram_law_with_norm ℝ
      (Submission.BoseGases.kinFT (fun z => ((bsWin ℓ u z * bsQ ℓ u f z : ℝ) : ℂ)) p)
      (Submission.BoseGases.kinFT (fun z => ((bsWin ℓ u z * bsQ ℓ u g z : ℝ) : ℂ)) p)
    linear_combination (norm := ring) (Submission.BoseGases.fsKinCoeff c ‖p‖) * hpar
  unfold bsOneBody
  rw [hcast (fun z => f z + g z), hcast (fun z => f z - g z), hcast f, hcast g]
  linear_combination ((2 * Real.pi) ^ 3)⁻¹ * key

/-! ## 7. The gap word -/

/-- **The mean-free box mass `gapBare ℓ u` is a quadratic form** (parallelogram identity). -/
lemma gapBare_parallelogram {ℓ : ℝ} (hℓ : 0 < ℓ) (u : EuclideanSpace ℝ (Fin 3))
    {f g : EuclideanSpace ℝ (Fin 3) → ℝ} (hf : Continuous f) (hg : Continuous g) :
    gapBare ℓ u (fun z => f z + g z) + gapBare ℓ u (fun z => f z - g z)
      = 2 * gapBare ℓ u f + 2 * gapBare ℓ u g := by
  have hΛ : IsCompact (lamBox ℓ u) := Gap.isCompact_lamBox hℓ u
  have hp : Continuous (bsQ ℓ u f) := Kinetic.Qfree_continuous hf ℓ u
  have hq : Continuous (bsQ ℓ u g) := Kinetic.Qfree_continuous hg ℓ u
  have e1 : gapBare ℓ u (fun z => f z + g z)
      = ∫ z in lamBox ℓ u, (bsQ ℓ u f z + bsQ ℓ u g z) ^ 2 := by
    unfold gapBare Qfree
    apply MeasureTheory.setIntegral_congr_fun hΛ.measurableSet
    intro w _
    show (bsQ ℓ u (fun z => f z + g z) w) ^ 2 = (bsQ ℓ u f w + bsQ ℓ u g w) ^ 2
    rw [show bsQ ℓ u (fun z => f z + g z) w = bsQ ℓ u f w + bsQ ℓ u g w from
      congrFun (bsQ_add hℓ u hf hg) w]
  have e2 : gapBare ℓ u (fun z => f z - g z)
      = ∫ z in lamBox ℓ u, (bsQ ℓ u f z - bsQ ℓ u g z) ^ 2 := by
    unfold gapBare Qfree
    apply MeasureTheory.setIntegral_congr_fun hΛ.measurableSet
    intro w _
    show (bsQ ℓ u (fun z => f z - g z) w) ^ 2 = (bsQ ℓ u f w - bsQ ℓ u g w) ^ 2
    rw [show bsQ ℓ u (fun z => f z - g z) w = bsQ ℓ u f w - bsQ ℓ u g w from
      congrFun (bsQ_sub hℓ u hf hg) w]
  have e3 : gapBare ℓ u f = ∫ z in lamBox ℓ u, (bsQ ℓ u f z) ^ 2 := rfl
  have e4 : gapBare ℓ u g = ∫ z in lamBox ℓ u, (bsQ ℓ u g z) ^ 2 := rfl
  rw [e1, e2, e3, e4]
  have h := mul_parallelogram (Λ := lamBox ℓ u) hΛ hp hq hp hq
  simpa only [pow_two] using h

end FsTAux

/-! ## 8. The parallelogram identity for `fsT` — the requested lemma -/

theorem fsT_parallelogram {ℓ d s εT b : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (hs : 0 < s) (hεT : 0 < εT) (hb : 0 < b) (u : EuclideanSpace ℝ (Fin 3)) {f g : EuclideanSpace ℝ (Fin 3) → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g) : Work.BoseKinLoc.fsT ℓ d s εT b u (fun z => f z + g z) + Work.BoseKinLoc.fsT ℓ d s εT b u (fun z => f z - g z) = 2 * Work.BoseKinLoc.fsT ℓ d s εT b u f + 2 * Work.BoseKinLoc.fsT ℓ d s εT b u g := by
  have ha2 : 0 < (d * ℓ) ^ (-2 : ℤ) := by positivity
  have hQf : ContDiff ℝ (⊤ : ℕ∞) (Qfree ℓ u f) := by
    have h' : Qfree ℓ u f = fun z => f z - bsMean ℓ u f := rfl
    rw [h']; exact hf.sub contDiff_const
  have hQg : ContDiff ℝ (⊤ : ℕ∞) (Qfree ℓ u g) := by
    have h' : Qfree ℓ u g = fun z => g z - bsMean ℓ u g := rfl
    rw [h']; exact hg.sub contDiff_const
  have hneu : neuWord ℓ d εT u (fun z => f z + g z) + neuWord ℓ d εT u (fun z => f z - g z)
      = 2 * neuWord ℓ d εT u f + 2 * neuWord ℓ d εT u g := by
    unfold neuWord
    rw [FsTAux.Qfree_add hℓ u hf.continuous hg.continuous,
      FsTAux.Qfree_sub hℓ u hf.continuous hg.continuous]
    have hpar := FsTAux.neuFrac_parallelogram_aux (ℓ := ℓ) (a2 := (d * ℓ) ^ (-2 : ℤ))
      hℓ ha2 u hQf hQg
    linear_combination ((1 / 2) * εT * (d * ℓ) ^ (-2 : ℤ)) * hpar
  have hgap : gapWord ℓ b u (fun z => f z + g z) + gapWord ℓ b u (fun z => f z - g z)
      = 2 * gapWord ℓ b u f + 2 * gapWord ℓ b u g := by
    unfold gapWord
    have hpar := FsTAux.gapBare_parallelogram hℓ u hf.continuous hg.continuous
    linear_combination (b * ℓ ^ (-2 : ℤ)) * hpar
  have hmom : momWord ℓ d εT b u (fun z => f z + g z) + momWord ℓ d εT b u (fun z => f z - g z)
      = 2 * momWord ℓ d εT b u f + 2 * momWord ℓ d εT b u g := by
    unfold momWord
    have hpar := FsTAux.momForm_parallelogram_aux (d := d) hℓ u hf hg
    linear_combination (b * εT * (d * ℓ) ^ (-2 : ℤ)) * hpar
  have hmain : mainWord ℓ d s εT u (fun z => f z + g z) + mainWord ℓ d s εT u (fun z => f z - g z)
      = 2 * mainWord ℓ d s εT u f + 2 * mainWord ℓ d s εT u g := by
    unfold mainWord
    have h1 := FsTAux.bsOneBody_parallelogram_aux (c := (2 * (s * ℓ))⁻¹) hℓ u hf hg
    have h2 := FsTAux.bsOneBody_parallelogram_aux (c := (2 * (d * s * ℓ))⁻¹) hℓ u hf hg
    linear_combination (1 - εT) * h1 + εT * h2
  rw [Work.BoseKinLoc.fsT_eq_sum ℓ d s εT b u (fun z => f z + g z),
    Work.BoseKinLoc.fsT_eq_sum ℓ d s εT b u (fun z => f z - g z),
    Work.BoseKinLoc.fsT_eq_sum ℓ d s εT b u f,
    Work.BoseKinLoc.fsT_eq_sum ℓ d s εT b u g]
  linear_combination hneu + hgap + hmom + hmain

end Work.BoseFixB2.Polar
