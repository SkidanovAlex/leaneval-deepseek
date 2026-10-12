import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB2.DvApriori.BandDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB2.DvApriori.gapWord_sub_eq_of_means_zero`

FS `eq:DefT`'s second kinetic piece is the anchored-box mean-free mass
`gapWord ℓ b u ψ = bℓ⁻²⟨Q_uψ, Q_uψ⟩`, and `Q_uψ = ψ − ⨍_{Λ(u)}ψ`.  For states whose
**box mean vanishes** the projection `Q_0` acts as the identity, so the polarisation
difference of `gapWord` is the integrated polarisation identity for squares:

`gapWord ℓ b 0 (ψ₁+ψ₂) − gapWord ℓ b 0 (ψ₁−ψ₂) = 4bℓ⁻² ∫_{acube ℓ} ψ₁ψ₂`.

## Contents

* `lamBox_zero_eq_acube` — the anchored moving box `Λ(0)` is the centred cube `acube ℓ`;
* `bsMean_eq_zero_of_boxIntegral_zero` — the anchored box mean of a mean-zero state vanishes;
* `gapBare_zero_eq_of_boxIntegral_zero` — `gapBare ℓ 0 ψ = ∫_{acube ℓ} ψ²` for mean-zero `ψ`;
* `integral_sq_sub_sq` — the integrated polarisation identity `∫(f+g)² − ∫(f−g)² = 4∫fg`
  over the centred cube, for continuous `f, g`;
* `gapWord_sub_eq_of_means_zero` — the requested identity.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseFixB2.DvApriori

set_option autoImplicit false

/-- The anchored moving box `Λ(0) = 0 + [−ℓ/2,ℓ/2]³` is the centred cube `acube ℓ`. -/
lemma lamBox_zero_eq_acube (ℓ : ℝ) :
    Work.BoseKinLoc.lamBox ℓ 0 = Submission.BoseGases.acube ℓ := by
  ext x
  simp [Work.BoseKinLoc.lamBox, Work.BSKinetic.bsBox]

/-- The anchored box mean `bsMean ℓ 0 ψ = ℓ⁻³∫_{acube ℓ}ψ` of a state with vanishing
box integral is `0`. -/
lemma bsMean_eq_zero_of_boxIntegral_zero {ℓ : ℝ} {ψ : EuclideanSpace ℝ (Fin 3) → ℝ}
    (h : ∫ z in Submission.BoseGases.acube ℓ, ψ z = 0) :
    Work.BSKinetic.bsMean ℓ 0 ψ = 0 := by
  simp only [Work.BSKinetic.bsMean, smul_zero, zero_add]
  rw [h, mul_zero]

/-- For a state whose integral over the centred cube vanishes, the mean-free box mass of the
anchored box is the plain `L²` mass: `gapBare ℓ 0 ψ = ∫_{acube ℓ}ψ²`. -/
lemma gapBare_zero_eq_of_boxIntegral_zero {ℓ : ℝ} {ψ : EuclideanSpace ℝ (Fin 3) → ℝ}
    (h : ∫ z in Submission.BoseGases.acube ℓ, ψ z = 0) :
    Work.BoseKinLoc.gapBare ℓ 0 ψ = ∫ z in Submission.BoseGases.acube ℓ, (ψ z) ^ 2 := by
  have hm : Work.BSKinetic.bsMean ℓ 0 ψ = 0 := bsMean_eq_zero_of_boxIntegral_zero h
  unfold Work.BoseKinLoc.gapBare Work.BoseKinLoc.Qfree Work.BSKinetic.bsQ
  rw [lamBox_zero_eq_acube ℓ, hm]
  simp

/-- **The integrated polarisation identity over the centred cube**: for continuous `f g`,
`∫_{acube ℓ}(f+g)² − ∫_{acube ℓ}(f−g)² = 4∫_{acube ℓ} f g`. -/
lemma integral_sq_sub_sq {ℓ : ℝ} (hℓ : 0 < ℓ) {f g : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hf : Continuous f) (hg : Continuous g) :
    (∫ z in Submission.BoseGases.acube ℓ, (f z + g z) ^ 2)
      - (∫ z in Submission.BoseGases.acube ℓ, (f z - g z) ^ 2)
      = 4 * ∫ z in Submission.BoseGases.acube ℓ, f z * g z := by
  have hK : IsCompact (Submission.BoseGases.acube ℓ) :=
    Submission.BoseGases.acube_compact hℓ
  have hf2 : IntegrableOn (fun z : EuclideanSpace ℝ (Fin 3) => (f z) ^ 2)
      (Submission.BoseGases.acube ℓ) := (hf.pow 2).continuousOn.integrableOn_compact hK
  have hg2 : IntegrableOn (fun z : EuclideanSpace ℝ (Fin 3) => (g z) ^ 2)
      (Submission.BoseGases.acube ℓ) := (hg.pow 2).continuousOn.integrableOn_compact hK
  have hA : IntegrableOn (fun z : EuclideanSpace ℝ (Fin 3) => (f z) ^ 2 + (g z) ^ 2)
      (Submission.BoseGases.acube ℓ) :=
    ((hf.pow 2).add (hg.pow 2)).continuousOn.integrableOn_compact hK
  have hfg : IntegrableOn (fun z : EuclideanSpace ℝ (Fin 3) => f z * g z)
      (Submission.BoseGases.acube ℓ) := (hf.mul hg).continuousOn.integrableOn_compact hK
  have key1 : (∫ z in Submission.BoseGases.acube ℓ, (f z + g z) ^ 2)
      = (∫ z in Submission.BoseGases.acube ℓ, (f z) ^ 2)
        + (∫ z in Submission.BoseGases.acube ℓ, (g z) ^ 2)
        + 2 * (∫ z in Submission.BoseGases.acube ℓ, f z * g z) := by
    rw [show (fun z : EuclideanSpace ℝ (Fin 3) => (f z + g z) ^ 2)
        = (fun z => ((f z) ^ 2 + (g z) ^ 2) + 2 * (f z * g z)) from by
      funext z; ring]
    rw [integral_add hA (hfg.const_mul 2)]
    rw [integral_add hf2 hg2, integral_const_mul]
  have key2 : (∫ z in Submission.BoseGases.acube ℓ, (f z - g z) ^ 2)
      = (∫ z in Submission.BoseGases.acube ℓ, (f z) ^ 2)
        + (∫ z in Submission.BoseGases.acube ℓ, (g z) ^ 2)
        - 2 * (∫ z in Submission.BoseGases.acube ℓ, f z * g z) := by
    rw [show (fun z : EuclideanSpace ℝ (Fin 3) => (f z - g z) ^ 2)
        = (fun z => ((f z) ^ 2 + (g z) ^ 2) - 2 * (f z * g z)) from by
      funext z; ring]
    rw [integral_sub hA (hfg.const_mul 2)]
    rw [integral_add hf2 hg2, integral_const_mul]
  rw [key1, key2]
  ring

/-- **The requested identity.**  For continuous states `ψ₁, ψ₂` with vanishing mean over the
box `acube ℓ`, the polarised (`+` vs `−`) difference of the anchored `gapWord` is the mixed
mass `4bℓ⁻²∫ψ₁ψ₂`. -/
theorem gapWord_sub_eq_of_means_zero {ℓ b : ℝ} (hℓ : 0 < ℓ) {ψ₁ ψ₂ : EuclideanSpace ℝ (Fin 3) → ℝ}
    (h₁ : Continuous ψ₁) (h₂ : Continuous ψ₂)
    (hm₁ : ∫ z in Submission.BoseGases.acube ℓ, ψ₁ z = 0)
    (hm₂ : ∫ z in Submission.BoseGases.acube ℓ, ψ₂ z = 0) :
    Work.BoseKinLoc.gapWord ℓ b 0 (fun z => ψ₁ z + ψ₂ z)
      - Work.BoseKinLoc.gapWord ℓ b 0 (fun z => ψ₁ z - ψ₂ z)
      = (b * ℓ ^ (-2 : ℤ) * 4) * ∫ z in Submission.BoseGases.acube ℓ, ψ₁ z * ψ₂ z := by
  have hK : IsCompact (Submission.BoseGases.acube ℓ) :=
    Submission.BoseGases.acube_compact hℓ
  have hI₁ : IntegrableOn ψ₁ (Submission.BoseGases.acube ℓ) :=
    h₁.continuousOn.integrableOn_compact hK
  have hI₂ : IntegrableOn ψ₂ (Submission.BoseGases.acube ℓ) :=
    h₂.continuousOn.integrableOn_compact hK
  -- the mean of the sum and of the difference vanish
  have hsum : ∫ z in Submission.BoseGases.acube ℓ, (ψ₁ z + ψ₂ z) = 0 := by
    rw [integral_add (f := ψ₁) (g := ψ₂) hI₁ hI₂, hm₁, hm₂, add_zero]
  have hdiff : ∫ z in Submission.BoseGases.acube ℓ, (ψ₁ z - ψ₂ z) = 0 := by
    rw [integral_sub (f := ψ₁) (g := ψ₂) hI₁ hI₂, hm₁, hm₂, sub_zero]
  -- reduce both `gapWord`s to plain `L²` masses
  have hb₁ := gapBare_zero_eq_of_boxIntegral_zero (ℓ := ℓ) hsum
  have hb₂ := gapBare_zero_eq_of_boxIntegral_zero (ℓ := ℓ) hdiff
  have hs : Work.BoseKinLoc.gapWord ℓ b 0 (fun z => ψ₁ z + ψ₂ z)
      = b * ℓ ^ (-2 : ℤ)
        * ∫ z in Submission.BoseGases.acube ℓ, (ψ₁ z + ψ₂ z) ^ 2 := by
    unfold Work.BoseKinLoc.gapWord
    rw [hb₁]
  have hd : Work.BoseKinLoc.gapWord ℓ b 0 (fun z => ψ₁ z - ψ₂ z)
      = b * ℓ ^ (-2 : ℤ)
        * ∫ z in Submission.BoseGases.acube ℓ, (ψ₁ z - ψ₂ z) ^ 2 := by
    unfold Work.BoseKinLoc.gapWord
    rw [hb₂]
  have hint := integral_sq_sub_sq (ℓ := ℓ) hℓ h₁ h₂
  rw [hs, hd]
  linear_combination (b * ℓ ^ (-2 : ℤ)) * hint

end Work.BoseFixB2.DvApriori
