import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.OneBodyKin.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.OneBodyKin.CrossKern` — the position-space kernel of the cross term

The cross term of the projected moving-box family form is

  `∫_u bsMean ℓ u ψ · bsPair ℓ F u ψ du`,

where `bsMean ℓ u ψ = (ℓ³)⁻¹ ∫_{Λ(u)} ψ` is the box mean and `bsPair ℓ F u ψ` is the
`χ_u`-weighted cross form `⟨χ_u, F(√−Δ)(χ_uψ)⟩`.  This module introduces the **position-space
kernel** of that cross term.  Writing the box mean as a sliding average over the unit cube
`bsMean ℓ u ψ = ∫_{s ∈ acube 1} ψ (ℓ • (u + s))`, the whole cross term is a convolution
quadratic form in `ψ`:

  `∫_u bsMean ℓ u ψ · bsPair ℓ F u ψ = (2π)⁻³ ∫_x ∫_y bsKern ℓ F (x − y) ψ x ψ y`,

with `bsKern` as defined below (`Work.OneBodyKin.bsMean_bsPair_eq_kernelForm`).

The kernel is compactly supported (`acube 1` and the support of `χ` are bounded,
`integrable_bsKern`) and its `p`-convention Fourier transform is the *symbol* of the cross term

  `kinFT (bsKern ℓ F) q = boxHat ℓ q · symD ℓ F q`

(`Work.OneBodyKin.kinFT_bsKern`), which — combined with the convolution-quadratic-form identity
`Work.OneBodyKin.quadForm_conv_eq_fourier` — turns the cross term into the symbol integral of
the target statement.
-/

noncomputable section

open MeasureTheory

namespace Work.OneBodyKin

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

set_option autoImplicit false

/-- **The position-space kernel of the cross term**

  `bsKern ℓ F d = ∫_{s ∈ acube 1} ∫_p F ‖p‖ · profHat (ℓ•p) · χ (s + ℓ⁻¹•d) · cos ⟪ℓ•p, s + ℓ⁻¹•d⟫ dp ds`.

It is the kernel of the convolution quadratic form whose symbol is `boxHat ℓ q · symD ℓ F q`. -/
noncomputable def bsKern (ℓ : ℝ) (F : ℝ → ℝ) (d : ℝ³) : ℝ :=
  ∫ s in acube 1, ∫ p : ℝ³,
    F ‖p‖ * profHat (ℓ • p) *
      (chi (s + ℓ⁻¹ • d) * Real.cos (inner ℝ (ℓ • p) (s + ℓ⁻¹ • d)))

/-- Unfolding lemma for `bsKern` (the definition is already the unfolded form; this is stated for
use as a rewrite rule). -/
lemma bsKern_def (ℓ : ℝ) (F : ℝ → ℝ) (d : ℝ³) :
    bsKern ℓ F d
      = ∫ s in acube 1, ∫ p : ℝ³,
          F ‖p‖ * profHat (ℓ • p) *
            (chi (s + ℓ⁻¹ • d) * Real.cos (inner ℝ (ℓ • p) (s + ℓ⁻¹ • d))) := rfl

/-- The cube `acube 1` is invariant under negation. -/
private lemma neg_mem_acube_iff (s : ℝ³) : -s ∈ acube 1 ↔ s ∈ acube 1 := by
  rw [mem_acube_iff, mem_acube_iff]
  have h : ∀ m : Fin 3, (-s).ofLp m = -(s.ofLp m) := fun m => by simp
  constructor
  · intro hh m
    have hm := hh m
    rw [h m] at hm
    exact ⟨by linarith [hm.2], by linarith [hm.1]⟩
  · intro hh m
    have hm := hh m
    rw [h m]
    exact ⟨by linarith [hm.2], by linarith [hm.1]⟩

/-- Negation is a measure-preserving substitution for the set integral over `acube 1`. -/
private lemma setIntegral_neg_acube (G : ℝ³ → ℝ) :
    (∫ s in acube 1, G (-s)) = ∫ s in acube 1, G s := by
  rw [← integral_indicator (acube_measurable 1), ← integral_indicator (acube_measurable 1)]
  rw [show (fun s : ℝ³ => (acube 1).indicator (fun s : ℝ³ => G (-s)) s)
      = fun s : ℝ³ => (acube 1).indicator G (-s) from by
    funext s
    by_cases hs : s ∈ acube 1
    · rw [Set.indicator_of_mem hs, Set.indicator_of_mem (neg_mem_acube_iff s |>.mpr hs)]
    · rw [Set.indicator_of_notMem hs,
        Set.indicator_of_notMem (fun hc => hs (neg_mem_acube_iff s |>.mp hc))]]
  exact Submission.BoseGases.integral_comp_neg (fun s : ℝ³ => (acube 1).indicator G s)

/-- **`bsKern` is even in the position variable**: this is the reflection symmetry `s ↦ −s` of
the cube together with the evenness of `χ` and of `cos`.  It makes the sign convention of the
kernel argument immaterial. -/
lemma bsKern_neg (ℓ : ℝ) (F : ℝ → ℝ) (d : ℝ³) :
    bsKern ℓ F (-d) = bsKern ℓ F d := by
  have hpt : ∀ s : ℝ³, (∫ p : ℝ³, F ‖p‖ * profHat (ℓ • p) *
        (chi (s + ℓ⁻¹ • (-d)) * Real.cos (inner ℝ (ℓ • p) (s + ℓ⁻¹ • (-d)))))
      = (∫ p : ℝ³, F ‖p‖ * profHat (ℓ • p) *
        (chi (-s + ℓ⁻¹ • d) * Real.cos (inner ℝ (ℓ • p) (-s + ℓ⁻¹ • d)))) := by
    intro s
    refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
    show F ‖p‖ * profHat (ℓ • p) *
        (chi (s + ℓ⁻¹ • (-d)) * Real.cos (inner ℝ (ℓ • p) (s + ℓ⁻¹ • (-d))))
      = F ‖p‖ * profHat (ℓ • p) *
        (chi (-s + ℓ⁻¹ • d) * Real.cos (inner ℝ (ℓ • p) (-s + ℓ⁻¹ • d)))
    have h1 : s + ℓ⁻¹ • (-d) = -(-s + ℓ⁻¹ • d) := by module
    rw [h1, chi_even, inner_neg_right, Real.cos_neg]
  rw [bsKern, bsKern,
    show (fun s : ℝ³ => (∫ p : ℝ³, F ‖p‖ * profHat (ℓ • p) *
        (chi (s + ℓ⁻¹ • (-d)) * Real.cos (inner ℝ (ℓ • p) (s + ℓ⁻¹ • (-d))))))
      = fun s : ℝ³ => (∫ p : ℝ³, F ‖p‖ * profHat (ℓ • p) *
        (chi (-s + ℓ⁻¹ • d) * Real.cos (inner ℝ (ℓ • p) (-s + ℓ⁻¹ • d)))) from funext hpt]
  exact setIntegral_neg_acube (fun t : ℝ³ => ∫ p : ℝ³, F ‖p‖ * profHat (ℓ • p) *
    (chi (t + ℓ⁻¹ • d) * Real.cos (inner ℝ (ℓ • p) (t + ℓ⁻¹ • d))))

end Work.OneBodyKin
