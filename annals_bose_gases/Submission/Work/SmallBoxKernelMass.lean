import ChallengeDeps
import Submission.Q0Chosen
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Kernel-mass completion (revised Goal-1 hinge): ∬w₂ = ∬w₁ + ĝω(0)·ℓ³, EXACT

(Work-in-progress module; Session-197.  The analytic hinge of the revised
Goal-1 of the `smallbox_dl_energy_bound` body — see SmallBoxDesignNote.md
Session-197 addendum.  Self-contained on top of the closed kernel-mass
layer `Submission.Q0Chosen` + `Submission.ScatKernelChosen`.)

FS `final_v2.tex` lm:w2>w1 (lines ~3840–3900) asserts the approximate
completion

    ∬ w₂ ≥ ∬ w₁ + ĝω(0)·(1−C(R/λ₁)²)(1−C(R/(ℓd))²)·∫χ²,

used to pass from the A0/Bogolubov block bound to the `¼(x−μ)²·∬w₁ −
½μ²·∬w₁` shape (the `−½ĝω(0)·n²/|B|²·∫χ²` term cancels at leading order).
In the corpus's EXACT transcription the masses are exact
(`Q0Chosen.w1c_acube_integral`: `∬wPair(g₀) = ℓ³·8π(av)`;
`w2c_acube_integral`: `∬wPair(g₂) = ℓ³·∫g₂`), and since
`g₂ = g₀(1+w₀) = g₀ + g₀·w₀` pointwise (`ScatKernelChosen.g0/g2`), the
completion is the EXACT EQUALITY

    ∬_box wPair(g₂) = ∬_box wPair(g₀) + ℓ³·∫(g₀·w₀)

(`ĝω(0) := ∫g₀·w₀` in this transcription, `∫χ_ℓ² = ℓ³`).  No
`(R/λ₁)²`-loss: the corpus's centred-box transcription is cleaner than FS's
approximate lm:w2>w1.  This module machine-checks that equality (plus the
pointwise and mass-level `g₂ = g₀ + g₀w₀` facts it rests on).  The
quadratic-completion algebra `½x²·∬w₂ − ½ĝω(0)·x²·∫χ² = ½x²·∬w₁` (the FS
A0-step) is then a pure-`ring` corollary for the block-bound derivation.
-/

noncomputable section

open MeasureTheory Metric
open scoped Real BigOperators ENNReal Topology ContDiff

namespace Submission

open _root_.BoseGases
open _root_.BoseGases.CInfty0Box
set_option autoImplicit false
set_option linter.unusedVariables false

namespace BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- pointwise `g₂ = g₀ + g₀·w₀` (`w₀ := Classical.choose h`), from
`g₂ := g₀(1+w₀)`, `g₀ := v(1−w₀)`. -/
lemma g2_eq_g0_add_g0w0 {v : ℝ³ → ℝ} (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (x : ℝ³) :
    g2 v h x = g0 v h x + g0 v h x * (Classical.choose h x) := by
  dsimp [g2, g0]
  ring

/-- the integrand identity at function level: `g₂ = g₀ + g₀·w₀` as
functions. -/
lemma g2_eq_g0_add_g0w0_fun {v : ℝ³ → ℝ} (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) :
    (fun x : ℝ³ => g2 v h x)
      = fun x : ℝ³ => g0 v h x + g0 v h x * (Classical.choose h x) := by
  funext x
  exact g2_eq_g0_add_g0w0 h x

/-- mass split: `∫g₂ = ∫g₀ + ∫(g₀·w₀)` (Bochner linearity, from the
pointwise identity and the integrability of the three summands). -/
lemma g2_mass_split {v : ℝ³ → ℝ} {R : ℝ} (hR : 0 < R) (hv_nonneg : 0 ≤ v)
    (hvrad : IsRadial v) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) :
    (∫ x : ℝ³, g2 v h x)
      = (∫ x : ℝ³, g0 v h x) + (∫ x : ℝ³, g0 v h x * (Classical.choose h x)) := by
  have hg0 : MeasureTheory.Integrable (g0 v h) := g0_integrable hR hv_supp h
  have hgw0 : MeasureTheory.Integrable (fun x : ℝ³ => g0 v h x * (Classical.choose h x)) :=
    g0w0_integrable hR hv_nonneg hvrad hv_supp h
  have hcong : (∫ x : ℝ³, g2 v h x)
      = ∫ x : ℝ³, g0 v h x + g0 v h x * (Classical.choose h x) := by
    apply integral_congr_ae
    exact ae_of_all _ (by intro x; exact g2_eq_g0_add_g0w0 h x)
  rw [hcong]
  exact MeasureTheory.integral_add hg0 hgw0

/-- **the kernel-mass completion (exact)**: over the centred cube
`∬wPair(g₂) = ∬wPair(g₀) + ℓ³·∫(g₀·w₀)` — the corpus-exact form of FS
lm:w2>w1 (`ĝω(0) := ∫g₀w₀`, `∫χ_ℓ² = ℓ³`; no `(R/λ₁)²`-loss). -/
lemma wPair_g2_g0_box_mass {v : ℝ³ → ℝ} {R ℓ : ℝ} (hR : 0 < R) (hv_nonneg : 0 ≤ v)
    (hvrad : IsRadial v) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hℓ : 0 < ℓ) (hRℓ : R ≤ ℓ * chiR0) :
    (∫ p in acube ℓ ×ˢ acube ℓ, wPairU ℓ (g2 v h) p)
      = (∫ p in acube ℓ ×ˢ acube ℓ, wPairU ℓ (g0 v h) p)
          + ℓ ^ 3 * (∫ x : ℝ³, g0 v h x * (Classical.choose h x)) := by
  have hw2 := w2c_acube_integral hR hv_nonneg hvrad hv_supp h hℓ hRℓ
  have hw1 := w1c_acube_integral hR hv_supp h hℓ hRℓ
  have hms := g2_mass_split hR hv_nonneg hvrad hv_supp h
  have hg0int : (∫ x : ℝ³, g0 v h x) = 8 * π * a v := g0_integral hR hv_supp h
  calc
    (∫ p in acube ℓ ×ˢ acube ℓ, wPairU ℓ (g2 v h) p)
        = ℓ ^ 3 * (∫ x : ℝ³, g2 v h x) := hw2
    _ = ℓ ^ 3 * ((∫ x : ℝ³, g0 v h x) + (∫ x : ℝ³, g0 v h x * (Classical.choose h x))) := by
        rw [hms]
    _ = ℓ ^ 3 * (∫ x : ℝ³, g0 v h x) + ℓ ^ 3 * (∫ x : ℝ³, g0 v h x * (Classical.choose h x)) := by ring
    _ = ℓ ^ 3 * (8 * π * a v) + ℓ ^ 3 * (∫ x : ℝ³, g0 v h x * (Classical.choose h x)) := by
        rw [hg0int]
    _ = (∫ p in acube ℓ ×ˢ acube ℓ, wPairU ℓ (g0 v h) p)
          + ℓ ^ 3 * (∫ x : ℝ³, g0 v h x * (Classical.choose h x)) := by
        rw [hw1]

/-- `∬w₂ = ∬w₁ + ℓ³·∫(g₀·w₀)`, in the order used by the A0-completion
(corpus form of FS lm:w2>w1's leading identity). -/
lemma wPair_g2_box_ge_w1_mass {v : ℝ³ → ℝ} {R ℓ : ℝ} (hR : 0 < R) (hv_nonneg : 0 ≤ v)
    (hvrad : IsRadial v) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hℓ : 0 < ℓ) (hRℓ : R ≤ ℓ * chiR0) :
    (∫ p in acube ℓ ×ˢ acube ℓ, wPairU ℓ (g0 v h) p)
        + ℓ ^ 3 * (∫ x : ℝ³, g0 v h x * (Classical.choose h x))
      ≤ (∫ p in acube ℓ ×ˢ acube ℓ, wPairU ℓ (g2 v h) p) := by
  rw [wPair_g2_g0_box_mass hR hv_nonneg hvrad hv_supp h hℓ hRℓ]

/-- **the A0 quadratic completion** (pure algebra; the FS
`½x²·∬w₂ − ½ĝω(0)·x²·∫χ² = ½x²·∬w₁`-cancellation, `∫χ_ℓ² = ℓ³`):
for a count-quadratic coefficient `n²/(2ℓ⁶)`,

    (n²/(2·ℓ⁶))·∬w₂ − (1/2)·(∫g₀w₀)·(n²/ℓ³) = (n²/(2·ℓ⁶))·∬w₁

given the mass equality `∬w₂ = ∬w₁ + ℓ³·∫g₀w₀`.  Stated over ℝ with
`W1 := ∬wPair(g₀)`, `W2 := ∬wPair(g₂)`, `G := ∫g₀·w₀` and the hypothesis
`W2 = W1 + ℓ³·G`. -/
lemma a0_quad_completion (n ℓ W1 W2 G : ℝ) (hℓ : ℓ ≠ 0) (hW : W2 = W1 + ℓ ^ 3 * G) :
    (n ^ 2 / (2 * ℓ ^ 6)) * W2 - (1 / 2) * G * (n ^ 2 / ℓ ^ 3)
      = (n ^ 2 / (2 * ℓ ^ 6)) * W1 := by
  rw [hW]
  have hc : (n ^ 2 / (2 * ℓ ^ 6)) * (ℓ ^ 3 * G) = (1 / 2) * G * (n ^ 2 / ℓ ^ 3) := by
    field_simp [hℓ]
  have hd : (n ^ 2 / (2 * ℓ ^ 6)) * (W1 + ℓ ^ 3 * G)
      = (n ^ 2 / (2 * ℓ ^ 6)) * W1 + (n ^ 2 / (2 * ℓ ^ 6)) * (ℓ ^ 3 * G) := by ring
  rw [hd, hc]
  ring

end BoseGases

end Submission
