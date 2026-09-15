import Submission.FUP.BMApply
import Submission.FUP.BMToDamping
import Submission.FUP.HanSchlagComparison
import Submission.FUP.BMReduction
import Submission.FUP.ExtensionOperator
import Submission.FUP.ModifyWeightFinal
import Submission.FUP.EomegaHessian
import Submission.FUP.PaleyWiener
import Submission.FUP.PSHToFourier4

open FractalUncertainty MeasureTheory FourierTransform Metric
open scoped ENNReal BigOperators
open Submission.FUP

set_option autoImplicit false
variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

namespace Submission.FUP

/-!
# The proof chain of Cohen's Theorem 1.1, with exactly two literature inputs

This module assembles the whole formalised part of the proof of Cohen's *Fractal uncertainty in
higher dimensions* (Annals 202 (1), 2025):

* §6.2 (the passage from damping functions to the uncertainty principle)
  — `Assembly.theorem_1_1_of_black_boxes`;
* §6.1 (line porosity of `Y` produces a weight `ω` with the Kohn–Nirenberg regularity and the
  Beurling–Malliavin growth conditions, whence — via Beurling–Malliavin — damping functions)
  — `BMApply.existence_damping_of_BM`;
* the passage from the raw Beurling–Malliavin theorem to the `L²` form used in §6.1
  — `higher_dim_BM_damping_of_BM`;
* Appendix A.1 (the comparison between Han–Schlag's original Theorem 5.1 — box porosity and
  `ℓ₁` damping functions — and the form used in §6 — ball porosity and `ℓ₂` damping functions)
  — `FUP_conditional_damping_of_han_schlag`.

The only remaining inputs are the two theorems of the literature, both recorded verbatim as `Prop`s
in `Submission.FUP.Spec`:

* `Spec.han_schlag_statement` — Han–Schlag's Theorem 5.1;
* `Spec.higher_dim_BM_statement` — Cohen's `thm:higher_dim_BM`.
-/

/-- Cohen's `prop:existence_damping` from the higher-dimensional Beurling–Malliavin theorem. -/
theorem existence_damping_of_higher_dim_BM (hd : 1 ≤ d)
    (hBM : Spec.higher_dim_BM_statement (d := d)) :
    Spec.existence_damping_statement (d := d) :=
  existence_damping_of_BM hd (higher_dim_BM_damping_of_BM hd hBM)

/-- Cohen's Theorem 1.4 from Han–Schlag's Theorem 5.1 (Appendix A.1). -/
theorem FUP_conditional_damping_of_han_schlag_statement (hd : 1 ≤ d)
    (hHS : Spec.han_schlag_statement (d := d)) :
    Spec.FUP_conditional_damping_statement (d := d) :=
  FUP_conditional_damping_of_han_schlag hd hHS

/-- **Cohen's Theorem 1.1 from the two literature inputs.** -/
theorem theorem_1_1_of_literature (hd : 1 ≤ d)
    (hHS : Spec.han_schlag_statement (d := d))
    (hBM : Spec.higher_dim_BM_statement (d := d)) :
    ∀ (ν : ℝ), 0 < ν → ∃ (β C : ℝ), β > 0 ∧ C > 0 ∧
      ∀ (h : ℝ) (X Y : Set ℝᵈ) (hX : MeasurableSet X) (hY : MeasurableSet Y),
        h ∈ Set.Ioo 0 (1 / 100) →
        X ⊆ cube (-1) 1 → PorousOnBalls ν h 1 X → Y ⊆ cube (-h⁻¹) h⁻¹ →
          PorousOnLines ν 1 h⁻¹ Y → ∀ (f : Lp ℂ 2),
            (𝓕 f : Lp ℂ 2) =ᵐ[volume.restrict Yᶜ] 0 →
            (eLpNorm (X.indicator (f : ℝᵈ → ℂ)) 2).toReal ≤ C * h ^ β * ‖f‖ :=
  theorem_1_1_of_black_boxes (FUP_conditional_damping_of_han_schlag hd hHS)
    (existence_damping_of_higher_dim_BM hd hBM)

/-- **Cohen's Theorem 1.1 from Han–Schlag's Theorem 5.1 and the three components of
Beurling–Malliavin** (§3–§4 PSH extension, §5 Hörmander, and Paley–Wiener). -/
theorem theorem_1_1_of_four_components (hd : 1 ≤ d)
    (hHS : Spec.han_schlag_statement (d := d))
    (hBM1 : BM_step1_statement (d := d))
    (hBM2 : psh_to_bounded_fourier_statement (d := d))
    (hPW : paley_wiener_statement (d := d)) :
    ∀ (ν : ℝ), 0 < ν → ∃ (β C : ℝ), β > 0 ∧ C > 0 ∧
      ∀ (h : ℝ) (X Y : Set ℝᵈ) (hX : MeasurableSet X) (hY : MeasurableSet Y),
        h ∈ Set.Ioo 0 (1 / 100) →
        X ⊆ cube (-1) 1 → PorousOnBalls ν h 1 X → Y ⊆ cube (-h⁻¹) h⁻¹ →
          PorousOnLines ν 1 h⁻¹ Y → ∀ (f : Lp ℂ 2),
            (𝓕 f : Lp ℂ 2) =ᵐ[volume.restrict Yᶜ] 0 →
            (eLpNorm (X.indicator (f : ℝᵈ → ℂ)) 2).toReal ≤ C * h ^ β * ‖f‖ :=
  theorem_1_1_of_literature hd hHS (higher_dim_BM_of_components hBM1 hBM2 hPW)

/-- **Cohen's Theorem 1.1 from the paper's own propositions and the literature.**  The inputs are
Han–Schlag's Theorem 5.1, §3 (`exact_psh_extension_statement`, `prop:Ew_is_psh`), the second step
of the Beurling–Malliavin theorem (`prop:psh_to_bounded_fourier` = §5) and the Paley–Wiener
criterion.  §4 (`modify_weight_statement`, the paper's `lem:modify_weight_lemma`, *including* the
convergence of the extensions of the truncations — Lemma 3.1, `lem:Ew_conv_cpct_subsets`) is
*proved* in `Submission.FUP.ModifyWeightFinal`, so §3 is applied directly to the truncations and
the limit is taken; the former, false, `Eomega_seq_statement` hypothesis is gone. -/
theorem theorem_1_1_of_paper_components (hd : 1 ≤ d)
    (hHS : Spec.han_schlag_statement (d := d))
    (hPSH : exact_psh_extension_statement (d := d))
    (hBM2 : psh_to_bounded_fourier_statement (d := d))
    (hPW : paley_wiener_statement (d := d)) :
    ∀ (ν : ℝ), 0 < ν → ∃ (β C : ℝ), β > 0 ∧ C > 0 ∧
      ∀ (h : ℝ) (X Y : Set ℝᵈ) (hX : MeasurableSet X) (hY : MeasurableSet Y),
        h ∈ Set.Ioo 0 (1 / 100) →
        X ⊆ cube (-1) 1 → PorousOnBalls ν h 1 X → Y ⊆ cube (-h⁻¹) h⁻¹ →
          PorousOnLines ν 1 h⁻¹ Y → ∀ (f : Lp ℂ 2),
            (𝓕 f : Lp ℂ 2) =ᵐ[volume.restrict Yᶜ] 0 →
            (eLpNorm (X.indicator (f : ℝᵈ → ℂ)) 2).toReal ≤ C * h ^ β * ‖f‖ :=
  theorem_1_1_of_four_components hd hHS
    (BM_step1_of_components (modify_weight_statement_proof hd) hPSH) hBM2 hPW

/-- **Cohen's Theorem 1.1 with §3 also proved.**  §3 of the paper (`prop:Ew_is_psh`,
`exact_psh_extension_statement`) is proved in `Submission.FUP.EomegaHessian`; the remaining
inputs are Han–Schlag's Theorem 5.1, §5 (Hörmander) and Paley–Wiener. -/
theorem theorem_1_1_of_three_components (hd : 1 ≤ d)
    (hHS : Spec.han_schlag_statement (d := d))
    (hBM2 : psh_to_bounded_fourier_statement (d := d))
    (hPW : paley_wiener_statement (d := d)) :
    ∀ (ν : ℝ), 0 < ν → ∃ (β C : ℝ), β > 0 ∧ C > 0 ∧
      ∀ (h : ℝ) (X Y : Set ℝᵈ) (hX : MeasurableSet X) (hY : MeasurableSet Y),
        h ∈ Set.Ioo 0 (1 / 100) →
        X ⊆ cube (-1) 1 → PorousOnBalls ν h 1 X → Y ⊆ cube (-h⁻¹) h⁻¹ →
          PorousOnLines ν 1 h⁻¹ Y → ∀ (f : Lp ℂ 2),
            (𝓕 f : Lp ℂ 2) =ᵐ[volume.restrict Yᶜ] 0 →
            (eLpNorm (X.indicator (f : ℝᵈ → ℂ)) 2).toReal ≤ C * h ^ β * ‖f‖ :=
  theorem_1_1_of_paper_components hd hHS (exact_psh_extension_statement_proof d) hBM2 hPW

/-- **Cohen's Theorem 1.1 from Han–Schlag's Theorem 5.1 and §5 alone.**  Both §3 (PSH
extension) and Paley–Wiener are now *proved* (`EomegaHessian`, `PaleyWiener`), and §4 is proved in
`ModifyWeightFinal`. -/
theorem theorem_1_1_of_two_components (hd : 1 ≤ d)
    (hHS : Spec.han_schlag_statement (d := d))
    (hBM2 : psh_to_bounded_fourier_statement (d := d)) :
    ∀ (ν : ℝ), 0 < ν → ∃ (β C : ℝ), β > 0 ∧ C > 0 ∧
      ∀ (h : ℝ) (X Y : Set ℝᵈ) (hX : MeasurableSet X) (hY : MeasurableSet Y),
        h ∈ Set.Ioo 0 (1 / 100) →
        X ⊆ cube (-1) 1 → PorousOnBalls ν h 1 X → Y ⊆ cube (-h⁻¹) h⁻¹ →
          PorousOnLines ν 1 h⁻¹ Y → ∀ (f : Lp ℂ 2),
            (𝓕 f : Lp ℂ 2) =ᵐ[volume.restrict Yᶜ] 0 →
            (eLpNorm (X.indicator (f : ℝᵈ → ℂ)) 2).toReal ≤ C * h ^ β * ‖f‖ :=
  theorem_1_1_of_three_components hd hHS hBM2 paley_wiener_statement_proof

/-- **Cohen's Theorem 1.1 from Han–Schlag's Theorem 5.1 and Beurling–Malliavin**
(the same statement, phrased with the conditional fractal uncertainty principle of §6). -/
theorem theorem_1_1_of_two_deep_inputs (hd : 1 ≤ d)
    (hFUP : Spec.FUP_conditional_damping_statement (d := d))
    (hBM : Spec.higher_dim_BM_statement (d := d)) :
    ∀ (ν : ℝ), 0 < ν → ∃ (β C : ℝ), β > 0 ∧ C > 0 ∧
      ∀ (h : ℝ) (X Y : Set ℝᵈ) (hX : MeasurableSet X) (hY : MeasurableSet Y),
        h ∈ Set.Ioo 0 (1 / 100) →
        X ⊆ cube (-1) 1 → PorousOnBalls ν h 1 X → Y ⊆ cube (-h⁻¹) h⁻¹ →
          PorousOnLines ν 1 h⁻¹ Y → ∀ (f : Lp ℂ 2),
            (𝓕 f : Lp ℂ 2) =ᵐ[volume.restrict Yᶜ] 0 →
            (eLpNorm (X.indicator (f : ℝᵈ → ℂ)) 2).toReal ≤ C * h ^ β * ‖f‖ :=
  theorem_1_1_of_BM_and_FUP hd hFUP (higher_dim_BM_damping_of_BM hd hBM)

/-- **Cohen's Theorem 1.1 from the paper's own propositions and the literature, in all
dimensions** (the `d = 0` case is degenerate and is handled separately). -/
theorem theorem_1_1_of_paper_components_all
    (hHS : Spec.han_schlag_statement (d := d))
    (hPSH : exact_psh_extension_statement (d := d))
    (hBM2 : psh_to_bounded_fourier_statement (d := d))
    (hPW : paley_wiener_statement (d := d)) :
    ∀ (ν : ℝ), 0 < ν → ∃ (β C : ℝ), β > 0 ∧ C > 0 ∧
      ∀ (h : ℝ) (X Y : Set ℝᵈ) (hX : MeasurableSet X) (hY : MeasurableSet Y),
        h ∈ Set.Ioo 0 (1 / 100) →
        X ⊆ cube (-1) 1 → PorousOnBalls ν h 1 X → Y ⊆ cube (-h⁻¹) h⁻¹ →
          PorousOnLines ν 1 h⁻¹ Y → ∀ (f : Lp ℂ 2),
            (𝓕 f : Lp ℂ 2) =ᵐ[volume.restrict Yᶜ] 0 →
            (eLpNorm (X.indicator (f : ℝᵈ → ℂ)) 2).toReal ≤ C * h ^ β * ‖f‖ := by
  intro ν hν
  rcases Nat.eq_zero_or_pos d with hd0 | hd0
  · subst hd0
    exact ⟨1, 1, by norm_num, by norm_num, theorem_1_1_of_subsingleton (d := 0) ν hν⟩
  · exact theorem_1_1_of_paper_components (Nat.one_le_iff_ne_zero.mpr (by omega)) hHS hPSH hBM2 hPW ν hν

/-- **Cohen's Theorem 1.1 with §3 also proved, in all dimensions.** -/
theorem theorem_1_1_of_three_components_all
    (hHS : Spec.han_schlag_statement (d := d))
    (hBM2 : psh_to_bounded_fourier_statement (d := d))
    (hPW : paley_wiener_statement (d := d)) :
    ∀ (ν : ℝ), 0 < ν → ∃ (β C : ℝ), β > 0 ∧ C > 0 ∧
      ∀ (h : ℝ) (X Y : Set ℝᵈ) (hX : MeasurableSet X) (hY : MeasurableSet Y),
        h ∈ Set.Ioo 0 (1 / 100) →
        X ⊆ cube (-1) 1 → PorousOnBalls ν h 1 X → Y ⊆ cube (-h⁻¹) h⁻¹ →
          PorousOnLines ν 1 h⁻¹ Y → ∀ (f : Lp ℂ 2),
            (𝓕 f : Lp ℂ 2) =ᵐ[volume.restrict Yᶜ] 0 →
            (eLpNorm (X.indicator (f : ℝᵈ → ℂ)) 2).toReal ≤ C * h ^ β * ‖f‖ :=
  theorem_1_1_of_paper_components_all hHS (exact_psh_extension_statement_proof d) hBM2 hPW

/-- **Cohen's Theorem 1.4 (`thm:higher_dim_BM`) from §5 alone.**  The two earlier steps of §2 —
the PSH extension of a Beurling–Malliavin weight (§3–§4) and the classical Paley–Wiener
criterion — are both proved (`EomegaHessian`, `PaleyWiener`). -/
theorem higher_dim_BM_of_psh_to_bounded_fourier (hd : 1 ≤ d)
    (hBM2 : psh_to_bounded_fourier_statement (d := d)) :
    Spec.higher_dim_BM_statement (d := d) :=
  higher_dim_BM_of_components
    (BM_step1_of_components (modify_weight_statement_proof hd)
      (exact_psh_extension_statement_proof d))
    hBM2 paley_wiener_statement_proof

/-- **Cohen's Theorem 1.4 (`thm:higher_dim_BM`) from the exact-data form of Hörmander's `∂̄`
theorem.**  §5 is now proved (`PSHToFourier4`, from `HormanderStatementExact`), so the
higher-dimensional Beurling–Malliavin multiplier theorem follows from Hörmander's `L²` theory of
the `∂̄` equation by the paper's §2. -/
theorem higher_dim_BM_of_hormander (hd : 1 ≤ d)
    (hH : HormanderStatementExact (d := d)) :
    Spec.higher_dim_BM_statement (d := d) :=
  higher_dim_BM_of_psh_to_bounded_fourier hd (psh_to_bounded_fourier_of_hormander_exact hH)

/-- **Cohen's Theorem 1.1 from Han–Schlag's Theorem 5.1 and Hörmander's `∂̄` theorem.**  These are
the *only* two inputs left: §3, §4, §5 and Paley–Wiener are all proved in this development. -/
theorem theorem_1_1_of_hormander (hd : 1 ≤ d)
    (hHS : Spec.han_schlag_statement (d := d))
    (hH : HormanderStatementExact (d := d)) :
    ∀ (ν : ℝ), 0 < ν → ∃ (β C : ℝ), β > 0 ∧ C > 0 ∧
      ∀ (h : ℝ) (X Y : Set ℝᵈ) (hX : MeasurableSet X) (hY : MeasurableSet Y),
        h ∈ Set.Ioo 0 (1 / 100) →
        X ⊆ cube (-1) 1 → PorousOnBalls ν h 1 X → Y ⊆ cube (-h⁻¹) h⁻¹ →
          PorousOnLines ν 1 h⁻¹ Y → ∀ (f : Lp ℂ 2),
            (𝓕 f : Lp ℂ 2) =ᵐ[volume.restrict Yᶜ] 0 →
            (eLpNorm (X.indicator (f : ℝᵈ → ℂ)) 2).toReal ≤ C * h ^ β * ‖f‖ :=
  theorem_1_1_of_two_components hd hHS (psh_to_bounded_fourier_of_hormander_exact hH)

/-- **Cohen's Theorem 1.1 from Han–Schlag's Theorem 5.1 and Hörmander's `∂̄` theorem, in all
dimensions.** -/
theorem theorem_1_1_of_hormander_all
    (hHS : Spec.han_schlag_statement (d := d))
    (hH : HormanderStatementExact (d := d)) :
    ∀ (ν : ℝ), 0 < ν → ∃ (β C : ℝ), β > 0 ∧ C > 0 ∧
      ∀ (h : ℝ) (X Y : Set ℝᵈ) (hX : MeasurableSet X) (hY : MeasurableSet Y),
        h ∈ Set.Ioo 0 (1 / 100) →
        X ⊆ cube (-1) 1 → PorousOnBalls ν h 1 X → Y ⊆ cube (-h⁻¹) h⁻¹ →
          PorousOnLines ν 1 h⁻¹ Y → ∀ (f : Lp ℂ 2),
            (𝓕 f : Lp ℂ 2) =ᵐ[volume.restrict Yᶜ] 0 →
            (eLpNorm (X.indicator (f : ℝᵈ → ℂ)) 2).toReal ≤ C * h ^ β * ‖f‖ := by
  intro ν hν
  rcases Nat.eq_zero_or_pos d with hd0 | hd0
  · subst hd0
    exact ⟨1, 1, by norm_num, by norm_num, theorem_1_1_of_subsingleton (d := 0) ν hν⟩
  · exact theorem_1_1_of_hormander (Nat.one_le_iff_ne_zero.mpr (by omega)) hHS hH ν hν

/-! ### The chain with Hörmander's theorem as a PROVED input

`Submission/FUP/HormanderPsh.lean` proves Hörmander's `∂̄`-theorem for u.s.c. weights with exact
data (`HormanderPsh.hormanderStatementExact`), i.e. precisely the hypothesis
`HormanderStatementExact` used by §5 (`Submission/FUP/PSHToFourierHormander.lean`).  Hence the
Hörmander input can be discharged, and the only literature input left in the whole development is
Han–Schlag's Theorem 5.1. -/

/-- §5 of Cohen's paper, with **no** unproved input: Hörmander's `∂̄`-theorem is proved in this
development (`HormanderPsh.hormanderStatementExact`). -/
theorem psh_to_bounded_fourier_proof (d : ℕ) :
    psh_to_bounded_fourier_statement (d := d) :=
  psh_to_bounded_fourier_of_hormander_exact (hormanderStatementExact d)

/-- **Cohen's Theorem 1.4 (`thm:higher_dim_BM`)** — with **no** unproved input: §5 is proved, and
so is Hörmander's `∂̄`-theorem. -/
theorem higher_dim_BM_proof (hd : 1 ≤ d) : Spec.higher_dim_BM_statement (d := d) :=
  higher_dim_BM_of_psh_to_bounded_fourier hd (psh_to_bounded_fourier_proof d)

/-- **Cohen's Theorem 1.1 from Han–Schlag's Theorem 5.1 alone.**  This is the sharpest form of the
reduction available: everything else in the paper — §2, §3, §4, §5 (including Hörmander's `∂̄`
theorem and the Beurling–Malliavin multiplier theorem) and the Paley–Wiener criterion — is proved
in this development. -/
theorem theorem_1_1_of_han_schlag (hd : 1 ≤ d)
    (hHS : Spec.han_schlag_statement (d := d)) :
    ∀ (ν : ℝ), 0 < ν → ∃ (β C : ℝ), β > 0 ∧ C > 0 ∧
      ∀ (h : ℝ) (X Y : Set ℝᵈ) (hX : MeasurableSet X) (hY : MeasurableSet Y),
        h ∈ Set.Ioo 0 (1 / 100) →
        X ⊆ cube (-1) 1 → PorousOnBalls ν h 1 X → Y ⊆ cube (-h⁻¹) h⁻¹ →
          PorousOnLines ν 1 h⁻¹ Y → ∀ (f : Lp ℂ 2),
            (𝓕 f : Lp ℂ 2) =ᵐ[volume.restrict Yᶜ] 0 →
            (eLpNorm (X.indicator (f : ℝᵈ → ℂ)) 2).toReal ≤ C * h ^ β * ‖f‖ :=
  theorem_1_1_of_two_components hd hHS (psh_to_bounded_fourier_proof d)

/-- **Cohen's Theorem 1.1 from Han–Schlag's Theorem 5.1 alone, in all dimensions.** -/
theorem theorem_1_1_of_han_schlag_all
    (hHS : Spec.han_schlag_statement (d := d)) :
    ∀ (ν : ℝ), 0 < ν → ∃ (β C : ℝ), β > 0 ∧ C > 0 ∧
      ∀ (h : ℝ) (X Y : Set ℝᵈ) (hX : MeasurableSet X) (hY : MeasurableSet Y),
        h ∈ Set.Ioo 0 (1 / 100) →
        X ⊆ cube (-1) 1 → PorousOnBalls ν h 1 X → Y ⊆ cube (-h⁻¹) h⁻¹ →
          PorousOnLines ν 1 h⁻¹ Y → ∀ (f : Lp ℂ 2),
            (𝓕 f : Lp ℂ 2) =ᵐ[volume.restrict Yᶜ] 0 →
            (eLpNorm (X.indicator (f : ℝᵈ → ℂ)) 2).toReal ≤ C * h ^ β * ‖f‖ := by
  intro ν hν
  rcases Nat.eq_zero_or_pos d with hd0 | hd0
  · subst hd0
    exact ⟨1, 1, by norm_num, by norm_num, theorem_1_1_of_subsingleton (d := 0) ν hν⟩
  · exact theorem_1_1_of_han_schlag (Nat.one_le_iff_ne_zero.mpr (by omega)) hHS ν hν

/-- **Cohen's Theorem 1.1 from Han–Schlag's Theorem 5.1 and §5 alone, in all dimensions.** -/
theorem theorem_1_1_of_two_components_all
    (hHS : Spec.han_schlag_statement (d := d))
    (hBM2 : psh_to_bounded_fourier_statement (d := d)) :
    ∀ (ν : ℝ), 0 < ν → ∃ (β C : ℝ), β > 0 ∧ C > 0 ∧
      ∀ (h : ℝ) (X Y : Set ℝᵈ) (hX : MeasurableSet X) (hY : MeasurableSet Y),
        h ∈ Set.Ioo 0 (1 / 100) →
        X ⊆ cube (-1) 1 → PorousOnBalls ν h 1 X → Y ⊆ cube (-h⁻¹) h⁻¹ →
          PorousOnLines ν 1 h⁻¹ Y → ∀ (f : Lp ℂ 2),
            (𝓕 f : Lp ℂ 2) =ᵐ[volume.restrict Yᶜ] 0 →
            (eLpNorm (X.indicator (f : ℝᵈ → ℂ)) 2).toReal ≤ C * h ^ β * ‖f‖ :=
  theorem_1_1_of_three_components_all hHS hBM2 paley_wiener_statement_proof

end Submission.FUP
