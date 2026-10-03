import Mathlib
import Submission.Work.Peluse.Nodes

/-!
# `PaperRoute`: the paper-faithful verbatim forms of Peluse's Theorems 3.5/3.7 and Corollary 3.8

Lead audit `PW_A6_A2_LEAD.md` §2.4 (2026-10-03).  This directory replaces the *band* route
(`Work.Peluse.UControl.Theorem37Chapter` / `Work.Peluse.PeluseUControl`, which demand `U^s` control
for **every** shift length `D ≥ 1`, including the degenerate range in which Peluse's Theorem 3.7 is
silent) by the paper's own regime, in which the node is assembled from the **proved** faithful
Proposition 3.4 (`Work.Peluse.UControl.prop34Holds : Prop34 P`) together with `Prop36S` (Peluse's
§5, the only open mathematics).

The wiring nodes (owner L1701):

* `Theorem37Paper P` — Peluse's Theorem 3.7 in the paper's regime (provisos
  `C·L ≤ δ^K·N₀` and `C·(δ⁻¹N₀/L)^K ≤ N₀`).  **DROPPED / UNUSED**: the audit
  `Submission/Work/Peluse/CONCAT_AUDIT_LEAD.md` §1.1/§1.3 shows that its only intended hypothesis
  `Prop36S P` is FALSE, and §1.19 replaces Q1 by the chapter `PiecePet`
  (`Work.Peluse.UControl.PiecePetTwo`, `PaperRoute/PiecePetTwo.lean`).  The definition is kept only
  because it is referenced by `PW_A6_A2_LEAD.md`; nothing on the route consumes it;
* `PeluseUControlPaper P` (Q2) — Corollary 3.8 + Theorem 3.7 with the *single* shift length
  `D = ⌊δ^K N^d / C⌋`, proved from `Theorem37Paper P` as `ucontrolPaper_of_theorem37Paper`;
* `crux_of_nodes_paper` (Q3) — the same `PeluseCrux` bookkeeping as the proved
  `Work.Peluse.crux_of_nodes`, from `PeluseUControlPaper` and `PeluseULowering`;
* `Work.KMTAreas.area_A2` (Q4) — the frozen target.

The statements below are the lead's, verbatim apart from the explicit coercions `ℕ → ℝ`.
-/

set_option autoImplicit false
open scoped BigOperators
open Polynomial

namespace Work.Peluse

noncomputable section

/-- **Peluse's Theorem 3.7** (`PW_A6_A2_LEAD.md` §2.4 Q1) for the configuration `(x, x+y, x+P(y))`,
in the paper's regime: besides the scale relations and the smallness `C·L ≤ δ^K·N₀` (Peluse's
`δ' ≪ δ^{O(1)}` with `δ' = L/N^d`), it carries the **non-degeneracy** `C·(δ⁻¹N₀/L)^K ≤ N₀`
(Peluse's `N ≫ (q/δδ')^{O(1)}`), which with `K ≥ d + 1` also forces the window condition
`2 ≤ ⌊δ'N⌋`. -/
def Theorem37Paper (P : Polynomial ℤ) : Prop :=
  ∃ s : ℕ, 2 ≤ s ∧ ∀ A' : ℝ, 1 ≤ A' → ∃ C : ℝ, 0 < C ∧ ∃ K : ℕ, 1 ≤ K ∧
    ∀ (N N₀ L : ℕ) (f₀ f₁ f : ℤ → ℂ) (δ : ℝ),
      2 ≤ P.natDegree → 1 ≤ N → 1 ≤ N₀ → 1 ≤ L →
      (N₀ : ℝ) ≤ A' * (N : ℝ) ^ P.natDegree →
      (N : ℝ) ^ P.natDegree ≤ A' * (δ⁻¹) * (N₀ : ℝ) →
      0 < δ → δ ≤ 1 →
      C * (L : ℝ) ≤ δ ^ K * (N₀ : ℝ) →
      C * ((δ⁻¹) * (N₀ : ℝ) / (L : ℝ)) ^ K ≤ (N₀ : ℝ) →
      SupportIn f₀ N₀ → SupportIn f₁ N₀ → SupportIn f N₀ →
      (∀ x : ℤ, ‖f₀ x‖ ≤ 1) → (∀ x : ℤ, ‖f₁ x‖ ≤ 1) → (∀ x : ℤ, ‖f x‖ ≤ 1) →
      δ ≤ ‖LambdaZ N₀ N P f₀ f₁ f‖ →
      δ ^ K ≤ C * A' ^ K * (δ⁻¹) ^ K *
        uNormPow s (arithIcc ((P.natDegree.factorial : ℤ) * P.leadingCoeff) L)
          (symIcc N₀) f

/-- **Corollary 3.8 + Theorem 3.7 at the single shift length of the crux**
(`PW_A6_A2_LEAD.md` §2.4 Q2): the `U^s` control of the dual function of `f₀, f₁` at the direction
set `lc P [D]` with `D = ⌊δ^K N^d / C⌋` and the support window `dSup P N₀ N`, under the
non-degeneracy `C·δ^{-K₂} ≤ N` on the `y`-range. -/
def PeluseUControlPaper (P : Polynomial ℤ) : Prop :=
  ∃ s : ℕ, 2 ≤ s ∧ ∀ A' : ℝ, 1 ≤ A' → ∃ C K K₂ : ℕ, 1 ≤ C ∧ 1 ≤ K ∧ 1 ≤ K₂ ∧
    ∀ (N N₀ : ℕ) (f₀ f₁ f₂ : ℤ → ℂ) (δ : ℝ),
      2 ≤ P.natDegree → 1 ≤ N → 1 ≤ N₀ →
      (N₀ : ℝ) ≤ A' * (N : ℝ) ^ P.natDegree →
      (N : ℝ) ^ P.natDegree ≤ A' * (δ⁻¹) * (N₀ : ℝ) →
      0 < δ → δ ≤ 1 → (C : ℝ) * (δ⁻¹) ^ K₂ ≤ (N : ℝ) →
      SupportIn f₀ N₀ → SupportIn f₁ N₀ → SupportIn f₂ N₀ →
      (∀ x : ℤ, ‖f₀ x‖ ≤ 1) → (∀ x : ℤ, ‖f₁ x‖ ≤ 1) → (∀ x : ℤ, ‖f₂ x‖ ≤ 1) →
      δ ≤ ‖LambdaZ N₀ N P f₀ f₁ f₂‖ →
      δ ^ K ≤ (C : ℝ) * A' ^ K * (δ⁻¹) ^ K *
        uNormPow s (arithIcc P.leadingCoeff
            (⌊δ ^ K * (N : ℝ) ^ P.natDegree / (C : ℝ)⌋).toNat)
          (symIcc (dSup P N₀ N)) (dualFn N P f₀ f₁)

end

end Work.Peluse
