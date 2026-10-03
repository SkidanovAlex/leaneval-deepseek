import Mathlib
import Submission.Work.Peluse.Nodes
import Submission.Work.Peluse.UControl.elementary_bound_v2

/-!
# The two chapters behind `Work.Peluse.UControl.coreChapter`

The target `CoreChapter P` (Peluse's Propositions 3.4 + 3.6 for the configuration
`(x, x+y, x+P(y))`, with the level free above a threshold `≥ 2` and the PET non-degeneracy side
condition) is assembled in `Submission/Work/Peluse/UControl/assembly.lean` from the two `Prop`s
defined here.

* `PiecePet P` — the paper's chain *at one fixed level*: from the data's hypotheses at exponent `K`,
  the PET gauge `A'·C_p ≤ C` and the direction bound `κ·L ≤ N₁`, the conclusion holds at level `s₀`.
* `PieceBand P` — the complementary regime: for every level `s ≥ 2`, whenever the smallness
  constant satisfies `C < Θ` (so that the shift parameter is *not* forced small), the conclusion.

## The dictionary

* the paper's `N` (the `x`-range) is our `N₁`, the paper's `M` (the `y`-range) is our `N`;
* the paper's scale relation `M^{deg P} ≍ N` is our `N^d ≍ N₁` (the two `A'`-hypotheses);
* the paper's window `δ'M` is our `⌊δ'N⌋`, and the paper's direction set `(deg P)!c_ℓ[δ'M^{deg P}]`
  is `arithIcc ((deg P)!·lc P) ⌊δ'N^d⌋ = arithIcc (dirCoeff P) (dirLen P δ' N)`;
* `Λ^{N₁,N}_{X,P}(g₀,g₁,g₂)` is `LambdaZ N₁ N P g₀ g₁ g₂`;
* the smallness hypothesis `C·⌊δ'N^d⌋ ≤ γ^K·N₁` is the paper's `δ' ≪ δ^{O(1)}` together with the
  scale relation, and `C ≤ (γδ')^K(δ'N)²` is the paper's `M₁M₂ ≫ (δδ')^{-O(1)}`
  (`M₁ = ⌊δ'N⌋`, `M₂ ≲ M₁`), i.e. the PET non-degeneracy condition which the workspace's
  refutations of the degenerate-window statements show is indispensable.
-/

set_option autoImplicit false
open scoped BigOperators
open Polynomial

namespace Work.Peluse.UControl

noncomputable section

open Work.Peluse

/-- The direction coefficient of the target: `(deg P)! · lc P`. -/
def dirCoeff (P : Polynomial ℤ) : ℤ := (P.natDegree.factorial : ℤ) * P.leadingCoeff

/-- The direction length of the target: `⌊δ' N^{deg P}⌋`. -/
def dirLen (P : Polynomial ℤ) (δ' : ℝ) (N : ℕ) : ℕ := (⌊δ' * (N : ℝ) ^ P.natDegree⌋).toNat

/-- The data hypotheses of `CoreChapter`, packaged into one `Prop`. -/
def Hyp (P : Polynomial ℤ) (A' C : ℝ) (K : ℕ) (N N₁ : ℕ) (g₀ g₁ g₂ : ℤ → ℂ) (γ δ' : ℝ) : Prop :=
  2 ≤ P.natDegree ∧ 1 ≤ N ∧ 1 ≤ N₁ ∧ 0 < γ ∧ γ ≤ 1 ∧ 0 < δ' ∧ δ' ≤ 1 ∧
  1 ≤ (⌊δ' * (N : ℝ)⌋).toNat ∧
  (N₁ : ℝ) ≤ A' * (N : ℝ) ^ P.natDegree ∧ (N : ℝ) ^ P.natDegree ≤ A' * γ⁻¹ * (N₁ : ℝ) ∧
  1 ≤ C ∧ 1 ≤ K ∧
  C * (dirLen P δ' N : ℝ) ≤ γ ^ K * (N₁ : ℝ) ∧
  C ≤ (γ * δ') ^ K * (δ' * (N : ℝ)) ^ 2 ∧
  SupportIn g₀ N₁ ∧ SupportIn g₁ N₁ ∧ SupportIn g₂ N₁ ∧
  (∀ x : ℤ, ‖g₀ x‖ ≤ 1) ∧ (∀ x : ℤ, ‖g₁ x‖ ≤ 1) ∧ (∀ x : ℤ, ‖g₂ x‖ ≤ 1) ∧
  γ ≤ ‖LambdaZ N₁ N P g₀ g₁ g₂‖

/-- The conclusion of the target at level `s`, with the constant `C₂` left out
(the target's right-hand side is `C₂ * Concl ...`). -/
def Concl (P : Polynomial ℤ) (A' C : ℝ) (K : ℕ) (N N₁ : ℕ) (g₂ : ℤ → ℂ) (γ δ' : ℝ)
    (s : ℕ) : Prop :=
  γ ^ K ≤ C * A' ^ K * γ⁻¹ ^ K *
    uNormPow s (arithIcc (dirCoeff P) (dirLen P δ' N)) (symIcc N₁) g₂

/-- **Chapter A — the paper's content, at a fixed level.**

Peluse's Propositions 3.4 + 3.6 for `(x, x+y, x+P(y))`: from the data's hypotheses at exponent `K`,
the PET gauge `A'·C_p ≤ C` and the direction bound `κ·L ≤ N₁`, the conclusion holds at the fixed
level `s₀`.

The two extra hypotheses are exactly what the paper's chain needs and provides:
* `A'·C_p ≤ C` says that the shift parameter `δ' = L/N^d` is small (the data gives
  `δ' ≲ γ^K A'/C`, while the PET/concatenation chain needs `δ' ≪ γ^{O(1)}/C_p`);
* `κ·L ≤ N₁` keeps the AP `κ[L]` inside the ambient interval, which is what the workspace's
  box-norm lemmas assume.
-/
def PiecePet (P : Polynomial ℤ) : Prop :=
  ∃ s₀ : ℕ, 1 ≤ s₀ ∧ ∀ A' : ℝ, 1 ≤ A' →
    ∃ Cp : ℝ, 1 ≤ Cp ∧ ∃ Kp : ℕ, 1 ≤ Kp ∧
    ∀ (C : ℝ), 1 ≤ C → ∀ (K : ℕ), Kp ≤ K →
    ∀ (N N₁ : ℕ) (g₀ g₁ g₂ : ℤ → ℂ) (γ δ' : ℝ),
      Hyp P A' C K N N₁ g₀ g₁ g₂ γ δ' →
      A' * Cp ≤ C →
      (dirCoeff P) * (dirLen P δ' N : ℤ) ≤ (N₁ : ℤ) →
      Concl P A' Cp K N N₁ g₂ γ δ' s₀

/-- **Chapter B — the complementary regime.**

The target's conclusion, for every level `s ≥ 2`, whenever the data's smallness constant `C` is
strictly below a prescribed bound `Θ`.  This is the regime in which the shift parameter is *not*
forced small by the paper's gauge, and in which the direction set `κ[L]` may leave the ambient
interval — the "band" of the area's notes, i.e. the range where the source's
`N ≫ (q/δδ')^{O(1)}` is genuinely used.
-/
def PieceBand (P : Polynomial ℤ) : Prop :=
  ∀ s : ℕ, 2 ≤ s → ∀ A' : ℝ, 1 ≤ A' → ∀ Θ : ℝ, 1 ≤ Θ →
    ∃ Cb : ℝ, 1 ≤ Cb ∧ ∃ Kb : ℕ, 1 ≤ Kb ∧
    ∀ (C : ℝ), 1 ≤ C → ∀ (K : ℕ), Kb ≤ K →
    ∀ (N N₁ : ℕ) (g₀ g₁ g₂ : ℤ → ℂ) (γ δ' : ℝ),
      Hyp P A' C K N N₁ g₀ g₁ g₂ γ δ' →
      C < Θ →
      γ ^ K ≤ Cb * C * A' ^ K * γ⁻¹ ^ K *
        uNormPow s (arithIcc (dirCoeff P) (dirLen P δ' N)) (symIcc N₁) g₂

end

end Work.Peluse.UControl
