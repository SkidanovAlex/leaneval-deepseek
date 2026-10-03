/-
# Definitions for `Work.KMTAreas.A4.lip2Gen` (Proposition `lip-2` with a free support window)

Krause--Mirek--Tao, §5.2, Proposition `lip-2` (the alternate inverse theorem for `g`) is needed by
Theorem `improv`(ii) with a **free support window** `N₀ ∈ [N^d/A, A N^d]`: the constants are
allowed to depend on `A` but not on `ρ` (the `P`-dependent window is unavoidable, see
`NOTES_A4_window_pin_GAP.md`).

The proof of `lip-2` (paper §5.2, and `A4/lip2Step1.lean` for the pinned window) proceeds through
the *fine* form of Proposition `lip`, in which the Fourier support of the returned dual function is
a union of `q ≲ δ^{-O(1)}` arcs of radius `2^k ≲ δ^{-O(1)}/N` around the `q`-torsion frequencies
(rather than the Ionescu--Wainger major arcs, whose cardinality is super-polynomial in `δ⁻¹`).
This module fixes the vocabulary of that chain:

* `LipL1FineA P` --- the free-window fine inverse theorem (the `A`-parameterised form of
  `Work.KMTAreas.A4.LipL1Fine`, proved for `A = 2` in `A4/lipL1Fine.lean`);
* `WeylIccStatement P` --- the inverse Weyl estimate in the interval (`Icc`) form, exactly the
  conclusion of `Work.KMTAreas.A4.lip2WeylIcc`.
-/
import Mathlib
import Submission.Work.KMTAreas.A4.lip2Defs

set_option autoImplicit false
set_option maxHeartbeats 800000

open scoped BigOperators
open Polynomial

namespace Work.KMTAreas.A4

open Work.Analysis.InverseTheory

/-! ## The free-window fine inverse theorem -/

/-- **Proposition `lip` in the free-window fine form** (`A`-parameterised version of
`Work.KMTAreas.A4.LipL1Fine`): for every `A ≥ 1` there are `C, K > 0` such that, for every
`ρ ∈ (0,1]` and every `1`-bounded triple `f, g, h` supported in `[-N₀,N₀]` with
`N^d/A ≤ N₀ ≤ A N^d` and `⟨Ã_N(f,g),h⟩ ≥ δ N^d`, there is `F` with

`‖F‖_∞ ≤ C δ^{-K}`, `‖F‖_{ℓ¹} ≤ C δ^{-K} N^d`, Fourier support in the union of the arcs of
radius `2^k` around a set `𝔸` of at most `C δ^{-K}` frequencies with `2^k ≤ C δ^{-K}/N`, and
`δ^K N^d ≤ ‖⟨f,F⟩‖`.

The proof follows `A4/lipL1Fine.lean` verbatim, running the Peluse dichotomy `PeluseInverseKMT P`
with the window `A` (which is how `PeluseInverseKMT` is stated) in place of the window `2`; the
only places the window enters are the truncation radius `winA A N d` and the mass bound
`2 MW + 1 ≤ K' δ^{-u} N^d`, which needs `K' ≥ 2A + 2`. -/
def LipL1FineA (P : Polynomial ℤ) : Prop :=
  ∀ A : ℝ, 1 ≤ A → ∃ C K : ℝ, 0 < C ∧ 0 < K ∧
    ∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1 →
    ∀ (N N₀ : ℕ) (δ : ℝ) (f g h : ℤ → ℂ), 1 ≤ N → 0 < δ → δ ≤ 1 →
      (N : ℝ) ^ P.natDegree / A ≤ (N₀ : ℝ) → (N₀ : ℝ) ≤ A * (N : ℝ) ^ P.natDegree →
      SupportIn f N₀ → SupportIn g N₀ → SupportIn h N₀ →
      (∀ x : ℤ, ‖f x‖ ≤ 1) → (∀ x : ℤ, ‖g x‖ ≤ 1) → (∀ x : ℤ, ‖h x‖ ≤ 1) →
      δ * (N : ℝ) ^ P.natDegree ≤ ‖bilinPair (AhalfZ N P f g) h‖ →
      ∃ (F : ℤ → ℂ) (k : ℤ) (𝔸 : Finset FreqCircle),
        (∀ x : ℤ, ‖F x‖ ≤ C * δ⁻¹ ^ K) ∧
        Summable (fun x : ℤ => ‖F x‖) ∧
        (∑' x : ℤ, ‖F x‖ ≤ C * δ⁻¹ ^ K * (N : ℝ) ^ P.natDegree) ∧
        FourierSupportIn F (⋃ α ∈ (𝔸 : Set FreqCircle), arcSet α ((2 : ℝ) ^ k)) ∧
        (𝔸.card : ℝ) ≤ C * δ⁻¹ ^ K ∧
        (2 : ℝ) ^ k ≤ C * δ⁻¹ ^ K / (N : ℝ) ∧
        δ ^ K * (N : ℝ) ^ P.natDegree ≤ ‖bilinPair f F‖

/-! ## The inverse Weyl estimate in the `Icc` form -/

/-- **The inverse Weyl estimate of `lip-2`** (the conclusion of `Work.KMTAreas.A4.lip2WeylIcc`):
if the windowed exponential sum `∑_{n ∈ Icc a b} win M γ (n - s) e (ξ P n)` is at least `ε`, with
`2 ≤ M`, `0 < ε ≤ 1/2` and `ε ^ (-K) ≤ M`, then `ξ · lc P` is within `C ε ^ (-K) / M ^ deg P` of a
rational number of denominator at most `C ε ^ (-K)`. -/
def WeylIccStatement (P : Polynomial ℤ) : Prop :=
  ∃ C K : ℝ, 0 < C ∧ 0 < K ∧
    ∀ (M ε : ℝ) (γ : FreqCircle) (ξ : ℝ) (s : ℤ) (a b : ℤ),
      2 ≤ M → 0 < ε → ε ≤ 1 / 2 → ε ^ (-K) ≤ M → a ≤ b →
      ε ≤ ‖winSumIcc M γ ξ P s a b‖ →
      ∃ (q : ℕ) (a' : ℤ), 1 ≤ q ∧ (q : ℝ) ≤ C * ε ^ (-K) ∧
        |ξ * (P.leadingCoeff : ℝ) - (a' : ℝ) / (q : ℝ)|
          ≤ C * ε ^ (-K) / M ^ P.natDegree

end Work.KMTAreas.A4
