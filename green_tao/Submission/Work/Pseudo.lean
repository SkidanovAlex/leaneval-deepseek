import Mathlib

set_option linter.unusedSectionVars false

/-!
# Pseudorandom measures (Green–Tao, §3)

Green–Tao's transference principle is stated for a `k`-pseudorandom measure `ν` on `ZMod p`,
i.e. a measure satisfying

* the `(m₀,t₀,L₀)`-**linear forms condition**: for every `m ≤ m₀`, `t ≤ t₀`, every family of
  `m` linear forms `ψᵢ(x) = ∑ⱼ Lᵢⱼ xⱼ + bᵢ` with rational coefficients of numerator and
  denominator at most `L₀`, whose coefficient tuples are nonzero and pairwise not rational
  multiples of each other, `𝔼_x ∏ᵢ ν(ψᵢ(x)) = 1 + O(ε)`, uniformly in the `bᵢ`;
* the `m₀`-**correlation condition**: for every `1 < m ≤ m₀` there is a weight `τ` with all
  moments bounded, `𝔼_x ∏ᵢ ν(x + hᵢ) ≤ ∑_{i<j} τ(hᵢ - hⱼ)`.

and `ν` is `k`-pseudorandom when the parameters are `(k·2^{k-1}, 3k-4, k)` and `2^{k-1}`.
-/

open Finset

namespace GTTrans

/-- Interpretation of a rational coefficient in `ZMod p` (meaningful when its denominator
is less than `p`). -/
def qmod (p : ℕ) [Fact p.Prime] (q : ℚ) : ZMod p := (q.num : ZMod p) / (q.den : ZMod p)

/-- A rational number whose numerator and denominator are bounded by `L₀`. -/
def IsSmallRat (L₀ : ℕ) (q : ℚ) : Prop := q.num.natAbs ≤ L₀ ∧ q.den ≤ L₀

/-- A nonzero tuple of rationals. -/
def NonzeroTuple {t : ℕ} (L : Fin t → ℚ) : Prop := ∃ j, L j ≠ 0

/-- Two tuples of rationals are not proportional. -/
def NotProp {t : ℕ} (L L' : Fin t → ℚ) : Prop := ¬ ∃ lam : ℚ, ∀ j, L' j = lam * L j

/-- The linear form `x ↦ ∑ⱼ Lⱼ xⱼ + b` on `(ZMod p)^t`. -/
def linForm (p : ℕ) [Fact p.Prime] {t : ℕ} (L : Fin t → ℚ) (b : ZMod p)
    (x : Fin t → ZMod p) : ZMod p :=
  (∑ j, qmod p (L j) * x j) + b

/-- **Green–Tao Definition 3.1**: the `(m₀,t₀,L₀)`-linear forms condition with error `ε`. -/
def LinFormsCond (p : ℕ) [Fact p.Prime] (ν : ZMod p → ℝ) (m₀ t₀ L₀ : ℕ) (ε : ℝ) : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι], 1 ≤ Fintype.card ι → Fintype.card ι ≤ m₀ →
  ∀ (t : ℕ), 1 ≤ t → t ≤ t₀ →
  ∀ (L : ι → Fin t → ℚ), (∀ i j, IsSmallRat L₀ (L i j)) →
    (∀ i, NonzeroTuple (L i)) → (∀ i i', i ≠ i' → NotProp (L i) (L i')) →
    ∀ b : ι → ZMod p,
      |((Fintype.card (Fin t → ZMod p) : ℝ))⁻¹ *
          ∑ x : Fin t → ZMod p, ∏ i, ν (linForm p (L i) (b i) x) - 1| ≤ ε

/-- **Green–Tao Definition 3.2**: the `m₀`-correlation condition, with moment bounds `C`. -/
def CorrCond (p : ℕ) [Fact p.Prime] (ν : ZMod p → ℝ) (m₀ : ℕ) (C : ℕ → ℕ → ℝ) : Prop :=
  ∀ m : ℕ, 1 < m → m ≤ m₀ → ∃ τ : ZMod p → ℝ,
    (∀ x, 0 ≤ τ x) ∧
    (∀ q : ℕ, 1 ≤ q → (Fintype.card (ZMod p) : ℝ)⁻¹ * ∑ x, (τ x) ^ q ≤ C m q) ∧
    ∀ h : Fin m → ZMod p,
      (Fintype.card (ZMod p) : ℝ)⁻¹ * ∑ x, ∏ i, ν (x + h i)
        ≤ ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), τ (h i - h j)

/-- **Green–Tao Definition 3.3**: `ν` is `k`-pseudorandom. -/
def KPseudorandom (p : ℕ) [Fact p.Prime] (k : ℕ) (ν : ZMod p → ℝ) (C : ℕ → ℕ → ℝ)
    (ε : ℝ) : Prop :=
  LinFormsCond p ν (k * 2 ^ (k - 1)) (3 * k - 4) k ε ∧ CorrCond p ν (2 ^ (k - 1)) C

/-- The `k`-pseudorandomness of a probability-like measure: `𝔼 ν = 1 + O(ε)` (the `m = 1`
case of the linear forms condition); stated separately for convenience. -/
def IsMeasureCond (p : ℕ) [Fact p.Prime] (ν : ZMod p → ℝ) (ε : ℝ) : Prop :=
  |(Fintype.card (ZMod p) : ℝ)⁻¹ * ∑ x, ν x - 1| ≤ ε

end GTTrans
