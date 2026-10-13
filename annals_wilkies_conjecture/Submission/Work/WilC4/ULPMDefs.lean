/-
  WilC4/ULPMDefs : the vocabulary of the lead's C4 route (2026-10-10).

  Design: `sources/wilkiesC4route/wilkies_C4_route.md`; statements: `WilC4/Route.lean`.
  This file only *defines* the route's notions, so that the lemmas about them can be delegated
  without access to the (still unproved) statements of `WilC4/Route.lean`.

  * `SameSide N B x₁ x₂`: `x₁, x₂` are on the same side of every breakpoint `b ∈ B`, each at
    distance more than the factor `N`.
  * `ModelULPM M`: uniform log-piecewise-monomiality of `M`-definable families.
  * `GapLemma M`: if `a > 0` is in a gap of the value set of the `dcl`-closed `T`, then every
    nonzero `z ∈ Dcl T {a}` has `ν z ∈ ℚ·ν a + Γ T`.
-/
import Submission.Work.WilC4.Defs

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilC4.Route
open WilkiesDesign WilkiesDesign.CG FirstOrder FirstOrder.Language Work.WilC4

/-- `x₁, x₂` lie on the same side of every breakpoint `b ∈ B`, each at distance > factor `N`. -/
def SameSide {M : Type} [Field M] [LinearOrder M] (N : ℕ) (B : Set M) (x₁ x₂ : M) : Prop :=
  ∀ b ∈ B, ((N : M) * b < x₁ ∧ (N : M) * b < x₂) ∨ ((N : M) * x₁ < b ∧ (N : M) * x₂ < b)

/-- **Uniform log-piecewise-monomial property (ULPM)** of a structure: for every `∅`-definable
family of functions `x ↦ y` (parameters `c`) there are `N`, a finite exponent set `Qs` and an
`∅`-definable family of finite breakpoint sets `B_c` such that any two positive points on the same
side (factor `N`) of every breakpoint have the same domain status and satisfy
`|y₂|/x₂^q ≍_N |y₁|/x₁^q` for some `q ∈ Qs`.  First-order for each formula (the `IsRpow`
encoding, `N`, `Qs` and the formula of `B` are fixed), so it transfers from `ℝ` to models. -/
def ModelULPM (M : Type) [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [Ring.CompatibleRing M] [rexpL.Structure M] [(constantsOn ℝ).Structure M] : Prop :=
  ∀ (k : ℕ) (Y : Set (Fin (k + 2) → M)), (∅ : Set M).Definable LRc Y →
    (∀ (c : Fin k → M) (x y y' : M), Fin.cons x (Fin.cons y c) ∈ Y →
        Fin.cons x (Fin.cons y' c) ∈ Y → y = y') →
    ∃ N : ℕ, 0 < N ∧ ∃ Qs : Finset ℚ, ∃ B : Set (Fin (k + 1) → M),
      (∅ : Set M).Definable LRc B ∧ ∀ c : Fin k → M,
        {x : M | Fin.cons x c ∈ B}.encard ≤ N ∧
        ∀ x₁ x₂ : M, 0 < x₁ → 0 < x₂ → SameSide N {x : M | Fin.cons x c ∈ B} x₁ x₂ →
          ((∃ y, Fin.cons x₁ (Fin.cons y c) ∈ Y) ↔ (∃ y, Fin.cons x₂ (Fin.cons y c) ∈ Y)) ∧
          ∀ y₁ y₂ : M, Fin.cons x₁ (Fin.cons y₁ c) ∈ Y → Fin.cons x₂ (Fin.cons y₂ c) ∈ Y →
            ∃ q ∈ Qs, ∃ t₁ t₂ : M, IsRpow x₁ q t₁ ∧ IsRpow x₂ q t₂ ∧
              |y₂| * t₁ ≤ (N : M) * (|y₁| * t₂) ∧ |y₁| * t₂ ≤ (N : M) * (|y₂| * t₁)

/-- **Gap lemma** (the whole content of the preparation step): if `a > 0` is in a gap of the
value set of the `dcl`-closed `T` (no `c ∈ T` has the value of `a`), then every nonzero `z`
definable from `T ∪ {a}` has `ν z ∈ ℚ·ν a + Γ T`. -/
def GapLemma (M : Type) [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [Ring.CompatibleRing M] [rexpL.Structure M] [(constantsOn ℝ).Structure M] : Prop :=
  ∀ (T : Set M), (∀ x : M, DefinableElt T ∅ x ↔ x ∈ T) →
    ∀ a : M, 0 < a → (∀ c ∈ T, c ≠ 0 → ¬ ValEq a c) →
    ∀ z ∈ Dcl T {a}, z ≠ 0 →
      ∃ (p : ℤ) (n : ℕ), 0 < n ∧ ∃ α ∈ T, α ≠ 0 ∧ IsUnitVal (z ^ n / (α * a ^ p))

end Work.WilC4.Route
