/-
Area `A7REC`: **the corrected C1e leaf** (`A7Y6Values2Prop`) and the Props of its proof.

## Why a corrected statement

The contracted leaf C1e is

```
A7Y6ValuesProp :  G simple, |G| = 2520, z involution, σ of order 3 with zσ = σz,
                  ρ : G → GL₆(ℂ) irreducible with trace (ρ z) = 2 and trace (ρ (zσ)) = -1,
                  τ' an involution inverting σ, the degree-6 character unique,
                  ⊢ trace (ρ σ) = 3  ∧  ∀ x, x⁷ = 1 → trace (ρ x) = -1.
```

Its hypotheses are *too weak* for the intended proof (and for any proof that does not already
know `G ≃* A₇`, which is the very thing the area is proving): nothing in
`A7Y6ValuesProp` relates the other involutions of `G` to `z`.  The value at `σ` is pinned down by
comparing *three* involutions — the commuting involution `z` and the involution `w σ` obtained
from an involution `w` inverting `σ` — and for that one must know that **all involutions of `G`
have trace `2`**, i.e. the one-class hypothesis `OneInvClass G` (supplied by area `FUS` and used
by every other C-leaf of this area).  With it the argument closes:

* `χ(σ) = χ(σ⁻¹) = conj (χ(σ))` is real (`w` inverts `σ`), so the multiplicities of the
  eigenvalues `ω`, `ω̄` of `ρ σ` agree, and `χ(σ) = a - b` with `a + 2b = 6`;
* `w σ` is an involution (`w` inverts `σ`), hence `trace (ρ (wσ)) = trace (ρ z) = 2`
  (`OneInvClass`); the eigenspace analysis of the commuting pair `ρ σ`, `ρ w`
  (`A7Y6SigmaLinProp`) then forces `a ≥ 2`, i.e. rules out `χ(σ) = -3`;
* `χ(σ) = 6` is excluded by the faithfulness of `ρ` (`A7RepNeOneProp`) and `χ(σ) = 0` by the
  two given traces `trace (ρ z) = 2`, `trace (ρ (zσ)) = -1`;
* the values at elements of order `7`: `χ(x) = χ(x³)` is the power map of the *cyclotomic*
  Galois automorphism `ζ ↦ ζ³` combined with the uniqueness of the degree-`6` character
  (`A7Y6PowerThreeProp`); multiplicities of the eigenvalues of `ρ x` are therefore constant on
  the nonzero residues (`A7ZetaSevenRelationProp`), so `χ(x) = n₀ - m` with `n₀ + 6m = 6` and
  `χ(x) ∈ {-1, 6}` (`A7Y6SevenValueProp`); `6` is again excluded by faithfulness.

The file also records the elementary local ingredient `A7InvertingInvolutionProp`
(an involution inverting `σ` inside the Sylow `2`-subgroup, from `S ≅ D₈` and
`S ≠ C_G(U)`; this is where the `A₇` *configuration*, not just `A7Y6ValuesProp`'s bare
hypotheses, is used).
-/
import Mathlib
import Submission.Work.A7REC.Excl

namespace Work.A7REC

open Subgroup
open scoped BigOperators

/-! ## 1. The corrected C1e leaf -/

/-- **C1e′ (the corrected C1e).**  The values of the degree-`6` irreducible character, on the
`A₇` configuration with one class of involutions.  Same conclusion as `A7Y6ValuesProp`, with the
missing one-class hypothesis `OneInvClass G` added; `A7Y6ValuesProp` is the special case obtained
by forgetting that hypothesis (so `A7Y6Values2Prop` is *stronger* as a statement:
`A7Y6ValuesProp` follows from it, which is the direction the assembly uses). -/
def A7Y6Values2Prop : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (z : G) (U V : Subgroup G),
    A7RecHyps G S z U V → OneInvClass G →
    ∀ (σ : G) (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
      (ρ : Representation ℂ G W),
      σ ∈ U → σ ≠ 1 → orderOf σ = 3 → z * σ = σ * z →
      Representation.IsIrreducible ρ → Module.finrank ℂ W = 6 →
      LinearMap.trace ℂ W (ρ z) = 2 → LinearMap.trace ℂ W (ρ (z * σ)) = -1 →
      (∀ (W' : Type) [AddCommGroup W'] [Module ℂ W'] [FiniteDimensional ℂ W']
        (ρ' : Representation ℂ G W'), Representation.IsIrreducible ρ' →
        Module.finrank ℂ W' = 6 →
        ∀ g : G, LinearMap.trace ℂ W' (ρ' g) = LinearMap.trace ℂ W (ρ g)) →
      LinearMap.trace ℂ W (ρ σ) = 3 ∧ ∀ x : G, orderOf x = 7 → LinearMap.trace ℂ W (ρ x) = -1

/-! ## 2. The Props of the proof of `A7Y6Values2Prop` -/

/-- **The linear algebra of the value at `σ`.**  Two commuting-in-a-twisted-sense linear
endomorphisms of a `6`-dimensional `ℂ`-space: if `B` conjugates `A` to `A² = A⁻¹`, `BA` has trace `2`,
and `C` is a commuting involution with `trace C = 2` and `trace (CA) = -1`, then
`trace A = 3`.

Everything is trace-theoretic: the eigenvalues of `A` are cube roots of unity with multiplicities
`(a, b, b)` (`B` swaps the `ω`- and `ω̄`-eigenspaces), `trace (BA) = p - q` on `Fix A` forces
`a ≥ 2` and `a` even, and `(a,b) = (2,2)` is incompatible with `trace C = 2`, `trace (CA) = -1`. -/
def A7Y6SigmaLinProp : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V],
    Module.finrank ℂ V = 6 →
    ∀ (A B C : Module.End ℂ V),
      A ^ 3 = 1 → B ^ 2 = 1 → B * A * B = A * A → C ^ 2 = 1 → A * C = C * A →
      LinearMap.trace ℂ V (B * A) = 2 →
      LinearMap.trace ℂ V C = 2 → LinearMap.trace ℂ V (C * A) = -1 →
      LinearMap.trace ℂ V A = 3

/-- **The `7`-th roots of unity relation.**  A vanishing integral combination of the `7`-th roots
of unity has all coefficients equal (the minimal polynomial of a primitive `7`-th root of unity
has degree `6`, and its six nonzero coefficients are equal). -/
def A7ZetaSevenRelationProp : Prop :=
  ∀ (ζ : ℂ), IsPrimitiveRoot ζ 7 → ∀ c : Fin 7 → ℤ,
    (∑ k : Fin 7, (c k : ℂ) * ζ ^ (k : ℕ)) = 0 → ∀ k l : Fin 7, c k = c l

/-- **The value at an element of order `7`, from the power map `g ↦ g³`.**  If the character
value at `x` (order `7`) is invariant under the cyclotomic power map `x ↦ x³`, then it is `-1` or
`6` (the multiplicities of the eigenvalues `ζ^k`, `k ≠ 0`, of `ρ x` are all equal). -/
def A7Y6SevenValueProp : Prop :=
  ∀ (G : Type) [Group G] (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V],
    Module.finrank ℂ V = 6 → ∀ (ρ : Representation ℂ G V) (x : G), orderOf x = 7 →
      LinearMap.trace ℂ V (ρ (x ^ 3)) = LinearMap.trace ℂ V (ρ x) →
      LinearMap.trace ℂ V (ρ x) = -1 ∨ LinearMap.trace ℂ V (ρ x) = 6

/-- **The power map `g ↦ g³` on elements of order `7`.**  The cyclotomic automorphism
`ζ ↦ ζ³` of `ℂ` conjugates the degree-`6` irreducible character to `g ↦ χ (g³)`; by the
uniqueness of the degree-`6` character the two agree, so `χ (x³) = χ x` for `x` of order `7`. -/
def A7Y6PowerThreeProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G]
    (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V),
    Representation.IsIrreducible ρ → Module.finrank ℂ V = 6 →
    (∀ (V' : Type) [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V']
      (ρ' : Representation ℂ G V'), Representation.IsIrreducible ρ' →
      Module.finrank ℂ V' = 6 →
      ∀ g : G, LinearMap.trace ℂ V' (ρ' g) = LinearMap.trace ℂ V (ρ g)) →
    ∀ x : G, orderOf x = 7 →
      LinearMap.trace ℂ V (ρ (x ^ 3)) = LinearMap.trace ℂ V (ρ x)

/-- **An element of order `7` is not in the kernel of a trace-`6` representation.**  If
`trace (ρ x) = finrank` for `x` of order `7`, then `ρ x = 1` (the eigenvalues of `ρ x` are `7`-th
roots of unity, so a maximal trace forces them all to be `1`). -/
def A7Y6TraceFinrankProp : Prop :=
  ∀ (G : Type) [Group G] (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (x : G), orderOf x = 7 →
    LinearMap.trace ℂ V (ρ x) = (Module.finrank ℂ V : ℂ) → ρ x = 1

/-- **Faithfulness.**  In a simple group, an irreducible representation whose trace at `z` is
different from the dimension has `ρ x ≠ 1` for every `x ≠ 1`. -/
def A7RepNeOneProp : Prop :=
  ∀ (G : Type) [Group G] (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (z : G), IsSimpleGroup G →
    LinearMap.trace ℂ V (ρ z) ≠ (Module.finrank ℂ V : ℂ) →
    ∀ x : G, x ≠ 1 → ρ x ≠ 1

/-- **The inverting involution.**  In the `A₇` configuration, some involution inverts a
non-identity element of `U`: `S ≅ D₈` has `5` involutions, the kernel `C_S(U)` of the conjugation
action of `S` on `U ≅ C₃` is a four-group (`3` involutions), and an element of `S` outside
`C_S(U)` inverts `σ`. -/
def A7InvertingInvolutionProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (ctx : A7RecCtx G) (σ : G),
    σ ∈ ctx.U → σ ≠ 1 → ∃ w : G, orderOf w = 2 ∧ w * σ * w⁻¹ = σ⁻¹

end Work.A7REC
