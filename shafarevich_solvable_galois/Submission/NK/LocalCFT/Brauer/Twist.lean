import Submission.NK.LocalCFT.Brauer.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The coefficient twist: which local Brauer statement is true for a `p`-adic field

This module records, as a *named classical input* and in the exact form in which it is true, the
local Brauer computation that the sibling area `Submission/Work/BrauerHasse/` consumes, and
explains why the *trivial*-coefficient form of that statement
(`NK.LocalCFT.LocalH2Nonvanishing`, i.e. `H²(G_κ, ℤ/p) ≠ 0` with trivial `ℤ/p`-coefficients)
is **not** the classical input when `ζ_p ∉ κ`.

## The two statements

Let `κ` be a `p`-adic field (`κ = 𝔭.adicCompletion K` for a number field `K` and a finite prime
`𝔭`) with separable closure `κ'` and `G_κ = Gal(κ'/κ)`, and let `ℓ` be a prime.  There are two
distinct `G_κ`-modules with underlying abelian group `ℤ/ℓ`:

* the **trivial** module `ℤ/ℓ` (the one implemented by `NK.BrauerHasse.Coeff p` together with
  `Rep.trivial`, and hence the one whose second cohomology is `NK.BrauerHasse.H2Profinite p ⊤`);
* the **cyclotomic twist** `μ_ℓ = ℤ/ℓ(1)`, on which `G_κ` acts through the cyclotomic character.

The classical computations (local class field theory) are

1. **Kummer/Brauer**: `H²(G_κ, μ_ℓ) ≅ Br(κ)[ℓ] ≅ ℤ/ℓ` for **every** `p`-adic `κ` and every prime
   `ℓ`.  (`Br(κ) ≅ ℚ/ℤ` is the invariant map; the Kummer sequence `1 → μ_ℓ → κ'ˣ → κ'ˣ → 1`
   together with Hilbert 90 gives `H²(G_κ, μ_ℓ) ≅ Br(κ)[ℓ]`.)  This is the input that the classical
   proof of Neukirch–Uchida uses, in the form of the *local invariant*
   `inv : Br(κ) ≅ ℚ/ℤ` — see NSW (7.2.6), Serre, *Local Fields*, XII–XIV.
2. **Local Tate duality** (Milne, *Arithmetic Duality Theorems*, Theorem I.2.1; Serre, *Local
   Fields*, XI §2, the Poitou–Tate theorem): for a finite `G_κ`-module `M`,
   `Ext^r_{G_κ}(M, κ'ˣ) ≅ H^{2-r}(G_κ, M)^∨`.  Taking `M = ℤ/ℓ` and `r = 0` gives
   `H²(G_κ, ℤ/ℓ) ≅ Hom(μ_ℓ(κ), ℚ/ℤ)` — with `μ_ℓ(κ)` the `ℓ`-th roots of unity *in* `κ`.

Consequently the two statements differ by exactly the twist: the trivial-coefficient group is

  `H²(G_κ, ℤ/ℓ) ≅ ℤ/ℓ  ⟺  μ_ℓ ⊆ κ`  (i.e. `ζ_ℓ ∈ κ`), and `= 0` otherwise,

while the twisted group `H²(G_κ, μ_ℓ) = Br(κ)[ℓ]` is `ℤ/ℓ` for all `κ`.  (Equivalently, with
`h^i = dim_{𝔽_ℓ} H^i(G_κ, M)`, the Euler characteristic theorem — Milne, *Arithmetic Duality
Theorems*, I.2.8 and I.2.9 — gives `h⁰ - h¹ + h² = -[κ:ℚ_p]·dim M` for `M` of `p`-power order and
`h⁰ - h¹ + h² = 0` for `M` of order prime to the residue characteristic; for
`M = ℤ/ℓ` over `κ` this yields exactly the formula above.)

## Why this matters

The sibling area `Submission/Work/BrauerHasse/` states its input with **trivial** coefficients
(`NK.BrauerHasse.LocalFieldBrauerCyclic`, `NK.BrauerHasse.LocalH2Input`, and hence the whole
Hasse-principle development `NK.BrauerHasse.exists_loc_ne_zero`).  By the formula above that
statement is *false* whenever `μ_p ⊄ κ`; the smallest counterexample is `κ = ℚ_p` with `p` odd
(then `μ_p ⊄ ℚ_p`, so `H²(G_ℚ_p, ℤ/p) = 0`).  It is *true* whenever `μ_p ⊆ κ`, and in that case it
is literally the classical statement, because then the cyclotomic character is trivial mod `p` and
the two `G_κ`-modules `μ_p` and `ℤ/p` *coincide*.

Note in particular that for `p = 2` there is no problem at all: `μ_2 = {±1} ⊆ κ` for every field
`κ` of characteristic `≠ 2`, so the trivial-coefficient input is *true* for `p = 2` and every
`p`-adic `κ`.  It is exactly the odd primes for which the different needs the hypothesis.

The definitions below therefore record the input in the honest, coefficient-correct form
(`NK.LocalCFT.LocalBrauerGroupInput`, the Kummer/Brauer statement restricted to the regime where
the trivial coefficients are the right ones), the vanishing in the complementary regime
(`NK.LocalCFT.LocalH2Vanishing`), and the resulting *equivalence* for the sibling's statement:
for a `p`-adic `κ`,

  `LocalH2Nonvanishing p κ κ'  ⟺  μ_p ⊆ κ`  (given the two classical inputs).

Everything in this file is proved; the two inputs are named classical theorems, as in
`Submission/Work/LocalCFT/Brauer/Basic.lean`.
-/

open CategoryTheory

universe u

namespace NK.LocalCFT

/-- **The local Brauer input in its coefficient-correct form.**

For a `p`-adic field `κ`: whenever `κ` contains a primitive `p`-th root of unity, the
trivial-`ℤ/p`-coefficient group `H²(G_κ, ℤ/p)` is non-zero (indeed `≅ ℤ/p`).  In that regime the
cyclotomic twist is trivial, so this is exactly the classical Kummer/Brauer computation
`H²(G_κ, μ_p) = Br(κ)[p] ≅ ℤ/p`.

This is the form of the input that is *true* for every `p`-adic field (see the module docstring):
outside the regime `μ_p ⊆ κ` the trivial-coefficient group differs from the Brauer group by the
cyclotomic twist and in fact vanishes. -/
def LocalBrauerGroupInput (p : ℕ) (κ κ' : Type u) [Field κ] [Field κ'] [Algebra κ κ']
    [IsSepClosure κ κ'] : Prop :=
  ∀ ζ : κ, IsPrimitiveRoot ζ p → LocalH2Nonvanishing p κ κ'

/-- **The complementary vanishing**, as a named classical input: for a `p`-adic field `κ` without a
primitive `p`-th root of unity, the trivial-coefficient group `H²(G_κ, ℤ/p)` *vanishes*.

Classically this is local Tate duality, `H²(G_κ, ℤ/ℓ) ≅ Hom(μ_ℓ(κ), ℚ/ℤ)` (Milne, *Arithmetic
Duality Theorems*, Theorem I.2.1), together with the Kummer computation `H²(G_κ, μ_ℓ) = Br(κ)[ℓ]`,
or equivalently the Euler characteristic theorem (`loc. cit.` I.2.8–I.2.9).  It is the reason why
the sibling's trivial-coefficient input cannot be stated without the hypothesis `μ_p ⊆ κ`. -/
def LocalH2Vanishing (p : ℕ) (κ κ' : Type u) [Field κ] [Field κ'] [Algebra κ κ']
    [IsSepClosure κ κ'] : Prop :=
  (¬ ∃ ζ : κ, IsPrimitiveRoot ζ p) → ¬ LocalH2Nonvanishing p κ κ'

/-- The corrected input, unwound at a primitive `p`-th root of unity. -/
theorem localH2Nonvanishing_of_zeta {p : ℕ} {κ κ' : Type u} [Field κ] [Field κ']
    [Algebra κ κ'] [IsSepClosure κ κ'] (h : LocalBrauerGroupInput p κ κ') {ζ : κ}
    (hζ : IsPrimitiveRoot ζ p) : LocalH2Nonvanishing p κ κ' :=
  h ζ hζ

/-- **The sibling's input forces `μ_p ⊆ κ`.**  Given the two classical inputs — the Kummer/Brauer
computation and the Tate-duality vanishing — the trivial-coefficient non-vanishing of
`H²(G_κ, ℤ/p)` is *equivalent* to `κ` containing a primitive `p`-th root of unity. -/
theorem localH2Nonvanishing_iff_exists_primitiveRoot {p : ℕ} {κ κ' : Type u} [Field κ] [Field κ']
    [Algebra κ κ'] [IsSepClosure κ κ'] (hbr : LocalBrauerGroupInput p κ κ')
    (hvan : LocalH2Vanishing p κ κ') :
    LocalH2Nonvanishing p κ κ' ↔ ∃ ζ : κ, IsPrimitiveRoot ζ p := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · by_contra hc
    exact hvan hc h
  · obtain ⟨ζ, hζ⟩ := h
    exact localH2Nonvanishing_of_zeta hbr hζ

/-- In the regime `μ_p ⊆ κ` (where the cyclotomic twist is trivial) the corrected input *is* the
sibling's trivial-coefficient statement: there is nothing to prove beyond unwinding. -/
theorem localBrauerGroupInput_iff_of_zeta {p : ℕ} {κ κ' : Type u} [Field κ] [Field κ']
    [Algebra κ κ'] [IsSepClosure κ κ'] (hζ : ∃ ζ : κ, IsPrimitiveRoot ζ p) :
    LocalBrauerGroupInput p κ κ' ↔ LocalH2Nonvanishing p κ κ' :=
  ⟨fun h => h _ hζ.choose_spec, fun h _ _ => h⟩

section Two

variable {κ : Type u} [Field κ]

/-- A field of characteristic `≠ 2` contains a primitive second root of unity. -/
theorem isPrimitiveRoot_neg_one_two (h : (2 : κ) ≠ 0) : IsPrimitiveRoot (-1 : κ) 2 := by
  refine ⟨by norm_num, fun m hm => ?_⟩
  rcases Nat.even_or_odd m with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · exact ⟨k, by ring⟩
  · exfalso
    have h2 : (2 : κ) = 0 := by
      have hodd : ((-1 : κ) ^ (2 * k + 1)) = -1 := by
        rw [pow_succ, pow_mul, neg_one_sq, one_pow, one_mul]
      rw [hodd] at hm
      have : (2 : κ) = 1 - (-1 : κ) := by ring
      rw [this, hm]; ring
    exact h h2

end Two

/-- **`p = 2` needs no hypothesis.**  Every field of characteristic `≠ 2` contains a primitive
second root of unity, so the corrected input applies to `p = 2` for *every* `p`-adic `κ`
(unconditionally in `κ`): the trivial-coefficient statement `H²(G_κ, ℤ/2) ≠ 0` is true there, as
in the classical theory. -/
theorem localH2Nonvanishing_two {κ κ' : Type u} [Field κ] [Field κ'] [Algebra κ κ']
    [IsSepClosure κ κ'] (h : LocalBrauerGroupInput 2 κ κ') (h2 : (2 : κ) ≠ 0) :
    LocalH2Nonvanishing 2 κ κ' :=
  localH2Nonvanishing_of_zeta h (isPrimitiveRoot_neg_one_two h2)

/-- **The sibling's `NK.BrauerHasse.LocalH2Input`, from the corrected input.**  Given the
coefficient-corrected (Kummer/Brauer) input and a primitive `p`-th root of unity in `κ`, the
sibling's trivial-coefficient `LocalH2Input` follows — because in that regime the cyclotomic twist
is trivial and the two statements coincide.  This is the usable bridge for
`Submission/Work/BrauerHasse/`: it needs the transport structure they already isolate and the
hypothesis `ζ_p ∈ κ`. -/
theorem localH2Input_of_zetaMem {p : ℕ} {K K' κ κ' : Type u} [Field K] [Field K']
    [Algebra K K'] [IsSepClosure K K'] [Field κ] [Field κ'] [Algebra κ κ']
    [IsSepClosure κ κ'] (htransport : ColimitTransport p K K' κ κ')
    (hbr : LocalBrauerGroupInput p κ κ') {ζ : κ} (hζ : IsPrimitiveRoot ζ p) :
    NK.BrauerHasse.LocalH2Input p K K' κ κ' :=
  localH2Input_of_transport htransport (localH2Nonvanishing_of_zeta hbr hζ)

section TwistTrivial

variable {p : ℕ} [NeZero p] {κ L : Type u} [Field κ] [Field L] [Algebra κ L]

/-- **The cyclotomic twist is trivial when `ζ_p ∈ κ`.**  If `κ` contains a primitive `p`-th root of
unity, then *every* `p`-th root of unity in any `κ`-algebra `L` is fixed by every
`κ`-algebra automorphism of `L`.  Equivalently: the `Gal(L/κ)`-modules `μ_p(L)` and (`p`-th roots
of unity of `κ` via `algebraMap`) coincide, so that the cyclotomic twist reduces to the trivial
module.

This is the mathematical content of the equivalence recorded in
`NK.LocalCFT.LocalBrauerGroupInput`: the Kummer/Brauer computation `H²(G_κ, μ_p) ≅ ℤ/p` and the
trivial-coefficient statement `H²(G_κ, ℤ/p) ≅ ℤ/p` are about the *same* module exactly here. -/
theorem algEquiv_apply_eq_of_pow_eq_one (hζ : ∃ ζ : κ, IsPrimitiveRoot ζ p)
    (σ : L ≃ₐ[κ] L) {x : L} (hx : x ^ p = 1) : σ x = x := by
  obtain ⟨ζ, hζ⟩ := hζ
  obtain ⟨i, -, rfl⟩ :=
    (IsPrimitiveRoot.map_of_injective (f := algebraMap κ L) hζ (algebraMap κ L).injective).eq_pow_of_pow_eq_one hx
  rw [map_pow, AlgEquiv.commutes]

end TwistTrivial

end NK.LocalCFT
