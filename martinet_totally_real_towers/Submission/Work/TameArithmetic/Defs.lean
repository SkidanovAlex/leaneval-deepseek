import Mathlib
import Submission.NumberField.MaximalProPOutsideS

/-!
# `Work.TameArithmetic` -- the arithmetic of the tame Golod--Shafarevich route

**Namespace** `Work.TameArithmetic`.

This chapter is the *arithmetic* half of the on-path proof of Martinet's theorem in this
workspace: the tame (restricted-ramification) Golod--Shafarevich input
`Submission.NumberField.TameGolodShafarevichInput`, which is the single `sorry` of
`Submission.lean`.

## The route (the source paper's route, `Submission/PLAN.md` §2 Route A)

Fix five primes `≡ 1 (mod 8)` (`primesS = {17, 41, 73, 89, 97}`) and let `K` be the maximal pro-`2`
extension of `ℚ` unramified outside `primesS` and at the infinite places (the *maximal tame
pro-`2` extension*; it exists with no class field theory, by
`Submission.NumberField.exists_maximal_proP_field_unramifiedOutside_inf`).  Write
`Γ = Gal(K/ℚ)`.  Then:

* (`d ≥ 5`) `Γ` admits a surjection onto `(ℤ/2)^5`, coming from the multiquadratic field
  `ℚ(√17, √41, √73, √89, √97)`
  (`Commons.NumberTheory.NumberField.exists_multiquadratic_totallyReal_unramifiedOutside`);
* (`d ≤ 5`, elementary) every quadratic extension of `ℚ` unramified outside `S` and at `∞` is
  `ℚ(√d)` with `d > 0` squarefree, `d ≡ 1 (mod 4)`, `d ∣ ∏ S` -- hence there are exactly
  `2^5 - 1` of them and `dim_{𝔽₂} H¹ = 5`; this is `QuadraticTame.lean` in this chapter;
* (`r ≤ 6`) the **Shafarevich--Koch relation bound**: `Γ` has a pro-`2` presentation with `5`
  generators and at most `6` relators (`r - d ≤ dim_{𝔽₂} V_S/ℚ^{×2} = 1`, the `2`-rank
  computation `V_S = {±1}·(ℚ^×)²` being elementary -- `VS.lean` in this chapter).  This is the one
  non-elementary input -- the tame case of `Sha_S ↪ C_S` (Shafarevich 1963; Koch, *Galois theory
  of `p`-extensions*, Ch. 11 Thm 11.3; NSW Ch. X §7 Cor. 10.7.7);
* the counting `4 · 6 = 24 ≤ 25 = 5²`, so that the finite `p`-group Golod--Shafarevich inequality
  (`Submission.GroupTheory.finitePGroupGolodShafarevich_of_commons`, Chapter B, proved in this
  workspace) applies: the group is infinite and therefore has finite quotients of unbounded order.

## The interface

* `primesS` -- the five primes;
* `TameUnivClause K`, `TameSubClause K` -- the two defining properties of the maximal tame pro-`2`
  extension `K` (its universal property, and the properties of the finite Galois extensions of `ℚ`
  embedding into it), stated for an *abstract* field type `K` (no `IntermediateField`-valued
  clause, which would suffer from the `IntermediateField.algebra'` /
  `DivisionRing.toRatAlgebra` instance ambiguity over `ℚ`);
* `IsMaximalTamePro2 K` -- `K` is algebraic over `ℚ`, Galois over `ℚ` (these are part of the
  interface) and satisfies the two clauses;
* `TamePro2Presentation K` -- a pro-`2` presentation of `Γ = Gal(K/ℚ)` with five generators and at
  most six relators, together with the abstract group `presentedGroup P` it presents;
* `IsProTwoModel K G` -- every finite quotient of `G` is the Galois group of a finite Galois
  extension of `ℚ` embedding into `K`;
* `TameRelationBound` -- the Shafarevich--Koch relation bound (a presentation as above exists);
* `TameArithmeticInput` -- the full arithmetic input: a maximal tame pro-`2` extension `K`, a
  presentation `P` of `Γ` with five generators and at most six relators, and
  `IsProTwoModel K (presentedGroup P)`.

The assembly `TameArithmeticInput → TameGolodShafarevichInput` is in `Assembly.lean`.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

open scoped Classical
open scoped NumberField
open NumberField

namespace Work.TameArithmetic

/-! ## The choice of `S`: five primes `≡ 1 (mod 8)` -/

/-- **The set `S = {17, 41, 73, 89, 97}`** of five primes `≡ 1 (mod 8)`.  The multiquadratic
certificate needs `q ≡ 1 (mod 8)` (so that `ℚ(√q)` is tame with different supported at `q`), and
the `2`-rank computation of `V_S` needs `q ≡ 1 (mod 4)` (so that `-1` is a local square at `q`). -/
def primesS : Finset ℕ := {17, 41, 73, 89, 97}

theorem primesS_prime : ∀ q ∈ primesS, Nat.Prime q := by decide

theorem primesS_odd : ∀ q ∈ primesS, q ≠ 2 := by decide

theorem primesS_card : primesS.card = 5 := by decide

theorem primesS_mod_eight : ∀ q ∈ primesS, q % 8 = 1 := by decide

theorem primesS_mod_four : ∀ q ∈ primesS, q % 4 = 1 := by decide

theorem primesS_prod_pos : 0 < ∏ q ∈ primesS, q :=
  Finset.prod_pos fun q hq => (primesS_prime q hq).pos

/-- The relation count is `r ≤ 6` and the generator count is `d = 5`, so that `4r ≤ d²`. -/
theorem four_mul_le_sq_of_rel_card_le_six {r : ℕ} (h : r ≤ 6) :
    4 * r ≤ 5 * 5 := by omega

/-! ## The maximal tame pro-`2` extension of `ℚ` -/

/-- **The universal property of the maximal pro-`2` extension `K` of `ℚ` unramified outside
`S = primesS` and at the infinite places**: every finite Galois pro-`2` extension `M/ℚ` whose
relative different is supported over `S` and which is unramified at the infinite places embeds
into `K`. -/
def TameUnivClause (K : Type) [Field K] [Algebra ℚ K] : Prop :=
  ∀ (M : Type) [Field M] [NumberField M] [Algebra ℚ M] [IsGalois ℚ M],
    IsPGroup 2 (M ≃ₐ[ℚ] M) →
    (∀ P : Ideal (𝓞 M), P.IsPrime → P ≠ ⊥ → P ∣ differentIdeal (𝓞 ℚ) (𝓞 M) →
      ∃ q ∈ primesS, P.LiesOver (Ideal.span ({(q : ℤ)} : Set ℤ))) →
    IsUnramifiedAtInfinitePlaces ℚ M → ∃ φ : M →ₐ[ℚ] K, True

/-- **The maximality of `K`**: every finite Galois extension `L/ℚ` that embeds into `K` is pro-`2`,
has `S`-supported relative different and is unramified at the infinite places (hence totally real,
being pro-`2` at `∞`). -/
def TameSubClause (K : Type) [Field K] [Algebra ℚ K] : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] [Algebra ℚ L] [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (φ : L →ₐ[ℚ] K), Function.Injective φ →
    IsPGroup 2 (L ≃ₐ[ℚ] L) ∧
      (∀ P : Ideal (𝓞 L), P.IsPrime → P ≠ ⊥ → P ∣ differentIdeal (𝓞 ℚ) (𝓞 L) →
        ∃ q ∈ primesS, P.LiesOver (Ideal.span ({(q : ℤ)} : Set ℤ))) ∧
    IsUnramifiedAtInfinitePlaces ℚ L

/-- **`K` is a maximal tame pro-`2` extension of `ℚ` (for `S = primesS`)**: `K` is algebraic and
Galois over `ℚ`, every `S`-tame pro-`2` extension of `ℚ` embeds into it, and every finite Galois
extension of `ℚ` embedding into it is `S`-tame and pro-`2`.

The algebraicity is part of the interface because it is exactly what makes
`Γ = Gal(K/ℚ)` residually finite (the finite Galois subextensions separate the points of `Γ`, and
a dense finitely generated subgroup of a residually finite group is residually finite); it holds
for the extension constructed by the sup-construction inside `AlgebraicClosure ℚ`. -/
def IsMaximalTamePro2 (K : Type) [Field K] [Algebra ℚ K] [IsGalois ℚ K] : Prop :=
  Algebra.IsAlgebraic ℚ K ∧ TameUnivClause K ∧ TameSubClause K

/-! ## A pro-`2` presentation of `Γ = Gal(K/ℚ)` -/

/-- **A pro-`2` presentation of `Γ = Gal(K/ℚ)` with five generators and at most six relators.**

The data are `gen : Fin 5 → Γ` (the generators) and `rel : Finset (FreeGroup (Fin 5))` (the
relators), subject to

* `ker_eq` -- the kernel of the presentation map `FreeGroup (Fin 5) →* Γ`, `x_i ↦ gen i`, is
  exactly the normal closure of `rel`.  Hence the abstract group
  `presentedGroup P = FreeGroup (Fin 5) ⧸ ⟪rel⟫` embeds into `Γ`, with image the subgroup
  generated by the `gen i`;
* `dense` -- the `gen i` generate `Γ` topologically (equivalently: generate every finite quotient
  of `Γ`).  Together with `ker_eq` this says that `presentedGroup P` is a *dense* finitely
  generated subgroup of the profinite group `Γ`.

The arithmetic content is the *existence* of such data (`TameRelationBound`): five generators
because `d(Γ) = |S| = 5`, and at most six relators because
`r - d ≤ dim_{𝔽₂} V_S/ℚ^{×2} = 1`. -/
structure TamePro2Presentation (K : Type) [Field K] [Algebra ℚ K] [IsGalois ℚ K] where
  rel : Finset (FreeGroup (Fin 5))
  gen : Fin 5 → (K ≃ₐ[ℚ] K)
  rel_card : rel.card ≤ 6
  ker_eq : MonoidHom.ker (FreeGroup.lift gen) =
    Subgroup.normalClosure (rel : Set (FreeGroup (Fin 5)))
  dense : (Subgroup.closure (Set.range gen)).topologicalClosure = ⊤

/-- **The abstract group presented by a pro-`2` presentation `P`**: five generators modulo the
normal closure of the relators.  It is countable and finitely presented, and by `P.ker_eq` it maps
injectively into `Γ = Gal(K/ℚ)`, with dense image. -/
abbrev presentedGroup {K : Type} [Field K] [Algebra ℚ K] [IsGalois ℚ K]
    (P : TamePro2Presentation K) : Type :=
  FreeGroup (Fin 5) ⧸ Subgroup.normalClosure (P.rel : Set (FreeGroup (Fin 5)))

/-- **`G` models the maximal tame pro-`2` extension `K`**: every finite quotient of `G` is the
Galois group of a finite Galois extension of `ℚ` which embeds into `K` -- equivalently, since `K`
is maximal, of a finite Galois extension of `ℚ` with `S`-supported different which is unramified
at the infinite places.

This is *not* automatic from a pro-`2` presentation: for the pro-`2` group `ℤ_2` the presentation
`⟨x | ⟩` has `ker (FreeGroup.lift g) = ⊥`, so the presented group is `ℤ`, which embeds densely in
`ℤ_2`; but `ℤ` has the finite quotient `ℤ/3`.  The condition says that the presented abstract
group has the same finite quotients as `Γ`; it is the "profinite completion" half of the input,
complementary to the relation count. -/
def IsProTwoModel (K : Type) [Field K] [Algebra ℚ K] [IsGalois ℚ K] (G : Type) [Group G] : Prop :=
  ∀ (N : Subgroup G) [N.Normal], Finite (G ⧸ N) →
    ∃ (L : Type) (_ : Field L) (_ : Algebra ℚ L) (_ : FiniteDimensional ℚ L) (_ : IsGalois ℚ L)
      (φ : L →ₐ[ℚ] K), Function.Injective φ ∧
      Nonempty ((L ≃ₐ[ℚ] L) ≃* (G ⧸ N))

/-! ## The named arithmetic inputs -/

/-- **The Shafarevich--Koch relation bound** (the one non-elementary input of the tame route):
there is a maximal tame pro-`2` extension `Γ` of `ℚ` (for `S = primesS`) admitting a pro-`2`
presentation with **five** generators and **at most six** relators.

The generator number is `d = |S| = 5` (multiquadratic lower bound plus the elementary quadratic
classification of `QuadraticTame.lean`), and the relator bound is
`r - d ≤ dim_{𝔽₂} V_S/ℚ^{×2} = 1` (`VS.lean`), i.e. `r ≤ 6`; numerically `4r ≤ 24 ≤ 25 = d²`.

Classically this is the tame case of `Sha_S ↪ C_S = (V_S/ℚ^{×2})^∨` together with the local terms
`Σ_{v ∈ S} dim H²(G_v, 𝔽₂) = |S|` (Shafarevich 1963; Koch, *Galois theory of `p`-extensions*,
Ch. 11 Thm 11.3; Neukirch--Schmidt--Wingberg Ch. X §7 Cor. 10.7.7). -/
def TameRelationBound : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Algebra ℚ K) (_ : IsGalois ℚ K),
    IsMaximalTamePro2 K ∧ Nonempty (TamePro2Presentation K)

/-- **The arithmetic input of the tame Golod--Shafarevich route**: a maximal tame pro-`2` extension
`K` of `ℚ` (for `S = primesS`), a pro-`2` presentation `P` of `Γ = Gal(K/ℚ)` with five generators
and at most six relators, and the abstract-model condition `IsProTwoModel K (presentedGroup P)`.

`Assembly.tameGolodShafarevichInput_of_arithmeticInput` derives
`Submission.NumberField.TameGolodShafarevichInput` from this input, using the elementary
arithmetic of `QuadraticTame.lean` (the multiquadratic certificate, giving the minimality of the
five-element generating set) and Chapter B
(`Submission.GroupTheory.finitePGroupGolodShafarevich_of_commons`, proved in this workspace). -/
def TameArithmeticInput : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Algebra ℚ K) (_ : IsGalois ℚ K),
    IsMaximalTamePro2 K ∧ ∃ P : TamePro2Presentation K, IsProTwoModel K (presentedGroup P)

/-- The relation bound is a consequence of the full arithmetic input. -/
theorem tameRelationBound_of_arithmeticInput (h : TameArithmeticInput) : TameRelationBound := by
  obtain ⟨K, iK, iAK, iGK, hmax, P, _⟩ := h
  exact ⟨K, iK, iAK, iGK, hmax, ⟨P⟩⟩

end Work.TameArithmetic
