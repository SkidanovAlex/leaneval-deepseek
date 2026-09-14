import Mathlib
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.Data.Nat.Factors
import Submission.Commons.NumberTheory.NumberField.adjoinRoot_numberField
import Submission.Vdw.GaloisAction
import Submission.Vdw.DifferentValuation
import Submission.Vdw.SplittingField
import Submission.Vdw.InertiaSwap

open Function Polynomial
open scoped BigOperators NumberField

set_option autoImplicit false

/-!
# Phase 2, Case I: the quotient field `K_f` and its discriminant

Bhargava, *Galois groups of random integer polynomials*, Annals of Math
201(2) (2025), proof of Theorem 1 (van der Waerden's conjecture).  The
remaining (irreducible) part of `E n H` is split into three cases by the
data of `K_f = ℚ[x]/(f)`:

* `C_f` — the product of the primes ramified in `K_f`;
* `D_f` — the absolute field discriminant `|Disc(K_f)|`.

**Case I** treats irreducible `f` with (primitive) Galois group `G_f < Sₙ`,
`C_f ≤ H^(1+δ)` and `D_f > H^(2+2δ)`.  Its starting point is that for such
`f` the field discriminant is *squarefull*, and that the polynomials with a
given discriminant are few modulo `C_f`; summing over squarefull
`D_f > H^(2+2δ)` yields the Case-I bound `O(H^(n-1))`.

This module lays the formal foundation for Case I: it constructs `K_f` as a
number field for a monic irreducible integer polynomial `f`, defines the
discriminant data, and records the precise open statements (marked `OPEN`)
that Case I needs.  Progress so far:

* `RamifiedAt` and the theorem `ramified_iff_prime_dvd_fieldDisc`:
  a rational prime `p` is ramified in `K_f` iff `p` divides the absolute
  field discriminant `D_f` — this is now **proved**, by way of Mathlib's
  `NumberField.not_dvd_discr_iff_isUnramifiedIn`
  (`Mathlib.NumberTheory.NumberField.Discriminant.Different`).
* The group-theoretic half of Case I is proved in `GaloisAction.lean`
  (natural action on the roots, Jordan: primitive proper ⇒ no transposition,
  `|Gal| ≤ n!`).
* The valuation half is **PROVED** in `DifferentValuation.lean` (the local
  structure of `v_p(D_f) = 1`), and step (c) — the tame-inertia
  transposition — is **PROVED** in `Submission/Vdw/InertiaSwap.lean`
  (`exists_isSwap_of_ramifiedPrimeStructure`, instantiated here as
  `fieldDisc_val_one_has_isSwap`).  Consequently
  `fieldDisc_squarefull_of_no_transposition` (Case-I squarefullness) is now a
  theorem, no longer open.
-/

namespace Submission.Vdw

noncomputable section

/-- `φℚ : ℤ → ℚ`, the standard embedding. -/
noncomputable def φℚ : ℤ →+* ℚ := algebraMap ℤ ℚ

/-- The quotient algebra `K_f := ℚ[x]/(f)`.  An `abbrev` (rather than a `def`)
so that the field / number-field / module instances of `AdjoinRoot` are
available on `Kpoly f` directly (see `kpolyFieldNote` below). -/
abbrev Kpoly (f : ℤ[X]) : Type :=
  AdjoinRoot (f.map φℚ)

/-- With `Kpoly` an abbreviation for `AdjoinRoot (f.map φℚ)`, Mathlib's own
instances apply: for `[Fact (Irreducible (f.map φℚ))]` the type `Kpoly f` is
a field (`Mathlib`), a `NumberField` (`NumberField.instNumberFieldAdjoinRoot`),
is separable over `ℚ` (`Algebra.IsAlgebraic.isSeparable_of_perfectField`), and
is finite-dimensional over `ℚ` (`NumberField.to_finiteDimensional`).  This
replaces the previous hand-rolled `kpolyField`/`kpolyNumberField` instances
(the commons lemma `adjoinRoot_numberField` is no longer needed here). -/
theorem kpolyFieldNote (f : ℤ[X]) [Fact (Irreducible (f.map φℚ))] :
    Module.Finite ℚ (Kpoly f) ∧ Algebra.IsSeparable ℚ (Kpoly f) := ⟨inferInstance, inferInstance⟩

/-- **Gauss's lemma:** a monic integer polynomial is irreducible over `ℤ`
iff it is irreducible over `ℚ`. -/
theorem monic_irreducible_int_iff_rat (f : ℤ[X]) (hf : f.Monic) :
    Irreducible f ↔ Irreducible (f.map φℚ) := by
  dsimp [φℚ]
  exact Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map hf

section Discriminant

/-- The absolute discriminant of `K_f`, as a natural number. -/
noncomputable def fieldDisc (f : ℤ[X]) [Fact (Irreducible (f.map φℚ))] : ℕ :=
  (NumberField.discr (Kpoly f)).natAbs

/-- The discriminant of the polynomial `f` (an integer). -/
noncomputable def polyDisc (f : ℤ[X]) : ℤ :=
  Polynomial.discr f

/-- An integer `N` is `k`-powerful if `pᵏ | N` for every prime divisor `p`
of `N`. -/
def Powerful (k N : ℕ) : Prop :=
  ∀ p : ℕ, Nat.Prime p → p ∣ N → p ^ k ∣ N

/-- Squarefull (2-powerful). -/
def Squarefull (N : ℕ) : Prop :=
  Powerful 2 N

/-- The radical of a natural number (product of its distinct prime factors),
`1` for `1` (and `0` for `0`). -/
noncomputable def radical (N : ℕ) : ℕ :=
  ∏ p ∈ Nat.primeFactors N, p

/-- The product `C_f` of the primes ramified in `K_f`; by
`ramified_iff_prime_dvd_fieldDisc` below this is the radical of `D_f`. -/
noncomputable def ramifiedProduct (f : ℤ[X]) [Fact (Irreducible (f.map φℚ))] : ℕ :=
  radical (fieldDisc f)

/-- The rational prime `p` is ramified in the number field `K_f` (Mathlib's
`Algebra.IsUnramifiedIn` at the principal ideal generated by `p`). -/
def RamifiedAt (f : ℤ[X]) [Fact (Irreducible (f.map φℚ))] (p : ℕ) : Prop :=
  ¬ Algebra.IsUnramifiedIn (𝓞 (Kpoly f)) (Ideal.span {(p : ℤ)})

/-- Divisibility reformulation: for a prime `p`, `p` ramifies in `K_f` iff
`p` divides the integer discriminant `discr (Kpoly f)`.  (Mathlib:
`NumberField.not_dvd_discr_iff_isUnramifiedIn`.) -/
theorem ramified_iff_prime_dvd_discr (f : ℤ[X]) [Fact (Irreducible (f.map φℚ))]
    (p : ℕ) (hp : Nat.Prime p) :
    RamifiedAt f p ↔ (p : ℤ) ∣ NumberField.discr (Kpoly f) := by
  classical
  unfold RamifiedAt
  have hmain : ¬ (p : ℤ) ∣ NumberField.discr (Kpoly f) ↔
      Algebra.IsUnramifiedIn (𝓞 (Kpoly f)) (Ideal.span {(p : ℤ)}) :=
    NumberField.not_dvd_discr_iff_isUnramifiedIn (K := Kpoly f) (𝒪 := 𝓞 (Kpoly f))
      ((Nat.prime_iff_prime_int).1 hp)
  constructor
  · intro hnu
    by_contra hdvd
    exact hnu (hmain.mp hdvd)
  · intro hdvd hnu
    exact (hmain.mpr hnu) hdvd

/-- For a prime `p`: `p` divides the integer discriminant of `K_f` iff `p`
divides the absolute discriminant `D_f = |discr (Kpoly f)|`. -/
theorem prime_dvd_discr_iff_dvd_fieldDisc (f : ℤ[X]) [Fact (Irreducible (f.map φℚ))]
    (p : ℕ) (_hp : Nat.Prime p) :
    (p : ℤ) ∣ NumberField.discr (Kpoly f) ↔ p ∣ fieldDisc f := by
  unfold fieldDisc
  constructor
  · intro h
    simpa using (Int.natAbs_dvd_natAbs.mpr h)
  · intro h
    simpa using (Int.natAbs_dvd_natAbs.mp h)

/-- **A prime ramifies in `K_f` iff it divides the absolute field
discriminant `D_f`** — the identification that makes `ramifiedProduct f`
(= the radical of `D_f`) literally "the product of the ramified primes". -/
theorem ramified_iff_prime_dvd_fieldDisc (f : ℤ[X]) [Fact (Irreducible (f.map φℚ))]
    (p : ℕ) (hp : Nat.Prime p) :
    RamifiedAt f p ↔ p ∣ fieldDisc f := by
  exact (ramified_iff_prime_dvd_discr f p hp).trans (prime_dvd_discr_iff_dvd_fieldDisc f p hp)

end Discriminant



/-- **Local structure of a once-divisible discriminant.**  For a monic
irreducible integer polynomial `f` (`K_f = ℚ[x]/(f)`), if the absolute field
discriminant `D_f` has exact `p`-adic valuation one, then `p` has exactly one
ramified prime `P` in `K_f`, with ramification index `2` and inertia degree
`1`, and every other prime of `K_f` over `p` is unramified.  (Proved in
`Submission/Vdw/DifferentValuation.lean` via the different-ideal norm; this
is the valuation-half input to the classical transposition argument.) -/
theorem fieldDisc_val_one_local_structure (f : ℤ[X]) [Fact (Irreducible (f.map φℚ))]
    (p : ℕ) (hp : Nat.Prime p) (hv : padicValNat p (fieldDisc f) = 1) :
    ∃ P : Ideal (𝓞 (Kpoly f)),
      P.IsMaximal ∧ P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ)) ∧
      P.ramificationIdx ℤ = 2 ∧ P.inertiaDeg ℤ = 1 ∧
      ∀ Q : Ideal (𝓞 (Kpoly f)), Q.IsMaximal →
        Q.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ)) → Q ≠ P →
        Q.ramificationIdx ℤ = 1 := by
  classical
  unfold fieldDisc at hv
  have hv' : padicValNat p ((differentIdeal ℤ (𝓞 (Kpoly f))).absNorm) = 1 := by
    rw [← padicValNat_differentIdeal_discr (K := Kpoly f) p] at hv
    exact hv
  exact ramified_prime_of_padicValNat_eq_one (K := Kpoly f) p hp hv'


/-- **Step 1 of (c), at `K_f`**: if a prime `p` divides the absolute field
discriminant `D_f = |discr K_f|`, then `p` is ramified in the splitting
field `L := (f.map φℚ).SplittingField` (whose automorphism group is
`Gal(f)`).  Proved from the tower discriminant formula
(`NumberField.discr_dvd_discr`, instantiated in `SplittingField.lean`). -/
theorem ramified_splittingField_of_dvd_fieldDisc (f : ℤ[X]) [Fact (Irreducible (f.map φℚ))]
    (p : ℕ) (hp : Nat.Prime p) (hdiv : p ∣ fieldDisc f) :
    ¬ Algebra.IsUnramifiedIn (𝓞 ((f.map φℚ).SplittingField)) (Ideal.span ({(p : ℤ)} : Set ℤ)) := by
  classical
  have hramK : ¬ Algebra.IsUnramifiedIn (𝓞 (AdjoinRoot (f.map φℚ)))
      (Ideal.span ({(p : ℤ)} : Set ℤ)) := by
    simpa [RamifiedAt, Kpoly] using ((ramified_iff_prime_dvd_fieldDisc f p hp).mpr hdiv)
  exact ramified_in_splittingField_of_ramified (p := f.map φℚ) (q := p) hp hramK

/-- Mapping a monic integer polynomial to `ℚ` preserves its degree. -/
theorem monic_natDegree_map_rat (f : ℤ[X]) (hf : f.Monic) :
    (f.map φℚ).natDegree = f.natDegree := by
  dsimp [φℚ]
  exact hf.natDegree_map (algebraMap ℤ ℚ)

/-- The natural permutation representation of the Galois group of
`p = f.map φℚ` (a monic irreducible integer `f`) on `Fin (natDegree p)`,
with `p` separable by characteristic zero. -/
noncomputable def irrGalFinHom (f : ℤ[X]) [Fact (Irreducible (f.map φℚ))] :
    (f.map φℚ).Gal →* Equiv.Perm (Fin ((f.map φℚ).natDegree)) :=
  galFinHom (f.map φℚ) (separable_of_irreducible_rat Fact.out)


/-- **Transitivity of the natural action for irreducible `f`.**  For a monic
irreducible integer polynomial, the image of `Gal (f.map φℚ)` in `S_n` (the
`irrGalFinHom` representation, `n = natDegree (f.map φℚ)`) is a
pretransitive (transitive) permutation group on the roots.  This is the
hypothesis under which the primitive/imprimitive dichotomy of Bhargava's
Theorem-1 proof applies to irreducible polynomials, and it makes
`MulAction.IsPreprimitive` (which extends `IsPretransitive`) the right
formalization of "primitive Galois group". -/
theorem irrGalFinHom_pretransitive (f : ℤ[X]) [Fact (Irreducible (f.map φℚ))] :
    MulAction.IsPretransitive ((irrGalFinHom f).range) (Fin ((f.map φℚ).natDegree)) := by
  classical
  dsimp [irrGalFinHom]
  exact galFinHom_pretransitive (f.map φℚ) Fact.out (separable_of_irreducible_rat Fact.out)

/-!
# Remaining research targets of Case I

`fieldDisc_dvd_polyDisc` (Dedekind divisibility) is **PROVED** — see
`Submission/Vdw/DedekindIndex.lean` (`Submission.Vdw.fieldDisc_dvd_polyDisc`),
built on the commons bridges `discr_powerBasis_eq_discr`,
`discr_dvd_of_isIntegral_basis` and `discr_map`.

`fieldDisc_squarefull_of_no_transposition` (the Case-I squarefullness input,
`valindcon` for `k = 2`) is **PROVED** (2026-09): the valuation half in
`DifferentValuation.lean`, step (c) — tame inertia at a prime over the unique
`(2,1)`-prime of `K_f` acts on the roots as a transposition — in
`Submission/Vdw/InertiaSwap.lean` (Hilbert-theory orbit argument over the
embeddings: `hilbertCore`, `inertia_fixes_emb_of_unramified`,
`exists_isSwap_of_ramifiedPrimeStructure`), and the group-theoretic half in
`GaloisAction.no_isSwap_of_preprimitive_proper`.  Nothing below is used by
`theorem_1` yet (the Case-I counting itself remains to be built).
-/


/-- **Failure of squarefullness** is witnessed by a prime dividing `N`
exactly once. -/
theorem not_squarefull_iff {N : ℕ} :
    ¬ Squarefull N ↔ ∃ p : ℕ, Nat.Prime p ∧ p ∣ N ∧ ¬ p ^ 2 ∣ N := by
  unfold Squarefull Powerful
  constructor
  · intro h
    by_contra hnone
    apply h
    intro p hp hpd
    by_contra hnot
    exact hnone ⟨p, hp, hpd, hnot⟩
  · rintro ⟨p, hp, hpd, hnot⟩ hsq
    exact hnot (hsq p hp hpd)

/-- **Bridge from step (c) to squarefullness.**  Combined with
`fieldDisc_val_one_has_isSwap` (step (c) below), this is the
contrapositive closing `fieldDisc_squarefull_of_no_transposition`: assuming
no transposition, a prime dividing `D_f` to the first power would give
`padicValNat p (fieldDisc f) = 1` (via
`padicValNat_eq_one_of_dvd_not_sq_dvd`), hence (by (c)) a transposition. -/
theorem squarefull_of_no_isSwap_of_val_one (f : ℤ[X]) [Fact (Irreducible (f.map φℚ))]
    (hnoswap : ∀ σ : (f.map φℚ).Gal, ¬ ((irrGalFinHom f) σ).IsSwap)
    (hval : ∀ p : ℕ, Nat.Prime p → padicValNat p (fieldDisc f) = 1 → False) :
    Squarefull (fieldDisc f) := by
  by_contra hns
  rcases (not_squarefull_iff.mp hns) with ⟨p, hp, hpd, hnot⟩
  have hN : fieldDisc f ≠ 0 := by
    unfold fieldDisc
    exact Int.natAbs_ne_zero.mpr (NumberField.discr_ne_zero (Kpoly f))
  exact hval p hp (padicValNat_eq_one_of_dvd_not_sq_dvd hp hN hpd hnot)

section OpenTargets

/-! **Dedekind divisibility (PROVED — see `Submission/Vdw/DedekindIndex.lean`,
`Submission.Vdw.fieldDisc_dvd_polyDisc`):** the field discriminant `D_f =
|discr K_f|` divides the polynomial discriminant of a monic `f`.  The proof
lives in `DedekindIndex.lean` to avoid an import cycle: it instantiates the
commons bridges (`discr_powerBasis_eq_discr`,
`discr_dvd_of_isIntegral_basis`, `discr_map`) on the power basis of
`K_f = ℚ[x]/(f)`. -/


/-- **Step (c): a once-divisible discriminant forces a transposition.**  If a
rational prime `p` divides the absolute field discriminant `D_f` exactly once
(`padicValNat p (fieldDisc f) = 1`), then the Galois group of `f` — in its
natural action on the `n` roots, via `irrGalFinHom f` — contains a
transposition.

**How this closes the squarefullness OPEN.**  With `fieldDisc_val_one_local_
structure` ((a)+(b)) in hand, this theorem implies `fieldDisc_squarefull_of_
no_transposition` by the contrapositive: if `D_f` were not squarefull there is
a prime `p | D_f` with `¬ p² | D_f`, whence `padicValNat p (fieldDisc f) = 1`
(valuation API), this theorem gives a transposition, contradicting the
no-swap hypothesis.

**Proof plan for (c)** (classical — the cycle-type theorem of inertia, as
used in the paper's proof of Proposition `valindcon`; one remaining research
thread):
*Let `q := f.map φℚ`, `L := q.SplittingField` (a `NumberField`, normal over
`ℚ`, with `q.Gal = Gal(L/ℚ)` as automorphism group), and let `G` act on the
`n` roots (elements of `𝒪_L`) by the `galRootPerm` action.  By
`fieldDisc_val_one_local_structure`, `p · 𝒪_{K_f} = P² · ∏_{j} Q_j` with
`P` the unique ramified prime (`ramificationIdx = 2`, `inertiaDeg = 1`) and
all `Q_j` unramified.  Pick a prime `𝔓` of `𝒪_L` over `P`.*

1. *(ramified lift, DONE)* `p` is ramified in `L` (`ramified_splittingField_
   of_dvd_fieldDisc`, from the tower discriminant formula), and in fact any
   prime `𝔓` over `P` is ramified over `ℚ` (`ramificationIdx 𝔓 ℤ ≥
   ramificationIdx P ℤ = 2`), so the inertia group `I(𝔓)` (elements of `G`
   acting trivially on the residue field of `L` at `𝔓`) is nontrivial.
2. *(fiber/embedding correspondence)* The `n` roots are the values `σ(α)`
   of the embeddings `σ : K_f ↪ L` at a generator `α`.  For `Q | p` a prime
   of `K_f`, the embeddings with `σ⁻¹(𝔓) = Q` number `e_Q · f_Q`, and this
   correspondence identifies the `I(𝔓)`-orbits of roots with the primes of
   `K_f` over `p`.
3. *(orbit sizes = ramification indices — the classical cycle-type theorem)*
   In the tower `L ⊇ σ(K_f) ⊇ ℚ`, the restriction map sends the inertia
   group `I(𝔓|p)` onto the inertia of the intermediate prime `σ(Q)`, with
   kernel `I(𝔓 | σ(Q))`; hence the orbit of a root over `Q` under `I(𝔓)`
   has size `|I(𝔓|p)| / |I(𝔓|σ(Q))| = |I(σ(Q)|p)| = e_Q` (equality of
   ramification indices; the tame case needs no cyclicity — only the order
   of the inertia group of the intermediate, which for the unramified `Q_j`
   is `1` and for `P` equals `e_P = 2` since `v_P(different) = e_P − 1`
   forces tame).  So `I(𝔓)` acts on the `n` roots as one 2-cycle (the two
   roots over `P`) and fixes every other root: **no residue-distinctness
   hypothesis is needed** (roots over distinct `Q_j` may share residues when
   `p | index`; the orbit statement handles that automatically).
4. *(transposition)* Any `1 ≠ σ ∈ I(𝔓)` fixes all roots outside the single
   2-orbit and must swap the two roots in it (a permutation fixing every
   point is trivial), hence `σ` is a transposition on the roots, i.e.
   `((irrGalFinHom f) σ).IsSwap` (via `rootFinEquiv`).  The pure
   permutation-content of this step is `isSwap_of_fixes_all_but_two` in
   `GaloisAction.lean`.

The formal development of steps 2–3 needs a new embedding/prime API:
embeddings `K_f ↪ L` (= roots), their contraction `σ⁻¹(𝔓)`, primes of
`𝒪_L` over primes of `K_f` (towers), and the restriction isomorphism of
inertia groups (`Mathlib.NumberTheory.RamificationInertia.Galois` +
`RamificationInertia` tower lemmas).  **OPEN** — not yet proved (current
research thread; steps 1 and the pure-permutation step 4 are proved). -/
theorem fieldDisc_val_one_has_isSwap (f : ℤ[X]) [Fact (Irreducible (f.map φℚ))]
    (p : ℕ) (hp : Nat.Prime p) (hv : padicValNat p (fieldDisc f) = 1) :
    ∃ σ : (f.map φℚ).Gal, ((irrGalFinHom f) σ).IsSwap := by
  classical
  -- the local structure of v_p(D_f) = 1 (DifferentValuation) is exactly the
  -- RamifiedPrimeStructure hypothesis of the generic theorem (InertiaSwap)
  have hR : RamifiedPrimeStructure (f.map φℚ) p := by
    exact fieldDisc_val_one_local_structure f p hp hv
  obtain ⟨σ, hswap⟩ := exists_isSwap_of_ramifiedPrimeStructure (p := f.map φℚ) p hp hR
  refine ⟨σ, ?_⟩
  simpa [irrGalFinHom] using hswap

/-- **Case-I squarefullness (valindcon, `k = 2`).**  Let `f` be a monic
irreducible integer polynomial.  If no element of the Galois group acts on
the roots as a transposition — equivalently, if the Galois group (in its
natural action on the roots) is primitive and a proper subgroup of `Sₙ`,
by Jordan (`GaloisAction.no_isSwap_of_preprimitive_proper`) — then
`D_f = |Disc(K_f)|` is squarefull.

**Group-theoretic half: PROVED** (Jordan, in `GaloisAction.lean`).
**Valuation half: (a)+(b) PROVED** — `Submission/Vdw/DifferentValuation.lean`
  (`Submission.Vdw.ramified_prime_of_padicValNat_eq_one`, instantiated here as
  `fieldDisc_val_one_local_structure`): if `v_p(D_f) = 1` then `p` has exactly
  one ramified prime `P` in `K_f`, with `ramificationIdx = 2` and
  `inertiaDeg = 1`, all other primes over `p` unramified.  It uses
  `absNorm_differentIdeal`, `dvd_differentIdeal_iff` (support), and
  `pow_sub_one_dvd_differentIdeal` (exponent bound `v_P(different) ≥ e_P − 1`,
  which suffices since `v_p(D_f) = 1` forces equality).
**Step (c): OPEN** — **cycle-type of inertia:** the tame inertia group of the
  Galois closure at a prime over this `P` (a cyclic group of order `e = 2`)
  acts on the `n` embeddings/roots of `K_f` as a single transposition — the
  Hilbert/inertia theory of `Mathlib.NumberTheory.RamificationInertia`
  (`RamificationInertia.Galois`, decomposition/inertia subgroups).
**OPEN** — the theorem below still needs step (c) to be closed. -/
theorem fieldDisc_squarefull_of_no_transposition (f : ℤ[X])
    [Fact (Irreducible (f.map φℚ))] (hf : f.Monic)
    (hnoswap : ∀ σ : (f.map φℚ).Gal, ¬ ((irrGalFinHom f) σ).IsSwap) :
    Squarefull (fieldDisc f) := by
  classical
  -- if a prime divided D_f exactly once, step (c) would give a transposition
  apply squarefull_of_no_isSwap_of_val_one f hnoswap
  intro p hp hv
  rcases (fieldDisc_val_one_has_isSwap f p hp hv) with ⟨σ, hσ⟩
  exact hnoswap σ hσ

/-- Group-theoretic half of Case I, assembled: a monic irreducible `f` whose
Galois group (natural action on the roots) is primitive and satisfies
`|Gal| < (natDegree f)!` acts on the roots without any transposition. -/
theorem no_isSwap_of_primitive_proper_of_card_lt (f : ℤ[X]) [Fact (Irreducible (f.map φℚ))]
    (_hf : f.Monic) (hprim : MulAction.IsPreprimitive ((irrGalFinHom f).range)
        (Fin ((f.map φℚ).natDegree)))
    (hcard : Nat.card (f.map φℚ).Gal < ((f.map φℚ).natDegree).factorial) :
    ∀ σ : (f.map φℚ).Gal, ¬ ((irrGalFinHom f) σ).IsSwap := by
  dsimp [irrGalFinHom]
  apply no_isSwap_of_preprimitive_proper (f.map φℚ)
    (separable_of_irreducible_rat Fact.out) hprim
  exact range_ne_top_of_card_lt_factorial (f.map φℚ)
    (separable_of_irreducible_rat Fact.out) hcard

end OpenTargets

end
end Submission.Vdw
