import Mathlib.FieldTheory.KrullTopology
import Mathlib.GroupTheory.Nilpotent
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Quotient.Bilinear
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Work.SSGRoute.ZConstruction.LevelKRealisationCounting
import Submission.Work.SSGRoute.ZConstruction.even_finrank_H1loc_levelK
import Submission.Work.SSGRoute.ZDataMup.exists_nonsplit_place_of_selmer_proj
import Submission.Work.SSGRoute.ZDataMup.finrank_localDataSpace_quotient
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The level-`K` degree-one Tate--Poitou realisation gate

## The statement, and its mathematical content

The target of this file,

  `Work.SSGRoute.ZDataMup.tatePoitou_h1_realisation`,

is the degree-one realisation of Tate--Poitou duality in the form consumed by the `μ_p`-case of
Schmidt--Wingberg's §4 (`Work.SSGRoute.ZDataMup.isMupZData_odd`): given a local Tate system `pair`
(with its product formula `hrec`) and local data `f` at a finite set `T` of pairwise non-`G_K`-
conjugate finite places, which is *orthogonal* (`horth`, the honest `IsOrthogonalToDual` family) to
every global locally constant `1`-cocycle unramified outside the `G_K`-conjugates of `T`, there is a
global locally constant `1`-cocycle `z` on `G_K`, unramified outside those conjugates and agreeing
with `f A` on each level-`K` local group `decomp k A ⊓ G_K`.

Writing `V_T` for the space of global cocycles appearing in `horth` (they are exactly the classes of
`H¹(G_{K,S}, ZMod p)` with `S` = the primes of `K` below `T`, since the action of `G_K` on `ZMod p`
is trivial), `W = loc(V_T) ⊆ P = ∏_{A ∈ T} H¹(decomp k A ⊓ G_K, ZMod p)` for the localisation, and
`B` for the (non-degenerate, by `IsLocalTateSystem.perfect`) descended sum pairing, the statement is
literally

  `horth` says `f ∈ W^⊥` (the left annihilator), `hrec` says `W ⊆ W^⊥`, and the conclusion asks for
  `f ∈ W`.  Since `dim W^⊥ = dim P - dim W`, the conclusion follows **for every** pairing satisfying
  the axioms as soon as `dim W ≥ ½ dim P`.

So the whole arithmetic content of the gate is the counting inequality of the level-`K`
localisation, i.e. the Euler characteristic / Tate--Poitou duality statement

  `dim P ≤ 2 · dim W`

(the *Lagrangian* property; Poitou--Tate, Milne, *Arithmetic Duality Theorems* I.4.10, NSW 8.6.8).
For a place set `T` covering the primes above `p` -- which is what the hypothesis `hTp` of the
statement provides (and what makes `|ZMod p|` a unit in the ring of `S`-integers, Milne's hypothesis
on `S`) -- this is the standard self-duality of the localisation for `M = ZMod p` and its cyclotomic
dual `μ_p`; in the intended instantiation of the consumer (`μ_p ⊆ K`, so that `ZMod p ≅ μ_p` as
`G_K`-modules and the module is its own Tate dual) the inequality is an equality.

## What is proved here, and what is not

Everything *formal* is proved and sorry-free -- in this file and in the workspace modules it
imports:

* `Work.SSGRoute.ZDataMup.tatePoitou_h1_realisation_of_counting` below: the gate from the counting
  inequality, by `Work.SSGRoute.ZConstruction.levelK_realisation_of_counting` (whose proof is the
  linear algebra of `LocalData.lean`: descent of the sum pairing, the radical identifications from
  `perfect`, isotropy from the product formula, and the maximality step
  `orthogonal_le_sup_of_ker_le_quotient`);
* the *easy* half `W ⊆ W^⊥` of the arithmetic (`sum_pair_selmer_eq_zero`, the product formula);
* the local dimension computations of the lane (`finrank_localDataSpace_quotient`,
  `finrank_lcCocycleImage_eq_H1loc`).

## The sharpness direction: the residual is *optimal*

The file also proves the *converse* of the assembly,
`Work.SSGRoute.ZDataMup.exists_counterdatum_of_not_counting`:

  if the counting inequality **fails**, then there is an admissible datum `f` -- locally constant
  `1`-cocycles on the level-`K` local groups which is orthogonal (`IsOrthogonalToDual`, the very
  hypothesis of the gate) to every global cocycle unramified outside the conjugates of `T` -- whose
  conclusion fails, i.e. which is *not* the localisation of any global cocycle unramified outside
  those conjugates.

So the counting inequality is not merely sufficient but **necessary**, and the gate with its own
orthogonality hypothesis is *equivalent* to it:

* `CountingInequality` ⟹ the conclusion for every admissible datum (the assembly
  `tatePoitou_h1_realisation_of_counting` below);
* `¬ CountingInequality` ⟹ an admissible datum whose conclusion fails (the sharpness theorem).

The proof of the sharpness direction is pure linear algebra and the workspace's local Tate system
machinery; both ingredients it uses are proved in this file:

* `bilinForm_descent` -- the sum pairing descends to the quotient
  `localDataSpace K T ⧸ localVanish K T` (`localVanish` lies in both radicals, by `perfect` and the
  vanishing-on-coboundaries axiom), and the descended form is non-degenerate, since the left radical
  is *exactly* `localVanish`;
* `exists_mem_orthogonal_not_mem_of_finrank_lt` -- for any bilinear form on a finite-dimensional
  space and any subspace `W` with `2 * dim W < dim V`, the orthogonal complement `W^⊥` is not
  contained in `W` (no non-degeneracy needed);

and then: a class `x ∈ W^⊥ \ W` in the quotient, lifted to a representative `F`, is a datum whose
local components are not realisable.  Two details make the *stated* orthogonality hypothesis
(`IsOrthogonalToDual`, over all functions on `G_k` vanishing on the inertia of the non-`T` places,
not only over the `selmerSpace` classes) come out right:

* any such `b` agrees on `G_K` with the Selmer cocycle `b'` equal to `b` on `G_K` and `0` off it, so
  the associated tuples differ by an element of `localVanish`, and the pairing is blind to those
  (`localVanish ≤ B.orthogonal ⊤`); hence `B F (b-tuple) = B F (b'-tuple) = BQ x (b'-class) = 0`;
* the same comparison shows that the class of the conclusion's `z` lies in the localisation image,
  so its coincidence with `f` on the local groups would force `x ∈ W` -- contradiction.

What is **not** available in this workspace, and is therefore exposed below as the explicit
hypothesis `CountingInequality` of the assembly (and as the single `sorry` of the target), is the
*global* half: the counting identity `dim P ≤ 2 · dim W` of the level-`K` localisation.  This is the
frontier of the whole development; the workspace files that state it are
`Work.SSGRoute.ZSplit.levelK_counting_identity` (`sorry`), `Work.SSGRoute.PT.pt_selmer_counting_identity`
(`sorry`), and the reduction `Work.SSGRoute.ZConstruction.LevelKRealisationCounting` (proved) shows
that it is *equivalent* to the realisation clause `W^⊥ ⊆ V` proved here modulo the inequality -- the
two are the two faces of the same arithmetic content.  Every input that would build it (the
canonical local Tate pairing, the local duality at the level-`K` local groups, the `Ext`-core
exactness) is `sorryAx`-tainted in this workspace, so the gate cannot be closed from the trusted
content and is filed with the explicit residual.

## Mathematical remark: the role of `hTp`, and the exact residual

Two remarks that pin down which arithmetic the residual `CountingInequality` is.

* The formal layer shows the conclusion holds as soon as `dim W ≥ ½ dim P`, and the hypothesis
  `hrec` (with `perfect`) shows `dim W ≤ ½ dim P` for any *admissible* pairing.  So the gate is
  *equivalent*, in a configuration, to the arithmetic statement
  `dim W = ½ dim P` (the Lagrangian property) — provided an admissible pairing exists there;
  in configurations where `dim W > ½ dim P` the hypothesis `hrec` is unsatisfiable and the gate is
  vacuous, and where `dim W < ½ dim P` the gate fails for every admissible pairing.  In particular
  the axioms `hpair`/`hrec` alone do not imply the conclusion: the content is the arithmetic.

* In the intended instantiation of the consumer (`μ_p ⊆ K`, so `ZMod p ≅ μ_p` as `G_K`-modules and
  the coefficient module is its own Tate dual) and with `T` covering the primes above `p` -- which
  `hTp` provides, making the order of the module a unit in the ring of `S`-integers, Milne's
  hypothesis on `S` -- the Lagrangian property is the standard self-duality of the level-`K`
  localisation and the gate is the true Tate--Poitou degree-one realisation.  Note that the
  *ramification* condition that the sibling gates carry (`IsRamifiedIn k Λ`) is not needed here:
  the module `ZMod p` is unramified over `G_K`, and its Tate dual `μ_p` is ramified exactly at the
  places above `p`, which `hTp` puts into the place set.  Hence `hTp` is the right hypothesis for
  this gate, and the configurations of `ZDataMup/TATEPOITOU_STATUS.md` that refute the
  `hTp`-free versions (place sets omitting the primes above `p`) are exactly the ones where the
  balance fails and `hrec` is unsatisfiable.

## The `hTp` hypothesis

The statement carries `hTp` (every place above `p` is `G_K`-conjugate to an element of `T`).  This is
exactly the place-set condition that Poitou--Tate requires: it makes `ZMod p` (and also its Tate
dual `μ_p`, whose `G_K`-action is ramified precisely at the places above `p`) unramified outside the
`G_K`-conjugates of `T`, and it makes the order of the coefficient module invertible in the ring of
`S`-integers.  It is *not* used by the formal layer below (which consumes only the inequality), but
it is what makes the residual inequality the true arithmetic statement rather than one of the
degenerate ones of `ZDataMup/TATEPOITOU_STATUS.md`, where a place set omitting the primes above `p`
has `dim P > 2 · dim W` and the conclusion fails.
-/

open scoped Pointwise

namespace Work.SSGRoute.ZDataMup

open _root_.SSGRoute

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

/-- **The counting inequality of the level-`K` localisation** (the residual arithmetic input of the
realisation gate).  With `P = ∏_{A ∈ T} H¹(decomp k A ⊓ G_K, ZMod p)` (the local-data space modulo
the tuples vanishing on the local groups) and `W = loc(V_T)` (the localisation image of the global
cocycles unramified outside the `G_K`-conjugates of `T`), this is `dim P ≤ 2 · dim W`: the
localisation is maximally isotropic.  It is the level-`K` Tate--Poitou counting identity
(`Work.SSGRoute.ZSplit.levelK_counting_identity`, `Work.SSGRoute.PT.pt_selmer_counting_identity`, both
open). -/
def CountingInequality (p : ℕ) (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω]
    (K : IntermediateField k Ω) [Normal k K] [DistribMulAction (K ≃ₐ[k] K) (ZMod p)]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    (T : Finset (ValuationSubring Ω)) : Prop :=
  Module.finrank (ZMod p)
      (↥(localDataSpace (p := p) K T) ⧸ localVanish (p := p) K T) ≤
    2 * Module.finrank (ZMod p)
      (((localImageIn (p := p) K T) ⊔ localVanish (p := p) K T).map
        (Submodule.mkQ (localVanish (p := p) K T)))

/-- **The realisation gate from the counting inequality.**  This is the target of this file with the
residual counting inequality as an explicit hypothesis.  It is the level-`K` instance of the
assembly `Work.SSGRoute.ZConstruction.levelK_realisation_of_counting`, restated in the vocabulary of
this lane (`ZDataMup.IsLocalTateSystem`, `ZDataMup.IsProductFormula`,
`ZDataMup.IsOrthogonalToDual`, `ZDataMup.CountingInequality`), so that the target below is a single
application of it. -/
theorem tatePoitou_h1_realisation_of_counting (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (k Ω : Type)
    [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K] [Fintype (K ≃ₐ[k] K)]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    (pair : Subgroup (Ω ≃ₐ[k] Ω) → ((Ω ≃ₐ[k] Ω) → ZMod p) → ((Ω ≃ₐ[k] Ω) → ZMod p) → ZMod p)
    (hpair : Work.SSGRoute.ZDataMup.IsLocalTateSystem p k Ω K pair)
    (hrec : Work.SSGRoute.ZDataMup.IsProductFormula p k Ω K pair)
    (T : Finset (ValuationSubring Ω)) (hTfin : ∀ A ∈ T, SSGRoute.IsFinPlace k A)
    (hTdisj : ∀ A ∈ T, ∀ B ∈ T,
      (∃ τ ∈ K.fixingSubgroup, ∀ x : Ω, x ∈ B ↔ (τ⁻¹ : Ω ≃ₐ[k] Ω) • x ∈ A) → A = B)
    (hTp : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B → B.valuation (p : Ω) < 1 →
      ∃ A ∈ T, ∃ τ ∈ K.fixingSubgroup, ∀ x : Ω, x ∈ B ↔ (τ⁻¹ : Ω ≃ₐ[k] Ω) • x ∈ A)
    (f : ValuationSubring Ω → (Ω ≃ₐ[k] Ω) → ZMod p)
    (hf : ∀ A ∈ T, SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A ⊓ K.fixingSubgroup) (f A) ∧
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A ⊓ K.fixingSubgroup) (f A))
    (horth : Work.SSGRoute.ZDataMup.IsOrthogonalToDual p k Ω K pair T f)
    (hcount : CountingInequality p k Ω K T) :
    ∃ z : (Ω ≃ₐ[k] Ω) → ZMod p,
      SSGRoute.IsCocycleOn (SSGRoute.res k K) K.fixingSubgroup z ∧
      SSGRoute.IsLocConstOn K.fixingSubgroup z ∧
      (∀ A ∈ T, SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (SSGRoute.decomp k A ⊓ K.fixingSubgroup)
        (fun σ => z σ - f A σ)) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ T, ¬ ∃ τ ∈ K.fixingSubgroup, ∀ x : Ω, x ∈ B ↔ (τ⁻¹ : Ω ≃ₐ[k] Ω) • x ∈ A) →
        ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → z σ = 0) :=
  Work.SSGRoute.ZConstruction.levelK_realisation_of_counting p hp k Ω K pair hpair hrec T hTfin
    hTdisj f hf horth hcount

/-- **The level-`K` degree-one Tate--Poitou realisation** (the target of this file).  Proved from the
counting inequality `CountingInequality` -- the residual arithmetic rung of the level-`K`
localisation -- by the assembly above.  The `sorry` is *only* the counting identity: every formal
step (descent of the sum pairing, the radical identifications from `perfect`, isotropy from the
product formula, maximality) is proved, see the module docstring. -/
theorem tatePoitou_h1_realisation (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K] [Fintype (K ≃ₐ[k] K)]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    (pair : Subgroup (Ω ≃ₐ[k] Ω) → ((Ω ≃ₐ[k] Ω) → ZMod p) → ((Ω ≃ₐ[k] Ω) → ZMod p) → ZMod p)
    (hpair : Work.SSGRoute.ZDataMup.IsLocalTateSystem p k Ω K pair)
    (hrec : Work.SSGRoute.ZDataMup.IsProductFormula p k Ω K pair)
    (T : Finset (ValuationSubring Ω)) (hTfin : ∀ A ∈ T, SSGRoute.IsFinPlace k A)
    (hTdisj : ∀ A ∈ T, ∀ B ∈ T,
      (∃ τ ∈ K.fixingSubgroup, ∀ x : Ω, x ∈ B ↔ (τ⁻¹ : Ω ≃ₐ[k] Ω) • x ∈ A) → A = B)
    (hTp : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B → B.valuation (p : Ω) < 1 →
      ∃ A ∈ T, ∃ τ ∈ K.fixingSubgroup, ∀ x : Ω, x ∈ B ↔ (τ⁻¹ : Ω ≃ₐ[k] Ω) • x ∈ A)
    (f : ValuationSubring Ω → (Ω ≃ₐ[k] Ω) → ZMod p)
    (hf : ∀ A ∈ T, SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A ⊓ K.fixingSubgroup) (f A) ∧
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A ⊓ K.fixingSubgroup) (f A))
    (horth : Work.SSGRoute.ZDataMup.IsOrthogonalToDual p k Ω K pair T f) :
    ∃ z : (Ω ≃ₐ[k] Ω) → ZMod p,
      SSGRoute.IsCocycleOn (SSGRoute.res k K) K.fixingSubgroup z ∧
      SSGRoute.IsLocConstOn K.fixingSubgroup z ∧
      (∀ A ∈ T, SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (SSGRoute.decomp k A ⊓ K.fixingSubgroup)
        (fun σ => z σ - f A σ)) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ T, ¬ ∃ τ ∈ K.fixingSubgroup, ∀ x : Ω, x ∈ B ↔ (τ⁻¹ : Ω ≃ₐ[k] Ω) • x ∈ A) →
        ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → z σ = 0) :=
  tatePoitou_h1_realisation_of_counting p hp k Ω K pair hpair hrec T hTfin hTdisj hTp f hf horth
    (by sorry)

section Parity

/-- **The local-data space `P` of the level-`K` localisation has even `𝔽_p`-dimension** whenever
`ζ_p ∈ K` (`p` odd).

`dim P = ∑_{A ∈ T} dim H¹(decomp k A ⊓ G_K, ZMod p)` (`finrank_localDataSpace_quotient`), and each
local term is *even*: the level-`K` local `H¹` is the Kummer group of the level-`K` local field
`K ⊔ Ω^{D_A}` (`ZConstruction.levelK_lcHoms_eq_kummerGroup`), whose cardinality is a square power of
`p` (`ZConstruction.natCard_homs_sq`), equivalently
`ZConstruction.even_finrank_H1loc_levelK` (`Work.SSGRoute.H1loc p k Ω K (ZMod p) (decomp k A ⊓ G_K)`
has even dimension).  So `dim P` is even when `T` has an even number of places and odd-dimensional
in no case with `|T| = 1`: in particular the configuration `k = ℚ`, `K = ℚ(ζ₃)`, `p = 3`,
`T = {v₃}` has `dim P = 4`, not `3` (the local count there is
`|ℚ₃(ζ₃)ˣ/(ℚ₃(ζ₃)ˣ)³| = 3^{[ℚ₃(ζ₃):ℚ₃] + 2} = 3⁴`).

This is the correction of the record in `NOTES_rigidity_open_question.md` §7: the local
`p`-power-quotient of a self-dual local field is `p^{n + 1 + δ}` with `δ = [μ_p ⊆ κ]` — the `δ` is
*not* double counting (`ζ_p = 1+π ∈ U¹` does not kill it), as the machine-checked local count and
the sanity check "my naive count would leave `ℚ₅` without its unramified cubic extension" show. -/
theorem even_finrank_localDataSpace_quotient (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (k Ω : Type)
    [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K] [Fintype (K ≃ₐ[k] K)]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Finset (ValuationSubring Ω)) (hTfin : ∀ A ∈ T, SSGRoute.IsFinPlace k A) :
    Even (Module.finrank (ZMod p)
      (↥(localDataSpace (p := p) K T) ⧸ localVanish (p := p) K T)) := by
  classical
  rw [finrank_localDataSpace_quotient (p := p) (K := K) T hTfin]
  have hEven : ∀ A : {A : ValuationSubring Ω // A ∈ T},
      Even (Module.finrank (ZMod p)
        ↥(lcCocycleImage (p := p) K (SSGRoute.decomp k A.1 ⊓ K.fixingSubgroup))) := by
    intro A
    rw [finrank_lcCocycleImage_eq_H1loc (p := p) (K := K)
      (H := SSGRoute.decomp k A.1 ⊓ K.fixingSubgroup) inf_le_right]
    exact ZConstruction.even_finrank_H1loc_levelK p hp k Ω K ζ hζ hζK A.1 (hTfin A.1 A.2)
  have key : ∀ s : Finset {A : ValuationSubring Ω // A ∈ T},
      Even (s.sum (fun A => Module.finrank (ZMod p)
        ↥(lcCocycleImage (p := p) K (SSGRoute.decomp k A.1 ⊓ K.fixingSubgroup)))) := by
    intro s
    induction s using Finset.induction with
    | empty => simp
    | insert a s ha ih => rw [Finset.sum_insert ha]; exact (hEven a).add ih
  exact key Finset.univ

end Parity

section Sharpness

open scoped BigOperators

/-- **Descent of a bilinear form to a quotient.**  If the submodule `V₀` lies in the left radical
`LinearMap.ker B` and in the right radical `B.orthogonal ⊤`, the form factors through `V ⧸ V₀`; and
if the left radical is exactly `V₀`, the descended form is non-degenerate. -/
theorem bilinForm_descent {K' V : Type*} [Field K'] [AddCommGroup V] [Module K' V]
    (V₀ : Submodule K' V) (B : LinearMap.BilinForm K' V) (hL : V₀ ≤ LinearMap.ker B)
    (hR : V₀ ≤ B.orthogonal ⊤) :
    ∃ Bq : LinearMap.BilinForm K' (V ⧸ V₀),
      (∀ x y : V, Bq (Submodule.mkQ V₀ x) (Submodule.mkQ V₀ y) = B x y) ∧
      (LinearMap.ker B = V₀ → LinearMap.ker Bq = ⊥) := by
  have hright : V₀ ≤ B.flip.ker := by
    intro x hx
    rw [LinearMap.mem_ker]
    ext y
    rw [LinearMap.BilinForm.flip_apply, LinearMap.zero_apply]
    exact LinearMap.BilinForm.mem_orthogonal_iff.mp (hR hx) y Submodule.mem_top
  refine ⟨LinearMap.liftQ₂ V₀ V₀ B hL hright, ?_, ?_⟩
  · intro x y
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply]
    exact LinearMap.liftQ₂_mk hL hright x y
  · intro hker
    rw [Submodule.eq_bot_iff]
    intro ā hā
    obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective V₀ ā
    have hā' : LinearMap.liftQ₂ V₀ V₀ B hL hright (Submodule.mkQ V₀ z) = 0 :=
      LinearMap.mem_ker.mp hā
    have hz : z ∈ LinearMap.ker B := by
      rw [LinearMap.mem_ker]
      ext y
      have h := LinearMap.congr_fun hā' (Submodule.mkQ V₀ y)
      rw [LinearMap.zero_apply, Submodule.mkQ_apply, Submodule.mkQ_apply,
        LinearMap.liftQ₂_mk hL hright] at h
      exact h
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    rw [← hker]
    exact hz

/-- **An element of the orthogonal complement outside the subspace, from the dimension count.**
For *any* bilinear form on a finite-dimensional space and any subspace `W` with
`2 * dim W < dim V`, the right orthogonal `W^⊥` is not contained in `W`; no non-degeneracy is
needed. -/
theorem exists_mem_orthogonal_not_mem_of_finrank_lt {K' V : Type*} [Field K'] [AddCommGroup V]
    [Module K' V] [FiniteDimensional K' V] (B : LinearMap.BilinForm K' V)
    (W : Submodule K' V) (hlt : 2 * Module.finrank K' ↥W < Module.finrank K' V) :
    ∃ x ∈ B.orthogonal W, x ∉ W := by
  have h1 := LinearMap.BilinForm.finrank_add_finrank_orthogonal' (B := B) W
  have h3 : Module.finrank K' ↥W < Module.finrank K' ↥(B.orthogonal W) := by omega
  by_contra hcon
  push_neg at hcon
  have h4 : Module.finrank K' ↥(B.orthogonal W) ≤ Module.finrank K' ↥W :=
    Submodule.finrank_mono hcon
  omega

/-- **Sharpness of the residual `CountingInequality`.**  If the level-`K` counting inequality fails,
then there is a datum `f` -- locally constant `1`-cocycles on the level-`K` local groups
`decomp k A ⊓ G_K`, orthogonal (`IsOrthogonalToDual`, the hypothesis of the gate) to every global
cocycle unramified outside the `G_K`-conjugates of `T` -- which is *not* realised by any global
cocycle.  So the counting inequality is necessary as well as sufficient: the realisation gate is
equivalent to it, and the residual of `tatePoitou_h1_realisation` is exactly this inequality. -/
theorem exists_counterdatum_of_not_counting (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (k Ω : Type)
    [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K] [Fintype (K ≃ₐ[k] K)]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    (pair : Subgroup (Ω ≃ₐ[k] Ω) → ((Ω ≃ₐ[k] Ω) → ZMod p) → ((Ω ≃ₐ[k] Ω) → ZMod p) → ZMod p)
    (hpair : Work.SSGRoute.ZDataMup.IsLocalTateSystem p k Ω K pair)
    (hrec : Work.SSGRoute.ZDataMup.IsProductFormula p k Ω K pair)
    (T : Finset (ValuationSubring Ω)) (hTfin : ∀ A ∈ T, SSGRoute.IsFinPlace k A)
    (hTdisj : ∀ A ∈ T, ∀ B ∈ T,
      (∃ τ ∈ K.fixingSubgroup, ∀ x : Ω, x ∈ B ↔ (τ⁻¹ : Ω ≃ₐ[k] Ω) • x ∈ A) → A = B)
    (hnot : ¬ CountingInequality p k Ω K T) :
    ∃ f : ValuationSubring Ω → (Ω ≃ₐ[k] Ω) → ZMod p,
      (∀ A ∈ T, SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A ⊓ K.fixingSubgroup) (f A) ∧
        SSGRoute.IsLocConstOn (SSGRoute.decomp k A ⊓ K.fixingSubgroup) (f A)) ∧
      Work.SSGRoute.ZDataMup.IsOrthogonalToDual p k Ω K pair T f ∧
      ¬ (∃ z : (Ω ≃ₐ[k] Ω) → ZMod p,
          SSGRoute.IsCocycleOn (SSGRoute.res k K) K.fixingSubgroup z ∧
          SSGRoute.IsLocConstOn K.fixingSubgroup z ∧
          (∀ A ∈ T, SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (SSGRoute.decomp k A ⊓ K.fixingSubgroup)
            (fun σ => z σ - f A σ)) ∧
          (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
            (∀ A ∈ T, ¬ ∃ τ ∈ K.fixingSubgroup, ∀ x : Ω, x ∈ B ↔ (τ⁻¹ : Ω ≃ₐ[k] Ω) • x ∈ A) →
            ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → z σ = 0)) := by
  classical
  -- the sum pairing and its radical identifications
  haveI hfinQ : Module.Finite (ZMod p)
      (↥(localDataSpace (p := p) K T) ⧸ localVanish (p := p) K T) :=
    finite_localDataSpace_quotient (p := p) (K := K) T hTfin
  obtain ⟨B, hB⟩ := sumPairing_bilinForm (p := p) (K := K) hpair T hTfin
  have hHA : ∀ A : {A : ValuationSubring Ω // A ∈ T},
      ∃ A' : ValuationSubring Ω, IsFinPlace k A' ∧
        decomp k A.1 ⊓ K.fixingSubgroup = decomp k A' ⊓ K.fixingSubgroup :=
    fun A => ⟨A.1, hTfin A.1 A.2, rfl⟩
  have hkerL : B.ker ≤ localVanish (p := p) K T := by
    intro x hx
    show x.1 ∈ productVanish (p := p) K T
    refine sum_pair_eq_zero_impEqZero (p := p) (K := K) (pair := pair) hpair hTfin (a := x.1) x.2 ?_
    intro b hb
    have hx0 : B x ⟨b, hb⟩ = 0 := by
      have h0 : B x = 0 := LinearMap.mem_ker.mp hx
      simpa using LinearMap.congr_fun h0 ⟨b, hb⟩
    rw [← hB x ⟨b, hb⟩]
    exact hx0
  have hkerL' : localVanish (p := p) K T ≤ B.ker := by
    intro x hx
    rw [LinearMap.mem_ker]
    ext y
    rw [hB x y]
    refine Finset.sum_eq_zero (fun A _ => ?_)
    have hxvan : ∀ g ∈ decomp k A.1 ⊓ K.fixingSubgroup, x.1 A g = 0 := by
      have h := hx
      rw [localVanish, Submodule.mem_comap] at h
      exact h A
    have h01 : IsCocycleOn (res k K) (decomp k A.1 ⊓ K.fixingSubgroup)
          (0 : (Ω ≃ₐ[k] Ω) → ZMod p) ∧
        IsLocConstOn (decomp k A.1 ⊓ K.fixingSubgroup) (0 : (Ω ≃ₐ[k] Ω) → ZMod p) :=
      ⟨isCocycleOn_zero _, isLocConstOn_zero _⟩
    have h0b : pair (decomp k A.1 ⊓ K.fixingSubgroup) 0 (y.1 A) = 0 :=
      hpair.vanishes_coboundary (decomp k A.1 ⊓ K.fixingSubgroup) (hHA A) 0 (y.1 A)
        h01 (y.2 A) (Or.inl ⟨0, fun g hg => by simp⟩)
    exact (pair_congr_of_eqOn_left (K := K) hpair (hHA A) (x.2 A) h01 (y.2 A) hxvan).trans h0b
  have hkerR : localVanish (p := p) K T ≤ B.orthogonal ⊤ := by
    intro x hx
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro y _
    rw [hB y x]
    refine Finset.sum_eq_zero (fun A _ => ?_)
    have hxvan : ∀ g ∈ decomp k A.1 ⊓ K.fixingSubgroup, x.1 A g = 0 := by
      have h := hx
      rw [localVanish, Submodule.mem_comap] at h
      exact h A
    have h0 : pair (decomp k A.1 ⊓ K.fixingSubgroup) (y.1 A) (x.1 A) =
        pair (decomp k A.1 ⊓ K.fixingSubgroup) (y.1 A) 0 :=
      pair_congr_of_eqOn_right (K := K) hpair (hHA A) (y.2 A) (x.2 A)
        ⟨isCocycleOn_zero _, isLocConstOn_zero _⟩ hxvan
    rw [h0]
    exact pair_zero_right_of_isLocalTateSystem (K := K) hpair (hHA A) (y.2 A)
  -- descent of the pairing to the quotient of the local-data space
  obtain ⟨BQ, hBQ, hBQker⟩ := bilinForm_descent (localVanish (p := p) K T) B hkerL' hkerR
  -- the localisation image in the quotient
  let Q := ↥(localDataSpace (p := p) K T) ⧸ localVanish (p := p) K T
  let WQ : Submodule (ZMod p) Q :=
    (localImageIn (p := p) K T ⊔ localVanish (p := p) K T).map (Submodule.mkQ (localVanish (p := p) K T))
  have hlt : 2 * Module.finrank (ZMod p) ↥WQ < Module.finrank (ZMod p) Q := by
    have h : ¬ (Module.finrank (ZMod p) Q ≤ 2 * Module.finrank (ZMod p) ↥WQ) := hnot
    exact not_le.mp h
  obtain ⟨x, hxorth, hxnotW⟩ := exists_mem_orthogonal_not_mem_of_finrank_lt BQ.flip WQ hlt
  obtain ⟨F, hF⟩ := Submodule.mkQ_surjective (localVanish (p := p) K T) x
  -- the datum
  let f : ValuationSubring Ω → (Ω ≃ₐ[k] Ω) → ZMod p :=
    fun A => if h : A ∈ T then F.1 ⟨A, h⟩ else 0
  have hfA : ∀ A (hA : A ∈ T), f A = F.1 ⟨A, hA⟩ := by
    intro A hA
    show (if h : A ∈ T then F.1 ⟨A, h⟩ else 0) = F.1 ⟨A, hA⟩
    rw [dif_pos hA]
  refine ⟨f, ?_, ?_, ?_⟩
  · intro A hA
    rw [hfA A hA]
    exact F.2 ⟨A, hA⟩
  · -- orthogonality against the whole `IsOrthogonalToDual` family
    intro b hb1 hb2 hb3
    -- the Selmer representative of `b`: keep `b` on `G_K`, kill it elsewhere
    let b' : (Ω ≃ₐ[k] Ω) → ZMod p := fun σ => if σ ∈ K.fixingSubgroup then b σ else 0
    have hb'1 : IsCocycleOn (res k K) K.fixingSubgroup b' := by
      intro g hg h hh
      have h1 := hb1 g hg h hh
      simp only [b', if_pos hg, if_pos (mul_mem hg hh), if_pos hh]
      exact h1
    have hb'2 : IsLocConstOn K.fixingSubgroup b' := by
      obtain ⟨U, hU, hc⟩ := hb2
      refine ⟨U, hU, fun g hg u hu huH => ?_⟩
      simp only [b', if_pos hg, if_pos (mul_mem hg huH)]
      exact hc g hg u hu huH
    have hb'3 : ∀ B : ValuationSubring Ω, IsFinPlace k B →
        (∀ A ∈ T, ¬ ∃ τ ∈ K.fixingSubgroup, ∀ x : Ω, x ∈ B ↔ (τ⁻¹ : Ω ≃ₐ[k] Ω) • x ∈ A) →
        ∀ σ : Ω ≃ₐ[k] Ω, IsInertia k B σ → b' σ = 0 := by
      intro B hB' hnotB σ hσI
      by_cases hσ : σ ∈ K.fixingSubgroup
      · simp only [b', if_pos hσ]
        exact hb3 B hB' hnotB σ hσ hσI
      · simp only [b', if_neg hσ]
    -- the tuple of `b` and the tuple of `b'`
    have hmem1 : (fun A : {A : ValuationSubring Ω // A ∈ T} => b) ∈
        localDataSpace (p := p) K T :=
      fun A => ⟨isCocycleOn_of_le inf_le_right hb1, isLocConstOn_of_le inf_le_right hb2⟩
    have hmem2 : (fun A : {A : ValuationSubring Ω // A ∈ T} => b') ∈
        localDataSpace (p := p) K T :=
      fun A => ⟨isCocycleOn_of_le inf_le_right hb'1, isLocConstOn_of_le inf_le_right hb'2⟩
    let Tb : ↥(localDataSpace (p := p) K T) := ⟨fun A => b, hmem1⟩
    let Tb' : ↥(localDataSpace (p := p) K T) := ⟨fun A => b', hmem2⟩
    have hdiff : (Tb - Tb') ∈ localVanish (p := p) K T := by
      intro A g hg
      have h1 : b' g = b g := by
        simp only [b']
        exact if_pos hg.2
      show (Tb - Tb').1 A g = 0
      simp only [Tb, Tb', Submodule.coe_sub, Pi.sub_apply]
      rw [h1, sub_self]
    have hlin : B F (Tb - Tb') = 0 :=
      LinearMap.BilinForm.mem_orthogonal_iff.mp (hkerR hdiff) F Submodule.mem_top
    have hBeq : B F Tb = B F Tb' := by
      have h1 : B F (Tb - Tb') = B F Tb - B F Tb' := map_sub _ _ _
      rw [h1] at hlin
      exact sub_eq_zero.mp hlin
    have hsel : B F Tb' = 0 := by
      have hloc : Tb' = localisationMap (p := p) K T ⟨b', hb'1, hb'2, hb'3⟩ := Subtype.ext rfl
      rw [hloc, ← hBQ F (localisationMap (p := p) K T ⟨b', hb'1, hb'2, hb'3⟩), hF]
      have hw : Submodule.mkQ (localVanish (p := p) K T)
          (localisationMap (p := p) K T ⟨b', hb'1, hb'2, hb'3⟩) ∈ WQ :=
        Submodule.mem_map_of_mem (Submodule.mem_sup_left (LinearMap.mem_range.mpr ⟨_, rfl⟩))
      have h0 := LinearMap.BilinForm.mem_orthogonal_iff.mp hxorth _ hw
      rwa [LinearMap.BilinForm.flip_apply] at h0
    -- the sum in the statement's form
    have hsum : (∑ A : {A : ValuationSubring Ω // A ∈ T},
        pair (decomp k A.1 ⊓ K.fixingSubgroup) (F.1 A)
          ((fun A : {A : ValuationSubring Ω // A ∈ T} => b) A)) = 0 := by
      rw [← hB F Tb]
      exact hBeq.trans hsel
    have hsumf : (∑ A : {A : ValuationSubring Ω // A ∈ T},
        pair (decomp k A.1 ⊓ K.fixingSubgroup) (f A.1) b) = 0 := by
      refine Eq.trans ?_ hsum
      refine Finset.sum_congr rfl (fun A _ => ?_)
      rw [hfA A.1 A.2]
    rw [← ZConstruction.sum_subtype_eq_sum_finset T
      (fun A => pair (decomp k A ⊓ K.fixingSubgroup) (f A) b)]
    exact hsumf
  · -- the datum is not realised
    rintro ⟨z, hz1, hz2, hz3, hz4⟩
    -- `z` is a Selmer cocycle up to its values off `G_K`
    let z' : (Ω ≃ₐ[k] Ω) → ZMod p := fun σ => if σ ∈ K.fixingSubgroup then z σ else 0
    have hz'1 : IsCocycleOn (res k K) K.fixingSubgroup z' := by
      intro g hg h hh
      have h1 := hz1 g hg h hh
      simp only [z', if_pos hg, if_pos (mul_mem hg hh), if_pos hh]
      exact h1
    have hz'2 : IsLocConstOn K.fixingSubgroup z' := by
      obtain ⟨U, hU, hc⟩ := hz2
      refine ⟨U, hU, fun g hg u hu huH => ?_⟩
      simp only [z', if_pos hg, if_pos (mul_mem hg huH)]
      exact hc g hg u hu huH
    have hz'3 : ∀ B : ValuationSubring Ω, IsFinPlace k B →
        (∀ A ∈ T, ¬ ∃ τ ∈ K.fixingSubgroup, ∀ x : Ω, x ∈ B ↔ (τ⁻¹ : Ω ≃ₐ[k] Ω) • x ∈ A) →
        ∀ σ : Ω ≃ₐ[k] Ω, IsInertia k B σ → z' σ = 0 := by
      intro B hB' hnotB σ hσI
      by_cases hσ : σ ∈ K.fixingSubgroup
      · simp only [z', if_pos hσ]
        exact hz4 B hB' hnotB σ hσ hσI
      · simp only [z', if_neg hσ]
    -- the tuple of `z` has the same class as a localisation
    have hZmem : (fun A : {A : ValuationSubring Ω // A ∈ T} => z) ∈
        localDataSpace (p := p) K T :=
      fun A => ⟨isCocycleOn_of_le inf_le_right hz1, isLocConstOn_of_le inf_le_right hz2⟩
    have hZ'mem : (fun A : {A : ValuationSubring Ω // A ∈ T} => z') ∈
        localDataSpace (p := p) K T :=
      fun A => ⟨isCocycleOn_of_le inf_le_right hz'1, isLocConstOn_of_le inf_le_right hz'2⟩
    let TZ : ↥(localDataSpace (p := p) K T) := ⟨fun A => z, hZmem⟩
    let TZ' : ↥(localDataSpace (p := p) K T) := ⟨fun A => z', hZ'mem⟩
    have hZdiff : (TZ - TZ') ∈ localVanish (p := p) K T := by
      intro A g hg
      have h1 : z' g = z g := by
        simp only [z']
        exact if_pos hg.2
      show (TZ - TZ').1 A g = 0
      simp only [TZ, TZ', Submodule.coe_sub, Pi.sub_apply]
      rw [h1, sub_self]
    have hZF : (TZ - F) ∈ localVanish (p := p) K T := by
      intro A g hg
      show (TZ - F).1 A g = 0
      simp only [TZ, Submodule.coe_sub, Pi.sub_apply]
      have hAg : z g = f A.1 g :=
        (sub_isCoboundaryOn_iff_eqOn (p := p)
          (H := decomp k A.1 ⊓ K.fixingSubgroup) inf_le_right z (f A.1)).mp
          (hz3 A.1 A.2) g hg
      rw [hAg, hfA A.1 A.2]
      simp
    have hx1 : Submodule.mkQ (localVanish (p := p) K T) TZ = x := by
      have h2 : Submodule.mkQ (localVanish (p := p) K T) (TZ - F) = 0 := by
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact hZF
      rw [map_sub] at h2
      exact (sub_eq_zero.mp h2).trans hF
    have hx2 : Submodule.mkQ (localVanish (p := p) K T) TZ ∈ WQ := by
      have h3 : Submodule.mkQ (localVanish (p := p) K T) TZ =
          Submodule.mkQ (localVanish (p := p) K T) TZ' := by
        have h4 : Submodule.mkQ (localVanish (p := p) K T) (TZ - TZ') = 0 := by
          rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
          exact hZdiff
        rw [map_sub] at h4
        exact sub_eq_zero.mp h4
      rw [h3]
      refine Submodule.mem_map_of_mem (Submodule.mem_sup_left ?_)
      exact LinearMap.mem_range.mpr ⟨⟨z', hz'1, hz'2, hz'3⟩, Subtype.ext rfl⟩
    rw [← hx1] at hxnotW
    exact hxnotW hx2

/-- **The axioms are rigid: the isotropy inequality.**  For any local Tate system `pair` satisfying
the product formula, the localisation image `W_T` of the level-`K` Selmer space is *isotropic* for
the descended sum pairing on the product `P = ∏_{A ∈ T} H¹(decomp k A ⊓ G_K, ZMod p)` of the local
`H¹`s -- and that pairing is non-degenerate (from the axiom `perfect`).  Consequently

  `2 · dim W_T ≤ dim P`.

This is the *converse* of the counting inequality `CountingInequality` (the residual of the
realisation target): the axioms alone give `dim W_T ≤ ½ dim P`, while the target asks for
`dim P ≤ 2 · dim W_T`.  So the two are compatible only in "Lagrangian" configurations, and no local
Tate system with the product formula exists as soon as `2 · dim W_T > dim P`
(`not_exists_pair_of_isotropy_fails`). -/
theorem sum_pairing_isotropy_le (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    (pair : Subgroup (Ω ≃ₐ[k] Ω) → ((Ω ≃ₐ[k] Ω) → ZMod p) → ((Ω ≃ₐ[k] Ω) → ZMod p) → ZMod p)
    (hpair : Work.SSGRoute.ZDataMup.IsLocalTateSystem p k Ω K pair)
    (hrec : Work.SSGRoute.ZDataMup.IsProductFormula p k Ω K pair)
    (T : Finset (ValuationSubring Ω)) (hTfin : ∀ A ∈ T, SSGRoute.IsFinPlace k A)
    (hTdisj : ∀ A ∈ T, ∀ B ∈ T,
      (∃ τ ∈ K.fixingSubgroup, ∀ x : Ω, x ∈ B ↔ (τ⁻¹ : Ω ≃ₐ[k] Ω) • x ∈ A) → A = B) :
    2 * Module.finrank (ZMod p)
        (((localImageIn (p := p) K T) ⊔ localVanish (p := p) K T).map
          (Submodule.mkQ (localVanish (p := p) K T))) ≤
      Module.finrank (ZMod p)
        (↥(localDataSpace (p := p) K T) ⧸ localVanish (p := p) K T) := by
  classical
  haveI hfinQ : Module.Finite (ZMod p)
      (↥(localDataSpace (p := p) K T) ⧸ localVanish (p := p) K T) :=
    finite_localDataSpace_quotient (p := p) (K := K) T hTfin
  obtain ⟨B, hB⟩ := sumPairing_bilinForm (p := p) (K := K) hpair T hTfin
  have hHA : ∀ A : {A : ValuationSubring Ω // A ∈ T},
      ∃ A' : ValuationSubring Ω, IsFinPlace k A' ∧
        decomp k A.1 ⊓ K.fixingSubgroup = decomp k A' ⊓ K.fixingSubgroup :=
    fun A => ⟨A.1, hTfin A.1 A.2, rfl⟩
  have hkerL : B.ker ≤ localVanish (p := p) K T := by
    intro x hx
    show x.1 ∈ productVanish (p := p) K T
    refine sum_pair_eq_zero_impEqZero (p := p) (K := K) (pair := pair) hpair hTfin (a := x.1) x.2 ?_
    intro b hb
    have hx0 : B x ⟨b, hb⟩ = 0 := by
      have h0 : B x = 0 := LinearMap.mem_ker.mp hx
      simpa using LinearMap.congr_fun h0 ⟨b, hb⟩
    rw [← hB x ⟨b, hb⟩]
    exact hx0
  have hkerL' : localVanish (p := p) K T ≤ B.ker := by
    intro x hx
    rw [LinearMap.mem_ker]
    ext y
    rw [hB x y]
    refine Finset.sum_eq_zero (fun A _ => ?_)
    have hxvan : ∀ g ∈ decomp k A.1 ⊓ K.fixingSubgroup, x.1 A g = 0 := by
      have h := hx
      rw [localVanish, Submodule.mem_comap] at h
      exact h A
    have h01 : IsCocycleOn (res k K) (decomp k A.1 ⊓ K.fixingSubgroup)
          (0 : (Ω ≃ₐ[k] Ω) → ZMod p) ∧
        IsLocConstOn (decomp k A.1 ⊓ K.fixingSubgroup) (0 : (Ω ≃ₐ[k] Ω) → ZMod p) :=
      ⟨isCocycleOn_zero _, isLocConstOn_zero _⟩
    have h0b : pair (decomp k A.1 ⊓ K.fixingSubgroup) 0 (y.1 A) = 0 :=
      hpair.vanishes_coboundary (decomp k A.1 ⊓ K.fixingSubgroup) (hHA A) 0 (y.1 A)
        h01 (y.2 A) (Or.inl ⟨0, fun g hg => by simp⟩)
    exact (pair_congr_of_eqOn_left (K := K) hpair (hHA A) (x.2 A) h01 (y.2 A) hxvan).trans h0b
  have hkerR : localVanish (p := p) K T ≤ B.orthogonal ⊤ := by
    intro x hx
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro y _
    rw [hB y x]
    refine Finset.sum_eq_zero (fun A _ => ?_)
    have hxvan : ∀ g ∈ decomp k A.1 ⊓ K.fixingSubgroup, x.1 A g = 0 := by
      have h := hx
      rw [localVanish, Submodule.mem_comap] at h
      exact h A
    have h0 : pair (decomp k A.1 ⊓ K.fixingSubgroup) (y.1 A) (x.1 A) =
        pair (decomp k A.1 ⊓ K.fixingSubgroup) (y.1 A) 0 :=
      pair_congr_of_eqOn_right (K := K) hpair (hHA A) (y.2 A) (x.2 A)
        ⟨isCocycleOn_zero _, isLocConstOn_zero _⟩ hxvan
    rw [h0]
    exact pair_zero_right_of_isLocalTateSystem (K := K) hpair (hHA A) (y.2 A)
  have hker : B.ker = localVanish (p := p) K T := le_antisymm hkerL hkerL'
  obtain ⟨BQ, hBQ, hBQker⟩ :=
    bilinForm_descent (localVanish (p := p) K T) B hkerL' hkerR
  have hkerBQ : LinearMap.ker BQ = ⊥ := hBQker hker
  -- the localVanish part of the image dies in the quotient
  have hWQeq : ((localImageIn (p := p) K T) ⊔ localVanish (p := p) K T).map
        (Submodule.mkQ (localVanish (p := p) K T))
      = (localImageIn (p := p) K T).map (Submodule.mkQ (localVanish (p := p) K T)) := by
    rw [Submodule.map_sup]
    have hbot : (localVanish (p := p) K T).map (Submodule.mkQ (localVanish (p := p) K T)) = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro x hx
      obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hy
    rw [hbot, sup_bot_eq]
  rw [hWQeq]
  let WQ : Submodule (ZMod p)
      (↥(localDataSpace (p := p) K T) ⧸ localVanish (p := p) K T) :=
    (localImageIn (p := p) K T).map (Submodule.mkQ (localVanish (p := p) K T))
  show 2 * Module.finrank (ZMod p) ↥WQ ≤
    Module.finrank (ZMod p) (↥(localDataSpace (p := p) K T) ⧸ localVanish (p := p) K T)
  -- isotropy of `WQ`: the product formula
  have hiso : WQ ≤ BQ.orthogonal WQ := by
    intro x hx
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro y hy
    obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hx
    obtain ⟨u', hu', rfl⟩ := Submodule.mem_map.mp hy
    obtain ⟨b, hbu⟩ := LinearMap.mem_range.mp hu
    obtain ⟨b', hbu'⟩ := LinearMap.mem_range.mp hu'
    rw [← hbu, ← hbu', hBQ, hB]
    have hterm : ∀ A : {A : ValuationSubring Ω // A ∈ T},
        pair (decomp k A.1 ⊓ K.fixingSubgroup) ((localisationMap (p := p) K T b').1 A)
            ((localisationMap (p := p) K T b).1 A)
          = pair (decomp k A.1 ⊓ K.fixingSubgroup) b'.1 b.1 := fun A => rfl
    rw [Finset.sum_congr rfl (fun A _ => hterm A),
      ZConstruction.sum_subtype_eq_sum_finset T
        (fun A => pair (decomp k A ⊓ K.fixingSubgroup) b'.1 b.1)]
    exact sum_pair_selmer_eq_zero hrec hTfin hTdisj b'.2 b.2
  -- the dimension count
  have h1 := LinearMap.BilinForm.finrank_add_finrank_orthogonal' (B := BQ) WQ
  rw [hkerBQ, inf_bot_eq, finrank_bot, add_zero] at h1
  have h2 : Module.finrank (ZMod p) ↥WQ ≤ Module.finrank (ZMod p) ↥(BQ.orthogonal WQ) :=
    Submodule.finrank_mono hiso
  omega

section Tightness

/-- **The residual is an *equality to hit*.**  For any admissible local Tate system at level `K`
(i.e. under the two axioms `hpair`, `hrec`), the counting inequality is *equivalent* to the
equality

  `2 · dim W_T = dim P`,

because the axioms already give the reverse inequality `2 · dim W_T ≤ dim P`
(`sum_pairing_isotropy_le`).  So the whole content of the target is the *Lagrangian* property of
the localisation: the axioms give the isotropy `W_T ⊆ W_T^⊥`, and the residual asks for
`W_T^⊥ ⊆ W_T`, which is an equality of dimensions.

In the tight (Lagrangian) case the side to compute is therefore the *lower* bound
`dim W_T ≥ ½ dim P`, i.e. the dimension of the localisation of the level-`K` Selmer space; the
upper bound `dim W_T ≤ ½ dim P` is the axioms, and the *left* side `dim P` is computable:
`dim P = ∑_{A ∈ T} e_A` (`finrank_localDataSpace_quotient` +
`finrank_lcCocycleImage_eq_H1loc`), where the local dimension is even
(`even_finrank_localDataSpace_quotient`) and, by the fleet's local Kummer count, is
`[K_{𝔓_A}:ℚ_p] + 2` when `p` is the residue characteristic of `A` and `2` otherwise
(`PTCore.finrank_H1loc_triv_eq`, `PTCore.h1loc_mup_finrank`, from
`NK.LocalInputs.natCard_KummerGroup_adicCompletion_eq_pow`).  For the reference configuration
`k = ℚ, K = ℚ(ζ₃), p = 3, T = {v₃}` this is `dim P = [ℚ₃(ζ₃):ℚ₃] + 2 = 4`, and the equality to hit
is `2 · dim W_T = 4`. -/
theorem countingInequality_iff_two_mul_finrank_eq (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K] [Fintype (K ≃ₐ[k] K)]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    (pair : Subgroup (Ω ≃ₐ[k] Ω) → ((Ω ≃ₐ[k] Ω) → ZMod p) → ((Ω ≃ₐ[k] Ω) → ZMod p) → ZMod p)
    (hpair : Work.SSGRoute.ZDataMup.IsLocalTateSystem p k Ω K pair)
    (hrec : Work.SSGRoute.ZDataMup.IsProductFormula p k Ω K pair)
    (T : Finset (ValuationSubring Ω)) (hTfin : ∀ A ∈ T, SSGRoute.IsFinPlace k A)
    (hTdisj : ∀ A ∈ T, ∀ B ∈ T,
      (∃ τ ∈ K.fixingSubgroup, ∀ x : Ω, x ∈ B ↔ (τ⁻¹ : Ω ≃ₐ[k] Ω) • x ∈ A) → A = B) :
    Work.SSGRoute.ZDataMup.CountingInequality p k Ω K T ↔
      2 * Module.finrank (ZMod p)
          (((localImageIn (p := p) K T) ⊔ localVanish (p := p) K T).map
            (Submodule.mkQ (localVanish (p := p) K T)))
        = Module.finrank (ZMod p)
            (↥(localDataSpace (p := p) K T) ⧸ localVanish (p := p) K T) := by
  constructor
  · intro hc
    have h1 := sum_pairing_isotropy_le p k Ω K pair hpair hrec T hTfin hTdisj
    have h2 : Module.finrank (ZMod p)
        (↥(localDataSpace (p := p) K T) ⧸ localVanish (p := p) K T) ≤
        2 * Module.finrank (ZMod p)
          (((localImageIn (p := p) K T) ⊔ localVanish (p := p) K T).map
            (Submodule.mkQ (localVanish (p := p) K T))) := hc
    omega
  · intro h
    exact le_of_eq h.symm


/-- **The counting inequality in terms of the local `H¹`-dimensions.**

By `finrank_localDataSpace_quotient` the left-hand side `dim P_T` of `CountingInequality` is the sum
of the local `H¹`-dimensions `dim lcCocycleImage K H_A` over the places `A ∈ T`, so the inequality is
literally `∑_{A ∈ T} dim H¹(H_A, ZMod p) ≤ 2 · dim W_T` -- the form in which the local
dimension computations of the arithmetic lanes (`PTCore.finrank_H1loc_triv_eq`,
`PTdualControl.finrank_H1loc_triv_levelK`, and the delegated
`finrank_H1loc_triv_eq_one_of_not_residueChar`) can be fed into it. -/
theorem countingInequality_iff_sum_localDims_le (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    (T : Finset (ValuationSubring Ω)) (hTfin : ∀ A ∈ T, SSGRoute.IsFinPlace k A) :
    CountingInequality p k Ω K T ↔
      (∑ A : {A : ValuationSubring Ω // A ∈ T},
          Module.finrank (ZMod p) ↥(lcCocycleImage (p := p) K
            (SSGRoute.decomp k A.1 ⊓ K.fixingSubgroup))) ≤
        2 * Module.finrank (ZMod p)
          (((localImageIn (p := p) K T) ⊔ localVanish (p := p) K T).map
            (Submodule.mkQ (localVanish (p := p) K T))) := by
  unfold CountingInequality
  rw [finrank_localDataSpace_quotient (p := p) (K := K) T hTfin]

end Tightness

/-- **The axioms are inconsistent as soon as the isotropy inequality is violated.**  If the
localisation image `W_T` of the level-`K` Selmer space is *more* than half of the local-data space
`P = ∏_{A ∈ T} H¹(decomp k A ⊓ G_K, ZMod p)`, then there is no local Tate system at level `K` with
the product formula at all: `IsLocalTateSystem ∧ IsProductFormula` is unsatisfiable.  In such a
configuration the realisation target `tatePoitou_h1_realisation` holds *vacuously*. -/
theorem not_exists_pair_of_isotropy_fails (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    (T : Finset (ValuationSubring Ω)) (hTfin : ∀ A ∈ T, SSGRoute.IsFinPlace k A)
    (hTdisj : ∀ A ∈ T, ∀ B ∈ T,
      (∃ τ ∈ K.fixingSubgroup, ∀ x : Ω, x ∈ B ↔ (τ⁻¹ : Ω ≃ₐ[k] Ω) • x ∈ A) → A = B)
    (hle : Module.finrank (ZMod p)
        (↥(localDataSpace (p := p) K T) ⧸ localVanish (p := p) K T) <
      2 * Module.finrank (ZMod p)
        (((localImageIn (p := p) K T) ⊔ localVanish (p := p) K T).map
          (Submodule.mkQ (localVanish (p := p) K T)))) :
    ¬ ∃ pair : Subgroup (Ω ≃ₐ[k] Ω) → ((Ω ≃ₐ[k] Ω) → ZMod p) → ((Ω ≃ₐ[k] Ω) → ZMod p) → ZMod p,
      Work.SSGRoute.ZDataMup.IsLocalTateSystem p k Ω K pair ∧
        Work.SSGRoute.ZDataMup.IsProductFormula p k Ω K pair := by
  rintro ⟨pair, hpair, hrec⟩
  have h := sum_pairing_isotropy_le p k Ω K pair hpair hrec T hTfin hTdisj
  omega


/-- **The level-`K` realisation gate is equivalent to the counting inequality.**

The conclusion of `tatePoitou_h1_realisation` holds for *every* admissible local datum satisfying
`IsOrthogonalToDual` if and only if the counting inequality `CountingInequality` holds.  (No
hypothesis on the place set beyond `hTfin`/`hTdisj` is needed for either direction; the statement's
`hTp` enters only in identifying the residual with the arithmetic of Poitou--Tate.) -/
theorem tatePoitou_h1_realisation_iff_counting (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (k Ω : Type)
    [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K] [Fintype (K ≃ₐ[k] K)]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    (pair : Subgroup (Ω ≃ₐ[k] Ω) → ((Ω ≃ₐ[k] Ω) → ZMod p) → ((Ω ≃ₐ[k] Ω) → ZMod p) → ZMod p)
    (hpair : Work.SSGRoute.ZDataMup.IsLocalTateSystem p k Ω K pair)
    (hrec : Work.SSGRoute.ZDataMup.IsProductFormula p k Ω K pair)
    (T : Finset (ValuationSubring Ω)) (hTfin : ∀ A ∈ T, SSGRoute.IsFinPlace k A)
    (hTdisj : ∀ A ∈ T, ∀ B ∈ T,
      (∃ τ ∈ K.fixingSubgroup, ∀ x : Ω, x ∈ B ↔ (τ⁻¹ : Ω ≃ₐ[k] Ω) • x ∈ A) → A = B) :
    ((∀ f : ValuationSubring Ω → (Ω ≃ₐ[k] Ω) → ZMod p,
        (∀ A ∈ T, SSGRoute.IsCocycleOn (SSGRoute.res k K)
            (SSGRoute.decomp k A ⊓ K.fixingSubgroup) (f A) ∧
          SSGRoute.IsLocConstOn (SSGRoute.decomp k A ⊓ K.fixingSubgroup) (f A)) →
        Work.SSGRoute.ZDataMup.IsOrthogonalToDual p k Ω K pair T f →
        ∃ z : (Ω ≃ₐ[k] Ω) → ZMod p,
          SSGRoute.IsCocycleOn (SSGRoute.res k K) K.fixingSubgroup z ∧
          SSGRoute.IsLocConstOn K.fixingSubgroup z ∧
          (∀ A ∈ T, SSGRoute.IsCoboundaryOn (SSGRoute.res k K)
            (SSGRoute.decomp k A ⊓ K.fixingSubgroup) (fun σ => z σ - f A σ)) ∧
          (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
            (∀ A ∈ T, ¬ ∃ τ ∈ K.fixingSubgroup, ∀ x : Ω, x ∈ B ↔ (τ⁻¹ : Ω ≃ₐ[k] Ω) • x ∈ A) →
            ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → z σ = 0)) ↔
      CountingInequality p k Ω K T) := by
  constructor
  · intro h
    by_contra hnot
    obtain ⟨f, hf, horth, hnotreal⟩ :=
      exists_counterdatum_of_not_counting p hp k Ω K pair hpair hrec T hTfin hTdisj hnot
    exact hnotreal (h f hf horth)
  · intro hcount f hf horth
    exact ZConstruction.levelK_realisation_of_counting p hp k Ω K pair hpair hrec T hTfin hTdisj
      f hf horth hcount


section Rigidity

/-- **The first rung of the rigidity of the axioms: a place outside `T` pairs trivially on the
whole `T`-Selmer space.**

Let `T` be a finite set of pairwise non-`G_K`-conjugate finite places and let `A₀` be a finite place
of `Ω` which is not `G_K`-conjugate to any element of `T`.  Then the local Tate pairing at `A₀`
vanishes on the `T`-Selmer space `V_T = selmerSpace K T`:

  `pair (decomp k A₀ ⊓ K.fixingSubgroup) a b = 0`  for all `a b ∈ V_T`.

This is a purely formal consequence of the product formula: applying `IsProductFormula` to the two
place sets `T` and `T ∪ {A₀}` with the *same* pair `a, b ∈ V_T` (which is unramified on the
conjugates of `T`, hence also of the larger set `T ∪ {A₀}`) gives

  `pair_{A₀}(a,b) + Σ_{A ∈ T} pair_A(a,b) = 0`  and  `Σ_{A ∈ T} pair_A(a,b) = 0`,

and subtracting them yields the claim.  The place set `T` is *not* assumed to contain the places
above `p` and the pairing is *not* assumed to be symmetric or to come from a canonical local Tate
pairing, so this holds for every `pair` satisfying the two axioms.

Together with `tatePoitou_h1_realisation_iff_counting` this is the formal content of the observation
that the axioms are *rigid*: they force the local pairing at a place to be trivial on the image of
every Selmer space omitting that place (in particular on the image of the classes which are
unramified there), which in a configuration where that image is large is incompatible with the
non-degeneracy axiom `perfect`. -/
theorem pair_zero_of_selmer_of_new_place (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    (pair : Subgroup (Ω ≃ₐ[k] Ω) → ((Ω ≃ₐ[k] Ω) → ZMod p) → ((Ω ≃ₐ[k] Ω) → ZMod p) → ZMod p)
    (hrec : Work.SSGRoute.ZDataMup.IsProductFormula p k Ω K pair)
    (T : Finset (ValuationSubring Ω)) (hTfin : ∀ A ∈ T, SSGRoute.IsFinPlace k A)
    (hTdisj : ∀ A ∈ T, ∀ B ∈ T,
      (∃ τ ∈ K.fixingSubgroup, ∀ x : Ω, x ∈ B ↔ (τ⁻¹ : Ω ≃ₐ[k] Ω) • x ∈ A) → A = B)
    (A₀ : ValuationSubring Ω) (hA₀ : SSGRoute.IsFinPlace k A₀)
    (hdisj : ∀ A ∈ T,
      ¬ ∃ τ ∈ K.fixingSubgroup, ∀ x : Ω, x ∈ A₀ ↔ (τ⁻¹ : Ω ≃ₐ[k] Ω) • x ∈ A)
    {a b : (Ω ≃ₐ[k] Ω) → ZMod p} (ha : a ∈ selmerSpace (p := p) K T)
    (hb : b ∈ selmerSpace (p := p) K T) :
    pair (SSGRoute.decomp k A₀ ⊓ K.fixingSubgroup) a b = 0 := by
  classical
  have hmem : A₀ ∉ T := by
    intro h
    exact hdisj A₀ h ⟨1, K.fixingSubgroup.one_mem, fun x => by simp⟩
  have hT'fin : ∀ A ∈ insert A₀ T, SSGRoute.IsFinPlace k A := by
    intro A hA
    rcases Finset.mem_insert.mp hA with rfl | hA
    · exact hA₀
    · exact hTfin A hA
  have hsymm : ∀ {A B : ValuationSubring Ω},
      (∃ τ ∈ K.fixingSubgroup, ∀ x : Ω, x ∈ B ↔ (τ⁻¹ : Ω ≃ₐ[k] Ω) • x ∈ A) →
      (∃ τ ∈ K.fixingSubgroup, ∀ x : Ω, x ∈ A ↔ (τ⁻¹ : Ω ≃ₐ[k] Ω) • x ∈ B) := by
    rintro A B ⟨τ, hτ, hx⟩
    exact ⟨τ⁻¹, K.fixingSubgroup.inv_mem hτ, fun x => by simpa using (hx (τ • x)).symm⟩
  have hT'disj : ∀ A ∈ insert A₀ T, ∀ B ∈ insert A₀ T,
      (∃ τ ∈ K.fixingSubgroup, ∀ x : Ω, x ∈ B ↔ (τ⁻¹ : Ω ≃ₐ[k] Ω) • x ∈ A) → A = B := by
    intro A hA B hB hconj
    rcases Finset.mem_insert.mp hA with hAeq | hAT
    · rcases Finset.mem_insert.mp hB with hBeq | hBT
      · exact hAeq.trans hBeq.symm
      · exact absurd (hsymm (hAeq ▸ hconj)) (hdisj B hBT)
    · rcases Finset.mem_insert.mp hB with hBeq | hBT
      · exact absurd (hBeq ▸ hconj) (hdisj A hAT)
      · exact hTdisj A hAT B hBT hconj
  have hunr' : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ insert A₀ T,
        ¬ ∃ τ ∈ K.fixingSubgroup, ∀ x : Ω, x ∈ B ↔ (τ⁻¹ : Ω ≃ₐ[k] Ω) • x ∈ A) →
      ∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B σ → a σ = 0 ∧ b σ = 0 := by
    intro B hB hnc σ hσ
    exact ⟨ha.2.2 B hB (fun A hA hc => hnc A (Finset.mem_insert_of_mem hA) hc) σ hσ,
      hb.2.2 B hB (fun A hA hc => hnc A (Finset.mem_insert_of_mem hA) hc) σ hσ⟩
  have hunr : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ T, ¬ ∃ τ ∈ K.fixingSubgroup, ∀ x : Ω, x ∈ B ↔ (τ⁻¹ : Ω ≃ₐ[k] Ω) • x ∈ A) →
      ∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B σ → a σ = 0 ∧ b σ = 0 :=
    fun B hB hnc σ hσ => ⟨ha.2.2 B hB hnc σ hσ, hb.2.2 B hB hnc σ hσ⟩
  have h1 := hrec a b ha.1 ha.2.1 hb.1 hb.2.1 (insert A₀ T) hT'fin hT'disj hunr'
  have h2 := hrec a b ha.1 ha.2.1 hb.1 hb.2.1 T hTfin hTdisj hunr
  rw [Finset.sum_insert hmem] at h1
  rw [h2, add_zero] at h1
  exact h1


/-- **Rigidity, second rung: a level-`K` local group with a *surjective* Selmer localisation
carries no non-trivial locally constant cocycle.**

Let `A` be a finite place of `Ω` which is not `G_K`-conjugate to any element of a place set `T`
(`hTfin`, `hTdisj`, `hdisj`), and suppose that every locally constant `1`-cocycle on the level-`K`
local group `H = decomp k A ⊓ K.fixingSubgroup` is the restriction of a class of the `T`-Selmer
space `V_T` (`hsurj`).  Then every locally constant cocycle on `H` vanishes on `H`, i.e.

  `H¹(H, ZMod p) = 0`.

Indeed, by `pair_zero_of_selmer_of_new_place` the local pairing at `A` vanishes on `V_T`; since the
pairing depends only on the restriction to `H`, it vanishes identically on the locally constant
cocycles on `H`; and by the non-degeneracy axiom `perfect` every such cocycle is then a coboundary,
i.e. vanishes on `H`.

This is the mechanism by which the axioms `IsLocalTateSystem`/`IsProductFormula` become *inconsistent*
whenever the Selmer localisation is surjective at a place whose level-`K` local group has non-trivial
`H¹` (which is the case for every finite place, the cyclotomic `ZMod p`-quotient of `G_{K_A}`): the
axioms are therefore *rigid*, and a configuration can support them only if the Selmer localisation is
small everywhere -- which is exactly the self-dual situation in which the level-`K` counting identity
(Poitou--Tate) holds. -/
theorem eqOn_zero_of_surjective_selmer_restriction (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    (pair : Subgroup (Ω ≃ₐ[k] Ω) → ((Ω ≃ₐ[k] Ω) → ZMod p) → ((Ω ≃ₐ[k] Ω) → ZMod p) → ZMod p)
    (hpair : Work.SSGRoute.ZDataMup.IsLocalTateSystem p k Ω K pair)
    (hrec : Work.SSGRoute.ZDataMup.IsProductFormula p k Ω K pair)
    (T : Finset (ValuationSubring Ω)) (hTfin : ∀ A' ∈ T, SSGRoute.IsFinPlace k A')
    (hTdisj : ∀ A' ∈ T, ∀ B ∈ T,
      (∃ τ ∈ K.fixingSubgroup, ∀ x : Ω, x ∈ B ↔ (τ⁻¹ : Ω ≃ₐ[k] Ω) • x ∈ A') → A' = B)
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (hdisj : ∀ A' ∈ T,
      ¬ ∃ τ ∈ K.fixingSubgroup, ∀ x : Ω, x ∈ A ↔ (τ⁻¹ : Ω ≃ₐ[k] Ω) • x ∈ A')
    (hsurj : ∀ f : (Ω ≃ₐ[k] Ω) → ZMod p,
      SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A ⊓ K.fixingSubgroup) f →
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A ⊓ K.fixingSubgroup) f →
      ∃ b ∈ selmerSpace (p := p) K T,
        ∀ g ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, b g = f g) :
    ∀ f : (Ω ≃ₐ[k] Ω) → ZMod p,
      SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A ⊓ K.fixingSubgroup) f →
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A ⊓ K.fixingSubgroup) f →
      ∀ g ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, f g = 0 := by
  intro f hf1 hf2
  have hH : ∃ A' : ValuationSubring Ω, SSGRoute.IsFinPlace k A' ∧
      SSGRoute.decomp k A ⊓ K.fixingSubgroup = SSGRoute.decomp k A' ⊓ K.fixingSubgroup :=
    ⟨A, hA, rfl⟩
  have hzero : ∀ b' : (Ω ≃ₐ[k] Ω) → ZMod p,
      SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A ⊓ K.fixingSubgroup) b' ∧
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A ⊓ K.fixingSubgroup) b' →
      pair (SSGRoute.decomp k A ⊓ K.fixingSubgroup) f b' = 0 := by
    intro b' hb'
    obtain ⟨b, hb, hbagree⟩ := hsurj f hf1 hf2
    obtain ⟨b'', hb'', hb''agree⟩ := hsurj b' hb'.1 hb'.2
    rw [pair_congr_of_eqOn_left (K := K) hpair hH ⟨hf1, hf2⟩
      ⟨isCocycleOn_of_le inf_le_right hb.1, isLocConstOn_of_le inf_le_right hb.2.1⟩ hb'
      (fun g hg => (hbagree g hg).symm)]
    rw [pair_congr_of_eqOn_right (K := K) hpair hH
      ⟨isCocycleOn_of_le inf_le_right hb.1, isLocConstOn_of_le inf_le_right hb.2.1⟩
      ⟨hb'.1, hb'.2⟩
      ⟨isCocycleOn_of_le inf_le_right hb''.1, isLocConstOn_of_le inf_le_right hb''.2.1⟩
      (fun g hg => (hb''agree g hg).symm)]
    exact pair_zero_of_selmer_of_new_place p k Ω K pair hrec T hTfin hTdisj A hA hdisj hb hb''
  have hcob : SSGRoute.IsCoboundaryOn (SSGRoute.res k K)
      (SSGRoute.decomp k A ⊓ K.fixingSubgroup) f :=
    hpair.perfect _ hH f ⟨hf1, hf2⟩ hzero
  intro g hg
  exact (isCoboundaryOn_iff_eqOn_zero (p := p) (K := K) inf_le_right f).mp hcob g hg


/-- **A `1`-cocycle whose kernel contains the trace of an open subgroup is locally constant.**

This is the second (cheap) ingredient of the "local cocycle from a cyclic level quotient" engine: in
`h1loc_finPlace_ne_zero` one constructs an additive function on the level-`K` local group
`H = decomp k A ⊓ K.fixingSubgroup` which is a homomorphism (the action of `H` on `ZMod p` through
`res k K` being trivial), and the only thing left to check for `IsLocConstOn H f` -- besides the
cocycle identity -- is that `f` vanishes on the trace `V ⊓ H` of an open subgroup `V ≤ G_k`. -/
theorem isLocConstOn_of_cocycle_of_open_kernel (p : ℕ) (k Ω : Type) [Field k] [Field Ω]
    [Algebra k Ω] {K : IntermediateField k Ω} [Normal k K]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)]
    {H V : Subgroup (Ω ≃ₐ[k] Ω)} (hH : H ≤ K.fixingSubgroup)
    (hVopen : IsOpen (V : Set (Ω ≃ₐ[k] Ω)))
    {f : (Ω ≃ₐ[k] Ω) → ZMod p} (hcoc : SSGRoute.IsCocycleOn (SSGRoute.res k K) H f)
    (hzero : ∀ u ∈ V, u ∈ H → f u = 0) :
    SSGRoute.IsLocConstOn H f := by
  refine ⟨V, hVopen, fun g hg u hu huin => ?_⟩
  have h1 := hcoc g hg u huin
  have hres : SSGRoute.res k K g = 1 := res_eq_one_of_mem_fixingSubgroup (K := K) (hH hg)
  rw [h1, hzero u hu huin, hres, one_smul, add_zero]


/-! ## The mechanism: the rigidity of the axioms as a criterion on the arithmetic

The two rungs above combine into the following *criterion*.  If at a finite place `A` the level-`K`
local cohomology is one-dimensional (`dim H¹(H_A, ZMod p) = 1`, which for `A ∤ p` means
`μ_p ⊄ K_A`) and some class of a Selmer space `V_T` with `A` outside the `G_K`-classes of `T` has a
*non-zero* restriction to `H_A`, then the restrictions of the classes of `V_T` already fill up the
whole local cohomology, so the rung-2 argument kills every locally constant cocycle at `A` -- in
particular the non-zero one.  Hence `IsLocalTateSystem ∧ IsProductFormula` is *unsatisfiable* in
that configuration, and the realisation target holds there *vacuously*.

This is the exact form in which the arithmetic of a configuration can be checked against the axioms:
it says that a configuration can only support the axioms if every global class (unramified outside
`T`) splits completely at every place `A ∉ T`-classes with `dim H¹(H_A, ZMod p) = 1`.  In particular
the axioms are *never* satisfiable in a non-self-dual configuration in which such a class and such a
place exist; the remaining configurations are the self-dual ones, where the canonical local Tate
pairing exists and the counting inequality is the genuine (Poitou--Tate) content. -/

/-- **`selmerSpace` is monotone in the place set**: a class unramified outside `T` is a fortiori
unramified outside any larger set. -/
theorem selmerSpace_mono {p : ℕ} {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    {K : IntermediateField k Ω} [Normal k K] [DistribMulAction (K ≃ₐ[k] K) (ZMod p)]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)] {T T' : Finset (ValuationSubring Ω)}
    (h : T ⊆ T') : selmerSpace (p := p) K T ≤ selmerSpace (p := p) K T' := by
  intro b hb
  exact ⟨hb.1, hb.2.1,
    fun B hB hnc σ hσ => hb.2.2 B hB (fun A hA hconj => hnc A (h hA) hconj) σ hσ⟩

/-- **The first rung for two place sets at once.**  If `T₁` and `T₂` are place sets with `A₀` outside
the `G_K`-classes of both and with the union still a set of pairwise non-`G_K`-conjugate places, then
the local pairing at `A₀` pairs any class of `V_{T₁}` trivially with any class of `V_{T₂}`.  This is
the first rung applied to the union `T₁ ∪ T₂` (which is non-conjugate and contains both sets), and it
is what makes the localisation images of *different* Selmer spaces jointly isotropic. -/
theorem pair_zero_of_selmer_of_two_placeSets {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] {K : IntermediateField k Ω}
    [FiniteDimensional k K] [IsGalois k K]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    {pair : Subgroup (Ω ≃ₐ[k] Ω) → ((Ω ≃ₐ[k] Ω) → ZMod p) → ((Ω ≃ₐ[k] Ω) → ZMod p) → ZMod p}
    (hrec : IsProductFormula p k Ω K pair) {T₁ T₂ : Finset (ValuationSubring Ω)}
    (hT₁fin : ∀ A ∈ T₁, SSGRoute.IsFinPlace k A)
    (hT₂fin : ∀ A ∈ T₂, SSGRoute.IsFinPlace k A)
    (hT₁disj : ∀ A ∈ T₁, ∀ B ∈ T₁,
      (∃ τ ∈ K.fixingSubgroup, ∀ x : Ω, x ∈ B ↔ (τ⁻¹ : Ω ≃ₐ[k] Ω) • x ∈ A) → A = B)
    (hT₂disj : ∀ A ∈ T₂, ∀ B ∈ T₂,
      (∃ τ ∈ K.fixingSubgroup, ∀ x : Ω, x ∈ B ↔ (τ⁻¹ : Ω ≃ₐ[k] Ω) • x ∈ A) → A = B)
    (hcross : ∀ A ∈ T₁, ∀ B ∈ T₂,
      ¬ ∃ τ ∈ K.fixingSubgroup, ∀ x : Ω, x ∈ B ↔ (τ⁻¹ : Ω ≃ₐ[k] Ω) • x ∈ A)
    (A₀ : ValuationSubring Ω) (hA₀ : SSGRoute.IsFinPlace k A₀)
    (hdisj₁ : ∀ A ∈ T₁,
      ¬ ∃ τ ∈ K.fixingSubgroup, ∀ x : Ω, x ∈ A₀ ↔ (τ⁻¹ : Ω ≃ₐ[k] Ω) • x ∈ A)
    (hdisj₂ : ∀ A ∈ T₂,
      ¬ ∃ τ ∈ K.fixingSubgroup, ∀ x : Ω, x ∈ A₀ ↔ (τ⁻¹ : Ω ≃ₐ[k] Ω) • x ∈ A)
    {a b : (Ω ≃ₐ[k] Ω) → ZMod p} (ha : a ∈ selmerSpace (p := p) K T₁)
    (hb : b ∈ selmerSpace (p := p) K T₂) :
    pair (SSGRoute.decomp k A₀ ⊓ K.fixingSubgroup) a b = 0 := by
  classical
  have hsymm : ∀ {A B : ValuationSubring Ω},
      (∃ τ ∈ K.fixingSubgroup, ∀ x : Ω, x ∈ B ↔ (τ⁻¹ : Ω ≃ₐ[k] Ω) • x ∈ A) →
      (∃ τ ∈ K.fixingSubgroup, ∀ x : Ω, x ∈ A ↔ (τ⁻¹ : Ω ≃ₐ[k] Ω) • x ∈ B) := by
    rintro A B ⟨τ, hτ, hx⟩
    exact ⟨τ⁻¹, K.fixingSubgroup.inv_mem hτ, fun x => by simpa using (hx (τ • x)).symm⟩
  have hfin : ∀ A ∈ T₁ ∪ T₂, SSGRoute.IsFinPlace k A := by
    intro A hA
    rcases Finset.mem_union.mp hA with h | h
    · exact hT₁fin A h
    · exact hT₂fin A h
  have hdisjU : ∀ A ∈ T₁ ∪ T₂, ∀ B ∈ T₁ ∪ T₂,
      (∃ τ ∈ K.fixingSubgroup, ∀ x : Ω, x ∈ B ↔ (τ⁻¹ : Ω ≃ₐ[k] Ω) • x ∈ A) → A = B := by
    intro A hA B hB hconj
    rcases Finset.mem_union.mp hA with hA₁ | hA₂
    · rcases Finset.mem_union.mp hB with hB₁ | hB₂
      · exact hT₁disj A hA₁ B hB₁ hconj
      · exact absurd hconj (hcross A hA₁ B hB₂)
    · rcases Finset.mem_union.mp hB with hB₁ | hB₂
      · exact absurd (hsymm hconj) (hcross B hB₁ A hA₂)
      · exact hT₂disj A hA₂ B hB₂ hconj
  have hdisj : ∀ A ∈ T₁ ∪ T₂,
      ¬ ∃ τ ∈ K.fixingSubgroup, ∀ x : Ω, x ∈ A₀ ↔ (τ⁻¹ : Ω ≃ₐ[k] Ω) • x ∈ A := by
    intro A hA
    rcases Finset.mem_union.mp hA with h | h
    · exact hdisj₁ A h
    · exact hdisj₂ A h
  exact pair_zero_of_selmer_of_new_place p k Ω K pair hrec (T₁ ∪ T₂) hfin hdisjU A₀ hA₀ hdisj
    (selmerSpace_mono Finset.subset_union_left ha)
    (selmerSpace_mono Finset.subset_union_right hb)

/-- **The mechanism, in its sharpest local form: the axioms are inconsistent where a Selmer
localisation is non-trivial at a one-dimensional local group.**

Let `A` be a finite place which is not `G_K`-conjugate to any element of the place set `T`, suppose
the level-`K` local cohomology at `A` is one-dimensional
(`hDim : dim lcCocycleImage K H_A = 1`, equivalently `dim H¹(H_A, ZMod p) = 1`), and suppose that
*some* class `b` of the `T`-Selmer space `V_T` has a non-zero restriction to `H_A` (`hbne`).  Then
every class of `V_T` restricts to a multiple of the non-zero restriction of `b`, so the restrictions
of the classes of `V_T` fill the whole (one-dimensional) local cohomology; the second rung
(`eqOn_zero_of_surjective_selmer_restriction`) then shows that every locally constant `1`-cocycle on
`H_A` vanishes on `H_A` -- in particular `b`, contradicting `hbne`.  Consequently there is **no**
local Tate system at level `K` with the product formula.

Arithmetically: `hDim` holds whenever `A ∤ p` and `μ_p ⊄ K_A` (so `A` is a place of degree `1` over
`ℚ_ℓ` with `p ∤ |κ| - 1` in the simplest case), and `hbne` says that the class `b` does not split
completely at `A`.  So a configuration with a non-self-dual coefficient module in which some global
class fails to split somewhere at a place of the above kind cannot support the axioms: the target is
*vacuously* true there. -/
theorem false_of_selmer_restriction_ne_zero_of_finrank_one (p : ℕ) [Fact p.Prime] (k Ω : Type)
    [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    (T : Finset (ValuationSubring Ω)) (hTfin : ∀ A ∈ T, SSGRoute.IsFinPlace k A)
    (hTdisj : ∀ A ∈ T, ∀ B ∈ T,
      (∃ τ ∈ K.fixingSubgroup, ∀ x : Ω, x ∈ B ↔ (τ⁻¹ : Ω ≃ₐ[k] Ω) • x ∈ A) → A = B)
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (hdisj : ∀ A' ∈ T,
      ¬ ∃ τ ∈ K.fixingSubgroup, ∀ x : Ω, x ∈ A ↔ (τ⁻¹ : Ω ≃ₐ[k] Ω) • x ∈ A')
    (hDim : Module.finrank (ZMod p)
        ↥(lcCocycleImage (p := p) K (SSGRoute.decomp k A ⊓ K.fixingSubgroup)) = 1)
    (pair : Subgroup (Ω ≃ₐ[k] Ω) → ((Ω ≃ₐ[k] Ω) → ZMod p) → ((Ω ≃ₐ[k] Ω) → ZMod p) → ZMod p)
    (hpair : IsLocalTateSystem p k Ω K pair)
    (hrec : IsProductFormula p k Ω K pair)
    {b : (Ω ≃ₐ[k] Ω) → ZMod p} (hb : b ∈ selmerSpace (p := p) K T)
    (hbne : ∃ g ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, b g ≠ 0) :
    False := by
  classical
  haveI hfinite : Finite ↥(lcCocycleImage (p := p) K
      (SSGRoute.decomp k A ⊓ K.fixingSubgroup)) :=
    finite_lcCocycleImage (p := p) (K := K) (hA := hA)
  haveI hmodfin : Module.Finite (ZMod p) ↥(lcCocycleImage (p := p) K
      (SSGRoute.decomp k A ⊓ K.fixingSubgroup)) := Module.Finite.of_finite
  -- the localisation of the `T`-Selmer space is surjective onto the one-dimensional local space
  have hsurj : ∀ f : (Ω ≃ₐ[k] Ω) → ZMod p,
      SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A ⊓ K.fixingSubgroup) f →
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A ⊓ K.fixingSubgroup) f →
      ∃ b' ∈ selmerSpace (p := p) K T,
        ∀ g ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, b' g = f g := by
    intro f hf1 hf2
    have hbC : b ∈ localCocycle (p := p) K (SSGRoute.decomp k A ⊓ K.fixingSubgroup) :=
      ⟨isCocycleOn_of_le inf_le_right hb.1, isLocConstOn_of_le inf_le_right hb.2.1⟩
    have hfC : f ∈ localCocycle (p := p) K (SSGRoute.decomp k A ⊓ K.fixingSubgroup) :=
      ⟨hf1, hf2⟩
    have hz : restrictToSub (p := p) (SSGRoute.decomp k A ⊓ K.fixingSubgroup) b ∈
        lcCocycleImage (p := p) K (SSGRoute.decomp k A ⊓ K.fixingSubgroup) :=
      Submodule.mem_map.mpr ⟨b, hbC, rfl⟩
    have hy : restrictToSub (p := p) (SSGRoute.decomp k A ⊓ K.fixingSubgroup) f ∈
        lcCocycleImage (p := p) K (SSGRoute.decomp k A ⊓ K.fixingSubgroup) :=
      Submodule.mem_map.mpr ⟨f, hfC, rfl⟩
    have hz0 : (⟨restrictToSub (p := p) (SSGRoute.decomp k A ⊓ K.fixingSubgroup) b, hz⟩ :
        ↥(lcCocycleImage (p := p) K (SSGRoute.decomp k A ⊓ K.fixingSubgroup))) ≠ 0 := by
      intro hzero
      obtain ⟨g, hg, hgne⟩ := hbne
      have h2 := congrArg (fun x : ↥(lcCocycleImage (p := p) K
        (SSGRoute.decomp k A ⊓ K.fixingSubgroup)) =>
          (x : ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup) → ZMod p) ⟨g, hg⟩) hzero
      exact hgne (by simpa [restrictToSub_apply] using h2)
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero'
      (⟨restrictToSub (p := p) (SSGRoute.decomp k A ⊓ K.fixingSubgroup) b, hz⟩ :
        ↥(lcCocycleImage (p := p) K (SSGRoute.decomp k A ⊓ K.fixingSubgroup))) hz0).mp hDim
      (⟨restrictToSub (p := p) (SSGRoute.decomp k A ⊓ K.fixingSubgroup) f, hy⟩ :
        ↥(lcCocycleImage (p := p) K (SSGRoute.decomp k A ⊓ K.fixingSubgroup)))
    refine ⟨c • b, Submodule.smul_mem _ c hb, fun g hg => ?_⟩
    have h1 := congrArg (fun x : ↥(lcCocycleImage (p := p) K
      (SSGRoute.decomp k A ⊓ K.fixingSubgroup)) =>
        (x : ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup) → ZMod p) ⟨g, hg⟩) hc
    simpa [restrictToSub_apply, Pi.smul_apply] using h1
  have hzero := eqOn_zero_of_surjective_selmer_restriction p k Ω K pair hpair hrec T hTfin
    hTdisj A hA hdisj hsurj b
    (isCocycleOn_of_le inf_le_right hb.1) (isLocConstOn_of_le inf_le_right hb.2.1)
  obtain ⟨g, hg, hgne⟩ := hbne
  exact hgne (hzero g hg)

/-- **The criterion in the `H1loc`-dimension form consumed by the arithmetic lanes.**

`finrank_lcCocycleImage_eq_H1loc` identifies the dimension of the local cocycle space
`lcCocycleImage K H_A` with that of `H1loc p k Ω K (ZMod p) H_A`; the arithmetic of a place produces
the latter (e.g. `PTCore.finrank_H1loc_triv_eq`, `PTdualControl.finrank_H1loc_triv_levelK`), so this
restatement of `false_of_selmer_restriction_ne_zero_of_finrank_one` can be applied without
re-deriving the identification. -/
theorem false_of_H1loc_finrank_one_of_selmer_restriction_ne_zero (p : ℕ) [Fact p.Prime]
    (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    (T : Finset (ValuationSubring Ω)) (hTfin : ∀ A ∈ T, SSGRoute.IsFinPlace k A)
    (hTdisj : ∀ A ∈ T, ∀ B ∈ T,
      (∃ τ ∈ K.fixingSubgroup, ∀ x : Ω, x ∈ B ↔ (τ⁻¹ : Ω ≃ₐ[k] Ω) • x ∈ A) → A = B)
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (hdisj : ∀ A' ∈ T,
      ¬ ∃ τ ∈ K.fixingSubgroup, ∀ x : Ω, x ∈ A ↔ (τ⁻¹ : Ω ≃ₐ[k] Ω) • x ∈ A')
    (hDim : Module.finrank (ZMod p)
        (Work.SSGRoute.H1loc p k Ω K (ZMod p) (SSGRoute.decomp k A ⊓ K.fixingSubgroup)) = 1)
    (pair : Subgroup (Ω ≃ₐ[k] Ω) → ((Ω ≃ₐ[k] Ω) → ZMod p) → ((Ω ≃ₐ[k] Ω) → ZMod p) → ZMod p)
    (hpair : IsLocalTateSystem p k Ω K pair)
    (hrec : IsProductFormula p k Ω K pair)
    {b : (Ω ≃ₐ[k] Ω) → ZMod p} (hb : b ∈ selmerSpace (p := p) K T)
    (hbne : ∃ g ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, b g ≠ 0) :
    False := by
  refine false_of_selmer_restriction_ne_zero_of_finrank_one p k Ω K T hTfin hTdisj A hA hdisj
    ?_ pair hpair hrec hb hbne
  rw [finrank_lcCocycleImage_eq_H1loc (p := p) (K := K)
    (H := SSGRoute.decomp k A ⊓ K.fixingSubgroup) inf_le_right]
  exact hDim
end Rigidity

end Sharpness

/-! ## The non-self-dual half: the axioms are inconsistent when `ζ_p ∉ K`

The criterion `false_of_selmer_restriction_ne_zero_of_finrank_one` above becomes a *vacuity theorem*
as soon as it is fed the two arithmetic facts of a non-self-dual configuration:

* a non-zero class `b` of the level-`K` Selmer space `V_T` (`hV` below; supplied by
  `Work.SSGRoute.ZDataMup.exists_nonzero_selmer_of_covers_p` for place sets covering the places
  above `p` -- the first layer of the cyclotomic `Z_p`-extension of `K` is a degree-`p` extension
  ramified only above `p`);
* a place `A` outside the `G_K`-classes of `T` at which `b` is non-split and whose level-`K` local
  cohomology is one-dimensional -- this is
  `Work.SSGRoute.ZDataMup.exists_nonsplit_place_of_selmer` (proved), imported here in the
  instance-variable shape as `..._proj`.

Consequently, for `ζ_p ∉ K` *every* configuration satisfying the place-set hypotheses carries
inconsistent axioms `IsLocalTateSystem ∧ IsProductFormula`, and the target of this file holds there
vacuously.  The only configuration in which the target has real content is the self-dual one
(`ζ_p ∈ K`), where it is the level-`K` counting identity (Poitou--Tate, Milne ADT I.4.10). -/

section NonSelfDual

/-- **The axioms are inconsistent in every non-self-dual configuration** (`hV` exposed; see
`exists_nonzero_selmer_of_covers_p`). -/
theorem axioms_false_of_not_zeta_of_selmer (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (k Ω : Type)
    [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    (T : Finset (ValuationSubring Ω)) (hTfin : ∀ A ∈ T, SSGRoute.IsFinPlace k A)
    (hTdisj : ∀ A ∈ T, ∀ B ∈ T,
      (∃ τ ∈ K.fixingSubgroup, ∀ x : Ω, x ∈ B ↔ (τ⁻¹ : Ω ≃ₐ[k] Ω) • x ∈ A) → A = B)
    (hnoζ : ¬ ∃ ζ : ↥K, IsPrimitiveRoot ζ p)
    (hV : ∃ b : (Ω ≃ₐ[k] Ω) → ZMod p,
      b ∈ selmerSpace (p := p) K T ∧ ∃ g ∈ K.fixingSubgroup, b g ≠ 0)
    (pair : Subgroup (Ω ≃ₐ[k] Ω) → ((Ω ≃ₐ[k] Ω) → ZMod p) → ((Ω ≃ₐ[k] Ω) → ZMod p) → ZMod p)
    (hpair : Work.SSGRoute.ZDataMup.IsLocalTateSystem p k Ω K pair)
    (hrec : Work.SSGRoute.ZDataMup.IsProductFormula p k Ω K pair) :
    False := by
  obtain ⟨b, hb, hbne⟩ := hV
  obtain ⟨A, hA, hdisj, hbneA, hDim⟩ :=
    exists_nonsplit_place_of_selmer_proj p hp k Ω K T hTfin hTdisj hnoζ hb hbne
  exact false_of_selmer_restriction_ne_zero_of_finrank_one p k Ω K T hTfin hTdisj A hA hdisj hDim
    pair hpair hrec hb hbneA

end NonSelfDual

end Work.SSGRoute.ZDataMup
/-!
## Appendix (revised): the exact shape of the residual, and the rigidity of the axioms

### 1. The residual is the *Lagrangian* (counting) statement, and the axioms give the opposite half

Two *proved* facts pin the residual down completely.

* (`tatePoitou_h1_realisation_iff_counting`)  At a fixed configuration `(k, Ω, K, pair, T)`
  satisfying `hpair` and `hrec`, the conclusion of the target for *every* admissible datum is
  equivalent to the counting inequality `CountingInequality`, i.e. to `dim P ≤ 2 · dim W_T` where
  `P = ∏_{A ∈ T} H¹(decomp k A ⊓ G_K, ZMod p)` is the product of the local `H¹`s and `W_T` is the
  localisation image of the level-`K` Selmer space.

* (`sum_pairing_isotropy_le`, added below)  The axioms give the *reverse* inequality:
  `2 · dim W_T ≤ dim P`.  Indeed `hrec` (the product formula) makes `W_T` isotropic for the
  descended sum pairing `B̄` on `P` (`sum_pair_selmer_eq_zero`), the axiom `perfect` makes `B̄`
  non-degenerate (`ker B̄ = ⊥`), and the dimension count
  `finrank W + finrank W^⊥ = finrank V` for a form with trivial radical finishes.

Hence the content of the target is precisely the *equality* `2 · dim W_T = dim P`, i.e. the
Lagrangian property of the level-`K` localisation: the axioms give `W_T ⊆ W_T^⊥` and the target
needs `W_T^⊥ ⊆ W_T`.  This is the middle exactness of the level-`K` Poitou--Tate sequence
(Milne, *Arithmetic Duality Theorems*, I.4.10; NSW 8.6.8), and nothing in this workspace supplies
it: the sibling lanes `ZSplit.levelK_counting_identity`, `PT.pt_selmer_counting_identity`,
`PT.pt_counting_identity_h1` all carry it as a `sorry`.  The target's own `sorry` is exactly that
inequality.

### 2. Vacuity criterion (proved): the axioms are *rigid*

`not_exists_pair_of_isotropy_fails` (added below): if `2 · dim W_T > dim P`, then there is **no**
local Tate system at level `K` with the product formula at all.  So in every configuration whose
Selmer localisation is "too large" the target is true *vacuously*.  Together with the rigidity
rungs proved earlier in this file (`pair_zero_of_selmer_of_new_place`,
`eqOn_zero_of_surjective_selmer_restriction`) this is the formal mechanism by which the axioms can
only exist in configurations with a small Selmer localisation.

### 3. A retraction, and the honest open question

An earlier version of this appendix contained a "worked configuration in which the counting
inequality provably fails".  **Retracted.**  Those dimension computations are unreliable: the
`𝔽₃`-ranks involved are the ranks of ray class groups modulo the image of the global units, and a
recomputation contradicts the recorded values (for `k = ℚ`, `K = ℚ(√2)`, `p = 3`, `T = {𝔭 | 3}` one
has `[O_K^× : O_K^× ∩ (1 + 𝔭²)] = 8` — `ε^8 ≡ 1 mod 𝔭²`, while `ε^4 ≢ 1` — hence
`|Cl(𝔭²)| = 72/8 = 9` and the localisation of the Selmer space is *at least* `2`-dimensional, not
`1`-dimensional as recorded; the *local* dimension there is `dim H¹(K_𝔭, ZMod 3) = 3` since
`|K_𝔭^× / (K_𝔭^×)³| = 3^3`).  Nothing in this file should be read as asserting that
`CountingInequality` fails anywhere.

What is genuinely open is the following.

* In the *self-dual* situation `μ_p ⊆ K` (in particular for the intended instantiation
  `isMupZData_odd`, where `ζ_p ∈ K`), the coefficient module is its own Tate dual and the canonical
  local Tate pairings are admissible; the counting inequality is then Poitou--Tate's middle
  exactness at level `K`, still missing here.

* In the *non*-self-dual situations `μ_p ⊄ K`, the canonical cup-product pairing is *not* perfect
  (its radical is the kernel of `α ↦ α ∪ χ_cyc`), so admissibility of *some* pairing is a separate
  question.  The vacuity criterion of §2 gives the axioms-free conclusion whenever the Selmer
  localisation is too large; whether it is always too large in the configurations where
  `CountingInequality` fails is not known to us, and it is exactly the question that decides
  whether the target is true in the non-self-dual cases.

### 4. Correction (session 8): the local dimension, and the parity of `dim P`

`even_finrank_localDataSpace_quotient` (proved above, axiom-clean): if `ζ_p ∈ K` and `p` is odd,
then `dim P = finrank (localDataSpace K T ⧸ localVanish K T)` is **even**.  Proof:
`dim P = ∑_{A ∈ T} dim H¹(decomp k A ⊓ G_K, ZMod p)` (`finrank_localDataSpace_quotient`), and each
local term is even (`ZConstruction.even_finrank_H1loc_levelK`, whose input is the machine-checked
local count `NK.LocalInputs.natCard_KummerGroup_adicCompletion_eq_pow`:
`|κˣ/(κˣ)^p| = p ^ ([κ:ℚ_p] + 1 + δ)`, `δ = [μ_p ⊆ κ]`; here `|ℚ₃(ζ₃)ˣ/(ℚ₃(ζ₃)ˣ)³| = 3^{2+2} = 81`,
so the local dimension is `4`, not `3`).

Consequently, in the self-dual configuration `k = ℚ`, `K = ℚ(ζ₃)`, `p = 3`, `T = {v₃}`:
`dim P = 4`, `dim W_T = 2`, hence `2 · dim W_T = 4 = dim P`: the isotropy inequality
`sum_pairing_isotropy_le` is an *equality* there, the axioms are satisfiable, the counting
inequality `dim P ≤ 2 · dim W_T` holds *with equality*, and the gate is not vacuous.  (This corrects
the earlier `dim P = 3` of `NOTES_rigidity_open_question.md` §7.)

Nothing in this appendix changes the statement or the name of the target.
-/

/-!
## Appendix 5 (session 9): the mechanism, and the two obstructions

The three lemmas of the `Mechanism` section above are the formal content of the rigidity of the
axioms:

* `selmerSpace_mono` -- `V_T ⊆ V_{T'}` for `T ⊆ T'`;
* `pair_zero_of_selmer_of_two_placeSets` -- the first rung for two place sets at once, hence the
  joint isotropy of the images of different Selmer spaces;
* `false_of_selmer_restriction_ne_zero_of_finrank_one` -- **the criterion**: if at a finite place
  `A` outside the `G_K`-classes of `T` the level-`K` local cohomology is one-dimensional
  (`finrank (lcCocycleImage K H_A) = 1`) and some class `b ∈ V_T` has `b|H_A ≠ 0`, then
  `IsLocalTateSystem ∧ IsProductFormula` is *unsatisfiable*: the target holds there vacuously.

Consequences recorded in `NOTES_rigidity_open_question.md` §8:

1. the criterion can only bite at places `A ∤ p` with `μ_p ⊄ K_A`, since for `A | p` the local
   dimension is at least `2` while every class unramified at `A` localises into the one-dimensional
   unramified subspace;
2. the reference configuration `k = K = ℚ`, `p = 3`, `T = {v₂, v₃}` *does* fail the counting
   inequality (`dim P_T = 3 > 2 · dim W_T = 2`) and *is* killed by the criterion (the class of the
   cubic field of conductor `9`, `2` inert in it, `dim H¹(ℚ₂, Z/3) = 1`);
3. the target is therefore equivalent to the conjunction of two *independent* arithmetic inputs:
   the counting inequality in the self-dual configurations (the Lagrangian property of the
   level-`K` localisation, i.e. level-`K` Poitou--Tate -- the frontier of the lanes
   `ZSplit.levelK_counting_identity` / `PT.pt_selmer_counting_identity`), and the Chebotarev-type
   existence of a non-split class at a place of the kind in 1. for the remaining configurations.
   The second input is *not* obtainable in this workspace at present: its available form
   (`NK.Reconstruct.ChebotarevDensityInput`) is derived from Artin reciprocity, whose file still
   carries a `sorry`.  Hence the target is neither provable from the trusted content nor false.
-/
