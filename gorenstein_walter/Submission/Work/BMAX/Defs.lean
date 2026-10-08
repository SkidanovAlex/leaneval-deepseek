/-
# AREA BMAX — Bender 1970, §1.1, §1.6, §1.7  ( = Bender 1981, Lemma 2.3 )

This is the definition module of the area `BMAX` of the `gorenstein_walter` project
(route: Bender 1981 + Bender–Glauberman 1981, Feit–Thompson available).

## What the area is about

Bender 1981 (*Finite groups with dihedral Sylow 2-subgroups*, J. Algebra **70** (1981),
216–228), Lemma 2.3, is the only maximal-subgroup lemma of §2 that is *not* proved
from first principles in B81: it is quoted as "see [1, 1.6/7]", i.e. from

  H. Bender, *On groups with abelian Sylow 2-subgroups*, Math. Z. **117** (1970),
  164–176, §1.1 (Thompson lemma), §1.6, §1.7.

B81 Lemma 2.3 states (with `A ⇝ B` meaning `N_{F*(A)}(X) ≤ B` for some `X ≤ F(A)`,
and `π = π(F(A))`):

  Let `Ĥ ⇝ M`. Then
  (i)   `F_π(M) ≤ Ĥ` unless `F*(Ĥ)` is a p-group (p a prime);
  (ii)  `F_{π'}(M) ∩ Ĥ = 1` (thus `t` inverts `F_{π'}(M)` if `t ∈ M`);
  (iii) if moreover `M ⇝ Ĥ`, then `Ĥ = M` unless `F*(Ĥ)` and `F*(M)` are p-groups
        for the same prime p.

The deliverable of this area is exactly that conjunction, in the vocabulary of
`Submission/Work/_design_gw/Contracts2.lean`, i.e. the Prop

  `Work.GW2.Lemma23Prop`

with `LocalToolkit` as its input.  `Lemma23Prop` is used by the CORE areas
(`CORE2A` Lemmas 2.4/2.5, `CORE2B` Lemmas 2.7/2.8 and Theorem 2.6).

## Contents of this file

* The vocabulary of the project is taken **by import** from `Submission.Work.GLUE.Defs`,
  which reproduces every definition of `Contracts2.lean` verbatim in namespace
  `Work.GW2` (`Lemma23Prop`, `LocalToolkit`, `BenderCtx`, `BenderSetup`, `BRel`,
  `fstarIn`, `fittingIn`, `primesOf`, …).  Nothing is re-declared here: re-declaring
  it would clash with GLUE when both modules are imported, and by definitional
  transparency `Work.GW2.X` *is* `GW2.X` for every definition `X` of the contract file.
* Bender's two input lemmas 1.6 and 1.7, and the Thompson lemma 1.1 they use, are
  *stated* here as Props (`Work.GW2.Bender16Prop`, `Work.GW2.Bender17Prop`,
  `Work.GW2.ThompsonLemmaProp`) in the project's vocabulary, together with the bundle
  `Work.GW2.BMAXToolkit`.

See `Submission/Work/BMAX/NOTES_BMAX.md` for the mathematical discussion (including the
exact correspondence between Bender's statements and the Props below) and
`Submission/Work/BMAX/Lemma23.lean` for the derivation of `Lemma23Prop`.
-/
import Submission.Work.ASM.Defs
import Submission.OddOrder.Isaacs.Ch04_Commutators.Main

open scoped MatrixGroups

namespace Work.GW2

open Subgroup

/-! ## 0. Auxiliary vocabulary of the area -/

section Vocabulary

variable {G : Type*} [Group G]

/-- The centre of a subgroup, as a subgroup of the ambient group. -/
def zcenterIn (K : Subgroup G) : Subgroup G where
  carrier := {x | x ∈ K ∧ ∀ y ∈ K, x * y = y * x}
  mul_mem' := by
    rintro x z ⟨hxK, hx⟩ ⟨hzK, hz⟩
    refine ⟨K.mul_mem hxK hzK, fun y hy => ?_⟩
    calc x * z * y = x * (z * y) := mul_assoc x z y
      _ = x * (y * z) := by rw [hz y hy]
      _ = x * y * z := (mul_assoc x y z).symm
      _ = y * x * z := by rw [hx y hy]
      _ = y * (x * z) := mul_assoc y x z
  one_mem' := by
    refine ⟨K.one_mem, fun y _ => ?_⟩
    rw [one_mul, mul_one]
  inv_mem' := by
    rintro x ⟨hxK, hx⟩
    refine ⟨K.inv_mem hxK, fun y hy => ?_⟩
    calc x⁻¹ * y = (y⁻¹ * x)⁻¹ := by rw [mul_inv_rev, inv_inv]
      _ = (x * y⁻¹)⁻¹ := by rw [hx y⁻¹ (K.inv_mem hy)]
      _ = y * x⁻¹ := by rw [mul_inv_rev, inv_inv]

theorem mem_zcenterIn {K : Subgroup G} {x : G} :
    x ∈ zcenterIn K ↔ x ∈ K ∧ ∀ y ∈ K, x * y = y * x := Iff.rfl

theorem zcenterIn_le (K : Subgroup G) : zcenterIn K ≤ K := fun _ hx => hx.1

/-- The set of primes dividing the order of `F(A)`, i.e. Bender's `π(F(A))`.
(`Work.GW2.BenderSetup.pi` is `primesOf (fittingIn B.Hhat)` by definition, so
`primesOf (fittingIn A)` is exactly the `π` of Bender 1981 Lemma 2.3 for `A = Ĥ`.) -/
theorem mem_primesOf {K : Subgroup G} {p : ℕ} :
    p ∈ primesOf K ↔ p ∈ (Nat.card K).primeFactors := Iff.rfl

end Vocabulary

/-! ## 1. Bender 1970, 1.1 (Thompson lemma)

Bender uses 1.1 twice in the proof of 1.7.  The printed statement (Math. Z. **117** (1970),
p. 165) is

  *"Let a product of a p-group `P` and a group `K` act on a p-group `B`, p a prime.
  Assume `K = O^p(K)`, `[P,K] = 1 = [C_B(P), K]`.  Then `K` centralizes `B`."*

The scan at this point is an OCR of a 1970 typescript and the hypotheses of the printed
statement are not faithfully recoverable from it.  The form below is the *standard
Thompson `P × K` lemma* in the shape in which the odd-order library has it
(`Submission.OddOrder.Isaacs.Ch04_Commutators.Main.BaerTrick`,
`actionCommutator_prodRight_eq_bot_of_prodRight_fixes_actionCommutator_prodLeft`,
the last step of Isaacs' Theorem 4.31): `P` and `K` act through a homomorphism
`φ : P × K →* MulAut B` (so their actions commute — Bender's `[P,K] = 1`), `B` and `P` are
p-groups, `K` is a p'-group (Bender's `K = O^p(K)` case), and `K` fixes the `P`-fixed
points of `B` (Bender's `[C_B(P), K] = 1`) *and* the commutator `[B,P]`; then `K` acts
trivially on `B`.  The `[B,P]`-hypothesis is the "obviously, `[O_q(B) ∩ A, O^p(S)] = 1`"
step of Bender's proof of 1.7; it is the one hypothesis that the odd-order library's
proof needs and that our OCR of 1.1 does not exhibit.

This Prop is **proved** in this area — see `Submission/Work/BMAX/Thompson.lean`, whose
theorem `Work.GW2.thompsonLemma11 : ThompsonLemmaProp` simply cites the library result.
So `ThompsonLemmaProp` is not an assumption of the area: it is one of its theorems. -/
def ThompsonLemmaProp : Prop :=
  ∀ (B : Type) [Group B] [Finite B] (p : ℕ) [Fact p.Prime]
    (P K : Type) [Group P] [Group K] [Finite K] (φ : P × K →* MulAut B),
    IsPGroup p B → IsPGroup p P → Nat.Coprime p (Nat.card K) →
    (∀ k : K, ∀ b : B, (∀ x : P, φ (x, 1) b = b) → φ (1, k) b = b) →
    (∀ k : K, ∀ b ∈ OddOrder.Isaacs.Ch04.actionCommutator (φ.comp (OddOrder.Isaacs.Ch04.prodLeftHom P K)),
      φ (1, k) b = b) →
    ∀ (k : K) (b : B), φ (1, k) b = b

/-! ## 2. Derived vocabulary: the `D`-group point of view -/

/-- **Sylow-2 heredity.**  Every subgroup of a group with cyclic or dihedral Sylow
2-subgroups again has cyclic or dihedral Sylow 2-subgroups.  This is the fact Bender uses
without comment when he says that *all proper subgroups* of the minimal counterexample are
`D`-groups (B81 §2, first line); it is `DS1` (`DihOrCycSubgroupProp`) of the blueprint.  It is
proved in this area as `Work.BMAX.DihOrCycSub`. -/
def DihOrCycSubgroupProp : Prop :=
  ∀ (X : Type) [Group X] [Finite X], DihOrCycSylow X → ∀ K : Subgroup X, DihOrCycSylow K

/-! ## 3. Bender 1970, 1.6  (in the `D`-group setting)

  *"Let `A` and `B` be different maximal subgroups of a simple group `G` such that
  `F*(A) ≤ B` and `F*(B) ≤ A`.  Then `F*(A)` and `F*(B)` are p-groups (for the same
  prime p)."*

`F*` here is `Work.GW2.fstar`, and `…In A` is the corresponding subgroup of the ambient
group (the convention of the contract file).

**Why the `IsDGroup` hypotheses.**  The contract's `layer X` is the join of the *normal*
quasisimple subgroups of `X`, whereas Bender's `E(X)` is the join of the *components*
(subnormal quasisimple subgroups); the two agree as soon as `X` has at most one component,
in particular for `D`-groups — the case in which B81 invokes these lemmas (all proper
subgroups of the minimal counterexample are `D`-groups, and `LayerUniqueProp` is the
blueprint's name for "there is at most one component").  Without the hypothesis the
statement is **false**: see `NOTES_FALSE_Bender17Prop.md` for an explicit counterexample
(`A = A₁₀ ∩ (S₅ ≀ C₂) ≅ (A₅ × A₅):C₄` has `layer A = fitting A = ⊥` in our sense while
Bender's `E(A) = A₅ × A₅`, so `BRel A B` is vacuous and Lemma 2.3(ii) fails).

The `D`-group hypotheses are *not* extra inputs of the area: `Lemma23Prop`'s inputs are
`LocalToolkit` and `BenderCtx`, and in `BenderCtx` the groups `Ĥ` and `M` are `D`-groups by
`BenderCtx.ih`, `BenderSetup.card_Hhat_lt_card_G`, `IsCoatom.card_lt_card` and the
Sylow-2 heredity `DihOrCycSubgroupProp` above. -/
def Bender16Prop : Prop :=
  ∀ (T : LocalToolkit) (G : Type) [Group G] [Finite G], IsSimpleGroup G →
    ∀ A B : Subgroup G, DihOrCycSylow A → IsDGroup A → DihOrCycSylow B → IsDGroup B →
      IsCoatom A → IsCoatom B → A ≠ B →
      fstarIn A ≤ B → fstarIn B ≤ A →
      ∃ p : ℕ, p.Prime ∧ IsPGroup p (fstarIn A) ∧ IsPGroup p (fstarIn B)

/-! ## 4. Bender 1970, 1.7 (in the `D`-group setting)

  *"Let `A` be a maximal subgroup of a simple group `G`, `S` a subnormal subgroup of
  `F*(A)` such that `C_{F*(A)}(S) ≤ S`, and `S ≤ B ≤ G`.  Then*
  *(i) `O_q(B) ∩ A = 1` for `q ∈ π(F(A))'`;*
  *(ii) if `p ∈ π(F(A))`, then `[O_p(B), O^p(F*(A))] = 1`.*
  *Furthermore, if `B` is a maximal subgroup of `G` and if `|π(F*(A))| ≥ 2` or
  `|π(F*(B))| ≥ 2`, then each of the following conditions guarantees `A = B`:*
  *(iii) `A` contains a subnormal subgroup `S` of `F*(B)` such that `C_{F*(B)}(S) ≤ S`."*

Bender 1981 quotes precisely this, together with 1.6, as Lemma 2.3.  In the form used in
B81 three things change, which is why the Prop below is stated in our vocabulary rather
than in the 1970 notation:

* the hypothesis `S ≤ B` is replaced by the relation `A ⇝ B` (`Work.GW2.BRel`), whose
  witnessing subgroup `S = N_{F*(A)}(X)` (for `X ≤ F(A)`) automatically satisfies
  `S ≤ F*(A)` subnormal with `C_{F*(A)}(S) ≤ S` (here `C(F*(A)) ≤ F*(A)`, i.e. the
  `FStarProp` of the toolkit, is what is needed);
* `π(F(A))` is written out as `primesOf (fittingIn A)`, and `O_q`/`F_π`/`F_{π'}`
  are the contract's `pCore`/`fittingPiIn`;
* the "furthermore" clause (iii) is stated in the contrapositive form that B81's Lemma 2.3
  (iii) has — the "same p" is supplied by 1.6, applied after (i)+(ii) give
  `F*(A) ≤ B` and `F*(B) ≤ A`:
  *"if we also have `M ⇝ Ĥ`, then `Ĥ = M` unless `F*(Ĥ)` and `F*(M)` are p-groups
  (p a prime)."*

The `IsDGroup`/`DihOrCycSylow` hypotheses are those of 1.6 above. -/
def Bender17Prop : Prop :=
  ∀ (T : LocalToolkit) (G : Type) [Group G] [Finite G], IsSimpleGroup G →
    ∀ A B : Subgroup G, DihOrCycSylow A → IsDGroup A → DihOrCycSylow B → IsDGroup B →
      IsCoatom A → B ≠ ⊤ → BRel A B →
      ((¬ ∃ p : ℕ, p.Prime ∧ IsPGroup p (fstarIn A)) →
          fittingPiIn (primesOf (fittingIn A)) B ≤ A) ∧
      (fittingPiIn (primesOf (fittingIn A))ᶜ B ⊓ A = ⊥) ∧
      (IsCoatom B → BRel B A →
        ((¬ ∃ p : ℕ, p.Prime ∧ IsPGroup p (fstarIn A)) ∨
          (¬ ∃ p : ℕ, p.Prime ∧ IsPGroup p (fstarIn B))) →
        fstarIn A ≤ B ∧ fstarIn B ≤ A)

/-! ## 5. The two halves of 1.7, as separate Props

`Bender17Prop` is split into `Bender17MainProp` (clauses (i) and (ii), which one proof
produces together) and `Bender17iiiProp` (the intermediate `F*(A) ≤ B` of Bender's proof
of 1.7(iii), symmetrized: applying (i)+(ii) to the pair `(B,A)` gives
`F*(A) ≤ B ∧ F*(B) ≤ A`, and then 1.6 gives `A = B` in the case excluded by B81 Lemma
2.3(iii)).  `Bender17Prop_of_parts` reassembles them. -/

/-- Bender 1970, 1.7(i)+(ii) in the form of Bender 1981, Lemma 2.3(i)+(ii):
`F_π(M) ≤ Ĥ` (unless `F*(Ĥ)` is a p-group) and `F_{π'}(M) ∩ Ĥ = 1`. -/
def Bender17MainProp : Prop :=
  ∀ (T : LocalToolkit) (G : Type) [Group G] [Finite G], IsSimpleGroup G →
    ∀ A B : Subgroup G, DihOrCycSylow A → IsDGroup A → DihOrCycSylow B → IsDGroup B →
      IsCoatom A → B ≠ ⊤ → BRel A B →
      ((¬ ∃ p : ℕ, p.Prime ∧ IsPGroup p (fstarIn A)) →
          fittingPiIn (primesOf (fittingIn A)) B ≤ A) ∧
      (fittingPiIn (primesOf (fittingIn A))ᶜ B ⊓ A = ⊥)

/-- Bender 1970, 1.7(iii): `F*(A) ≤ B` and `F*(B) ≤ A` when both relations hold **and at
least one of `F*(A)`, `F*(B)` is not a p-group**.

The side condition is Bender's: his 1.7(iii) is stated under "`|π(F*(A))| ≥ 2` or
`|π(F*(B))| ≥ 2`", and B81's Lemma 2.3(iii) reads "`Ĥ = M` *unless* `F*(Ĥ)` and `F*(M)`
are p-groups".  It is not removable: if both `F*` are p-groups the conclusion `F*(A) ≤ B`
is false in general — e.g. `G = PSL(2,31)`, `A`, `B` distinct Sylow 2-subgroups
(`≅ D₃₂`) that are maximal with `A ∩ B ⊇ C₂ × C₂`: both relations hold, both `F*` are
2-groups, but `F*(A) = A ≰ B` (GAP-verified).  The case both are p-groups is the one in
which B81's Lemma 2.4 (Glauberman's `Z(J)`-theorem) gives `A = B`; in the derivation of
`Lemma23Prop` the *prime equality* needed there is supplied by `FstarSamePrimeProp`. -/
def Bender17iiiProp : Prop :=
  ∀ (T : LocalToolkit) (G : Type) [Group G] [Finite G], IsSimpleGroup G →
    ∀ A B : Subgroup G, DihOrCycSylow A → IsDGroup A → DihOrCycSylow B → IsDGroup B →
      IsCoatom A → B ≠ ⊤ → BRel A B → IsCoatom B → BRel B A →
      ((¬ ∃ p : ℕ, p.Prime ∧ IsPGroup p (fstarIn A)) ∨
        (¬ ∃ p : ℕ, p.Prime ∧ IsPGroup p (fstarIn B))) →
      fstarIn A ≤ B ∧ fstarIn B ≤ A

/-- **The `π`-equality step of Bender 1970, 1.6, in the `⇝`-setting.**  If `A ≠ B` are
coatomic `D`-groups with `A ⇝ B`, `B ⇝ A`, and both `F*(A)`, `F*(B)` are non-trivial
p-groups, then the two primes agree.

This is the only piece of Lemma 2.3(iii) that does not follow from 1.7(i)+(ii) plus 1.6:
in the case both `F*` are p-groups the intermediate `F*(A) ≤ B` of 1.7(iii) is *false*
(see `Bender17iiiProp` above), and the prime equality is what one gets instead — Bender's
own proof of 1.6 derives `π(F(A)) = π(F(B))` from "subgroups of coprime order of `F(A)`
and `F(B)` centralize each other"; with the relation `⇝` in place of the inclusions it is
derived in `BMAX/FstarSamePrime.lean` from Lemma 2.3(i)+(ii) applied to the pair `(B,A)`
(the non-trivial centre of `F*(A)` is a q-subgroup of `B` for every prime `q | |F*(A)|`,
and `F_{π'}(B) ∩ A = 1` says it cannot be a π'-subgroup of `F(B)`). -/
def FstarSamePrimeProp : Prop :=
  ∀ (T : LocalToolkit) (G : Type) [Group G] [Finite G], IsSimpleGroup G →
    ∀ A B : Subgroup G, DihOrCycSylow A → IsDGroup A → DihOrCycSylow B → IsDGroup B →
      IsCoatom A → B ≠ ⊤ → BRel A B → IsCoatom B → BRel B A → A ≠ B →
      fstarIn A ≠ ⊥ → fstarIn B ≠ ⊥ →
      ∀ p q : ℕ, p.Prime → q.Prime → IsPGroup p (fstarIn A) → IsPGroup q (fstarIn B) → p = q

theorem Bender17Prop_of_parts (h1 : Bender17MainProp) (h3 : Bender17iiiProp) :
    Bender17Prop := by
  intro T G _ _ hG A B hA hDA hB hDB hcA hne hrel
  exact ⟨(h1 T G hG A B hA hDA hB hDB hcA hne hrel).1,
         (h1 T G hG A B hA hDA hB hDB hcA hne hrel).2,
         fun hcB hrel' hside => h3 T G hG A B hA hDA hB hDB hcA hne hrel hcB hrel' hside⟩

/-! ## 6. The area's input bundle

`BMAXToolkit` collects the Props above.  The area's deliverable is

  `Work.GW2.lemma23 (T : LocalToolkit) (K : BMAXToolkit) : Lemma23Prop`

(`Submission/Work/BMAX/Lemma23.lean`), i.e. exactly the contract's `lemma23`, with the
Bender-1970 inputs made explicit.  `Bender16Prop` and `Bender17Prop` are theorems of
Bender 1970 for `D`-groups and do not depend on Gorenstein–Walter, so the interface is not
circular; they are delegated as separate deliverables of this area. -/
/-- **The layer case of Bender's local analysis** — *not needed* since GW design pass 18:
the mixed case in which it was used is empty (`BMAX/Core18Aux.lean`,
`Work.BMAX.layerIn_eq_bot_of_mixed`, and `BMAX/Core18Bender17iiiCond.lean` derive
`Bender17iiiProp` without it).  The statement is kept for the record (it is also what
`Work.CORE2A.dedekindLayerDGroup` stubs, and it is likely true but not in any source).

(The old docstring follows.)

Bender's proof of 1970, 1.7(iii) needs, in the case `F(A) = O_p(A)` is a `p`-group while
`E(A) ≠ 1`, that `F(A)` is a *Dedekind* group (every subgroup of `F(A)` is normal in it) —
equivalently `F(A)` abelian or Hamiltonian.  It is the only piece of the derivation of
`Bender17iiiProp` that does not follow from 1.7(i)+(ii) (applied both ways), 1.6 and the
π-equality step, and no source states it for a *single* maximal subgroup: Bender 1.6/1.7
are about a *pair* of maximal subgroups.  GAP scans over all maximal subgroups of ~130
simple groups found no counterexample.  See `BMAX/Bender17iiiCond.lean`
(`Bender17iiiCond_of_layer : LayerDedekindProp → Bender17iiiProp`). -/
def LayerDedekindProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (hG : IsSimpleGroup G) (A : Subgroup G) (hA : IsCoatom A)
    (hp : ∃ p : ℕ, p.Prime ∧ IsPGroup p (fittingIn A)) (hL : layerIn A ≠ ⊥),
    ∀ X : Subgroup G, X ≤ fittingIn A → fittingIn A ≤ normalizer (X : Set G)

structure BMAXToolkit : Prop where
  /-- Bender 1970, 1.1 (Thompson lemma). -/
  t11 : ThompsonLemmaProp
  /-- Bender 1970, 1.6. -/
  b16 : Bender16Prop
  /-- Bender 1970, 1.7. -/
  b17 : Bender17Prop
  /-- The `π`-equality step of Bender 1970, 1.6 (see `FstarSamePrimeProp`). -/
  sameP : FstarSamePrimeProp

/-- Build the toolkit from the Thompson lemma, 1.6, the two halves of 1.7 and the
`π`-equality step of 1.6. -/
theorem BMAXToolkit.of_parts (h11 : ThompsonLemmaProp) (h16 : Bender16Prop)
    (h1 : Bender17MainProp) (h3 : Bender17iiiProp) (hsp : FstarSamePrimeProp) :
    BMAXToolkit :=
  ⟨h11, h16, Bender17Prop_of_parts h1 h3, hsp⟩

end Work.GW2
