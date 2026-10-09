/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The local inputs: vocabulary and named statements

This file collects the *vocabulary* and the *named statements* of local arithmetic that
Shafarevich's theorem uses, in the form of `Prop`-valued definitions so that a caller can name
them as hypotheses.  Anything that could be proved with the current library is proved in the
sibling files of this directory (`Work.LocalFields.*`); the definitions here record the deep
inputs whose proofs are far beyond the current library, with their precise classical content
described in the docstrings.

## Contents

* `Work.LocalFields.AbsoluteGaloisGroup` : the absolute Galois group of a field.
* `Work.LocalFields.IsPadicField` : a local field of residue characteristic `p`.
* `Work.LocalFields.IsLocalFieldExtension`, `Work.LocalFields.IsUnramifiedLocalExtension` :
  extensions of local fields and the unramified condition `[l:k] = [κ_l:κ_k]`.
* `Work.LocalFields.HasUnramifiedExtensionOfDegree` : the unique unramified extension of degree
  `n` and its Frobenius.
* `Work.LocalFields.DemushkinProPStructure` : the structure of the maximal pro-`p` quotient of
  `Gal(k̄/k)` for a `p`-adic field `k`.
* `Work.LocalFields.DecompositionGroupIsLocalGaloisGroup` : `Gal(L_w/K_v) ≅ D_w`
  (this one is *proved*: see
  `Work.LocalFields.nonempty_localGaloisGroup_mulEquiv_decompositionGroup`).
* `Work.LocalFields.IsProP`, `Work.LocalFields.DemushkinProPStructure` : the structure of the
  maximal pro-`p` quotient of `Gal(k̄/k)` for a `p`-adic field.

The local/global embedding-problem inputs live in `Submission/Work/LocalFields/EmbeddingProblem.lean`
(`Work.LocalFields.LocalEmbeddingProblemInput`, `Work.LocalFields.HasEmbeddingPropertyWithAbelianKernel`).
-/
import Submission.Work.LocalFields.Basic
import Submission.Work.LocalFields.Decomposition
import Submission.Work.LocalFields.CompletionLocalField
import Submission.Work.LocalFields.CompletionExtension
import Submission.Work.LocalFields.Ramification
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.LocalFields

open scoped NumberField Pointwise Valued WithZero

/-! ## The absolute Galois group -/

/-- The **absolute Galois group** of a field `k`, realised as the `k`-automorphisms of an
algebraic closure of `k`. -/
abbrev AbsoluteGaloisGroup (k : Type*) [Field k] : Type _ :=
  (AlgebraicClosure k) ≃ₐ[k] (AlgebraicClosure k)

/-- A `p`-adic field: a non-archimedean local field of residue characteristic `p`. -/
def IsPadicField (k : Type*) [Field k] [Valued k (WithZero (Multiplicative ℤ))] [IsLocalField k]
    (p : ℕ) : Prop :=
  Nat.Prime p ∧ ringChar (Valued.ResidueField k) = p

/-- A `p`-adic field is a local field whose residue field has characteristic `p`. -/
theorem IsPadicField.prime {k : Type*} [Field k] [Valued k (WithZero (Multiplicative ℤ))]
    [IsLocalField k] {p : ℕ} (h : IsPadicField k p) : Nat.Prime p := h.1

/-! ## Extensions of local fields -/

/-- An extension `l/k` of non-archimedean local fields, where the valuation of `l` extends the
valuation of `k` (in the sense of `Valuation.HasExtension`). -/
class IsLocalFieldExtension (k : Type*) [Field k] [Valued k (WithZero (Multiplicative ℤ))]
    [IsLocalField k] (l : Type*) [Field l] [Valued l (WithZero (Multiplicative ℤ))]
    [IsLocalField l] [Algebra k l] : Prop where
  /-- The valuation of `l` extends the valuation of `k`. -/
  hasExtension : (Valued.v (R := k)).HasExtension (Valued.v (R := l))

attribute [instance] IsLocalFieldExtension.hasExtension

/-- An extension `l/k` of local fields is **unramified** if the degree of the residue field
extension equals `[l : k]`; equivalently `e = 1`. -/
def IsUnramifiedLocalExtension (k : Type*) [Field k] [Valued k (WithZero (Multiplicative ℤ))]
    [IsLocalField k] (l : Type*) [Field l] [Valued l (WithZero (Multiplicative ℤ))]
    [IsLocalField l] [Algebra k l] [IsLocalFieldExtension k l] : Prop :=
  Module.finrank (Valued.ResidueField k) (Valued.ResidueField l) = Module.finrank k l

/-- **The unique unramified extension of degree `n`.**

For a non-archimedean local field `k` and `n ≠ 0` there is a finite Galois extension `l/k` of
degree `n` which is unramified, and it is unique up to `k`-isomorphism; its residue field is the
unique extension of `κ_k` of degree `n`.  (Equivalently: the unramified extensions of `k` form a
single `Ẑ`-tower and `Gal(k^ur/k) ≅ Ẑ`, with the Frobenius as the canonical generator.) -/
def HasUnramifiedExtensionOfDegree (k : Type*) [Field k]
    [Valued k (WithZero (Multiplicative ℤ))] [IsLocalField k] (n : ℕ) : Prop :=
  ∃ (l : Type) (_ : Field l) (_ : Valued l (WithZero (Multiplicative ℤ)))
    (_ : IsLocalField l) (_ : Algebra k l) (_ : IsLocalFieldExtension k l)
    (_ : FiniteDimensional k l) (_ : IsGalois k l),
    Module.finrank k l = n ∧ IsUnramifiedLocalExtension k l ∧
      ∀ (l' : Type) (_ : Field l') (_ : Valued l' (WithZero (Multiplicative ℤ)))
        (_ : IsLocalField l') (_ : Algebra k l') (_ : IsLocalFieldExtension k l')
        (_ : FiniteDimensional k l') (_ : IsGalois k l'),
        Module.finrank k l' = n → IsUnramifiedLocalExtension k l' → Nonempty (l ≃ₐ[k] l')

/-! ## The local–global dictionary

The statements relating a finite Galois extension `L/K` of number fields, a prime `w` of `L` above
a prime `v` of `K`, the completions `L_w`, `K_v`, the decomposition group `D_w` and the tensor
product `L ⊗_K K_v`. -/

/-- **The decomposition group is the local Galois group.**  If `w` is a finite prime of `L` lying
over `v`, then the completion `L_w` is a Galois extension of `K_v` whose Galois group is
canonically isomorphic to the decomposition group `D_w`.

This is *proved* in `Submission/Work/LocalFields/nonempty_galois_completion_equiv.lean`; the
definition is kept here only to name the statement.  See
`Work.LocalFields.nonempty_localGaloisGroup_mulEquiv_decompositionGroup`. -/
def DecompositionGroupIsLocalGaloisGroup {K L : Type*} [Field K] [Field L] [NumberField K]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (v : FinitePrime K) (w : FinitePrime L) [hw : w.asIdeal.LiesOver v.asIdeal] : Prop :=
  Nonempty (localGaloisGroup v w ≃* decompositionGroup K w)

/-- The statement `DecompositionGroupIsLocalGaloisGroup` holds. -/
theorem decompositionGroupIsLocalGaloisGroup {K L : Type*} [Field K] [Field L] [NumberField K]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (v : FinitePrime K) (w : FinitePrime L) [hw : w.asIdeal.LiesOver v.asIdeal] :
    DecompositionGroupIsLocalGaloisGroup v w :=
  nonempty_localGaloisGroup_mulEquiv_decompositionGroup v w

/-! ## The structure of the maximal pro-`p` quotient -/

/-- A topological group is **pro-`p`** if it is a profinite `p`-group. -/
structure IsProP (p : ℕ) (G : Type*) [Group G] [TopologicalSpace G] : Prop where
  /-- the group is compact. -/
  compactSpace : CompactSpace G
  /-- the group is totally disconnected. -/
  totallyDisconnectedSpace : TotallyDisconnectedSpace G
  /-- the group operations are continuous. -/
  isTopologicalGroup : IsTopologicalGroup G
  /-- every element has `p`-power order. -/
  isPGroup : IsPGroup p G

/-- The number `d = [k : ℚ_p] + 1` of topological generators of the Demushkin group `G_k(p)`. -/
noncomputable def demushkinGenerators (k : Type*) [Field k] (p : ℕ) [Fact p.Prime]
    [Algebra ℚ_[p] k] : ℕ :=
  Module.finrank ℚ_[p] k + 1

/-- **Demushkin's structure theorem for `Gal(k̄/k)^{pro-p}` (named statement).**

For a `p`-adic field `k`, the maximal pro-`p` quotient `Q = G_k(p)` of the absolute Galois group
of `k` is a *Demushkin group*: a pro-`p` group topologically generated by `d = [k : ℚ_p] + 1`
elements subject to a single relation, of cohomological dimension `2`, with `H²(Q, 𝔽_p) ≅ 𝔽_p`
and the cup product `H¹(Q, 𝔽_p) × H¹(Q, 𝔽_p) → H²(Q, 𝔽_p)` a non-degenerate pairing
(Demushkin, Labute, Serre; see Serre, *Cohomologie galoisienne*, II §5).

Formal content recorded here: `k` is a `p`-adic field, and there is a pro-`p` group `Q` with a
continuous surjection `G_k ↠ Q` that is universal among pro-`p` quotients of `G_k`, which is
topologically generated by *exactly* `d = [k : ℚ_p] + 1` elements (so `d` is not a free
parameter: it is determined by `k`), and which admits a presentation with `d` generators and a
single relation.  The cohomological-dimension and duality clauses are **not** formalised here:
they require the cohomology of pro-`p` groups, which is not available in the current library. -/
def DemushkinProPStructure (k : Type*) [Field k] [Valued k (WithZero (Multiplicative ℤ))]
    [IsLocalField k] (p : ℕ) [Fact p.Prime] [Algebra ℚ_[p] k] : Prop :=
  IsPadicField k p ∧
    ∃ (Q : Type) (_ : Group Q) (_ : TopologicalSpace Q),
      IsProP p Q ∧
      (∃ S : Finset Q, S.card = demushkinGenerators k p ∧ Subgroup.closure (S : Set Q) = ⊤) ∧
      (∃ (H : Type) (_ : Group H) (_ : TopologicalSpace H), IsProP p H ∧
        ∃ (S : Finset H), S.card = demushkinGenerators k p ∧
          Subgroup.closure (S : Set H) = ⊤ ∧
          ∃ (φ : H →* Q) (r : H), Function.Surjective φ ∧ Continuous φ ∧
            closure ((Subgroup.normalClosure ({r} : Set H) : Subgroup H) : Set H) =
              (φ.ker : Set H)) ∧
      ∃ π : AbsoluteGaloisGroup k →* Q, Function.Surjective π ∧ Continuous π ∧
        ∀ (Q' : Type) (_ : Group Q') (_ : TopologicalSpace Q'),
          IsProP p Q' → ∀ π' : AbsoluteGaloisGroup k →* Q', Continuous π' →
            Function.Surjective π' → ∃ φ : Q →* Q', Continuous φ ∧ φ.comp π = π'

/-! ## Global inputs (not formalised)

The global inputs of Shafarevich's argument are not formalised in this directory, because they
require a development of global class field theory which is out of scope for the local chapter.
For reference, the precise classical statements are:

* **Hasse's local–global principle for the Brauer group.**  For a number field `K`, the map
  `Br(K) → ∏_v Br(K_v)` (over all places `v`, including the archimedean ones) is injective; and a
  central simple algebra over `K` splits if and only if it splits at every place.  Equivalently,
  the Brauer group of a number field is the direct sum of its local Brauer groups modulo the
  diagonal ("Hasse's exact sequence" `0 → Br(K) → ⊕_v Br(K_v) → ℚ/ℤ → 0`).

* **Grünwald–Wang.**  Let `K` be a number field, `n ≥ 1`, `S` a finite set of places of `K` and
  for each `v ∈ S` a cyclic extension `L_v/K_v` of degree dividing `n`.  If `K` is not a
  "`2`-special" field (the exceptional case: `K` has exactly one non-archimedean place `v₀` above
  `2`, `v₀` is non-split for `K(ζ_{2^n})`, and `-1 ∈ K^{∗4}`), then there is a cyclic extension
  `L/K` of degree `n` with `L ⊗_K K_v ≅ L_v` for `v ∈ S`.  In the exceptional case one has to
  allow an obstruction (Wang's counterexample).

* **Solvability of embedding problems over local fields.**  Over a non-archimedean local field
  `k`, every finite embedding problem with abelian kernel is solvable after replacing the given
  realisation by an unramified twist; the obstruction lies in `H²(Gal(l/k), A)` and is computed
  by local class field theory (Tate duality).  The classical source for the `p`-group version
  is Shafarevich, *On p-extensions* (1962); the general statement used by the global argument is
  Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, chapter 9.
-/

end Work.LocalFields
