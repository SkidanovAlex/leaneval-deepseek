import Mathlib.FieldTheory.KrullTopology
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.FieldTheory.IsSepClosed
import Submission.NeukirchUchida.Conjugation
import Submission.NeukirchUchida.Uniqueness
import Submission.Commons.FieldTheory.Galois.eq_one_of_preserves_and_centralizes
import Submission.NeukirchUchida.PlaceRigidity

/-!
# The deep core of the Neukirch–Uchida theorem

Reference: J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*,
2nd ed., Springer 2008, Chapter XII, Theorem 12.2.1 (Neukirch–Uchida).

Theorem 12.2.1 states: let `k₁`, `k₂` be number fields with separable closures
`k̄₁`, `k̄₂`.  Every isomorphism `σ : G(k̄₁|k₁) ≃ G(k̄₂|k₂)` of *profinite
groups* is induced by a unique field isomorphism `α : k̄₂ → k̄₁` with
`α(k₂) = k₁`, i.e. `σ(g)(x) = α⁻¹ (g (α x))`.

Here `G(k̄ᵢ|kᵢ)` is `Gal(kᵢ'/kᵢ)` and "isomorphism of profinite groups" is
formalized as `ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)` together with
`he : IsHomeomorph ϕ` (for Galois groups of algebraic extensions the Krull
topology is profinite, see `Mathlib.FieldTheory.Galois.Profinite`).

## State of the reduction

* The *elementary half* — that a base-field-mapping `σ` induces such a
  conjugation isomorphism — is fully proved in `Conjugation.lean`, and the
  *compatibility* of the induced field-side and group-side correspondences in
  `FieldTransport.lean`.

* The **uniqueness half** is reduced to `centralizer_trivial` (below) by
  `Uniqueness.lean` (`unique_sigma_of_centralizer_trivial`), and
  `centralizer_trivial` is itself *proved* from the triviality of the centre of
  the absolute Galois group of a number field, CoNF (12.1.6)
  (`center_trivial` below), using the shared-commons lemma
  `Commons.FieldTheory.Galois.eq_one_of_preserves_and_centralizes`.

* The **existence half** (`exists_sigma`) is the remaining deep input.  Its
  proof in CoNF XII §2 uses Neukirch's theorem characterizing decomposition
  groups of places among the closed subgroups of `G_k` isomorphic to local
  Galois groups (CoNF (12.1.9)), Čebotarev density, and the solvability of
  split embedding problems (CoNF Chapter IX) — none of which is available yet.

Thus the challenge theorem depends on exactly two statements below:
`exists_sigma` and `center_trivial`. -/

namespace Submission.NeukirchUchida

open scoped Topology

/-- **The centre of the absolute Galois group of a number field is trivial**
(CoNF XII, (12.1.6)).

Every element of `Gal(F'/F)` commuting with all elements of `Gal(F'/F)` is the
identity, for `F` a number field and `F'` a separable closure of `F`.  In the
book this is deduced from Neukirch's characterization of decomposition groups
of places among the closed subgroups of `G(F)` isomorphic to local Galois
groups (CoNF (12.1.9)), using the local theory of `p`-adic fields. -/
theorem center_trivial (F : Type*) [Field F] [NumberField F] (F' : Type*)
    [Field F'] [Algebra F F'] [IsSepClosure F F'] (c : Gal(F'/F))
    (h : ∀ g : Gal(F'/F), c * g = g * c) : c = 1 :=
  center_trivial_of_sepClosure (F := F) (F' := F') c h

/-- **(12.1.6) in the form needed for uniqueness.**  A ring automorphism of
`K'` which preserves the embedded copy of `K` and commutes with every element
of `Gal(K'/K)` is the identity (for `K` a number field and `K'` a separable
closure of it).

This is proved from `center_trivial` (CoNF (12.1.6)) by the argument recorded
in the docstring of
`Commons.FieldTheory.Galois.eq_one_of_preserves_and_centralizes`: such a `c`
restricts to an automorphism `δ` of the image `K' ≅ K` of the base field; if
`δ = id` then `c ∈ Gal(K'/K)` is central and `center_trivial` for `K` applies;
if `δ ≠ id`, the fixed field `F` of `δ` inside `K` is a number field,
`Gal(K'/F)` has centre containing `c ≠ 1`, contradicting `center_trivial` for
`F`. -/
theorem centralizer_trivial.{uK, uK'} {K : Type uK} [Field K] [NumberField K] {K' : Type uK'}
    [Field K'] [Algebra K K'] [IsSepClosure K K'] (c : K' ≃+* K')
    (hpres : ∀ x ∈ (algebraMap K K').range, c x ∈ (algebraMap K K').range)
    (hcomm : ∀ g : Gal(K'/K), c.trans (g.toRingEquiv.trans c.symm) = g.toRingEquiv) :
    c = 1 :=
  Commons.FieldTheory.Galois.eq_one_of_preserves_and_centralizes
    (center_trivial.{uK, uK'}) c hpres hcomm

variable {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
  [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
  [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']

/-- **Existence** (the heart of Neukirch–Uchida): every homeomorphic
isomorphism of the absolute Galois groups is induced by a base-field-mapping
field isomorphism between the separable closures.  (CoNF XII Thm 12.2.1;
the proof occupies §12.1–§12.2 of Chapter XII.)

This is the *only* remaining gap of the whole development.  Its precise reduction to named
classical inputs is proved in `Submission/NeukirchUchida/Reduction.lean`:

* `exists_sigma_of_inputs_homeomorph` (with the inputs of CoNF (12.1.9)-if, the reconstruction of
  §12.2 and the anabelian rigidity of the decomposition groups) implies the statement below;
* `Submission/NeukirchUchida/Detection.lean` shows that is suffices to check the conjugation on the
  decomposition subgroups (`conjugates_of_eq_on_decompositionGroup'`);
* the "only if" half of (12.1.9) — a decomposition group is non-trivial, self-normalising and
  isomorphic to the absolute Galois group of a p-adic field — is
  `PlaceSystem.normalizer_decompositionGroup` together with the local/global bridge
  `NK.NeukirchUchida.nonempty_mulEquiv_decompositionGroupOf_localGalois`.

What is missing is the local structure theory of `G_κ` (CoNF (12.1.10) and the Demushkin theory of
pro-`p` groups of local fields), the canonical local Artin map, global class field theory and
Čebotarev; those are being built in `Submission/Work/{ProfiniteP,LocalAnabelian,LocalReciprocity,
GlobalCFT,Chebotarev}`. -/
theorem exists_sigma (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (he : IsHomeomorph ϕ) :
    ∃ σ : K₂' ≃+* K₁', Conjugates σ ϕ := by
  sorry

/-- **Uniqueness** of the inducing field isomorphism.  Reduces (via
`Uniqueness.lean`) to `centralizer_trivial`, i.e. to triviality of the centre of
the absolute Galois group of a number field (CoNF (12.1.6)). -/
theorem unique_sigma (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (he : IsHomeomorph ϕ)
    {σ₁ σ₂ : K₂' ≃+* K₁'} (h₁ : Conjugates σ₁ ϕ) (h₂ : Conjugates σ₂ ϕ) :
    σ₁ = σ₂ :=
  unique_sigma_of_centralizer_trivial
    (fun c hpres hcomm => centralizer_trivial c hpres hcomm) ϕ h₁ h₂

/-- The Neukirch–Uchida theorem (CoNF XII Thm 12.2.1), stated for the
challenge's types: unique existence of the inducing field isomorphism. -/
theorem neukirch_uchida_core (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (he : IsHomeomorph ϕ) :
    ∃! σ : K₂' ≃+* K₁', Conjugates σ ϕ := by
  rcases exists_sigma ϕ he with ⟨σ, hσ⟩
  exact ⟨σ, hσ, fun y hy => unique_sigma ϕ he hy hσ⟩

end Submission.NeukirchUchida
