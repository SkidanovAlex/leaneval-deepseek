import Mathlib
import Submission.Work.SSGRoute.PTembedding.LocalCFTImports
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Degree-`p` Galois subextensions of the maximal abelian subextension

Let `F' / F` be a Galois extension and let `A = maxAbelianSubext F F'` be the maximal abelian
subextension, i.e. the fixed field of the commutator subgroup of `Gal(F'/F)`.  A Galois
subextension `L ≤ F'` of prime degree `p` has Galois group of order `p`, hence cyclic, hence
abelian, so `L ≤ A` by maximality of `A` (`le_maxAbelianSubext_of_commutative`).

Consequently the degree-`p` Galois subextensions of `F'` and of `A` are the same objects:
`restrict` (the inverse of `lift`) and `lift` give mutually inverse maps between the two sets of
degree-`p` Galois levels, and the Galois property and the `F`-dimension are transported along the
canonical `F`-algebra isomorphisms `restrictAlgEquiv` and `liftAlgEquiv`.  Hence the two counting
types have the same cardinality.
-/

namespace Work.SSGRoute.PTembedding

open Module

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

section Core

variable {F F' : Type*} [Field F] [Field F'] [Algebra F F']

/-- The lift of the restriction of a level `L ≤ A` is `L` itself. -/
private lemma levelMap_restrict_eq (L : IntermediateField F F')
    (h : L ≤ NK.LocalReciprocity.maxAbelianSubext F F') :
    NK.LocalReciprocity.levelMap (L.restrict h) = L := by
  rw [show NK.LocalReciprocity.levelMap (L.restrict h) = IntermediateField.lift (L.restrict h) from
      rfl,
    IntermediateField.lift_restrict]

/-- The restriction of the lift of a level of `A` is the level itself. -/
private lemma restrict_levelMap_eq
    (X : IntermediateField F ↥(NK.LocalReciprocity.maxAbelianSubext F F'))
    (h : NK.LocalReciprocity.levelMap X ≤ NK.LocalReciprocity.maxAbelianSubext F F') :
    (NK.LocalReciprocity.levelMap X).restrict h = X := by
  ext x
  rw [IntermediateField.mem_restrict,
    show (x.1 : F') ∈ NK.LocalReciprocity.levelMap X ↔
        (x.1 : F') ∈ IntermediateField.lift X from Iff.rfl,
    IntermediateField.mem_lift]

end Core

section Main

variable {F F' : Type*} [Field F] [Field F'] [Algebra F F'] [IsGalois F F']

/-- A Galois subextension of `F' / F` of prime degree `p` is abelian over `F`, hence contained in
the maximal abelian subextension. -/
private lemma mem_maxAbelianSubext_of_finrank_prime (p : ℕ) [Fact p.Prime]
    (L : IntermediateField F F') [IsGalois F L] (h : Module.finrank F ↥L = p) :
    L ≤ NK.LocalReciprocity.maxAbelianSubext F F' := by
  haveI : FiniteDimensional F ↥L :=
    Module.finite_of_finrank_pos (by rw [h]; exact (Fact.out : p.Prime).pos)
  have hcard : Nat.card Gal(↥L/F) = p := by
    rw [IsGalois.card_aut_eq_finrank F ↥L, h]
  haveI : IsCyclic Gal(↥L/F) := isCyclic_of_prime_card hcard
  exact NK.LocalReciprocity.le_maxAbelianSubext_of_commutative L (fun σ τ => mul_comm' σ τ)

private noncomputable def toMaxAbelian (p : ℕ) [Fact p.Prime]
    (x : {L : IntermediateField F F' // IsGalois F L ∧ Module.finrank F ↥L = p}) :
    {L : IntermediateField F ↥(NK.LocalReciprocity.maxAbelianSubext F F') //
      IsGalois F ↥L ∧ Module.finrank F ↥L = p} := by
  haveI : IsGalois F ↥x.1 := x.2.1
  have hle : x.1 ≤ NK.LocalReciprocity.maxAbelianSubext F F' :=
    mem_maxAbelianSubext_of_finrank_prime p x.1 x.2.2
  exact ⟨x.1.restrict hle, IsGalois.of_algEquiv (IntermediateField.restrictAlgEquiv hle),
    by rw [← LinearEquiv.finrank_eq (IntermediateField.restrictAlgEquiv hle).toLinearEquiv]
       exact x.2.2⟩

private noncomputable def ofMaxAbelian (p : ℕ) [Fact p.Prime]
    (y : {L : IntermediateField F ↥(NK.LocalReciprocity.maxAbelianSubext F F') //
      IsGalois F ↥L ∧ Module.finrank F ↥L = p}) :
    {L : IntermediateField F F' // IsGalois F L ∧ Module.finrank F ↥L = p} := by
  haveI : IsGalois F ↥y.1 := y.2.1
  exact ⟨NK.LocalReciprocity.levelMap y.1,
    IsGalois.of_algEquiv (NK.LocalReciprocity.levelEquiv y.1),
    by rw [← LinearEquiv.finrank_eq (NK.LocalReciprocity.levelEquiv y.1).toLinearEquiv]
       exact y.2.2⟩

private noncomputable def equivGaloisDegP (p : ℕ) [Fact p.Prime] :
    {L : IntermediateField F F' // IsGalois F L ∧ Module.finrank F ↥L = p} ≃
    {L : IntermediateField F ↥(NK.LocalReciprocity.maxAbelianSubext F F') //
      IsGalois F ↥L ∧ Module.finrank F ↥L = p} where
  toFun := by intro x; exact toMaxAbelian p x
  invFun := by intro y; exact ofMaxAbelian p y
  left_inv := by
    intro x
    apply Subtype.ext
    show NK.LocalReciprocity.levelMap (x.1.restrict _) = x.1
    exact levelMap_restrict_eq _ _
  right_inv := by
    intro y
    apply Subtype.ext
    show (NK.LocalReciprocity.levelMap y.1).restrict _ = y.1
    exact restrict_levelMap_eq _ _

end Main

theorem natCard_galoisExtensions_maxAbelian (p : ℕ) [Fact p.Prime] {F F' : Type*} [Field F]
    [Field F'] [Algebra F F'] [IsGalois F F'] :
    Nat.card {L : IntermediateField F F' // IsGalois F L ∧ Module.finrank F ↥L = p}
      = Nat.card {L : IntermediateField F ↥(NK.LocalReciprocity.maxAbelianSubext F F') //
          IsGalois F ↥L ∧ Module.finrank F ↥L = p} :=
  Nat.card_congr (equivGaloisDegP p)

end Work.SSGRoute.PTembedding
