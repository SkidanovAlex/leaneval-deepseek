import Mathlib.FieldTheory.PolynomialGaloisGroup
import Submission.Commons.GroupTheory.GroupAction.primitive_ne_top_no_isSwap

open Function Polynomial Filter
open scoped BigOperators

set_option autoImplicit false

/-!
# The natural permutation action of a polynomial's Galois group on its roots

Bhargava, *Galois groups of random integer polynomials* (Annals of Math 201(2)
(2025)), proof of Theorem 1.  The argument splits polynomials whose Galois
group is not `Sₙ` by group-theoretic properties (`primitive`, `transitive`,
`contains a transposition`) of the natural action of `Gal(f)` on the `n`
roots of `f`.  This module makes that action explicit for a polynomial over
`ℚ`:  it identifies the root set of a separable polynomial with
`Fin (natDegree)` and pushes the Galois action forward to a homomorphism
`p.Gal →* S_{natDegree p}` (`galFinHom`), proving the standard consequences:

* the action is faithful (`galRootPerm_injective`, `galFinHom_injective`);
* `Nat.card p.Gal ≤ (p.natDegree)!` (`gal_card_le_factorial`);
* **Jordan's theorem in this setting** (`no_isSwap_of_preprimitive_proper`):
  if the image of `p.Gal` in `Sₙ` is a proper *primitive* (preprimitive)
  permutation group, then no element of `p.Gal` acts on the roots as a
  transposition — the group-theoretic input for the Case-I squarefullness
  statement (`fieldDisc_squarefull_of_no_transposition`, see `CaseI.lean`).

The module is written over `ℚ` (the base field of the challenge theorem);
characteristic zero is used only to get separability of irreducible
polynomials (`separable_of_irreducible_rat`).

**Transitivity note.**  When `p` is irreducible, Mathlib's
`Polynomial.Gal.galAction_isPretransitive p p.SplittingField hp` states that
the Galois action on the roots is transitive.  Wiring its `MulAction`
instance (`Polynomial.Gal.galAction` vs `galActionAux`) to the
`galRootPerm`/`galFinHom` representation is deferred until the counting
arguments need the statement.
-/

namespace Submission.Vdw

noncomputable section

open Polynomial

/-- An irreducible polynomial over `ℚ` is separable (characteristic zero). -/
theorem separable_of_irreducible_rat {p : ℚ[X]} (hp : Irreducible p) : p.Separable := by
  rw [Polynomial.separable_iff_derivative_ne_zero hp]
  intro hder
  have hconst : p.natDegree = 0 := Polynomial.derivative_eq_zero.mp hder
  have hpos : 0 < p.natDegree := by
    rw [Polynomial.natDegree_pos_iff_degree_pos]
    exact Polynomial.degree_pos_of_irreducible hp
  omega

/-- The roots of a separable polynomial in its splitting field, identified with
`Fin p.natDegree`. -/
noncomputable def rootFinEquiv (p : ℚ[X]) (hsep : p.Separable) :
    p.rootSet p.SplittingField ≃ Fin p.natDegree :=
  Fintype.equivFinOfCardEq (by
    simpa using Polynomial.card_rootSet_eq_natDegree (F := ℚ) (K := p.SplittingField)
      hsep (Polynomial.SplittingField.splits p))

/-- Conjugation of permutations by an equivalence of the underlying types, as
a monoid homomorphism. -/
noncomputable def permCongrHom {α β : Type*} (e : α ≃ β) :
    Equiv.Perm α →* Equiv.Perm β where
  toFun := e.permCongr
  map_one' := by
    ext x
    simp [Equiv.permCongr_apply]
  map_mul' := Equiv.permCongr_mul e

/-- The natural action of `p.Gal` on the roots of `p` in its splitting field,
as permutations of the root set (the `galActionHom` representation). -/
noncomputable def galRootPerm (p : ℚ[X]) :
    p.Gal →* Equiv.Perm (p.rootSet p.SplittingField) := by
  classical
  haveI : Fact ((p.map (algebraMap ℚ p.SplittingField)).Splits) :=
    ⟨Polynomial.SplittingField.splits p⟩
  exact Polynomial.Gal.galActionHom p p.SplittingField

/-- The natural action of `p.Gal` on `Fin p.natDegree` (the roots after
identification), a homomorphism `p.Gal →* S_{natDegree p}`. -/
noncomputable def galFinHom (p : ℚ[X]) (hsep : p.Separable) :
    p.Gal →* Equiv.Perm (Fin p.natDegree) :=
  (permCongrHom (rootFinEquiv p hsep)).comp (galRootPerm p)

set_option linter.style.haveILetI false in
/-- The action of `p.Gal` on the roots in the splitting field is faithful
(`Polynomial.Gal.galActionHom_injective`). -/
theorem galRootPerm_injective (p : ℚ[X]) : Function.Injective (galRootPerm p) := by
  classical
  have hfact : Fact ((p.map (algebraMap ℚ p.SplittingField)).Splits) :=
    ⟨Polynomial.SplittingField.splits p⟩
  letI : Fact ((p.map (algebraMap ℚ p.SplittingField)).Splits) := hfact
  exact Polynomial.Gal.galActionHom_injective p p.SplittingField

/-- The natural permutation representation `p.Gal → S_{natDegree p}` is
faithful. -/
theorem galFinHom_injective (p : ℚ[X]) (hsep : p.Separable) :
    Function.Injective (galFinHom p hsep) := by
  intro σ τ h
  apply galRootPerm_injective p
  apply (Equiv.permCongr (rootFinEquiv p hsep)).injective
  exact h

/-- A separable polynomial of degree `n` has Galois group of cardinality at
most `n!`. -/
theorem gal_card_le_factorial (p : ℚ[X]) (hsep : p.Separable) :
    Nat.card p.Gal ≤ (p.natDegree).factorial := by
  rw [Nat.card_eq_fintype_card]
  calc
    Fintype.card p.Gal ≤ Fintype.card (Equiv.Perm (Fin p.natDegree)) :=
      Fintype.card_le_of_injective (galFinHom p hsep) (galFinHom_injective p hsep)
    _ = (p.natDegree).factorial := by
      simp [Fintype.card_perm]

/-- Conjugation by an equivalence maps the swap of two points to the swap of
their images: `e.permCongr (swap a b) = swap (e a) (e b)`. -/
theorem permCongr_swap {α β : Type*} (e : α ≃ β) [DecidableEq α] [DecidableEq β]
    (a b : α) : e.permCongr (Equiv.swap a b) = Equiv.swap (e a) (e b) := by
  ext x
  rw [Equiv.permCongr_apply]
  by_cases hxa : x = e a
  · subst hxa
    simp
  · by_cases hxb : x = e b
    · subst hxb
      simp
    · have hne_a : e.symm x ≠ a := by
        intro hsym
        exact hxa (by
          calc x = e (e.symm x) := by simp
          _ = e a := by rw [hsym])
      have hne_b : e.symm x ≠ b := by
        intro hsym
        exact hxb (by
          calc x = e (e.symm x) := by simp
          _ = e b := by rw [hsym])
      simp [Equiv.swap_apply_of_ne_of_ne hne_a hne_b, Equiv.swap_apply_of_ne_of_ne hxa hxb]

/-- Conjugating a transposition by an equivalence yields a transposition. -/
theorem permCongr_isSwap_of_isSwap {α β : Type*} (e : α ≃ β) [DecidableEq α] [DecidableEq β]
    {g : Equiv.Perm α} (h : g.IsSwap) : (e.permCongr g).IsSwap := by
  rcases h with ⟨a, b, hab, hg⟩
  refine ⟨e a, e b, ?_, ?_⟩
  · intro hEq
    exact hab (Equiv.injective e hEq)
  · rw [hg, permCongr_swap e a b]

/-- **Jordan in this setting.**  If the image of `p.Gal` in `S_{natDegree p}`
is a proper preprimitive (primitive) permutation group, then no element of
`p.Gal` acts on the roots as a transposition.  (The statement is phrased
through the faithful `S_{natDegree p}`-representation `galFinHom`; see also
`permCongr_isSwap_of_isSwap` for transporting transposition statements from
the root set through the identification `rootFinEquiv`.) -/
theorem no_isSwap_of_preprimitive_proper (p : ℚ[X]) (hsep : p.Separable)
    (hprim : MulAction.IsPreprimitive ((galFinHom p hsep).range) (Fin p.natDegree))
    (hprop : (galFinHom p hsep).range ≠ ⊤) :
    ∀ σ : p.Gal, ¬ ((galFinHom p hsep) σ).IsSwap := by
  intro σ hswap
  have hmem : (galFinHom p hsep σ) ∈ (galFinHom p hsep).range := ⟨σ, rfl⟩
  exact (Commons.GroupTheory.GroupAction.primitive_ne_top_no_isSwap
    (G := (galFinHom p hsep).range) hprim hprop) ⟨galFinHom p hsep σ, hswap, hmem⟩

/-- The Galois group and its permutation image in `S_{natDegree p}` have the
same cardinality (the representation is faithful). -/
theorem gal_card_eq_card_range (p : ℚ[X]) (hsep : p.Separable) :
    Nat.card p.Gal = Nat.card ((galFinHom p hsep).range) := by
  classical
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact (Fintype.card_coeSort_range (galFinHom_injective p hsep)).symm

/-- If `|Gal| < (natDegree p)!` then the permutation image is a proper
subgroup of the full symmetric group. -/
theorem range_ne_top_of_card_lt_factorial (p : ℚ[X]) (hsep : p.Separable)
    (h : Nat.card p.Gal < (p.natDegree).factorial) :
    (galFinHom p hsep).range ≠ ⊤ := by
  intro htop
  have hsurj : Function.Surjective (galFinHom p hsep) :=
    (MonoidHom.range_eq_top).mp htop
  have hbij : Function.Bijective (galFinHom p hsep) :=
    ⟨galFinHom_injective p hsep, hsurj⟩
  have hcard : Nat.card p.Gal = Nat.card (Equiv.Perm (Fin p.natDegree)) := by
    exact Nat.card_congr (Equiv.ofBijective (galFinHom p hsep) hbij)
  have hfact : Nat.card (Equiv.Perm (Fin p.natDegree)) = (p.natDegree).factorial := by
    rw [Nat.card_eq_fintype_card]
    simp [Fintype.card_perm]
  rw [hcard, hfact] at h
  exact (Nat.lt_irrefl _) h

end

section Transitivity

/-! ## Transitivity of the natural action for irreducible polynomials

When `p` is irreducible over `ℚ`, its Galois group acts transitively on the
roots (equivalently, on `Fin p.natDegree` through the faithful representation
`galFinHom`).  Mathlib provides the root-level statement
`Polynomial.Gal.galAction_isPretransitive`; the lemmas below transport it
through the identification `rootFinEquiv` to the `Fin`-indexed
representation used throughout this project.  This is the hypothesis under
which "primitive" (`MulAction.IsPreprimitive`, which extends
`MulAction.IsPretransitive`) is meaningful for the natural action of the
Galois group of an irreducible polynomial. -/

/-- The Galois action on the roots of an irreducible polynomial is
transitive at the level of root permutations (`galRootPerm`). -/
theorem galRootPerm_pretransitive (p : ℚ[X]) (hp : Irreducible p) :
    ∀ x y : p.rootSet p.SplittingField, ∃ σ : p.Gal,
      galRootPerm p σ x = y := by
  classical
  intro x y
  letI : Fact ((p.map (algebraMap ℚ p.SplittingField)).Splits) :=
    ⟨Polynomial.SplittingField.splits p⟩
  have ht := Polynomial.Gal.galAction_isPretransitive (F := ℚ) (p := p)
    (E := p.SplittingField) hp
  letI : MulAction.IsPretransitive p.Gal (p.rootSet p.SplittingField) := ht
  rcases MulAction.exists_smul_eq p.Gal x y with ⟨σ, hσ⟩
  refine ⟨σ, ?_⟩
  change Polynomial.Gal.galActionHom (F := ℚ) (p := p) (E := p.SplittingField) σ x = y
  change (σ • x : p.rootSet p.SplittingField) = y
  exact hσ

/-- Under the root/`Fin` identification `rootFinEquiv`, the permutation
`galFinHom p hsep σ` sends `i` to the image of the root to which `σ`
moves `(rootFinEquiv p hsep).symm i`. -/
theorem galFinHom_apply (p : ℚ[X]) (hsep : p.Separable) (σ : p.Gal) (i : Fin p.natDegree) :
    galFinHom p hsep σ i =
      (rootFinEquiv p hsep) (galRootPerm p σ ((rootFinEquiv p hsep).symm i)) := by
  classical
  simp [galFinHom, permCongrHom, Equiv.permCongr_apply]

/-- **Transitivity for irreducible polynomials.**  If `p` is irreducible
over `ℚ`, then the image of its Galois group in `S_{natDegree p}` (the
`galFinHom` representation) acts pretransitively on `Fin p.natDegree`. -/
theorem galFinHom_pretransitive (p : ℚ[X]) (hp : Irreducible p) (hsep : p.Separable) :
    MulAction.IsPretransitive ((galFinHom p hsep).range) (Fin p.natDegree) := by
  classical
  refine ⟨fun i j => ?_⟩
  rcases galRootPerm_pretransitive p hp
      ((rootFinEquiv p hsep).symm i) ((rootFinEquiv p hsep).symm j) with ⟨σ, hσ⟩
  refine ⟨⟨galFinHom p hsep σ, ⟨σ, rfl⟩⟩, ?_⟩
  rw [MulAction.subgroup_smul_def, Equiv.Perm.smul_def]
  rw [galFinHom_apply p hsep σ i, hσ]
  simp

end Transitivity

section IsSwapContent

open Equiv

/-- **Pure content of step 4 of (c).**  If a permutation `σ` fixes every
point except possibly `a` and `b` (`a ≠ b`), and `σ` does not fix `a`, then
`σ` is the transposition `swap a b`.  (Applied to a nontrivial inertia
element once the orbit structure is known: orbits of size one are fixed
pointwise and the single two-element orbit forces the swap.) -/
theorem isSwap_of_fixes_all_but_two {ι : Type*} [DecidableEq ι] (σ : Equiv.Perm ι)
    (a b : ι) (hab : a ≠ b) (hfix : ∀ x : ι, x ≠ a → x ≠ b → σ x = x)
    (hma : σ a ≠ a) : σ.IsSwap := by
  have hmem_a : σ a = a ∨ σ a = b := by
    by_contra h
    push_neg at h
    have hfixa : σ (σ a) = σ a := hfix (σ a) h.1 h.2
    exact h.1 (σ.injective hfixa)
  have hσa : σ a = b := by
    rcases hmem_a with h | h
    · exact (hma h).elim
    · exact h
  have hmem_b : σ b = a ∨ σ b = b := by
    by_contra hb
    push_neg at hb
    have hfixb : σ (σ b) = σ b := hfix (σ b) hb.1 hb.2
    exact hb.2 (σ.injective hfixb)
  have hσb : σ b = a := by
    rcases hmem_b with h | h
    · exact h
    · -- σ b = b but σ a = b, contradicting injectivity
      have hinj : a = b := σ.injective (by rw [hσa, h])
      exact (hab hinj).elim
  refine ⟨a, b, hab, ?_⟩
  ext x
  by_cases hxa : x = a
  · subst x
    simp [hσa]
  · by_cases hxb : x = b
    · subst x
      simp [hσb]
    · rw [hfix x hxa hxb]
      exact (Equiv.swap_apply_of_ne_of_ne hxa hxb).symm

end IsSwapContent


end Submission.Vdw
