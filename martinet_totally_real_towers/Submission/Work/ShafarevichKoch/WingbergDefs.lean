import Mathlib
import Submission.Work.ShafarevichKoch.Kc
import Submission.Work.ShafarevichKoch.CoeffZ
import Submission.Work.ShafarevichKoch.Kc_unit_eq_or_eq_neg
import Submission.Work.ShafarevichKoch.Cohomology3Map

/-!
# `Work.ShafarevichKoch.WingbergDefs` -- the objects of Wingberg's duality

This module fixes the vocabulary in which this chapter states its **classical arithmetic input**,
Wingberg's duality (Neukirch--Schmidt--Wingberg, *Cohomology of Number Fields*, Ch. VIII §8
Theorem 8.8.1; see also Hajir--Maire--Ramakrishna, `arXiv:2103.09508`, Theorem 1.7 and §1.2) in
the unramified case `S = ∅`, for `Kc = ℚ(√-30030)`:

* `Work.ShafarevichKoch.PDual A` : the Pontryagin dual `Hom(A, ℂˣ)` of a finite abelian group
  `A`, written additively (for `A` finite this is the dual `A^∨` of the classical statement);
* `Work.ShafarevichKoch.twoPrimaryPart A` : the `2`-primary part of a commutative group `A`
  (the *p*-part `Cl_K ⊗ ℤ_p` of Wingberg's `H¹(G_∅, O_∅^×)`, NSW Ch. VIII §8 Lemma 8.8.4);
* `Work.ShafarevichKoch.Cl2Part` : the `2`-primary part of `Cl(Kc)`.

## Main declarations

* `Work.ShafarevichKoch.PDual`, `twoPrimaryPart`, `Cl2Part`, `mem_twoPrimaryPart`.
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open scoped Classical

noncomputable section

namespace Work.ShafarevichKoch

open Work.ConCohomology

/-- **The Pontryagin dual of a finite abelian group**, `Hom(A, ℂˣ)`, written additively.  For
finite `A` this is the dual `A^∨` appearing in Wingberg's duality
`Ĥ^i(G_∅, O_{K_∅}^×) ≅ Ĥ^{3-i}(G_∅,ℤ)^∨` (NSW Ch. VIII §8 Thm 8.8.1). -/
abbrev PDual (A : Type*) [AddCommGroup A] : Type _ := A →+ Additive ℂˣ

/-- **The `2`-primary part of a commutative group `A`**: the subgroup of elements of `2`-power
order.  For `A = Cl(Kc)` this is Wingberg's `Cl_K ⊗ ℤ_2`, the group that NSW Ch. VIII §8
Lemma 8.8.4 identifies with `H¹(G_∅, O_{K_∅}^×)`. -/
def twoPrimaryPart (A : Type*) [CommGroup A] : Subgroup A where
  carrier := {y : A | ∃ k : ℕ, y ^ (2 ^ k) = 1}
  mul_mem' := by
    rintro a b ⟨k, hk⟩ ⟨m, hm⟩
    refine ⟨k + m, ?_⟩
    have h1 : a ^ (2 ^ (k + m)) = 1 := by
      rw [pow_add, pow_mul, hk, one_pow]
    have h2 : b ^ (2 ^ (k + m)) = 1 := by
      rw [pow_add, mul_comm, pow_mul, hm, one_pow]
    rw [mul_pow, h1, h2, one_mul]
  one_mem' := ⟨0, by simp⟩
  inv_mem' := by
    rintro a ⟨k, hk⟩
    exact ⟨k, by rw [inv_pow, hk, inv_one]⟩

@[simp] lemma mem_twoPrimaryPart {A : Type*} [CommGroup A] (y : A) :
    y ∈ twoPrimaryPart A ↔ ∃ k : ℕ, y ^ (2 ^ k) = 1 := Iff.rfl

/-- **The `2`-primary part of the class group of `Kc`**, i.e. `Cl(Kc) ⊗ ℤ_2`. -/
abbrev Cl2Part : Type _ := ↥(twoPrimaryPart (ClassGroup (NumberField.RingOfIntegers Work.ClassFieldTower.Kc)))

instance : Finite Cl2Part :=
  Finite.of_injective (fun x : Cl2Part => (x : ClassGroup (NumberField.RingOfIntegers Work.ClassFieldTower.Kc)))
    Subtype.val_injective

section Duality

variable (M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Work.ClassFieldTower.Kc 2)

/-- **Wingberg's duality in the unramified case, for `Kc`** (Neukirch--Schmidt--Wingberg Ch. VIII
§8 Theorem 8.8.1, in the two instances `i = 1` and `i = 0`, together with NSW Ch. VIII §8
Lemma 8.8.4, as displayed by Hajir--Maire--Ramakrishna `arXiv:2103.09508` §1.2):

* `H²(G_∅,ℤ)^∨ ≅ Cl(Kc) ⊗ ℤ_2`, the `2`-primary part of the class group;
* `H³(G_∅,ℤ)^∨ ≅ Ĥ⁰(G_∅,O_{K_∅}^×)`, the universal-norm quotient of the units, hence a quotient
  of `(𝓞 Kc)ˣ = {±1}`;
* both cohomology groups are finite (part of the classical setting for an imaginary quadratic
  base field).

This is the single named classical input of this chapter; every other ingredient of the relation
bound is proved here or in the workspace. -/
def WingbergDuality : Prop :=
  Finite (H2 (Work.ClassFieldTower.galoisGroup M) ℤ) ∧
    Finite (H3 (Work.ClassFieldTower.galoisGroup M) ℤ) ∧
    Nonempty (PDual (H2 (Work.ClassFieldTower.galoisGroup M) ℤ) ≃+ Additive Cl2Part) ∧
    (∃ N : Subgroup (RingUnit Work.ClassFieldTower.Kc),
      Nonempty (PDual (H3 (Work.ClassFieldTower.galoisGroup M) ℤ) ≃+
        Additive (RingUnit Work.ClassFieldTower.Kc ⧸ N)))

end Duality


end Work.ShafarevichKoch
