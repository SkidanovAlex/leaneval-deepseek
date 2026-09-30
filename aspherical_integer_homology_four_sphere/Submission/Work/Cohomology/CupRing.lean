import Mathlib
import Submission.Work.Cohomology.cupH
import Submission.Work.Cohomology.cupUnit
import Submission.Work.Cohomology.cupAssoc
import Submission.Work.Cohomology.cupNatural
import Submission.Work.Cohomology.cupLeibniz

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The cohomology ring of a simplicial set: packaging

`Submission/Work/Cohomology/AlexanderWhitney.lean` defines the Alexander–Whitney cup product of
singular cochains of a simplicial set `X` and `Submission/Work/Cohomology/cupH.lean` proves that it
descends to a pairing on cohomology (an unexplicit `∃`).  This file *packages* that: it fixes the
pairing once and for all (`cupH'`), defines the unit class `oneH ∈ H⁰`, and records the ring laws
on `H^*` (unit, associativity, and the elementary consequences of bilinearity).

## Casts

The product `cupH' R X n m : H^n →ₗ H^m →ₗ H^{n+m}` changes the degree in a way that involves
arithmetic on `ℕ` (`n + 0 = n`, `0 + n = n`, `(n+m)+k = n+(m+k)`).  In `H^{n+0}` vs `H^n` the
indices are *definitionally* equal (`Nat.add` recurses on its second argument), so the right unit
law and the bilinearity statements are cast-free; for the left unit law and associativity we
transport along `(Nat.zero_add n).symm` and `Nat.add_assoc n m k`, exactly as the cochain-level
statements `cupUnit` and `cupAssoc` do.

## Main definitions

* `cupH'` — the cup product `H^n →ₗ H^m →ₗ H^{n+m}` (a choice of the `∃` in `cupH`), with its
  computation rule `cupH'_apply` on the classes of cocycles;
* `oneH` — the unit class `1 ∈ H⁰`, the class of the augmentation `unitCochain`.

## Main results

* `cupH'_one_right`, `cupH'_one_left` — the unit laws;
* `cupH'_assoc` — associativity;
* `cupH'_zero_left`, `cupH'_zero_right`, and the bilinearity statements `cupH'_add_left`,
  `cupH'_add_right`, `cupH'_smul_left`, `cupH'_smul_right`.
-/

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

variable (R : Type) [CommRing R] (X : SSet)

/-- The `R`-module of `n`-cochains of a simplicial set. -/
abbrev Cochain (n : ℕ) : Type _ :=
  (X.chainComplex (ModuleCat.of R R)).X n →ₗ[R] R

/-! ## The unit `0`-cocycle -/

/-- Every `0`-cochain evaluated at a `0`-simplex: the augmentation. -/
theorem unitCochain_apply_gen (σ : X _⦋0⦌) :
    genEval R X (unitCochain R X) σ = 1 :=
  genEval_unitCochain R X σ

/-- **The augmentation is a cocycle.**  Its coboundary vanishes because it takes the same value on
all vertices. -/
theorem cochainDiff_unitCochain :
    cochainDiff R X (unitCochain R X) = 0 := by
  apply genEval_ext
  intro σ
  rw [genEval_cochainDiff]
  simp only [unitCochain_apply_gen, mul_one]
  rw [Fin.sum_univ_two]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, genEval, LinearMap.zero_apply]
  ring

/-- The **unit class** `1 ∈ H⁰(X;R)`: the cohomology class of the augmentation. -/
noncomputable def oneH : (SSetCochainComplex R X).homology 0 :=
  cohomologyClassOf R X (unitCochain R X) (cochainDiff_unitCochain R X)

/-! ## The product on cohomology -/

/-- **The cup product on cohomology**, a choice of the pairing whose existence is `cupH`. -/
noncomputable def cupH' (n m : ℕ) :
    (SSetCochainComplex R X).homology n →ₗ[R] (SSetCochainComplex R X).homology m →ₗ[R]
      (SSetCochainComplex R X).homology (n + m) :=
  (Classical.choose (cupH R X)) n m

/-- **The computation rule for `cupH'`**: on the classes of two cocycles `α`, `β` it is the class
of `α ⌣ β`. -/
theorem cupH'_apply {n m : ℕ} (α : Cochain R X n) (β : Cochain R X m)
    (hα : cochainDiff R X α = 0) (hβ : cochainDiff R X β = 0)
    (hαβ : cochainDiff R X (cup R X α β) = 0) :
    cupH' R X n m (cohomologyClassOf R X α hα) (cohomologyClassOf R X β hβ) =
      cohomologyClassOf R X (cup R X α β) hαβ :=
  Classical.choose_spec (cupH R X) n m α β hα hβ hαβ

/-! ## Elementary API for the cochain level

The following are immediate from `cup_apply` and the definitions; they are stated here so that the
cohomology-level statements below depend only on this file. -/

/-- The cup product with the zero cochain on the left vanishes. -/
theorem cup_zero_left' {n m : ℕ} (β : Cochain R X m) :
    cup R X (0 : Cochain R X n) β = 0 := by
  have h := (cupBilinear R X n m).2.1 (0 : R) (0 : Cochain R X n) β
  simpa using h

/-- The cup product with the zero cochain on the right vanishes. -/
theorem cup_zero_right' {n m : ℕ} (α : Cochain R X n) :
    cup R X α (0 : Cochain R X m) = 0 := by
  have h := (cupBilinear R X n m).2.2.2 (0 : R) α (0 : Cochain R X m)
  simpa using h

/-- The product of two cocycles is a cocycle (the Leibniz rule). -/
theorem cochainDiff_cup_of_cocycles {n m : ℕ} (α : Cochain R X n) (β : Cochain R X m)
    (hα : cochainDiff R X α = 0) (hβ : cochainDiff R X β = 0) :
    cochainDiff R X (cup R X α β) = 0 := by
  rw [cupLeibniz R X α β, hα, hβ, cup_zero_left' R X, cup_zero_right' R X, eqRec_zero R X,
    smul_zero, add_zero]

/-! ## Cohomology classes and their representatives -/

/-- The cycle built from a cocycle has the cocycle as underlying cochain, so the associated
cohomology class is the class of the cocycle. -/
theorem cohomologyClassOf_eq_homologyπ (n : ℕ)
    (z : (SSetCochainComplex R X).cycles n) :
    cohomologyClassOf R X ((SSetCochainComplex R X).iCycles n z)
        (cochainDiff_iCycles R X n z) =
      ((SSetCochainComplex R X).homologyπ n).hom z := by
  rw [cohomologyClassOf, show cocycleOf R X ((SSetCochainComplex R X).iCycles n z)
      (cochainDiff_iCycles R X n z) = z from by
    apply iCycles_injective R X n
    rw [iCycles_cocycleOf]]

/-- **Every cohomology class is the class of a cocycle.** -/
theorem exists_cohomologyClassOf (n : ℕ) (x : (SSetCochainComplex R X).homology n) :
    ∃ (α : Cochain R X n) (hα : cochainDiff R X α = 0),
      cohomologyClassOf R X α hα = x := by
  have hsurj : Function.Surjective
      (fun z : (SSetCochainComplex R X).cycles n =>
        ((SSetCochainComplex R X).homologyπ n).hom z) :=
    (ModuleCat.epi_iff_surjective _).mp inferInstance
  obtain ⟨z, hz⟩ := hsurj x
  refine ⟨(SSetCochainComplex R X).iCycles n z, cochainDiff_iCycles R X n z, ?_⟩
  rw [cohomologyClassOf_eq_homologyπ R X n z]
  simpa using hz

/-- Two equal cocycles have equal cohomology classes. -/
theorem cohomologyClassOf_congr {n : ℕ} {α β : Cochain R X n} (h : α = β)
    (hα : cochainDiff R X α = 0) (hβ : cochainDiff R X β = 0) :
    cohomologyClassOf R X α hα = cohomologyClassOf R X β hβ := by
  subst h
  exact congrArg (fun h' => cohomologyClassOf R X α h') (Subsingleton.elim hα hβ)

/-! ## Transport along equalities of degrees -/

/-- Transporting a cocycle along an equality of degrees keeps it a cocycle. -/
theorem cochainDiff_cast {p q : ℕ} (h : p = q) (α : Cochain R X p)
    (hα : cochainDiff R X α = 0) :
    cochainDiff R X (h ▸ α) = 0 := by
  cases h
  exact hα

/-- Transporting a cochain along `h` and back is the identity. -/
theorem eqRec_symm_eqRec_self' {p q : ℕ} (h : p = q) (α : Cochain R X p) :
    h.symm ▸ (h ▸ α) = α := by
  cases h
  rfl

/-- **Transport of cohomology classes along an equality of degrees.** -/
theorem cohomologyClassOf_cast {p q : ℕ} (h : p = q) (α : Cochain R X p)
    (hα : cochainDiff R X α = 0) :
    h ▸ cohomologyClassOf R X α hα =
      cohomologyClassOf R X (h ▸ α) (cochainDiff_cast R X h α hα) := by
  cases h
  rfl

/-- A convenient form of `cupH'_apply` with the cocycle condition for the product supplied
automatically. -/
theorem cupH'_apply' {n m : ℕ} (α : Cochain R X n) (β : Cochain R X m)
    (hα : cochainDiff R X α = 0) (hβ : cochainDiff R X β = 0) :
    cupH' R X n m (cohomologyClassOf R X α hα) (cohomologyClassOf R X β hβ) =
      cohomologyClassOf R X (cup R X α β)
        (cochainDiff_cup_of_cocycles R X α β hα hβ) :=
  cupH'_apply R X α β hα hβ _

/-! ## The ring laws on cohomology -/

/-- The zero class is absorbing on the left. -/
theorem cupH'_zero_left (n m : ℕ) (y : (SSetCochainComplex R X).homology m) :
    cupH' R X n m 0 y = 0 := by
  rw [map_zero, LinearMap.zero_apply]

/-- The zero class is absorbing on the right. -/
theorem cupH'_zero_right (n m : ℕ) (x : (SSetCochainComplex R X).homology n) :
    cupH' R X n m x 0 = 0 := by
  rw [map_zero]

/-- Additivity in the first variable. -/
theorem cupH'_add_left (n m : ℕ) (x x' : (SSetCochainComplex R X).homology n)
    (y : (SSetCochainComplex R X).homology m) :
    cupH' R X n m (x + x') y = cupH' R X n m x y + cupH' R X n m x' y := by
  rw [map_add, LinearMap.add_apply]

/-- Additivity in the second variable. -/
theorem cupH'_add_right (n m : ℕ) (x : (SSetCochainComplex R X).homology n)
    (y y' : (SSetCochainComplex R X).homology m) :
    cupH' R X n m x (y + y') = cupH' R X n m x y + cupH' R X n m x y' := by
  rw [map_add]

/-- Homogeneity in the first variable. -/
theorem cupH'_smul_left (n m : ℕ) (a : R) (x : (SSetCochainComplex R X).homology n)
    (y : (SSetCochainComplex R X).homology m) :
    cupH' R X n m (a • x) y = a • cupH' R X n m x y := by
  rw [map_smul, LinearMap.smul_apply]

/-- Homogeneity in the second variable. -/
theorem cupH'_smul_right (n m : ℕ) (a : R) (x : (SSetCochainComplex R X).homology n)
    (y : (SSetCochainComplex R X).homology m) :
    cupH' R X n m x (a • y) = a • cupH' R X n m x y := by
  rw [map_smul]

/-- **The right unit law**: `x ⌣ 1 = x`.  The degree `n + 0` is definitionally `n`, so no
transport is needed. -/
theorem cupH'_one_right (n : ℕ) (x : (SSetCochainComplex R X).homology n) :
    cupH' R X n 0 x (oneH R X) = x := by
  obtain ⟨α, hα, rfl⟩ := exists_cohomologyClassOf R X n x
  show cupH' R X n 0 (cohomologyClassOf R X α hα)
    (cohomologyClassOf R X (unitCochain R X) (cochainDiff_unitCochain R X)) =
      cohomologyClassOf R X α hα
  rw [cupH'_apply' R X α (unitCochain R X) hα (cochainDiff_unitCochain R X)]
  exact cohomologyClassOf_congr R X (cupUnit R X α).2 _ _

/-- **The left unit law**: `1 ⌣ x = x`, transported along `0 + n = n`. -/
theorem cupH'_one_left (n : ℕ) (x : (SSetCochainComplex R X).homology n) :
    cupH' R X 0 n (oneH R X) x = (Nat.zero_add n).symm ▸ x := by
  obtain ⟨α, hα, rfl⟩ := exists_cohomologyClassOf R X n x
  show cupH' R X 0 n (cohomologyClassOf R X (unitCochain R X) (cochainDiff_unitCochain R X))
    (cohomologyClassOf R X α hα) = _
  rw [cupH'_apply' R X (unitCochain R X) α (cochainDiff_unitCochain R X) hα]
  rw [cohomologyClassOf_cast R X (Nat.zero_add n).symm α hα]
  exact cohomologyClassOf_congr R X (by
    have hu : (Nat.zero_add n) ▸ cup R X (unitCochain R X) α = α := (cupUnit R X α).1
    have h2 := congrArg (fun t => (Nat.zero_add n).symm ▸ t) hu
    simpa [eqRec_symm_eqRec_self'] using h2) _ _

/-- **Associativity** of the cup product on cohomology, transported along
`(n + m) + k = n + (m + k)`. -/
theorem cupH'_assoc (n m k : ℕ) (x : (SSetCochainComplex R X).homology n)
    (y : (SSetCochainComplex R X).homology m) (z : (SSetCochainComplex R X).homology k) :
    (Nat.add_assoc n m k) ▸ (cupH' R X (n + m) k (cupH' R X n m x y) z) =
      cupH' R X n (m + k) x (cupH' R X m k y z) := by
  obtain ⟨α, hα, rfl⟩ := exists_cohomologyClassOf R X n x
  obtain ⟨β, hβ, rfl⟩ := exists_cohomologyClassOf R X m y
  obtain ⟨γ, hγ, rfl⟩ := exists_cohomologyClassOf R X k z
  rw [cupH'_apply' R X α β hα hβ]
  rw [cupH'_apply' R X (cup R X α β) γ (cochainDiff_cup_of_cocycles R X α β hα hβ) hγ]
  rw [cohomologyClassOf_cast R X (Nat.add_assoc n m k) (cup R X (cup R X α β) γ)
    (cochainDiff_cup_of_cocycles R X (cup R X α β) γ
      (cochainDiff_cup_of_cocycles R X α β hα hβ) hγ)]
  rw [cupH'_apply' R X β γ hβ hγ]
  rw [cupH'_apply' R X α (cup R X β γ) hα (cochainDiff_cup_of_cocycles R X β γ hβ hγ)]
  exact cohomologyClassOf_congr R X (cupAssoc R X α β γ) _ _

end

end Work.Cohomology
