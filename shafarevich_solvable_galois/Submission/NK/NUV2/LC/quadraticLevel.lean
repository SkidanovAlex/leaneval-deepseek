import Mathlib.Algebra.Torsor.Defs
import Mathlib.FieldTheory.Galois.Basic
import Submission.NK.LocalReciprocity.le_maxAbelianSubext_of_commutative
import Submission.NK.NUV2.LC.adjoinSq_normal_finrank_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The quadratic level of a unit inside the maximal abelian subextension

For a field `F` with Galois extension `F'` and `b ∈ F`, the field `F(√b)` is an abelian (degree
`≤ 2`) extension of `F`, hence lies in `F^{ab} = NK.LocalReciprocity.maxAbelianSubext F F'`.  This
is the level at which the **two-variable Hilbert symbol** `(a,b) = inv_{F(√b)/F}(a)` lives; it is the
missing ingredient for *stating* the classical sub-pieces of the `p = 2` product formula.

## What is here

* `commute_of_card_le_two` — a **finite** group of cardinality `≤ 2` is commutative;
* `isMulCommutative_gal_of_finrank_le_two` — the Galois group of a Galois extension of degree
  `≤ 2` is commutative;
* `adjoinSq_le_maxAbelianSubext` / `mem_maxAbelianSubext_of_sq` — `F(√b) ≤ F^{ab}` and
  `√b ∈ F^{ab}`;
* `quadLevel` — `F(√b)` as a level *of* `F^{ab}`, together with its finiteness, normality and
  commutativity instances, i.e. the object that the local invariant map
  (`NK.NUV2.LC.localInvariant`, in `invariantMap.lean`) can be evaluated at.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped Classical

namespace NK.NUV2.LC

section CardTwo

variable {G : Type*} [Group G]

/-- **In a finite group of cardinality `≤ 2` every element is an involution.** -/
theorem mul_self_eq_one_of_card_le_two [Finite G] (h : Nat.card G ≤ 2) (x : G) : x * x = 1 := by
  have hpos : 0 < Nat.card G := Nat.card_pos
  have hdvd : orderOf x ∣ Nat.card G := orderOf_dvd_natCard x
  have hle : orderOf x ≤ 2 := le_trans (Nat.le_of_dvd hpos hdvd) h
  have hpos' : 0 < orderOf x := orderOf_pos x
  rcases (by omega : orderOf x = 1 ∨ orderOf x = 2) with h1 | h2
  · rw [show x = 1 from orderOf_eq_one_iff.mp h1, mul_one]
  · rw [← sq, ← h2, pow_orderOf_eq_one]

/-- **In a finite group of cardinality `≤ 2` any two non-identity elements are equal.** -/
theorem eq_of_ne_one_of_card_le_two [Finite G] (h : Nat.card G ≤ 2) {x y : G} (hx : x ≠ 1)
    (hy : y ≠ 1) : x = y := by
  by_contra hxy
  haveI : Fintype G := Fintype.ofFinite G
  have h1x : (1 : G) ∉ ({x, y} : Finset G) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun h' => hx h'.symm, fun h' => hy h'.symm⟩
  have hxy' : x ∉ ({y} : Finset G) := by
    simpa only [Finset.mem_singleton] using hxy
  have hcard : ({1, x, y} : Finset G).card = 3 := by
    rw [Finset.card_insert_of_notMem h1x, Finset.card_insert_of_notMem hxy',
      Finset.card_singleton]
  have hle : ({1, x, y} : Finset G).card ≤ Fintype.card G := Finset.card_le_univ _
  rw [Nat.card_eq_fintype_card] at h
  omega

/-- **A finite group of cardinality `≤ 2` is commutative.**  Either it is trivial, or every element
has order dividing `2`.  (Finiteness is a genuine hypothesis: `Nat.card G = 0` for an infinite
group, which is `≤ 2`.) -/
theorem commute_of_card_le_two [Finite G] (h : Nat.card G ≤ 2) (a b : G) : a * b = b * a := by
  have hsq : ∀ x : G, x * x = 1 := fun x => mul_self_eq_one_of_card_le_two h x
  have hinv : ∀ x : G, x⁻¹ = x := fun x => inv_eq_of_mul_eq_one_right (hsq x)
  calc a * b = (a * b)⁻¹ := (hinv (a * b)).symm
    _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
    _ = b * a := by rw [hinv b, hinv a]

end CardTwo

/-- **The Galois group of a Galois extension of degree `≤ 2` is commutative.** -/
theorem isMulCommutative_gal_of_finrank_le_two {K E : Type*} [Field K] [Field E] [Algebra K E]
    [FiniteDimensional K E] [IsGalois K E] (h : Module.finrank K E ≤ 2) :
    ∀ σ τ : E ≃ₐ[K] E, σ * τ = τ * σ := by
  haveI : Finite (E ≃ₐ[K] E) := inferInstance
  intro σ τ
  refine commute_of_card_le_two ?_ σ τ
  rw [IsGalois.card_aut_eq_finrank]
  exact h

section Quad

variable {F : Type*} {F' : Type*} [Field F] [Field F'] [Algebra F F'] [IsGalois F F']

/-- **`F(√b)` is an abelian extension of `F`**, hence lies in the maximal abelian subextension
`F^{ab} = NK.LocalReciprocity.maxAbelianSubext F F'`.

The extension has degree `≤ 2` (`adjoinSq_normal_finrank_le`), and a Galois extension of degree
`≤ 2` has a commutative Galois group (`isMulCommutative_gal_of_finrank_le_two`); the maximality
`le_maxAbelianSubext_of_commutative` concludes.  (The separability needed for `IsGalois` comes from
`IsGalois F F'`, via the intermediate-field instance for separability.) -/
theorem adjoinSq_le_maxAbelianSubext (y : F') (b : F) (hy : y * y = algebraMap F F' b)
    [NeZero (2 : F)] :
    IntermediateField.adjoin F ({y} : Set F') ≤
      NK.LocalReciprocity.maxAbelianSubext F F' := by
  obtain ⟨hN, hfd, hrank⟩ := adjoinSq_normal_finrank_le (K := F) (L := F') y b hy
  haveI : FiniteDimensional F ↥(IntermediateField.adjoin F ({y} : Set F')) := hfd
  haveI : Normal F ↥(IntermediateField.adjoin F ({y} : Set F')) := hN
  haveI : IsGalois F ↥(IntermediateField.adjoin F ({y} : Set F')) :=
    IsGalois.mk (to_isSeparable := inferInstance) (to_normal := hN)
  exact NK.LocalReciprocity.le_maxAbelianSubext_of_commutative _
    (isMulCommutative_gal_of_finrank_le_two hrank)

/-- **A square root of an element of the base field lies in `F^{ab}`.** -/
theorem mem_maxAbelianSubext_of_sq (y : F') (b : F) (hy : y * y = algebraMap F F' b)
    [NeZero (2 : F)] : y ∈ NK.LocalReciprocity.maxAbelianSubext F F' :=
  adjoinSq_le_maxAbelianSubext y b hy
    (IntermediateField.subset_adjoin F ({y} : Set F') (Set.mem_singleton y))

/-- **The quadratic level `F(√b)` of a square root `y` of `b`, viewed as a level of `F^{ab}`.**

Together with `quadLevel_normal`, `quadLevel_finiteDimensional` and `quadLevel_commutative`, this is
the level at which the Hilbert symbol `(·, b)` lives: the local invariant map
`NK.NUV2.LC.localInvariant` (`invariantMap.lean`) can be evaluated at it. -/
noncomputable def quadLevel (y : F') (b : F) (hy : y * y = algebraMap F F' b) [NeZero (2 : F)] :
    IntermediateField F (NK.LocalReciprocity.maxAbelianSubext F F') :=
  IntermediateField.adjoin F
    ({⟨y, mem_maxAbelianSubext_of_sq y b hy⟩} :
      Set ↥(NK.LocalReciprocity.maxAbelianSubext F F'))

theorem quadLevel_coe_mul_self (y : F') (b : F) (hy : y * y = algebraMap F F' b)
    [NeZero (2 : F)] :
    (⟨y, mem_maxAbelianSubext_of_sq y b hy⟩ :
        ↥(NK.LocalReciprocity.maxAbelianSubext F F')) *
        ⟨y, mem_maxAbelianSubext_of_sq y b hy⟩ =
      algebraMap F ↥(NK.LocalReciprocity.maxAbelianSubext F F') b :=
  Subtype.ext (by simpa using hy)

/-- The quadratic level is finite-dimensional over the base. -/
theorem quadLevel_finiteDimensional (y : F') (b : F) (hy : y * y = algebraMap F F' b)
    [NeZero (2 : F)] : FiniteDimensional F ↥(quadLevel y b hy) :=
  (adjoinSq_normal_finrank_le (K := F) (L := ↥(NK.LocalReciprocity.maxAbelianSubext F F'))
    ⟨y, mem_maxAbelianSubext_of_sq y b hy⟩ b (quadLevel_coe_mul_self y b hy)).2.1

/-- The quadratic level is normal over the base. -/
theorem quadLevel_normal (y : F') (b : F) (hy : y * y = algebraMap F F' b) [NeZero (2 : F)] :
    Normal F ↥(quadLevel y b hy) :=
  (adjoinSq_normal_finrank_le (K := F) (L := ↥(NK.LocalReciprocity.maxAbelianSubext F F'))
    ⟨y, mem_maxAbelianSubext_of_sq y b hy⟩ b (quadLevel_coe_mul_self y b hy)).1

/-- The finrank of the quadratic level is at most `2`. -/
theorem quadLevel_finrank_le_two (y : F') (b : F) (hy : y * y = algebraMap F F' b)
    [NeZero (2 : F)] : Module.finrank F ↥(quadLevel y b hy) ≤ 2 :=
  (adjoinSq_normal_finrank_le (K := F) (L := ↥(NK.LocalReciprocity.maxAbelianSubext F F'))
    ⟨y, mem_maxAbelianSubext_of_sq y b hy⟩ b (quadLevel_coe_mul_self y b hy)).2.2

/-- **The Galois group of the quadratic level is commutative** — so the quadratic level is an
abelian level, as required by the local reciprocity datum. -/
theorem quadLevel_commutative (y : F') (b : F) (hy : y * y = algebraMap F F' b) [NeZero (2 : F)] :
    ∀ σ τ : ↥(quadLevel y b hy) ≃ₐ[F] ↥(quadLevel y b hy), σ * τ = τ * σ := by
  haveI := quadLevel_finiteDimensional y b hy
  haveI := quadLevel_normal y b hy
  haveI : IsGalois F ↥(quadLevel y b hy) :=
    IsGalois.mk (to_isSeparable := inferInstance) (to_normal := quadLevel_normal y b hy)
  exact isMulCommutative_gal_of_finrank_le_two (quadLevel_finrank_le_two y b hy)

end Quad

end NK.NUV2.LC
