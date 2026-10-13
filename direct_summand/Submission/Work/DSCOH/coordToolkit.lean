/-
Area DSCOH — coordinate toolkit for the chart Čech complex of the free shifted module `S(-d)`.

The chart Čech complex of `S(-d)` is build from the degree-zero parts `degZero (shift d) S` of the
localizations of `S = A[X₀,…,X_{n-1}]` at the monomials `X_S = ∏_{i∈S} Xᵢ`.  The lemma
`Work.DSCOH.locAt_monomial_basis` provides, for every chart `S`, an `A`-basis of `locAt S`
indexed by the Laurent exponents `β : Fin n → ℤ` with `β i ≥ 0` for `i ∉ S`, with two
compatibilities: the `S`-action multiplies the exponent by `Xᵢ`, and the structure maps `resAt`
are the identity on exponents.

This file turns that interface into the computational lemmas needed to analyse the chart Čech
complex: the `β`-coordinate functional of an element of a chart localization is `A`-linear
(`coordFun`), the structure maps are compatible with coordinates (`repr_resAt`), and the
`T`-component of the Čech differential has the expected coordinate form (`coord_cechDiff`).

Everything here is stated with the basis family as an explicit argument, so that it can be used
with the basis produced by `locAt_monomial_basis`.
-/
import Mathlib
import Submission.Work.DSCOH.Chart
import Submission.Work.DSCOH.shift_gradedSMul
import Submission.Work.DSCOH.divPow_toLoc_mem
import Submission.Work.DSCOH.cechDiff_apply_coe

open MvPolynomial Module

namespace Work.DSCOH

variable {A : Type*} [CommRing A] {n : ℕ}

/-! ## The negative part `Z(β)` of a Laurent exponent -/

/-- The set of coordinates in which the Laurent exponent `β` is negative. -/
noncomputable def Zset (β : Fin n → ℤ) : Finset (Fin n) := Finset.univ.filter (fun i => β i < 0)

lemma mem_Zset {β : Fin n → ℤ} {i : Fin n} : i ∈ Zset β ↔ β i < 0 := by
  simp [Zset]

/-- `β` is a legitimate exponent index for the chart `S` exactly when `Z(β) ⊆ S`. -/
lemma Zset_subset_iff (S : Finset (Fin n)) (β : Fin n → ℤ) :
    Zset β ⊆ S ↔ ∀ i, i ∉ S → 0 ≤ β i := by
  constructor
  · intro h i hi
    by_contra hc
    exact hi (h (by rw [mem_Zset]; omega))
  · intro h i hi
    rw [mem_Zset] at hi
    by_contra hmem
    exact absurd (h i hmem) (by omega)

/-- The complement of `Zset β`: the coordinates in which `β` is nonnegative. -/
noncomputable def Pset (β : Fin n → ℤ) : Finset (Fin n) := Finset.univ.filter (fun i => 0 ≤ β i)

lemma mem_Pset {β : Fin n → ℤ} {i : Fin n} : i ∈ Pset β ↔ 0 ≤ β i := by simp [Pset]

lemma Zset_union_Pset (β : Fin n → ℤ) : Zset β ∪ Pset β = Finset.univ := by
  ext i
  simp only [Finset.mem_union, mem_Zset, mem_Pset, Finset.mem_univ]
  exact iff_true_intro (by omega)

lemma Zset_disjoint_Pset (β : Fin n → ℤ) : Disjoint (Zset β) (Pset β) := by
  rw [Finset.disjoint_left]
  intro i hi hi'
  rw [mem_Zset] at hi
  rw [mem_Pset] at hi'
  omega

/-- The elements of `V \ Z` are exactly the elements of `P`. -/
lemma mem_sdiff_Zset {β : Fin n → ℤ} {i : Fin n} :
    i ∈ (Finset.univ : Finset (Fin n)) \ Zset β ↔ 0 ≤ β i := by
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, mem_Zset]
  omega

/-- `β` is its own legitimate exponent at the chart `Z(β)`. -/
lemma Zset_valid_self (β : Fin n → ℤ) : ∀ i, i ∉ Zset β → 0 ≤ β i := by
  intro i hi
  rw [mem_Zset] at hi
  omega

/-- The exponent condition at a chart `T` is inherited by `T \ {i}` when `β i ≥ 0`. -/
lemma Zset_index_erase {β : Fin n → ℤ} {T : Finset (Fin n)} {i : Fin n}
    (hT : Zset β ⊆ T) (hi : i ∈ T) (hiZ : i ∉ Zset β) :
    ∀ j, j ∉ T.erase i → 0 ≤ β j := by
  intro j hj
  by_cases hji : j = i
  · subst hji
    rw [mem_Zset] at hiZ
    omega
  · exact (Zset_subset_iff T β).mp hT j
      (fun hmem => hj (Finset.mem_erase.mpr ⟨hji, hmem⟩))

/-- The chart `T \ {i}` of `Z(β)` lies at level `q + 2` when `T` lies at level `q + 3`. -/
lemma card_erase_of_mem' {T : Finset (Fin n)} {i : Fin n} {q : ℕ}
    (hi : i ∈ T) (hcard : T.card = q + 3) : (T.erase i).card = q + 1 + 1 := by
  rw [Finset.card_erase_of_mem hi]
  omega

/-- The underlying element of a component of a chart Čech term. -/
noncomputable def cechCoeff {d : ℕ} {q : ℕ}
    (a : CechTerm (A := A) (n := n) (M := Poly A n) (shift (A := A) (n := n) d) q)
    (S : Finset (Fin n)) (hS : S.card = q + 1) : locAt (A := A) (M := Poly A n) S :=
  (a ⟨S, hS⟩ : degZero (A := A) (M := Poly A n) (shift (A := A) (n := n) d) S).1

/-! ## The coordinate functional -/

variable (B : (S : Finset (Fin n)) →
    Module.Basis {β : Fin n → ℤ // ∀ i, i ∉ S → 0 ≤ β i} A (locAt (A := A) (M := Poly A n) S))

/-- The `β`-coordinate functional on the chart localization at `S`, read in the monomial basis
`B S`. -/
noncomputable def coordFun (S : Finset (Fin n))
    (β : {β : Fin n → ℤ // ∀ i, i ∉ S → 0 ≤ β i}) :
    locAt (A := A) (M := Poly A n) S →ₗ[A] A :=
  (Finsupp.lapply (M := A) β).comp (B S).repr.toLinearMap

lemma coordFun_apply (S : Finset (Fin n))
    (β : {β : Fin n → ℤ // ∀ i, i ∉ S → 0 ≤ β i})
    (x : locAt (A := A) (M := Poly A n) S) :
    coordFun B S β x = (B S).repr x β := rfl

/-! ## Coordinates and the structure maps -/

/-- The structure map `resAt h` is the identity on exponents, so it is compatible with the
coordinate functionals: the coordinates of `resAt h x` are those of `x`, and zero on exponents
that were not legitimate at the smaller chart. -/
lemma repr_resAt
    (hB2 : ∀ (S T : Finset (Fin n)) (h : S ⊆ T) (β : {β : Fin n → ℤ // ∀ i, i ∉ S → 0 ≤ β i}),
      resAt (M := Poly A n) h (B S β) = B T ⟨β.1, fun i hi => β.2 i (fun hmem => hi (h hmem))⟩)
    {S T : Finset (Fin n)} (h : S ⊆ T) (β : {β : Fin n → ℤ // ∀ i, i ∉ T → 0 ≤ β i})
    (x : locAt (A := A) (M := Poly A n) S) :
    ((B T).repr (resAt (M := Poly A n) h x)) β =
      if hβ : ∀ i, i ∉ S → 0 ≤ β.1 i then ((B S).repr x) ⟨β.1, hβ⟩ else 0 := by
  by_cases hβ : ∀ i, i ∉ S → 0 ≤ β.1 i
  · rw [dif_pos hβ]
    have key : (coordFun B T β).comp ((resAt (M := Poly A n) h).restrictScalars A :
        locAt (A := A) (M := Poly A n) S →ₗ[A] locAt (A := A) (M := Poly A n) T)
        = coordFun B S ⟨β.1, hβ⟩ := by
      refine Basis.ext (B S) fun β' => ?_
      rw [LinearMap.comp_apply, LinearMap.restrictScalars_apply, coordFun_apply, coordFun_apply,
        hB2 S T h β', Basis.repr_self, Basis.repr_self]
      by_cases hh : β'.1 = β.1
      · simp [Finsupp.single_apply, Subtype.ext_iff, hh]
      · simp [Finsupp.single_apply, Subtype.ext_iff, hh]
    have h2 := congrArg (fun f : locAt (A := A) (M := Poly A n) S →ₗ[A] A => f x) key
    simpa only [coordFun_apply, LinearMap.comp_apply, LinearMap.restrictScalars_apply] using h2
  · rw [dif_neg hβ]
    have key : (coordFun B T β).comp ((resAt (M := Poly A n) h).restrictScalars A :
        locAt (A := A) (M := Poly A n) S →ₗ[A] locAt (A := A) (M := Poly A n) T) = 0 := by
      refine Basis.ext (B S) fun β' => ?_
      rw [LinearMap.comp_apply, LinearMap.restrictScalars_apply, coordFun_apply,
        hB2 S T h β', Basis.repr_self, LinearMap.zero_apply]
      have hne : β'.1 ≠ β.1 := by
        intro hh
        exact hβ (fun i hi => by rw [← hh]; exact β'.2 i hi)
      simp [Finsupp.single_apply, Subtype.ext_iff, hne]
    have h2 := congrArg (fun f : locAt (A := A) (M := Poly A n) S →ₗ[A] A => f x) key
    simpa only [coordFun_apply, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
      LinearMap.zero_apply] using h2

/-! ## The coordinate form of the Čech differential -/

/-- **The coordinate form of the Čech differential.**  For a legitimate exponent `β` at the
chart `T`, the `β`-coordinate of the `T`-component of the differential is the alternating sum
over `i ∈ T` of the `β`-coordinates of the `(T \ {i})`-components, the terms being dropped
exactly when `β` is no longer a legitimate exponent at `T \ {i}`. -/
theorem coord_cechDiff (d : ℕ)
    (hB2 : ∀ (S T : Finset (Fin n)) (h : S ⊆ T) (β : {β : Fin n → ℤ // ∀ i, i ∉ S → 0 ≤ β i}),
      resAt (M := Poly A n) h (B S β) = B T ⟨β.1, fun i hi => β.2 i (fun hmem => hi (h hmem))⟩)
    [SetLike.GradedSMul (homSub A n) (shift (A := A) (n := n) d)]
    (q : ℕ) (a : CechTerm (A := A) (n := n) (M := Poly A n) (shift (A := A) (n := n) d) q)
    (T : {S : Finset (Fin n) // S.card = q + 1 + 1})
    (β : {β : Fin n → ℤ // ∀ i, i ∉ T.1 → 0 ≤ β i}) :
    ((B T.1).repr ((cechDiff (A := A) (n := n) (M := Poly A n)
      (shift (A := A) (n := n) d) q a) T).1) β =
      ∑ i ∈ T.1.attach, ((-1 : ℤ) ^ ((T.1.filter fun j => j < i.1)).card) •
        (if hβ : ∀ j, j ∉ T.1.erase i.1 → 0 ≤ β.1 j
          then ((B (T.1.erase i.1)).repr
            (a ⟨T.1.erase i.1, by rw [Finset.card_erase_of_mem i.2]; omega⟩).1) ⟨β.1, hβ⟩
          else 0) := by
  rw [← coordFun_apply B T.1 β ((cechDiff (A := A) (n := n) (M := Poly A n)
    (shift (A := A) (n := n) d) q a) T).1]
  rw [show ((cechDiff (A := A) (n := n) (M := Poly A n)
      (shift (A := A) (n := n) d) q a) T).1 =
    ∑ i ∈ T.1.attach, ((-1 : ℤ) ^ ((T.1.filter fun j => j < i.1)).card) •
      resAt (M := Poly A n) (Finset.erase_subset i.1 T.1)
        (a ⟨T.1.erase i.1, by rw [Finset.card_erase_of_mem i.2]; omega⟩ :
          locAt (A := A) (M := Poly A n) (T.1.erase i.1))
      from cechDiff_apply_coe (A := A) (n := n) (M := Poly A n) (shift (A := A) (n := n) d) q a T]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul]
  congr 1
  exact repr_resAt B hB2 (Finset.erase_subset i.1 T.1) β
    (a ⟨T.1.erase i.1, by rw [Finset.card_erase_of_mem i.2]; omega⟩ :
      locAt (A := A) (M := Poly A n) (T.1.erase i.1))

end Work.DSCOH
