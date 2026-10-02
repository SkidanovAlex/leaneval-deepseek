import Mathlib
import Submission.Work.LerayHirsch.LH

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Injectivity of `π^*` in *every* degree, from the full Leray–Hirsch theorem

`Submission/Work/LerayHirsch/LH.lean` proves the **separation principle** in the *even* degrees:
if `LerayHirsch Z` holds for the projectivisation `π : P(E) → B` of a complex gluing-data bundle
`Z`, then

`CohMap_projMap_injective_of_LerayHirsch : Function.Injective (π^* : H^{2k}(B) → H^{2k}(P(E)))`

by putting the class in the `i = 0` slot of the Leray–Hirsch decomposition `Σ_i π^*(x_i) ⌣ ζ^i`
and using the unit law `x ⌣ ζ⁰ = x`.

This file supplies the **odd-degree** companion and glues the two, giving injectivity of `π^*` in
*every* degree `n` from the full statement `LerayHirschFull Z = LerayHirsch Z ∧ LerayHirschOdd Z`:

`CohMap_projMap_injective_of_LerayHirschFull :
  LerayHirschFull Z → Function.Injective (π^* : H^n(B) → H^n(P(E)))` for all `n`.

Everything here is unconditional; the only input is the odd-degree Leray–Hirsch
theorem itself.  The proof is verbatim the even one, with `lhTerm`/`lhMap` replaced by
`lhTermOdd`/`lhMapOdd` and `cupChern_zetaPow_zero` by the unit law of `cupH'`
(`Work.Cohomology.cupH'_one_right`):

* `lhSoloFamilyOdd`, `lhMapOdd_eq_single` — the family supported at a single index, and the value
  of `lhMapOdd` on it (the odd analogue of `lhSoloFamily`/`lhMap_eq_single`);
* `lhTermOdd_zero_index` — the `i = 0` summand of `lhMapOdd` **is** the pullback `π^*`
  (the odd analogue of `lhTerm_zero_index`);
* `CohMap_projMap_injective_of_LerayHirschOdd` — injectivity in the odd degrees `2k+1`;
* `CohMap_projMap_injective_of_LerayHirschFull` — the result, in every degree.

The degree bookkeeping is by `Nat.even_or_odd`: for `n = 2k` use the even theorem, for `n = 2k+1`
the odd one.  (The transports inside `lhTermOdd` are `rfl`-transports up to definitional unfolding,
which is what makes the statements below close by `cohTransport_rfl`.)
-/

namespace Work.LerayHirsch

open Work.TangentClasses Work.Thom

open scoped LinearAlgebra.Projectivization

noncomputable section

variable {B : Type} [TopologicalSpace B] {ι : Type} {m : ℕ}

/-! ## The odd-degree Leray–Hirsch decomposition -/

/-- A **family supported at a single odd index**: the odd-degree companion of `lhSoloFamily`.  The
value at index `i₀` is `x ∈ H^{2k+1-2i₀}(B)`, and `0` at every other index. -/
noncomputable def lhSoloFamilyOdd {B : Type} [TopologicalSpace B] {m : ℕ} {k : ℕ}
    (i₀ : {i : Fin m // (i : ℕ) ≤ k}) (x : Coh ℤ (2 * k + 1 - 2 * (i₀ : ℕ)) B) :
    (i : {i : Fin m // (i : ℕ) ≤ k}) → Coh ℤ (2 * k + 1 - 2 * (i : ℕ)) B :=
  fun i => if h : i = i₀ then h ▸ x else 0

theorem lhSoloFamilyOdd_self {B : Type} [TopologicalSpace B] {m k : ℕ}
    (i₀ : {i : Fin m // (i : ℕ) ≤ k}) (x : Coh ℤ (2 * k + 1 - 2 * (i₀ : ℕ)) B) :
    lhSoloFamilyOdd i₀ x i₀ = x := by
  rw [lhSoloFamilyOdd]; simp

theorem lhSoloFamilyOdd_of_ne {B : Type} [TopologicalSpace B] {m k : ℕ}
    {i₀ : {i : Fin m // (i : ℕ) ≤ k}} (x : Coh ℤ (2 * k + 1 - 2 * (i₀ : ℕ)) B)
    {i : {i : Fin m // (i : ℕ) ≤ k}} (hi : i ≠ i₀) : lhSoloFamilyOdd i₀ x i = 0 := by
  rw [lhSoloFamilyOdd]; simp [hi]

/-- A summand of the **odd** Leray–Hirsch map vanishes when its cohomology class does. -/
theorem lhTermOdd_zero (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) [Fintype ι]
    (k : ℕ) (i : {i : Fin m // (i : ℕ) ≤ k}) : lhTermOdd Z k i 0 = 0 := by
  unfold lhTermOdd
  simp only [map_zero, LinearMap.zero_apply, Work.Thom.cohTransport_zero]

/-- The **`i = 0` summand** of the *odd* Leray–Hirsch map is the pullback `π^*`: the odd-degree
companion of `lhTerm_zero_index`.  It is the unit law of `cupH'`
(`Work.Cohomology.cupH'_one_right`, i.e. `x ⌣ 1 = x`), with `1 = ζ⁰ = oneH`. -/
theorem lhTermOdd_zero_index {B : Type} [TopologicalSpace B] {ι : Type} [Fintype ι] {m : ℕ}
    (hm : 1 ≤ m) (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (k : ℕ)
    (x : Coh ℤ (2 * k + 1) B) :
    lhTermOdd Z k ⟨⟨0, hm⟩, Nat.zero_le k⟩ x
      = cohTransport (by omega : (2 * k + 1) + 0 = 2 * k + 1)
          ((CohMap (projMap Z) ℤ (2 * k + 1)).hom x) := by
  unfold lhTermOdd
  simp only [zetaPow_zero, cohTransport_rfl]
  exact Work.Cohomology.cupH'_one_right ℤ (Work.Whitney.ssB (ProjSpace Z)) (2 * k + 1 - 2 * 0)
     ((CohMap (projMap Z) ℤ (2 * k + 1 - 2 * 0)).hom x)

/-- The **odd** Leray–Hirsch map of a family supported at one index. -/
theorem lhMapOdd_eq_single (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) [Fintype ι]
    (k : ℕ) (i₀ : {i : Fin m // (i : ℕ) ≤ k}) (x : Coh ℤ (2 * k + 1 - 2 * (i₀ : ℕ)) B) :
    lhMapOdd Z k (lhSoloFamilyOdd i₀ x) = lhTermOdd Z k i₀ x := by
  unfold lhMapOdd
  have h : ∀ i, lhTermOdd Z k i (lhSoloFamilyOdd i₀ x i)
      = if i = i₀ then lhTermOdd Z k i₀ x else 0 := by
    intro i
    by_cases hi : i = i₀
    · subst hi; rw [lhSoloFamilyOdd_self, if_pos rfl]
    · rw [lhSoloFamilyOdd_of_ne x hi, lhTermOdd_zero, if_neg hi]
  rw [Finset.sum_congr rfl (fun i _ => h i), Finset.sum_ite_eq', if_pos (Finset.mem_univ i₀)]

/-! ## Injectivity of `π^*` -/

/-- **Injectivity of `π^*` in the odd degrees** `2k+1`, from the odd part of the Leray–Hirsch
theorem.  The proof is the one of `CohMap_projMap_injective_of_LerayHirsch` with the odd
decomposition in place of the even one. -/
theorem CohMap_projMap_injective_of_LerayHirschOdd {B : Type} [TopologicalSpace B]
    {ι : Type} [Fintype ι] {m : ℕ} (hm : 1 ≤ m)
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (h : LerayHirschOdd Z) (k : ℕ) :
    Function.Injective (CohMap (projMap Z) ℤ (2 * k + 1)).hom := by
  intro x y hxy
  have hx : lhMapOdd Z k (lhSoloFamilyOdd ⟨⟨0, hm⟩, Nat.zero_le k⟩ x)
      = (CohMap (projMap Z) ℤ (2 * k + 1)).hom x := by
    rw [lhMapOdd_eq_single, lhTermOdd_zero_index hm Z k x]
    exact cohTransport_rfl _
  have hy : lhMapOdd Z k (lhSoloFamilyOdd ⟨⟨0, hm⟩, Nat.zero_le k⟩ y)
      = (CohMap (projMap Z) ℤ (2 * k + 1)).hom y := by
    rw [lhMapOdd_eq_single, lhTermOdd_zero_index hm Z k y]
    exact cohTransport_rfl _
  have h2 : lhMapOdd Z k (lhSoloFamilyOdd ⟨⟨0, hm⟩, Nat.zero_le k⟩ x)
      = lhMapOdd Z k (lhSoloFamilyOdd ⟨⟨0, hm⟩, Nat.zero_le k⟩ y) := by
    rw [hx, hy, hxy]
  have h3 := (h k).1 h2
  have := congrFun h3 ⟨⟨0, hm⟩, Nat.zero_le k⟩
  simpa [lhSoloFamilyOdd_self] using this

end

/-- **The separation principle in every degree**: for a complex gluing-data bundle `Z` whose
projectivisation satisfies the *full* Leray–Hirsch theorem (`LerayHirschFull Z`: the even-degree
*and* odd-degree decomposition maps are bijective), the pullback

`π^* : H^n(B;ℤ) ⟶ H^n(P(E);ℤ)`

is injective for **every** `n`.

This is the form consumed by the Whitney-sum argument of `Submission/Work/Whitney/` §6(c) and by
`Work.LerayHirsch.WhitneySumFormulaFromLerayHirsch`: a relation between classes on `B` can be
checked after pulling back to the projectivisation, in *all* degrees (the odd degrees matter as soon
as the base has odd cohomology). -/
theorem CohMap_projMap_injective_of_LerayHirschFull {B : Type} [TopologicalSpace B]
    {ι : Type} [Fintype ι] {m : ℕ} (hm : 1 ≤ m)
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (h : Work.LerayHirsch.LerayHirschFull Z) (n : ℕ) :
    Function.Injective (Work.Thom.CohMap (Work.LerayHirsch.projMap Z) ℤ n).hom := by
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · have hn : n = 2 * k := by omega
    rw [hn]
    exact CohMap_projMap_injective_of_LerayHirsch hm Z h.1 k
  · have hn : n = 2 * k + 1 := by omega
    rw [hn]
    exact CohMap_projMap_injective_of_LerayHirschOdd hm Z h.2 k

end Work.LerayHirsch
