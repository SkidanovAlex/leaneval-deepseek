/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.MotV
-/
import Mathlib
import Submission.Work.MotV.Defs
import Submission.Work.MotV.hurwitzDefs
import Submission.Work.Genus.Defs
import Submission.Work.Genus.Order.ord_div
import Submission.Work.Genus.Order.ord_deriv_ge
import Submission.Work.Genus.Order.ord_deriv_nonneg
import Submission.Work.Genus.Order.ord_C_mul
import Submission.Work.Genus.Order.ord_add_eq_of_lt
import Submission.Work.Genus.OrderInf.ordInf_div
import Submission.Work.Genus.OrderInf.ordInf_deriv_ge
import Submission.Work.Genus.OrderInf.ordInf_mul
import Submission.Work.Genus.OrderInf.ordInf_polynomial
import Submission.Work.Genus.Deriv.deriv_add
import Submission.Work.Genus.Deriv.deriv_algebraMap
import Submission.Work.Genus.Deriv.deriv_eq_zero_iff
import Submission.Work.Genus.Main.exists_algebraMap_eq_of_natDegree_eq_zero
import Submission.Work.Genus.CharP.DescentBasic
import Submission.Work.Genus.CharP.exists_pow_eq_of_deriv_eq_zero
import Submission.Work.Genus.CharP.size_lt_of_pow_eq
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Node H0: the Hurwitz-lite lemma over a rational function field

This file proves `Work.MotV.hurwitz_five_ratFunc`: over an algebraically closed field `M` with
`ringChar M ≠ 5`, an element `r` of `M(y)` whose value `r * (r - 1)` is a fifth power at every
`ℤᵐ⁰`-valued valuation trivial on `M` is constant.

## Structure of the proof

* `ordc c f` (in `Submission.Work.MotV.hurwitzDefs`) is the order of vanishing of `f` at the point
  `c` of the affine line; `FifthHyp f` is the pointwise statement that the orders of `f` and of
  `f - 1` are divisible by `5` at every `c`.
* §1–§5 collect the elementary facts about the reduced form `f.num / f.denom` of a rational
  function, the multiplicities of the roots of a polynomial, the order at infinity, and the sums of
  the finite orders of the derivative.
* §6–§7 prove the counting argument: if `f` satisfies `FifthHyp` and `deriv f ≠ 0`, then the
  divisor of `deriv f` has too many zeros and not enough poles, a contradiction.  In characteristic
  `p ≠ 5` the inseparability of `f` is removed by the Frobenius descent (§7), the decreasing
  measure being `CharP.Size f = f.num.natDegree + f.denom.natDegree`.
* §9–§10 extract the hypothesis `FifthHyp` from the valuation-theoretic hypothesis, and the final
  theorem assembles the pieces.
-/

open Polynomial
open scoped WithZero

namespace Work.MotV
noncomputable section

/-! ## §1 Elementary facts about the reduced form -/

private lemma not_isRoot_denom_of_isRoot_num {M : Type*} [Field M] {f : RatFunc M} {c : M}
    (hc : f.num.IsRoot c) : ¬ f.denom.IsRoot c := by
  intro hd
  have h1 : (X - C c) ∣ f.num := dvd_iff_isRoot.mpr hc
  have h2 : (X - C c) ∣ f.denom := dvd_iff_isRoot.mpr hd
  exact (irreducible_X_sub_C c).not_isUnit
    ((RatFunc.isCoprime_num_denom f).isUnit_of_dvd' h1 h2)

private lemma not_isRoot_num_of_isRoot_denom {M : Type*} [Field M] {f : RatFunc M} {c : M}
    (hc : f.denom.IsRoot c) : ¬ f.num.IsRoot c :=
  fun h => not_isRoot_denom_of_isRoot_num h hc

private lemma not_isRoot_denom_of_isRoot_num_sub_denom {M : Type*} [Field M] {f : RatFunc M}
    {c : M} (hc : (f.num - f.denom).IsRoot c) : ¬ f.denom.IsRoot c := by
  intro hd
  have h1 : (X - C c) ∣ f.num - f.denom := dvd_iff_isRoot.mpr hc
  have h2 : (X - C c) ∣ f.denom := dvd_iff_isRoot.mpr hd
  have h3 : (X - C c) ∣ f.num := by
    have := dvd_add h1 h2
    simpa using this
  exact (irreducible_X_sub_C c).not_isUnit
    ((RatFunc.isCoprime_num_denom f).isUnit_of_dvd' h3 h2)

private lemma not_isRoot_num_sub_denom_of_isRoot_denom {M : Type*} [Field M] {f : RatFunc M}
    {c : M} (hc : f.denom.IsRoot c) : ¬ (f.num - f.denom).IsRoot c := by
  intro hd
  have h1 : (X - C c) ∣ f.num - f.denom := dvd_iff_isRoot.mpr hd
  have h2 : (X - C c) ∣ f.denom := dvd_iff_isRoot.mpr hc
  have h3 : (X - C c) ∣ f.num := by
    have := dvd_add h1 h2
    simpa using this
  exact (irreducible_X_sub_C c).not_isUnit
    ((RatFunc.isCoprime_num_denom f).isUnit_of_dvd' h3 h2)

private lemma not_isRoot_num_sub_denom_of_isRoot_num {M : Type*} [Field M] {f : RatFunc M}
    {c : M} (hc : f.num.IsRoot c) : ¬ (f.num - f.denom).IsRoot c := by
  intro hd
  have h1 : (X - C c) ∣ f.num - f.denom := dvd_iff_isRoot.mpr hd
  have h2 : (X - C c) ∣ f.num := dvd_iff_isRoot.mpr hc
  have h3 : (X - C c) ∣ f.denom := by
    have h := dvd_sub h2 h1
    simpa using h
  exact (irreducible_X_sub_C c).not_isUnit
    ((RatFunc.isCoprime_num_denom f).isUnit_of_dvd' h2 h3)

/-- The numerator and the denominator of `f - 1` in reduced form. -/
private lemma num_sub_one {M : Type*} [Field M] {f : RatFunc M} (hf1 : f - 1 ≠ 0) :
    (f - 1).num = f.num - f.denom ∧ (f - 1).denom = f.denom := by
  have hq : f.denom ≠ 0 := RatFunc.denom_ne_zero f
  have hcop : IsCoprime (f.num - f.denom) f.denom := by
    have h := (RatFunc.isCoprime_num_denom f).add_mul_right_left (-1)
    simpa [sub_eq_add_neg] using h
  have hmon : f.denom.Monic := RatFunc.monic_denom f
  have hx : algebraMap (Polynomial M) (RatFunc M) (f.num - f.denom)
      / algebraMap (Polynomial M) (RatFunc M) f.denom = f - 1 := by
    conv_rhs => rw [← RatFunc.num_div_denom f]
    rw [map_sub, sub_div, div_self (RatFunc.algebraMap_ne_zero hq)]
  have h := Work.Genus.Order.num_denom_eq_of_isCoprime hq hmon hcop hx.symm
  exact ⟨h.1.symm, h.2.symm⟩

/-! ## §2 Divisibility of the multiplicities of the roots -/

private lemma five_dvd_rootMultiplicity_num {M : Type*} [Field M] {f : RatFunc M} (h5 : FifthHyp f)
    {c : M} (hc : f.num.IsRoot c) : (5 : ℤ) ∣ (f.num.rootMultiplicity c : ℤ) := by
  have h := (h5 c).1
  have hmB : f.denom.rootMultiplicity c = 0 :=
    rootMultiplicity_eq_zero (not_isRoot_denom_of_isRoot_num hc)
  simpa only [ordc, hmB, Nat.cast_zero, sub_zero] using h

private lemma five_dvd_rootMultiplicity_denom {M : Type*} [Field M] {f : RatFunc M}
    (h5 : FifthHyp f) {c : M} (hc : f.denom.IsRoot c) :
    (5 : ℤ) ∣ (f.denom.rootMultiplicity c : ℤ) := by
  have h := (h5 c).1
  have hmA : f.num.rootMultiplicity c = 0 :=
    rootMultiplicity_eq_zero (not_isRoot_num_of_isRoot_denom hc)
  have h' : (5 : ℤ) ∣ -((f.denom.rootMultiplicity c : ℤ)) := by
    simpa only [ordc, hmA, Nat.cast_zero, zero_sub] using h
  simpa using h'

private lemma five_dvd_rootMultiplicity_num_sub_denom {M : Type*} [Field M] {f : RatFunc M}
    (hf1 : f - 1 ≠ 0) (h5 : FifthHyp f) {c : M} (hc : (f.num - f.denom).IsRoot c) :
    (5 : ℤ) ∣ ((f.num - f.denom).rootMultiplicity c : ℤ) := by
  have h := (h5 c).2
  have hn := num_sub_one hf1
  have hmB : f.denom.rootMultiplicity c = 0 :=
    rootMultiplicity_eq_zero (not_isRoot_denom_of_isRoot_num_sub_denom hc)
  simpa only [ordc, hn.1, hn.2, hmB, Nat.cast_zero, sub_zero] using h

/-- **Roots of a polynomial all of whose root multiplicities are divisible by `5` are at most a
fifth of its degree.** -/
private lemma five_mul_card_roots_le {M : Type*} [Field M] [IsAlgClosed M] [DecidableEq M]
    {P : Polynomial M} (hP : P ≠ 0)
    (h5 : ∀ c, P.IsRoot c → (5 : ℤ) ∣ (P.rootMultiplicity c : ℤ)) :
    5 * ((P.roots.toFinset).card : ℤ) ≤ (P.natDegree : ℤ) := by
  have hsum := sum_rootMultiplicity_eq_natDegree P hP
  have h5le : ∀ c ∈ P.roots.toFinset, (5 : ℤ) ≤ (P.rootMultiplicity c : ℤ) := by
    intro c hc
    have hroot : P.IsRoot c := (Polynomial.mem_roots hP).mp (Multiset.mem_toFinset.mp hc)
    have hpos : 0 < P.rootMultiplicity c := (rootMultiplicity_pos hP).mpr hroot
    obtain ⟨k, hk⟩ := h5 c hroot
    have hkpos : 0 < k := by
      by_contra hk0
      have hk0' : k ≤ 0 := not_lt.mp hk0
      nlinarith [hpos]
    have hk1 : (1 : ℤ) ≤ k := by omega
    nlinarith [hk, hk1]
  calc 5 * ((P.roots.toFinset).card : ℤ)
      = ∑ _c ∈ P.roots.toFinset, (5 : ℤ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ ∑ c ∈ P.roots.toFinset, (P.rootMultiplicity c : ℤ) := Finset.sum_le_sum h5le
    _ = (P.natDegree : ℤ) := hsum

/-! ## §3 A rational function of size zero is constant -/

private lemma isConst_of_size_eq_zero {M : Type*} [Field M] {f : RatFunc M}
    (h : Work.Genus.CharP.Size f = 0) : ∃ c : M, f = algebraMap M (RatFunc M) c := by
  have hnum : f.num.natDegree = 0 := by
    have := h; simp only [Work.Genus.CharP.Size] at this; omega
  have hden : f.denom.natDegree = 0 := by
    have := h; simp only [Work.Genus.CharP.Size] at this; omega
  exact Work.Genus.Main.exists_algebraMap_eq_of_natDegree_eq_zero hnum hden

/-! ## §4 The bound at infinity -/

private lemma deriv_algebraMap_const {M : Type*} [Field M] (c : M) :
    Work.Genus.deriv (algebraMap M (RatFunc M) c) = 0 := by
  have h1 : algebraMap M (RatFunc M) c
      = algebraMap (Polynomial M) (RatFunc M) (Polynomial.C c) := by
    rw [show (Polynomial.C c : Polynomial M) = algebraMap M (Polynomial M) c from rfl]
    exact (IsScalarTower.algebraMap_apply M (Polynomial M) (RatFunc M) c).symm
  rw [h1, Work.Genus.Deriv.deriv_algebraMap, Polynomial.derivative_C, map_zero]

private lemma deriv_sub_one {M : Type*} [Field M] (f : RatFunc M) :
    Work.Genus.deriv (f - 1) = Work.Genus.deriv f := by
  have h2 : (-(1 : RatFunc M)) = algebraMap M (RatFunc M) (-1) := by simp
  rw [sub_eq_add_neg, h2, Work.Genus.Deriv.deriv_add,
    deriv_algebraMap_const (M := M) (-1), add_zero]

private lemma max_ordInf_le_ordInf_deriv {M : Type*} [Field M] {f : RatFunc M} (hf : f ≠ 0)
    (hf1 : f - 1 ≠ 0) (hd : Work.Genus.deriv f ≠ 0) :
    max (Work.Genus.ordInf f) (Work.Genus.ordInf (f - 1)) + 1
      ≤ Work.Genus.ordInf (Work.Genus.deriv f) := by
  have h1 : Work.Genus.ordInf f + 1 ≤ Work.Genus.ordInf (Work.Genus.deriv f) :=
    Work.Genus.OrderInf.ordInf_deriv_ge hf hd
  have h2 : Work.Genus.ordInf (f - 1) + 1 ≤ Work.Genus.ordInf (Work.Genus.deriv f) := by
    have := Work.Genus.OrderInf.ordInf_deriv_ge hf1 (by rw [deriv_sub_one]; exact hd)
    rwa [deriv_sub_one] at this
  have hmax : max (Work.Genus.ordInf f) (Work.Genus.ordInf (f - 1)) + 1
      = max (Work.Genus.ordInf f + 1) (Work.Genus.ordInf (f - 1) + 1) := by
    rw [max_add_add_right]
  rw [hmax]
  exact max_le h1 h2

/-! ## §5 The sum of the finite orders -/

private lemma roots_num_subset_placeSet {M : Type*} [Field M] [DecidableEq M] (f : RatFunc M) :
    f.num.roots.toFinset ⊆ placeSet f := by
  intro c hc
  simp only [placeSet, Multiset.mem_toFinset, Multiset.mem_add] at hc ⊢
  tauto

private lemma roots_denom_subset_placeSet {M : Type*} [Field M] [DecidableEq M] (f : RatFunc M) :
    f.denom.roots.toFinset ⊆ placeSet f := by
  intro c hc
  simp only [placeSet, Multiset.mem_toFinset, Multiset.mem_add] at hc ⊢
  tauto

private lemma roots_num_sub_denom_subset_placeSet {M : Type*} [Field M] [DecidableEq M]
    (f : RatFunc M) : (f.num - f.denom).roots.toFinset ⊆ placeSet f := by
  intro c hc
  simp only [placeSet, Multiset.mem_toFinset, Multiset.mem_add] at hc ⊢
  tauto

private lemma roots_derivA_subset_placeSet {M : Type*} [Field M] [DecidableEq M] (f : RatFunc M) :
    (f.num.derivative * f.denom - f.num * f.denom.derivative).roots.toFinset ⊆ placeSet f := by
  intro c hc
  simp only [placeSet, Multiset.mem_toFinset, Multiset.mem_add] at hc ⊢
  tauto

private lemma sum_rootMultiplicity_of_subset {M : Type*} [Field M] [IsAlgClosed M] [DecidableEq M]
    {P : Polynomial M} (hP : P ≠ 0) {W : Finset M} (hW : P.roots.toFinset ⊆ W) :
    ∑ c ∈ W, (P.rootMultiplicity c : ℤ) = (P.natDegree : ℤ) := by
  have hmain : ∑ c ∈ P.roots.toFinset, (P.rootMultiplicity c : ℤ) = (P.natDegree : ℤ) :=
    sum_rootMultiplicity_eq_natDegree P hP
  have hsub : ∑ c ∈ P.roots.toFinset, (P.rootMultiplicity c : ℤ)
      = ∑ c ∈ W, (P.rootMultiplicity c : ℤ) := by
    refine Finset.sum_subset hW ?_
    intro c _ hc
    have hnr : ¬ P.IsRoot c := fun hr => hc (Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hP).mpr hr))
    rw [Polynomial.rootMultiplicity_eq_zero hnr, Nat.cast_zero]
  rw [← hsub, hmain]

/-- The numerator of `deriv f` does not vanish when `deriv f` does not vanish. -/
private lemma derivA_ne_zero {M : Type*} [Field M] {f : RatFunc M}
    (hd : Work.Genus.deriv f ≠ 0) :
    f.num.derivative * f.denom - f.num * f.denom.derivative ≠ 0 := by
  intro h
  apply hd
  rw [Work.Genus.Order.deriv_eq_div, h, map_zero, zero_div]

private lemma sum_ordc_deriv_eq {M : Type*} [Field M] [IsAlgClosed M] [DecidableEq M]
    {f : RatFunc M} (hf : f ≠ 0) (hd : Work.Genus.deriv f ≠ 0) :
    ∑ c ∈ placeSet f, ordc c (Work.Genus.deriv f)
      = ((f.num.derivative * f.denom - f.num * f.denom.derivative).natDegree : ℤ)
        - 2 * (f.denom.natDegree : ℤ) := by
  have hN0 : f.num.derivative * f.denom - f.num * f.denom.derivative ≠ 0 := derivA_ne_zero hd
  have hB0 : f.denom ≠ 0 := RatFunc.denom_ne_zero f
  have hB20 : f.denom ^ 2 ≠ 0 := pow_ne_zero 2 hB0
  have hterm : ∀ c ∈ placeSet f, ordc c (Work.Genus.deriv f)
      = ((f.num.derivative * f.denom - f.num * f.denom.derivative).rootMultiplicity c : ℤ)
        - 2 * (f.denom.rootMultiplicity c : ℤ) := by
    intro c _
    rw [ordc_eq_ord hd, Work.Genus.Order.deriv_eq_div,
      Work.Genus.Order.ord_div (irreducible_X_sub_C c) hN0 hB20]
    rw [Work.Genus.Order.multiplicity_pow_of_irreducible (irreducible_X_sub_C c) hB0 2,
      rootMultiplicity_eq_multiplicity, rootMultiplicity_eq_multiplicity]
    rw [ite_eq_right hN0, ite_eq_right hB0]
    push_cast
    first | refl_ring1 | ring
  have hsumN : ∑ c ∈ placeSet f,
      ((f.num.derivative * f.denom - f.num * f.denom.derivative).rootMultiplicity c : ℤ)
      = ((f.num.derivative * f.denom - f.num * f.denom.derivative).natDegree : ℤ) :=
    sum_rootMultiplicity_of_subset hN0 (roots_derivA_subset_placeSet f)
  have hsumB : ∑ c ∈ placeSet f, (f.denom.rootMultiplicity c : ℤ) = (f.denom.natDegree : ℤ) :=
    sum_rootMultiplicity_of_subset hB0 (roots_denom_subset_placeSet f)
  calc ∑ c ∈ placeSet f, ordc c (Work.Genus.deriv f)
      = ∑ c ∈ placeSet f, (((f.num.derivative * f.denom - f.num * f.denom.derivative).rootMultiplicity c : ℤ)
          - 2 * (f.denom.rootMultiplicity c : ℤ)) := Finset.sum_congr rfl hterm
    _ = (∑ c ∈ placeSet f, ((f.num.derivative * f.denom - f.num * f.denom.derivative).rootMultiplicity c : ℤ))
          - 2 * ∑ c ∈ placeSet f, (f.denom.rootMultiplicity c : ℤ) := by
        rw [Finset.sum_sub_distrib, Finset.mul_sum]
    _ = ((f.num.derivative * f.denom - f.num * f.denom.derivative).natDegree : ℤ)
          - 2 * (f.denom.natDegree : ℤ) := by rw [hsumN, hsumB]

private lemma ordInf_deriv_eq {M : Type*} [Field M] {f : RatFunc M}
    (hd : Work.Genus.deriv f ≠ 0) :
    Work.Genus.ordInf (Work.Genus.deriv f)
      = 2 * (f.denom.natDegree : ℤ)
        - ((f.num.derivative * f.denom - f.num * f.denom.derivative).natDegree : ℤ) := by
  have hN0 : f.num.derivative * f.denom - f.num * f.denom.derivative ≠ 0 := derivA_ne_zero hd
  have hB0 : f.denom ≠ 0 := RatFunc.denom_ne_zero f
  have hB20 : f.denom ^ 2 ≠ 0 := pow_ne_zero 2 hB0
  rw [Work.Genus.Order.deriv_eq_div,
    Work.Genus.OrderInf.ordInf_div (RatFunc.algebraMap_ne_zero hN0)
      (RatFunc.algebraMap_ne_zero hB20)]
  rw [Work.Genus.OrderInf.ordInf_polynomial, Work.Genus.OrderInf.ordInf_polynomial,
    Polynomial.natDegree_pow]
  push_cast
  first | refl_ring1 | ring

/-! ## §9 Insurance: the finite-place count, proved here -/

private lemma not_isRoot_num_of_isRoot_num_sub_denom {M : Type*} [Field M] {f : RatFunc M}
    {c : M} (hc : (f.num - f.denom).IsRoot c) : ¬ f.num.IsRoot c := by
  intro ha
  have h1 : (X - C c) ∣ f.num - f.denom := dvd_iff_isRoot.mpr hc
  have h2 : (X - C c) ∣ f.num := dvd_iff_isRoot.mpr ha
  have h3 : (X - C c) ∣ f.denom := by
    have h := dvd_sub h2 h1
    simpa using h
  exact (irreducible_X_sub_C c).not_isUnit
    ((RatFunc.isCoprime_num_denom f).isUnit_of_dvd' h2 h3)

private lemma derivA_ne_zero' {M : Type*} [Field M] {f : RatFunc M}
    (hd : Work.Genus.deriv f ≠ 0) :
    f.num.derivative * f.denom - f.num * f.denom.derivative ≠ 0 := derivA_ne_zero hd

private lemma ordc_deriv_ge_f (M : Type*) [Field M] [DecidableEq M] {f : RatFunc M} {c : M}
    (hf : f ≠ 0) (hd : Work.Genus.deriv f ≠ 0) :
    ordc c f - 1 ≤ ordc c (Work.Genus.deriv f) := by
  rw [ordc_eq_ord hf, ordc_eq_ord hd]
  exact Work.Genus.Order.ord_deriv_ge (irreducible_X_sub_C c) hf hd

private lemma ordc_deriv_ge_sub_one (M : Type*) [Field M] [DecidableEq M] {f : RatFunc M} {c : M}
    (hf1 : f - 1 ≠ 0) (hd : Work.Genus.deriv f ≠ 0) :
    ordc c (f - 1) - 1 ≤ ordc c (Work.Genus.deriv f) := by
  have hderiv : Work.Genus.deriv (f - 1) = Work.Genus.deriv f := deriv_sub_one f
  rw [ordc_eq_ord hf1, ordc_eq_ord hd]
  have := Work.Genus.Order.ord_deriv_ge (irreducible_X_sub_C c) hf1
    (by rw [hderiv]; exact hd)
  rwa [hderiv] at this

private lemma ordc_deriv_nonneg_f (M : Type*) [Field M] [DecidableEq M] {f : RatFunc M} {c : M}
    (hf : f ≠ 0) (hd : Work.Genus.deriv f ≠ 0) (h : 0 ≤ ordc c f) :
    0 ≤ ordc c (Work.Genus.deriv f) := by
  rw [ordc_eq_ord hf] at h
  rw [ordc_eq_ord hd]
  exact Work.Genus.Order.ord_deriv_nonneg (irreducible_X_sub_C c) hf hd h

/-- **The finite-place half of the Hurwitz count** (self-contained version). -/
private lemma sum_ordc_deriv_ge_priv {M : Type*} [Field M] [IsAlgClosed M] [DecidableEq M]
    {f : RatFunc M} (hf : f ≠ 0) (hf1 : f - 1 ≠ 0) (hd : Work.Genus.deriv f ≠ 0) :
    ((f.num.natDegree : ℤ) - ((f.num.roots.toFinset).card : ℤ))
      + (((f.num - f.denom).natDegree : ℤ) - (((f.num - f.denom).roots.toFinset).card : ℤ))
      - ((f.denom.natDegree : ℤ) + ((f.denom.roots.toFinset).card : ℤ))
    ≤ ∑ c ∈ placeSet f, ordc c (Work.Genus.deriv f) := by
  classical
  have hA0 : f.num ≠ 0 := RatFunc.num_ne_zero hf
  have hB0 : f.denom ≠ 0 := RatFunc.denom_ne_zero f
  have hAB0 : f.num - f.denom ≠ 0 := by
    intro h
    have h' : (f - 1).num = 0 := by rw [(num_sub_one hf1).1]; exact h
    exact hf1 (RatFunc.num_eq_zero_iff.mp h')
  set L : M → ℤ := fun c =>
      (if f.num.IsRoot c then ((f.num.rootMultiplicity c : ℤ) - 1) else 0)
    + (if (f.num - f.denom).IsRoot c then (((f.num - f.denom).rootMultiplicity c : ℤ) - 1) else 0)
    + (if f.denom.IsRoot c then (-((f.denom.rootMultiplicity c : ℤ) + 1)) else 0) with hL
  -- the pointwise bound
  have hpoint : ∀ c ∈ placeSet f, L c ≤ ordc c (Work.Genus.deriv f) := by
    intro c _
    by_cases hA : f.num.IsRoot c
    · have hB : ¬ f.denom.IsRoot c := not_isRoot_denom_of_isRoot_num hA
      have hAB : ¬ (f.num - f.denom).IsRoot c := not_isRoot_num_sub_denom_of_isRoot_num hA
      have hmB : f.denom.rootMultiplicity c = 0 := rootMultiplicity_eq_zero hB
      have hval : ordc c f = (f.num.rootMultiplicity c : ℤ) := by
        simp only [ordc, hmB, Nat.cast_zero, sub_zero]
      have := ordc_deriv_ge_f M (f := f) (c := c) hf hd
      simp only [hL, hA, hAB, hB, if_true, if_false, add_zero, zero_add]
      linarith
    · by_cases hAB : (f.num - f.denom).IsRoot c
      · have hB : ¬ f.denom.IsRoot c := not_isRoot_denom_of_isRoot_num_sub_denom hAB
        have hn := num_sub_one hf1
        have hmB : f.denom.rootMultiplicity c = 0 := rootMultiplicity_eq_zero hB
        have hval : ordc c (f - 1) = ((f.num - f.denom).rootMultiplicity c : ℤ) := by
          simp only [ordc, hn.1, hn.2, hmB, Nat.cast_zero, sub_zero]
        have := ordc_deriv_ge_sub_one M (f := f) (c := c) hf1 hd
        simp only [hL, hA, hAB, hB, if_true, if_false, add_zero, zero_add]
        linarith
      · by_cases hB : f.denom.IsRoot c
        · have hmA : f.num.rootMultiplicity c = 0 := rootMultiplicity_eq_zero hA
          have hval : ordc c f = -((f.denom.rootMultiplicity c : ℤ)) := by
            simp only [ordc, hmA, Nat.cast_zero, zero_sub]
          have := ordc_deriv_ge_f M (f := f) (c := c) hf hd
          simp only [hL, hA, hAB, hB, if_true, if_false, add_zero, zero_add]
          linarith
        · have hmA : f.num.rootMultiplicity c = 0 := rootMultiplicity_eq_zero hA
          have hmB : f.denom.rootMultiplicity c = 0 := rootMultiplicity_eq_zero hB
          have hval : ordc c f = 0 := by
            simp only [ordc, hmA, hmB, Nat.cast_zero, sub_self]
          have hnn : 0 ≤ ordc c (Work.Genus.deriv f) :=
            ordc_deriv_nonneg_f M (f := f) (c := c) hf hd (by rw [hval])
          simp only [hL, hA, hAB, hB, if_false, add_zero]
          exact hnn
  -- evaluate the sum of the lower bound
  have hLsum : ∑ c ∈ placeSet f, L c
      = ((f.num.natDegree : ℤ) - ((f.num.roots.toFinset).card : ℤ))
        + (((f.num - f.denom).natDegree : ℤ) - (((f.num - f.denom).roots.toFinset).card : ℤ))
        - ((f.denom.natDegree : ℤ) + ((f.denom.roots.toFinset).card : ℤ)) := by
    have h1 : ∑ c ∈ placeSet f, (if f.num.IsRoot c then ((f.num.rootMultiplicity c : ℤ) - 1) else 0)
        = (f.num.natDegree : ℤ) - ((f.num.roots.toFinset).card : ℤ) := by
      rw [← Finset.sum_filter]
      have hfilter : (placeSet f).filter (fun c => f.num.IsRoot c) = f.num.roots.toFinset := by
        refine Finset.ext fun c => ?_
        rw [Finset.mem_filter, Multiset.mem_toFinset, Polynomial.mem_roots hA0]
        exact ⟨fun h => h.2, fun h => ⟨roots_num_subset_placeSet f (Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hA0).mpr h)), h⟩⟩
      rw [hfilter, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one,
        sum_rootMultiplicity_eq_natDegree f.num hA0]
    have h2 : ∑ c ∈ placeSet f,
        (if (f.num - f.denom).IsRoot c then (((f.num - f.denom).rootMultiplicity c : ℤ) - 1) else 0)
        = ((f.num - f.denom).natDegree : ℤ) - (((f.num - f.denom).roots.toFinset).card : ℤ) := by
      rw [← Finset.sum_filter]
      have hfilter : (placeSet f).filter (fun c => (f.num - f.denom).IsRoot c)
          = (f.num - f.denom).roots.toFinset := by
        refine Finset.ext fun c => ?_
        rw [Finset.mem_filter, Multiset.mem_toFinset, Polynomial.mem_roots hAB0]
        exact ⟨fun h => h.2, fun h => ⟨roots_num_sub_denom_subset_placeSet f (Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hAB0).mpr h)), h⟩⟩
      rw [hfilter, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one,
        sum_rootMultiplicity_eq_natDegree (f.num - f.denom) hAB0]
    have h3 : ∑ c ∈ placeSet f, (if f.denom.IsRoot c then (-((f.denom.rootMultiplicity c : ℤ) + 1)) else 0)
        = -((f.denom.natDegree : ℤ) + ((f.denom.roots.toFinset).card : ℤ)) := by
      rw [← Finset.sum_filter]
      have hfilter : (placeSet f).filter (fun c => f.denom.IsRoot c) = f.denom.roots.toFinset := by
        refine Finset.ext fun c => ?_
        rw [Finset.mem_filter, Multiset.mem_toFinset, Polynomial.mem_roots hB0]
        exact ⟨fun h => h.2, fun h => ⟨roots_denom_subset_placeSet f (Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hB0).mpr h)), h⟩⟩
      rw [hfilter]
      have : ∀ c ∈ f.denom.roots.toFinset, (-((f.denom.rootMultiplicity c : ℤ) + 1))
          = -((f.denom.rootMultiplicity c : ℤ)) - 1 := fun c _ => by ring
      rw [Finset.sum_congr rfl this, Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.sum_const,
        nsmul_eq_mul, mul_one, sum_rootMultiplicity_eq_natDegree f.denom hB0]
      first | refl_ring1 | ring
    rw [hL]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, h1, h2, h3]
    first | refl_ring1 | ring
  calc ((f.num.natDegree : ℤ) - ((f.num.roots.toFinset).card : ℤ))
      + (((f.num - f.denom).natDegree : ℤ) - (((f.num - f.denom).roots.toFinset).card : ℤ))
      - ((f.denom.natDegree : ℤ) + ((f.denom.roots.toFinset).card : ℤ))
      = ∑ c ∈ placeSet f, L c := hLsum.symm
    _ ≤ ∑ c ∈ placeSet f, ordc c (Work.Genus.deriv f) := Finset.sum_le_sum hpoint

/-! ## §6 The counting argument -/

private lemma false_of_fifthHyp_of_deriv_ne_zero {M : Type*} [Field M] [IsAlgClosed M]
    {f : RatFunc M} (hf : FifthHyp f) (hd : Work.Genus.deriv f ≠ 0) : False := by
  classical
  have hf0 : f ≠ 0 := by
    intro h
    exact hd (by rw [h]; simp [Work.Genus.deriv])
  have hf1 : f - 1 ≠ 0 := by
    intro h
    have h1 : f = 1 := sub_eq_zero.mp h
    exact hd (by rw [h1]; simp [Work.Genus.deriv])
  have hB0 : f.denom ≠ 0 := RatFunc.denom_ne_zero f
  -- the finite count
  have hlow := sum_ordc_deriv_ge_priv (f := f) hf0 hf1 hd
  have hsum := sum_ordc_deriv_eq (f := f) hf0 hd
  have hinf := ordInf_deriv_eq (f := f) hd
  have hmax := max_ordInf_le_ordInf_deriv hf0 hf1 hd
  -- the order of `f` and of `f - 1` at infinity
  have hordf : Work.Genus.ordInf f = (f.denom.natDegree : ℤ) - (f.num.natDegree : ℤ) := by
    simp only [Work.Genus.ordInf, RatFunc.intDegree]
    first | refl_ring1 | ring
  have hordf1 : Work.Genus.ordInf (f - 1)
      = (f.denom.natDegree : ℤ) - ((f.num - f.denom).natDegree : ℤ) := by
    have hn := num_sub_one hf1
    simp only [Work.Genus.ordInf, RatFunc.intDegree, hn.1, hn.2]
    first | refl_ring1 | ring
  -- the bound on the degree of the numerator of the derivative
  have hNbound : ((f.num.derivative * f.denom - f.num * f.denom.derivative).natDegree : ℤ)
      ≤ 2 * (f.denom.natDegree : ℤ)
        - (max (Work.Genus.ordInf f) (Work.Genus.ordInf (f - 1)) + 1) := by
    linarith
  -- the key inequality
  have hkey : ((f.num.natDegree : ℤ) - ((f.num.roots.toFinset).card : ℤ))
      + (((f.num - f.denom).natDegree : ℤ) - (((f.num - f.denom).roots.toFinset).card : ℤ))
      - ((f.denom.natDegree : ℤ) + ((f.denom.roots.toFinset).card : ℤ))
      + (max (Work.Genus.ordInf f) (Work.Genus.ordInf (f - 1)) + 1) ≤ 0 := by
    linarith
  -- divisibility bounds on the numbers of roots
  have h5A : 5 * ((f.num.roots.toFinset).card : ℤ) ≤ (f.num.natDegree : ℤ) :=
    five_mul_card_roots_le (f.num_ne_zero hf0) (fun c hc => five_dvd_rootMultiplicity_num hf hc)
  have h5B : 5 * ((f.denom.roots.toFinset).card : ℤ) ≤ (f.denom.natDegree : ℤ) :=
    five_mul_card_roots_le hB0 (fun c hc => five_dvd_rootMultiplicity_denom hf hc)
  have h5AB : 5 * (((f.num - f.denom).roots.toFinset).card : ℤ)
      ≤ ((f.num - f.denom).natDegree : ℤ) :=
    five_mul_card_roots_le (fun hP => hf1 (by
      have h0 : (f - 1).num = 0 := by rw [(num_sub_one hf1).1]; exact hP
      exact RatFunc.num_eq_zero_iff.mp h0))
      (fun c hc => five_dvd_rootMultiplicity_num_sub_denom hf1 hf hc)
  -- `b ≤ max a d`
  have hbmax : (f.denom.natDegree : ℤ)
      ≤ max (f.num.natDegree : ℤ) ((f.num - f.denom).natDegree : ℤ) := by
    rcases lt_or_ge f.num.natDegree f.denom.natDegree with hlt | hge
    · have hd_eq : (f.num - f.denom).natDegree = f.denom.natDegree :=
        Polynomial.natDegree_sub_eq_right_of_natDegree_lt hlt
      rw [hd_eq]
      exact le_max_right _ _
    · exact le_trans (by exact_mod_cast hge) (le_max_left _ _)
  set M₀ : ℤ := max (f.num.natDegree : ℤ) ((f.num - f.denom).natDegree : ℤ) with hM₀
  have haM : (f.num.natDegree : ℤ) ≤ M₀ := by rw [hM₀]; exact le_max_left _ _
  have hdM : ((f.num - f.denom).natDegree : ℤ) ≤ M₀ := by rw [hM₀]; exact le_max_right _ _
  have hM₀0 : (0 : ℤ) ≤ M₀ := le_trans (Int.natCast_nonneg _) haM
  have hbM : (f.denom.natDegree : ℤ) ≤ M₀ := by rw [hM₀]; exact hbmax
  -- `max a d = a + d - min a d`
  have hmaxmin : max (f.num.natDegree : ℤ) ((f.num - f.denom).natDegree : ℤ)
      = (f.num.natDegree : ℤ) + ((f.num - f.denom).natDegree : ℤ)
        - min (f.num.natDegree : ℤ) ((f.num - f.denom).natDegree : ℤ) := by
    rcases le_total (f.num.natDegree : ℤ) ((f.num - f.denom).natDegree : ℤ) with hle | hle
    · rw [min_eq_left hle, max_eq_right hle]; ring
    · rw [min_eq_right hle, max_eq_left hle]; ring
  have hkey' : M₀ - (((f.num.roots.toFinset).card : ℤ)
      + (((f.num - f.denom).roots.toFinset).card : ℤ) + ((f.denom.roots.toFinset).card : ℤ)) + 1 ≤ 0 := by
    rw [hordf, hordf1] at hkey
    have h3 : max ((f.denom.natDegree : ℤ) - (f.num.natDegree : ℤ))
        ((f.denom.natDegree : ℤ) - ((f.num - f.denom).natDegree : ℤ))
        = (f.denom.natDegree : ℤ)
          - min (f.num.natDegree : ℤ) ((f.num - f.denom).natDegree : ℤ) := by
      rcases le_total (f.num.natDegree : ℤ) ((f.num - f.denom).natDegree : ℤ) with hle | hle
      · rw [min_eq_left hle, max_eq_left (sub_le_sub_left hle (f.denom.natDegree : ℤ))]
      · rw [min_eq_right hle, max_eq_right (sub_le_sub_left hle (f.denom.natDegree : ℤ))]
    rw [h3] at hkey
    rw [hM₀, hmaxmin]
    linarith
  have hz : 5 * (((f.num.roots.toFinset).card : ℤ)
      + (((f.num - f.denom).roots.toFinset).card : ℤ) + ((f.denom.roots.toFinset).card : ℤ))
      ≤ 3 * M₀ := by
    linarith [h5A, h5B, h5AB, haM, hdM, hbM]
  linarith


/-! ## §7 The characteristic-zero / characteristic-`p` dichotomy -/

private lemma charZero_or_charP {M : Type*} [Field M] (hM : ringChar M ≠ 5) :
    CharZero M ∨ ∃ p : ℕ, Nat.Prime p ∧ p ≠ 5 ∧ CharP M p := by
  rcases CharP.char_is_prime_or_zero M (ringChar M) with hprime | hzero
  · exact Or.inr ⟨ringChar M, hprime, fun h => hM h, ringChar.charP M⟩
  · exact Or.inl ((CharP.charP_zero_iff_charZero M).mp (ringChar.eq_iff.mp hzero))

/-- **The Frobenius descent.**  In characteristic `p ≠ 5`, if `f = u ^ p` satisfies the pointwise
hypothesis then so does `u`: the orders of `f` and of `f - 1 = (u - 1) ^ p` are `p` times those of
`u` and of `u - 1`, and `5` is coprime to `p`. -/
private lemma fifthHyp_pow {M : Type*} [Field M] {p : ℕ} [Fact p.Prime] [CharP M p]
    (hp5 : p ≠ 5) {f u : RatFunc M} (hf : FifthHyp f) (hu : f = u ^ p) (hu1 : u ≠ 1) :
    FifthHyp u := by
  classical
  have hnotdvd : ¬ ((5 : ℤ) ∣ (p : ℤ)) := by
    rintro h
    have h' : p = 5 := (Fact.out : Nat.Prime p).dvd_iff_eq (by norm_num) |>.mp (Int.ofNat_dvd.mp h)
    exact hp5 h'
  intro c
  constructor
  · by_cases hu0 : u = 0
    · rw [ordc, hu0, RatFunc.num_zero, RatFunc.denom_zero, Polynomial.rootMultiplicity_zero]
      have h1 : Polynomial.rootMultiplicity c (1 : Polynomial M) = 0 := by
        rw [show (1 : Polynomial M) = Polynomial.C (1 : M) from Polynomial.C_1.symm,
          Polynomial.rootMultiplicity_C]
      simp [h1]
    · have h1 := (hf c).1
      rw [hu, ordc_pow hu0 p] at h1
      rcases (show Prime (5 : ℤ) from by norm_num).dvd_mul.mp h1 with h | h
      · exact absurd h hnotdvd
      · exact h
  · by_cases hu1' : u - 1 = 0
    · exact absurd (sub_eq_zero.mp hu1') hu1
    · have h2 := (hf c).2
      have hsub : f - 1 = (u - 1) ^ p := by
        rw [hu]
        conv_lhs => rw [← one_pow p]
        exact (sub_pow_char u (1 : RatFunc M)).symm
      rw [hsub, ordc_pow hu1' p] at h2
      rcases (show Prime (5 : ℤ) from by norm_num).dvd_mul.mp h2 with h | h
      · exact absurd h hnotdvd
      · exact h

/-! ## §8 The strong induction -/

private theorem isConst_of_fifthHyp_aux {M : Type*} [Field M] [IsAlgClosed M]
    (hM : ringChar M ≠ 5) :
    ∀ n : ℕ, ∀ f : RatFunc M, FifthHyp f → Work.Genus.CharP.Size f = n →
      ∃ c : M, f = algebraMap M (RatFunc M) c := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro f hf hsize
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · exact isConst_of_size_eq_zero (by rw [hsize]; exact hn0)
    · rcases eq_or_ne (Work.Genus.deriv f) 0 with hd | hd
      · rcases charZero_or_charP (M := M) hM with hcz | ⟨p, hpprime, hp5, hchar⟩
        · haveI : CharZero M := hcz
          exact Work.Genus.Deriv.deriv_eq_zero_iff f |>.mp hd
        · haveI : Fact p.Prime := ⟨hpprime⟩
          haveI : CharP M p := hchar
          haveI : PerfectField M := IsAlgClosed.perfectField M
          obtain ⟨u, hu⟩ := Work.Genus.CharP.exists_pow_eq_of_deriv_eq_zero (p := p) hd
          have hlt : Work.Genus.CharP.Size u < n := by
            have := Work.Genus.CharP.size_lt_of_pow_eq (x := f) (X := u) (p := p) hu
              (by rw [hsize]; exact hnpos)
            rwa [hsize] at this
          have hu1 : u ≠ 1 := by
            intro h1
            have h1' : f = 1 := by rw [hu, h1, one_pow]
            have : Work.Genus.CharP.Size f = 0 := by rw [h1']; simp [Work.Genus.CharP.Size]
            omega
          have hu5 : FifthHyp u := fifthHyp_pow hp5 hf hu hu1
          obtain ⟨c, hc⟩ := ih (Work.Genus.CharP.Size u) hlt u hu5 rfl
          exact ⟨c ^ p, by rw [hu, hc, ← map_pow]⟩
      · exact (false_of_fifthHyp_of_deriv_ne_zero hf hd).elim


/-! ## §10 The place valuation and the extraction of `FifthHyp` -/

variable {M : Type*} [Field M]

private lemma ordc_neg [DecidableEq M] {c : M} (f : RatFunc M) : ordc c (-f) = ordc c f := by
  rcases eq_or_ne f 0 with rfl | hf
  · rw [neg_zero]
  · have h1 : (-f) = algebraMap M (RatFunc M) (-1) * f := by
      rw [map_neg, map_one, neg_one_mul]
    rw [h1, ordc_mul (by simp) hf, ordc_algebraMap]
    first | refl_ring1 | ring

private lemma ordc_zero [DecidableEq M] {c : M} : ordc c (0 : RatFunc M) = 0 := by
  rw [ordc, RatFunc.num_zero, RatFunc.denom_zero]
  have h : Polynomial.rootMultiplicity c (1 : Polynomial M) = 0 := by
    rw [show (1 : Polynomial M) = Polynomial.C (1 : M) from Polynomial.C_1.symm,
      Polynomial.rootMultiplicity_C]
  simp [h]

private lemma ordc_one {c : M} : ordc c (1 : RatFunc M) = 0 := by
  rw [show (1 : RatFunc M) = algebraMap M (RatFunc M) 1 from by simp, ordc_algebraMap]

private lemma ordc_neg_one {c : M} : ordc c (-1 : RatFunc M) = 0 := by
  rw [show (-1 : RatFunc M) = algebraMap M (RatFunc M) (-1) from by simp, ordc_algebraMap]

private lemma min_ordc_le_ordc_add [DecidableEq M] {c : M} {f g : RatFunc M} (hf : f ≠ 0)
    (hg : g ≠ 0) (hfg : f + g ≠ 0) : min (ordc c f) (ordc c g) ≤ ordc c (f + g) := by
  rw [ordc_eq_ord hf, ordc_eq_ord hg, ordc_eq_ord hfg]
  exact Work.Genus.Order.min_ord_le_ord_add (irreducible_X_sub_C c) hf hg hfg

private lemma ordc_add_eq_of_lt [DecidableEq M] {c : M} {f g : RatFunc M} (hf : f ≠ 0)
    (hg : g ≠ 0) (h : ordc c f < ordc c g) : ordc c (f + g) = ordc c f := by
  have hfg : f + g ≠ 0 := by
    intro h0
    have hg' : g = -f := (neg_eq_iff_add_eq_zero.mpr h0).symm
    rw [hg', ordc_neg] at h
    exact lt_irrefl _ h
  rw [ordc_eq_ord hfg, ordc_eq_ord hf]
  exact Work.Genus.Order.ord_add_eq_of_lt (irreducible_X_sub_C c) hf
    (by rwa [ordc_eq_ord hf, ordc_eq_ord hg] at h)

private lemma exp_max' (a b : ℤ) :
    max (WithZero.exp a) (WithZero.exp b) = WithZero.exp (max a b) := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, max_eq_right (WithZero.exp_le_exp.mpr h)]
  · rw [max_eq_left h, max_eq_left (WithZero.exp_le_exp.mpr h)]

private def placeValFun (M : Type*) [Field M] (c : M) (f : RatFunc M) : ℤᵐ⁰ :=
  letI := Classical.decEq (RatFunc M)
  if f = 0 then 0 else WithZero.exp (-(ordc c f))

private lemma placeValFun_apply {c : M} {f : RatFunc M} (hf : f ≠ 0) :
    placeValFun M c f = WithZero.exp (-(ordc c f)) := by
  rw [placeValFun]
  exact ite_eq_right hf

private lemma placeValFun_zero {c : M} : placeValFun M c (0 : RatFunc M) = 0 := by
  rw [placeValFun]
  exact ite_eq_left rfl

/-- The place valuation at the point `c` of the affine line: `f ↦ exp (-ordc c f)`. -/
private def placeVal (M : Type*) [Field M] [DecidableEq M] (c : M) : Valuation (RatFunc M) ℤᵐ⁰ where
  toFun := placeValFun M c
  map_zero' := placeValFun_zero
  map_one' := by
    rw [placeValFun_apply (one_ne_zero : (1 : RatFunc M) ≠ 0), ordc_one, neg_zero,
      WithZero.exp_zero]
  map_mul' f g := by
    rcases eq_or_ne f 0 with rfl | hf
    · rw [zero_mul, placeValFun_zero, zero_mul]
    rcases eq_or_ne g 0 with rfl | hg
    · rw [mul_zero, placeValFun_zero, mul_zero]
    calc placeValFun M c (f * g)
        = WithZero.exp (-(ordc c (f * g))) := placeValFun_apply (mul_ne_zero hf hg)
      _ = WithZero.exp (-(ordc c f + ordc c g)) := by rw [ordc_mul hf hg]
      _ = WithZero.exp (-(ordc c f)) * WithZero.exp (-(ordc c g)) := by
            rw [neg_add, WithZero.exp_add]
      _ = placeValFun M c f * placeValFun M c g := by
            rw [placeValFun_apply hf, placeValFun_apply hg]
  map_add_le_max' f g := by
    rcases eq_or_ne f 0 with rfl | hf
    · rw [zero_add, placeValFun_zero]
      exact le_max_right 0 (placeValFun M c g)
    rcases eq_or_ne g 0 with rfl | hg
    · rw [add_zero, placeValFun_zero]
      exact le_max_left (placeValFun M c f) 0
    rcases eq_or_ne (f + g) 0 with hfg | hfg
    · rw [hfg, placeValFun_zero]
      exact zero_le
    · rw [placeValFun_apply hfg, placeValFun_apply hf, placeValFun_apply hg, exp_max']
      refine WithZero.exp_le_exp.mpr ?_
      have h := min_ordc_le_ordc_add (c := c) hf hg hfg
      rw [max_neg_neg]
      exact neg_le_neg h

private lemma placeVal_apply [DecidableEq M] {c : M} {f : RatFunc M} (hf : f ≠ 0) :
    placeVal M c f = WithZero.exp (-(ordc c f)) := placeValFun_apply hf

private lemma placeVal_zero [DecidableEq M] {c : M} :
    placeVal M c (0 : RatFunc M) = 0 := placeValFun_zero

private lemma placeVal_ne_zero [DecidableEq M] {c : M} {f : RatFunc M} (hf : f ≠ 0) :
    placeVal M c f ≠ 0 := by
  rw [placeVal_apply hf]
  exact WithZero.exp_ne_zero

private lemma algebraMap_ne_zero' {k : M} (hk : k ≠ 0) :
    algebraMap M (RatFunc M) k ≠ 0 := by
  rw [RatFunc.algebraMap_eq_C]
  intro h
  have h' : RatFunc.C k = RatFunc.C (0 : M) := by rw [h, map_zero]
  exact hk (RatFunc.C_injective h')

private lemma placeVal_triv [DecidableEq M] (c : M) : TrivOn M (placeVal M c) := by
  intro k hk
  rw [placeVal_apply (algebraMap_ne_zero' hk), ordc_algebraMap, neg_zero, WithZero.exp_zero]

/-- **The pointwise hypothesis from a fifth-power valued `r * (r - 1)`** (self-contained
version). -/
theorem fifthHyp_of_fifthPowerValued' [DecidableEq M] (r : RatFunc M)
    (hr : FifthPowerValued M (r * (r - 1))) : FifthHyp r := by
  intro c
  have hsum : (5 : ℤ) ∣ ordc c r + ordc c (r - 1) := by
    by_cases hg : r * (r - 1) = 0
    · rcases mul_eq_zero.mp hg with h | h
      · rw [h, ordc_zero, zero_sub, ordc_neg_one, add_zero]
        exact dvd_zero 5
      · have hr1 : r = 1 := sub_eq_zero.mp h
        rw [hr1, ordc_one, sub_self, ordc_zero, add_zero]
        exact dvd_zero 5
    · have hr0 : r ≠ 0 := fun h => hg (by rw [h, zero_mul])
      have hr1 : r - 1 ≠ 0 := fun h => hg (by rw [h, mul_zero])
      obtain ⟨u, hu⟩ := hr (placeVal M c) (placeVal_triv c)
      have hu_ne : placeVal M c u ≠ 0 := by
        intro h
        have h0 : placeVal M c (r * (r - 1)) = 0 := by
          rw [hu, h, zero_pow (by norm_num : 5 ≠ 0)]
        exact placeVal_ne_zero hg h0
      have hu0 : u ≠ 0 := by
        intro h
        exact hu_ne (by rw [h, placeVal_zero])
      have key : -(ordc c (r * (r - 1))) = -(5 * ordc c u) := by
        have h1 : WithZero.exp (-(ordc c (r * (r - 1))))
            = WithZero.exp (5 • (-(ordc c u))) := by
          rw [placeVal_apply hg, placeVal_apply hu0, ← WithZero.exp_nsmul] at hu
          exact hu
        have h2 := WithZero.exp_inj.mp h1
        rwa [show (5 : ℕ) • (-(ordc c u)) = -(5 * ordc c u) from by rw [nsmul_eq_mul]; ring] at h2
      have h5 : (5 : ℤ) ∣ ordc c (r * (r - 1)) := by
        rw [neg_inj.mp key]
        exact dvd_mul_right 5 _
      rwa [ordc_mul hr0 hr1] at h5
  -- split the sum
  rcases eq_or_ne r 0 with h0 | hr0
  · subst h0
    refine ⟨by rw [ordc_zero]; exact dvd_zero 5, ?_⟩
    rw [show (0 : RatFunc M) - 1 = -1 from by ring, ordc_neg_one]
    exact dvd_zero 5
  rcases eq_or_ne (r - 1) 0 with h1 | hr1
  · have hr_eq : r = 1 := sub_eq_zero.mp h1
    subst hr_eq
    refine ⟨by rw [ordc_one]; exact dvd_zero 5, ?_⟩
    rw [sub_self, ordc_zero]
    exact dvd_zero 5
  by_cases hA : ordc c (r - 1) < 0
  · -- `q < 0` forces `p = q`
    have hp : ordc c r = ordc c (r - 1) := by
      have h := ordc_add_eq_of_lt (c := c) (f := r - 1) (g := 1) hr1 one_ne_zero (by
        rw [ordc_one]; exact hA)
      rwa [show r - 1 + 1 = r from sub_add_cancel r 1] at h
    rw [hp] at hsum
    have h2 : (5 : ℤ) ∣ 2 * ordc c (r - 1) := by simpa [two_mul] using hsum
    rcases (show Prime (5 : ℤ) from by norm_num).dvd_mul.mp h2 with h | h
    · exact absurd h (by norm_num)
    · exact ⟨hp.symm ▸ h, h⟩
  · rw [not_lt] at hA
    by_cases hB : ordc c r < 0
    · -- `p < 0` forces `q = p`
      have hq : ordc c (r - 1) = ordc c r := by
        have h := ordc_add_eq_of_lt (c := c) (f := r) (g := -1) hr0 (by simp) (by
          rw [ordc_neg_one]; exact hB)
        rwa [show r + (-1) = r - 1 from (sub_eq_add_neg r 1).symm] at h
      rw [hq] at hsum
      have h2 : (5 : ℤ) ∣ 2 * ordc c r := by simpa [two_mul] using hsum
      rcases (show Prime (5 : ℤ) from by norm_num).dvd_mul.mp h2 with h | h
      · exact absurd h (by norm_num)
      · exact ⟨h, hq.symm ▸ h⟩
    · rw [not_lt] at hB
      -- both orders are non-negative, and at most one of them is positive
      have hp0 : ordc c r = 0 ∨ ordc c (r - 1) = 0 := by
        by_contra hc
        rw [not_or] at hc
        have hpp : 0 < ordc c r := lt_of_le_of_ne hB (Ne.symm hc.1)
        have hqq : 0 < ordc c (r - 1) := lt_of_le_of_ne hA (Ne.symm hc.2)
        have hne : (1 - r : RatFunc M) ≠ 0 := by
          intro h0
          have : r = 1 := (sub_eq_zero.mp h0).symm
          rw [this, ordc_one] at hpp
          exact lt_irrefl 0 hpp
        have hne2 : r + (1 - r) ≠ 0 := by
          rw [show r + (1 - r) = (1 : RatFunc M) from by ring]
          exact one_ne_zero
        have hmin := min_ordc_le_ordc_add (c := c) (f := r) (g := 1 - r) hr0 hne hne2
        have h1' : ordc c (1 - r) = ordc c (r - 1) := by
          rw [show (1 - r : RatFunc M) = -(r - 1) from by ring, ordc_neg]
        rw [h1', show r + (1 - r) = (1 : RatFunc M) from by ring, ordc_one] at hmin
        exact absurd (lt_of_lt_of_le (lt_min hpp hqq) hmin) (lt_irrefl 0)
      rcases hp0 with h | h
      · rw [h, zero_add] at hsum
        exact ⟨h.symm ▸ dvd_zero 5, hsum⟩
      · rw [h, add_zero] at hsum
        exact ⟨hsum, h.symm ▸ dvd_zero 5⟩



/-- Node H0 (Hurwitz-lite over a rational function field, used by the constants-only node).  Over
an algebraically closed field `M` with `ringChar M ≠ 5`, an element `r` of `M(y)` whose value
`r * (r - 1)` is a fifth power at every `ℤᵐ⁰`-valued valuation trivial on `M` is constant.

Route.  Since `M` is algebraically closed, the `ℤᵐ⁰`-valued valuations of `M(y)` trivial on `M`
are `k · ord_Q` for the places `Q ∈ M ∪ {∞}`, so `hr` says `5 ∣ ord_Q (r(r-1))` at every place;
because at most one of `ord_Q r`, `ord_Q (r - 1)` is nonzero unless `Q` is a pole, this is
equivalent to: every zero and every pole order of `r` and of `r - 1` is divisible by `5`.  Then
`div r = 5D` for some divisor `D` (the value group of `M(y)*` is `ℤ`, generated by `y - c`), so
`r = c · s^5` and `r - 1 = c' · t^5`; taking derivatives, `r'` has all zero orders `≥ 4` and all
pole orders `≥ 4n + 1` where `n = deg r`, so `deg (div r') = 2n - 2 ≥ (3n)(4/5) = 12n/5` (three
fibres `0`, `1`, `∞` of at least `n/5` points each), forcing `n = 0`.  Concretely: build the
places as `HeightOneSpectrum` valuations of `Polynomial M` (at `X` and at `X - C c`) plus
`inftyValuation`, and prove the elementary local bounds `ord_Q (r') ≥ ord_Q (r - r(Q)) - 1` and
`deg (div r') = 2n - 2`.
`char ≠ 5` is necessary: in characteristic 5, `r = s⁵` satisfies the hypothesis. -/
theorem hurwitz_five_ratFunc {M : Type*} [Field M] [IsAlgClosed M] (hM : ringChar M ≠ 5)
    (r : RatFunc M) (hr : FifthPowerValued M (r * (r - 1))) :
    ∃ c : M, algebraMap M _ c = r := by
  classical
  obtain ⟨c, hc⟩ := isConst_of_fifthHyp_aux hM (Work.Genus.CharP.Size r) r
    (fifthHyp_of_fifthPowerValued' r hr) rfl
  exact ⟨c, hc.symm⟩

end
end Work.MotV
