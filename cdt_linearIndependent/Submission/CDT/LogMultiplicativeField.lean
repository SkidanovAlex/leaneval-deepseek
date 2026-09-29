import Mathlib
import Submission.CDT.LogMultiplicative
import Submission.Commons.LinearAlgebra.linearIndependent_map_of_linearIndependent_fintype

/-!
# Function-field Lindemann–Weierstrass with field coefficients

`Submission.CDT.LogMultiplicative` proves the multiplicative-dependence form of the function-field
Lindemann–Weierstrass theorem with *rational* (equivalently, by clearing denominators, integer)
coefficients: if `Σᵢ cᵢ·(dRat fᵢ)/fᵢ = dRat h` with `cᵢ ∈ ℚ`, then some nontrivial product
`∏ᵢ fᵢ ^ mᵢ` (`mᵢ ∈ ℤ`) is constant.

Here the coefficients are allowed to be arbitrary elements of `K`: if `Σᵢ cᵢ·(dRat fᵢ)/fᵢ = dRat h`
with `c : ι → K` not identically zero, then again some nontrivial product `∏ᵢ fᵢ ^ mᵢ` with
*integer* exponents is constant.  The extra ingredient is the fact that a linear system with
rational coefficients has the same solution space over `ℚ` as over its field extensions
(`Commons.LinearAlgebra.linearIndependent_map_of_linearIndependent_fintype`): the residue relation
`Σᵢ cᵢ · ordAt α fᵢ = 0` (with `cᵢ ∈ K`, `ordAt α fᵢ ∈ ℤ`) is a `K`-linear relation among integer
vectors, hence produces a nonzero *rational* solution — and one only needs the relation at the
finitely many zeros and poles of the `fᵢ`.
-/

noncomputable section

namespace Submission.CDT

open Polynomial

variable {K : Type*} [Field K] [CharZero K]

/-- The finite set of points at which some `f i` has a zero or a pole. -/
def zerosPoles {ι : Type*} [Fintype ι] (f : ι → RatFunc K) : Finset K := by
  classical
  exact Finset.univ.biUnion (fun i => ((f i).num * (f i).denom).roots.toFinset)

omit [CharZero K] in
/-- Outside `zerosPoles f` every `f i` is finite and nonzero. -/
lemma ordAt_eq_zero_of_notMem_zerosPoles {ι : Type*} [Fintype ι] (f : ι → RatFunc K)
    (hf : ∀ i, f i ≠ 0) (i : ι) {α : K} (hα : α ∉ zerosPoles f) : ordAt α (f i) = 0 := by
  classical
  have hmem : α ∉ ((f i).num * (f i).denom).roots.toFinset := fun h =>
    hα (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, h⟩)
  have hne : (f i).num * (f i).denom ≠ 0 :=
    mul_ne_zero (RatFunc.num_ne_zero (hf i)) (RatFunc.denom_ne_zero _)
  have hnr : ¬ ((f i).num * (f i).denom).IsRoot α := by
    intro h
    exact hmem (by rw [Multiset.mem_toFinset]; exact (Polynomial.mem_roots hne).mpr h)
  have hrm : Polynomial.rootMultiplicity α ((f i).num * (f i).denom) = 0 :=
    Polynomial.rootMultiplicity_eq_zero hnr
  rw [Polynomial.rootMultiplicity_mul hne] at hrm
  have hnum : Polynomial.rootMultiplicity α (f i).num = 0 := by omega
  have hden : Polynomial.rootMultiplicity α (f i).denom = 0 := by omega
  rw [ordAt, hnum, hden]
  norm_num

section IsAlgClosed

variable [IsAlgClosed K]

/-- **Function-field Lindemann–Weierstrass (multiplicative-dependence form, field
coefficients).**  Let `K` be algebraically closed of characteristic `0`, `f : ι → K(X)` a finite
family of nonzero rational functions, and `c : ι → K` a *nonzero* coefficient family.  If
`Σᵢ cᵢ·(dRat fᵢ)/fᵢ = dRat h` for some `h ∈ K(X)`, then the `fᵢ` are multiplicatively dependent:
there are integers `mᵢ`, not all zero, with `∏ᵢ fᵢ ^ mᵢ ∈ K`. -/
theorem exists_int_prod_zpow_const_of_sum_dRat_div_field {ι : Type*} [Fintype ι]
    (f : ι → RatFunc K) (hf : ∀ i, f i ≠ 0) (c : ι → K) (hc : c ≠ 0)
    (h : ∃ h₀ : RatFunc K,
      ∑ i, algebraMap K (RatFunc K) (c i) * (dRat (f i) / f i) = dRat h₀) :
    ∃ m : ι → ℤ, m ≠ 0 ∧ ∃ C : K, C ≠ 0 ∧ ∏ i, f i ^ (m i) = algebraMap K (RatFunc K) C := by
  classical
  obtain ⟨h₀, hh₀⟩ := h
  -- the residue of the combination is `Σᵢ cᵢ·ordAt α fᵢ`, hence vanishes
  have hres : ∀ α : K,
      ResidueAt α (∑ i, algebraMap K (RatFunc K) (c i) * (dRat (f i) / f i))
        (∑ i, c i * ((ordAt α (f i) : ℤ) : K)) := by
    intro α
    refine ResidueAt.sum (s := Finset.univ) (fun i _ => ?_)
    exact ResidueAt.const_mul (residueAt_dRat_div_self (f i) (hf i) α) (c i)
  have hzero : ∀ α : K, ∑ i, c i * ((ordAt α (f i) : ℤ) : K) = 0 := by
    intro α
    by_contra hne
    have h1 : ordAt α (dRat h₀) = -1 := by
      have h2 := (hres α).ordAt_eq_neg_one hne
      rwa [hh₀] at h2
    exact ordAt_dRat_ne_neg_one α h₀ h1
  -- the vectors of orders, restricted to the finite set of zeros and poles
  set S : Finset K := zerosPoles f with hS
  set vK : ι → ↥(S : Set K) → K := fun i s => ((ordAt (s : K) (f i) : ℤ) : K) with hvK
  set vQ : ι → ↥(S : Set K) → ℚ := fun i s => (ordAt (s : K) (f i) : ℚ) with hvQ
  -- the `K`-linear relation given by `c`
  have hLIK : ¬ LinearIndependent K vK := by
    intro hLI
    have h2 := (Fintype.linearIndependent_iff.mp hLI) c (by
      funext s
      simpa [vK] using hzero (s : K))
    exact hc (funext h2)
  -- hence a rational relation
  have hLIQ : ¬ LinearIndependent ℚ vQ := fun hh => hLIK (by
    have h1 := Commons.LinearAlgebra.linearIndependent_map_of_linearIndependent_fintype
      (K := ℚ) (L := K) vQ hh
    simpa [vK, vQ, Rat.cast_intCast] using h1)
  rw [Fintype.linearIndependent_iff] at hLIQ
  push Not at hLIQ
  obtain ⟨g, hg, i₀, hi₀⟩ := hLIQ
  -- clear denominators
  obtain ⟨N, hNpos, hm⟩ := Commons.Data.Rat.exists_nat_mul_eq_int g
  choose m hm' using hm
  have hNne : (N : ℚ) ≠ 0 := by exact_mod_cast hNpos.ne'
  -- the integer relation at the points of `S`
  have hSrel : ∀ s : ↥(S : Set K), ∑ i, m i * ordAt (s : K) (f i) = 0 := by
    intro s
    have h1 : ∑ i, (g i) * ((ordAt (s : K) (f i) : ℤ) : ℚ) = 0 := by
      have h2 := congrFun hg s
      simpa [vQ] using h2
    have h3 : ∑ i, (m i : ℚ) * ((ordAt (s : K) (f i) : ℤ) : ℚ) = 0 := by
      have h4 : ∀ i, (m i : ℚ) = (N : ℚ) * g i := fun i => (hm' i).symm
      calc ∑ i, (m i : ℚ) * ((ordAt (s : K) (f i) : ℤ) : ℚ)
          = ∑ i, (N : ℚ) * (g i * ((ordAt (s : K) (f i) : ℤ) : ℚ)) := by
            refine Finset.sum_congr rfl (fun i _ => ?_)
            rw [h4 i]; ring
        _ = (N : ℚ) * ∑ i, (g i) * ((ordAt (s : K) (f i) : ℤ) : ℚ) := by
            rw [Finset.mul_sum]
        _ = 0 := by rw [h1, mul_zero]
    have h5 : (((∑ i, m i * ordAt (s : K) (f i)) : ℤ) : ℚ) = 0 := by
      have h6 : (((∑ i, m i * ordAt (s : K) (f i)) : ℤ) : ℚ)
          = ∑ i, (m i : ℚ) * ((ordAt (s : K) (f i) : ℤ) : ℚ) := by
        rw [Int.cast_sum]
        exact Finset.sum_congr rfl (fun i _ => by rw [Int.cast_mul])
      rw [h6, h3]
    exact_mod_cast h5
  -- the relation at every point
  have hrel : ∀ α : K, ∑ i, m i * ordAt α (f i) = 0 := by
    intro α
    by_cases hα : α ∈ S
    · exact hSrel ⟨α, hα⟩
    · refine Finset.sum_eq_zero (fun i _ => ?_)
      rw [ordAt_eq_zero_of_notMem_zerosPoles f hf i (by simpa [hS] using hα), mul_zero]
  refine ⟨m, ?_, ?_⟩
  · intro hm0
    exact hi₀ (by
      have h1 := hm' i₀
      rw [hm0] at h1
      exact (mul_eq_zero.mp h1).resolve_left hNne)
  · -- the product of the `f i ^ m i` has order zero everywhere, hence is constant
    have hord : ∀ α : K, ordAt α (∏ i, f i ^ (m i)) = 0 := by
      intro α
      have h1 : ordAt α (∏ i, f i ^ (m i)) = ∑ i, ordAt α (f i ^ (m i)) :=
        ordAt_prod α Finset.univ (fun i => f i ^ (m i)) (fun i _ => zpow_ne_zero (m i) (hf i))
      rw [h1, Finset.sum_congr rfl (fun i _ => ordAt_zpow α (hf i) (m i)), hrel α]
    have hdR : dRat (∏ i, f i ^ (m i)) = 0 := by
      by_contra hne
      obtain ⟨α, hα⟩ := exists_ordAt_ne_zero_of_dRat_ne_zero (∏ i, f i ^ (m i)) hne
      exact hα (hord α)
    obtain ⟨C, hC⟩ := exists_const_of_dRat_eq_zero hdR
    refine ⟨C, ?_, hC⟩
    intro hC0
    have h0 : (∏ i, f i ^ (m i)) = 0 := by rw [hC, hC0, map_zero]
    exact (Finset.prod_ne_zero_iff.mpr (fun i _ => zpow_ne_zero (m i) (hf i))) h0

/-- **A rational function is determined up to a constant factor and a power by its logarithmic
derivative**: if `(dRat f)/f = n·(dRat g)/g` with `n ∈ ℤ`, then `f = C·g ^ n` for some `C ≠ 0`. -/
theorem exists_const_mul_zpow_of_dRat_div_eq {f g : RatFunc K} (hf : f ≠ 0) (hg : g ≠ 0) (n : ℤ)
    (h : dRat f / f = algebraMap K (RatFunc K) (n : K) * (dRat g / g)) :
    ∃ C : K, C ≠ 0 ∧ f = algebraMap K (RatFunc K) C * g ^ n := by
  classical
  set F : Fin 2 → RatFunc K := ![f, g] with hF
  set c : Fin 2 → ℤ := ![1, -n] with hc
  have hF0 : ∀ i, F i ≠ 0 := by
    intro i; fin_cases i
    · simpa [hF] using hf
    · simpa [hF] using hg
  have hsum : ∑ i, algebraMap K (RatFunc K) ((c i : ℤ) : K) * (dRat (F i) / F i) = dRat 0 := by
    rw [Fin.sum_univ_two]
    simp only [hc, hF, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [h, dRat_zero, Int.cast_one, Int.cast_neg, map_one, map_neg]
    ring
  obtain ⟨C, hC0, hC⟩ := prod_zpow_const_of_sum_dRat_div F hF0 c ⟨0, hsum⟩
  refine ⟨C, hC0, ?_⟩
  rw [Fin.prod_univ_two] at hC
  simp only [hc, hF, Matrix.cons_val_zero, Matrix.cons_val_one] at hC
  rw [zpow_one, zpow_neg] at hC
  rw [← hC]
  field_simp

/-- **The product of two rational functions whose logarithmic derivatives add up to a derivative is a
constant**: `(dRat f)/f + (dRat g)/g = dRat h` forces `f·g ∈ K`. -/
theorem exists_const_mul_of_dRat_div_add {f g h : RatFunc K} (hf : f ≠ 0) (hg : g ≠ 0)
    (hh : dRat f / f + dRat g / g = dRat h) :
    ∃ C : K, C ≠ 0 ∧ f * g = algebraMap K (RatFunc K) C := by
  classical
  set F : Fin 2 → RatFunc K := ![f, g] with hF
  set c : Fin 2 → ℤ := ![1, 1] with hc
  have hF0 : ∀ i, F i ≠ 0 := by
    intro i; fin_cases i
    · simpa [hF] using hf
    · simpa [hF] using hg
  have hsum : ∑ i, algebraMap K (RatFunc K) ((c i : ℤ) : K) * (dRat (F i) / F i) = dRat h := by
    rw [Fin.sum_univ_two]
    simp only [hc, hF, Matrix.cons_val_zero, Matrix.cons_val_one]
    simpa using hh
  obtain ⟨C, hC0, hC⟩ := prod_zpow_const_of_sum_dRat_div F hF0 c ⟨h, hsum⟩
  refine ⟨C, hC0, ?_⟩
  rw [Fin.prod_univ_two] at hC
  simp only [hc, hF, Matrix.cons_val_zero, Matrix.cons_val_one] at hC
  rw [zpow_one, zpow_one] at hC
  exact hC

end IsAlgClosed

end Submission.CDT
