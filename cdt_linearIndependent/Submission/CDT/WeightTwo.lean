import Mathlib
import Submission.CDT.ResidueMul
import Submission.CDT.LogMultiplicative

/-!
# The weight-two residue relation

Given rational functions `f : ι → K(X)` and a weight-two relation
`Σᵢⱼ cᵢⱼ · (fᵢ'/fᵢ)(fⱼ'/fⱼ) = h'`, the classical residue argument of the function-field
Lindemann–Weierstrass theorem still applies — but only after removing the *double* poles.

If `α` is a zero or a pole of exactly one of the functions, say `f k`, while all the other
`f i` (`i ≠ k`) are finite at `α` with finite nonzero logarithmic derivative, and the coefficient of
the diagonal term `(f k'/f k)²` vanishes, then every term of the relation has order `≥ -1` at `α`,
and taking residues gives

`(f k'/f k)(α) · Σ_{i ≠ k} (cᵢₖ + cₖᵢ) · (fᵢ'/fᵢ)(α) = 0`.

Since `h' = dRat h` never has a simple pole, that number is forced to be `0`.
-/

noncomputable section

namespace Submission.CDT

open Polynomial

variable {K : Type*} [Field K] [CharZero K]

/-- The double sum behind the weight-two residue computation: splitting the outer index at `k`. -/
private theorem sum_double_ite {ι M : Type*} [Fintype ι] [DecidableEq ι] [AddCommMonoid M]
    (k : ι) (D E : ι → ι → M) :
    (∑ i, ∑ j, (if i = k then (if j = k then 0 else D i j) else (if j = k then E i j else 0)))
      = (∑ i ∈ Finset.univ.erase k, D k i) + (∑ i ∈ Finset.univ.erase k, E i k) := by
  have hGk : (∑ j ∈ Finset.univ, (if j = k then 0 else D k j))
      = ∑ j ∈ Finset.univ.erase k, D k j := by
    have h1 : (∑ j ∈ Finset.univ, (if j = k then 0 else D k j))
        = ∑ j ∈ Finset.univ.erase k, (if j = k then 0 else D k j) :=
      (Finset.sum_subset (Finset.erase_subset k Finset.univ) (fun x _ hx => by
        have hxk : x = k := by
          by_contra hne
          exact hx (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ x⟩)
        rw [hxk, if_pos rfl])).symm
    rw [h1]
    exact Finset.sum_congr rfl (fun x hx => by rw [if_neg (Finset.mem_erase.mp hx).1])
  have hGi : ∀ i ∈ Finset.univ.erase k, (∑ j, (if j = k then E i j else 0)) = E i k := by
    intro i _
    rw [Finset.sum_ite_eq' Finset.univ k (fun j => E i j), if_pos (Finset.mem_univ k)]
  have hinner : ∀ i, (∑ j, (if i = k then (if j = k then 0 else D i j)
        else (if j = k then E i j else 0)))
      = (if i = k then (∑ j ∈ Finset.univ, (if j = k then 0 else D k j))
          else (∑ j, (if j = k then E i j else 0))) := by
    intro i
    by_cases hik : i = k
    · rw [hik]; simp
    · rw [if_neg hik]
      exact Finset.sum_congr rfl (fun j _ => by rw [if_neg hik])
  rw [Finset.sum_congr rfl (fun i _ => hinner i)]
  have houter : (∑ i, (if i = k then (∑ j ∈ Finset.univ, (if j = k then 0 else D k j))
        else (∑ j, (if j = k then E i j else 0))))
      = (∑ j ∈ Finset.univ, (if j = k then 0 else D k j))
        + ∑ i ∈ Finset.univ.erase k, (∑ j, (if j = k then E i j else 0)) := by
    have h1 := Finset.sum_erase_add (Finset.univ : Finset ι)
      (fun i => if i = k then (∑ j ∈ Finset.univ, (if j = k then 0 else D k j))
        else (∑ j, (if j = k then E i j else 0))) (Finset.mem_univ k)
    rw [if_pos rfl] at h1
    have h2 : (∑ x ∈ Finset.univ.erase k, (if x = k then (∑ j ∈ Finset.univ, (if j = k then 0 else D k j))
          else (∑ j, (if j = k then E x j else 0))))
        = ∑ x ∈ Finset.univ.erase k, (∑ j, (if j = k then E x j else 0)) :=
      Finset.sum_congr rfl (fun x hx => if_neg (Finset.mem_erase.mp hx).1)
    rw [h2, add_comm] at h1
    exact h1.symm
  rw [houter, hGk, Finset.sum_congr rfl hGi]

/-- **The weight-two residue relation.** -/
theorem residueAt_weight_two_eq_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → RatFunc K) (hf : ∀ i, f i ≠ 0) (c : ι → ι → K) {α : K} {k : ι}
    (hk : ordAt α (f k) ≠ 0) (hkk : c k k = 0)
    (hfin : ∀ i, i ≠ k → ordAt α (f i) = 0)
    (hlog : ∀ i, i ≠ k → ordAt α (dRat (f i) / f i) = 0)
    {h : RatFunc K}
    (hsum : ∑ i, ∑ j, algebraMap K (RatFunc K) (c i j)
        * ((dRat (f i) / f i) * (dRat (f j) / f j)) = dRat h) :
    ∑ i ∈ Finset.univ.erase k, (c i k + c k i) * valueAt α (dRat (f i) / f i) = 0 := by
  classical
  have hterm : ∀ i j, ResidueAt α
      (algebraMap K (RatFunc K) (c i j) * ((dRat (f i) / f i) * (dRat (f j) / f j)))
      (c i j * (if i = k ∧ j = k then 0
        else if i = k then valueAt α (dRat (f j) / f j) * ((ordAt α (f k) : ℤ) : K)
        else if j = k then valueAt α (dRat (f i) / f i) * ((ordAt α (f k) : ℤ) : K)
        else 0)) := by
    intro i j
    by_cases hik : i = k
    · by_cases hjk : j = k
      · simp only [hik, hjk, hkk, map_zero, zero_mul, if_true, and_self]
        exact ResidueAt.of_ordAt_nonneg (by rw [ordAt_zero])
      · simp only [hik, hjk, if_true, if_false]
        exact ResidueAt.const_mul
          (residueAt_dRat_div_self_mul_dRat_div_self (f := f k) (hf k) (hlog j hjk)) (c k j)
    · by_cases hjk : j = k
      · simp only [hik, hjk, if_true, if_false]
        refine ResidueAt.const_mul ?_ (c i k)
        have h := residueAt_dRat_div_self_mul_dRat_div_self (f := f k) (g := f i) (hf k)
          (hlog i hik)
        rw [mul_comm (dRat (f k) / f k) (dRat (f i) / f i)] at h
        exact h
      · simp only [hik, hjk, if_false]
        refine ResidueAt.const_mul ?_ (c i j)
        have h := ResidueAt.mul (hlog i hik) (residueAt_dRat_div_self (f j) (hf j) α)
        rw [hfin j hjk, Int.cast_zero, mul_zero] at h
        exact h
  have hsumres : ResidueAt α
      (∑ i, ∑ j, algebraMap K (RatFunc K) (c i j)
        * ((dRat (f i) / f i) * (dRat (f j) / f j)))
      (∑ i, ∑ j, c i j * (if i = k ∧ j = k then 0
        else if i = k then valueAt α (dRat (f j) / f j) * ((ordAt α (f k) : ℤ) : K)
        else if j = k then valueAt α (dRat (f i) / f i) * ((ordAt α (f k) : ℤ) : K)
        else 0)) :=
    ResidueAt.sum (fun i _ => ResidueAt.sum (fun j _ => hterm i j))
  rw [hsum] at hsumres
  have hcompute : (∑ i, ∑ j, c i j * (if i = k ∧ j = k then 0
        else if i = k then valueAt α (dRat (f j) / f j) * ((ordAt α (f k) : ℤ) : K)
        else if j = k then valueAt α (dRat (f i) / f i) * ((ordAt α (f k) : ℤ) : K)
        else 0))
      = ((ordAt α (f k) : ℤ) : K) * ∑ i ∈ Finset.univ.erase k,
          (c i k + c k i) * valueAt α (dRat (f i) / f i) := by
    set A : K := ((ordAt α (f k) : ℤ) : K) with hAdef
    set D : ι → ι → K := fun i j => c i j * (valueAt α (dRat (f j) / f j) * A) with hD
    set E : ι → ι → K := fun i j => c i j * (valueAt α (dRat (f i) / f i) * A) with hE
    have hpt : ∀ i j, c i j * (if i = k ∧ j = k then 0
          else if i = k then valueAt α (dRat (f j) / f j) * A
          else if j = k then valueAt α (dRat (f i) / f i) * A
          else 0)
        = (if i = k then (if j = k then 0 else D i j) else (if j = k then E i j else 0)) := by
      intro i j
      by_cases hik : i = k
      · by_cases hjk : j = k
        · simp [hik, hjk]
        · simp [hik, hjk, hD]
      · by_cases hjk : j = k
        · simp [hik, hjk, hE]
        · simp [hik, hjk]
    rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hpt i j))]
    rw [sum_double_ite k D E]
    calc (∑ i ∈ Finset.univ.erase k, D k i) + (∑ i ∈ Finset.univ.erase k, E i k)
        = (A * ∑ i ∈ Finset.univ.erase k, c k i * valueAt α (dRat (f i) / f i))
          + (A * ∑ i ∈ Finset.univ.erase k, c i k * valueAt α (dRat (f i) / f i)) := by
          congr 1
          · rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun i _ => ?_)
            simp only [hD]; ring
          · rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun i _ => ?_)
            simp only [hE]; ring
      _ = A * ∑ i ∈ Finset.univ.erase k, (c i k + c k i) * valueAt α (dRat (f i) / f i) := by
          simp only [Finset.mul_sum]
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [hcompute] at hsumres
  by_contra hS
  have hA0 : ((ordAt α (f k) : ℤ) : K) ≠ 0 := by
    intro h0
    exact hk (Int.cast_eq_zero.mp h0)
  exact ordAt_dRat_ne_neg_one α h (hsumres.ordAt_eq_neg_one (mul_ne_zero hA0 hS))

/-- **The weight-two relation, isolated at one other function.**  If in the situation of
`residueAt_weight_two_eq_zero` only one index `i₀ ≠ k` carries a nonzero coefficient
`c i₀ k + c k i₀`, then the value `(fᵢ₀'/fᵢ₀)(α)` must vanish. -/
theorem weight_two_value_eq_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → RatFunc K) (hf : ∀ i, f i ≠ 0) (c : ι → ι → K) {α : K} {k : ι}
    (hk : ordAt α (f k) ≠ 0) (hkk : c k k = 0)
    (hfin : ∀ i, i ≠ k → ordAt α (f i) = 0)
    (hlog : ∀ i, i ≠ k → ordAt α (dRat (f i) / f i) = 0)
    {h : RatFunc K}
    (hsum : ∑ i, ∑ j, algebraMap K (RatFunc K) (c i j)
        * ((dRat (f i) / f i) * (dRat (f j) / f j)) = dRat h)
    {i₀ : ι} (hi₀ : i₀ ≠ k) (hcoef : c i₀ k + c k i₀ ≠ 0)
    (hother : ∀ i, i ≠ k → i ≠ i₀ → c i k + c k i = 0) :
    valueAt α (dRat (f i₀) / f i₀) = 0 := by
  have h := residueAt_weight_two_eq_zero f hf c hk hkk hfin hlog hsum
  have h1 : (∑ i ∈ Finset.univ.erase k, (c i k + c k i) * valueAt α (dRat (f i) / f i))
      = (c i₀ k + c k i₀) * valueAt α (dRat (f i₀) / f i₀) := by
    refine Finset.sum_eq_single i₀ ?_ ?_
    · intro b hb hbne
      rw [hother b (Finset.mem_erase.mp hb).1 hbne, zero_mul]
    · intro hnotin
      exact absurd (Finset.mem_erase.mpr ⟨hi₀, Finset.mem_univ i₀⟩) hnotin
  rw [h1] at h
  exact (mul_eq_zero.mp h).resolve_left hcoef

end Submission.CDT
