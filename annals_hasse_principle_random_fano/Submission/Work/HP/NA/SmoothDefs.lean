import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.NA.Setup

/-!
# Auxiliary material for `card_smooth_cond`

Pivot monomials `X_{j0}^d` and `X_{j0}^{d} X_k`, together with the linear map
`a ↦ (f_a(x), (∂_i f_a(x))_{i ≠ j0})` whose kernel is counted in `card_smooth_cond`.
-/

noncomputable section
open Finset
set_option autoImplicit false

namespace Work.HP
namespace NA

/-- The pivot monomial `X_{j0}^d`, as an element of `Mon d n`. -/
def pM0 (d n : ℕ) (j0 : Fin (n + 1)) : Mon d n :=
  ⟨fun i => if i = j0 then ⟨d, Nat.lt_succ_self d⟩ else 0, by
    have h : (∑ x, ((if x = j0 then (⟨d, Nat.lt_succ_self d⟩ : Fin (d + 1)) else 0 :
        Fin (d + 1)) : ℕ)) = ∑ x, (if x = j0 then d else 0) := by
      apply Finset.sum_congr rfl; intro i _; by_cases h : i = j0 <;> simp [h]
    rw [h]; simp⟩

/-- The pivot monomial `X_{j0}^{d} X_k`, of degree `d + 1`, for `k ≠ j0`. -/
def pMk (d n : ℕ) (j0 k : Fin (n + 1)) (hk : k ≠ j0) : Mon (d + 1) n :=
  ⟨fun i => if i = j0 then ⟨d, by omega⟩ else if i = k then ⟨1, by omega⟩ else 0, by
    have h : (∑ x, ((if x = j0 then (⟨d, by omega⟩ : Fin (d + 1 + 1)) else
        if x = k then (⟨1, by omega⟩ : Fin (d + 1 + 1)) else 0 : Fin (d + 1 + 1)) : ℕ))
        = ∑ x, (if x = j0 then d else if x = k then 1 else 0) := by
      apply Finset.sum_congr rfl; intro i _
      rcases eq_or_ne i j0 with h | h <;> rcases eq_or_ne i k with h2 | h2 <;> simp_all
    rw [h]
    rw [show (∑ x, (if x = j0 then d else if x = k then 1 else 0))
        = ∑ x, ((if x = j0 then d else 0) + (if x = k then 1 else 0)) from by
      apply Finset.sum_congr rfl; intro i _
      rcases eq_or_ne i j0 with h | h <;> rcases eq_or_ne i k with h2 | h2 <;> simp_all]
    rw [Finset.sum_add_distrib]; simp⟩

section coord
variable (d n : ℕ) (j0 : Fin (n + 1))

@[simp] lemma pM0_apply_j0 : ((pM0 d n j0).1 j0 : ℕ) = d := by
  simp [pM0]

@[simp] lemma pM0_apply_ne {i : Fin (n + 1)} (h : i ≠ j0) : ((pM0 d n j0).1 i : ℕ) = 0 := by
  simp [pM0, h]

end coord

section coordk
variable (d n : ℕ) (j0 k : Fin (n + 1)) (hk : k ≠ j0)

@[simp] lemma pMk_apply_j0 : ((pMk d n j0 k hk).1 j0 : ℕ) = d := by
  simp [pMk]

@[simp] lemma pMk_apply_k : ((pMk d n j0 k hk).1 k : ℕ) = 1 := by
  simp [pMk, hk]

@[simp] lemma pMk_apply_other {i : Fin (n + 1)} (h1 : i ≠ j0) (h2 : i ≠ k) :
    ((pMk d n j0 k hk).1 i : ℕ) = 0 := by
  simp [pMk, h1, h2]

end coordk

variable {R : Type*} [CommRing R] (d n : ℕ) (x : Fin (n + 1) → R)

/-! ## Linearity of `fev` and `dfev` in the coefficient vector -/

lemma fev_add (a b : Mon d n → R) :
    fev d n (a + b) x = fev d n a x + fev d n b x := by
  simp only [fev, Pi.add_apply, add_mul, Finset.sum_add_distrib]

lemma fev_smul (c : R) (a : Mon d n → R) : fev d n (c • a) x = c * fev d n a x := by
  simp only [fev, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun m _ => by ring)

lemma dfev_add (a b : Mon d n → R) (j : Fin (n + 1)) :
    dfev d n (a + b) x j = dfev d n a x j + dfev d n b x j := by
  simp only [dfev, Pi.add_apply, add_mul, Finset.sum_add_distrib]

lemma dfev_smul (c : R) (a : Mon d n → R) (j : Fin (n + 1)) :
    dfev d n (c • a) x j = c * dfev d n a x j := by
  simp only [dfev, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun m _ => by ring)

/-- The linear map `a ↦ (f_a(x), (∂_i f_a(x))_{i ≠ j0})`, with the `j0`-slot holding `f_a(x)`. -/
def smoothMap (j0 : Fin (n + 1)) : (Mon d n → R) →ₗ[R] (Fin (n + 1) → R) where
  toFun a := fun j => if j = j0 then fev d n a x else dfev d n a x j
  map_add' a b := by
    funext j
    by_cases h : j = j0 <;> simp [h, fev_add, dfev_add, Pi.add_apply]
  map_smul' c a := by
    funext j
    by_cases h : j = j0 <;> simp [h, fev_smul, dfev_smul, Pi.smul_apply, smul_eq_mul]

@[simp] lemma smoothMap_apply (j0 : Fin (n + 1)) (a : Mon d n → R) (j : Fin (n + 1)) :
    smoothMap d n x j0 a j = if j = j0 then fev d n a x else dfev d n a x j := rfl

lemma smoothMap_zero_iff (j0 : Fin (n + 1)) (a : Mon d n → R) :
    smoothMap d n x j0 a = 0 ↔
      (fev d n a x = 0 ∧ ∀ i, i ≠ j0 → dfev d n a x i = 0) := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · simpa [smoothMap_apply] using congrFun h j0
    · intro i hi
      simpa [smoothMap_apply, hi] using congrFun h i
  · rintro ⟨h1, h2⟩
    funext j
    rw [smoothMap_apply]
    by_cases h : j = j0
    · simp [h, h1]
    · simp [h, h2 j h]

/-! ## Evaluation of `fev`/`dfev` on single monomials -/

lemma fev_single (m : Mon d n) (c : R) :
    fev d n (Pi.single m c) x = c * veronese d n x m := by
  have key : (Pi.single m c : Mon d n → R) = fun m' => if m' = m then c else 0 := by
    funext m'; rw [Pi.single_apply]
  rw [fev, key]
  simp only [ite_mul, zero_mul]
  simpa using Finset.sum_ite_eq' Finset.univ m (fun m' => c * veronese d n x m')

lemma dfev_single (m : Mon d n) (c : R) (j : Fin (n + 1)) :
    dfev d n (Pi.single m c) x j = c * ((m.1 j : ℕ) : R) *
      ∏ i, x i ^ (if i = j then (m.1 i : ℕ) - 1 else (m.1 i : ℕ)) := by
  have key : (Pi.single m c : Mon d n → R) = fun m' => if m' = m then c else 0 := by
    funext m'; rw [Pi.single_apply]
  rw [dfev, key]
  simp only [ite_mul, zero_mul]
  simpa using Finset.sum_ite_eq' Finset.univ m
    (fun m' => c * ((m.1 j : ℕ) : R) *
      ∏ i, x i ^ (if i = j then (m.1 i : ℕ) - 1 else (m.1 i : ℕ)))

lemma veronese_pM0 (j0 : Fin (n + 1)) :
    veronese d n x (pM0 d n j0) = x j0 ^ d := by
  simp only [veronese]
  trans ∏ i, (if i = j0 then x j0 ^ d else 1)
  · apply Finset.prod_congr rfl; intro i _
    by_cases h : i = j0
    · rw [h]; simp [pM0_apply_j0]
    · rw [pM0_apply_ne d n j0 h]; simp [h]
  · simpa using Finset.prod_ite_eq' Finset.univ j0 (fun _ => x j0 ^ d)

lemma veronese_pMk (j0 k : Fin (n + 1)) (hk : k ≠ j0) :
    veronese (d + 1) n x (pMk d n j0 k hk) = x j0 ^ d * x k := by
  simp only [veronese]
  trans (∏ i, (if i = j0 then x j0 ^ d else 1)) * (∏ i, (if i = k then x k else 1))
  · rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl; intro i _
    by_cases h1 : i = j0
    · by_cases h2 : i = k
      · exact absurd (h1.symm.trans h2) (Ne.symm hk)
      · rw [h1]; simp [pMk_apply_j0, Ne.symm hk]
    · by_cases h2 : i = k
      · rw [h2]; simp [pMk_apply_k, hk]
      · rw [pMk_apply_other d n j0 k hk h1 h2]; simp [h1, h2]
  · rw [Finset.prod_ite_eq', Finset.prod_ite_eq']
    simp

lemma dpv_pMk (j0 k : Fin (n + 1)) (hk : k ≠ j0) :
    (∏ i, x i ^ (if i = k then ((pMk d n j0 k hk).1 i : ℕ) - 1
        else ((pMk d n j0 k hk).1 i : ℕ))) = x j0 ^ d := by
  trans ∏ i, (if i = j0 then x j0 ^ d else 1)
  · apply Finset.prod_congr rfl; intro i _
    by_cases h1 : i = j0
    · by_cases h2 : i = k
      · exact absurd (h1.symm.trans h2) (Ne.symm hk)
      · rw [h1]; simp [pMk_apply_j0, Ne.symm hk]
    · by_cases h2 : i = k
      · rw [h2]; simp [pMk_apply_k, hk]
      · rw [pMk_apply_other d n j0 k hk h1 h2]; simp [h1, h2]
  · simpa using Finset.prod_ite_eq' Finset.univ j0 (fun _ => x j0 ^ d)

/-- Value of `f_a` at `x` when `a` is the basis vector at `X_{j0}^d`. -/
lemma fev_pM0 (j0 : Fin (n + 1)) (c : R) :
    fev d n (Pi.single (pM0 d n j0) c) x = c * x j0 ^ d := by
  rw [fev_single, veronese_pM0]

lemma dfev_pM0 (j0 : Fin (n + 1)) (c : R) {j : Fin (n + 1)} (hj : j ≠ j0) :
    dfev d n (Pi.single (pM0 d n j0) c) x j = 0 := by
  rw [dfev_single, pM0_apply_ne d n j0 hj]
  simp

lemma fev_pMk (j0 k : Fin (n + 1)) (hk : k ≠ j0) (c : R) :
    fev (d + 1) n (Pi.single (pMk d n j0 k hk) c) x = c * (x j0 ^ d * x k) := by
  rw [fev_single, veronese_pMk]

lemma dfev_pMk (j0 k : Fin (n + 1)) (hk : k ≠ j0) (c : R) {j : Fin (n + 1)} (hj : j ≠ j0) :
    dfev (d + 1) n (Pi.single (pMk d n j0 k hk) c) x j
      = if j = k then c * x j0 ^ d else 0 := by
  rw [dfev_single]
  by_cases h : j = k
  · rw [h]
    rw [if_pos rfl, dpv_pMk d n x j0 k hk, pMk_apply_k]
    simp
  · rw [pMk_apply_other d n j0 k hk hj h]; simp [h]

/-! ## The explicit section of `smoothMap` on the standard basis -/

lemma smoothMap_single_pM0 (j0 : Fin (n + 1)) :
    smoothMap (d + 1) n x j0 (Pi.single (pM0 (d + 1) n j0) (1 : R))
      = Pi.single j0 ((x j0) ^ (d + 1)) := by
  funext i
  rw [smoothMap_apply]
  by_cases hi : i = j0
  · rw [if_pos hi, fev_pM0, Pi.single_apply, if_pos hi]; ring
  · rw [if_neg hi, dfev_pM0 (d + 1) n x j0 1 hi, Pi.single_eq_of_ne hi]

lemma smoothMap_single_pMk (j0 k : Fin (n + 1)) (hk : k ≠ j0) :
    smoothMap (d + 1) n x j0 (Pi.single (pMk d n j0 k hk) (1 : R))
      = Pi.single j0 ((x j0) ^ d * x k) + Pi.single k ((x j0) ^ d) := by
  funext i
  rw [smoothMap_apply]
  by_cases hi : i = j0
  · rw [if_pos hi, fev_pMk, Pi.add_apply, Pi.single_apply, if_pos hi,
      Pi.single_apply, if_neg (fun h : i = k => hk ((hi.symm.trans h).symm))]
    ring
  · rw [if_neg hi, dfev_pMk d n x j0 k hk 1 hi]
    by_cases h : i = k
    · rw [if_pos h, Pi.add_apply, Pi.single_eq_of_ne hi, Pi.single_apply, if_pos h]; ring
    · rw [if_neg h, Pi.add_apply, Pi.single_eq_of_ne hi, Pi.single_apply, if_neg h]; simp

/-- A candidate preimage of the `j`-th standard basis vector under `smoothMap`,
where `yi` is the inverse of `x j0`. -/
def svFun (d n : ℕ) (x : Fin (n + 1) → R) (j0 : Fin (n + 1)) (yi : R) :
    Fin (n + 1) → (Mon (d + 1) n → R) :=
  fun j => if h : j = j0 then
      (yi ^ (d + 1)) • (Pi.single (pM0 (d + 1) n j0) (1 : R) : Mon (d + 1) n → R)
    else
      (yi ^ d) • (Pi.single (pMk d n j0 j h) (1 : R) : Mon (d + 1) n → R)
        + (-(x j * yi ^ (d + 1))) •
            (Pi.single (pM0 (d + 1) n j0) (1 : R) : Mon (d + 1) n → R)

end NA
end Work.HP

