import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.Vero
import Submission.Work.HP.HP3.DotLinDefs
import Submission.Work.HP.HP3.VeroProdDefs
import Submission.Work.HP.HP3.VeroProdExtra
import Submission.Work.HP.HP3.cond_iff_eq_addE
import Submission.Work.HP.HP3.prodVecR_pair

/-!
# The `Θ`-construction in coefficient-vector form

For a degree-`(d-1)` monomial exponent vector `m : Mon (d-1) n`, `mulVecR d n hd m` is the
`ℝ`-linear map sending a linear form `L : Fin (n+1) → ℝ` to the coefficient vector of the
degree-`d` form `X^m · ⟨L, X⟩`.  On integer vectors `c` it agrees with `prodVecR d n m c`, and
on the concrete forms `L_j = x_{i₀}X_j - x_j X_{i₀}` (which vanish at `x`) it is a two-term vector.
-/

set_option autoImplicit false
noncomputable section
open Finset

namespace Work.HP.Vero

open Work.HP

/-- The monomial `X_i ^ d` as an element of `Mon d n`. -/
def powMon (d n : ℕ) (i : Fin (n + 1)) : Mon d n where
  val j := ⟨if j = i then d else 0, by split <;> omega⟩
  property := by rw [Finset.sum_ite_eq']; simp

@[simp] lemma powMon_val (d n : ℕ) (i j : Fin (n + 1)) :
    ((powMon d n i).1 j : ℕ) = if j = i then d else 0 := rfl

lemma veronese_powMon {R : Type*} [CommSemiring R] (d n : ℕ) (i : Fin (n + 1))
    (x : Fin (n + 1) → R) : veronese d n x (powMon d n i) = x i ^ d := by
  simp only [veronese]
  rw [Finset.prod_eq_single i]
  · simp [powMon]
  · intro j _ hji
    simp [powMon, hji]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- `ν_d(x)(m + e_k) = ν_{d-1}(x)(m) · x_k`. -/
lemma veronese_addE (d n : ℕ) (hd : 1 ≤ d) (m : Mon (d - 1) n) (k : Fin (n + 1))
    (x : Fin (n + 1) → ℤ) :
    veronese d n x (addE d n hd m k) = veronese (d - 1) n x m * x k := by
  have h1 : ∀ i : Fin (n + 1), x i ^ ((m.1 i : ℕ) + (if i = k then 1 else 0))
      = x i ^ (m.1 i : ℕ) * x i ^ (if i = k then 1 else 0) :=
    fun i => pow_add (x i) _ _
  have hk : (∏ i : Fin (n + 1), x i ^ (if i = k then 1 else 0)) = x k := by
    rw [Finset.prod_eq_single k]
    · simp
    · intro j _ hjk; simp [hjk]
    · intro h; exact absurd (Finset.mem_univ k) h
  simp only [veronese, addE_val]
  rw [Finset.prod_congr rfl (fun i _ => h1 i), Finset.prod_mul_distrib, hk]

/-- The realified Veronese map: `ν_{d,n}(x)` read off as a real vector. -/
def veroneseR (d n : ℕ) (x : Fin (n + 1) → ℤ) : Mon d n → ℝ :=
  fun m => ((veronese d n x m : ℤ) : ℝ)

/-- `ν_d(x)(m + e_k) = ν_{d-1}(x)(m) · x_k`, over `ℝ`. -/
lemma veroneseR_addE (d n : ℕ) (hd : 1 ≤ d) (q : Mon (d - 1) n) (k : Fin (n + 1))
    (x : Fin (n + 1) → ℤ) :
    veroneseR d n x (addE d n hd q k) = veroneseR (d - 1) n x q * (x k : ℝ) := by
  simp only [veroneseR, veronese_addE d n hd q k x, Int.cast_mul]

/-- The `ℝ`-linear map `L ↦ X^m · ⟨L, X⟩` on degree-`d` coefficient vectors: its `m'`-th
coordinate is `L k` if `m' = m + e_k`, and `0` otherwise. -/
def mulVecR (d n : ℕ) (hd : 1 ≤ d) (m : Mon (d - 1) n) :
    (Fin (n + 1) → ℝ) →ₗ[ℝ] (Mon d n → ℝ) where
  toFun L := fun m' => ∑ k : Fin (n + 1), if m' = addE d n hd m k then L k else 0
  map_add' L L' := by
    funext m'
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    by_cases h : m' = addE d n hd m k <;> simp [h]
  map_smul' a L := by
    funext m'
    simp only [Pi.smul_apply]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    by_cases h : m' = addE d n hd m k <;> simp [h]

@[simp] lemma mulVecR_apply (d n : ℕ) (hd : 1 ≤ d) (m : Mon (d - 1) n)
    (L : Fin (n + 1) → ℝ) (m' : Mon d n) :
    mulVecR d n hd m L m' = ∑ k : Fin (n + 1), if m' = addE d n hd m k then L k else 0 := rfl

/-- On integer coefficient vectors `mulVecR` is `prodVecR`. -/
lemma mulVecR_intCastPi (d n : ℕ) (hd : 1 ≤ d) (m : Mon (d - 1) n) (c : Fin (n + 1) → ℤ) :
    mulVecR d n hd m (intCastPi c) = prodVecR d n m c := by
  funext m'
  rw [mulVecR_apply, prodVecR, HP3.prodVec_apply d n hd m c m', Int.cast_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  by_cases h : m' = addE d n hd m k <;> simp [h, intCastPi_apply]

/-- `mulVecR` on a single coordinate vector. -/
lemma mulVecR_single (d n : ℕ) (hd : 1 ≤ d) (m : Mon (d - 1) n) (j : Fin (n + 1)) (c : ℝ) :
    mulVecR d n hd m (Pi.single j c : Fin (n + 1) → ℝ)
      = c • Pi.single (addE d n hd m j) (1 : ℝ) := by
  funext m'
  rw [mulVecR_apply]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single j]
  · by_cases h : m' = addE d n hd m j <;> simp [h]
  · intro k _ hk
    have hz : (Pi.single j c : Fin (n + 1) → ℝ) k = 0 := by simp [hk]
    rw [hz]
    by_cases h : m' = addE d n hd m k <;> simp [h]
  · intro h; exact absurd (Finset.mem_univ j) h

/-- `mulVecR` on the linear form `L_j = x_{i₀}X_j - x_jX_{i₀}` vanishing at `x`. -/
lemma mulVecR_L (d n : ℕ) (hd : 1 ≤ d) (i₀ j : Fin (n + 1)) (x : Fin (n + 1) → ℤ)
    (m : Mon (d - 1) n) :
    mulVecR d n hd m (fun k => (x i₀ : ℝ) * (if k = j then 1 else 0)
        - (x j : ℝ) * (if k = i₀ then 1 else 0))
      = (x i₀ : ℝ) • Pi.single (addE d n hd m j) (1 : ℝ)
        - (x j : ℝ) • Pi.single (addE d n hd m i₀) (1 : ℝ) := by
  have hvec : (fun k => (x i₀ : ℝ) * (if k = j then 1 else 0)
        - (x j : ℝ) * (if k = i₀ then 1 else 0))
      = (x i₀ : ℝ) • (Pi.single j (1 : ℝ) : Fin (n + 1) → ℝ)
        - (x j : ℝ) • (Pi.single i₀ (1 : ℝ) : Fin (n + 1) → ℝ) := by
    funext k
    by_cases h1 : k = j <;> by_cases h2 : k = i₀ <;> simp_all [Pi.single_eq_same]
  rw [hvec, map_sub, map_smul, map_smul, mulVecR_single, mulVecR_single, one_smul, one_smul]

/-- The form `L_j = x_{i₀}X_j - x_jX_{i₀}` pairs to zero with `x`. -/
lemma dotLin_L (n : ℕ) (x : Fin (n + 1) → ℤ) (i₀ j : Fin (n + 1)) :
    dotLin x (fun k => (x i₀ : ℝ) * (if k = j then 1 else 0)
        - (x j : ℝ) * (if k = i₀ then 1 else 0)) = 0 := by
  simp only [dotLin_apply]
  have hsplit : ∀ k : Fin (n + 1), (x k : ℝ) * ((x i₀ : ℝ) * (if k = j then 1 else 0)
      - (x j : ℝ) * (if k = i₀ then 1 else 0))
      = (x k : ℝ) * (x i₀ : ℝ) * (if k = j then 1 else 0)
        - (x k : ℝ) * (x j : ℝ) * (if k = i₀ then 1 else 0) := fun k => by ring
  rw [Finset.sum_congr rfl (fun k _ => hsplit k), Finset.sum_sub_distrib]
  have hA : (∑ k : Fin (n + 1),
      (x k : ℝ) * (x i₀ : ℝ) * (if k = j then 1 else 0)) = (x j : ℝ) * (x i₀ : ℝ) := by
    rw [Finset.sum_eq_single j]
    · simp
    · intro k _ hk; rw [if_neg hk]; ring
    · intro h; exact absurd (Finset.mem_univ j) h
  have hB : (∑ k : Fin (n + 1),
      (x k : ℝ) * (x j : ℝ) * (if k = i₀ then 1 else 0)) = (x i₀ : ℝ) * (x j : ℝ) := by
    rw [Finset.sum_eq_single i₀]
    · simp
    · intro k _ hk; rw [if_neg hk]; ring
    · intro h; exact absurd (Finset.mem_univ i₀) h
  simp only [hA, hB]; ring

/-- Evaluation of a degree-`d` form at `x`, on the coefficient vector of `X^m·⟨c,X⟩`. -/
lemma evalLin_prodVecR (d n : ℕ) (m : Mon (d - 1) n) (c : Fin (n + 1) → ℤ)
    (x : Fin (n + 1) → ℤ) :
    evalLin d n x (prodVecR d n m c) = ((formEval d n (prodVec d n m c) x : ℤ) : ℝ) := by
  simp only [evalLin, LinearMap.coe_mk, AddHom.coe_mk, prodVecR, formEval, Int.cast_id]
  rw [Int.cast_sum]
  refine Finset.sum_congr rfl (fun m' _ => ?_)
  rw [Int.cast_mul]

/-- `m - e_j` for a degree-`d` monomial with positive `j`-th exponent. -/
def subE (d n : ℕ) (m : Mon d n) (j : Fin (n + 1)) (hj : 1 ≤ (m.1 j : ℕ)) : Mon (d - 1) n where
  val i := ⟨(m.1 i : ℕ) - (if i = j then 1 else 0), by
    have hd : 1 ≤ d := by
      have hle := Finset.single_le_sum (f := fun k => (m.1 k : ℕ))
        (fun k _ => Nat.zero_le _) (Finset.mem_univ j)
      rw [m.2] at hle
      omega
    by_cases hij : i = j
    · subst hij
      have h1 : (m.1 i : ℕ) - (if i = i then 1 else 0) = (m.1 i : ℕ) - 1 := by rw [if_pos rfl]
      rw [h1]
      have := (m.1 i).isLt
      omega
    · have h1 : (m.1 i : ℕ) - (if i = j then 1 else 0) = (m.1 i : ℕ) := by
        rw [if_neg hij, tsub_zero]
      rw [h1]
      have hmem : i ∈ Finset.univ.erase j := Finset.mem_erase.mpr ⟨hij, Finset.mem_univ i⟩
      have hle : (m.1 i : ℕ) ≤ ∑ k ∈ Finset.univ.erase j, (m.1 k : ℕ) :=
        Finset.single_le_sum (f := fun k => (m.1 k : ℕ)) (fun k _ => Nat.zero_le _) hmem
      have herase : ∑ k ∈ Finset.univ.erase j, (m.1 k : ℕ) = d - (m.1 j : ℕ) := by
        have h := Finset.sum_erase_add (Finset.univ : Finset (Fin (n + 1)))
          (fun k => (m.1 k : ℕ)) (Finset.mem_univ j)
        rw [m.2] at h
        omega
      omega⟩
  property := by
    rw [← Finset.sum_erase_add (Finset.univ : Finset (Fin (n + 1)))
      (fun i => (m.1 i : ℕ) - (if i = j then 1 else 0)) (Finset.mem_univ j)]
    have hother : ∑ i ∈ Finset.univ.erase j, ((m.1 i : ℕ) - (if i = j then 1 else 0))
        = ∑ i ∈ Finset.univ.erase j, (m.1 i : ℕ) := by
      refine Finset.sum_congr rfl (fun i hi => ?_)
      rw [if_neg (Finset.mem_erase.mp hi).1, tsub_zero]
    have hj' : (m.1 j : ℕ) - (if j = j then 1 else 0) = (m.1 j : ℕ) - 1 := by rw [if_pos rfl]
    have herase : ∑ i ∈ Finset.univ.erase j, (m.1 i : ℕ) = d - (m.1 j : ℕ) := by
      have h := Finset.sum_erase_add (Finset.univ : Finset (Fin (n + 1)))
        (fun i => (m.1 i : ℕ)) (Finset.mem_univ j)
      rw [m.2] at h
      omega
    rw [hother, hj', herase]
    omega

@[simp] lemma subE_val (d n : ℕ) (m : Mon d n) (j : Fin (n + 1)) (hj : 1 ≤ (m.1 j : ℕ))
    (i : Fin (n + 1)) :
    ((subE d n m j hj).1 i : ℕ) = (m.1 i : ℕ) - (if i = j then 1 else 0) := rfl

/-- `(m - e_j) + e_j = m`. -/
lemma addE_subE (d n : ℕ) (hd : 1 ≤ d) (m : Mon d n) (j : Fin (n + 1))
    (hj : 1 ≤ (m.1 j : ℕ)) : addE d n hd (subE d n m j hj) j = m := by
  refine Subtype.ext (funext fun i => Fin.ext ?_)
  show ((addE d n hd (subE d n m j hj) j).1 i : ℕ) = (m.1 i : ℕ)
  rw [addE_val, subE_val]
  by_cases hij : i = j
  · subst hij
    have h1 : (m.1 i : ℕ) - (if i = i then 1 else 0) + (if i = i then 1 else 0) = (m.1 i : ℕ) := by
      rw [if_pos rfl]; omega
    rw [h1]
  · have h1 : (m.1 i : ℕ) - (if i = j then 1 else 0) + (if i = j then 1 else 0) = (m.1 i : ℕ) := by
      rw [if_neg hij, tsub_zero, add_zero]
    rw [h1]

end Work.HP.Vero
