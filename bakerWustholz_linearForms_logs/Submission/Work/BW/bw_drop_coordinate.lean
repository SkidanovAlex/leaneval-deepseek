import Mathlib
import Submission.Work.BW.Defs
import Submission.Work.BW.bw_arith_C_pred

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open Complex

theorem bw_drop_coordinate {K : Type*} [Field K] [NumberField K] {n : ℕ} (φ : K →+* ℂ)
    (α : Fin n → K) (hα : ∀ i, α i ≠ 0) (b : Fin n → ℤ) (k : Fin n) (hbk : b k = 0)
    {B : ℕ} (hB : 2 ≤ B) (hbB : ∀ i, (b i).natAbs ≤ B) (hΛ : lam φ α b ≠ 0)
    (IH : ∀ m < n, ∀ β : Fin m → K, (∀ i, β i ≠ 0) → BWHolds φ β) :
    Real.log ‖lam φ α b‖ ≥
      -(BakerWustholz.C n (Module.finrank ℚ K) * max (Real.log B) (1 / (Module.finrank ℚ K : ℝ))
          * ∏ i, BakerWustholz.modifiedHeight φ (α i)) := by
  classical
  have hn1 : 1 ≤ n := by have := k.isLt; omega
  have hd1 : 1 ≤ Module.finrank ℚ K := Module.finrank_pos
  have hdR : (0 : ℝ) < (Module.finrank ℚ K : ℝ) :=
    by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd1)
  have hmod_ge : ∀ i : Fin n,
      1 / (Module.finrank ℚ K : ℝ) ≤ BakerWustholz.modifiedHeight φ (α i) := by
    intro i
    simp only [BakerWustholz.modifiedHeight]
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hCnn : 0 ≤ BakerWustholz.C n (Module.finrank ℚ K) := by
    have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    have hdR1 : (1 : ℝ) ≤ (Module.finrank ℚ K : ℝ) := by exact_mod_cast hd1
    have hlog : 0 ≤ Real.log (2 * (n : ℝ) * (Module.finrank ℚ K : ℝ)) :=
      Real.log_nonneg (by nlinarith)
    simp only [BakerWustholz.C]
    exact mul_nonneg (by positivity) hlog
  set C' : Finset (Fin n) := Finset.univ.erase k with hC'def
  have hk_mem : k ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ k
  have hC'card : C'.card = n - 1 := by
    rw [hC'def, Finset.card_erase_of_mem hk_mem, Finset.card_univ, Fintype.card_fin]
  set e : Fin (n - 1) ≃ {i : Fin n // i ∈ C'} :=
    (Finset.orderIsoOfFin C' hC'card).toEquiv with he
  set β : Fin (n - 1) → K := fun j => α (e j).1 with hβdef
  set b' : Fin (n - 1) → ℤ := fun j => b (e j).1 with hb'def
  have hβne : ∀ j, β j ≠ 0 := fun j => hα _
  have hb'B : ∀ j, (b' j).natAbs ≤ B := fun j => hbB _
  have h1 : (∑ j : Fin (n - 1), (b' j : ℂ) * Complex.log (φ (β j)))
      = ∑ i : {i : Fin n // i ∈ C'}, (b i.1 : ℂ) * Complex.log (φ (α i.1)) :=
    Equiv.sum_comp e (fun i : {i : Fin n // i ∈ C'} => (b i.1 : ℂ) * Complex.log (φ (α i.1)))
  have h2 : (∑ i : {i : Fin n // i ∈ C'}, (b i.1 : ℂ) * Complex.log (φ (α i.1)))
      = ∑ i ∈ C', (b i : ℂ) * Complex.log (φ (α i)) := by
    conv_lhs => rw [← Finset.attach_eq_univ (s := C')]
    exact Finset.sum_attach C' (fun i : Fin n => (b i : ℂ) * Complex.log (φ (α i)))
  have h3 : (∑ i ∈ C', (b i : ℂ) * Complex.log (φ (α i)))
      + (b k : ℂ) * Complex.log (φ (α k))
      = ∑ i : Fin n, (b i : ℂ) * Complex.log (φ (α i)) := by
    rw [hC'def]
    exact Finset.sum_erase_add Finset.univ _ hk_mem
  have hlam_eq : lam φ β b' = lam φ α b := by
    simp only [lam]
    rw [h1, h2, ← h3, hbk]
    simp
  have hprod_eq : (∏ j : Fin (n - 1), BakerWustholz.modifiedHeight φ (β j))
      = ∏ i ∈ C', BakerWustholz.modifiedHeight φ (α i) := by
    have h : (∏ j : Fin (n - 1), BakerWustholz.modifiedHeight φ (β j))
        = ∏ i : {i : Fin n // i ∈ C'}, BakerWustholz.modifiedHeight φ (α i.1) :=
      Equiv.prod_comp e (fun i : {i : Fin n // i ∈ C'} =>
        BakerWustholz.modifiedHeight φ (α i.1))
    rw [h]
    conv_lhs => rw [← Finset.attach_eq_univ (s := C')]
    exact Finset.prod_attach C' (fun i : Fin n => BakerWustholz.modifiedHeight φ (α i))
  have hprod_split : (∏ i : Fin n, BakerWustholz.modifiedHeight φ (α i))
      = BakerWustholz.modifiedHeight φ (α k)
        * ∏ i ∈ C', BakerWustholz.modifiedHeight φ (α i) := by
    rw [hC'def]
    exact (Finset.mul_prod_erase Finset.univ _ hk_mem).symm
  have hne : lam φ β b' ≠ 0 := by rw [hlam_eq]; exact hΛ
  have hIH0 : BWHolds φ β := IH (n - 1) (by omega) β hβne
  have hIH := hIH0 b' B hB hb'B hne
  have hstep : BakerWustholz.C (n - 1) (Module.finrank ℚ K)
      ≤ BakerWustholz.C n (Module.finrank ℚ K) * BakerWustholz.modifiedHeight φ (α k) := by
    have h := bw_arith_C_pred n (Module.finrank ℚ K) hn1 hd1
    have hC' := hmod_ge k
    have hdk : ((Module.finrank ℚ K : ℝ)) ≠ 0 := ne_of_gt hdR
    calc BakerWustholz.C (n - 1) (Module.finrank ℚ K)
        = ((Module.finrank ℚ K : ℝ) * BakerWustholz.C (n - 1) (Module.finrank ℚ K))
            * (1 / (Module.finrank ℚ K : ℝ)) := by field_simp
      _ ≤ (BakerWustholz.C n (Module.finrank ℚ K)) * (1 / (Module.finrank ℚ K : ℝ)) :=
            mul_le_mul_of_nonneg_right h (by positivity)
      _ ≤ (BakerWustholz.C n (Module.finrank ℚ K)) * BakerWustholz.modifiedHeight φ (α k) :=
            mul_le_mul_of_nonneg_left hC' hCnn
  have hP'nn : 0 ≤ ∏ j : Fin (n - 1), BakerWustholz.modifiedHeight φ (β j) :=
    Finset.prod_nonneg (fun j _ =>
      le_trans (by positivity : (0:ℝ) ≤ 1/(Module.finrank ℚ K :ℝ)) (hmod_ge (e j).1))
  have hMnn : 0 ≤ max (Real.log (B:ℝ)) (1 / (Module.finrank ℚ K : ℝ)) :=
    le_trans (by positivity : (0:ℝ) ≤ 1/(Module.finrank ℚ K :ℝ)) (le_max_right _ _)
  have hbound : BakerWustholz.C (n - 1) (Module.finrank ℚ K)
        * max (Real.log (B:ℝ)) (1 / (Module.finrank ℚ K : ℝ))
        * (∏ j : Fin (n - 1), BakerWustholz.modifiedHeight φ (β j))
      ≤ BakerWustholz.C n (Module.finrank ℚ K)
        * max (Real.log (B:ℝ)) (1 / (Module.finrank ℚ K : ℝ))
        * (∏ i : Fin n, BakerWustholz.modifiedHeight φ (α i)) := by
    rw [hprod_split, ← hprod_eq]
    have hmul := mul_le_mul_of_nonneg_right hstep (mul_nonneg hMnn hP'nn)
    nlinarith [hmul]
  rw [hlam_eq] at hIH
  linarith [hIH, hbound]

end Work.BW
