import Mathlib
import Submission.Work.Peluse.PET.prodCubeSum_last_split
import Submission.Work.Peluse.PET.tsum_cubeShiftSum_norm_sq_le
import Submission.Work.Peluse.PET.tsum_sum_shift

set_option autoImplicit false
set_option maxHeartbeats 1600000
open scoped BigOperators

namespace Work.Peluse.PET
namespace TwoMul

noncomputable section

open Work.Peluse

def cubeProd {n : ℕ} (Q : Fin n → Finset ℤ) (h : ℤ → ℂ)
    (z z' : (i : Fin n) → {x : ℤ // x ∈ Q i}) (y : ℤ) : ℂ :=
  ∏ τ : Fin n → Bool, (star^[Work.Peluse.weight τ])
    (h (y + Work.Peluse.cornerShift (fun i => (z i).1) (fun i => (z' i).1) τ))

def cubeShiftSum {n : ℕ} (Q : Fin (n + 1) → Finset ℤ) (h : ℤ → ℂ)
    (z z' : (i : Fin n) → {x : ℤ // x ∈ Q i.castSucc}) (x : ℤ) : ℂ :=
  ∑ a : {x : ℤ // x ∈ Q (Fin.last n)}, cubeProd (fun i => Q i.castSucc) h z z' (x + a.1)

def nu {t : ℕ} (S : Finset ℤ) (Q : Fin t → Finset ℤ) : ℝ :=
  ((S.card : ℝ))⁻¹ * (∏ i : Fin t, (((Q i).card : ℝ))⁻¹)^2

def pairNum {t : ℕ} (Q : Fin t → Finset ℤ) : ℝ := ∏ i : Fin t, (((Q i).card : ℝ))^2

abbrev PetTuple (n : ℕ) (Q : Fin (n + 1) → Finset ℤ) : Type :=
  ((i : Fin n) → {x : ℤ // x ∈ Q i.castSucc}) × ((i : Fin n) → {x : ℤ // x ∈ Q i.castSucc})

lemma nu_nonneg {t : ℕ} (S : Finset ℤ) (Q : Fin t → Finset ℤ) : 0 ≤ nu S Q := by
  unfold nu; positivity

lemma pairNum_nonneg {t : ℕ} (Q : Fin t → Finset ℤ) : 0 ≤ pairNum Q := by
  unfold pairNum; positivity

lemma cornerShift_allFalse {n : ℕ} (z z' : (i : Fin n) → ℤ) :
    Work.Peluse.cornerShift z z' (fun _ => false) = ∑ i, z' i := by
  unfold Work.Peluse.cornerShift
  refine Finset.sum_congr rfl fun i _ => ?_
  simp

lemma cubeProd_zero_of_notMem {n : ℕ} {Q : Fin n → Finset ℤ} {h : ℤ → ℂ} {S : Finset ℤ}
    (hsupp : ∀ x : ℤ, x ∉ S → h x = 0) (z z' : (i : Fin n) → {x : ℤ // x ∈ Q i}) (y : ℤ)
    (hy : y + Work.Peluse.cornerShift (fun i => (z i).1) (fun i => (z' i).1)
      (fun _ => false) ∉ S) :
    cubeProd Q h z z' y = 0 := by
  unfold cubeProd
  refine Finset.prod_eq_zero (Finset.mem_univ (fun _ : Fin n => false)) ?_
  rw [show Work.Peluse.weight (fun _ : Fin n => false) = 0 from ?_]
  · simp only [Function.iterate_zero_apply]
    exact hsupp _ hy
  · unfold Work.Peluse.weight
    simp

lemma summable_cubeProd {n : ℕ} {Q : Fin n → Finset ℤ} {h : ℤ → ℂ} {N : ℕ}
    (hsupp : ∀ x : ℤ, x ∉ Work.Peluse.symIcc N → h x = 0)
    (z z' : (i : Fin n) → {x : ℤ // x ∈ Q i}) :
    Summable (cubeProd Q h z z') := by
  set u : ℤ := Work.Peluse.cornerShift (fun i => (z i).1) (fun i => (z' i).1)
    (fun _ => false) with hu
  refine summable_of_ne_finset_zero (s := Finset.Icc (-(N : ℤ) - u) ((N : ℤ) - u)) ?_
  intro y hy
  have hy' : y ∉ Finset.Icc (-(N : ℤ) - u) ((N : ℤ) - u) := hy
  refine cubeProd_zero_of_notMem (S := Work.Peluse.symIcc N) hsupp z z' y ?_
  simp only [Work.Peluse.symIcc, Finset.mem_Icc, not_and_or, not_le] at hy' ⊢
  rcases hy' with h | h <;> omega

lemma cubeShiftSum_eq_zero_of_notMem {n : ℕ} {Q : Fin (n + 1) → Finset ℤ} {h : ℤ → ℂ} {N : ℕ}
    (hbd : ∀ a ∈ Q (Fin.last n), |a| ≤ (N : ℤ))
    (hsupp : ∀ x : ℤ, x ∉ Work.Peluse.symIcc N → h x = 0)
    (z z' : (i : Fin n) → {x : ℤ // x ∈ Q i.castSucc}) :
    ∀ x : ℤ, x ∉ Finset.Icc (-(2 * (N : ℤ)) - Work.Peluse.cornerShift (fun i => (z i).1)
        (fun i => (z' i).1) (fun _ => false))
      (2 * (N : ℤ) - Work.Peluse.cornerShift (fun i => (z i).1) (fun i => (z' i).1)
        (fun _ => false)) →
      cubeShiftSum Q h z z' x = 0 := by
  intro x hx
  rw [cubeShiftSum]
  refine Finset.sum_eq_zero fun a _ => ?_
  have ha : -(N : ℤ) ≤ a.1 ∧ a.1 ≤ (N : ℤ) := abs_le.mp (hbd a.1 a.2)
  refine cubeProd_zero_of_notMem (S := Work.Peluse.symIcc N) hsupp z z' (x + a.1) ?_
  simp only [Work.Peluse.symIcc, Finset.mem_Icc, not_and_or, not_le] at hx ⊢
  rcases hx with h | h <;> omega

lemma card_interval_le {N : ℕ} (u : ℤ) :
    ((Finset.Icc (-(2 * (N : ℤ)) - u) (2 * (N : ℤ) - u)).card : ℝ)
      ≤ 2 * ((Work.Peluse.symIcc N).card : ℝ) := by
  rw [Int.card_Icc, Work.Peluse.symIcc, Int.card_Icc]
  have h1 : (2 * (N : ℤ) - u + 1 - (-(2 * (N : ℤ)) - u)).toNat = 4 * N + 1 := by
    rw [show (2 * (N:ℤ) - u + 1 - (-(2 * (N:ℤ)) - u)) = 4 * (N:ℤ) + 1 by ring]
    omega
  have h2 : ((N : ℤ) + 1 - (-(N : ℤ))).toNat = 2 * N + 1 := by
    rw [show ((N:ℤ) + 1 - (-(N:ℤ))) = 2 * (N:ℤ) + 1 by ring]
    omega
  rw [h1, h2]
  push_cast
  exact_mod_cast (by omega : 4 * N + 1 ≤ 2 * (2 * N + 1))

lemma norm_sum_sq_le_card {s : Finset ℤ} (f : ℤ → ℂ) :
    ‖∑ x ∈ s, f x‖ ^ 2 ≤ (s.card : ℝ) * ∑ x ∈ s, ‖f x‖ ^ 2 := by
  have h1 : ‖∑ x ∈ s, f x‖ ≤ ∑ x ∈ s, ‖f x‖ := norm_sum_le _ _
  have h2 : (∑ x ∈ s, ‖f x‖) ^ 2 ≤ (s.card : ℝ) * ∑ x ∈ s, ‖f x‖ ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  exact le_trans (pow_le_pow_left₀ (norm_nonneg _) h1 2) h2

lemma norm_ofReal_of_nonneg {r : ℝ} (hr : 0 ≤ r) : ‖((r : ℝ) : ℂ)‖ = r := by
  have h2 : ‖(((r : ℝ)) : ℂ)‖ ^ 2 = r ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]; ring
  nlinarith [norm_nonneg (((r : ℝ) : ℂ))]

lemma norm_natCast_complex (n : ℕ) : ‖((n : ℕ) : ℂ)‖ = (n : ℝ) := by
  have h2 : ‖(((n : ℕ)) : ℂ)‖ ^ 2 = (n : ℝ) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_natCast]
    push_cast; ring
  nlinarith [norm_nonneg (((n : ℕ) : ℂ))]

lemma card_tuple_eq_pairNum {n : ℕ} (Q : Fin (n + 1) → Finset ℤ) :
    (Fintype.card (PetTuple n Q) : ℝ) = pairNum (fun i : Fin n => Q i.castSucc) := by
  change (Fintype.card (((i : Fin n) → {x : ℤ // x ∈ Q i.castSucc}) ×
      ((i : Fin n) → {x : ℤ // x ∈ Q i.castSucc})) : ℝ) = pairNum (fun i : Fin n => Q i.castSucc)
  have hcard : Fintype.card ((i : Fin n) → {x : ℤ // x ∈ Q i.castSucc})
      = ∏ i : Fin n, (Q i.castSucc).card := by
    rw [Fintype.card_pi]
    exact Finset.prod_congr rfl fun i _ => Fintype.card_coe (Q i.castSucc)
  rw [Fintype.card_prod, hcard]
  unfold pairNum
  rw [Finset.prod_pow]
  push_cast
  ring

end
end TwoMul

open TwoMul

theorem two_mul_boxNormPow_succ_ge {n : ℕ} (Q : Fin (n + 1) → Finset ℤ) {N : ℕ} (hN : 0 < N)
    (h : ℤ → ℂ) (hQ : ∀ i, (Q i).Nonempty)
    (hbd : ∀ a ∈ Q (Fin.last n), |a| ≤ (N : ℤ))
    (hsupp : ∀ x : ℤ, x ∉ Work.Peluse.symIcc N → h x = 0)
    (hreal : ∀ x : ℤ, h x = ((‖h x‖ : ℝ) : ℂ)) :
    (Work.Peluse.boxNormPow n (fun i : Fin n => Q i.castSucc) (Work.Peluse.symIcc N) h) ^ 2
      ≤ 2 * Work.Peluse.boxNormPow (n + 1) Q (Work.Peluse.symIcc N) h := by
  classical
  have hQncard : (0 : ℝ) < ((Q (Fin.last n)).card : ℝ) := by
    have : 0 < (Q (Fin.last n)).card := Finset.card_pos.mpr (hQ (Fin.last n))
    exact_mod_cast this
  have hScard : (0 : ℝ) < ((Work.Peluse.symIcc N).card : ℝ) := by
    have : 0 < (Work.Peluse.symIcc N).card := Finset.card_pos.mpr ⟨0, by
      rw [Work.Peluse.symIcc, Finset.mem_Icc]; omega⟩
    exact_mod_cast this
  have hfs : Work.Peluse.FinSuppZ h := ⟨N, fun x hx => by
    apply hsupp
    rw [Work.Peluse.symIcc, Finset.mem_Icc]
    intro hcon
    have h1 : |x| ≤ (N : ℤ) := abs_le.mpr ⟨hcon.1, hcon.2⟩
    rw [Int.abs_eq_natAbs] at h1
    have h2 : x.natAbs ≤ N := by exact_mod_cast h1
    omega⟩
  set W : ℝ := ∑ p : PetTuple n Q, ∑' x : ℤ, ‖cubeShiftSum Q h p.1 p.2 x‖ ^ 2 with hWdef
  set V : ℂ := ∑ p : PetTuple n Q,
    ∑' x : ℤ, cubeProd (fun i : Fin n => Q i.castSucc) h p.1 p.2 x with hVdef
  have hWnn : 0 ≤ W := by
    rw [hWdef]
    exact Finset.sum_nonneg fun p _ => tsum_nonneg fun x => by positivity
  -- (I) the top-dimensional cube sum
  have hI : Work.Peluse.boxSumPow (n + 1) Q (Work.Peluse.symIcc N) h
      = ((nu (Work.Peluse.symIcc N) Q * W : ℝ) : ℂ) := by
    rw [Work.Peluse.boxSumPow, prodCubeSum_last_split Q (Work.Peluse.symIcc N) h hfs]
    rw [show (∑ p : PetTuple n Q,
          ∑' x : ℤ, ‖∑ a : {x : ℤ // x ∈ Q (Fin.last n)},
            ∏ τ : Fin n → Bool, (star^[Work.Peluse.weight τ])
              (h (x + a.1 + Work.Peluse.cornerShift (fun i => (p.1 i).1) (fun i => (p.2 i).1) τ))‖ ^ 2)
        = (∑ p : PetTuple n Q, ∑' x : ℤ, ‖cubeShiftSum Q h p.1 p.2 x‖ ^ 2) from
      Finset.sum_congr rfl fun p _ => tsum_congr fun x => by simp only [cubeShiftSum, cubeProd]]
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_mul]
    rw [show ((Work.Peluse.symIcc N).card : ℝ)⁻¹ * (∏ i : Fin (n + 1), (((Q i).card : ℝ))⁻¹)
        * (∏ i : Fin (n + 1), (((Q i).card : ℝ))⁻¹) = nu (Work.Peluse.symIcc N) Q from by
      unfold nu; rw [pow_two]; ring]
  -- (II) the lower-dimensional cube sum
  have hII : Work.Peluse.boxSumPow n (fun i : Fin n => Q i.castSucc) (Work.Peluse.symIcc N) h
      = ((nu (Work.Peluse.symIcc N) (fun i : Fin n => Q i.castSucc) : ℝ) : ℂ) * V := by
    rw [Work.Peluse.boxSumPow, Work.Peluse.prodCubeSum]
    have hconst : ((Work.Peluse.symIcc N).card : ℂ)⁻¹
        * (∏ i : Fin n, (((Q i.castSucc).card : ℂ))⁻¹)
        * (∏ i : Fin n, (((Q i.castSucc).card : ℂ))⁻¹)
        = ((nu (Work.Peluse.symIcc N) (fun i : Fin n => Q i.castSucc) : ℝ) : ℂ) := by
      unfold nu
      rw [pow_two]
      push_cast
      ring
    rw [hconst]
    congr 1
    rw [hVdef, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    exact tsum_congr fun x => by simp only [cubeProd]
  have hbn : Work.Peluse.boxNormPow n (fun i : Fin n => Q i.castSucc) (Work.Peluse.symIcc N) h
      = nu (Work.Peluse.symIcc N) (fun i : Fin n => Q i.castSucc) * ‖V‖ := by
    rw [Work.Peluse.boxNormPow, hII, norm_mul,
      norm_ofReal_of_nonneg (nu_nonneg _ _)]
  have hbn1 : Work.Peluse.boxNormPow (n + 1) Q (Work.Peluse.symIcc N) h
      = nu (Work.Peluse.symIcc N) Q * W := by
    rw [Work.Peluse.boxNormPow, hI,
      norm_ofReal_of_nonneg (mul_nonneg (nu_nonneg _ _) hWnn)]
  -- per-p bound
  have hper : ∀ p : PetTuple n Q,
      ‖∑' x : ℤ, cubeProd (fun i : Fin n => Q i.castSucc) h p.1 p.2 x‖ ^ 2
        ≤ 2 * ((Work.Peluse.symIcc N).card : ℝ)
          * (∑' x : ℤ, ‖cubeShiftSum Q h p.1 p.2 x‖ ^ 2)
          / ((Q (Fin.last n)).card : ℝ) ^ 2 := by
    intro p
    have hD2 : ∑' x : ℤ, cubeShiftSum Q h p.1 p.2 x
        = ((Q (Fin.last n)).card : ℂ)
          * ∑' x : ℤ, cubeProd (fun i : Fin n => Q i.castSucc) h p.1 p.2 x := by
      have h1 : (∑' x : ℤ, cubeShiftSum Q h p.1 p.2 x)
          = ∑' x : ℤ, ∑ a ∈ Q (Fin.last n),
              cubeProd (fun i : Fin n => Q i.castSucc) h p.1 p.2 (x + a) := by
        refine tsum_congr fun x => ?_
        rw [cubeShiftSum]
        exact Finset.sum_attach (Q (Fin.last n))
          (fun a => cubeProd (fun i : Fin n => Q i.castSucc) h p.1 p.2 (x + a))
      exact h1.trans (tsum_sum_shift (Q (Fin.last n)) (summable_cubeProd hsupp p.1 p.2))
    have hD3 : ‖∑' x : ℤ, cubeShiftSum Q h p.1 p.2 x‖ ^ 2
        ≤ 2 * ((Work.Peluse.symIcc N).card : ℝ)
          * (∑' x : ℤ, ‖cubeShiftSum Q h p.1 p.2 x‖ ^ 2) := by
      simpa only [cubeShiftSum, cubeProd] using
        tsum_cubeShiftSum_norm_sq_le Q hN h hbd hsupp p.1 p.2
    have hnorm : ‖∑' x : ℤ, cubeShiftSum Q h p.1 p.2 x‖
        = ((Q (Fin.last n)).card : ℝ)
          * ‖∑' x : ℤ, cubeProd (fun i : Fin n => Q i.castSucc) h p.1 p.2 x‖ := by
      rw [hD2, norm_mul, norm_natCast_complex]
    have hsq : ((Q (Fin.last n)).card : ℝ) ^ 2
        * ‖∑' x : ℤ, cubeProd (fun i : Fin n => Q i.castSucc) h p.1 p.2 x‖ ^ 2
        ≤ 2 * ((Work.Peluse.symIcc N).card : ℝ)
          * (∑' x : ℤ, ‖cubeShiftSum Q h p.1 p.2 x‖ ^ 2) := by
      calc ((Q (Fin.last n)).card : ℝ) ^ 2
            * ‖∑' x : ℤ, cubeProd (fun i : Fin n => Q i.castSucc) h p.1 p.2 x‖ ^ 2
          = ‖∑' x : ℤ, cubeShiftSum Q h p.1 p.2 x‖ ^ 2 := by rw [hnorm, mul_pow]
        _ ≤ _ := hD3
    rw [le_div_iff₀ (pow_pos hQncard 2)]
    nlinarith [hsq]
  -- the ‖V‖ bound
  have hVbound : ‖V‖ ^ 2 ≤ 2 * ((Work.Peluse.symIcc N).card : ℝ)
      * pairNum (fun i : Fin n => Q i.castSucc) / ((Q (Fin.last n)).card : ℝ) ^ 2 * W := by
    have hsum_le : ‖V‖ ^ 2 ≤ (Fintype.card (PetTuple n Q) : ℝ)
        * ∑ p : PetTuple n Q, (2 * ((Work.Peluse.symIcc N).card : ℝ)
            * (∑' x : ℤ, ‖cubeShiftSum Q h p.1 p.2 x‖ ^ 2)
            / ((Q (Fin.last n)).card : ℝ) ^ 2) := by
      rw [hVdef]
      refine le_trans (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2) ?_
      refine le_trans sq_sum_le_card_mul_sum_sq ?_
      exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun p _ => hper p)
        (Nat.cast_nonneg _)
    have hfac : (∑ p : PetTuple n Q, (2 * ((Work.Peluse.symIcc N).card : ℝ)
            * (∑' x : ℤ, ‖cubeShiftSum Q h p.1 p.2 x‖ ^ 2)
            / ((Q (Fin.last n)).card : ℝ) ^ 2))
        = 2 * ((Work.Peluse.symIcc N).card : ℝ) / ((Q (Fin.last n)).card : ℝ) ^ 2 * W := by
      rw [hWdef, Finset.mul_sum]
      exact Finset.sum_congr rfl fun p _ => by ring
    rw [hfac, card_tuple_eq_pairNum] at hsum_le
    calc ‖V‖ ^ 2 ≤ pairNum (fun i : Fin n => Q i.castSucc)
          * (2 * ((Work.Peluse.symIcc N).card : ℝ) / ((Q (Fin.last n)).card : ℝ) ^ 2 * W) := hsum_le
      _ = 2 * ((Work.Peluse.symIcc N).card : ℝ) * pairNum (fun i : Fin n => Q i.castSucc)
          / ((Q (Fin.last n)).card : ℝ) ^ 2 * W := by ring
  -- coefficient identities
  have hcoef1 : nu (Work.Peluse.symIcc N) (fun i : Fin n => Q i.castSucc)
      * ((Work.Peluse.symIcc N).card : ℝ) * pairNum (fun i : Fin n => Q i.castSucc) = 1 := by
    have hS0 : ((Work.Peluse.symIcc N).card : ℝ) ≠ 0 := ne_of_gt hScard
    have hprod : (∏ i : Fin n, (((Q i.castSucc).card : ℝ))⁻¹)
        * (∏ i : Fin n, ((Q i.castSucc).card : ℝ)) = 1 := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_eq_one fun i _ => ?_
      rw [inv_mul_cancel₀]
      exact_mod_cast Finset.card_ne_zero.mpr (hQ i.castSucc)
    calc nu (Work.Peluse.symIcc N) (fun i : Fin n => Q i.castSucc)
          * ((Work.Peluse.symIcc N).card : ℝ) * pairNum (fun i : Fin n => Q i.castSucc)
        = (((Work.Peluse.symIcc N).card : ℝ)⁻¹ * ((Work.Peluse.symIcc N).card : ℝ))
          * ((∏ i : Fin n, (((Q i.castSucc).card : ℝ))⁻¹)
              * (∏ i : Fin n, ((Q i.castSucc).card : ℝ))) ^ 2 := by
            unfold nu pairNum
            rw [Finset.prod_pow]
            ring
      _ = 1 := by rw [inv_mul_cancel₀ hS0, hprod]; ring
  have hcoef2 : nu (Work.Peluse.symIcc N) Q * ((Q (Fin.last n)).card : ℝ) ^ 2
      = nu (Work.Peluse.symIcc N) (fun i : Fin n => Q i.castSucc) := by
    have hp : ((Q (Fin.last n)).card : ℝ) ≠ 0 := ne_of_gt hQncard
    have h1 : (((Q (Fin.last n)).card : ℝ))⁻¹ * ((Q (Fin.last n)).card : ℝ) = 1 :=
      inv_mul_cancel₀ hp
    calc nu (Work.Peluse.symIcc N) Q * ((Q (Fin.last n)).card : ℝ) ^ 2
        = ((Work.Peluse.symIcc N).card : ℝ)⁻¹
          * ((∏ i : Fin n, (((Q i.castSucc).card : ℝ))⁻¹)
              * ((((Q (Fin.last n)).card : ℝ))⁻¹ * ((Q (Fin.last n)).card : ℝ))) ^ 2 := by
          unfold nu
          rw [Fin.prod_univ_castSucc]
          ring
      _ = ((Work.Peluse.symIcc N).card : ℝ)⁻¹
          * (∏ i : Fin n, (((Q i.castSucc).card : ℝ))⁻¹) ^ 2 := by
          rw [h1]; ring
      _ = nu (Work.Peluse.symIcc N) (fun i : Fin n => Q i.castSucc) := by
          unfold nu; ring
  have hcoef : (nu (Work.Peluse.symIcc N) (fun i : Fin n => Q i.castSucc)) ^ 2
      * (2 * ((Work.Peluse.symIcc N).card : ℝ) * pairNum (fun i : Fin n => Q i.castSucc)
          / ((Q (Fin.last n)).card : ℝ) ^ 2) = 2 * nu (Work.Peluse.symIcc N) Q := by
    have hp2 : ((Q (Fin.last n)).card : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hQncard)
    have hA : (nu (Work.Peluse.symIcc N) (fun i : Fin n => Q i.castSucc)) ^ 2
        * (2 * ((Work.Peluse.symIcc N).card : ℝ) * pairNum (fun i : Fin n => Q i.castSucc)
            / ((Q (Fin.last n)).card : ℝ) ^ 2)
        = 2 * (nu (Work.Peluse.symIcc N) (fun i : Fin n => Q i.castSucc)
            * ((Work.Peluse.symIcc N).card : ℝ) * pairNum (fun i : Fin n => Q i.castSucc))
          * (nu (Work.Peluse.symIcc N) (fun i : Fin n => Q i.castSucc)
            / ((Q (Fin.last n)).card : ℝ) ^ 2) := by
      rw [div_eq_mul_inv, div_eq_mul_inv]; ring
    rw [hA, hcoef1]
    have hb : 2 * 1 * (nu (Work.Peluse.symIcc N) (fun i : Fin n => Q i.castSucc)
        / ((Q (Fin.last n)).card : ℝ) ^ 2)
        = 2 * (nu (Work.Peluse.symIcc N) (fun i : Fin n => Q i.castSucc)
        / ((Q (Fin.last n)).card : ℝ) ^ 2) := by ring
    rw [hb]
    congr 1
    rw [div_eq_iff hp2]
    exact hcoef2.symm
  rw [hbn, hbn1]
  calc (nu (Work.Peluse.symIcc N) (fun i : Fin n => Q i.castSucc) * ‖V‖) ^ 2
      = (nu (Work.Peluse.symIcc N) (fun i : Fin n => Q i.castSucc)) ^ 2 * ‖V‖ ^ 2 := by ring
    _ ≤ (nu (Work.Peluse.symIcc N) (fun i : Fin n => Q i.castSucc)) ^ 2
        * (2 * ((Work.Peluse.symIcc N).card : ℝ) * pairNum (fun i : Fin n => Q i.castSucc)
            / ((Q (Fin.last n)).card : ℝ) ^ 2 * W) :=
        mul_le_mul_of_nonneg_left hVbound (sq_nonneg _)
    _ = 2 * nu (Work.Peluse.symIcc N) Q * W := by rw [← mul_assoc, hcoef]
    _ = 2 * (nu (Work.Peluse.symIcc N) Q * W) := by ring


end Work.Peluse.PET
