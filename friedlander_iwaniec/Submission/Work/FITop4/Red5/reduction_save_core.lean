import Mathlib
import Submission.Work.FITop4.Red5.window_setup
import Submission.Work.FITop4.Red5.thin_annulus_own
import Submission.Work.FITop4.Red5.window_T2_shell_of_crux
import Submission.Work.FITop4.Red5.window_T2_cop_le
import Submission.Work.FITop4.Red5.window_bound_act
import Submission.Work.FITop4.Defs4
import Submission.Work.FITop4.Red5.Vocab
import Submission.Work.FITop.Defs
import Submission.Work.FITop3.Majorant.majorant_props
import Submission.Work.FITop4.Numeric4.numHyp_proof2
import Submission.Work.FITop4.Red5.window_cover
import Submission.Work.FITop4.Red5.red5num_proof
import Submission.Work.FITop4.Red5.mollifier_family
import Submission.Work.FITop4.Red5.BformPiTauSmall_le2
import Submission.Work.FITop4.Red5.BformPiTau_tauReduce
import Submission.Work.FITop4.Red5.pieceDefs
import Submission.Work.FITop4.Red5.isPrimitive_of_sqfree_primary
import Submission.Work.FITop4.Red5.window_T3_le
import Submission.Work.FITop4.Red5.window_T1_le
import Submission.Work.FITop4.Red5.sieve_inner_le_pieces_act
import Submission.Work.FIChain.AcountAtilC_le_const_mul_rpow
import Submission.Work.FITop4.Red5.Red5NumC
import Submission.Work.FITop4.Red5.window_error_sum
import Submission.Work.FITop4.Red5.tauOf_le_of_Nrange
import Submission.Work.FITop4.Red5.red5numC_proof

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.FITop4.Red5

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 1. Elementary window facts -/

lemma two_mul_MtopN_le_x {x N : ℕ} (hN : 1 ≤ N) (htop : MtopN x N * (2 * N) ≤ x) :
    2 * MtopN x N ≤ x := by
  calc 2 * MtopN x N ≤ (2 * N) * MtopN x N := Nat.mul_le_mul_right _ (by omega)
    _ = MtopN x N * (2 * N) := by ring
    _ ≤ x := htop

lemma x_lt_N_mul_two_MtopN_add_two (x N : ℕ) (hN : 1 ≤ N) :
    x < N * (2 * MtopN x N + 2) := by
  have hmod : x % (2 * N) < 2 * N := Nat.mod_lt _ (by omega)
  have hdecomp : x = (x / (2 * N)) * (2 * N) + x % (2 * N) := by
    rw [mul_comm]; exact (Nat.div_add_mod x (2 * N)).symm
  rw [MtopN]
  calc x = (x / (2 * N)) * (2 * N) + x % (2 * N) := hdecomp
    _ < (x / (2 * N)) * (2 * N) + 2 * N := by omega
    _ = N * (2 * (x / (2 * N)) + 2) := by ring

lemma N_mul_two_MtopN_add_two_le_succ_mul {x N : ℕ} (hMge : N ≤ 2 * MtopN x N) :
    N * (2 * MtopN x N + 2) ≤ (2 * MtopN x N + 1) * (N + 1) := by
  have h : N * (2 * MtopN x N + 2) + (2 * MtopN x N + 1)
      = (2 * MtopN x N + 1) * (N + 1) + N := by ring
  omega

lemma Iterm_eq_zero_of_window {x N Pz : ℕ} {C τ : ℝ} {m : ℕ}
    (hN : 1 ≤ N) (hMge : N ≤ 2 * MtopN x N)
    (hm : 2 * MtopN x N < m) :
    Iterm x N Pz C τ m = 0 := by
  refine Iterm_eq_zero_of_lt x N Pz C τ ?_
  have h1 : N * (2 * MtopN x N + 2) ≤ (2 * MtopN x N + 1) * (N + 1) :=
    N_mul_two_MtopN_add_two_le_succ_mul hMge
  have h2 : (2 * MtopN x N + 1) * (N + 1) ≤ m * (N + 1) :=
    Nat.mul_le_mul_right _ (by omega)
  have h3 : x < N * (2 * MtopN x N + 2) := x_lt_N_mul_two_MtopN_add_two x N hN
  omega

lemma BformPiTau_eq_sum_window (x N Pz : ℕ) (C τ : ℝ)
    (hN : 1 ≤ N) (htop : MtopN x N * (2 * N) ≤ x) (hMge : N ≤ 2 * MtopN x N) :
    BformPiTau x N Pz C τ
      = ∑ m ∈ Finset.Icc 1 (2 * MtopN x N), Iterm x N Pz C τ m := by
  rw [BformPiTau_eq_sum_Iterm]
  refine (Finset.sum_subset ?_ ?_).symm
  · intro m hm
    rw [Finset.mem_Icc] at hm ⊢
    exact ⟨hm.1, le_trans hm.2 (two_mul_MtopN_le_x hN htop)⟩
  · intro m hm hnot
    rw [Finset.mem_Icc] at hm
    exact Iterm_eq_zero_of_window hN hMge (by
      by_contra h
      exact hnot (Finset.mem_Icc.mpr ⟨hm.1, by omega⟩))

/-! ## 2. The `badInd` split -/

lemma two_badInd_mul_le (mm x : ℕ) (τ : ℝ) (n : ℕ) (X : ℝ) (hX : 0 ≤ X)
    (hτ : TauCond τ n) :
    2 * badInd mm x τ n * X
      ≤ 2 * (if Nat.Coprime mm n then (0 : ℝ) else 1) * X
        + 2 * (if (mm : ℝ) * (n : ℝ) > (x : ℝ) then (1 : ℝ) else 0) * X := by
  rw [badInd, goodPred]
  by_cases hc : Nat.Coprime mm n
  · by_cases hs : (mm : ℝ) * (n : ℝ) > (x : ℝ)
    · have hnat : ¬ (mm * n ≤ x) := fun h => not_le.mpr hs (by exact_mod_cast h)
      rw [if_neg (fun h => hnat h.2.1), if_pos hc, if_pos hs]
      linarith
    · have hle : (mm : ℝ) * (n : ℝ) ≤ (x : ℝ) := not_lt.mp hs
      have hnat : mm * n ≤ x := by exact_mod_cast hle
      rw [if_pos ⟨hc, hnat, hτ⟩, if_pos hc, if_neg hs]
      linarith
  · rw [if_neg (fun h => hc h.1), if_neg hc]
    have hnn : (0 : ℝ) ≤ (if (mm : ℝ) * (n : ℝ) > (x : ℝ) then (1 : ℝ) else 0) := by
      split_ifs <;> norm_num
    nlinarith [hX, hnn]

/-- `pieceCoeff` vanishes off its support condition. -/
lemma tauCond_of_pieceCoeff_ne_zero {Pa : Work.FITop.Params} {φ : ℝ} {q p : ℝ → ℝ}
    {z : GaussianInt} (h : pieceCoeff Pa φ q p z ≠ 0) :
    (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) ≤ Pa.τ := by
  rw [pieceCoeff] at h
  split_ifs at h with hc
  · exact hc.2.2
  · exact absurd rfl h

lemma prime_of_pieceCoeff_ne_zero {Pa : Work.FITop.Params} {φ : ℝ} {q p : ℝ → ℝ}
    {z : GaussianInt} (h : pieceCoeff Pa φ q p z ≠ 0) :
    Work.FIPlan.IsPrimary z := by
  rw [pieceCoeff] at h
  split_ifs at h with hc
  · exact hc.1.1
  · exact absurd rfl h

lemma isPrimitive_of_pieceCoeff_ne_zero {Pa : Work.FITop.Params} {φ : ℝ} {q p : ℝ → ℝ}
    {z : GaussianInt} (h : pieceCoeff Pa φ q p z ≠ 0) :
    Work.FIPlan.IsPrimitive z := by
  have hmu : ArithmeticFunction.moebius (Work.FIPlan.gnorm z) ≠ 0 := by
    intro h0
    apply h
    rw [pieceCoeff]
    split_ifs
    · rw [h0]; simp
    · rfl
  exact isPrimitive_of_sqfree_primary
    (ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp hmu)
    (prime_of_pieceCoeff_ne_zero h)

/-- The termwise `badInd` bound for one piece coefficient. -/
lemma badInd_mul_norm_le (x : ℕ) (τ : ℝ) (mm : ℕ) (w z : GaussianInt)
    (Pa : Work.FITop.Params) (hτ : Pa.τ = τ)
    (φ : ℝ) (q p : ℝ → ℝ) :
    2 * badInd mm x τ (Work.FIPlan.gnorm z)
        * ‖pieceCoeff Pa φ q p z * Work.FITop3.Zc w z‖
      ≤ 2 * (if Nat.Coprime mm (Work.FIPlan.gnorm z) then (0 : ℝ) else 1)
          * ‖pieceCoeff Pa φ q p z * Work.FITop3.Zc w z‖
        + 2 * (if (mm : ℝ) * (Work.FIPlan.gnorm z : ℝ) > (x : ℝ) then (1 : ℝ) else 0)
          * ‖pieceCoeff Pa φ q p z * Work.FITop3.Zc w z‖ := by
  by_cases hpc : pieceCoeff Pa φ q p z = 0
  · rw [hpc]; simp only [zero_mul, norm_zero, mul_zero, mul_zero]; positivity
  · refine two_badInd_mul_le mm x τ (Work.FIPlan.gnorm z) _ (norm_nonneg _) ?_
    rw [← hτ]
    exact tauCond_of_pieceCoeff_ne_zero hpc


/-! ## 3. The count bound over the window ladder -/

private lemma rpow_34_pow (j : ℕ) (c : ℝ) (hc : 0 ≤ c) :
    (c ^ j) ^ ((3 : ℝ) / 4) = (c ^ ((3 : ℝ) / 4)) ^ j := by
  calc (c ^ j) ^ ((3 : ℝ) / 4) = (c ^ (j : ℝ)) ^ ((3 : ℝ) / 4) := by rw [Real.rpow_natCast]
    _ = c ^ ((j : ℝ) * ((3 : ℝ) / 4)) := by rw [Real.rpow_mul hc]
    _ = c ^ (((3 : ℝ) / 4) * j) := by rw [mul_comm]
    _ = (c ^ ((3 : ℝ) / 4)) ^ (j : ℝ) := by rw [Real.rpow_mul hc]
    _ = (c ^ ((3 : ℝ) / 4)) ^ j := by rw [Real.rpow_natCast]

private lemma geom_sum_fin_le {r : ℝ} (hr : 1 < r) (n : ℕ) :
    (∑ j : Fin n, r ^ (j : ℕ)) ≤ r ^ n / (r - 1) := by
  rw [Fin.sum_univ_eq_sum_range (fun i => r ^ i) n, geom_sum_eq (ne_of_gt hr) n]
  apply div_le_div_of_nonneg_right _ (by linarith : (0 : ℝ) ≤ r - 1)
  have h : (1 : ℝ) ≤ r ^ n := one_le_pow₀ hr.le
  linarith

lemma MnOf_le_two_pow_mul (x N j : ℕ) : MnOf x N j ≤ 2 ^ j * M0N x N := by
  by_cases h : j < JJN x N
  · rw [MnOf_of_lt h]
  · rw [MnOf_of_not_lt h]
    calc MtopN x N ≤ 2 ^ (JJN x N) * M0N x N := le_of_lt (MtopN_lt_two_pow_JJN x N)
      _ ≤ 2 ^ j * M0N x N := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (by omega))

/-- The `(3/4)`-count of the pieces of the window ladder, with an explicit constant. -/
lemma piece_count_window (x N : ℕ) (θ : ℝ) (K K' : ℕ) (a : Fin K → ℝ)
    (hN : 1 ≤ N) (hx1 : 1 ≤ x) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (hpow : (2 : ℝ) ^ (JJN x N) * (M0N x N : ℝ) ≤ (x : ℝ) / (N : ℝ))
    (haN : ∀ i, (N : ℝ) ≤ a i) (ha2 : ∀ i, a i ≤ 2 * (N : ℝ))
    (hK : (K : ℝ) ≤ 4 / θ + 4) (hK' : (K' : ℝ) ≤ 4 / θ + 4) :
    (∑ i, ∑ _k : Fin K', ∑ j : Fin (JJN x N + 1), (((MnOf x N j : ℝ) * a i) ^ ((3 : ℝ) / 4)))
      ≤ 64 * ((4 : ℝ) ^ ((3 : ℝ) / 4) / ((2 : ℝ) ^ ((3 : ℝ) / 4) - 1)) * θ ^ (-(2 : ℝ))
          * (x : ℝ) ^ ((3 : ℝ) / 4) := by
  set r : ℝ := (2 : ℝ) ^ ((3 : ℝ) / 4) with hrdef
  have hr1 : 1 < r := Real.one_lt_rpow (by norm_num) (by norm_num)
  have hrm1 : 0 < r - 1 := by linarith
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hxpos : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (by omega : 0 < x)
  have hM0pos : 0 < (M0N x N : ℝ) := by exact_mod_cast M0N_pos x N
  have hper : ∀ i : Fin K,
      (∑ j : Fin (JJN x N + 1), (((MnOf x N j : ℝ) * a i) ^ ((3 : ℝ) / 4)))
        ≤ ((4 : ℝ) ^ ((3 : ℝ) / 4) / (r - 1)) * (x : ℝ) ^ ((3 : ℝ) / 4) := by
    intro i
    have hai0 : 0 ≤ a i := le_trans (by positivity) (haN i)
    have hAu0 : 0 ≤ ((M0N x N : ℝ) * a i) ^ ((3 : ℝ) / 4) := Real.rpow_nonneg (by positivity) _
    have hterm : ∀ j : Fin (JJN x N + 1),
        ((MnOf x N j : ℝ) * a i) ^ ((3 : ℝ) / 4)
          ≤ ((M0N x N : ℝ) * a i) ^ ((3 : ℝ) / 4) * r ^ (j : ℕ) := by
      intro j
      have h1 : (MnOf x N j : ℝ) ≤ (2 : ℝ) ^ (j : ℕ) * (M0N x N : ℝ) := by
        exact_mod_cast MnOf_le_two_pow_mul x N j
      have hle : ((MnOf x N j : ℝ) * a i)
          ≤ (((2 : ℝ) ^ (j : ℕ)) * (M0N x N : ℝ)) * a i :=
        mul_le_mul_of_nonneg_right h1 hai0
      calc ((MnOf x N j : ℝ) * a i) ^ ((3 : ℝ) / 4)
          ≤ ((((2 : ℝ) ^ (j : ℕ)) * (M0N x N : ℝ)) * a i) ^ ((3 : ℝ) / 4) :=
            Real.rpow_le_rpow (by positivity) hle (by norm_num)
        _ = r ^ (j : ℕ) * ((M0N x N : ℝ) ^ ((3 : ℝ) / 4) * (a i) ^ ((3 : ℝ) / 4)) := by
            rw [Real.mul_rpow (by positivity) hai0, Real.mul_rpow (by positivity) hM0pos.le,
              rpow_34_pow (j : ℕ) 2 (by norm_num), hrdef]
            ring
        _ = ((M0N x N : ℝ) * a i) ^ ((3 : ℝ) / 4) * r ^ (j : ℕ) := by
            rw [← Real.mul_rpow hM0pos.le hai0]; ring
    have hsum : (∑ j : Fin (JJN x N + 1), ((MnOf x N j : ℝ) * a i) ^ ((3 : ℝ) / 4))
        ≤ ((M0N x N : ℝ) * a i) ^ ((3 : ℝ) / 4)
            * (∑ j : Fin (JJN x N + 1), r ^ (j : ℕ)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun j _ => hterm j)
    have hbig : (((2 : ℝ) ^ (JJN x N + 1)) * (M0N x N : ℝ)) * a i ≤ 4 * (x : ℝ) := by
      have h2N0 : (0 : ℝ) ≤ 2 * (N : ℝ) := by positivity
      calc (((2 : ℝ) ^ (JJN x N + 1)) * (M0N x N : ℝ)) * a i
          ≤ (((2 : ℝ) ^ (JJN x N + 1)) * (M0N x N : ℝ)) * (2 * (N : ℝ)) :=
            mul_le_mul_of_nonneg_left (ha2 i) (by positivity)
        _ = 4 * ((2 : ℝ) ^ (JJN x N) * (M0N x N : ℝ) * (N : ℝ)) := by
            rw [pow_succ]; ring
        _ ≤ 4 * (x : ℝ) := by
            have h3 : (2 : ℝ) ^ (JJN x N) * (M0N x N : ℝ) * (N : ℝ) ≤ (x : ℝ) := by
              have h := mul_le_mul_of_nonneg_right hpow hNpos.le
              rwa [div_mul_cancel₀ _ (ne_of_gt hNpos)] at h
            linarith
    have hkey : ((((2 : ℝ) ^ (JJN x N + 1)) * (M0N x N : ℝ)) * a i) ^ ((3 : ℝ) / 4)
        = ((M0N x N : ℝ) * a i) ^ ((3 : ℝ) / 4) * r ^ (JJN x N + 1) := by
      rw [Real.mul_rpow (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (JJN x N + 1) * (M0N x N : ℝ)) hai0,
        Real.mul_rpow (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (JJN x N + 1)) hM0pos.le,
        rpow_34_pow (JJN x N + 1) 2 (by norm_num), hrdef]
      rw [Real.mul_rpow hM0pos.le hai0]
      ring
    calc (∑ j : Fin (JJN x N + 1), ((MnOf x N j : ℝ) * a i) ^ ((3 : ℝ) / 4))
        ≤ ((M0N x N : ℝ) * a i) ^ ((3 : ℝ) / 4)
            * (∑ j : Fin (JJN x N + 1), r ^ (j : ℕ)) := hsum
      _ ≤ ((M0N x N : ℝ) * a i) ^ ((3 : ℝ) / 4) * (r ^ (JJN x N + 1) / (r - 1)) :=
          mul_le_mul_of_nonneg_left (geom_sum_fin_le hr1 (JJN x N + 1)) hAu0
      _ = (((M0N x N : ℝ) * a i) ^ ((3 : ℝ) / 4) * r ^ (JJN x N + 1)) / (r - 1) := by
          rw [mul_div_assoc']
      _ = ((((2 : ℝ) ^ (JJN x N + 1)) * (M0N x N : ℝ)) * a i) ^ ((3 : ℝ) / 4) / (r - 1) := by
          rw [← hkey]
      _ ≤ (4 * (x : ℝ)) ^ ((3 : ℝ) / 4) / (r - 1) :=
          div_le_div_of_nonneg_right (Real.rpow_le_rpow (by positivity) hbig (by norm_num)) hrm1.le
      _ = ((4 : ℝ) ^ ((3 : ℝ) / 4) / (r - 1)) * (x : ℝ) ^ ((3 : ℝ) / 4) := by
          rw [Real.mul_rpow (by norm_num) hxpos.le]; ring
  have hstep : (∑ i, ∑ _k : Fin K', ∑ j : Fin (JJN x N + 1),
        (((MnOf x N j : ℝ) * a i) ^ ((3 : ℝ) / 4)))
      = (K' : ℝ) * (∑ i, ∑ j : Fin (JJN x N + 1), (((MnOf x N j : ℝ) * a i) ^ ((3 : ℝ) / 4))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  have hK0 : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
  have hK'0 : (0 : ℝ) ≤ (K' : ℝ) := Nat.cast_nonneg K'
  have h4θ : (4 : ℝ) / θ + 4 ≤ 8 / θ := by
    have hkey : (8 : ℝ) / θ - (4 / θ + 4) = 4 * (1 - θ) / θ := by field_simp; ring
    have hnn : 0 ≤ 4 * (1 - θ) / θ := div_nonneg (by linarith) (le_of_lt hθ0)
    linarith
  have hKK' : (K : ℝ) * (K' : ℝ) ≤ 64 * θ ^ (-(2 : ℝ)) := by
    have hK8 : (K : ℝ) ≤ 8 / θ := le_trans hK h4θ
    have hK'8 : (K' : ℝ) ≤ 8 / θ := le_trans hK' h4θ
    have hmul : (K : ℝ) * (K' : ℝ) ≤ (8 / θ) * (8 / θ) :=
      mul_le_mul hK8 hK'8 hK'0 (by positivity)
    have heq : (8 / θ) * (8 / θ) = 64 * θ ^ (-(2 : ℝ)) := by
      rw [show (-(2 : ℝ)) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg hθ0.le, Real.rpow_natCast]
      field_simp
      norm_num
    rwa [heq] at hmul
  have hC0 : 0 ≤ (4 : ℝ) ^ ((3 : ℝ) / 4) / (r - 1) := by
    apply div_nonneg (Real.rpow_nonneg (by norm_num) _) hrm1.le
  have hx34 : 0 ≤ (x : ℝ) ^ ((3 : ℝ) / 4) := Real.rpow_nonneg hxpos.le _
  have hsum_i : (∑ i, ∑ j : Fin (JJN x N + 1), (((MnOf x N j : ℝ) * a i) ^ ((3 : ℝ) / 4)))
      ≤ (K : ℝ) * (((4 : ℝ) ^ ((3 : ℝ) / 4) / (r - 1)) * (x : ℝ) ^ ((3 : ℝ) / 4)) := by
    calc (∑ i, ∑ j : Fin (JJN x N + 1), (((MnOf x N j : ℝ) * a i) ^ ((3 : ℝ) / 4)))
        ≤ ∑ _i : Fin K, ((4 : ℝ) ^ ((3 : ℝ) / 4) / (r - 1)) * (x : ℝ) ^ ((3 : ℝ) / 4) :=
          Finset.sum_le_sum (fun i _ => hper i)
      _ = (K : ℝ) * (((4 : ℝ) ^ ((3 : ℝ) / 4) / (r - 1)) * (x : ℝ) ^ ((3 : ℝ) / 4)) := by
          rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  calc (∑ i, ∑ _k : Fin K', ∑ j : Fin (JJN x N + 1), (((MnOf x N j : ℝ) * a i) ^ ((3 : ℝ) / 4)))
      = (K' : ℝ) * (∑ i, ∑ j : Fin (JJN x N + 1), (((MnOf x N j : ℝ) * a i) ^ ((3 : ℝ) / 4))) := hstep
    _ ≤ (K' : ℝ) * ((K : ℝ) * (((4 : ℝ) ^ ((3 : ℝ) / 4) / (r - 1)) * (x : ℝ) ^ ((3 : ℝ) / 4))) :=
        mul_le_mul_of_nonneg_left hsum_i hK'0
    _ = ((K : ℝ) * (K' : ℝ)) * (((4 : ℝ) ^ ((3 : ℝ) / 4) / (r - 1)) * (x : ℝ) ^ ((3 : ℝ) / 4)) := by
        ring
    _ ≤ (64 * θ ^ (-(2 : ℝ))) * (((4 : ℝ) ^ ((3 : ℝ) / 4) / (r - 1)) * (x : ℝ) ^ ((3 : ℝ) / 4)) :=
        mul_le_mul_of_nonneg_right hKK' (mul_nonneg hC0 hx34)
    _ = 64 * ((4 : ℝ) ^ ((3 : ℝ) / 4) / ((2 : ℝ) ^ ((3 : ℝ) / 4) - 1)) * θ ^ (-(2 : ℝ))
          * (x : ℝ) ^ ((3 : ℝ) / 4) := by rw [hrdef]; ring

/-! ## 4. The T2 split -/

lemma window_T2_split
    (x N Mn : ℕ) (τ : ℝ) (K K' : ℕ)
    (a : Fin K → ℝ) (p : Fin K → ℝ → ℝ) (φ : Fin K' → ℝ) (q : Fin K' → ℝ → ℝ)
    (Pa : Fin K → Fin K' → Work.FITop.Params) (hPaτ : ∀ i k, (Pa i k).τ = τ) :
    (∑ i, ∑ k, ∑ mm ∈ (Finset.Icc (Mn + 1) (2 * Mn)).filter
        (fun m : ℕ => (m : ℝ) * a i < (x : ℝ)),
      ∑ w ∈ wSph mm, ∑ z ∈ primAnn (2 * N),
        2 * badInd mm x τ (Work.FIPlan.gnorm z)
          * ‖pieceCoeff (Pa i k) (φ k) (q k) (p i) z * Work.FITop3.Zc w z‖)
      ≤ (∑ i, ∑ k, ∑ mm ∈ (Finset.Icc (Mn + 1) (2 * Mn)).filter
            (fun m : ℕ => (m : ℝ) * a i < (x : ℝ)),
          ∑ w ∈ wSph mm, ∑ z ∈ primAnn (2 * N),
            2 * (if Nat.Coprime mm (Work.FIPlan.gnorm z) then (0 : ℝ) else 1)
              * ‖pieceCoeff (Pa i k) (φ k) (q k) (p i) z * Work.FITop3.Zc w z‖)
        + (∑ i, ∑ k, ∑ mm ∈ (Finset.Icc (Mn + 1) (2 * Mn)).filter
            (fun m : ℕ => (m : ℝ) * a i < (x : ℝ)),
          ∑ w ∈ wSph mm, ∑ z ∈ primAnn (2 * N),
            2 * (if (mm : ℝ) * (Work.FIPlan.gnorm z : ℝ) > (x : ℝ) then (1 : ℝ) else 0)
              * ‖pieceCoeff (Pa i k) (φ k) (q k) (p i) z * Work.FITop3.Zc w z‖) := by
  have h1 : (∑ i, ∑ k, ∑ mm ∈ (Finset.Icc (Mn + 1) (2 * Mn)).filter
        (fun m : ℕ => (m : ℝ) * a i < (x : ℝ)),
      ∑ w ∈ wSph mm, ∑ z ∈ primAnn (2 * N),
        2 * badInd mm x τ (Work.FIPlan.gnorm z)
          * ‖pieceCoeff (Pa i k) (φ k) (q k) (p i) z * Work.FITop3.Zc w z‖)
      ≤ ∑ i, ∑ k, ∑ mm ∈ (Finset.Icc (Mn + 1) (2 * Mn)).filter
        (fun m : ℕ => (m : ℝ) * a i < (x : ℝ)),
      ∑ w ∈ wSph mm, ∑ z ∈ primAnn (2 * N),
        (2 * (if Nat.Coprime mm (Work.FIPlan.gnorm z) then (0 : ℝ) else 1)
            * ‖pieceCoeff (Pa i k) (φ k) (q k) (p i) z * Work.FITop3.Zc w z‖
          + 2 * (if (mm : ℝ) * (Work.FIPlan.gnorm z : ℝ) > (x : ℝ) then (1 : ℝ) else 0)
            * ‖pieceCoeff (Pa i k) (φ k) (q k) (p i) z * Work.FITop3.Zc w z‖) := by
    apply Finset.sum_le_sum; intro i _
    apply Finset.sum_le_sum; intro k _
    apply Finset.sum_le_sum; intro mm _
    apply Finset.sum_le_sum; intro w _
    apply Finset.sum_le_sum; intro z _
    exact badInd_mul_norm_le x τ mm w z (Pa i k) (hPaτ i k) (φ k) (q k) (p i)
  simpa only [Finset.sum_add_distrib] using h1


/-! ## 5. `Params` constructions with a free `τ` -/

/-- `exists_params5` with the `τ`-identification dropped: the free threshold `τ` only has to
satisfy the two `Params` fields `(log x)^{A+124} ≤ τ ≤ x^{η/3}`. -/
theorem exists_params5_tau (x : ℕ) (η B θ ϑ τ : ℝ) (Pz : ℕ) (C M N' : ℝ)
    (hx : 3 ≤ x) (hη : 0 < η) (hB : 0 < B) (hθ0 : 0 < θ) (hϑ0 : 0 < ϑ)
    (hϑ : ϑ = varthetaOf x Asave) (hθ : θ = thetaOf x Asave)
    (hτ1 : (Real.log (x : ℝ)) ^ (Asave + 124) ≤ τ) (hτ2 : τ ≤ (x : ℝ) ^ (η / 3))
    (hPlo : (Real.log (Real.log (x : ℝ))) ^ 2 ≤ Real.log (Pz : ℝ))
    (hPhi : Real.log (Pz : ℝ) ≤ Real.log (x : ℝ) * (Real.log (Real.log (x : ℝ))) ^ (-2 : ℤ))
    (hP2 : 2 ≤ Pz) (hNlo : (x : ℝ) ^ ((1 : ℝ) / 4 + η) < N')
    (hNhi : N' < (x : ℝ) ^ ((1 : ℝ) / 2) * (Real.log (x : ℝ)) ^ (-B))
    (hN1 : 1 ≤ N') (hM1 : 1 ≤ M) (hMN : ϑ * (x : ℝ) < M * N') (hMNx : M * N' ≤ (x : ℝ))
    (hMge : N' ≤ M) (hC1 : 1 ≤ C) (hC2 : C ≤ N' ^ (1 - η)) :
    ∃ Pa : Work.FITop.Params, Pa.x = x ∧ Pa.η = η ∧ Pa.A = Asave ∧ Pa.A' = Aprime Asave ∧
      Pa.B = B ∧ Pa.θ = θ ∧ Pa.ϑ = ϑ ∧ Pa.τ = τ ∧ Pa.Pz = Pz ∧ Pa.C = C ∧
      Pa.M = M ∧ Pa.N = N' := by
  refine ⟨{ x := x, η := η, A := Asave, A' := Aprime Asave, B := B, θ := θ, ϑ := ϑ, τ := τ,
            Pz := Pz, C := C, M := M, N := N',
            hx := hx, hη := hη, hA := Asave_pos, hA' := ?_, hB := hB, hθ0 := hθ0,
            hϑ0 := hϑ0, hϑ := hϑ, hθ := hθ, hτ1 := hτ1, hτ2 := hτ2, hPlo := hPlo,
            hPhi := hPhi, hP2 := hP2, hNlo := hNlo, hNhi := hNhi, hN1 := hN1, hM1 := hM1,
            hMN := hMN, hMNx := hMNx, hMge := hMge, hC1 := hC1, hC2 := hC2 },
          rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  unfold Aprime
  exact le_refl _

/-- `params_family` with a free threshold `τ` (`Pa.τ = τ` instead of `tauOf x Asave`). -/
theorem params_family_tau (x N Pz : ℕ) (C θ ϑ τ η B : ℝ) (Mn K K' : ℕ)
    (a : Fin K → ℝ)
    (hx : 3 ≤ x) (hN : 1 ≤ N) (hP2 : 2 ≤ Pz)
    (hη0 : 0 < η) (hη1 : η < 3 / 32)
    (hC1 : 1 ≤ C) (hC2 : C ≤ (N : ℝ) ^ (1 - η))
    (hϑ0 : 0 < ϑ) (hB : 0 < B)
    (hτ1 : (Real.log (x : ℝ)) ^ (Asave + 124) ≤ τ) (hτ2 : τ ≤ (x : ℝ) ^ (η / 3))
    (hϑ : ϑ = varthetaOf x Asave) (hθ : θ = thetaOf x Asave)
    (hNlo : (x : ℝ) ^ ((1 : ℝ) / 4 + η) < (N : ℝ))
    (hNhi : 2 * (N : ℝ) < (x : ℝ) ^ ((1 : ℝ) / 2) * (Real.log (x : ℝ)) ^ (-B))
    (hPlo : (Real.log (Real.log (x : ℝ))) ^ 2 ≤ Real.log (Pz : ℝ))
    (hPhi : Real.log (Pz : ℝ) ≤ Real.log (x : ℝ) * (Real.log (Real.log (x : ℝ))) ^ (-2 : ℤ))
    (haN : ∀ i, (N : ℝ) ≤ a i) (ha2 : ∀ i, a i ≤ 2 * (N : ℝ))
    (hMn1 : 1 ≤ Mn) (hMn4 : 4 ≤ Mn)
    (hMNx : (Mn : ℝ) * (2 * (N : ℝ)) ≤ (x : ℝ))
    (hMge : 2 * (N : ℝ) ≤ (Mn : ℝ))
    (hMN : ϑ * (x : ℝ) < (Mn : ℝ) * (N : ℝ)) :
    ∃ (Pa : Fin K → Fin K' → Work.FITop.Params) (f : Fin K → Fin K' → ℤ → ℝ),
      (∀ i k, (Pa i k).M = (Mn : ℝ)) ∧
      (∀ i k, (Pa i k).N = a i) ∧
      (∀ i k, (Pa i k).C = C) ∧
      (∀ i k, (Pa i k).Pz = Pz) ∧
      (∀ i k, (Pa i k).θ = θ) ∧
      (∀ i k, (Pa i k).ϑ = ϑ) ∧
      (∀ i k, (Pa i k).τ = τ) ∧
      (∀ i k, Work.FITop3.IsMajorant (Pa i k) (f i k)) ∧
      (∀ i k, (Pa i k).x = x ∧ (Pa i k).η = η ∧ (Pa i k).A = Asave ∧
          (Pa i k).A' = Aprime Asave ∧ (Pa i k).ϑ = varthetaOf x Asave ∧
          (Pa i k).θ = thetaOf x Asave ∧ (Pa i k).τ = τ ∧
          (Pa i k).Pz = Pz ∧ (Pa i k).C = C) := by
  have hLpos : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < x))
  have hθpos : 0 < θ := by
    rw [hθ]; unfold thetaOf
    exact Real.rpow_pos_of_pos hLpos _
  have hMnpos : (0 : ℝ) < (Mn : ℝ) := by exact_mod_cast (by omega : 0 < Mn)
  have hPa_exists : ∀ i : Fin K, ∃ Pa : Work.FITop.Params,
      Pa.M = (Mn : ℝ) ∧ Pa.N = a i ∧ Pa.C = C ∧ Pa.Pz = Pz ∧ Pa.θ = θ ∧ Pa.ϑ = ϑ ∧
      Pa.τ = τ ∧ Pa.x = x ∧ Pa.η = η ∧ Pa.A = Asave ∧ Pa.A' = Aprime Asave ∧
      Pa.ϑ = varthetaOf x Asave ∧ Pa.θ = thetaOf x Asave ∧ Pa.τ = τ ∧
      Pa.Pz = Pz ∧ Pa.C = C := by
    intro i
    have hai1 : (1 : ℝ) ≤ a i := le_trans (by exact_mod_cast hN) (haN i)
    have hNlo_i : (x : ℝ) ^ ((1 : ℝ) / 4 + η) < a i := lt_of_lt_of_le hNlo (haN i)
    have hNhi_i : a i < (x : ℝ) ^ ((1 : ℝ) / 2) * (Real.log (x : ℝ)) ^ (-B) :=
      lt_of_le_of_lt (ha2 i) hNhi
    have hϑx' : ϑ * (x : ℝ) < (Mn : ℝ) * a i := by
      have hle : (Mn : ℝ) * (N : ℝ) ≤ (Mn : ℝ) * a i :=
        mul_le_mul_of_nonneg_left (haN i) (le_of_lt hMnpos)
      linarith
    have hMNx_i : (Mn : ℝ) * a i ≤ (x : ℝ) :=
      le_trans (mul_le_mul_of_nonneg_left (ha2 i) (le_of_lt hMnpos)) hMNx
    have hMge_i : a i ≤ (Mn : ℝ) := le_trans (ha2 i) hMge
    have hC2_i : C ≤ (a i) ^ (1 - η) := by
      have hle : (N : ℝ) ^ (1 - η) ≤ (a i) ^ (1 - η) :=
        Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ (N : ℝ)) (haN i)
          (by linarith : (0 : ℝ) ≤ 1 - η)
      linarith
    obtain ⟨Pa, hPax, hPaη, hPaA, hPaA', hPaB, hPaθ, hPaϑ, hPaτ, hPaPz, hPaC, hPaM, hPaN⟩ :=
      exists_params5_tau x η B θ ϑ τ Pz C (Mn : ℝ) (a i)
        hx hη0 hB hθpos hϑ0 hϑ hθ hτ1 hτ2 hPlo hPhi hP2 hNlo_i hNhi_i hai1
        (by exact_mod_cast hMn1) hϑx' hMNx_i hMge_i hC1 hC2_i
    exact ⟨Pa, hPaM, hPaN, hPaC, hPaPz, hPaθ, hPaϑ, hPaτ, hPax, hPaη, hPaA, hPaA',
      by rw [hPaϑ, hϑ], by rw [hPaθ, hθ], hPaτ, hPaPz, hPaC⟩
  choose Pa hPa using hPa_exists
  refine ⟨fun i _ => Pa i, fun _ _ => Work.FITop3.majorant (Mn : ℝ),
    (fun i _ => (hPa i).1),
    (fun i _ => (hPa i).2.1),
    (fun i _ => (hPa i).2.2.1),
    (fun i _ => (hPa i).2.2.2.1),
    (fun i _ => (hPa i).2.2.2.2.1),
    (fun i _ => (hPa i).2.2.2.2.2.1),
    (fun i _ => (hPa i).2.2.2.2.2.2.1),
    ?_, ?_⟩
  · intro i k
    have hMeq : (Pa i).M = (Mn : ℝ) := (hPa i).1
    have hM4 : 4 ≤ (Pa i).M := by rw [hMeq]; exact_mod_cast hMn4
    have h := Work.FITop3.Majorant.majorant_props (Pa i) hM4
    rw [hMeq] at h
    exact h
  · intro i k
    obtain ⟨-, -, -, -, -, -, -, hPax, hPaη, hPaA, hPaA', hPaϑ', hPaθ', hPaτ', hPaPz', hPaC'⟩ :=
      hPa i
    exact ⟨hPax, hPaη, hPaA, hPaA', hPaϑ', hPaθ', hPaτ', hPaPz', hPaC'⟩

/-- `window_family` with a free threshold `τ`. -/
theorem window_family_tau (x N Pz : ℕ) (C τ η θ ϑ B : ℝ) (K K' : ℕ) (a : Fin K → ℝ)
    (hx : 3 ≤ x) (hN : 1 ≤ N) (hP2 : 2 ≤ Pz) (hη0 : 0 < η) (hη1 : η < 3 / 32)
    (hC1 : 1 ≤ C) (hC2 : C ≤ (N : ℝ) ^ (1 - η))
    (hϑ0 : 0 < ϑ) (hB : 0 < B)
    (hτ1 : (Real.log (x : ℝ)) ^ (Asave + 124) ≤ τ) (hτ2 : τ ≤ (x : ℝ) ^ (η / 3))
    (hϑ : ϑ = varthetaOf x Asave) (hθ : θ = thetaOf x Asave)
    (hNlo : (x : ℝ) ^ ((1 : ℝ) / 4 + η) < (N : ℝ))
    (hNhi : 2 * (N : ℝ) < (x : ℝ) ^ ((1 : ℝ) / 2) * (Real.log (x : ℝ)) ^ (-B))
    (hPlo : (Real.log (Real.log (x : ℝ))) ^ 2 ≤ Real.log (Pz : ℝ))
    (hPhi : Real.log (Pz : ℝ) ≤ Real.log (x : ℝ) * (Real.log (Real.log (x : ℝ))) ^ (-2 : ℤ))
    (haN : ∀ i, (N : ℝ) ≤ a i) (ha2 : ∀ i, a i ≤ 2 * (N : ℝ))
    (hMn1 : ∀ j : Fin (JJN x N + 1), 1 ≤ MnOf x N j)
    (hMn4 : ∀ j : Fin (JJN x N + 1), 4 ≤ MnOf x N j)
    (hMNx : ∀ j : Fin (JJN x N + 1), (MnOf x N j : ℝ) * (2 * (N : ℝ)) ≤ (x : ℝ))
    (hMge : ∀ j : Fin (JJN x N + 1), 2 * (N : ℝ) ≤ (MnOf x N j : ℝ))
    (hMN : ∀ j : Fin (JJN x N + 1),
      ϑ * (x : ℝ) < (MnOf x N j : ℝ) * (N : ℝ)) :
    ∃ (Pa : Fin K → Fin K' → Fin (JJN x N + 1) → Work.FITop.Params)
      (f : Fin K → Fin K' → Fin (JJN x N + 1) → ℤ → ℝ),
      (∀ i k j, (Pa i k j).M = (MnOf x N j : ℝ)) ∧
      (∀ i k j, (Pa i k j).N = a i) ∧
      (∀ i k j, (Pa i k j).C = C) ∧
      (∀ i k j, (Pa i k j).Pz = Pz) ∧
      (∀ i k j, (Pa i k j).θ = θ) ∧
      (∀ i k j, (Pa i k j).ϑ = ϑ) ∧
      (∀ i k j, (Pa i k j).τ = τ) ∧
      (∀ i k j, Work.FITop3.IsMajorant (Pa i k j) (f i k j)) ∧
      (∀ i k j, (Pa i k j).x = x ∧ (Pa i k j).η = η ∧ (Pa i k j).A = Asave ∧
          (Pa i k j).A' = Aprime Asave ∧
          (Pa i k j).ϑ = varthetaOf x Asave ∧
          (Pa i k j).θ = thetaOf x Asave ∧
          (Pa i k j).τ = τ ∧
          (Pa i k j).Pz = Pz ∧ (Pa i k j).C = C) := by
  have hper : ∀ j : Fin (JJN x N + 1),
      ∃ (Pa : Fin K → Fin K' → Work.FITop.Params) (f : Fin K → Fin K' → ℤ → ℝ),
        (∀ i k, (Pa i k).M = (MnOf x N j : ℝ)) ∧
        (∀ i k, (Pa i k).N = a i) ∧
        (∀ i k, (Pa i k).C = C) ∧
        (∀ i k, (Pa i k).Pz = Pz) ∧
        (∀ i k, (Pa i k).θ = θ) ∧
        (∀ i k, (Pa i k).ϑ = ϑ) ∧
        (∀ i k, (Pa i k).τ = τ) ∧
        (∀ i k, Work.FITop3.IsMajorant (Pa i k) (f i k)) ∧
        (∀ i k, (Pa i k).x = x ∧ (Pa i k).η = η ∧ (Pa i k).A = Asave ∧
            (Pa i k).A' = Aprime Asave ∧
            (Pa i k).ϑ = varthetaOf x Asave ∧
            (Pa i k).θ = thetaOf x Asave ∧
            (Pa i k).τ = τ ∧
            (Pa i k).Pz = Pz ∧ (Pa i k).C = C) := by
    intro j
    exact params_family_tau x N Pz C θ ϑ τ η B (MnOf x N j) K K' a
      hx hN hP2 hη0 hη1 hC1 hC2 hϑ0 hB hτ1 hτ2 hϑ hθ hNlo hNhi hPlo hPhi haN ha2
      (hMn1 j) (hMn4 j) (hMNx j) (hMge j) (hMN j)
  choose Pa f hPaf using hper
  refine ⟨fun i k j => Pa j i k, fun i k j => f j i k,
    (fun i k j => (hPaf j).1 i k),
    (fun i k j => (hPaf j).2.1 i k),
    (fun i k j => (hPaf j).2.2.1 i k),
    (fun i k j => (hPaf j).2.2.2.1 i k),
    (fun i k j => (hPaf j).2.2.2.2.1 i k),
    (fun i k j => (hPaf j).2.2.2.2.2.1 i k),
    (fun i k j => (hPaf j).2.2.2.2.2.2.1 i k),
    (fun i k j => (hPaf j).2.2.2.2.2.2.2.1 i k),
    (fun i k j => (hPaf j).2.2.2.2.2.2.2.2 i k)⟩

/-- `window_MnFacts` from the `η`-independent record `Red5NumC`. -/
theorem window_MnFactsC {x N Pz : ℕ} {η : ℝ} (h : Red5NumC x N Pz η)
    (j : Fin (JJN x N + 1)) :
    (1 ≤ MnOf x N j) ∧ (4 ≤ MnOf x N j) ∧
    (2 * (N : ℝ) ≤ (MnOf x N j : ℝ)) ∧
    ((N : ℝ) ≤ (MnOf x N j : ℝ)) ∧
    ((MnOf x N j : ℝ) * (2 * (N : ℝ)) ≤ (x : ℝ)) ∧
    (varthetaOf x Asave * (x : ℝ) < (MnOf x N j : ℝ) * (N : ℝ)) := by
  have hjle : (j : ℕ) ≤ JJN x N := by have := j.isLt; omega
  have hM0ge2N : 2 * N ≤ M0N x N := by exact_mod_cast h.hM0ge2N
  have htopNat : MtopN x N * (2 * N) ≤ x := by exact_mod_cast h.htop
  rcases lt_or_eq_of_le hjle with hjlt | hjeq
  · have hMn : MnOf x N (j : ℕ) = 2 ^ (j : ℕ) * M0N x N := MnOf_of_lt hjlt
    have hone : 1 ≤ 2 ^ (j : ℕ) := Nat.one_le_two_pow
    have hM0le : M0N x N ≤ MnOf x N (j : ℕ) := by
      rw [hMn]
      calc M0N x N = 1 * M0N x N := (one_mul _).symm
        _ ≤ 2 ^ (j : ℕ) * M0N x N := Nat.mul_le_mul_right _ hone
    have h2Nle : 2 * N ≤ MnOf x N (j : ℕ) := le_trans hM0ge2N hM0le
    have hNle : N ≤ MnOf x N (j : ℕ) := le_trans (by omega : N ≤ 2 * N) h2Nle
    have hJJN1 : 1 ≤ JJN x N := by omega
    have hpowle : 2 ^ (j : ℕ) ≤ 2 ^ (JJN x N - 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hleMtop : MnOf x N (j : ℕ) ≤ MtopN x N := by
      rw [hMn]
      exact le_trans (Nat.mul_le_mul_right _ hpowle) (two_pow_pred_JJN_mul_le_MtopN hJJN1)
    have hleMtopR : (MnOf x N (j : ℕ) : ℝ) ≤ (MtopN x N : ℝ) := by exact_mod_cast hleMtop
    refine ⟨le_trans (by norm_num) (le_trans h.hM0ge4 hM0le),
            le_trans h.hM0ge4 hM0le, ?_, ?_, ?_, ?_⟩
    · exact_mod_cast h2Nle
    · exact_mod_cast hNle
    · calc (MnOf x N (j : ℕ) : ℝ) * (2 * (N : ℝ))
          = ((MnOf x N (j : ℕ) * (2 * N) : ℕ) : ℝ) := by push_cast; ring
        _ ≤ ((MtopN x N * (2 * N) : ℕ) : ℝ) := by
              exact_mod_cast Nat.mul_le_mul_right _ hleMtop
        _ ≤ (x : ℝ) := by exact_mod_cast htopNat
    · have hleR : (M0N x N : ℝ) ≤ (MnOf x N (j : ℕ) : ℝ) := by exact_mod_cast hM0le
      calc varthetaOf x Asave * (x : ℝ) < (M0N x N : ℝ) * (N : ℝ) := h.hM0hing
        _ ≤ (MnOf x N (j : ℕ) : ℝ) * (N : ℝ) :=
              mul_le_mul_of_nonneg_right hleR (Nat.cast_nonneg N)
  · have hjnotlt : ¬ (j : ℕ) < JJN x N := by omega
    have hMn : MnOf x N (j : ℕ) = MtopN x N := MnOf_of_not_lt hjnotlt
    have hM0le : M0N x N ≤ MtopN x N := h.hM0leMtop
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hMn]; exact h.hMtop1
    · rw [hMn]; exact le_trans h.hM0ge4 hM0le
    · rw [hMn]; exact h.hMtopge2N
    · rw [hMn]
      have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
      linarith [h.hMtopge2N]
    · rw [hMn]; exact h.htop
    · rw [hMn]; exact h.hMtoping



/-! ## 5b. The extra hypothesis `2N ≤ θ² M_j` of the shell estimate -/

lemma theta_sq (x : ℕ) :
    (thetaOf x Asave) ^ (2 : ℕ) = (Real.log (x : ℝ)) ^ (-(2 * Aprime Asave)) := by
  unfold thetaOf
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  congr 1
  push_cast
  ring

lemma two_N_le_theta_sq_MnOf {x N Pz : ℕ} {η : ℝ} (h : Red5NumC x N Pz η)
    (hN : 1 ≤ N)
    (hNhi : (N : ℝ) < (x : ℝ) ^ ((1 : ℝ) / 2)
        * (Real.log (x : ℝ)) ^ (-(Work.FITop4.BmaxBig η)))
    (j : Fin (JJN x N + 1)) :
    2 * (N : ℝ) ≤ (thetaOf x Asave) ^ (2 : ℕ) * (MnOf x N j : ℝ) := by
  have hx4 : 4 ≤ x := h.hx4
  have hlog1 : 1 ≤ Real.log (x : ℝ) := h.hlog1
  have hlogpos : 0 < Real.log (x : ℝ) := by linarith
  have hlog2 : 2 ≤ Real.log (x : ℝ) := by have := h.hlog4; linarith
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hxpos : (0 : ℝ) < (x : ℝ) := by
    exact lt_of_lt_of_le (by norm_num : (0:ℝ) < 4) (by exact_mod_cast hx4)
  have hB31 : (2 : ℝ) ^ (31 : ℕ) ≤ BmaxBig η := BmaxBig_ge_pow31 η
  have hA2 : Asave + 2 * Aprime Asave + 1 ≤ 2 * BmaxBig η := by
    have h1 : Asave + 2 * Aprime Asave + 1 ≤ (2 : ℝ) ^ (32 : ℕ) := by
      unfold Asave Aprime; norm_num
    have h2 : (2 : ℝ) ^ (32 : ℕ) = 2 * (2 : ℝ) ^ (31 : ℕ) := by ring
    linarith [h1, h2.le, hB31]
  -- `N² < x (log x)^{-2B}`
  have hNsq : (N : ℝ) ^ 2 < (x : ℝ) * (Real.log (x : ℝ)) ^ (-(2 * BmaxBig η)) := by
    have hRpos : 0 < (x : ℝ) ^ ((1 : ℝ) / 2) * (Real.log (x : ℝ)) ^ (-(BmaxBig η)) := by
      positivity
    have h1 : (N : ℝ) * (N : ℝ)
        < ((x : ℝ) ^ ((1 : ℝ) / 2) * (Real.log (x : ℝ)) ^ (-(BmaxBig η)))
          * ((x : ℝ) ^ ((1 : ℝ) / 2) * (Real.log (x : ℝ)) ^ (-(BmaxBig η))) := by
      exact lt_trans (mul_lt_mul_of_pos_right hNhi hNpos)
        (mul_lt_mul_of_pos_left hNhi hRpos)
    have hL : ((Real.log (x : ℝ)) ^ (-(BmaxBig η))) ^ 2
        = (Real.log (x : ℝ)) ^ (-(2 * BmaxBig η)) := by
      rw [pow_two, ← Real.rpow_add hlogpos]
      congr 1
      ring
    have hX : (x : ℝ) ^ ((1 : ℝ) / 2) * (x : ℝ) ^ ((1 : ℝ) / 2) = (x : ℝ) := by
      rw [← Real.rpow_add hxpos]
      norm_num
    have h2 : ((x : ℝ) ^ ((1 : ℝ) / 2) * (Real.log (x : ℝ)) ^ (-(BmaxBig η)))
          * ((x : ℝ) ^ ((1 : ℝ) / 2) * (Real.log (x : ℝ)) ^ (-(BmaxBig η)))
        = (x : ℝ) * (Real.log (x : ℝ)) ^ (-(2 * BmaxBig η)) := by
      calc ((x : ℝ) ^ ((1 : ℝ) / 2) * (Real.log (x : ℝ)) ^ (-(BmaxBig η)))
            * ((x : ℝ) ^ ((1 : ℝ) / 2) * (Real.log (x : ℝ)) ^ (-(BmaxBig η)))
          = ((x : ℝ) ^ ((1 : ℝ) / 2) * (x : ℝ) ^ ((1 : ℝ) / 2))
            * ((Real.log (x : ℝ)) ^ (-(BmaxBig η))) ^ 2 := by ring
        _ = (x : ℝ) * (Real.log (x : ℝ)) ^ (-(2 * BmaxBig η)) := by rw [hX, hL]
    rw [pow_two]
    exact lt_of_lt_of_eq h1 h2
  -- `x ≥ 2 N² (log x)^{A+2A'}`
  have hkey : 2 * (N : ℝ) ^ 2 * (Real.log (x : ℝ)) ^ (Asave + 2 * Aprime Asave) ≤ (x : ℝ) := by
    have h1 : 2 * (N : ℝ) ^ 2 * (Real.log (x : ℝ)) ^ (Asave + 2 * Aprime Asave)
        < 2 * ((x : ℝ) * (Real.log (x : ℝ)) ^ (-(2 * BmaxBig η)))
            * (Real.log (x : ℝ)) ^ (Asave + 2 * Aprime Asave) := by
      apply mul_lt_mul_of_pos_right _ (Real.rpow_pos_of_pos hlogpos _)
      linarith [hNsq]
    have hL : (Real.log (x : ℝ)) ^ (-(2 * BmaxBig η))
          * (Real.log (x : ℝ)) ^ (Asave + 2 * Aprime Asave)
        = (Real.log (x : ℝ)) ^ (Asave + 2 * Aprime Asave + -(2 * BmaxBig η)) := by
      rw [← Real.rpow_add hlogpos]
      congr 1
      ring
    have h2 : 2 * ((x : ℝ) * (Real.log (x : ℝ)) ^ (-(2 * BmaxBig η)))
          * (Real.log (x : ℝ)) ^ (Asave + 2 * Aprime Asave)
        = 2 * (x : ℝ) * (Real.log (x : ℝ)) ^ (Asave + 2 * Aprime Asave + -(2 * BmaxBig η)) := by
      calc 2 * ((x : ℝ) * (Real.log (x : ℝ)) ^ (-(2 * BmaxBig η)))
            * (Real.log (x : ℝ)) ^ (Asave + 2 * Aprime Asave)
          = 2 * (x : ℝ) * ((Real.log (x : ℝ)) ^ (-(2 * BmaxBig η))
              * (Real.log (x : ℝ)) ^ (Asave + 2 * Aprime Asave)) := by ring
        _ = 2 * (x : ℝ) * (Real.log (x : ℝ)) ^ (Asave + 2 * Aprime Asave + -(2 * BmaxBig η)) := by
              rw [hL]
    have h3 : Asave + 2 * Aprime Asave + -(2 * BmaxBig η) ≤ (-1 : ℝ) := by linarith [hA2]
    have h4a : (Real.log (x : ℝ)) ^ (Asave + 2 * Aprime Asave + -(2 * BmaxBig η))
        ≤ (Real.log (x : ℝ)) ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hlog1 h3
    have h4b : (Real.log (x : ℝ)) ^ (-1 : ℝ) ≤ 1 / 2 := by
      rw [Real.rpow_neg_one, inv_le_iff_one_le_mul₀ hlogpos]
      linarith [hlog2]
    have h4 : (Real.log (x : ℝ)) ^ (Asave + 2 * Aprime Asave + -(2 * BmaxBig η)) ≤ 1 / 2 :=
      le_trans h4a h4b
    have h5 : 2 * (x : ℝ) * (Real.log (x : ℝ)) ^ (Asave + 2 * Aprime Asave + -(2 * BmaxBig η))
        ≤ (x : ℝ) := by nlinarith [h4, hxpos]
    linarith [h1, h2.le, h5]
  -- `M0N ≥ ϑ x / N`
  have hM0ge : (varthetaOf x Asave * (x : ℝ)) / (N : ℝ) ≤ (M0N x N : ℝ) := by
    have h1 : varthetaOf x Asave * (x : ℝ) / (N : ℝ) < ((YsN x N : ℕ) : ℝ) + 1 :=
      Nat.lt_floor_add_one _
    have hM0 : ((M0N x N : ℕ) : ℝ) = ((YsN x N : ℕ) : ℝ) + 2 := by
      unfold M0N; push_cast; ring
    rw [hM0]; linarith
  have hMn : (M0N x N : ℝ) ≤ (MnOf x N j : ℝ) := by
    have h1 : M0N x N ≤ MnOf x N j := by
      by_cases hj : (j : ℕ) < JJN x N
      · rw [MnOf_of_lt hj]
        calc M0N x N = 1 * M0N x N := (one_mul _).symm
          _ ≤ 2 ^ (j : ℕ) * M0N x N := Nat.mul_le_mul_right _ Nat.one_le_two_pow
      · rw [MnOf_of_not_lt hj]; exact h.hM0leMtop
    exact_mod_cast h1
  have hθ2 : (thetaOf x Asave) ^ (2 : ℕ) = (Real.log (x : ℝ)) ^ (-(2 * Aprime Asave)) :=
    theta_sq x
  have hϑ : varthetaOf x Asave = (Real.log (x : ℝ)) ^ (-Asave) := rfl
  have hpow : (Real.log (x : ℝ)) ^ (-(2 * Aprime Asave)) * (Real.log (x : ℝ)) ^ (-Asave)
      = (Real.log (x : ℝ)) ^ (-(Asave + 2 * Aprime Asave)) := by
    rw [← Real.rpow_add hlogpos]
    congr 1
    ring
  have hfin : 2 * (N : ℝ) ≤ (thetaOf x Asave) ^ (2 : ℕ) * (M0N x N : ℝ) := by
    rw [hθ2]
    have hLs : 0 < (Real.log (x : ℝ)) ^ (Asave + 2 * Aprime Asave) := Real.rpow_pos_of_pos hlogpos _
    have hxL : 2 * (N : ℝ) ^ 2
        ≤ (x : ℝ) * (Real.log (x : ℝ)) ^ (-(Asave + 2 * Aprime Asave)) := by
      rw [Real.rpow_neg hlogpos.le, ← div_eq_mul_inv]
      exact (le_div_iff₀ hLs).mpr (by linarith [hkey])
    have hxdiv : (Real.log (x : ℝ)) ^ (-(2 * Aprime Asave)) * (varthetaOf x Asave * (x : ℝ))
        = (x : ℝ) * (Real.log (x : ℝ)) ^ (-(Asave + 2 * Aprime Asave)) := by
      rw [hϑ, ← hpow]; ring
    have hkey2 : 2 * (N : ℝ)
        ≤ (Real.log (x : ℝ)) ^ (-(2 * Aprime Asave))
            * ((varthetaOf x Asave * (x : ℝ)) / (N : ℝ)) := by
      rw [show (Real.log (x : ℝ)) ^ (-(2 * Aprime Asave))
              * ((varthetaOf x Asave * (x : ℝ)) / (N : ℝ))
            = ((Real.log (x : ℝ)) ^ (-(2 * Aprime Asave)) * (varthetaOf x Asave * (x : ℝ)))
              / (N : ℝ) by ring]
      rw [hxdiv, le_div_iff₀ hNpos]
      have h2 : 2 * (N : ℝ) * (N : ℝ) = 2 * (N : ℝ) ^ 2 := by ring
      rw [h2]
      linarith [hxL]
    have hstep : (Real.log (x : ℝ)) ^ (-(2 * Aprime Asave))
          * ((varthetaOf x Asave * (x : ℝ)) / (N : ℝ))
        ≤ (Real.log (x : ℝ)) ^ (-(2 * Aprime Asave)) * (M0N x N : ℝ) :=
      mul_le_mul_of_nonneg_left hM0ge (by positivity)
    linarith [hstep, hkey2]
  exact le_trans hfin (mul_le_mul_of_nonneg_left hMn (by positivity))

/-! ## 6. The assembled reduction -/


theorem reduction_save_core :
    ∃ c : ℝ, 0 < c ∧ ∃ x₀ : ℕ, ∀ (x N Pz : ℕ) (C τ η : ℝ),
      x₀ ≤ x → 1 ≤ N → 1 ≤ C → 2 ≤ Pz → 0 < η → η < 3 / 32 →
      (1 : ℝ) ≤ Real.log (Real.log (x : ℝ)) →
      (x : ℝ) ^ ((1 : ℝ) / 4 + η) < (N : ℝ) →
      (N : ℝ) < (x : ℝ) ^ ((1 : ℝ) / 2) * (Real.log (x : ℝ)) ^ (-(Work.FITop4.BmaxBig η)) →
      2 * (N : ℝ) < (x : ℝ) ^ ((1 : ℝ) / 2) * (Real.log (x : ℝ)) ^ (-(Work.FITop4.BmaxBig η - 1)) →
      C ≤ (N : ℝ) ^ (1 - η) →
      (Real.log (Real.log (x : ℝ))) ^ 2 ≤ Real.log (Pz : ℝ) →
      Real.log (Pz : ℝ) ≤ Real.log (x : ℝ) * (Real.log (Real.log (x : ℝ))) ^ (-2 : ℤ) →
      (Real.log (x : ℝ)) ^ (Work.FITop4.Asave + 124) ≤ τ →
      τ ≤ (x : ℝ) ^ (η / 3) →
      1 ≤ (Work.FITop4.varthetaOf x Work.FITop4.Asave) * (x : ℝ) →
      ∃ (ι : Type) (_ : Fintype ι) (Pa : ι → Work.FITop.Params) (f : ι → ℤ → ℝ)
        (φ : ι → ℝ) (β : ι → GaussianInt → ℂ),
        (∀ i, (Pa i).x = x ∧ (Pa i).η = η ∧ (Pa i).A = Work.FITop4.Asave ∧
              (Pa i).A' = Work.FITop4.Aprime Work.FITop4.Asave ∧
              (Pa i).ϑ = Work.FITop4.varthetaOf x Work.FITop4.Asave ∧
              (Pa i).θ = Work.FITop4.thetaOf x Work.FITop4.Asave ∧
              (Pa i).τ = Work.FITop4.tauOf x Work.FITop4.Asave ∧ (Pa i).Pz = Pz ∧ (Pa i).C = C ∧
              (N : ℝ) ≤ (Pa i).N ∧ (Pa i).N ≤ 2 * (N : ℝ)) ∧
        (∀ i, Work.FITop4.IsMajorant (Pa i) (f i)) ∧
        (∀ i, Work.FITop4.IsBetaCoeff (Pa i) (φ i) (β i)) ∧
        (∑ i, ((((Pa i).M * (Pa i).N) ^ ((3 : ℝ) / 4)))) ≤
            c * (Work.FITop4.thetaOf x Work.FITop4.Asave) ^ (-(2 : ℝ)) * (x : ℝ) ^ ((3 : ℝ) / 4) ∧
        Work.FITop4.BformPiTau x N Pz C τ ≤
            (∑ i, Real.sqrt (100 * (Pa i).M * Work.FITop3.Dform (Pa i) (f i) (β i)))
          + c * ((Work.FITop4.thetaOf x Work.FITop4.Asave) * (x : ℝ) ^ ((3 : ℝ) / 4)
                * (Real.log (x : ℝ)) ^ (100 : ℕ)
              + (Work.FITop4.varthetaOf x Work.FITop4.Asave) ^ ((3 : ℝ) / 4) * (x : ℝ) ^ ((3 : ℝ) / 4)
                * (Real.log (x : ℝ)) ^ (65536 : ℕ)) := by
  obtain ⟨x₀C, hRed5C⟩ := red5numC_proof
  obtain ⟨cCop, hcCop, hCop⟩ := window_T2_cop_le
  obtain ⟨cCrux, hcCrux, hCrux⟩ := thin_annulus_Zint_count_own
  obtain ⟨cShell, hcShell, hShell⟩ := window_T2_shell_of_crux cCrux hcCrux hCrux
  obtain ⟨cSmall, hcSmall, x₀Small, hSmall⟩ := BformPiTauSmall_le2
  obtain ⟨cT3, hcT3, hT3le⟩ := window_T3_le
  obtain ⟨cTauR, hcTauR, x₀TauR, hTauReduce⟩ := BformPiTau_tauReduce
  obtain ⟨cAc, hcAc, hAc⟩ := Work.FIChain.AcountAtilC_le_const_mul_rpow
  obtain ⟨cErr, hcErr, hErr⟩ := window_error_sum
  have hCnt_pos : 0 < 64 * ((4 : ℝ) ^ ((3 : ℝ) / 4) / ((2 : ℝ) ^ ((3 : ℝ) / 4) - 1)) := by
    apply mul_pos (by norm_num)
    apply div_pos (Real.rpow_pos_of_pos (by norm_num) _)
    have h : (1 : ℝ) < (2 : ℝ) ^ ((3 : ℝ) / 4) := Real.one_lt_rpow (by norm_num) (by norm_num)
    linarith
  refine ⟨cTauR * cAc + cCop + cShell + cT3 + cSmall + cErr * (cCop + cShell + cT3)
      + 64 * ((4 : ℝ) ^ ((3 : ℝ) / 4) / ((2 : ℝ) ^ ((3 : ℝ) / 4) - 1)) + 1,
    by positivity, x₀C + x₀Small + x₀TauR + 64, ?_⟩
  intro x N Pz C τ η hx0 hN hC hP2 hη0 hη1 hll hNlo hNhi hNhi2 hC2 hPlo hPhi hτ1 hτ2 hϑx1
  have hx0C : x₀C ≤ x := le_trans (by omega) hx0
  have hx0S : x₀Small ≤ x := le_trans (by omega) hx0
  have hx0R : x₀TauR ≤ x := le_trans (by omega) hx0
  have hx64 : 64 ≤ x := le_trans (by omega) hx0
  have hx1 : 1 ≤ x := by omega
  have hx3 : 3 ≤ x := by omega
  have hx4 : 4 ≤ x := by omega
  have hNum : Red5NumC x N Pz η := hRed5C x N Pz η hx0C hN hP2 hη0 hη1 hll hNlo hNhi hPlo
  have hlog1 : (1 : ℝ) ≤ Real.log (x : ℝ) := hNum.hlog1
  have hlogpos : 0 < Real.log (x : ℝ) := by linarith
  have hϑ0 : 0 < varthetaOf x Asave := hNum.hv0
  have hθ0 : 0 < thetaOf x Asave := hNum.ht0
  have hθ14 : thetaOf x Asave ≤ 1 / 4 := hNum.ht14
  have hθ1 : thetaOf x Asave ≤ 1 := le_trans hθ14 (by norm_num)
  have hBpos : 0 < BmaxBig η - 1 := by
    have h := BmaxBig_ge_pow31 η
    have h2 : (1 : ℝ) < (2 : ℝ) ^ (31 : ℕ) := by norm_num
    linarith
  -- `tauOf x Asave ≤ x^{η/3}`, so that `Params` with `.τ = tauOf x Asave` exists
  have hTauOf : tauOf x Asave ≤ (x : ℝ) ^ (η / 3) :=
    tauOf_le_of_Nrange x (N : ℝ) η hlog1 (by exact_mod_cast hN) hNlo hNhi hη0 hη1
  have hTauOf1 : (Real.log (x : ℝ)) ^ (Asave + 124) ≤ tauOf x Asave := by
    unfold tauOf
    apply Real.rpow_le_rpow_of_exponent_le hlog1
    norm_num [Asave]
  obtain ⟨K, K', a, p, φ, q, haN2, hpcd, hqcd, hp0, hp1, hpsup, hple2N, hpsum_le, hpsum_eq,
    hpder, hq0, hq1, hq0z, hqsup, hang, hqder, hKle, hK'le⟩ :=
    mollifier_family N (thetaOf x Asave) hN hθ0 hθ14
  have haN : ∀ i, (N : ℝ) ≤ a i := fun i => (haN2 i).1
  have ha2 : ∀ i, a i ≤ 2 * (N : ℝ) := fun i => (haN2 i).2
  obtain ⟨Pa, f, hPaM, hPaN, hPaC, hPaPz, hPaθ, hPaϑ, hPaτ, hMaj, hPaFields⟩ :=
    window_family_tau x N Pz C (tauOf x Asave) η (thetaOf x Asave) (varthetaOf x Asave)
      (BmaxBig η - 1) K K' a hx3 hN hP2 hη0 hη1 hC hC2 hϑ0 hBpos hTauOf1 hTauOf rfl rfl
      hNlo hNhi2 hPlo hPhi haN ha2
      (fun j => (window_MnFactsC hNum j).1) (fun j => (window_MnFactsC hNum j).2.1)
      (fun j => (window_MnFactsC hNum j).2.2.2.2.1) (fun j => (window_MnFactsC hNum j).2.2.1)
      (fun j => (window_MnFactsC hNum j).2.2.2.2.2)
  -- local abbreviations for the window arithmetic
  set L100 : ℝ := (Real.log (x : ℝ)) ^ (100 : ℕ) with hL100def
  set L65536 : ℝ := (Real.log (x : ℝ)) ^ (65536 : ℕ) with hL65536def
  have hL100pos : 0 < L100 := by rw [hL100def]; exact pow_pos hlogpos 100
  have hL100nn : 0 ≤ L100 := le_of_lt hL100pos
  have hL65536nn : 0 ≤ L65536 := by
    rw [hL65536def]; exact pow_nonneg (le_of_lt hlogpos) 65536
  set F : Fin K → Fin K' → Fin (JJN x N + 1) → ℝ :=
    fun i k j => Real.sqrt (100 * (Pa i k j).M
      * Work.FITop3.Dform (Pa i k j) (f i k j) (pieceCoeff (Pa i k j) (φ k) (q k) (p i)))
    with hFdef
  have hK'ne : K' ≠ 0 := by
    intro h0
    have h := hang 0 (by linarith [Real.pi_pos]) (le_of_lt Real.pi_pos)
    have hempty : (Finset.univ : Finset (Fin K')) = ∅ := by
      apply Finset.card_eq_zero.mp
      rw [Finset.card_univ, Fintype.card_fin]
      exact h0
    rw [hempty, Finset.sum_empty] at h
    norm_num at h
  have hK'pos : 0 < K' := Nat.pos_of_ne_zero hK'ne
  -- the small-`m` piece
  have hsmallSum := hSmall x N (M0N x N) Pz 3 C (tauOf x Asave) (varthetaOf x Asave)
    hx0S hN (by norm_num) (by norm_num) hϑ0 hNum.hv8 hϑx1 hNum.hM0le3
  -- each window
  have hwin : ∀ j : Fin (JJN x N + 1),
      (∑ m ∈ Finset.Icc (MnOf x N j + 1) (2 * MnOf x N j), Iterm x N Pz C (tauOf x Asave) m)
        ≤ (∑ i, ∑ k, F i k j)
          + ((max cCop cShell) * T2RHS x N (MnOf x N j) Pz (thetaOf x Asave)
              + cT3 * T3RHS x N (MnOf x N j) (thetaOf x Asave)) := by
    intro j
    have hMf := window_MnFactsC hNum j
    have hMn1 : 1 ≤ MnOf x N j := hMf.1
    have hMnN : (N : ℝ) ≤ (MnOf x N j : ℝ) := hMf.2.2.2.1
    -- the T2 hypothesis
    have hT2 : (∑ i, ∑ k, ∑ mm ∈ (Finset.Icc (MnOf x N j + 1) (2 * MnOf x N j)).filter
            (fun m : ℕ => (m : ℝ) * a i < (x : ℝ)),
          ∑ w ∈ wSph mm, ∑ z ∈ primAnn (2 * N),
            2 * badInd mm x (tauOf x Asave) (Work.FIPlan.gnorm z)
              * ‖pieceCoeff (Pa i k j) (φ k) (q k) (p i) z * Work.FITop3.Zc w z‖)
        ≤ (max cCop cShell) * T2RHS x N (MnOf x N j) Pz (thetaOf x Asave) := by
      set A1 : ℝ := (MnOf x N j : ℝ) ^ ((1 : ℝ) / 4) * (N : ℝ) ^ ((5 : ℝ) / 4) with hA1def
      set A2 : ℝ := (Pz : ℝ)⁻¹ * (MnOf x N j : ℝ) ^ ((3 : ℝ) / 4) * (N : ℝ) ^ ((3 : ℝ) / 4) with hA2def
      set A3 : ℝ := (thetaOf x Asave) * ((MnOf x N j : ℝ) * (N : ℝ)) ^ ((3 : ℝ) / 4) with hA3def
      have hA1nn : 0 ≤ A1 := by rw [hA1def]; positivity
      have hA2nn : 0 ≤ A2 := by rw [hA2def]; positivity
      have hA3nn : 0 ≤ A3 := by rw [hA3def]; positivity
      have hmax0 : 0 ≤ max cCop cShell := le_of_lt (lt_of_lt_of_le hcCop (le_max_left _ _))
      have hc2 : cCop ≤ max cCop cShell := le_max_left _ _
      have hc3 : cShell ≤ max cCop cShell := le_max_right _ _
      have hT2Rh : T2RHS x N (MnOf x N j) Pz (thetaOf x Asave) = (A1 + A2 + A3) * L100 := by
        rw [hA1def, hA2def, hA3def, hL100def]
        unfold T2RHS
        ring
      have hsplit := window_T2_split x N (MnOf x N j) (tauOf x Asave) K K' a p φ q
        (fun i k => Pa i k j) (fun i k => hPaτ i k j)
      have hA := hCop x N (MnOf x N j) Pz (tauOf x Asave) (thetaOf x Asave) K K' a p φ q
          (fun i k => Pa i k j) hx4 hMn1 hN hP2 hθ0 hθ14 hNum.hN2x (fun i k => hPaM i k j)
          (fun i k => hPaN i k j) (fun i k => hPaPz i k j) (fun i k => hPaτ i k j)
          haN ha2 hp0 hp1 hpsup hpsum_le hq0 hq1 hq0z hqsup hang hMnN
      have hB := hShell x N (MnOf x N j) (tauOf x Asave) (thetaOf x Asave) K K' a p φ q
          (fun i k => Pa i k j) hx4 hMn1 hN hθ0 hθ14 hNum.hN2x hNum.hθsqrtN
          (two_N_le_theta_sq_MnOf hNum hN hNhi j)
          (fun i k => hPaM i k j) (fun i k => hPaN i k j) (fun i k => hPaτ i k j)
          haN ha2 hp0 hp1 hpsup hpsum_le hq0 hq1 hq0z hqsup hang
          (fun i k z hz => isPrimitive_of_pieceCoeff_ne_zero hz) hMnN
      have hA' : (∑ i, ∑ k, ∑ mm ∈ (Finset.Icc (MnOf x N j + 1) (2 * MnOf x N j)).filter
            (fun m : ℕ => (m : ℝ) * a i < (x : ℝ)),
          ∑ w ∈ wSph mm, ∑ z ∈ primAnn (2 * N),
            2 * (if Nat.Coprime mm (Work.FIPlan.gnorm z) then (0 : ℝ) else 1)
              * ‖pieceCoeff (Pa i k j) (φ k) (q k) (p i) z * Work.FITop3.Zc w z‖)
          ≤ cCop * (A1 + A2) * L100 := by
        rw [hA1def, hA2def, hL100def]
        exact hA
      have hB' : (∑ i, ∑ k, ∑ mm ∈ (Finset.Icc (MnOf x N j + 1) (2 * MnOf x N j)).filter
            (fun m : ℕ => (m : ℝ) * a i < (x : ℝ)),
          ∑ w ∈ wSph mm, ∑ z ∈ primAnn (2 * N),
            2 * (if (mm : ℝ) * (Work.FIPlan.gnorm z : ℝ) > (x : ℝ) then (1 : ℝ) else 0)
              * ‖pieceCoeff (Pa i k j) (φ k) (q k) (p i) z * Work.FITop3.Zc w z‖)
          ≤ cShell * A3 * L100 := by
        rw [hA3def, hL100def]
        simpa only [mul_assoc] using hB
      have hfin : cCop * (A1 + A2) * L100 + cShell * A3 * L100
          ≤ max cCop cShell * T2RHS x N (MnOf x N j) Pz (thetaOf x Asave) := by
        rw [hT2Rh]
        have e1 : cCop * (A1 + A2) * L100 ≤ max cCop cShell * (A1 + A2) * L100 :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hc2 (by linarith [hA1nn, hA2nn])) hL100nn
        have e2 : cShell * A3 * L100 ≤ max cCop cShell * A3 * L100 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc3 hA3nn) hL100nn
        have e3 : max cCop cShell * (A1 + A2) * L100 + max cCop cShell * A3 * L100
            = max cCop cShell * ((A1 + A2 + A3) * L100) := by ring
        linarith [e1, e2, e3]
      linarith [hsplit, hA', hB', hfin]
    -- the T3 hypothesis
    have hT3 : (∑ mm ∈ Finset.Icc (MnOf x N j + 1) (2 * MnOf x N j), ∑ w ∈ wSph mm,
          ∑ z ∈ primAnn (2 * N),
          cGInd mm N x Pz (tauOf x Asave) (Work.FIPlan.gnorm z)
            * (1 - ∑ i, p i (Work.FIPlan.gnorm z))
            * |(ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℝ)|
            * (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ)
            * (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ))
        ≤ cT3 * T3RHS x N (MnOf x N j) (thetaOf x Asave) := by
      have h := hT3le x N (MnOf x N j) Pz (tauOf x Asave) (thetaOf x Asave) K a p
        (fun i => Pa i ⟨0, hK'pos⟩ j) (by omega) hMn1 hN hP2 hθ0 hθ14
        (fun i => hPaM i ⟨0, hK'pos⟩ j) (fun i => hPaN i ⟨0, hK'pos⟩ j) haN
        (fun i => by rw [hPaN i ⟨0, hK'pos⟩ j]; exact haN i)
        hp0 hp1 hpsup hple2N hpsum_le hpsum_eq hNum.hθsqrtN hMnN
      simpa only [T3RHS, mul_assoc] using h
    simpa only [hFdef, add_assoc] using
      window_bound_act x N Pz (MnOf x N j) C (tauOf x Asave) (thetaOf x Asave) K K' a p φ q
        (fun i k => Pa i k j) (fun i k => f i k j) (max cCop cShell) cT3
        hMn1 hN hP2 haN (fun i k => hPaM i k j) (fun i k => hPaN i k j) (fun i k => hPaC i k j)
        (fun i k => hPaPz i k j) (fun i k => hPaθ i k j) (fun i k => hPaτ i k j)
        hp0 hp1 hpsup hple2N hq0 hq0z hqsup hang hpsum_le (fun i k => hMaj i k j) hT2 hT3
  -- sum the window bounds
  have hwinSum : (∑ j : Fin (JJN x N + 1),
        ∑ m ∈ Finset.Icc (MnOf x N j + 1) (2 * MnOf x N j), Iterm x N Pz C (tauOf x Asave) m)
      ≤ (∑ i, ∑ k, ∑ j : Fin (JJN x N + 1), F i k j)
        + (∑ j : Fin (JJN x N + 1),
            ((max cCop cShell) * T2RHS x N (MnOf x N j) Pz (thetaOf x Asave)
              + cT3 * T3RHS x N (MnOf x N j) (thetaOf x Asave))) := by
    have h := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hwin j)
    have hmainEq : (∑ j : Fin (JJN x N + 1), ∑ i, ∑ k, F i k j)
        = ∑ i, ∑ k, ∑ j : Fin (JJN x N + 1), F i k j := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    have hEq : (∑ j : Fin (JJN x N + 1), ((∑ i, ∑ k, F i k j)
          + ((max cCop cShell) * T2RHS x N (MnOf x N j) Pz (thetaOf x Asave)
              + cT3 * T3RHS x N (MnOf x N j) (thetaOf x Asave))))
        = (∑ i, ∑ k, ∑ j : Fin (JJN x N + 1), F i k j)
          + (∑ j : Fin (JJN x N + 1),
              ((max cCop cShell) * T2RHS x N (MnOf x N j) Pz (thetaOf x Asave)
                + cT3 * T3RHS x N (MnOf x N j) (thetaOf x Asave))) := by
      rw [Finset.sum_add_distrib, hmainEq]
    rw [hEq] at h
    exact h
  -- the error sum
  have herrSum := hErr x N Pz η (max cCop cShell) cT3 (thetaOf x Asave) hNum
    (le_of_lt (lt_of_lt_of_le hcCop (le_max_left _ _))) (le_of_lt hcT3) rfl
    (fun j => (window_MnFactsC hNum j).2.2.2.2.1)
  have hmax_le : max cCop cShell + cT3 ≤ cCop + cShell + cT3 := by
    have h : max cCop cShell ≤ cCop + cShell := max_le (le_add_of_nonneg_right (le_of_lt hcShell))
      (le_add_of_nonneg_left (le_of_lt hcCop))
    linarith
  have herrSum' : (∑ j : Fin (JJN x N + 1),
        ((max cCop cShell) * T2RHS x N (MnOf x N j) Pz (thetaOf x Asave)
          + cT3 * T3RHS x N (MnOf x N j) (thetaOf x Asave)))
      ≤ cErr * (cCop + cShell + cT3) * ((thetaOf x Asave) * (x : ℝ) ^ ((3 : ℝ) / 4)
          * (Real.log (x : ℝ)) ^ (100 : ℕ)) := by
    refine le_trans herrSum ?_
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_left hmax_le (le_of_lt hcErr)
  -- the covering decomposition
  have hBsumpi : BformPiTau x N Pz C (tauOf x Asave)
      = ∑ m ∈ Finset.Icc 1 (2 * MtopN x N), Iterm x N Pz C (tauOf x Asave) m :=
    BformPiTau_eq_sum_window x N Pz C (tauOf x Asave) hN (by exact_mod_cast hNum.htop)
      (by have h : 2 * N ≤ MtopN x N := by exact_mod_cast hNum.hMtopge2N
          omega)
  have hcover := window_cover x N (Iterm x N Pz C (tauOf x Asave))
    (fun m => Iterm_nonneg x N Pz C (tauOf x Asave) m)
  -- the ladder identity
  have hladder : (∑ j : Fin (JJN x N + 1),
        ∑ m ∈ Finset.Icc (MnOf x N j + 1) (2 * MnOf x N j), Iterm x N Pz C (tauOf x Asave) m)
      = (∑ j ∈ Finset.range (JJN x N),
            ∑ m ∈ Finset.Icc (2 ^ j * M0N x N + 1) (2 ^ (j + 1) * M0N x N),
              Iterm x N Pz C (tauOf x Asave) m)
        + (∑ m ∈ Finset.Icc (MtopN x N + 1) (2 * MtopN x N), Iterm x N Pz C (tauOf x Asave) m) := by
    rw [Fin.sum_univ_eq_sum_range (fun n =>
          ∑ m ∈ Finset.Icc (MnOf x N n + 1) (2 * MnOf x N n), Iterm x N Pz C (tauOf x Asave) m)
        (JJN x N + 1), Finset.sum_range_succ]
    congr 1
    · apply Finset.sum_congr rfl
      intro j hj
      have hp : 2 * (2 ^ j * M0N x N) = 2 ^ (j + 1) * M0N x N := by rw [pow_succ]; ring
      rw [MnOf_of_lt (Finset.mem_range.mp hj), hp]
    · rw [MnOf_of_not_lt (by omega : ¬ (JJN x N < JJN x N))]
  -- final assembly on `BformPiTau (tauOf x Asave)`
  have hassem : BformPiTau x N Pz C (tauOf x Asave)
      ≤ (∑ i, ∑ k, ∑ j : Fin (JJN x N + 1), F i k j)
        + cErr * (cCop + cShell + cT3) * ((thetaOf x Asave) * (x : ℝ) ^ ((3 : ℝ) / 4)
            * (Real.log (x : ℝ)) ^ (100 : ℕ))
        + cSmall * ((varthetaOf x Asave) ^ ((3 : ℝ) / 4) * (x : ℝ) ^ ((3 : ℝ) / 4)
            * (Real.log (x : ℝ)) ^ (65536 : ℕ)) := by
    have hsmallB : (∑ m ∈ Finset.Icc 1 (M0N x N), Iterm x N Pz C (tauOf x Asave) m)
        ≤ cSmall * ((varthetaOf x Asave) ^ ((3 : ℝ) / 4) * (x : ℝ) ^ ((3 : ℝ) / 4)
            * (Real.log (x : ℝ)) ^ (65536 : ℕ)) := by
      refine le_trans hsmallSum ?_
      rw [Real.mul_rpow hϑ0.le (Nat.cast_nonneg x)]
      exact le_of_eq (by ring)
    rw [hBsumpi]
    refine le_trans hcover ?_
    linarith [hladder, hwinSum, herrSum', hsmallB]
  -- the `τ`-reduction error
  have hBtau := hTauReduce x N Pz C τ hx0R hN hC hP2 hτ1
  have hAcil : Work.FITop.AcountAtil x ≤ cAc * (x : ℝ) ^ ((3 : ℝ) / 4) := hAc x hx1
  have hErrtau : cTauR * Work.FITop.AcountAtil x * (Real.log (x : ℝ)) ^ (-(Asave - 200000))
      ≤ (cTauR * cAc) * ((varthetaOf x Asave) ^ ((3 : ℝ) / 4) * (x : ℝ) ^ ((3 : ℝ) / 4)
          * (Real.log (x : ℝ)) ^ (65536 : ℕ)) := by
    have hlog0 : 0 ≤ Real.log (x : ℝ) := le_of_lt hlogpos
    have hϑ34 : (varthetaOf x Asave) ^ ((3 : ℝ) / 4) = (Real.log (x : ℝ)) ^ (-(3 * Asave / 4)) := by
      unfold varthetaOf
      rw [← Real.rpow_mul hlog0]
      congr 1
      ring
    have hexp : -(Asave - 200000) ≤ -(3 * Asave / 4) + (65536 : ℝ) := by
      unfold Asave; norm_num
    have hmono : (Real.log (x : ℝ)) ^ (-(Asave - 200000))
        ≤ (Real.log (x : ℝ)) ^ (-(3 * Asave / 4) + (65536 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hlog1 hexp
    have hsplit : (Real.log (x : ℝ)) ^ (-(3 * Asave / 4) + (65536 : ℝ))
        = (Real.log (x : ℝ)) ^ (-(3 * Asave / 4)) * (Real.log (x : ℝ)) ^ (65536 : ℕ) := by
      rw [Real.rpow_add hlogpos]
      rw [show (Real.log (x : ℝ)) ^ (65536 : ℝ) = (Real.log (x : ℝ)) ^ (65536 : ℕ)
        from Real.rpow_natCast _ _]
    have hx34 : 0 ≤ (x : ℝ) ^ ((3 : ℝ) / 4) := Real.rpow_nonneg (by positivity) _
    have hAc0 : 0 ≤ Work.FITop.AcountAtil x := by
      rw [Work.FITop.AcountAtil, Submission.ASP.Acount, Nat.floor_natCast]
      exact Finset.sum_nonneg (fun n _ => Work.FITop.atilFIa_nonneg n)
    have hE0 : 0 ≤ (Real.log (x : ℝ)) ^ (-(Asave - 200000)) := Real.rpow_nonneg hlog0 _
    have h1 : cTauR * Work.FITop.AcountAtil x ≤ cTauR * (cAc * (x : ℝ) ^ ((3 : ℝ) / 4)) :=
      mul_le_mul_of_nonneg_left hAcil (le_of_lt hcTauR)
    have h2 : (Real.log (x : ℝ)) ^ (-(Asave - 200000))
        ≤ (Real.log (x : ℝ)) ^ (-(3 * Asave / 4)) * (Real.log (x : ℝ)) ^ (65536 : ℕ) := by
      rw [← hsplit]; exact hmono
    have hb : 0 ≤ cTauR * (cAc * (x : ℝ) ^ ((3 : ℝ) / 4)) :=
      mul_nonneg (le_of_lt hcTauR) (mul_nonneg (le_of_lt hcAc) hx34)
    have hstep : cTauR * Work.FITop.AcountAtil x * (Real.log (x : ℝ)) ^ (-(Asave - 200000))
        ≤ (cTauR * (cAc * (x : ℝ) ^ ((3 : ℝ) / 4)))
          * ((Real.log (x : ℝ)) ^ (-(3 * Asave / 4)) * (Real.log (x : ℝ)) ^ (65536 : ℕ)) :=
      mul_le_mul h1 h2 hE0 hb
    calc cTauR * Work.FITop.AcountAtil x * (Real.log (x : ℝ)) ^ (-(Asave - 200000))
        ≤ (cTauR * (cAc * (x : ℝ) ^ ((3 : ℝ) / 4)))
          * ((Real.log (x : ℝ)) ^ (-(3 * Asave / 4)) * (Real.log (x : ℝ)) ^ (65536 : ℕ)) := hstep
      _ = (cTauR * cAc) * ((Real.log (x : ℝ)) ^ (-(3 * Asave / 4)) * (x : ℝ) ^ ((3 : ℝ) / 4)
            * (Real.log (x : ℝ)) ^ (65536 : ℕ)) := by ring
      _ = (cTauR * cAc) * ((varthetaOf x Asave) ^ ((3 : ℝ) / 4) * (x : ℝ) ^ ((3 : ℝ) / 4)
            * (Real.log (x : ℝ)) ^ (65536 : ℕ)) := by rw [hϑ34]
  have hcombined : BformPiTau x N Pz C τ
      ≤ (∑ i, ∑ k, ∑ j : Fin (JJN x N + 1), F i k j)
        + cErr * (cCop + cShell + cT3) * ((thetaOf x Asave) * (x : ℝ) ^ ((3 : ℝ) / 4)
            * (Real.log (x : ℝ)) ^ (100 : ℕ))
        + cSmall * ((varthetaOf x Asave) ^ ((3 : ℝ) / 4) * (x : ℝ) ^ ((3 : ℝ) / 4)
            * (Real.log (x : ℝ)) ^ (65536 : ℕ))
        + (cTauR * cAc) * ((varthetaOf x Asave) ^ ((3 : ℝ) / 4) * (x : ℝ) ^ ((3 : ℝ) / 4)
            * (Real.log (x : ℝ)) ^ (65536 : ℕ)) := by
    have hmid : BformPiTau x N Pz C (tauOf x Asave)
          + cTauR * Work.FITop.AcountAtil x * (Real.log (x : ℝ)) ^ (-(Asave - 200000))
        ≤ (∑ i, ∑ k, ∑ j : Fin (JJN x N + 1), F i k j)
          + cErr * (cCop + cShell + cT3) * ((thetaOf x Asave) * (x : ℝ) ^ ((3 : ℝ) / 4)
              * (Real.log (x : ℝ)) ^ (100 : ℕ))
          + cSmall * ((varthetaOf x Asave) ^ ((3 : ℝ) / 4) * (x : ℝ) ^ ((3 : ℝ) / 4)
              * (Real.log (x : ℝ)) ^ (65536 : ℕ))
          + (cTauR * cAc) * ((varthetaOf x Asave) ^ ((3 : ℝ) / 4) * (x : ℝ) ^ ((3 : ℝ) / 4)
              * (Real.log (x : ℝ)) ^ (65536 : ℕ)) := by
      linarith [hassem, hErrtau]
    exact le_trans hBtau hmid
  have hθterm0 : 0 ≤ (thetaOf x Asave) * (x : ℝ) ^ ((3 : ℝ) / 4)
      * (Real.log (x : ℝ)) ^ (100 : ℕ) := by
    have h1 : 0 ≤ (x : ℝ) ^ ((3 : ℝ) / 4) := Real.rpow_nonneg (by positivity) _
    have h2 : 0 ≤ (Real.log (x : ℝ)) ^ (100 : ℕ) := pow_nonneg (le_of_lt hlogpos) _
    positivity
  have hϑterm0 : 0 ≤ (varthetaOf x Asave) ^ ((3 : ℝ) / 4) * (x : ℝ) ^ ((3 : ℝ) / 4)
      * (Real.log (x : ℝ)) ^ (65536 : ℕ) := by
    have h1 : 0 ≤ (x : ℝ) ^ ((3 : ℝ) / 4) := Real.rpow_nonneg (by positivity) _
    have h2 : 0 ≤ (Real.log (x : ℝ)) ^ (65536 : ℕ) := pow_nonneg (le_of_lt hlogpos) _
    have h3 : 0 ≤ (varthetaOf x Asave) ^ ((3 : ℝ) / 4) := Real.rpow_nonneg hϑ0.le _
    positivity
  have hcS : cErr * (cCop + cShell + cT3)
      ≤ cTauR * cAc + cCop + cShell + cT3 + cSmall + cErr * (cCop + cShell + cT3)
        + 64 * ((4 : ℝ) ^ ((3 : ℝ) / 4) / ((2 : ℝ) ^ ((3 : ℝ) / 4) - 1)) + 1 := by
    have h : 0 ≤ cTauR * cAc + cCop + cShell + cT3 + cSmall
        + 64 * ((4 : ℝ) ^ ((3 : ℝ) / 4) / ((2 : ℝ) ^ ((3 : ℝ) / 4) - 1)) + 1 := by positivity
    linarith
  have hcs4 : cSmall + cTauR * cAc ≤ cTauR * cAc + cCop + cShell + cT3 + cSmall
      + cErr * (cCop + cShell + cT3)
      + 64 * ((4 : ℝ) ^ ((3 : ℝ) / 4) / ((2 : ℝ) ^ ((3 : ℝ) / 4) - 1)) + 1 := by
    have h : 0 ≤ cCop + cShell + cT3 + cErr * (cCop + cShell + cT3)
        + 64 * ((4 : ℝ) ^ ((3 : ℝ) / 4) / ((2 : ℝ) ^ ((3 : ℝ) / 4) - 1)) + 1 := by positivity
    linarith
  have hfinal : BformPiTau x N Pz C τ
      ≤ (∑ i, ∑ k, ∑ j : Fin (JJN x N + 1), F i k j)
        + (cTauR * cAc + cCop + cShell + cT3 + cSmall + cErr * (cCop + cShell + cT3)
            + 64 * ((4 : ℝ) ^ ((3 : ℝ) / 4) / ((2 : ℝ) ^ ((3 : ℝ) / 4) - 1)) + 1)
          * ((thetaOf x Asave) * (x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log (x : ℝ)) ^ (100 : ℕ)
            + (varthetaOf x Asave) ^ ((3 : ℝ) / 4) * (x : ℝ) ^ ((3 : ℝ) / 4)
              * (Real.log (x : ℝ)) ^ (65536 : ℕ)) := by
    nlinarith [hcombined, hcS, hcs4, hθterm0, hϑterm0]
  have hmain_reindex : (∑ i, ∑ k, ∑ j : Fin (JJN x N + 1), F i k j)
      = (∑ t : Fin K × Fin K' × Fin (JJN x N + 1), F t.1 t.2.1 t.2.2) := by
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i _
    rw [Fintype.sum_prod_type]
  rw [hmain_reindex] at hfinal
  -- count conjunct
  have hcount := piece_count_window x N (thetaOf x Asave) K K' a hN hx1 hθ0 hθ1
    hNum.hpowJJN haN ha2 hKle hK'le
  have hcount' : (∑ t : Fin K × Fin K' × Fin (JJN x N + 1),
        (((Pa t.1 t.2.1 t.2.2).M * (Pa t.1 t.2.1 t.2.2).N) ^ ((3 : ℝ) / 4)))
      ≤ 64 * ((4 : ℝ) ^ ((3 : ℝ) / 4) / ((2 : ℝ) ^ ((3 : ℝ) / 4) - 1))
          * (thetaOf x Asave) ^ (-(2 : ℝ)) * (x : ℝ) ^ ((3 : ℝ) / 4) := by
    have hreindex : (∑ t : Fin K × Fin K' × Fin (JJN x N + 1),
          (((Pa t.1 t.2.1 t.2.2).M * (Pa t.1 t.2.1 t.2.2).N) ^ ((3 : ℝ) / 4)))
        = ∑ i, ∑ _k : Fin K', ∑ j : Fin (JJN x N + 1),
            (((MnOf x N j : ℝ) * a i) ^ ((3 : ℝ) / 4)) := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro i _
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro j _
      rw [hPaM i k j, hPaN i k j]
    rw [hreindex]
    exact hcount
  refine ⟨Fin K × Fin K' × Fin (JJN x N + 1), inferInstance,
    (fun t : Fin K × Fin K' × Fin (JJN x N + 1) => Pa t.1 t.2.1 t.2.2),
    (fun t : Fin K × Fin K' × Fin (JJN x N + 1) => f t.1 t.2.1 t.2.2),
    (fun t : Fin K × Fin K' × Fin (JJN x N + 1) => φ t.2.1),
    (fun t : Fin K × Fin K' × Fin (JJN x N + 1) =>
      pieceCoeff (Pa t.1 t.2.1 t.2.2) (φ t.2.1) (q t.2.1) (p t.1)),
    ?_, ?_, ?_, ?_, ?_⟩
  · intro t
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hPaFields t.1 t.2.1 t.2.2
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9,
      by rw [hPaN t.1 t.2.1 t.2.2]; exact haN t.1,
      by rw [hPaN t.1 t.2.1 t.2.2]; exact ha2 t.1⟩
  · intro t; exact hMaj t.1 t.2.1 t.2.2
  · intro t
    refine pieceCoeff_isBetaCoeff (hqcd t.2.1) (hq0 t.2.1) (hq1 t.2.1) ?_ ?_
      (hpcd t.1) (hp0 t.1) (hp1 t.1) ?_ ?_
    · intro α hα
      obtain ⟨h1, h2⟩ := hqsup t.2.1 α hα
      exact ⟨h1, by rw [hPaθ t.1 t.2.1 t.2.2]; exact h2⟩
    · intro jn hj α
      rw [hPaθ t.1 t.2.1 t.2.2]
      exact hqder t.2.1 jn hj α
    · intro u hu
      obtain ⟨h1, h2⟩ := hpsup t.1 u hu
      refine ⟨?_, ?_⟩
      · rw [hPaN t.1 t.2.1 t.2.2]; exact h1
      · rw [hPaθ t.1 t.2.1 t.2.2, hPaN t.1 t.2.1 t.2.2]; exact h2
    · intro jn hj u
      rw [hPaθ t.1 t.2.1 t.2.2, hPaN t.1 t.2.1 t.2.2]
      exact hpder t.1 jn hj u
  · refine le_trans hcount' ?_
    have hθ0' : 0 ≤ (thetaOf x Asave) ^ (-(2 : ℝ)) := Real.rpow_nonneg hθ0.le _
    have hx34 : 0 ≤ (x : ℝ) ^ ((3 : ℝ) / 4) := Real.rpow_nonneg (by positivity) _
    have hle : 64 * ((4 : ℝ) ^ ((3 : ℝ) / 4) / ((2 : ℝ) ^ ((3 : ℝ) / 4) - 1))
        ≤ cTauR * cAc + cCop + cShell + cT3 + cSmall + cErr * (cCop + cShell + cT3)
          + 64 * ((4 : ℝ) ^ ((3 : ℝ) / 4) / ((2 : ℝ) ^ ((3 : ℝ) / 4) - 1)) + 1 := by
      have h : 0 ≤ cTauR * cAc + cCop + cShell + cT3 + cSmall + cErr * (cCop + cShell + cT3) + 1 := by
        positivity
      linarith
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hle hθ0') hx34
  · exact hfinal

end

end Work.FITop4.Red5
