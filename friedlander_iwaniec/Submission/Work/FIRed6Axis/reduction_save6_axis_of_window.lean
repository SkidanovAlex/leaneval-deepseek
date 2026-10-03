import Mathlib
import Submission.Work.FIRed6Axis.Statement
import Submission.Work.FIRed6Axis.window_bound_act_axis
import Submission.Work.FITop4.Defs6
import Submission.Work.FITop4.Areas6
import Submission.Work.FITop4.Red5.Vocab
import Submission.Work.FITop4.Red5.sieve_step
import Submission.Work.FITop4.Defs4
import Submission.Work.FITop4.Red5.Aseq_tau_sq_le
import Submission.Commons.NumberTheory.FriedlanderIwaniec.Aseq_eq_intpairs_ncard
import Submission.Commons.NumberTheory.FriedlanderIwaniec.card_sq_add_pow_four_intpairs_asymptotic
import Submission.Work.FITop4.Red5.radial_partition_le
import Submission.Work.FITop4.Red5.angular_partition_le
import Submission.Work.FITop.Defs
import Submission.Work.FITop4.Red4.sum_norm_inner_le
import Submission.Work.FITop4.Red5.assembly_helpers
import Submission.Work.FITop4.Red5.piecesSetup
import Submission.Work.FITop4.Red5.pieceDefs
import Submission.Work.FITop4.Red5.anFI_sum_eq_gauss_primary
import Submission.Work.FITop4.Red5.sieve_inner_le_pieces_zint
import Submission.Work.FITop4.Red5.window_T1_le
import Submission.Work.FITop4.Red5.BformPiTau_tauReduce
import Submission.Work.FITop4.Red5.BformPiTauSmall_le
import Submission.Work.FITop3.Majorant.majorant_props
import Submission.Work.FITop4.Red5.reduction_save_core
import Submission.Work.FITop4.Witness6.exists_isMajorant6_seq
import Submission.Work.FITop4.Red5.window_bound_act

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.FIRed6Axis

open Finset
open scoped BigOperators
open Work.FITop4
open Work.FITop4.Red5

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## Helper lemmas for the axis-aware reduction -/

/-- `4π L^{-A'} ≤ L^{-A}` when `L ≥ 2`, `A > 0` and `A' ≥ 2A + 2^{20}`.  With `L = log x`,
`A' = Aprime A` this is `4πθ ≤ ϑ` for `θ = (log x)^{-A'}`, `ϑ = (log x)^{-A}`. -/
lemma axis_four_pi_rpow_neg_le (L A A' : ℝ) (hL : 2 ≤ L) (hA : 0 < A)
    (hA' : 2 * A + (2 : ℝ) ^ (20 : ℕ) ≤ A') :
    4 * Real.pi * L ^ (-A') ≤ L ^ (-A) := by
  have hL0 : (0:ℝ) < L := by linarith
  have hL1 : (1:ℝ) ≤ L := by linarith
  have hA'A : (2:ℝ) ^ (20 : ℕ) ≤ A' - A := by linarith
  have hstep1 : (2:ℝ) ^ ((2:ℝ) ^ (20 : ℕ)) ≤ L ^ ((2:ℝ) ^ (20 : ℕ)) :=
    Real.rpow_le_rpow (by norm_num) hL (by positivity)
  have hstep2 : L ^ ((2:ℝ) ^ (20 : ℕ)) ≤ L ^ (A' - A) :=
    Real.rpow_le_rpow_of_exponent_le hL1 hA'A
  have hstep3 : (32:ℝ) ≤ (2:ℝ) ^ ((2:ℝ) ^ (20 : ℕ)) := by
    rw [show (2:ℝ) ^ (20:ℕ) = ((2^20 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    calc (32:ℝ) = (2:ℝ)^5 := by norm_num
      _ ≤ (2:ℝ)^(2^20) := pow_le_pow_right₀ (by norm_num) (by norm_num)
  have hkey : 4 * Real.pi ≤ L ^ (A' - A) := by
    have h16 : 4 * Real.pi < 32 := by nlinarith [Real.pi_lt_four]
    linarith [hstep1, hstep2, hstep3]
  calc 4 * Real.pi * L ^ (-A') ≤ L ^ (A' - A) * L ^ (-A') :=
        mul_le_mul_of_nonneg_right hkey (Real.rpow_nonneg hL0.le _)
    _ = L ^ (-A) := by
        rw [← Real.rpow_add hL0]
        congr 1
        ring

/-- The far/near angular transfer: if the boundary `φ` of a cell is *not* far from the axes
(`¬ farAngle ϑ θ φ`) and `φ < α ≤ φ + 2πθ`, then `α` lies within `4ϑ` of a multiple of `π/2`
(using `2πθ ≤ ϑ`). -/
lemma not_farAngle_nearArg {ϑ θ φ α : ℝ} (h : ¬ farAngle ϑ θ φ) (hθ : 0 ≤ θ)
    (hle : 2 * Real.pi * θ ≤ ϑ) (h1 : φ < α) (h2 : α ≤ φ + 2 * Real.pi * θ) :
    ∃ m : ℤ, |α - (m : ℝ) * (Real.pi / 2)| ≤ 4 * ϑ := by
  rw [farAngle] at h
  push_neg at h
  obtain ⟨m, hm⟩ := h
  refine ⟨m, ?_⟩
  have hφ1 : (0:ℝ) ≤ α - φ := by linarith
  have hφ : α - φ ≤ 2 * Real.pi * θ := by linarith
  have hm2 := abs_lt.mp hm
  rw [abs_le]
  constructor <;> nlinarith [hm2.1, hm2.2, hφ, hφ1, hle]

/-- For fixed `D : ℕ` and `ε > 0`, `(log x)^D ≤ x^ε` for all large `x`. -/
lemma axis_log_pow_le_rpow_eventually (D : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x → (Real.log (x : ℝ)) ^ D ≤ (x : ℝ) ^ ε := by
  by_cases hD : D = 0
  · refine ⟨1, fun x hx => ?_⟩
    rw [hD, pow_zero]
    exact Real.one_le_rpow (by exact_mod_cast hx) hε.le
  · set T : ℝ := (2 * (D : ℝ) / ε) ^ 2 + 1 with hT
    refine ⟨Nat.ceil (Real.exp T) + 2, fun x hx => ?_⟩
    have hxT : Real.exp T < (x : ℝ) := by
      have h1 : Real.exp T ≤ (Nat.ceil (Real.exp T) : ℝ) := Nat.le_ceil _
      have h2 : (Nat.ceil (Real.exp T) : ℝ) + 2 ≤ (x : ℝ) := by exact_mod_cast hx
      linarith
    have hlogT : T ≤ Real.log (x : ℝ) := by
      have h := Real.log_lt_log (Real.exp_pos T) hxT
      rw [Real.log_exp] at h
      exact le_of_lt h
    have hT1 : 1 ≤ T := by
      rw [hT]; have : (0:ℝ) ≤ (2 * (D:ℝ) / ε) ^ 2 := sq_nonneg _; linarith
    have hlogpos : 0 < Real.log (x : ℝ) := by linarith
    have hxpos : (0:ℝ) < (x:ℝ) := by
      have : (0:ℝ) < Real.exp T := Real.exp_pos T
      linarith
    have hloglog : Real.log (Real.log (x:ℝ)) ≤ 2 * (Real.log (x:ℝ)) ^ ((1:ℝ)/2) := by
      have h := Real.log_le_rpow_div (x := Real.log (x:ℝ)) hlogpos.le
        (by norm_num : (0:ℝ) < (1:ℝ)/2)
      have hhalf : (Real.log (x:ℝ)) ^ ((1:ℝ)/2) / ((1:ℝ)/2)
          = 2 * (Real.log (x:ℝ)) ^ ((1:ℝ)/2) := by
        rw [div_eq_mul_inv, show ((1:ℝ)/2)⁻¹ = 2 by norm_num]
        ring
      rwa [hhalf] at h
    have hsqrtpos : 0 < (Real.log (x:ℝ)) ^ ((1:ℝ)/2) := Real.rpow_pos_of_pos hlogpos _
    have hsqrt : 2 * (D : ℝ) / ε ≤ (Real.log (x:ℝ)) ^ ((1:ℝ)/2) := by
      have hT2 : (2 * (D:ℝ) / ε) ^ 2 ≤ Real.log (x:ℝ) := by
        rw [hT] at hlogT; linarith
      have hnonneg : (0:ℝ) ≤ 2 * (D:ℝ) / ε := by positivity
      have h1 : ((2 * (D:ℝ) / ε) ^ 2) ^ ((1:ℝ)/2) ≤ (Real.log (x:ℝ)) ^ ((1:ℝ)/2) :=
        Real.rpow_le_rpow (by positivity) hT2 (by norm_num)
      have h2 : ((2 * (D:ℝ) / ε) ^ 2) ^ ((1:ℝ)/2) = 2 * (D:ℝ) / ε := by
        have hcast : ((2 * (D:ℝ) / ε) ^ 2 : ℝ) = (2 * (D:ℝ) / ε) ^ (((2:ℕ)):ℝ) := by
          rw [Real.rpow_natCast]
        rw [hcast, ← Real.rpow_mul hnonneg]
        rw [show (((2:ℕ)):ℝ) * ((1:ℝ)/2) = 1 by norm_num, Real.rpow_one]
      rwa [h2] at h1
    have hkey : (D:ℝ) * Real.log (Real.log (x:ℝ)) ≤ ε * Real.log (x:ℝ) := by
      have h1 : (D:ℝ) * Real.log (Real.log (x:ℝ))
          ≤ (D:ℝ) * (2 * (Real.log (x:ℝ)) ^ ((1:ℝ)/2)) :=
        mul_le_mul_of_nonneg_left hloglog (Nat.cast_nonneg D)
      have h2 : (D:ℝ) * (2 * (Real.log (x:ℝ)) ^ ((1:ℝ)/2))
          ≤ ε * Real.log (x:ℝ) := by
        have hε2 : 2 * (D:ℝ) ≤ ε * (Real.log (x:ℝ)) ^ ((1:ℝ)/2) := by
          have h := mul_le_mul_of_nonneg_left hsqrt hε.le
          have hc : ε * (2 * (D:ℝ) / ε) = 2 * (D:ℝ) := by
            rw [mul_comm ε (2 * (D:ℝ) / ε), div_mul_cancel₀ _ (ne_of_gt hε)]
          rw [hc] at h
          exact h
        have hsq : (Real.log (x:ℝ)) ^ ((1:ℝ)/2) * (Real.log (x:ℝ)) ^ ((1:ℝ)/2)
            = Real.log (x:ℝ) := by
          rw [← Real.rpow_add hlogpos, show (1:ℝ)/2 + (1:ℝ)/2 = 1 by norm_num, Real.rpow_one]
        calc (D:ℝ) * (2 * (Real.log (x:ℝ)) ^ ((1:ℝ)/2))
            = (2 * (D:ℝ)) * (Real.log (x:ℝ)) ^ ((1:ℝ)/2) := by ring
          _ ≤ (ε * (Real.log (x:ℝ)) ^ ((1:ℝ)/2)) * (Real.log (x:ℝ)) ^ ((1:ℝ)/2) :=
              mul_le_mul_of_nonneg_right hε2 hsqrtpos.le
          _ = ε * Real.log (x:ℝ) := by rw [mul_assoc, hsq]
      linarith
    have hlogeq : Real.log ((Real.log (x:ℝ)) ^ D) = (D:ℝ) * Real.log (Real.log (x:ℝ)) := by
      rw [Real.log_pow]
    have hlogeq2 : Real.log ((x:ℝ) ^ ε) = ε * Real.log (x:ℝ) := Real.log_rpow hxpos ε
    rw [← Real.log_le_log_iff (pow_pos hlogpos D) (Real.rpow_pos_of_pos hxpos ε)]
    rw [hlogeq, hlogeq2]
    exact hkey

/-! ## The accumulated near-axis error -/

/-- Geometric bound `∑_{j<n} r^j ≤ r^n/(r-1)` for `r > 1`. -/
lemma axis_geom_sum_fin_le {r : ℝ} (hr : 1 < r) (n : ℕ) :
    (∑ j : Fin n, r ^ (j : ℕ)) ≤ r ^ n / (r - 1) := by
  rw [Fin.sum_univ_eq_sum_range (fun i => r ^ i) n, geom_sum_eq (ne_of_gt hr) n]
  apply div_le_div_of_nonneg_right _ (by linarith : (0 : ℝ) ≤ r - 1)
  have h : (1 : ℝ) ≤ r ^ n := one_le_pow₀ hr.le
  linarith

/-- `(c^j)^e = (c^e)^j` (`c ≥ 0`). -/
lemma axis_pow_rpow (c e : ℝ) (hc : 0 ≤ c) (j : ℕ) :
    ((c ^ j : ℝ) ^ e) = (c ^ e) ^ j := by
  calc ((c ^ j : ℝ) ^ e) = (c ^ ((j : ℕ) : ℝ)) ^ e := by rw [Real.rpow_natCast]
    _ = c ^ (((j : ℕ) : ℝ) * e) := (Real.rpow_mul hc _ _).symm
    _ = c ^ (e * ((j : ℕ) : ℝ)) := by rw [mul_comm]
    _ = (c ^ e) ^ ((j : ℕ) : ℝ) := Real.rpow_mul hc _ _
    _ = (c ^ e) ^ j := by rw [Real.rpow_natCast]

/-- The elementary factor identity behind the near-error accumulation.  (The exponents are written
in the `-((1:ℝ)/4)` spelling in which `Real.rpow_neg` produces them.) -/
lemma axis_near_fac_eq (x N ϑ : ℝ) (hx : 0 ≤ x) (hN : 0 < N) :
    N ^ (-((1:ℝ)/4)) * (ϑ * N + Real.sqrt N + N ^ ((5:ℝ)/6) + N ^ ((2:ℝ)/3) + 1)
        * (x / N) ^ ((3:ℝ)/4)
      = x ^ ((3:ℝ)/4)
          * (ϑ + N ^ (-((1:ℝ)/2)) + N ^ (-((1:ℝ)/6)) + N ^ (-((1:ℝ)/3)) + N ^ (-((1:ℝ)))) := by
  have hdiv : (x / N) ^ ((3:ℝ)/4) = x ^ ((3:ℝ)/4) * N ^ (-((3:ℝ)/4)) := by
    calc (x / N) ^ ((3:ℝ)/4) = x ^ ((3:ℝ)/4) / N ^ ((3:ℝ)/4) :=
          Real.div_rpow hx hN.le ((3:ℝ)/4)
      _ = x ^ ((3:ℝ)/4) * (N ^ ((3:ℝ)/4))⁻¹ := div_eq_mul_inv _ _
      _ = x ^ ((3:ℝ)/4) * N ^ (-((3:ℝ)/4)) := by rw [Real.rpow_neg hN.le ((3:ℝ)/4)]
  rw [hdiv, Real.sqrt_eq_rpow N]
  have hNN : N ^ (-((1:ℝ))) * N = 1 := by
    rw [Real.rpow_neg hN.le ((1:ℝ)), Real.rpow_one, inv_mul_cancel₀ (ne_of_gt hN)]
  have h1 : N ^ (-((1:ℝ))) * (ϑ * N) = ϑ := by
    rw [mul_comm ϑ N, ← mul_assoc, hNN, one_mul]
  have h2 : N ^ (-((1:ℝ))) * N ^ ((1:ℝ)/2) = N ^ (-((1:ℝ)/2)) := by
    rw [← Real.rpow_add hN]; norm_num
  have h3 : N ^ (-((1:ℝ))) * N ^ ((5:ℝ)/6) = N ^ (-((1:ℝ)/6)) := by
    rw [← Real.rpow_add hN]; norm_num
  have h4 : N ^ (-((1:ℝ))) * N ^ ((2:ℝ)/3) = N ^ (-((1:ℝ)/3)) := by
    rw [← Real.rpow_add hN]; norm_num
  have h5 : N ^ (-((1:ℝ))) * 1 = N ^ (-((1:ℝ))) := mul_one _
  have h34 : N ^ (-((1:ℝ)/4)) * N ^ (-((3:ℝ)/4)) = N ^ (-((1:ℝ))) := by
    rw [← Real.rpow_add hN]; norm_num
  calc N ^ (-((1:ℝ)/4)) * (ϑ * N + N ^ ((1:ℝ)/2) + N ^ ((5:ℝ)/6) + N ^ ((2:ℝ)/3) + 1)
        * (x ^ ((3:ℝ)/4) * N ^ (-((3:ℝ)/4)))
      = x ^ ((3:ℝ)/4) * (N ^ (-((1:ℝ)/4)) * N ^ (-((3:ℝ)/4))
          * (ϑ * N + N ^ ((1:ℝ)/2) + N ^ ((5:ℝ)/6) + N ^ ((2:ℝ)/3) + 1)) := by ring
    _ = x ^ ((3:ℝ)/4) * (N ^ (-((1:ℝ)))
          * (ϑ * N + N ^ ((1:ℝ)/2) + N ^ ((5:ℝ)/6) + N ^ ((2:ℝ)/3) + 1)) := by rw [h34]
    _ = x ^ ((3:ℝ)/4)
          * (ϑ + N ^ (-((1:ℝ)/2)) + N ^ (-((1:ℝ)/6)) + N ^ (-((1:ℝ)/3)) + N ^ (-((1:ℝ)))) := by
        simp only [mul_add, h1, h2, h3, h4, h5]

/-- **The accumulated near-axis error over the window ladder.** -/
theorem axis_near_error_ladder_le :
    ∃ K : ℝ, 0 < K ∧ ∃ x₀ : ℕ, ∀ (x N Pz : ℕ) (η : ℝ),
      x₀ ≤ x → 1 ≤ N → 0 < η → Red5NumC x N Pz η →
      (x : ℝ) ^ ((1 : ℝ) / 4 + η) < (N : ℝ) →
      (∑ j : Fin (JJN x N + 1),
        ((MnOf x N j : ℝ) ^ ((3 : ℝ) / 4) * (N : ℝ) ^ (-(1 : ℝ) / 4)
          * (varthetaOf x Asave * (N : ℝ) + Real.sqrt (N : ℝ)
              + (N : ℝ) ^ ((5 : ℝ) / 6) + (N : ℝ) ^ ((2 : ℝ) / 3) + 1)
          * (Real.log (2 + (N : ℝ))) ^ (20 : ℕ)))
        ≤ K * varthetaOf x Asave * (x : ℝ) ^ ((3 : ℝ) / 4)
            * (Real.log (x : ℝ)) ^ Kaxis := by
  set r : ℝ := (2 : ℝ) ^ ((3 : ℝ) / 4) with hrdef
  have hr1 : 1 < r := by rw [hrdef]; exact Real.one_lt_rpow (by norm_num) (by norm_num)
  have hrm1 : 0 < r - 1 := by linarith
  have hrne : r - 1 ≠ 0 := ne_of_gt hrm1
  set c1 : ℝ := 1 + 1 / (r - 1) with hc1def
  have hc1pos : 0 < c1 := by
    rw [hc1def]; have := div_pos one_pos hrm1; linarith
  set K : ℝ := 5 * c1 with hKdef
  have hKpos : 0 < K := by rw [hKdef]; positivity
  obtain ⟨x₀L, hx₀L⟩ := axis_log_pow_le_rpow_eventually 200000000 ((1:ℝ)/48) (by norm_num)
  refine ⟨K, hKpos, max x₀L 64, ?_⟩
  intro x N Pz η hx0 hN hη0 hNum hNlo
  have hx64 : 64 ≤ x := le_trans (le_max_right _ _) hx0
  have hxL : x₀L ≤ x := le_trans (le_max_left _ _) hx0
  have hx1 : 1 ≤ x := by omega
  have hxpos : (0:ℝ) < (x:ℝ) := by exact_mod_cast (by omega : 0 < x)
  have hxn0 : 0 ≤ (x:ℝ) := le_of_lt hxpos
  have hlog1 : 1 ≤ Real.log (x:ℝ) := hNum.hlog1
  have hlogpos : 0 < Real.log (x:ℝ) := by linarith
  have hNpos : 0 < N := by omega
  have hNp : (0:ℝ) < (N:ℝ) := by exact_mod_cast hNpos
  have hNn0 : 0 ≤ (N:ℝ) := le_of_lt hNp
  have hϑ0 : 0 < varthetaOf x Asave := hNum.hv0
  have hϑnn : 0 ≤ varthetaOf x Asave := le_of_lt hϑ0
  have hM0pos : 0 < (M0N x N : ℝ) := by exact_mod_cast M0N_pos x N
  -- the geometric bound on the ladder
  have hgeom : (∑ j : Fin (JJN x N + 1), (MnOf x N j : ℝ) ^ ((3:ℝ)/4))
      ≤ c1 * ((x:ℝ)/(N:ℝ)) ^ ((3:ℝ)/4) := by
    rw [Fin.sum_univ_eq_sum_range (fun i => (MnOf x N i : ℝ) ^ ((3:ℝ)/4)) (JJN x N + 1),
      Finset.sum_range_succ]
    have hpart1 : (∑ i ∈ Finset.range (JJN x N), (MnOf x N i : ℝ) ^ ((3:ℝ)/4))
        = (M0N x N : ℝ) ^ ((3:ℝ)/4) * (∑ i ∈ Finset.range (JJN x N), r ^ i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      have hi' : i < JJN x N := Finset.mem_range.mp hi
      rw [MnOf_of_lt hi']
      have hcast : ((2 ^ i * M0N x N : ℕ) : ℝ) = (2:ℝ)^i * (M0N x N : ℝ) := by push_cast; ring
      rw [hcast, Real.mul_rpow (by positivity) hM0pos.le,
        axis_pow_rpow 2 ((3:ℝ)/4) (by norm_num) i, ← hrdef]
      ring
    rw [hpart1, MnOf_of_not_lt (lt_irrefl (JJN x N))]
    have hb1 : (M0N x N : ℝ) ^ ((3:ℝ)/4) * (∑ i ∈ Finset.range (JJN x N), r ^ i)
        ≤ ((x:ℝ)/(N:ℝ)) ^ ((3:ℝ)/4) / (r - 1) := by
      have hs : (∑ i ∈ Finset.range (JJN x N), r ^ i) ≤ r^(JJN x N)/(r-1) := by
        rw [← Fin.sum_univ_eq_sum_range (fun i => r^i) (JJN x N)]
        exact axis_geom_sum_fin_le hr1 (JJN x N)
      have h1 : (M0N x N : ℝ) ^ ((3:ℝ)/4) * (∑ i ∈ Finset.range (JJN x N), r ^ i)
          ≤ (M0N x N : ℝ) ^ ((3:ℝ)/4) * (r^(JJN x N)/(r-1)) :=
        mul_le_mul_of_nonneg_left hs (Real.rpow_nonneg hM0pos.le _)
      refine le_trans h1 ?_
      have hA : (M0N x N : ℝ) ^ ((3:ℝ)/4) * (r ^ (JJN x N) / (r - 1))
          = ((2:ℝ) ^ (JJN x N) * (M0N x N : ℝ)) ^ ((3:ℝ)/4) / (r - 1) := by
        rw [Real.mul_rpow (by positivity) hM0pos.le,
          axis_pow_rpow 2 ((3:ℝ)/4) (by norm_num) (JJN x N), ← hrdef]
        ring
      rw [hA]
      exact div_le_div_of_nonneg_right
        (Real.rpow_le_rpow (by positivity) hNum.hpowJJN (by norm_num)) hrm1.le
    have hb2 : (MtopN x N : ℝ) ^ ((3:ℝ)/4) ≤ ((x:ℝ)/(N:ℝ)) ^ ((3:ℝ)/4) :=
      Real.rpow_le_rpow (by positivity)
        (le_trans hNum.hMtoplepow hNum.hpowJJN) (by norm_num)
    have hid : c1 * ((x:ℝ)/(N:ℝ)) ^ ((3:ℝ)/4)
        = ((x:ℝ)/(N:ℝ)) ^ ((3:ℝ)/4) / (r - 1) + ((x:ℝ)/(N:ℝ)) ^ ((3:ℝ)/4) := by
      rw [hc1def]
      field_simp
      ring
    linarith [hb1, hb2, hid]
  -- the factor
  set Fac : ℝ := (N:ℝ)^(-(1:ℝ)/4)
      * (varthetaOf x Asave * (N:ℝ) + Real.sqrt (N:ℝ)
          + (N:ℝ)^((5:ℝ)/6) + (N:ℝ)^((2:ℝ)/3) + 1)
      * (Real.log (2 + (N:ℝ)))^(20:ℕ) with hFacdef
  set FacB : ℝ := (N:ℝ)^(-(1:ℝ)/4)
      * (varthetaOf x Asave * (N:ℝ) + Real.sqrt (N:ℝ)
          + (N:ℝ)^((5:ℝ)/6) + (N:ℝ)^((2:ℝ)/3) + 1) with hFacBdef
  have hFacBnn : 0 ≤ FacB := by
    rw [hFacBdef]
    have h1 : 0 ≤ (N:ℝ)^(-(1:ℝ)/4) := Real.rpow_nonneg hNn0 _
    have h2 : 0 ≤ varthetaOf x Asave * (N:ℝ) + Real.sqrt (N:ℝ)
        + (N:ℝ)^((5:ℝ)/6) + (N:ℝ)^((2:ℝ)/3) + 1 := by
      have hb : 0 ≤ varthetaOf x Asave * (N:ℝ) := mul_nonneg hϑnn hNn0
      have hs := Real.sqrt_nonneg (N:ℝ)
      have hp5 : 0 ≤ (N:ℝ)^((5:ℝ)/6) := Real.rpow_nonneg hNn0 _
      have hp2 : 0 ≤ (N:ℝ)^((2:ℝ)/3) := Real.rpow_nonneg hNn0 _
      linarith
    positivity
  have hFacnn : 0 ≤ Fac := by
    rw [hFacdef]
    have h3 : 0 ≤ (Real.log (2 + (N:ℝ)))^(20:ℕ) :=
      pow_nonneg (Real.log_nonneg (by linarith)) 20
    positivity
  have hsplit : (∑ j : Fin (JJN x N + 1),
        ((MnOf x N j : ℝ) ^ ((3 : ℝ) / 4) * (N : ℝ) ^ (-(1 : ℝ) / 4)
          * (varthetaOf x Asave * (N : ℝ) + Real.sqrt (N : ℝ)
              + (N : ℝ) ^ ((5 : ℝ) / 6) + (N : ℝ) ^ ((2 : ℝ) / 3) + 1)
          * (Real.log (2 + (N : ℝ))) ^ (20 : ℕ)))
      = Fac * (∑ j : Fin (JJN x N + 1), (MnOf x N j : ℝ) ^ ((3 : ℝ) / 4)) := by
    rw [hFacdef, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have h2Nx : 2 + (N:ℝ) ≤ (x:ℝ) := by
    have h1 : (2:ℝ) ≤ (x:ℝ)/2 := by
      have h64 : (64:ℝ) ≤ (x:ℝ) := by exact_mod_cast hx64
      linarith
    have h2 : (N:ℝ) ≤ (x:ℝ)/2 := by linarith [hNum.h2Nx]
    linarith
  have hlog2N : Real.log (2 + (N:ℝ)) ≤ Real.log (x:ℝ) :=
    Real.log_le_log (by linarith) h2Nx
  have hFac_le : Fac ≤ FacB * (Real.log (x:ℝ))^(20:ℕ) := by
    rw [hFacdef, hFacBdef]
    have h3 : (Real.log (2 + (N:ℝ)))^(20:ℕ) ≤ (Real.log (x:ℝ))^(20:ℕ) :=
      pow_le_pow_left₀ (Real.log_nonneg (by linarith)) hlog2N 20
    calc (N:ℝ)^(-(1:ℝ)/4) * (varthetaOf x Asave * (N:ℝ) + Real.sqrt (N:ℝ)
            + (N:ℝ)^((5:ℝ)/6) + (N:ℝ)^((2:ℝ)/3) + 1)
          * (Real.log (2 + (N:ℝ)))^(20:ℕ)
        ≤ ((N:ℝ)^(-(1:ℝ)/4) * (varthetaOf x Asave * (N:ℝ) + Real.sqrt (N:ℝ)
            + (N:ℝ)^((5:ℝ)/6) + (N:ℝ)^((2:ℝ)/3) + 1))
          * (Real.log (x:ℝ))^(20:ℕ) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = (N:ℝ)^(-(1:ℝ)/4) * (varthetaOf x Asave * (N:ℝ) + Real.sqrt (N:ℝ)
            + (N:ℝ)^((5:ℝ)/6) + (N:ℝ)^((2:ℝ)/3) + 1)
          * (Real.log (x:ℝ))^(20:ℕ) := rfl
  have hFacB' : FacB = (N:ℝ)^(-((1:ℝ)/4))
      * (varthetaOf x Asave * (N:ℝ) + Real.sqrt (N:ℝ)
          + (N:ℝ)^((5:ℝ)/6) + (N:ℝ)^((2:ℝ)/3) + 1) := by
    rw [hFacBdef, show (-(1:ℝ)/4) = -((1:ℝ)/4) by ring]
  have hfacid : FacB * ((x:ℝ)/(N:ℝ))^((3:ℝ)/4)
      = (x:ℝ)^((3:ℝ)/4) * (varthetaOf x Asave + (N:ℝ)^(-((1:ℝ)/2))
          + (N:ℝ)^(-((1:ℝ)/6)) + (N:ℝ)^(-((1:ℝ)/3)) + (N:ℝ)^(-((1:ℝ)))) := by
    rw [hFacB']
    exact axis_near_fac_eq (x:ℝ) (N:ℝ) (varthetaOf x Asave) hxn0 hNp
  -- the four decaying terms
  have hdecay : ∀ (e : ℝ), e < 0 → (N:ℝ)^e ≤ (x:ℝ)^(e * ((1:ℝ)/4 + η)) := by
    intro e he
    have h1 : (N:ℝ)^e < ((x:ℝ)^((1:ℝ)/4 + η))^e :=
      Real.rpow_lt_rpow_of_neg (Real.rpow_pos_of_pos hxpos _) hNlo he
    have h2 : ((x:ℝ)^((1:ℝ)/4 + η))^e = (x:ℝ)^(e * ((1:ℝ)/4 + η)) := by
      rw [← Real.rpow_mul hxn0]
      congr 1
      ring
    linarith [h1, h2.le]
  have hdec1 : (N:ℝ)^(-((1:ℝ)/2)) ≤ (x:ℝ)^(-((1:ℝ)/24)) := by
    have h := hdecay (-((1:ℝ)/2)) (by norm_num)
    have he : (-((1:ℝ)/2)) * ((1:ℝ)/4 + η) ≤ -((1:ℝ)/24) := by nlinarith
    exact le_trans h (Real.rpow_le_rpow_of_exponent_le (by linarith : (1:ℝ) ≤ (x:ℝ)) he)
  have hdec2 : (N:ℝ)^(-((1:ℝ)/6)) ≤ (x:ℝ)^(-((1:ℝ)/24)) := by
    have h := hdecay (-((1:ℝ)/6)) (by norm_num)
    have he : (-((1:ℝ)/6)) * ((1:ℝ)/4 + η) ≤ -((1:ℝ)/24) := by nlinarith
    exact le_trans h (Real.rpow_le_rpow_of_exponent_le (by linarith : (1:ℝ) ≤ (x:ℝ)) he)
  have hdec3 : (N:ℝ)^(-((1:ℝ)/3)) ≤ (x:ℝ)^(-((1:ℝ)/24)) := by
    have h := hdecay (-((1:ℝ)/3)) (by norm_num)
    have he : (-((1:ℝ)/3)) * ((1:ℝ)/4 + η) ≤ -((1:ℝ)/24) := by nlinarith
    exact le_trans h (Real.rpow_le_rpow_of_exponent_le (by linarith : (1:ℝ) ≤ (x:ℝ)) he)
  have hdec4 : (N:ℝ)^(-((1:ℝ))) ≤ (x:ℝ)^(-((1:ℝ)/24)) := by
    have h := hdecay (-((1:ℝ))) (by norm_num)
    have he : (-((1:ℝ))) * ((1:ℝ)/4 + η) ≤ -((1:ℝ)/24) := by nlinarith
    exact le_trans h (Real.rpow_le_rpow_of_exponent_le (by linarith : (1:ℝ) ≤ (x:ℝ)) he)
  -- the log-power absorption
  have hlogpow : (Real.log (x:ℝ)) ^ (20:ℕ) * (Real.log (x:ℝ)) ^ (Asave - Kaxis)
      ≤ (x:ℝ) ^ ((1:ℝ)/24) := by
    have h1 : (Real.log (x:ℝ)) ^ (20:ℕ) * (Real.log (x:ℝ)) ^ (Asave - Kaxis)
        = (Real.log (x:ℝ)) ^ ((((20:ℕ)):ℝ) + (Asave - Kaxis)) := by
      rw [← Real.rpow_natCast (Real.log (x:ℝ)) 20, ← Real.rpow_add hlogpos]
    have hexp : ((((20:ℕ)):ℝ) + (Asave - Kaxis)) ≤ ((200000000 : ℕ) : ℝ) := by
      norm_num [Work.FITop4.Asave, Work.FIRed6Axis.Kaxis]
    have h2 : (Real.log (x:ℝ)) ^ ((((20:ℕ)):ℝ) + (Asave - Kaxis))
        ≤ (Real.log (x:ℝ)) ^ (((200000000 : ℕ)) : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hlog1 hexp
    have h3 : (Real.log (x:ℝ)) ^ (((200000000 : ℕ)) : ℝ) ≤ (x:ℝ) ^ ((1:ℝ)/48) := by
      rw [Real.rpow_natCast]
      exact hx₀L x hxL
    have h4 : (x:ℝ) ^ ((1:ℝ)/48) ≤ (x:ℝ) ^ ((1:ℝ)/24) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith : (1:ℝ) ≤ (x:ℝ)) (by norm_num)
    rw [h1]
    exact le_trans h2 (le_trans h3 h4)
  have hϑL : varthetaOf x Asave * (Real.log (x:ℝ))^Kaxis
      = (Real.log (x:ℝ))^(Kaxis - Asave) := by
    have h1 : (Real.log (x:ℝ))^Kaxis = (Real.log (x:ℝ))^((Kaxis:ℝ)) := by
      rw [Real.rpow_natCast]
    have h2 : varthetaOf x Asave = (Real.log (x:ℝ))^(-Asave) := rfl
    rw [h1, h2, ← Real.rpow_add hlogpos]
    congr 1
    ring
  have hkey : (Real.log (x:ℝ))^(20:ℕ) * (x:ℝ)^(-((1:ℝ)/24))
      ≤ varthetaOf x Asave * (Real.log (x:ℝ))^Kaxis := by
    rw [hϑL]
    have hlp0 : 0 < (Real.log (x:ℝ))^(Asave - Kaxis) := Real.rpow_pos_of_pos hlogpos _
    have hxp0 : 0 < (x:ℝ)^((1:ℝ)/24) := Real.rpow_pos_of_pos hxpos _
    have hpos : 0 < (Real.log (x:ℝ))^(Asave - Kaxis) * (x:ℝ)^((1:ℝ)/24) := mul_pos hlp0 hxp0
    have hone : ((Real.log (x:ℝ))^(20:ℕ) * (x:ℝ)^(-((1:ℝ)/24)))
          * ((Real.log (x:ℝ))^(Asave - Kaxis) * (x:ℝ)^((1:ℝ)/24))
        ≤ (x:ℝ)^((1:ℝ)/24) := by
      have h1 : (x:ℝ)^(-((1:ℝ)/24)) * (x:ℝ)^((1:ℝ)/24) = 1 := by
        rw [← Real.rpow_add hxpos]
        norm_num
      calc ((Real.log (x:ℝ))^(20:ℕ) * (x:ℝ)^(-((1:ℝ)/24)))
            * ((Real.log (x:ℝ))^(Asave - Kaxis) * (x:ℝ)^((1:ℝ)/24))
          = ((Real.log (x:ℝ))^(20:ℕ) * (Real.log (x:ℝ))^(Asave - Kaxis))
            * ((x:ℝ)^(-((1:ℝ)/24)) * (x:ℝ)^((1:ℝ)/24)) := by ring
        _ = ((Real.log (x:ℝ))^(20:ℕ) * (Real.log (x:ℝ))^(Asave - Kaxis)) * 1 := by rw [h1]
        _ ≤ (x:ℝ)^((1:ℝ)/24) * 1 := mul_le_mul_of_nonneg_right hlogpow (by norm_num)
        _ = (x:ℝ)^((1:ℝ)/24) := mul_one _
    have htwo : (Real.log (x:ℝ))^(Kaxis - Asave)
          * ((Real.log (x:ℝ))^(Asave - Kaxis) * (x:ℝ)^((1:ℝ)/24))
        = (x:ℝ)^((1:ℝ)/24) := by
      have h3 : (Real.log (x:ℝ))^(Kaxis - Asave) * (Real.log (x:ℝ))^(Asave - Kaxis) = 1 := by
        rw [← Real.rpow_add hlogpos]
        rw [show (Kaxis - Asave) + (Asave - Kaxis) = 0 by ring, Real.rpow_zero]
      rw [← mul_assoc, h3, one_mul]
    exact le_of_mul_le_mul_right (hone.trans (le_of_eq htwo.symm)) hpos
  -- assembly
  have hL20 : (Real.log (x:ℝ))^(20:ℕ) ≤ (Real.log (x:ℝ))^Kaxis :=
    pow_le_pow_right₀ hlog1 (by norm_num [Work.FIRed6Axis.Kaxis])
  have hSumNnn : 0 ≤ (∑ j : Fin (JJN x N + 1), (MnOf x N j : ℝ) ^ ((3 : ℝ) / 4)) :=
    Finset.sum_nonneg (fun j _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hFacBlog : 0 ≤ FacB * (Real.log (x:ℝ))^(20:ℕ) :=
    mul_nonneg hFacBnn (pow_nonneg (le_of_lt hlogpos) 20)
  have hmain1 : (∑ j : Fin (JJN x N + 1),
        ((MnOf x N j : ℝ) ^ ((3 : ℝ) / 4) * (N : ℝ) ^ (-(1 : ℝ) / 4)
          * (varthetaOf x Asave * (N : ℝ) + Real.sqrt (N : ℝ)
              + (N : ℝ) ^ ((5 : ℝ) / 6) + (N : ℝ) ^ ((2 : ℝ) / 3) + 1)
          * (Real.log (2 + (N : ℝ))) ^ (20 : ℕ)))
      ≤ c1 * ((x:ℝ)^((3:ℝ)/4) * (varthetaOf x Asave + 4 * (x:ℝ)^(-((1:ℝ)/24)))
            * (Real.log (x:ℝ))^(20:ℕ)) := by
    rw [hsplit]
    have hs1 : Fac * (∑ j : Fin (JJN x N + 1), (MnOf x N j : ℝ) ^ ((3 : ℝ) / 4))
        ≤ (FacB * (Real.log (x:ℝ))^(20:ℕ)) * (c1 * ((x:ℝ)/(N:ℝ)) ^ ((3:ℝ)/4)) :=
      mul_le_mul hFac_le hgeom hSumNnn hFacBlog
    refine le_trans hs1 ?_
    have hbr : varthetaOf x Asave + (N:ℝ)^(-((1:ℝ)/2)) + (N:ℝ)^(-((1:ℝ)/6))
          + (N:ℝ)^(-((1:ℝ)/3)) + (N:ℝ)^(-((1:ℝ)))
        ≤ varthetaOf x Asave + 4 * (x:ℝ)^(-((1:ℝ)/24)) := by
      linarith [hdec1, hdec2, hdec3, hdec4]
    have h1 : (FacB * (Real.log (x:ℝ))^(20:ℕ)) * (c1 * ((x:ℝ)/(N:ℝ)) ^ ((3:ℝ)/4))
        = c1 * ((FacB * ((x:ℝ)/(N:ℝ)) ^ ((3:ℝ)/4)) * (Real.log (x:ℝ))^(20:ℕ)) := by ring
    rw [h1, hfacid]
    have hLp0 : 0 ≤ (Real.log (x:ℝ))^(20:ℕ) := pow_nonneg (le_of_lt hlogpos) 20
    have hx34n : 0 ≤ (x:ℝ)^((3:ℝ)/4) := Real.rpow_nonneg hxn0 ((3:ℝ)/4)
    have hinner : (x:ℝ)^((3:ℝ)/4) * (varthetaOf x Asave + (N:ℝ)^(-((1:ℝ)/2))
          + (N:ℝ)^(-((1:ℝ)/6)) + (N:ℝ)^(-((1:ℝ)/3)) + (N:ℝ)^(-((1:ℝ))))
        ≤ (x:ℝ)^((3:ℝ)/4) * (varthetaOf x Asave + 4 * (x:ℝ)^(-((1:ℝ)/24))) :=
      mul_le_mul_of_nonneg_left hbr hx34n
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hinner hLp0) hc1pos.le
  have hmain2 : c1 * ((x:ℝ)^((3:ℝ)/4) * (varthetaOf x Asave + 4 * (x:ℝ)^(-((1:ℝ)/24)))
        * (Real.log (x:ℝ))^(20:ℕ))
      ≤ K * varthetaOf x Asave * (x:ℝ)^((3:ℝ)/4) * (Real.log (x:ℝ))^Kaxis := by
    have hLpnn : 0 ≤ (Real.log (x:ℝ))^Kaxis := pow_nonneg (le_of_lt hlogpos) _
    have hx34n : 0 ≤ (x:ℝ)^((3:ℝ)/4) := Real.rpow_nonneg hxn0 _
    have hxinv : 0 ≤ (x:ℝ)^(-((1:ℝ)/24)) := Real.rpow_nonneg hxn0 _
    have e : c1 * ((x:ℝ)^((3:ℝ)/4) * (varthetaOf x Asave + 4 * (x:ℝ)^(-((1:ℝ)/24)))
          * (Real.log (x:ℝ))^(20:ℕ))
        = c1 * (x:ℝ)^((3:ℝ)/4) * varthetaOf x Asave * (Real.log (x:ℝ))^(20:ℕ)
          + 4 * c1 * (x:ℝ)^((3:ℝ)/4) * (x:ℝ)^(-((1:ℝ)/24)) * (Real.log (x:ℝ))^(20:ℕ) := by ring
    rw [e]
    have t1 : c1 * (x:ℝ)^((3:ℝ)/4) * varthetaOf x Asave * (Real.log (x:ℝ))^(20:ℕ)
        ≤ c1 * (x:ℝ)^((3:ℝ)/4) * varthetaOf x Asave * (Real.log (x:ℝ))^Kaxis := by
      have h := mul_le_mul_of_nonneg_left hL20
        (mul_nonneg (mul_nonneg hc1pos.le hx34n) hϑnn)
      nlinarith [h]
    have t2 : 4 * c1 * (x:ℝ)^((3:ℝ)/4) * (x:ℝ)^(-((1:ℝ)/24)) * (Real.log (x:ℝ))^(20:ℕ)
        ≤ 4 * c1 * (x:ℝ)^((3:ℝ)/4) * varthetaOf x Asave * (Real.log (x:ℝ))^Kaxis := by
      have h1 : (4 * c1 * (x:ℝ)^((3:ℝ)/4)) * ((Real.log (x:ℝ))^(20:ℕ) * (x:ℝ)^(-((1:ℝ)/24)))
          ≤ (4 * c1 * (x:ℝ)^((3:ℝ)/4)) * (varthetaOf x Asave * (Real.log (x:ℝ))^Kaxis) :=
        mul_le_mul_of_nonneg_left hkey (by positivity)
      nlinarith [h1]
    have t3 : c1 * (x:ℝ)^((3:ℝ)/4) * varthetaOf x Asave * (Real.log (x:ℝ))^Kaxis
          + 4 * c1 * (x:ℝ)^((3:ℝ)/4) * varthetaOf x Asave * (Real.log (x:ℝ))^Kaxis
        = K * varthetaOf x Asave * (x:ℝ)^((3:ℝ)/4) * (Real.log (x:ℝ))^Kaxis := by
      rw [hKdef]; ring
    linarith [t1, t2, t3]
  linarith [hmain1, hmain2]


/-- Reindexing a sum over `Fin K × {k // k ∉ S} × Fin n` as a sum over the corresponding
`Finset`-filtered angular index. -/
lemma sum_far_reindex {K K' n : ℕ} (S : Finset (Fin K')) (g : Fin K → Fin K' → Fin n → ℝ) :
    (∑ t : Fin K × {k : Fin K' // k ∉ S} × Fin n, g t.1 t.2.1.1 t.2.2)
      = ∑ i, ∑ k ∈ (Finset.univ.filter (fun k : Fin K' => k ∉ S)), ∑ j : Fin n, g i k j := by
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  rw [Fintype.sum_prod_type]
  exact (Finset.sum_subtype (Finset.univ.filter (fun k : Fin K' => k ∉ S)) (by simp)
    (fun k => ∑ j : Fin n, g i k j)).symm

/-- **The axis-aware §§4–5.2 reduction** (`Work.FIRed6Axis.ReductionAxis`, unfold it): the
conclusion of `Work.FITop4.Red6.reduction_save6_maj` with every piece in a *far* cell and one extra
near-axis error term.

NOTE (this is the corrected statement): `WindowAxisBound`'s near constant `Cnear` is now *hoisted*
outside its universal block, so it does not depend on `(x,N,Pz,Mn,C,τ,θ,ϑ,K,K',a,p,φ,q,Pa,f,S,c2,c3)`;
`hW` is equivalent to a family of per-window bounds *with the same constant*, which is exactly what
the accumulation over the ladder needs.  `Work.FIRed6Axis.window_bound_act_axis` (proved) derives it
from `NearAxisBound`.  Do not re-prove anything about the weak (inside-∃) form.

Copy the proof of `Work.FITop4.Red6.reduction_save6_maj`
(`Submission/Work/FITop4/Red6/reduction_save6_maj.lean`) and change exactly two things.

(1) The angular family must be the *explicit* partition of (5.12): prove a local variant of
`Work.FITop4.Red5.angular_partition_le0` whose statement exposes the witness
`φ k = -(π(1+θ)) + k·(πθ)`, `q k = tent (πθ)`, `K' = ⌈2/θ⌉+1` (copy that proof; the radial family
comes from `Work.FITop4.Red5.radial_pieces_flat` as in `mollifier_family`).  Let
`S := (Finset.univ : Finset (Fin K')).filter (fun k => ¬ farAngle ϑ θ (φ k))` be the *near* set
(`Work.FIRed6Axis.farAngle`); then `k ∉ S` gives `FarPiece (Pa i) (φ i)` via
`Work.FIRed6Axis.farAngle_farPiece`, and `k ∈ S` gives the near-zone containment required by
`WindowAxisBound`: for `z` with `InPolarBox (Pa i k) (φ k) z`, the `(≤)`-form of `¬ farAngle` plus
`Work.FIRed6Axis.not_farAngle_nearArg` gives `nearArg (2ϑ + 4πθ) z`, hence `nearArg (4ϑ) z` because
`4πθ ≤ ϑ` (prove `4πθ ≤ ϑ` from `Pa.hθ`, `Pa.hϑ`, `Pa.hA'` and `1 ≤ log(log x)`).  No cardinality of
`S` is needed.

(2) The per-window step is `hW : WindowAxisBound` instead of `window_bound_act`; instantiate it at
each window's data (the `T2`/`T3` hypotheses are supplied exactly as in `reduction_save6_maj`, by
`Work.FITop4.Red5.window_T2_cop_le`/`window_T2_shell_of_crux` and `window_T3_le`), and use
`hT1 : FarT1Bound` for the far Cauchy term.  Extract the single constant once
(`obtain ⟨Cnear, hCnear_pos, hWb⟩ := hW`) and use `hWb` at every window.  The piece family is then
`ι = Fin K × {k : Fin K' // k ∉ S} × Fin (JJN x N + 1)` with `Pa i = PaOrig i i.2.1 i.2.2`,
`φ i = φ i.2.1`, `β i = pieceCoeff …`; the count `Σ_i (M_iN_i)^{3/4}` over the subfamily is at most
`piece_count_window`'s count over the full family; and
`BformPiTau x N Pz C τ ≤ Σ_i √(100 M_i Dform_i) + c·(the two round-5 error terms)
+ Cnear·Σ_j (Mn_j)^{3/4}N^{-1/4}(ϑN+√N+N^{5/6}+N^{2/3}+1)(log)^{20}` with
`Σ_j (Mn_j)^{3/4} ≤ C(x/N)^{3/4}` (the ladder `Mn_j = 2^j M0N`, `MtopN = ⌊x/(2N)⌋`), i.e. the
accumulated near error is `≤ C x^{3/4}(log)^{20}(ϑ + N^{-1/2} + N^{-1/6} + N^{-1/3} + N^{-1})`,
which is `≤ ϑ x^{3/4}(log x)^{Kaxis}` for `x` large: enlarge the theorem's own threshold `x₀` (an
existential) and absorb each non-`ϑ` term with `(log x)^D ≤ x^{ε}` eventually and `N ≥ x^{1/4+η}`.
Everything else (`window_cover`, `window_error_sum`, `BformPiTau_eq_sum_window`,
`BformPiTauSmall_le2`, `BformPiTau_tauReduce`, the `τ`-reduction and the final absorption into
`θ x^{3/4}(log x)^{100} + ϑ^{3/4}x^{3/4}(log x)^{65536}`) is verbatim. -/
theorem reduction_save6_axis_of_window (hW : Work.FIRed6Axis.WindowAxisBound)
    (hT1 : Work.FIRed6Axis.FarT1Bound) : Work.FIRed6Axis.ReductionAxis := by
  unfold Work.FIRed6Axis.ReductionAxis
  obtain ⟨Cnear, hCnear_pos, hWb⟩ := hW
  obtain ⟨x₀C, hRed5C⟩ := red5numC_proof
  obtain ⟨cCop, hcCop, hCop⟩ := window_T2_cop_le
  obtain ⟨cCrux, hcCrux, hCrux⟩ := thin_annulus_Zint_count_own
  obtain ⟨cShell, hcShell, hShell⟩ := window_T2_shell_of_crux cCrux hcCrux hCrux
  obtain ⟨cSmall, hcSmall, x₀Small, hSmall⟩ := BformPiTauSmall_le2
  obtain ⟨cT3, hcT3, hT3le⟩ := window_T3_le
  obtain ⟨cTauR, hcTauR, x₀TauR, hTauReduce⟩ := BformPiTau_tauReduce
  obtain ⟨cAc, hcAc, hAc⟩ := Work.FIChain.AcountAtilC_le_const_mul_rpow
  obtain ⟨cErr, hcErr, hErr⟩ := window_error_sum
  obtain ⟨cNearK, hcNearK, x₀Near, hNearLadder⟩ := axis_near_error_ladder_le
  have hCnt_pos : 0 < 64 * ((4 : ℝ) ^ ((3 : ℝ) / 4) / ((2 : ℝ) ^ ((3 : ℝ) / 4) - 1)) := by
    apply mul_pos (by norm_num)
    apply div_pos (Real.rpow_pos_of_pos (by norm_num) _)
    have h : (1 : ℝ) < (2 : ℝ) ^ ((3 : ℝ) / 4) := Real.one_lt_rpow (by norm_num) (by norm_num)
    linarith
  set c0 : ℝ := cErr * (cCop + cShell + cT3) + (cSmall + cTauR * cAc) + Cnear * cNearK
      + 64 * ((4 : ℝ) ^ ((3 : ℝ) / 4) / ((2 : ℝ) ^ ((3 : ℝ) / 4) - 1)) + 1 with hc0def
  have hc0pos : 0 < c0 := by
    rw [hc0def]
    have h1 : 0 < cErr * (cCop + cShell + cT3) := by positivity
    have h2 : 0 < cSmall + cTauR * cAc := by positivity
    have h3 : 0 < Cnear * cNearK := by positivity
    linarith
  refine ⟨c0, hc0pos, x₀C + x₀Small + x₀TauR + x₀Near + 64, ?_⟩
  intro x N Pz C τ η hx0 hN hC hP2 hη0 hη1 hll hNlo hNhi hNhi2 hC2 hPlo hPhi hτ1 hτ2 hϑx1
  have hx0C : x₀C ≤ x := le_trans (by omega) hx0
  have hx0S : x₀Small ≤ x := le_trans (by omega) hx0
  have hx0R : x₀TauR ≤ x := le_trans (by omega) hx0
  have hx0N : x₀Near ≤ x := le_trans (by omega) hx0
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
  have hϑ1 : varthetaOf x Asave ≤ 1 := le_trans hNum.hv14 (by norm_num)
  have h4pic : 4 * Real.pi * thetaOf x Asave ≤ varthetaOf x Asave := by
    unfold thetaOf varthetaOf
    exact axis_four_pi_rpow_neg_le (Real.log (x : ℝ)) Asave (Aprime Asave)
      (by linarith [hNum.hlog4]) Asave_pos le_rfl
  have hBpos : 0 < BmaxBig η - 1 := by
    have h := BmaxBig_ge_pow31 η
    have h2 : (1 : ℝ) < (2 : ℝ) ^ (31 : ℕ) := by norm_num
    linarith
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
  obtain ⟨Pa, f₀, hPaM, hPaN, hPaC, hPaPz, hPaθ, hPaϑ, hPaτ, _, hPaFields⟩ :=
    window_family_tau x N Pz C (tauOf x Asave) η (thetaOf x Asave) (varthetaOf x Asave)
      (BmaxBig η - 1) K K' a hx3 hN hP2 hη0 hη1 hC hC2 hϑ0 hBpos hTauOf1 hTauOf rfl rfl
      hNlo hNhi2 hPlo hPhi haN ha2
      (fun j => (window_MnFactsC hNum j).1) (fun j => (window_MnFactsC hNum j).2.1)
      (fun j => (window_MnFactsC hNum j).2.2.2.2.1) (fun j => (window_MnFactsC hNum j).2.2.1)
      (fun j => (window_MnFactsC hNum j).2.2.2.2.2)
  have hM4 : ∀ i k j, 4 ≤ (Pa i k j).M := fun i k j => by
    rw [hPaM i k j]; exact_mod_cast (window_MnFactsC hNum j).2.1
  have hfam : ∃ f : Fin K → Fin K' → Fin (JJN x N + 1) → ℤ → ℝ,
      ∀ i k j, Work.FITop4.IsMajorant6 (Pa i k j) (f i k j) :=
    ⟨fun i k j => Classical.choose
        (Work.FITop4.Witness6.exists_isMajorant6_seq (Pa i k j) (hM4 i k j)),
     fun i k j => Classical.choose_spec
        (Work.FITop4.Witness6.exists_isMajorant6_seq (Pa i k j) (hM4 i k j))⟩
  obtain ⟨f, hMaj6⟩ := hfam
  have hMaj : ∀ i k j, Work.FITop3.IsMajorant (Pa i k j) (f i k j) :=
    fun i k j => Work.FITop4.IsMajorant6.toMajorant (hMaj6 i k j)
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
  -- the near angular set and its complement
  set S : Finset (Fin K') := (Finset.univ : Finset (Fin K')).filter
      (fun k => ¬ farAngle (varthetaOf x Asave) (thetaOf x Asave) (φ k)) with hSdef
  set farS : Finset (Fin K') := (Finset.univ : Finset (Fin K')).filter
      (fun k => k ∉ S) with hfarSdef
  have hfarSmem : ∀ k : Fin K', k ∈ farS ↔ k ∉ S := by
    intro k
    rw [hfarSdef]
    simp
  have hS_far : ∀ k : Fin K', k ∉ S → farAngle (varthetaOf x Asave) (thetaOf x Asave) (φ k) := by
    intro k hk
    by_contra hc
    exact hk (by rw [hSdef]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩)
  -- the near-zone containment
  have hnear : ∀ i k j, k ∈ S → ∀ z, Work.FITop4.InPolarBox (Pa i k j) (φ k) z →
      nearArg (4 * (varthetaOf x Asave)) z := by
    intro i k j hk z hz
    have hnf : ¬ farAngle (varthetaOf x Asave) (thetaOf x Asave) (φ k) := by
      rw [hSdef] at hk
      exact (Finset.mem_filter.mp hk).2
    have hzθ : Complex.arg z.toComplex ≤ φ k + 2 * Real.pi * (thetaOf x Asave) := by
      rw [← hPaθ i k j]
      exact hz.2.2.2.2
    obtain ⟨m, hm⟩ := not_farAngle_nearArg hnf (le_of_lt hθ0) (by linarith [h4pic])
      hz.2.2.2.1 hzθ
    exact ⟨m, hm⟩
  -- the small-`m` piece
  have hsmallSum := hSmall x N (M0N x N) Pz 3 C (tauOf x Asave) (varthetaOf x Asave)
    hx0S hN (by norm_num) (by norm_num) hϑ0 hNum.hv8 hϑx1 hNum.hM0le3
  -- the near term per window
  set NF : Fin (JJN x N + 1) → ℝ := fun j =>
    Cnear * (MnOf x N j : ℝ) ^ ((3 : ℝ) / 4) * (N : ℝ) ^ (-(1 : ℝ) / 4)
      * (varthetaOf x Asave * (N : ℝ) + Real.sqrt (N : ℝ)
          + (N : ℝ) ^ ((5 : ℝ) / 6) + (N : ℝ) ^ ((2 : ℝ) / 3) + 1)
      * (Real.log (2 + (N : ℝ))) ^ (20 : ℕ) with hNFdef
  -- each window
  have hwin : ∀ j : Fin (JJN x N + 1),
      (∑ m ∈ Finset.Icc (MnOf x N j + 1) (2 * MnOf x N j), Iterm x N Pz C (tauOf x Asave) m)
        ≤ (∑ i, ∑ k ∈ farS, F i k j)
          + ((max cCop cShell) * T2RHS x N (MnOf x N j) Pz (thetaOf x Asave)
              + cT3 * T3RHS x N (MnOf x N j) (thetaOf x Asave))
          + NF j := by
    intro j
    have hMf := window_MnFactsC hNum j
    have hMn1 : 1 ≤ MnOf x N j := hMf.1
    have hMnN : (N : ℝ) ≤ (MnOf x N j : ℝ) := hMf.2.2.2.1
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
    simpa only [hFdef, hNFdef, hfarSdef, add_assoc] using
      hWb x N Pz (MnOf x N j) C (tauOf x Asave) (thetaOf x Asave) (varthetaOf x Asave) K K' a p φ q
        (fun i k => Pa i k j) (fun i k => f i k j) S (max cCop cShell) cT3
        hMn1 hN hP2 hθ0 hθ1 hϑ0 hϑ1 h4pic hMnN haN
        (fun i k => hPaM i k j) (fun i k => hPaN i k j) (fun i k => hPaC i k j)
        (fun i k => hPaPz i k j) (fun i k => hPaθ i k j) (fun i k => hPaτ i k j)
        hp0 hp1 hpsup hple2N hq0 hq0z hqsup hang hpsum_le (fun i k => hMaj i k j) hT2 hT3
        (fun k hk i z hz => hnear i k j hk z hz)
  -- sum the window bounds
  have hwinSum : (∑ j : Fin (JJN x N + 1),
        ∑ m ∈ Finset.Icc (MnOf x N j + 1) (2 * MnOf x N j), Iterm x N Pz C (tauOf x Asave) m)
      ≤ (∑ i, ∑ k ∈ farS, ∑ j : Fin (JJN x N + 1), F i k j)
        + (∑ j : Fin (JJN x N + 1),
            ((max cCop cShell) * T2RHS x N (MnOf x N j) Pz (thetaOf x Asave)
              + cT3 * T3RHS x N (MnOf x N j) (thetaOf x Asave)))
        + (∑ j : Fin (JJN x N + 1), NF j) := by
    have h := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hwin j)
    have hmainEq : (∑ j : Fin (JJN x N + 1), ∑ i, ∑ k ∈ farS, F i k j)
        = ∑ i, ∑ k ∈ farS, ∑ j : Fin (JJN x N + 1), F i k j := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    have hEq : (∑ j : Fin (JJN x N + 1), ((∑ i, ∑ k ∈ farS, F i k j)
          + ((max cCop cShell) * T2RHS x N (MnOf x N j) Pz (thetaOf x Asave)
              + cT3 * T3RHS x N (MnOf x N j) (thetaOf x Asave)) + NF j))
        = (∑ i, ∑ k ∈ farS, ∑ j : Fin (JJN x N + 1), F i k j)
          + (∑ j : Fin (JJN x N + 1),
              ((max cCop cShell) * T2RHS x N (MnOf x N j) Pz (thetaOf x Asave)
                + cT3 * T3RHS x N (MnOf x N j) (thetaOf x Asave)))
          + (∑ j : Fin (JJN x N + 1), NF j) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hmainEq]
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
  -- the near error accumulated
  have hnearSum : (∑ j : Fin (JJN x N + 1), NF j)
      ≤ Cnear * cNearK * ((varthetaOf x Asave) * (x : ℝ) ^ ((3 : ℝ) / 4)
          * (Real.log (x : ℝ)) ^ Kaxis) := by
    have hl := hNearLadder x N Pz η hx0N hN hη0 hNum hNlo
    have hsumEq : (∑ j : Fin (JJN x N + 1), NF j)
        = Cnear * (∑ j : Fin (JJN x N + 1),
            ((MnOf x N j : ℝ) ^ ((3 : ℝ) / 4) * (N : ℝ) ^ (-(1 : ℝ) / 4)
              * (varthetaOf x Asave * (N : ℝ) + Real.sqrt (N : ℝ)
                  + (N : ℝ) ^ ((5 : ℝ) / 6) + (N : ℝ) ^ ((2 : ℝ) / 3) + 1)
              * (Real.log (2 + (N : ℝ))) ^ (20 : ℕ))) := by
      rw [hNFdef, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hsumEq]
    have h1 := mul_le_mul_of_nonneg_left hl (le_of_lt hCnear_pos)
    refine le_trans h1 ?_
    exact le_of_eq (by ring)
  -- the covering decomposition
  have hBsumpi : BformPiTau x N Pz C (tauOf x Asave)
      = ∑ m ∈ Finset.Icc 1 (2 * MtopN x N), Iterm x N Pz C (tauOf x Asave) m :=
    BformPiTau_eq_sum_window x N Pz C (tauOf x Asave) hN (by exact_mod_cast hNum.htop)
      (by have h : 2 * N ≤ MtopN x N := by exact_mod_cast hNum.hMtopge2N
          omega)
  have hcover := window_cover x N (Iterm x N Pz C (tauOf x Asave))
    (fun m => Iterm_nonneg x N Pz C (tauOf x Asave) m)
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
      ≤ (∑ i, ∑ k ∈ farS, ∑ j : Fin (JJN x N + 1), F i k j)
        + cErr * (cCop + cShell + cT3) * ((thetaOf x Asave) * (x : ℝ) ^ ((3 : ℝ) / 4)
            * (Real.log (x : ℝ)) ^ (100 : ℕ))
        + cSmall * ((varthetaOf x Asave) ^ ((3 : ℝ) / 4) * (x : ℝ) ^ ((3 : ℝ) / 4)
            * (Real.log (x : ℝ)) ^ (65536 : ℕ))
        + (Cnear * cNearK) * ((varthetaOf x Asave) * (x : ℝ) ^ ((3 : ℝ) / 4)
            * (Real.log (x : ℝ)) ^ Kaxis) := by
    have hsmallB : (∑ m ∈ Finset.Icc 1 (M0N x N), Iterm x N Pz C (tauOf x Asave) m)
        ≤ cSmall * ((varthetaOf x Asave) ^ ((3 : ℝ) / 4) * (x : ℝ) ^ ((3 : ℝ) / 4)
            * (Real.log (x : ℝ)) ^ (65536 : ℕ)) := by
      refine le_trans hsmallSum ?_
      rw [Real.mul_rpow hϑ0.le (Nat.cast_nonneg x)]
      exact le_of_eq (by ring)
    rw [hBsumpi]
    refine le_trans hcover ?_
    linarith [hladder, hwinSum, herrSum', hsmallB, hnearSum]
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
      ≤ (∑ i, ∑ k ∈ farS, ∑ j : Fin (JJN x N + 1), F i k j)
        + cErr * (cCop + cShell + cT3) * ((thetaOf x Asave) * (x : ℝ) ^ ((3 : ℝ) / 4)
            * (Real.log (x : ℝ)) ^ (100 : ℕ))
        + (cSmall + cTauR * cAc) * ((varthetaOf x Asave) ^ ((3 : ℝ) / 4) * (x : ℝ) ^ ((3 : ℝ) / 4)
            * (Real.log (x : ℝ)) ^ (65536 : ℕ))
        + (Cnear * cNearK) * ((varthetaOf x Asave) * (x : ℝ) ^ ((3 : ℝ) / 4)
            * (Real.log (x : ℝ)) ^ Kaxis) := by
    have hmid : BformPiTau x N Pz C (tauOf x Asave)
          + cTauR * Work.FITop.AcountAtil x * (Real.log (x : ℝ)) ^ (-(Asave - 200000))
        ≤ (∑ i, ∑ k ∈ farS, ∑ j : Fin (JJN x N + 1), F i k j)
          + cErr * (cCop + cShell + cT3) * ((thetaOf x Asave) * (x : ℝ) ^ ((3 : ℝ) / 4)
              * (Real.log (x : ℝ)) ^ (100 : ℕ))
          + (cSmall + cTauR * cAc) * ((varthetaOf x Asave) ^ ((3 : ℝ) / 4) * (x : ℝ) ^ ((3 : ℝ) / 4)
              * (Real.log (x : ℝ)) ^ (65536 : ℕ))
          + (Cnear * cNearK) * ((varthetaOf x Asave) * (x : ℝ) ^ ((3 : ℝ) / 4)
              * (Real.log (x : ℝ)) ^ Kaxis) := by
      have hX : cSmall * ((varthetaOf x Asave) ^ ((3 : ℝ) / 4) * (x : ℝ) ^ ((3 : ℝ) / 4)
              * (Real.log (x : ℝ)) ^ (65536 : ℕ))
            + (cTauR * cAc) * ((varthetaOf x Asave) ^ ((3 : ℝ) / 4) * (x : ℝ) ^ ((3 : ℝ) / 4)
              * (Real.log (x : ℝ)) ^ (65536 : ℕ))
          = (cSmall + cTauR * cAc) * ((varthetaOf x Asave) ^ ((3 : ℝ) / 4) * (x : ℝ) ^ ((3 : ℝ) / 4)
              * (Real.log (x : ℝ)) ^ (65536 : ℕ)) := by ring
      linarith [hassem, hErrtau, hX]
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
  have hnearterm0 : 0 ≤ (varthetaOf x Asave) * (x : ℝ) ^ ((3 : ℝ) / 4)
      * (Real.log (x : ℝ)) ^ Kaxis := by
    have h1 : 0 ≤ (x : ℝ) ^ ((3 : ℝ) / 4) := Real.rpow_nonneg (by positivity) _
    have h2 : 0 ≤ (Real.log (x : ℝ)) ^ Kaxis := pow_nonneg (le_of_lt hlogpos) _
    positivity
  have h64le : 64 * ((4 : ℝ) ^ ((3 : ℝ) / 4) / ((2 : ℝ) ^ ((3 : ℝ) / 4) - 1)) ≤ c0 := by
    rw [hc0def]
    have h1 : 0 ≤ cErr * (cCop + cShell + cT3) := by positivity
    have h2 : 0 ≤ cSmall + cTauR * cAc := by positivity
    have h3 : 0 ≤ Cnear * cNearK := by positivity
    linarith
  have hAsmall : cErr * (cCop + cShell + cT3) ≤ c0 := by
    rw [hc0def]
    have h1 : 0 ≤ cSmall + cTauR * cAc := by positivity
    have h2 : 0 ≤ Cnear * cNearK := by positivity
    have h3 : 0 ≤ 64 * ((4 : ℝ) ^ ((3 : ℝ) / 4) / ((2 : ℝ) ^ ((3 : ℝ) / 4) - 1)) := le_of_lt hCnt_pos
    linarith
  have hAbig : cSmall + cTauR * cAc ≤ c0 := by
    rw [hc0def]
    have h1 : 0 ≤ cErr * (cCop + cShell + cT3) := by positivity
    have h2 : 0 ≤ Cnear * cNearK := by positivity
    have h3 : 0 ≤ 64 * ((4 : ℝ) ^ ((3 : ℝ) / 4) / ((2 : ℝ) ^ ((3 : ℝ) / 4) - 1)) := le_of_lt hCnt_pos
    linarith
  have hAnear : Cnear * cNearK ≤ c0 := by
    rw [hc0def]
    have h1 : 0 ≤ cErr * (cCop + cShell + cT3) := by positivity
    have h2 : 0 ≤ cSmall + cTauR * cAc := by positivity
    have h3 : 0 ≤ 64 * ((4 : ℝ) ^ ((3 : ℝ) / 4) / ((2 : ℝ) ^ ((3 : ℝ) / 4) - 1)) := le_of_lt hCnt_pos
    linarith
  have hfinal : BformPiTau x N Pz C τ
      ≤ (∑ i, ∑ k ∈ farS, ∑ j : Fin (JJN x N + 1), F i k j)
        + c0 * ((thetaOf x Asave) * (x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log (x : ℝ)) ^ (100 : ℕ)
            + (varthetaOf x Asave) ^ ((3 : ℝ) / 4) * (x : ℝ) ^ ((3 : ℝ) / 4)
              * (Real.log (x : ℝ)) ^ (65536 : ℕ))
        + c0 * (varthetaOf x Asave) * (x : ℝ) ^ ((3 : ℝ) / 4)
            * (Real.log (x : ℝ)) ^ Kaxis := by
    have h1 : cErr * (cCop + cShell + cT3) * ((thetaOf x Asave) * (x : ℝ) ^ ((3 : ℝ) / 4)
            * (Real.log (x : ℝ)) ^ (100 : ℕ))
        ≤ c0 * ((thetaOf x Asave) * (x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log (x : ℝ)) ^ (100 : ℕ)) :=
      mul_le_mul_of_nonneg_right hAsmall hθterm0
    have h2 : (cSmall + cTauR * cAc) * ((varthetaOf x Asave) ^ ((3 : ℝ) / 4)
            * (x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log (x : ℝ)) ^ (65536 : ℕ))
        ≤ c0 * ((varthetaOf x Asave) ^ ((3 : ℝ) / 4)
            * (x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log (x : ℝ)) ^ (65536 : ℕ)) :=
      mul_le_mul_of_nonneg_right hAbig hϑterm0
    have h3 : (Cnear * cNearK) * ((varthetaOf x Asave) * (x : ℝ) ^ ((3 : ℝ) / 4)
            * (Real.log (x : ℝ)) ^ Kaxis)
        ≤ c0 * ((varthetaOf x Asave) * (x : ℝ) ^ ((3 : ℝ) / 4)
            * (Real.log (x : ℝ)) ^ Kaxis) :=
      mul_le_mul_of_nonneg_right hAnear hnearterm0
    linarith [hcombined, h1, h2, h3]
  have hmain_reindex : (∑ i, ∑ k ∈ farS, ∑ j : Fin (JJN x N + 1), F i k j)
      = (∑ t : Fin K × {k : Fin K' // k ∉ S} × Fin (JJN x N + 1), F t.1 t.2.1.1 t.2.2) := by
    rw [sum_far_reindex S (fun i k j => F i k j)]
  rw [hmain_reindex] at hfinal
  -- count conjunct
  have hcount := piece_count_window x N (thetaOf x Asave) K K' a hN hx1 hθ0 hθ1
    hNum.hpowJJN haN ha2 hKle hK'le
  have hcount_sub : (∑ i, ∑ k ∈ farS, ∑ j : Fin (JJN x N + 1),
        (((MnOf x N j : ℝ) * a i) ^ ((3 : ℝ) / 4)))
      ≤ 64 * ((4 : ℝ) ^ ((3 : ℝ) / 4) / ((2 : ℝ) ^ ((3 : ℝ) / 4) - 1)) * (thetaOf x Asave) ^ (-(2 : ℝ))
          * (x : ℝ) ^ ((3 : ℝ) / 4) := by
    refine le_trans ?_ hcount
    apply Finset.sum_le_sum
    intro i _
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun k _ _ => Finset.sum_nonneg (fun j _ => Real.rpow_nonneg
        (mul_nonneg (Nat.cast_nonneg _) (le_trans (by positivity) (haN i))) ((3 : ℝ) / 4)))
  have hcount' : (∑ t : Fin K × {k : Fin K' // k ∉ S} × Fin (JJN x N + 1),
        (((Pa t.1 t.2.1.1 t.2.2).M * (Pa t.1 t.2.1.1 t.2.2).N) ^ ((3 : ℝ) / 4)))
      ≤ c0 * (thetaOf x Asave) ^ (-(2 : ℝ)) * (x : ℝ) ^ ((3 : ℝ) / 4) := by
    rw [sum_far_reindex S (fun i k j => ((Pa i k j).M * (Pa i k j).N) ^ ((3 : ℝ) / 4))]
    simp only [hPaM, hPaN]
    refine le_trans hcount_sub ?_
    have hA : (0:ℝ) ≤ (thetaOf x Asave) ^ (-(2 : ℝ)) * (x : ℝ) ^ ((3 : ℝ) / 4) :=
      mul_nonneg (Real.rpow_nonneg hθ0.le _) (Real.rpow_nonneg (by positivity) _)
    have hB := mul_le_mul_of_nonneg_right h64le hA
    calc 64 * ((4 : ℝ) ^ ((3 : ℝ) / 4) / ((2 : ℝ) ^ ((3 : ℝ) / 4) - 1)) * (thetaOf x Asave) ^ (-(2 : ℝ))
          * (x : ℝ) ^ ((3 : ℝ) / 4)
        = (64 * ((4 : ℝ) ^ ((3 : ℝ) / 4) / ((2 : ℝ) ^ ((3 : ℝ) / 4) - 1)))
            * ((thetaOf x Asave) ^ (-(2 : ℝ)) * (x : ℝ) ^ ((3 : ℝ) / 4)) := by ring
      _ ≤ c0 * ((thetaOf x Asave) ^ (-(2 : ℝ)) * (x : ℝ) ^ ((3 : ℝ) / 4)) := hB
      _ = c0 * (thetaOf x Asave) ^ (-(2 : ℝ)) * (x : ℝ) ^ ((3 : ℝ) / 4) := by ring
  refine ⟨Fin K × {k : Fin K' // k ∉ S} × Fin (JJN x N + 1), inferInstance,
    (fun t : Fin K × {k : Fin K' // k ∉ S} × Fin (JJN x N + 1) => Pa t.1 t.2.1.1 t.2.2),
    (fun t : Fin K × {k : Fin K' // k ∉ S} × Fin (JJN x N + 1) => f t.1 t.2.1.1 t.2.2),
    (fun t : Fin K × {k : Fin K' // k ∉ S} × Fin (JJN x N + 1) => φ t.2.1.1),
    (fun t : Fin K × {k : Fin K' // k ∉ S} × Fin (JJN x N + 1) =>
      pieceCoeff (Pa t.1 t.2.1.1 t.2.2) (φ t.2.1.1) (q t.2.1.1) (p t.1)),
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hPaFields t.1 t.2.1.1 t.2.2
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9,
      by rw [hPaN t.1 t.2.1.1 t.2.2]; exact haN t.1,
      by rw [hPaN t.1 t.2.1.1 t.2.2]; exact ha2 t.1⟩
  · intro t; exact hMaj6 t.1 t.2.1.1 t.2.2
  · intro t
    refine pieceCoeff_isBetaCoeff (hqcd t.2.1.1) (hq0 t.2.1.1) (hq1 t.2.1.1) ?_ ?_
      (hpcd t.1) (hp0 t.1) (hp1 t.1) ?_ ?_
    · intro α hα
      obtain ⟨h1, h2⟩ := hqsup t.2.1.1 α hα
      exact ⟨h1, by rw [hPaθ t.1 t.2.1.1 t.2.2]; exact h2⟩
    · intro jn hj α
      rw [hPaθ t.1 t.2.1.1 t.2.2]
      exact hqder t.2.1.1 jn hj α
    · intro u hu
      obtain ⟨h1, h2⟩ := hpsup t.1 u hu
      refine ⟨?_, ?_⟩
      · rw [hPaN t.1 t.2.1.1 t.2.2]; exact h1
      · rw [hPaθ t.1 t.2.1.1 t.2.2, hPaN t.1 t.2.1.1 t.2.2]; exact h2
    · intro jn hj u
      rw [hPaθ t.1 t.2.1.1 t.2.2, hPaN t.1 t.2.1.1 t.2.2]
      exact hpder t.1 jn hj u
  · intro t
    have hk : t.2.1.1 ∉ S := t.2.1.2
    have hfa : farAngle (varthetaOf x Asave) (thetaOf x Asave) (φ t.2.1.1) := hS_far t.2.1.1 hk
    have hfa' : farAngle (Pa t.1 t.2.1.1 t.2.2).ϑ (Pa t.1 t.2.1.1 t.2.2).θ (φ t.2.1.1) := by
      rw [hPaϑ t.1 t.2.1.1 t.2.2, hPaθ t.1 t.2.1.1 t.2.2]
      exact hfa
    exact farAngle_farPiece hfa'
  · exact hcount'
  · simpa only [hFdef, hL100def, hL65536def] using hfinal

end

end Work.FIRed6Axis
