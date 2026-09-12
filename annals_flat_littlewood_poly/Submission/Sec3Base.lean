import Mathlib
import Submission.RS
import Submission.Sec3Defs
import Submission.Sec3H_defs
import Submission.Sec3H_deriv
import Submission.Sec3H_lbounds
import Submission.Sec3H_origin
import Submission.Sec3H_intervals
import Submission.Sec3_c_bridge
import Submission.Sec3_c_expand
import Submission.ArcFamily

/-! Section 3, Theorem 2.3 of the paper (quadrant family for the cosine polynomial). -/

noncomputable section
open scoped Polynomial BigOperators
open Polynomial Complex

set_option autoImplicit false

namespace Submission
namespace Sec3

/-- Cosine-bad-cell threshold on good cells: `2^(-7)·η^3·√(2^(t+1))`. -/
def goodCellBound (t q : ℕ) : ℝ :=
  (1 : ℝ) / 2 ^ 7 * ((2 * (Sec3H.T t : ℝ) * Real.pi / (q : ℝ)) ^ 3) * Real.sqrt (2 ^ (t + 1) : ℝ)

/-- `η := 2·T·π/q`, cell width in `x = 2Tθ`-space. -/
def eta (t q : ℕ) : ℝ := (2 * (Sec3H.T t : ℝ) * Real.pi) / (q : ℝ)

/-- The `Re H`-threshold `η^3/2^7`. -/
def cellThresh (t q : ℕ) : ℝ := (eta t q) ^ 3 / (2 ^ 7 : ℝ)

/-- `goodCellBound = √(2^(t+1)) · cellThresh`. -/
lemma goodCellBound_eq (t q : ℕ) :
    goodCellBound t q = Real.sqrt (2 ^ (t + 1) : ℝ) * cellThresh t q := by
  unfold goodCellBound cellThresh eta
  ring

/-! ## 1. Basic arithmetic context -/

/-- `m_t ≥ 2^(t+11)`. -/
lemma mt_ge_2pow (t : ℕ) : 2 ^ (t + 11) ≤ m_t t := by
  unfold m_t
  have h1 : 1 ≤ 2 ^ t := by
    exact pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2) (Nat.zero_le t)
  omega

/-- `0 < q` from `2^400 ≤ q`. -/
lemma q_pos_of_large (q : ℕ) (hq0 : 2 ^ 400 ≤ q) : 0 < q := by
  have h1 : 0 < (2 ^ 400 : ℕ) := by positivity
  omega

/-- η = π·2^(t+11)/q. -/
lemma eta_eq (t q : ℕ) : eta t q = ((2 : ℝ) ^ (t + 11) * Real.pi) / (q : ℝ) := by
  unfold eta Sec3H.T
  rw [show (2 * ((2 ^ (t + 10) : ℕ) : ℝ)) = ((2 : ℝ) ^ (t + 11)) by
    norm_num
    rw [show t + 11 = (t + 10) + 1 by omega]
    rw [pow_succ']
    ring]

/-- `η > 0`. -/
lemma eta_pos (t q : ℕ) (hq0 : 2 ^ 400 ≤ q) : 0 < eta t q := by
  have hq : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (q_pos_of_large q hq0)
  have hT0 : 0 < (Sec3H.T t : ℝ) := by
    unfold Sec3H.T
    exact_mod_cast (pow_pos (by norm_num : 0 < 2) (t + 10))
  unfold eta
  exact div_pos (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hT0) Real.pi_pos) hq

/-- `η ≤ π/2^43`. -/
lemma eta_le_pi_div (t q : ℕ) (hq0 : 2 ^ 400 ≤ q) (hlo : 2 ^ 43 * m_t t ≤ q) :
    eta t q ≤ Real.pi / 2 ^ 43 := by
  have hmt : 2 ^ (t + 11) ≤ m_t t := mt_ge_2pow t
  have hle : 2 ^ 43 * 2 ^ (t + 11) ≤ q := le_trans (Nat.mul_le_mul_left (2 ^ 43) hmt) hlo
  have hcast : ((2 ^ 43 * 2 ^ (t + 11) : ℕ) : ℝ) ≤ (q : ℝ) := by exact_mod_cast hle
  have hnum : ((2 ^ 43 * 2 ^ (t + 11) : ℕ) : ℝ) = (2 ^ 43 : ℝ) * ((2 : ℝ) ^ (t + 11)) := by norm_num
  have hmul : (2 ^ 43 : ℝ) * ((2 : ℝ) ^ (t + 11)) ≤ (q : ℝ) := by
    rw [← hnum]
    exact hcast
  have hd : ((2 : ℝ) ^ (t + 11)) / (q : ℝ) ≤ (1 : ℝ) / 2 ^ 43 := by
    have hq : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (q_pos_of_large q hq0)
    rw [div_le_div_iff₀ hq (by positivity : (0 : ℝ) < 2 ^ 43)]
    ring_nf at hmul ⊢
    exact hmul
  calc
    eta t q = (((2 : ℝ) ^ (t + 11)) / (q : ℝ)) * Real.pi := by
        rw [eta_eq]
        ring
    _ ≤ (1 / 2 ^ 43 : ℝ) * Real.pi := by
        exact mul_le_mul_of_nonneg_right hd Real.pi_pos.le
    _ = Real.pi / 2 ^ 43 := by ring

/-- `η ≤ 2^-13`. -/
lemma eta_le_2n13 (t q : ℕ) (hq0 : 2 ^ 400 ≤ q) (hlo : 2 ^ 43 * m_t t ≤ q) :
    eta t q ≤ (1 : ℝ) / 2 ^ 13 := by
  have hpi : Real.pi ≤ (4 : ℝ) := le_of_lt Real.pi_lt_four
  calc
    eta t q ≤ Real.pi / 2 ^ 43 := eta_le_pi_div t q hq0 hlo
    _ ≤ (4 : ℝ) / 2 ^ 43 := div_le_div_of_nonneg_right hpi (by positivity : (0 : ℝ) ≤ 2 ^ 43)
    _ ≤ (1 : ℝ) / 2 ^ 13 := by norm_num

/-- `1024·η ≤ 1/8`. -/
lemma eta_buffer (t q : ℕ) (hq0 : 2 ^ 400 ≤ q) (hlo : 2 ^ 43 * m_t t ≤ q) :
    (1024 : ℝ) * eta t q ≤ (1 : ℝ) / 8 := by
  have h1 : (1024 : ℝ) * eta t q ≤ (1024 : ℝ) * ((1 : ℝ) / 2 ^ 13) :=
    mul_le_mul_of_nonneg_left (eta_le_2n13 t q hq0 hlo) (by norm_num)
  have h2 : (1024 : ℝ) * ((1 : ℝ) / 2 ^ 13) ≤ (1 : ℝ) / 8 := by norm_num
  exact le_trans h1 h2

/-- `cellThresh ≤ 1/2`. -/
lemma cellThresh_le_half (t q : ℕ) (hq0 : 2 ^ 400 ≤ q) (hlo : 2 ^ 43 * m_t t ≤ q) :
    cellThresh t q ≤ (1 : ℝ) / 2 := by
  have hη0 : 0 ≤ eta t q := le_of_lt (eta_pos t q hq0)
  have hη3 : eta t q ^ 3 ≤ ((1 : ℝ) / 2 ^ 13) ^ 3 := by
    exact pow_le_pow_left₀ hη0 (eta_le_2n13 t q hq0 hlo) 3
  unfold cellThresh
  calc
    eta t q ^ 3 / (2 ^ 7 : ℝ) ≤ ((1 / 2 ^ 13) ^ 3) / (2 ^ 7 : ℝ) := by
        exact div_le_div_of_nonneg_right hη3 (by norm_num)
    _ ≤ (1 : ℝ) / 2 := by norm_num

/-- `Re H ≥ 1/2` on a buffer implies the cell threshold. -/
lemma thresh_of_half {t q : ℕ} (hq0 : 2 ^ 400 ≤ q) (hlo : 2 ^ 43 * m_t t ≤ q)
    (x : ℝ) (h : (1 / 2 : ℝ) ≤ (Sec3H.H t x).re) : cellThresh t q ≤ |(Sec3H.H t x).re| := by
  have hle : cellThresh t q ≤ (1 / 2 : ℝ) := cellThresh_le_half t q hq0 hlo
  calc
    cellThresh t q ≤ (1 / 2 : ℝ) := hle
    _ ≤ (Sec3H.H t x).re := h
    _ ≤ |(Sec3H.H t x).re| := le_abs_self _




/-! ## 2. Cells, buffers, no-7-consecutive-bad -/

/-- x-cell `[jη,(j+1)η]`. -/
def cell (t q : ℕ) (j : ℕ) : Set ℝ :=
  Set.Icc (((j : ℕ) : ℝ) * eta t q) ((((j + 1 : ℕ) : ℝ) * eta t q))

/-- A cell is good when `cellThresh ≤ |Re H|` everywhere on it. -/
def cellGood (t q : ℕ) (j : ℕ) : Prop :=
  ∀ x : ℝ, x ∈ cell t q j → cellThresh t q ≤ |(Sec3H.H t x).re|

/-- `H` is continuous. -/
lemma cont_H (t : ℕ) : Continuous (Sec3H.H t) := by
  have h := Sec3H.contDiff_H (n := (0 : WithTop ℕ∞)) t
  exact h.continuous

/-- `Re ∘ H t` is continuous. -/
lemma cont_ReH (t : ℕ) : Continuous (fun x : ℝ => (Sec3H.H t x).re) := by
  have h1 : Continuous (fun z : ℂ => z.re) := by
    change Continuous (Complex.reCLM : ℂ → ℝ)
    exact Complex.reCLM.continuous
  exact h1.comp (cont_H t)

/-- `|c t|` is continuous. -/
lemma cont_abs_c (t : ℕ) : Continuous (fun θ : ℝ => |c t θ|) := by
  have hx : Continuous (fun θ : ℝ => 2 * (Sec3H.T t : ℝ) * θ) := by fun_prop
  have h1 : Continuous (fun θ : ℝ => (Sec3H.H t (2 * (Sec3H.T t : ℝ) * θ)).re) := (cont_ReH t).comp hx
  have h2 : Continuous (fun θ : ℝ => Real.sqrt (2 ^ (t + 1) : ℝ) * (Sec3H.H t (2 * (Sec3H.T t : ℝ) * θ)).re) := by
    exact continuous_const.mul h1
  have h3 : Continuous (fun θ : ℝ => |Real.sqrt (2 ^ (t + 1) : ℝ) * (Sec3H.H t (2 * (Sec3H.T t : ℝ) * θ)).re|) := h2.abs
  convert h3 using 1
  funext θ
  rw [Sec3H.c_eq_sqrt_re_H]

/-- `T > 0`. -/
lemma T_pos_real (t : ℕ) : (0 : ℝ) < (Sec3H.T t : ℝ) := by
  unfold Sec3H.T
  positivity

/-- From a Re-H threshold bound at `x = 2Tθ` to the cosine bound. -/
lemma abs_c_of_thresh {t q : ℕ} {θ : ℝ}
    (h : cellThresh t q ≤ |(Sec3H.H t (2 * (Sec3H.T t : ℝ) * θ)).re|) :
    goodCellBound t q ≤ |c t θ| := by
  have hsq : 0 ≤ Real.sqrt (2 ^ (t + 1) : ℝ) := Real.sqrt_nonneg _
  calc
    goodCellBound t q = Real.sqrt (2 ^ (t + 1) : ℝ) * cellThresh t q := by rw [goodCellBound_eq]
    _ ≤ Real.sqrt (2 ^ (t + 1) : ℝ) * |(Sec3H.H t (2 * (Sec3H.T t : ℝ) * θ)).re| := by
        exact mul_le_mul_of_nonneg_left h hsq
    _ = |Real.sqrt (2 ^ (t + 1) : ℝ) * (Sec3H.H t (2 * (Sec3H.T t : ℝ) * θ)).re| := by
        rw [abs_mul, abs_of_nonneg hsq]
    _ = |c t θ| := by rw [Sec3H.c_eq_sqrt_re_H]

/-- Bad point of `Re H` implies small cosine. -/
lemma c_abs_lt_of_reH_lt {t q : ℕ} {θ : ℝ}
    (h : |(Sec3H.H t (2 * (Sec3H.T t : ℝ) * θ)).re| < cellThresh t q) :
    |c t θ| < goodCellBound t q := by
  have hsq : 0 ≤ Real.sqrt (2 ^ (t + 1) : ℝ) := Real.sqrt_nonneg _
  have hsqpos : 0 < Real.sqrt (2 ^ (t + 1) : ℝ) := by
    exact Real.sqrt_pos.2 (by positivity)
  have h1 : Real.sqrt (2 ^ (t + 1) : ℝ) * |(Sec3H.H t (2 * (Sec3H.T t : ℝ) * θ)).re| <
      Real.sqrt (2 ^ (t + 1) : ℝ) * cellThresh t q := by
    exact mul_lt_mul_of_pos_left h hsqpos
  have h2 : |Real.sqrt (2 ^ (t + 1) : ℝ) * (Sec3H.H t (2 * (Sec3H.T t : ℝ) * θ)).re| =
      Real.sqrt (2 ^ (t + 1) : ℝ) * |(Sec3H.H t (2 * (Sec3H.T t : ℝ) * θ)).re| := by
    rw [abs_mul, abs_of_nonneg hsq]
  calc
    |c t θ| = |Real.sqrt (2 ^ (t + 1) : ℝ) * (Sec3H.H t (2 * (Sec3H.T t : ℝ) * θ)).re| := by
        rw [Sec3H.c_eq_sqrt_re_H]
    _ = Real.sqrt (2 ^ (t + 1) : ℝ) * |(Sec3H.H t (2 * (Sec3H.T t : ℝ) * θ)).re| := h2
    _ < Real.sqrt (2 ^ (t + 1) : ℝ) * cellThresh t q := h1
    _ = goodCellBound t q := by rw [goodCellBound_eq]

/-- A cell inside `[-1/8,1/8]` (near `x = 0`) is good. -/
lemma cellGood_zero_buf (t q : ℕ) (j : ℕ) (ht : Odd t) (hq0 : 2 ^ 400 ≤ q)
    (hlo : 2 ^ 43 * m_t t ≤ q)
    (hj : ((j + 1 : ℕ) : ℝ) * eta t q ≤ (1 : ℝ) / 8) : cellGood t q j := by
  intro x hx
  have hxge : ((j : ℕ) : ℝ) * eta t q ≤ x := hx.1
  have hxle : x ≤ (((j + 1 : ℕ) : ℝ) * eta t q) := hx.2
  have hnn : 0 ≤ x := le_trans (mul_nonneg (by positivity : (0 : ℝ) ≤ (j : ℝ)) (le_of_lt (eta_pos t q hq0))) hxge
  have hxabs : |x| ≤ (1 : ℝ) / 8 := by
    rw [abs_of_nonneg hnn]
    exact le_trans hxle hj
  exact thresh_of_half hq0 hlo x (Sec3H.H_re_ge_half_near_zero t ht x hxabs)

/-- A cell within `1/8` of `x = Tπ` is good. -/
lemma cellGood_Tpi_buf (t q : ℕ) (j : ℕ) (ht : Odd t) (hq0 : 2 ^ 400 ≤ q)
    (hlo : 2 ^ 43 * m_t t ≤ q)
    (hj1 : ((j : ℕ) : ℝ) * eta t q ≥ (Sec3H.T t : ℝ) * Real.pi - (1 : ℝ) / 8)
    (hj2 : (((j + 1 : ℕ) : ℝ) * eta t q) ≤ (Sec3H.T t : ℝ) * Real.pi + (1 : ℝ) / 8) :
    cellGood t q j := by
  intro x hx
  have hxge : ((j : ℕ) : ℝ) * eta t q ≤ x := hx.1
  have hxle : x ≤ (((j + 1 : ℕ) : ℝ) * eta t q) := hx.2
  have hd1 : -(1 : ℝ) / 8 ≤ x - (Sec3H.T t : ℝ) * Real.pi := by nlinarith [hj1, hxge]
  have hd2 : x - (Sec3H.T t : ℝ) * Real.pi ≤ (1 : ℝ) / 8 := by nlinarith [hj2, hxle]
  have hxabs : |x - (Sec3H.T t : ℝ) * Real.pi| ≤ (1 : ℝ) / 8 := by
    rw [abs_le]
    constructor
    · linarith
    · linarith
  exact thresh_of_half hq0 hlo x (Sec3H.H_re_ge_half_near_Tpi t ht x hxabs)

/-- Cells `j ≤ 1023` near `x=0` are good. -/
lemma cellGood_small (t q : ℕ) (j : ℕ) (ht : Odd t) (hq0 : 2 ^ 400 ≤ q)
    (hlo : 2 ^ 43 * m_t t ≤ q) (hj : j + 1 ≤ 1024) : cellGood t q j := by
  apply cellGood_zero_buf t q j ht hq0 hlo
  have hη0 : 0 ≤ eta t q := le_of_lt (eta_pos t q hq0)
  have hcast : ((j + 1 : ℕ) : ℝ) ≤ (1024 : ℝ) := by exact_mod_cast hj
  calc
    ((j + 1 : ℕ) : ℝ) * eta t q ≤ (1024 : ℝ) * eta t q := by
        exact mul_le_mul_of_nonneg_right hcast hη0
    _ ≤ (1 : ℝ) / 8 := eta_buffer t q hq0 hlo

/-- A bad cell has index at least 1024. -/
lemma bad_index_ge (t q : ℕ) (j : ℕ) (ht : Odd t) (hq0 : 2 ^ 400 ≤ q)
    (hlo : 2 ^ 43 * m_t t ≤ q) (hj : ¬ cellGood t q j) : 1024 ≤ j := by
  by_contra h
  have hj' : j + 1 ≤ 1024 := by omega
  exact hj (cellGood_small t q j ht hq0 hlo hj')

/-- A bad cell in the quadrant (index `< q/2`) stays at least 1024 cells away from `q/2`. -/
lemma bad_index_q2 (t q : ℕ) (j : ℕ) (ht : Odd t) (hq0 : 2 ^ 400 ≤ q)
    (hlo : 2 ^ 43 * m_t t ≤ q) (hj : ¬ cellGood t q j) (hjq : j < q / 2) :
    (j : ℝ) < (q : ℝ) / 2 - 1024 := by
  by_contra h
  have hnot : (q : ℝ) / 2 - 1024 ≤ (j : ℝ) := le_of_not_gt h
  have hq : 0 < q := q_pos_of_large q hq0
  have hqη : (q : ℝ) * eta t q = 2 * (Sec3H.T t : ℝ) * Real.pi := by
    unfold eta
    have hqne : (q : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hq)
    field_simp [hqne]
  have h2j : 2 * (j + 1) ≤ q := by
    have h1 : j + 1 ≤ q / 2 := by omega
    have h2 : 2 * (q / 2) ≤ q := by omega
    omega
  have hcast : ((j + 1 : ℕ) : ℝ) ≤ (q : ℝ) / 2 := by
    have hc : (2 : ℝ) * ((j + 1 : ℕ) : ℝ) ≤ (q : ℝ) := by exact_mod_cast h2j
    nlinarith
  have hη0 : 0 ≤ eta t q := le_of_lt (eta_pos t q hq0)
  have hqhalf : (q : ℝ) / 2 - (j : ℝ) ≤ 1024 := by nlinarith [hnot]
  have hdist : ((Sec3H.T t : ℝ) * Real.pi - ((j : ℕ) : ℝ) * eta t q) ≤ (1 : ℝ) / 8 := by
    have hsplit : ((Sec3H.T t : ℝ) * Real.pi - ((j : ℕ) : ℝ) * eta t q) =
        ((q : ℝ) / 2 - (j : ℝ)) * eta t q := by
      nlinarith [hqη]
    rw [hsplit]
    calc
      ((q : ℝ) / 2 - (j : ℝ)) * eta t q ≤ 1024 * eta t q := by
          exact mul_le_mul_of_nonneg_right hqhalf hη0
      _ ≤ (1 : ℝ) / 8 := eta_buffer t q hq0 hlo
  have h1 : ((j : ℕ) : ℝ) * eta t q ≥ (Sec3H.T t : ℝ) * Real.pi - (1 : ℝ) / 8 := by
    nlinarith [hdist]
  have h2 : (((j + 1 : ℕ) : ℝ) * eta t q) ≤ (Sec3H.T t : ℝ) * Real.pi + (1 : ℝ) / 8 := by
    have h3 : ((j + 1 : ℕ) : ℝ) * eta t q ≤ (q : ℝ) / 2 * eta t q := by
        exact mul_le_mul_of_nonneg_right hcast hη0
    nlinarith [h3, hqη]
  exact hj (cellGood_Tpi_buf t q j ht hq0 hlo h1 h2)

/-- Any 7 consecutive cells contain a good cell. -/
lemma exists_good_in_seven (t q : ℕ) (j : ℕ) (hq0 : 2 ^ 400 ≤ q)
    (hlo : 2 ^ 43 * m_t t ≤ q) : ∃ m : Fin 7, cellGood t q (j + m.1) := by
  have hηsmall : eta t q < (1 : ℝ) / 2 ^ 11 := by
    have h := eta_le_2n13 t q hq0 hlo
    have hc : (1 : ℝ) / 2 ^ 13 < (1 : ℝ) / 2 ^ 11 := by norm_num
    exact lt_of_le_of_lt h hc
  rcases Sec3H.intervals_nice t (η := eta t q) (a := (j : ℝ) * eta t q)
      (eta_pos t q hq0) hηsmall with ⟨m, hm⟩
  refine ⟨m, ?_⟩
  intro x hx
  have h1 : ((j + m.1 : ℕ) : ℝ) * eta t q = (j : ℝ) * eta t q + (m : ℕ) * eta t q := by
    rw [Nat.cast_add]
    ring
  have h2 : ((j + m.1 + 1 : ℕ) : ℝ) * eta t q =
      (j : ℝ) * eta t q + (((m : ℕ) + 1) * eta t q) := by
    rw [show (j + m.1 + 1 : ℕ) = (j + 1) + m.1 by omega]
    rw [Nat.cast_add, Nat.cast_add, Nat.cast_one]
    ring
  unfold cell at hx
  rw [h1, h2] at hx
  have hmain := hm x hx
  exact hmain

/-- No 7 consecutive cells can all be bad. -/
lemma no_seven_bad (t q : ℕ) (j : ℕ) (hq0 : 2 ^ 400 ≤ q)
    (hlo : 2 ^ 43 * m_t t ≤ q) : ¬ ∀ m : Fin 7, ¬ cellGood t q (j + m.1) := by
  intro h
  rcases exists_good_in_seven t q j hq0 hlo with ⟨m, hg⟩
  exact h m hg

/-- A run of consecutive bad cells has length at most 6. -/
lemma run_len_le (t q : ℕ) (s e : ℕ) (hq0 : 2 ^ 400 ≤ q) (hlo : 2 ^ 43 * m_t t ≤ q)
    (hbad : ∀ j : ℕ, s ≤ j → j ≤ e → ¬ cellGood t q j) : e ≤ s + 5 := by
  by_contra h
  have h6 : s + 6 ≤ e := by omega
  have h7 : ¬ ∀ m : Fin 7, ¬ cellGood t q (s + m.1) := no_seven_bad t q s hq0 hlo
  apply h7
  intro m
  exact hbad (s + m.1) (by omega) (by omega)


/-! ## 3. Zero-counting of `c(θ) = b` on `(0,π)` -/

/-- `θ ↦ zθ θ = e^{2iθ}` is injective on `(0,π)`. -/
lemma zθ_inj {a b : ℝ} (ha0 : 0 < a) (hab : a < Real.pi) (hb0 : 0 < b) (hbb : b < Real.pi)
    (h : zθ a = zθ b) : a = b := by
  unfold zθ eθ at h
  let E : ℝ → ℂ := fun x => Complex.exp (((x : ℝ) : ℂ) * Complex.I)
  have hE : E (2 * a) = E (2 * b) := by simpa [E] using h
  have hEne : ∀ x : ℝ, E x ≠ 0 := by
    intro x
    unfold E
    exact Complex.exp_ne_zero _
  have h1 : E (2 * a - 2 * b) = 1 := by
    have hstep : E (2 * a - 2 * b) = E (2 * a) * E (-(2 * b)) := by
      unfold E
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [hstep]
    have hinv : E (-(2 * b)) = (E (2 * b))⁻¹ := by
      unfold E
      rw [← Complex.exp_neg]
      congr 1
      push_cast
      ring
    rw [hinv, hE]
    field_simp [hEne (2 * b)]
  have h2 : Complex.exp (((2 * a - 2 * b : ℝ) : ℂ) * Complex.I) = 1 := by
    simpa [E] using h1
  rcases (Complex.exp_eq_one_iff.mp h2) with ⟨n, hn⟩
  have hI : (Complex.I : ℂ) ≠ 0 := by norm_num
  have hc : (((2 * (a - b) : ℝ) : ℂ)) = (((n : ℤ) : ℂ) * (2 * (Real.pi : ℂ))) := by
    apply mul_right_cancel₀ hI
    calc
      ((2 * (a - b) : ℝ) : ℂ) * Complex.I = ((2 * a - 2 * b : ℝ) : ℂ) * Complex.I := by congr 1; ring
      _ = ((n : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by simpa [mul_assoc, mul_left_comm, mul_comm] using hn
      _ = (((n : ℤ) : ℂ) * (2 * (Real.pi : ℂ))) * Complex.I := by ring
  have hre := congrArg Complex.re hc
  have hmain : 2 * (a - b) = (n : ℝ) * (2 * Real.pi) := by
    simpa using hre
  have hmain' : a - b = (n : ℝ) * Real.pi := by nlinarith
  by_cases hn0 : n = 0
  · rw [hn0] at hmain'
    norm_num at hmain'
    linarith
  · exfalso
    have hnn : 1 ≤ |(n : ℤ)| := Int.one_le_abs hn0
    have h2' : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast hnn
    have hge : Real.pi ≤ |(n : ℝ)| * Real.pi := by
      have hm := mul_le_mul_of_nonneg_right h2' Real.pi_pos.le
      simpa [mul_comm] using hm
    have habs : |a - b| = |(n : ℝ)| * Real.pi := by
      rw [hmain', abs_mul]
      congr 1
      exact abs_of_nonneg Real.pi_pos.le
    have hablt : |a - b| < Real.pi := by
      rw [abs_lt]
      constructor <;> linarith
    nlinarith

/-- `m_t t = 2T + 2^t − 1`. -/
lemma m_t_eq_T (t : ℕ) : m_t t = 2 * Sec3H.T t + 2 ^ t - 1 := by
  unfold m_t Sec3H.T
  have h : 2 ^ (t + 11) = 2 * 2 ^ (t + 10) := by
    rw [show t + 11 = (t + 10) + 1 by omega]
    rw [pow_succ']
  rw [h]

/-- `T ≥ 1`. -/
lemma T_ge_one (t : ℕ) : 1 ≤ Sec3H.T t := by
  unfold Sec3H.T
  exact pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2) (Nat.zero_le (t + 10))

/-- complex-form polynomial `C(u) = Σ_r P_r u^{T+r} + Σ_r Q_r u^{2T+r}`. -/
def cpoly (t : ℕ) : ℂ[X] :=
  (∑ r ∈ Finset.range (2 ^ t),
      Polynomial.C ((RudinShapiro.P t).coeff r) * Polynomial.X ^ (Sec3H.T t + r)) +
  (∑ r ∈ Finset.range (2 ^ t),
      Polynomial.C ((RudinShapiro.Q t).coeff r) * Polynomial.X ^ (2 * Sec3H.T t + r))

/-- conjugate-reversed polynomial: `conjpoly(u) = u^D·conj(C(u))` on `|u|=1`. -/
def conjpoly (t : ℕ) : ℂ[X] :=
  (∑ r ∈ Finset.range (2 ^ t),
      Polynomial.C (star ((RudinShapiro.P t).coeff r)) * Polynomial.X ^ (Sec3H.T t + 2 ^ t - 1 - r)) +
  (∑ r ∈ Finset.range (2 ^ t),
      Polynomial.C (star ((RudinShapiro.Q t).coeff r)) * Polynomial.X ^ (2 ^ t - 1 - r))

/-- evaluation of `cpoly` at `u`. -/
lemma cpoly_eval (t : ℕ) (u : ℂ) :
    (cpoly t).eval u =
      (∑ r ∈ Finset.range (2 ^ t), (RudinShapiro.P t).coeff r * u ^ (Sec3H.T t + r)) +
      (∑ r ∈ Finset.range (2 ^ t), (RudinShapiro.Q t).coeff r * u ^ (2 * Sec3H.T t + r)) := by
  unfold cpoly
  simp [Polynomial.eval_add, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X]

/-- `c(θ) = Re (cpoly.eval (zθ θ))`. -/
lemma c_eq_cpoly_re (t : ℕ) (θ : ℝ) :
    (c t θ : ℂ) = ((cpoly t).eval (zθ θ)).re := by
  rw [c_eq_re_complex_sum]
  rw [← cpoly_eval t (zθ θ)]

/-- evaluation of `conjpoly` at `u`. -/
lemma conjpoly_eval (t : ℕ) (u : ℂ) :
    (conjpoly t).eval u =
      (∑ r ∈ Finset.range (2 ^ t),
        star ((RudinShapiro.P t).coeff r) * u ^ (Sec3H.T t + 2 ^ t - 1 - r)) +
      (∑ r ∈ Finset.range (2 ^ t),
        star ((RudinShapiro.Q t).coeff r) * u ^ (2 ^ t - 1 - r)) := by
  unfold conjpoly
  simp [Polynomial.eval_add, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X]

/-- `u * conj u = 1` for unit-modulus `u`. -/
lemma unit_mul_star {u : ℂ} (hu : ‖u‖ = 1) : u * star u = 1 := by
  have h1 : u * star u = (Complex.normSq u : ℂ) := by simpa using (Complex.mul_conj u)
  rw [h1]
  have h2 : Complex.normSq u = ‖u‖ ^ 2 := Complex.normSq_eq_norm_sq u
  rw [h2, hu]
  norm_num

/-- `star u = u⁻¹` on the unit circle. -/
lemma unit_star_inv {u : ℂ} (hu : ‖u‖ = 1) : star u = u⁻¹ := by
  have h1 : star u * u = 1 := by simpa [mul_comm] using (unit_mul_star hu)
  exact eq_inv_of_mul_eq_one_left h1

/-- `u^D·conj(u^k) = u^{D−k}` for unit `u`, `k ≤ D`. -/
lemma unit_pow_star_pow {u : ℂ} (hu : ‖u‖ = 1) (k D : ℕ) (hk : k ≤ D) :
    u ^ D * star (u ^ k) = u ^ (D - k) := by
  have hstar : star u = u⁻¹ := unit_star_inv hu
  calc
    u ^ D * star (u ^ k) = u ^ D * (star u) ^ k := by rw [star_pow]
    _ = u ^ D * (u⁻¹) ^ k := by rw [hstar]
    _ = u ^ (D - k) := by
      have hD : D = (D - k) + k := by omega
      have hcancel : u ^ k * (u⁻¹) ^ k = 1 := by
        have h1 : u * u⁻¹ = 1 := by
          have hne : u ≠ 0 := by
            intro hz
            have h2 : ‖(0 : ℂ)‖ = 1 := by simpa [hz] using hu
            norm_num at h2
          exact mul_inv_cancel₀ hne
        rw [← mul_pow, h1]
        norm_num
      calc
        u ^ D * (u⁻¹) ^ k = u ^ ((D - k) + k) * (u⁻¹) ^ k := by rw [← hD]
        _ = (u ^ (D - k) * u ^ k) * (u⁻¹) ^ k := by rw [pow_add]
        _ = u ^ (D - k) * (u ^ k * (u⁻¹) ^ k) := by rw [← mul_assoc]
        _ = u ^ (D - k) * 1 := by rw [hcancel]
        _ = u ^ (D - k) := by rw [mul_one]

/-- `u^D·conj(a·u^k) = conj(a)·u^{D−k}` for unit `u`, `k ≤ D`. -/
lemma unit_mul_pow_star {u : ℂ} (hu : ‖u‖ = 1) (a : ℂ) (k D : ℕ) (hk : k ≤ D) :
    u ^ D * star (a * u ^ k) = star a * u ^ (D - k) := by
  calc
    u ^ D * star (a * u ^ k) = u ^ D * (star (u ^ k) * star a) := by rw [star_mul]
    _ = (u ^ D * star (u ^ k)) * star a := by ring
    _ = u ^ (D - k) * star a := by rw [unit_pow_star_pow hu k D hk]
    _ = star a * u ^ (D - k) := by ring

/-- exponent identity for the P-block: `D − (T+r) = T + 2^t − 1 − r`. -/
lemma expo_eq_P (t r : ℕ) (hr : r < 2 ^ t) :
    m_t t - (Sec3H.T t + r) = Sec3H.T t + 2 ^ t - 1 - r := by
  rw [m_t_eq_T]
  omega

/-- exponent identity for the Q-block: `D − (2T+r) = 2^t − 1 − r`. -/
lemma expo_eq_Q (t r : ℕ) (hr : r < 2 ^ t) :
    m_t t - (2 * Sec3H.T t + r) = 2 ^ t - 1 - r := by
  rw [m_t_eq_T]
  omega

/-- `u^D·conj(C(u)) = conjpoly(u)` for unit `u` (`D := m_t`). -/
lemma conjpoly_eval_unit (t : ℕ) {u : ℂ} (hu : ‖u‖ = 1) :
    (conjpoly t).eval u = u ^ (m_t t) * star ((cpoly t).eval u) := by
  rw [conjpoly_eval, cpoly_eval]
  have hsumP : (∑ r ∈ Finset.range (2 ^ t), star ((RudinShapiro.P t).coeff r) * u ^ (Sec3H.T t + 2 ^ t - 1 - r)) =
      u ^ (m_t t) * star (∑ r ∈ Finset.range (2 ^ t), (RudinShapiro.P t).coeff r * u ^ (Sec3H.T t + r)) := by
    rw [star_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    have hr' : r < 2 ^ t := Finset.mem_range.mp hr
    have hk : Sec3H.T t + r ≤ m_t t := by
      rw [m_t_eq_T]
      omega
    calc
      star ((RudinShapiro.P t).coeff r) * u ^ (Sec3H.T t + 2 ^ t - 1 - r)
          = star ((RudinShapiro.P t).coeff r) * u ^ (m_t t - (Sec3H.T t + r)) := by
              rw [← expo_eq_P t r hr']
      _ = u ^ (m_t t) * star ((RudinShapiro.P t).coeff r * u ^ (Sec3H.T t + r)) := by
              exact (unit_mul_pow_star hu ((RudinShapiro.P t).coeff r) (Sec3H.T t + r) (m_t t) hk).symm
  have hsumQ : (∑ r ∈ Finset.range (2 ^ t), star ((RudinShapiro.Q t).coeff r) * u ^ (2 ^ t - 1 - r)) =
      u ^ (m_t t) * star (∑ r ∈ Finset.range (2 ^ t), (RudinShapiro.Q t).coeff r * u ^ (2 * Sec3H.T t + r)) := by
    rw [star_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    have hr' : r < 2 ^ t := Finset.mem_range.mp hr
    have hk : 2 * Sec3H.T t + r ≤ m_t t := by
      rw [m_t_eq_T]
      omega
    calc
      star ((RudinShapiro.Q t).coeff r) * u ^ (2 ^ t - 1 - r)
          = star ((RudinShapiro.Q t).coeff r) * u ^ (m_t t - (2 * Sec3H.T t + r)) := by
              rw [← expo_eq_Q t r hr']
      _ = u ^ (m_t t) * star ((RudinShapiro.Q t).coeff r * u ^ (2 * Sec3H.T t + r)) := by
              exact (unit_mul_pow_star hu ((RudinShapiro.Q t).coeff r) (2 * Sec3H.T t + r) (m_t t) hk).symm
  rw [star_add, mul_add, hsumP, hsumQ]

/-- `w + conj w = 2·Re w`. -/
lemma two_re_add_conj (w : ℂ) : w + star w = (2 : ℂ) * (w.re : ℂ) := by
  apply Complex.ext
  · simp
    ring
  · simp

/-- coefficient of a finite sum of polynomials. -/
lemma coeff_finset_sum (s : Finset ℕ) (f : ℕ → ℂ[X]) (N : ℕ) :
    (∑ r ∈ s, f r).coeff N = ∑ r ∈ s, (f r).coeff N := by
  rw [show (∑ r ∈ s, f r) = s.sum f by rfl]
  refine Finset.induction_on s ?base ?step
  · simp
  · intro a s has ih
    rw [Finset.sum_insert has, Finset.sum_insert has, Polynomial.coeff_add, ih]



/-- `G(u) := u^D(C(u) − b) + u^D·conj(C(u) − b)`, `D := m_t t`. -/
def zpoly (t : ℕ) (b : ℝ) : ℂ[X] :=
  Polynomial.X ^ (m_t t) * cpoly t + conjpoly t -
    Polynomial.C (((2 * b : ℝ) : ℂ)) * Polynomial.X ^ (m_t t)

/-- Evaluation of `zpoly` on the unit circle. -/
lemma zpoly_eval (t : ℕ) (b : ℝ) {u : ℂ} (hu : ‖u‖ = 1) :
    (zpoly t b).eval u =
      u ^ (m_t t) * ((cpoly t).eval u + star ((cpoly t).eval u) - ((2 * b : ℝ) : ℂ)) := by
  unfold zpoly
  simp [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_X, conjpoly_eval_unit t hu]
  ring_nf

/-- `c(θ) = b` makes `u = zθ θ` a root of `zpoly t b`. -/
lemma zpoly_eval_of_c_eq (t : ℕ) (b : ℝ) (θ : ℝ) (h : c t θ = b) :
    (zpoly t b).eval (zθ θ) = 0 := by
  have hu : ‖zθ θ‖ = 1 := norm_zθ θ
  rw [zpoly_eval t b hu]
  have hmain : (cpoly t).eval (zθ θ) + star ((cpoly t).eval (zθ θ)) - ((2 * b : ℝ) : ℂ) = 0 := by
    have hc := c_eq_cpoly_re t θ
    have hre' : ((cpoly t).eval (zθ θ)).re = c t θ := by
      exact (Complex.ofReal_injective hc).symm
    have hw := two_re_add_conj ((cpoly t).eval (zθ θ))
    rw [hre'] at hw
    have hw1 : (cpoly t).eval (zθ θ) + star ((cpoly t).eval (zθ θ)) = (2 : ℂ) * (b : ℂ) := by
      simpa [h] using hw
    rw [hw1]
    norm_num
  rw [hmain]
  ring

/-- degree bound for a sum of monomials of exponent `≤ D`. -/
lemma block_natDegree_le {s : Finset ℕ} (c : ℕ → ℂ) (e : ℕ → ℕ) (D : ℕ)
    (he : ∀ r ∈ s, e r ≤ D) :
    (∑ r ∈ s, Polynomial.C (c r) * Polynomial.X ^ (e r)).natDegree ≤ D := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro N hN
  rw [coeff_finset_sum]
  apply Finset.sum_eq_zero
  intro r hr
  rw [Polynomial.coeff_C_mul_X_pow]
  have he' : e r < N := lt_of_le_of_lt (he r hr) hN
  simp [ne_of_gt he']

/-- `natDegree (cpoly t) ≤ m_t t`. -/
lemma cpoly_natDegree_le (t : ℕ) : (cpoly t).natDegree ≤ m_t t := by
  unfold cpoly
  apply le_trans (Polynomial.natDegree_add_le _ _)
  apply max_le
  · apply block_natDegree_le
    intro r hr
    rw [m_t_eq_T]
    have hr' : r < 2 ^ t := Finset.mem_range.mp hr
    omega
  · apply block_natDegree_le
    intro r hr
    rw [m_t_eq_T]
    have hr' : r < 2 ^ t := Finset.mem_range.mp hr
    omega

/-- `natDegree (conjpoly t) ≤ m_t t`. -/
lemma conjpoly_natDegree_le (t : ℕ) : (conjpoly t).natDegree ≤ m_t t := by
  unfold conjpoly
  apply le_trans (Polynomial.natDegree_add_le _ _)
  apply max_le
  · apply block_natDegree_le
    intro r hr
    rw [m_t_eq_T]
    have hr' : r < 2 ^ t := Finset.mem_range.mp hr
    omega
  · apply block_natDegree_le
    intro r hr
    rw [m_t_eq_T]
    have hr' : r < 2 ^ t := Finset.mem_range.mp hr
    omega

/-- `natDegree (X^D·cpoly) ≤ 2·m_t`. -/
lemma X_mul_cpoly_natDegree_le (t : ℕ) :
    (Polynomial.X ^ (m_t t) * cpoly t).natDegree ≤ 2 * m_t t := by
  have h1 := Polynomial.natDegree_mul_le (p := Polynomial.X ^ (m_t t)) (q := cpoly t)
  rw [Polynomial.natDegree_X_pow] at h1
  nlinarith [h1, cpoly_natDegree_le t]

/-- `natDegree (zpoly t b) ≤ 2·m_t t`. -/
lemma zpoly_natDegree_le (t : ℕ) (b : ℝ) : (zpoly t b).natDegree ≤ 2 * m_t t := by
  unfold zpoly
  have h3 := Polynomial.natDegree_C_mul_X_pow_le (((2 * b : ℝ) : ℂ)) (m_t t)
  calc
    (Polynomial.X ^ (m_t t) * cpoly t + conjpoly t -
        Polynomial.C (((2 * b : ℝ) : ℂ)) * Polynomial.X ^ (m_t t)).natDegree
        ≤ max (Polynomial.X ^ (m_t t) * cpoly t + conjpoly t).natDegree
            (Polynomial.C (((2 * b : ℝ) : ℂ)) * Polynomial.X ^ (m_t t)).natDegree :=
            Polynomial.natDegree_sub_le _ _
    _ ≤ 2 * m_t t := by
        apply max_le
        · apply le_trans (Polynomial.natDegree_add_le _ _)
          apply max_le
          · exact X_mul_cpoly_natDegree_le t
          · exact le_trans (conjpoly_natDegree_le t) (by omega)
        · exact le_trans h3 (by omega)

/-- `(P t).coeff 0 ≠ 0`. -/
lemma P_coeff_ne_zero (t : ℕ) : (RudinShapiro.P t).coeff 0 ≠ 0 := by
  rcases (RudinShapiro.P_coeff_mem t 0 (by positivity : 0 < 2 ^ t)) with h | h
  · rw [h]; norm_num
  · rw [h]; norm_num

/-- `(cpoly t).coeff T = (P t).coeff 0`. -/
lemma cpoly_coeff_T (t : ℕ) : (cpoly t).coeff (Sec3H.T t) = (RudinShapiro.P t).coeff 0 := by
  unfold cpoly
  rw [Polynomial.coeff_add, coeff_finset_sum, coeff_finset_sum]
  have hs1 : (∑ r ∈ Finset.range (2 ^ t),
      (Polynomial.C ((RudinShapiro.P t).coeff r) * Polynomial.X ^ (Sec3H.T t + r)).coeff (Sec3H.T t))
      = (RudinShapiro.P t).coeff 0 := by
    rw [Finset.sum_eq_single 0]
    · simp
    · intro b hb hb0
      rw [Polynomial.coeff_C_mul_X_pow]
      simp [hb0]
    · intro h0not
      have h0 : 0 ∈ Finset.range (2 ^ t) := by simpa using (pow_pos (by norm_num : 0 < 2) t)
      exact False.elim (h0not h0)
  have hs2 : (∑ r ∈ Finset.range (2 ^ t),
      (Polynomial.C ((RudinShapiro.Q t).coeff r) * Polynomial.X ^ (2 * Sec3H.T t + r)).coeff (Sec3H.T t)) = 0 := by
    apply Finset.sum_eq_zero
    intro r hr
    rw [Polynomial.coeff_C_mul_X_pow]
    have hf : ¬ Sec3H.T t = 2 * Sec3H.T t + r := by
      have hT1 : 1 ≤ Sec3H.T t := T_ge_one t
      omega
    simp [hf]
  rw [hs1, hs2]
  simp

/-- coefficient of `zpoly` at `m_t + T` equals `(P t).coeff 0`. -/
lemma zpoly_coeff_mt_T (t : ℕ) (b : ℝ) :
    (zpoly t b).coeff (m_t t + Sec3H.T t) = (RudinShapiro.P t).coeff 0 := by
  unfold zpoly
  rw [Polynomial.coeff_sub, Polynomial.coeff_add]
  have hc1 : (Polynomial.X ^ (m_t t) * cpoly t).coeff (m_t t + Sec3H.T t) = (cpoly t).coeff (Sec3H.T t) := by
    have hcm : (cpoly t * Polynomial.X ^ (m_t t)).coeff (Sec3H.T t + m_t t) = (cpoly t).coeff (Sec3H.T t) := by
      exact Polynomial.coeff_mul_X_pow (p := cpoly t) (n := m_t t) (d := Sec3H.T t)
    have hX : Polynomial.X ^ (m_t t) * cpoly t = cpoly t * Polynomial.X ^ (m_t t) := by ring
    rw [hX]
    rwa [show Sec3H.T t + m_t t = m_t t + Sec3H.T t by omega] at hcm
  have hc2 : (conjpoly t).coeff (m_t t + Sec3H.T t) = 0 := by
    exact Polynomial.coeff_eq_zero_of_natDegree_lt
      (lt_of_le_of_lt (conjpoly_natDegree_le t) (by
        have hT1 : 1 ≤ Sec3H.T t := T_ge_one t
        omega))
  have hc3 : (Polynomial.C (((2 * b : ℝ) : ℂ)) * Polynomial.X ^ (m_t t)).coeff (m_t t + Sec3H.T t) = 0 := by
    rw [Polynomial.coeff_C_mul_X_pow]
    have hT0 : Sec3H.T t ≠ 0 := by
      have hT1 : 1 ≤ Sec3H.T t := T_ge_one t
      omega
    simp [hT0]
  rw [hc1, hc2, hc3, cpoly_coeff_T]
  norm_num

/-- `zpoly t b` is nonzero. -/
lemma zpoly_ne_zero (t : ℕ) (b : ℝ) : zpoly t b ≠ 0 := by
  intro h
  have hc := congrArg (fun p : ℂ[X] => p.coeff (m_t t + Sec3H.T t)) h
  rw [zpoly_coeff_mt_T] at hc
  have hp : (RudinShapiro.P t).coeff 0 ≠ 0 := P_coeff_ne_zero t
  exact hp hc

/-- If `c = b` on a finite set inside `(0,π)`, its cardinality is `≤ 2·m_t`. -/
lemma zero_count (t : ℕ) (b : ℝ) (S : Finset ℝ)
    (hS : ∀ θ ∈ S, θ ∈ Set.Ioo 0 Real.pi) (hz : ∀ θ ∈ S, c t θ = b) :
    S.card ≤ 2 * m_t t := by
  let u : ℝ → ℂ := fun θ => zθ θ
  have himg : (S.image u).card = S.card := by
    apply Finset.card_image_of_injOn
    intro a ha b hb h
    exact zθ_inj (hS a ha).1 (hS a ha).2 (hS b hb).1 (hS b hb).2 h
  have hroot : ∀ θ ∈ S, (zpoly t b).eval (u θ) = 0 := by
    intro θ hθ
    exact zpoly_eval_of_c_eq t b θ (hz θ hθ)
  have hsub : S.image u ⊆ (zpoly t b).roots.toFinset := by
    intro w hw
    rcases Finset.mem_image.mp hw with ⟨θ, hθ, rfl⟩
    have hne : (zpoly t b) ≠ 0 := zpoly_ne_zero t b
    have hm : u θ ∈ (zpoly t b).roots := by
      exact (Polynomial.mem_roots hne).2 (hroot θ hθ)
    simpa using hm
  calc
    S.card = (S.image u).card := himg.symm
    _ ≤ ((zpoly t b).roots.toFinset).card := Finset.card_le_card hsub
    _ ≤ (zpoly t b).roots.card := Multiset.toFinset_card_le _
    _ ≤ (zpoly t b).natDegree := Polynomial.card_roots' (zpoly t b)
    _ ≤ 2 * m_t t := zpoly_natDegree_le t b


