import Mathlib
import Submission.HvdH.Interfaces

namespace Work.Main.param

/-!
# Small-term cost estimates for the main step (`Work.Main.param.smallCosts`)

All four conjuncts are elementary arithmetic bounds on the parameters
`bpar n = clog 2 n`, `ppar n = 6 bpar n`, `Tpar n = 2^(clog 2 ⌈4n/b⌉)` and
`apar n = ⌈(12 d² b)^(1/4)⌉` (`d = 1729`) of §5.1 of Harvey–van der Hoeven.
-/

/-- `(s+1)^2 + 2 ≤ 2^s` for `s ≥ 8` (used to dominate `b + 3` by `2^(√b)`). -/
theorem sq_succ_add_two_le_two_pow (s : ℕ) (hs : 8 ≤ s) : (s+1)^2 + 2 ≤ 2^s := by
  induction s, hs using Nat.le_induction with
  | base => norm_num
  | succ s hs ih =>
    calc (s+1+1)^2 + 2 = (s+2)^2 + 2 := by ring
      _ ≤ 2 * ((s+1)^2 + 2) := by nlinarith
      _ ≤ 2 * 2^s := Nat.mul_le_mul_left 2 ih
      _ = 2^(s+1) := by ring

/-- `(b+3)^K ≤ 2^(b-1)` whenever `256 K² ≤ b` and `K ≥ 1`. -/
theorem pow3_le (b K : ℕ) (hK : 1 ≤ K) (hb : 256 * K^2 ≤ b) : (b+3)^K ≤ 2^(b-1) := by
  have hb256 : 256 ≤ b := by nlinarith [hK, hb]
  have hs8 : 8 ≤ Nat.sqrt b := by rw [Nat.le_sqrt]; nlinarith [hb256]
  have hlt : b < (Nat.sqrt b + 1)^2 := by
    have := Nat.lt_succ_sqrt b; simpa [pow_two] using this
  have h2 : b + 3 ≤ 2^(Nat.sqrt b) := by
    have := sq_succ_add_two_le_two_pow (Nat.sqrt b) hs8
    nlinarith
  have h3 : (b+3)^K ≤ (2^(Nat.sqrt b))^K := Nat.pow_le_pow_left h2 K
  rw [← pow_mul] at h3
  refine h3.trans (Nat.pow_le_pow_right (by norm_num) ?_)
  have h16 : 16*K ≤ Nat.sqrt b := by rw [Nat.le_sqrt]; nlinarith [hb]
  have h5 : Nat.sqrt b * Nat.sqrt b ≤ b := Nat.sqrt_le b
  have h4' : Nat.sqrt b * K * 16 ≤ b := by nlinarith
  have h6 : Nat.sqrt b * K ≤ b / 16 := (Nat.le_div_iff_mul_le (by norm_num : 0 < 16)).mpr h4'
  have h7 : b / 16 ≤ b - 1 := by omega
  omega

/-- `(√(6b) + 1) · α(b) ≤ 1000 (b+1)` where `α(b) = √(√(12 d² b - 1)) + 1`. -/
theorem sqrtProd_aux (b : ℕ) :
    (Nat.sqrt (6*b)+1) * (Nat.sqrt (Nat.sqrt (12*HvdH.D^2*b-1))+1) ≤ 1000*(b+1) := by
  have hD : 0 < HvdH.D^2 := by norm_num [HvdH.D]
  set s := Nat.sqrt (6*b) with hsdef
  set t := Nat.sqrt (Nat.sqrt (12*HvdH.D^2*b-1)) with htdef
  have hs : s*s ≤ 6*b := by rw [hsdef]; exact Nat.sqrt_le _
  have ht : t^4 ≤ 12*HvdH.D^2*b := by
    have h1 : t*t ≤ Nat.sqrt (12*HvdH.D^2*b-1) := by rw [htdef]; exact Nat.sqrt_le _
    have h2 : Nat.sqrt (12*HvdH.D^2*b-1) * Nat.sqrt (12*HvdH.D^2*b-1) ≤ 12*HvdH.D^2*b-1 := Nat.sqrt_le _
    have h3 : 12*HvdH.D^2*b-1 ≤ 12*HvdH.D^2*b := Nat.sub_le _ _
    have ht2 : t^2 ≤ Nat.sqrt (12*HvdH.D^2*b-1) := by nlinarith [h1]
    have : t^2 * t^2 ≤ 12*HvdH.D^2*b := by nlinarith
    calc t^4 = t^2 * t^2 := by ring
      _ ≤ 12*HvdH.D^2*b := this
  have hs3 : s ≤ 3*(b+1) := by
    rw [← Nat.mul_self_le_mul_self_iff]
    nlinarith [hs]
  have hspow : (s+1)^4 ≤ 256*(b+1)^2 := by nlinarith [hs3, hs]
  have htpow : (t+1)^4 ≤ 192*HvdH.D^2*(b+1) := by
    rcases Nat.eq_zero_or_pos t with h0 | hpos
    · rw [h0]; norm_num
      nlinarith [hD]
    · have hle : t + 1 ≤ 2*t := by omega
      have h16 : (t+1)^4 ≤ 16*t^4 := by
        calc (t+1)^4 ≤ (2*t)^4 := Nat.pow_le_pow_left hle 4
          _ = 16*t^4 := by ring
      nlinarith [h16, ht]
  have hbpos : 0 < b+1 := by omega
  have hconst : 49152 * HvdH.D^2 ≤ 1000^4 := by norm_num [HvdH.D]
  have key : ((s+1)*(t+1))^4 ≤ (1000*(b+1))^4 := by
    have h1 : ((s+1)*(t+1))^4 = (s+1)^4 * (t+1)^4 := by ring
    rw [h1]
    have h2 : (s+1)^4 * (t+1)^4 ≤ (256*(b+1)^2) * (192*HvdH.D^2*(b+1)) :=
      Nat.mul_le_mul hspow htpow
    have h4 : (b+1)^3 ≤ (b+1)^4 := Nat.pow_le_pow_right hbpos (by norm_num)
    have h5 : 49152 * HvdH.D^2 * (b+1)^3 ≤ 1000^4 * (b+1)^3 := Nat.mul_le_mul_right _ hconst
    have h6 : 1000^4 * (b+1)^3 ≤ 1000^4 * (b+1)^4 := Nat.mul_le_mul_left _ h4
    have h7 : (256*(b+1)^2) * (192*HvdH.D^2*(b+1)) ≤ (1000*(b+1))^4 := by
      nlinarith [h5, h6]
    exact h2.trans h7
  exact (Nat.pow_le_pow_iff_left (by norm_num : (4:ℕ) ≠ 0)).mp key

theorem smallCosts {n K : ℕ} (hn : 1 ≤ n) (hb : 256 * K ^ 2 ≤ HvdH.bpar n)
    (hTb : HvdH.Tpar n * HvdH.bpar n < 8 * n) :
    (n.size + 2) ^ K ≤ n * n.size ∧ HvdH.bpar n ≤ n.size ∧
      HvdH.Tpar n * HvdH.ppar n ^ 2 ≤ 300 * (n * n.size) ∧
      HvdH.Tpar n * (Nat.sqrt (HvdH.ppar n) + 1) * HvdH.apar n * HvdH.ppar n ≤
        1000000 * (n * n.size) := by
  have hpar_size : HvdH.bpar n ≤ n.size := by
    rw [HvdH.bpar, Nat.clog_le_iff_le_pow (by norm_num : 1 < 2)]
    exact le_of_lt ((Nat.size_le (m := n) (n := n.size)).mp le_rfl)
  have hsize_le : n.size ≤ HvdH.bpar n + 1 := by
    rw [Nat.size_le]
    have h1 : n ≤ 2 ^ HvdH.bpar n := Nat.le_pow_clog (by norm_num : 1 < 2) n
    have h2 : (2:ℕ) ^ HvdH.bpar n < 2 ^ (HvdH.bpar n + 1) :=
      Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  have hsize1 : 1 ≤ n.size := by
    have h0 : 0 < n := by omega
    have := Nat.size_pos.mpr h0
    omega
  have h2size : HvdH.bpar n + 1 ≤ 2 * n.size := by omega
  refine ⟨?_, hpar_size, ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos K with hK0 | hKpos
    · rw [hK0]
      calc (1:ℕ) = 1 * 1 := by ring
        _ ≤ n * n.size := Nat.mul_le_mul (by omega) hsize1
    · have hbK : (n.size + 2)^K ≤ (HvdH.bpar n + 3)^K :=
        Nat.pow_le_pow_left (by omega) K
      have hpow : (HvdH.bpar n + 3)^K ≤ 2^(HvdH.bpar n - 1) := pow3_le _ _ hKpos hb
      have hb1 : 1 ≤ HvdH.bpar n := by nlinarith [hKpos, hb]
      have hlt : 2^(HvdH.bpar n - 1) < n := by
        have h1 : 1 < n := by
          by_contra hc
          have hc' : n ≤ 1 := by omega
          have : HvdH.bpar n = 0 := Nat.clog_of_right_le_one hc' 2
          omega
        simpa [HvdH.bpar, Nat.pred_eq_sub_one] using
          Nat.pow_pred_clog_lt_self (by norm_num : 1 < 2) h1
      have hnle : n ≤ n * n.size := by
        calc n = n * 1 := (Nat.mul_one n).symm
          _ ≤ n * n.size := Nat.mul_le_mul_left n hsize1
      exact le_trans (le_trans hbK hpow) (le_trans (le_of_lt hlt) hnle)
  · have hppar : HvdH.ppar n = 6 * HvdH.bpar n := rfl
    rw [hppar]
    have h1 : HvdH.Tpar n * (6 * HvdH.bpar n)^2
        = 36*HvdH.bpar n*(HvdH.Tpar n * HvdH.bpar n) := by ring
    rw [h1]
    have hle1 : 36*HvdH.bpar n*(HvdH.Tpar n * HvdH.bpar n) ≤ 36*HvdH.bpar n*(8*n) :=
      Nat.mul_le_mul_left _ (le_of_lt hTb)
    calc 36*HvdH.bpar n*(HvdH.Tpar n * HvdH.bpar n)
        ≤ 36*HvdH.bpar n*(8*n) := hle1
      _ = 288*(n*HvdH.bpar n) := by ring
      _ ≤ 288*(n*n.size) := Nat.mul_le_mul_left 288 (Nat.mul_le_mul_left n hpar_size)
      _ ≤ 300*(n*n.size) := Nat.mul_le_mul_right _ (by norm_num)
  · have hppar : HvdH.ppar n = 6 * HvdH.bpar n := rfl
    have hapar : HvdH.apar n = Nat.sqrt (Nat.sqrt (12 * HvdH.D^2 * HvdH.bpar n - 1)) + 1 := rfl
    rw [hppar, hapar]
    have hsp := sqrtProd_aux (HvdH.bpar n)
    have hrw : HvdH.Tpar n * (Nat.sqrt (6*HvdH.bpar n)+1)
          * (Nat.sqrt (Nat.sqrt (12*HvdH.D^2*HvdH.bpar n-1))+1) * (6*HvdH.bpar n)
        = 6 * (HvdH.Tpar n * HvdH.bpar n)
          * ((Nat.sqrt (6*HvdH.bpar n)+1) * (Nat.sqrt (Nat.sqrt (12*HvdH.D^2*HvdH.bpar n-1))+1)) := by
      ring
    rw [hrw]
    calc 6 * (HvdH.Tpar n * HvdH.bpar n)
          * ((Nat.sqrt (6*HvdH.bpar n)+1) * (Nat.sqrt (Nat.sqrt (12*HvdH.D^2*HvdH.bpar n-1))+1))
        ≤ 6 * (8*n) * (1000*(HvdH.bpar n + 1)) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left 6 (le_of_lt hTb)) hsp
      _ = 48000 * (n * (HvdH.bpar n + 1)) := by ring
      _ ≤ 48000 * (n * (2*n.size)) := Nat.mul_le_mul_left 48000 (Nat.mul_le_mul_left n h2size)
      _ = 96000 * (n * n.size) := by ring
      _ ≤ 1000000 * (n * n.size) := Nat.mul_le_mul_right _ (by norm_num)

end Work.Main.param
