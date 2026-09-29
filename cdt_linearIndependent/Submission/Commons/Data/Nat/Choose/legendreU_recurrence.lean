import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Rat.Star

open scoped BigOperators

namespace Commons.Data.Nat.Choose

/-! Creative-telescoping infrastructure used in the proof of
`legendreU_recurrence`. -/
namespace LegendreU

noncomputable def A (t : ℚ) (m k : ℕ) : ℚ :=
  (Nat.choose m (2 * k) : ℚ) * (Nat.choose (2 * k) k : ℚ) * t ^ (m - 2 * k) *
    (((t * t - 1) / 4) ^ k)
noncomputable def cb (r : ℕ) : ℚ := (Nat.choose (2 * r) r : ℚ)
noncomputable def masterQ (t : ℚ) (m k : ℕ) : ℚ :=
  ((m : ℚ) + 2) * A t (m + 2) k - ((2 * (m : ℚ) + 3) * t) * A t (m + 1) k
    + ((m : ℚ) + 1) * A t m k
noncomputable def G (t : ℚ) (m k : ℕ) : ℚ :=
  A t m k * 4 * (k : ℚ) ^ 2 * t ^ 2 * ((m : ℚ) + 1) /
    (((m : ℚ) + 1 - 2 * (k : ℚ)) * ((m : ℚ) + 2 - 2 * (k : ℚ)))

lemma A_eq_zero (t : ℚ) {m k : ℕ} (h : m < 2 * k) : A t m k = 0 := by
  unfold A
  rw [Nat.choose_eq_zero_of_lt h]
  ring

lemma choose_pred_self (n : ℕ) (hn : 1 ≤ n) : Nat.choose n (n - 1) = n := by
  have hs : n - (n - 1) = 1 := by omega
  rw [← Nat.choose_symm (by omega : n - 1 ≤ n), hs]
  rw [Nat.choose_one_right]

lemma A_twom_m (t : ℚ) (r : ℕ) : A t (2 * r) r = cb r * (((t * t - 1) / 4) ^ r) := by
  unfold A cb
  have he : 2 * r - 2 * r = 0 := by omega
  rw [he]
  simp
lemma A_twom1_m (t : ℚ) (r : ℕ) : A t (2 * r + 1) r = (2 * (r : ℚ) + 1) * cb r * t * (((t * t - 1) / 4) ^ r) := by
  unfold A cb
  have he : (2 * r + 1) - 2 * r = 1 := by omega
  have hc : Nat.choose (2 * r + 1) (2 * r) = 2 * r + 1 := by
    have hp := choose_pred_self (2 * r + 1) (by omega)
    have hs : (2 * r + 1) - 1 = 2 * r := by omega
    simpa [hs] using hp
  rw [he, hc]
  simp [pow_one]
lemma choose_twom2_mul_two (r : ℕ) : Nat.choose (2 * r + 2) (2 * r) * 2 = (2 * r + 2) * (2 * r + 1) := by
  have h1 := Nat.choose_succ_right_eq (2 * r + 2) (2 * r)
  have hs : (2 * r + 2) - 2 * r = 2 := by omega
  rw [hs] at h1
  have hp := choose_pred_self (2 * r + 2) (by omega)
  have hs' : (2 * r + 2) - 1 = 2 * r + 1 := by omega
  have hp' : Nat.choose (2 * r + 2) (2 * r + 1) = 2 * r + 2 := by simpa [hs'] using hp
  calc
    Nat.choose (2 * r + 2) (2 * r) * 2 = Nat.choose (2 * r + 2) (2 * r + 1) * (2 * r + 1) := h1.symm
    _ = (2 * r + 2) * (2 * r + 1) := by rw [hp']
lemma choose_add3_sub2 (r : ℕ) : Nat.choose (2 * r + 3) (2 * r + 2) = 2 * r + 3 := by
  have hp := choose_pred_self (2 * r + 3) (by omega)
  have hs' : (2 * r + 3) - 1 = 2 * r + 2 := by omega
  simpa [hs'] using hp
lemma choose_add3_mul_six (r : ℕ) :
    Nat.choose (2 * r + 3) (2 * r) * 6 = (2 * r + 3) * (2 * r + 2) * (2 * r + 1) := by
  have hA := Nat.choose_succ_right_eq (2 * r + 3) (2 * r)
  have hB := Nat.choose_succ_right_eq (2 * r + 3) (2 * r + 1)
  have hsA : (2 * r + 3) - 2 * r = 3 := by omega
  have hsB : (2 * r + 3) - (2 * r + 1) = 2 := by omega
  have hA' : Nat.choose (2 * r + 3) (2 * r + 1) * (2 * r + 1) =
      Nat.choose (2 * r + 3) (2 * r) * 3 := by
    rw [hsA] at hA
    exact hA
  have hB' : Nat.choose (2 * r + 3) (2 * r + 2) * (2 * r + 2) =
      Nat.choose (2 * r + 3) (2 * r + 1) * 2 := by
    rw [hsB] at hB
    exact hB
  have hp' := choose_add3_sub2 r
  calc
    Nat.choose (2 * r + 3) (2 * r) * 6
        = Nat.choose (2 * r + 3) (2 * r) * 3 * 2 := by ring
    _ = Nat.choose (2 * r + 3) (2 * r + 1) * (2 * r + 1) * 2 := by rw [hA']
    _ = (Nat.choose (2 * r + 3) (2 * r + 1) * 2) * (2 * r + 1) := by ring
    _ = Nat.choose (2 * r + 3) (2 * r + 2) * (2 * r + 2) * (2 * r + 1) := by rw [← hB']
    _ = (2 * r + 3) * (2 * r + 2) * (2 * r + 1) := by rw [hp']
lemma A_twom2_m (t : ℚ) (r : ℕ) : A t (2 * r + 2) r =
    (2 * (r : ℚ) + 2) * (2 * (r : ℚ) + 1) / 2 * cb r * t ^ 2 * (((t * t - 1) / 4) ^ r) := by
  unfold A
  have he : (2 * r + 2) - 2 * r = 2 := by omega
  rw [he]
  have hcN := choose_twom2_mul_two r
  have hcq : ((Nat.choose (2 * r + 2) (2 * r) : ℕ) : ℚ) * 2 =
      (2 * (r : ℚ) + 2) * (2 * (r : ℚ) + 1) := by
    exact_mod_cast hcN
  have hc : ((Nat.choose (2 * r + 2) (2 * r) : ℕ) : ℚ) =
      (2 * (r : ℚ) + 2) * (2 * (r : ℚ) + 1) / 2 := by
    calc
      ((Nat.choose (2 * r + 2) (2 * r) : ℕ) : ℚ)
          = (((Nat.choose (2 * r + 2) (2 * r) : ℕ) : ℚ) * 2) / 2 := by
            field_simp [show (2 : ℚ) ≠ 0 by norm_num]
      _ = (2 * (r : ℚ) + 2) * (2 * (r : ℚ) + 1) / 2 := by rw [hcq]
  rw [hc]
  unfold cb
  ring
lemma A_twom2_m1 (t : ℚ) (r : ℕ) : A t (2 * r + 2) (r + 1) =
    cb (r + 1) * (((t * t - 1) / 4) ^ (r + 1)) := by
  unfold A cb
  have htwo : 2 * (r + 1) = 2 * r + 2 := by ring
  rw [htwo]
  have he : 2 * r + 2 - (2 * r + 2) = 0 := by omega
  rw [he]
  simp
lemma A_twom3_m (t : ℚ) (r : ℕ) : A t (2 * r + 3) r =
    (2 * (r : ℚ) + 3) * (2 * (r : ℚ) + 2) * (2 * (r : ℚ) + 1) / 6 * cb r * t ^ 3
      * (((t * t - 1) / 4) ^ r) := by
  unfold A
  have he : (2 * r + 3) - 2 * r = 3 := by omega
  rw [he]
  have hcN := choose_add3_mul_six r
  have hcq : ((Nat.choose (2 * r + 3) (2 * r) : ℕ) : ℚ) * 6 =
      (2 * (r : ℚ) + 3) * (2 * (r : ℚ) + 2) * (2 * (r : ℚ) + 1) := by
    exact_mod_cast hcN
  have hc : ((Nat.choose (2 * r + 3) (2 * r) : ℕ) : ℚ) =
      (2 * (r : ℚ) + 3) * (2 * (r : ℚ) + 2) * (2 * (r : ℚ) + 1) / 6 := by
    calc
      ((Nat.choose (2 * r + 3) (2 * r) : ℕ) : ℚ)
          = (((Nat.choose (2 * r + 3) (2 * r) : ℕ) : ℚ) * 6) / 6 := by
            field_simp [show (6 : ℚ) ≠ 0 by norm_num]
      _ = (2 * (r : ℚ) + 3) * (2 * (r : ℚ) + 2) * (2 * (r : ℚ) + 1) / 6 := by rw [hcq]
  rw [hc]
  unfold cb
  ring
lemma A_twom3_m1 (t : ℚ) (r : ℕ) : A t (2 * r + 3) (r + 1) =
    (2 * (r : ℚ) + 3) * cb (r + 1) * t * (((t * t - 1) / 4) ^ (r + 1)) := by
  unfold A cb
  have htwo : 2 * (r + 1) = 2 * r + 2 := by ring
  rw [htwo]
  have hc : Nat.choose (2 * r + 3) (2 * r + 2) = 2 * r + 3 := choose_add3_sub2 r
  have he : (2 * r + 3) - (2 * r + 2) = 1 := by omega
  rw [he, hc]
  simp [pow_one]

lemma cb_succ (r : ℕ) : ((r : ℚ) + 1) * cb (r + 1) = 2 * (2 * (r : ℚ) + 1) * cb r := by
  have hq0 : (((r + 1 : ℕ) : ℚ)) * ((Nat.centralBinom (r + 1) : ℕ) : ℚ) =
      2 * (2 * (r : ℚ) + 1) * ((Nat.centralBinom r : ℕ) : ℚ) := by
    have h := Nat.succ_mul_centralBinom_succ r
    exact_mod_cast h
  have hcast : ((r + 1 : ℕ) : ℚ) = (r : ℚ) + 1 := by
    rw [Nat.cast_add]
    norm_num
  rw [hcast] at hq0
  change ((r : ℚ) + 1) * ((Nat.centralBinom (r + 1) : ℕ) : ℚ) =
      2 * (2 * (r : ℚ) + 1) * ((Nat.centralBinom r : ℕ) : ℚ)
  -- convert centralBinom (r+1) / r to choose forms
  rw [Nat.centralBinom]
  exact hq0


lemma cb_sq_succ (r : ℕ) :
    ((Nat.choose (2 * (r + 1)) (r + 1) : ℕ) : ℚ) * ((r : ℚ) + 1) ^ 2 =
      ((Nat.choose (2 * r) r : ℕ) : ℚ) * (2 * (r : ℚ) + 2) * (2 * (r : ℚ) + 1) := by
  have hq0 : (((r + 1 : ℕ) : ℚ)) * ((Nat.centralBinom (r + 1) : ℕ) : ℚ) =
      2 * (2 * (r : ℚ) + 1) * ((Nat.centralBinom r : ℕ) : ℚ) := by
    have h := Nat.succ_mul_centralBinom_succ r
    exact_mod_cast h
  have hcast : ((r + 1 : ℕ) : ℚ) = (r : ℚ) + 1 := by
    rw [Nat.cast_add]
    norm_num
  rw [hcast] at hq0
  have hq2 : ((Nat.centralBinom (r + 1) : ℕ) : ℚ) * ((r : ℚ) + 1) ^ 2 =
      (2 * (r : ℚ) + 2) * (2 * (r : ℚ) + 1) * ((Nat.centralBinom r : ℕ) : ℚ) := by
    calc
      ((Nat.centralBinom (r + 1) : ℕ) : ℚ) * ((r : ℚ) + 1) ^ 2
          = (((Nat.centralBinom (r + 1) : ℕ) : ℚ) * ((r : ℚ) + 1)) * ((r : ℚ) + 1) := by ring
      _ = ((((r : ℚ) + 1) * (Nat.centralBinom (r + 1) : ℕ) : ℚ)) * ((r : ℚ) + 1) := by ring
      _ = (2 * (2 * (r : ℚ) + 1) * ((Nat.centralBinom r : ℕ) : ℚ)) * ((r : ℚ) + 1) := by rw [hq0]
      _ = (2 * (r : ℚ) + 2) * (2 * (r : ℚ) + 1) * ((Nat.centralBinom r : ℕ) : ℚ) := by ring
  change ((Nat.centralBinom (r + 1) : ℕ) : ℚ) * ((r : ℚ) + 1) ^ 2 =
      ((Nat.centralBinom r : ℕ) : ℚ) * (2 * (r : ℚ) + 2) * (2 * (r : ℚ) + 1)
  calc
    ((Nat.centralBinom (r + 1) : ℕ) : ℚ) * ((r : ℚ) + 1) ^ 2
        = (2 * (r : ℚ) + 2) * (2 * (r : ℚ) + 1) * ((Nat.centralBinom r : ℕ) : ℚ) := hq2
    _ = ((Nat.centralBinom r : ℕ) : ℚ) * (2 * (r : ℚ) + 2) * (2 * (r : ℚ) + 1) := by ring

lemma choose_step (m k : ℕ) (hk : 2 * k + 2 ≤ m) :
    (Nat.choose m (2 * k + 2) : ℚ) * (2 * (k:ℚ) + 2) * (2*(k:ℚ)+1) =
    (Nat.choose m (2 * k) : ℚ) * ((m : ℚ) - 2 * (k : ℚ)) * ((m : ℚ) - 1 - 2 * (k : ℚ)) := by
  have h1c : ((Nat.choose m (2*k+2) : ℕ) : ℚ) * (((2 * k + 2 : ℕ) : ℚ)) =
      ((Nat.choose m (2*k+1) : ℕ) : ℚ) * (((m - (2*k+1) : ℕ)) : ℚ) := by
    exact_mod_cast (Nat.choose_succ_right_eq m (2 * k + 1))
  have h2c : ((Nat.choose m (2*k+1) : ℕ) : ℚ) * (((2 * k + 1 : ℕ) : ℚ)) =
      ((Nat.choose m (2*k) : ℕ) : ℚ) * (((m - 2*k : ℕ)) : ℚ) := by
    exact_mod_cast (Nat.choose_succ_right_eq m (2 * k))
  have hs1 : ((m - 2 * k : ℕ) : ℚ) = (m : ℚ) - 2 * (k:ℚ) := by
    rw [Nat.cast_sub (by omega : 2 * k ≤ m)]
    norm_num
  have hs2 : ((m - (2*k+1) : ℕ) : ℚ) = (m : ℚ) - 1 - 2*(k:ℚ) := by
    rw [Nat.cast_sub (by omega : 2 * k + 1 ≤ m)]
    push_cast
    ring
  calc
    (Nat.choose m (2 * k + 2) : ℚ) * (2 * (k:ℚ) + 2) * (2*(k:ℚ)+1)
        = ((Nat.choose m (2*k+2) : ℕ) : ℚ) * ((2 * k + 2 : ℕ) : ℚ) * ((2 * k + 1 : ℕ) : ℚ) := by norm_num
    _ = ((Nat.choose m (2*k+1) : ℕ) : ℚ) * ((m - (2*k+1) : ℕ) : ℚ) * ((2 * k + 1 : ℕ) : ℚ) := by rw [h1c]
    _ = ((Nat.choose m (2*k+1) : ℕ) : ℚ) * ((2 * k + 1 : ℕ) : ℚ) * ((m - (2*k+1) : ℕ) : ℚ) := by ring
    _ = ((Nat.choose m (2*k) : ℕ) : ℚ) * ((m - 2*k : ℕ) : ℚ) * ((m - (2*k+1) : ℕ) : ℚ) := by rw [h2c]
    _ = (Nat.choose m (2 * k) : ℚ) * ((m : ℚ) - 2 * (k:ℚ)) * ((m : ℚ) - 1 - 2*(k:ℚ)) := by rw [hs1, hs2]

lemma choose_product (m k : ℕ) (hk : 2 * k + 2 ≤ m) :
    (Nat.choose m (2 * (k + 1)) : ℚ) * (Nat.choose (2 * (k + 1)) (k + 1) : ℚ) * ((k : ℚ) + 1) ^ 2 =
      (Nat.choose m (2 * k) : ℚ) * (Nat.choose (2 * k) k : ℚ) * ((m : ℚ) - 2 * (k : ℚ))
        * ((m : ℚ) - 1 - 2 * (k : ℚ)) := by
  have htwo : 2 * (k + 1) = 2 * k + 2 := by ring
  rw [htwo]
  have hcb := cb_sq_succ k
  rw [htwo] at hcb
  have hcs := choose_step m k hk
  calc
    (Nat.choose m (2 * k + 2) : ℚ) * (Nat.choose (2 * k + 2) (k + 1) : ℚ) * ((k : ℚ) + 1) ^ 2
        = (Nat.choose m (2 * k + 2) : ℚ) * ((Nat.choose (2 * k + 2) (k + 1) : ℚ) * ((k : ℚ) + 1) ^ 2) := by ring
    _ = (Nat.choose m (2 * k + 2) : ℚ) * ((Nat.choose (2 * k) k : ℚ) * (2 * (k:ℚ) + 2) * (2 * (k:ℚ) + 1)) := by rw [hcb]
    _ = ((Nat.choose m (2 * k + 2) : ℚ) * (2 * (k:ℚ) + 2) * (2 * (k:ℚ) + 1)) * (Nat.choose (2 * k) k : ℚ) := by ring
    _ = ((Nat.choose m (2 * k) : ℚ) * ((m : ℚ) - 2 * (k:ℚ)) * ((m : ℚ) - 1 - 2*(k:ℚ))) * (Nat.choose (2 * k) k : ℚ) := by rw [hcs]
    _ = (Nat.choose m (2 * k) : ℚ) * (Nat.choose (2 * k) k : ℚ) * ((m : ℚ) - 2 * (k : ℚ)) * ((m : ℚ) - 1 - 2 * (k : ℚ)) := by ring

-- P3: A_succ_right
lemma A_succ_right (t : ℚ) (m k : ℕ) (hk : 2 * k + 2 ≤ m) :
    A t m (k + 1) * 4 * ((k : ℚ) + 1) ^ 2 * t ^ 2 =
      A t m k * ((m : ℚ) - 2 * (k : ℚ)) * ((m : ℚ) - 1 - 2 * (k : ℚ)) * (t ^ 2 - 1) := by
  have hcp := choose_product m k hk
  have hpow : t ^ (m - 2 * (k + 1)) * t ^ 2 = t ^ (m - 2 * k) := by
    have hstep : m - 2 * (k + 1) + 2 = m - 2 * k := by omega
    rw [← pow_add, hstep]
  have hc : 4 * (((t * t - 1) / 4) ^ (k + 1)) = (((t * t - 1) / 4) ^ k) * (t ^ 2 - 1) := by
    rw [pow_succ]
    ring_nf
  unfold A
  calc
    (Nat.choose m (2 * (k + 1)) : ℚ) * (Nat.choose (2 * (k + 1)) (k + 1) : ℚ) * t ^ (m - 2 * (k + 1))
        * (((t * t - 1) / 4) ^ (k + 1)) * 4 * ((k : ℚ) + 1) ^ 2 * t ^ 2
      = ((Nat.choose m (2 * (k + 1)) : ℚ) * (Nat.choose (2 * (k + 1)) (k + 1) : ℚ) * ((k : ℚ) + 1) ^ 2)
          * (t ^ (m - 2 * (k + 1)) * t ^ 2)
          * (4 * (((t * t - 1) / 4) ^ (k + 1))) := by ring
    _ = ((Nat.choose m (2 * k) : ℚ) * (Nat.choose (2 * k) k : ℚ) * ((m : ℚ) - 2 * (k : ℚ)) * ((m : ℚ) - 1 - 2 * (k : ℚ)))
          * (t ^ (m - 2 * (k + 1)) * t ^ 2)
          * (4 * (((t * t - 1) / 4) ^ (k + 1))) := by rw [hcp]
    _ = ((Nat.choose m (2 * k) : ℚ) * (Nat.choose (2 * k) k : ℚ) * ((m : ℚ) - 2 * (k : ℚ)) * ((m : ℚ) - 1 - 2 * (k : ℚ)))
          * t ^ (m - 2 * k)
          * (4 * (((t * t - 1) / 4) ^ (k + 1))) := by rw [hpow]
    _ = ((Nat.choose m (2 * k) : ℚ) * (Nat.choose (2 * k) k : ℚ) * ((m : ℚ) - 2 * (k : ℚ)) * ((m : ℚ) - 1 - 2 * (k : ℚ)))
          * t ^ (m - 2 * k)
          * ((((t * t - 1) / 4) ^ k) * (t ^ 2 - 1)) := by rw [hc]
    _ = (Nat.choose m (2 * k) : ℚ) * (Nat.choose (2 * k) k : ℚ) * t ^ (m - 2 * k) * (((t * t - 1) / 4) ^ k)
          * ((m : ℚ) - 2 * (k : ℚ)) * ((m : ℚ) - 1 - 2 * (k : ℚ)) * (t ^ 2 - 1) := by ring

lemma A_succ_left (t : ℚ) (m k : ℕ) (hk : 2 * k ≤ m) :
    A t (m + 1) k * ((m : ℚ) + 1 - 2 * (k : ℚ)) = A t m k * t * ((m : ℚ) + 1) := by
  unfold A
  have hstep : (m + 1) - 2 * k = (m - 2 * k) + 1 := by omega
  have hpow : t ^ ((m + 1) - 2 * k) = t ^ (m - 2 * k) * t := by
    rw [hstep, pow_succ]
  have hcoef1 : ((m + 1 - 2 * k : ℕ) : ℚ) = (m : ℚ) + 1 - 2 * (k : ℚ) := by
    rw [Nat.cast_sub (by omega : 2 * k ≤ m + 1)]
    norm_num
  have hch : ((Nat.choose (m + 1) (2 * k) : ℕ) : ℚ) * ((m + 1 - 2 * k : ℕ) : ℚ) =
      ((Nat.choose m (2 * k) : ℕ) : ℚ) * (((m + 1 : ℕ) : ℚ)) := by
    exact_mod_cast (Nat.choose_mul_succ_eq m (2 * k)).symm
  have hm1 : ((m + 1 : ℕ) : ℚ) = (m : ℚ) + 1 := by norm_num
  have hinter :
      (Nat.choose (m + 1) (2 * k) : ℚ) * t ^ ((m + 1) - 2 * k) * ((m : ℚ) + 1 - 2 * (k : ℚ)) =
        (Nat.choose m (2 * k) : ℚ) * t ^ (m - 2 * k) * t * ((m : ℚ) + 1) := by
    rw [← hcoef1]
    calc
      (Nat.choose (m + 1) (2 * k) : ℚ) * t ^ ((m + 1) - 2 * k) * ((m + 1 - 2 * k : ℕ) : ℚ)
          = ((Nat.choose (m + 1) (2 * k) : ℚ) * ((m + 1 - 2 * k : ℕ) : ℚ)) * t ^ ((m + 1) - 2 * k) := by ring
      _ = ((Nat.choose m (2 * k) : ℚ) * (((m + 1 : ℕ) : ℚ))) * t ^ ((m + 1) - 2 * k) := by rw [hch]
      _ = (Nat.choose m (2 * k) : ℚ) * (((m + 1 : ℕ) : ℚ)) * (t ^ (m - 2 * k) * t) := by rw [hpow]
      _ = (Nat.choose m (2 * k) : ℚ) * t ^ (m - 2 * k) * t * (((m + 1 : ℕ) : ℚ)) := by ring
      _ = (Nat.choose m (2 * k) : ℚ) * t ^ (m - 2 * k) * t * ((m : ℚ) + 1) := by rw [hm1]
  calc
    (Nat.choose (m + 1) (2 * k) : ℚ) * (Nat.choose (2 * k) k : ℚ) * t ^ ((m + 1) - 2 * k)
        * (((t * t - 1) / 4) ^ k) * ((m : ℚ) + 1 - 2 * (k : ℚ))
        = ((Nat.choose (m + 1) (2 * k) : ℚ) * t ^ ((m + 1) - 2 * k) * ((m : ℚ) + 1 - 2 * (k : ℚ)))
            * ((Nat.choose (2 * k) k : ℚ) * (((t * t - 1) / 4) ^ k)) := by ring
    _ = ((Nat.choose m (2 * k) : ℚ) * t ^ (m - 2 * k) * t * ((m : ℚ) + 1))
            * ((Nat.choose (2 * k) k : ℚ) * (((t * t - 1) / 4) ^ k)) := by rw [hinter]
    _ = (Nat.choose m (2 * k) : ℚ) * (Nat.choose (2 * k) k : ℚ) * t ^ (m - 2 * k)
            * (((t * t - 1) / 4) ^ k) * t * ((m : ℚ) + 1) := by ring

lemma hcast_add (m : ℕ) : ((m + 1 : ℕ) : ℚ) = (m : ℚ) + 1 := by
  rw [Nat.cast_add]
  norm_num

lemma A_double_left (t : ℚ) (m k : ℕ) (hk : 2 * k ≤ m) :
    A t (m + 2) k * ((m : ℚ) + 2 - 2 * (k : ℚ)) * ((m : ℚ) + 1 - 2 * (k : ℚ)) =
      A t m k * t ^ 2 * ((m : ℚ) + 2) * ((m : ℚ) + 1) := by
  have h2raw := A_succ_left t (m + 1) k (by omega)
  have hidx : (m + 1) + 1 = m + 2 := by omega
  have h2a : A t (m + 2) k * (((m + 1 : ℕ) : ℚ) + 1 - 2 * (k : ℚ)) =
      A t (m + 1) k * t * (((m + 1 : ℕ) : ℚ) + 1) := by
    simpa [hidx] using h2raw
  have hcA : ((m + 1 : ℕ) : ℚ) + 1 = (m : ℚ) + 2 := by
    rw [hcast_add m]
    ring
  have h2 : A t (m + 2) k * ((m : ℚ) + 2 - 2 * (k : ℚ)) = A t (m + 1) k * t * ((m : ℚ) + 2) := by
    calc
      A t (m + 2) k * ((m : ℚ) + 2 - 2 * (k : ℚ))
          = A t (m + 2) k * ((((m + 1 : ℕ) : ℚ) + 1) - 2 * (k : ℚ)) := by rw [← hcA]
      _ = A t (m + 1) k * t * (((m + 1 : ℕ) : ℚ) + 1) := h2a
      _ = A t (m + 1) k * t * ((m : ℚ) + 2) := by rw [hcA]
  have h1 := A_succ_left t m k hk
  calc
    A t (m + 2) k * ((m : ℚ) + 2 - 2 * (k : ℚ)) * ((m : ℚ) + 1 - 2 * (k : ℚ))
        = (A t (m + 2) k * ((m : ℚ) + 2 - 2 * (k : ℚ))) * ((m : ℚ) + 1 - 2 * (k : ℚ)) := by ring
    _ = (A t (m + 1) k * t * ((m : ℚ) + 2)) * ((m : ℚ) + 1 - 2 * (k : ℚ)) := by rw [h2]
    _ = t * ((m : ℚ) + 2) * (A t (m + 1) k * ((m : ℚ) + 1 - 2 * (k : ℚ))) := by ring
    _ = t * ((m : ℚ) + 2) * (A t m k * t * ((m : ℚ) + 1)) := by rw [h1]
    _ = A t m k * t ^ 2 * ((m : ℚ) + 2) * ((m : ℚ) + 1) := by ring

lemma masterQ_mul_D (t : ℚ) (m k : ℕ) (hk : 2 * k + 2 ≤ m) :
    masterQ t m k * (((m : ℚ) + 1 - 2 * (k : ℚ)) * ((m : ℚ) + 2 - 2 * (k : ℚ))) =
      A t m k * ((m : ℚ) + 1) * (
        ((m : ℚ) + 2) ^ 2 * t ^ 2 - (2 * (m : ℚ) + 3) * t ^ 2 * ((m : ℚ) + 2 - 2 * (k : ℚ))
          + ((m : ℚ) + 1 - 2 * (k : ℚ)) * ((m : ℚ) + 2 - 2 * (k : ℚ))) := by
  have h1 := A_succ_left t m k (by omega)
  have h2 := A_double_left t m k (by omega)
  calc
    masterQ t m k * (((m : ℚ) + 1 - 2 * (k : ℚ)) * ((m : ℚ) + 2 - 2 * (k : ℚ)))
        = ((m : ℚ) + 2) * (A t (m + 2) k * ((m : ℚ) + 2 - 2 * (k : ℚ)) * ((m : ℚ) + 1 - 2 * (k : ℚ)))
            - ((2 * (m : ℚ) + 3) * t) * (A t (m + 1) k * ((m : ℚ) + 1 - 2 * (k : ℚ))) * ((m : ℚ) + 2 - 2 * (k : ℚ))
            + ((m : ℚ) + 1) * A t m k * (((m : ℚ) + 1 - 2 * (k : ℚ)) * ((m : ℚ) + 2 - 2 * (k : ℚ))) := by
            unfold masterQ
            ring
    _ = ((m : ℚ) + 2) * (A t m k * t ^ 2 * ((m : ℚ) + 2) * ((m : ℚ) + 1))
            - ((2 * (m : ℚ) + 3) * t) * (A t m k * t * ((m : ℚ) + 1)) * ((m : ℚ) + 2 - 2 * (k : ℚ))
            + ((m : ℚ) + 1) * A t m k * (((m : ℚ) + 1 - 2 * (k : ℚ)) * ((m : ℚ) + 2 - 2 * (k : ℚ))) := by rw [h1, h2]
    _ = A t m k * ((m : ℚ) + 1) * (
        ((m : ℚ) + 2) ^ 2 * t ^ 2 - (2 * (m : ℚ) + 3) * t ^ 2 * ((m : ℚ) + 2 - 2 * (k : ℚ))
          + ((m : ℚ) + 1 - 2 * (k : ℚ)) * ((m : ℚ) + 2 - 2 * (k : ℚ))) := by ring

lemma den_nz1 (m k : ℕ) (hk : 2 * k + 2 ≤ m) : (m : ℚ) + 1 - 2 * (k : ℚ) ≠ 0 := by
  have hgt : 0 < m + 1 - 2 * k := by omega
  have hs : (m : ℚ) + 1 - 2 * (k : ℚ) = ((m + 1 - 2 * k : ℕ) : ℚ) := by
    rw [Nat.cast_sub (by omega : 2 * k ≤ m + 1)]
    norm_num
  rw [hs]
  exact_mod_cast (ne_of_gt hgt)

lemma den_nz2 (m k : ℕ) (hk : 2 * k + 2 ≤ m) : (m : ℚ) + 2 - 2 * (k : ℚ) ≠ 0 := by
  have hgt : 0 < m + 2 - 2 * k := by omega
  have hs : (m : ℚ) + 2 - 2 * (k : ℚ) = ((m + 2 - 2 * k : ℕ) : ℚ) := by
    rw [Nat.cast_sub (by omega : 2 * k ≤ m + 2)]
    norm_num
  rw [hs]
  exact_mod_cast (ne_of_gt hgt)

lemma den_nz3 (m k : ℕ) (hk : 2 * k + 2 ≤ m) : (m : ℚ) - 2 * (k : ℚ) ≠ 0 := by
  have hgt : 0 < m - 2 * k := by omega
  have hs : (m : ℚ) - 2 * (k : ℚ) = ((m - 2 * k : ℕ) : ℚ) := by
    rw [Nat.cast_sub (by omega : 2 * k ≤ m)]
    norm_num
  rw [hs]
  exact_mod_cast (ne_of_gt hgt)

lemma den_nz4 (m k : ℕ) (hk : 2 * k + 2 ≤ m) : (m : ℚ) - 1 - 2 * (k : ℚ) ≠ 0 := by
  have hgt : 0 < m - (2 * k + 1) := by omega
  have hs : (m : ℚ) - 1 - 2 * (k : ℚ) = ((m - (2 * k + 1) : ℕ) : ℚ) := by
    rw [Nat.cast_sub (by omega : 2 * k + 1 ≤ m)]
    push_cast
    ring
  rw [hs]
  exact_mod_cast (ne_of_gt hgt)

lemma G_mul_D0 (t : ℚ) (m k : ℕ) (hk : 2 * k + 2 ≤ m) :
    G t m k * (((m : ℚ) + 1 - 2 * (k : ℚ)) * ((m : ℚ) + 2 - 2 * (k : ℚ))) =
      A t m k * 4 * (k : ℚ) ^ 2 * t ^ 2 * ((m : ℚ) + 1) := by
  unfold G
  exact div_mul_cancel₀ (A t m k * 4 * (k : ℚ) ^ 2 * t ^ 2 * ((m : ℚ) + 1))
    (mul_ne_zero (den_nz1 m k hk) (den_nz2 m k hk))

lemma G_shift (t : ℚ) (m k : ℕ) (hk : 2 * k + 2 ≤ m) :
    G t m (k + 1) = A t m k * (t ^ 2 - 1) * ((m : ℚ) + 1) := by
  have hsr := A_succ_right t m k hk
  unfold G
  have hcast_add (m : ℕ) : ((m + 1 : ℕ) : ℚ) = (m : ℚ) + 1 := by
    rw [Nat.cast_add]
    norm_num
  rw [hcast_add k]
  rw [hsr]
  have hden2 : ((m : ℚ) + 1 - 2 * ((k : ℚ) + 1)) * ((m : ℚ) + 2 - 2 * ((k : ℚ) + 1)) =
      ((m : ℚ) - 2 * (k : ℚ)) * ((m : ℚ) - 1 - 2 * (k : ℚ)) := by ring
  rw [hden2]
  calc
    (A t m k * ((m : ℚ) - 2 * (k : ℚ)) * ((m : ℚ) - 1 - 2 * (k : ℚ)) * (t ^ 2 - 1) * ((m : ℚ) + 1))
        / (((m : ℚ) - 2 * (k : ℚ)) * ((m : ℚ) - 1 - 2 * (k : ℚ)))
        = (A t m k * (t ^ 2 - 1) * ((m : ℚ) + 1) * (((m : ℚ) - 2 * (k : ℚ)) * ((m : ℚ) - 1 - 2 * (k : ℚ))))
            / (((m : ℚ) - 2 * (k : ℚ)) * ((m : ℚ) - 1 - 2 * (k : ℚ))) := by ring
    _ = A t m k * (t ^ 2 - 1) * ((m : ℚ) + 1) := by field_simp [den_nz3 m k hk, den_nz4 m k hk]

lemma G_mul_D1 (t : ℚ) (m k : ℕ) (hk : 2 * k + 2 ≤ m) :
    G t m (k + 1) * (((m : ℚ) + 1 - 2 * (k : ℚ)) * ((m : ℚ) + 2 - 2 * (k : ℚ))) =
      A t m k * (t ^ 2 - 1) * ((m : ℚ) + 1)
        * (((m : ℚ) + 1 - 2 * (k : ℚ)) * ((m : ℚ) + 2 - 2 * (k : ℚ))) := by
  rw [G_shift t m k hk]

lemma G_mul_D (t : ℚ) (m k : ℕ) (hk : 2 * k + 2 ≤ m) :
    (G t m k - G t m (k + 1)) * (((m : ℚ) + 1 - 2 * (k : ℚ)) * ((m : ℚ) + 2 - 2 * (k : ℚ))) =
      A t m k * ((m : ℚ) + 1) * (4 * (k : ℚ) ^ 2 * t ^ 2
        - (t ^ 2 - 1) * ((m : ℚ) + 1 - 2 * (k : ℚ)) * ((m : ℚ) + 2 - 2 * (k : ℚ))) := by
  have h0 := G_mul_D0 t m k hk
  have h1 := G_mul_D1 t m k hk
  calc
    (G t m k - G t m (k + 1)) * (((m : ℚ) + 1 - 2 * (k : ℚ)) * ((m : ℚ) + 2 - 2 * (k : ℚ)))
        = G t m k * (((m : ℚ) + 1 - 2 * (k : ℚ)) * ((m : ℚ) + 2 - 2 * (k : ℚ)))
          - G t m (k + 1) * (((m : ℚ) + 1 - 2 * (k : ℚ)) * ((m : ℚ) + 2 - 2 * (k : ℚ))) := by ring
    _ = A t m k * 4 * (k : ℚ) ^ 2 * t ^ 2 * ((m : ℚ) + 1)
        - A t m k * (t ^ 2 - 1) * ((m : ℚ) + 1)
          * (((m : ℚ) + 1 - 2 * (k : ℚ)) * ((m : ℚ) + 2 - 2 * (k : ℚ))) := by rw [h0, h1]
    _ = A t m k * ((m : ℚ) + 1) * (4 * (k : ℚ) ^ 2 * t ^ 2
        - (t ^ 2 - 1) * ((m : ℚ) + 1 - 2 * (k : ℚ)) * ((m : ℚ) + 2 - 2 * (k : ℚ))) := by ring

lemma tel (t : ℚ) (m k : ℕ) (hk : 2 * k + 2 ≤ m) : masterQ t m k = G t m k - G t m (k + 1) := by
  have h1 := masterQ_mul_D t m k hk
  have h2 := G_mul_D t m k hk
  have hDnz : ((m : ℚ) + 1 - 2 * (k : ℚ)) * ((m : ℚ) + 2 - 2 * (k : ℚ)) ≠ 0 :=
    mul_ne_zero (den_nz1 m k hk) (den_nz2 m k hk)
  have hz : (masterQ t m k - (G t m k - G t m (k + 1))) *
      (((m : ℚ) + 1 - 2 * (k : ℚ)) * ((m : ℚ) + 2 - 2 * (k : ℚ))) = 0 := by
    calc
      (masterQ t m k - (G t m k - G t m (k + 1))) * (((m : ℚ) + 1 - 2 * (k : ℚ)) * ((m : ℚ) + 2 - 2 * (k : ℚ)))
          = masterQ t m k * (((m : ℚ) + 1 - 2 * (k : ℚ)) * ((m : ℚ) + 2 - 2 * (k : ℚ)))
            - (G t m k - G t m (k + 1)) * (((m : ℚ) + 1 - 2 * (k : ℚ)) * ((m : ℚ) + 2 - 2 * (k : ℚ))) := by ring
      _ = A t m k * ((m : ℚ) + 1) * (
              ((m : ℚ) + 2) ^ 2 * t ^ 2 - (2 * (m : ℚ) + 3) * t ^ 2 * ((m : ℚ) + 2 - 2 * (k : ℚ))
                + ((m : ℚ) + 1 - 2 * (k : ℚ)) * ((m : ℚ) + 2 - 2 * (k : ℚ)))
          - A t m k * ((m : ℚ) + 1) * (4 * (k : ℚ) ^ 2 * t ^ 2
              - (t ^ 2 - 1) * ((m : ℚ) + 1 - 2 * (k : ℚ)) * ((m : ℚ) + 2 - 2 * (k : ℚ))) := by rw [h1, h2]
      _ = 0 := by ring
  have hz' : masterQ t m k - (G t m k - G t m (k + 1)) = 0 := by
    exact (mul_eq_zero.mp hz).resolve_right hDnz
  exact sub_eq_zero.mp hz'


lemma G_twom_m (t : ℚ) (r : ℕ) :
    G t (2 * r) r = cb r * (((t * t - 1) / 4) ^ r) * (2 * (2 * (r : ℚ) + 1) * (r : ℚ) ^ 2 * t ^ 2) := by
  unfold G
  rw [A_twom_m]
  have hA : 2 * (r : ℚ) + 1 - 2 * (r : ℚ) ≠ 0 := by
    have h : 2 * (r : ℚ) + 1 - 2 * (r : ℚ) = 1 := by ring
    rw [h]
    norm_num
  have hB : 2 * (r : ℚ) + 2 - 2 * (r : ℚ) ≠ 0 := by
    have h : 2 * (r : ℚ) + 2 - 2 * (r : ℚ) = 2 := by ring
    rw [h]
    norm_num
  push_cast
  field_simp [hA, hB]
  ring

lemma hred_even (t : ℚ) (r : ℕ) :
    (2 * (r : ℚ) + 2) * (cb (r + 1) * (((t * t - 1) / 4) ^ (r + 1))) =
      (2 * (r : ℚ) + 1) * cb r * (((t * t - 1) / 4) ^ r) * (t ^ 2 - 1) := by
  calc
    (2 * (r : ℚ) + 2) * (cb (r + 1) * (((t * t - 1) / 4) ^ (r + 1)))
        = ((r : ℚ) + 1) * cb (r + 1) * (((t * t - 1) / 4) ^ (r + 1)) * 2 := by ring
    _ = (2 * (2 * (r : ℚ) + 1) * cb r) * (((t * t - 1) / 4) ^ (r + 1)) * 2 := by rw [cb_succ]
    _ = (2 * (2 * (r : ℚ) + 1) * cb r) * (((t * t - 1) / 4) ^ r * ((t * t - 1) / 4)) * 2 := by rw [pow_succ]
    _ = (2 * (r : ℚ) + 1) * cb r * (((t * t - 1) / 4) ^ r) * (t ^ 2 - 1) := by ring_nf

lemma boundary_even (t : ℚ) (r : ℕ) :
    masterQ t (2 * r) r + masterQ t (2 * r) (r + 1) = G t (2 * r) r := by
  have h00 : A t (2 * r) (r + 1) = 0 := by
    apply A_eq_zero
    omega
  have h10 : A t (2 * r + 1) (r + 1) = 0 := by
    apply A_eq_zero
    omega
  unfold masterQ
  rw [G_twom_m]
  rw [A_twom_m, A_twom1_m, A_twom2_m, A_twom2_m1, h00, h10]
  push_cast
  rw [hred_even]
  ring

lemma G_twom1_m (t : ℚ) (r : ℕ) :
    G t (2 * r + 1) r =
      cb r * (((t * t - 1) / 4) ^ r)
        * ((2 * (r : ℚ) + 1) * (2 * (r : ℚ) + 2) * 4 * (r : ℚ) ^ 2 * t ^ 3 / 6) := by
  unfold G
  rw [A_twom1_m]
  have hA : 2 * (r : ℚ) + 1 + 1 - 2 * (r : ℚ) ≠ 0 := by
    have h : 2 * (r : ℚ) + 1 + 1 - 2 * (r : ℚ) = 2 := by ring
    rw [h]
    norm_num
  have hB : 2 * (r : ℚ) + 1 + 2 - 2 * (r : ℚ) ≠ 0 := by
    have h : 2 * (r : ℚ) + 1 + 2 - 2 * (r : ℚ) = 3 := by ring
    rw [h]
    norm_num
  push_cast
  field_simp [hA, hB]
  ring

lemma hred_odd (t : ℚ) (r : ℕ) :
    4 * ((r : ℚ) + 1) ^ 2 * t * (cb (r + 1) * (((t * t - 1) / 4) ^ (r + 1))) =
      2 * (2 * (r : ℚ) + 1) * ((r : ℚ) + 1) * cb r * (((t * t - 1) / 4) ^ r) * t * (t ^ 2 - 1) := by
  calc
    4 * ((r : ℚ) + 1) ^ 2 * t * (cb (r + 1) * (((t * t - 1) / 4) ^ (r + 1)))
        = 4 * ((r : ℚ) + 1) * (((r : ℚ) + 1) * cb (r + 1)) * t * (((t * t - 1) / 4) ^ (r + 1)) := by ring
    _ = 4 * ((r : ℚ) + 1) * (2 * (2 * (r : ℚ) + 1) * cb r) * t * (((t * t - 1) / 4) ^ (r + 1)) := by rw [cb_succ]
    _ = 4 * ((r : ℚ) + 1) * (2 * (2 * (r : ℚ) + 1) * cb r) * t
          * (((t * t - 1) / 4) ^ r * ((t * t - 1) / 4)) := by rw [pow_succ]
    _ = 2 * (2 * (r : ℚ) + 1) * ((r : ℚ) + 1) * cb r * (((t * t - 1) / 4) ^ r) * t * (t ^ 2 - 1) := by ring_nf

lemma cornerQ_odd_r (t : ℚ) (r : ℕ) :
    masterQ t (2 * r + 1) r =
      cb r * (((t * t - 1) / 4) ^ r) * (
        (2 * (r : ℚ) + 3) ^ 2 * (2 * (r : ℚ) + 2) * (2 * (r : ℚ) + 1) / 6 * t ^ 3
          - (4 * (r : ℚ) + 5) * (2 * (r : ℚ) + 2) * (2 * (r : ℚ) + 1) / 2 * t ^ 3
          + (2 * (r : ℚ) + 2) * (2 * (r : ℚ) + 1) * t) := by
  unfold masterQ
  rw [A_twom3_m, A_twom2_m, A_twom1_m]
  push_cast
  ring

lemma cornerQ_odd_r1 (t : ℚ) (r : ℕ) :
    masterQ t (2 * r + 1) (r + 1) =
      4 * ((r : ℚ) + 1) ^ 2 * t * (cb (r + 1) * (((t * t - 1) / 4) ^ (r + 1))) := by
  have h01 : A t (2 * r + 1) (r + 1) = 0 := by
    apply A_eq_zero
    omega
  unfold masterQ
  rw [A_twom3_m1, A_twom2_m1, h01]
  push_cast
  ring

lemma cornerQ_odd_r1_elim (t : ℚ) (r : ℕ) :
    masterQ t (2 * r + 1) (r + 1) =
      2 * (2 * (r : ℚ) + 1) * ((r : ℚ) + 1) * cb r * (((t * t - 1) / 4) ^ r) * t * (t ^ 2 - 1) := by
  rw [cornerQ_odd_r1]
  exact hred_odd t r

lemma boundary_odd (t : ℚ) (r : ℕ) :
    masterQ t (2 * r + 1) r + masterQ t (2 * r + 1) (r + 1) = G t (2 * r + 1) r := by
  rw [cornerQ_odd_r, cornerQ_odd_r1_elim, G_twom1_m]
  ring

noncomputable def S (t : ℚ) (m : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (m / 2 + 1), A t m k

lemma two_mul_div_add_gt (m x : ℕ) : m < 2 * (m / 2 + 1 + x) := by
  have h1 : m < 2 * (m / 2) + 2 := by omega
  omega

lemma sum_A_eq_S (t : ℚ) (m M : ℕ) (hM : m / 2 ≤ M) :
    (∑ k ∈ Finset.range (M + 1), A t m k) = S t m := by
  unfold S
  have hsplit := Finset.sum_range_add (fun k => A t m k) (m / 2 + 1) (M + 1 - (m / 2 + 1))
  have hlen : m / 2 + 1 + (M + 1 - (m / 2 + 1)) = M + 1 := by omega
  rw [hlen] at hsplit
  rw [hsplit]
  have hextra : (∑ x ∈ Finset.range (M + 1 - (m / 2 + 1)), A t m (m / 2 + 1 + x)) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro x hx
    exact A_eq_zero t (two_mul_div_add_gt m x)
  rw [hextra]
  ring

lemma G_zero (t : ℚ) (n : ℕ) : G t n 0 = 0 := by
  unfold G
  ring

lemma boundary (t : ℚ) (n : ℕ) :
    masterQ t n (n / 2) + masterQ t n (n / 2 + 1) = G t n (n / 2) := by
  rcases Nat.even_or_odd n with hE | hO
  · rcases hE with ⟨r, hr⟩
    have hr2 : n = 2 * r := by
      rw [two_mul r]
      exact hr
    rw [hr2]
    rw [show (2 * r) / 2 = r by omega]
    exact boundary_even t r
  · rcases hO with ⟨r, hr⟩
    rw [hr]
    rw [show (2 * r + 1) / 2 = r by omega]
    exact boundary_odd t r

lemma masterSum_zero (t : ℚ) (n : ℕ) :
    (∑ k ∈ Finset.range (n / 2 + 2), masterQ t n k) = 0 := by
  have hsplit : (∑ k ∈ Finset.range (n / 2 + 2), masterQ t n k)
      = (∑ k ∈ Finset.range (n / 2), masterQ t n k) + masterQ t n (n / 2)
        + masterQ t n (n / 2 + 1) := by
    rw [show n / 2 + 2 = (n / 2 + 1) + 1 by omega]
    rw [Finset.sum_range_succ]
    rw [Finset.sum_range_succ]
  have htel : (∑ k ∈ Finset.range (n / 2), masterQ t n k)
      = (∑ k ∈ Finset.range (n / 2), (G t n k - G t n (k + 1))) := by
    refine Finset.sum_congr rfl ?_
    intro k hk
    have hklt : k < n / 2 := Finset.mem_range.mp hk
    have hkk : 2 * k + 2 ≤ n := by
      have hk' : k + 1 ≤ n / 2 := Nat.succ_le_of_lt hklt
      omega
    exact tel t n k hkk
  calc
    (∑ k ∈ Finset.range (n / 2 + 2), masterQ t n k)
        = (∑ k ∈ Finset.range (n / 2), masterQ t n k) + masterQ t n (n / 2)
          + masterQ t n (n / 2 + 1) := hsplit
    _ = (∑ k ∈ Finset.range (n / 2), (G t n k - G t n (k + 1))) + masterQ t n (n / 2)
          + masterQ t n (n / 2 + 1) := by rw [htel]
    _ = (G t n 0 - G t n (n / 2)) + masterQ t n (n / 2) + masterQ t n (n / 2 + 1) := by
          rw [Finset.sum_range_sub']
    _ = G t n 0 - G t n (n / 2) + (masterQ t n (n / 2) + masterQ t n (n / 2 + 1)) := by ring
    _ = G t n 0 - G t n (n / 2) + G t n (n / 2) := by rw [boundary t n]
    _ = 0 := by
          rw [G_zero t n]
          ring

lemma masterSum_eq (t : ℚ) (n : ℕ) :
    (∑ k ∈ Finset.range (n / 2 + 2), masterQ t n k) =
      ((n : ℚ) + 2) * S t (n + 2) - ((2 * (n : ℚ) + 3) * t) * S t (n + 1)
        + ((n : ℚ) + 1) * S t n := by
  unfold masterQ
  rw [show n / 2 + 2 = n / 2 + 1 + 1 by omega]
  simp [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have h0 := sum_A_eq_S t n (n / 2 + 1) (by omega : n / 2 ≤ n / 2 + 1)
  have h1 := sum_A_eq_S t (n + 1) (n / 2 + 1) (by omega : (n + 1) / 2 ≤ n / 2 + 1)
  have h2 := sum_A_eq_S t (n + 2) (n / 2 + 1) (by omega : (n + 2) / 2 ≤ n / 2 + 1)
  have h2c : (∑ k ∈ Finset.range (n / 2 + 1 + 1), ((n : ℚ) + 2) * A t (n + 2) k) =
      ((n : ℚ) + 2) * S t (n + 2) := by
    rw [← h2, Finset.mul_sum]
  have h1c : (∑ k ∈ Finset.range (n / 2 + 1 + 1), ((2 * (n : ℚ) + 3) * t) * A t (n + 1) k) =
      ((2 * (n : ℚ) + 3) * t) * S t (n + 1) := by
    rw [← h1, Finset.mul_sum]
  have h0c : (∑ k ∈ Finset.range (n / 2 + 1 + 1), ((n : ℚ) + 1) * A t n k) =
      ((n : ℚ) + 1) * S t n := by
    rw [← h0, Finset.mul_sum]
  rw [h2c, h1c, h0c]

lemma S_recurrence (t : ℚ) (n : ℕ) :
    ((n : ℚ) + 2) * S t (n + 2) - ((2 * (n : ℚ) + 3) * t) * S t (n + 1) + ((n : ℚ) + 1) * S t n = 0 := by
  have h0 := masterSum_zero t n
  rw [masterSum_eq] at h0
  exact h0

lemma S_body (t : ℚ) (m : ℕ) :
    S t m = (∑ j ∈ Finset.range (m / 2 + 1),
      (Nat.choose m (2 * j) : ℚ) * (Nat.choose (2 * j) j : ℚ) * t ^ (m - 2 * j)
        * (((t * t - 1) / 4) ^ j)) := by
  unfold S A
  rfl


end LegendreU

open LegendreU

/-- The 3-term recurrence (Legendre) for the coefficients of
`(1 - 2tX + X^2)^(-1/2)`: with
`U(t,m) := Σ_{j=0}^{⌊m/2⌋} C(m,2j)·C(2j,j)·t^(m−2j)·((t²−1)/4)^j`
(`Finset.range (m / 2 + 1) = {j | j ≤ m/2}`, and `Nat.choose m (2*j) = 0`
for `2j > m` by `Nat.choose_eq_zero_of_lt`), prove for every `m ≥ 1`:
`(m+1)·U(t,m+1) = (2m+1)·t·U(t,m) − m·U(t,m−1)`.

PROOF SKETCH (creative telescoping — mirror the structure of the file
`Commons.Data.Nat.Choose.zagierC_recurrence`, which you should read first):
write `A(m,j)` for the summand `C(m,2j)·C(2j,j)·t^(m−2j)·c^j`, `c = (t²−1)/4`,
and let `S(m) := Σ_{j ∈ range (m+1)} A(m,j)` (equals `U(t,m)`, since the extra
summands vanish: `C(m,2j) = 0` when `2j > m`).  One checks by pure rational
algebra in `m,j,t` (the certificate identity, verified by dividing by `A(m,j)`
and using the ratios `A(m+1,j)/A(m,j) = t·(m+1)/(m+1−2j)`,
`A(m+2,j)/A(m,j) = t²·(m+2)(m+1)/((m+2−2j)(m+1−2j))` and
`A(m,j+1)/A(m,j) = (m−2j)(m−2j−1)(t²−1)/(4(j+1)²t²)`) that for `m ≥ 1` and
`0 ≤ 2j ≤ m−2`:

`(m+2)·A(m+2,j) − (2m+3)·t·A(m+1,j) + (m+1)·A(m,j) = G(m,j) − G(m,j+1)`,

with `G(m,j) := A(m,j)·4·j²·t²·(m+1)/((m+2−2j)·(m+1−2j))` (and `G(m,j+1)`
the same expression at `j+1`).  Summing over `j` telescopes `G`; handle the
remaining boundary `j`-terms near `j ≈ m/2` separately using explicit
evaluations of the corner summands (see the boundary and corner handling in
`zagierC_recurrence`; you need the central-binomial step
`(m+1)·C(2(m+1),m+1) = 2(2m+1)·C(2m,m)`, i.e.
`Nat.succ_mul_centralBinom_succ`).  The result is
`(m+2)·S(m+2) − (2m+3)·t·S(m+1) + (m+1)·S(m) = 0`; reindexing `m ↦ m−1`
gives the target for `m ≥ 2`, and the case `m = 1` is checked directly from
`S(0)=1`, `S(1)=t`, `S(2)=(3t²−1)/2` (prove those three small evaluations as
helper statements inside your file).  All arithmetic is in `ℚ`
(`exact_mod_cast` integer binomial identities); take care to sum over a common
range (e.g. `Finset.range (m+3)`) and to use `Nat.choose_eq_zero_of_lt` so
that out-of-range summands vanish.  Reorganize freely; only this stated
statement matters. -/
theorem legendreU_recurrence (t : ℚ) (m : ℕ) (hm : 1 ≤ m) :
    let U : ℚ → ℕ → ℚ := fun t m =>
        ∑ j ∈ Finset.range (m / 2 + 1),
          (Nat.choose m (2 * j) : ℚ) * (Nat.choose (2 * j) j : ℚ) * t ^ (m - 2 * j) *
            (((t * t - 1) / 4) ^ j)
    ((m : ℚ) + 1) * U t (m + 1) =
      ((2 * (m : ℚ) + 1) * t) * U t m - (m : ℚ) * U t (m - 1) := by

  have hrec := S_recurrence t (m - 1)
  have hIdx1 : (m - 1) + 2 = m + 1 := by omega
  have hIdx2 : (m - 1) + 1 = m := by omega
  rw [hIdx1, hIdx2] at hrec
  have hc1 : ((m - 1 : ℕ) : ℚ) + 2 = (m : ℚ) + 1 := by
    rw [Nat.cast_sub (show 1 ≤ m from hm)]
    ring
  have hc2 : 2 * ((m - 1 : ℕ) : ℚ) + 3 = 2 * (m : ℚ) + 1 := by
    rw [Nat.cast_sub (show 1 ≤ m from hm)]
    ring
  have hc3 : ((m - 1 : ℕ) : ℚ) + 1 = (m : ℚ) := by
    rw [Nat.cast_sub (show 1 ≤ m from hm)]
    ring
  rw [hc1, hc2, hc3] at hrec
  have hgoal : ((m : ℚ) + 1) * S t (m + 1) =
      ((2 * (m : ℚ) + 1) * t) * S t m - (m : ℚ) * S t (m - 1) := by
    nlinarith [hrec]
  dsimp
  rw [← S_body t (m + 1), ← S_body t m, ← S_body t (m - 1)]
  exact hgoal

end Commons.Data.Nat.Choose