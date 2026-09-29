import Submission.Work.ZagC.defs

/-!
# Franel's recurrence for the explicit second solution `g`

Creative telescoping: summing the `ε²`-level certificate identity

`LFop (fun j => t2 j k) m = Y2 m (k+1) - Y2 m k`

over `k ∈ {0,…,m+1}` shows that `YY m = Σ_k t2 m k = 12 g_m` satisfies Franel's
recurrence `LFop YY m = 0` for `m ≥ 1`, hence so does `g`.
-/

namespace Work.ZagC

open Finset
open scoped BigOperators

noncomputable section

/-! ### Binomial ratio lemmas -/

lemma choose_succ_ratio (n j : ℕ) (hj : j ≤ n) :
    (((n+1).choose j : ℕ) : ℚ) = ((n.choose j : ℕ) : ℚ) * ((n:ℚ) + 1) / ((n:ℚ) - (j:ℚ) + 1) := by
  have hcast : ((((n+1).choose j : ℕ) : ℚ)) * (((n+1-j:ℕ)):ℚ)
      = (((n.choose j : ℕ)):ℚ) * (((n+1:ℕ)):ℚ) := by
    exact_mod_cast (Nat.choose_mul_succ_eq n j).symm
  have hsub : (((n+1-j:ℕ)):ℚ) = (n:ℚ) - (j:ℚ) + 1 := by
    rw [show n + 1 - j = (n - j) + 1 from by omega, Nat.cast_add, Nat.cast_sub hj]
    push_cast; ring
  rw [hsub] at hcast
  push_cast at hcast
  have hden : (n:ℚ) - (j:ℚ) + 1 ≠ 0 := by
    have hjn : (j:ℚ) ≤ (n:ℚ) := by exact_mod_cast hj
    intro h0; linarith
  rw [eq_div_iff hden]
  linear_combination hcast

lemma choose_succ_right_ratio (n j : ℕ) (hj : j ≤ n) :
    ((n.choose (j+1) : ℕ) : ℚ) = ((n.choose j : ℕ) : ℚ) * ((n:ℚ) - (j:ℚ)) / ((j:ℚ) + 1) := by
  have hcast : (((n.choose (j+1) : ℕ) : ℚ)) * ((j:ℚ) + 1)
      = (((n.choose j : ℕ)):ℚ) * ((n:ℚ) - (j:ℚ)) := by
    have h := congrArg (fun t : ℕ => (t : ℚ)) (Nat.choose_succ_right_eq n j)
    push_cast at h
    rw [Nat.cast_sub hj] at h
    exact h
  push_cast at hcast
  have hden : (j:ℚ) + 1 ≠ 0 := by positivity
  rw [eq_div_iff hden]
  linear_combination hcast

lemma choose_pred_ratio (n j : ℕ) (h1 : 1 ≤ j) (hj : j ≤ n) :
    ((n.choose (j-1) : ℕ) : ℚ) = ((n.choose j : ℕ) : ℚ) * (j:ℚ) / ((n:ℚ) - (j:ℚ) + 1) := by
  have h := Nat.choose_succ_right_eq n (j-1)
  rw [show j - 1 + 1 = j from by omega, show n - (j-1) = n - j + 1 from by omega] at h
  have hcast : (((n.choose (j-1) : ℕ) : ℚ)) * (((n-j+1:ℕ)):ℚ)
      = (((n.choose j : ℕ)):ℚ) * ((j:ℕ):ℚ) := by
    exact_mod_cast h.symm
  have hsub : (((n-j+1:ℕ)):ℚ) = (n:ℚ) - (j:ℚ) + 1 := by
    rw [show n - j + 1 = (n - j) + 1 from rfl, Nat.cast_add, Nat.cast_sub hj]
    push_cast; ring
  rw [hsub] at hcast
  push_cast at hcast
  have hden : (n:ℚ) - (j:ℚ) + 1 ≠ 0 := by
    have hjn : (j:ℚ) ≤ (n:ℚ) := by exact_mod_cast hj
    intro h0; linarith
  rw [eq_div_iff hden]
  linear_combination hcast

lemma choose_pred_pred_ratio (n j : ℕ) (hn : 1 ≤ n) (hj : j ≤ n) :
    (((n-1).choose j : ℕ) : ℚ) = ((n.choose j : ℕ) : ℚ) * ((n:ℚ) - (j:ℚ)) / (n:ℚ) := by
  have h := Nat.choose_mul_succ_eq (n-1) j
  rw [show n - 1 + 1 = n from by omega] at h
  have hcast : ((((n-1).choose j : ℕ) : ℚ)) * ((n:ℕ):ℚ)
      = (((n.choose j : ℕ)):ℚ) * (((n-j:ℕ)):ℚ) := by
    exact_mod_cast h
  rw [Nat.cast_sub hj] at hcast
  push_cast at hcast
  have hden : (n:ℚ) ≠ 0 := by
    have : (0:ℚ) < (n:ℚ) := by exact_mod_cast (by omega : 0 < n)
    linarith
  rw [eq_div_iff hden]
  linear_combination hcast

lemma choose_succ_succ_ratio (n k : ℕ) (hk : k ≤ n) :
    (((n+1).choose (k+1) : ℕ) : ℚ) = ((n.choose k : ℕ) : ℚ) * ((n:ℚ) + 1) / ((k:ℚ) + 1) := by
  have h1 : (((n+1).choose (k+1) : ℕ) : ℚ)
      = (((n.choose k : ℕ)):ℚ) + (((n.choose (k+1) : ℕ)):ℚ) := by
    exact_mod_cast Nat.choose_succ_succ n k
  have h2 : (((n.choose (k+1) : ℕ)):ℚ) * (((k+1:ℕ)):ℚ)
      = (((n.choose k : ℕ)):ℚ) * (((n-k:ℕ)):ℚ) := by
    exact_mod_cast Nat.choose_succ_right_eq n k
  have hk' : (((k+1:ℕ)):ℚ) + (((n-k:ℕ)):ℚ) = (((n+1:ℕ)):ℚ) := by
    have : k + 1 + (n - k) = n + 1 := by omega
    exact_mod_cast this
  have h2' : (((n.choose (k+1) : ℕ)):ℚ) * ((k:ℚ) + 1)
      = (((n.choose k : ℕ)):ℚ) * ((n:ℚ) - (k:ℚ)) := by
    have := congrArg (fun t : ℕ => (t : ℚ)) (Nat.choose_succ_right_eq n k)
    push_cast at this
    rw [Nat.cast_sub hk] at this
    exact this
  have hk'' : (k:ℚ) + 1 + ((n:ℚ) - (k:ℚ)) = (n:ℚ) + 1 := by
    have h : (k:ℚ) ≤ (n:ℚ) := by exact_mod_cast hk
    ring
  have hcast : ((((n+1).choose (k+1) : ℕ) : ℚ)) * ((k:ℚ) + 1)
      = (((n.choose k : ℕ)):ℚ) * ((n:ℚ) + 1) := by
    rw [h1, add_mul, h2', ← hk'']
    ring
  have hden : (k:ℚ) + 1 ≠ 0 := by positivity
  rw [eq_div_iff hden]
  exact hcast

/-! ### The termwise telescoping identity -/

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
lemma tele_gen (m k : ℕ) (hm : 1 ≤ m) (hk : k + 1 ≤ m) :
    LFop (fun j => t2 j k) m = Y2 m (k+1) - Y2 m k := by
  have hmk : k ≤ m := by omega
  have hx : m + 1 - k = (m - k) + 1 := by omega
  have hy : m - 1 - k = (m - k) - 1 := by omega
  have hz : m + 1 - (k + 1) = m - k := by omega
  have h1 : Hh ((m - k) + 1) = Hh (m - k) + (((m-k)+1:ℕ):ℚ)⁻¹ := Hh_succ (m-k)
  have h1' : H2h ((m - k) + 1) = H2h (m - k) + ((((m-k)+1:ℕ)):ℚ)⁻¹^2 := H2h_succ (m-k)
  have h2 : Hh ((m - k) - 1) = Hh (m - k) - (((m-k:ℕ)):ℚ)⁻¹ := Hh_pred (m-k)
  have h2' : H2h ((m - k) - 1) = H2h (m - k) - ((((m-k:ℕ)):ℚ)⁻¹)^2 := H2h_pred (m-k)
  have h3 : Hh (k + 1) = Hh k + (((k+1:ℕ)):ℚ)⁻¹ := Hh_succ k
  have h3' : H2h (k + 1) = H2h k + ((((k+1:ℕ)):ℚ)⁻¹)^2 := H2h_succ k
  have h5 := choose_succ_ratio m k hmk
  have h6 := choose_pred_pred_ratio m k hm hmk
  have h7 := choose_succ_succ_ratio m k hmk
  have hd4 : (m:ℚ) - (k:ℚ) ≠ 0 := by
    have : (m:ℚ) ≠ (k:ℚ) := by
      exact_mod_cast (by omega : m ≠ k)
    exact sub_ne_zero.mpr this
  have hd1 : (m:ℚ) - (k:ℚ) + 1 ≠ 0 := by
    have hjn : (k:ℚ) + 1 ≤ (m:ℚ) + 1 := by
      exact_mod_cast (by omega : k + 1 ≤ m + 1)
    intro h0; linarith
  have hd2 : (k:ℚ) + 1 ≠ 0 := by positivity
  have hd3 : (m:ℚ) ≠ 0 := by
    have : 0 < m := by omega
    exact_mod_cast Nat.pos_iff_ne_zero.mp this
  have hd5 : (m:ℚ) + 1 ≠ 0 := by positivity
  unfold LFop Y2 t2 Ncert dNcert ddNcert
  simp only []
  rw [hx, hy, hz]
  rw [h1, h1', h2, h2', h3, h3', h5, h6, h7]
  push_cast
  rw [Nat.cast_sub hmk]
  field_simp [hd1, hd2, hd3, hd4, hd5]
  ring

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
lemma tele_eq (m : ℕ) (hm : 1 ≤ m) :
    LFop (fun j => t2 j m) m = Y2 m (m+1) - Y2 m m := by
  have h1 : m + 1 - m = 1 := by omega
  have h2 : m - m = 0 := by omega
  have h3 : m + 1 - (m + 1) = 0 := by omega
  have h4 : Hh (m + 1) = Hh m + (((m+1:ℕ)):ℚ)⁻¹ := Hh_succ m
  have h4' : H2h (m + 1) = H2h m + ((((m+1:ℕ)):ℚ)⁻¹)^2 := H2h_succ m
  have h5 : ((m-1).choose m : ℕ) = 0 := Nat.choose_eq_zero_of_lt (by omega)
  have hd3 : (m:ℚ) ≠ 0 := by
    have : 0 < m := by omega
    exact_mod_cast Nat.pos_iff_ne_zero.mp this
  have hd5 : (m:ℚ) + 1 ≠ 0 := by positivity
  unfold LFop Y2 t2 Ncert dNcert ddNcert
  simp only []
  rw [h1, h2, h3, h4, h4']
  simp only [Hh_zero, Hh_one, H2h_zero, H2h_one, Nat.choose_self,
    Nat.choose_succ_self_right, h5]
  push_cast
  field_simp [hd3, hd5]
  ring

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
lemma tele_succ (m : ℕ) (hm : 1 ≤ m) :
    LFop (fun j => t2 j (m+1)) m = Y2 m (m+2) - Y2 m (m+1) := by
  have h3 : m + 1 - (m + 1) = 0 := by omega
  have h6a : (m.choose (m+1) : ℕ) = 0 := Nat.choose_eq_zero_of_lt (by omega)
  have h6b : ((m-1).choose (m+1) : ℕ) = 0 := Nat.choose_eq_zero_of_lt (by omega)
  have h6c : ((m+1).choose (m+2) : ℕ) = 0 := Nat.choose_eq_zero_of_lt (by omega)
  have hd3 : (m:ℚ) ≠ 0 := by
    have : 0 < m := by omega
    exact_mod_cast Nat.pos_iff_ne_zero.mp this
  have hd5 : (m:ℚ) + 1 ≠ 0 := by positivity
  unfold LFop Y2 t2 Ncert dNcert ddNcert
  simp only []
  simp only [h3, h6a, h6b, h6c, Nat.choose_self]
  push_cast
  norm_num
  field_simp [hd3, hd5]
  ring

/-- The termwise telescoping identity, all `k ≤ m+1`. -/
lemma telescoping (m k : ℕ) (hm : 1 ≤ m) (hk : k ≤ m+1) :
    LFop (fun j => t2 j k) m = Y2 m (k+1) - Y2 m k := by
  rcases lt_or_ge k m with h | h
  · exact tele_gen m k hm (by omega)
  · rcases eq_or_lt_of_le h with h' | h'
    · subst h'; exact tele_eq m hm
    · have hk' : k = m + 1 := by omega
      subst hk'; exact tele_succ m hm

/-! ### Summing over `k` -/

lemma YY_succ_eq (m : ℕ) : YY (m+1) = ∑ k ∈ Finset.range (m+2), t2 (m+1) k := rfl

lemma YY_eq_range (m : ℕ) : YY m = ∑ k ∈ Finset.range (m+2), t2 m k := by
  have h : (∑ k ∈ Finset.range (m+2), t2 m k)
      = (∑ k ∈ Finset.range (m+1), t2 m k) + t2 m (m+1) :=
    Finset.sum_range_succ (fun k => t2 m k) (m+1)
  unfold YY
  rw [h, t2_eq_zero_of_lt (show m < m + 1 by omega), add_zero]

lemma YY_pred_eq_range (m : ℕ) (hm : 1 ≤ m) :
    YY (m-1) = ∑ k ∈ Finset.range (m+2), t2 (m-1) k := by
  have hsub : (∑ k ∈ Finset.range (m - 1 + 1), t2 (m-1) k)
      = ∑ k ∈ Finset.range m, t2 (m-1) k := by
    rw [show m - 1 + 1 = m from by omega]
  unfold YY
  rw [hsub]
  refine Finset.sum_subset (Finset.range_subset_range.mpr (by omega : m ≤ m + 2)) ?_
  intro x hx hxnot
  rw [Finset.mem_range] at hx
  have hx' : m ≤ x := by
    by_contra hcon
    exact hxnot (Finset.mem_range.mpr (by omega))
  exact t2_eq_zero_of_lt (by omega)

lemma LFop_YY_eq (m : ℕ) (hm : 1 ≤ m) :
    LFop YY m = ∑ k ∈ Finset.range (m+2), LFop (fun j => t2 j k) m := by
  have key : (∑ k ∈ Finset.range (m+2), ((((m+1:ℕ)):ℚ)^2 * t2 (m+1) k
        - (7*(m:ℚ)^2 + 7*(m:ℚ) + 2) * t2 m k - 8*(m:ℚ)^2 * t2 (m-1) k))
      = ∑ k ∈ Finset.range (m+2), LFop (fun j => t2 j k) m := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [LFop]
  have key2a := Finset.sum_sub_distrib (s := Finset.range (m+2))
    (f := fun k => ((((m+1:ℕ)):ℚ)^2 * t2 (m+1) k)) (g := fun k => (7*(m:ℚ)^2 + 7*(m:ℚ) + 2) * t2 m k)
  have key2b := Finset.sum_sub_distrib (s := Finset.range (m+2))
    (f := fun k => ((((m+1:ℕ)):ℚ)^2 * t2 (m+1) k - (7*(m:ℚ)^2 + 7*(m:ℚ) + 2) * t2 m k))
    (g := fun k => 8*(m:ℚ)^2 * t2 (m-1) k)
  have key2 : (∑ k ∈ Finset.range (m+2), ((((m+1:ℕ)):ℚ)^2 * t2 (m+1) k
        - (7*(m:ℚ)^2 + 7*(m:ℚ) + 2) * t2 m k - 8*(m:ℚ)^2 * t2 (m-1) k))
      = (∑ k ∈ Finset.range (m+2), ((((m+1:ℕ)):ℚ)^2 * t2 (m+1) k))
        - (∑ k ∈ Finset.range (m+2), (7*(m:ℚ)^2 + 7*(m:ℚ) + 2) * t2 m k)
        - (∑ k ∈ Finset.range (m+2), 8*(m:ℚ)^2 * t2 (m-1) k) := by
    rw [key2b, key2a]
  rw [LFop, YY_succ_eq m, YY_eq_range m, YY_pred_eq_range m hm,
    Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← key2, key]

lemma LFop_YY_zero (m : ℕ) (hm : 1 ≤ m) : LFop YY m = 0 := by
  rw [LFop_YY_eq m hm]
  have hterm : ∀ k ∈ Finset.range (m+2), LFop (fun j => t2 j k) m = Y2 m (k+1) - Y2 m k := by
    intro k hk
    rw [Finset.mem_range] at hk
    exact telescoping m k hm (by omega)
  rw [Finset.sum_congr rfl hterm, Finset.sum_range_sub (fun k => Y2 m k) (m+2)]
  rw [Y2_eq_zero_of_lt (show m + 1 < m + 2 by omega), Y2_zero]
  ring

lemma LFop_smul (c : ℚ) (u : ℕ → ℚ) (m : ℕ) : LFop (fun t => c * u t) m = c * LFop u m := by
  unfold LFop; ring

lemma LFop_g_zero (m : ℕ) (hm : 1 ≤ m) : LFop g m = 0 := by
  have h := LFop_YY_zero m hm
  have h2 : YY = fun t => 12 * g t := by
    funext t; rw [YY_eq_twelve_g]
  rw [h2, LFop_smul] at h
  have h12 : (12 : ℚ) ≠ 0 := by norm_num
  exact (mul_eq_zero.mp h).resolve_left h12

lemma g_zero : g 0 = 0 := by
  unfold g sm
  simp

lemma g_one : g 1 = 1 := by
  unfold g sm
  rw [Finset.sum_range_succ, Finset.sum_range_succ]
  norm_num [Hh_zero, Hh_one, H2h_zero, H2h_one, Nat.choose_self, Nat.choose_zero_right]

end

end Work.ZagC
