import Mathlib
import Submission.CDTPlan.InterfacesA
import Submission.CDT.ZagierHBC
import Submission.Work.ZagC.defs
import Submission.Work.ZagC.telescoping
import Submission.Work.ZagC.lcmfacts
import Submission.Work.ZagC.transfer
import Submission.Work.ZagC.lcmUpto_mul_Hh
import Submission.Work.ZagC.lcmUpto_sq_mul_H2h

/-!
# Integrality of Zagier's `c_n` (`Submission.CDTPlan.ZagierCIntegrality`)

We prove `8·[1,…,n]²·c_n ∈ ℤ` for the sequence `c_n = Submission.CDT.HC_coeff n` of
Calegari–Dimitrov–Tang (arXiv:2408.15403, Lemma `defabc` item 2, `H_C` half).

The proof route:

* (`Submission.Work.ZagC.telescoping`) the explicit second Franel solution
  `g_m = Σ_{k≤m} C(m,k)³((3/8)(H_k − H_{m−k})² + (1/8)(H2_k + H2_{m−k}))` satisfies
  Franel's recurrence `(m+1)²g_{m+1} = (7m²+7m+2)g_m + 8m²g_{m−1}` (`m ≥ 1`) with
  `g_0 = 0`, `g_1 = 1` — proved by creative telescoping on the `ε²`-coefficient of the
  deformed Franel sum `Σ_k C(m,k+ε)³`;
* (`Work.ZagC.transfer`) the binomial transform `Cfun g` satisfies Zagier's
  inhomogeneous recurrence `L_C (Cfun g) = 1`, exactly as `HC_coeff` does, and the two
  initial values agree, so `HC_coeff = Cfun g`;
* (`eight_lcm_sq_g` below, using `Work.ZagC.lcmUpto_mul_Hh` and
  `Work.ZagC.lcmUpto_sq_mul_H2h`) `8·[1,…,m]²·g_m ∈ ℤ` — the denominators of `g_m` are
  cleared by `[1,…,m]²` because `d_m H_k ∈ ℤ` and `d_m² H2_k ∈ ℤ` for `k ≤ m`;
* (`int_transfer` below) for `m ≤ n` one has `[1,…,m] ∣ [1,…,n]`, so
  `8·[1,…,n]²·g_m = q²·(8·[1,…,m]²·g_m)` with `q = [1,…,n]/[1,…,m] ∈ ℤ`; summing against
  the integer binomial coefficients `C(n,m)` gives `8·[1,…,n]²·c_n ∈ ℤ`.
-/

namespace Work.ZagC

open Finset
open scoped BigOperators

noncomputable section

open Submission.CDTPlan

/-! ### Franel's recurrence for `g` and the identification `c_n = Σ_m C(n,m) g_m` -/

/-- `L_F g` is the Kronecker delta at `0`. -/
lemma LFop_g_ite (m : ℕ) : LFop g m = if m = 0 then 1 else 0 := by
  rcases Nat.eq_zero_or_pos m with h | h
  · subst h
    rw [if_pos rfl, LFop]
    simp [g_zero, g_one]
  · rw [if_neg (by omega), LFop_g_zero m h]

/-- Zagier's recurrence operator applied to `HC_coeff` is `1`. -/
lemma LCop_HC (n : ℕ) : LCop Submission.CDT.HC_coeff n = 1 := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h
    rw [LCop]
    norm_num [Submission.CDT.HC_coeff_zero, Submission.CDT.HC_coeff_one]
  · simpa only [LCop] using Submission.CDT.HC_coeff_recurrence n h

/-- Zagier's recurrence operator applied to the binomial transform of `g` is `1`. -/
lemma LCop_Cfun_g (n : ℕ) : LCop (Cfun g) n = 1 := by
  rw [transfer g n]
  have hterm : ∀ m ∈ Finset.range (n+2),
      ((n.choose m : ℕ) : ℚ) * LFop g m = if m = 0 then (1:ℚ) else 0 := by
    intro m _
    rw [LFop_g_ite m]
    by_cases h0 : m = 0
    · subst h0; simp
    · simp [h0]
  rw [Finset.sum_congr rfl hterm,
    Finset.sum_ite_eq' (Finset.range (n+2)) 0 (fun _ => (1:ℚ))]
  simp

/-- `c_n = Σ_{m≤n} C(n,m) g_m`: both sides satisfy Zagier's recurrence with the same
initial values. -/
lemma HC_eq_Cfun_g : Submission.CDT.HC_coeff = Cfun g := by
  funext n
  refine Nat.twoStepInduction ?h0 ?h1 ?hstep n
  · rw [Cfun, Submission.CDT.HC_coeff_zero]
    simp [g_zero]
  · rw [Cfun, Finset.sum_range_succ, Finset.sum_range_succ,
      Submission.CDT.HC_coeff_one]
    norm_num [g_zero, g_one, Nat.choose_self, Nat.choose_zero_right]
  · intro k hk hk1
    have h1 := LCop_Cfun_g (k+1)
    have h2 := LCop_HC (k+1)
    rw [LCop] at h1 h2
    rw [show k + 1 - 1 = k from by omega, show k + 1 + 1 = k + 2 from by omega] at h1 h2
    rw [← hk, ← hk1] at h1
    have hA : (((k+2:ℕ)) : ℚ) ^ 2 ≠ 0 := by positivity
    have hgoal : (((k+2:ℕ)) : ℚ) ^ 2 * Cfun g (k+2)
        - (((k+2:ℕ)) : ℚ) ^ 2 * Submission.CDT.HC_coeff (k+2) = 0 := by
      linear_combination h1 - h2
    have hfac : (((k+2:ℕ)) : ℚ) ^ 2 * (Cfun g (k+2) - Submission.CDT.HC_coeff (k+2)) = 0 := by
      rw [mul_sub]; linarith [hgoal]
    rcases mul_eq_zero.mp hfac with h | h
    · exact absurd h hA
    · linarith [sub_eq_zero.mp h]

/-! ### Integrality of `8·[1,…,m]²·g_m` -/

/-- `8·[1,…,m]²·g_m ∈ ℤ`: the `ℓ¹`-denominators of the harmonic numbers are cleared by
`[1,…,m]` and `[1,…,m]²` respectively. -/
lemma eight_lcm_sq_g (m : ℕ) :
    ∃ z : ℤ, 8 * (lcmUpto m : ℚ) ^ 2 * g m = z := by
  have hterm : ∀ k ≤ m, ∃ w : ℤ, 8 * (lcmUpto m : ℚ) ^ 2 * sm m k = w := by
    intro k hk
    obtain ⟨a, ha⟩ := lcmUpto_mul_Hh m k hk
    obtain ⟨b, hb⟩ := lcmUpto_mul_Hh m (m-k) (by omega)
    obtain ⟨c, hc⟩ := lcmUpto_sq_mul_H2h m k hk
    obtain ⟨e, he⟩ := lcmUpto_sq_mul_H2h m (m-k) (by omega)
    refine ⟨((m.choose k : ℤ))^3 * (3*(a-b)^2 + (c+e)), ?_⟩
    have ha' : (lcmUpto m : ℚ) * Hh k = (a : ℚ) := ha
    have hb' : (lcmUpto m : ℚ) * Hh (m-k) = (b : ℚ) := hb
    have hc' : (lcmUpto m : ℚ) ^ 2 * H2h k = (c : ℚ) := hc
    have he' : (lcmUpto m : ℚ) ^ 2 * H2h (m-k) = (e : ℚ) := he
    have hd' : ((lcmUpto m : ℚ)) * (Hh k - Hh (m-k)) = (a : ℚ) - (b : ℚ) := by
      rw [mul_sub, ha', hb']
    have hd2 : ((lcmUpto m : ℚ)) ^ 2 * (Hh k - Hh (m-k)) ^ 2 = ((a : ℚ) - (b : ℚ)) ^ 2 := by
      rw [← hd']; ring
    have hS2 : ((lcmUpto m : ℚ)) ^ 2 * (H2h k + H2h (m-k)) = (c : ℚ) + (e : ℚ) := by
      rw [mul_add, hc', he']
    unfold sm
    push_cast
    linear_combination (3 * ((m.choose k : ℚ))^3) * hd2 + (((m.choose k : ℚ))^3) * hS2
  classical
  have hsum : 8 * (lcmUpto m : ℚ) ^ 2 * g m
      = ∑ k ∈ Finset.range (m+1), 8 * (lcmUpto m : ℚ) ^ 2 * sm m k := by
    rw [g, Finset.mul_sum]
  let W : ℕ → ℤ := fun k => if hk : k ≤ m then Classical.choose (hterm k hk) else 0
  have hW : ∀ k ∈ Finset.range (m+1),
      8 * (lcmUpto m : ℚ) ^ 2 * sm m k = (W k : ℚ) := by
    intro k hk
    rw [Finset.mem_range] at hk
    have hle : k ≤ m := by omega
    simp only [W, dif_pos hle]
    exact Classical.choose_spec (hterm k hle)
  refine ⟨∑ k ∈ Finset.range (m+1), W k, ?_⟩
  rw [hsum, Finset.sum_congr rfl hW]
  push_cast
  ring

/-! ### Transferring the integrality along the binomial transform -/

/-- If `8·[1,…,m]²·u_m ∈ ℤ` for all `m`, then `8·[1,…,n]²·(Σ_{m≤n} C(n,m)u_m) ∈ ℤ`:
`[1,…,m] ∣ [1,…,n]` for `m ≤ n`. -/
lemma int_transfer (u : ℕ → ℚ)
    (hu : ∀ m : ℕ, ∃ z : ℤ, 8 * (lcmUpto m : ℚ) ^ 2 * u m = z) (n : ℕ) :
    ∃ z : ℤ, 8 * (lcmUpto n : ℚ) ^ 2 * Cfun u n = z := by
  classical
  choose Z hZ using hu
  let Q : ℕ → ℕ := fun m => lcmUpto n / lcmUpto m
  have hterm : ∀ m ∈ Finset.range (n+1),
      8 * (lcmUpto n : ℚ) ^ 2 * (((n.choose m : ℕ) : ℚ) * u m)
        = ((((n.choose m : ℤ) * (Q m : ℤ) ^ 2 * Z m : ℤ)) : ℚ) := by
    intro m hm
    rw [Finset.mem_range] at hm
    have hmn : m ≤ n := by omega
    have hQm : lcmUpto m * Q m = lcmUpto n := by
      simp only [Q]
      exact Nat.mul_div_cancel' (lcmUpto_dvd_of_le hmn)
    have hcast : (lcmUpto n : ℚ) ^ 2 = (lcmUpto m : ℚ) ^ 2 * ((Q m : ℚ)) ^ 2 := by
      rw [← hQm]; push_cast; ring
    have hZ' : 8 * (lcmUpto m : ℚ) ^ 2 * u m = (Z m : ℚ) := hZ m
    rw [hcast]
    calc 8 * ((lcmUpto m : ℚ) ^ 2 * (Q m : ℚ) ^ 2) * (((n.choose m : ℕ) : ℚ) * u m)
        = ((Q m : ℚ) ^ 2 * ((n.choose m : ℕ) : ℚ))
            * (8 * (lcmUpto m : ℚ) ^ 2 * u m) := by ring
      _ = ((Q m : ℚ) ^ 2 * ((n.choose m : ℕ) : ℚ)) * (Z m : ℚ) := by rw [hZ']
      _ = ((((n.choose m : ℤ) * (Q m : ℤ) ^ 2 * Z m : ℤ)) : ℚ) := by push_cast; ring
  refine ⟨∑ m ∈ Finset.range (n+1), (n.choose m : ℤ) * (Q m : ℤ) ^ 2 * Z m, ?_⟩
  rw [Cfun, Finset.mul_sum]
  rw [Finset.sum_congr rfl hterm]
  push_cast
  ring

/-! ### The theorem -/

theorem zagier_c_integrality : ZagierCIntegrality := by
  intro n _
  rw [show Submission.CDT.HC_coeff = Cfun g from HC_eq_Cfun_g]
  exact int_transfer g eight_lcm_sq_g n

end

end Work.ZagC
