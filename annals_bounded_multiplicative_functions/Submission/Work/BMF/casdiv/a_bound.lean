import Mathlib
import Submission.Work.BMF.halasz_defs
import Submission.Work.BMF.halasz_basic
import Submission.Work.BMF.halasz_intM
import Submission.Work.BMF.casdiv.wdb_support
import Submission.Work.BMF.casdiv.yr_bound
import Submission.Work.BMF.halasz_mertens_aux
import Submission.Work.BMF.mrlas.Wsup_measurable
import Submission.Work.BMF.mrlas.Wsup_le_Zrcp
import Submission.Work.BMF.mrlas.casdiv_zrcp_ratio

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 2000000

namespace Work.BMF.casdiv

open Finset Real MeasureTheory intervalIntegral
open scoped BigOperators

/-! ## Elementary estimates -/

private lemma one_sub_exp_neg_ge {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    s / 2 ≤ 1 - Real.exp (-s) := by
  have hexp : (1:ℝ) + s ≤ Real.exp s := by linarith [Real.add_one_le_exp s]
  have h2 : Real.exp (-s) ≤ 1 / (1 + s) := by
    rw [Real.exp_neg]
    have h := one_div_le_one_div_of_le (show (0:ℝ) < 1 + s by linarith) hexp
    simpa [one_div] using h
  have h4 : s / 2 ≤ s / (1 + s) := by
    rw [div_le_div_iff₀ (by norm_num) (by linarith)]
    nlinarith
  have h5 : 1 - 1 / (1 + s) = s / (1 + s) := by
    field_simp
    ring
  linarith

/-- `Σ_{k<n} r^k ≤ (1-r)⁻¹` for `0 ≤ r < 1`. -/
private lemma geom_sum_le_inv {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (n : ℕ) :
    (∑ k ∈ Finset.range n, r^k) ≤ (1-r)⁻¹ := by
  have h := geom_sum_mul_neg r n
  have h2 : 0 < 1 - r := by linarith
  rw [inv_eq_one_div, le_div_iff₀ h2, h]
  have h3 : 0 ≤ r^n := pow_nonneg hr0 n
  linarith

private lemma geom_exp_sum_le {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) (n : ℕ) :
    (∑ k ∈ Finset.range n, Real.exp (-((k:ℝ) * α))) ≤ 2 / α := by
  have hr0 : 0 ≤ Real.exp (-α) := (Real.exp_pos _).le
  have hr1 : Real.exp (-α) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  have hsum : (∑ k ∈ Finset.range n, (Real.exp (-α))^k)
      = ∑ k ∈ Finset.range n, Real.exp (-((k:ℝ) * α)) := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [← hsum]
  have hlt := geom_sum_le_inv hr0 hr1 n
  have h1 : α / 2 ≤ 1 - Real.exp (-α) := one_sub_exp_neg_ge hα0.le hα1
  have hpos : 0 < 1 - Real.exp (-α) := lt_of_lt_of_le (by linarith) h1
  have h2 : (1 - Real.exp (-α))⁻¹ ≤ (α/2)⁻¹ :=
    (inv_le_inv₀ hpos (by linarith : (0:ℝ) < α/2)).mpr h1
  have h3 : (α/2)⁻¹ = 2 / α := by field_simp
  rw [h3] at h2
  linarith

private lemma sum_range_two_pow_le (n : ℕ) : (∑ k ∈ Finset.range n, (2:ℝ)^k) ≤ (2:ℝ)^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, pow_succ]
    linarith

private lemma sqrt_exp (t : ℝ) : Real.sqrt (Real.exp t) = Real.exp (t/2) := by
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (Real.exp_pos t), Real.log_exp]
  congr 1
  ring

private lemma exp_two_pow_succ (j : ℕ) :
    Real.exp ((2:ℝ)^(j+1)) = (Real.exp ((2:ℝ)^j))^2 := by
  rw [pow_succ, pow_two, ← Real.exp_add]
  congr 1
  ring

private lemma log_eleven_gt_two : (2:ℝ) < Real.log 11 := by
  rw [← Real.exp_lt_exp, Real.exp_log (by norm_num : (0:ℝ) < 11)]
  have h2 : Real.exp 2 = (Real.exp 1)^2 := by
    rw [show (2:ℝ) = 1 + 1 by norm_num, Real.exp_add]
    ring
  rw [h2]
  nlinarith [Real.exp_one_lt_d9, Real.exp_pos 1]

/-- `Σ_{k<n} (1/2)^k ≤ 2`. -/
private lemma geom_half_sum_le (n : ℕ) : (∑ k ∈ Finset.range n, ((1:ℝ)/2)^k) ≤ 2 := by
  have hlt := geom_sum_le_inv (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1:ℝ)/2 < 1) n
  have h : (1 - ((1:ℝ)/2))⁻¹ = 2 := by norm_num
  rw [h] at hlt
  exact hlt

/-- `Σ_{k ∈ range n} (1/2)^(k+1) ≤ 1`. -/
private lemma geom_half_sum_shift_le (n : ℕ) :
    (∑ k ∈ Finset.range n, ((1:ℝ)/2)^(k+1)) ≤ 1 := by
  have h1 : (∑ k ∈ Finset.range n, ((1:ℝ)/2)^(k+1))
      = ((1:ℝ)/2) * ∑ k ∈ Finset.range n, ((1:ℝ)/2)^k := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [pow_succ]
    ring
  rw [h1]
  have h2 := geom_half_sum_le n
  linarith

/-! ## The logarithmically weighted prime sum -/

/-- `Σ_{p ≤ x} (log p) p^{-(1+α)} ≤ 6 log 4 / α` for `3 ≤ x`, `0 < α ≤ 1`. -/
private lemma sum_log_rpow_le {x α : ℝ} (hx : 3 ≤ x) (hα0 : 0 < α) (hα1 : α ≤ 1) :
    (∑ p ∈ (⌊x⌋₊).primesLE, Real.log p * (p:ℝ) ^ (-(1 + α))) ≤ 6 * Real.log 4 / α := by
  have hx0 : (0:ℝ) < x := by linarith
  have hlogx0 : 0 < Real.log x := Real.log_pos (by linarith)
  set K : ℕ := ⌊Real.log x⌋₊ with hKdef
  have hKp : ∀ p ∈ (⌊x⌋₊).primesLE, ⌊Real.log p⌋₊ ≤ K := by
    intro p hp
    have hp1 : p ≤ ⌊x⌋₊ := (Nat.mem_primesLE.mp hp).1
    have hppos : (0:ℝ) < (p:ℝ) := by
      exact_mod_cast (Nat.Prime.pos (Nat.mem_primesLE.mp hp).2)
    have hpx : (p:ℝ) ≤ x := le_trans (by exact_mod_cast hp1) (Nat.floor_le hx0.le)
    exact Nat.floor_mono (Real.log_le_log hppos hpx)
  have hsplit : (∑ p ∈ (⌊x⌋₊).primesLE, Real.log p * (p:ℝ) ^ (-(1 + α)))
      = ∑ k ∈ Finset.range (K+1),
          ∑ p ∈ ((⌊x⌋₊).primesLE.filter (fun p : ℕ => ⌊Real.log p⌋₊ = k)),
            Real.log p * (p:ℝ) ^ (-(1 + α)) := by
    have h1 : ∀ p ∈ (⌊x⌋₊).primesLE, Real.log p * (p:ℝ) ^ (-(1 + α))
        = ∑ k ∈ Finset.range (K+1),
            (if ⌊Real.log p⌋₊ = k then Real.log p * (p:ℝ) ^ (-(1 + α)) else 0) := by
      intro p hp
      rw [Finset.sum_ite_eq,
        if_pos (Finset.mem_range.mpr (Nat.lt_succ_of_le (hKp p hp)))]
    calc (∑ p ∈ (⌊x⌋₊).primesLE, Real.log p * (p:ℝ) ^ (-(1 + α)))
        = ∑ p ∈ (⌊x⌋₊).primesLE, ∑ k ∈ Finset.range (K+1),
            (if ⌊Real.log p⌋₊ = k then Real.log p * (p:ℝ) ^ (-(1 + α)) else 0) :=
          Finset.sum_congr rfl h1
      _ = ∑ k ∈ Finset.range (K+1), ∑ p ∈ (⌊x⌋₊).primesLE,
            (if ⌊Real.log p⌋₊ = k then Real.log p * (p:ℝ) ^ (-(1 + α)) else 0) :=
          Finset.sum_comm
      _ = ∑ k ∈ Finset.range (K+1),
          ∑ p ∈ ((⌊x⌋₊).primesLE.filter (fun p : ℕ => ⌊Real.log p⌋₊ = k)),
            Real.log p * (p:ℝ) ^ (-(1 + α)) := by
          refine Finset.sum_congr rfl (fun k _ => ?_)
          rw [Finset.sum_filter]
  refine le_trans hsplit.le ?_
  have hterm : ∀ k ∈ Finset.range (K+1),
      (∑ p ∈ ((⌊x⌋₊).primesLE.filter (fun p : ℕ => ⌊Real.log p⌋₊ = k)),
          Real.log p * (p:ℝ) ^ (-(1 + α)))
        ≤ Real.exp (-(k:ℝ) * (1 + α)) * (Real.log 4 * Real.exp ((k:ℝ) + 1)) := by
    intro k _
    have hpt : ∀ p ∈ (⌊x⌋₊).primesLE.filter (fun p : ℕ => ⌊Real.log p⌋₊ = k),
        Real.log p * (p:ℝ) ^ (-(1 + α))
          ≤ Real.exp (-(k:ℝ) * (1 + α)) * Real.log p := by
      intro p hp
      obtain ⟨hpP, hpk⟩ := Finset.mem_filter.mp hp
      have hpprime : p.Prime := (Nat.mem_primesLE.mp hpP).2
      have hppos : (0:ℝ) < (p:ℝ) := by exact_mod_cast hpprime.pos
      have hlogp : 0 < Real.log p := Real.log_pos (by exact_mod_cast hpprime.one_lt)
      have hpge : (k:ℝ) ≤ Real.log p := by
        have h1 : ((⌊Real.log p⌋₊ : ℕ) : ℝ) ≤ Real.log p := Nat.floor_le hlogp.le
        rw [hpk] at h1
        exact h1
      have hrpow : (p:ℝ) ^ (-(1+α)) ≤ Real.exp (-(k:ℝ)*(1+α)) := by
        rw [Real.rpow_def_of_pos hppos, Real.exp_le_exp]
        nlinarith [hpge, hα0]
      calc Real.log p * (p:ℝ)^(-(1+α)) ≤ Real.log p * Real.exp (-(k:ℝ)*(1+α)) :=
            mul_le_mul_of_nonneg_left hrpow hlogp.le
        _ = Real.exp (-(k:ℝ)*(1+α)) * Real.log p := by ring
    have hfiber : (∑ p ∈ (⌊x⌋₊).primesLE.filter (fun p : ℕ => ⌊Real.log p⌋₊ = k), Real.log p)
        ≤ Real.log 4 * Real.exp ((k:ℝ) + 1) := by
      have hsub : (⌊x⌋₊).primesLE.filter (fun p : ℕ => ⌊Real.log p⌋₊ = k)
          ⊆ (⌊Real.exp ((k:ℝ)+1)⌋₊).primesLE := by
        intro p hp
        obtain ⟨hpP, hpk⟩ := Finset.mem_filter.mp hp
        rw [Nat.mem_primesLE] at hpP ⊢
        refine ⟨?_, hpP.2⟩
        apply Nat.le_floor
        have h1 : Real.log (p:ℝ) < (k:ℝ) + 1 := by
          have h2 := Nat.lt_floor_add_one (Real.log (p:ℝ))
          rw [hpk] at h2
          push_cast at h2
          exact h2
        calc (p:ℝ) = Real.exp (Real.log (p:ℝ)) :=
              (Real.exp_log (by exact_mod_cast (Nat.Prime.pos hpP.2))).symm
          _ ≤ Real.exp ((k:ℝ) + 1) := le_of_lt (Real.exp_lt_exp.mpr h1)
      calc (∑ p ∈ (⌊x⌋₊).primesLE.filter (fun p : ℕ => ⌊Real.log p⌋₊ = k), Real.log p)
          ≤ ∑ p ∈ (⌊Real.exp ((k:ℝ)+1)⌋₊).primesLE, Real.log p := by
            refine Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p hp _ => ?_)
            exact Real.log_nonneg (by
              exact_mod_cast (Nat.Prime.one_le (Nat.prime_of_mem_primesLE hp)))
        _ = Chebyshev.theta (↑⌊Real.exp ((k:ℝ)+1)⌋₊) :=
            (Chebyshev.theta_eq_sum_primesLE_log _).symm
        _ ≤ Real.log 4 * (⌊Real.exp ((k:ℝ)+1)⌋₊ : ℝ) :=
            Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg _)
        _ ≤ Real.log 4 * Real.exp ((k:ℝ)+1) := by
            refine mul_le_mul_of_nonneg_left ?_ (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 4))
            exact Nat.floor_le (le_of_lt (Real.exp_pos _))
    calc (∑ p ∈ (⌊x⌋₊).primesLE.filter (fun p : ℕ => ⌊Real.log p⌋₊ = k),
            Real.log p * (p:ℝ)^(-(1+α)))
        ≤ ∑ p ∈ (⌊x⌋₊).primesLE.filter (fun p : ℕ => ⌊Real.log p⌋₊ = k),
            Real.exp (-(k:ℝ)*(1+α)) * Real.log p := Finset.sum_le_sum hpt
      _ = Real.exp (-(k:ℝ)*(1+α)) *
            (∑ p ∈ (⌊x⌋₊).primesLE.filter (fun p : ℕ => ⌊Real.log p⌋₊ = k), Real.log p) :=
          (Finset.mul_sum _ _ _).symm
      _ ≤ Real.exp (-(k:ℝ)*(1+α)) * (Real.log 4 * Real.exp ((k:ℝ)+1)) :=
          mul_le_mul_of_nonneg_left hfiber (Real.exp_pos _).le
  refine le_trans (Finset.sum_le_sum hterm) ?_
  have hk_sum : (∑ k ∈ Finset.range (K+1),
        Real.exp (-(k:ℝ) * (1 + α)) * (Real.log 4 * Real.exp ((k:ℝ) + 1)))
      = Real.log 4 * Real.exp 1 * (∑ k ∈ Finset.range (K+1), Real.exp (-((k:ℝ) * α))) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    have h1 : -(k:ℝ) * (1 + α) + ((k:ℝ) + 1) = 1 + (-((k:ℝ) * α)) := by ring
    calc Real.exp (-(k:ℝ) * (1 + α)) * (Real.log 4 * Real.exp ((k:ℝ) + 1))
        = Real.log 4 * (Real.exp (-(k:ℝ) * (1 + α)) * Real.exp ((k:ℝ) + 1)) := by ring
      _ = Real.log 4 * Real.exp (-(k:ℝ) * (1 + α) + ((k:ℝ) + 1)) := by
            conv_rhs => rw [Real.exp_add]
      _ = Real.log 4 * Real.exp (1 + (-((k:ℝ) * α))) := by rw [h1]
      _ = Real.log 4 * Real.exp 1 * Real.exp (-((k:ℝ) * α)) := by
          rw [Real.exp_add]; ring
  rw [hk_sum]
  have hgeom := geom_exp_sum_le hα0 hα1 (K+1)
  have hexp1 : Real.exp 1 ≤ 3 := le_of_lt Real.exp_one_lt_three
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  calc Real.log 4 * Real.exp 1 * (∑ k ∈ Finset.range (K+1), Real.exp (-((k:ℝ) * α)))
      ≤ Real.log 4 * Real.exp 1 * (2 / α) :=
        mul_le_mul_of_nonneg_left hgeom (by positivity)
    _ = 2 * Real.exp 1 * Real.log 4 / α := by ring
    _ ≤ 6 * Real.log 4 / α := by
        refine div_le_div_of_nonneg_right ?_ hα0.le
        nlinarith


/-! ## The difference of two `Wsup` values -/

/-- For a `1`-bounded `f`, the difference of the two prime sums `Re Σ_{p ≤ x} f p p^{-1-α-it}` and
`Re Σ_{p ≤ x} f p p^{-1-β-it}` is at most `Σ_{p ≤ x} (p^{-(1+α)} - p^{-(1+β)})` for every `t`. -/
private lemma vF_re_le_add (f : ℕ → ℂ) (hb : ∀ n, ‖f n‖ ≤ 1) (x : ℝ) {α β : ℝ} (hαβ : α ≤ β)
    (T : ℝ) (t : {t : ℝ // |t| ≤ T}) :
    (vF f x (((1+α:ℝ):ℂ) + t.1 * Complex.I)).re
      ≤ (vF f x (((1+β:ℝ):ℂ) + t.1 * Complex.I)).re
        + ∑ p ∈ (⌊x⌋₊).primesLE, ((p:ℝ) ^ (-(1+α)) - (p:ℝ) ^ (-(1+β))) := by
  have hterm : ∀ p ∈ (⌊x⌋₊).primesLE,
      (f p * ((p:ℂ)^(-(((1+α:ℝ):ℂ) + t.1 * Complex.I)))).re
        ≤ (f p * ((p:ℂ)^(-(((1+β:ℝ):ℂ) + t.1 * Complex.I)))).re
          + ((p:ℝ)^(-(1+α)) - (p:ℝ)^(-(1+β))) := by
    intro p hp
    have hpprime : p.Prime := (Nat.mem_primesLE.mp hp).2
    have hp0nat : 0 < p := hpprime.pos
    have hp0 : (0:ℝ) < p := by exact_mod_cast hp0nat
    have hp1 : (1:ℝ) ≤ p := by exact_mod_cast (show 1 ≤ p by omega)
    have hpne : (p:ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hp0nat)
    have hfac : (p:ℂ)^(-(((1+α:ℝ):ℂ) + t.1 * Complex.I))
        = (p:ℂ)^(-(((1+β:ℝ):ℂ) + t.1 * Complex.I)) * (p:ℂ)^(-(((α-β:ℝ):ℂ))) := by
      rw [show -(((1+α:ℝ):ℂ) + t.1 * Complex.I)
            = (-(((1+β:ℝ):ℂ) + t.1 * Complex.I)) + (-(((α-β:ℝ):ℂ))) by push_cast; ring,
        Complex.cpow_add _ _ hpne]
    have hreal : (p:ℂ)^(-(((α-β:ℝ):ℂ))) = (((p:ℝ)^(-(α-β)) : ℝ) : ℂ) := by
      rw [show (p:ℂ) = (((p:ℝ)):ℂ) by simp]
      rw [show -(((α-β:ℝ):ℂ)) = (((-(α-β):ℝ):ℂ)) by push_cast; ring]
      rw [← Complex.ofReal_cpow hp0.le]
    have hr1 : (1:ℝ) ≤ (p:ℝ)^(-(α-β)) := by
      rw [show -(α-β) = β-α by ring]
      calc (1:ℝ) = (p:ℝ)^(0:ℝ) := (Real.rpow_zero _).symm
        _ ≤ (p:ℝ)^(β-α) := Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
    have hdiff : f p * ((p:ℂ)^(-(((1+α:ℝ):ℂ) + t.1 * Complex.I)))
          - f p * ((p:ℂ)^(-(((1+β:ℝ):ℂ) + t.1 * Complex.I)))
        = (f p * ((p:ℂ)^(-(((1+β:ℝ):ℂ) + t.1 * Complex.I))))
          * ((((p:ℝ)^(-(α-β)) : ℝ) : ℂ) - 1) := by
      rw [hfac, hreal]; ring
    have hnorm1 : ‖(f p * ((p:ℂ)^(-(((1+β:ℝ):ℂ) + t.1 * Complex.I))))‖ ≤ (p:ℝ)^(-(1+β)) := by
      rw [norm_mul, Complex.norm_natCast_cpow_of_pos hp0nat,
        show (-(((1+β:ℝ):ℂ) + t.1 * Complex.I)).re = -(1+β) by simp]
      calc ‖f p‖ * (p:ℝ)^(-(1+β)) ≤ 1 * (p:ℝ)^(-(1+β)) :=
            mul_le_mul_of_nonneg_right (hb p) (Real.rpow_nonneg (Nat.cast_nonneg p) _)
        _ = _ := one_mul _
    have hnorm2 : ‖((((p:ℝ)^(-(α-β)) : ℝ) : ℂ) - 1)‖ = (p:ℝ)^(-(α-β)) - 1 := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg]
      linarith
    have hrpow : (p:ℝ)^(-(1+β)) * ((p:ℝ)^(-(α-β)) - 1)
        = (p:ℝ)^(-(1+α)) - (p:ℝ)^(-(1+β)) := by
      rw [mul_sub, mul_one, ← Real.rpow_add hp0]
      congr 1
      ring
    have hdiff_le : (f p * ((p:ℂ)^(-(((1+α:ℝ):ℂ) + t.1 * Complex.I)))).re
             - (f p * ((p:ℂ)^(-(((1+β:ℝ):ℂ) + t.1 * Complex.I)))).re
           ≤ (p:ℝ)^(-(1+α)) - (p:ℝ)^(-(1+β)) := by
      rw [← Complex.sub_re, hdiff]
      refine le_trans (Complex.re_le_norm _) ?_
      rw [norm_mul, hnorm2]
      refine le_trans (mul_le_mul hnorm1 le_rfl (by linarith)
        (Real.rpow_nonneg (Nat.cast_nonneg p) _)) ?_
      exact le_of_eq hrpow
    linarith [hdiff_le]
  have h1 : (vF f x (((1+α:ℝ):ℂ) + t.1 * Complex.I)).re
      = ∑ p ∈ (⌊x⌋₊).primesLE,
          (f p * ((p:ℂ)^(-(((1+α:ℝ):ℂ) + t.1 * Complex.I)))).re := by
    rw [vF]
    exact map_sum Complex.reAddGroupHom _ _
  have h2 : (vF f x (((1+β:ℝ):ℂ) + t.1 * Complex.I)).re
      = ∑ p ∈ (⌊x⌋₊).primesLE,
          (f p * ((p:ℂ)^(-(((1+β:ℝ):ℂ) + t.1 * Complex.I)))).re := by
    rw [vF]
    exact map_sum Complex.reAddGroupHom _ _
  rw [h1, h2, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum hterm

/-- `Wsup f x α T ≤ Wsup f x β T + Σ_{p ≤ x} (p^{-(1+α)} - p^{-(1+β)})` for `α ≤ β`. -/
private lemma Wsup_le_add_sum (f : ℕ → ℂ) (hb : ∀ n, ‖f n‖ ≤ 1) (x α β T : ℝ)
    (hαβ : α ≤ β) (hT : 0 ≤ T) :
    Wsup f x α T ≤ Wsup f x β T +
      ∑ p ∈ (⌊x⌋₊).primesLE, ((p:ℝ) ^ (-(1+α)) - (p:ℝ) ^ (-(1+β))) := by
  haveI : Nonempty {t : ℝ // |t| ≤ T} := ⟨⟨0, by rw [abs_zero]; exact hT⟩⟩
  have hbdd : BddAbove (Set.range (fun t : {t : ℝ // |t| ≤ T} =>
      (vF f x (((1+β:ℝ):ℂ) + t.1 * Complex.I)).re)) := by
    refine ⟨∑ p ∈ (⌊x⌋₊).primesLE, (p:ℝ)^(-(1+β)), ?_⟩
    rintro y ⟨t, rfl⟩
    calc (vF f x (((1+β:ℝ):ℂ) + t.1 * Complex.I)).re
        ≤ ∑ p ∈ (⌊x⌋₊).primesLE, ‖f p * ((p:ℂ)^(-(((1+β:ℝ):ℂ) + t.1 * Complex.I)))‖ := by
          rw [vF, Complex.re_sum]
          exact Finset.sum_le_sum (fun p _ => Complex.re_le_norm _)
      _ ≤ ∑ p ∈ (⌊x⌋₊).primesLE, (p:ℝ)^(-(1+β)) := by
          refine Finset.sum_le_sum (fun p hp => ?_)
          have hp2 : 0 < p := (Nat.mem_primesLE.mp hp).2.pos
          rw [norm_mul, Complex.norm_natCast_cpow_of_pos hp2,
            show (-(((1+β:ℝ):ℂ) + t.1 * Complex.I)).re = -(1+β) by simp]
          calc ‖f p‖ * (p:ℝ)^(-(1+β)) ≤ 1 * (p:ℝ)^(-(1+β)) :=
                mul_le_mul_of_nonneg_right (hb p) (Real.rpow_nonneg (Nat.cast_nonneg p) _)
            _ = _ := one_mul _
  have key : Wsup f x α T ≤ Wsup f x β T +
      ∑ p ∈ (⌊x⌋₊).primesLE, ((p:ℝ) ^ (-(1+α)) - (p:ℝ) ^ (-(1+β))) := by
    have h : (⨆ t : {t : ℝ // |t| ≤ T},
        (vF f x (((1+α:ℝ):ℂ) + t.1 * Complex.I)).re)
        ≤ Wsup f x β T + ∑ p ∈ (⌊x⌋₊).primesLE, ((p:ℝ)^(-(1+α)) - (p:ℝ)^(-(1+β))) :=
      ciSup_le (fun t => by
        have h1 := vF_re_le_add f hb x hαβ T t
        have h2 : (vF f x (((1+β:ℝ):ℂ) + t.1 * Complex.I)).re ≤ Wsup f x β T :=
          le_ciSup hbdd t
        linarith)
    exact h
  exact key

/-- `Wsup f x α T` is "almost monotone" in `α`: lowering `α` can raise the value by at most an
absolute constant, as long as `1 / log x ≤ α ≤ β ≤ 2 α` and `β ≤ 1`. -/
private theorem Wsup_factor_two :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : ℕ → ℂ), (∀ n, ‖f n‖ ≤ 1) → ∀ x α β T : ℝ,
      3 ≤ x → 1 / Real.log x ≤ α → α ≤ β → β ≤ 2 * α → β ≤ 1 → 0 ≤ T →
        Wsup f x α T ≤ Wsup f x β T + C := by
  refine ⟨6 * Real.log 4 + 1, by positivity, ?_⟩
  intro f hb x α β T hx hα hαβ hβ2 hβ1 hT
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have hα0 : 0 < α := lt_of_lt_of_le
    (by rw [one_div]; exact inv_pos.mpr (Real.log_pos (by linarith))) hα
  have hα1 : α ≤ 1 := le_trans hαβ hβ1
  have hS := sum_log_rpow_le hx hα0 hα1
  have hD := Wsup_le_add_sum f hb x α β T hαβ hT
  have hterm : ∀ p ∈ (⌊x⌋₊).primesLE,
      (p:ℝ)^(-(1+α)) - (p:ℝ)^(-(1+β))
        ≤ (β - α) * (Real.log p * (p:ℝ)^(-(1+α))) := by
    intro p hp
    have hpprime : p.Prime := (Nat.mem_primesLE.mp hp).2
    have hp0 : (0:ℝ) < (p:ℝ) := by exact_mod_cast hpprime.pos
    have h1 : (p:ℝ)^(-(1+α)) - (p:ℝ)^(-(1+β))
        = (p:ℝ)^(-(1+α)) * (1 - (p:ℝ)^(-(β-α))) := by
      rw [mul_sub, mul_one, ← Real.rpow_add hp0]
      congr 1
      ring
    have h2 : 1 - (p:ℝ)^(-(β-α)) ≤ (β-α) * Real.log p := by
      have h3 : -(Real.log (p:ℝ) * (β-α)) + 1 ≤ Real.exp (-(Real.log (p:ℝ) * (β-α))) :=
        Real.add_one_le_exp _
      rw [Real.rpow_def_of_pos hp0,
        show Real.log (p:ℝ) * -(β-α) = -(Real.log (p:ℝ) * (β-α)) by ring]
      linarith
    rw [h1]
    calc (p:ℝ)^(-(1+α)) * (1 - (p:ℝ)^(-(β-α)))
        ≤ (p:ℝ)^(-(1+α)) * ((β-α) * Real.log p) :=
          mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg hp0.le _)
      _ = (β - α) * (Real.log p * (p:ℝ)^(-(1+α))) := by ring
  have hDle : (∑ p ∈ (⌊x⌋₊).primesLE, ((p:ℝ)^(-(1+α)) - (p:ℝ)^(-(1+β))))
      ≤ (β-α) * (6 * Real.log 4 / α) := by
    calc (∑ p ∈ (⌊x⌋₊).primesLE, ((p:ℝ)^(-(1+α)) - (p:ℝ)^(-(1+β))))
        ≤ ∑ p ∈ (⌊x⌋₊).primesLE, (β - α) * (Real.log p * (p:ℝ)^(-(1+α))) :=
          Finset.sum_le_sum hterm
      _ = (β-α) * (∑ p ∈ (⌊x⌋₊).primesLE, Real.log p * (p:ℝ)^(-(1+α))) := by
          rw [Finset.mul_sum]
      _ ≤ (β-α) * (6 * Real.log 4 / α) :=
          mul_le_mul_of_nonneg_left hS (by linarith)
  have hfin : (β-α) * (6 * Real.log 4 / α) ≤ 6 * Real.log 4 := by
    have hl4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    have hdiv : (β-α)/α ≤ 1 := by
      rw [div_le_one hα0]
      linarith
    calc (β-α) * (6 * Real.log 4 / α) = ((β-α)/α) * (6 * Real.log 4) := by ring
      _ ≤ 1 * (6 * Real.log 4) := mul_le_mul_of_nonneg_right hdiv (by linarith)
      _ = 6 * Real.log 4 := one_mul _
  linarith [hD, hDle, hfin]

/-! ## Turning the almost-monotonicity into an integral comparison -/

private lemma intervalIntegrable_expWsup_div {f : ℕ → ℂ} (hb : ∀ n, ‖f n‖ ≤ 1) {x T a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun γ : ℝ => Real.exp (Wsup f x γ T) / γ) volume a b := by
  have hm : AEStronglyMeasurable (fun γ : ℝ => Real.exp (Wsup f x γ T) / γ)
      (volume.restrict (Set.uIoc a b)) :=
    (((Work.BMF.mrlas.Wsup_measurable f x T).exp).div measurable_id).aestronglyMeasurable
  refine IntervalIntegrable.mono_fun' (g := fun _ : ℝ => Real.exp (Zrcp x) / a)
    intervalIntegrable_const hm ?_
  filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_uIoc] with γ hγ
  rw [Set.uIoc_of_le hab] at hγ
  have hγ0 : 0 < γ := lt_of_lt_of_le ha hγ.1.le
  have hW : Real.exp (Wsup f x γ T) ≤ Real.exp (Zrcp x) :=
    Real.exp_le_exp.mpr (Work.BMF.mrlas.Wsup_le_Zrcp f hb x T γ (le_of_lt hγ0))
  rw [Real.norm_of_nonneg (div_nonneg (Real.exp_nonneg _) hγ0.le)]
  calc Real.exp (Wsup f x γ T) / γ ≤ Real.exp (Zrcp x) / γ :=
        div_le_div_of_nonneg_right hW hγ0.le
    _ ≤ Real.exp (Zrcp x) / a := div_le_div_of_nonneg_left (Real.exp_nonneg _) ha hγ.1.le

/-- The window bound: lowering `α` to `α/2` costs at most a constant factor in `exp (Wsup …)`,
and the corresponding integral over the window `[α, 2α]` dominates it. -/
private theorem exp_Wsup_le_window :
    ∃ K : ℝ, 0 < K ∧ ∀ (f : ℕ → ℂ), (∀ n, ‖f n‖ ≤ 1) → ∀ x T : ℝ,
      11 ≤ x → 0 ≤ T → ∀ α : ℝ, 1 / Real.log x ≤ α → α ≤ 1 / 2 →
        Real.exp (Wsup f x α T) ≤
          K * ∫ γ in α..(2 * α), Real.exp (Wsup f x γ T) / γ := by
  obtain ⟨C_P, hC_P_pos, hP⟩ := Wsup_factor_two
  refine ⟨Real.exp C_P / Real.log 2, div_pos (Real.exp_pos _) (Real.log_pos (by norm_num)), ?_⟩
  intro f hb x T hx hT α hα hαhalf
  have hx3 : (3:ℝ) ≤ x := by linarith
  have hα0 : 0 < α := lt_of_lt_of_le
    (by rw [one_div]; exact inv_pos.mpr (Real.log_pos (by linarith))) hα
  have hint : IntervalIntegrable (fun γ : ℝ => Real.exp (Wsup f x γ T) / γ) volume α (2*α) :=
    intervalIntegrable_expWsup_div hb hα0 (by linarith)
  have hpt : ∀ γ ∈ Set.Icc α (2*α),
      Real.exp (-C_P) * Real.exp (Wsup f x α T) / γ
        ≤ Real.exp (Wsup f x γ T) / γ := by
    intro γ hγ
    obtain ⟨hγ1, hγ2⟩ := hγ
    have hγ0 : 0 < γ := lt_of_lt_of_le hα0 hγ1
    have hbnd : Wsup f x α T ≤ Wsup f x γ T + C_P :=
      hP f hb x α γ T hx3 hα hγ1 hγ2 (by linarith [hαhalf]) hT
    have hexp : Real.exp (-C_P) * Real.exp (Wsup f x α T) ≤ Real.exp (Wsup f x γ T) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr (by linarith)
    exact div_le_div_of_nonneg_right hexp hγ0.le
  have hint2 : IntervalIntegrable
      (fun γ : ℝ => Real.exp (-C_P) * Real.exp (Wsup f x α T) / γ) volume α (2*α) := by
    have h1 : (fun γ : ℝ => Real.exp (-C_P) * Real.exp (Wsup f x α T) / γ)
        = (fun γ : ℝ => (Real.exp (-C_P) * Real.exp (Wsup f x α T)) * γ⁻¹) := by
      funext γ; ring
    rw [h1]
    exact (intervalIntegrable_inv (f := fun γ : ℝ => γ) (fun γ hγ => by
      rw [Set.uIcc_of_le (by linarith)] at hγ
      exact ne_of_gt (lt_of_lt_of_le hα0 hγ.1)) continuousOn_id).const_mul _
  have hmono := intervalIntegral.integral_mono_on (by linarith) hint2 hint hpt
  have hval : (∫ γ in α..(2*α), Real.exp (-C_P) * Real.exp (Wsup f x α T) / γ)
      = Real.exp (-C_P) * Real.exp (Wsup f x α T) * Real.log 2 := by
    rw [show (fun γ : ℝ => Real.exp (-C_P) * Real.exp (Wsup f x α T) / γ)
        = (fun γ : ℝ => (Real.exp (-C_P) * Real.exp (Wsup f x α T)) * γ⁻¹) by
          funext γ; ring,
      intervalIntegral.integral_const_mul,
      integral_inv_of_pos hα0 (by linarith : (0:ℝ) < 2*α)]
    rw [show (2*α)/α = 2 by field_simp]
  rw [hval] at hmono
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h4 : Real.exp C_P * (Real.exp (-C_P) * Real.exp (Wsup f x α T) * Real.log 2)
      = Real.exp (Wsup f x α T) * Real.log 2 := by
    rw [show Real.exp C_P * (Real.exp (-C_P) * Real.exp (Wsup f x α T) * Real.log 2)
        = (Real.exp C_P * Real.exp (-C_P)) * (Real.exp (Wsup f x α T) * Real.log 2) by ring,
      ← Real.exp_add, show C_P + -C_P = (0:ℝ) by ring, Real.exp_zero, one_mul]
  have hstep : Real.exp (Wsup f x α T) * Real.log 2
      ≤ Real.exp C_P * ∫ γ in α..(2*α), Real.exp (Wsup f x γ T) / γ := by
    have h5 := mul_le_mul_of_nonneg_left hmono (Real.exp_pos C_P).le
    rwa [h4] at h5
  rw [div_mul_eq_mul_div]
  exact (le_div_iff₀ hlog2).mpr hstep

/-- Uniform lower bound for the `α`-integral appearing in `a_bound`. -/
private theorem exp_Wsup_int_lower :
    ∃ c : ℝ, 0 < c ∧ ∀ (f : ℕ → ℂ), (∀ n, ‖f n‖ ≤ 1) → ∀ x T : ℝ, 11 ≤ x → 0 ≤ T →
      c ≤ ∫ α in (1 / Real.log x)..1, Real.exp (Wsup f x α T) / α := by
  obtain ⟨C₀, hC₀_pos, hlow⟩ := Wsup_lower
  refine ⟨Real.exp (-(1 + C₀)) / 2, div_pos (Real.exp_pos _) (by norm_num), ?_⟩
  intro f hb x T hx hT
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have hα1 : 1 / Real.log x ≤ 1 := by
    rw [div_le_one hlogx]
    have h := Real.log_le_log (by norm_num : (0:ℝ) < 11) hx
    linarith [h, log_eleven_gt_two]
  have hα0 : 0 < 1 / Real.log x := by rw [one_div]; exact inv_pos.mpr hlogx
  have hpt : ∀ α ∈ Set.Icc (1 / Real.log x) 1,
      Real.exp (-(1 + C₀)) ≤ Real.exp (Wsup f x α T) / α := by
    intro α hα
    have hα0' : 0 < α := lt_of_lt_of_le hα0 hα.1
    have hW := hlow f hb x α T hα0' hα.2 hT
    have hkey : Real.exp (-(1 + C₀)) * α ≤ Real.exp (Wsup f x α T) := by
      calc Real.exp (-(1 + C₀)) * α ≤ Real.exp (-C₀) * α := by
            refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) hα0'.le
        _ = Real.exp (-(Real.log (1/α) + C₀)) := by
            rw [show -(Real.log (1/α) + C₀) = Real.log α + (-C₀) by
                  rw [one_div, Real.log_inv]; ring]
            rw [Real.exp_add, Real.exp_log hα0']
            ring
        _ ≤ Real.exp (Wsup f x α T) := Real.exp_le_exp.mpr hW
    rw [le_div_iff₀ hα0']
    linarith
  have hint := intervalIntegrable_expWsup_div (f := f) (x := x) (T := T) hb hα0 hα1
  have hmono := intervalIntegral.integral_mono_on hα1 intervalIntegrable_const hint hpt
  rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
  have hlen : (1:ℝ)/2 ≤ 1 - 1/Real.log x := by
    have h2 : (2:ℝ) ≤ Real.log x := by
      have h := Real.log_le_log (by norm_num : (0:ℝ) < 11) hx
      linarith [h, log_eleven_gt_two]
    have h3 : 1 / Real.log x ≤ 1/2 := by
      rw [div_le_div_iff₀ hlogx (by norm_num)]
      linarith
    linarith
  have hpos : 0 ≤ Real.exp (-(1 + C₀)) := le_of_lt (Real.exp_pos _)
  linarith [mul_le_mul_of_nonneg_right hlen hpos]

/-- Mertens: `exp (Zrcp y) ≤ C (log y / log x) exp (Zrcp x)` for `11 ≤ y ≤ x`. -/
private lemma Zrcp_exp_ratio :
    ∃ C : ℝ, 0 < C ∧ ∀ x y : ℝ, 11 ≤ y → y ≤ x →
      Real.exp (Zrcp y) ≤ C * (Real.log y / Real.log x) * Real.exp (Zrcp x) := by
  obtain ⟨C₀, hC₀_pos, hMr⟩ := Commons.NumberTheory.Mertens.primeRecips_sub_loglog_bound
  obtain ⟨C_z, hC_z, hZ⟩ := Work.BMF.mrlas.casdiv_zrcp_ratio C₀ hC₀_pos
    (fun t ht => by simpa only [Work.BMF.Zrcp] using hMr t ht)
  refine ⟨C_z, hC_z, ?_⟩
  intro x y hy hyx
  have h := hZ x y (le_trans (by norm_num : (2:ℝ) ≤ 11) hy) hyx
  calc Real.exp (Zrcp y) ≤ C_z * Real.exp (Zrcp x) * (Real.log y / Real.log x) := h
    _ = C_z * (Real.log y / Real.log x) * Real.exp (Zrcp x) := by ring

/-- Telescoping of integrals over a decreasing sequence of windows. -/
private lemma sum_integral_decreasing {G : ℝ → ℝ} {b : ℕ → ℝ} {n : ℕ}
    (h : ∀ k < n, IntervalIntegrable G volume (b k) (b (k+1))) :
    (∑ k ∈ Finset.range n, ∫ γ in b (k+1)..b k, G γ) = ∫ γ in b n..b 0, G γ := by
  have h1 : (∑ k ∈ Finset.range n, ∫ γ in b (k+1)..b k, G γ)
      = ∑ k ∈ Finset.range n, -∫ γ in b k..b (k+1), G γ :=
    Finset.sum_congr rfl (fun k _ => intervalIntegral.integral_symm (b k) (b (k+1)))
  rw [h1, Finset.sum_neg_distrib, intervalIntegral.sum_integral_adjacent_intervals h]
  exact (intervalIntegral.integral_symm (b 0) (b n)).symm


/-- The dyadic exponents `2^{-k}`. -/
private noncomputable def cseq : ℕ → ℝ := fun k => ((1:ℝ)/2)^k

private lemma cseq_eq (k : ℕ) : cseq k = 1/(2:ℝ)^k := by
  show ((1:ℝ)/2)^k = 1/(2:ℝ)^k
  rw [div_pow, one_pow]

private lemma cseq_pos (k : ℕ) : 0 < cseq k := by
  show (0:ℝ) < ((1:ℝ)/2)^k
  positivity

private lemma cseq_le_one (k : ℕ) : cseq k ≤ 1 := by
  show ((1:ℝ)/2)^k ≤ 1
  calc ((1:ℝ)/2)^k ≤ 1^k := pow_le_pow_left₀ (by norm_num) (by norm_num) k
    _ = 1 := one_pow k

private lemma cseq_succ (k : ℕ) : cseq (k+1) = cseq k * ((1:ℝ)/2) := by
  show ((1:ℝ)/2)^(k+1) = ((1:ℝ)/2)^k * ((1:ℝ)/2)
  rw [pow_succ]

private lemma cseq_two_mul (k : ℕ) : 2 * cseq (k+1) = cseq k := by
  rw [cseq_succ]; ring

private lemma cseq_succ_le (k : ℕ) : cseq (k+1) ≤ cseq k := by
  rw [cseq_succ]
  have := cseq_pos k
  nlinarith

private lemma two_mul_cseq_pred {J : ℕ} (hJ : 1 ≤ J) : 2 * cseq J = cseq (J-1) := by
  have h : cseq J = cseq (J-1) * ((1:ℝ)/2) := by
    conv_lhs => rw [← Nat.sub_add_cancel hJ]
    rw [cseq_succ]
  rw [h]; ring

private lemma cseq_le_half {k : ℕ} (hk : 1 ≤ k) : cseq k ≤ 1/2 := by
  have h1 : cseq k = cseq (k-1) * ((1:ℝ)/2) := by
    conv_lhs => rw [← Nat.sub_add_cancel hk]
    rw [cseq_succ]
  rw [h1]
  have h2 : cseq (k-1) ≤ 1 := cseq_le_one (k-1)
  have h3 : 0 ≤ cseq (k-1) := (cseq_pos _).le
  nlinarith

private lemma cseq_one : cseq 1 = 1/2 := by
  show ((1:ℝ)/2)^(1:ℕ) = 1/2
  norm_num

private lemma inv_log_le_cseq {x : ℝ} (hL : 0 < Real.log x) {k : ℕ}
    (hk : (2:ℝ)^k ≤ Real.log x) : 1/Real.log x ≤ cseq k := by
  rw [cseq_eq]
  exact one_div_le_one_div_of_le (by positivity) hk

private lemma cseq_le_two_inv_log {x : ℝ} (hL : 0 < Real.log x) {k : ℕ}
    (hk : Real.log x ≤ 2 * (2:ℝ)^k) : cseq k ≤ 2/Real.log x := by
  rw [cseq_eq, div_le_div_iff₀ (by positivity) hL]
  linarith

private lemma intervalIntegrable_expWsup_div' {f : ℕ → ℂ} (hb : ∀ n, ‖f n‖ ≤ 1)
    {x T a b : ℝ} (ha : 0 < a) (hb0 : 0 < b) :
    IntervalIntegrable (fun γ : ℝ => Real.exp (Wsup f x γ T) / γ) volume a b := by
  rcases le_total a b with h | h
  · exact intervalIntegrable_expWsup_div hb ha h
  · have h' : IntervalIntegrable (fun γ : ℝ => Real.exp (Wsup f x γ T) / γ) volume b a :=
      intervalIntegrable_expWsup_div hb hb0 h
    exact h'.symm

/-- **Main bound.** -/
theorem a_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : ℕ → ℂ), f 1 = 1 →
      (∀ m n : ℕ, m.Coprime n → f (m * n) = f m * f n) → (∀ n, ‖f n‖ ≤ 1) →
      ∀ x T : ℝ, 11 ≤ x → 2 ≤ T →
        (∫ t in (1 : ℝ)..x, ‖Mf f t‖ / t ^ 2) ≤
          C * ((∫ α in (1 / Real.log x)..1, Real.exp (Wsup f x α (T + 1)) / α) +
               Real.exp (Zrcp x) / Real.sqrt T) := by
  obtain ⟨C_yr, hC_yr_pos, hY⟩ := yr_bound
  obtain ⟨K_w, hK_w_pos, hW⟩ := exp_Wsup_le_window
  obtain ⟨C_P, hC_P_pos, hP⟩ := Wsup_factor_two
  obtain ⟨c_low, hc_low_pos, hcl⟩ := exp_Wsup_int_lower
  obtain ⟨C_z, hC_z_pos, hZ⟩ := Zrcp_exp_ratio
  refine ⟨max (C_yr * (K_w + K_w * Real.exp C_P) + (2 + C_yr) / c_low)
      (C_yr * (3 * C_z + 1)) + 1, ?_, ?_⟩
  · have h1 : 0 < C_yr * (K_w + K_w * Real.exp C_P) + (2 + C_yr) / c_low := by positivity
    have h2 := le_max_left (C_yr * (K_w + K_w * Real.exp C_P) + (2 + C_yr) / c_low)
      (C_yr * (3 * C_z + 1))
    linarith
  intro f hf1 hmul hb x T hx hT
  have hx1 : (1:ℝ) < x := by linarith
  have hx0 : (0:ℝ) < x := by linarith
  have hx3 : (3:ℝ) ≤ x := by linarith
  have hL : 0 < Real.log x := Real.log_pos hx1
  have hL2 : (2:ℝ) < Real.log x :=
    lt_of_lt_of_le log_eleven_gt_two (Real.log_le_log (by norm_num : (0:ℝ) < 11) hx)
  have hT0 : (0:ℝ) ≤ T + 1 := by linarith
  -- the scale `J` with `2^J < log x ≤ 2^(J+1)`
  have hex : ∃ j : ℕ, Real.log x ≤ (2:ℝ)^(j+1) := by
    obtain ⟨j, hj⟩ := exists_nat_gt (Real.log x)
    refine ⟨j, le_trans (le_of_lt hj) ?_⟩
    calc (j:ℝ) ≤ (2:ℝ)^j := by
          have h : j < 2^j := Nat.lt_two_pow_self
          exact_mod_cast h.le
      _ ≤ (2:ℝ)^(j+1) := pow_le_pow_right₀ (by norm_num) (Nat.le_succ j)
  set J : ℕ := Nat.find hex with hJdef
  have hJspec : Real.log x ≤ (2:ℝ)^(J+1) := Nat.find_spec hex
  have hJmin : ∀ j < J, ¬ (Real.log x ≤ (2:ℝ)^(j+1)) := fun j hj => Nat.find_min hex hj
  have hJpos : 0 < J := by
    by_contra h
    have h0 : J = 0 := Nat.eq_zero_of_not_pos h
    rw [h0] at hJspec
    norm_num at hJspec
    linarith [hL2]
  have hJlt : (2:ℝ)^J < Real.log x := by
    have h := hJmin (J-1) (by omega)
    rw [Nat.sub_add_cancel (by omega : 1 ≤ J)] at h
    exact not_le.mp h
  set a : ℕ → ℝ := fun j => Real.exp ((2:ℝ)^j) with hadef
  have ha_mono : ∀ j k : ℕ, j ≤ k → a j ≤ a k := by
    intro j k hjk
    exact Real.exp_le_exp.mpr (pow_le_pow_right₀ (by norm_num) hjk)
  have ha1 : a 1 = Real.exp 2 := by
    show Real.exp ((2:ℝ)^(1:ℕ)) = Real.exp 2
    norm_num
  have ha1_gt : (1:ℝ) < a 1 := by rw [ha1]; exact Real.one_lt_exp_iff.mpr (by norm_num)
  have ha1_pos : (0:ℝ) < a 1 := lt_trans zero_lt_one ha1_gt
  have haJx : a J ≤ x := by
    show Real.exp ((2:ℝ)^J) ≤ x
    calc Real.exp ((2:ℝ)^J) ≤ Real.exp (Real.log x) := Real.exp_le_exp.mpr hJlt.le
      _ = x := Real.exp_log hx0
  have hsj : Real.sqrt x ≤ a J := by
    show Real.sqrt x ≤ Real.exp ((2:ℝ)^J)
    rw [show Real.sqrt x = Real.exp (Real.log x / 2) from by
      rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx0]; congr 1; ring]
    have h2 : (2:ℝ)^(J+1) = 2 * (2:ℝ)^J := by rw [pow_succ]; ring
    exact Real.exp_le_exp.mpr (by linarith [hJspec, h2])
  have ha2_ge3 : (3:ℝ) ≤ a 2 := by
    have h2 : (3:ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp 2]
    have h3 : Real.exp 2 ≤ a 2 := by
      show Real.exp 2 ≤ Real.exp ((2:ℝ)^(2:ℕ))
      exact Real.exp_le_exp.mpr (by norm_num)
    linarith
  have ha2_ge11 : (11:ℝ) ≤ a 2 := by
    have h1 : (2.7:ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h2 : a 2 = (Real.exp 1)^4 := by
      show Real.exp ((2:ℝ)^(2:ℕ)) = _
      rw [show (2:ℝ)^(2:ℕ) = 4 by norm_num, show (4:ℝ) = 1 + 1 + 1 + 1 by norm_num]
      rw [Real.exp_add, Real.exp_add, Real.exp_add]
      ring
    rw [h2]
    have h2' : (2.7:ℝ)^2 < (Real.exp 1)^2 := by nlinarith [h1, Real.exp_pos 1]
    have h3' : (2.7:ℝ)^4 < (Real.exp 1)^4 := by nlinarith [h2', h1, Real.exp_pos 1]
    have h5 : (11:ℝ) < (2.7:ℝ)^4 := by norm_num
    linarith
  have hInt : ∀ u v : ℝ, 1 ≤ u → u ≤ v →
      IntervalIntegrable (fun t : ℝ => ‖Mf f t‖ / t^2) volume u v :=
    fun u v hu huv => Work.BMF.intervalIntegrable_norm_Mf_div_sq f hu huv
  have ha1J : a 1 ≤ a J := ha_mono 1 J (by omega)
  -- the decomposition
  have hdecomp : (∫ t in (1:ℝ)..x, ‖Mf f t‖/t^2)
      = (∫ t in (1:ℝ)..(a 1), ‖Mf f t‖/t^2) + (∫ t in (a 1)..(a J), ‖Mf f t‖/t^2)
        + (∫ t in (a J)..x, ‖Mf f t‖/t^2) := by
    have h1 := intervalIntegral.integral_add_adjacent_intervals
      (hInt 1 (a 1) le_rfl ha1_gt.le) (hInt (a 1) x ha1_gt.le (le_trans ha1J haJx))
    have h2 := intervalIntegral.integral_add_adjacent_intervals
      (hInt (a 1) (a J) ha1_gt.le ha1J) (hInt (a J) x (le_trans ha1_gt.le ha1J) haJx)
    linarith [h1, h2]
  -- the small range
  have hsmall : (∫ t in (1:ℝ)..(a 1), ‖Mf f t‖/t^2) ≤ 2 := by
    have hpt : ∀ t ∈ Set.Icc (1:ℝ) (a 1), ‖Mf f t‖/t^2 ≤ (1:ℝ)/t := by
      intro t ht
      have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht.1
      have h1 : ‖Mf f t‖ ≤ t := Work.BMF.Mf_norm_le_x f hb t ht0.le
      rw [div_le_div_iff₀ (by positivity : (0:ℝ) < t^2) ht0]
      nlinarith [norm_nonneg (Mf f t)]
    have hinv : IntervalIntegrable (fun t : ℝ => (1:ℝ)/t) volume 1 (a 1) := by
      have h : IntervalIntegrable (fun t : ℝ => t⁻¹) volume 1 (a 1) :=
        intervalIntegrable_inv (f := fun t : ℝ => t) (fun t ht => by
          rw [Set.uIcc_of_le ha1_gt.le] at ht
          exact ne_of_gt (lt_of_lt_of_le zero_lt_one ht.1)) continuousOn_id
      simpa [one_div] using h
    have hmono := intervalIntegral.integral_mono_on ha1_gt.le (hInt 1 (a 1) le_rfl ha1_gt.le) hinv hpt
    have hval : (∫ t in (1:ℝ)..(a 1), (1:ℝ)/t) = 2 := by
      rw [show (∫ t in (1:ℝ)..(a 1), (1:ℝ)/t) = ∫ t in (1:ℝ)..(a 1), t⁻¹ from
            intervalIntegral.integral_congr (fun t _ => by rw [one_div])]
      rw [integral_inv_of_pos (by norm_num) ha1_pos, ha1, div_one, Real.log_exp]
    linarith [hmono, hval]
  -- telescoping the middle range
  have hmid : (∫ t in (a 1)..(a J), ‖Mf f t‖/t^2)
      = ∑ k ∈ Finset.range (J-1), ∫ t in a (k+1)..a (k+2), ‖Mf f t‖/t^2 := by
    have h := intervalIntegral.sum_integral_adjacent_intervals
      (a := fun k : ℕ => a (k+1)) (f := fun t : ℝ => ‖Mf f t‖/t^2) (n := J-1)
      (fun k _ => hInt (a (k+1)) (a (k+2))
        (le_trans ha1_gt.le (ha_mono 1 (k+1) (by omega))) (ha_mono (k+1) (k+2) (by omega)))
    have h2 : a ((J-1)+1) = a J := by
      congr 1
      exact Nat.sub_add_cancel (by omega : 1 ≤ J)
    rw [h2] at h
    simpa using h.symm
  -- each middle block
  have hblock : ∀ k ∈ Finset.range (J-1),
      (∫ t in a (k+1)..a (k+2), ‖Mf f t‖/t^2)
        ≤ C_yr * (Real.exp (Wsup f x (cseq (k+2)) (T+1))
            + Real.exp (Zrcp (a (k+2))) / Real.sqrt T + cseq (k+2)) := by
    intro k hk
    rw [Finset.mem_range] at hk
    have hkJ : k + 2 ≤ J := by omega
    have hsq : Real.sqrt (a (k+2)) = a (k+1) := by
      show Real.sqrt (Real.exp ((2:ℝ)^(k+2))) = Real.exp ((2:ℝ)^(k+1))
      rw [sqrt_exp]
      congr 1
      rw [show (2:ℝ)^(k+2) = (2:ℝ)^(k+1) * 2 by rw [pow_succ]]
      ring
    have hy3 : (3:ℝ) ≤ a (k+2) := le_trans ha2_ge3 (ha_mono 2 (k+2) (by omega))
    have hyx : a (k+2) ≤ x := le_trans (ha_mono (k+2) J hkJ) haJx
    have hkey := hY f hf1 hmul hb x (a (k+2)) T hx hy3 hyx hT
    rw [hsq] at hkey
    have hlog : Real.log (a (k+2)) = (2:ℝ)^(k+2) := by
      show Real.log (Real.exp ((2:ℝ)^(k+2))) = _
      rw [Real.log_exp]
    rw [hlog] at hkey
    have hcast : (1:ℝ) / (2:ℝ)^(k+2) = cseq (k+2) := (cseq_eq (k+2)).symm
    rwa [hcast] at hkey
  -- the top range
  have htop : (∫ t in a J..x, ‖Mf f t‖/t^2)
      ≤ C_yr * (Real.exp (Wsup f x (1/Real.log x) (T+1))
          + Real.exp (Zrcp x) / Real.sqrt T + 1/Real.log x) := by
    have h1 : (∫ t in a J..x, ‖Mf f t‖/t^2) ≤ ∫ t in Real.sqrt x..x, ‖Mf f t‖/t^2 := by
      refine intervalIntegral.integral_mono_interval hsj haJx le_rfl ?_
        (hInt (Real.sqrt x) x (Real.one_le_sqrt.mpr hx1.le) (le_trans hsj haJx))
      exact Filter.Eventually.of_forall (fun t => div_nonneg (norm_nonneg _) (by positivity))
    have h2 := hY f hf1 hmul hb x x T hx (by linarith) le_rfl hT
    exact le_trans h1 h2
  -- the E-terms
  have hEterms : ∀ k ∈ Finset.range (J-1),
      Real.exp (Wsup f x (cseq (k+2)) (T+1))
        ≤ K_w * ∫ γ in cseq (k+2)..cseq (k+1),
            Real.exp (Wsup f x γ (T+1))/γ := by
    intro k hk
    rw [Finset.mem_range] at hk
    have hpow : (2:ℝ)^(k+2) ≤ Real.log x := by
      calc (2:ℝ)^(k+2) ≤ (2:ℝ)^J := pow_le_pow_right₀ (by norm_num) (by omega)
        _ ≤ Real.log x := hJlt.le
    have hα1 : 1/Real.log x ≤ cseq (k+2) := inv_log_le_cseq hL hpow
    have hαhalf : cseq (k+2) ≤ 1/2 := cseq_le_half (by omega)
    have h := hW f hb x (T+1) hx hT0 (cseq (k+2)) hα1 hαhalf
    have h2α : 2 * cseq (k+2) = cseq (k+1) := cseq_two_mul (k+1)
    rwa [h2α] at h
  have hEsum : (∑ k ∈ Finset.range (J-1), Real.exp (Wsup f x (cseq (k+2)) (T+1)))
      ≤ K_w * ∫ γ in cseq J..(1/2:ℝ), Real.exp (Wsup f x γ (T+1))/γ := by
    have htel : (∑ k ∈ Finset.range (J-1),
        ∫ γ in cseq (k+2)..cseq (k+1), Real.exp (Wsup f x γ (T+1))/γ)
        = ∫ γ in cseq J..(1/2:ℝ), Real.exp (Wsup f x γ (T+1))/γ := by
      have h := sum_integral_decreasing
        (G := fun γ : ℝ => Real.exp (Wsup f x γ (T+1))/γ)
        (b := fun k : ℕ => cseq (k+1)) (n := J-1) (fun k _ =>
          intervalIntegrable_expWsup_div' hb (cseq_pos (k+1)) (cseq_pos (k+2)))
      have h2 : cseq ((J-1)+1) = cseq J := by
        congr 1
        exact Nat.sub_add_cancel (by omega : 1 ≤ J)
      have h3 : cseq (0+1) = 1/2 := by rw [Nat.zero_add]; exact cseq_one
      rw [h2, h3] at h
      have h4 : (∑ k ∈ Finset.range (J-1),
          ∫ γ in cseq (k+2)..cseq (k+1), Real.exp (Wsup f x γ (T+1))/γ)
          = ∑ k ∈ Finset.range (J-1),
          ∫ γ in cseq (k+1+1)..cseq (k+1), Real.exp (Wsup f x γ (T+1))/γ := by
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [show k + 1 + 1 = k + 2 by omega]
      rw [h4, h]
    calc (∑ k ∈ Finset.range (J-1), Real.exp (Wsup f x (cseq (k+2)) (T+1)))
        ≤ ∑ k ∈ Finset.range (J-1), K_w * ∫ γ in cseq (k+2)..cseq (k+1),
            Real.exp (Wsup f x γ (T+1))/γ := Finset.sum_le_sum hEterms
      _ = K_w * ∑ k ∈ Finset.range (J-1), ∫ γ in cseq (k+2)..cseq (k+1),
            Real.exp (Wsup f x γ (T+1))/γ := by rw [Finset.mul_sum]
      _ = K_w * ∫ γ in cseq J..(1/2:ℝ), Real.exp (Wsup f x γ (T+1))/γ := by rw [htel]
  have hEmid_int : ∫ γ in cseq J..(1/2:ℝ), Real.exp (Wsup f x γ (T+1))/γ
      ≤ ∫ γ in (1/Real.log x)..1, Real.exp (Wsup f x γ (T+1))/γ := by
    refine intervalIntegral.integral_mono_interval ?_ ?_ ?_ ?_
      (intervalIntegrable_expWsup_div hb (by rw [one_div]; exact inv_pos.mpr hL)
          (by rw [div_le_one hL]; linarith [hL2]))
    · exact inv_log_le_cseq hL hJlt.le
    · exact cseq_le_half (by omega)
    · norm_num
    · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioc] with γ hγ
      have hγ0 : 0 < γ := lt_trans (by rw [one_div]; exact inv_pos.mpr hL) hγ.1
      exact div_nonneg (Real.exp_nonneg _) hγ0.le
  have hEtop : Real.exp (Wsup f x (1/Real.log x) (T+1))
      ≤ K_w * Real.exp C_P * ∫ γ in (1/Real.log x)..1, Real.exp (Wsup f x γ (T+1))/γ := by
    have hα1 : 1/Real.log x ≤ cseq J := inv_log_le_cseq hL hJlt.le
    have hβ2 : cseq J ≤ 2 * (1/Real.log x) := by
      rw [show 2 * (1/Real.log x) = 2 / Real.log x by ring]
      refine cseq_le_two_inv_log hL ?_
      have h6 : (2:ℝ)^(J+1) = 2 * (2:ℝ)^J := by rw [pow_succ]; ring
      linarith [hJspec, h6]
    have hβ1 : cseq J ≤ 1 := cseq_le_one J
    have hstep := hP f hb x (1/Real.log x) (cseq J) (T+1) hx3 le_rfl hα1 hβ2 hβ1 hT0
    have hexp1 : Real.exp (Wsup f x (1/Real.log x) (T+1))
        ≤ Real.exp C_P * Real.exp (Wsup f x (cseq J) (T+1)) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr (by linarith [hstep])
    have hαhalfJ : cseq J ≤ 1/2 := cseq_le_half (by omega)
    have hWs : Real.exp (Wsup f x (cseq J) (T+1))
        ≤ K_w * ∫ γ in cseq J..cseq (J-1), Real.exp (Wsup f x γ (T+1))/γ := by
      have h := hW f hb x (T+1) hx hT0 (cseq J) hα1 hαhalfJ
      rwa [two_mul_cseq_pred (by omega : 1 ≤ J)] at h
    have hWint : (∫ γ in cseq J..cseq (J-1), Real.exp (Wsup f x γ (T+1))/γ)
        ≤ ∫ γ in (1/Real.log x)..1, Real.exp (Wsup f x γ (T+1))/γ := by
      refine intervalIntegral.integral_mono_interval hα1 ?_ ?_ ?_
        (intervalIntegrable_expWsup_div hb (by rw [one_div]; exact inv_pos.mpr hL)
          (by rw [div_le_one hL]; linarith [hL2]))
      · have hh := two_mul_cseq_pred (J := J) (by omega : 1 ≤ J)
        have h2 := cseq_pos (J-1)
        nlinarith
      · exact cseq_le_one (J-1)
      · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioc] with γ hγ
        have hγ0 : 0 < γ := lt_trans (by rw [one_div]; exact inv_pos.mpr hL) hγ.1
        exact div_nonneg (Real.exp_nonneg _) hγ0.le
    calc Real.exp (Wsup f x (1/Real.log x) (T+1))
        ≤ Real.exp C_P * Real.exp (Wsup f x (cseq J) (T+1)) := hexp1
      _ ≤ Real.exp C_P * (K_w * ∫ γ in (1/Real.log x)..1,
            Real.exp (Wsup f x γ (T+1))/γ) :=
          mul_le_mul_of_nonneg_left (le_trans hWs (mul_le_mul_of_nonneg_left hWint hK_w_pos.le))
            (Real.exp_pos C_P).le
      _ = K_w * Real.exp C_P * ∫ γ in (1/Real.log x)..1, Real.exp (Wsup f x γ (T+1))/γ := by
          ring
  -- the Z-terms
  have hZterms : ∀ k ∈ Finset.range (J-1),
      Real.exp (Zrcp (a (k+2))) / Real.sqrt T
        ≤ C_z * ((2:ℝ)^(k+2)/Real.log x) * (Real.exp (Zrcp x)/Real.sqrt T) := by
    intro k hk
    rw [Finset.mem_range] at hk
    have hkJ : k + 2 ≤ J := by omega
    have hy11 : (11:ℝ) ≤ a (k+2) := le_trans ha2_ge11 (ha_mono 2 (k+2) (by omega))
    have hyx : a (k+2) ≤ x := le_trans (ha_mono (k+2) J hkJ) haJx
    have h := hZ x (a (k+2)) hy11 hyx
    have hlog : Real.log (a (k+2)) = (2:ℝ)^(k+2) := by
      show Real.log (Real.exp ((2:ℝ)^(k+2))) = _
      rw [Real.log_exp]
    rw [hlog] at h
    calc Real.exp (Zrcp (a (k+2))) / Real.sqrt T
        ≤ (C_z * ((2:ℝ)^(k+2)/Real.log x) * Real.exp (Zrcp x)) / Real.sqrt T :=
          div_le_div_of_nonneg_right h (Real.sqrt_nonneg T)
      _ = C_z * ((2:ℝ)^(k+2)/Real.log x) * (Real.exp (Zrcp x)/Real.sqrt T) := by ring
  have hsum2 : (∑ k ∈ Finset.range (J-1), (2:ℝ)^(k+2) / Real.log x) ≤ 2 := by
    have h1 : (∑ k ∈ Finset.range (J-1), (2:ℝ)^(k+2)) ≤ 2 * Real.log x := by
      have h2 : (∑ k ∈ Finset.range (J-1), (2:ℝ)^(k+2))
          = 4 * ∑ k ∈ Finset.range (J-1), (2:ℝ)^k := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [show (2:ℝ)^(k+2) = (2:ℝ)^k * 4 by rw [pow_add]; norm_num]
        ring
      rw [h2]
      have h3 := sum_range_two_pow_le (J-1)
      have hJ1 : J - 1 + 1 = J := Nat.sub_add_cancel (by omega : 1 ≤ J)
      have h5 : (2:ℝ)^J = (2:ℝ)^(J-1) * 2 := by
        conv_lhs => rw [← hJ1]
        rw [pow_succ]
      nlinarith [h3, h5, hJlt]
    calc (∑ k ∈ Finset.range (J-1), (2:ℝ)^(k+2) / Real.log x)
        = (∑ k ∈ Finset.range (J-1), (2:ℝ)^(k+2)) / Real.log x := by rw [Finset.sum_div]
      _ ≤ 2 * Real.log x / Real.log x := div_le_div_of_nonneg_right h1 hL.le
      _ = 2 := by field_simp
  -- abbreviations for the final bookkeeping
  set SE : ℝ := (∑ k ∈ Finset.range (J-1), Real.exp (Wsup f x (cseq (k+2)) (T+1))) with hSE
  set SZ : ℝ := (∑ k ∈ Finset.range (J-1), Real.exp (Zrcp (a (k+2))) / Real.sqrt T) with hSZ
  set Sc : ℝ := (∑ k ∈ Finset.range (J-1), cseq (k+2)) with hSc
  set ET : ℝ := Real.exp (Wsup f x (1/Real.log x) (T+1)) with hET
  set ZT : ℝ := Real.exp (Zrcp x) / Real.sqrt T with hZT
  set cT : ℝ := 1/Real.log x with hcT
  set Ival : ℝ := (∫ γ in (1/Real.log x)..1, Real.exp (Wsup f x γ (T+1))/γ) with hIval
  have hEbound : SE + ET ≤ (K_w + K_w * Real.exp C_P) * Ival := by
    rw [hSE, hET, hIval]
    have h1 := le_trans hEsum (mul_le_mul_of_nonneg_left hEmid_int hK_w_pos.le)
    linarith [h1, hEtop]
  have hZbound : SZ + ZT ≤ (3*C_z + 1) * ZT := by
    rw [hSZ, hZT]
    have hE0 : 0 ≤ Real.exp (Zrcp x)/Real.sqrt T :=
      div_nonneg (Real.exp_nonneg _) (Real.sqrt_nonneg T)
    have h1 : (∑ k ∈ Finset.range (J-1), Real.exp (Zrcp (a (k+2))) / Real.sqrt T)
        ≤ C_z * (Real.exp (Zrcp x)/Real.sqrt T) * 2 := by
      calc (∑ k ∈ Finset.range (J-1), Real.exp (Zrcp (a (k+2))) / Real.sqrt T)
          ≤ ∑ k ∈ Finset.range (J-1),
              C_z * ((2:ℝ)^(k+2)/Real.log x) * (Real.exp (Zrcp x)/Real.sqrt T) :=
            Finset.sum_le_sum hZterms
        _ = C_z * (Real.exp (Zrcp x)/Real.sqrt T)
              * (∑ k ∈ Finset.range (J-1), (2:ℝ)^(k+2)/Real.log x) := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl (fun k _ => by ring)
        _ ≤ C_z * (Real.exp (Zrcp x)/Real.sqrt T) * 2 :=
            mul_le_mul_of_nonneg_left hsum2 (by positivity)
    have h2 : Real.exp (Zrcp x) / Real.sqrt T ≤ (C_z + 1) * (Real.exp (Zrcp x)/Real.sqrt T) := by
      nlinarith [hC_z_pos, hE0]
    linarith [h1, h2]
  have hcbound : Sc + cT ≤ 1 := by
    rw [hSc, hcT]
    have h1 : (∑ k ∈ Finset.range (J-1), cseq (k+2))
        = ((1:ℝ)/2) * ∑ k ∈ Finset.range (J-1), cseq (k+1) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [cseq_succ]
      ring
    have h2 : (∑ k ∈ Finset.range (J-1), cseq (k+1)) ≤ 1 := geom_half_sum_shift_le (J-1)
    have h3 : 1/Real.log x ≤ 1/2 := by
      rw [div_le_div_iff₀ hL (by norm_num)]
      have h4 : (2:ℝ) ≤ Real.log x := by
        have hh := Real.log_le_log (by norm_num : (0:ℝ) < 11) hx
        linarith [hh, log_eleven_gt_two]
      linarith
    rw [h1]
    have h4 : ((1:ℝ)/2) * (∑ k ∈ Finset.range (J-1), cseq (k+1)) ≤ 1/2 := by
      nlinarith [h2]
    linarith [h3, h4]
  have hmid_sum' : (∑ k ∈ Finset.range (J-1), ∫ t in a (k+1)..a (k+2), ‖Mf f t‖/t^2)
      ≤ C_yr * (SE + SZ + Sc) := by
    rw [hSE, hSZ, hSc]
    calc (∑ k ∈ Finset.range (J-1), ∫ t in a (k+1)..a (k+2), ‖Mf f t‖/t^2)
        ≤ ∑ k ∈ Finset.range (J-1), C_yr * (Real.exp (Wsup f x (cseq (k+2)) (T+1))
            + Real.exp (Zrcp (a (k+2))) / Real.sqrt T + cseq (k+2)) :=
          Finset.sum_le_sum hblock
      _ = C_yr * ∑ k ∈ Finset.range (J-1), (Real.exp (Wsup f x (cseq (k+2)) (T+1))
            + Real.exp (Zrcp (a (k+2))) / Real.sqrt T + cseq (k+2)) := by
          rw [Finset.mul_sum]
      _ = C_yr * ((∑ k ∈ Finset.range (J-1), Real.exp (Wsup f x (cseq (k+2)) (T+1)))
          + (∑ k ∈ Finset.range (J-1), Real.exp (Zrcp (a (k+2))) / Real.sqrt T)
          + (∑ k ∈ Finset.range (J-1), cseq (k+2))) := by
          congr 1
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have htop' : (∫ t in a J..x, ‖Mf f t‖/t^2) ≤ C_yr * (ET + ZT + cT) := by
    rw [hET, hZT, hcT]
    exact htop
  have hcl' : c_low ≤ Ival := by
    rw [hIval]
    exact hcl f hb x (T+1) hx (by linarith)
  have hI0 : 0 < Ival := lt_of_lt_of_le hc_low_pos hcl'
  have hZ0 : 0 ≤ ZT := by rw [hZT]; positivity
  have key : (∫ t in (1:ℝ)..x, ‖Mf f t‖/t^2)
      ≤ max (C_yr * (K_w + K_w * Real.exp C_P) + (2 + C_yr) / c_low) (C_yr * (3 * C_z + 1))
        * (Ival + ZT) := by
    have hA : 0 ≤ C_yr * (K_w + K_w * Real.exp C_P) := by positivity
    have hB : 0 ≤ C_yr * (3 * C_z + 1) := by positivity
    have hD : (2 + C_yr) ≤ ((2 + C_yr)/c_low) * Ival := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hc_low_pos]
      nlinarith [hcl', hC_yr_pos]
    have hm1 := le_max_left (C_yr * (K_w + K_w * Real.exp C_P) + (2 + C_yr) / c_low)
      (C_yr * (3 * C_z + 1))
    have hm2 := le_max_right (C_yr * (K_w + K_w * Real.exp C_P) + (2 + C_yr) / c_low)
      (C_yr * (3 * C_z + 1))
    nlinarith [hdecomp, hsmall, hmid_sum', htop', hEbound, hZbound, hcbound, hD, hm1, hm2,
      hA, hB, hI0, hZ0]
  refine le_trans key ?_
  refine mul_le_mul_of_nonneg_right ?_ (by linarith [hI0, hZ0])
  linarith

end Work.BMF.casdiv
