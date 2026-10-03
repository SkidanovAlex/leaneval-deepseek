import Mathlib
import Submission.Work.FIArea2.R6.BSBoxDefs
import Submission.Work.FIArea2.R6.uboxSum_le_dsum3
import Submission.Work.FIArea2.R6.ul_le_star_public
import Submission.Work.FIArea2.R6.star_eq_WC
import Submission.Work.FIArea2.R6.WC_cube
import Submission.Work.FIArea2.sum_tau_pow_div_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `FIArea2/R6/ubox_bound3` — the unweighted box estimate at the cube cutoff (exponent `2^26`)

Combines

* `R6/uboxSum_le_dsum3`: `uboxSum r X Y ≤ 2^20·Σ_{d³ ≤ r(X²+Y²)} τ(d)^20·ndCount d r X Y`;
* `R6/ndCount_le_UL` + `R6/ul_le_star_public`: `ndCount d ≤ (r/d)·Star d`;
* `R6/star_eq_WC`: `Star d = Σ_{c ∣ d} φ(c)·WC c`;
* `R6/WC_cube`: `WC c r X Y ≤ C·X·Y·r·τ(c)^5/c` for `c³ ≤ r(X²+Y²)`, which applies to every
  `c ∣ d` in the outer sum because `c³ ≤ d³`;

to get `Star d ≤ C·X·Y·r·τ(d)^6`, hence

  `uboxSum r X Y ≤ 2^20·C·(C_W·r²·X·Y)·Σ_{d ≤ √(r(X²+Y²))} τ(d)^26/d
                  ≤ C'·r²·X·Y·(1 + log(r+X+Y+2))^{2^26}`

by `sum_tau_pow_div_le 26` and `log √(r(X²+Y²)) + 2 ≤ 6·(1 + log(r+X+Y+2))`.

This replaces `R6/ubox_bound` (exponent `800`) in the §9 lacunarity chain; the raised exponent is
absorbed by `R6/LacPropK` (cap `2^27`), cf. `R6/BFun29`.
-/

set_option maxHeartbeats 1000000

namespace Work.FIArea2.R6

open Finset
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## 0.  The count identity `ndCount ≤ UL` (copied from `R6/NdCountSqMine`) -/

/-- Pushing an indicator inside a sum. -/
private lemma if_sum_push (p : Prop) [Decidable p] (s : Finset ℤ) (g : ℤ → ℝ) :
    (if p then (∑ y ∈ s, g y) else 0) = ∑ y ∈ s, (if p then g y else 0) := by
  by_cases hp : p <;> simp [hp]

/-- `ndCount d r X Y ≤ UL d r X Y`: the two counts differ only in whether the non-vanishing of the
four variables is imposed by a filter or by an indicator. -/
lemma ndCount_le_UL (d r X Y : ℕ) : ndCount d r X Y ≤ UL d r X Y := by
  have hnd : ndCount d r X Y
      = ∑ x ∈ Finset.Icc (-(r:ℤ)) (r:ℤ), ∑ y ∈ Finset.Icc (-(r:ℤ)) (r:ℤ),
          ∑ h1 ∈ Finset.Icc (-(X:ℤ)) (X:ℤ), ∑ h2 ∈ Finset.Icc (-(Y:ℤ)) (Y:ℤ),
            (if x ≠ 0 then (if y ≠ 0 then (if h1 ≠ 0 then (if h2 ≠ 0 then
              (if (d:ℤ) ∣ x * h1^2 - y * h2^2 ∧ x * h1^2 - y * h2^2 ≠ 0 then (1:ℝ) else 0)
              else 0) else 0) else 0) else 0) := by
    unfold ndCount zPz
    simp only [Finset.sum_filter, if_sum_push]
  rw [hnd]
  unfold UL
  refine Finset.sum_le_sum (fun x _ => ?_)
  refine Finset.sum_le_sum (fun y _ => ?_)
  refine Finset.sum_le_sum (fun h1 _ => ?_)
  refine Finset.sum_le_sum (fun h2 _ => ?_)
  by_cases hx0 : x = 0
  · simp [hx0]
  by_cases hy0 : y = 0
  · simp [hy0]
  by_cases h10 : h1 = 0
  · simp [h10]
  by_cases h20 : h2 = 0
  · simp [h20]
  have hm : h1 ^ 2 * x - h2 ^ 2 * y = x * h1 ^ 2 - y * h2 ^ 2 := by ring
  by_cases hc : (d : ℤ) ∣ x * h1 ^ 2 - y * h2 ^ 2 ∧ x * h1 ^ 2 - y * h2 ^ 2 ≠ 0
  · have hc' : (d : ℤ) ∣ h1 ^ 2 * x - h2 ^ 2 * y ∧ h1 ^ 2 * x - h2 ^ 2 * y ≠ 0 := by
      rw [hm]; exact hc
    simp only [hx0, hy0, h10, h20, ne_eq, not_false_eq_true, true_and, if_true, hc, hc']
    norm_num
  · rw [if_neg hc]
    simp only [hx0, hy0, h10, h20, ne_eq, not_false_eq_true, true_and, if_true]
    split_ifs <;> norm_num

/-! ## 1.  The logarithmic comparison -/

/-- `log √M + 2 ≤ 6·(1 + log(r+X+Y+2))` for `M = r(X²+Y²)`, `r,X,Y ≥ 1`. -/
private lemma log_sqrtM_le (r X Y : ℕ) (hr : 1 ≤ r) (hX : 1 ≤ X) (hY : 1 ≤ Y) :
    Real.log ((Nat.sqrt (r * (X ^ 2 + Y ^ 2)) : ℕ) : ℝ) + 2
      ≤ 6 * (1 + Real.log ((r : ℝ) + (X : ℝ) + (Y : ℝ) + 2)) := by
  set S : ℝ := (r : ℝ) + (X : ℝ) + (Y : ℝ) with hS
  have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hX1 : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hY1 : (1 : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hY
  have hSpos : (0 : ℝ) < S := by rw [hS]; linarith
  have hM1 : 1 ≤ r * (X ^ 2 + Y ^ 2) := by
    have h2 : 1 ≤ X ^ 2 + Y ^ 2 := by nlinarith
    calc (1 : ℕ) = 1 * 1 := by ring
      _ ≤ r * (X ^ 2 + Y ^ 2) := Nat.mul_le_mul hr h2
  have hMle : ((r * (X ^ 2 + Y ^ 2) : ℕ) : ℝ) ≤ S ^ 3 := by
    have hcast : ((r * (X ^ 2 + Y ^ 2) : ℕ) : ℝ)
        = (r : ℝ) * ((X : ℝ) ^ 2 + (Y : ℝ) ^ 2) := by push_cast; ring
    have h2 : (X : ℝ) ^ 2 + (Y : ℝ) ^ 2 ≤ ((X : ℝ) + (Y : ℝ)) ^ 2 := by
      nlinarith [sq_nonneg ((X : ℝ) - (Y : ℝ))]
    have h3 : ((X : ℝ) + (Y : ℝ)) ^ 2 ≤ S ^ 2 := by
      rw [hS]; exact pow_le_pow_left₀ (by linarith) (by linarith) 2
    have h4 : ((r * (X ^ 2 + Y ^ 2) : ℕ) : ℝ) ≤ (r : ℝ) * S ^ 2 := by
      rw [hcast]
      exact mul_le_mul_of_nonneg_left (le_trans h2 h3) (by linarith)
    have h5 : (r : ℝ) * S ^ 2 ≤ S * S ^ 2 :=
      mul_le_mul_of_nonneg_right (by rw [hS]; linarith) (pow_nonneg (le_of_lt hSpos) 2)
    linarith [h4, h5, show S * S ^ 2 = S ^ 3 by ring]
  have hsqrt1 : (1 : ℝ) ≤ ((Nat.sqrt (r * (X ^ 2 + Y ^ 2)) : ℕ) : ℝ) := by
    have h1 : 1 ≤ Nat.sqrt (r * (X ^ 2 + Y ^ 2)) := by
      rw [Nat.le_sqrt']
      calc (1 : ℕ) = 1 ^ 2 := by ring
        _ ≤ r * (X ^ 2 + Y ^ 2) := by simpa using hM1
    exact_mod_cast h1
  have hsq_le : ((Nat.sqrt (r * (X ^ 2 + Y ^ 2)) : ℕ) : ℝ)
      ≤ ((r * (X ^ 2 + Y ^ 2) : ℕ) : ℝ) := by
    exact_mod_cast Nat.sqrt_le_self (r * (X ^ 2 + Y ^ 2))
  have hlogS : Real.log S ≤ Real.log (S + 2) := Real.log_le_log hSpos (by linarith)
  have hlog : Real.log ((Nat.sqrt (r * (X ^ 2 + Y ^ 2)) : ℕ) : ℝ) ≤ 3 * Real.log (S + 2) := by
    have h1 : Real.log ((Nat.sqrt (r * (X ^ 2 + Y ^ 2)) : ℕ) : ℝ)
        ≤ Real.log ((r * (X ^ 2 + Y ^ 2) : ℕ) : ℝ) :=
      Real.log_le_log (by linarith) hsq_le
    have h2 : Real.log ((r * (X ^ 2 + Y ^ 2) : ℕ) : ℝ) ≤ Real.log (S ^ 3) :=
      Real.log_le_log (by linarith) hMle
    have h3 : Real.log (S ^ 3) = 3 * Real.log S := by
      rw [Real.log_pow]; push_cast; ring
    have h4 : 3 * Real.log S ≤ 3 * Real.log (S + 2) :=
      mul_le_mul_of_nonneg_left hlogS (by norm_num)
    linarith [h1, h2, h3, h4]
  have hL1 : (1 : ℝ) ≤ 1 + Real.log (S + 2) := by
    have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ S + 2)
    linarith
  have hS2 : (S : ℝ) + 2 = ((r : ℝ) + (X : ℝ) + (Y : ℝ) + 2) := by rw [hS]
  rw [hS2]
  linarith [hlog, hL1]

/-! ## 2.  The box estimate -/

theorem ubox_bound3
    (hLD : ∀ (c X S : ℕ) [NeZero c],
      (∑ h1 ∈ zPz X, ∑ v1 ∈ zPz S, ∑ v2 ∈ zPz S,
          (((Finset.univ : Finset (ZMod c)).filter
              (fun z => (v2 : ZMod c) * z ^ 2
                = (v1 : ZMod c) * ((h1 : ZMod c)) ^ 2)).card : ℝ)
            / ((max v1.natAbs v2.natAbs : ℕ) : ℝ))
        ≤ 64 * (X : ℝ) * (S : ℝ) * ((c.divisors.card : ℝ)) ^ 5)
    (hWB : ∃ C : ℝ, 0 < C ∧ ∀ (c r X Y : ℕ), 1 ≤ c → 1 ≤ r → 1 ≤ X → 1 ≤ Y →
      Work.FIArea2.R6.WC c r X Y
        ≤ C * (X : ℝ) * (Y : ℝ) * (r : ℝ) * ((c.divisors.card : ℕ) : ℝ) / (c : ℝ)
          + C * (X : ℝ) * (Y : ℝ) * (min (c : ℝ) ((X : ℝ) ^ 2 + (Y : ℝ) ^ 2))
              / (c : ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (r X Y : ℕ), 1 ≤ r → 1 ≤ X → 1 ≤ Y →
      Work.FIArea2.R6.uboxSum r X Y
        ≤ C * (r : ℝ) ^ 2 * (X : ℝ) * (Y : ℝ)
          * (1 + Real.log ((r : ℝ) + (X : ℝ) + (Y : ℝ) + 2)) ^ ((2 : ℕ) ^ (26 : ℕ)) := by
  obtain ⟨C20, hC20, h20⟩ := uboxSum_le_dsum3
  obtain ⟨CW, hCW, hWC⟩ := WC_cube hLD hWB
  obtain ⟨K, hK, hKb⟩ := Work.FIArea2.sum_tau_pow_div_le 26
  set N : ℕ := (2 : ℕ) ^ (26 : ℕ) with hN
  have h6pos : (0 : ℝ) < (6 : ℝ) ^ N := pow_pos (by norm_num) N
  refine ⟨C20 * CW * K * ((6 : ℝ) ^ N) + 1, ?_, ?_⟩
  · exact add_pos (mul_pos (mul_pos (mul_pos hC20 hCW) hK) h6pos) one_pos
  set P : ℝ := (6 : ℝ) ^ N with hP
  clear_value P N
  intro r X Y hr hX hY
  set M : ℕ := r * (X ^ 2 + Y ^ 2) with hM
  set L : ℝ := 1 + Real.log ((r : ℝ) + (X : ℝ) + (Y : ℝ) + 2) with hL
  have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hX1 : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hY1 : (1 : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hY
  have hL1 : (1 : ℝ) ≤ L := by
    rw [hL]
    have h0 : (0 : ℝ) ≤ Real.log ((r : ℝ) + (X : ℝ) + (Y : ℝ) + 2) :=
      Real.log_nonneg (by linarith)
    linarith
  have hLnn : (0 : ℝ) ≤ L := le_trans zero_le_one hL1
  -- Step 1: `Star d ≤ CW·X·Y·r·τ(d)^6`
  have hStar : ∀ d ∈ (Finset.Icc 1 (Nat.sqrt M)).filter (fun d => d ^ 3 ≤ M),
      Star d r X Y ≤ CW * (X : ℝ) * (Y : ℝ) * (r : ℝ) * ((d.divisors.card : ℝ)) ^ 6 := by
    intro d hd
    have hdI : d ∈ Finset.Icc 1 (Nat.sqrt M) := (Finset.mem_filter.mp hd).1
    have hd3 : d ^ 3 ≤ M := (Finset.mem_filter.mp hd).2
    have hdpos : 0 < d := by
      have h1 : 1 ≤ d := (Finset.mem_Icc.mp hdI).1
      omega
    have hdne : d ≠ 0 := by omega
    rw [star_eq_WC d r X Y hdpos]
    have hterm : ∀ c ∈ d.divisors,
        (Nat.totient c : ℝ) * Work.FIArea2.R6.WC c r X Y
          ≤ CW * (X : ℝ) * (Y : ℝ) * (r : ℝ) * ((d.divisors.card : ℝ)) ^ 5 := by
      intro c hc
      have hcd : c ∣ d := Nat.dvd_of_mem_divisors hc
      have hc1 : 1 ≤ c := Nat.pos_of_dvd_of_pos hcd hdpos
      have hcpos : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc1
      have hc3 : c ^ 3 ≤ r * (X ^ 2 + Y ^ 2) := by
        have h3 : c ^ 3 ≤ d ^ 3 := Nat.pow_le_pow_left (Nat.le_of_dvd hdpos hcd) 3
        calc c ^ 3 ≤ d ^ 3 := h3
          _ ≤ M := hd3
          _ = r * (X ^ 2 + Y ^ 2) := hM
      have hwc := hWC c r X Y hc1 hr hX hY hc3
      have hφc : (Nat.totient c : ℝ) ≤ (c : ℝ) := by
        exact_mod_cast Nat.totient_le c
      have hτc : ((c.divisors.card : ℝ)) ≤ ((d.divisors.card : ℝ)) := by
        exact_mod_cast Finset.card_le_card (Nat.divisors_subset_of_dvd hdne hcd)
      have hA : (0 : ℝ) ≤ CW * (X : ℝ) * (Y : ℝ) * (r : ℝ) := by positivity
      have hstep : (Nat.totient c : ℝ)
            * (CW * (X : ℝ) * (Y : ℝ) * (r : ℝ) * ((c.divisors.card : ℝ)) ^ 5 / (c : ℝ))
          ≤ CW * (X : ℝ) * (Y : ℝ) * (r : ℝ) * ((d.divisors.card : ℝ)) ^ 5 := by
        have h1 : (Nat.totient c : ℝ) / (c : ℝ) ≤ 1 := by
          rw [div_le_one hcpos]; exact hφc
        have h2 : (Nat.totient c : ℝ)
              * (CW * (X : ℝ) * (Y : ℝ) * (r : ℝ) * ((c.divisors.card : ℝ)) ^ 5 / (c : ℝ))
            = ((Nat.totient c : ℝ) / (c : ℝ))
              * (CW * (X : ℝ) * (Y : ℝ) * (r : ℝ) * ((c.divisors.card : ℝ)) ^ 5) := by ring
        rw [h2]
        have h3 : ((Nat.totient c : ℝ) / (c : ℝ))
              * (CW * (X : ℝ) * (Y : ℝ) * (r : ℝ) * ((c.divisors.card : ℝ)) ^ 5)
            ≤ 1 * (CW * (X : ℝ) * (Y : ℝ) * (r : ℝ) * ((c.divisors.card : ℝ)) ^ 5) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
        have h4 : ((c.divisors.card : ℝ)) ^ 5 ≤ ((d.divisors.card : ℝ)) ^ 5 :=
          pow_le_pow_left₀ (by positivity) hτc 5
        have h5 : CW * (X : ℝ) * (Y : ℝ) * (r : ℝ) * ((c.divisors.card : ℝ)) ^ 5
            ≤ CW * (X : ℝ) * (Y : ℝ) * (r : ℝ) * ((d.divisors.card : ℝ)) ^ 5 :=
          mul_le_mul_of_nonneg_left h4 hA
        linarith [h3, h5]
      calc (Nat.totient c : ℝ) * Work.FIArea2.R6.WC c r X Y
          ≤ (Nat.totient c : ℝ)
              * (CW * (X : ℝ) * (Y : ℝ) * (r : ℝ) * ((c.divisors.card : ℝ)) ^ 5 / (c : ℝ)) :=
            mul_le_mul_of_nonneg_left hwc (by positivity)
        _ ≤ _ := hstep
    calc (∑ c ∈ d.divisors, (Nat.totient c : ℝ) * Work.FIArea2.R6.WC c r X Y)
        ≤ ∑ c ∈ d.divisors, CW * (X : ℝ) * (Y : ℝ) * (r : ℝ)
            * ((d.divisors.card : ℝ)) ^ 5 := Finset.sum_le_sum hterm
      _ = ((d.divisors.card : ℕ) : ℝ) * (CW * (X : ℝ) * (Y : ℝ) * (r : ℝ)
            * ((d.divisors.card : ℝ)) ^ 5) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = CW * (X : ℝ) * (Y : ℝ) * (r : ℝ) * ((d.divisors.card : ℝ)) ^ 6 := by
          rw [pow_succ]; ring
  -- Step 2: the termwise bound
  have hterm : ∀ d ∈ (Finset.Icc 1 (Nat.sqrt M)).filter (fun d => d ^ 3 ≤ M),
      ((d.divisors.card : ℝ)) ^ 20 * ndCount d r X Y
        ≤ CW * (r : ℝ) ^ 2 * (X : ℝ) * (Y : ℝ)
            * (((d.divisors.card : ℝ)) ^ 26 / (d : ℝ)) := by
    intro d hd
    have hdI : d ∈ Finset.Icc 1 (Nat.sqrt M) := (Finset.mem_filter.mp hd).1
    have hd3 : d ^ 3 ≤ M := (Finset.mem_filter.mp hd).2
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hdI).1
    have hdpos : 0 < d := by omega
    have hdposR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hdpos
    have hnd : ndCount d r X Y ≤ (r : ℝ) / (d : ℝ) * Star d r X Y :=
      le_trans (ndCount_le_UL d r X Y) (ul_le_star_public d r X Y hd1)
    have hsd : Star d r X Y ≤ CW * (X : ℝ) * (Y : ℝ) * (r : ℝ)
        * ((d.divisors.card : ℝ)) ^ 6 := hStar d (Finset.mem_filter.mpr ⟨hdI, hd3⟩)
    have hτnn : (0 : ℝ) ≤ ((d.divisors.card : ℝ)) ^ 20 := by positivity
    calc ((d.divisors.card : ℝ)) ^ 20 * ndCount d r X Y
        ≤ ((d.divisors.card : ℝ)) ^ 20 * ((r : ℝ) / (d : ℝ) * Star d r X Y) :=
          mul_le_mul_of_nonneg_left hnd hτnn
      _ ≤ ((d.divisors.card : ℝ)) ^ 20
            * ((r : ℝ) / (d : ℝ) * (CW * (X : ℝ) * (Y : ℝ) * (r : ℝ)
                * ((d.divisors.card : ℝ)) ^ 6)) := by
          refine mul_le_mul_of_nonneg_left ?_ hτnn
          exact mul_le_mul_of_nonneg_left hsd (by positivity)
      _ = CW * (r : ℝ) ^ 2 * (X : ℝ) * (Y : ℝ)
            * (((d.divisors.card : ℝ)) ^ 26 / (d : ℝ)) := by
          have hdd : (d : ℝ) ≠ 0 := ne_of_gt hdposR
          field_simp
  -- Step 3: assemble
  have hfilter : (∑ d ∈ (Finset.Icc 1 (Nat.sqrt M)).filter (fun d => d ^ 3 ≤ M),
        ((d.divisors.card : ℝ)) ^ 26 / (d : ℝ))
      ≤ ∑ d ∈ Finset.Icc 1 (Nat.sqrt M), ((d.divisors.card : ℝ)) ^ 26 / (d : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun d _ _ => by positivity)
  have hKb' : (∑ d ∈ Finset.Icc 1 (Nat.sqrt M), ((d.divisors.card : ℝ)) ^ 26 / (d : ℝ))
      ≤ K * (Real.log ((Nat.sqrt M : ℕ) : ℝ) + 2) ^ N := hKb (Nat.sqrt M)
  have hM1 : 1 ≤ M := by
    rw [hM]
    have h3 : 1 ≤ X ^ 2 + Y ^ 2 :=
      le_trans (Nat.one_le_pow 2 X hX) (Nat.le_add_right _ _)
    calc (1 : ℕ) = 1 * 1 := by norm_num
      _ ≤ r * (X ^ 2 + Y ^ 2) := Nat.mul_le_mul hr h3
  have hpow : (Real.log ((Nat.sqrt M : ℕ) : ℝ) + 2) ^ N ≤ (6 * L) ^ N := by
    refine pow_le_pow_left₀ ?_ ?_ N
    · have h1 : (1 : ℝ) ≤ ((Nat.sqrt M : ℕ) : ℝ) := by
        have h2 : 1 ≤ Nat.sqrt M := by
          rw [Nat.le_sqrt']
          simpa using hM1
        exact_mod_cast h2
      have h0 := Real.log_nonneg h1
      linarith only [h0]
    · have h := log_sqrtM_le r X Y hr hX hY
      rw [← hM, ← hL] at h
      exact h
  have hB : (∑ d ∈ (Finset.Icc 1 (Nat.sqrt M)).filter (fun d => d ^ 3 ≤ M),
        ((d.divisors.card : ℝ)) ^ 26 / (d : ℝ)) ≤ K * (6 * L) ^ N :=
    le_trans hfilter (le_trans hKb' (mul_le_mul_of_nonneg_left hpow hK.le))
  have hC : (∑ d ∈ (Finset.Icc 1 (Nat.sqrt M)).filter (fun d => d ^ 3 ≤ M),
        CW * (r : ℝ) ^ 2 * (X : ℝ) * (Y : ℝ) * (((d.divisors.card : ℝ)) ^ 26 / (d : ℝ)))
      = CW * (r : ℝ) ^ 2 * (X : ℝ) * (Y : ℝ)
        * (∑ d ∈ (Finset.Icc 1 (Nat.sqrt M)).filter (fun d => d ^ 3 ≤ M),
            ((d.divisors.card : ℝ)) ^ 26 / (d : ℝ)) := by
    rw [Finset.mul_sum]
  have hA : (∑ d ∈ (Finset.Icc 1 (Nat.sqrt M)).filter (fun d => d ^ 3 ≤ M),
        ((d.divisors.card : ℝ)) ^ 20 * ndCount d r X Y)
      ≤ CW * (r : ℝ) ^ 2 * (X : ℝ) * (Y : ℝ)
        * (∑ d ∈ (Finset.Icc 1 (Nat.sqrt M)).filter (fun d => d ^ 3 ≤ M),
            ((d.divisors.card : ℝ)) ^ 26 / (d : ℝ)) := by
    rw [← hC]
    exact Finset.sum_le_sum hterm
  have hsum : (∑ d ∈ (Finset.Icc 1 (Nat.sqrt M)).filter (fun d => d ^ 3 ≤ M),
        ((d.divisors.card : ℝ)) ^ 20 * ndCount d r X Y)
      ≤ CW * (r : ℝ) ^ 2 * (X : ℝ) * (Y : ℝ) * (K * (6 * L) ^ N) :=
    le_trans hA (mul_le_mul_of_nonneg_left hB (by positivity))
  -- Step 4: absorb `P = 6^N` into the constant
  have hZ : (0 : ℝ) ≤ (r : ℝ) ^ 2 * (X : ℝ) * (Y : ℝ) * L ^ N :=
    mul_nonneg (by positivity) (pow_nonneg hLnn N)
  have hmain : C20 * (∑ d ∈ (Finset.Icc 1 (Nat.sqrt M)).filter (fun d => d ^ 3 ≤ M),
        ((d.divisors.card : ℝ)) ^ 20 * ndCount d r X Y)
      ≤ (C20 * CW * K * P + 1)
        * ((r : ℝ) ^ 2 * (X : ℝ) * (Y : ℝ) * L ^ N) := by
    have h1 : C20 * (∑ d ∈ (Finset.Icc 1 (Nat.sqrt M)).filter (fun d => d ^ 3 ≤ M),
          ((d.divisors.card : ℝ)) ^ 20 * ndCount d r X Y)
        ≤ C20 * (CW * (r : ℝ) ^ 2 * (X : ℝ) * (Y : ℝ) * (K * (6 * L) ^ N)) :=
      mul_le_mul_of_nonneg_left hsum hC20.le
    have h2 : C20 * (CW * (r : ℝ) ^ 2 * (X : ℝ) * (Y : ℝ) * (K * (6 * L) ^ N))
        = (C20 * CW * K * P) * ((r : ℝ) ^ 2 * (X : ℝ) * (Y : ℝ) * L ^ N) := by
      rw [hP, mul_pow]; ring
    have h3 : (C20 * CW * K * P) * ((r : ℝ) ^ 2 * (X : ℝ) * (Y : ℝ) * L ^ N)
        ≤ (C20 * CW * K * P + 1) * ((r : ℝ) ^ 2 * (X : ℝ) * (Y : ℝ) * L ^ N) :=
      mul_le_mul_of_nonneg_right (by linarith) hZ
    linarith [h1, h2, h3]
  calc Work.FIArea2.R6.uboxSum r X Y
      ≤ C20 * ∑ d ∈ (Finset.Icc 1 (Nat.sqrt (r * (X ^ 2 + Y ^ 2)))).filter
            (fun d => d ^ 3 ≤ r * (X ^ 2 + Y ^ 2)),
          ((d.divisors.card : ℝ)) ^ 20 * ndCount d r X Y := h20 r X Y hr hX hY
    _ = C20 * ∑ d ∈ (Finset.Icc 1 (Nat.sqrt M)).filter (fun d => d ^ 3 ≤ M),
          ((d.divisors.card : ℝ)) ^ 20 * ndCount d r X Y := by rw [hM]
    _ ≤ (C20 * CW * K * P + 1) * ((r : ℝ) ^ 2 * (X : ℝ) * (Y : ℝ) * L ^ N) := hmain
    _ = (C20 * CW * K * P + 1) * (r : ℝ) ^ 2 * (X : ℝ) * (Y : ℝ) * L ^ N := by
        ring

end

end Work.FIArea2.R6
