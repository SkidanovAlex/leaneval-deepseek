import Mathlib
import Submission.FixedUDefs
import Submission.Deep
import Submission.DeepCore
set_option maxRecDepth 20000

/-!
# Case-1 weighted sum is at most C(N,v)·r^k

Context: the fixed-U environment with ground set `X`, `U ⊆ X`, `V` ranging
over `v`-subsets of `X\U`, k-uniform r-spread S.  Here we only use the
*count bound* for the case-1 fibres:

  hc1 : for all s,t with 1 ≤ t ≤ s,
      |case1Fiber(s,t)| ≤ |bigB0(s)| · 4^s · φ(s,t)
      where φ(s,t) = r^k·(ρv/n)^s·(vr/n)^{-t},  n := |X|,
      bigB0(s) = the subsets of X\U of sizes v..v+s.

Conclusion:
  Σ_{j ∈ idxSet k} wfib(j)·|case1Fiber(j.1,j.2)| ≤ C(N,v)·r^k
with C(N,v) := |cardSubsets (X\U) v|, idxSet k := {(s,t): 1≤s≤k, 1≤t≤s},
wfib(s,t) := exp(26·t − 20·s).
-/
open Finset
open scoped BigOperators
open Real

namespace Submission.Sun

variable {α : Type*} [DecidableEq α]

/-- the t-sum over Icc 1 k with the condition t ≤ s collapses to Icc 1 s -/
lemma sum_ite_Icc_le_s_aux {s k : ℕ} (hs1 : 1 ≤ s) (hsk : s ≤ k) (f : ℕ → ℝ) :
    (∑ t ∈ Finset.Icc 1 k, if t ≤ s then f t else 0) = ∑ t ∈ Finset.Icc 1 s, f t := by
  classical
  calc
    (∑ t ∈ Finset.Icc 1 k, if t ≤ s then f t else 0)
        = ∑ t ∈ (Finset.Icc 1 k).filter (fun t => t ≤ s), f t := by
          rw [Finset.sum_filter]
    _ = ∑ t ∈ Finset.Icc 1 s, f t := by
          congr 1
          ext t
          constructor
          · intro ht
            have h := Finset.mem_filter.mp ht
            have h1 : 1 ≤ t := (Finset.mem_Icc.mp h.1).1
            exact Finset.mem_Icc.mpr ⟨h1, h.2⟩
          · intro ht
            have h := Finset.mem_Icc.mp ht
            rw [Finset.mem_filter]
            exact ⟨Finset.mem_Icc.mpr ⟨h.1, le_trans h.2 hsk⟩, h.2⟩

/-- a sum over idxSet equals the double sum over s,t -/
lemma sum_idxSet_aux {k : ℕ} (f : ℕ × ℕ → ℝ) :
    (∑ j ∈ idxSet k, f j) = ∑ s ∈ Finset.Icc 1 k, ∑ t ∈ Finset.Icc 1 s, f (s, t) := by
  classical
  calc
    (∑ j ∈ idxSet k, f j) = ∑ j ∈ ((Finset.Icc 1 k) ×ˢ (Finset.Icc 1 k)).filter (fun (s,t) => t ≤ s), f j := by
        rfl
    _ = ∑ s ∈ Finset.Icc 1 k, ∑ t ∈ Finset.Icc 1 k, if t ≤ s then f (s, t) else 0 := by
        rw [Finset.sum_filter, Finset.sum_product]
    _ = ∑ s ∈ Finset.Icc 1 k, ∑ t ∈ Finset.Icc 1 s, f (s, t) := by
          apply Finset.sum_congr rfl
          intro s hs
          have hs1 : 1 ≤ s := (Finset.mem_Icc.mp hs).1
          have hsk : s ≤ k := (Finset.mem_Icc.mp hs).2
          exact sum_ite_Icc_le_s_aux (s := s) (k := k) hs1 hsk (fun t => f (s, t))

/-- per-(s,t) bound: wfib·|fiber| ≤ (s+1)·C(N,v)·r^k·(1/4)^s·q^t,
    q := exp26·|X|/(v·r) -/
lemma c1term_le {X : Finset α} {S : Finset (Finset α)} {U : Finset α} {v k s t : ℕ} {r : ℝ}
    (hv : 0 < v) (hr1 : 1 ≤ r) (hn : 0 < X.card) (hvn : v ≤ (X \ U).card)
    (hfib : (((case1Fiber X S U v r k s t).card : ℝ) ≤
      (bigB0 X U v s).card * (4 : ℝ) ^ s * phiVal r k X v s t)) :
    wfib (s, t) * (((case1Fiber X S U v r k s t).card : ℝ)) ≤
      ((s + 1 : ℕ) : ℝ) * (((X \ U).card.choose v : ℕ) : ℝ) * (r ^ k) *
        ((1 / 4 : ℝ) ^ s) * ((Real.exp 26 * (X.card : ℝ) / ((v : ℝ) * r)) ^ t) := by
  classical
  let Cc : ℝ := (((X \ U).card.choose v : ℕ) : ℝ)
  let q : ℝ := Real.exp 26 * (X.card : ℝ) / ((v : ℝ) * r)
  let base1 : ℝ := (4 : ℝ) * rho * (((X \ U).card : ℝ) / (X.card : ℝ)) * Real.exp (-20)
  let Nv : ℝ := ((X \ U).card : ℝ) / (v : ℝ)
  have hvR : 0 < (v : ℝ) := by exact_mod_cast hv
  have hnR : 0 < (X.card : ℝ) := by exact_mod_cast hn
  have hrR : 0 < r := lt_of_lt_of_le (by norm_num) hr1
  have hrho0 : 0 ≤ rho := by unfold rho; positivity
  -- φ ≥ 0
  have hphi0 : 0 ≤ phiVal r k X v s t := by
    unfold phiVal phi
    have hr0 : 0 ≤ r := le_of_lt hrR
    have hn0 : 0 ≤ (X.card : ℝ) := le_of_lt hnR
    have hv0 : 0 ≤ (v : ℝ) := le_of_lt hvR
    have hden0 : 0 ≤ (((v : ℝ) * r / (X.card : ℝ)) ^ t) := by positivity
    have hbase0 : 0 ≤ (rho : ℝ) * (v : ℝ) / (X.card : ℝ) := by positivity
    have hnum0 : 0 ≤ (r ^ k) * (((rho : ℝ) * (v : ℝ) / (X.card : ℝ)) ^ s) := by
      exact mul_nonneg (pow_nonneg hr0 k) (pow_nonneg hbase0 s)
    exact div_nonneg hnum0 hden0
  have hw0 : 0 ≤ wfib (s, t) := by unfold wfib; positivity
  have hw4 : 0 ≤ wfib (s, t) * (4 : ℝ) ^ s * phiVal r k X v s t := by
    exact mul_nonneg (mul_nonneg hw0 (by positivity)) hphi0
  -- decompose wfib and φ into separated power factors
  have hwf : wfib (s, t) = (Real.exp (-20)) ^ s * (Real.exp 26) ^ t := by
    have h1 : Real.exp ((26 : ℝ) * (t : ℝ)) = (Real.exp 26) ^ t := by
      have h : (26 : ℝ) * (t : ℝ) = ((t : ℕ) : ℝ) * (26 : ℝ) := by ring
      rw [h]
      exact Real.exp_nat_mul (26 : ℝ) t
    have h2 : Real.exp (-((20 : ℝ) * (s : ℝ))) = (Real.exp (-20)) ^ s := by
      have h : -((20 : ℝ) * (s : ℝ)) = ((s : ℕ) : ℝ) * (-20 : ℝ) := by ring
      rw [h]
      exact Real.exp_nat_mul (-20 : ℝ) s
    calc
      wfib (s, t) = Real.exp ((26 : ℝ) * (t : ℝ) - (20 : ℝ) * (s : ℝ)) := rfl
      _ = Real.exp ((26 : ℝ) * (t : ℝ)) * Real.exp (-((20 : ℝ) * (s : ℝ))) := by
          rw [show (26 : ℝ) * (t : ℝ) - (20 : ℝ) * (s : ℝ) = (26 : ℝ) * (t : ℝ) + (-((20 : ℝ) * (s : ℝ))) by ring]
          rw [Real.exp_add]
      _ = (Real.exp 26) ^ t * (Real.exp (-20)) ^ s := by rw [h1, h2]
      _ = (Real.exp (-20)) ^ s * (Real.exp 26) ^ t := by ring
  have hphi : phiVal r k X v s t = (r ^ k) * ((rho * (v : ℝ) / (X.card : ℝ)) ^ s)
        * ((X.card : ℝ) / ((v : ℝ) * r)) ^ t := by
    unfold phiVal phi
    calc
      ((r ^ k) * ((rho * (v : ℝ) / (X.card : ℝ)) ^ s)) / (((v : ℝ) * r / (X.card : ℝ)) ^ t)
          = ((r ^ k) * ((rho * (v : ℝ) / (X.card : ℝ)) ^ s))
              * ((((v : ℝ) * r / (X.card : ℝ)) ^ t)⁻¹) := by
              rw [div_eq_mul_inv]
      _ = (r ^ k) * ((rho * (v : ℝ) / (X.card : ℝ)) ^ s) * ((X.card : ℝ) / ((v : ℝ) * r)) ^ t := by
              have hinv : (((v : ℝ) * r / (X.card : ℝ)) ^ t)⁻¹ = ((X.card : ℝ) / ((v : ℝ) * r)) ^ t := by
                rw [← inv_pow]
                congr 1
                field_simp [hvR.ne', hrR.ne', hnR.ne']
              rw [hinv]
  -- the algebra: gather s-powers and t-powers, clean the bases
  have hscomb : (Real.exp (-20)) ^ s * (4 : ℝ) ^ s * Nv ^ s * ((rho * (v : ℝ) / (X.card : ℝ)) ^ s)
      = (Real.exp (-20) * 4 * Nv * (rho * (v : ℝ) / (X.card : ℝ))) ^ s := by
      rw [← mul_pow, ← mul_pow, ← mul_pow]
  have htcomb : (Real.exp 26) ^ t * ((X.card : ℝ) / ((v : ℝ) * r)) ^ t
      = (Real.exp 26 * ((X.card : ℝ) / ((v : ℝ) * r))) ^ t := by
      rw [← mul_pow]
  have hbase : Real.exp (-20) * 4 * Nv * (rho * (v : ℝ) / (X.card : ℝ)) = base1 := by
      dsimp [base1, Nv]
      field_simp [hvR.ne', hnR.ne']
  have htbase : Real.exp 26 * ((X.card : ℝ) / ((v : ℝ) * r)) = q := by
      dsimp [q]
      field_simp [hrR.ne', hnR.ne']
  have halg : (wfib (s, t) * (4 : ℝ) ^ s * phiVal r k X v s t) * Nv ^ s
      = (r ^ k) * base1 ^ s * (q ^ t) := by
    calc
      (wfib (s, t) * (4 : ℝ) ^ s * phiVal r k X v s t) * Nv ^ s
          = ((Real.exp (-20)) ^ s * (Real.exp 26) ^ t * (4 : ℝ) ^ s
              * ((r ^ k) * ((rho * (v : ℝ) / (X.card : ℝ)) ^ s) * ((X.card : ℝ) / ((v : ℝ) * r)) ^ t)) * Nv ^ s := by
              rw [hwf, hphi]
      _ = (r ^ k) * ((Real.exp (-20)) ^ s * (4 : ℝ) ^ s * Nv ^ s * ((rho * (v : ℝ) / (X.card : ℝ)) ^ s))
              * ((Real.exp 26) ^ t * ((X.card : ℝ) / ((v : ℝ) * r)) ^ t) := by ring
      _ = (r ^ k) * ((Real.exp (-20) * 4 * Nv * (rho * (v : ℝ) / (X.card : ℝ))) ^ s)
              * ((Real.exp 26 * ((X.card : ℝ) / ((v : ℝ) * r))) ^ t) := by
              rw [hscomb, htcomb]
      _ = (r ^ k) * base1 ^ s * (q ^ t) := by
              have hps : (Real.exp (-20) * 4 * Nv * (rho * (v : ℝ) / (X.card : ℝ))) ^ s = base1 ^ s :=
                congrArg (fun z : ℝ => z ^ s) hbase
              have hpt : (Real.exp 26 * ((X.card : ℝ) / ((v : ℝ) * r))) ^ t = q ^ t :=
                congrArg (fun z : ℝ => z ^ t) htbase
              rw [hps, hpt]
  -- monotonicity: base1 ≤ 1/4
  have hNn1 : ((X \ U).card : ℝ) / (X.card : ℝ) ≤ 1 := by
    have hsub : X \ U ⊆ X := Finset.sdiff_subset
    have hcard : (X \ U).card ≤ X.card := Finset.card_le_card hsub
    have hcast : ((X \ U).card : ℝ) ≤ (X.card : ℝ) := by exact_mod_cast hcard
    rw [div_le_iff₀ hnR]
    simpa using hcast
  have h18 : (4 : ℝ) * rho * Real.exp (-20) ≤ (1 / 4 : ℝ) := by
    calc
      (4 : ℝ) * rho * Real.exp (-20) = Real.exp (-20) * (2 : ℝ) ^ 18 := by
          unfold rho
          norm_num [pow_succ]
          ring
      _ ≤ 1 / 4 := exp_neg20_two18_le_quarter
  have hbase14 : base1 ≤ (1 / 4 : ℝ) := by
    calc
      base1 = ((4 : ℝ) * rho * Real.exp (-20)) * (((X \ U).card : ℝ) / (X.card : ℝ)) := by
          dsimp [base1]
          ring
      _ ≤ ((4 : ℝ) * rho * Real.exp (-20)) * 1 := by
          exact mul_le_mul_of_nonneg_left hNn1 (by positivity)
      _ = (4 : ℝ) * rho * Real.exp (-20) := by ring
      _ ≤ 1 / 4 := h18
  have hbase0 : 0 ≤ base1 := by dsimp [base1]; positivity
  have hb14pow : base1 ^ s ≤ (1 / 4 : ℝ) ^ s := pow_le_pow_left₀ hbase0 hbase14 s
  have hP0 : 0 ≤ ((s + 1 : ℕ) : ℝ) * Cc * (r ^ k) := by positivity
  have hqt0 : 0 ≤ q ^ t := by positivity
  calc
    wfib (s, t) * (((case1Fiber X S U v r k s t).card : ℝ))
        ≤ wfib (s, t) * (((bigB0 X U v s).card : ℝ) * (4 : ℝ) ^ s * phiVal r k X v s t) := by
            exact mul_le_mul_of_nonneg_left hfib hw0
    _ = (((bigB0 X U v s).card : ℝ)) * (wfib (s, t) * (4 : ℝ) ^ s * phiVal r k X v s t) := by ring
    _ ≤ (((s + 1 : ℕ) : ℝ) * Cc * (((X \ U).card : ℝ) / (v : ℝ)) ^ s)
            * (wfib (s, t) * (4 : ℝ) ^ s * phiVal r k X v s t) := by
            have hb := bigB0_real_le (X := X) (U := U) (v := v) (s := s) hv hvn
            exact mul_le_mul_of_nonneg_right hb hw4
    _ = ((s + 1 : ℕ) : ℝ) * Cc * ((wfib (s, t) * (4 : ℝ) ^ s * phiVal r k X v s t) * Nv ^ s) := by
            dsimp [Nv]
            ring
    _ = ((s + 1 : ℕ) : ℝ) * Cc * ((r ^ k) * base1 ^ s * (q ^ t)) := by
            rw [halg]
    _ = ((s + 1 : ℕ) : ℝ) * Cc * (r ^ k) * base1 ^ s * (q ^ t) := by ring
    _ ≤ ((s + 1 : ℕ) : ℝ) * Cc * (r ^ k) * ((1 / 4 : ℝ) ^ s) * (q ^ t) := by
            -- base1^s ≤ (1/4)^s with nonneg prefix
            have h1 : ((s + 1 : ℕ) : ℝ) * Cc * (r ^ k) * base1 ^ s
                ≤ ((s + 1 : ℕ) : ℝ) * Cc * (r ^ k) * (1 / 4 : ℝ) ^ s := by
                exact mul_le_mul_of_nonneg_left hb14pow hP0
            exact mul_le_mul_of_nonneg_right h1 hqt0

/-- generic double-sum bound:
    Σ_s Σ_{t≤s} (s+1)·Cc·F·(1/4)^s·q^t ≤ Cc·F  provided 0 ≤ q ≤ 1/2, 0 ≤ Cc, 0 ≤ F -/
lemma double_sum_le {k : ℕ} {Cc F q : ℝ} (hC0 : 0 ≤ Cc) (hF0 : 0 ≤ F)
    (hq0 : 0 ≤ q) (hq : q ≤ 1 / 2) :
    (∑ s ∈ Finset.Icc 1 k, ∑ t ∈ Finset.Icc 1 s,
        ((s + 1 : ℕ) : ℝ) * Cc * F * ((1 / 4 : ℝ) ^ s) * q ^ t) ≤ Cc * F := by
  classical
  calc
    (∑ s ∈ Finset.Icc 1 k, ∑ t ∈ Finset.Icc 1 s,
        ((s + 1 : ℕ) : ℝ) * Cc * F * ((1 / 4 : ℝ) ^ s) * q ^ t)
        = (∑ s ∈ Finset.Icc 1 k,
            ((s + 1 : ℕ) : ℝ) * Cc * F * ((1 / 4 : ℝ) ^ s) * (∑ t ∈ Finset.Icc 1 s, q ^ t)) := by
            apply Finset.sum_congr rfl
            intro s hs
            calc
              (∑ t ∈ Finset.Icc 1 s, ((s + 1 : ℕ) : ℝ) * Cc * F * ((1 / 4 : ℝ) ^ s) * q ^ t)
                  = (∑ t ∈ Finset.Icc 1 s,
                      (((s + 1 : ℕ) : ℝ) * Cc * F * ((1 / 4 : ℝ) ^ s)) * q ^ t) := by
                      apply Finset.sum_congr rfl
                      intro t ht
                      ring
              _ = (((s + 1 : ℕ) : ℝ) * Cc * F * ((1 / 4 : ℝ) ^ s)) * (∑ t ∈ Finset.Icc 1 s, q ^ t) := by
                      exact (Finset.mul_sum (Finset.Icc 1 s) (fun t : ℕ => q ^ t)
                        (((s + 1 : ℕ) : ℝ) * Cc * F * ((1 / 4 : ℝ) ^ s))).symm
    _ ≤ (∑ s ∈ Finset.Icc 1 k, ((s + 1 : ℕ) : ℝ) * Cc * F * ((1 / 4 : ℝ) ^ s)) := by
        apply Finset.sum_le_sum
        intro s hs
        have hqs : (∑ t ∈ Finset.Icc 1 s, q ^ t) ≤ 1 := sum_q_Icc_le_one (s := s) (q := q) hq0 hq
        have hX0 : 0 ≤ ((s + 1 : ℕ) : ℝ) * Cc * F * ((1 / 4 : ℝ) ^ s) := by positivity
        calc
          ((s + 1 : ℕ) : ℝ) * Cc * F * ((1 / 4 : ℝ) ^ s) * (∑ t ∈ Finset.Icc 1 s, q ^ t)
              ≤ ((s + 1 : ℕ) : ℝ) * Cc * F * ((1 / 4 : ℝ) ^ s) * 1 := by
                  exact mul_le_mul_of_nonneg_left hqs hX0
          _ = ((s + 1 : ℕ) : ℝ) * Cc * F * ((1 / 4 : ℝ) ^ s) := by ring
    _ = (∑ s ∈ Finset.Icc 1 k, (((s + 1 : ℕ) : ℝ) * ((1 / 4 : ℝ) ^ s)) * (Cc * F)) := by
        apply Finset.sum_congr rfl
        intro s hs
        ring
    _ = (∑ s ∈ Finset.Icc 1 k, ((s + 1 : ℕ) : ℝ) * ((1 / 4 : ℝ) ^ s)) * (Cc * F) := by
        exact (Finset.sum_mul (Finset.Icc 1 k)
          (fun s : ℕ => ((s + 1 : ℕ) : ℝ) * ((1 / 4 : ℝ) ^ s)) (Cc * F)).symm
    _ ≤ 1 * (Cc * F) := by
        have hsumc : (∑ s ∈ Finset.Icc 1 k, ((s + 1 : ℕ) : ℝ) * (1 / 4 : ℝ) ^ s) ≤ 1 :=
          sum_succ_fourth_le_one k
        exact mul_le_mul_of_nonneg_right hsumc (mul_nonneg hC0 hF0)
    _ = Cc * F := by ring

/-- case-1 weighted sum ≤ C(N,v)·r^k -/
theorem c1Sum_le {X : Finset α} {S : Finset (Finset α)} {U : Finset α} {v k : ℕ} {r : ℝ}
    (hU : U ⊆ X) (hS : ∀ A ∈ S, A ⊆ X) (hnm : ¬ ∃ A' ∈ S, A' ⊆ U)
    (huni : ∀ A ∈ S, A.card = k) (hr1 : 1 ≤ r)
    (hv : 0 < v) (hn : 0 < X.card) (hvn : v ≤ (X \ U).card)
    (hq : Real.exp 26 * (X.card : ℝ) / ((v : ℝ) * r) ≤ 1 / 2)
    (hc1 : ∀ s t : ℕ, 1 ≤ t → t ≤ s →
      (((case1Fiber X S U v r k s t).card : ℝ) ≤
        (bigB0 X U v s).card * (4 : ℝ) ^ s * phiVal r k X v s t)) :
    (∑ j ∈ idxSet k, wfib j * (case1Fiber X S U v r k j.1 j.2).card)
      ≤ (cardSubsets (X \ U) v).card * (r ^ k) := by
  classical
  let Cc : ℝ := (((X \ U).card.choose v : ℕ) : ℝ)
  let q : ℝ := Real.exp 26 * (X.card : ℝ) / ((v : ℝ) * r)
  have hvR : 0 < (v : ℝ) := by exact_mod_cast hv
  have hnR : 0 < (X.card : ℝ) := by exact_mod_cast hn
  have hrR : 0 < r := lt_of_lt_of_le (by norm_num) hr1
  have hC0 : 0 ≤ Cc := by dsimp [Cc]; positivity
  have hrk0 : 0 ≤ r ^ k := by positivity
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hq_le : q ≤ 1 / 2 := by simpa [q] using hq
  calc
    (∑ j ∈ idxSet k, wfib j * (case1Fiber X S U v r k j.1 j.2).card)
        = (∑ s ∈ Finset.Icc 1 k, ∑ t ∈ Finset.Icc 1 s,
            wfib (s, t) * (case1Fiber X S U v r k s t).card) := by
            have hrei := sum_idxSet_aux (k := k)
              (f := fun j : ℕ × ℕ => wfib j * (case1Fiber X S U v r k j.1 j.2).card)
            simpa using hrei
    _ ≤ (∑ s ∈ Finset.Icc 1 k, ∑ t ∈ Finset.Icc 1 s,
          ((s + 1 : ℕ) : ℝ) * Cc * (r ^ k) * ((1 / 4 : ℝ) ^ s) * (q ^ t)) := by
        apply Finset.sum_le_sum
        intro s hs
        apply Finset.sum_le_sum
        intro t ht
        have hs1 : 1 ≤ s := (Finset.mem_Icc.mp hs).1
        have ht1 : 1 ≤ t := (Finset.mem_Icc.mp ht).1
        have hts : t ≤ s := (Finset.mem_Icc.mp ht).2
        have hbnd := c1term_le (X := X) (S := S) (U := U) (v := v) (k := k) (s := s) (t := t)
          (r := r) hv hr1 hn hvn (hc1 s t ht1 hts)
        simpa [Cc, q] using hbnd
    _ ≤ Cc * (r ^ k) := by
        exact double_sum_le (k := k) (Cc := Cc) (F := r ^ k) (q := q) hC0 hrk0 hq0 hq_le
    _ = ((cardSubsets (X \ U) v).card : ℝ) * (r ^ k) := by
        have hcv : Cc = ((cardSubsets (X \ U) v).card : ℝ) := by
            dsimp [Cc]
            exact_mod_cast (card_cardSubsets (X := X \ U) (w := v)).symm
        rw [hcv]

end Submission.Sun
