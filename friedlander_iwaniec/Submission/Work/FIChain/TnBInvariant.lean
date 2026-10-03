import Mathlib
import Submission.Work.FIChain.LamPlusBLayerDefs
import Submission.Work.FIChain.VfBFacts
import Submission.Work.FIChain.OddLayerSum_pair_recursion
import Submission.Work.FIChain.SnB_le_window
import Submission.Work.FIChain.OddLayersMajorantDefs

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.FIChain
open Finset
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section

lemma rhoB_nonneg' {B : ℝ} (hB : 1 ≤ B) : 0 ≤ rhoB B := by
  rw [rhoB]; positivity

lemma levB_nonneg' {B : ℝ} (hB : 1 ≤ B) (k : ℕ) : 0 ≤ levB B k := by
  rw [levB]; exact div_nonneg (pow_nonneg (rhoB_nonneg' hB) k) (by linarith)

lemma levB_succ' {B : ℝ} (k : ℕ) : levB B (k + 1) = rhoB B * levB B k := by
  rw [levB, levB, pow_succ]; ring

lemma one_le_rpow_of_one_le {x a : ℝ} (hx : 1 ≤ x) (ha : 0 ≤ a) : 1 ≤ x ^ a := by
  have h := Real.rpow_le_rpow (by norm_num : (0:ℝ) ≤ 1) hx ha
  simpa using h

lemma rpow_mul_inv_self {p B : ℝ} (hp : 0 ≤ p) (hB1 : 0 < B + 1) :
    (p ^ (B + 1)) ^ (1 / (B + 1)) = p := by
  rw [← Real.rpow_mul hp (B + 1) (1 / (B + 1))]
  have h : (B + 1) * (1 / (B + 1)) = 1 := by field_simp
  rw [h, Real.rpow_one]

lemma le_rpow_inv {B D : ℝ} (hD : 0 < D) (hB1 : 0 < B + 1) {q : ℕ}
    (hcond : (q:ℝ) ^ (B + 1) ≤ D) : (q:ℝ) ≤ D ^ (1 / (B + 1)) := by
  have h := Real.rpow_le_rpow (by positivity : (0:ℝ) ≤ (q:ℝ) ^ (B + 1)) hcond
    (by positivity : (0:ℝ) ≤ 1 / (B + 1))
  rwa [rpow_mul_inv_self (by positivity : (0:ℝ) ≤ (q:ℝ)) hB1] at h

lemma budget_child {B D : ℝ} (hD : 0 < D) (hB1 : 0 < B + 1) {q0 q1 : ℕ}
    (hq1 : 1 ≤ q1) (hcond : (q0:ℝ) ^ (B + 1) ≤ D) (hlt : q1 < q0) :
    D ^ rhoB B ≤ (D / (q0:ℝ)) / (q1:ℝ) := by
  have hq0 : 1 ≤ q0 := by omega
  have hq0pos : (0:ℝ) < (q0:ℝ) := by exact_mod_cast hq0
  have hq1pos : (0:ℝ) < (q1:ℝ) := by exact_mod_cast hq1
  have hthr : (q0:ℝ) ≤ D ^ (1 / (B + 1)) := le_rpow_inv hD hB1 hcond
  have hthr' : (0:ℝ) ≤ D ^ (1 / (B + 1)) := by positivity
  have hsq : (q0:ℝ) ^ 2 ≤ D ^ (2 / (B + 1)) := by
    have h2 : (D ^ (1 / (B + 1))) * (D ^ (1 / (B + 1))) = D ^ (2 / (B + 1)) := by
      rw [← Real.rpow_add hD, show (1 / (B + 1)) + (1 / (B + 1)) = 2 / (B + 1) by ring]
    calc (q0:ℝ) ^ 2 = (q0:ℝ) * (q0:ℝ) := by ring
      _ ≤ (D ^ (1 / (B + 1))) * (D ^ (1 / (B + 1))) :=
          mul_le_mul hthr hthr (by positivity) (by positivity)
      _ = D ^ (2 / (B + 1)) := h2
  have hq1le : (q1:ℝ) ≤ (q0:ℝ) := by exact_mod_cast le_of_lt hlt
  have hprod : (q0:ℝ) * (q1:ℝ) ≤ D ^ (2 / (B + 1)) := by
    calc (q0:ℝ) * (q1:ℝ) ≤ (q0:ℝ) * (q0:ℝ) := by nlinarith
      _ = (q0:ℝ) ^ 2 := by ring
      _ ≤ D ^ (2 / (B + 1)) := hsq
  have hprodpos : 0 < (q0:ℝ) * (q1:ℝ) := mul_pos hq0pos hq1pos
  have hinv : (1:ℝ) / D ^ (2 / (B + 1)) ≤ 1 / ((q0:ℝ) * (q1:ℝ)) :=
    one_div_le_one_div_of_le hprodpos hprod
  have h1 : D * (1 / D ^ (2 / (B + 1))) ≤ D * (1 / ((q0:ℝ) * (q1:ℝ))) :=
    mul_le_mul_of_nonneg_left hinv (le_of_lt hD)
  rw [mul_one_div, mul_one_div] at h1
  have h2 : D / D ^ (2 / (B + 1)) = D ^ rhoB B := by
    have h4 : D ^ rhoB B = D ^ (1 - 2 / (B + 1)) := by
      congr 1
      rw [rhoB]
      field_simp
      ring
    rw [h4, Real.rpow_sub hD, Real.rpow_one]
  have h3 : (D / (q0:ℝ)) / (q1:ℝ) = D / ((q0:ℝ) * (q1:ℝ)) := div_div _ _ _
  rw [← h2, h3]
  exact h1

lemma child_threshold {B D : ℝ} (hB : 1 ≤ B) (hD : 1 ≤ D) (hB1 : 0 < B + 1) {q0 q1 : ℕ}
    (hq1 : 1 ≤ q1) (hcond : (q0:ℝ) ^ (B + 1) ≤ D) (hlt : q1 < q0) (k : ℕ) :
    D ^ levB B (k+1) ≤ ((D / (q0:ℝ)) / (q1:ℝ)) ^ levB B k := by
  have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hstep := budget_child hDpos hB1 hq1 hcond hlt
  have ha : D ^ levB B (k+1) = (D ^ rhoB B) ^ levB B k := by
    rw [levB_succ' k, Real.rpow_mul (le_of_lt hDpos) (rhoB B) (levB B k)]
  rw [ha]
  exact Real.rpow_le_rpow (by positivity) hstep (levB_nonneg' hB k)

lemma stair_le_filter (S : Finset ℕ) (w : ℕ → ℝ) (hw : ∀ p ∈ S, 0 ≤ w p) (k : ℕ) (q0 : ℕ) :
    (∑ q1 ∈ S.filter (fun q1 : ℕ => q1 < q0),
        w q1 * (∑ q' ∈ S.filter (fun q' : ℕ => q' < q1), w q') ^ k)
      ≤ (∑ q1 ∈ S.filter (fun q1 : ℕ => q1 < q0), w q1) ^ (k+1) / ((k:ℝ)+1) := by
  have hw' : ∀ p ∈ S.filter (fun q1 : ℕ => q1 < q0), 0 ≤ w p :=
    fun p hp => hw p (Finset.mem_filter.mp hp).1
  have h := prefix_pow_le_local (S.filter (fun q1 : ℕ => q1 < q0)) w hw' k
  refine le_trans (le_of_eq ?_) h
  refine Finset.sum_congr rfl (fun q1 hq1 => ?_)
  have hlt : q1 < q0 := (Finset.mem_filter.mp hq1).2
  have hset : (S.filter (fun q1 : ℕ => q1 < q0)).filter (fun q' : ℕ => q' < q1)
      = S.filter (fun q' : ℕ => q' < q1) := by
    ext q'
    rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_filter]
    constructor
    · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨h1, lt_trans h2 hlt⟩, h2⟩
  rw [hset]

theorem TnB_odd_le_invariant (B : ℝ) (hB : 1 ≤ B) (ν : ℕ → ℝ)
    (hν0 : ∀ p : ℕ, p.Prime → 0 ≤ ν p) (hν1 : ∀ p : ℕ, p.Prime → ν p ≤ 1 / 2) :
    ∀ k : ℕ, ∀ D y : ℝ, 1 ≤ D →
      (TnB B ν (2 * k + 1) D y
        ≤ VfB ν (D ^ levB B k)
          * (∑ q ∈ (Nat.primesBelow ⌈y⌉₊).filter (fun q : ℕ => D ^ levB B k ≤ (q : ℝ)), ν q)
              ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ))
      ∧ ((y:ℝ) ≤ D ^ levB B k → TnB B ν (2 * k + 1) D y = 0) := by
  intro k
  induction k with
  | zero =>
      intro D y hD
      have hB1 : (0:ℝ) < B + 1 := by linarith
      have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD
      have hγval : levB B 0 = 1 / (B + 1) := by rw [levB]; simp
      set γ : ℝ := D ^ levB B 0 with hγdef
      have hT1 : TnB B ν 1 D y
          = ∑ p ∈ (Nat.primesBelow ⌈y⌉₊).filter (fun p => TcondB B 1 D p),
              ν p * VfB ν (p:ℝ) := by
        rw [show (1:ℕ) = 0 + 1 from rfl, TnB]
        simp [TnB]
      constructor
      · have hge : ∀ p : ℕ, p.Prime → D < (p:ℝ)^(B+1) → γ ≤ (p:ℝ) := by
          intro p hp hlt
          rw [hγdef, hγval]
          have h1 : D ^ (1/(B+1)) < ((p:ℝ)^(B+1)) ^ (1/(B+1)) :=
            Real.rpow_lt_rpow (le_of_lt hDpos) hlt (by positivity)
          have h2 : ((p:ℝ)^(B+1)) ^ (1/(B+1)) = (p:ℝ) :=
            rpow_mul_inv_self (by positivity) hB1
          linarith
        rw [hT1]
        have hm : ∑ p ∈ (Nat.primesBelow ⌈y⌉₊).filter (fun p => TcondB B 1 D p), ν p * VfB ν (p:ℝ)
            ≤ VfB ν γ * (∑ q ∈ (Nat.primesBelow ⌈y⌉₊).filter (fun q : ℕ => γ ≤ (q:ℝ)), ν q) := by
          calc ∑ p ∈ (Nat.primesBelow ⌈y⌉₊).filter (fun p => TcondB B 1 D p), ν p * VfB ν (p:ℝ)
              ≤ ∑ p ∈ (Nat.primesBelow ⌈y⌉₊).filter (fun p => TcondB B 1 D p), ν p * VfB ν γ := by
                refine Finset.sum_le_sum (fun p hp => ?_)
                rw [Finset.mem_filter] at hp
                obtain ⟨hpb, hpc⟩ := hp
                have hp' : p.Prime := (Nat.mem_primesBelow.mp hpb).2
                have hlt : D < (p:ℝ)^(B+1) := (TcondB_one B D p).mp hpc
                exact mul_le_mul_of_nonneg_left (VfB_antitone hν0 hν1 (hge p hp' hlt)) (hν0 p hp')
            _ = VfB ν γ * ∑ p ∈ (Nat.primesBelow ⌈y⌉₊).filter (fun p => TcondB B 1 D p), ν p := by
                rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun p _ => by ring)
            _ ≤ VfB ν γ * ∑ q ∈ (Nat.primesBelow ⌈y⌉₊).filter (fun q : ℕ => γ ≤ (q:ℝ)), ν q := by
                refine mul_le_mul_of_nonneg_left ?_ (le_of_lt (VfB_pos hν1 _))
                refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
                · intro p hp
                  rw [Finset.mem_filter] at hp ⊢
                  obtain ⟨hpb, hpc⟩ := hp
                  have hp' : p.Prime := (Nat.mem_primesBelow.mp hpb).2
                  exact ⟨hpb, hge p hp' ((TcondB_one B D p).mp hpc)⟩
                · intro q hq _
                  exact hν0 q (Nat.mem_primesBelow.mp (Finset.mem_filter.mp hq).1).2
        simpa using hm
      · intro hy
        rw [hT1]
        refine Finset.sum_eq_zero (fun p hp => ?_)
        rw [Finset.mem_filter] at hp
        obtain ⟨hpb, hpc⟩ := hp
        have hlt : D < (p:ℝ)^(B+1) := (TcondB_one B D p).mp hpc
        have hpy : (p:ℝ) < y := Nat.lt_ceil.mp (Nat.mem_primesBelow.mp hpb).1
        have hγpos : (0:ℝ) < D ^ levB B 0 := by rw [hγval]; positivity
        have hpy' : (p:ℝ) < D ^ (1/(B+1)) := by
          have h2 : (p:ℝ) < γ := lt_of_lt_of_le hpy hy
          rw [hγdef, hγval] at h2
          exact h2
        have hle : (p:ℝ)^(B+1) ≤ D := by
          have h2 : (p:ℝ)^(B+1) < (D ^ (1/(B+1)))^(B+1) :=
            Real.rpow_lt_rpow (by positivity) hpy' hB1
          rw [← Real.rpow_mul (le_of_lt hDpos) (1/(B+1)) (B+1),
            show (1/(B+1)) * (B+1) = 1 by field_simp, Real.rpow_one] at h2
          exact le_of_lt h2
        linarith
  | succ k ih =>
      intro D y hD
      have hB1 : (0:ℝ) < B + 1 := by linarith
      have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD
      set γ : ℝ := D ^ levB B (k+1) with hγdef
      set S : Finset ℕ := (Nat.primesBelow ⌈y⌉₊).filter (fun q : ℕ => γ ≤ (q:ℝ)) with hSdef
      set F : Finset ℕ := (Nat.primesBelow ⌈y⌉₊).filter (fun q : ℕ => (q:ℝ)^(B+1) ≤ D) with hFdef
      have hSsub : S ⊆ Nat.primesBelow ⌈y⌉₊ := Finset.filter_subset _ _
      have hFsub : F ⊆ Nat.primesBelow ⌈y⌉₊ := Finset.filter_subset _ _
      have hSν : ∀ q ∈ S, 0 ≤ ν q := fun q hq => hν0 q (Nat.mem_primesBelow.mp (hSsub hq)).2
      have hFν : ∀ q ∈ F, 0 ≤ ν q := fun q hq => hν0 q (Nat.mem_primesBelow.mp (hFsub hq)).2
      have hFcond : ∀ q ∈ F, (q:ℝ)^(B+1) ≤ D := by
        intro q hq
        have h := hq
        rw [hFdef] at h
        exact (Finset.mem_filter.mp h).2
      have hFmem : ∀ q ∈ F, q ∈ Nat.primesBelow ⌈y⌉₊ := by
        intro q hq
        have h := hq
        rw [hFdef] at h
        exact (Finset.mem_filter.mp h).1
      have hPnn : ∀ q, 0 ≤ chainPref S ν q := fun q =>
        Finset.sum_nonneg (fun q' hq' => hSν q' (Finset.mem_filter.mp hq').1)
      -- the child bound
      have hchildbound : ∀ q0 q1 : ℕ, q0 ∈ F → q1 < q0 → 1 ≤ q1 →
          TnB B ν (2*k+1) ((D/(q0:ℝ))/(q1:ℝ)) (q1:ℝ)
            ≤ VfB ν γ * (chainPref S ν q1) ^ (2*k+1) / ((2*k+1).factorial : ℝ) := by
        intro q0 q1 hq0F hq1lt hq1
        have hq0cond := hFcond q0 hq0F
        have hq0ceil : q0 < ⌈y⌉₊ := Nat.mem_primesBelow.mp (hFmem q0 hq0F) |>.1
        have hD''1 : 1 ≤ (D/(q0:ℝ))/(q1:ℝ) := le_trans (one_le_rpow_of_one_le hD (rhoB_nonneg' hB))
          (budget_child hDpos hB1 hq1 hq0cond hq1lt)
        have hchild := (ih ((D/(q0:ℝ))/(q1:ℝ)) (q1:ℝ) hD''1).1
        have hγle := child_threshold hB hD hB1 hq1 hq0cond hq1lt k
        have hV : VfB ν (((D/(q0:ℝ))/(q1:ℝ)) ^ levB B k) ≤ VfB ν γ :=
          VfB_antitone hν0 hν1 hγle
        have hmass : (∑ q ∈ (Nat.primesBelow ⌈(q1:ℝ)⌉₊).filter
              (fun q : ℕ => ((D/(q0:ℝ))/(q1:ℝ)) ^ levB B k ≤ (q:ℝ)), ν q) ≤ chainPref S ν q1 := by
          rw [chainPref]
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
          · intro q hq
            rw [Finset.mem_filter] at hq
            obtain ⟨hqb, hqth⟩ := hq
            rw [Nat.mem_primesBelow, Nat.ceil_natCast] at hqb
            exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
              ⟨Nat.mem_primesBelow.mpr
                ⟨lt_of_lt_of_le hqb.1 (le_of_lt (lt_of_lt_of_le hq1lt (le_of_lt hq0ceil))), hqb.2⟩,
               le_trans hγle hqth⟩, hqb.1⟩
          · intro q hq _
            exact hSν q (Finset.mem_filter.mp hq).1
        have hMn : 0 ≤ (∑ q ∈ (Nat.primesBelow ⌈(q1:ℝ)⌉₊).filter
              (fun q : ℕ => ((D/(q0:ℝ))/(q1:ℝ)) ^ levB B k ≤ (q:ℝ)), ν q) :=
          Finset.sum_nonneg (fun q hq =>
            hν0 q (Nat.mem_primesBelow.mp (Finset.mem_filter.mp hq).1).2)
        have hstep : VfB ν (((D/(q0:ℝ))/(q1:ℝ)) ^ levB B k)
              * (∑ q ∈ (Nat.primesBelow ⌈(q1:ℝ)⌉₊).filter
                  (fun q : ℕ => ((D/(q0:ℝ))/(q1:ℝ)) ^ levB B k ≤ (q:ℝ)), ν q) ^ (2*k+1)
            ≤ VfB ν γ * (chainPref S ν q1) ^ (2*k+1) :=
          mul_le_mul hV (pow_le_pow_left₀ hMn hmass _) (pow_nonneg hMn _)
            (le_of_lt (VfB_pos hν1 γ))
        calc TnB B ν (2*k+1) ((D/(q0:ℝ))/(q1:ℝ)) (q1:ℝ)
            ≤ VfB ν (((D/(q0:ℝ))/(q1:ℝ)) ^ levB B k)
                * (∑ q ∈ (Nat.primesBelow ⌈(q1:ℝ)⌉₊).filter
                    (fun q : ℕ => ((D/(q0:ℝ))/(q1:ℝ)) ^ levB B k ≤ (q:ℝ)), ν q) ^ (2*k+1)
                / ((2*k+1).factorial : ℝ) := hchild
          _ ≤ VfB ν γ * (chainPref S ν q1) ^ (2*k+1) / ((2*k+1).factorial : ℝ) :=
              div_le_div_of_nonneg_right hstep (by positivity)
      -- the vanishing of the child
      have hchildzero : ∀ q0 q1 : ℕ, q0 ∈ F → q1 < q0 → 1 ≤ q1 → ((q1:ℝ) ≤ γ) →
          TnB B ν (2*k+1) ((D/(q0:ℝ))/(q1:ℝ)) (q1:ℝ) = 0 := by
        intro q0 q1 hq0F hq1lt hq1 hq1le
        have hq0cond := hFcond q0 hq0F
        have hD''1 : 1 ≤ (D/(q0:ℝ))/(q1:ℝ) := le_trans (one_le_rpow_of_one_le hD (rhoB_nonneg' hB))
          (budget_child hDpos hB1 hq1 hq0cond hq1lt)
        have hγle := child_threshold hB hD hB1 hq1 hq0cond hq1lt k
        exact (ih ((D/(q0:ℝ))/(q1:ℝ)) (q1:ℝ) hD''1).2 (le_trans hq1le hγle)
      have hper : ∀ q0 ∈ F,
          TnB B ν (2*k+2) (D/(q0:ℝ)) (q0:ℝ)
            ≤ VfB ν γ / ((2*k+1).factorial : ℝ)
                * (∑ q1 ∈ S.filter (fun q1 : ℕ => q1 < q0),
                    ν q1 * chainPref S ν q1 ^ (2*k+1)) := by
        intro q0 hq0F
        have hq0cond := hFcond q0 hq0F
        have hq0ceil : q0 < ⌈y⌉₊ := Nat.mem_primesBelow.mp (hFmem q0 hq0F) |>.1
        rw [TnB_eq_sum_primes_of_even B ν (D/(q0:ℝ)) (q0:ℝ) (by omega) ⟨k+1, by ring⟩]
        have hsub : S.filter (fun q1 : ℕ => q1 < q0) ⊆ Nat.primesBelow ⌈(q0:ℝ)⌉₊ := by
          intro q1 hq1
          rw [Finset.mem_filter, hSdef, Finset.mem_filter] at hq1
          obtain ⟨⟨hq1b, _⟩, hlt⟩ := hq1
          rw [Nat.mem_primesBelow, Nat.ceil_natCast]
          exact ⟨hlt, (Nat.mem_primesBelow.mp hq1b).2⟩
        have hzero : ∀ q1 ∈ Nat.primesBelow ⌈(q0:ℝ)⌉₊,
            q1 ∉ S.filter (fun q1 : ℕ => q1 < q0) →
            ν q1 * TnB B ν (2*k+2-1) ((D/(q0:ℝ))/(q1:ℝ)) (q1:ℝ) = 0 := by
          intro q1 hq1 hq1not
          rw [Nat.mem_primesBelow, Nat.ceil_natCast] at hq1
          obtain ⟨hq1lt, hq1prime⟩ := hq1
          have hq1notS : q1 ∉ S := fun hmem => hq1not (Finset.mem_filter.mpr ⟨hmem, hq1lt⟩)
          have hq1memY : q1 ∈ Nat.primesBelow ⌈y⌉₊ :=
            Nat.mem_primesBelow.mpr ⟨lt_of_lt_of_le hq1lt (le_of_lt hq0ceil), hq1prime⟩
          have hq1small : (q1:ℝ) ≤ γ := by
            by_contra hcon
            exact hq1notS (Finset.mem_filter.mpr ⟨hq1memY, le_of_lt (not_le.mp hcon)⟩)
          have hz := hchildzero q0 q1 hq0F hq1lt hq1prime.one_le hq1small
          rw [show 2*k+2-1 = 2*k+1 from by omega, hz, mul_zero]
        rw [← Finset.sum_subset hsub hzero, Finset.mul_sum]
        refine Finset.sum_le_sum (fun q1 hq1 => ?_)
        rw [Finset.mem_filter, hSdef, Finset.mem_filter] at hq1
        obtain ⟨⟨hq1b, _⟩, hq1lt⟩ := hq1
        have hq1prime : q1.Prime := (Nat.mem_primesBelow.mp hq1b).2
        calc ν q1 * TnB B ν (2*k+2-1) ((D/(q0:ℝ))/(q1:ℝ)) (q1:ℝ)
            ≤ ν q1 * (VfB ν γ * (chainPref S ν q1) ^ (2*k+1) / ((2*k+1).factorial : ℝ)) :=
              mul_le_mul_of_nonneg_left (hchildbound q0 q1 hq0F hq1lt hq1prime.one_le)
                (hν0 q1 hq1prime)
          _ = VfB ν γ / ((2*k+1).factorial : ℝ) * (ν q1 * chainPref S ν q1 ^ (2*k+1)) := by ring
      have hstep1 : TnB B ν (2*(k+1)+1) D y
          ≤ VfB ν γ / ((2*k+1).factorial : ℝ) * (∑ q0 ∈ F, layerSummand S ν k q0) := by
        rw [show 2*(k+1)+1 = 2*k+3 from by omega]
        rw [TnB_eq_sum_primes_of_odd B ν D y (by omega) ⟨k+1, by ring⟩]
        rw [← hFdef]
        calc ∑ q0 ∈ F, ν q0 * TnB B ν (2*k+3-1) (D/(q0:ℝ)) (q0:ℝ)
            ≤ ∑ q0 ∈ F, ν q0 * (VfB ν γ / ((2*k+1).factorial : ℝ)
                * (∑ q1 ∈ S.filter (fun q1 : ℕ => q1 < q0),
                    ν q1 * chainPref S ν q1 ^ (2*k+1))) := by
              refine Finset.sum_le_sum (fun q0 hq0 => mul_le_mul_of_nonneg_left (hper q0 hq0) (hFν q0 hq0))
          _ = VfB ν γ / ((2*k+1).factorial : ℝ) * (∑ q0 ∈ F, layerSummand S ν k q0) := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl (fun q0 _ => ?_)
              simp only [layerSummand]
              ring
      have hFS : (∑ q0 ∈ F, layerSummand S ν k q0) ≤ ∑ q0 ∈ S, layerSummand S ν k q0 := by
        have hzero : ∀ q0 ∈ F, q0 ∉ S → layerSummand S ν k q0 = 0 := by
          intro q0 hq0F hq0notS
          have hq0notS' : ¬ (γ ≤ (q0:ℝ)) := fun hcon =>
            hq0notS (Finset.mem_filter.mpr ⟨hFmem q0 hq0F, hcon⟩)
          have hq0small : (q0:ℝ) < γ := not_le.mp hq0notS'
          have hempty : S.filter (fun q1 : ℕ => q1 < q0) = ∅ := by
            refine Finset.eq_empty_iff_forall_notMem.mpr (fun q1 hq1 => ?_)
            rw [Finset.mem_filter, hSdef, Finset.mem_filter] at hq1
            obtain ⟨⟨_, hγq1⟩, hlt⟩ := hq1
            have : (q1:ℝ) < (q0:ℝ) := by exact_mod_cast hlt
            linarith
          simp only [layerSummand, hempty, Finset.sum_empty, mul_zero]
        have h1 : (∑ q0 ∈ F.filter (fun q0 => q0 ∈ S), layerSummand S ν k q0)
            = ∑ q0 ∈ F, layerSummand S ν k q0 := by
          refine Finset.sum_subset (Finset.filter_subset _ _) ?_
          intro x hx hxnot
          exact hzero x hx (fun hmem => hxnot (Finset.mem_filter.mpr ⟨hx, hmem⟩))
        have h2 : (∑ q0 ∈ F.filter (fun q0 => q0 ∈ S), layerSummand S ν k q0)
            ≤ ∑ q0 ∈ S, layerSummand S ν k q0 := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
          · intro x hx; exact (Finset.mem_filter.mp hx).2
          · intro x hx _
            rw [layerSummand]
            refine mul_nonneg (hSν x hx) (Finset.sum_nonneg (fun y hy => ?_))
            exact mul_nonneg (hSν y (Finset.mem_filter.mp hy).1) (pow_nonneg (hPnn y) _)
        rw [← h1]
        exact h2
      have hmid : (∑ q0 ∈ S, layerSummand S ν k q0)
          ≤ ∑ q0 ∈ S, ν q0 * (chainPref S ν q0 ^ (2*k+2) / (((2*k+2 : ℕ) : ℝ))) := by
        refine Finset.sum_le_sum (fun q0 hq0 => ?_)
        simp only [layerSummand, chainPref]
        refine mul_le_mul_of_nonneg_left ?_ (hSν q0 hq0)
        have h := stair_le_filter S ν hSν (2*k+1) q0
        have e2 : (((2*k+1 : ℕ) : ℝ) + 1) = (((2*k+2 : ℕ)) : ℝ) := by push_cast; ring
        rw [e2] at h
        exact h
      have hstair2 : (∑ q0 ∈ S, ν q0 * chainPref S ν q0 ^ (2*k+2))
          ≤ (∑ q0 ∈ S, ν q0) ^ (2*k+3) / (((2*k+3 : ℕ) : ℝ)) := by
        have h := prefix_pow_le_local S ν hSν (2*k+2)
        have e2 : (((2*k+2 : ℕ) : ℝ) + 1) = (((2*k+3 : ℕ)) : ℝ) := by push_cast; ring
        rw [e2] at h
        exact h
      have hWnn : 0 ≤ ∑ q0 ∈ S, ν q0 := Finset.sum_nonneg hSν
      have hfact : (((2*k+1).factorial : ℝ) * (((2*k+2 : ℕ)) : ℝ) * (((2*k+3 : ℕ)) : ℝ))
          = ((2*k+3).factorial : ℝ) := by
        have h1 : (2*k+3).factorial = (2*k+3) * (2*k+2).factorial := Nat.factorial_succ (2*k+2)
        have h2 : (2*k+2).factorial = (2*k+2) * (2*k+1).factorial := Nat.factorial_succ (2*k+1)
        rw [h1, h2]; push_cast; ring
      have hfinal : TnB B ν (2*(k+1)+1) D y
          ≤ VfB ν γ * (∑ q0 ∈ S, ν q0) ^ (2*k+3) / ((2*k+3).factorial : ℝ) := by
        have hVS : 0 ≤ VfB ν γ / ((2*k+1).factorial : ℝ) :=
          div_nonneg (le_of_lt (VfB_pos hν1 γ)) (by positivity)
        have hcast : 0 ≤ VfB ν γ / ((2*k+1).factorial : ℝ) / (((2*k+2 : ℕ) : ℝ)) :=
          div_nonneg hVS (by positivity)
        calc TnB B ν (2*(k+1)+1) D y
            ≤ VfB ν γ / ((2*k+1).factorial : ℝ) * (∑ q0 ∈ F, layerSummand S ν k q0) := hstep1
          _ ≤ VfB ν γ / ((2*k+1).factorial : ℝ) * (∑ q0 ∈ S, layerSummand S ν k q0) :=
              mul_le_mul_of_nonneg_left hFS hVS
          _ ≤ VfB ν γ / ((2*k+1).factorial : ℝ)
                * (∑ q0 ∈ S, ν q0 * (chainPref S ν q0 ^ (2*k+2) / (((2*k+2 : ℕ) : ℝ)))) :=
              mul_le_mul_of_nonneg_left hmid hVS
          _ = VfB ν γ / ((2*k+1).factorial : ℝ) / (((2*k+2 : ℕ) : ℝ))
                * (∑ q0 ∈ S, ν q0 * chainPref S ν q0 ^ (2*k+2)) := by
              rw [Finset.mul_sum, Finset.mul_sum]
              refine Finset.sum_congr rfl (fun q0 _ => ?_)
              field_simp
          _ ≤ VfB ν γ / ((2*k+1).factorial : ℝ) / (((2*k+2 : ℕ) : ℝ))
                * ((∑ q0 ∈ S, ν q0) ^ (2*k+3) / (((2*k+3 : ℕ) : ℝ))) :=
              mul_le_mul_of_nonneg_left hstair2 hcast
          _ = VfB ν γ * (∑ q0 ∈ S, ν q0) ^ (2*k+3) / ((2*k+3).factorial : ℝ) := by
              rw [← hfact]
              field_simp
      constructor
      · have hgoal : TnB B ν (2*k+3) D y ≤ VfB ν γ * (∑ q0 ∈ S, ν q0) ^ (2*k+3)
            / ((2*k+3).factorial : ℝ) := hfinal
        rwa [show 2*(k+1)+1 = 2*k+3 from by omega]
      · intro hy
        have hgoal : TnB B ν (2*k+3) D y = 0 := by
          rw [TnB_eq_sum_primes_of_odd B ν D y (by omega) ⟨k+1, by ring⟩]
          rw [← hFdef]
          refine Finset.sum_eq_zero (fun q0 hq0 => ?_)
          have hq0cond := hFcond q0 hq0
          have hq0lt : (q0:ℝ) < y :=
            Nat.lt_ceil.mp (Nat.mem_primesBelow.mp (hFmem q0 hq0)).1
          rw [show 2*k+3-1 = 2*k+2 from by omega]
          rw [TnB_eq_sum_primes_of_even B ν (D/(q0:ℝ)) (q0:ℝ) (by omega) ⟨k+1, by ring⟩]
          have hq0small : (q0:ℝ) < γ := by
            have h2 : y ≤ γ := by rw [hγdef]; exact hy
            linarith
          rw [show 2*k+2-1 = 2*k+1 from by omega]
          have hzero : (∑ q1 ∈ Nat.primesBelow ⌈(q0:ℝ)⌉₊,
                ν q1 * TnB B ν (2*k+1) ((D/(q0:ℝ))/(q1:ℝ)) (q1:ℝ)) = 0 := by
            refine Finset.sum_eq_zero (fun q1 hq1 => ?_)
            rw [Nat.mem_primesBelow, Nat.ceil_natCast] at hq1
            obtain ⟨hq1lt, hq1prime⟩ := hq1
            have hq1small : (q1:ℝ) ≤ γ := by
              have h1 : (q1:ℝ) < (q0:ℝ) := by exact_mod_cast hq1lt
              linarith
            have hz := hchildzero q0 q1 hq0 hq1lt hq1prime.one_le hq1small
            rw [hz, mul_zero]
          rw [hzero, mul_zero]
        rwa [show 2*(k+1)+1 = 2*k+3 from by omega]

end
end Work.FIChain
