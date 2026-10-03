import Mathlib
import Submission.Commons.Analysis.Series.harmonic_sum_le_rpow
import Submission.Work.A3.Weil.geomBound_le_layerCake
import Submission.Work.A3.Weil.card_intDist_le_linear

/-!
# The one-dimensional arithmetic estimate for the Weyl sum

This is the elementary arithmetic input to the `k`-fold Weyl differencing for `Work.A3.weyl_poly`:
for a real `Λ` lying within `1/(q·Q)` of a reduced fraction `a/q` (with `1 ≤ q ≤ Q`), the sum of
the geometric (first-derivative-test) quantities `geomBound N (Λ·P)` over `1 ≤ |P| ≤ M` is at most
`C_ε N^ε (M + q + M N / q)`.

The proof splits the sum at each level `k ∈ [1,N]`:
* the layer-cake bound `geomBound_le_layerCake` turns `geomBound N (ΛP)` into twice the number of
  `k ≤ N` with `intDist (ΛP) ≤ 1/(2k)`;
* `card_intDist_le_linear` counts, for each `k`, how many `|P| ≤ M` can satisfy that inequality:
  the multiples of `q` contribute `2M/q`, and each of the at most `2⌊q/k⌋` admissible residue
  classes modulo `q` contributes at most `2M/q + 1` further points;
* the harmonic sum `∑_{k≤N} ⌊q/k⌋ ≤ C_ε q N^ε` closes the estimate.
-/

namespace Work.A3.Weil

open Finset
open scoped BigOperators

noncomputable section

private lemma final_arith {C1 M Q A Ne P : ℝ} (hC1 : 0 < C1) (hM : 1 ≤ M)
    (hP1 : 1 ≤ P) (hP2 : M ≤ P) (hP3 : Q ≤ P) (hP4 : A ≤ P)
    (hP5 : M * Ne ≤ P) (hP6 : Q * Ne ≤ P) :
    4 * M + 2 + 4 * A + 8 * C1 * (M * Ne) + 4 * C1 * (Q * Ne) ≤ (12 * C1 + 10) * P := by
  have hPpos : 0 < P := lt_of_lt_of_le one_pos hP1
  have h1 : (4:ℝ) * M ≤ 4 * P := by linarith
  have h2 : (2:ℝ) ≤ 2 * P := by linarith
  have h3 : (4:ℝ) * A ≤ 4 * P := by linarith
  have h4 : 8 * C1 * (M * Ne) ≤ 8 * C1 * P := by nlinarith [hP5, hC1]
  have h5 : 4 * C1 * (Q * Ne) ≤ 4 * C1 * P := by nlinarith [hP6, hC1]
  have h6 : 8 * C1 * P ≤ 12 * C1 * P := by nlinarith [hC1, hPpos]
  linarith

set_option maxHeartbeats 2000000 in
theorem oneD_arith {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N M Q : ℕ) (Λ : ℝ) (a q : ℤ),
      1 ≤ N → 1 ≤ M → 1 ≤ Q → 2 * M ≤ Q → 1 ≤ q → q ≤ Q → IsCoprime a q →
      |Λ - (a : ℝ) / (q : ℝ)| ≤ 1 / ((q : ℝ) * (Q : ℝ)) →
      (∑ P ∈ (Finset.Icc (-(M : ℤ)) (M : ℤ)), if P = 0 then 0 else Work.A3.Weil.geomBound N (Λ * (P : ℝ)))
        ≤ C * (N : ℝ) ^ ε * ((M : ℝ) + (q : ℝ) + (M : ℝ) * (N : ℝ) / (q : ℝ)) := by
  classical
  obtain ⟨C1, hC1pos, hC1⟩ := Commons.Analysis.Series.harmonic_sum_le_rpow hε
  refine ⟨12 * C1 + 10, by positivity, ?_⟩
  intro N M Q Λ a q hN hM hQ1 h2M hq1 hqQ hcop hΛ
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := le_trans zero_le_one hNR
  have hMr : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hM0 : (0 : ℝ) ≤ (M : ℝ) := le_trans zero_le_one hMr
  have hqR : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
  have hqpos : (0 : ℝ) < (q : ℝ) := lt_of_lt_of_le one_pos hqR
  have hqne : (q : ℝ) ≠ 0 := ne_of_gt hqpos
  have hNe : (1 : ℝ) ≤ (N : ℝ) ^ ε := Real.one_le_rpow hNR (le_of_lt hε)
  have hNepos : (0 : ℝ) < (N : ℝ) ^ ε := lt_of_lt_of_le one_pos hNe
  set S : Finset ℤ := (Finset.Icc (-(M : ℤ)) (M : ℤ)).filter (fun P : ℤ => P ≠ 0) with hS
  -- (0) reindex the target sum over `S`
  have hLHS : (∑ P ∈ (Finset.Icc (-(M : ℤ)) (M : ℤ)),
        if P = 0 then 0 else Work.A3.Weil.geomBound N (Λ * (P : ℝ)))
      = ∑ P ∈ S, Work.A3.Weil.geomBound N (Λ * (P : ℝ)) := by
    rw [hS, Finset.sum_filter]
    exact Finset.sum_congr rfl (fun P _ => by by_cases hp : P = 0 <;> simp [hp])
  -- (1) layer cake, termwise
  have hstep1 : (∑ P ∈ S, Work.A3.Weil.geomBound N (Λ * (P : ℝ)))
      ≤ ∑ P ∈ S, (2 + 2 * (((Finset.Icc 1 N).filter (fun k : ℕ =>
          Submission.VanDerCorput.intDist (Λ * (P : ℝ)) ≤ 1 / (2 * (k : ℝ)))).card : ℝ)) :=
    Finset.sum_le_sum (fun P _ => geomBound_le_layerCake hN _)
  -- (2) split the constant term off
  have hstep2 : (∑ P ∈ S, (2 + 2 * (((Finset.Icc 1 N).filter (fun k : ℕ =>
          Submission.VanDerCorput.intDist (Λ * (P : ℝ)) ≤ 1 / (2 * (k : ℝ)))).card : ℝ)))
      = 2 * (S.card : ℝ) + 2 * (∑ P ∈ S, (((Finset.Icc 1 N).filter (fun k : ℕ =>
          Submission.VanDerCorput.intDist (Λ * (P : ℝ)) ≤ 1 / (2 * (k : ℝ)))).card : ℝ)) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, ← Finset.mul_sum, nsmul_eq_mul]
    ring
  -- (3) swap the two sums
  have hstep3 : (∑ P ∈ S, (((Finset.Icc 1 N).filter (fun k : ℕ =>
          Submission.VanDerCorput.intDist (Λ * (P : ℝ)) ≤ 1 / (2 * (k : ℝ)))).card : ℝ))
      = ∑ k ∈ Finset.Icc 1 N, ((S.filter (fun P : ℤ =>
          Submission.VanDerCorput.intDist (Λ * (P : ℝ)) ≤ 1 / (2 * (k : ℝ)))).card : ℝ) := by
    have hL : (∑ P ∈ S, (((Finset.Icc 1 N).filter (fun k : ℕ =>
            Submission.VanDerCorput.intDist (Λ * (P : ℝ)) ≤ 1 / (2 * (k : ℝ)))).card : ℝ))
        = ∑ P ∈ S, ∑ k ∈ Finset.Icc 1 N,
            (if Submission.VanDerCorput.intDist (Λ * (P : ℝ)) ≤ 1 / (2 * (k : ℝ))
              then (1 : ℝ) else 0) := by
      refine Finset.sum_congr rfl (fun P _ => ?_)
      rw [Finset.card_filter]
      push_cast
      rfl
    have hR : (∑ k ∈ Finset.Icc 1 N, ((S.filter (fun P : ℤ =>
            Submission.VanDerCorput.intDist (Λ * (P : ℝ)) ≤ 1 / (2 * (k : ℝ)))).card : ℝ))
        = ∑ k ∈ Finset.Icc 1 N, ∑ P ∈ S,
            (if Submission.VanDerCorput.intDist (Λ * (P : ℝ)) ≤ 1 / (2 * (k : ℝ))
              then (1 : ℝ) else 0) := by
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [Finset.card_filter]
      push_cast
      rfl
    rw [hL, hR, Finset.sum_comm]
  -- (4) per-`k` counting bound
  have hstep4 : ∀ k ∈ Finset.Icc 1 N, ((S.filter (fun P : ℤ =>
        Submission.VanDerCorput.intDist (Λ * (P : ℝ)) ≤ 1 / (2 * (k : ℝ)))).card : ℝ)
      ≤ 2 * ((M : ℝ) / (q : ℝ)) + 2 * (⌊(q : ℝ) / (k : ℝ)⌋₊ : ℝ) * (2 * ((M : ℝ) / (q : ℝ)) + 1) := by
    intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    have hchild := card_intDist_le_linear (M := M) (Q := Q) (k := k) (Λ := Λ) (a := a) (q := q)
      hM hq1 h2M hk1 hcop hΛ
    have hgoal : ((S.filter (fun P : ℤ =>
          Submission.VanDerCorput.intDist (Λ * (P : ℝ)) ≤ 1 / (2 * (k : ℝ)))).card : ℝ)
        = (((Finset.Icc (-(M : ℤ)) (M : ℤ)).filter (fun P : ℤ =>
          P ≠ 0 ∧ Submission.VanDerCorput.intDist (Λ * (P : ℝ))
            ≤ 1 / (2 * (k : ℝ)))).card : ℝ) := by
      simp only [hS, Finset.filter_filter]
    rw [hgoal]
    exact hchild
  -- (5) sum the per-`k` bounds
  have hstep5 : (∑ k ∈ Finset.Icc 1 N, ((S.filter (fun P : ℤ =>
        Submission.VanDerCorput.intDist (Λ * (P : ℝ)) ≤ 1 / (2 * (k : ℝ)))).card : ℝ))
      ≤ ∑ k ∈ Finset.Icc 1 N,
          (2 * ((M : ℝ) / (q : ℝ))
            + 2 * (⌊(q : ℝ) / (k : ℝ)⌋₊ : ℝ) * (2 * ((M : ℝ) / (q : ℝ)) + 1)) :=
    Finset.sum_le_sum hstep4
  -- (6) evaluate the resulting sum
  have hstep6 : (∑ k ∈ Finset.Icc 1 N, (2 * ((M : ℝ) / (q : ℝ))
          + 2 * (⌊(q : ℝ) / (k : ℝ)⌋₊ : ℝ) * (2 * ((M : ℝ) / (q : ℝ)) + 1)))
      = (N : ℝ) * (2 * ((M : ℝ) / (q : ℝ)))
        + 2 * (2 * ((M : ℝ) / (q : ℝ)) + 1) * (∑ k ∈ Finset.Icc 1 N,
            (⌊(q : ℝ) / (k : ℝ)⌋₊ : ℝ)) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, ← Finset.sum_mul, ← Finset.mul_sum,
      Nat.card_Icc, nsmul_eq_mul]
    simp only [Nat.add_sub_cancel]
    ring
  -- (7) harmonic bound on the floors
  have hfloor : (∑ k ∈ Finset.Icc 1 N, (⌊(q : ℝ) / (k : ℝ)⌋₊ : ℝ))
      ≤ C1 * (q : ℝ) * (N : ℝ) ^ ε := by
    have hpt : ∀ k ∈ Finset.Icc 1 N, (⌊(q : ℝ) / (k : ℝ)⌋₊ : ℝ) ≤ (q : ℝ) / (k : ℝ) := by
      intro k hk
      have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
      have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
      exact Nat.floor_le (by positivity)
    calc (∑ k ∈ Finset.Icc 1 N, (⌊(q : ℝ) / (k : ℝ)⌋₊ : ℝ))
        ≤ ∑ k ∈ Finset.Icc 1 N, (q : ℝ) / (k : ℝ) := Finset.sum_le_sum hpt
      _ = (q : ℝ) * (∑ k ∈ Finset.Icc 1 N, (1 : ℝ) / (k : ℝ)) := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl (fun k _ => by rw [mul_one_div])
      _ ≤ (q : ℝ) * (C1 * (N : ℝ) ^ ε) :=
            mul_le_mul_of_nonneg_left (hC1 N hN) (le_of_lt hqpos)
      _ = C1 * (q : ℝ) * (N : ℝ) ^ ε := by ring
  -- (8) assemble the bound on the inner sum over `k`
  have hsumU : (∑ k ∈ Finset.Icc 1 N, ((S.filter (fun P : ℤ =>
        Submission.VanDerCorput.intDist (Λ * (P : ℝ)) ≤ 1 / (2 * (k : ℝ)))).card : ℝ))
      ≤ 2 * (N : ℝ) * ((M : ℝ) / (q : ℝ))
        + 2 * (2 * ((M : ℝ) / (q : ℝ)) + 1) * (C1 * (q : ℝ) * (N : ℝ) ^ ε) := by
    refine le_trans hstep5 ?_
    rw [hstep6]
    have h1 : (N : ℝ) * (2 * ((M : ℝ) / (q : ℝ))) = 2 * (N : ℝ) * ((M : ℝ) / (q : ℝ)) := by ring
    rw [h1]
    refine add_le_add le_rfl ?_
    have hfac : (0 : ℝ) ≤ 2 * (2 * ((M : ℝ) / (q : ℝ)) + 1) := by
      have h1 : 0 ≤ (M : ℝ) / (q : ℝ) := div_nonneg hM0 (le_of_lt hqpos)
      linarith
    exact mul_le_mul_of_nonneg_left hfloor hfac
  -- (9) the cardinality of `S`
  have hcard : (S.card : ℝ) ≤ 2 * (M : ℝ) + 1 := by
    have hsub : S ⊆ Finset.Icc (-(M : ℤ)) (M : ℤ) := by
      intro Q' hQ'
      rw [hS] at hQ'
      exact (Finset.mem_filter.mp hQ').1
    have h1 : S.card ≤ (Finset.Icc (-(M : ℤ)) (M : ℤ)).card := Finset.card_le_card hsub
    have h2 : (Finset.Icc (-(M : ℤ)) (M : ℤ)).card = 2 * M + 1 := by
      rw [Int.card_Icc]
      have h3 : (((M : ℤ) + 1 - (-(M : ℤ))).toNat) = 2 * M + 1 := by
        have h4 : (M : ℤ) + 1 - (-(M : ℤ)) = ((2 * M + 1 : ℕ) : ℤ) := by push_cast; ring
        rw [h4, Int.toNat_natCast]
      rw [h3]
    rw [h2] at h1
    exact_mod_cast h1
  -- (10) put the pieces together
  have htotal : 2 * (S.card : ℝ) + 2 * (∑ k ∈ Finset.Icc 1 N, ((S.filter (fun P : ℤ =>
        Submission.VanDerCorput.intDist (Λ * (P : ℝ)) ≤ 1 / (2 * (k : ℝ)))).card : ℝ))
      ≤ 4 * (M : ℝ) + 2 + 4 * ((M : ℝ) * (N : ℝ) / (q : ℝ))
        + 8 * C1 * ((M : ℝ) * (N : ℝ) ^ ε) + 4 * C1 * ((q : ℝ) * (N : ℝ) ^ ε) := by
    have h2S : 2 * (S.card : ℝ) ≤ 4 * (M : ℝ) + 2 := by linarith
    have h2U : 2 * (∑ k ∈ Finset.Icc 1 N, ((S.filter (fun P : ℤ =>
          Submission.VanDerCorput.intDist (Λ * (P : ℝ)) ≤ 1 / (2 * (k : ℝ)))).card : ℝ))
        ≤ 4 * ((M : ℝ) * (N : ℝ) / (q : ℝ))
          + 8 * C1 * ((M : ℝ) * (N : ℝ) ^ ε) + 4 * C1 * ((q : ℝ) * (N : ℝ) ^ ε) := by
      have h := mul_le_mul_of_nonneg_left hsumU (by norm_num : (0 : ℝ) ≤ 2)
      have hexp : (2 : ℝ) * (2 * (N : ℝ) * ((M : ℝ) / (q : ℝ))
            + 2 * (2 * ((M : ℝ) / (q : ℝ)) + 1) * (C1 * (q : ℝ) * (N : ℝ) ^ ε))
          = 4 * ((M : ℝ) * (N : ℝ) / (q : ℝ))
            + 8 * C1 * ((M : ℝ) * (N : ℝ) ^ ε) + 4 * C1 * ((q : ℝ) * (N : ℝ) ^ ε) := by
        field_simp
        ring
      linarith [h, hexp]
    linarith [h2S, h2U]
  have hkey : (∑ P ∈ S, Work.A3.Weil.geomBound N (Λ * (P : ℝ)))
      ≤ 4 * (M : ℝ) + 2 + 4 * ((M : ℝ) * (N : ℝ) / (q : ℝ))
        + 8 * C1 * ((M : ℝ) * (N : ℝ) ^ ε) + 4 * C1 * ((q : ℝ) * (N : ℝ) ^ ε) := by
    calc (∑ P ∈ S, Work.A3.Weil.geomBound N (Λ * (P : ℝ)))
        ≤ ∑ P ∈ S, (2 + 2 * (((Finset.Icc 1 N).filter (fun k : ℕ =>
            Submission.VanDerCorput.intDist (Λ * (P : ℝ)) ≤ 1 / (2 * (k : ℝ)))).card : ℝ)) := hstep1
      _ = 2 * (S.card : ℝ) + 2 * (∑ P ∈ S, (((Finset.Icc 1 N).filter (fun k : ℕ =>
            Submission.VanDerCorput.intDist (Λ * (P : ℝ)) ≤ 1 / (2 * (k : ℝ)))).card : ℝ)) := hstep2
      _ = 2 * (S.card : ℝ) + 2 * (∑ k ∈ Finset.Icc 1 N, ((S.filter (fun P : ℤ =>
            Submission.VanDerCorput.intDist (Λ * (P : ℝ)) ≤ 1 / (2 * (k : ℝ)))).card : ℝ)) := by
          rw [hstep3]
      _ ≤ _ := htotal
  -- final arithmetic with the master quantity `P`
  have hMNq : 0 ≤ (M : ℝ) * (N : ℝ) / (q : ℝ) := div_nonneg (mul_nonneg hM0 hN0) (le_of_lt hqpos)
  set Pq : ℝ := (N : ℝ) ^ ε * ((M : ℝ) + (q : ℝ) + (M : ℝ) * (N : ℝ) / (q : ℝ)) with hPq
  have hbr1 : (M : ℝ) ≤ (M : ℝ) + (q : ℝ) + (M : ℝ) * (N : ℝ) / (q : ℝ) := by
    linarith [hMNq, hqpos.le]
  have hbr2 : (q : ℝ) ≤ (M : ℝ) + (q : ℝ) + (M : ℝ) * (N : ℝ) / (q : ℝ) := by
    linarith [hMNq, hM0]
  have hbr3 : (M : ℝ) * (N : ℝ) / (q : ℝ)
      ≤ (M : ℝ) + (q : ℝ) + (M : ℝ) * (N : ℝ) / (q : ℝ) := by
    linarith [hMNq, hM0, hqpos.le]
  have hP1 : (1 : ℝ) ≤ Pq := by
    rw [hPq]
    calc (1 : ℝ) ≤ (M : ℝ) := hMr
      _ = (1 : ℝ) * (M : ℝ) := by ring
      _ ≤ (N : ℝ) ^ ε * (M : ℝ) := mul_le_mul_of_nonneg_right hNe hM0
      _ ≤ (N : ℝ) ^ ε * ((M : ℝ) + (q : ℝ) + (M : ℝ) * (N : ℝ) / (q : ℝ)) :=
          mul_le_mul_of_nonneg_left hbr1 (le_of_lt hNepos)
  have hP2 : (M : ℝ) ≤ Pq := by
    rw [hPq]
    calc (M : ℝ) = (1 : ℝ) * (M : ℝ) := by ring
      _ ≤ (N : ℝ) ^ ε * (M : ℝ) := mul_le_mul_of_nonneg_right hNe hM0
      _ ≤ (N : ℝ) ^ ε * ((M : ℝ) + (q : ℝ) + (M : ℝ) * (N : ℝ) / (q : ℝ)) :=
          mul_le_mul_of_nonneg_left hbr1 (le_of_lt hNepos)
  have hP3 : (q : ℝ) ≤ Pq := by
    rw [hPq]
    calc (q : ℝ) = (1 : ℝ) * (q : ℝ) := by ring
      _ ≤ (N : ℝ) ^ ε * (q : ℝ) := mul_le_mul_of_nonneg_right hNe hqpos.le
      _ ≤ (N : ℝ) ^ ε * ((M : ℝ) + (q : ℝ) + (M : ℝ) * (N : ℝ) / (q : ℝ)) :=
          mul_le_mul_of_nonneg_left hbr2 (le_of_lt hNepos)
  have hP4 : (M : ℝ) * (N : ℝ) / (q : ℝ) ≤ Pq := by
    rw [hPq]
    calc (M : ℝ) * (N : ℝ) / (q : ℝ)
        = (1 : ℝ) * ((M : ℝ) * (N : ℝ) / (q : ℝ)) := by ring
      _ ≤ (N : ℝ) ^ ε * ((M : ℝ) * (N : ℝ) / (q : ℝ)) :=
          mul_le_mul_of_nonneg_right hNe hMNq
      _ ≤ (N : ℝ) ^ ε * ((M : ℝ) + (q : ℝ) + (M : ℝ) * (N : ℝ) / (q : ℝ)) :=
          mul_le_mul_of_nonneg_left hbr3 (le_of_lt hNepos)
  have hP5 : (M : ℝ) * (N : ℝ) ^ ε ≤ Pq := by
    rw [hPq]
    calc (M : ℝ) * (N : ℝ) ^ ε = (N : ℝ) ^ ε * (M : ℝ) := by ring
      _ ≤ (N : ℝ) ^ ε * ((M : ℝ) + (q : ℝ) + (M : ℝ) * (N : ℝ) / (q : ℝ)) :=
          mul_le_mul_of_nonneg_left hbr1 (le_of_lt hNepos)
  have hP6 : (q : ℝ) * (N : ℝ) ^ ε ≤ Pq := by
    rw [hPq]
    calc (q : ℝ) * (N : ℝ) ^ ε = (N : ℝ) ^ ε * (q : ℝ) := by ring
      _ ≤ (N : ℝ) ^ ε * ((M : ℝ) + (q : ℝ) + (M : ℝ) * (N : ℝ) / (q : ℝ)) :=
          mul_le_mul_of_nonneg_left hbr2 (le_of_lt hNepos)
  have hfin := final_arith (C1 := C1) (M := (M : ℝ)) (Q := (q : ℝ))
    (A := (M : ℝ) * (N : ℝ) / (q : ℝ)) (Ne := (N : ℝ) ^ ε) (P := Pq)
    hC1pos hMr hP1 hP2 hP3 hP4 hP5 hP6
  calc (∑ P ∈ (Finset.Icc (-(M : ℤ)) (M : ℤ)),
        if P = 0 then 0 else Work.A3.Weil.geomBound N (Λ * (P : ℝ)))
      = ∑ Q' ∈ S, Work.A3.Weil.geomBound N (Λ * (Q' : ℝ)) := hLHS
    _ ≤ 4 * (M : ℝ) + 2 + 4 * ((M : ℝ) * (N : ℝ) / (q : ℝ))
        + 8 * C1 * ((M : ℝ) * (N : ℝ) ^ ε) + 4 * C1 * ((q : ℝ) * (N : ℝ) ^ ε) := hkey
    _ ≤ (12 * C1 + 10) * Pq := hfin
    _ = (12 * C1 + 10) * (N : ℝ) ^ ε
        * ((M : ℝ) + (q : ℝ) + (M : ℝ) * (N : ℝ) / (q : ℝ)) := by
        rw [hPq]; ring

end

end Work.A3.Weil
