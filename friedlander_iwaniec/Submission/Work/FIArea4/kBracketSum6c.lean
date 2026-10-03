import Mathlib
import Submission.Work.FIArea4.A6R2.Defs
import Submission.Work.FIArea4.A6R2.KsetDyadicBounds
import Submission.Work.FIArea4.A6R2.BracketGeomSum
import Submission.Work.FIArea4.A6R2.absorb6
import Submission.Work.S15crux.prelude
import Submission.Work.FIArea4.S15EGDefs
import Submission.Work.FIArea4.A4varbounds
import Submission.Work.FIArea4.A6Defs
import Submission.Work.FIArea4.sum_rpow_half_le
import Submission.Work.FIArea4.S15EG_crude_piece2
import Submission.Work.FIArea4.S15EG_crude_piece3
import Submission.Work.FIArea4.S15EG_p14Last_le
import Submission.Work.FIArea4.crude_bracket_le

namespace Work.FIArea4

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

set_option maxHeartbeats 4000000

noncomputable section

private lemma p14Last_nonneg (R S : ℕ) (ε : ℝ) : 0 ≤ p14Last R S ε := by
  unfold Work.FIArea4.p14Last
  exact mul_nonneg (Real.rpow_nonneg (by positivity) _)
    (Real.rpow_nonneg (by positivity) _)

lemma kset_card_le (Pa : Work.FITop.Params) (X j e : ℕ) (hX : 1 ≤ X) (he : 1 ≤ e) :
    ((Work.S15crux.kset Pa X j e).card : ℝ)
      ≤ ((Nat.log 2 (4 * Work.FIArea4.S15Y Pa X j) + 1 : ℕ) : ℝ) := by
  have hsub : Work.S15crux.kset Pa X j e
      ⊆ Finset.range (Nat.log 2 (4 * Work.FIArea4.S15Y Pa X j) + 1) := by
    intro k hk
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le (Work.FIArea4.A6R2.KsetDyadicBounds Pa X j e hX he hk).2.2
  have h := Finset.card_le_card hsub
  rw [Finset.card_range] at h
  exact_mod_cast h

lemma bracket_sum_crude (Pa : Work.FITop.Params) (X j e : ℕ)
    (hX : 1 ≤ X) (hXN : (X : ℝ) ≤ Pa.N) (he : 1 ≤ e) :
    (∑ k ∈ Work.S15crux.kset Pa X j e,
        p14Bracket (2 ^ k) (S15EG_Re Pa e) (S15EG_Se Pa) ((1 : ℝ) / 4000))
      ≤ 16 * (S15Y Pa X j : ℝ)
        + 256 * Pa.N * (X : ℝ) ^ (-(1 : ℝ) / 2)
        + 31000 * ((S15Y Pa X j : ℝ)) ^ ((1 : ℝ) / 3) * Pa.N ^ ((2 : ℝ) / 3)
            * (Real.log Pa.N + 1) ^ (4 : ℕ)
        + 64 * ((Nat.log 2 (4 * S15Y Pa X j) + 1 : ℕ) : ℝ)
            * Pa.N ^ ((23 : ℝ) / 24 + (1 : ℝ) / 4000) := by
  classical
  set Kset := Work.S15crux.kset Pa X j e with hKset
  set Y : ℝ := (S15Y Pa X j : ℝ) with hY
  set R : ℝ := (S15EG_Re Pa e : ℝ) with hR
  set S : ℝ := (S15EG_Se Pa : ℝ) with hS
  set L : ℝ := Real.log Pa.N + 1 with hL
  have hN1 : (1 : ℝ) ≤ Pa.N := Pa.hN1
  have hN0 : (0 : ℝ) ≤ Pa.N := by linarith
  have hX0 : (0 : ℝ) ≤ (X : ℝ) := Nat.cast_nonneg X
  have hXpos : (0 : ℝ) < (X : ℝ) := by
    exact_mod_cast (show 0 < X by omega)
  have he1 : (1 : ℝ) ≤ (e : ℝ) := by exact_mod_cast he
  have he0 : (0 : ℝ) < (e : ℝ) := by linarith
  have hY1 : (1 : ℝ) ≤ Y := by
    rw [hY]; exact_mod_cast Work.FIArea4.A6R2.S15Y_ge_one Pa X j
  have hY0 : (0 : ℝ) ≤ Y := by linarith
  have hR1 : (1 : ℝ) ≤ R := by
    rw [hR]; exact_mod_cast S15EG_Re_pos Pa e
  have hS1 : (1 : ℝ) ≤ S := by
    rw [hS]; exact_mod_cast S15EG_Se_pos Pa
  have hR0 : (0 : ℝ) ≤ R := by linarith
  have hS0 : (0 : ℝ) ≤ S := by linarith
  have hRS0 : (0 : ℝ) ≤ R * S := mul_nonneg hR0 hS0
  have hL0 : (0 : ℝ) ≤ L := by
    rw [hL]; have := Real.log_nonneg hN1; linarith
  have hL4 : (0 : ℝ) ≤ L ^ (4 : ℕ) := pow_nonneg hL0 4
  by_cases hne : Kset.Nonempty
  · have hYepos : (0 : ℝ) < Y / (e : ℝ) := div_pos (by linarith) he0
    have hbmax : (2 : ℝ) ^ (Kset.max' hne) < 4 * (Y / (e : ℝ)) := by
      have h := (Work.FIArea4.A6R2.KsetDyadicBounds Pa X j e hX he
        (Finset.max'_mem Kset hne)).1
      rwa [← hY] at h
    obtain ⟨hg1, hg3⟩ :=
      Work.FIArea4.A6R2.BracketGeomSum Kset (Kset.max' hne) (Finset.max'_mem Kset hne)
        (fun k hk => Finset.le_max' Kset k hk) hYepos hbmax
    have hhalf : (∑ k ∈ Kset, ((2 : ℝ) ^ k) ^ (-(1 : ℝ) / 2))
        ≤ 4 * ((2 : ℝ) * (X : ℝ) / (e : ℝ)) ^ (-(1 : ℝ) / 2) := by
      have h1 := sum_rpow_half_le (T := Kset) (k0 := Kset.min' hne)
        (fun k hk => Finset.min'_le Kset k hk)
      refine le_trans h1 ?_
      have hb : (2 : ℝ) * (X : ℝ) / (e : ℝ) ≤ (2 : ℝ) ^ (Kset.min' hne) := by
        have h := (Work.FIArea4.A6R2.KsetDyadicBounds Pa X j e hX he
          (Finset.min'_mem Kset hne)).2.1
        have h2 : 2 * ((X : ℝ) / (e : ℝ)) = (2 : ℝ) * (X : ℝ) / (e : ℝ) := by
          rw [mul_div_assoc]
        rwa [h2] at h
      have hpos : (0 : ℝ) < (2 : ℝ) * (X : ℝ) / (e : ℝ) :=
        div_pos (by linarith [hXpos]) he0
      have hle := Real.rpow_le_rpow_of_nonpos hpos hb (by norm_num : (-(1 : ℝ) / 2) ≤ 0)
      exact mul_le_mul_of_nonneg_left hle (by norm_num)
    have heY : (e : ℝ) ≤ (S15Y Pa X j : ℝ) := by
      have hdne : (Work.S15crux.dset Pa X j e).Nonempty := by
        have h1 : (Work.S15crux.kset Pa X j e).Nonempty := hKset ▸ hne
        rw [show Work.S15crux.kset Pa X j e
            = (Work.S15crux.dset Pa X j e).image Work.S15crux.dk from rfl] at h1
        rwa [Finset.image_nonempty] at h1
      obtain ⟨d', hd'⟩ := hdne
      rw [Work.S15crux.dset, Finset.mem_filter, Finset.mem_Icc] at hd'
      obtain ⟨⟨hd1, hdle⟩, _⟩ := hd'
      have hle : e ≤ Work.FIArea4.S15Y Pa X j := by
        calc e = e * 1 := by ring
          _ ≤ e * d' := Nat.mul_le_mul_left e hd1
          _ ≤ e * (Work.FIArea4.S15Y Pa X j / e) := Nat.mul_le_mul_left e hdle
          _ ≤ Work.FIArea4.S15Y Pa X j := Nat.mul_div_le _ _
      exact_mod_cast hle
    have hp2 := S15EG_crude_piece2 Pa X j e hX hXN he heY
    rw [← hR, ← hS] at hp2
    have hp3 := S15EG_crude_piece3 Pa X j e hX he
    rw [← hY, ← hR, ← hS, ← hL] at hp3
    have hp4 := S15EG_p14Last_le Pa e
    have hcard := kset_card_le Pa X j e hX he
    rw [← hKset] at hcard
    have hfac2 : (∑ k ∈ Kset, ((2 : ℝ) ^ k) ^ (-(1 : ℝ) / 2) * R * S)
        = (∑ k ∈ Kset, ((2 : ℝ) ^ k) ^ (-(1 : ℝ) / 2)) * R * S := by
      rw [Finset.sum_mul, Finset.sum_mul]
    have hfac3 : (∑ k ∈ Kset, ((2 : ℝ) ^ k) ^ ((1 : ℝ) / 3) * ((R * S) ^ ((2 : ℝ) / 3))
          * (Real.log (2 * R * S) + 1) ^ (4 : ℕ))
        = (∑ k ∈ Kset, ((2 : ℝ) ^ k) ^ ((1 : ℝ) / 3)) * ((R * S) ^ ((2 : ℝ) / 3))
          * (Real.log (2 * R * S) + 1) ^ (4 : ℕ) := by
      rw [Finset.sum_mul, Finset.sum_mul]
    have hfac4 : (∑ k ∈ Kset, p14Last (S15EG_Re Pa e) (S15EG_Se Pa) ((1 : ℝ) / 4000))
        = (Kset.card : ℝ) * p14Last (S15EG_Re Pa e) (S15EG_Se Pa) ((1 : ℝ) / 4000) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    have hA2 : (∑ k ∈ Kset, ((2 : ℝ) ^ k) ^ (-(1 : ℝ) / 2) * R * S)
        ≤ 120 * (Pa.N * (X : ℝ) ^ (-(1 : ℝ) / 2)) := by
      rw [hfac2]
      have hstep : (∑ k ∈ Kset, ((2 : ℝ) ^ k) ^ (-(1 : ℝ) / 2)) * (R * S)
          ≤ 4 * (30 * Pa.N * (X : ℝ) ^ (-(1 : ℝ) / 2)) := by
        calc (∑ k ∈ Kset, ((2 : ℝ) ^ k) ^ (-(1 : ℝ) / 2)) * (R * S)
            ≤ (4 * ((2 : ℝ) * (X : ℝ) / (e : ℝ)) ^ (-(1 : ℝ) / 2)) * (R * S) :=
              mul_le_mul_of_nonneg_right hhalf hRS0
          _ = 4 * (((2 : ℝ) * (X : ℝ) / (e : ℝ)) ^ (-(1 : ℝ) / 2) * (R * S)) := by ring
          _ ≤ 4 * (30 * Pa.N * (X : ℝ) ^ (-(1 : ℝ) / 2)) :=
              mul_le_mul_of_nonneg_left hp2 (by norm_num)
      calc (∑ k ∈ Kset, ((2 : ℝ) ^ k) ^ (-(1 : ℝ) / 2)) * R * S
          = (∑ k ∈ Kset, ((2 : ℝ) ^ k) ^ (-(1 : ℝ) / 2)) * (R * S) := by ring
        _ ≤ 4 * (30 * Pa.N * (X : ℝ) ^ (-(1 : ℝ) / 2)) := hstep
        _ = 120 * (Pa.N * (X : ℝ) ^ (-(1 : ℝ) / 2)) := by ring
    have hA3 : (∑ k ∈ Kset, ((2 : ℝ) ^ k) ^ ((1 : ℝ) / 3) * ((R * S) ^ ((2 : ℝ) / 3))
          * (Real.log (2 * R * S) + 1) ^ (4 : ℕ))
        ≤ 30000 * Y ^ ((1 : ℝ) / 3) * Pa.N ^ ((2 : ℝ) / 3) * L ^ (4 : ℕ) := by
      rw [hfac3]
      have hnn : (0 : ℝ) ≤ ((R * S) ^ ((2 : ℝ) / 3)) * (Real.log (2 * R * S) + 1) ^ (4 : ℕ) := by
        apply mul_nonneg (Real.rpow_nonneg hRS0 _)
        apply pow_nonneg
        have h2 : (0 : ℝ) ≤ Real.log (2 * R * S) := by
          rw [show (2 : ℝ) * R * S = 2 * (R * S) by ring]
          exact Real.log_nonneg (by nlinarith [hR1, hS1])
        linarith
      have hstep : (∑ k ∈ Kset, ((2 : ℝ) ^ k) ^ ((1 : ℝ) / 3))
            * (((R * S) ^ ((2 : ℝ) / 3)) * (Real.log (2 * R * S) + 1) ^ (4 : ℕ))
          ≤ (16 * (Y / (e : ℝ)) ^ ((1 : ℝ) / 3))
            * (((R * S) ^ ((2 : ℝ) / 3)) * (Real.log (2 * R * S) + 1) ^ (4 : ℕ)) :=
        mul_le_mul_of_nonneg_right hg3 hnn
      calc (∑ k ∈ Kset, ((2 : ℝ) ^ k) ^ ((1 : ℝ) / 3)) * ((R * S) ^ ((2 : ℝ) / 3))
              * (Real.log (2 * R * S) + 1) ^ (4 : ℕ)
          = (∑ k ∈ Kset, ((2 : ℝ) ^ k) ^ ((1 : ℝ) / 3))
              * (((R * S) ^ ((2 : ℝ) / 3)) * (Real.log (2 * R * S) + 1) ^ (4 : ℕ)) := by ring
        _ ≤ (16 * (Y / (e : ℝ)) ^ ((1 : ℝ) / 3))
              * (((R * S) ^ ((2 : ℝ) / 3)) * (Real.log (2 * R * S) + 1) ^ (4 : ℕ)) := hstep
        _ = 16 * (Y / (e : ℝ)) ^ ((1 : ℝ) / 3) * ((R * S) ^ ((2 : ℝ) / 3))
              * (Real.log (2 * R * S) + 1) ^ (4 : ℕ) := by ring
        _ ≤ 30000 * Y ^ ((1 : ℝ) / 3) * Pa.N ^ ((2 : ℝ) / 3) * L ^ (4 : ℕ) := hp3
    have hA4 : (∑ k ∈ Kset, p14Last (S15EG_Re Pa e) (S15EG_Se Pa) ((1 : ℝ) / 4000))
        ≤ ((Nat.log 2 (4 * S15Y Pa X j) + 1 : ℕ) : ℝ)
            * (8 * Pa.N ^ ((23 : ℝ) / 24 + (1 : ℝ) / 4000)) := by
      rw [hfac4]
      exact mul_le_mul hcard hp4 (p14Last_nonneg _ _ _) (Nat.cast_nonneg _)
    have hA1 : (∑ k ∈ Kset, (2 : ℝ) ^ k) ≤ 16 * (Y / (e : ℝ)) := hg1
    have hcongr : ∀ k : ℕ, p14Bracket (2 ^ k) (S15EG_Re Pa e) (S15EG_Se Pa) ((1 : ℝ) / 4000)
        = (2 : ℝ) ^ k + ((2 : ℝ) ^ k) ^ (-(1 : ℝ) / 2) * R * S
          + ((2 : ℝ) ^ k) ^ ((1 : ℝ) / 3) * ((R * S) ^ ((2 : ℝ) / 3))
              * (Real.log (2 * R * S) + 1) ^ (4 : ℕ)
          + p14Last (S15EG_Re Pa e) (S15EG_Se Pa) ((1 : ℝ) / 4000) := by
      intro k
      unfold Work.FIArea4.p14Bracket
      push_cast
      ring
    have hfinal : 16 * (Y / (e : ℝ)) + 120 * (Pa.N * (X : ℝ) ^ (-(1 : ℝ) / 2))
        + 30000 * Y ^ ((1 : ℝ) / 3) * Pa.N ^ ((2 : ℝ) / 3) * L ^ (4 : ℕ)
        + ((Nat.log 2 (4 * S15Y Pa X j) + 1 : ℕ) : ℝ) * (8 * Pa.N ^ ((23 : ℝ) / 24 + (1 : ℝ) / 4000))
      ≤ 16 * Y + 256 * Pa.N * (X : ℝ) ^ (-(1 : ℝ) / 2)
        + 31000 * Y ^ ((1 : ℝ) / 3) * Pa.N ^ ((2 : ℝ) / 3) * L ^ (4 : ℕ)
        + 64 * ((Nat.log 2 (4 * S15Y Pa X j) + 1 : ℕ) : ℝ)
            * Pa.N ^ ((23 : ℝ) / 24 + (1 : ℝ) / 4000) := by
      have hc1 : 16 * (Y / (e : ℝ)) ≤ 16 * Y := by
        have h : Y / (e : ℝ) ≤ Y := by
          rw [div_le_iff₀ he0]; nlinarith [he1, hY0]
        linarith
      have hc2 : 120 * (Pa.N * (X : ℝ) ^ (-(1 : ℝ) / 2))
          ≤ 256 * Pa.N * (X : ℝ) ^ (-(1 : ℝ) / 2) := by
        rw [show (256 : ℝ) * Pa.N * (X : ℝ) ^ (-(1 : ℝ) / 2)
              = 256 * (Pa.N * (X : ℝ) ^ (-(1 : ℝ) / 2)) by ring]
        exact mul_le_mul_of_nonneg_right (by norm_num)
          (mul_nonneg hN0 (Real.rpow_nonneg hX0 _))
      have hc3 : 30000 * Y ^ ((1 : ℝ) / 3) * Pa.N ^ ((2 : ℝ) / 3) * L ^ (4 : ℕ)
          ≤ 31000 * Y ^ ((1 : ℝ) / 3) * Pa.N ^ ((2 : ℝ) / 3) * L ^ (4 : ℕ) := by
        rw [show (31000 : ℝ) * Y ^ ((1 : ℝ) / 3) * Pa.N ^ ((2 : ℝ) / 3) * L ^ (4 : ℕ)
              = 31000 * (Y ^ ((1 : ℝ) / 3) * Pa.N ^ ((2 : ℝ) / 3) * L ^ (4 : ℕ)) by ring]
        rw [show (30000 : ℝ) * Y ^ ((1 : ℝ) / 3) * Pa.N ^ ((2 : ℝ) / 3) * L ^ (4 : ℕ)
              = 30000 * (Y ^ ((1 : ℝ) / 3) * Pa.N ^ ((2 : ℝ) / 3) * L ^ (4 : ℕ)) by ring]
        exact mul_le_mul_of_nonneg_right (by norm_num)
          (mul_nonneg (mul_nonneg (Real.rpow_nonneg hY0 _) (Real.rpow_nonneg hN0 _)) hL4)
      have hc4 : ((Nat.log 2 (4 * S15Y Pa X j) + 1 : ℕ) : ℝ)
            * (8 * Pa.N ^ ((23 : ℝ) / 24 + (1 : ℝ) / 4000))
          ≤ 64 * ((Nat.log 2 (4 * S15Y Pa X j) + 1 : ℕ) : ℝ)
              * Pa.N ^ ((23 : ℝ) / 24 + (1 : ℝ) / 4000) := by
        rw [show (64 : ℝ) * ((Nat.log 2 (4 * S15Y Pa X j) + 1 : ℕ) : ℝ)
              * Pa.N ^ ((23 : ℝ) / 24 + (1 : ℝ) / 4000)
              = 64 * (((Nat.log 2 (4 * S15Y Pa X j) + 1 : ℕ) : ℝ)
                  * Pa.N ^ ((23 : ℝ) / 24 + (1 : ℝ) / 4000)) by ring]
        rw [show ((Nat.log 2 (4 * S15Y Pa X j) + 1 : ℕ) : ℝ)
              * (8 * Pa.N ^ ((23 : ℝ) / 24 + (1 : ℝ) / 4000))
              = 8 * (((Nat.log 2 (4 * S15Y Pa X j) + 1 : ℕ) : ℝ)
                  * Pa.N ^ ((23 : ℝ) / 24 + (1 : ℝ) / 4000)) by ring]
        exact mul_le_mul_of_nonneg_right (by norm_num)
          (mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg hN0 _))
      exact add_le_add (add_le_add (add_le_add hc1 hc2) hc3) hc4
    calc (∑ k ∈ Kset, p14Bracket (2 ^ k) (S15EG_Re Pa e) (S15EG_Se Pa) ((1 : ℝ) / 4000))
        = ∑ k ∈ Kset, ((2 : ℝ) ^ k + ((2 : ℝ) ^ k) ^ (-(1 : ℝ) / 2) * R * S
            + ((2 : ℝ) ^ k) ^ ((1 : ℝ) / 3) * ((R * S) ^ ((2 : ℝ) / 3))
                * (Real.log (2 * R * S) + 1) ^ (4 : ℕ)
            + p14Last (S15EG_Re Pa e) (S15EG_Se Pa) ((1 : ℝ) / 4000)) :=
          Finset.sum_congr rfl (fun k _ => hcongr k)
      _ = (∑ k ∈ Kset, (2 : ℝ) ^ k)
            + (∑ k ∈ Kset, ((2 : ℝ) ^ k) ^ (-(1 : ℝ) / 2) * R * S)
            + (∑ k ∈ Kset, ((2 : ℝ) ^ k) ^ ((1 : ℝ) / 3) * ((R * S) ^ ((2 : ℝ) / 3))
                * (Real.log (2 * R * S) + 1) ^ (4 : ℕ))
            + (∑ k ∈ Kset, p14Last (S15EG_Re Pa e) (S15EG_Se Pa) ((1 : ℝ) / 4000)) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
      _ ≤ 16 * (Y / (e : ℝ)) + 120 * (Pa.N * (X : ℝ) ^ (-(1 : ℝ) / 2))
            + 30000 * Y ^ ((1 : ℝ) / 3) * Pa.N ^ ((2 : ℝ) / 3) * L ^ (4 : ℕ)
            + ((Nat.log 2 (4 * S15Y Pa X j) + 1 : ℕ) : ℝ)
                * (8 * Pa.N ^ ((23 : ℝ) / 24 + (1 : ℝ) / 4000)) :=
          add_le_add (add_le_add (add_le_add hA1 hA2) hA3) hA4
      _ ≤ 16 * Y + 256 * Pa.N * (X : ℝ) ^ (-(1 : ℝ) / 2)
            + 31000 * Y ^ ((1 : ℝ) / 3) * Pa.N ^ ((2 : ℝ) / 3) * L ^ (4 : ℕ)
            + 64 * ((Nat.log 2 (4 * S15Y Pa X j) + 1 : ℕ) : ℝ)
                * Pa.N ^ ((23 : ℝ) / 24 + (1 : ℝ) / 4000) := hfinal
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne]
    simp only [Finset.sum_empty]
    apply add_nonneg
    apply add_nonneg
    apply add_nonneg
    · exact mul_nonneg (by norm_num) hY0
    · apply mul_nonneg
      · exact mul_nonneg (by norm_num) hN0
      · exact Real.rpow_nonneg hX0 _
    · apply mul_nonneg
      · apply mul_nonneg
        · exact mul_nonneg (by norm_num) (Real.rpow_nonneg hY0 _)
        · exact Real.rpow_nonneg hN0 _
      · exact hL4
    · apply mul_nonneg
      · exact mul_nonneg (by norm_num) (Nat.cast_nonneg _)
      · exact Real.rpow_nonneg hN0 _

theorem kBracketSum6c :
    ∃ C : ℝ, 0 < C ∧ ∀ (Pa : Work.FITop.Params) (X j e : ℕ),
      1 ≤ X → (X : ℝ) ≤ (Pa.N : ℝ) ^ ((1 : ℝ) / 9) → 1 ≤ e →
      (∑ k ∈ Work.S15crux.kset Pa X j e,
          Work.FIArea4.p14Bracket (2 ^ k) (Work.FIArea4.S15EG_Re Pa e)
            (Work.FIArea4.S15EG_Se Pa) ((1 : ℝ) / 4000))
        ≤ C * (Real.log (Pa.N : ℝ) + 1) ^ 4 *
            (Work.FIArea4.S15Br6 Pa X
              + (Pa.N : ℝ) ^ ((1 : ℝ) / 3) * (X : ℝ) ^ (-(1 : ℝ) / 3)
                  * (Pa.N : ℝ) ^ ((2 : ℝ) / 3) * (e : ℝ) ^ (-(1 : ℝ))) := by
  refine ⟨100000, by norm_num, ?_⟩
  intro Pa X j e hX hXN9 he
  have hN1 : (1 : ℝ) ≤ Pa.N := Pa.hN1
  have hN0 : (0 : ℝ) ≤ Pa.N := by linarith
  have hX0 : (0 : ℝ) ≤ (X : ℝ) := Nat.cast_nonneg X
  have hXN : (X : ℝ) ≤ Pa.N := by
    have h1 : Pa.N ^ ((1 : ℝ) / 9) ≤ Pa.N := by
      calc Pa.N ^ ((1 : ℝ) / 9) ≤ Pa.N ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
        _ = Pa.N := Real.rpow_one _
    linarith
  have hcrude := bracket_sum_crude Pa X j e hX hXN he
  have habs := crude_bracket_le Pa X j hX
  have hext0 : (0 : ℝ) ≤ Pa.N ^ ((1 : ℝ) / 3) * (X : ℝ) ^ (-(1 : ℝ) / 3)
      * Pa.N ^ ((2 : ℝ) / 3) * (e : ℝ) ^ (-(1 : ℝ)) :=
    mul_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg hN0 _) (Real.rpow_nonneg hX0 _))
      (Real.rpow_nonneg hN0 _)) (Real.rpow_nonneg (Nat.cast_nonneg e) _)
  have hLnn : (0 : ℝ) ≤ 100000 * (Real.log Pa.N + 1) ^ 4 := by
    have h1 : (0 : ℝ) ≤ Real.log Pa.N := Real.log_nonneg hN1
    positivity
  calc (∑ k ∈ Work.S15crux.kset Pa X j e,
          Work.FIArea4.p14Bracket (2 ^ k) (Work.FIArea4.S15EG_Re Pa e)
            (Work.FIArea4.S15EG_Se Pa) ((1 : ℝ) / 4000))
      ≤ 16 * (S15Y Pa X j : ℝ) + 256 * Pa.N * (X : ℝ) ^ (-(1 : ℝ) / 2)
          + 31000 * ((S15Y Pa X j : ℝ)) ^ ((1 : ℝ) / 3) * Pa.N ^ ((2 : ℝ) / 3)
              * (Real.log Pa.N + 1) ^ (4 : ℕ)
          + 64 * ((Nat.log 2 (4 * S15Y Pa X j) + 1 : ℕ) : ℝ)
              * Pa.N ^ ((23 : ℝ) / 24 + (1 : ℝ) / 4000) := hcrude
    _ ≤ 100000 * (Real.log Pa.N + 1) ^ (4 : ℕ) * S15Br6 Pa X := habs
    _ ≤ 100000 * (Real.log Pa.N + 1) ^ (4 : ℕ)
          * (S15Br6 Pa X + Pa.N ^ ((1 : ℝ) / 3) * (X : ℝ) ^ (-(1 : ℝ) / 3)
              * Pa.N ^ ((2 : ℝ) / 3) * (e : ℝ) ^ (-(1 : ℝ))) :=
        mul_le_mul_of_nonneg_left (by linarith [hext0]) hLnn

end

end Work.FIArea4
