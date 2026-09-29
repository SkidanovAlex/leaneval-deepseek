import Mathlib
import Submission.CDTPlan.InterfacesA
import Submission.Work.APsi.defs
import Submission.Work.APsi.slit_facts
import Submission.Work.APsi.lune_facts

import Submission.CDTPlan.InterfacesA

/-!
# Area `Psi_A`: `psi_A` analytic facts (`Submission.CDTPlan.PsiAFacts`)

`psi_A = -(4/5) . lune (36/5) (-(slitsA .))` with `slitsA` the composition of the four slit
maps with rotations (CDT arXiv:2408.15403).  The proof composes the generic facts on a single
slit map (`Submission.Work.APsi.slit_facts`) and on the lune map
(`Submission.Work.APsi.lune_facts`) along the chain `psiA_st1, ..., psiA_st5`.
-/

namespace Work.APsi

open Submission.CDTPlan Complex Metric

noncomputable section

lemma psiA_mem_closedBall_one {z : ℂ} : z ∈ closedBall 0 1 ↔ ‖z‖ ≤ 1 := by
  rw [mem_closedBall, dist_zero_right]

lemma psiA_mem_ball_one {z : ℂ} : z ∈ ball 0 1 ↔ ‖z‖ < 1 := by
  rw [mem_ball, dist_zero_right]

/-- `‖(m : ℂ)/n‖ ≤ 1` for `m ≤ n`, `n > 0`. -/
lemma psiA_norm_div_le_one (m n : ℕ) (hn : 0 < n) (h : m ≤ n) : ‖((m : ℂ) / n)‖ ≤ 1 := by
  rw [show ((m : ℂ) / n) = ((m / n : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [div_le_one (by exact_mod_cast hn)]
  exact_mod_cast h

lemma psiA_mapsTo_closedBall_const_mul (a : ℂ) (ha : ‖a‖ ≤ 1) :
    Set.MapsTo (fun z : ℂ => a * z) (closedBall 0 1) (closedBall 0 1) := by
  intro z hz
  rw [psiA_mem_closedBall_one] at hz ⊢
  rw [norm_mul]
  nlinarith [norm_nonneg z, norm_nonneg a]

lemma psiA_mapsTo_ball_const_mul (a : ℂ) (ha : ‖a‖ ≤ 1) :
    Set.MapsTo (fun z : ℂ => a * z) (ball 0 1) (ball 0 1) := by
  intro z hz
  rw [psiA_mem_ball_one] at hz ⊢
  rw [norm_mul]
  calc ‖a‖ * ‖z‖ ≤ 1 * ‖z‖ := by nlinarith [norm_nonneg z]
    _ = ‖z‖ := one_mul _
    _ < 1 := hz

lemma psiA_mapsTo_rot_closedBall {f : ℂ → ℂ} (hf : Set.MapsTo f (closedBall 0 1) (closedBall 0 1))
    (t : ℝ) : Set.MapsTo (fun z : ℂ => rot t * f z) (closedBall 0 1) (closedBall 0 1) := by
  intro z hz
  have h1 : f z ∈ closedBall 0 1 := hf hz
  rw [psiA_mem_closedBall_one] at h1 ⊢
  rw [norm_mul, norm_rot, one_mul]
  exact h1

lemma psiA_mapsTo_rot_ball {f : ℂ → ℂ} (hf : Set.MapsTo f (ball 0 1) (ball 0 1)) (t : ℝ) :
    Set.MapsTo (fun z : ℂ => rot t * f z) (ball 0 1) (ball 0 1) := by
  intro z hz
  have h1 : f z ∈ ball 0 1 := hf hz
  rw [psiA_mem_ball_one] at h1 ⊢
  rw [norm_mul, norm_rot, one_mul]
  exact h1

/-- the four slit stages and the final rotation -/
def psiA_st1 (z : ℂ) : ℂ := slit (9 / 10) ((491 / 500 : ℂ) * z)
def psiA_st2 (z : ℂ) : ℂ := slit (379 / 625) (rot (2033 / 25000) * psiA_st1 z)
def psiA_st3 (z : ℂ) : ℂ := slit (673 / 1250) (rot (2927 / 25000) * psiA_st2 z)
def psiA_st4 (z : ℂ) : ℂ := slit (7487 / 10000) (rot (453 / 12500) * psiA_st3 z)
def psiA_st5 (z : ℂ) : ℂ := rot (-1971 / 25000) * psiA_st4 z

lemma psiA_slitsA_eq : slitsA = psiA_st5 := by
  funext z
  simp only [slitsA, psiA_st5, psiA_st4, psiA_st3, psiA_st2, psiA_st1]

lemma psiA_st1_cont : ContinuousOn psiA_st1 (closedBall 0 1) := by
  have h := (slit_facts (9 / 10) (by norm_num) (by norm_num)).1
  have h2 : ContinuousOn (fun z : ℂ => (491 / 500 : ℂ) * z) (closedBall 0 1) :=
    continuousOn_id.const_mul _
  have hm := psiA_mapsTo_closedBall_const_mul _ (psiA_norm_div_le_one 491 500 (by norm_num) (by norm_num))
  exact h.comp h2 hm

lemma psiA_st1_diff : DifferentiableOn ℂ psiA_st1 (ball 0 1) := by
  have h := (slit_facts (9 / 10) (by norm_num) (by norm_num)).2.1
  have h2 : DifferentiableOn ℂ (fun z : ℂ => (491 / 500 : ℂ) * z) (ball 0 1) :=
    differentiableOn_id.const_mul _
  have hm := psiA_mapsTo_ball_const_mul _ (psiA_norm_div_le_one 491 500 (by norm_num) (by norm_num))
  exact h.comp h2 hm

lemma psiA_st1_maps : Set.MapsTo psiA_st1 (closedBall 0 1) (closedBall 0 1) := by
  have hb := (slit_facts (9 / 10) (by norm_num) (by norm_num)).2.2.2.1
  intro z hz
  have h1 : (491 / 500 : ℂ) * z ∈ closedBall 0 1 :=
    psiA_mapsTo_closedBall_const_mul _ (psiA_norm_div_le_one 491 500 (by norm_num) (by norm_num)) hz
  rw [psiA_mem_closedBall_one] at h1 ⊢
  exact hb _ h1

lemma psiA_st1_maps_ball : Set.MapsTo psiA_st1 (ball 0 1) (ball 0 1) := by
  have hb := (slit_facts (9 / 10) (by norm_num) (by norm_num)).2.2.2.2.1
  intro z hz
  have h1 : (491 / 500 : ℂ) * z ∈ ball 0 1 :=
    psiA_mapsTo_ball_const_mul _ (psiA_norm_div_le_one 491 500 (by norm_num) (by norm_num)) hz
  rw [psiA_mem_ball_one] at h1 ⊢
  exact hb _ h1

lemma psiA_st1_zero : ∀ z : ℂ, psiA_st1 z = 0 → z = 0 := by
  have hz0 := (slit_facts (9 / 10) (by norm_num) (by norm_num)).2.2.2.2.2
  intro z hz
  have h : (491 / 500 : ℂ) * z = 0 := hz0 _ hz
  rcases mul_eq_zero.mp h with h1 | h2
  · exact absurd h1 (by norm_num)
  · exact h2

lemma psiA_st2_cont : ContinuousOn psiA_st2 (closedBall 0 1) := by
  have h := (slit_facts (379 / 625) (by norm_num) (by norm_num)).1
  have h2 : ContinuousOn (fun z : ℂ => rot (2033 / 25000) * psiA_st1 z) (closedBall 0 1) :=
    psiA_st1_cont.const_mul _
  have hm : Set.MapsTo (fun z : ℂ => rot (2033 / 25000) * psiA_st1 z) (closedBall 0 1) (closedBall 0 1) :=
    psiA_mapsTo_rot_closedBall psiA_st1_maps _
  exact h.comp h2 hm

lemma psiA_st2_diff : DifferentiableOn ℂ psiA_st2 (ball 0 1) := by
  have h := (slit_facts (379 / 625) (by norm_num) (by norm_num)).2.1
  have h2 : DifferentiableOn ℂ (fun z : ℂ => rot (2033 / 25000) * psiA_st1 z) (ball 0 1) :=
    psiA_st1_diff.const_mul _
  have hm : Set.MapsTo (fun z : ℂ => rot (2033 / 25000) * psiA_st1 z) (ball 0 1) (ball 0 1) :=
    psiA_mapsTo_rot_ball psiA_st1_maps_ball _
  exact h.comp h2 hm

lemma psiA_st2_maps : Set.MapsTo psiA_st2 (closedBall 0 1) (closedBall 0 1) := by
  have hb := (slit_facts (379 / 625) (by norm_num) (by norm_num)).2.2.2.1
  intro z hz
  have h1 : rot (2033 / 25000) * psiA_st1 z ∈ closedBall 0 1 := psiA_mapsTo_rot_closedBall psiA_st1_maps _ hz
  rw [psiA_mem_closedBall_one] at h1 ⊢
  exact hb _ h1

lemma psiA_st2_maps_ball : Set.MapsTo psiA_st2 (ball 0 1) (ball 0 1) := by
  have hb := (slit_facts (379 / 625) (by norm_num) (by norm_num)).2.2.2.2.1
  intro z hz
  have h1 : rot (2033 / 25000) * psiA_st1 z ∈ ball 0 1 := psiA_mapsTo_rot_ball psiA_st1_maps_ball _ hz
  rw [psiA_mem_ball_one] at h1 ⊢
  exact hb _ h1

lemma psiA_st2_zero : ∀ z : ℂ, psiA_st2 z = 0 → z = 0 := by
  have hz0 := (slit_facts (379 / 625) (by norm_num) (by norm_num)).2.2.2.2.2
  intro z hz
  have h : rot (2033 / 25000) * psiA_st1 z = 0 := hz0 _ hz
  rcases mul_eq_zero.mp h with h1 | h2
  · exact absurd h1 (rot_ne_zero _)
  · exact psiA_st1_zero z h2

lemma psiA_st3_cont : ContinuousOn psiA_st3 (closedBall 0 1) := by
  have h := (slit_facts (673 / 1250) (by norm_num) (by norm_num)).1
  have h2 : ContinuousOn (fun z : ℂ => rot (2927 / 25000) * psiA_st2 z) (closedBall 0 1) :=
    psiA_st2_cont.const_mul _
  have hm : Set.MapsTo (fun z : ℂ => rot (2927 / 25000) * psiA_st2 z) (closedBall 0 1) (closedBall 0 1) :=
    psiA_mapsTo_rot_closedBall psiA_st2_maps _
  exact h.comp h2 hm

lemma psiA_st3_diff : DifferentiableOn ℂ psiA_st3 (ball 0 1) := by
  have h := (slit_facts (673 / 1250) (by norm_num) (by norm_num)).2.1
  have h2 : DifferentiableOn ℂ (fun z : ℂ => rot (2927 / 25000) * psiA_st2 z) (ball 0 1) :=
    psiA_st2_diff.const_mul _
  have hm : Set.MapsTo (fun z : ℂ => rot (2927 / 25000) * psiA_st2 z) (ball 0 1) (ball 0 1) :=
    psiA_mapsTo_rot_ball psiA_st2_maps_ball _
  exact h.comp h2 hm

lemma psiA_st3_maps : Set.MapsTo psiA_st3 (closedBall 0 1) (closedBall 0 1) := by
  have hb := (slit_facts (673 / 1250) (by norm_num) (by norm_num)).2.2.2.1
  intro z hz
  have h1 : rot (2927 / 25000) * psiA_st2 z ∈ closedBall 0 1 := psiA_mapsTo_rot_closedBall psiA_st2_maps _ hz
  rw [psiA_mem_closedBall_one] at h1 ⊢
  exact hb _ h1

lemma psiA_st3_maps_ball : Set.MapsTo psiA_st3 (ball 0 1) (ball 0 1) := by
  have hb := (slit_facts (673 / 1250) (by norm_num) (by norm_num)).2.2.2.2.1
  intro z hz
  have h1 : rot (2927 / 25000) * psiA_st2 z ∈ ball 0 1 := psiA_mapsTo_rot_ball psiA_st2_maps_ball _ hz
  rw [psiA_mem_ball_one] at h1 ⊢
  exact hb _ h1

lemma psiA_st3_zero : ∀ z : ℂ, psiA_st3 z = 0 → z = 0 := by
  have hz0 := (slit_facts (673 / 1250) (by norm_num) (by norm_num)).2.2.2.2.2
  intro z hz
  have h : rot (2927 / 25000) * psiA_st2 z = 0 := hz0 _ hz
  rcases mul_eq_zero.mp h with h1 | h2
  · exact absurd h1 (rot_ne_zero _)
  · exact psiA_st2_zero z h2

lemma psiA_st4_cont : ContinuousOn psiA_st4 (closedBall 0 1) := by
  have h := (slit_facts (7487 / 10000) (by norm_num) (by norm_num)).1
  have h2 : ContinuousOn (fun z : ℂ => rot (453 / 12500) * psiA_st3 z) (closedBall 0 1) :=
    psiA_st3_cont.const_mul _
  have hm : Set.MapsTo (fun z : ℂ => rot (453 / 12500) * psiA_st3 z) (closedBall 0 1) (closedBall 0 1) :=
    psiA_mapsTo_rot_closedBall psiA_st3_maps _
  exact h.comp h2 hm

lemma psiA_st4_diff : DifferentiableOn ℂ psiA_st4 (ball 0 1) := by
  have h := (slit_facts (7487 / 10000) (by norm_num) (by norm_num)).2.1
  have h2 : DifferentiableOn ℂ (fun z : ℂ => rot (453 / 12500) * psiA_st3 z) (ball 0 1) :=
    psiA_st3_diff.const_mul _
  have hm : Set.MapsTo (fun z : ℂ => rot (453 / 12500) * psiA_st3 z) (ball 0 1) (ball 0 1) :=
    psiA_mapsTo_rot_ball psiA_st3_maps_ball _
  exact h.comp h2 hm

lemma psiA_st4_maps : Set.MapsTo psiA_st4 (closedBall 0 1) (closedBall 0 1) := by
  have hb := (slit_facts (7487 / 10000) (by norm_num) (by norm_num)).2.2.2.1
  intro z hz
  have h1 : rot (453 / 12500) * psiA_st3 z ∈ closedBall 0 1 := psiA_mapsTo_rot_closedBall psiA_st3_maps _ hz
  rw [psiA_mem_closedBall_one] at h1 ⊢
  exact hb _ h1

lemma psiA_st4_maps_ball : Set.MapsTo psiA_st4 (ball 0 1) (ball 0 1) := by
  have hb := (slit_facts (7487 / 10000) (by norm_num) (by norm_num)).2.2.2.2.1
  intro z hz
  have h1 : rot (453 / 12500) * psiA_st3 z ∈ ball 0 1 := psiA_mapsTo_rot_ball psiA_st3_maps_ball _ hz
  rw [psiA_mem_ball_one] at h1 ⊢
  exact hb _ h1

lemma psiA_st4_zero : ∀ z : ℂ, psiA_st4 z = 0 → z = 0 := by
  have hz0 := (slit_facts (7487 / 10000) (by norm_num) (by norm_num)).2.2.2.2.2
  intro z hz
  have h : rot (453 / 12500) * psiA_st3 z = 0 := hz0 _ hz
  rcases mul_eq_zero.mp h with h1 | h2
  · exact absurd h1 (rot_ne_zero _)
  · exact psiA_st3_zero z h2

lemma psiA_st5_cont : ContinuousOn psiA_st5 (closedBall 0 1) := by
  have h2 : ContinuousOn (fun z : ℂ => rot (-1971 / 25000) * psiA_st4 z) (closedBall 0 1) :=
    psiA_st4_cont.const_mul _
  exact h2

lemma psiA_st5_diff : DifferentiableOn ℂ psiA_st5 (ball 0 1) := by
  have h2 : DifferentiableOn ℂ (fun z : ℂ => rot (-1971 / 25000) * psiA_st4 z) (ball 0 1) :=
    psiA_st4_diff.const_mul _
  exact h2

lemma psiA_st5_maps : Set.MapsTo psiA_st5 (closedBall 0 1) (closedBall 0 1) := by
  intro z hz
  have h1 : rot (-1971 / 25000) * psiA_st4 z ∈ closedBall 0 1 :=
    psiA_mapsTo_rot_closedBall psiA_st4_maps _ hz
  exact h1

lemma psiA_st5_maps_ball : Set.MapsTo psiA_st5 (ball 0 1) (ball 0 1) := by
  intro z hz
  have h1 : rot (-1971 / 25000) * psiA_st4 z ∈ ball 0 1 := psiA_mapsTo_rot_ball psiA_st4_maps_ball _ hz
  exact h1

lemma psiA_st5_zero : ∀ z : ℂ, psiA_st5 z = 0 → z = 0 := by
  intro z hz
  simp only [psiA_st5] at hz
  rcases mul_eq_zero.mp hz with h1 | h2
  · exact absurd h1 (rot_ne_zero _)
  · exact psiA_st4_zero z h2

lemma psiA_st5_zero_val : psiA_st5 0 = 0 := by
  simp [psiA_st5, psiA_st4, psiA_st3, psiA_st2, psiA_st1, slit]

theorem psiA_facts : PsiAFacts := by
  have hpsiA : psiA = fun z : ℂ => -((4 : ℂ) / 5) * lune (36 / 5) (-(psiA_st5 z)) := by
    funext z
    simp only [psiA, psiA_slitsA_eq]
  unfold PsiAFacts
  rw [hpsiA]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have hl := (lune_facts (36 / 5) (by norm_num)).1
    have h2 : ContinuousOn (fun z : ℂ => -(psiA_st5 z)) (closedBall 0 1) := psiA_st5_cont.neg
    have hm : Set.MapsTo (fun z : ℂ => -(psiA_st5 z)) (closedBall 0 1) (closedBall 0 1) := by
      intro z hz
      have h1 : psiA_st5 z ∈ closedBall 0 1 := psiA_st5_maps hz
      rw [psiA_mem_closedBall_one] at h1 ⊢
      simpa only [norm_neg] using h1
    exact (hl.comp h2 hm).const_mul _
  · have hl := (lune_facts (36 / 5) (by norm_num)).2.1
    have h2 : DifferentiableOn ℂ (fun z : ℂ => -(psiA_st5 z)) (ball 0 1) := psiA_st5_diff.neg
    have hm : Set.MapsTo (fun z : ℂ => -(psiA_st5 z)) (ball 0 1) (ball 0 1) := by
      intro z hz
      have h1 : psiA_st5 z ∈ ball 0 1 := psiA_st5_maps_ball hz
      rw [psiA_mem_ball_one] at h1 ⊢
      simpa only [norm_neg] using h1
    exact (hl.comp h2 hm).const_mul _
  · dsimp only
    rw [psiA_st5_zero_val, neg_zero, (lune_facts (36 / 5) (by norm_num)).2.2.1]
    ring
  · intro z hz
    have h5 : ‖psiA_st5 z‖ ≤ 1 := by
      have h := psiA_st5_maps hz
      rwa [psiA_mem_closedBall_one] at h
    have hl := (lune_facts (36 / 5) (by norm_num)).2.2.2.1
    have h2 : ‖lune (36 / 5) (-(psiA_st5 z))‖ ≤ 1 := hl _ (by simpa using h5)
    have hc : ‖((4 : ℂ) / 5)‖ = (4 / 5 : ℝ) := by
      rw [show ((4 : ℂ) / 5) = ((4 / 5 : ℝ) : ℂ) by norm_num, Complex.norm_real]
      norm_num
    have h1 : ‖-((4 : ℂ) / 5) * lune (36 / 5) (-(psiA_st5 z))‖
        = (4 / 5) * ‖lune (36 / 5) (-(psiA_st5 z))‖ := by
      rw [norm_mul, norm_neg, hc]
    rw [h1]
    nlinarith
  · intro z hz hzero
    have hzero' : -((4 : ℂ) / 5) * lune (36 / 5) (-(psiA_st5 z)) = 0 := hzero
    have hl := (lune_facts (36 / 5) (by norm_num)).2.2.2.2.2
    have h1 : lune (36 / 5) (-(psiA_st5 z)) = 0 :=
      (mul_eq_zero.mp hzero').resolve_left (by norm_num)
    have h2 : -(psiA_st5 z) = 0 := hl _ h1
    exact psiA_st5_zero z (neg_eq_zero.mp h2)

end

end Work.APsi
