import Mathlib
import Submission.Work.LinnikAreas.sumI_arith
import Submission.Work.LinnikBurgess.sumI_defs
import Submission.Work.LinnikBurgess.sumI_aux.bSumBox_le
import Submission.Work.LinnikBurgess.frame_count_prov_helpers
import Submission.Work.LinnikBurgess.frame_count_prov_aux.masterSum_eq_masterSum2
import Submission.Work.LinnikBurgess.frameMod_bridge
import Submission.Work.LinnikBurgess.frame_step_card_d_nohb
import Submission.Work.LinnikBurgess.a2_sum_bound
import Submission.Work.LinnikBurgess.DLd_perm
import Submission.Work.LinnikBurgess.caseI_slot_bound

open scoped BigOperators
open Classical

namespace Work.LinnikAreas

open Work.LinnikBurgess

private lemma frameMod_eq_prod' (d a0 a1 : ℕ) :
    frameMod d a0 a1 = ∏ p ∈ d.primeFactors, p ^ (max 0 (d.factorization p
        - padicValNat p 2 - padicValNat p (((a0 : ℤ) - (a1 : ℤ)).natAbs))) := rfl

private lemma val_zero_triple (x0 x1 x2 : ℕ) : (![x0, x1, x2] : Fin 3 → ℕ) 0 = x0 := rfl
private lemma val_one_triple (x0 x1 x2 : ℕ) : (![x0, x1, x2] : Fin 3 → ℕ) 1 = x1 := rfl
private lemma val_two_triple (x0 x1 x2 : ℕ) : (![x0, x1, x2] : Fin 3 → ℕ) 2 = x2 := rfl

theorem sumI_le_SIframe (H m d g : ℕ) : sumI H m d g ≤ SIframe H m d g := by
  classical
  have hswap : (∑ x0 ∈ Finset.Icc 1 H, ∑ x1 ∈ Finset.Icc 1 H, ∑ x2 ∈ Finset.Icc 1 H,
        ∑ b ∈ box3 H, (if condAB d g ![x0,x1,x2] b ∧ CaseI ![x0,x1,x2] b
          then wtAB m ![x0,x1,x2] b else 0))
      = (∑ x0 ∈ Finset.Icc 1 H, ∑ b ∈ box3 H, ∑ x1 ∈ Finset.Icc 1 H, ∑ x2 ∈ Finset.Icc 1 H,
          (if condAB d g ![x0,x1,x2] b ∧ CaseI ![x0,x1,x2] b
            then wtAB m ![x0,x1,x2] b else 0)) := by
    refine Finset.sum_congr rfl (fun x0 _ => ?_)
    refine (Finset.sum_congr rfl (fun x1 _ =>
      Finset.sum_comm (s := Finset.Icc 1 H) (t := box3 H)
        (f := fun x2 b => (if condAB d g ![x0,x1,x2] b ∧ CaseI ![x0,x1,x2] b
          then wtAB m ![x0,x1,x2] b else 0)))).trans
      (Finset.sum_comm (s := Finset.Icc 1 H) (t := box3 H)
        (f := fun x1 b => ∑ x2 ∈ Finset.Icc 1 H,
          (if condAB d g ![x0,x1,x2] b ∧ CaseI ![x0,x1,x2] b
            then wtAB m ![x0,x1,x2] b else 0)))
  calc sumI H m d g
      = ∑ a ∈ box3 H, ∑ b ∈ box3 H,
          (if condAB d g a b ∧ CaseI a b then wtAB m a b else 0) := by rw [sumI]
    _ ≤ ∑ x0 ∈ Finset.Icc 1 H, ∑ x1 ∈ Finset.Icc 1 H, ∑ x2 ∈ Finset.Icc 1 H,
          ∑ b ∈ box3 H, (if condAB d g ![x0,x1,x2] b ∧ CaseI ![x0,x1,x2] b
            then wtAB m ![x0,x1,x2] b else 0) := by
        rw [box3, sum_piFinset_fin3]
    _ = ∑ x0 ∈ Finset.Icc 1 H, ∑ b ∈ box3 H, ∑ x1 ∈ Finset.Icc 1 H, ∑ x2 ∈ Finset.Icc 1 H,
          (if condAB d g ![x0,x1,x2] b ∧ CaseI ![x0,x1,x2] b
            then wtAB m ![x0,x1,x2] b else 0) := hswap
    _ ≤ SIframe H m d g := by
        rw [SIframe]
        refine Finset.sum_le_sum (fun x0 _ => Finset.sum_le_sum (fun b _ =>
          Finset.sum_le_sum (fun x1 _ => Finset.sum_le_sum (fun x2 _ => ?_))))
        by_cases hP : condAB d g ![x0,x1,x2] b ∧ CaseI ![x0,x1,x2] b
        · rw [if_pos hP]
          have hQ : (∀ l : Fin 3, b l ≠ x0) ∧ x1 ≠ x0 ∧ x2 ≠ x0
              ∧ DLd d ![x0,x1,x2] b ∧ g ∣ ∏ k : Fin 3, del x0 (b k) := by
            obtain ⟨hcond, _⟩ := hP
            obtain ⟨hnib, h01, h02, hdl, hg⟩ := hcond
            refine ⟨?_, ?_, ?_, hdl, ?_⟩
            · intro l hh
              exact hnib l (by rw [val_zero_triple]; exact hh.symm)
            · intro hh
              exact h01 (by rw [val_zero_triple, val_one_triple]; exact hh.symm)
            · intro hh
              exact h02 (by rw [val_zero_triple, val_two_triple]; exact hh.symm)
            · refine dvd_trans hg ?_
              simpa [val_zero_triple] using contAB_dvd_prod_del (![x0,x1,x2] : Fin 3 → ℕ) b 0
          rw [if_pos hQ]
        · rw [if_neg hP]
          split
          · simp only [wtAB, wg]; positivity
          · rfl

/-! ## Step 2: the inner `(x1,x2)`-sum is bounded by `frameG` (AM-GM + frame step) -/

theorem TTsum_le_frameG {H m d x0 : ℕ} (hd : 0 < d) (b : Fin 3 → ℕ) :
    TTsum H m d x0 b ≤ frameG H m d x0 := by
  classical
  set s := Finset.Icc 1 H with hs
  set P : ℕ → ℕ → Prop := fun x1 x2 => x1 ≠ x0 ∧ x2 ≠ x0 ∧ DLd d ![x0,x1,x2] b with hP
  have hsymm : ∀ x1 x2, P x2 x1 ↔ P x1 x2 := by
    intro x1 x2
    have hsw : DLd d ![x0,x2,x1] b ↔ DLd d ![x0,x1,x2] b := by
      have h := DLd_perm (d := d) (![x0,x1,x2] : Fin 3 → ℕ) b (Equiv.swap 1 2)
      have hfun : (fun l : Fin 3 => ![x0,x1,x2] (Equiv.swap 1 2 l)) = ![x0,x2,x1] := by
        funext l; fin_cases l <;> rfl
      rwa [hfun] at h
    simp only [hP]
    constructor
    · rintro ⟨h2, h1, hdl⟩
      exact ⟨h1, h2, hsw.mp hdl⟩
    · rintro ⟨h1, h2, hdl⟩
      exact ⟨h2, h1, hsw.mpr hdl⟩
  have hpt : ∀ x1 x2 : ℕ, 2 * (if P x1 x2 then wg m x0 x1 * wg m x0 x2 else 0)
      ≤ (if P x1 x2 then ((Nat.gcd m (del x0 x1) : ℕ) : ℝ) else 0)
        + (if P x1 x2 then ((Nat.gcd m (del x0 x2) : ℕ) : ℝ) else 0) := by
    intro x1 x2
    by_cases h : P x1 x2
    · rw [if_pos h, if_pos h, if_pos h]
      have h1 := wg_sq m x0 x1
      have h2 := wg_sq m x0 x2
      nlinarith [sq_nonneg (wg m x0 x1 - wg m x0 x2), wg_nonneg m x0 x1, wg_nonneg m x0 x2]
    · simp [h]
  have h2A : 2 * (∑ x1 ∈ s, ∑ x2 ∈ s, (if P x1 x2 then wg m x0 x1 * wg m x0 x2 else 0))
      ≤ (∑ x1 ∈ s, ∑ x2 ∈ s, (if P x1 x2 then ((Nat.gcd m (del x0 x1) : ℕ) : ℝ) else 0))
        + (∑ x1 ∈ s, ∑ x2 ∈ s, (if P x1 x2 then ((Nat.gcd m (del x0 x2) : ℕ) : ℝ) else 0)) := by
    rw [Finset.mul_sum]
    calc ∑ x1 ∈ s, 2 * (∑ x2 ∈ s, (if P x1 x2 then wg m x0 x1 * wg m x0 x2 else 0))
        = ∑ x1 ∈ s, (∑ x2 ∈ s, 2 * (if P x1 x2 then wg m x0 x1 * wg m x0 x2 else 0)) := by
          refine Finset.sum_congr rfl (fun x1 _ => ?_)
          rw [Finset.mul_sum]
      _ ≤ ∑ x1 ∈ s, ((∑ x2 ∈ s, (if P x1 x2 then ((Nat.gcd m (del x0 x1) : ℕ) : ℝ) else 0))
            + (∑ x2 ∈ s, (if P x1 x2 then ((Nat.gcd m (del x0 x2) : ℕ) : ℝ) else 0))) := by
          refine Finset.sum_le_sum (fun x1 _ => ?_)
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_le_sum (fun x2 _ => hpt x1 x2)
      _ = (∑ x1 ∈ s, ∑ x2 ∈ s, (if P x1 x2 then ((Nat.gcd m (del x0 x1) : ℕ) : ℝ) else 0))
            + (∑ x1 ∈ s, ∑ x2 ∈ s, (if P x1 x2 then ((Nat.gcd m (del x0 x2) : ℕ) : ℝ) else 0)) := by
          rw [Finset.sum_add_distrib]
  have hB' : (∑ x1 ∈ s, ∑ x2 ∈ s, (if P x1 x2 then ((Nat.gcd m (del x0 x2) : ℕ) : ℝ) else 0))
      = (∑ x1 ∈ s, ∑ x2 ∈ s, (if P x1 x2 then ((Nat.gcd m (del x0 x1) : ℕ) : ℝ) else 0)) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun bb _ => ?_))
    by_cases hab : P a bb
    · have hba : P bb a := (hsymm a bb).mpr hab
      rw [if_pos hba, if_pos hab]
    · have hba : ¬ P bb a := fun hc => hab ((hsymm a bb).mp hc)
      rw [if_neg hba, if_neg hab]
  have hAB : (∑ x1 ∈ s, ∑ x2 ∈ s, (if P x1 x2 then wg m x0 x1 * wg m x0 x2 else 0))
      ≤ (∑ x1 ∈ s, ∑ x2 ∈ s, (if P x1 x2 then ((Nat.gcd m (del x0 x1) : ℕ) : ℝ) else 0)) := by
    have h := h2A
    rw [hB'] at h
    linarith
  have hcard : (∑ x1 ∈ s, ∑ x2 ∈ s, (if P x1 x2 then ((Nat.gcd m (del x0 x1) : ℕ) : ℝ) else 0))
      = ∑ x1 ∈ s.filter (fun x1 => x1 ≠ x0),
          ((Nat.gcd m (del x0 x1) : ℕ) : ℝ) * (((s.filter (fun x2 => P x1 x2)).card : ℕ) : ℝ) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun x1 _ => ?_)
    by_cases h0 : x1 ≠ x0
    · have hcardeq : (((s.filter (fun x2 => P x1 x2)).card : ℕ) : ℝ)
          = ∑ x2 ∈ s, (if P x1 x2 then (1:ℝ) else 0) := by
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
      rw [if_pos h0, hcardeq, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun x2 _ => ?_)
      by_cases h : P x1 x2
      · simp only [if_pos h, mul_one]
      · simp only [if_neg h, mul_zero]
    · have hno : ∀ x2, ¬ P x1 x2 := fun x2 hx2 => h0 hx2.1
      have hsum : (∑ x2 ∈ s, (if P x1 x2 then ((Nat.gcd m (del x0 x1) : ℕ) : ℝ) else 0)) = 0 :=
        Finset.sum_eq_zero (fun x2 _ => by rw [if_neg (hno x2)])
      rw [if_neg h0, hsum]
  have hframe : (∑ x1 ∈ s.filter (fun x1 => x1 ≠ x0),
        ((Nat.gcd m (del x0 x1) : ℕ) : ℝ) * (((s.filter (fun x2 => P x1 x2)).card : ℕ) : ℝ))
      ≤ frameG H m d x0 := by
    rw [frameG, ← hs]
    refine Finset.sum_le_sum (fun x1 hx1 => mul_le_mul_of_nonneg_left ?_ (by positivity))
    have hne : x1 ≠ x0 := (Finset.mem_filter.mp hx1).2
    have hsub : s.filter (fun x2 => P x1 x2) ⊆ frameStepSetD d H x0 x1 b := by
      intro x2 hx2
      obtain ⟨hx2s, hPx⟩ := Finset.mem_filter.mp hx2
      exact mem_frameStepSetD_of_DLd b hx2s hPx.2.2
    have hcardle := Finset.card_le_card hsub
    have hfs := frame_step_card_d_nohb (d := d) (a0 := x0) (a1 := x1) (b := b) (H := H) hd
      (fun hh => hne hh.symm)
    rw [← frameMod_eq_prod' d x0 x1] at hfs
    have h1 : (((s.filter (fun x2 => P x1 x2)).card : ℕ) : ℝ)
        ≤ ((frameStepSetD d H x0 x1 b).card : ℕ) := by exact_mod_cast hcardle
    have h2 : (((frameStepSetD d H x0 x1 b).card : ℕ) : ℝ)
        ≤ (3 : ℝ) ^ d.primeFactors.card * ((H : ℝ) / (frameMod d x0 x1 : ℝ) + 1) := by
      have h3 : (((frameStepSetD d H x0 x1 b).card : ℕ) : ℝ)
          ≤ ((3 ^ d.primeFactors.card * (H / frameMod d x0 x1 + 1) : ℕ) : ℝ) := by
        exact_mod_cast hfs
      refine h3.trans ?_
      push_cast
      have h4 : ((H / frameMod d x0 x1 : ℕ) : ℝ) ≤ (H : ℝ) / (frameMod d x0 x1 : ℝ) :=
        Nat.cast_div_le
      exact mul_le_mul_of_nonneg_left (add_le_add h4 le_rfl) (by positivity)
    linarith
  rw [TTsum]
  have h1 := hAB
  have h2 := hcard
  have h3 := hframe
  simp only [hP, hs] at h1 h2 h3
  exact h1.trans ((le_of_eq h2).trans h3)

lemma frameG_nonneg (H m d x0 : ℕ) : 0 ≤ frameG H m d x0 := by
  rw [frameG]
  exact Finset.sum_nonneg (fun x _ => mul_nonneg (by positivity) (by positivity))

theorem SIframe_le (H m d g : ℕ) (hd : 0 < d) :
    SIframe H m d g
      ≤ ∑ x0 ∈ Finset.Icc 1 H, frameG H m d x0 * bSumBox H m g x0 := by
  classical
  rw [SIframe]
  refine Finset.sum_le_sum (fun x0 _ => ?_)
  have hinner : ∀ b ∈ box3 H,
      (∑ x1 ∈ Finset.Icc 1 H, ∑ x2 ∈ Finset.Icc 1 H,
        (if (∀ l : Fin 3, b l ≠ x0) ∧ x1 ≠ x0 ∧ x2 ≠ x0 ∧ DLd d ![x0,x1,x2] b
            ∧ g ∣ ∏ k : Fin 3, del x0 (b k)
          then wtAB m ![x0,x1,x2] b else 0))
      ≤ (if (∀ l : Fin 3, b l ≠ x0) ∧ g ∣ ∏ k : Fin 3, del x0 (b k)
          then ∏ k : Fin 3, wg m x0 (b k) else 0) * frameG H m d x0 := by
    intro b _
    by_cases hBC : (∀ l : Fin 3, b l ≠ x0) ∧ g ∣ ∏ k : Fin 3, del x0 (b k)
    · rw [if_pos hBC]
      have hsplit : (∑ x1 ∈ Finset.Icc 1 H, ∑ x2 ∈ Finset.Icc 1 H,
          (if (∀ l : Fin 3, b l ≠ x0) ∧ x1 ≠ x0 ∧ x2 ≠ x0 ∧ DLd d ![x0,x1,x2] b
              ∧ g ∣ ∏ k : Fin 3, del x0 (b k)
            then wtAB m ![x0,x1,x2] b else 0))
          = (∏ k : Fin 3, wg m x0 (b k)) * TTsum H m d x0 b := by
        rw [TTsum, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun x1 _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun x2 _ => ?_)
        by_cases hfull : (∀ l : Fin 3, b l ≠ x0) ∧ x1 ≠ x0 ∧ x2 ≠ x0 ∧ DLd d ![x0,x1,x2] b
            ∧ g ∣ ∏ k : Fin 3, del x0 (b k)
        · have hTT : x1 ≠ x0 ∧ x2 ≠ x0 ∧ DLd d ![x0,x1,x2] b :=
            ⟨hfull.2.1, hfull.2.2.1, hfull.2.2.2.1⟩
          rw [if_pos hfull, if_pos hTT]
          simp only [wtAB, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
            Matrix.tail_cons, Matrix.head_cons, Fin.prod_univ_three]
          ring
        · have hTT : ¬ (x1 ≠ x0 ∧ x2 ≠ x0 ∧ DLd d ![x0,x1,x2] b) :=
            fun h => hfull ⟨hBC.1, h.1, h.2.1, h.2.2, hBC.2⟩
          rw [if_neg hfull, if_neg hTT, mul_zero]
      rw [hsplit]
      exact mul_le_mul_of_nonneg_left
        (TTsum_le_frameG (H := H) (m := m) (d := d) (x0 := x0) hd b)
        (Finset.prod_nonneg (fun k _ => wg_nonneg m x0 (b k)))
    · rw [if_neg hBC]
      have hzero : (∑ x1 ∈ Finset.Icc 1 H, ∑ x2 ∈ Finset.Icc 1 H,
          (if (∀ l : Fin 3, b l ≠ x0) ∧ x1 ≠ x0 ∧ x2 ≠ x0 ∧ DLd d ![x0,x1,x2] b
              ∧ g ∣ ∏ k : Fin 3, del x0 (b k)
            then wtAB m ![x0,x1,x2] b else 0)) = 0 := by
        refine Finset.sum_eq_zero (fun x1 _ => Finset.sum_eq_zero (fun x2 _ => ?_))
        rw [if_neg (fun h => hBC ⟨h.1, h.2.2.2.2⟩)]
      rw [hzero, zero_mul]
  calc (∑ b ∈ box3 H, ∑ x1 ∈ Finset.Icc 1 H, ∑ x2 ∈ Finset.Icc 1 H,
        (if (∀ l : Fin 3, b l ≠ x0) ∧ x1 ≠ x0 ∧ x2 ≠ x0 ∧ DLd d ![x0,x1,x2] b
            ∧ g ∣ ∏ k : Fin 3, del x0 (b k)
          then wtAB m ![x0,x1,x2] b else 0))
      ≤ ∑ b ∈ box3 H, (if (∀ l : Fin 3, b l ≠ x0) ∧ g ∣ ∏ k : Fin 3, del x0 (b k)
          then ∏ k : Fin 3, wg m x0 (b k) else 0) * frameG H m d x0 :=
        Finset.sum_le_sum hinner
    _ = (∑ b ∈ box3 H, (if (∀ l : Fin 3, b l ≠ x0) ∧ g ∣ ∏ k : Fin 3, del x0 (b k)
          then ∏ k : Fin 3, wg m x0 (b k) else 0)) * frameG H m d x0 := by
        rw [Finset.sum_mul]
    _ = bSumBox H m g x0 * frameG H m d x0 := rfl
    _ = frameG H m d x0 * bSumBox H m g x0 := by ring

theorem frameG_sum_le {H m d : ℕ} (hm : 0 < m) (hd : 0 < d) (hmd : Nat.Coprime m d) :
    (∑ x0 ∈ Finset.Icc 1 H, frameG H m d x0)
      ≤ 4 * (3:ℝ) ^ d.primeFactors.card * (((m.divisors.card : ℕ) : ℝ))
          * (((H:ℝ)^3 * ((d.divisors.card : ℕ) : ℝ) / (d:ℝ)) + (H:ℝ)^2) := by
  classical
  have hper : ∀ x0 ∈ Finset.Icc 1 H, frameG H m d x0
      ≤ 4 * (3:ℝ) ^ d.primeFactors.card
          * (((H:ℝ)^2 * ((d.divisors.card : ℕ) : ℝ) / (d:ℝ)) + (H:ℝ))
          * (((m.divisors.card : ℕ) : ℝ)) := by
    intro x0 hx0
    have hbound := a2_sum_bound (m := m) (d := d) (H := H) hm hmd hd x0 hx0
    rw [frameG]
    calc (∑ x ∈ (Finset.Icc 1 H).filter (fun x => x ≠ x0),
          ((Nat.gcd m (del x0 x) : ℕ) : ℝ)
            * ((3:ℝ) ^ d.primeFactors.card * ((H:ℝ) / (frameMod d x0 x : ℝ) + 1)))
        ≤ (3:ℝ) ^ d.primeFactors.card
            * (∑ x ∈ (Finset.Icc 1 H).filter (fun x => x ≠ x0),
              ((Nat.gcd m (del x0 x) : ℕ) : ℝ)
                * ((H:ℝ) * ((Nat.gcd d (del x0 x) : ℕ) : ℝ) * 2 / (d:ℝ) + 1)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_le_sum (fun x _ => ?_)
          have ha := frameMod_arith_two (d := d) (H := H) (a0 := x0) (a1 := x) hd
          have hgcd := mul_le_mul_of_nonneg_left ha
            (by positivity : (0:ℝ) ≤ ((Nat.gcd m (del x0 x) : ℕ) : ℝ))
          calc ((Nat.gcd m (del x0 x) : ℕ) : ℝ)
                * ((3:ℝ) ^ d.primeFactors.card * ((H:ℝ) / (frameMod d x0 x : ℝ) + 1))
              = (3:ℝ) ^ d.primeFactors.card * (((Nat.gcd m (del x0 x) : ℕ) : ℝ)
                  * ((H:ℝ) / (frameMod d x0 x : ℝ) + 1)) := by ring
            _ ≤ (3:ℝ) ^ d.primeFactors.card * (((Nat.gcd m (del x0 x) : ℕ) : ℝ)
                  * ((H:ℝ) * ((Nat.gcd d (del x0 x) : ℕ) : ℝ) * 2 / (d:ℝ) + 1)) :=
                mul_le_mul_of_nonneg_left hgcd (by positivity)
      _ ≤ (3:ℝ) ^ d.primeFactors.card
            * (2 * (∑ x ∈ (Finset.Icc 1 H).filter (fun x => x ≠ x0),
              ((Nat.gcd m (del x0 x) : ℕ) : ℝ)
                * ((H:ℝ) * ((Nat.gcd d (del x0 x) : ℕ) : ℝ) / (d:ℝ) + 1))) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [Finset.mul_sum]
          refine Finset.sum_le_sum (fun x _ => ?_)
          have h2 : (H:ℝ) * ((Nat.gcd d (del x0 x) : ℕ) : ℝ) * 2 / (d:ℝ)
              = 2 * ((H:ℝ) * ((Nat.gcd d (del x0 x) : ℕ) : ℝ) / (d:ℝ)) := by ring
          have hthis : (H:ℝ) * ((Nat.gcd d (del x0 x) : ℕ) : ℝ) * 2 / (d:ℝ) + 1
              ≤ 2 * ((H:ℝ) * ((Nat.gcd d (del x0 x) : ℕ) : ℝ) / (d:ℝ) + 1) := by
            rw [h2]; linarith
          calc ((Nat.gcd m (del x0 x) : ℕ) : ℝ)
                * ((H:ℝ) * ((Nat.gcd d (del x0 x) : ℕ) : ℝ) * 2 / (d:ℝ) + 1)
              ≤ ((Nat.gcd m (del x0 x) : ℕ) : ℝ)
                * (2 * ((H:ℝ) * ((Nat.gcd d (del x0 x) : ℕ) : ℝ) / (d:ℝ) + 1)) :=
                mul_le_mul_of_nonneg_left hthis (Nat.cast_nonneg _)
            _ = 2 * (((Nat.gcd m (del x0 x) : ℕ) : ℝ)
                * ((H:ℝ) * ((Nat.gcd d (del x0 x) : ℕ) : ℝ) / (d:ℝ) + 1)) := by ring
      _ ≤ (3:ℝ) ^ d.primeFactors.card
            * (2 * (2 * (((H:ℝ)^2 * ((d.divisors.card : ℕ) : ℝ) / (d:ℝ)) + (H:ℝ))
              * (((m.divisors.card : ℕ) : ℝ)))) := by
          have hkey : (∑ x ∈ (Finset.Icc 1 H).filter (fun x => x ≠ x0),
                ((Nat.gcd m (del x0 x) : ℕ) : ℝ)
                  * ((H:ℝ) * ((Nat.gcd d (del x0 x) : ℕ) : ℝ) / (d:ℝ) + 1))
              ≤ 2 * (((H:ℝ)^2 * ((d.divisors.card : ℕ) : ℝ) / (d:ℝ)) + (H:ℝ))
                * (((m.divisors.card : ℕ) : ℝ)) := hbound
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hkey (by norm_num : (0:ℝ) ≤ 2)) (by positivity)
      _ = 4 * (3:ℝ) ^ d.primeFactors.card
            * (((H:ℝ)^2 * ((d.divisors.card : ℕ) : ℝ) / (d:ℝ)) + (H:ℝ))
            * (((m.divisors.card : ℕ) : ℝ)) := by ring
  calc (∑ x0 ∈ Finset.Icc 1 H, frameG H m d x0)
      ≤ ∑ _x0 ∈ Finset.Icc 1 H, 4 * (3:ℝ) ^ d.primeFactors.card
          * (((H:ℝ)^2 * ((d.divisors.card : ℕ) : ℝ) / (d:ℝ)) + (H:ℝ))
          * (((m.divisors.card : ℕ) : ℝ)) := Finset.sum_le_sum hper
    _ = (4 * (3:ℝ) ^ d.primeFactors.card
          * (((H:ℝ)^2 * ((d.divisors.card : ℕ) : ℝ) / (d:ℝ)) + (H:ℝ))
          * (((m.divisors.card : ℕ) : ℝ))) * ((Finset.Icc 1 H).card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        ring
    _ = 4 * (3:ℝ) ^ d.primeFactors.card * (((m.divisors.card : ℕ) : ℝ))
          * (((H:ℝ)^3 * ((d.divisors.card : ℕ) : ℝ) / (d:ℝ)) + (H:ℝ)^2) := by
        rw [Nat.card_Icc, Nat.add_sub_cancel]
        push_cast
        ring

theorem rhs_step {H m d g : ℕ} (hm : 0 < m) (hd : 0 < d) (hg : 0 < g) :
    32 * (3:ℝ)^d.primeFactors.card * (((g.divisors.card:ℕ):ℝ))^2
        * (((m.divisors.card:ℕ):ℝ))^4
        * ((((d.divisors.card:ℕ):ℝ) * ((H:ℝ)^6/((d:ℝ)*(g:ℝ))) + (H:ℝ)^5/(g:ℝ)))
      ≤ rhsC 30000 H m d g := by
  rw [rhsC]
  have htau := tau_three_pow_le hm hd hg
  have hX1 : (0:ℝ) ≤ (H:ℝ)^6/((d:ℝ)*(g:ℝ)) := by positivity
  have hX2 : (0:ℝ) ≤ (H:ℝ)^5/(g:ℝ) := by positivity
  have hTd1 : (1:ℝ) ≤ ((d.divisors.card:ℕ):ℝ) := by
    have h1 : 1 ≤ d.divisors.card :=
      Nat.one_le_iff_ne_zero.mpr (Finset.card_ne_zero.mpr
        ⟨1, by rw [Nat.mem_divisors]; exact ⟨one_dvd d, ne_of_gt hd⟩⟩)
    exact_mod_cast h1
  have hcoef : 32 * (3:ℝ)^d.primeFactors.card * (((g.divisors.card:ℕ):ℝ))^2
        * (((m.divisors.card:ℕ):ℝ))^4
      ≤ 32 * (3:ℝ)^d.primeFactors.card * (((d.divisors.card:ℕ):ℝ))
        * (((g.divisors.card:ℕ):ℝ))^2 * (((m.divisors.card:ℕ):ℝ))^4 := by
    have h0 : (0:ℝ) ≤ 32 * (3:ℝ)^d.primeFactors.card * (((g.divisors.card:ℕ):ℝ))^2
        * (((m.divisors.card:ℕ):ℝ))^4 := by positivity
    calc 32 * (3:ℝ)^d.primeFactors.card * (((g.divisors.card:ℕ):ℝ))^2
          * (((m.divisors.card:ℕ):ℝ))^4
        = (32 * (3:ℝ)^d.primeFactors.card * (((g.divisors.card:ℕ):ℝ))^2
            * (((m.divisors.card:ℕ):ℝ))^4) * 1 := by ring
      _ ≤ (32 * (3:ℝ)^d.primeFactors.card * (((g.divisors.card:ℕ):ℝ))^2
            * (((m.divisors.card:ℕ):ℝ))^4) * ((d.divisors.card:ℕ):ℝ) :=
          mul_le_mul_of_nonneg_left hTd1 h0
      _ = 32 * (3:ℝ)^d.primeFactors.card * (((d.divisors.card:ℕ):ℝ))
            * (((g.divisors.card:ℕ):ℝ))^2 * (((m.divisors.card:ℕ):ℝ))^4 := by ring
  have h1 : 32 * (3:ℝ)^d.primeFactors.card * (((g.divisors.card:ℕ):ℝ))^2
        * (((m.divisors.card:ℕ):ℝ))^4
        * (((d.divisors.card:ℕ):ℝ) * ((H:ℝ)^6/((d:ℝ)*(g:ℝ))))
      ≤ 30000 * ((((m*d*g).divisors.card:ℕ):ℝ))^8 * ((H:ℝ)^6/((d:ℝ)*(g:ℝ))) := by
    calc 32 * (3:ℝ)^d.primeFactors.card * (((g.divisors.card:ℕ):ℝ))^2
          * (((m.divisors.card:ℕ):ℝ))^4
          * (((d.divisors.card:ℕ):ℝ) * ((H:ℝ)^6/((d:ℝ)*(g:ℝ))))
        = (32 * (3:ℝ)^d.primeFactors.card * (((d.divisors.card:ℕ):ℝ))
            * (((g.divisors.card:ℕ):ℝ))^2 * (((m.divisors.card:ℕ):ℝ))^4)
          * ((H:ℝ)^6/((d:ℝ)*(g:ℝ))) := by ring
      _ ≤ (30000 * ((((m*d*g).divisors.card:ℕ):ℝ))^8)
            * ((H:ℝ)^6/((d:ℝ)*(g:ℝ))) := mul_le_mul_of_nonneg_right htau hX1
      _ = 30000 * ((((m*d*g).divisors.card:ℕ):ℝ))^8 * ((H:ℝ)^6/((d:ℝ)*(g:ℝ))) := by ring
  have h2 : 32 * (3:ℝ)^d.primeFactors.card * (((g.divisors.card:ℕ):ℝ))^2
        * (((m.divisors.card:ℕ):ℝ))^4 * ((H:ℝ)^5/(g:ℝ))
      ≤ 30000 * ((((m*d*g).divisors.card:ℕ):ℝ))^8 * ((H:ℝ)^5/(g:ℝ)) :=
    mul_le_mul_of_nonneg_right (hcoef.trans htau) hX2
  calc 32 * (3:ℝ)^d.primeFactors.card * (((g.divisors.card:ℕ):ℝ))^2
        * (((m.divisors.card:ℕ):ℝ))^4
        * ((((d.divisors.card:ℕ):ℝ) * ((H:ℝ)^6/((d:ℝ)*(g:ℝ))) + (H:ℝ)^5/(g:ℝ)))
      = 32 * (3:ℝ)^d.primeFactors.card * (((g.divisors.card:ℕ):ℝ))^2
          * (((m.divisors.card:ℕ):ℝ))^4
          * (((d.divisors.card:ℕ):ℝ) * ((H:ℝ)^6/((d:ℝ)*(g:ℝ))))
        + 32 * (3:ℝ)^d.primeFactors.card * (((g.divisors.card:ℕ):ℝ))^2
          * (((m.divisors.card:ℕ):ℝ))^4 * ((H:ℝ)^5/(g:ℝ)) := by ring
    _ ≤ 30000 * ((((m*d*g).divisors.card:ℕ):ℝ))^8 * ((H:ℝ)^6/((d:ℝ)*(g:ℝ)))
          + 30000 * ((((m*d*g).divisors.card:ℕ):ℝ))^8 * ((H:ℝ)^5/(g:ℝ)) := add_le_add h1 h2
    _ = 30000 * ((((m*d*g).divisors.card:ℕ):ℝ))^8
          * ((H:ℝ)^6/((d:ℝ)*(g:ℝ)) + (H:ℝ)^5/(g:ℝ)) := by ring

theorem sumI_le_own {H m d g : ℕ} (hm : Squarefree m) (hmd : Nat.Coprime m d)
    (hmg : Nat.Coprime m g) (hd : 0 < d) (hg : 0 < g) :
    sumI H m d g ≤ rhsC 30000 H m d g := by
  have hm0 : 0 < m := Nat.pos_of_ne_zero hm.ne_zero
  have hS := SIframe_le H m d g hd
  have hF := frameG_sum_le (H := H) (m := m) (d := d) hm0 hd hmd
  have hB : ∀ x0 ∈ Finset.Icc 1 H, bSumBox H m g x0
      ≤ 8 * (((g.divisors.card:ℕ):ℝ))^2 * ((H:ℝ)^3/(g:ℝ))
          * (((m.divisors.card:ℕ):ℝ))^3 :=
    fun x0 hx0 => Work.LinnikBurgess.sumI_aux.bSumBox_le (m := m) (g := g) (H := H) hm0 hmg hg hx0
  have hSB : SIframe H m d g
      ≤ (8 * (((g.divisors.card:ℕ):ℝ))^2 * ((H:ℝ)^3/(g:ℝ))
          * (((m.divisors.card:ℕ):ℝ))^3) * (∑ x0 ∈ Finset.Icc 1 H, frameG H m d x0) := by
    calc SIframe H m d g
        ≤ ∑ x0 ∈ Finset.Icc 1 H, frameG H m d x0 * bSumBox H m g x0 := hS
      _ ≤ ∑ x0 ∈ Finset.Icc 1 H, frameG H m d x0
            * (8 * (((g.divisors.card:ℕ):ℝ))^2 * ((H:ℝ)^3/(g:ℝ))
                * (((m.divisors.card:ℕ):ℝ))^3) :=
          Finset.sum_le_sum (fun x0 hx0 =>
            mul_le_mul_of_nonneg_left (hB x0 hx0) (frameG_nonneg H m d x0))
      _ = (∑ x0 ∈ Finset.Icc 1 H, frameG H m d x0)
            * (8 * (((g.divisors.card:ℕ):ℝ))^2 * ((H:ℝ)^3/(g:ℝ))
                * (((m.divisors.card:ℕ):ℝ))^3) := by
          rw [Finset.sum_mul]
      _ = (8 * (((g.divisors.card:ℕ):ℝ))^2 * ((H:ℝ)^3/(g:ℝ))
            * (((m.divisors.card:ℕ):ℝ))^3) * (∑ x0 ∈ Finset.Icc 1 H, frameG H m d x0) := by
          ring
  have hmain : SIframe H m d g
      ≤ 32 * (3:ℝ)^d.primeFactors.card * (((g.divisors.card:ℕ):ℝ))^2
          * (((m.divisors.card:ℕ):ℝ))^4
          * ((((d.divisors.card:ℕ):ℝ) * ((H:ℝ)^6/((d:ℝ)*(g:ℝ))) + (H:ℝ)^5/(g:ℝ))) := by
    calc SIframe H m d g
        ≤ (8 * (((g.divisors.card:ℕ):ℝ))^2 * ((H:ℝ)^3/(g:ℝ))
            * (((m.divisors.card:ℕ):ℝ))^3) * (∑ x0 ∈ Finset.Icc 1 H, frameG H m d x0) := hSB
      _ ≤ (8 * (((g.divisors.card:ℕ):ℝ))^2 * ((H:ℝ)^3/(g:ℝ))
            * (((m.divisors.card:ℕ):ℝ))^3)
          * (4 * (3:ℝ)^d.primeFactors.card * (((m.divisors.card:ℕ):ℝ))
              * (((H:ℝ)^3 * ((d.divisors.card:ℕ):ℝ) / (d:ℝ)) + (H:ℝ)^2)) :=
          mul_le_mul_of_nonneg_left hF (by positivity)
      _ = 32 * (3:ℝ)^d.primeFactors.card * (((g.divisors.card:ℕ):ℝ))^2
            * (((m.divisors.card:ℕ):ℝ))^4
            * ((((d.divisors.card:ℕ):ℝ) * ((H:ℝ)^6/((d:ℝ)*(g:ℝ))) + (H:ℝ)^5/(g:ℝ))) := by
          ring
  exact (sumI_le_SIframe H m d g).trans (hmain.trans (rhs_step hm0 hd hg))

end Work.LinnikAreas
