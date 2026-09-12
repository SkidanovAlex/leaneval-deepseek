import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Data.Int.Star
import Mathlib.Data.Int.SuccPred

open scoped BigOperators
set_option maxHeartbeats 600000

namespace Commons.Analysis.Interval

noncomputable section

/-- count of `t ∈ N` where `|f t - g (t+y)| ≥ κ/2` -/
private def cntBad (f g : ℤ → ℝ) (κ : ℝ) (N : Finset ℤ) (y : ℤ) : ℕ :=
  (N.filter (fun t : ℤ => κ / 2 ≤ |f t - g (t + y)|)).card

/-- count of `t ∈ N` where `g (t+y) ≤ w` -/
private def cntLow (g : ℤ → ℝ) (w : ℝ) (N : Finset ℤ) (y : ℤ) : ℕ :=
  (N.filter (fun t : ℤ => g (t + y) ≤ w)).card

lemma Icc_translate_image (a b q : ℤ) :
    Finset.Icc (q + a) (q + b) = (Finset.Icc a b).image (fun t : ℤ => t + q) := by
  ext s
  rw [Finset.mem_Icc, Finset.mem_image]
  constructor
  · intro h
    refine ⟨s - q, ?_, ?_⟩
    · rw [Finset.mem_Icc]
      omega
    · omega
  · rintro ⟨t, ht, rfl⟩
    rw [Finset.mem_Icc] at ht
    omega

lemma card_filter_image_translate (N : Finset ℤ) (q : ℤ) (p : ℤ → Prop) [DecidablePred p] :
    ((N.image (fun t : ℤ => t + q)).filter p).card = (N.filter (fun t : ℤ => p (t + q))).card := by
  rw [Finset.filter_image]
  have hinj : Function.Injective (fun t : ℤ => t + q) := by
    intro x y h
    exact add_right_cancel h
  rw [Finset.card_image_of_injective _ hinj]

lemma sum_mem_union_Icc (a b minQ maxQ t i : ℤ)
    (hta : a ≤ t) (htb : t ≤ b) (hmin : minQ ≤ i) (hmax : i ≤ maxQ)
    (hspan : maxQ - minQ ≤ b - a) :
    t + i ∈ Finset.Icc (minQ + a) (minQ + b) ∨
      t + i ∈ Finset.Icc (maxQ + a) (maxQ + b) := by
  rcases le_or_gt (t + i) (minQ + b) with h | h
  · left
    rw [Finset.mem_Icc]
    constructor <;> omega
  · right
    rw [Finset.mem_Icc]
    constructor <;> omega

/-- double counting: summing left-fibers equals summing right-fibers -/
lemma sum_card_left_eq_sum_card_right {A B : Finset ℤ} (r : ℤ → ℤ → Prop) [DecidableRel r] :
    (∑ a ∈ A, ((B.filter (fun b => r a b)).card : ℝ)) =
      (∑ b ∈ B, ((A.filter (fun a => r a b)).card : ℝ)) := by
  calc
    (∑ a ∈ A, ((B.filter (fun b => r a b)).card : ℝ))
        = (∑ a ∈ A, ∑ b ∈ B, if r a b then (1 : ℝ) else 0) := by
          apply Finset.sum_congr rfl
          intro a ha
          exact (Finset.sum_boole (fun b : ℤ => r a b) B).symm
    _ = (∑ b ∈ B, ∑ a ∈ A, if r a b then (1 : ℝ) else 0) := by
          exact Finset.sum_comm
    _ = (∑ b ∈ B, ((A.filter (fun a => r a b)).card : ℝ)) := by
          apply Finset.sum_congr rfl
          intro b hb
          exact Finset.sum_boole (fun a : ℤ => r a b) A

/-- Per-block estimate. -/
lemma aux_averaging_count_block {f g : ℤ → ℝ} {κ δ : ℝ} (hκ : 0 < κ) (hδ : 0 < δ)
    (hδ12 : δ < 1 / 2) (a b c₀ d₀ : ℤ) (I₁ I₂ I₃ : Finset ℤ)
    (hpart : ∀ t : ℤ, t ∈ Finset.Icc a b ↔ t ∈ I₁ ∨ t ∈ I₂ ∨ t ∈ I₃)
    (hI3lo : δ * ((Finset.Icc a b).card : ℝ) / 2 ≤ (I₃.card : ℝ))
    (hI3hi : (I₃.card : ℝ) ≤ δ * ((Finset.Icc a b).card : ℝ))
    (hI2 : (I₂.card : ℝ) ≤ δ * ((Finset.Icc a b).card : ℝ))
    (hsep : ∀ t₁ : ℤ, t₁ ∈ I₁ → ∀ t₃ : ℤ, t₃ ∈ I₃ → f t₃ + κ ≤ f t₁)
    (hblk : (Finset.Icc c₀ d₀).card ≤ (Finset.Icc a b).card) :
    (((Finset.Icc c₀ d₀).filter (fun y : ℤ =>
        ((((Finset.Icc a b).filter (fun t : ℤ => |f t - g (t + y)| ≥ κ / 2)).card : ℝ) <
          δ * ((Finset.Icc a b).card : ℝ) / 4))).card : ℝ)
      ≤ 32 * δ * ((Finset.Icc a b).card : ℝ) := by
  classical
  set N : Finset ℤ := Finset.Icc a b with hN
  set n : ℕ := N.card with hn
  change (((Finset.Icc c₀ d₀).filter (fun y : ℤ =>
      (cntBad f g κ N y : ℝ) < δ * (n : ℝ) / 4)).card : ℝ) ≤ 32 * δ * (n : ℝ)
  have hpartN : ∀ t : ℤ, t ∈ N ↔ t ∈ I₁ ∨ t ∈ I₂ ∨ t ∈ I₃ := by simpa [hN] using hpart
  have hI3loN : δ * (n : ℝ) / 2 ≤ (I₃.card : ℝ) := by simpa [hN, hn] using hI3lo
  have hI3hiN : (I₃.card : ℝ) ≤ δ * (n : ℝ) := by simpa [hN, hn] using hI3hi
  have hI2N : (I₂.card : ℝ) ≤ δ * (n : ℝ) := by simpa [hN, hn] using hI2
  have hblkN : (Finset.Icc c₀ d₀).card ≤ n := by simpa [hN, hn] using hblk
  by_cases hn0 : n = 0
  · have hNempty : N = ∅ := Finset.card_eq_zero.mp (by simpa [hn] using hn0)
    have hcond : ∀ y : ℤ, ¬ (cntBad f g κ N y : ℝ) < δ * (n : ℝ) / 4 := by
      intro y
      rw [hn0]
      simp [cntBad, hNempty]
    have hfil : (Finset.Icc c₀ d₀).filter (fun y : ℤ =>
        (cntBad f g κ N y : ℝ) < δ * (n : ℝ) / 4) = ∅ := by
      ext y
      simp [hcond y]
    rw [hfil]
    simp [hn0]
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
    have hnposR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
    have hNne : N.Nonempty := Finset.card_pos.mp (by simpa [hn] using hnpos)
    let B : Finset ℤ := Finset.Icc c₀ d₀
    have hBlkB : B.card ≤ n := by simpa [B] using hblkN
    have hI1sub : I₁ ⊆ N := by
      intro t ht
      exact (hpartN t).2 (Or.inl ht)
    have hI2sub : I₂ ⊆ N := by
      intro t ht
      exact (hpartN t).2 (Or.inr (Or.inl ht))
    have hI3sub : I₃ ⊆ N := by
      intro t ht
      exact (hpartN t).2 (Or.inr (Or.inr ht))
    have hI3pos : (0 : ℝ) < (I₃.card : ℝ) := by
      have h1 : (0 : ℝ) < δ * (n : ℝ) / 2 := by positivity
      linarith
    have hI3ne : I₃.Nonempty := Finset.card_pos.mp (by exact_mod_cast hI3pos)
    have hsum : (n : ℝ) ≤ (I₁.card : ℝ) + (I₂.card : ℝ) + (I₃.card : ℝ) := by
      have hcov : N ⊆ I₁ ∪ I₂ ∪ I₃ := by
        intro t ht
        simpa [Finset.mem_union, or_assoc] using (hpartN t).1 ht
      have hN1 : N.card ≤ (I₁ ∪ I₂ ∪ I₃).card := Finset.card_le_card hcov
      have h2 : (I₁ ∪ I₂ ∪ I₃).card ≤ (I₁ ∪ I₂).card + I₃.card :=
        Finset.card_union_le (I₁ ∪ I₂) I₃
      have h3 : (I₁ ∪ I₂).card ≤ I₁.card + I₂.card := Finset.card_union_le I₁ I₂
      calc
        (n : ℝ) = (N.card : ℝ) := by rw [hn]
        _ ≤ ((I₁ ∪ I₂ ∪ I₃).card : ℝ) := by exact_mod_cast hN1
        _ ≤ ((I₁ ∪ I₂).card : ℝ) + (I₃.card : ℝ) := by exact_mod_cast h2
        _ ≤ (I₁.card : ℝ) + (I₂.card : ℝ) + (I₃.card : ℝ) := by
          have h3r : ((I₁ ∪ I₂).card : ℝ) ≤ (I₁.card : ℝ) + (I₂.card : ℝ) := by
            exact_mod_cast h3
          nlinarith
    have hI1big : (n : ℝ) - (I₂.card : ℝ) - (I₃.card : ℝ) ≤ (I₁.card : ℝ) := by
      nlinarith [hsum]
    have hI1pos : (0 : ℝ) < (I₁.card : ℝ) := by
      have hbd : (n : ℝ) * (1 - 2 * δ) ≤ (I₁.card : ℝ) := by
        nlinarith [hI1big, hI2N, hI3hiN]
      have hposbd : (0 : ℝ) < (n : ℝ) * (1 - 2 * δ) := by
        have h12 : 0 < 1 - 2 * δ := by nlinarith [hδ12]
        nlinarith
      nlinarith
    have hI1ne : I₁.Nonempty := Finset.card_pos.mp (by exact_mod_cast hI1pos)
    let w₁ : ℝ := (I₁.image f).min' (hI1ne.image f)
    let w₃ : ℝ := (I₃.image f).max' (hI3ne.image f)
    have hw1 : ∀ t₁ : ℤ, t₁ ∈ I₁ → w₁ ≤ f t₁ := by
      intro t₁ ht₁
      change (I₁.image f).min' (hI1ne.image f) ≤ f t₁
      exact Finset.min'_le (I₁.image f) (f t₁) (Finset.mem_image.mpr ⟨t₁, ht₁, rfl⟩)
    have hw3 : ∀ t₃ : ℤ, t₃ ∈ I₃ → f t₃ ≤ w₃ := by
      intro t₃ ht₃
      change f t₃ ≤ (I₃.image f).max' (hI3ne.image f)
      exact Finset.le_max' (I₃.image f) (f t₃) (Finset.mem_image.mpr ⟨t₃, ht₃, rfl⟩)
    have hw1mem : w₁ ∈ I₁.image f := by
      change (I₁.image f).min' (hI1ne.image f) ∈ I₁.image f
      exact Finset.min'_mem (I₁.image f) (hI1ne.image f)
    have hw3mem : w₃ ∈ I₃.image f := by
      change (I₃.image f).max' (hI3ne.image f) ∈ I₃.image f
      exact Finset.max'_mem (I₃.image f) (hI3ne.image f)
    have hw13 : w₃ + κ ≤ w₁ := by
      rcases Finset.mem_image.mp hw1mem with ⟨t₁, ht₁, hft₁⟩
      rcases Finset.mem_image.mp hw3mem with ⟨t₃, ht₃, hft₃⟩
      have h := hsep t₁ ht₁ t₃ ht₃
      rw [← hft₁, ← hft₃]
      exact h
    let w : ℝ := (w₁ + w₃) / 2
    have hw13mid : w₃ + κ / 2 ≤ w := by
      dsimp [w]
      nlinarith [hw13]
    have hw13mid' : w ≤ w₁ - κ / 2 := by
      dsimp [w]
      nlinarith [hw13]
    let BadSet : Finset ℤ := B.filter (fun y : ℤ =>
        (cntBad f g κ N y : ℝ) < δ * (n : ℝ) / 4)
    let Q : Finset ℤ := B.filter (fun y : ℤ =>
        (cntLow g w N y : ℝ) ≤ 4 * δ * (n : ℝ))
    -- 1. bad points of B belong to Q
    have hbad_in_Q : ∀ y : ℤ, y ∈ B →
        (cntBad f g κ N y : ℝ) < δ * (n : ℝ) / 4 →
        (cntLow g w N y : ℝ) ≤ 4 * δ * (n : ℝ) := by
      intro y hyB hybad
      by_contra hnot
      have hLowBig : 4 * δ * (n : ℝ) < (cntLow g w N y : ℝ) := by
        exact lt_of_not_ge hnot
      let A : Finset ℤ := N.filter (fun t : ℤ => g (t + y) ≤ w)
      let A0 : Finset ℤ := A.filter (fun t : ℤ => t ∉ I₂ ∪ I₃)
      let X : Finset ℤ := I₂ ∪ I₃
      have hA0subBad : A0 ⊆ N.filter (fun t : ℤ => κ / 2 ≤ |f t - g (t + y)|) := by
        intro t htA0
        have htA : t ∈ A := (Finset.mem_filter.mp htA0).1
        have htnot : t ∉ I₂ ∪ I₃ := (Finset.mem_filter.mp htA0).2
        have htN : t ∈ N := (Finset.mem_filter.mp htA).1
        have hgt : g (t + y) ≤ w := (Finset.mem_filter.mp htA).2
        have htI1 : t ∈ I₁ := by
          rcases (hpartN t).1 htN with h1 | h2 | h3
          · exact h1
          · exfalso; exact htnot (Finset.mem_union.mpr (Or.inl h2))
          · exfalso; exact htnot (Finset.mem_union.mpr (Or.inr h3))
        have hfg : κ / 2 ≤ f t - g (t + y) := by
          have hw1t := hw1 t htI1
          nlinarith [hw1t, hgt, hw13mid']
        have hfg0 : 0 ≤ f t - g (t + y) := by
          have hw1t := hw1 t htI1
          nlinarith [hw1t, hgt, hw13mid']
        rw [Finset.mem_filter]
        rw [abs_of_nonneg hfg0]
        exact ⟨htN, hfg⟩
      have hA0le : (A.card : ℝ) ≤ (A0.card : ℝ) + (I₂.card : ℝ) + (I₃.card : ℝ) := by
        have hAcov : A ⊆ A0 ∪ X := by
          intro t htA
          by_cases htX : t ∈ X
          · exact Finset.mem_union.mpr (Or.inr htX)
          · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨htA, htX⟩))
        have hA1 : A.card ≤ (A0 ∪ X).card := Finset.card_le_card hAcov
        have hA2 : (A0 ∪ X).card ≤ A0.card + X.card := Finset.card_union_le A0 X
        have hX : (X.card : ℝ) ≤ (I₂.card : ℝ) + (I₃.card : ℝ) := by
          have hXu := Finset.card_union_le I₂ I₃
          exact_mod_cast hXu
        calc
          (A.card : ℝ) ≤ ((A0 ∪ X).card : ℝ) := by exact_mod_cast hA1
          _ ≤ (A0.card : ℝ) + (X.card : ℝ) := by exact_mod_cast hA2
          _ ≤ (A0.card : ℝ) + (I₂.card : ℝ) + (I₃.card : ℝ) := by
            nlinarith
      have hcB : (A0.card : ℝ) ≤ (cntBad f g κ N y : ℝ) := by
        have := Finset.card_le_card hA0subBad
        exact_mod_cast this
      have hcontra : 2 * δ * (n : ℝ) < (cntBad f g κ N y : ℝ) := by
        have hL : (cntLow g w N y : ℝ) = (A.card : ℝ) := by rfl
        nlinarith [hLowBig, hA0le, hcB, hI2N, hI3hiN, hL]
      nlinarith [hybad, hcontra]
    have hBadQ : BadSet ⊆ Q := by
      intro y hy
      rcases Finset.mem_filter.mp hy with ⟨hyB, hybad⟩
      exact Finset.mem_filter.mpr ⟨hyB, hbad_in_Q y hyB hybad⟩
    by_cases hQempty : Q = ∅
    · have hBadEmpty : BadSet = ∅ := by
        apply Finset.subset_empty.mp
        simpa [hQempty] using hBadQ
      change (BadSet.card : ℝ) ≤ 32 * δ * (n : ℝ)
      rw [hBadEmpty]
      simp
      have hz : (0 : ℝ) ≤ 32 * δ * (n : ℝ) := by
        have h1 : (0 : ℝ) ≤ 32 * δ := by nlinarith [hδ]
        exact mul_nonneg h1 (by exact_mod_cast Nat.zero_le n)
      simpa using hz
    · have hQcard : 0 < Q.card := by
        by_contra h
        have hc : Q.card = 0 := by omega
        exact hQempty (Finset.card_eq_zero.mp hc)
      have hQne : Q.Nonempty := Finset.card_pos.mp hQcard
      have hQsubB : Q ⊆ B := by
        intro y hy
        exact (Finset.mem_filter.mp hy).1
      let minQ : ℤ := Q.min' hQne
      let maxQ : ℤ := Q.max' hQne
      have hminQmem : minQ ∈ Q := by
        change Q.min' hQne ∈ Q
        exact Finset.min'_mem Q hQne
      have hmaxQmem : maxQ ∈ Q := by
        change Q.max' hQne ∈ Q
        exact Finset.max'_mem Q hQne
      have hminQle : minQ ≤ maxQ := by
        change Q.min' hQne ≤ Q.max' hQne
        exact Finset.min'_le Q (Q.max' hQne) hmaxQmem
      have hminB : minQ ∈ B := hQsubB hminQmem
      have hmaxB : maxQ ∈ B := hQsubB hmaxQmem
      have hminQlow : (cntLow g w N minQ : ℝ) ≤ 4 * δ * (n : ℝ) :=
        (Finset.mem_filter.mp hminQmem).2
      have hmaxQlow : (cntLow g w N maxQ : ℝ) ≤ 4 * δ * (n : ℝ) :=
        (Finset.mem_filter.mp hmaxQmem).2
      let S : Finset ℤ := Finset.Icc minQ maxQ
      have hQsubS : Q ⊆ S := by
        intro y hy
        rw [Finset.mem_Icc]
        constructor
        · change Q.min' hQne ≤ y
          exact Finset.min'_le Q y hy
        · change y ≤ Q.max' hQne
          exact Finset.le_max' Q y hy
      have hSsubB : S ⊆ B := by
        intro z hz
        rw [Finset.mem_Icc] at hz
        rcases Finset.mem_Icc.mp hminB with ⟨hcmin, hminb⟩
        rcases Finset.mem_Icc.mp hmaxB with ⟨hc', hmaxd⟩
        rw [Finset.mem_Icc]
        constructor <;> omega
      have hSleB : S.card ≤ B.card := Finset.card_le_card hSsubB
      have hSleN : S.card ≤ N.card := by
        exact le_trans hSleB (by simpa [B, hn] using hblkN)
      have hSleNcast : (S.card : ℤ) ≤ (N.card : ℤ) := by exact_mod_cast hSleN
      have hab : a ≤ b := by
        rcases hNne with ⟨x, hx⟩
        rw [hN] at hx
        exact (Finset.mem_Icc.mp hx).1.trans (Finset.mem_Icc.mp hx).2
      have hconv : ((maxQ + 1 - minQ).toNat : ℤ) ≤ ((b + 1 - a).toNat : ℤ) := by
        calc
          ((maxQ + 1 - minQ).toNat : ℤ) = (S.card : ℤ) := by
            rw [Int.card_Icc]
          _ ≤ (N.card : ℤ) := hSleNcast
          _ = ((b + 1 - a).toNat : ℤ) := by
            rw [hN, Int.card_Icc]
      have hspanZ : maxQ + 1 - minQ ≤ b + 1 - a := by
        have hn1a : 0 ≤ maxQ + 1 - minQ := by omega
        have hn1b : 0 ≤ b + 1 - a := by omega
        have := hconv
        rw [Int.toNat_of_nonneg hn1a, Int.toNat_of_nonneg hn1b] at this
        exact this
      have hspan : maxQ - minQ ≤ b - a := by omega
      let U : Finset ℤ := Finset.Icc (minQ + a) (minQ + b) ∪ Finset.Icc (maxQ + a) (maxQ + b)
      let V : Finset ℤ := U.filter (fun s : ℤ => g s ≤ w)
      have hVle : (V.card : ℝ) ≤ 8 * δ * (n : ℝ) := by
        have hA : ((Finset.Icc (minQ + a) (minQ + b)).filter (fun s : ℤ => g s ≤ w)).card =
            cntLow g w N minQ := by
          unfold cntLow
          calc
            ((Finset.Icc (minQ + a) (minQ + b)).filter (fun s : ℤ => g s ≤ w)).card
                = ((N.image (fun t : ℤ => t + minQ)).filter (fun s : ℤ => g s ≤ w)).card := by
                  rw [Icc_translate_image a b minQ]
            _ = (N.filter (fun t : ℤ => g (t + minQ) ≤ w)).card := by
                  exact card_filter_image_translate N minQ (fun s : ℤ => g s ≤ w)
        have hB : ((Finset.Icc (maxQ + a) (maxQ + b)).filter (fun s : ℤ => g s ≤ w)).card =
            cntLow g w N maxQ := by
          unfold cntLow
          calc
            ((Finset.Icc (maxQ + a) (maxQ + b)).filter (fun s : ℤ => g s ≤ w)).card
                = ((N.image (fun t : ℤ => t + maxQ)).filter (fun s : ℤ => g s ≤ w)).card := by
                  rw [Icc_translate_image a b maxQ]
            _ = (N.filter (fun t : ℤ => g (t + maxQ) ≤ w)).card := by
                  exact card_filter_image_translate N maxQ (fun s : ℤ => g s ≤ w)
        have hsplit : V.card ≤
            ((Finset.Icc (minQ + a) (minQ + b)).filter (fun s : ℤ => g s ≤ w)).card +
            ((Finset.Icc (maxQ + a) (maxQ + b)).filter (fun s : ℤ => g s ≤ w)).card := by
          calc
            V.card = (U.filter (fun s : ℤ => g s ≤ w)).card := by rfl
            _ = ((Finset.Icc (minQ + a) (minQ + b)).filter (fun s : ℤ => g s ≤ w) ∪
                  (Finset.Icc (maxQ + a) (maxQ + b)).filter (fun s : ℤ => g s ≤ w)).card := by
                  dsimp [U]
                  rw [Finset.filter_union]
            _ ≤ ((Finset.Icc (minQ + a) (minQ + b)).filter (fun s : ℤ => g s ≤ w)).card +
                  ((Finset.Icc (maxQ + a) (maxQ + b)).filter (fun s : ℤ => g s ≤ w)).card := by
                  exact Finset.card_union_le _ _
        calc
          (V.card : ℝ) ≤ (((Finset.Icc (minQ + a) (minQ + b)).filter (fun s : ℤ => g s ≤ w)).card : ℝ) +
                ((Finset.Icc (maxQ + a) (maxQ + b)).filter (fun s : ℤ => g s ≤ w)).card := by
              exact_mod_cast hsplit
          _ = (cntLow g w N minQ : ℝ) + (cntLow g w N maxQ : ℝ) := by rw [hA, hB]
          _ ≤ 8 * δ * (n : ℝ) := by nlinarith [hminQlow, hmaxQlow]
      -- per-t bound b_t ≤ V
      have hbtleV : ∀ t : ℤ, t ∈ I₃ →
          (S.filter (fun i : ℤ => g (t + i) ≤ w)).card ≤ V.card := by
        intro t ht
        have hmap : (S.filter (fun i : ℤ => g (t + i) ≤ w)).card =
            ((S.filter (fun i : ℤ => g (t + i) ≤ w)).image (fun i : ℤ => t + i)).card := by
          exact (Finset.card_image_of_injective
            (S.filter (fun i : ℤ => g (t + i) ≤ w))
            (by intro x y hxy; exact add_left_cancel hxy)).symm
        rw [hmap]
        apply Finset.card_le_card
        intro s hs
        rcases Finset.mem_image.mp hs with ⟨i, hi, hsi⟩
        subst s
        have hiS : i ∈ S := (Finset.mem_filter.mp hi).1
        have hlow : g (t + i) ≤ w := (Finset.mem_filter.mp hi).2
        have htN : t ∈ N := hI3sub ht
        have htab : a ≤ t ∧ t ≤ b := Finset.mem_Icc.mp (by simpa [hN] using htN)
        rw [Finset.mem_filter]
        constructor
        · dsimp [U]
          rw [Finset.mem_union]
          rcases Finset.mem_Icc.mp hiS with ⟨hminQle_i, h_i_le_maxQ⟩
          rcases sum_mem_union_Icc a b minQ maxQ t i htab.1 htab.2 hminQle_i h_i_le_maxQ hspan with hu | hu
          · exact Or.inl hu
          · exact Or.inr hu
        · exact hlow
      -- S' bound
      let S' : Finset ℤ := S.filter (fun i : ℤ =>
          δ * (n : ℝ) / 4 < (cntLow g w I₃ i : ℝ))
      have hS'subS : S' ⊆ S := by
        intro i hi
        exact (Finset.mem_filter.mp hi).1
      -- (a) for i ∈ S \ S': countBad is not small
      have hSnotS' : ∀ i : ℤ, i ∈ S → i ∉ S' →
          ¬ (cntBad f g κ N i : ℝ) < δ * (n : ℝ) / 4 := by
        intro i hiS hiS'
        have hlowSmall : (cntLow g w I₃ i : ℝ) ≤ δ * (n : ℝ) / 4 := by
          have : ¬ (δ * (n : ℝ) / 4 < (cntLow g w I₃ i : ℝ)) := by
            intro h
            apply hiS'
            exact Finset.mem_filter.mpr ⟨hiS, h⟩
          exact le_of_not_gt this
        have hHighSub : (I₃.filter (fun t : ℤ => w < g (t + i))) ⊆
            N.filter (fun t : ℤ => κ / 2 ≤ |f t - g (t + i)|) := by
          intro t htHigh
          have htI3 : t ∈ I₃ := (Finset.mem_filter.mp htHigh).1
          have hgt : w < g (t + i) := (Finset.mem_filter.mp htHigh).2
          have htN : t ∈ N := hI3sub htI3
          have hfg : κ / 2 ≤ g (t + i) - f t := by
            have hw3t := hw3 t htI3
            nlinarith [hw3t, hgt, hw13mid]
          have hfg0 : 0 ≤ g (t + i) - f t := by nlinarith [hfg, hκ]
          have hfgabs : κ / 2 ≤ |g (t + i) - f t| := by
            rw [abs_of_nonneg hfg0]
            exact hfg
          rw [abs_sub_comm] at hfgabs
          exact Finset.mem_filter.mpr ⟨htN, hfgabs⟩
        have hcntHigh : ((I₃.filter (fun t : ℤ => w < g (t + i))).card : ℝ) =
            (I₃.card : ℝ) - (cntLow g w I₃ i : ℝ) := by
          have hnot_eq : I₃.filter (fun t : ℤ => w < g (t + i)) =
              I₃.filter (fun t : ℤ => ¬ g (t + i) ≤ w) := by
            apply Finset.filter_congr
            intro t ht
            exact lt_iff_not_ge
          rw [hnot_eq]
          unfold cntLow
          have hsum := Finset.card_filter_add_card_filter_not (s := I₃) (p := fun t : ℤ => g (t + i) ≤ w)
          have hmain : ((I₃.filter (fun t : ℤ => g (t + i) ≤ w)).card : ℝ) +
              ((I₃.filter (fun t : ℤ => ¬ g (t + i) ≤ w)).card : ℝ) = (I₃.card : ℝ) := by
            have hc := congrArg (fun x : ℕ => (x : ℝ)) hsum
            simpa [Nat.cast_add] using hc
          nlinarith
        have hcB3 : ((I₃.filter (fun t : ℤ => w < g (t + i))).card : ℝ) ≤
            (cntBad f g κ N i : ℝ) := by
          have := Finset.card_le_card hHighSub
          exact_mod_cast this
        have hbig : δ * (n : ℝ) / 4 ≤ (cntBad f g κ N i : ℝ) := by
          nlinarith [hcB3, hcntHigh, hlowSmall, hI3loN]
        exact not_lt_of_ge hbig
      -- (b) |S'| ≤ 32δn
      have hS'le : (S'.card : ℝ) ≤ 32 * δ * (n : ℝ) := by
        have hterm : ∀ i : ℤ, i ∈ S' → (δ * (n : ℝ) / 4) ≤ (cntLow g w I₃ i : ℝ) := by
          intro i hi
          have hlt : δ * (n : ℝ) / 4 < (cntLow g w I₃ i : ℝ) := (Finset.mem_filter.mp hi).2
          exact le_of_lt hlt
        have hbigsum : (S'.card : ℝ) * (δ * (n : ℝ) / 4) ≤
            (∑ i ∈ S', (cntLow g w I₃ i : ℝ)) := by
          have h1 := Finset.sum_le_sum (s := S') hterm
          have h1r : (∑ _i ∈ S', (δ * (n : ℝ) / 4)) ≤ (∑ i ∈ S', (cntLow g w I₃ i : ℝ)) := h1
          rwa [Finset.sum_const, nsmul_eq_mul] at h1r
        have hswap := sum_card_left_eq_sum_card_right (A := S') (B := I₃)
          (r := fun (i t : ℤ) => g (t + i) ≤ w)
        have hsumle : (∑ i ∈ S', (cntLow g w I₃ i : ℝ)) ≤ (I₃.card : ℝ) * (V.card : ℝ) := by
          calc
            (∑ i ∈ S', (cntLow g w I₃ i : ℝ))
                = (∑ i ∈ S', ((I₃.filter (fun t : ℤ => g (t + i) ≤ w)).card : ℝ)) := by
                  apply Finset.sum_congr rfl
                  intro i hi
                  rfl
            _ = (∑ t ∈ I₃, ((S'.filter (fun i : ℤ => g (t + i) ≤ w)).card : ℝ)) := hswap
            _ ≤ (∑ _t ∈ I₃, (V.card : ℝ)) := by
                  apply Finset.sum_le_sum
                  intro t ht
                  have hs := Finset.filter_subset_filter (fun i : ℤ => g (t + i) ≤ w) hS'subS
                  have h1 := Finset.card_le_card hs
                  exact_mod_cast (le_trans h1 (hbtleV t ht))
            _ = (I₃.card : ℝ) * (V.card : ℝ) := by
                  rw [Finset.sum_const, nsmul_eq_mul]
        have hineq : (S'.card : ℝ) * (δ * (n : ℝ) / 4) ≤ (I₃.card : ℝ) * (V.card : ℝ) := by
          exact le_trans hbigsum hsumle
        have hineq2 : (S'.card : ℝ) * (δ * (n : ℝ) / 4) ≤ 8 * δ * δ * (n : ℝ) * (n : ℝ) := by
          nlinarith [hineq, hI3hiN, hVle]
        have hcpos : 0 < δ * (n : ℝ) / 4 := by nlinarith [hδ, hnposR]
        have hdiv : (S'.card : ℝ) ≤ (8 * δ * δ * (n : ℝ) * (n : ℝ)) / (δ * (n : ℝ) / 4) := by
          exact (le_div_iff₀ hcpos).mpr hineq2
        have hval : (8 * δ * δ * (n : ℝ) * (n : ℝ)) / (δ * (n : ℝ) / 4) = 32 * δ * (n : ℝ) := by
          field_simp [hcpos.ne']
          ring
        rw [hval] at hdiv
        exact hdiv
      have hBadS' : BadSet ⊆ S' := by
        intro i hi
        have hiQ : i ∈ Q := hBadQ hi
        have hiS : i ∈ S := hQsubS hiQ
        by_contra hnot
        have hnb := hSnotS' i hiS hnot
        exact hnb (Finset.mem_filter.mp hi).2
      have hfin : (BadSet.card : ℝ) ≤ 32 * δ * (n : ℝ) := by
        have hc := Finset.card_le_card hBadS'
        have hcr : (BadSet.card : ℝ) ≤ (S'.card : ℝ) := by exact_mod_cast hc
        exact le_trans hcr hS'le
      simpa [BadSet] using hfin


lemma window_card (c : ℤ) (j n : ℕ) :
    (Finset.Icc (c + (j : ℤ) * (n : ℤ)) (c + (j : ℤ) * (n : ℤ) + (n : ℤ) - 1)).card = n := by
  rw [Int.card_Icc]
  have h : (c + (j : ℤ) * (n : ℤ) + (n : ℤ) - 1) + 1 - (c + (j : ℤ) * (n : ℤ)) = (n : ℤ) := by ring
  rw [h]
  simp

lemma covered_by_windows {c d : ℤ} {n k m : ℕ} (hn : 0 < n)
    (hm : m = (Finset.Icc c d).card) (hk : k = m / n + 1)
    {y : ℤ} (hy : y ∈ Finset.Icc c d) :
    ∃ j : ℕ, j < k ∧
      y ∈ Finset.Icc (c + (j : ℤ) * (n : ℤ)) (c + (j : ℤ) * (n : ℤ) + (n : ℤ) - 1) := by
  classical
  have hc : c ≤ y := (Finset.mem_Icc.mp hy).1
  have hd : y ≤ d := (Finset.mem_Icc.mp hy).2
  have hcd : c ≤ d := le_trans hc hd
  let x : ℕ := (y - c).toNat
  have hxy : (x : ℤ) = y - c := by
    dsimp [x]
    exact Int.toNat_of_nonneg (sub_nonneg.mpr hc)
  have hm1 : 1 ≤ m := by
    rw [hm]
    exact Finset.card_pos.mpr ⟨y, hy⟩
  have hx_le : (x : ℤ) ≤ (d - c : ℤ) := by
    rw [hxy]
    omega
  have hmZ : (m : ℤ) = d + 1 - c := by
    rw [hm, Int.card_Icc]
    exact Int.toNat_of_nonneg (by omega)
  have hx_le_m1 : (x : ℝ) ≤ (m : ℝ) - 1 := by
    have hnat : x ≤ m - 1 := by
      have h1 : (x : ℤ) ≤ (m : ℤ) - 1 := by omega
      rw [← Nat.cast_pred hm1] at h1
      exact_mod_cast h1
    have hc2 : ((x : ℕ) : ℝ) ≤ (((m - 1 : ℕ) : ℕ) : ℝ) := by exact_mod_cast hnat
    simpa [Nat.cast_pred hm1] using hc2
  have hkn : (m : ℝ) + 1 ≤ (k : ℝ) * (n : ℝ) := by
    rw [hk]
    have hdiv0 : m / n * n + m % n = m := by
      simpa [Nat.mul_comm] using (Nat.div_add_mod m n)
    have hdivR : (((m / n : ℕ) : ℝ) * ((n : ℕ) : ℝ) + ((m % n : ℕ) : ℝ)) = ((m : ℕ) : ℝ) := by
      rw [← Nat.cast_mul, ← Nat.cast_add]
      exact congrArg (fun z : ℕ => (z : ℝ)) hdiv0
    have hmodle : ((m % n : ℕ) : ℝ) ≤ (n : ℝ) - 1 := by
      have hmod : m % n < n := Nat.mod_lt m hn
      have h1 : m % n ≤ n - 1 := by omega
      have h2 : ((m % n : ℕ) : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by exact_mod_cast h1
      have h3 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
        rw [Nat.cast_pred hn]
      rw [h3] at h2
      exact h2
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hq : (((m / n + 1 : ℕ) : ℕ) : ℝ) = ((m / n : ℕ) : ℝ) + 1 := by
      simpa using (Nat.cast_add (R := ℝ) (m / n) 1)
    nlinarith
  have hx_lt : (x : ℝ) < (k : ℝ) * (n : ℝ) := by
    nlinarith
  let j : ℕ := x / n
  let r : ℕ := x % n
  refine ⟨j, ?_, ?_⟩
  · have hJ : x / n < k := by
      rw [Nat.div_lt_iff_lt_mul hn]
      exact_mod_cast hx_lt
    simpa [j] using hJ
  · have hdiv2 : x = j * n + r := by
      dsimp [j, r]
      have h := (Nat.div_add_mod x n).symm
      simpa [Nat.mul_comm] using h
    have hrlt : r < n := by
      dsimp [r]
      exact Nat.mod_lt x hn
    have hy_eq : y = c + (x : ℤ) := by omega
    have hx_int : (x : ℤ) = (j : ℤ) * (n : ℤ) + (r : ℤ) := by
      have := congrArg (fun z : ℕ => (z : ℤ)) hdiv2
      simpa [Nat.cast_add, Nat.cast_mul] using this
    rw [Finset.mem_Icc]
    have hr1 : (r : ℤ) ≤ (n : ℤ) - 1 := by
      have : (r : ℤ) < (n : ℤ) := by exact_mod_cast hrlt
      omega
    constructor <;> omega

/-- Main averaging count estimate. -/
theorem aux_averaging_count {f g : ℤ → ℝ} {κ δ : ℝ} (hκ : 0 < κ) (hδ : 0 < δ)
    (a b : ℤ) (I₁ I₂ I₃ : Finset ℤ) (c d : ℤ)
    (hpart : ∀ t : ℤ, t ∈ Finset.Icc a b ↔ t ∈ I₁ ∨ t ∈ I₂ ∨ t ∈ I₃)
    (hI3lo : δ * ((Finset.Icc a b).card : ℝ) / 2 ≤ (I₃.card : ℝ))
    (hI3hi : (I₃.card : ℝ) ≤ δ * ((Finset.Icc a b).card : ℝ))
    (hI2 : (I₂.card : ℝ) ≤ δ * ((Finset.Icc a b).card : ℝ))
    (hsep : ∀ t₁ : ℤ, t₁ ∈ I₁ → ∀ t₃ : ℤ, t₃ ∈ I₃ → f t₃ + κ ≤ f t₁)
    (hJlen : ((Finset.Icc a b).card : ℝ) ≤ ((Finset.Icc c d).card : ℝ)) :
    (((Finset.Icc c d).filter (fun y : ℤ =>
        ((((Finset.Icc a b).filter (fun t : ℤ => |f t - g (t + y)| ≥ κ / 2)).card : ℝ) <
          δ * (((Finset.Icc a b).card : ℝ)) / 4))).card : ℝ)
      ≤ 64 * δ * ((Finset.Icc c d).card : ℝ) := by
  classical
  set N : Finset ℤ := Finset.Icc a b with hN
  set n : ℕ := N.card with hn
  set M : Finset ℤ := Finset.Icc c d with hM
  set m : ℕ := M.card with hm
  change (((M.filter (fun y : ℤ =>
      (cntBad f g κ N y : ℝ) < δ * (n : ℝ) / 4)).card : ℝ) ≤ 64 * δ * (m : ℝ))
  have hJlenN : n ≤ m := by
    exact_mod_cast (by simpa [hN, hM, hn, hm] using hJlen)
  have hJlenR : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hJlenN
  let cond : ℤ → Prop := fun y => (cntBad f g κ N y : ℝ) < δ * (n : ℝ) / 4
  let BadM : Finset ℤ := M.filter cond
  by_cases hn0 : n = 0
  · have hNempty : N = ∅ := Finset.card_eq_zero.mp (by simpa [hn] using hn0)
    have hcond : ∀ y : ℤ, ¬ cond y := by
      intro y
      dsimp [cond]
      rw [hn0]
      simp [cntBad, hNempty]
    have hfil : BadM = ∅ := by
      ext y
      simp [BadM, hcond y]
    change (BadM.card : ℝ) ≤ 64 * δ * (m : ℝ)
    rw [hfil]
    simp
    have hz : (0 : ℝ) ≤ 64 * δ * (m : ℝ) := by
      have h1 : (0 : ℝ) ≤ 64 * δ := by nlinarith [hδ]
      exact mul_nonneg h1 (by exact_mod_cast Nat.zero_le m)
    simpa using hz
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
    have hmpos : 0 < m := lt_of_lt_of_le hnpos hJlenN
    by_cases h12 : δ < 1 / 2
    · let k : ℕ := m / n + 1
      let K : Finset ℕ := Finset.range k
      let W : ℕ → Finset ℤ := fun j =>
        Finset.Icc (c + (j : ℤ) * (n : ℤ)) (c + (j : ℤ) * (n : ℤ) + (n : ℤ) - 1)
      let BadW : ℕ → Finset ℤ := fun j => (W j).filter cond
      have hcover : BadM ⊆ K.biUnion BadW := by
        intro y hy
        rcases Finset.mem_filter.mp hy with ⟨hyM, hcondy⟩
        have hyIcc : y ∈ Finset.Icc c d := by simpa [hM] using hyM
        have hcv := covered_by_windows (c := c) (d := d) (n := n) (k := k) (m := m) hnpos
          (by simpa [hM] using hm) (by rfl) hyIcc
        rcases hcv with ⟨j, hjk, hjmem⟩
        exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_range.mpr hjk,
          Finset.mem_filter.mpr ⟨hjmem, hcondy⟩⟩
      have hcard2 : BadM.card ≤ ∑ j ∈ K, (BadW j).card := by
        calc
          BadM.card ≤ (K.biUnion BadW).card := Finset.card_le_card hcover
          _ ≤ ∑ j ∈ K, (BadW j).card := Finset.card_biUnion_le
      have hper : ∀ j ∈ K, ((BadW j).card : ℝ) ≤ 32 * δ * (n : ℝ) := by
        intro j hj
        have hblk : (Finset.Icc (c + (j : ℤ) * (n : ℤ)) (c + (j : ℤ) * (n : ℤ) + (n : ℤ) - 1)).card ≤ n := by
          rw [window_card c j n]
        have hb := aux_averaging_count_block (f := f) (g := g) (κ := κ) (δ := δ) hκ hδ h12
          (c₀ := c + (j : ℤ) * (n : ℤ)) (d₀ := c + (j : ℤ) * (n : ℤ) + (n : ℤ) - 1)
          a b I₁ I₂ I₃ hpart hI3lo hI3hi hI2 hsep hblk
        dsimp [BadW, cond]
        simpa [W, hN, hn, cntBad] using hb
      have hsumR : (∑ j ∈ K, ((BadW j).card : ℝ)) ≤ (k : ℝ) * (32 * δ * (n : ℝ)) := by
        have hle := Finset.sum_le_sum hper
        rw [Finset.sum_const, nsmul_eq_mul] at hle
        simpa [K] using hle
      have hBadM : (BadM.card : ℝ) ≤ (k : ℝ) * (32 * δ * (n : ℝ)) := by
        have h1 : (BadM.card : ℝ) ≤ ((∑ j ∈ K, (BadW j).card) : ℝ) := by exact_mod_cast hcard2
        exact le_trans (by simpa [Nat.cast_sum] using h1) hsumR
      have hknR : (k : ℝ) * (n : ℝ) ≤ (m : ℝ) + (n : ℝ) := by
        dsimp [k]
        have hdivm : ((m / n : ℕ) : ℝ) * (n : ℝ) ≤ (m : ℝ) := by
          exact_mod_cast (Nat.div_mul_le_self m n)
        have hq : (((m / n + 1 : ℕ) : ℕ) : ℝ) = ((m / n : ℕ) : ℝ) + 1 := by
          simpa using (Nat.cast_add (R := ℝ) (m / n) 1)
        nlinarith
      have hfinal : (k : ℝ) * (32 * δ * (n : ℝ)) ≤ 64 * δ * (m : ℝ) := by
        have h1 : (k : ℝ) * (32 * δ * (n : ℝ)) = 32 * δ * ((k : ℝ) * (n : ℝ)) := by ring
        rw [h1]
        have hnonneg : (0 : ℝ) ≤ 32 * δ := by nlinarith [hδ]
        have hstep1 : 32 * δ * ((k : ℝ) * (n : ℝ)) ≤ 32 * δ * ((m : ℝ) + (n : ℝ)) := by
          exact mul_le_mul_of_nonneg_left hknR hnonneg
        have hstep2 : 32 * δ * ((m : ℝ) + (n : ℝ)) ≤ 64 * δ * (m : ℝ) := by
          nlinarith [hJlenR, hδ]
        exact le_trans hstep1 hstep2
      have hres : (BadM.card : ℝ) ≤ 64 * δ * (m : ℝ) := le_trans hBadM hfinal
      simpa [BadM, cond] using hres
    · have hge : (1 : ℝ) ≤ 64 * δ := by nlinarith
      have hsub : BadM ⊆ M := by
        intro y hy
        exact (Finset.mem_filter.mp hy).1
      have hle_m : (BadM.card : ℝ) ≤ (m : ℝ) := by
        have := Finset.card_le_card hsub
        have hc : (BadM.card : ℝ) ≤ (M.card : ℝ) := by exact_mod_cast this
        simpa [← hm] using hc
      have hz : (m : ℝ) ≤ 64 * δ * (m : ℝ) := by
        have hmnn : (0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast Nat.zero_le m
        nlinarith
      exact le_trans hle_m hz

end
end Commons.Analysis.Interval