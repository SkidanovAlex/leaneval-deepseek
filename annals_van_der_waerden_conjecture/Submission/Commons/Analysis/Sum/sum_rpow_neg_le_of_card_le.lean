import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SumIntegralComparisons

open Finset

namespace Commons.Analysis.Sum

lemma sum_Icc_rpow_neg_le (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) (k : ℕ) :
    ∑ j ∈ Finset.Icc 1 k, (j : ℝ) ^ (-γ) ≤ (1 / (1 - γ)) * (k : ℝ) ^ (1 - γ) := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    rw [Finset.Icc_eq_empty (by norm_num : ¬ (1:ℕ) ≤ 0)]
    simp only [Finset.sum_empty]
    simp [Real.zero_rpow (by linarith : (1:ℝ) - γ ≠ 0)]
  · have hk1 : 1 ≤ k := hk
    have hIcc : Finset.Icc 1 k = insert 1 (Finset.Icc 2 k) := by
      rw [← Finset.insert_Icc_succ_left_eq_Icc (a := 1) (b := k) hk1]
      norm_num [Order.succ]
    rw [hIcc, Finset.sum_insert (by simp)]
    have h1 : ((1:ℕ):ℝ) ^ (-γ) = 1 := by
      rw [Nat.cast_one, Real.one_rpow]
    rw [h1]
    have hcongr : (∑ j ∈ Finset.Icc 2 k, (j:ℝ) ^ (-γ))
        = ∑ i ∈ Finset.Ico 1 k, (((i+1:ℕ)):ℝ) ^ (-γ) := by
      have h := Finset.sum_Ico_add' (α := ℕ) (f := fun j : ℕ => (j:ℝ) ^ (-γ)) 1 k 1
      rw [Finset.Ico_add_one_right_eq_Icc] at h
      exact h.symm
    rw [hcongr]
    have hAnti : AntitoneOn (fun x : ℝ => x ^ (-γ)) (Set.Icc (↑(1:ℕ) : ℝ) (↑k : ℝ)) := by
      refine (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by linarith : -γ ≤ 0)).mono ?_
      intro x hx
      simp only [Set.mem_Icc] at hx
      simp only [Set.mem_Ioi]
      have : (1:ℝ) ≤ x := by exact_mod_cast hx.1
      linarith
    have hint := AntitoneOn.sum_le_integral_Ico (a := 1) (b := k) hk1
        (f := fun x : ℝ => x ^ (-γ)) hAnti
    have hInt : (∫ x : ℝ in (↑(1:ℕ) : ℝ)..(↑k : ℝ), x ^ (-γ)) = ((↑k : ℝ)^(1-γ) - 1)/(1-γ) := by
      rw [integral_rpow (Or.inl (by linarith : -1 < -γ))]
      have h2 : (-γ + 1 : ℝ) = 1 - γ := by ring
      rw [h2]
      norm_num
    have hden : 0 < 1 - γ := by linarith
    have key : 1 + ((k:ℝ)^(1-γ) - 1)/(1-γ) ≤ (1/(1-γ)) * (k:ℝ)^(1-γ) := by
      rw [one_div, ← div_eq_inv_mul]
      rw [← sub_nonneg]
      have : (k:ℝ)^(1-γ)/(1-γ) - (1 + ((k:ℝ)^(1-γ) - 1)/(1-γ)) = γ/(1-γ) := by
        field_simp
        ring
      rw [this]
      positivity
    calc 1 + ∑ i ∈ Finset.Ico 1 k, (((i+1:ℕ)):ℝ) ^ (-γ)
        ≤ 1 + ∫ x : ℝ in (↑(1:ℕ) : ℝ)..(↑k : ℝ), x ^ (-γ) := by linarith [hint]
      _ = 1 + ((k:ℝ)^(1-γ) - 1)/(1-γ) := by rw [hInt]
      _ ≤ (1/(1-γ)) * (k:ℝ)^(1-γ) := key

lemma card_le_of_card_filter_le {s : Finset ℕ} {c X β : ℝ} (hc : 0 < c) (hX : 1 ≤ X)
    (hnX : ∀ n ∈ s, (n:ℝ) ≤ X)
    (hcard : ∀ Y : ℕ, ((s.filter (fun n => n ≤ Y)).card : ℝ) ≤ c * (Y:ℝ)^β) :
    (s.card : ℝ) ≤ c * X^β := by
  have hXpos : (0:ℝ) < X := lt_of_lt_of_le zero_lt_one hX
  rcases le_or_gt 0 β with hβ | hβ
  · have hY : ((Nat.floor X : ℕ) : ℝ) ≤ X := Nat.floor_le (le_of_lt hXpos)
    have hs_eq : s.filter (fun n => n ≤ Nat.floor X) = s := by
      apply Finset.filter_true_of_mem
      intro n hn
      exact Nat.le_floor (hnX n hn)
    calc (s.card:ℝ) = ((s.filter (fun n => n ≤ Nat.floor X)).card : ℝ) := by rw [hs_eq]
      _ ≤ c * ((Nat.floor X : ℕ) : ℝ)^β := hcard (Nat.floor X)
      _ ≤ c * X^β := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (by positivity) hY hβ) (le_of_lt hc)
  · have hY : X ≤ ((Nat.ceil X : ℕ) : ℝ) := Nat.le_ceil X
    have hs_eq : s.filter (fun n => n ≤ Nat.ceil X) = s := by
      apply Finset.filter_true_of_mem
      intro n hn
      have h1 : (n:ℝ) ≤ ((Nat.ceil X : ℕ) : ℝ) := le_trans (hnX n hn) hY
      exact_mod_cast h1
    calc (s.card:ℝ) = ((s.filter (fun n => n ≤ Nat.ceil X)).card : ℝ) := by rw [hs_eq]
      _ ≤ c * ((Nat.ceil X : ℕ) : ℝ)^β := hcard (Nat.ceil X)
      _ ≤ c * X^β := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos hXpos hY (le_of_lt hβ)) (le_of_lt hc)

lemma rpow_neg_mul_pow_eq (n c α β : ℝ) (hn : 0 < n) (hc : 0 < c) (hβ : β ≠ 0) :
    c ^ (α/β) * (c * n^β) ^ (-(α/β)) = n ^ (-α) := by
  rw [Real.mul_rpow (le_of_lt hc) (Real.rpow_nonneg (le_of_lt hn) β)]
  rw [← mul_assoc, ← Real.rpow_add hc]
  have h1 : α/β + -(α/β) = 0 := by ring
  rw [h1, Real.rpow_zero, one_mul]
  rw [← Real.rpow_mul (le_of_lt hn) β (-(α/β))]
  congr 1
  field_simp

lemma rpow_neg_le_of_le_mul_rpow (n c α β A : ℝ) (hn : 0 < n) (hc : 0 < c) (hα : 0 < α)
    (hβ : 0 < β) (hApos : 0 < A) (hAle : A ≤ c * n^β) :
    n ^ (-α) ≤ c ^ (α/β) * A ^ (-(α/β)) := by
  have hγ : -(α/β) ≤ 0 := by
    have : 0 < α/β := div_pos hα hβ
    linarith
  have hle : (c * n^β) ^ (-(α/β)) ≤ A ^ (-(α/β)) :=
    Real.rpow_le_rpow_of_nonpos hApos hAle hγ
  have h2 := mul_le_mul_of_nonneg_left hle (by positivity : (0:ℝ) ≤ c ^ (α/β))
  rw [rpow_neg_mul_pow_eq n c α β hn hc hβ.ne'] at h2
  exact h2

theorem sum_rpow_neg_le_of_card_le (α β : ℝ) (hαβ : α < β) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s : Finset ℕ) (c X : ℝ), 0 < c → 1 ≤ X →
      (∀ n ∈ s, 1 ≤ n) → (∀ n ∈ s, (n : ℝ) ≤ X) →
      (∀ Y : ℕ, ((s.filter (fun n => n ≤ Y)).card : ℝ) ≤ c * (Y : ℝ) ^ β) →
      ∑ n ∈ s, ((n : ℝ) ^ (-α)) ≤ C * c * X ^ (β - α) := by
  refine ⟨max 1 (1/(1-α/β)), ?_, ?_⟩
  · exact le_trans zero_le_one (le_max_left _ _)
  · intro s c X hc hX hge hle hcard
    by_cases hα : α ≤ 0
    · have hXpos : (0:ℝ) < X := lt_of_lt_of_le zero_lt_one hX
      have hcardX : (s.card : ℝ) ≤ c * X^β := card_le_of_card_filter_le hc hX hle hcard
      have hterm : ∀ n ∈ s, (n:ℝ)^(-α) ≤ X^(-α) := by
        intro n hn
        have hn0 : (0:ℝ) ≤ (n:ℝ) := by positivity
        exact Real.rpow_le_rpow hn0 (hle n hn) (by linarith)
      have hsum : ∑ n ∈ s, (n:ℝ)^(-α) ≤ (s.card:ℝ) * X^(-α) := by
        calc ∑ n ∈ s, (n:ℝ)^(-α) ≤ ∑ n ∈ s, X^(-α) := Finset.sum_le_sum hterm
          _ = (s.card:ℝ) * X^(-α) := by simp [Finset.sum_const, nsmul_eq_mul]
      have hXneg : 0 ≤ X^(-α) := Real.rpow_nonneg (le_of_lt hXpos) _
      calc ∑ n ∈ s, (n:ℝ)^(-α)
          ≤ (s.card:ℝ) * X^(-α) := hsum
        _ ≤ (c * X^β) * X^(-α) := mul_le_mul_of_nonneg_right hcardX hXneg
        _ = c * X^(β - α) := by
            rw [mul_assoc, ← Real.rpow_add hXpos]
            congr 1
        _ ≤ max 1 (1/(1-α/β)) * c * X^(β-α) := by
            have hle1 : (1:ℝ) ≤ max 1 (1/(1-α/β)) := le_max_left _ _
            have hnn : 0 ≤ c * X^(β-α) := by
              have := Real.rpow_nonneg (le_of_lt hXpos) (β-α); positivity
            calc c * X^(β-α) = 1 * (c*X^(β-α)) := by ring
              _ ≤ max 1 (1/(1-α/β)) * (c*X^(β-α)) := mul_le_mul_of_nonneg_right hle1 hnn
              _ = max 1 (1/(1-α/β)) * c * X^(β-α) := by ring
    · rw [not_le] at hα
      have hαpos : 0 < α := hα
      have hβpos : 0 < β := lt_trans hαpos hαβ
      have hγpos : 0 < α/β := div_pos hαpos hβpos
      have hγlt1 : α/β < 1 := by rw [div_lt_one hβpos]; exact hαβ
      have hXpos : (0:ℝ) < X := lt_of_lt_of_le zero_lt_one hX
      have hcardX : (s.card : ℝ) ≤ c * X^β := card_le_of_card_filter_le hc hX hle hcard
      have hstrict : ∀ n ∈ s, ∀ m ∈ s, n < m →
          (s.filter (fun x => x ≤ n)).card < (s.filter (fun x => x ≤ m)).card := by
        intro n hn m hm hnm
        have hsub : s.filter (fun x => x ≤ n) ⊆ s.filter (fun x => x ≤ m) := by
          intro x hx
          simp only [Finset.mem_filter] at hx ⊢
          exact ⟨hx.1, le_trans hx.2 (le_of_lt hnm)⟩
        have hne : s.filter (fun x => x ≤ n) ≠ s.filter (fun x => x ≤ m) := by
          intro heq
          have : m ∈ s.filter (fun x => x ≤ n) := by
            rw [heq]; exact Finset.mem_filter.mpr ⟨hm, le_refl m⟩
          exact absurd (Finset.mem_filter.mp this).2 (not_le.mpr hnm)
        exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩)
      have hinj : Set.InjOn (fun n : ℕ => (s.filter (fun m => m ≤ n)).card) ↑s := by
        intro n hn m hm heq
        change (s.filter (fun x => x ≤ n)).card = (s.filter (fun x => x ≤ m)).card at heq
        rcases lt_trichotomy n m with hlt | heq' | hgt
        · exact absurd (heq ▸ hstrict n hn m hm hlt) (lt_irrefl _)
        · exact heq'
        · exact absurd (heq ▸ hstrict m hm n hn hgt) (lt_irrefl _)
      have hA1 : ∀ n ∈ s, 1 ≤ (s.filter (fun m => m ≤ n)).card := by
        intro n hn
        have : 0 < (s.filter (fun m => m ≤ n)).card :=
          Finset.card_pos.mpr ⟨n, Finset.mem_filter.mpr ⟨hn, le_refl n⟩⟩
        omega
      have hA2 : ∀ n ∈ s, (s.filter (fun m => m ≤ n)).card ≤ s.card :=
        fun n _ => Finset.card_le_card (Finset.filter_subset _ _)
      have hterm : ∀ n ∈ s, (n:ℝ)^(-α) ≤
          c^(α/β) * (((s.filter (fun m => m ≤ n)).card : ℕ) : ℝ)^(-(α/β)) := by
        intro n hn
        have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast (hge n hn)
        have hApos : (0:ℝ) < (((s.filter (fun m => m ≤ n)).card : ℕ) : ℝ) := by
          have := hA1 n hn; positivity
        exact rpow_neg_le_of_le_mul_rpow (n:ℝ) c α β _ hnpos hc hαpos hβpos hApos (hcard n)
      have hstep1 : ∑ n ∈ s, (n:ℝ)^(-α)
          ≤ c^(α/β) * ∑ n ∈ s, (((s.filter (fun m => m ≤ n)).card : ℕ):ℝ)^(-(α/β)) := by
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum hterm
      have himg : ∑ n ∈ s, (((s.filter (fun m => m ≤ n)).card : ℕ):ℝ)^(-(α/β))
          = ∑ j ∈ s.image (fun n : ℕ => (s.filter (fun m => m ≤ n)).card), (j:ℝ)^(-(α/β)) := by
        rw [← Finset.sum_image (f := fun j : ℕ => (j:ℝ)^(-(α/β))) hinj]
      have hsub : s.image (fun n : ℕ => (s.filter (fun m => m ≤ n)).card) ⊆ Finset.Icc 1 s.card := by
        intro j hj
        rw [Finset.mem_image] at hj
        obtain ⟨n, hn, rfl⟩ := hj
        exact Finset.mem_Icc.mpr ⟨hA1 n hn, hA2 n hn⟩
      have himg_le : ∑ j ∈ s.image (fun n : ℕ => (s.filter (fun m => m ≤ n)).card), (j:ℝ)^(-(α/β))
          ≤ ∑ j ∈ Finset.Icc 1 s.card, (j:ℝ)^(-(α/β)) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intro j hj _
        exact Real.rpow_nonneg (by positivity) _
      have hharm := sum_Icc_rpow_neg_le (α/β) hγpos hγlt1 s.card
      have hcard_rpow : (s.card:ℝ)^(1-α/β) ≤ (c*X^β)^(1-α/β) :=
        Real.rpow_le_rpow (by positivity) hcardX (by linarith)
      have hcard_rpow2 : (c*X^β)^(1-α/β) = c^(1-α/β) * X^(β-α) := by
        rw [Real.mul_rpow (le_of_lt hc) (Real.rpow_nonneg (le_of_lt hXpos) β)]
        congr 1
        rw [← Real.rpow_mul (le_of_lt hXpos)]
        congr 1
        field_simp
      have hcard_rpow' : (s.card:ℝ)^(1-α/β) ≤ c^(1-α/β) * X^(β-α) := by
        rw [hcard_rpow2] at hcard_rpow; exact hcard_rpow
      have hcc : c^(α/β) * c^(1-α/β) = c := by
        rw [← Real.rpow_add hc]
        have : α/β + (1 - α/β) = 1 := by ring
        rw [this, Real.rpow_one]
      have hγsub : 0 < 1 - α/β := by linarith
      have hns : 0 ≤ 1/(1-α/β) := div_nonneg zero_le_one (le_of_lt hγsub)
      have hcpos : 0 ≤ c^(α/β) := Real.rpow_nonneg (le_of_lt hc) _
      calc ∑ n ∈ s, (n:ℝ)^(-α)
          ≤ c^(α/β) * ∑ n ∈ s, (((s.filter (fun m => m ≤ n)).card : ℕ):ℝ)^(-(α/β)) := hstep1
        _ = c^(α/β) * ∑ j ∈ s.image (fun n : ℕ => (s.filter (fun m => m ≤ n)).card), (j:ℝ)^(-(α/β)) := by rw [himg]
        _ ≤ c^(α/β) * ∑ j ∈ Finset.Icc 1 s.card, (j:ℝ)^(-(α/β)) :=
              mul_le_mul_of_nonneg_left himg_le hcpos
        _ ≤ c^(α/β) * ((1/(1-α/β)) * (s.card:ℝ)^(1-α/β)) :=
              mul_le_mul_of_nonneg_left hharm hcpos
        _ ≤ c^(α/β) * ((1/(1-α/β)) * (c^(1-α/β) * X^(β-α))) := by
              apply mul_le_mul_of_nonneg_left _ hcpos
              apply mul_le_mul_of_nonneg_left hcard_rpow' hns
        _ = (1/(1-α/β)) * c * X^(β-α) := by
              rw [show c^(α/β) * ((1/(1-α/β)) * (c^(1-α/β) * X^(β-α)))
                    = (1/(1-α/β)) * (c^(α/β) * c^(1-α/β)) * X^(β-α) by ring]
              rw [hcc]
        _ ≤ max 1 (1/(1-α/β)) * c * X^(β-α) := by
              have hle1 : (1/(1-α/β)) ≤ max 1 (1/(1-α/β)) := le_max_right _ _
              have hnn : 0 ≤ c * X^(β-α) := by
                have := Real.rpow_nonneg (le_of_lt hXpos) (β-α); positivity
              calc (1/(1-α/β)) * c * X^(β-α) = (1/(1-α/β)) * (c * X^(β-α)) := by ring
                _ ≤ max 1 (1/(1-α/β)) * (c * X^(β-α)) := mul_le_mul_of_nonneg_right hle1 hnn
                _ = max 1 (1/(1-α/β)) * c * X^(β-α) := by ring

end Commons.Analysis.Sum