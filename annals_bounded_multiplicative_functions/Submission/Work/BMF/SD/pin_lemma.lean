import Mathlib
import Submission.Work.BMF.SD.beta_pinning

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The `β`-pinning lemma

If a `δ`-dense subset `A ⊆ [1,L]` of the integers has `‖β h‖ ≤ ε` for all `h ∈ A` (with
`ε ≤ δ/36`, `δ ≤ 1/2`), then some `q ≤ K/δ` satisfies `‖q β‖ ≤ K ε/(δ³ L)`.

The proof follows the same strategy as `Work.BMF.SD.beta_pinning` (which handles the
stronger hypothesis `ε ≤ δ²/100`): take `q₀` minimal with `‖q₀ β‖ ≤ 2ε`, observe that `A` is
`q₀`-separated (hence `q₀ ≤ 2/δ`), count the near-integers of `β` in arithmetic progressions
(`counting_bound`), and split on whether the counting error is dominated by the diagonal term.
The only change is in the numeric constants, the hypothesis `ε ≤ δ²/100` being replaced by the
weaker `ε ≤ δ/36`.
-/

set_option maxHeartbeats 800000

open Classical

namespace Work.BMF.SD

open Finset

/-- **Pinning a real `β` to a rational.**  If a positive-density set `A ⊆ [1,L]` has
`‖β h‖ ≤ ε` for all `h ∈ A` and `ε ≤ δ/36`, then some `q ≤ K/δ` has `‖q β‖ ≤ K ε/(δ³ L)`. -/
theorem pin_lemma : ∃ K : ℝ, 0 < K ∧ ∀ (β : ℝ) (L : ℕ) (δ ε : ℝ) (A : Finset ℕ),
    1 ≤ L → 0 < δ → δ ≤ 1 / 2 → 0 < ε → ε ≤ δ / 36 →
    (∀ h ∈ A, 1 ≤ h ∧ h ≤ L) → δ * (L : ℝ) ≤ (A.card : ℝ) →
    (∀ h ∈ A, ∃ m : ℤ, |β * (h : ℝ) - m| ≤ ε) →
    ∃ q : ℕ, 1 ≤ q ∧ (q : ℝ) ≤ K / δ ∧ ∃ m : ℤ,
      |(q : ℝ) * β - m| ≤ K * ε / (δ ^ 3 * (L : ℝ)) := by
  refine ⟨1000, by norm_num, ?_⟩
  intro β L δ ε A hL hδ0 hδ hε hεδ hA hAcard hgood
  have hLpos : (0:ℝ) < (L:ℝ) := by exact_mod_cast hL
  have hLne : (L:ℝ) ≠ 0 := ne_of_gt hLpos
  have hδne : δ ≠ 0 := ne_of_gt hδ0
  have h2ε : 2*ε ≤ δ/18 := by linarith [hεδ]
  have hεhalf : ε ≤ 1/2 := by linarith [hεδ, hδ]
  have h2nneg : (0:ℝ) ≤ 2*ε := by linarith [hε.le]
  rcases lt_or_ge (δ * (L:ℝ)) 2 with hsmall | hbig
  · -- trivial case `δL < 2`
    have hne : A.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hemp; rw [hemp, Finset.card_empty] at hAcard; simp at hAcard
      exact absurd hAcard (not_le.mpr (mul_pos hδ0 hLpos))
    have hmem := Finset.min'_mem A hne
    refine ⟨A.min' hne, (hA _ hmem).1, ?_, ?_⟩
    · have h3 : ((A.min' hne : ℕ):ℝ) ≤ (L:ℝ) := by exact_mod_cast (hA _ hmem).2
      have h2 : (L:ℝ) < 2/δ := by rw [lt_div_iff₀ hδ0]; linarith
      have h4 : (2:ℝ)/δ ≤ 1000/δ := div_le_div_of_nonneg_right (by norm_num) hδ0.le
      linarith
    · obtain ⟨m, hm⟩ := hgood _ hmem
      refine ⟨m, ?_⟩
      have hδ3L : δ^3 * (L:ℝ) ≤ 1000 := by
        have h2 : δ^2 ≤ 1/4 := by nlinarith [hδ, hδ0]
        have h3 : δ^3 * (L:ℝ) = δ^2 * (δ * (L:ℝ)) := by ring
        rw [h3]; nlinarith [h2, hsmall, hδ0.le, hLpos.le]
      calc |((A.min' hne : ℕ):ℝ) * β - m| = |β * ((A.min' hne : ℕ):ℝ) - m| := by rw [mul_comm]
        _ ≤ ε := hm
        _ ≤ 1000 * ε / (δ^3 * (L:ℝ)) := by
            rw [le_div_iff₀ (by positivity)]
            nlinarith [hδ3L, hε.le]
  · -- main case `2 ≤ δL`
    have hAcard2 : 2 ≤ A.card := by
      have : (2:ℝ) ≤ (A.card:ℝ) := le_trans hbig hAcard
      exact_mod_cast this
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < A.card)
    -- the gap is `2ε`-good
    have hgap : ∀ {x y : ℕ}, x ∈ A → y ∈ A → x ≠ y →
        ∃ k : ℤ, |β * ((max x y - min x y : ℕ):ℝ) - k| ≤ 2*ε := by
      intro x y hx hy hxy
      rcases le_total x y with h | h
      · rw [max_eq_right h, min_eq_left h]
        obtain ⟨ma, hma⟩ := hgood x hx
        obtain ⟨mb, hmb⟩ := hgood y hy
        refine ⟨mb - ma, ?_⟩
        rw [Nat.cast_sub h, Int.cast_sub]
        have h2 : β * ((y:ℝ) - (x:ℝ)) - ((mb:ℝ) - (ma:ℝ))
            = (β*(y:ℝ) - (mb:ℝ)) - (β*(x:ℝ) - (ma:ℝ)) := by ring
        rw [h2]
        calc |(β*(y:ℝ) - (mb:ℝ)) - (β*(x:ℝ) - (ma:ℝ))|
            ≤ |β*(y:ℝ) - (mb:ℝ)| + |β*(x:ℝ) - (ma:ℝ)| := by
              have h3 := abs_sub_le (β*(y:ℝ) - (mb:ℝ)) 0 (β*(x:ℝ) - (ma:ℝ))
              rwa [sub_zero, zero_sub, abs_neg] at h3
          _ ≤ 2*ε := by linarith
      · rw [max_eq_left h, min_eq_right h]
        obtain ⟨ma, hma⟩ := hgood x hx
        obtain ⟨mb, hmb⟩ := hgood y hy
        refine ⟨ma - mb, ?_⟩
        rw [Nat.cast_sub h, Int.cast_sub]
        have h2 : β * ((x:ℝ) - (y:ℝ)) - ((ma:ℝ) - (mb:ℝ))
            = (β*(x:ℝ) - (ma:ℝ)) - (β*(y:ℝ) - (mb:ℝ)) := by ring
        rw [h2]
        calc |(β*(x:ℝ) - (ma:ℝ)) - (β*(y:ℝ) - (mb:ℝ))|
            ≤ |β*(x:ℝ) - (ma:ℝ)| + |β*(y:ℝ) - (mb:ℝ)| := by
              have h3 := abs_sub_le (β*(x:ℝ) - (ma:ℝ)) 0 (β*(y:ℝ) - (mb:ℝ))
              rwa [sub_zero, zero_sub, abs_neg] at h3
          _ ≤ 2*ε := by linarith
    have hex : ∃ n : ℕ, 1 ≤ n ∧ ∃ m : ℤ, |β*(n:ℝ) - m| ≤ 2*ε := by
      refine ⟨max a b - min a b, ?_, hgap ha hb hab⟩
      rcases le_total a b with h | h
      · rw [max_eq_right h, min_eq_left h]; omega
      · rw [max_eq_left h, min_eq_right h]; omega
    set q₀ : ℕ := Nat.find hex with hq0def
    have hq0spec : 1 ≤ q₀ ∧ ∃ m : ℤ, |β*(q₀:ℝ) - m| ≤ 2*ε := by
      rw [hq0def]; exact Nat.find_spec hex
    have hq0min : ∀ m : ℕ, (1 ≤ m ∧ ∃ k : ℤ, |β*(m:ℝ) - k| ≤ 2*ε) → q₀ ≤ m := by
      intro m hm; rw [hq0def]; exact Nat.find_min' hex hm
    obtain ⟨m₀, hm₀⟩ := hq0spec.2
    set β₀ : ℝ := |β*(q₀:ℝ) - (m₀:ℝ)| with hβ0def
    have hβ0le : β₀ ≤ 2*ε := hm₀
    have hβ0nn : 0 ≤ β₀ := abs_nonneg _
    have hsep : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → q₀ ≤ max x y - min x y := by
      intro x hx y hy hxy
      exact hq0min _ ⟨by
        rcases le_total x y with h | h
        · rw [max_eq_right h, min_eq_left h]; omega
        · rw [max_eq_left h, min_eq_right h]; omega, hgap hx hy hxy⟩
    have hsep' := separated_card_bound A q₀ L hq0spec.1 (fun x hx => (hA x hx).2) hsep
    have hq0le : (q₀:ℝ) ≤ 2/δ := by
      have hc1ge : δ*(L:ℝ)/2 ≤ ((A.card - 1 : ℕ):ℝ) := by
        have hc1 : ((A.card - 1 : ℕ):ℝ) = (A.card:ℝ) - 1 := by
          have h1 : 1 ≤ A.card := by omega
          rw [Nat.cast_sub h1]; norm_num
        rw [hc1]; linarith [hAcard, hbig]
      have hsepR : ((A.card - 1 : ℕ):ℝ) * (q₀:ℝ) ≤ (L:ℝ) := by exact_mod_cast hsep'
      have hpos : 0 < δ*(L:ℝ)/2 := by linarith
      have hq0nn : (0:ℝ) ≤ (q₀:ℝ) := Nat.cast_nonneg q₀
      have hstep : (δ*(L:ℝ)/2) * (q₀:ℝ) ≤ (L:ℝ) :=
        le_trans (mul_le_mul_of_nonneg_right hc1ge hq0nn) hsepR
      have h1 : (q₀:ℝ) ≤ (L:ℝ)/(δ*(L:ℝ)/2) := by
        rw [le_div_iff₀ hpos]; linarith [hstep]
      have h2 : (L:ℝ)/(δ*(L:ℝ)/2) = 2/δ := by
        rw [div_eq_div_iff (ne_of_gt hpos) hδne]; ring
      rw [h2] at h1; exact h1
    have hq0le1000 : (q₀:ℝ) ≤ 1000/δ := le_trans hq0le (div_le_div_of_nonneg_right (by norm_num) hδ0.le)
    by_cases hβ0zero : β₀ = 0
    · refine ⟨q₀, hq0spec.1, hq0le1000, ⟨m₀, ?_⟩⟩
      rw [mul_comm, show |β*(q₀:ℝ) - (m₀:ℝ)| = 0 by rw [← hβ0def]; exact hβ0zero]
      positivity
    · have hβ0pos : 0 < β₀ := lt_of_le_of_ne hβ0nn (Ne.symm hβ0zero)
      rcases lt_or_ge (δ*(L:ℝ)) (100/δ) with hmid | hlarge
      · -- `2 ≤ δL < 100/δ`
        refine ⟨q₀, hq0spec.1, hq0le1000, ⟨m₀, ?_⟩⟩
        rw [mul_comm, show |β*(q₀:ℝ) - (m₀:ℝ)| = β₀ by rw [hβ0def]]
        have h5 : 2*δ^3*(L:ℝ) ≤ 1000 := by
          have h7 : δ^3*(L:ℝ) = δ^2 * (δ*(L:ℝ)) := by ring
          have h8 : δ^2 * (δ*(L:ℝ)) < δ^2 * (100/δ) :=
            mul_lt_mul_of_pos_left hmid (by positivity)
          have h9 : δ^2 * (100/δ) = 100*δ := by field_simp
          nlinarith [h7, h8, h9, hδ, hδ0]
        calc β₀ ≤ 2*ε := hβ0le
          _ ≤ 1000*ε/(δ^3*(L:ℝ)) := by
              rw [le_div_iff₀ (by positivity)]
              nlinarith [h5, hε.le]
      · -- `100/δ ≤ δL`
        have hArd : (A.card:ℝ) ≤
            ((Finset.filter (fun (n:ℕ) => ∃ k : ℤ, |β*(n:ℝ) - (k:ℝ)| ≤ ε) (Finset.Icc 1 L)).card : ℝ) := by
          have hsub : A ⊆ (Finset.Icc 1 L).filter (fun n => ∃ k:ℤ, |β*(n:ℝ) - (k:ℝ)| ≤ ε) := by
            intro n hn
            exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨(hA n hn).1, (hA n hn).2⟩, hgood n hn⟩
          exact_mod_cast Finset.card_le_card hsub
        have hcount := counting_bound β L q₀ hq0spec.1 m₀ ε hε
          (by rw [← hβ0def]; exact hβ0pos) hεhalf
        have hmain : δ*(L:ℝ) ≤ β₀*(L:ℝ) + 2*ε*(L:ℝ) + 4*ε*(q₀:ℝ)/β₀ + 2*(q₀:ℝ) := by
          have h1 := le_trans (le_trans hAcard hArd) hcount
          rw [show |β*(q₀:ℝ) - (m₀:ℝ)| = β₀ by rw [hβ0def]] at h1
          have h2 : (β₀*(L:ℝ) + 2*(q₀:ℝ)) * (2*ε/β₀ + 1)
              = β₀*(L:ℝ) + 2*ε*(L:ℝ) + 4*ε*(q₀:ℝ)/β₀ + 2*(q₀:ℝ) := by
            field_simp; ring
          linarith [h1, h2.le, h2.ge]
        rcases lt_or_ge (δ*(L:ℝ)/2) (4*ε*(q₀:ℝ)/β₀) with hcaseB | hcaseA
        · have hbl : β₀ < 8*ε*(q₀:ℝ)/(δ*(L:ℝ)) := by
            rw [lt_div_iff₀ hβ0pos] at hcaseB
            rw [lt_div_iff₀ (by positivity : 0 < δ*(L:ℝ))]
            nlinarith [hcaseB]
          have hb2 : 8*ε*(q₀:ℝ)/(δ*(L:ℝ)) ≤ 16*ε/(δ^2*(L:ℝ)) := by
            rw [div_le_div_iff₀ (by positivity : (0:ℝ) < δ*(L:ℝ))
                  (by positivity : (0:ℝ) < δ^2*(L:ℝ))]
            have hd : (q₀:ℝ)*δ ≤ 2 := by rw [← le_div_iff₀ hδ0]; exact hq0le
            have h1 : 8*ε*(q₀:ℝ)*(δ^2*(L:ℝ)) = (8*ε*δ*(L:ℝ)) * ((q₀:ℝ)*δ) := by ring
            have h2 : 16*ε*(δ*(L:ℝ)) = (8*ε*δ*(L:ℝ)) * 2 := by ring
            rw [h1, h2]
            exact mul_le_mul_of_nonneg_left hd (by positivity)
          have hb3 : 16*ε/(δ^2*(L:ℝ)) ≤ 1000*ε/(δ^3*(L:ℝ)) := by
            rw [div_le_div_iff₀ (by positivity : (0:ℝ) < δ^2*(L:ℝ))
                  (by positivity : (0:ℝ) < δ^3*(L:ℝ))]
            have h1 : 16*ε*(δ^3*(L:ℝ)) = (16*ε*(δ^2*(L:ℝ))) * δ := by ring
            have h2 : 1000*ε*(δ^2*(L:ℝ)) = (16*ε*(δ^2*(L:ℝ))) * ((1000:ℝ)/16) := by ring
            rw [h1, h2]
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            nlinarith [hδ]
          exact ⟨q₀, hq0spec.1, hq0le1000, ⟨m₀, by
            rw [mul_comm, show |β*(q₀:ℝ) - (m₀:ℝ)| = β₀ by rw [hβ0def]]
            exact le_trans hbl.le (le_trans hb2 hb3)⟩⟩
        · exfalso
          have hb0ge : δ/2 - 2*ε - 2*(q₀:ℝ)/(L:ℝ) ≤ β₀ := by
            have h2 : δ*(L:ℝ)/2 ≤ β₀*(L:ℝ) + 2*ε*(L:ℝ) + 2*(q₀:ℝ) := by
              nlinarith [hmain, hcaseA]
            have h3 : δ/2 - β₀ - 2*ε ≤ 2*(q₀:ℝ)/(L:ℝ) := by
              rw [le_div_iff₀ hLpos]; nlinarith [h2]
            linarith
          have hq0L : 2*(q₀:ℝ)/(L:ℝ) ≤ δ/25 := by
            have h3 : 50*(q₀:ℝ) ≤ δ*(L:ℝ) := by
              have h4 : 50*(q₀:ℝ) ≤ 50*(2/δ) := by
                have := hq0le; nlinarith [hδ0]
              have h5 : 50*(2/δ) = 100/δ := by field_simp; ring
              have := mul_le_mul_of_nonneg_right hlarge hδ0.le
              rw [h5] at h4
              have h6 : (100/δ)*δ = 100 := by field_simp
              rw [h6] at this
              nlinarith [h4, this]
            rw [div_le_iff₀ hLpos]
            nlinarith [h3]
          have h2e : 2*ε ≤ δ/18 := h2ε
          have hge : (2:ℝ)/5 * δ ≤ β₀ := by linarith [hb0ge, hq0L, h2e]
          have hle : β₀ ≤ (1:ℝ)/18 * δ := by linarith [hβ0le, h2e]
          nlinarith [hge, hle, hδ0]

end Work.BMF.SD
