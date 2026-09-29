import Mathlib
import Submission.Work.Holonomy3.defs
import Submission.Work.Holonomy3.seed_helpers
import Submission.Work.Holonomy3.index_error_bound
import Submission.Work.Holonomy3.block_sum_bound

set_option maxHeartbeats 4000000

namespace Work.Holonomy3

open Submission.CDT.Discrepancy

/-- **The paper's `(seed sum est)`** (the "Seeding" step of the fine holonomy bound). If the sorted
exponent vector `n` of the minimal-order monomial lies in the box `n j ≤ (m+δ)D` with normalised
coordinates `n j / ((m+δ)D)` of box discrepancy `< ε`, then the sum of the exponents over the block of
indices `j/d ∈ [γ_k/m, γ_{k+1}/m)` equals `(γ_{k+1}² - γ_k²)·(Σ_j n_j)/m²` up to a relative error
`η`, for `ε` small and `d` large. This is what converts the Cauchy bound into the blockwise
rearrangement integral of the theorem. -/
theorem seed_sum_estimate {l : ℕ} (m : ℕ) (hm : 1 ≤ m) (η : ℝ) (hη : 0 < η) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∃ d₀ : ℕ,
      ∀ d : ℕ, d₀ ≤ d → ∀ D : ℕ, ∀ δ : ℝ, 0 ≤ δ → δ < ε →
      ∀ γ : Fin (l + 2) → ℝ, γ 0 = 0 → γ (Fin.last (l + 1)) = m → StrictMono γ →
      ∀ n : Fin d → ℕ, Monotone n →
      (∀ j, (n j : ℝ) ≤ (m + δ) * D) →
      Submission.CDT.Discrepancy.disc (fun j => (n j : ℝ) / ((m + δ) * D)) < ε →
      ∀ k : Fin (l + 1),
        |(∑ j ∈ Finset.univ.filter (fun j : Fin d =>
            γ k.castSucc / m ≤ (j : ℝ) / d ∧ (j : ℝ) / d < γ k.succ / m), (n j : ℝ))
          - (γ k.succ ^ 2 - γ k.castSucc ^ 2) * ((∑ j, (n j : ℝ)) / (m : ℝ) ^ 2)|
          ≤ η * (∑ j, (n j : ℝ)) := by
  refine ⟨min (η / 64) (1 / 64), lt_min (by positivity) (by norm_num), ?_⟩
  intro ε hε hεlt
  refine ⟨⌈64 / η⌉₊ + 64, ?_⟩
  intro d hd D δ hδ0 hδε γ hγ0 hγlast hγmono n hmono hbound hdisc k
  have hdpos : 0 < d := by
    have h : (64 : ℕ) ≤ ⌈64 / η⌉₊ + 64 := Nat.le_add_left 64 _
    omega
  have hdposR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hdpos
  have hd64 : (64 : ℝ) ≤ (d : ℝ) := by
    have h : (64 : ℕ) ≤ d := le_trans (Nat.le_add_left 64 _) hd
    exact_mod_cast h
  have hεη : ε ≤ η / 64 := le_trans (le_of_lt hεlt) (min_le_left _ _)
  have hε1 : ε ≤ 1 / 64 := le_trans (le_of_lt hεlt) (min_le_right _ _)
  have hηd : (20 : ℝ) ≤ η * (d : ℝ) := by
    have h1 : 64 / η ≤ ((⌈64 / η⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
    have h2 : ((⌈64 / η⌉₊ : ℕ) : ℝ) + 64 ≤ (d : ℝ) := by exact_mod_cast hd
    have h3 : η * (64 / η) = 64 := by field_simp
    nlinarith [hη.le, h1, h2, h3]
  set Q : ℝ := ((m : ℝ) + δ) * (D : ℝ) with hQ
  by_cases hD0 : D = 0
  · have hn0 : ∀ j : Fin d, n j = 0 := by
      intro j
      have hb := hbound j
      rw [hQ] at hb
      rw [hD0] at hb
      simp only [Nat.cast_zero, mul_zero] at hb
      have h0 : (0 : ℝ) ≤ (n j : ℝ) := Nat.cast_nonneg _
      have h1 : (n j : ℝ) = 0 := le_antisymm hb h0
      exact_mod_cast h1
    simp [hn0]
  · have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have hDpos : 0 < D := Nat.pos_of_ne_zero hD0
    have hQpos : 0 < Q := by
      rw [hQ]
      exact mul_pos (by linarith) (by exact_mod_cast hDpos)
    have htmono : Monotone (fun j : Fin d => (n j : ℝ) / Q) := by
      intro i j hij
      have h1 : (n i : ℝ) ≤ (n j : ℝ) := by exact_mod_cast hmono hij
      exact div_le_div_of_nonneg_right h1 (le_of_lt hQpos)
    have ht01 : ∀ j : Fin d, (n j : ℝ) / Q ∈ Set.Icc 0 1 := by
      intro j
      refine ⟨div_nonneg (Nat.cast_nonneg _) (le_of_lt hQpos), ?_⟩
      rw [div_le_one hQpos]
      exact hbound j
    have hdisc' : disc (fun j : Fin d => (n j : ℝ) / Q) ≤ ε := le_of_lt hdisc
    have hidx : ∀ j : Fin d, |(n j : ℝ) / Q - (j : ℝ) / (d : ℝ)| ≤ ε + 1 / (d : ℝ) :=
      fun j => index_error_bound hdpos _ ht01 htmono (le_of_lt hε) hdisc' j
    set a : ℝ := γ k.castSucc / (m : ℝ) with ha
    set b : ℝ := γ k.succ / (m : ℝ) with hb
    have hm0 : (0 : ℝ) < (m : ℝ) := by linarith
    have ha0 : 0 ≤ a := by
      rw [ha]
      have h : (0 : ℝ) ≤ γ k.castSucc := by
        have h' := hγmono.monotone (Fin.zero_le (k.castSucc))
        rwa [hγ0] at h'
      exact div_nonneg h (le_of_lt hm0)
    have hab : a ≤ b := by
      rw [ha, hb]
      exact div_le_div_of_nonneg_right (le_of_lt (hγmono Fin.castSucc_lt_succ)) (le_of_lt hm0)
    have hb1 : b ≤ 1 := by
      rw [hb]
      have h : γ k.succ ≤ (m : ℝ) := by
        have h' := hγmono.monotone (Fin.le_last (k.succ))
        rwa [hγlast] at h'
      rw [div_le_one hm0]
      exact h
    have hconst : (γ k.succ ^ 2 - γ k.castSucc ^ 2) * ((∑ j : Fin d, (n j : ℝ)) / (m : ℝ) ^ 2)
        = (b ^ 2 - a ^ 2) * (∑ j : Fin d, (n j : ℝ)) := by
      rw [ha, hb]
      field_simp
    rw [hconst]
    set BB : Finset (Fin d) := Finset.univ.filter (fun j : Fin d =>
      a ≤ (j : ℝ) / (d : ℝ) ∧ (j : ℝ) / (d : ℝ) < b) with hBB
    set TB : ℝ := ∑ j ∈ BB, (n j : ℝ) / Q with hTB
    set TA : ℝ := ∑ j : Fin d, (n j : ℝ) / Q with hTA
    set SB : ℝ := ∑ j ∈ BB, (n j : ℝ) with hSBdef
    set SA : ℝ := ∑ j : Fin d, (n j : ℝ) with hSAdef
    set sB : ℝ := ∑ j ∈ BB, (j : ℝ) / (d : ℝ) with hsBdef
    set eB : ℝ := ∑ j ∈ BB, ((n j : ℝ) / Q - (j : ℝ) / (d : ℝ)) with heBdef
    set sA : ℝ := ∑ j : Fin d, (j : ℝ) / (d : ℝ) with hsAdef
    set eA : ℝ := ∑ j : Fin d, ((n j : ℝ) / Q - (j : ℝ) / (d : ℝ)) with heAdef
    have hcard : ((BB.card : ℕ) : ℝ) ≤ (d : ℝ) := by
      have h : BB.card ≤ d := by
        rw [hBB]
        exact le_trans (Finset.card_filter_le _ _) (by simp)
      exact_mod_cast h
    have heB : |eB| ≤ ε * (d : ℝ) + 1 := by
      rw [heBdef]
      calc |∑ j ∈ BB, ((n j : ℝ) / Q - (j : ℝ) / (d : ℝ))|
          ≤ ∑ j ∈ BB, |(n j : ℝ) / Q - (j : ℝ) / (d : ℝ)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ j ∈ BB, (ε + 1 / (d : ℝ)) := Finset.sum_le_sum (fun j _ => hidx j)
        _ = (BB.card : ℝ) * (ε + 1 / (d : ℝ)) := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (d : ℝ) * (ε + 1 / (d : ℝ)) := mul_le_mul_of_nonneg_right hcard (by positivity)
        _ = ε * (d : ℝ) + 1 := by field_simp
    have heA : |eA| ≤ ε * (d : ℝ) + 1 := by
      rw [heAdef]
      calc |∑ j : Fin d, ((n j : ℝ) / Q - (j : ℝ) / (d : ℝ))|
          ≤ ∑ j : Fin d, |(n j : ℝ) / Q - (j : ℝ) / (d : ℝ)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ j : Fin d, (ε + 1 / (d : ℝ)) := Finset.sum_le_sum (fun j _ => hidx j)
        _ = (d : ℝ) * (ε + 1 / (d : ℝ)) := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        _ = ε * (d : ℝ) + 1 := by field_simp
    have hsplitB : TB = sB + eB := by
      rw [hTB, hsBdef, heBdef, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    have hsplitA : TA = sA + eA := by
      rw [hTA, hsAdef, heAdef, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    have hsA : sA = ((d : ℝ) - 1) / 2 := by
      rw [hsAdef]; exact sum_Fin_cast_div hdpos
    have hscaleB : SB = Q * TB := by
      rw [hSBdef, hTB, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j _ => by field_simp)
    have hscaleA : SA = Q * TA := by
      rw [hSAdef, hTA, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j _ => by field_simp)
    have hb2 : 0 ≤ b ^ 2 - a ^ 2 := by nlinarith [ha0, hab]
    have hb2' : b ^ 2 - a ^ 2 ≤ 1 := by nlinarith [ha0, hab, hb1]
    have hsB : |sB - (d : ℝ) / 2 * (b ^ 2 - a ^ 2)| ≤ 5 := by
      rw [hsBdef]
      have h := block_sum_bound (a := a) (b := b) hdpos ha0 hab hb1
      simpa only [hBB] using h
    have hmain : |SB - (b ^ 2 - a ^ 2) * SA| ≤ Q * (11 / 2 + 2 * (ε * (d : ℝ) + 1)) := by
      rw [hscaleB, hscaleA]
      have hre : Q * TB - (b ^ 2 - a ^ 2) * (Q * TA) = Q * (TB - (b ^ 2 - a ^ 2) * TA) := by
        ring
      rw [hre, abs_mul, abs_of_nonneg (le_of_lt hQpos)]
      refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hQpos)
      have hrewrite : TB - (b ^ 2 - a ^ 2) * TA
          = (sB - (b ^ 2 - a ^ 2) * ((d : ℝ) - 1) / 2) + (eB - (b ^ 2 - a ^ 2) * eA) := by
        rw [hsplitB, hsplitA, hsA]
        ring
      rw [hrewrite]
      have hA : |sB - (b ^ 2 - a ^ 2) * ((d : ℝ) - 1) / 2| ≤ 5 + (b ^ 2 - a ^ 2) / 2 := by
        have hkey : (b ^ 2 - a ^ 2) * ((d : ℝ) - 1) / 2
            = (d : ℝ) / 2 * (b ^ 2 - a ^ 2) - (b ^ 2 - a ^ 2) / 2 := by ring
        rw [hkey]
        have hrw : sB - ((d : ℝ) / 2 * (b ^ 2 - a ^ 2) - (b ^ 2 - a ^ 2) / 2)
            = (sB - (d : ℝ) / 2 * (b ^ 2 - a ^ 2)) + (b ^ 2 - a ^ 2) / 2 := by ring
        rw [hrw]
        calc |(sB - (d : ℝ) / 2 * (b ^ 2 - a ^ 2)) + (b ^ 2 - a ^ 2) / 2|
            ≤ |sB - (d : ℝ) / 2 * (b ^ 2 - a ^ 2)| + |(b ^ 2 - a ^ 2) / 2| := abs_add_le _ _
          _ = |sB - (d : ℝ) / 2 * (b ^ 2 - a ^ 2)| + (b ^ 2 - a ^ 2) / 2 := by
              rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ (b ^ 2 - a ^ 2) / 2)]
          _ ≤ 5 + (b ^ 2 - a ^ 2) / 2 := by linarith
      have hB : |eB - (b ^ 2 - a ^ 2) * eA|
          ≤ (ε * (d : ℝ) + 1) + (b ^ 2 - a ^ 2) * (ε * (d : ℝ) + 1) := by
        have h1 : |eB - (b ^ 2 - a ^ 2) * eA| ≤ |eB| + |(b ^ 2 - a ^ 2) * eA| := by
          have h := abs_add_le eB (-((b ^ 2 - a ^ 2) * eA))
          rw [abs_neg] at h
          simpa only [sub_eq_add_neg] using h
        rw [abs_mul, abs_of_nonneg hb2] at h1
        exact h1.trans (add_le_add heB (mul_le_mul_of_nonneg_left heA hb2))
      calc |(sB - (b ^ 2 - a ^ 2) * ((d : ℝ) - 1) / 2) + (eB - (b ^ 2 - a ^ 2) * eA)|
          ≤ |sB - (b ^ 2 - a ^ 2) * ((d : ℝ) - 1) / 2| + |eB - (b ^ 2 - a ^ 2) * eA| :=
            abs_add_le _ _
        _ ≤ (5 + (b ^ 2 - a ^ 2) / 2)
              + ((ε * (d : ℝ) + 1) + (b ^ 2 - a ^ 2) * (ε * (d : ℝ) + 1)) := add_le_add hA hB
        _ ≤ 11 / 2 + 2 * (ε * (d : ℝ) + 1) := by
              have hX : (0 : ℝ) ≤ ε * (d : ℝ) + 1 := by positivity
              have hprod : (b ^ 2 - a ^ 2) * (ε * (d : ℝ) + 1) ≤ 1 * (ε * (d : ℝ) + 1) :=
                mul_le_mul_of_nonneg_right hb2' hX
              nlinarith [hb2, hb2', hX, hprod]
    have hlow : Q * ((d : ℝ) / 2 - 3 / 2 - ε * (d : ℝ)) ≤ SA := by
      rw [hscaleA]
      refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hQpos)
      have key : ((d : ℝ) - 1) / 2 - (ε * (d : ℝ) + 1) ≤ TA := by
        rw [hsplitA, hsA]
        have h := neg_abs_le eA
        linarith [heA, h]
      linarith [key]
    have harith : 11 / 2 + 2 * (ε * (d : ℝ) + 1) ≤ η * ((d : ℝ) / 2 - 3 / 2 - ε * (d : ℝ)) := by
      rcases le_or_gt η 1 with hη1 | hη1
      · have h1 : ε * (d : ℝ) ≤ η * (d : ℝ) / 64 := by
          have h := mul_le_mul_of_nonneg_right hεη (by positivity : (0 : ℝ) ≤ (d : ℝ))
          linarith
        have h2 : (9 : ℝ) ≤ 29 * (η * (d : ℝ)) / 64 := by nlinarith [hηd]
        nlinarith [h1, h2, hη1, hη.le, hηd, hd64, hε.le]
      · have h1 : ε * (d : ℝ) ≤ (d : ℝ) / 64 := by
          have h := mul_le_mul_of_nonneg_right hε1 (by positivity : (0 : ℝ) ≤ (d : ℝ))
          linarith
        have h2 : (9 : ℝ) * η ≤ 29 * (η * (d : ℝ)) / 64 := by nlinarith [hηd, hη.le, hd64]
        nlinarith [h1, h2, le_of_lt hη1, hηd, hη.le, hd64, hε.le]
    calc |SB - (b ^ 2 - a ^ 2) * SA| ≤ Q * (11 / 2 + 2 * (ε * (d : ℝ) + 1)) := hmain
      _ ≤ Q * (η * ((d : ℝ) / 2 - 3 / 2 - ε * (d : ℝ))) :=
            mul_le_mul_of_nonneg_left harith (le_of_lt hQpos)
      _ = η * (Q * ((d : ℝ) / 2 - 3 / 2 - ε * (d : ℝ))) := by ring
      _ ≤ η * SA := mul_le_mul_of_nonneg_left hlow hη.le


end Work.Holonomy3
