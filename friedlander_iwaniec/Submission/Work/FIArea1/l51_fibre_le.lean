import Mathlib

namespace Work.FIArea1

open Finset

/-- For every integer `a`, one has `-(a.natAbs) ≤ a` (as integers). -/
lemma l51_neg_natAbs_le (a : ℤ) : -((a.natAbs : ℕ) : ℤ) ≤ a := by
  have h := Int.le_natAbs (a := -a)
  simp only [Int.natAbs_neg] at h
  linarith

/-- If `a` lies in the symmetric interval `[-K, K]` of the integers, then `a.natAbs ≤ K`. -/
lemma l51_natAbs_le_of_Icc {a : ℤ} {K : ℕ} (h1 : -((K : ℕ) : ℤ) ≤ a)
    (h2 : a ≤ ((K : ℕ) : ℤ)) : a.natAbs ≤ K := by
  have hle : a.natAbs ≤ (((K : ℕ) : ℤ)).natAbs := by
    rw [Int.natAbs_le_iff_sq_le]
    have hprod : (0 : ℤ) ≤ (((K : ℕ) : ℤ) - a) * (((K : ℕ) : ℤ) + a) :=
      mul_nonneg (sub_nonneg.mpr h2) (by linarith)
    nlinarith [hprod]
  simpa using hle

/-- **The fibre of the ratio equation at a fixed pair `(c₁,c₂)` with `c₁c₂ ≠ 0`.**

The integer pairs `(S₁,S₂)` with `S₁,S₂ ∈ [-K,K] ∖ {0}` and `c₁²S₂ = c₂²S₁` number at most
`3K/M²`, where `g = gcd(|c₁|,|c₂|)`, `a = |c₁|/g`, `b = |c₂|/g` and `M = max a b`.

*Route.* `g > 0`, `|c₁| = g a`, `|c₂| = g b`, so `c₁² = g²a²`, `c₂² = g²b²`, and cancelling `g²`
gives `a² S₂ = b² S₁`. As `(a,b) = 1` (hence `(a²,b²) = 1`), `a² ∣ S₁`; writing `S₁ = a² t`
one gets `S₂ = b² t`, so the solutions are exactly `(a²t, b²t)` — i.e. the map
`(S₁,S₂) ↦ t = S₁/a²` is injective on the fibre. Also `|S₁| = a²|t| ≤ K`, `|S₂| = b²|t| ≤ K`
and `t ≠ 0` (as `S₁ ≠ 0`). Hence the fibre injects into `{t : M²|t| ≤ K, t ≠ 0}`, a set of at
most `2(K/M²)+1` integers (those `|t| ≤ K/M²`); when the fibre is nonempty `M² ≤ K`, so
`2(K/M²)+1 ≤ 3K/M²`, and when it is empty the bound is trivial. -/
theorem l51_fibre_le (K : ℕ) (c₁ c₂ : ℤ) (hc₁ : c₁ ≠ 0) (hc₂ : c₂ ≠ 0) :
    (((((Finset.Icc (-(K : ℤ)) (K : ℤ)).erase 0).product
        ((Finset.Icc (-(K : ℤ)) (K : ℤ)).erase 0)).filter
      (fun ss : ℤ × ℤ => c₁ ^ 2 * ss.2 = c₂ ^ 2 * ss.1)).card : ℝ)
    ≤ 3 * (K : ℝ) / ((max (c₁.natAbs / c₁.natAbs.gcd c₂.natAbs)
                            (c₂.natAbs / c₁.natAbs.gcd c₂.natAbs) : ℕ) : ℝ) ^ 2 := by
  classical
  set g : ℕ := c₁.natAbs.gcd c₂.natAbs with hg
  set A : ℕ := c₁.natAbs / g with hA
  set B : ℕ := c₂.natAbs / g with hB
  set M : ℕ := max A B with hM
  set F : Finset (ℤ × ℤ) :=
    (((Finset.Icc (-(K : ℤ)) (K : ℤ)).erase 0).product
      ((Finset.Icc (-(K : ℤ)) (K : ℤ)).erase 0)).filter
      (fun ss : ℤ × ℤ => c₁ ^ 2 * ss.2 = c₂ ^ 2 * ss.1) with hF
  have hgpos : 0 < g := by
    rw [hg]
    exact Nat.gcd_pos_of_pos_left _ (Int.natAbs_pos.mpr hc₁)
  have hAg : A * g = c₁.natAbs := by
    rw [hA, hg]
    exact Nat.div_mul_cancel (Nat.gcd_dvd_left c₁.natAbs c₂.natAbs)
  have hBg : B * g = c₂.natAbs := by
    rw [hB, hg]
    exact Nat.div_mul_cancel (Nat.gcd_dvd_right c₁.natAbs c₂.natAbs)
  have hApos : 0 < A := Nat.pos_of_mul_pos_right (by rw [hAg]; exact Int.natAbs_pos.mpr hc₁)
  have hBpos : 0 < B := Nat.pos_of_mul_pos_right (by rw [hBg]; exact Int.natAbs_pos.mpr hc₂)
  have hMpos : 0 < M := by rw [hM]; exact lt_of_lt_of_le hBpos (le_max_right A B)
  have hAne : (A : ℤ) ≠ 0 := by exact_mod_cast (ne_of_gt hApos)
  have hA2ne : ((A : ℤ) ^ 2) ≠ 0 := pow_ne_zero 2 hAne
  have hgne : (g : ℤ) ≠ 0 := by exact_mod_cast (ne_of_gt hgpos)
  have hcopZ : IsCoprime ((A : ℤ) ^ 2) ((B : ℤ) ^ 2) := by
    have hgpos' : 0 < c₁.natAbs.gcd c₂.natAbs := by rw [← hg]; exact hgpos
    have hAB : Nat.Coprime A B := by
      rw [hA, hB, hg]
      exact Nat.coprime_div_gcd_div_gcd hgpos'
    have h2 : Nat.Coprime (A ^ 2) (B ^ 2) := hAB.pow 2 2
    simpa using h2.isCoprime
  have hc1 : c₁ ^ 2 = (A : ℤ) ^ 2 * (g : ℤ) ^ 2 := by
    rw [← Int.natAbs_sq c₁, ← hAg]
    push_cast
    ring
  have hc2 : c₂ ^ 2 = (B : ℤ) ^ 2 * (g : ℤ) ^ 2 := by
    rw [← Int.natAbs_sq c₂, ← hBg]
    push_cast
    ring
  have hkey : ∀ S₁ S₂ : ℤ, c₁ ^ 2 * S₂ = c₂ ^ 2 * S₁ → (A : ℤ) ^ 2 * S₂ = (B : ℤ) ^ 2 * S₁ := by
    intro S₁ S₂ h
    have h2 : (g : ℤ) ^ 2 * ((A : ℤ) ^ 2 * S₂) = (g : ℤ) ^ 2 * ((B : ℤ) ^ 2 * S₁) := by
      rw [hc1, hc2] at h
      nlinarith [h]
    exact mul_left_cancel₀ (pow_ne_zero 2 hgne) h2
  have hA2dvd : ∀ S₁ S₂ : ℤ, c₁ ^ 2 * S₂ = c₂ ^ 2 * S₁ → (A : ℤ) ^ 2 ∣ S₁ := by
    intro S₁ S₂ h
    have hk := hkey S₁ S₂ h
    exact IsCoprime.dvd_of_dvd_mul_left hcopZ ⟨S₂, hk.symm⟩
  set N : ℕ := K / M ^ 2 with hN
  set T : Finset ℤ := (Finset.Icc (-(N : ℤ)) (N : ℤ)).erase 0 with hT
  have hcardT : T.card = 2 * N := by
    rw [hT]
    have h0mem : (0 : ℤ) ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) := by
      rw [Finset.mem_Icc]; exact ⟨by simp, by simp⟩
    rw [Finset.card_erase_of_mem h0mem, Int.card_Icc]
    have h1 : ((N : ℤ) + 1 - (-(N : ℤ))).toNat = 2 * N + 1 := by
      rw [show (N : ℤ) + 1 - (-(N : ℤ)) = ((2 * N + 1 : ℕ) : ℤ) by push_cast; ring,
        Int.toNat_natCast]
    rw [h1]
    omega
  have hsub : F ⊆ T.image (fun t : ℤ => ((A : ℤ) ^ 2 * t, (B : ℤ) ^ 2 * t)) := by
    intro ss hss
    rw [hF] at hss
    simp only [Finset.mem_filter, Finset.mem_product, Finset.product_eq_sprod,
      Finset.mem_erase, Finset.mem_Icc] at hss
    obtain ⟨⟨⟨hs1ne, hs1lo, hs1hi⟩, hs2ne, hs2lo, hs2hi⟩, heq⟩ := hss
    obtain ⟨t, ht⟩ := hA2dvd ss.1 ss.2 heq
    have htne : t ≠ 0 := by
      intro h0; rw [h0, mul_zero] at ht; exact hs1ne ht
    have ht2 : ss.2 = (B : ℤ) ^ 2 * t := by
      have h1 : (A : ℤ) ^ 2 * ss.2 = (A : ℤ) ^ 2 * ((B : ℤ) ^ 2 * t) := by
        rw [hkey ss.1 ss.2 heq, ht]; ring
      exact mul_left_cancel₀ hA2ne h1
    have hle1 : ss.1.natAbs ≤ K := l51_natAbs_le_of_Icc hs1lo hs1hi
    have hle2 : ss.2.natAbs ≤ K := l51_natAbs_le_of_Icc hs2lo hs2hi
    have hA2t : A ^ 2 * t.natAbs ≤ K := by
      have h : ss.1.natAbs = A ^ 2 * t.natAbs := by
        rw [ht, Int.natAbs_mul, Int.natAbs_pow]; simp
      rwa [h] at hle1
    have hB2t : B ^ 2 * t.natAbs ≤ K := by
      have h : ss.2.natAbs = B ^ 2 * t.natAbs := by
        rw [ht2, Int.natAbs_mul, Int.natAbs_pow]; simp
      rwa [h] at hle2
    have hM2t : M ^ 2 * t.natAbs ≤ K := by
      rw [hM]
      rcases le_total A B with h | h
      · rw [max_eq_right h]; exact hB2t
      · rw [max_eq_left h]; exact hA2t
    have htn : t.natAbs ≤ N := by
      rw [hN]
      exact (Nat.le_div_iff_mul_le (pow_pos hMpos 2)).mpr
        (by rw [mul_comm]; exact hM2t)
    rw [Finset.mem_image]
    refine ⟨t, ?_, ?_⟩
    · rw [hT, Finset.mem_erase, Finset.mem_Icc]
      refine ⟨htne, ?_, ?_⟩
      · have h1 : ((t.natAbs : ℕ) : ℤ) ≤ ((N : ℕ) : ℤ) := by exact_mod_cast htn
        have h2 : -((t.natAbs : ℕ) : ℤ) ≤ t := l51_neg_natAbs_le t
        linarith
      · have h1 : ((t.natAbs : ℕ) : ℤ) ≤ ((N : ℕ) : ℤ) := by exact_mod_cast htn
        have h2 : t ≤ ((t.natAbs : ℕ) : ℤ) := Int.le_natAbs
        linarith
    · exact Prod.ext ht.symm ht2.symm
  have hcard : (F.card : ℝ) ≤ 2 * (N : ℝ) := by
    calc (F.card : ℝ)
        ≤ ((T.image (fun t : ℤ => ((A : ℤ) ^ 2 * t, (B : ℤ) ^ 2 * t))).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub
      _ ≤ (T.card : ℝ) := by exact_mod_cast Finset.card_image_le
      _ = ((2 * N : ℕ) : ℝ) := by rw [hcardT]
      _ = 2 * (N : ℝ) := by push_cast; ring
  have hNle : (N : ℝ) ≤ (K : ℝ) / (M : ℝ) ^ 2 := by
    rw [hN]
    have h := Nat.cast_div_le (α := ℝ) (m := K) (n := M ^ 2)
    simpa [Nat.cast_pow] using h
  calc (F.card : ℝ) ≤ 2 * (N : ℝ) := hcard
    _ ≤ 2 * ((K : ℝ) / (M : ℝ) ^ 2) := by linarith [hNle]
    _ ≤ 3 * ((K : ℝ) / (M : ℝ) ^ 2) := by
        have hnn : 0 ≤ (K : ℝ) / (M : ℝ) ^ 2 :=
          div_nonneg (Nat.cast_nonneg K) (sq_nonneg (M : ℝ))
        linarith
    _ = 3 * (K : ℝ) / (M : ℝ) ^ 2 := by ring

end Work.FIArea1
