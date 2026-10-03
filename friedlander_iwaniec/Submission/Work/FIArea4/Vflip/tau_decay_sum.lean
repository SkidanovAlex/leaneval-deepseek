import Mathlib

open MeasureTheory Filter Set

namespace Work.FIArea4.Vflip

open Classical

lemma tauDecay_pt1 {δ μ : ℝ} (hμ : 0 < μ) (x : ℝ) (hx : 0 ≤ x) :
    x^δ * (1 + x/μ)^(-(2:ℝ)) ≤ x^δ := by
  have h : (1:ℝ) ≤ 1 + x/μ := by
    have : 0 ≤ x/μ := div_nonneg hx (le_of_lt hμ)
    linarith
  have h2 : (1 + x/μ)^(-(2:ℝ)) ≤ 1 := by
    apply Real.rpow_le_one_of_one_le_of_nonpos h
    norm_num
  calc x^δ * (1 + x/μ)^(-(2:ℝ)) ≤ x^δ * 1 :=
        mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg hx _)
    _ = x^δ := by ring

lemma tauDecay_pt2 {δ μ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) (hμ : 0 < μ) (x : ℝ) (hx : 0 ≤ x) :
    x^δ * (1 + x/μ)^(-(2:ℝ)) ≤ μ^2 * x^(δ-2) := by
  rcases eq_or_lt_of_le hx with h | h
  · rw [← h, Real.zero_rpow hδ0.ne', zero_mul,
      Real.zero_rpow (by linarith : δ - 2 ≠ 0), mul_zero]
  · have hxp : 0 < x := h
    have h1 : (1 + x/μ)^(-(2:ℝ)) = μ^2/(μ+x)^2 := by
      rw [show (1 + x/μ) = (μ+x)/μ by field_simp]
      simp only [Real.rpow_neg (show (0:ℝ) ≤ (μ+x)/μ by positivity), Real.rpow_two,
        div_pow, inv_div]
    rw [h1]
    have hxs : x^(δ-2) * x^2 = x^δ := by
      rw [← Real.rpow_two, ← Real.rpow_add hxp (δ-2) 2, show (δ-2)+2 = δ by ring]
    have hstep : x^(δ-2) * x^2 ≤ x^(δ-2) * (μ+x)^2 := by
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hx (δ-2))
      exact pow_le_pow_left₀ hx (by linarith) 2
    calc x^δ * (μ^2/(μ+x)^2)
        = x^(δ-2) * x^2 * (μ^2/(μ+x)^2) := by rw [← hxs]
      _ ≤ x^(δ-2) * (μ+x)^2 * (μ^2/(μ+x)^2) :=
            mul_le_mul_of_nonneg_right hstep (by positivity)
      _ = μ^2 * x^(δ-2) := by field_simp

lemma tauDecay_half_le_of_floor {μ : ℝ} {N : ℕ} (hμ : 1 ≤ μ) (_hNle : (N:ℝ) ≤ μ)
    (hNlt : μ < (N:ℝ) + 1) : μ / 2 ≤ (N:ℝ) := by
  by_cases h : μ < 2
  · have hNpos : (0:ℝ) < (N:ℝ) := by linarith
    have hN1 : (1:ℝ) ≤ (N:ℝ) := by
      have : (0:ℕ) < N := by exact_mod_cast hNpos
      exact_mod_cast this
    linarith
  · simp only [not_lt] at h
    have h1 : μ - 1 < (N:ℝ) := by linarith
    linarith

lemma tauDecay_tail_bound {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) (N : ℕ) (hN : 1 ≤ N) :
    (∑' i : ℕ, ((i + N + 1 : ℕ) : ℝ) ^ (δ - 2)) ≤ (N : ℝ) ^ (δ - 1) / (1 - δ) := by
  have hd2 : δ - 2 < -1 := by linarith
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  have hanti : AntitoneOn (fun x : ℝ => x ^ (δ - 2)) (Set.Ici (N : ℝ)) :=
    (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by linarith : δ - 2 ≤ 0)).mono
      (fun x hx => lt_of_lt_of_le hNr hx)
  have hint : IntegrableOn (fun x : ℝ => x ^ (δ - 2)) (Set.Ioi (N : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt hd2 hNr
  have hnn : ∀ t ∈ Set.Ioi (N : ℝ), 0 ≤ t ^ (δ - 2) :=
    fun t ht => Real.rpow_nonneg (le_of_lt (lt_of_lt_of_le hNr (le_of_lt ht))) _
  have h := AntitoneOn.tsum_comp_add_le_integral (f := fun x : ℝ => x ^ (δ - 2)) N hanti hint hnn
  refine h.trans ?_
  rw [integral_Ioi_rpow_of_lt hd2 hNr]
  rw [show (δ - 2) + 1 = δ - 1 by ring]
  rw [show -(N:ℝ) ^ (δ-1) / (δ-1) = (N:ℝ)^(δ-1)/(1-δ) by
      rw [show (1:ℝ) - δ = -(δ-1) by ring, div_neg]; ring]

lemma tauDecay_rpow_two_le (a : ℝ) (ha : a ≤ 1) : (2:ℝ)^a ≤ 2 := by
  have h := Real.rpow_le_rpow_of_exponent_le (show (1:ℝ) ≤ 2 by norm_num) ha
  rwa [Real.rpow_one] at h

noncomputable def tauDecayNterm (δ μ : ℝ) : ℕ → ℝ :=
  fun n => (n:ℝ) ^ δ * (1 + (n:ℝ) / μ) ^ (-(2:ℝ))

noncomputable def tauDecayZterm (δ μ : ℝ) : ℤ → ℝ :=
  fun k => (k.natAbs : ℝ) ^ δ * (1 + |(k:ℝ)| / μ) ^ (-(2:ℝ))

lemma tauDecay_nterm_summable {δ μ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) (hμ : 0 < μ) :
    Summable (tauDecayNterm δ μ) := by
  have hbase : Summable (fun n : ℕ => (n:ℝ)^(δ-2)) := Real.summable_nat_rpow.mpr (by linarith)
  have hmaj : Summable (fun n : ℕ => μ^2 * (n:ℝ)^(δ-2)) := hbase.mul_left _
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hmaj
  · simp only [tauDecayNterm]
    exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)
      (Real.rpow_nonneg (by positivity) _)
  · simp only [tauDecayNterm]
    exact tauDecay_pt2 hδ0 hδ1 hμ (n:ℝ) (Nat.cast_nonneg n)

lemma tauDecay_nat_sum_bound (δ μ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hμ : 0 < μ) :
    (∑' n : ℕ, tauDecayNterm δ μ n) ≤ 4/(1-δ) * μ^(1+δ) := by
  have hf : Summable (tauDecayNterm δ μ) := tauDecay_nterm_summable hδ0 hδ1 hμ
  obtain ⟨N, hNle, hNlt⟩ : ∃ N : ℕ, (N:ℝ) ≤ μ ∧ μ < (N:ℝ) + 1 :=
    ⟨⌊μ⌋₊, Nat.floor_le (le_of_lt hμ), Nat.lt_floor_add_one μ⟩
  have hsplit := Summable.sum_add_tsum_nat_add (f := tauDecayNterm δ μ) (N+1) hf
  have hhead : (∑ i ∈ Finset.range (N+1), tauDecayNterm δ μ i) ≤ 2 * μ^(1+δ) := by
    have h1 : ∀ i ∈ Finset.range (N+1), tauDecayNterm δ μ i ≤ (N:ℝ)^δ := by
      intro i hi
      rw [Finset.mem_range] at hi
      have hiN : (i:ℝ) ≤ (N:ℝ) := by exact_mod_cast Nat.le_of_lt_succ hi
      calc tauDecayNterm δ μ i = (i:ℝ)^δ * (1 + (i:ℝ)/μ)^(-(2:ℝ)) := rfl
        _ ≤ (i:ℝ)^δ := tauDecay_pt1 hμ (i:ℝ) (Nat.cast_nonneg i)
        _ ≤ (N:ℝ)^δ := Real.rpow_le_rpow (Nat.cast_nonneg i) hiN (le_of_lt hδ0)
    calc (∑ i ∈ Finset.range (N+1), tauDecayNterm δ μ i)
        ≤ ∑ i ∈ Finset.range (N+1), (N:ℝ)^δ := Finset.sum_le_sum h1
      _ = ((N+1 : ℕ) : ℝ) * (N:ℝ)^δ := by simp
      _ ≤ 2 * μ^(1+δ) := by
          rcases Nat.eq_zero_or_pos N with hN0 | hNpos
          · subst hN0
            simp only [Nat.cast_zero]
            rw [Real.zero_rpow hδ0.ne', mul_zero]
            positivity
          · have hN1R : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hNpos
            have hNp : (0:ℝ) < (N:ℝ) := by exact_mod_cast hNpos
            have hkey : ((N:ℝ)+1) * (N:ℝ)^δ ≤ 2 * (N:ℝ)^(1+δ) := by
              rw [Real.rpow_add hNp 1 δ, Real.rpow_one]
              nlinarith [Real.rpow_nonneg (le_of_lt hNp) δ, hN1R]
            calc ((N+1 : ℕ) : ℝ) * (N:ℝ)^δ = ((N:ℝ)+1) * (N:ℝ)^δ := by
                  rw [Nat.cast_add, Nat.cast_one]
              _ ≤ 2 * (N:ℝ)^(1+δ) := hkey
              _ ≤ 2 * μ^(1+δ) := by
                  apply mul_le_mul_of_nonneg_left _ (by norm_num)
                  exact Real.rpow_le_rpow (Nat.cast_nonneg N) hNle (by linarith)
  have htail : (∑' i : ℕ, tauDecayNterm δ μ (i + (N+1))) ≤ 2/(1-δ) * μ^(1+δ) := by
    have hb : Summable (fun n : ℕ => (n:ℝ)^(δ-2)) := Real.summable_nat_rpow.mpr (by linarith)
    rcases Nat.eq_zero_or_pos N with hN0 | hNpos
    · subst hN0
      have hps : ∀ i : ℕ, tauDecayNterm δ μ (i + 1) ≤ μ^2 * (((i + 1 : ℕ)):ℝ)^(δ-2) := by
        intro i
        have := tauDecay_pt2 hδ0 hδ1 hμ (((i + 1 : ℕ)):ℝ) (Nat.cast_nonneg _)
        simpa [tauDecayNterm] using this
      have hsl : Summable (fun i : ℕ => tauDecayNterm δ μ (i + 1)) := (summable_nat_add_iff 1).mpr hf
      have hsr : Summable (fun i : ℕ => μ^2 * (((i + 1 : ℕ)):ℝ)^(δ-2)) :=
        ((summable_nat_add_iff 1).mpr hb).mul_left _
      have hle := Summable.tsum_le_tsum hps hsl hsr
      rw [tsum_mul_left] at hle
      refine hle.trans ?_
      have hs2 : Summable (fun i : ℕ => (((i + 1 : ℕ)):ℝ)^(δ-2)) := (summable_nat_add_iff 1).mpr hb
      have hzero : (∑' i : ℕ, (((i + 1 : ℕ)):ℝ)^(δ-2))
          = 1 + ∑' i : ℕ, (((i + 2 : ℕ)):ℝ)^(δ-2) := by
        rw [Summable.tsum_eq_zero_add hs2]
        have h0 : (((0 + 1 : ℕ)):ℝ)^(δ-2) = 1 := by
          simp only [Nat.zero_add, Nat.cast_one, Real.one_rpow]
        rw [h0]
      have htb := tauDecay_tail_bound hδ0 hδ1 1 (le_refl 1)
      simp only [Nat.cast_one, Real.one_rpow] at htb
      have hT : (∑' i : ℕ, (((i + 1 : ℕ)):ℝ)^(δ-2)) ≤ (2-δ)/(1-δ) := by
        rw [hzero]
        have hsum : (∑' i : ℕ, (((i + 2 : ℕ)):ℝ)^(δ-2)) ≤ 1/(1-δ) := htb
        have : (1:ℝ) + 1/(1-δ) = (2-δ)/(1-δ) := by
          have h1d : (1:ℝ) - δ ≠ 0 := by linarith
          nth_rewrite 1 [show (1:ℝ) = (1-δ)/(1-δ) by rw [div_self h1d]]
          rw [← add_div]
          congr 1
          ring
        linarith [hsum, this]
      have hμ1 : μ < 1 := by
        have h := hNlt
        simp only [Nat.cast_zero, zero_add] at h
        exact h
      have hμsq : μ^(2:ℝ) ≤ μ^(1+δ) :=
        Real.rpow_le_rpow_of_exponent_ge hμ (le_of_lt hμ1) (by linarith : 1 + δ ≤ 2)
      rw [show μ^2 = μ^(2:ℝ) by rw [Real.rpow_two]]
      calc μ^(2:ℝ) * (∑' i : ℕ, (((i + 1 : ℕ)):ℝ)^(δ-2))
          ≤ μ^(2:ℝ) * ((2-δ)/(1-δ)) := mul_le_mul_of_nonneg_left hT (Real.rpow_nonneg (le_of_lt hμ) _)
        _ = μ^(2:ℝ) * (2-δ) / (1-δ) := by ring
        _ ≤ μ^(1+δ) * 2 / (1-δ) := by
              apply div_le_div_of_nonneg_right _ (by linarith)
              apply mul_le_mul hμsq _ _ (Real.rpow_nonneg (le_of_lt hμ) _)
              · linarith
              · linarith
        _ = 2/(1-δ) * μ^(1+δ) := by ring
    · have hps : ∀ i : ℕ, tauDecayNterm δ μ (i + (N+1)) ≤ μ^2 * (((i + (N+1) : ℕ)):ℝ)^(δ-2) := by
        intro i
        have := tauDecay_pt2 hδ0 hδ1 hμ (((i + (N+1) : ℕ)):ℝ) (Nat.cast_nonneg _)
        simpa [tauDecayNterm] using this
      have hsl : Summable (fun i : ℕ => tauDecayNterm δ μ (i + (N+1))) :=
        (summable_nat_add_iff (N+1)).mpr hf
      have hsr : Summable (fun i : ℕ => μ^2 * (((i + (N+1) : ℕ)):ℝ)^(δ-2)) :=
        ((summable_nat_add_iff (N+1)).mpr hb).mul_left _
      have hle := Summable.tsum_le_tsum hps hsl hsr
      rw [tsum_mul_left] at hle
      refine hle.trans ?_
      have hT : (∑' i : ℕ, (((i + (N+1) : ℕ)):ℝ)^(δ-2)) ≤ (N:ℝ)^(δ-1)/(1-δ) :=
        tauDecay_tail_bound hδ0 hδ1 N hNpos
      have hN1 : (1:ℕ) ≤ N := hNpos
      have hμ1 : (1:ℝ) ≤ μ := by
        have hNr : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN1
        linarith [hNle]
      have hhalf : μ/2 ≤ (N:ℝ) := tauDecay_half_le_of_floor hμ1 hNle hNlt
      have hNp : (0:ℝ) < N := by exact_mod_cast hNpos
      have hμ2p : (0:ℝ) < μ/2 := by linarith
      have hpow : (N:ℝ)^(δ-1) ≤ (μ/2)^(δ-1) :=
        Real.rpow_le_rpow_of_nonpos hμ2p hhalf (by linarith)
      have hdiv : (μ/2)^(δ-1) = μ^(δ-1) * 2^(1-δ) := by
        rw [Real.div_rpow (le_of_lt hμ) (by norm_num : (0:ℝ) ≤ 2), div_eq_mul_inv,
            ← Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2) (δ-1),
            show -(δ-1) = 1-δ by ring]
      have hkey : μ^2 * (N:ℝ)^(δ-1) ≤ 2^(1-δ)*μ^(1+δ) := by
        calc μ^2 * (N:ℝ)^(δ-1) ≤ μ^2 * ((μ/2)^(δ-1)) :=
              mul_le_mul_of_nonneg_left hpow (by positivity)
          _ = 2^(1-δ)*μ^(1+δ) := by
              rw [hdiv, ← mul_assoc,
                show μ^2 * μ^(δ-1) = μ^(1+δ) by
                  rw [show μ^2 = μ^(2:ℝ) by rw [Real.rpow_two]]
                  rw [← Real.rpow_add hμ 2 (δ-1), show (2:ℝ)+(δ-1) = 1+δ by ring]]
              ring
      calc μ^2 * (∑' i : ℕ, (((i + (N+1) : ℕ)):ℝ)^(δ-2))
          ≤ μ^2 * ((N:ℝ)^(δ-1)/(1-δ)) :=
              mul_le_mul_of_nonneg_left hT (by positivity)
        _ = μ^2 * (N:ℝ)^(δ-1) / (1-δ) := by ring
        _ ≤ 2^(1-δ)*μ^(1+δ)/(1-δ) := div_le_div_of_nonneg_right hkey (by linarith)
        _ ≤ 2/(1-δ)*μ^(1+δ) := by
              have h2 : (2:ℝ)^(1-δ) ≤ 2 := tauDecay_rpow_two_le (1-δ) (by linarith)
              calc 2^(1-δ)*μ^(1+δ)/(1-δ)
                  = (2^(1-δ)*μ^(1+δ))/(1-δ) := by ring
                _ ≤ (2*μ^(1+δ))/(1-δ) := by
                    apply div_le_div_of_nonneg_right _ (by linarith)
                    exact mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg (le_of_lt hμ) _)
                _ = 2/(1-δ)*μ^(1+δ) := by ring
  rw [← hsplit]
  calc (∑ i ∈ Finset.range (N+1), tauDecayNterm δ μ i) + (∑' i : ℕ, tauDecayNterm δ μ (i + (N+1)))
      ≤ 2 * μ^(1+δ) + 2/(1-δ) * μ^(1+δ) := add_le_add hhead htail
    _ = (2 + 2/(1-δ)) * μ^(1+δ) := by ring
    _ ≤ 4/(1-δ) * μ^(1+δ) := by
        apply mul_le_mul_of_nonneg_right _ (le_of_lt (Real.rpow_pos_of_pos hμ _))
        have hle1 : (2:ℝ) ≤ 2/(1-δ) := by
          rw [le_div_iff₀ (by linarith : (0:ℝ) < 1-δ)]; linarith
        rw [show (4:ℝ)/(1-δ) = 2/(1-δ) + 2/(1-δ) by ring]
        linarith [hle1]


theorem tau_decay_sum : ∀ δ : ℝ, 0 < δ → δ < 1 → ∃ C : ℝ, 0 < C ∧
    ∀ μ : ℝ, 0 < μ →
      (∑' k : ℤ, (k.natAbs : ℝ) ^ δ * (1 + |(k:ℝ)| / μ) ^ (-(2:ℝ))) ≤ C * μ ^ (1 + δ) := by
  intro δ hδ0 hδ1
  refine ⟨8/(1-δ), ?_, ?_⟩
  · exact div_pos (by norm_num) (by linarith)
  · intro μ hμ
    have hpt : ∀ k : ℤ, tauDecayZterm δ μ k ≤ μ^2 * |(k:ℝ)|^(δ-2) := by
      intro k
      have h := tauDecay_pt2 hδ0 hδ1 hμ |(k:ℝ)| (abs_nonneg _)
      simpa [tauDecayZterm, Int.natCast_natAbs] using h
    have hsumabs : Summable (fun k : ℤ => |(k:ℝ)|^(δ-2)) := by
      refine (Real.summable_abs_int_rpow (b := 2-δ) (by linarith)).congr (fun k => ?_)
      rw [show -(2-δ) = δ-2 by ring]
    have hsummaj : Summable (fun k : ℤ => μ^2 * |(k:ℝ)|^(δ-2)) := hsumabs.mul_left _
    have hgs : Summable (tauDecayZterm δ μ) := by
      refine Summable.of_nonneg_of_le (fun k => ?_) hpt hsummaj
      simp only [tauDecayZterm]
      exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
        (Real.rpow_nonneg (by positivity) _)
    have hEven : Function.Even (tauDecayZterm δ μ) := by
      intro k
      simp [tauDecayZterm]
    have hg0 : tauDecayZterm δ μ 0 = 0 := by
      simp [tauDecayZterm, Real.zero_rpow hδ0.ne']
    have hrei := tsum_int_eq_zero_add_two_mul_tsum_pnat hEven hgs
    have hpn : (∑' n : ℕ+, tauDecayZterm δ μ ↑↑n) = ∑' n : ℕ, tauDecayNterm δ μ n := by
      have h1 : (∑' n : ℕ+, tauDecayZterm δ μ ↑↑n) = ∑' n : ℕ, tauDecayZterm δ μ (n:ℤ) :=
        tsum_pnat_eq_tsum_of_eq_zero (f := fun n : ℕ => tauDecayZterm δ μ (n:ℤ)) hg0
      rw [h1]
      apply tsum_congr
      intro n
      simp [tauDecayZterm, tauDecayNterm]
    have hmain : (∑' k : ℤ, tauDecayZterm δ μ k) = 2 * (∑' n : ℕ, tauDecayNterm δ μ n) := by
      rw [hrei, hg0, zero_add, hpn, nsmul_eq_mul]
      norm_num
    change (∑' k : ℤ, tauDecayZterm δ μ k) ≤ 8/(1-δ) * μ ^ (1 + δ)
    rw [hmain]
    have hS := tauDecay_nat_sum_bound δ μ hδ0 hδ1 hμ
    have h2 := mul_le_mul_of_nonneg_left hS (by norm_num : (0:ℝ) ≤ 2)
    rw [show (2:ℝ) * (4/(1-δ)*μ^(1+δ)) = 8/(1-δ)*μ^(1+δ) by ring] at h2
    exact h2


end Work.FIArea4.Vflip
