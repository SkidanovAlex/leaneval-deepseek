import Mathlib.Algebra.Order.Archimedean.Real.Basic

namespace Commons.Analysis.Real

/-- Given a rapidly decreasing sequence of logarithmic scales `lq` (with shrinkage factor at
least `R`, where `R · η ^ (2 ^ (m-1)) ≥ 2`), there are positive integer weights `d h` with all
products `d h * lq h` comparable to a common value `D` up to a factor `1 + Θ`, and with `d`
increasing so fast that `d i ≤ η ^ (2 ^ (m-1) * (j - i)) * d j` for `i ≤ j`. -/
lemma exists_weights_of_rapidly_decreasing_scales {m : ℕ} (hm : 0 < m) (lq : Fin m → ℝ)
    (Θ η R : ℝ) (hΘ : 0 < Θ) (hη : 0 < η) (hη1 : η ≤ 1 / 2)
    (hlq : ∀ h, 1 ≤ lq h)
    (hdec : ∀ i j : Fin m, i ≤ j → R ^ ((j : ℕ) - (i : ℕ)) * lq j ≤ lq i)
    (hR : 2 ≤ R * η ^ (2 ^ (m - 1))) :
    ∃ (d : Fin m → ℕ) (D : ℝ), 0 < D ∧ (∀ h, 1 ≤ d h) ∧
      (∀ h, D ≤ (d h : ℝ) * lq h ∧ (d h : ℝ) * lq h ≤ (1 + Θ) * D) ∧
      (∀ i j : Fin m, i ≤ j →
        (d i : ℝ) ≤ η ^ (2 ^ (m - 1) * ((j : ℕ) - (i : ℕ))) * (d j : ℝ)) := by
  classical
  let z : Fin m := ⟨0, hm⟩
  let K : ℕ := 2 ^ (m - 1)
  let c : ℝ := η ^ K
  let L : ℝ := lq z
  let D : ℝ := L / Θ + 2 * L / c ^ (m - 1) + 1
  have hDdef : D = L / Θ + 2 * L / c ^ (m - 1) + 1 := rfl
  have hη1' : η ≤ 1 := by linarith
  have hcpos : 0 < c := pow_pos hη K
  have hcle1 : c ≤ 1 := pow_le_one₀ (le_of_lt hη) hη1'
  have hRc : 2 ≤ R * c := hR
  have hRpos : 0 < R := by
    have h : 0 < R * c := lt_of_lt_of_le (by norm_num) hRc
    exact pos_of_mul_pos_left h (le_of_lt hcpos)
  have hRge2 : 2 ≤ R := by
    have h1 : R * c ≤ R * 1 := mul_le_mul_of_nonneg_left hcle1 (le_of_lt hRpos)
    nlinarith [hRc, h1]
  have hRge1 : 1 ≤ R := by linarith
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one (hlq z)
  have hlq_le_L : ∀ h : Fin m, lq h ≤ L := by
    intro h
    have hzh : z ≤ h := by rw [Fin.le_def]; simp [z]
    have hd := hdec z h hzh
    have hRpow : 1 ≤ R ^ ((h : ℕ) - (z : ℕ)) := one_le_pow₀ hRge1
    have hposh : 0 ≤ lq h := le_of_lt (lt_of_lt_of_le zero_lt_one (hlq h))
    calc lq h = 1 * lq h := (one_mul _).symm
      _ ≤ R ^ ((h : ℕ) - (z : ℕ)) * lq h := mul_le_mul_of_nonneg_right hRpow hposh
      _ ≤ L := hd
  have hL_le : L ≤ Θ * D := by
    have hLD : L / Θ ≤ D := by
      rw [hDdef]
      have h2 : 0 ≤ 2 * L / c ^ (m - 1) := div_nonneg (by positivity) (by positivity)
      linarith
    have h' := (div_le_iff₀ hΘ).mp hLD
    rw [mul_comm D Θ] at h'
    exact h'
  have hDpos : 0 < D := by
    rw [hDdef]
    have h1 : 0 < L / Θ := div_pos hLpos hΘ
    have h2 : 0 ≤ 2 * L / c ^ (m - 1) := div_nonneg (by positivity) (by positivity)
    linarith
  have hD_ge : 2 * L / c ^ (m - 1) ≤ D := by
    rw [hDdef]
    have h1 : 0 ≤ L / Θ := div_nonneg (le_of_lt hLpos) (le_of_lt hΘ)
    linarith
  refine ⟨fun h => ⌈D / lq h⌉₊, D, hDpos, ?hd1, ?hcomp, ?hgrowth⟩
  · intro h
    rw [Nat.one_le_ceil_iff]
    exact div_pos hDpos (lt_of_lt_of_le zero_lt_one (hlq h))
  · intro h
    have hlqpos : 0 < lq h := lt_of_lt_of_le zero_lt_one (hlq h)
    constructor
    · have hceil := Nat.le_ceil (D / lq h)
      have h1 : (D / lq h) * lq h ≤ (⌈D / lq h⌉₊ : ℝ) * lq h :=
        mul_le_mul_of_nonneg_right hceil (le_of_lt hlqpos)
      have h2 : (D / lq h) * lq h = D := div_mul_cancel₀ D (ne_of_gt hlqpos)
      linarith [h1, h2]
    · have hceil : (⌈D / lq h⌉₊ : ℝ) < D / lq h + 1 :=
        Nat.ceil_lt_add_one (div_nonneg (le_of_lt hDpos) (le_of_lt hlqpos))
      have h1 : (⌈D / lq h⌉₊ : ℝ) * lq h < (D / lq h + 1) * lq h :=
        mul_lt_mul_of_pos_right hceil hlqpos
      have h2 : (D / lq h + 1) * lq h = D + lq h := by
        rw [add_mul, one_mul, div_mul_cancel₀ D (ne_of_gt hlqpos)]
      have h3 : lq h ≤ Θ * D := le_trans (hlq_le_L h) hL_le
      linarith [h1, h2, h3]
  · intro i j hij
    have hij' : (i : ℕ) ≤ (j : ℕ) := hij
    by_cases hlt : (i : ℕ) < (j : ℕ)
    · set t : ℕ := (j : ℕ) - (i : ℕ) with ht
      have ht1 : 1 ≤ t := by omega
      have ht_le : t ≤ m - 1 := by have hj : (j : ℕ) < m := j.isLt; omega
      have hexp : η ^ (2 ^ (m - 1) * t) = c ^ t := by
        show η ^ (K * t) = (η ^ K) ^ t
        rw [pow_mul]
      rw [hexp]
      have hlqi : 0 < lq i := lt_of_lt_of_le zero_lt_one (hlq i)
      have hlqj : 0 < lq j := lt_of_lt_of_le zero_lt_one (hlq j)
      have hb_le : lq j ≤ c ^ t * lq i / 2 := by
        have hRtp : 0 < R ^ t := pow_pos hRpos t
        have hb1 : lq j ≤ lq i / R ^ t := by
          rw [le_div_iff₀ hRtp]
          have hd := hdec i j hij
          rw [ht, mul_comm]
          exact hd
        have hRt_le : 1 / R ^ t ≤ c ^ t / 2 := by
          have hpow : (2 : ℝ) ^ t ≤ R ^ t * c ^ t := by
            have h1 : (2 : ℝ) ^ t ≤ (R * c) ^ t := pow_le_pow_left₀ (by norm_num) hRc t
            rwa [mul_pow] at h1
          have hpow2 : (2 : ℝ) ≤ (2 : ℝ) ^ t := by
            have h := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) ht1
            simpa using h
          have hmain : (2 : ℝ) ≤ R ^ t * c ^ t := le_trans hpow2 hpow
          rw [div_le_div_iff₀ hRtp (by norm_num : (0 : ℝ) < 2)]
          nlinarith [hmain]
        calc lq j ≤ lq i / R ^ t := hb1
          _ = lq i * (1 / R ^ t) := by ring
          _ ≤ lq i * (c ^ t / 2) := mul_le_mul_of_nonneg_left hRt_le (le_of_lt hlqi)
          _ = c ^ t * lq i / 2 := by ring
      have h2 : c ^ t * lq i / 2 ≤ c ^ t * lq i - lq j := by linarith
      have h1 : 2 * lq j ≤ D * c ^ t := by
        have hctp : 0 < c ^ t := pow_pos hcpos t
        have hKmin_pos : 0 < c ^ (m - 1) := pow_pos hcpos (m - 1)
        have hKmin_le : c ^ (m - 1) ≤ c ^ t :=
          pow_le_pow_of_le_one (le_of_lt hcpos) hcle1 ht_le
        have h2L : 2 * lq j ≤ 2 * L := by linarith [hlq_le_L j]
        have hB : 2 * L ≤ (2 * L / c ^ (m - 1)) * c ^ t := by
          rw [div_mul_eq_mul_div, le_div_iff₀ hKmin_pos]
          have hA : 2 * L * c ^ (m - 1) ≤ 2 * L * c ^ t :=
            mul_le_mul_of_nonneg_left hKmin_le (by linarith [hLpos])
          exact hA
        have h3 : (2 * L / c ^ (m - 1)) * c ^ t ≤ D * c ^ t :=
          mul_le_mul_of_nonneg_right hD_ge (le_of_lt hctp)
        linarith [h2L, hB, h3]
      have hDnn : 0 ≤ D := le_of_lt hDpos
      have hab : lq i * lq j ≤ D * (c ^ t * lq i - lq j) := by
        have step1 : D * (c ^ t * lq i / 2) ≤ D * (c ^ t * lq i - lq j) :=
          mul_le_mul_of_nonneg_left h2 hDnn
        have step2 : lq i * lq j ≤ D * (c ^ t * lq i / 2) := by
          have hnp : 0 ≤ lq i / 2 := div_nonneg (le_of_lt hlqi) (by norm_num)
          have hh := mul_le_mul_of_nonneg_right h1 hnp
          have hc : 2 * lq j * (lq i / 2) = lq i * lq j := by ring
          nlinarith [hh, hc]
        linarith [step1, step2]
      have hcentral : D / lq i + 1 ≤ c ^ t * D / lq j := by
        rw [div_add' D 1 (lq i) (ne_of_gt hlqi)]
        rw [div_le_div_iff₀ hlqi hlqj]
        nlinarith [hab]
      have hdi : (⌈D / lq i⌉₊ : ℝ) ≤ D / lq i + 1 :=
        le_of_lt (Nat.ceil_lt_add_one (div_nonneg (le_of_lt hDpos) (le_of_lt hlqi)))
      have hdj : D / lq j ≤ (⌈D / lq j⌉₊ : ℝ) := Nat.le_ceil _
      calc (⌈D / lq i⌉₊ : ℝ) ≤ D / lq i + 1 := hdi
        _ ≤ c ^ t * D / lq j := hcentral
        _ = c ^ t * (D / lq j) := by rw [mul_div_assoc]
        _ ≤ c ^ t * (⌈D / lq j⌉₊ : ℝ) :=
            mul_le_mul_of_nonneg_left hdj (le_of_lt (pow_pos hcpos t))
    · have heq : (i : ℕ) = (j : ℕ) := le_antisymm hij' (not_lt.mp hlt)
      have hfin : i = j := Fin.ext heq
      subst hfin
      rw [Nat.sub_self]
      simp

end Commons.Analysis.Real