import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Integral.Pi

open MeasureTheory
open scoped BigOperators

namespace Commons.Analysis.Convolution

/-- Pointwise domination of the one-dimensional tent `(max 1 u)^{-s}` by a
positive nice function: for `s ≥ 0`, `u ≥ 0`,
`(max 1 u)^{-s} ≤ 2^s (1 + u)^{-s}`. -/
private lemma max_one_rpow_neg_le {s u : ℝ} (hs : 0 ≤ s) (hu : 0 ≤ u) :
    (max 1 u) ^ (-s) ≤ (2 : ℝ) ^ s * (1 + u) ^ (-s) := by
  set M := max 1 u with hM
  have hM1 : 1 ≤ M := le_max_left _ _
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM1
  have hupos : 0 < 1 + u := by linarith
  have hbound : 1 + u ≤ 2 * M := by
    rcases le_total u 1 with h | h
    · rw [hM, max_eq_left h]; linarith
    · rw [hM, max_eq_right h]; linarith
  have hkey : (1 + u) ^ s / (2 : ℝ) ^ s ≤ M ^ s := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ s)]
    have h := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ 1 + u) hbound hs
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hMpos.le] at h
    simpa [mul_comm] using h
  have h2pos : 0 < (2 : ℝ) ^ s := Real.rpow_pos_of_pos (by norm_num) s
  have hdpos : 0 < (1 + u) ^ s / (2 : ℝ) ^ s :=
    div_pos (Real.rpow_pos_of_pos hupos s) h2pos
  calc (max 1 u) ^ (-s) = M ^ (-s) := by rw [hM]
    _ = (M ^ s)⁻¹ := Real.rpow_neg hMpos.le s
    _ ≤ ((1 + u) ^ s / (2 : ℝ) ^ s)⁻¹ :=
        (inv_le_inv₀ (Real.rpow_pos_of_pos hMpos s) hdpos).mpr hkey
    _ = (2 : ℝ) ^ s * (1 + u) ^ (-s) := by
        rw [inv_div, div_eq_mul_inv, ← Real.rpow_neg hupos.le s]

/-- One-dimensional base case: for `c > 0` and `s > 1`, the function
`t ↦ (1 + |c * t|)^{-s}` is integrable on `ℝ`. -/
private lemma integrable_one_add_abs_mul_rpow_neg {c s : ℝ} (hc : 0 < c) (hs : 1 < s) :
    Integrable (fun t : ℝ => (1 + |c * t|) ^ (-s)) (volume : Measure ℝ) := by
  have hs0 : 0 ≤ s := le_of_lt (lt_trans zero_lt_one hs)
  have hbase : Integrable (fun t : ℝ => (1 + |t|) ^ (-s)) (volume : Measure ℝ) := by
    have h := integrable_one_add_norm (E := ℝ) (μ := (volume : Measure ℝ)) (r := s)
      (by simpa [Module.finrank_self] using hs)
    simpa [Real.norm_eq_abs] using h
  set c' := min c 1 with hc'
  have hc'pos : 0 < c' := lt_min hc zero_lt_one
  have hc'le1 : c' ≤ 1 := min_le_right _ _
  have hc'lec : c' ≤ c := min_le_left _ _
  have hbnd : ∀ t : ℝ, c' * (1 + |t|) ≤ 1 + |c * t| := by
    intro t
    have h1 : c' * 1 ≤ 1 := by simpa using hc'le1
    have h2 : c' * |t| ≤ c * |t| := mul_le_mul_of_nonneg_right hc'lec (abs_nonneg t)
    rw [abs_mul, abs_of_pos hc]
    calc c' * (1 + |t|) = c' * 1 + c' * |t| := by ring
      _ ≤ 1 + c * |t| := add_le_add h1 h2
  have hle : ∀ t : ℝ, (1 + |c * t|) ^ (-s) ≤ c' ^ (-s) * (1 + |t|) ^ (-s) := by
    intro t
    have hx : 0 < c' * (1 + |t|) := mul_pos hc'pos (by positivity)
    calc (1 + |c * t|) ^ (-s)
        ≤ (c' * (1 + |t|)) ^ (-s) :=
          Real.rpow_le_rpow_of_nonpos hx (hbnd t) (neg_nonpos.mpr hs0)
      _ = c' ^ (-s) * (1 + |t|) ^ (-s) := Real.mul_rpow hc'pos.le (by positivity)
  refine (hbase.const_mul (c' ^ (-s))).mono' ?_ ?_
  · apply Continuous.aestronglyMeasurable
    apply Continuous.rpow_const
    · exact continuous_const.add ((continuous_const.mul continuous_id).abs)
    · intro t; exact Or.inl (by positivity)
  · filter_upwards with t
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _)]
    exact hle t

/-- Pointwise bound for the anisotropic tent: with `s = A / k`, the tent
`(max 1 (max_i |c_i y_i|))^{-A}` is dominated by the product of the one-dimensional
profiles `∏_i (1 + |c_i y_i|)^{-s}` (times a constant). -/
private lemma tent_bound (k : ℕ) (hk : 1 ≤ k) {A s : ℝ} (hA : (k : ℝ) < A)
    (hs : s = A / (k : ℝ)) (c : Fin k → ℝ) (y : Fin k → ℝ) :
    (max 1 ((Finset.univ : Finset (Fin k)).sup' ⟨⟨0, hk⟩, Finset.mem_univ _⟩
        fun i => |c i * y i|)) ^ (-A)
    ≤ ((2 : ℝ) ^ s) ^ k * ∏ i, (1 + |c i * y i|) ^ (-s) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  have hkRne : (k : ℝ) ≠ 0 := ne_of_gt hkR
  have hApos : 0 < A := lt_trans hkR hA
  have hs0 : 0 ≤ s := by rw [hs]; exact div_nonneg hApos.le hkR.le
  have hks : (k : ℝ) * s = A := by rw [hs]; exact mul_div_cancel₀ A hkRne
  set t := (Finset.univ : Finset (Fin k)).sup' ⟨⟨0, hk⟩, Finset.mem_univ _⟩
      (fun i => |c i * y i|) with ht
  set m := max 1 t with hm
  have hb_pos : ∀ i, 0 < max 1 |c i * y i| := fun i => lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hb_le_m : ∀ i, max 1 |c i * y i| ≤ m := by
    intro i
    have hle_t : |c i * y i| ≤ t := by
      rw [ht]
      exact Finset.le_sup' (fun j => |c j * y j|) (Finset.mem_univ i)
    rw [hm]; exact max_le (le_max_left _ _) (le_trans hle_t (le_max_right _ _))
  have hprod_le : ∏ i : Fin k, max 1 |c i * y i| ≤ m ^ k := by
    calc ∏ i : Fin k, max 1 |c i * y i| ≤ ∏ _i : Fin k, m :=
          Finset.prod_le_prod (fun i _ => (hb_pos i).le) (fun i _ => hb_le_m i)
      _ = m ^ k := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hprod_pos : 0 < ∏ i : Fin k, max 1 |c i * y i| := Finset.prod_pos (fun i _ => hb_pos i)
  have hm_nonneg : 0 ≤ m := by rw [hm]; exact le_trans zero_le_one (le_max_left _ _)
  have hstep_d : (m ^ k) ^ (-s) ≤ (∏ i : Fin k, max 1 |c i * y i|) ^ (-s) :=
    Real.rpow_le_rpow_of_nonpos hprod_pos hprod_le (neg_nonpos.mpr hs0)
  have hstep_e : (m ^ k) ^ (-s) = m ^ (-A) := by
    rw [← Real.rpow_natCast_mul hm_nonneg k (-s), mul_neg, hks]
  have hstep_f : (∏ i : Fin k, max 1 |c i * y i|) ^ (-s)
      = ∏ i : Fin k, (max 1 |c i * y i|) ^ (-s) := by
    rw [← Real.finsetProd_rpow Finset.univ (fun i => max 1 |c i * y i|)
      (fun i _ => (hb_pos i).le) (-s)]
  have hstep_g : ∏ i : Fin k, (max 1 |c i * y i|) ^ (-s)
      ≤ ∏ i : Fin k, ((2 : ℝ) ^ s * (1 + |c i * y i|) ^ (-s)) :=
    Finset.prod_le_prod (fun i _ => Real.rpow_nonneg (le_of_lt (hb_pos i)) _)
      (fun i _ => max_one_rpow_neg_le hs0 (abs_nonneg _))
  have hstep_g' : ∏ i : Fin k, ((2 : ℝ) ^ s * (1 + |c i * y i|) ^ (-s))
      = ((2 : ℝ) ^ s) ^ k * ∏ i : Fin k, (1 + |c i * y i|) ^ (-s) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  calc m ^ (-A) = (m ^ k) ^ (-s) := hstep_e.symm
    _ ≤ (∏ i : Fin k, max 1 |c i * y i|) ^ (-s) := hstep_d
    _ = ∏ i : Fin k, (max 1 |c i * y i|) ^ (-s) := hstep_f
    _ ≤ ∏ i : Fin k, ((2 : ℝ) ^ s * (1 + |c i * y i|) ^ (-s)) := hstep_g
    _ = ((2 : ℝ) ^ s) ^ k * ∏ i : Fin k, (1 + |c i * y i|) ^ (-s) := hstep_g'

theorem integrable_aniso_tent_scaled (k : ℕ) (hk : 1 ≤ k) {A δ : ℝ} (hA : (k : ℝ) < A) (hδ : 0 < δ) :
    MeasureTheory.Integrable (fun y : Fin k → ℝ =>
      (max 1 ((Finset.univ : Finset (Fin k)).sup' ⟨⟨0, hk⟩, Finset.mem_univ _⟩
        fun i => |δ ^ (i.val + 1) * y i|)) ^ (-A)) := by
  set s : ℝ := A / (k : ℝ) with hsdef
  have hkR : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  have hs_gt_one : 1 < s := by
    rw [hsdef, one_lt_div hkR]; exact hA
  have hf1 : ∀ i : Fin k, Integrable (fun t : ℝ => (1 + |δ ^ (i.val + 1) * t|) ^ (-s))
      (volume : Measure ℝ) :=
    fun i => integrable_one_add_abs_mul_rpow_neg (pow_pos hδ _) hs_gt_one
  have hf2 : Integrable (fun y : Fin k → ℝ => ∏ i, (1 + |δ ^ (i.val + 1) * y i|) ^ (-s))
      (volume : Measure (Fin k → ℝ)) :=
    Integrable.fintype_prod (μ := fun _ : Fin k => (volume : Measure ℝ))
      (f := fun i : Fin k => fun t : ℝ => (1 + |δ ^ (i.val + 1) * t|) ^ (-s)) hf1
  have hf3 : Integrable (fun y : Fin k → ℝ => ((2 : ℝ) ^ s) ^ k * ∏ i, (1 + |δ ^ (i.val + 1) * y i|) ^ (-s))
      (volume : Measure (Fin k → ℝ)) := hf2.const_mul _
  refine hf3.mono' ?_ ?_
  · apply Continuous.aestronglyMeasurable
    apply Continuous.rpow_const
    · apply Continuous.max continuous_const
      apply Continuous.finset_sup'_apply
      intro i _
      exact (continuous_const.mul (continuous_apply i)).abs
    · intro y
      exact Or.inl (ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_left _ _)))
  · filter_upwards with y
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (le_trans zero_le_one (le_max_left _ _)) _)]
    exact tent_bound k hk hA hsdef (fun i => δ ^ (i.val + 1)) y

end Commons.Analysis.Convolution