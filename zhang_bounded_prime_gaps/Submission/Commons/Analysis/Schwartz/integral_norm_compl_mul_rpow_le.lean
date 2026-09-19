import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Order.CompletePartialOrder

namespace Commons.Analysis.Schwartz

open MeasureTheory Set

/-- Auxiliary combinatorial inequality: `(1 + t)^r ≤ 2^r * (1 + t^r)` for `t ≥ 0`. -/
theorem one_add_pow_le_two_pow_mul (t : ℝ) (ht : 0 ≤ t) (r : ℕ) :
    (1 + t) ^ r ≤ 2 ^ r * (1 + t ^ r) := by
  have h1 : 1 + t ≤ 2 * max 1 t := by
    rcases le_total 1 t with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith
  have h2 : (max 1 t) ^ r ≤ 1 + t ^ r := by
    rcases le_total 1 t with h | h
    · rw [max_eq_right h]
      exact le_add_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1)
    · rw [max_eq_left h, one_pow]
      exact le_add_of_nonneg_right (pow_nonneg ht r)
  calc (1 + t) ^ r ≤ (2 * max 1 t) ^ r := pow_le_pow_left₀ (by linarith) h1 r
    _ = 2 ^ r * (max 1 t) ^ r := by rw [mul_pow]
    _ ≤ 2 ^ r * (1 + t ^ r) := mul_le_mul_of_nonneg_left h2 (by positivity)

/-- **Weighted tail integral of a Schwartz function.**  For a Schwartz function
`f : 𝓢(ℝ, ℂ)`, a polynomial weight `(1 + |x|)^r` and any target rate `m`, there
is `C > 0` with

    ∫_{ρ ≤ |x|} (1 + |x|)^r ‖f x‖ dx ≤ C / ρ^m      for all `ρ ≥ 1`.

This generalizes `Commons.Analysis.Schwartz.integral_norm_compl_abs_le` (the
case `r = 0`) to polynomial weights, as needed when the integrand carries a
factor growing like `|ξ|` (e.g. the inverse pole factor of Polymath8a's
Lemma 4.1, whose off-cube contribution is bounded by Schwartz decay).

Suggested route: `SchwartzMap.decay f (m + r + 2) 0` gives `C₀ > 0` with
`|x|^(m+r+2) * ‖f x‖ ≤ C₀`; on `|x| ≥ ρ ≥ 1`,
`(1 + |x|)^r ‖f x‖ ≤ (2|x|)^r * C₀ / |x|^(m+r+2) = 2^r C₀ / |x|^(m+2)`, so the
set integral is at most `2 · ∫_ρ^∞ 2^r C₀ x^{−(m+2)} dx = 2^{r+1} C₀/((m+1)ρ^{m+1})`,
which is `≤ C/ρ^m` for `ρ ≥ 1`.  (Use `MeasureTheory.integral_Ioi_rpow_of_lt` /
`intervalIntegral` for the one-dimensional tail, and
`Integrable.integrableOn` with `SchwartzMap.integrable` for measurability.) -/
theorem integral_norm_compl_mul_rpow_le (f : SchwartzMap ℝ ℂ) (r m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ρ : ℝ, 1 ≤ ρ →
      ∫ x in {x : ℝ | ρ ≤ |x|}, (1 + |x|) ^ r * ‖f x‖ ≤ C / ρ ^ m := by
  obtain ⟨C0, hC0pos, hC0⟩ := SchwartzMap.decay f (m + r + 2) 0
  have hdec : ∀ x : ℝ, |x| ^ (m + r + 2) * ‖f x‖ ≤ C0 := by
    intro x
    have h := hC0 x
    simpa [Real.norm_eq_abs] using h
  -- Pointwise decay of the weighted integrand on the tail.
  have hbound : ∀ x : ℝ, 1 ≤ |x| →
      (1 + |x|) ^ r * ‖f x‖ ≤ (2 : ℝ) ^ r * C0 * |x| ^ (-(↑(m + 2) : ℝ)) := by
    intro x hx
    have hxpos : 0 < |x| := lt_of_lt_of_le zero_lt_one hx
    have hA : (1 + |x|) ^ r ≤ (2 : ℝ) ^ r * |x| ^ r := by
      have h1 : 1 + |x| ≤ 2 * |x| := by linarith
      have h2 := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 1 + |x|) h1 r
      rwa [mul_pow] at h2
    have hB : ‖f x‖ ≤ C0 * |x| ^ (-(↑(m + r + 2) : ℝ)) := by
      have hkpos : 0 < |x| ^ (m + r + 2) := pow_pos hxpos _
      have hdle : ‖f x‖ ≤ C0 / |x| ^ (m + r + 2) :=
        (le_div_iff₀ hkpos).mpr (by linarith [hdec x])
      calc ‖f x‖ ≤ C0 / |x| ^ (m + r + 2) := hdle
        _ = C0 * |x| ^ (-(↑(m + r + 2) : ℝ)) := by
              rw [Real.rpow_neg (abs_nonneg x), Real.rpow_natCast, div_eq_mul_inv]
    calc (1 + |x|) ^ r * ‖f x‖
        ≤ ((2 : ℝ) ^ r * |x| ^ r) * (C0 * |x| ^ (-(↑(m + r + 2) : ℝ))) :=
          mul_le_mul hA hB (norm_nonneg _) (by positivity)
      _ = (2 : ℝ) ^ r * C0 * |x| ^ (-(↑(m + 2) : ℝ)) := by
          have hrw : |x| ^ r * |x| ^ (-(↑(m + r + 2) : ℝ)) = |x| ^ (-(↑(m + 2) : ℝ)) := by
            rw [← Real.rpow_natCast (|x|) r, ← Real.rpow_add hxpos]
            congr 1
            push_cast
            ring
          calc ((2 : ℝ) ^ r * |x| ^ r) * (C0 * |x| ^ (-(↑(m + r + 2) : ℝ)))
              = (2 : ℝ) ^ r * C0 * (|x| ^ r * |x| ^ (-(↑(m + r + 2) : ℝ))) := by ring
            _ = (2 : ℝ) ^ r * C0 * |x| ^ (-(↑(m + 2) : ℝ)) := by rw [hrw]
  -- Global integrability of the weighted integrand.
  have hGint : Integrable (fun x : ℝ => (1 + |x|) ^ r * ‖f x‖) volume := by
    have hmea : AEStronglyMeasurable (fun x : ℝ => (1 + |x|) ^ r * ‖f x‖) volume :=
      (((continuous_const.add continuous_abs).pow r).mul f.continuous.norm).aestronglyMeasurable
    have hDint : Integrable (fun x : ℝ => (2 : ℝ) ^ r * (‖f x‖ + ‖x‖ ^ r * ‖f x‖)) volume :=
      ((f.integrable.norm).add (f.integrable_pow_mul volume r)).const_mul _
    refine hDint.mono' hmea ?_
    filter_upwards with x
    rw [Real.norm_of_nonneg (by positivity)]
    have h := one_add_pow_le_two_pow_mul |x| (abs_nonneg x) r
    calc (1 + |x|) ^ r * ‖f x‖ ≤ (2 : ℝ) ^ r * (1 + |x| ^ r) * ‖f x‖ :=
          mul_le_mul_of_nonneg_right h (norm_nonneg _)
      _ = (2 : ℝ) ^ r * (‖f x‖ + ‖x‖ ^ r * ‖f x‖) := by
          rw [Real.norm_eq_abs]; ring
  refine ⟨2 ^ (r + 1) * C0 / (m + 1),
    div_pos (mul_pos (by positivity) hC0pos) (by positivity), ?_⟩
  intro ρ hρ
  have hρpos : 0 < ρ := lt_of_lt_of_le zero_lt_one hρ
  have ha2 : (-(↑(m + 2) : ℝ)) < -1 := by
    have h : (1 : ℝ) < (↑(m + 2) : ℝ) := by
      have : (1 : ℕ) < m + 2 := by omega
      exact_mod_cast this
    linarith
  have hgOn_Ioi : IntegrableOn (fun x : ℝ => (2 : ℝ) ^ r * C0 * x ^ (-(↑(m + 2) : ℝ)))
      (Ioi ρ) volume :=
    (integrableOn_Ioi_rpow_of_lt ha2 hρpos).const_mul ((2 : ℝ) ^ r * C0)
  have hval : ∫ x in Ioi ρ, (2 : ℝ) ^ r * C0 * x ^ (-(↑(m + 2) : ℝ))
      = (2 : ℝ) ^ r * C0 * ρ ^ (-(↑(m + 1) : ℝ)) / (m + 1) := by
    rw [integral_const_mul, integral_Ioi_rpow_of_lt ha2 hρpos]
    have hmm : (-(↑(m + 2) : ℝ)) + 1 = -(↑(m + 1) : ℝ) := by push_cast; ring
    rw [hmm, neg_div_neg_eq]
    push_cast
    ring
  have hright : ∫ x in Ici ρ, (1 + |x|) ^ r * ‖f x‖
      ≤ (2 : ℝ) ^ r * C0 * ρ ^ (-(↑(m + 1) : ℝ)) / (m + 1) := by
    have hgOn : IntegrableOn (fun x : ℝ => (2 : ℝ) ^ r * C0 * x ^ (-(↑(m + 2) : ℝ)))
        (Ici ρ) volume := by
      have hhalf : IntegrableOn (fun x : ℝ => (2 : ℝ) ^ r * C0 * x ^ (-(↑(m + 2) : ℝ)))
          (Ioi (ρ / 2)) volume :=
        (integrableOn_Ioi_rpow_of_lt ha2 (by positivity)).const_mul ((2 : ℝ) ^ r * C0)
      refine hhalf.mono_set ?_
      intro x hx
      simp only [mem_Ici] at hx
      simp only [mem_Ioi]
      linarith
    have hmono := setIntegral_mono_of_nonneg (s := Ici ρ)
      (f := fun x : ℝ => (1 + |x|) ^ r * ‖f x‖)
      (g := fun x : ℝ => (2 : ℝ) ^ r * C0 * x ^ (-(↑(m + 2) : ℝ)))
      (fun x _ => by positivity)
      (fun x hx => by
        have hxnn : 0 ≤ x := le_trans (le_of_lt hρpos) hx
        have hx1 : 1 ≤ |x| := by rw [abs_of_nonneg hxnn]; exact le_trans hρ hx
        simpa [abs_of_nonneg hxnn] using hbound x hx1)
      hgOn
    refine hmono.trans ?_
    rw [integral_Ici_eq_integral_Ioi, hval]
  have hleft : ∫ x in Iic (-ρ), (1 + |x|) ^ r * ‖f x‖
      ≤ (2 : ℝ) ^ r * C0 * ρ ^ (-(↑(m + 1) : ℝ)) / (m + 1) := by
    have hcomp : ∫ x in Ioi ρ, (1 + |-x|) ^ r * ‖f (-x)‖
        = ∫ x in Iic (-ρ), (1 + |x|) ^ r * ‖f x‖ := by
      simpa using integral_comp_neg_Ioi ρ (fun y : ℝ => (1 + |y|) ^ r * ‖f y‖)
    rw [← hcomp]
    have hmono := setIntegral_mono_of_nonneg (s := Ioi ρ)
      (f := fun x : ℝ => (1 + |-x|) ^ r * ‖f (-x)‖)
      (g := fun x : ℝ => (2 : ℝ) ^ r * C0 * x ^ (-(↑(m + 2) : ℝ)))
      (fun x _ => by positivity)
      (fun x hx => by
        have hxnn : 0 ≤ x := le_trans (le_of_lt hρpos) (le_of_lt hx)
        have hx1 : 1 ≤ |-x| := by rw [abs_neg, abs_of_nonneg hxnn]; exact le_trans hρ (le_of_lt hx)
        simpa [abs_neg, abs_of_nonneg hxnn] using hbound (-x) hx1)
      hgOn_Ioi
    refine hmono.trans ?_
    rw [hval]
  have hS : {x : ℝ | ρ ≤ |x|} = Iic (-ρ) ∪ Ici ρ := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_Iic, Set.mem_Ici]
    rw [le_abs]
    constructor
    · rintro (h | h)
      · exact Or.inr h
      · exact Or.inl (by linarith)
    · rintro (h | h)
      · exact Or.inr (by linarith)
      · exact Or.inl h
  have hdisj : Disjoint (Iic (-ρ)) (Ici ρ) := by
    rw [Set.disjoint_left]
    intro x hx1 hx2
    simp only [Set.mem_Iic] at hx1
    simp only [Set.mem_Ici] at hx2
    linarith
  rw [hS, setIntegral_union hdisj measurableSet_Ici hGint.integrableOn hGint.integrableOn]
  have hsum : (∫ x in Iic (-ρ), (1 + |x|) ^ r * ‖f x‖)
      + (∫ x in Ici ρ, (1 + |x|) ^ r * ‖f x‖)
      ≤ 2 * ((2 : ℝ) ^ r * C0 * ρ ^ (-(↑(m + 1) : ℝ)) / (m + 1)) := by
    have h := add_le_add hleft hright
    calc (∫ x in Iic (-ρ), (1 + |x|) ^ r * ‖f x‖)
          + (∫ x in Ici ρ, (1 + |x|) ^ r * ‖f x‖)
        ≤ ((2 : ℝ) ^ r * C0 * ρ ^ (-(↑(m + 1) : ℝ)) / (m + 1))
            + ((2 : ℝ) ^ r * C0 * ρ ^ (-(↑(m + 1) : ℝ)) / (m + 1)) := h
      _ = 2 * ((2 : ℝ) ^ r * C0 * ρ ^ (-(↑(m + 1) : ℝ)) / (m + 1)) := by ring
  refine hsum.trans ?_
  have hstep1 : 2 * ((2 : ℝ) ^ r * C0 * ρ ^ (-(↑(m + 1) : ℝ)) / (m + 1))
      = 2 ^ (r + 1) * C0 / ((m + 1) * ρ ^ (m + 1)) := by
    rw [Real.rpow_neg (le_of_lt hρpos), Real.rpow_natCast, pow_succ]
    field_simp
    ring
  have hstep2 : 2 ^ (r + 1) * C0 / ((m + 1) * ρ ^ (m + 1))
      ≤ 2 ^ (r + 1) * C0 / (m + 1) / ρ ^ m := by
    rw [div_div]
    refine div_le_div_of_nonneg_left (mul_nonneg (by positivity) (le_of_lt hC0pos))
      (mul_pos (by positivity) (pow_pos hρpos m)) ?_
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hρ (Nat.le_succ m)) (by positivity)
  exact hstep1.trans_le hstep2

end Commons.Analysis.Schwartz