import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Order.CompletePartialOrder
import Submission.Commons.Analysis.Real.verticalLogWeight_integral_le

namespace Commons.Analysis.Schwartz

open MeasureTheory Set

/-- **Tail integral of a Schwartz function.**  For a Schwartz function
`f : 𝓢(ℝ, ℂ)` and every `m : ℕ` there is `C > 0` with

    ∫_{ρ ≤ |x|} ‖f x‖ dx ≤ C / ρ^m      for all `ρ ≥ 1`.

This is the quantitative form of the rapid decay `‖f x‖ = O(|x|^{-k})` needed
when bounding the contribution of the region outside a cube of side `ρ` in the
ξ-integral of a Fourier expansion (e.g. Polymath8a Lemma 4.1, step (iii)). -/
theorem integral_norm_compl_abs_le (f : SchwartzMap ℝ ℂ) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ρ : ℝ, 1 ≤ ρ → ∫ x in {x : ℝ | ρ ≤ |x|}, ‖f x‖ ≤ C / ρ ^ m := by
  obtain ⟨C0, hC0pos, hC0⟩ := SchwartzMap.decay f (m + 2) 0
  have hdecay : ∀ x : ℝ, ‖x‖ ^ (m + 2) * ‖f x‖ ≤ C0 := by
    intro x
    simpa using hC0 x
  have hgint : Integrable (fun x : ℝ => ‖f x‖) volume := f.integrable.norm
  have ha2 : (-(↑(m + 2) : ℝ)) < -1 := by
    have h : (1 : ℝ) < (↑(m + 2) : ℝ) := by
      have : (1 : ℕ) < m + 2 := by omega
      exact_mod_cast this
    linarith
  -- Pointwise decay: for positive `x`, `‖f x‖ ≤ C0 * x ^ (-(m+2))`.
  have hcmp_f : ∀ x : ℝ, 0 < x → ‖f x‖ ≤ C0 * x ^ (-(↑(m + 2) : ℝ)) := by
    intro x hxpos
    have h := hdecay x
    rw [Real.norm_eq_abs, abs_of_pos hxpos] at h
    have h1 : ‖f x‖ * x ^ (m + 2) ≤ C0 := by linarith
    calc ‖f x‖ ≤ C0 / x ^ (m + 2) := (le_div_iff₀ (by positivity)).mpr h1
      _ = C0 * x ^ (-(↑(m + 2) : ℝ)) := by
          rw [Real.rpow_neg (le_of_lt hxpos), Real.rpow_natCast, div_eq_mul_inv]
  have hcmp_g : ∀ x : ℝ, 0 < x → ‖f (-x)‖ ≤ C0 * x ^ (-(↑(m + 2) : ℝ)) := by
    intro x hxpos
    have h := hdecay (-x)
    rw [Real.norm_eq_abs, abs_neg, abs_of_pos hxpos] at h
    have h1 : ‖f (-x)‖ * x ^ (m + 2) ≤ C0 := by linarith
    calc ‖f (-x)‖ ≤ C0 / x ^ (m + 2) := (le_div_iff₀ (by positivity)).mpr h1
      _ = C0 * x ^ (-(↑(m + 2) : ℝ)) := by
          rw [Real.rpow_neg (le_of_lt hxpos), Real.rpow_natCast, div_eq_mul_inv]
  -- The one-sided tail bound.
  have htail : ∀ (G : ℝ → ℝ), Integrable G volume →
      (∀ x : ℝ, 0 < x → G x ≤ C0 * x ^ (-(↑(m + 2) : ℝ))) →
      ∀ ρ : ℝ, 0 < ρ → ∫ x in Ioi ρ, G x ≤ C0 * ρ ^ (-(↑(m + 1) : ℝ)) / (m + 1) := by
    intro G hGint hGbound ρ hρ
    have hcmp : ∀ x ∈ Ioi ρ, G x ≤ C0 * x ^ (-(↑(m + 2) : ℝ)) :=
      fun x hx => hGbound x (hρ.trans hx)
    have hint : IntegrableOn (fun x : ℝ => C0 * x ^ (-(↑(m + 2) : ℝ))) (Ioi ρ) volume := by
      rw [IntegrableOn]
      exact (integrableOn_Ioi_rpow_of_lt ha2 hρ).const_mul C0
    have hmono := setIntegral_mono_on hGint.integrableOn hint measurableSet_Ioi hcmp
    calc ∫ x in Ioi ρ, G x ≤ ∫ x in Ioi ρ, C0 * x ^ (-(↑(m + 2) : ℝ)) := hmono
      _ = C0 * ∫ x in Ioi ρ, x ^ (-(↑(m + 2) : ℝ)) := by rw [integral_const_mul]
      _ = C0 * (ρ ^ (-(↑(m + 1) : ℝ)) / (m + 1)) := by
            rw [integral_Ioi_rpow_of_lt ha2 hρ]
            have hmm : (-(↑(m + 2) : ℝ)) + 1 = -(↑(m + 1) : ℝ) := by push_cast; ring
            rw [hmm, neg_div_neg_eq]
            push_cast
            ring
      _ = C0 * ρ ^ (-(↑(m + 1) : ℝ)) / (m + 1) := by ring
  refine ⟨2 * C0 / (m + 1), div_pos (by positivity) (by positivity), ?_⟩
  intro ρ hρ
  have hρpos : 0 < ρ := lt_of_lt_of_le zero_lt_one hρ
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
  rw [hS, setIntegral_union hdisj measurableSet_Ici hgint.integrableOn hgint.integrableOn]
  have hleft : ∫ x in Iic (-ρ), ‖f x‖ ≤ C0 * ρ ^ (-(↑(m + 1) : ℝ)) / (m + 1) := by
    rw [← integral_comp_neg_Ioi ρ (fun x : ℝ => ‖f x‖)]
    exact htail (fun x : ℝ => ‖f (-x)‖) hgint.comp_neg hcmp_g ρ hρpos
  have hright : ∫ x in Ici ρ, ‖f x‖ ≤ C0 * ρ ^ (-(↑(m + 1) : ℝ)) / (m + 1) := by
    rw [integral_Ici_eq_integral_Ioi]
    exact htail (fun x : ℝ => ‖f x‖) hgint hcmp_f ρ hρpos
  have hsum : (∫ x in Iic (-ρ), ‖f x‖) + (∫ x in Ici ρ, ‖f x‖)
      ≤ 2 * (C0 * ρ ^ (-(↑(m + 1) : ℝ)) / (m + 1)) := by
    have h := add_le_add hleft hright
    calc (∫ x in Iic (-ρ), ‖f x‖) + (∫ x in Ici ρ, ‖f x‖)
        ≤ C0 * ρ ^ (-(↑(m + 1) : ℝ)) / (m + 1)
            + C0 * ρ ^ (-(↑(m + 1) : ℝ)) / (m + 1) := h
      _ = 2 * (C0 * ρ ^ (-(↑(m + 1) : ℝ)) / (m + 1)) := by ring
  calc (∫ x in Iic (-ρ), ‖f x‖) + (∫ x in Ici ρ, ‖f x‖)
      ≤ 2 * (C0 * ρ ^ (-(↑(m + 1) : ℝ)) / (m + 1)) := hsum
    _ = 2 * C0 / ((m + 1) * ρ ^ (m + 1)) := by
          rw [Real.rpow_neg (le_of_lt hρpos), Real.rpow_natCast]
          field_simp
    _ ≤ 2 * C0 / (m + 1) / ρ ^ m := by
          rw [div_div]
          refine div_le_div_of_nonneg_left (mul_nonneg (by norm_num) (le_of_lt hC0pos))
            (mul_pos (by positivity) (pow_pos hρpos m)) ?_
          exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hρ (Nat.le_succ m)) (by positivity)

end Commons.Analysis.Schwartz