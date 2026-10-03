import Mathlib

/-!
# An integrable function on `ℝ` is small along a sequence tending to `+∞`

If `f : ℝ → ℝ` is integrable (with respect to Lebesgue measure), then for every `N` and every
`ε > 0` there is a point `x > N` with `|f x| < ε`: otherwise `|f| ≥ ε` on the whole tail
`(N, ∞)`, whose lintegral of the constant `ε` is `⊤`, contradicting finiteness of `∫⁻ ‖f‖`.
Iterating with `N = n` and `ε = 1/(n+1)` produces a sequence `u n → +∞` along which `f (u n) → 0`.
-/

namespace Work.FatouL1

open MeasureTheory Filter

/-- For an integrable `f`, `|f|` takes values `< ε` arbitrarily far to the right of any `N`. -/
lemma exists_gt_abs_lt {f : ℝ → ℝ} (hf : MeasureTheory.Integrable f) (N : ℝ) {ε : ℝ}
    (hε : 0 < ε) : ∃ x, N < x ∧ |f x| < ε := by
  by_contra h
  have hge : ∀ x, N < x → ε ≤ |f x| := by
    intro x hx
    by_contra hlt
    exact h ⟨x, hx, not_le.mp hlt⟩
  have hle : ∫⁻ x in Set.Ioi N, ENNReal.ofReal ε ≤ ∫⁻ x in Set.Ioi N, ENNReal.ofReal |f x| := by
    apply lintegral_mono_ae
    rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with x hx
    exact ENNReal.ofReal_le_ofReal (hge x hx)
  have htop : ∫⁻ x in Set.Ioi N, ENNReal.ofReal ε = ⊤ := by
    rw [setLIntegral_const, Real.volume_Ioi]
    exact ENNReal.mul_top (ENNReal.ofReal_ne_zero_iff.mpr hε)
  have hfin : ∫⁻ x in Set.Ioi N, ENNReal.ofReal |f x| < ⊤ := by
    calc ∫⁻ x in Set.Ioi N, ENNReal.ofReal |f x|
        ≤ ∫⁻ x, ENNReal.ofReal |f x| := setLIntegral_le_lintegral _ _
      _ = ∫⁻ x, ENNReal.ofReal ‖f x‖ := by simp [Real.norm_eq_abs]
      _ < ⊤ := (hasFiniteIntegral_iff_norm f).mp hf.2
  exact absurd (htop ▸ hle) (not_le.mpr hfin)

theorem existsSeqTendstoZero {f : ℝ → ℝ} (hf : MeasureTheory.Integrable f) :
    ∃ u : ℕ → ℝ, Filter.Tendsto u Filter.atTop Filter.atTop ∧
      Filter.Tendsto (fun n => f (u n)) Filter.atTop (nhds 0) := by
  have key : ∀ n : ℕ, ∃ x, (n : ℝ) < x ∧ |f x| < 1 / ((n : ℝ) + 1) := fun n =>
    exists_gt_abs_lt hf (n : ℝ) (by positivity)
  choose u hu using key
  refine ⟨u, ?_, ?_⟩
  · exact tendsto_atTop_mono (fun n => le_of_lt (hu n).1) tendsto_natCast_atTop_atTop
  · have h1 : Tendsto (fun n : ℕ => |f (u n)|) atTop (nhds 0) :=
      squeeze_zero (fun n => abs_nonneg _) (fun n => le_of_lt (hu n).2)
        tendsto_one_div_add_atTop_nhds_zero_nat
    have h2 : Tendsto (fun n : ℕ => ‖f (u n)‖) atTop (nhds 0) := by
      simpa only [Real.norm_eq_abs] using h1
    exact tendsto_zero_iff_norm_tendsto_zero.mpr h2

end Work.FatouL1
