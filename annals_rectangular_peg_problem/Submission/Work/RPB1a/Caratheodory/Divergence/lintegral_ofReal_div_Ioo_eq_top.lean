import Mathlib

namespace Work.RPB1a.Caratheodory.Divergence

open Complex Set Metric MeasureTheory
open scoped ENNReal Real Topology

/-- The lower integral of `c / ρ` over `(0, ρ₀)` is infinite: no geometric sequence of annuli
can sum to a finite number, since their contributions are bounded below by the positive constant
`c / 2`. -/
theorem lintegral_ofReal_div_Ioo_eq_top {c ρ₀ : ℝ} (hc : 0 < c) (hρ₀ : 0 < ρ₀) :
    ∫⁻ ρ in Ioo (0 : ℝ) ρ₀, ENNReal.ofReal (c / ρ) = ⊤ := by
  have hc2 : (0 : ℝ) < c / 2 := by linarith
  let f : ℝ → ℝ≥0∞ := fun ρ => ENNReal.ofReal (c / ρ)
  let S : ℕ → Set ℝ := fun n => Ioo (ρ₀ * (1 / 2 : ℝ) ^ (n + 1)) (ρ₀ * (1 / 2 : ℝ) ^ n)
  have hr0 : (0 : ℝ) ≤ (1 / 2 : ℝ) := by norm_num
  have hr1 : (1 / 2 : ℝ) ≤ 1 := by norm_num
  have hSmeas : ∀ n, MeasurableSet (S n) := fun n => measurableSet_Ioo
  have hdisj : Pairwise (Function.onFun Disjoint S) := by
    intro m n hmn
    rw [Function.onFun_apply]
    rw [Set.disjoint_left]
    intro x hxm hxn
    obtain ⟨hxm1, hxm2⟩ := Set.mem_Ioo.mp hxm
    obtain ⟨hxn1, hxn2⟩ := Set.mem_Ioo.mp hxn
    rcases lt_or_gt_of_ne hmn with hlt | hgt
    · have hle : (1 / 2 : ℝ) ^ n ≤ (1 / 2 : ℝ) ^ (m + 1) :=
        pow_le_pow_of_le_one hr0 hr1 (by omega)
      have hmul : ρ₀ * (1 / 2 : ℝ) ^ n ≤ ρ₀ * (1 / 2 : ℝ) ^ (m + 1) :=
        mul_le_mul_of_nonneg_left hle (le_of_lt hρ₀)
      linarith
    · have hle : (1 / 2 : ℝ) ^ m ≤ (1 / 2 : ℝ) ^ (n + 1) :=
        pow_le_pow_of_le_one hr0 hr1 (by omega)
      have hmul : ρ₀ * (1 / 2 : ℝ) ^ m ≤ ρ₀ * (1 / 2 : ℝ) ^ (n + 1) :=
        mul_le_mul_of_nonneg_left hle (le_of_lt hρ₀)
      linarith
  have hsub : (⋃ n, S n) ⊆ Ioo (0 : ℝ) ρ₀ := by
    intro x hx
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
    obtain ⟨hn1, hn2⟩ := Set.mem_Ioo.mp hn
    refine Set.mem_Ioo.mpr ⟨?_, ?_⟩
    · have hp : 0 < ρ₀ * (1 / 2 : ℝ) ^ (n + 1) := by positivity
      linarith
    · have hle : (1 / 2 : ℝ) ^ n ≤ 1 := pow_le_one₀ hr0 hr1
      have hmul : ρ₀ * (1 / 2 : ℝ) ^ n ≤ ρ₀ := by
        simpa using mul_le_mul_of_nonneg_left hle (le_of_lt hρ₀)
      linarith
  have hpiece : ∀ n, ENNReal.ofReal (c / 2) ≤ ∫⁻ ρ in S n, f ρ := by
    intro n
    have hden : (0 : ℝ) < ρ₀ * (1 / 2 : ℝ) ^ n := by positivity
    have hvol : volume (S n) = ENNReal.ofReal (ρ₀ * (1 / 2 : ℝ) ^ (n + 1)) := by
      have hSeq : S n = Ioo (ρ₀ * (1 / 2 : ℝ) ^ (n + 1)) (ρ₀ * (1 / 2 : ℝ) ^ n) := rfl
      rw [hSeq, Real.volume_Ioo]
      congr 1
      rw [pow_succ]
      ring
    have hconst : ∫⁻ ρ in S n, (fun _ => ENNReal.ofReal (c / (ρ₀ * (1 / 2 : ℝ) ^ n))) ρ
        = ENNReal.ofReal (c / 2) := by
      rw [setLIntegral_const, hvol,
        ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ c / (ρ₀ * (1 / 2 : ℝ) ^ n))]
      congr 1
      rw [pow_succ]
      field_simp
    have hae : (fun _ => ENNReal.ofReal (c / (ρ₀ * (1 / 2 : ℝ) ^ n)))
        ≤ᵐ[volume.restrict (S n)] f := by
      rw [Filter.EventuallyLE, ae_restrict_iff' (hSmeas n)]
      filter_upwards with x hx
      obtain ⟨hx1, hx2⟩ := Set.mem_Ioo.mp hx
      have hxpos : 0 < x := lt_trans (by positivity : (0 : ℝ) < ρ₀ * (1 / 2 : ℝ) ^ (n + 1)) hx1
      have hle : c / (ρ₀ * (1 / 2 : ℝ) ^ n) ≤ c / x :=
        div_le_div_of_nonneg_left (le_of_lt hc) hxpos (le_of_lt hx2)
      exact ENNReal.ofReal_le_ofReal hle
    calc ENNReal.ofReal (c / 2)
        = ∫⁻ ρ in S n, (fun _ => ENNReal.ofReal (c / (ρ₀ * (1 / 2 : ℝ) ^ n))) ρ := hconst.symm
      _ ≤ ∫⁻ ρ in S n, f ρ := lintegral_mono_ae hae
  have hne : ENNReal.ofReal (c / 2) ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hc2
  have hmain : ⊤ ≤ ∫⁻ ρ in Ioo (0 : ℝ) ρ₀, f ρ := by
    calc ⊤ = ∑' n, ENNReal.ofReal (c / 2) := (ENNReal.tsum_const_eq_top_of_ne_zero hne).symm
      _ ≤ ∑' n, ∫⁻ ρ in S n, f ρ := ENNReal.tsum_le_tsum hpiece
      _ = ∫⁻ ρ in ⋃ n, S n, f ρ := (lintegral_iUnion hSmeas hdisj f).symm
      _ ≤ ∫⁻ ρ in Ioo (0 : ℝ) ρ₀, f ρ := lintegral_mono_set hsub
  exact eq_top_iff.mpr hmain

end Work.RPB1a.Caratheodory.Divergence
