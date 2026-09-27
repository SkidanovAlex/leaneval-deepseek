import Mathlib

namespace Work.EKLC7

open MeasureTheory

/-- **Integrals of a bounded measurable function vanish on every Borel set of finite mass,
provided they vanish on every compact set.**

Let `β` be a Borel measure on `ℝ × ℝ` which is finite on compacts (equivalently, locally
finite, `ℝ × ℝ` being σ-compact and locally compact).  Let `Ψ` be measurable with `|Ψ| ≤ C`.
If `∫_K Ψ ∂β = 0` for every compact `K`, then `∫_A Ψ ∂β = 0` for every measurable `A`
with `β A < ∞`.

The point is that `β` is automatically inner regular for sets of finite `β`-measure
(`MeasureTheory.Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure`,
`MeasurableSet.exists_isCompact_sdiff_lt`), so `A` can be approximated from inside by a
compact set `K` with `β (A \ K) < δ`; the hypothesis gives `∫_K Ψ = 0` while
`‖∫_{A\K} Ψ‖ ≤ C · β (A \ K) ≤ C δ`, and `δ` is arbitrarily small. -/
theorem SepL2BorelIntegral
    {β : MeasureTheory.Measure (ℝ × ℝ)} [MeasureTheory.IsFiniteMeasureOnCompacts β]
    {Ψ : ℝ × ℝ → ℝ} (hΨ : Measurable Ψ) {C : ℝ} (hC : ∀ z, |Ψ z| ≤ C)
    (hK : ∀ K : Set (ℝ × ℝ), IsCompact K → ∫ z in K, Ψ z ∂β = 0)
    {A : Set (ℝ × ℝ)} (hA : MeasurableSet A) (hAfin : β A ≠ ⊤) :
    ∫ z in A, Ψ z ∂β = 0 := by
  -- The bound `hC` forces `C ≥ 0`.
  have hCnn : 0 ≤ C := le_trans (abs_nonneg (Ψ 0)) (hC 0)
  -- `Ψ` is integrable on `A`, since `A` has finite `β`-mass and `Ψ` is bounded.
  have hIntA : IntegrableOn Ψ A β := by
    refine IntegrableOn.of_bound (lt_top_iff_ne_top.mpr hAfin) hΨ.aestronglyMeasurable.restrict C ?_
    filter_upwards with z
    simpa [Real.norm_eq_abs] using hC z
  -- It suffices to show that the norm of the integral is at most every positive `ε`.
  have key : ∀ ε : ℝ, 0 < ε → ‖∫ z in A, Ψ z ∂β‖ ≤ ε := by
    intro ε hε
    have hC1 : 0 < C + 1 := by linarith
    set δ := ε / (C + 1) with hδdef
    have hδpos : 0 < δ := div_pos hε hC1
    -- Inner regularity of `β` on the finite mass set `A`.
    obtain ⟨K, hKA, hKc, hKl⟩ :=
      hA.exists_isCompact_sdiff_lt hAfin (ENNReal.ofReal_pos.mpr hδpos).ne'
    have hIntD : IntegrableOn Ψ (A \ K) β := hIntA.mono_set Set.sdiff_subset
    -- Split the integral over `A` into the parts over `K` and over `A \ K`.
    have hsplit : ∫ z in A, Ψ z ∂β = ∫ z in K, Ψ z ∂β + ∫ z in A \ K, Ψ z ∂β := by
      have h := integral_inter_add_sdiff (μ := β) (f := Ψ) (s := A) (t := K) hKc.measurableSet hIntA
      rw [Set.inter_eq_right.mpr hKA] at h
      linarith
    -- Bound the integral over the small set.
    have hnorm : ‖∫ z in A \ K, Ψ z ∂β‖ ≤ C * (β (A \ K)).toReal :=
      norm_setIntegral_le_of_norm_le_const (lt_top_iff_ne_top.mpr (ne_top_of_lt hKl))
        (fun z _ => by simpa [Real.norm_eq_abs] using hC z)
    have h1 : (β (A \ K)).toReal < δ := by
      have hb : (ENNReal.ofReal δ) ≠ ⊤ := ENNReal.ofReal_ne_top
      have := (ENNReal.toReal_lt_toReal (ne_top_of_lt hKl) hb).mpr hKl
      rwa [ENNReal.toReal_ofReal hδpos.le] at this
    have h2 : C * δ ≤ ε := by
      rw [hδdef, ← mul_div_assoc, div_le_iff₀ hC1]
      nlinarith [hε.le, hCnn]
    rw [hsplit, hK K hKc, zero_add]
    exact hnorm.trans (le_trans (mul_le_mul_of_nonneg_left h1.le hCnn) h2)
  exact norm_eq_zero.mp
    (le_antisymm (le_of_forall_pos_le_add (fun ε hε => by simpa using key ε hε)) (norm_nonneg _))

end Work.EKLC7
