import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Topology.MetricSpace.Holder
import Submission.Work.CoreResiduals.BiotSavart.WindowExtDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals.BiotSavart

open Set

/-- **Local boundedness of the two-sided extension.**  On any bounded time window
`Ioo (t₀-1) (t₀+1)` the extension `windowExt ω S y ·` is uniformly bounded in `y`, with a bound
`M + (|t₀|+1+|S|)·|M₁|` built from the strip bound `M` on `ω` and the strip bound `M₁` on `∂ₜω`.

Indeed, on `Ioo (t₀-1) (t₀+1)` one has `|t| ≤ |t₀|+1`; below the strip the extension is
`ω y 0 + t • ∂ₜω(y,0)`, inside it is `ω y t`, and above it is
`ω y S + (t-S) • ∂ₜω(y,S)`, and each of the three terms is bounded by `M` resp.
`(|t₀|+1+|S|)·|M₁|` using the triangle inequality and `‖c • v‖ = |c| ‖v‖`. -/
theorem windowExt_localBdd {α : NNReal} {ω : R3 → ℝ → R3} {R S : ℝ}
    (hS : 0 < S) (hbun : BSAdmissibleStripFull α ω R S) (t₀ : ℝ) :
    ∃ M : ℝ, ∀ t ∈ Set.Ioo (t₀ - 1) (t₀ + 1), ∀ y : R3, ‖windowExt ω S y t‖ ≤ M := by
  obtain ⟨hb, htd, _htdh⟩ := hbun
  obtain ⟨_hR, _hsupp, hMb, _hH, _hN, _hmeas⟩ := hb
  obtain ⟨M, hM⟩ := hMb
  obtain ⟨_hdiff, hM₁b, _hmeas₁⟩ := htd
  obtain ⟨M₁, hM₁⟩ := hM₁b
  refine ⟨M + (|t₀| + 1 + |S|) * |M₁|, ?_⟩
  intro t ht y
  have hnn : (0 : ℝ) ≤ (|t₀| + 1 + |S|) * |M₁| :=
    mul_nonneg (by positivity) (abs_nonneg M₁)
  have hSnn : (0 : ℝ) ≤ |t₀| + 1 + |S| := by positivity
  -- `|t| ≤ |t₀| + 1` on the window
  have htB : |t| ≤ |t₀| + 1 := by
    have h1 : |t - t₀| < 1 := by
      rw [abs_lt]
      exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    calc |t| = |(t - t₀) + t₀| := by ring_nf
      _ ≤ |t - t₀| + |t₀| := abs_add_le _ _
      _ ≤ |t₀| + 1 := by linarith
  have hb1 : ‖ω y 0‖ ≤ M := hM 0 ⟨le_refl 0, le_of_lt hS⟩ y
  have hb1S : ‖ω y S‖ ≤ M := hM S ⟨le_of_lt hS, le_refl S⟩ y
  have hb2 : ‖FiniteTimeSingularity.timeDeriv ω y 0‖ ≤ |M₁| :=
    le_trans (hM₁ 0 ⟨le_refl 0, le_of_lt hS⟩ y) (le_abs_self M₁)
  have hb2S : ‖FiniteTimeSingularity.timeDeriv ω y S‖ ≤ |M₁| :=
    le_trans (hM₁ S ⟨le_of_lt hS, le_refl S⟩ y) (le_abs_self M₁)
  rcases le_or_gt t 0 with hle | hlt
  · -- below the strip
    rw [windowExt_of_nonpos hle]
    have hmul : |t| * ‖FiniteTimeSingularity.timeDeriv ω y 0‖
        ≤ (|t₀| + 1 + |S|) * |M₁| := by
      calc |t| * ‖FiniteTimeSingularity.timeDeriv ω y 0‖
          ≤ (|t₀| + 1) * |M₁| :=
            mul_le_mul htB hb2 (norm_nonneg _) (by positivity)
        _ ≤ (|t₀| + 1 + |S|) * |M₁| :=
            mul_le_mul_of_nonneg_right (by linarith [abs_nonneg S]) (abs_nonneg M₁)
    calc ‖ω y 0 + t • FiniteTimeSingularity.timeDeriv ω y 0‖
        ≤ ‖ω y 0‖ + ‖t • FiniteTimeSingularity.timeDeriv ω y 0‖ := norm_add_le _ _
      _ = ‖ω y 0‖ + |t| * ‖FiniteTimeSingularity.timeDeriv ω y 0‖ := by
            rw [norm_smul, Real.norm_eq_abs]
      _ ≤ M + (|t₀| + 1 + |S|) * |M₁| := add_le_add hb1 hmul
  · by_cases h2 : t ≤ S
    · -- inside the strip
      rw [windowExt_of_mem_Icc ⟨le_of_lt hlt, h2⟩]
      exact le_trans (hM t ⟨le_of_lt hlt, h2⟩ y) (le_add_of_nonneg_right hnn)
    · -- above the strip
      rw [windowExt_of_ge hS (le_of_lt (lt_of_not_ge h2))]
      have h1 : |t - S| ≤ |t₀| + 1 + |S| := by
        calc |t - S| ≤ |t| + |S| := abs_sub _ _
          _ ≤ |t₀| + 1 + |S| := by linarith
      have hmul : |t - S| * ‖FiniteTimeSingularity.timeDeriv ω y S‖
          ≤ (|t₀| + 1 + |S|) * |M₁| :=
        mul_le_mul h1 hb2S (norm_nonneg _) hSnn
      calc ‖ω y S + (t - S) • FiniteTimeSingularity.timeDeriv ω y S‖
          ≤ ‖ω y S‖ + ‖(t - S) • FiniteTimeSingularity.timeDeriv ω y S‖ := norm_add_le _ _
        _ = ‖ω y S‖ + |t - S| * ‖FiniteTimeSingularity.timeDeriv ω y S‖ := by
              rw [norm_smul, Real.norm_eq_abs]
        _ ≤ M + (|t₀| + 1 + |S|) * |M₁| := add_le_add hb1S hmul

end Work.CoreResiduals.BiotSavart
