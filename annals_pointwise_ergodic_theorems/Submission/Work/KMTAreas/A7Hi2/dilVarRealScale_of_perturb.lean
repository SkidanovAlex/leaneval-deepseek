import Mathlib
import Submission.Work.KMTAreas.A7Hi2.dilVarRealScale
import Submission.Port.Aesm

/-!
# The real-scale lacunary dilation variational estimate from a perturbation estimate

`Work.KMTAreas.A7Hi.DilVarClean` is the JSW/Lépingle lacunary variational estimate for *integral*
scales `σ : ℕ → ℕ`.  The real-scale form (needed by the low-pass Ionescu--Wainger walk) is deduced
here from the integral-scale estimate plus an estimate for the *perturbation* between a real scale
`τ` and the integer `⌊τ⌋`:

for real lacunary `σ`, with `c n = ⌊σ n⌋` (so that `c n ≤ σ n < c n + 1`, `c` is again lacunary, and
`K_{σ n} - K_{c n}` is a kernel of small mass),

  `K_{σ n} = K_{c n} + (K_{σ n} - K_{c n})`

pointwise (all three `tsum`s converge absolutely, for `f` bounded).  Subadditivity of the
variational norm then gives, pointwise in `x`,

  `Vʳ(n ↦ K_{σ n} * f x) ≤ Vʳ(n ↦ K_{c n} * f x) + Vʳ(n ↦ (K_{σ n} - K_{c n}) * f x)`,

and Minkowski's inequality in `ℓᵖ` plus the two estimates on the right (`DilVarClean` for the
integral-scale family, `hpert` for the perturbation family) yield the result.

The only subtlety is that the convolution `∑'_j (1/τ) K (j/τ) f (x - j)` is the junk value `0` for
an unbounded `f`, so the pointwise identity is not available in general.  But if the `ℓᵖ`-seminorm
of `f` is *infinite* then the target inequality is trivial (`⊤` on the right), and otherwise
`f ∈ ℓᵖ(ℤ) ⊆ ℓ^∞(ℤ)` is bounded and every `tsum` in sight converges absolutely.
-/

set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A7Hi2

open MeasureTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

/-! ## The two elementary ingredients -/

/-- The sampled dilation kernel of a Schwartz map at a real scale `τ ≥ 1` is summable: Schwartz
decay `‖K x‖ ≤ B (1 + |x|)^{-2}` gives the summable majorant `j ↦ B τ (1 + |j|)^{-2}`. -/
lemma summable_dilateR (K : SchwartzMap ℝ ℂ) {τ : ℝ} (hτ : 1 ≤ τ) :
    Summable (fun j : ℤ => (1 / τ) * K ((j : ℝ) / τ)) := by
  obtain ⟨B, hBpos, hB⟩ := Commons.Analysis.Fourier.schwartz_decay_real K 2
  have hτpos : (0 : ℝ) < τ := lt_of_lt_of_le one_pos hτ
  refine Summable.of_norm_bounded (f := fun j : ℤ => (1 / τ) * K ((j : ℝ) / τ))
    (g := fun j : ℤ => B * τ * (1 + |(j : ℝ)|) ^ (-2 : ℝ)) ?_ ?_
  · exact Work.KMTAreas.A7.summable_int_one_add_abs_neg_two.mul_left _
  · intro j
    have h := hB ((j : ℝ) / τ)
    have hfeq : (1 + |(j : ℝ) / τ|) = (1 + |(j : ℝ)| / τ) := by
      rw [abs_div, abs_of_pos hτpos]
    rw [hfeq] at h
    have hnn : (0 : ℝ) ≤ 1 / τ := by positivity
    calc ‖(1 / τ) * K ((j : ℝ) / τ)‖
        = (1 / τ) * ‖K ((j : ℝ) / τ)‖ := by
          rw [norm_mul, norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos hτpos, one_div]
      _ ≤ (1 / τ) * (B * (1 + |(j : ℝ)| / τ) ^ (-2 : ℝ)) :=
          mul_le_mul_of_nonneg_left h hnn
      _ ≤ (1 / τ) * (B * (τ ^ 2 * (1 + |(j : ℝ)|) ^ (-2 : ℝ))) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hBpos.le) hnn
          exact Work.KMTAreas.A7.one_add_div_rpow_neg_two_le τ hτ _
      _ = B * τ * (1 + |(j : ℝ)|) ^ (-2 : ℝ) := by field_simp

/-- **Splitting a dilated convolution sum at two real scales.**  For `τ, cc ≥ 1` and a bounded `f`,
the `τ`-dilated convolution sum is the `cc`-dilated sum plus the sum for the difference kernel
(both kernels are `ℓ¹` by `summable_dilateR`, so all three series converge absolutely). -/
lemma tsum_split_dilate (K : SchwartzMap ℝ ℂ) (τ : ℝ) (hτ : 1 ≤ τ) (cc : ℝ) (hcc : 1 ≤ cc)
    (f : ℤ → ℂ) (M : ℝ) (hM : ∀ x : ℤ, ‖f x‖ ≤ M) (x : ℤ) :
    (∑' j : ℤ, (1 / τ) * K ((j : ℝ) / τ) * f (x - j))
      = (∑' j : ℤ, (1 / cc) * K ((j : ℝ) / cc) * f (x - j))
        + (∑' j : ℤ, ((1 / τ) * K ((j : ℝ) / τ) - (1 / cc) * K ((j : ℝ) / cc))
            * f (x - j)) := by
  have h1 : Summable (fun j : ℤ => (1 / τ) * K ((j : ℝ) / τ) * f (x - j)) :=
    Work.KMTAreas.A7.summable_mul_bounded (fun j : ℤ => (1 / τ) * K ((j : ℝ) / τ))
      (summable_dilateR K hτ) f M hM x
  have h2 : Summable (fun j : ℤ => (1 / cc) * K ((j : ℝ) / cc) * f (x - j)) :=
    Work.KMTAreas.A7.summable_mul_bounded (fun j : ℤ => (1 / cc) * K ((j : ℝ) / cc))
      (summable_dilateR K hcc) f M hM x
  have hsub : (∑' j : ℤ, ((1 / τ) * K ((j : ℝ) / τ)
        - (1 / cc) * K ((j : ℝ) / cc)) * f (x - j))
      = (∑' j : ℤ, (1 / τ) * K ((j : ℝ) / τ) * f (x - j))
        - (∑' j : ℤ, (1 / cc) * K ((j : ℝ) / cc) * f (x - j)) := by
    rw [← Summable.tsum_sub h1 h2]
    exact tsum_congr fun j => by ring
  rw [hsub]
  ring

/-! ## The assembly -/

theorem dilVarRealScale_of_perturb (K : SchwartzMap ℝ ℂ)
    (hmass : ∃ Cm : ℝ, 0 < Cm ∧ ∀ (τ : ℝ) (hτ : 1 ≤ τ),
      (∑' j : ℤ, (1 / τ) * ‖K ((j : ℝ) / τ)‖) ≤ Cm)
    (hpert : ∀ (p : ℝ) (hp : 1 < p) (r : NNReal) (hr : 2 < r),
      ∃ C : ℝ, 0 < C ∧ ∀ (τ : ℕ → ℝ) (c : ℕ → ℕ) (hτ1 : ∀ n, 1 ≤ τ n)
        (hc1 : ∀ n, 1 ≤ c n) (hcτ : ∀ n, ((c n : ℕ) : ℝ) ≤ τ n ∧ τ n < ((c n : ℕ) : ℝ) + 1)
        (hτ2 : ∀ n, 2 * τ n ≤ τ (n + 1)) (f : ℤ → ℂ),
        MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => ∑' j : ℤ, ((1 / τ n) * K ((j : ℝ) / τ n)
              - (1 / ((c n : ℕ) : ℝ)) * K ((j : ℝ) / ((c n : ℕ) : ℝ))) * f (x - j)))
          (ENNReal.ofReal p) MeasureTheory.Measure.count
          ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm f (ENNReal.ofReal p)
              MeasureTheory.Measure.count)
    (p : ℝ) (hp : 1 < p) (r : NNReal) (hr : 2 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ (σ : ℕ → ℝ) (hσ1 : ∀ n, 1 ≤ σ n) (hσ2 : ∀ n, 2 * σ n ≤ σ (n + 1))
      (f : ℤ → ℂ),
      MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => ∑' j : ℤ, (1 / σ n) * K ((j : ℝ) / σ n) * f (x - j)))
        (ENNReal.ofReal p) MeasureTheory.Measure.count
        ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm f (ENNReal.ofReal p)
            MeasureTheory.Measure.count := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := hpert p hp r hr
  obtain ⟨C₂, hC₂pos, hC₂⟩ := Work.KMTAreas.A7Hi.DilVarClean p hp r hr K
  have hp0 : (0 : ℝ) < p := lt_trans zero_lt_one hp
  have hr1 : (1 : NNReal) ≤ r := le_trans (by norm_num : (1 : NNReal) ≤ 2) (le_of_lt hr)
  have hCpos : (0 : ℝ) < C₁ + C₂ := by linarith
  refine ⟨C₁ + C₂, hCpos, ?_⟩
  intro σ hσ1 hσ2 f
  set c : ℕ → ℕ := fun n => ⌊σ n⌋₊ with hcdef
  obtain ⟨hc1, hcle, hclt, hc2⟩ := roundRealScale σ hσ1 hσ2
  rcases eq_top_or_lt_top (a := MeasureTheory.eLpNorm f (ENNReal.ofReal p)
    (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)) with htop | hfin
  · -- `f ∉ ℓᵖ`: the right-hand side is `⊤`
    rw [htop, ENNReal.mul_top (ENNReal.ofReal_ne_zero_iff.mpr hCpos)]
    exact le_top
  · -- `f ∈ ℓᵖ`, hence `f` is bounded and the convolution sums are absolutely convergent
    have hq0 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr hp0).ne'
    have hqt : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
    have hQne : (∫⁻ x : ℤ, ‖f x‖ₑ ^ p
        ∂(MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)) ≠ ⊤ := by
      intro hc
      rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) hq0 hqt,
        ENNReal.toReal_ofReal hp0.le, hc,
        ENNReal.top_rpow_of_pos (by positivity : (0 : ℝ) < 1 / p)] at hfin
      exact absurd hfin (lt_irrefl _)
    obtain ⟨M, hM⟩ := Work.KMTAreas.A7.norm_le_of_summable_norm_rpow hp0
      (Work.KMTAreas.A7.summable_norm_rpow_of_lintegral_ne_top hp0 hQne)
    -- the pointwise variational inequality, `K_{σ n} = K_{c n} + (K_{σ n} - K_{c n})`
    have hpoint : ∀ x : ℤ, PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => ∑' j : ℤ, (1 / σ n) * K ((j : ℝ) / σ n) * f (x - j))
        ≤ PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => ∑' j : ℤ,
              (1 / ((c n : ℕ) : ℝ)) * K ((j : ℝ) / ((c n : ℕ) : ℝ)) * f (x - j))
          + PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => ∑' j : ℤ, ((1 / σ n) * K ((j : ℝ) / σ n)
              - (1 / ((c n : ℕ) : ℝ)) * K ((j : ℝ) / ((c n : ℕ) : ℝ))) * f (x - j)) := by
      intro x
      have hsplit : (fun n : ℕ => ∑' j : ℤ, (1 / σ n) * K ((j : ℝ) / σ n) * f (x - j))
          = (fun n : ℕ => ∑' j : ℤ,
                (1 / ((c n : ℕ) : ℝ)) * K ((j : ℝ) / ((c n : ℕ) : ℝ)) * f (x - j))
            + (fun n : ℕ => ∑' j : ℤ, ((1 / σ n) * K ((j : ℝ) / σ n)
                - (1 / ((c n : ℕ) : ℝ)) * K ((j : ℝ) / ((c n : ℕ) : ℝ))) * f (x - j)) := by
        funext n
        exact tsum_split_dilate K (σ n) (hσ1 n) (((c n : ℕ) : ℝ))
          (by exact_mod_cast hc1 n) f M hM x
      rw [hsplit]
      exact Submission.PointwiseErgodicTheorems.variationalNorm_add_le hr1 _ _
    refine (Work.KMTAreas.A7.eLpNorm_mono_ennreal hpoint hq0 hqt).trans ?_
    refine (Work.KMTAreas.A7Hi.eLpNorm_count_add_le p (le_of_lt hp) _ _).trans ?_
    refine (add_le_add (hC₂ c hc1 hc2 f)
      (hC₁ σ c hσ1 hc1 (fun n => ⟨hcle n, hclt n⟩) hσ2 f)).trans ?_
    rw [← add_mul, ← ENNReal.ofReal_add hC₂pos.le hC₁pos.le, add_comm C₂ C₁]

end

end Work.KMTAreas.A7Hi2
