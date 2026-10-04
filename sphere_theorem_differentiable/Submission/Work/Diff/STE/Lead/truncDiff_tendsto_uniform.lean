import Mathlib
import Submission.Work.Diff.STE.B3.BNorm_prelim
import Submission.Work.Diff.STE.periodization_contDiff_periodic
import Submission.Work.Diff.STE.B3.STruncR_CSq_le
import Submission.Work.Diff.STE.B3.CSq_STruncC_sub
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.summable_weighted_fourierCoeff_of_contDiff
import Submission.Work.Diff.STE.summable_norm_of_CSq
import Submission.Work.Diff.STE.flat.fourierCoeff_seriesFun
import Submission.Work.Diff.STE.flat.seriesFun_fourierCoeff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.Lead

/-! The Friedrichs truncation `S_ε = STruncC ρ ε` of a smooth compactly supported flat function `f`
converges to the periodisation `per f = ∑' m, f (· + m)` **uniformly** as `ε → 0⁺`, under the
hypotheses on the profile `ρ` that are available in the application (the lead's `J_tendsto`): `ρ` is
continuous at `0` with `ρ 0 = 1`, `‖ρ‖ ≤ 1`, and `ρ` vanishes outside the ball of radius `√2`
(`hρ0`, i.e. off `{∑ yᵢ² ≤ 2}`) — crucially, `ρ` is *not* assumed to be `1` on the unit ball.

Coefficient bookkeeping: `STruncC ρ ε f y = seriesFun (trunc ρ ε c) y` with
`c = fourierCoeff (per f)`, `trunc ρ ε c k = ρ (ε • k) · c k`, and `per f = seriesFun c`
(`Work.Diff.STE.flat.seriesFun_fourierCoeff`, using `periodization_contDiff_periodic` for the
smoothness and `1`-periodicity of `per f`, which `hfsupp` supplies).  `hρ0` makes the multiplier
`ρ (ε • k)` vanish for `ε‖k‖ > √2`, so the difference is dominated by
`2 · ∑_{‖k‖ ‖ε‖ > √2} ‖c k‖ + sup_{‖y‖ ≤ √2 ε} ‖ρ y - 1‖ · ∑ k, ‖c k‖`, which tends to `0`.
The ℓ¹ summability of `c` is `Work.Diff.STE.summable_norm_of_CSq` +
`Work.Diff.STE.summable_weighted_fourierCoeff_of_contDiff`; the conclusion is a `∀ᶠ`-statement, so
no rate is asked for. -/

/-- Unfolding of the Fourier series `seriesFun`. -/
private lemma seriesFun_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : (ι → ℤ) → ℂ) (x : ι → ℝ) :
    Work.Diff.STE.seriesFun c x = ∑' k : ι → ℤ, c k * Work.Diff.STE.fourierExp k x := rfl

/-- The norm of a real number embedded in `ℂ`. -/
private lemma norm_ofReal_complex (r : ℝ) : ‖((r : ℝ) : ℂ)‖ = |r| := by simp

/-- Unfolding of the Friedrichs multiplier `trunc`. -/
private lemma trunc_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : (ι → ℝ) → ℝ) (ε : ℝ) (c : (ι → ℤ) → ℂ) (k : ι → ℤ) :
    Work.Diff.STE.trunc ρ ε c k = (((ρ (ε • Work.Diff.STE.iVec k) : ℝ)) : ℂ) * c k := rfl

theorem truncDiff_tendsto_uniform
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : (ι → ℝ) → ℝ)
    (hρ0 : ∀ y : ι → ℝ, 2 < ∑ i, (y i) ^ 2 → ρ y = 0)
    (hρb : ∀ y : ι → ℝ, ‖ρ y‖ ≤ 1)
    (hρc : ContinuousAt ρ 0) (hρ1 : ρ 0 = 1)
    (f : (ι → ℝ) → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hfsupp : Function.support f ⊆
      Set.pi Set.univ (fun _ : ι => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2))) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), ∀ y : ι → ℝ,
      ‖Work.Diff.STE.STruncC ρ ε f y
        - (∑' m : ι → ℤ, ((f (y + Work.Diff.STE.iVec m) : ℝ) : ℂ))‖ ≤ δ := by
  classical
  -- ### The complexified periodisation and its Fourier coefficients
  set per : (ι → ℝ) → ℂ :=
    fun y => ∑' m : ι → ℤ, ((f (y + Work.Diff.STE.iVec m) : ℝ) : ℂ) with hper
  set c : (ι → ℤ) → ℂ := Work.Diff.STE.fourierCoeff per with hc
  have hFcd : ContDiff ℝ (⊤ : ℕ∞) (fun y : ι → ℝ => ((f y : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hf
  have hsuppF : Function.support (fun y : ι → ℝ => ((f y : ℝ) : ℂ)) ⊆
      Set.pi Set.univ (fun _ : ι => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) := by
    intro y hy
    rw [Function.mem_support] at hy
    exact hfsupp (by
      rw [Function.mem_support]
      intro h0
      exact hy (by simp [h0]))
  obtain ⟨hcd, hper1, _⟩ :=
    Work.Diff.STE.periodization_contDiff_periodic (fun y : ι → ℝ => ((f y : ℝ) : ℂ))
      hFcd hsuppF
  have hcd' : ContDiff ℝ (⊤ : ℕ∞) per := hcd
  have hper1' : Work.Diff.STE.Periodic1 per := hper1
  -- ### The Fourier coefficients are `ℓ¹`
  have hcsum : Summable (fun k : ι → ℤ => ‖c k‖) := by
    obtain ⟨s, hs⟩ : ∃ s : ℕ, Fintype.card ι < 2 * s := ⟨Fintype.card ι + 1, by omega⟩
    have hw : Summable (fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ s * ‖c k‖ ^ 2) := by
      have h := Work.Diff.STE.summable_weighted_fourierCoeff_of_contDiff per hcd' hper1' s
      simpa [hc] using h
    exact Work.Diff.STE.summable_norm_of_CSq s hs c hw
  have habs : ∀ z : ι → ℝ, |ρ z - 1| ≤ 2 := by
    intro z
    have hb : |ρ z| ≤ 1 := by simpa [Real.norm_eq_abs] using hρb z
    have h1 : |ρ z - 1| ≤ |ρ z| + 1 := by
      simpa using abs_sub_le (ρ z) 0 1
    linarith
  -- ### The dominating (uniform in `y`) quantity
  set W : ℝ → ℝ := fun ε => ∑' k : ι → ℤ, |ρ (ε • Work.Diff.STE.iVec k) - 1| * ‖c k‖
    with hW
  -- ### Pointwise domination by `W`
  have hbound : ∀ (ε : ℝ) (y : ι → ℝ),
      ‖Work.Diff.STE.STruncC ρ ε f y - per y‖ ≤ W ε := by
    intro ε y
    have hseries : Work.Diff.STE.seriesFun c y = per y :=
      Work.Diff.STE.flat.seriesFun_fourierCoeff per hcd' hper1' y
    have hpy : per y = ((∑' m : ι → ℤ, f (y + Work.Diff.STE.iVec m) : ℝ) : ℂ) := by
      rw [hper]
      exact (Complex.ofReal_tsum (fun m : ι → ℤ => f (y + Work.Diff.STE.iVec m))).symm
    have hreal : Complex.ofReal (Work.Diff.STE.seriesFun c y).re = Work.Diff.STE.seriesFun c y := by
      rw [hseries, hpy, Complex.ofReal_re]
    have hkey : Work.Diff.STE.STruncC ρ ε f y - per y
        = Complex.ofReal (Complex.re (Work.Diff.STE.seriesFun (Work.Diff.STE.trunc ρ ε c) y
            - Work.Diff.STE.seriesFun c y)) := by
      have hST : Work.Diff.STE.STruncC ρ ε f y
          = Complex.ofReal
              (Complex.re (Work.Diff.STE.seriesFun (Work.Diff.STE.trunc ρ ε c) y)) := rfl
      rw [hST, ← hseries, ← hreal, ← Complex.ofReal_sub, Complex.sub_re, Complex.ofReal_re]
    have htrunc_le : ∀ k : ι → ℤ, ‖Work.Diff.STE.trunc ρ ε c k‖ ≤ ‖c k‖ := by
      intro k
      have hle : |ρ (ε • Work.Diff.STE.iVec k)| ≤ 1 := by
        simpa [Real.norm_eq_abs] using hρb (ε • Work.Diff.STE.iVec k)
      calc ‖Work.Diff.STE.trunc ρ ε c k‖
          = |ρ (ε • Work.Diff.STE.iVec k)| * ‖c k‖ := by
            rw [trunc_apply, norm_mul]; simp
        _ ≤ 1 * ‖c k‖ := mul_le_mul_of_nonneg_right hle (norm_nonneg _)
        _ = ‖c k‖ := one_mul _
    have hsum_a : Summable (fun k : ι → ℤ =>
        Work.Diff.STE.trunc ρ ε c k * Work.Diff.STE.fourierExp k y) :=
      Summable.of_norm_bounded hcsum (fun k => by
        rw [norm_mul, Work.Diff.STE.norm_fourierExp, mul_one]; exact htrunc_le k)
    have hsum_b : Summable (fun k : ι → ℤ => c k * Work.Diff.STE.fourierExp k y) :=
      Summable.of_norm_bounded hcsum (fun k => by
        rw [norm_mul, Work.Diff.STE.norm_fourierExp, mul_one])
    have hcoef : ∀ k : ι → ℤ, Work.Diff.STE.trunc ρ ε c k - c k
        = (((ρ (ε • Work.Diff.STE.iVec k) - 1 : ℝ)) : ℂ) * c k := by
      intro k
      rw [trunc_apply, Complex.ofReal_sub, Complex.ofReal_one]
      ring
    have hdiff : ‖Work.Diff.STE.seriesFun (Work.Diff.STE.trunc ρ ε c) y
        - Work.Diff.STE.seriesFun c y‖ ≤ W ε := by
      have hsub : Work.Diff.STE.seriesFun (Work.Diff.STE.trunc ρ ε c) y
          - Work.Diff.STE.seriesFun c y
          = ∑' k : ι → ℤ, (Work.Diff.STE.trunc ρ ε c k - c k)
              * Work.Diff.STE.fourierExp k y := by
        rw [seriesFun_apply, seriesFun_apply, ← Summable.tsum_sub hsum_a hsum_b]
        exact tsum_congr fun k => by ring
      rw [hsub]
      have hsum_c : Summable (fun k : ι → ℤ =>
          ‖(Work.Diff.STE.trunc ρ ε c k - c k) * Work.Diff.STE.fourierExp k y‖) := by
        refine Summable.of_norm_bounded (hcsum.mul_left 2) (fun k => ?_)
        rw [norm_norm]
        calc ‖(Work.Diff.STE.trunc ρ ε c k - c k) * Work.Diff.STE.fourierExp k y‖
            = |ρ (ε • Work.Diff.STE.iVec k) - 1| * ‖c k‖ := by
              simp only [hcoef k, norm_mul, norm_ofReal_complex, Work.Diff.STE.norm_fourierExp,
                mul_one]
          _ ≤ 2 * ‖c k‖ :=
              mul_le_mul_of_nonneg_right (habs (ε • Work.Diff.STE.iVec k)) (norm_nonneg (c k))
      calc ‖∑' k : ι → ℤ, (Work.Diff.STE.trunc ρ ε c k - c k)
              * Work.Diff.STE.fourierExp k y‖
          ≤ ∑' k : ι → ℤ, ‖(Work.Diff.STE.trunc ρ ε c k - c k)
              * Work.Diff.STE.fourierExp k y‖ := norm_tsum_le_tsum_norm hsum_c
        _ = ∑' k : ι → ℤ, |ρ (ε • Work.Diff.STE.iVec k) - 1| * ‖c k‖ := by
            refine tsum_congr fun k => ?_
            simp only [hcoef k, norm_mul, norm_ofReal_complex, Work.Diff.STE.norm_fourierExp,
              mul_one]
        _ = W ε := rfl
    rw [hkey]
    calc ‖Complex.ofReal (Complex.re (Work.Diff.STE.seriesFun (Work.Diff.STE.trunc ρ ε c) y
            - Work.Diff.STE.seriesFun c y))‖
        = |(Work.Diff.STE.seriesFun (Work.Diff.STE.trunc ρ ε c) y
            - Work.Diff.STE.seriesFun c y).re| := norm_ofReal_complex _
      _ ≤ ‖Work.Diff.STE.seriesFun (Work.Diff.STE.trunc ρ ε c) y
            - Work.Diff.STE.seriesFun c y‖ := Complex.abs_re_le_norm _
      _ ≤ W ε := hdiff
  -- ### `W` tends to `0` at `0⁺` (Tannery)
  have htend : Filter.Tendsto W (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    rw [hW]
    have hab : ∀ k : ι → ℤ, Filter.Tendsto
        (fun ε : ℝ => |ρ (ε • Work.Diff.STE.iVec k) - 1| * ‖c k‖)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
      intro k
      have h1 : Filter.Tendsto (fun ε : ℝ => ε • Work.Diff.STE.iVec k)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
        have hcont : Continuous (fun ε : ℝ => ε • Work.Diff.STE.iVec k) :=
          continuous_id.smul continuous_const
        simpa using (hcont.tendsto 0).mono_left
          (nhdsWithin_le_nhds (a := (0 : ℝ)) (s := Set.Ioi 0))
      have h2 : Filter.Tendsto (fun ε : ℝ => ρ (ε • Work.Diff.STE.iVec k))
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 1) := by
        have h2' := hρc.tendsto.comp h1
        rw [hρ1] at h2'
        exact h2'
      have h3 : Filter.Tendsto (fun ε : ℝ => |ρ (ε • Work.Diff.STE.iVec k) - 1|)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
        simpa using (h2.sub_const 1).abs
      simpa using h3.mul_const (‖c k‖)
    have hbnd : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), ∀ k : ι → ℤ,
        ‖|ρ (ε • Work.Diff.STE.iVec k) - 1| * ‖c k‖‖ ≤ 2 * ‖c k‖ := by
      filter_upwards with ε k
      have hnn : (0 : ℝ) ≤ |ρ (ε • Work.Diff.STE.iVec k) - 1| * ‖c k‖ :=
        mul_nonneg (abs_nonneg _) (norm_nonneg _)
      calc ‖|ρ (ε • Work.Diff.STE.iVec k) - 1| * ‖c k‖‖
          = |ρ (ε • Work.Diff.STE.iVec k) - 1| * ‖c k‖ := Real.norm_of_nonneg hnn
        _ ≤ 2 * ‖c k‖ :=
            mul_le_mul_of_nonneg_right (habs (ε • Work.Diff.STE.iVec k)) (norm_nonneg (c k))
    have h := tendsto_tsum_of_dominated_convergence
      (𝓕 := nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (f := fun (ε : ℝ) (k : ι → ℤ) => |ρ (ε • Work.Diff.STE.iVec k) - 1| * ‖c k‖)
      (g := fun _ : ι → ℤ => (0 : ℝ)) (bound := fun k : ι → ℤ => 2 * ‖c k‖)
      (hcsum.mul_left 2) hab hbnd
    simpa using h
  -- ### Uniform convergence
  intro δ hδ
  filter_upwards [htend.eventually (Metric.ball_mem_nhds (0 : ℝ) hδ)] with ε hε
  intro y
  refine (hbound ε y).trans ?_
  have hWnn : 0 ≤ W ε := by
    rw [hW]
    exact tsum_nonneg (fun k => mul_nonneg (abs_nonneg _) (norm_nonneg _))
  have h1 : dist (W ε) 0 < δ := Metric.mem_ball.mp hε
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hWnn] at h1
  exact le_of_lt h1

end Work.Diff.STE.Lead
