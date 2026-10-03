import Mathlib
import Submission.Commons.Analysis.DiscreteCZ.discrete_convolution_lp_bounded
import Submission.Port.Aesm

namespace Commons.Analysis.DiscreteCZ

open _root_.MeasureTheory

/-- **Extension of an `ℓᵖ` convolution bound from finitely supported inputs.**

If the convolution operator `T f x = ∑'_y K (x - y) • f y` satisfies the `ℓᵖ` bound
`‖T f‖_p ≤ c ‖f‖_p` for every finitely supported `f`, then it satisfies the same bound for every
`f`.  The proof approximates `f` by its truncations `f_N = f · 1_{[-N,N]}` (which are finitely
supported), and applies Fatou's lemma for `eLpNorm`: at every point `x` either the convolution
series for `f` is summable, in which case the partial convolutions converge to `T f x`, or it is
not, in which case `T f x = 0` by the definition of `tsum`. -/
theorem lp_bound_of_finsupp {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    {K : ℤ → ℂ} {p c : ℝ} (hp : 0 < p) (hc : 0 ≤ c)
    (hfin : ∀ f : ℤ → H, (∃ t : Finset ℤ, ∀ x : ℤ, x ∉ t → f x = 0) →
      MeasureTheory.eLpNorm (fun x : ℤ => ∑' y : ℤ, K (x - y) • f y) (ENNReal.ofReal p)
          (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)
        ≤ ENNReal.ofReal c * MeasureTheory.eLpNorm f (ENNReal.ofReal p)
            (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)) :
    ∀ f : ℤ → H, Summable (fun n : ℤ => ‖f n‖ ^ p) →
      MeasureTheory.eLpNorm (fun x : ℤ => ∑' y : ℤ, K (x - y) • f y) (ENNReal.ofReal p)
          (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)
        ≤ ENNReal.ofReal c * MeasureTheory.eLpNorm f (ENNReal.ofReal p)
            (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ) := by
  intro f _hf
  -- Truncations of `f` to the symmetric intervals `[-N, N]`.
  let fN : ℕ → ℤ → H := fun N n => if n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) then f n else 0
  have hfN_supp : ∀ N, ∃ t : Finset ℤ, ∀ x : ℤ, x ∉ t → fN N x = 0 := fun N =>
    ⟨Finset.Icc (-(N : ℤ)) (N : ℤ), fun x hx => by simp only [fN]; rw [if_neg hx]⟩
  have hfN_le : ∀ N n, ‖fN N n‖ ≤ ‖f n‖ := by
    intro N n
    by_cases hn : n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ)
    · simp only [fN]; rw [if_pos hn]
    · simp only [fN]; rw [if_neg hn, norm_zero]; positivity
  -- The bound for the finitely supported truncations.
  have hboundN : ∀ N, MeasureTheory.eLpNorm (fun x : ℤ => ∑' y : ℤ, K (x - y) • fN N y)
        (ENNReal.ofReal p) (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)
      ≤ ENNReal.ofReal c * MeasureTheory.eLpNorm f (ENNReal.ofReal p)
          (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ) := by
    intro N
    refine (hfin (fN N) (hfN_supp N)).trans ?_
    gcongr
    exact eLpNorm_mono (hf := by pw_aesm) (fun n => hfN_le N n)
  -- Pointwise comparison of `T f` with the partial convolutions.
  have hpoint : ∀ x : ℤ,
      ‖∑' y : ℤ, K (x - y) • f y‖ₑ
        ≤ Filter.liminf (fun N => ‖∑' y : ℤ, K (x - y) • fN N y‖ₑ) Filter.atTop := by
    intro x
    by_cases hx : Summable (fun y : ℤ => K (x - y) • f y)
    · have hpartial : ∀ N, (∑' y : ℤ, K (x - y) • fN N y)
          = ∑ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), K (x - m) • f m := by
        intro N
        rw [tsum_eq_sum (s := Finset.Icc (-(N : ℤ)) (N : ℤ))
          (f := fun y : ℤ => K (x - y) • fN N y) (fun y hy => by
            simp only [fN]; rw [if_neg hy, smul_zero])]
        exact Finset.sum_congr rfl (fun m hm => by simp only [fN]; rw [if_pos hm])
      have hconv : Filter.Tendsto (fun N => ∑' y : ℤ, K (x - y) • fN N y) Filter.atTop
          (nhds (∑' y : ℤ, K (x - y) • f y)) := by
        have h1 := tendsto_sum_Icc_tsum_int (fun y : ℤ => K (x - y) • f y) hx
        exact h1.congr (fun N => (hpartial N).symm)
      have h4 : Filter.Tendsto (fun N => ‖∑' y : ℤ, K (x - y) • fN N y‖ₑ) Filter.atTop
          (nhds ‖∑' y : ℤ, K (x - y) • f y‖ₑ) :=
        (continuous_enorm.tendsto _).comp hconv
      rw [h4.liminf_eq]
    · have h0 : (∑' y : ℤ, K (x - y) • f y) = 0 := tsum_eq_zero_of_not_summable hx
      rw [h0, enorm_zero]
      exact bot_le
  -- Fatou's lemma for `eLpNorm`.
  refine (eLpNorm_le_liminf_of_enorm_le_liminf (E := H) hp
    (u := fun N x => ∑' y : ℤ, K (x - y) • fN N y)
    (U := fun x => ∑' y : ℤ, K (x - y) • f y) hpoint).trans ?_
  refine Filter.liminf_le_of_le (by isBoundedDefault) (fun b hb => ?_)
  obtain ⟨N, hN⟩ := hb.exists
  exact le_trans hN (hboundN N)

end Commons.Analysis.DiscreteCZ
