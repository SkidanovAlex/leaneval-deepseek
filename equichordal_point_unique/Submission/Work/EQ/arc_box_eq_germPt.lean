import Mathlib
import Submission.Work.EQ.Defs
import Submission.Work.EQ.hetero_box
import Submission.Work.EQ.hetero_leaf
import Submission.Work.EQ.arc_near_A1
import Submission.Work.EQ.germPt_basic
import Submission.Work.EQ.orb_sep
import Submission.Work.EQ.loc_estimates

namespace Work.EQ

open Complex Filter Set
open scoped Topology

noncomputable section

/-- **Intermediate value, from `0⁺`.**  If `f` is continuous on `(0,A)`, tends to `0` at `0⁺`,
and `y` lies strictly between `0` and `f (A/2)`, then `y` is attained strictly inside `(0,A)`. -/
lemma exists_eq_of_tendsto_zero {f : ℝ → ℝ} {A : ℝ} (hA : 0 < A)
    (hcont : ContinuousOn f (Ioo 0 A))
    (htend : Tendsto f (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0))
    {y : ℝ} (hy0 : 0 < y) (hy : y < f (A / 2)) :
    ∃ s : ℝ, 0 < s ∧ s < A ∧ f s = y := by
  have hA2lt : A / 2 < A := by linarith
  have hev : ∀ᶠ s in nhdsWithin (0 : ℝ) (Ioi 0), f s < y := htend (Iio_mem_nhds hy0)
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
  obtain ⟨δ, hδpos, hδ⟩ := hev
  set s₁ : ℝ := min (δ / 2) (A / 4) with hs₁def
  have hs₁pos : 0 < s₁ := by
    rw [hs₁def]; exact lt_min (by linarith) (by linarith)
  have hs₁ltδ : s₁ < δ := by
    rw [hs₁def]; exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hs₁ltA2 : s₁ < A / 2 := by
    rw [hs₁def]; exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hs₁y : f s₁ < y := by
    have hb : dist s₁ 0 < δ := by
      rw [Real.dist_eq, sub_zero, abs_of_pos hs₁pos]
      exact hs₁ltδ
    exact hδ hb (Set.mem_Ioi.mpr hs₁pos)
  have hcont' : ContinuousOn f (Icc s₁ (A / 2)) :=
    hcont.mono (fun x hx => ⟨lt_of_lt_of_le hs₁pos hx.1, lt_of_le_of_lt hx.2 hA2lt⟩)
  have hmem : y ∈ Ioo (f s₁) (f (A / 2)) := ⟨hs₁y, hy⟩
  obtain ⟨s, hs, hfs⟩ := intermediate_value_Ioo hs₁ltA2.le hcont' hmem
  exact ⟨s, lt_of_lt_of_le hs₁pos hs.1.le, lt_of_lt_of_le hs.2 hA2lt.le, hfs⟩

/-- **The arc near `A₁` is the germ curve.**  For a symmetric normalised equichordal curve and
a stable germ `h`, and for *any* prescribed `ε > 0`, there are thresholds `ρ', h' > 0`
(with `2ρ' < 1`) such that every point `z` of the upper arc with `0 < z.im ≤ h'` and
`|z.re + 1/2| ≤ ρ'` is a germ point with parameter `< ε`:
`∃ s, 0 < s ∧ s < ε ∧ germPt a h s = z`.

This is the converse of `germPt_mem_arc` (`Submission.Work.EQ.hetero_box`) and follows the same
route.  Take a `d : LocData a` (`locData_nonempty`); pick `ρ' := min (d.ρ/2) (1/8)` so that
`2ρ' ≤ d.ρ` and `2ρ' < 1`; pick `h'_0 ≤ d.h`, `h'_0 ≤ y₀` (from `chi_sep`) and
`d.C * h'_0^2 / (1 - d.κ^2) ≤ ρ'` so that `arc_chi_zero` applies.  Get `ε_g` from
`germ_chi_zero` (so that for `t < ε_g`, `germPt a h t` is in the box and `χ = 0`), and put
`ε'' := min ε ε_g ε₃` where `ε₃` is the continuity/positivity threshold of `germPt_basic`.
Then `g := fun s => (germPt a h s).im` is continuous on `(0, ε'')`, positive there, and tends to
`0` as `s → 0⁺` (because `germPt a h s → -1/2`, `germPt_basic`); hence for every
`y ∈ (0, Y)` with `Y := g (ε''/2) > 0` there is `s ∈ (0, ε'')` with `g s = y`
(`intermediate_value_Ioo` between a small `s₁` with `g s₁ < y` — which exists by the limit —
and `ε''/2`).  Take `h' := min h'_0 (Y/2)`.  For `z` in the box, `y := z.im` satisfies
`0 < y < Y`, so `z.im = (germPt a h s).im` for some `s ∈ (0, ε'')`.  Both `z` and
`germPt a h s` lie in the box and have `χ = 0` (`arc_chi_zero` resp. `germ_chi_zero`), and both
have the same height `y ≤ y₀`, so `chi_sep` forces `z.re + 1/2 = (germPt a h s).re + 1/2`;
with equal heights this gives `germPt a h s = z` (`Complex.ext`). -/
theorem arc_box_eq_germPt {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {ρ₁ ρ₂ : ℝ → ℝ}
    (hC : NormEqCurve a ρ₁ ρ₂) (hs₁ : ∀ θ, ρ₁ (-θ) = ρ₁ θ) (hs₂ : ∀ θ, ρ₂ θ = ρ₁ (Real.pi - θ))
    {h : ℂ → ℂ} {r : ℝ} (hh : IsStableGerm a h r) (ε : ℝ) (hε : 0 < ε) :
    ∃ ρ' h' : ℝ, 0 < ρ' ∧ 0 < h' ∧ 2 * ρ' < 1 ∧
      ∀ z : ℂ, z ∈ arcSet a ρ₁ → 0 < z.im → z.im ≤ h' → |z.re + 1 / 2| ≤ ρ' →
        ∃ s : ℝ, 0 < s ∧ s < ε ∧ germPt a h s = z := by
  obtain ⟨d⟩ := locData_nonempty ha0 ha1
  -- the working width
  set ρ' : ℝ := min (d.ρ / 2) (1 / 8) with hρ'def
  have hρ'pos : 0 < ρ' := by
    rw [hρ'def]; exact lt_min (by linarith [d.ρpos]) (by norm_num)
  have h2ρ'ρ : 2 * ρ' ≤ d.ρ := by
    rw [hρ'def]; have := min_le_left (d.ρ / 2) (1 / 8); linarith
  have h2ρ'1 : 2 * ρ' < 1 := by
    rw [hρ'def]; have := min_le_right (d.ρ / 2) (1 / 8); linarith
  -- separation threshold
  obtain ⟨y₀, hy₀pos, hy₀h, hy₀sep⟩ := chi_sep d hρ'pos h2ρ'ρ
  -- the drift threshold
  set h'₀ : ℝ := min y₀ (min (Real.sqrt (ρ' * (1 - d.κ ^ 2) / d.C)) d.h) with hh'₀def
  have hh'₀pos : 0 < h'₀ := by
    rw [hh'₀def]
    exact lt_min hy₀pos (lt_min (Real.sqrt_pos.mpr (div_pos (mul_pos hρ'pos d.one_sub_sq_pos)
      d.Cpos)) d.hpos)
  have hh'₀y₀ : h'₀ ≤ y₀ := by rw [hh'₀def]; exact min_le_left _ _
  have hh'₀h : h'₀ ≤ d.h := by
    rw [hh'₀def]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hh'₀drift : d.C * h'₀ ^ 2 / (1 - d.κ ^ 2) ≤ ρ' := by
    have hsqrt : h'₀ ≤ Real.sqrt (ρ' * (1 - d.κ ^ 2) / d.C) := by
      rw [hh'₀def]; exact le_trans (min_le_right _ _) (min_le_left _ _)
    have h0 : 0 ≤ ρ' * (1 - d.κ ^ 2) / d.C :=
      (div_pos (mul_pos hρ'pos d.one_sub_sq_pos) d.Cpos).le
    have hsq : h'₀ ^ 2 ≤ ρ' * (1 - d.κ ^ 2) / d.C := by
      calc h'₀ ^ 2 ≤ (Real.sqrt (ρ' * (1 - d.κ ^ 2) / d.C)) ^ 2 :=
            pow_le_pow_left₀ hh'₀pos.le hsqrt 2
        _ = ρ' * (1 - d.κ ^ 2) / d.C := Real.sq_sqrt h0
    calc d.C * h'₀ ^ 2 / (1 - d.κ ^ 2)
        ≤ d.C * (ρ' * (1 - d.κ ^ 2) / d.C) / (1 - d.κ ^ 2) := by
          apply div_le_div_of_nonneg_right _ d.one_sub_sq_pos.le
          exact mul_le_mul_of_nonneg_left hsq d.Cpos.le
      _ = ρ' := by
          rw [mul_div_assoc', mul_div_cancel_left₀ _ (ne_of_gt d.Cpos)]
          exact mul_div_cancel_right₀ ρ' (ne_of_gt d.one_sub_sq_pos)
  -- the germ-`χ` threshold
  obtain ⟨ε_g, hε_gpos, hε_g⟩ := germ_chi_zero ha0 ha1 hh d hρ'pos h2ρ'ρ hh'₀pos hh'₀h
  -- the basic germ threshold
  obtain ⟨ε₃, hε₃pos, hε₃cont, hε₃im, hε₃tend⟩ := germPt_basic ha0 ha1 hh
  -- the working germ parameter bound
  set ε₀ : ℝ := min (min ε ε_g) ε₃ / 2 with hε₀def
  have hε₀pos : 0 < ε₀ := by
    rw [hε₀def]; exact div_pos (lt_min (lt_min hε hε_gpos) hε₃pos) (by norm_num)
  have hε₀ε₃ : ε₀ ≤ ε₃ := by
    rw [hε₀def]
    have h1 : min (min ε ε_g) ε₃ / 2 ≤ min (min ε ε_g) ε₃ := by
      have h3 : 0 ≤ min (min ε ε_g) ε₃ := le_of_lt (lt_min (lt_min hε hε_gpos) hε₃pos)
      linarith
    exact le_trans h1 (min_le_right _ _)
  have hε₀εg : ε₀ < ε_g := by
    rw [hε₀def]
    have h1 : min (min ε ε_g) ε₃ / 2 ≤ min ε ε_g / 2 :=
      div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
    have h2 : min ε ε_g ≤ ε_g := min_le_right _ _
    have h3 : 0 < min ε ε_g := lt_min hε hε_gpos
    linarith
  have hε₀ε : ε₀ < ε := by
    rw [hε₀def]
    have h1 : min (min ε ε_g) ε₃ / 2 ≤ min ε ε_g / 2 :=
      div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
    have h2 : min ε ε_g ≤ ε := min_le_left _ _
    have h3 : 0 < min ε ε_g := lt_min hε hε_gpos
    linarith
  -- the height function
  have hgcont : ContinuousOn (fun s : ℝ => (germPt a h s).im) (Ioo 0 ε₀) :=
    Complex.continuous_im.comp_continuousOn
      (hε₃cont.mono (fun x hx => ⟨hx.1, lt_of_lt_of_le hx.2 hε₀ε₃⟩))
  have hgtend : Tendsto (fun s : ℝ => (germPt a h s).im) (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0) := by
    have h1 := (Complex.continuous_im.tendsto (((-(1 / 2) : ℝ)) : ℂ)).comp hε₃tend
    have h2 : (fun s : ℝ => (germPt a h s).im) = (Complex.im ∘ germPt a h) := rfl
    rw [h2]
    simpa using h1
  -- every height below `g (ε₀/2)` is attained
  have hcov : ∀ y : ℝ, 0 < y → y < (germPt a h (ε₀ / 2)).im →
      ∃ s : ℝ, 0 < s ∧ s < ε₀ ∧ (germPt a h s).im = y :=
    fun y hy0 hyY => exists_eq_of_tendsto_zero hε₀pos hgcont hgtend hy0 hyY
  have hYpos : 0 < (germPt a h (ε₀ / 2)).im :=
    hε₃im (ε₀ / 2) (by linarith) (by linarith [hε₀pos, hε₀ε₃])
  -- conclusion
  refine ⟨ρ', min h'₀ ((germPt a h (ε₀ / 2)).im / 2), hρ'pos,
    lt_min hh'₀pos (by linarith), h2ρ'1, ?_⟩
  intro z hz hzim hzy hzx
  have hy0 : 0 < z.im := hzim
  have hzy₀ : z.im ≤ y₀ := le_trans (le_trans hzy (min_le_left _ _)) hh'₀y₀
  have hyY : z.im < (germPt a h (ε₀ / 2)).im := by
    have h1 : z.im ≤ (germPt a h (ε₀ / 2)).im / 2 := le_trans hzy (min_le_right _ _)
    linarith [hYpos]
  obtain ⟨s, hs0, hslt, hsim⟩ := hcov z.im hy0 hyY
  have hsε : s < ε := lt_of_lt_of_le hslt hε₀ε.le
  have hsεg : s < ε_g := lt_of_lt_of_le hslt hε₀εg.le
  obtain ⟨hboxg, -, hχg⟩ := hε_g s hs0 hsεg
  -- `χ` vanishes at `z`
  have hh'h : min h'₀ ((germPt a h (ε₀ / 2)).im / 2) ≤ d.h :=
    le_trans (min_le_left _ _) hh'₀h
  have hdrift : d.C * (min h'₀ ((germPt a h (ε₀ / 2)).im / 2)) ^ 2 / (1 - d.κ ^ 2) ≤ ρ' := by
    have hle : min h'₀ ((germPt a h (ε₀ / 2)).im / 2) ≤ h'₀ := min_le_left _ _
    have hpos : 0 < min h'₀ ((germPt a h (ε₀ / 2)).im / 2) :=
      lt_min hh'₀pos (by linarith [hYpos])
    have hsq : (min h'₀ ((germPt a h (ε₀ / 2)).im / 2)) ^ 2 ≤ h'₀ ^ 2 :=
      pow_le_pow_left₀ hpos.le hle 2
    calc d.C * (min h'₀ ((germPt a h (ε₀ / 2)).im / 2)) ^ 2 / (1 - d.κ ^ 2)
        ≤ d.C * h'₀ ^ 2 / (1 - d.κ ^ 2) := by
          apply div_le_div_of_nonneg_right _ d.one_sub_sq_pos.le
          exact mul_le_mul_of_nonneg_left hsq d.Cpos.le
      _ ≤ ρ' := hh'₀drift
  have hχz : LocData.chi a (z.re + 1 / 2) z.im = 0 :=
    arc_chi_zero ha0 ha1 hC hs₁ hs₂ d hρ'pos h2ρ'ρ h2ρ'1 hh'h hdrift hz hzim hzx hzy
  -- the germ point has the same `χ`
  have hχs : LocData.chi a ((germPt a h s).re + 1 / 2) z.im = 0 := by
    rw [← hsim]; exact hχg
  have hxeq : (germPt a h s).re + 1 / 2 = z.re + 1 / 2 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have h := hy₀sep _ _ z.im hboxg hzx hlt hy0 hzy₀
      rw [hχs, hχz] at h
      exact absurd h (lt_irrefl 0)
    · have h := hy₀sep _ _ z.im hzx hboxg hlt hy0 hzy₀
      rw [hχz, hχs] at h
      exact absurd h (lt_irrefl 0)
  refine ⟨s, hs0, hsε, ?_⟩
  apply Complex.ext
  · show (germPt a h s).re = z.re
    linarith
  · show (germPt a h s).im = z.im
    exact hsim

end

end Work.EQ
