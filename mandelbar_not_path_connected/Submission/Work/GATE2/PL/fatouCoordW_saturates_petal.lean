import Mathlib
import Submission.Work.FatouCoord.Exist.fatouCoordW_image_bdd
import Submission.Work.FatouCoord.Main
import Submission.Work.GATE2.PL.continuousOn_root_of_strictMono
import Submission.Work.GATE2.PL.existsUnique_im_eq_of_pair
import Submission.Work.GATE2.PL.re_growth_of_pair

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The chart Fatou coordinate saturates a right half-plane, with preimages far to the right

For a parabolic germ `f z = z + z ^ 2 * h z` (`h 0 = 1`) quantified by `ParabolicBounds`, and
for `Re (1 - a) > 0` (i.e. `Re a < 1`, the hypothesis `ha`), the Fatou coordinate in the chart
`w = -1/z`,

`ψ w = fatouCoordW f (1 - a) w = w - (1 - a) log w + O(1/Re w)`,

takes every value `τ` of a right half-plane `{Re τ > X}` at a point `w` with arbitrarily
prescribed lower bound `Mh` on `Re w`:

`∃ X, ∀ τ, X < Re τ → ∃ w, Mh < Re w ∧ ψ w = τ`.

This strengthens `Exist.fatouCoordW_image_bdd`, which only reaches the points of a *strip*
`|Im τ| ≤ B`.  The extra work is the imaginary direction: we follow, for each `s > N`, the
unique point `t s` on the vertical line `Re w = s` with `Im ψ (s + i t s) = Im τ`, and show that
`F s = Re ψ (s + i t s)` is continuous and grows at least linearly in `s`.  The two inputs are

* the mean value bound `‖ψ w₂ - ψ w₁ - (w₂ - w₁)‖ ≤ (1/2) ‖w₂ - w₁‖` on `{Re w > N}`, valid
  because `‖deriv ψ - 1‖ ≤ 1/2` there (`fatouCoordW_deriv_close`);
* the upper bound `Re ψ w ≤ Re w + |Im (1 - a)| π/2 + K / Re w`, which follows from
  `ψ w = w - (1 - a) log w + O(1/Re w)` and `|arg w| ≤ π/2` for `Re w > 0`
  (`fatouCoordW_tsum_bound`).

The point is that `Re ψ w` at the *height* `Im τ` is at most `s + |Im (1-a)| π/2 + o(1)`, so a
target with large enough real part is to the right of the graph of `F`, while `F → +∞`
linearly; the intermediate value theorem then produces the preimage.
-/

open Set Filter Metric Function
open scoped Topology

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace Work.GATE2.PL

noncomputable section

variable {ψ : ℂ → ℂ}

/-- The half-plane `{Re > N}` is convex. -/
lemma convex_re_gt (N : ℝ) : Convex ℝ {w : ℂ | N < w.re} := by
  have h : Convex ℝ (Complex.reLm ⁻¹' (Set.Ioi N)) := (convex_Ioi N).linear_preimage Complex.reLm
  convert h using 1
  ext z
  simp [Complex.reLm, Set.mem_Ioi]

/-- **Mean value bound.**  If `ψ` is (complex) differentiable on the half-plane `{Re > N}` and
`‖deriv ψ - 1‖ ≤ C` there, then `ψ` differs from the identity by a `C`-Lipschitz map there. -/
lemma pair_bound {N C : ℝ} {ψ : ℂ → ℂ}
    (hdiff : ∀ w : ℂ, N < w.re → DifferentiableAt ℂ ψ w)
    (hderiv : ∀ w : ℂ, N < w.re → ‖deriv ψ w - 1‖ ≤ C) :
    ∀ w₁ w₂ : ℂ, N < w₁.re → N < w₂.re →
      ‖ψ w₂ - ψ w₁ - (w₂ - w₁)‖ ≤ C * ‖w₂ - w₁‖ := by
  intro w₁ w₂ h₁ h₂
  have hf : ∀ x ∈ {w : ℂ | N < w.re}, DifferentiableAt ℂ (fun w : ℂ => ψ w - w) x :=
    fun x hx => (hdiff x hx).sub differentiableAt_id
  have hb : ∀ x ∈ {w : ℂ | N < w.re}, ‖deriv (fun w : ℂ => ψ w - w) x‖ ≤ C := by
    intro x hx
    have h2 : deriv (fun w : ℂ => ψ w - w) x = deriv ψ x - 1 := by
      have h3 : deriv (fun w : ℂ => ψ w - w) x = deriv ψ x - deriv (fun w : ℂ => w) x :=
        deriv_sub (hdiff x hx) differentiableAt_id
      rw [h3]
      simp
    rw [h2]
    exact hderiv x hx
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℂ) hf hb (convex_re_gt N) h₁ h₂
  convert h using 2
  ring

/-- Lower bound for the change of the imaginary part along a vertical segment. -/
lemma im_diff_ge {N C : ℝ} {ψ : ℂ → ℂ}
    (hpair : ∀ w₁ w₂ : ℂ, N < w₁.re → N < w₂.re →
      ‖ψ w₂ - ψ w₁ - (w₂ - w₁)‖ ≤ C * ‖w₂ - w₁‖)
    {s : ℝ} (hs : N < s) {t₁ t₂ : ℝ} (h : t₁ ≤ t₂) :
    (1 - C) * (t₂ - t₁) ≤
      (ψ ((s : ℂ) + (t₂ : ℂ) * Complex.I)).im - (ψ ((s : ℂ) + (t₁ : ℂ) * Complex.I)).im := by
  have h₁ : N < ((s : ℂ) + (t₁ : ℂ) * Complex.I).re := by simpa using hs
  have h₂ : N < ((s : ℂ) + (t₂ : ℂ) * Complex.I).re := by simpa using hs
  have hpair' := hpair _ _ h₁ h₂
  have hnorm : ‖((s : ℂ) + (t₂ : ℂ) * Complex.I) - ((s : ℂ) + (t₁ : ℂ) * Complex.I)‖
      = t₂ - t₁ := by
    have hsub : ((s : ℂ) + (t₂ : ℂ) * Complex.I) - ((s : ℂ) + (t₁ : ℂ) * Complex.I)
        = (((t₂ - t₁ : ℝ)) : ℂ) * Complex.I := by rw [Complex.ofReal_sub]; ring
    rw [hsub, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_nonneg (by linarith : (0 : ℝ) ≤ t₂ - t₁)
  have him : (ψ ((s : ℂ) + (t₂ : ℂ) * Complex.I) - ψ ((s : ℂ) + (t₁ : ℂ) * Complex.I)
      - (((s : ℂ) + (t₂ : ℂ) * Complex.I) - ((s : ℂ) + (t₁ : ℂ) * Complex.I))).im
      = (ψ ((s : ℂ) + (t₂ : ℂ) * Complex.I)).im - (ψ ((s : ℂ) + (t₁ : ℂ) * Complex.I)).im
        - (t₂ - t₁) := by
    simp only [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re,
      Complex.I_im, Complex.I_re, mul_zero, mul_one, add_zero]
    ring
  have ha := Complex.abs_im_le_norm (ψ ((s : ℂ) + (t₂ : ℂ) * Complex.I)
      - ψ ((s : ℂ) + (t₁ : ℂ) * Complex.I)
      - (((s : ℂ) + (t₂ : ℂ) * Complex.I) - ((s : ℂ) + (t₁ : ℂ) * Complex.I)))
  rw [him] at ha
  rw [hnorm] at hpair'
  have := (abs_le.mp (le_trans ha hpair')).1
  linarith

/-- The imaginary part of `ψ` is strictly increasing along each vertical line `{Re = s}`. -/
lemma im_strictMono {N C : ℝ} {ψ : ℂ → ℂ} (hC1 : C < 1)
    (hpair : ∀ w₁ w₂ : ℂ, N < w₁.re → N < w₂.re →
      ‖ψ w₂ - ψ w₁ - (w₂ - w₁)‖ ≤ C * ‖w₂ - w₁‖)
    {s : ℝ} (hs : N < s) :
    StrictMono (fun t : ℝ => (ψ ((s : ℂ) + (t : ℂ) * Complex.I)).im) := by
  intro t₁ t₂ ht
  have h := im_diff_ge hpair hs (le_of_lt ht)
  have hpos : 0 < (1 - C) * (t₂ - t₁) := mul_pos (by linarith) (by linarith)
  linarith

/-- Joint continuity of `(s, z) ↦ Im ψ (s + z i)` at the points of the half-plane `{Re > N}`. -/
lemma continuousAt_pair {N : ℝ} {ψ : ℂ → ℂ}
    (hdiff : ∀ w : ℂ, N < w.re → DifferentiableAt ℂ ψ w) {s z : ℝ} (hs : N < s) :
    ContinuousAt (fun p : ℝ × ℝ => (ψ ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)).im) (s, z) := by
  have hdiffOn : DifferentiableOn ℂ ψ {w : ℂ | N < w.re} :=
    fun w hw => (hdiff w hw).differentiableWithinAt
  have hcontOn : ContinuousOn ψ {w : ℂ | N < w.re} := hdiffOn.continuousOn
  let F : ℝ × ℝ → ℂ := fun p => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I
  have hFmem : F (s, z) ∈ {w : ℂ | N < w.re} := by
    have hre : (F (s, z)).re = s := by dsimp only [F]; simp
    rw [Set.mem_ofPred_eq, hre]; exact hs
  have h1 : ContinuousAt ψ (F (s, z)) :=
    hcontOn.continuousAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hFmem)
  have hFcont : Continuous F :=
    (Complex.continuous_ofReal.comp continuous_fst).add
      ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const)
  have h2 : ContinuousAt (ψ ∘ F) (s, z) := h1.comp hFcont.continuousAt
  have h3 : ContinuousAt (Complex.im ∘ (ψ ∘ F)) (s, z) :=
    Complex.continuous_im.continuousAt.comp h2
  dsimp only [F] at h3
  exact h3

/-- **Upper bound for the real part.**  If `ψ` differs from `approxCoord c w = w - c log w`
by at most `K / Re w` on the half-plane `{Re > N}`, and `0 ≤ Re c`, then on that half-plane
`Re ψ w ≤ Re w + |Im c| π/2 + K / Re w`. -/
lemma re_le_of_norm_sub {c : ℂ} {ψ : ℂ → ℂ} {N K : ℝ} (hcR : 0 ≤ c.re) (hK : 0 ≤ K)
    (hb : ∀ w : ℂ, N < w.re → ‖ψ w - Work.FatouCoord.approxCoord c w‖ ≤ K / w.re)
    {w : ℂ} (hN : N < w.re) (h1 : 1 ≤ w.re) :
    (ψ w).re ≤ w.re + |c.im| * (Real.pi / 2) + K / w.re := by
  have hw0 : 0 < w.re := lt_of_lt_of_le zero_lt_one h1
  have hwnorm1 : 1 ≤ ‖w‖ := le_trans h1 (Complex.re_le_norm w)
  have hlog : 0 ≤ Real.log ‖w‖ := Real.log_nonneg hwnorm1
  have harg : |w.arg| ≤ Real.pi / 2 := Complex.abs_arg_le_pi_div_two_iff.mpr (le_of_lt hw0)
  have harg' := abs_le.mp harg
  have happrox : (Work.FatouCoord.approxCoord c w).re ≤ w.re + |c.im| * (Real.pi / 2) := by
    rw [Work.FatouCoord.approxCoord_apply, Complex.sub_re, Complex.mul_re, Complex.log_re,
      Complex.log_im]
    have hclog : 0 ≤ c.re * Real.log ‖w‖ := mul_nonneg hcR hlog
    have hargle : c.im * w.arg ≤ |c.im| * (Real.pi / 2) := by
      rcases lt_trichotomy c.im 0 with hc | hc | hc
      · have h4 : c.im * w.arg ≤ c.im * (-(Real.pi / 2)) := mul_le_mul_of_nonpos_left harg'.1 hc.le
        rw [abs_of_neg hc]; linarith
      · rw [hc]; simp
      · have h4 : c.im * w.arg ≤ c.im * (Real.pi / 2) := mul_le_mul_of_nonneg_left harg'.2 hc.le
        rw [abs_of_nonneg hc.le]; linarith
    linarith
  have hsplit : (ψ w).re = (Work.FatouCoord.approxCoord c w).re
      + (ψ w - Work.FatouCoord.approxCoord c w).re := by
    rw [← Complex.add_re, add_sub_cancel]
  have hle : (ψ w - Work.FatouCoord.approxCoord c w).re
      ≤ ‖ψ w - Work.FatouCoord.approxCoord c w‖ := Complex.re_le_norm _
  have hb' := hb w hN
  linarith

/-- **The chart Fatou coordinate saturates a right half-plane with preimages of large real
part.**  For a parabolic germ satisfying `ParabolicBounds`, the Fatou coordinate
`ψ = fatouCoordW f (1 - a)` in the chart `w = -1/z` maps `{Re w > Mh}` onto the right
half-plane `{Re τ > X}`. -/
theorem fatouCoordW_saturates_petal {f h : ℂ → ℂ} {a : ℂ} {r A A' : ℝ}
    (hb : Work.FatouCoord.ParabolicBounds f h a r A A') (ha : a.re < 1) (Mh : ℝ) :
    ∃ X : ℝ, ∀ τ : ℂ, X < τ.re →
      ∃ w : ℂ, Mh < w.re ∧ Work.FatouCoord.fatouCoordW f (1 - a) w = τ := by
  obtain ⟨Nd, hNdpos, _hrNd, hdiffd⟩ := Work.FatouCoord.Exist.fatouCoordW_differentiable hb
  obtain ⟨Nc, hNcpos, _hrNc, hderc⟩ := Work.FatouCoord.Exist.fatouCoordW_deriv_close hb
  obtain ⟨Nb, K, hNbpos, _hrNb, hKnn, hbdd⟩ := Work.FatouCoord.Exist.fatouCoordW_tsum_bound hb
  set N : ℝ := max (max Nd Nc) (max Nb 1) + 1 with hNdef
  have hNdN : Nd < N := by
    rw [hNdef]
    have h1 : Nd ≤ max Nd Nc := le_max_left _ _
    have h2 : max Nd Nc ≤ max (max Nd Nc) (max Nb 1) := le_max_left _ _
    linarith
  have hNcN : Nc < N := by
    rw [hNdef]
    have h1 : Nc ≤ max Nd Nc := le_max_right _ _
    have h2 : max Nd Nc ≤ max (max Nd Nc) (max Nb 1) := le_max_left _ _
    linarith
  have hNbN : Nb < N := by
    rw [hNdef]
    have h1 : Nb ≤ max Nb 1 := le_max_left _ _
    have h2 : max Nb 1 ≤ max (max Nd Nc) (max Nb 1) := le_max_right _ _
    linarith
  have hN1 : (1 : ℝ) < N := by
    rw [hNdef]
    have h1 : (1 : ℝ) ≤ max Nb 1 := le_max_right _ _
    have h2 : max Nb 1 ≤ max (max Nd Nc) (max Nb 1) := le_max_right _ _
    linarith
  have hcR : (0 : ℝ) ≤ (1 - a).re := by
    rw [Complex.sub_re, Complex.one_re]
    linarith
  -- differentiability and derivative bound on the half-plane `{Re > N}`
  have hdiff : ∀ w : ℂ, N < w.re → DifferentiableAt ℂ (Work.FatouCoord.fatouCoordW f (1 - a)) w := by
    intro w hw
    have hNd : Nd < w.re := lt_trans hNdN hw
    exact (hdiffd w hNd).differentiableAt
      ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hNd)
  have hderiv : ∀ w : ℂ, N < w.re →
      ‖deriv (Work.FatouCoord.fatouCoordW f (1 - a)) w - 1‖ ≤ (1 / 2 : ℝ) :=
    fun w hw => hderc w (lt_trans hNcN hw)
  have hpair := pair_bound hdiff hderiv
  have hC1 : (1 / 2 : ℝ) < 1 := by norm_num
  -- the level and the threshold
  set s₀ : ℝ := max N Mh + 1 with hs₀def
  have hNs₀ : N < s₀ := by
    rw [hs₀def]
    have h : N ≤ max N Mh := le_max_left _ _
    linarith
  have hMhs₀ : Mh < s₀ := by
    rw [hs₀def]
    have h : Mh ≤ max N Mh := le_max_right _ _
    linarith
  have h1s₀ : (1 : ℝ) ≤ s₀ := le_of_lt (lt_trans hN1 hNs₀)
  set X : ℝ := s₀ + |(1 - a).im| * (Real.pi / 2) + K / s₀ + 1 with hXdef
  refine ⟨X, ?_⟩
  intro τ hτ
  set y : ℝ := τ.im with hydef
  -- the level set `t s` of the imaginary part on the vertical line `Re = s`
  have hexU : ∀ s : ℝ, s₀ ≤ s →
      ∃! u : ℝ, (Work.FatouCoord.fatouCoordW f (1 - a) ((s : ℂ) + (u : ℂ) * Complex.I)).im = y :=
    fun s hs => existsUnique_im_eq_of_pair hC1 hpair (lt_of_lt_of_le hNs₀ hs) y
  let t : ℝ → ℝ := fun s => if h : s₀ ≤ s then Classical.choose (hexU s h) else 0
  have ht : ∀ s : ℝ, s₀ ≤ s →
      (Work.FatouCoord.fatouCoordW f (1 - a) ((s : ℂ) + (t s : ℂ) * Complex.I)).im = y := by
    intro s hs
    dsimp only [t]
    rw [dite_eq_left hs]
    exact (Classical.choose_spec (hexU s hs)).1
  -- continuity of `t`
  have htcont : ContinuousOn t (Ici s₀) := by
    refine continuousOn_root_of_strictMono
      (T := fun s z => (Work.FatouCoord.fatouCoordW f (1 - a) ((s : ℂ) + (z : ℂ) * Complex.I)).im)
      (S := Ici s₀) (y := y) (t := t) ?_ ?_ ?_
    · intro s hs
      exact im_strictMono hC1 hpair (lt_of_lt_of_le hNs₀ hs)
    · intro s hs z
      exact continuousAt_pair hdiff (lt_of_lt_of_le hNs₀ hs)
    · intro s hs
      exact ht s hs
  -- the real part along the level set
  set F : ℝ → ℝ :=
    fun s => (Work.FatouCoord.fatouCoordW f (1 - a) ((s : ℂ) + (t s : ℂ) * Complex.I)).re
    with hFdef
  have hFcont : ContinuousOn F (Ici s₀) := by
    have hline : ContinuousOn (fun s : ℝ => ((s : ℂ) + (t s : ℂ) * Complex.I)) (Ici s₀) := by
      have h1 : ContinuousOn (fun s : ℝ => (t s : ℂ)) (Ici s₀) :=
        Complex.continuous_ofReal.comp_continuousOn htcont
      have h2 : ContinuousOn (fun s : ℝ => (s : ℂ)) (Ici s₀) :=
        Complex.continuous_ofReal.comp_continuousOn continuousOn_id
      exact h2.add (h1.mul continuousOn_const)
    have hdiffOn : DifferentiableOn ℂ (Work.FatouCoord.fatouCoordW f (1 - a))
        {w : ℂ | N < w.re} := fun w hw => (hdiff w hw).differentiableWithinAt
    have hre : ContinuousOn
        (fun w : ℂ => (Work.FatouCoord.fatouCoordW f (1 - a) w).re) {w : ℂ | N < w.re} :=
      Complex.continuous_re.comp_continuousOn hdiffOn.continuousOn
    have hmaps : MapsTo (fun s : ℝ => ((s : ℂ) + (t s : ℂ) * Complex.I)) (Ici s₀)
        {w : ℂ | N < w.re} := by
      intro s hs
      have hre' : ((s : ℂ) + (t s : ℂ) * Complex.I).re = s := by simp
      rw [Set.mem_ofPred_eq, hre']
      exact lt_of_lt_of_le hNs₀ hs
    have hcomp := hre.comp hline hmaps
    rw [hFdef]
    exact hcomp
  -- `F s₀` is below the target
  have hFs₀ : F s₀ < τ.re := by
    have hmem : N < ((s₀ : ℂ) + (t s₀ : ℂ) * Complex.I).re := by simpa using hNs₀
    have h1 := re_le_of_norm_sub (c := 1 - a) (N := N) (K := K) hcR hKnn
        (fun w hw => hbdd w (lt_trans hNbN hw)) hmem (by simpa using h1s₀)
    have hre₀ : ((s₀ : ℂ) + (t s₀ : ℂ) * Complex.I).re = s₀ := by simp
    rw [hre₀] at h1
    have h2 : s₀ + |(1 - a).im| * (Real.pi / 2) + K / s₀ < X := by
      rw [hXdef]; linarith
    rw [hFdef]
    linarith
  -- `F` grows at least linearly
  set q : ℝ := 1 - (1 / 2) / Real.sqrt (1 - (1 / 2 : ℝ) ^ 2) with hqdef
  have hqpos : 0 < q := by
    have hsqrt : (0 : ℝ) < Real.sqrt (1 - (1 / 2 : ℝ) ^ 2) := Real.sqrt_pos_of_pos (by norm_num)
    have hlt : (1 / 2 : ℝ) < Real.sqrt (1 - (1 / 2 : ℝ) ^ 2) := by
      have hsq : (Real.sqrt (1 - (1 / 2 : ℝ) ^ 2)) ^ 2 = 1 - (1 / 2 : ℝ) ^ 2 :=
        Real.sq_sqrt (by norm_num)
      nlinarith [Real.sqrt_nonneg (1 - (1 / 2 : ℝ) ^ 2)]
    rw [hqdef, sub_pos, div_lt_one hsqrt]
    exact hlt
  have hqne : q ≠ 0 := hqpos.ne'
  set s₁ : ℝ := s₀ + (τ.re - F s₀ + 1) / q with hs₁def
  have hs₁ge : s₀ ≤ s₁ := by
    rw [hs₁def]
    have h1 : 0 ≤ (τ.re - F s₀ + 1) / q := div_nonneg (by linarith) hqpos.le
    linarith
  have hFs₁ : τ.re < F s₁ := by
    have hgr : q * (s₁ - s₀) ≤ F s₁ - F s₀ := by
      rw [hFdef, hqdef]
      exact re_growth_of_pair (ψ := Work.FatouCoord.fatouCoordW f (1 - a)) (N := N) (C := 1 / 2)
        (by norm_num) hC1 hpair hNs₀ hs₁ge (t₀ := t s₀) (t₁ := t s₁)
        (by rw [ht s₀ (le_refl s₀), ht s₁ hs₁ge])
    have h2 : q * (s₁ - s₀) = τ.re - F s₀ + 1 := by
      rw [hs₁def, add_sub_cancel_left, ← mul_div_assoc, mul_div_cancel_left₀ _ hqne]
    rw [h2] at hgr
    linarith
  -- the intermediate value theorem produces the preimage
  obtain ⟨s, hs_mem, hsF⟩ :=
    intermediate_value_Icc hs₁ge (hFcont.mono (fun x hx => hx.1))
      (show τ.re ∈ Set.Icc (F s₀) (F s₁) from ⟨hFs₀.le, hFs₁.le⟩)
  refine ⟨(s : ℂ) + (t s : ℂ) * Complex.I, ?_, ?_⟩
  · have hre' : ((s : ℂ) + (t s : ℂ) * Complex.I).re = s := by simp
    rw [hre']
    exact lt_of_lt_of_le hMhs₀ hs_mem.1
  · have hsge : s₀ ≤ s := hs_mem.1
    have him : (Work.FatouCoord.fatouCoordW f (1 - a) ((s : ℂ) + (t s : ℂ) * Complex.I)).im
        = y := ht s hsge
    have hre : (Work.FatouCoord.fatouCoordW f (1 - a) ((s : ℂ) + (t s : ℂ) * Complex.I)).re
        = τ.re := by
      rw [hFdef] at hsF
      exact hsF
    refine Complex.ext hre ?_
    rw [him, hydef]

end

end Work.GATE2.PL
