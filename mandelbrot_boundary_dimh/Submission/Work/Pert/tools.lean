import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Pert.norm_le_periodic_halfplane2
import Submission.Work.Pert.norm_le_periodic_lowerHalfplane2
import Submission.Work.Parab.Setup
import Submission.Work.Parab.inversion.deriv_ne_zero_of_injOn

/-!
# PERT assembly tools

Small, reusable tools for the assembly of `PertData` (Shishikura §4.2, A.4).

* `exists_subset_of_forall_seq`: the "sequential ⟹ neighbourhood" pigeonhole.  `FatouContinuity`
  (A.2.1(iii)) is a statement about sequences `f_n → f₀`; the perturbation layer needs a
  *neighbourhood* statement (one `(L, δ₀)` working for every `f` near `f₀`).  If the conclusion
  is known for every sequence `(a n) ∈ B n` with `(B n)` the basic sets of the neighbourhood
  filter, then it holds on one of the `B N`.
* `eq_const_of_inv_of_tendsto`: a function that is invariant along a dynamics and has a limit at
  the attracting point is constant on the whole domain.  This is the engine of the identification
  of the *limit* Fatou coordinates `Φ_{±,0}` with the datum's coordinates `d.φ`, `d.Φ`
  (see `NOTES_pert2_findings.md` §7): both satisfy the same Abel equation, so their difference is
  invariant.
* `tau0_re`, `tau0_im`: `τ₀(z) = -1/z` in coordinates; these turn every statement about
  `τ₀ '' Qreg ...` into a statement about `Qreg ...`.
* `Qreg_subset_shift`: the basic monotonicity of Shishikura's regions under moving the two
  vertices apart.  (This is what makes the moving gates `Q_f^±` eventually contain every compact
  of a fixed limit region, and what allows enlarging a limit region.)
-/

namespace Work.Pert

open MandelDim Complex Set Filter MeasureTheory
open scoped Topology

noncomputable section

/-! ## Sequential ⟹ neighbourhood -/

/-- **Pigeonhole.**  If `B : ℕ → Set α` is a decreasing family of basic sets, and every sequence
`a` with `a n ∈ B n` has `g (a n) → x`, then one of the `B N` is already contained in
`g ⁻¹' ball x ε`.  (Suppose not: choose `a N ∈ B N` with `g (a N) ∉ ball x ε` and contradict the
hypothesis at that sequence.) -/
theorem exists_subset_of_forall_seq {α : Type*} {B : ℕ → Set α} {g : α → ℂ} {x : ℂ} {ε : ℝ}
    (h : ∀ a : ℕ → α, (∀ n, a n ∈ B n) → ∃ N, ∀ n, N ≤ n → g (a n) ∈ Metric.ball x ε) :
    ∃ N, ∀ a ∈ B N, g a ∈ Metric.ball x ε := by
  by_contra hc
  have hc' : ∀ N, ∃ a, a ∈ B N ∧ g a ∉ Metric.ball x ε := by
    intro N
    by_contra h
    exact hc ⟨N, fun a ha => by by_contra hga; exact h ⟨a, ha, hga⟩⟩
  choose a ha hga using hc'
  obtain ⟨N, hN⟩ := h a ha
  exact hga N (hN N le_rfl)

/-! ## Invariant functions with a limit at the attractor are constant -/

private lemma iterate_mem {α : Type*} {F : α → α} {U : Set α} (hF : MapsTo F U U) :
    ∀ n (z : α), z ∈ U → F^[n] z ∈ U := by
  intro n
  induction n with
  | zero => intro z hz; simpa using hz
  | succ n ih =>
    intro z hz
    rw [Function.iterate_succ_apply']
    exact hF (ih z hz)

/-- If `H` is invariant under `F` on `U`, the `F`-orbits of points of `U` converge to `z₀`, and
`H` has a limit `L` at `z₀` along `U`, then `H ≡ L` on `U`. -/
theorem eq_const_of_inv_of_tendsto {U : Set ℂ} {F H : ℂ → ℂ} {z₀ L : ℂ}
    (hF : MapsTo F U U) (hinv : ∀ z ∈ U, H (F z) = H z)
    (hconv : ∀ z ∈ U, Tendsto (fun n : ℕ => F^[n] z) atTop (𝓝 z₀))
    (hlim : Tendsto H (𝓝[U] z₀) (𝓝 L)) :
    ∀ z ∈ U, H z = L := by
  intro z hz
  have hiter : ∀ n : ℕ, H (F^[n] z) = H z := by
    intro n
    induction n with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ_apply', hinv _ (iterate_mem hF k z hz), ih]
  have hconvU : Tendsto (fun n : ℕ => F^[n] z) atTop (𝓝[U] z₀) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨hconv z hz, Eventually.of_forall fun n => iterate_mem hF n z hz⟩
  have h1 : Tendsto (fun n : ℕ => H (F^[n] z)) atTop (𝓝 L) := hlim.comp hconvU
  have h2 : Tendsto (fun n : ℕ => H (F^[n] z)) atTop (𝓝 (H z)) :=
    tendsto_const_nhds.congr' (Eventually.of_forall fun n => (hiter n).symm)
  exact tendsto_nhds_unique h2 h1

/-! ## `τ₀` in coordinates -/

theorem tau0_re (w : ℂ) : (MandelDim.tau0 w).re = -w.re / ‖w‖ ^ 2 := by
  have h : MandelDim.tau0 w = -(w⁻¹) := by
    simp only [MandelDim.tau0, div_eq_mul_inv, neg_mul, one_mul]
  rw [h, Complex.neg_re, Complex.inv_re, Complex.sq_norm, neg_div]

theorem tau0_im (w : ℂ) : (MandelDim.tau0 w).im = w.im / ‖w‖ ^ 2 := by
  have h : MandelDim.tau0 w = -(w⁻¹) := by
    simp only [MandelDim.tau0, div_eq_mul_inv, neg_mul, one_mul]
  rw [h, Complex.neg_im, Complex.inv_im, Complex.sq_norm, neg_div]
  ring

/-- `τ₀` is an involution on `ℂ ∖ {0}` (at `0` both sides give the junk value `0`). -/
theorem tau0_tau0 (w : ℂ) : MandelDim.tau0 (MandelDim.tau0 w) = w := by
  simp only [MandelDim.tau0, div_eq_mul_inv]
  rw [mul_inv, inv_neg, inv_one, inv_inv]
  ring

/-- The real part of `τ₀ w` has the sign opposite to the real part of `w`. -/
theorem tau0_re_sign {w : ℂ} (hw : w ≠ 0) : (MandelDim.tau0 w).re < 0 ↔ 0 < w.re := by
  have h2 : (0 : ℝ) < ‖w‖ ^ 2 := by
    have : 0 < ‖w‖ := norm_pos_iff.mpr hw
    positivity
  rw [tau0_re, neg_div, neg_lt_zero, div_pos_iff]
  constructor
  · rintro (⟨h, _⟩ | ⟨_, h'⟩)
    · exact h
    · exact absurd h2 (not_lt.mpr h'.le)
  · exact fun h => Or.inl ⟨h, h2⟩

/-! ## Monotonicity of Shishikura's regions -/

/-- Moving the left vertex to the left and the right vertex to the right enlarges `Qreg`. -/
theorem Qreg_subset_shift {a b : ℂ} {t : ℝ} (ht : 0 ≤ t) :
    MandelDim.Qreg (some a) (some b) ⊆ MandelDim.Qreg (some (a - t)) (some (b + t)) := by
  intro z hz
  simp only [MandelDim.Qreg, Set.mem_ofPred_eq, Option.mem_some_iff] at hz ⊢
  obtain ⟨h1, h2⟩ := hz
  constructor
  · rintro b₁ rfl
    have h : z - (a - (t : ℂ)) = (z - a) + (t : ℂ) := by ring
    rw [h, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, add_zero]
    linarith [h1 a rfl]
  · rintro b₁ rfl
    have h : z - (b + (t : ℂ)) = (z - b) - (t : ℂ) := by ring
    rw [h, Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, sub_zero]
    linarith [h2 b rfl]

/-! ## The parabolic basin lies in the domain of `f` -/

theorem ParabolicBasin.subset_dom {f : ℂ → ℂ} {D : Set ℂ} {z : ℂ}
    (h : z ∈ MandelDim.ParabolicBasin f D) : z ∈ D := by
  obtain ⟨U, hU, hmaps, _⟩ := h
  have hzU : z ∈ U := mem_of_mem_nhds hU
  have := hmaps 0 hzU
  simpa using this

/-! ## The datum's `E` is `1`-equivariant on `DE` -/

/-- `E (w+1) = E w + 1` (the T-equivariance of the datum's horn map), from the two Abel
equations.  Only `w ∈ d.DE` is needed: `w + 1` is automatically legal because `d.φ w ∈ D₀`. -/
theorem ParabData.E_add_one {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    {w : ℂ} (hw : w ∈ d.DE) : d.E (w + 1) = d.E w + 1 := by
  obtain ⟨hwφ, hwb⟩ := hw
  have hD0 : d.φ w ∈ D₀ := ParabolicBasin.subset_dom hwb
  have h1 : w + 1 ∈ d.Dφ := (d.succ_iff w hwφ).2 hD0
  show d.Φ (d.φ (w + 1)) = d.Φ (d.φ w) + 1
  rw [d.φ_abel w hwφ h1]
  exact d.Φ_abel (d.φ w) hwb

/-! ## The datum's `φ` has no critical point in the repelling sector -/

/-- On Shishikura's sector `QLeft ξ₀` (open, contained in `Dφ`, on which `φ` is injective) the
derivative of `d.φ` never vanishes. -/
theorem ParabData.deriv_phi_ne_zero {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    {w : ℂ} (hw : w ∈ MandelDim.QLeft d.ξ₀) : deriv d.φ w ≠ 0 :=
  Work.Parab.inversion.deriv_ne_zero_of_injOn (Work.Parab.isOpen_QLeft d.ξ₀)
    (d.φ_holo.mono d.Q_sub) d.φ_inj w hw

/-! ## The `τ₀`-image of a region is away from the repelling direction -/

/-- Inside `Qreg (some a) (some b)`, points with negative real part (``left'' of the vertex `a`,
which is assumed real) have imaginary part dominating the distance to `a`. -/
theorem Qreg_abs_im_gt {a b z : ℂ} (hz : z ∈ MandelDim.Qreg (some a) (some b))
    (ha : a.im = 0) (hzre : z.re < 0) (hare : 0 < a.re) :
    |z.re - a.re| < |z.im - a.im| := by
  simp only [MandelDim.Qreg, Set.mem_ofPred_eq, Option.mem_some_iff] at hz
  have h := hz.1 a rfl
  rw [Complex.sub_re, Complex.sub_im, ha, sub_zero] at h
  have hlt : z.re - a.re < 0 := by linarith
  have h2 : a.re - z.re < |z.im| := by linarith
  rw [show z.im - a.im = z.im by rw [ha, sub_zero], abs_of_neg hlt]
  linarith

/-- Consequently, for such points, `τ₀ z` lies outside the cone `|arg| < π/4` around the
*positive* real axis, i.e. `|Re (τ₀ z)| < |Im (τ₀ z)|`. -/
theorem tau0_abs_re_lt_abs_im_of_Qreg {a b z : ℂ} (hz : z ∈ MandelDim.Qreg (some a) (some b))
    (ha : a.im = 0) (hzre : z.re < 0) (hare : 0 < a.re) :
    |(MandelDim.tau0 z).re| < |(MandelDim.tau0 z).im| := by
  have h := Qreg_abs_im_gt hz ha hzre hare
  have him : |z.im - a.im| = |z.im| := by rw [ha, sub_zero]
  have hre : |z.re - a.re| = a.re - z.re := by
    rw [abs_of_neg (by linarith : z.re - a.re < 0)]
    ring
  rw [him, hre] at h
  have hkey : -z.re < |z.im| := by linarith
  have hz0 : z ≠ 0 := by
    intro h0
    rw [h0] at hzre
    simp at hzre
  have hpos : (0 : ℝ) < ‖z‖ ^ 2 := by
    have : 0 < ‖z‖ := norm_pos_iff.mpr hz0
    positivity
  rw [tau0_re, tau0_im, abs_div, abs_div, abs_neg]
  rw [abs_of_pos hpos]
  rw [abs_of_neg hzre]
  exact div_lt_div_of_pos_right hkey hpos

/-! ## Maximum modulus at the two ends, with periodicity only on the half-planes -/

/-- The hypothesis actually available in the PERT assembly: `D = R̃_f + 1/α - Ẽ_{f₀}` is
`1`-periodic only where the two maps are `T`-equivariant, i.e. on `{|Im| ≥ y}`; the maximum
modulus argument only ever needs the periodicity there.  We extend `D` by `0` off that set and
apply the global-periodicity lemmas `norm_le_periodic_halfplane2` / `..._lowerHalfplane2`. -/
theorem norm_le_periodic_ends_local (D : ℂ → ℂ) {y δ : ℝ} (hδ : 0 < δ) (hy : 0 < y)
    (hperU : ∀ w : ℂ, y ≤ w.im → D (w + 1) = D w)
    (hperL : ∀ w : ℂ, w.im ≤ -y → D (w + 1) = D w)
    (hdiffU : DifferentiableOn ℂ D {w : ℂ | y ≤ w.im})
    (hdiffL : DifferentiableOn ℂ D {w : ℂ | w.im ≤ -y})
    (hendU : ∃ L : ℂ, Filter.Tendsto D (Filter.comap Complex.im Filter.atTop) (nhds L))
    (hendL : ∃ L : ℂ, Filter.Tendsto D (Filter.comap Complex.im Filter.atBot) (nhds L))
    (hlineU : ∀ w : ℂ, w.im = y → ‖D w‖ < δ)
    (hlineL : ∀ w : ℂ, w.im = -y → ‖D w‖ < δ) :
    ∀ w : ℂ, y ≤ |w.im| → ‖D w‖ < δ := by
  classical
  set D' : ℂ → ℂ := fun w => if y ≤ |w.im| then D w else 0 with hD'def
  have hD'eq : ∀ w : ℂ, y ≤ |w.im| → D' w = D w := by
    intro w hw
    simp only [hD'def]
    rw [if_pos hw]
  have him1 : ∀ w : ℂ, (w + 1).im = w.im := fun w => by simp
  have hdisj : ∀ w : ℂ, y ≤ |w.im| → (y ≤ w.im ∨ w.im ≤ -y) := by
    intro w hw
    by_cases h : 0 ≤ w.im
    · exact Or.inl (by rwa [abs_of_nonneg h] at hw)
    · exact Or.inr (by rw [abs_of_neg (not_le.mp h)] at hw; linarith)
  have hper' : ∀ w : ℂ, D' (w + 1) = D' w := by
    intro w
    rw [hD'def]
    simp only [him1 w]
    by_cases h : y ≤ |w.im|
    · rw [if_pos h, if_pos h]
      rcases hdisj w h with hw | hw
      · exact hperU w hw
      · exact hperL w hw
    · rw [if_neg h, if_neg h]
  have hevU : D' =ᶠ[Filter.comap Complex.im Filter.atTop] D := by
    filter_upwards [Filter.mem_comap.mpr
      ⟨{x : ℝ | y ≤ x}, Filter.eventually_ge_atTop y, subset_rfl⟩] with w hw
    have hw' : y ≤ w.im := hw
    exact hD'eq w (by rw [abs_of_nonneg (le_trans (le_of_lt hy) hw')]; exact hw')
  have hevL : D' =ᶠ[Filter.comap Complex.im Filter.atBot] D := by
    filter_upwards [Filter.mem_comap.mpr
      ⟨{x : ℝ | x ≤ -y}, Filter.eventually_le_atBot (-y), subset_rfl⟩] with w hw
    have hw' : w.im ≤ -y := hw
    exact hD'eq w (by
      have h0 : w.im ≤ 0 := by linarith
      rw [abs_of_nonpos h0]; linarith)
  have hdiffU' : DifferentiableOn ℂ D' {w : ℂ | y ≤ w.im} := by
    refine hdiffU.congr fun w hw => ?_
    have hw' : y ≤ w.im := hw
    exact hD'eq w (by rw [abs_of_nonneg (le_trans (le_of_lt hy) hw')]; exact hw')
  have hdiffL' : DifferentiableOn ℂ D' {w : ℂ | w.im ≤ -y} := by
    refine hdiffL.congr fun w hw => ?_
    have hw' : w.im ≤ -y := hw
    have h0 : w.im ≤ 0 := by linarith
    exact hD'eq w (by rw [abs_of_nonpos h0]; linarith)
  have hendU' : ∃ L : ℂ, Filter.Tendsto D' (Filter.comap Complex.im Filter.atTop) (nhds L) := by
    obtain ⟨L, hL⟩ := hendU
    exact ⟨L, hL.congr' hevU.symm⟩
  have hendL' : ∃ L : ℂ, Filter.Tendsto D' (Filter.comap Complex.im Filter.atBot) (nhds L) := by
    obtain ⟨L, hL⟩ := hendL
    exact ⟨L, hL.congr' hevL.symm⟩
  have hlineU' : ∀ w : ℂ, w.im = y → ‖D' w‖ < δ := by
    intro w hw
    rw [hD'eq w (by rw [hw, abs_of_pos hy])]
    exact hlineU w hw
  have hlineL' : ∀ w : ℂ, w.im = -y → ‖D' w‖ < δ := by
    intro w hw
    rw [hD'eq w (by rw [hw, abs_neg, abs_of_pos hy])]
    exact hlineL w hw
  intro w hw
  by_cases hpos : 0 ≤ w.im
  · rw [abs_of_nonneg hpos] at hw
    have h := norm_le_periodic_halfplane2 D' hδ hper' hdiffU' hendU' hlineU' w hw
    rwa [hD'eq w (by rw [abs_of_nonneg hpos]; exact hw)] at h
  · have hneg : w.im < 0 := not_le.mp hpos
    have hw' : w.im ≤ -y := by
      rw [abs_of_neg hneg] at hw
      linarith [hw]
    have h := norm_le_periodic_lowerHalfplane2 D' hδ hper' hdiffL' hendL' hlineL' w hw'
    rwa [hD'eq w (by rw [abs_of_neg hneg]; linarith)] at h

/-! ## The mean over a period equals the end value -/

/-- For a `1`-periodic holomorphic function `P` with a limit `L` at the upper end (uniformly in
`Re`), the mean of `P` over one period at *any* height `y` equals `L`.  This is (A.4.4):
`c₊(f) - c₋(f) = ∫_{iη₀}^{1+iη₀}(Ẽ_f - id) → 0` reduces to `∫₀¹(Ẽ₀ - id)(x + iη₀)dx = 0`, the
`E_upper` normalisation of the datum's horn map. -/
theorem intervalIntegral_period_eq_of_tendsto {P : ℂ → ℂ} {L : ℂ} {y : ℝ}
    (hdiff : ∀ M : ℝ, y ≤ M → DifferentiableOn ℂ P {w : ℂ | y ≤ w.im ∧ w.im ≤ M})
    (hper : ∀ w : ℂ, P (w + 1) = P w)
    (hlim : Filter.Tendsto P (Filter.comap Complex.im Filter.atTop) (nhds L)) :
    ∫ x in (0 : ℝ)..1, P ((x : ℂ) + y * Complex.I) = L := by
  have hcoord : ∀ (M : ℝ) (x : ℝ),
      ((x : ℂ) + (y * Complex.I).im * Complex.I) = (x : ℂ) + y * Complex.I := by
    intro M x
    simp
  -- (1) the horizontal mean over a period is independent of the height
  have hmean : ∀ M : ℝ, y ≤ M →
      (∫ x in (0 : ℝ)..1, P ((x : ℂ) + y * Complex.I)) =
        ∫ x in (0 : ℝ)..1, P ((x : ℂ) + M * Complex.I) := by
    intro M hM
    have hrect := integral_boundary_rect_eq_zero_of_differentiableOn P (y * Complex.I)
      (1 + M * Complex.I) ?_
    · simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_one, mul_zero, zero_mul, add_zero, sub_zero,
        Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im, zero_add] at hrect
      have hcancel : (∫ t in y..M, P (((1 : ℝ) : ℂ) + t * Complex.I)) =
          ∫ t in y..M, P (((0 : ℝ) : ℂ) + t * Complex.I) := by
        apply intervalIntegral.integral_congr
        intro t _
        have h := hper (t * Complex.I)
        simpa [add_comm] using h
      rw [hcancel] at hrect
      have hzero : (∫ x in (0 : ℝ)..1, P ((x : ℂ) + y * Complex.I)) -
          (∫ x in (0 : ℝ)..1, P ((x : ℂ) + M * Complex.I)) = 0 := by
        simpa using hrect
      exact sub_eq_zero.mp hzero
    · refine (hdiff M hM).mono ?_
      intro w hw
      rw [mem_reProdIm] at hw
      simp only [Set.uIcc, Set.mem_Icc, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_one, mul_zero, zero_mul, add_zero,
        sub_zero, Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im, zero_add,
        min_eq_left hM, max_eq_right hM, min_eq_left (zero_le_one), max_eq_right (zero_le_one)]
        at hw
      exact ⟨hw.2.1, hw.2.2⟩
  -- (2) the mean tends to `L`
  have hlim' : Filter.Tendsto (fun M : ℝ => ∫ x in (0 : ℝ)..1, P ((x : ℂ) + M * Complex.I))
      Filter.atTop (nhds L) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨M₀, hM₀⟩ : ∃ M₀ : ℝ, ∀ w : ℂ, M₀ ≤ w.im → ‖P w - L‖ < ε / 2 := by
      have hball : Metric.ball L (ε / 2) ∈ nhds L := Metric.ball_mem_nhds L (by linarith)
      have hpre : {w : ℂ | ‖P w - L‖ < ε / 2} ∈ Filter.comap Complex.im Filter.atTop := by
        have h1 : P ⁻¹' Metric.ball L (ε / 2) ∈ Filter.comap Complex.im Filter.atTop :=
          Filter.mem_map.mp (hlim hball)
        have hset : P ⁻¹' Metric.ball L (ε / 2) = {w : ℂ | ‖P w - L‖ < ε / 2} := by
          ext w
          simp [Metric.mem_ball, dist_eq_norm]
        rwa [hset] at h1
      obtain ⟨t, ht, hsub⟩ := Filter.mem_comap.mp hpre
      obtain ⟨M₀, hM₀⟩ := Filter.mem_atTop_sets.mp ht
      exact ⟨M₀, fun w hw => hsub (hM₀ w.im hw)⟩
    refine ⟨max M₀ y, fun M hM => ?_⟩
    have hMy : y ≤ M := le_trans (le_max_right _ _) hM
    have hmap : Set.MapsTo (fun x : ℝ => (x : ℂ) + M * Complex.I) (Set.uIcc 0 1)
        {w : ℂ | y ≤ w.im ∧ w.im ≤ M} := by
      intro x hx
      simp only [Set.mem_ofPred_eq, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
        Complex.I_re, Complex.I_im, Complex.ofReal_re, mul_one, mul_zero, add_zero, zero_add]
      exact ⟨hMy, le_rfl⟩
    have hcont : ContinuousOn (fun x : ℝ => P ((x : ℂ) + M * Complex.I)) (Set.uIcc 0 1) :=
      ContinuousOn.comp (hdiff M hMy).continuousOn (by fun_prop) hmap
    have hInt : IntervalIntegrable (fun x : ℝ => P ((x : ℂ) + M * Complex.I)) volume 0 1 :=
      hcont.intervalIntegrable
    have hIntL : IntervalIntegrable (fun _ : ℝ => L) volume 0 1 :=
      continuousOn_const.intervalIntegrable
    have hsub_int : (∫ x in (0 : ℝ)..1, (P ((x : ℂ) + M * Complex.I) - L)) =
        (∫ x in (0 : ℝ)..1, P ((x : ℂ) + M * Complex.I)) - L := by
      rw [intervalIntegral.integral_sub hInt hIntL, intervalIntegral.integral_const]
      simp
    have hbound : ‖∫ x in (0 : ℝ)..1, (P ((x : ℂ) + M * Complex.I) - L)‖ ≤
        (ε / 2) * |1 - 0| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro x _
      have hx : M₀ ≤ ((x : ℂ) + M * Complex.I).im := by
        simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
          Complex.I_im, Complex.ofReal_re, mul_one, mul_zero, add_zero]
        linarith [le_trans (le_max_left M₀ y) hM]
      exact le_of_lt (hM₀ _ hx)
    rw [hsub_int] at hbound
    rw [dist_eq_norm]
    calc ‖(∫ x in (0 : ℝ)..1, P ((x : ℂ) + M * Complex.I)) - L‖ ≤ (ε / 2) * |1 - 0| := hbound
      _ = ε / 2 := by norm_num
      _ < ε := by linarith
  -- (3) conclude
  have hconst : (fun M : ℝ => ∫ x in (0 : ℝ)..1, P ((x : ℂ) + M * Complex.I)) =ᶠ[Filter.atTop]
      (fun _ : ℝ => ∫ x in (0 : ℝ)..1, P ((x : ℂ) + y * Complex.I)) :=
    Filter.eventually_atTop.mpr ⟨y, fun M hM => (hmean M hM).symm⟩
  have h2 : Filter.Tendsto (fun M : ℝ => ∫ x in (0 : ℝ)..1, P ((x : ℂ) + M * Complex.I))
      Filter.atTop (nhds (∫ x in (0 : ℝ)..1, P ((x : ℂ) + y * Complex.I))) :=
    tendsto_const_nhds.congr' hconst.symm
  exact tendsto_nhds_unique h2 hlim'

end

end Work.Pert
