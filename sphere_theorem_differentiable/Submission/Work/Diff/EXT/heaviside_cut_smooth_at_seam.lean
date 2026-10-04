import Mathlib
import Submission.Work.Diff.EXT.ufslice
import Submission.Work.Diff.EXT.norm_iteratedFDeriv_le_seamPartials

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option linter.unusedVariables false

open scoped Topology ContDiff
open Filter

namespace Work.Diff.EXT

universe u v

/-! ## The Heaviside cut and the seam-flatness predicate -/

/-- The Heaviside cut of `F` at the hyperplane `p.1 = T`:
`p ↦ if p.1 < T then F p else 0`. -/
noncomputable def seamCut {E : Type u} {Z : Type v} [Zero Z] (T : ℝ) (F : ℝ × E → Z) :
    ℝ × E → Z := fun p => if p.1 < T then F p else 0

lemma seamCut_of_lt {E : Type u} {Z : Type v} [Zero Z] {T : ℝ} {F : ℝ × E → Z} {p : ℝ × E}
    (h : p.1 < T) : seamCut T F p = F p := by simp [seamCut, h]

lemma seamCut_of_ge {E : Type u} {Z : Type v} [Zero Z] {T : ℝ} {F : ℝ × E → Z} {p : ℝ × E}
    (h : ¬ p.1 < T) : seamCut T F p = 0 := by simp [seamCut, h]

/-- **Pointwise seam flatness.**  For every seam point `(T,y)` with `y` in the ball of radius `ρ`
around `y₀`, the `j`-th iterated Fréchet derivative of `F` is arbitrarily small on a left
neighbourhood of `(T,y)`, restricted to the ball of radius `ρ` around `y₀` (where `F` is known to
be smooth). -/
def SeamFlatPt {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Z : Type v} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (T : ℝ) (y₀ : E) (ρ : ℝ) (F : ℝ × E → Z) (j : ℕ) : Prop :=
  ∀ y ∈ Metric.ball y₀ ρ, ∀ ε > 0, ∃ δ > 0, ∀ q : ℝ × E, q.1 < T → ‖q.2 - y₀‖ < ρ →
    |q.1 - T| < δ → ‖q.2 - y‖ < δ → ‖iteratedFDeriv ℝ j F q‖ < ε

lemma mem_ball_iff_norm {E : Type u} [SeminormedAddCommGroup E] {y y₀ : E} {ρ : ℝ} :
    y ∈ Metric.ball y₀ ρ ↔ ‖y - y₀‖ < ρ := by
  rw [Metric.mem_ball, dist_eq_norm]

/-! ## Two elementary facts about the product `ℝ × E` -/

lemma norm_snd_le {E : Type u} [SeminormedAddCommGroup E] (p : ℝ × E) :
    ‖p.2‖ ≤ ‖p‖ := by
  rw [Prod.norm_def]; exact le_max_right _ _

lemma norm_fst_le {E : Type u} [SeminormedAddCommGroup E] (p : ℝ × E) :
    ‖p.1‖ ≤ ‖p‖ := by
  rw [Prod.norm_def]; exact le_max_left _ _

/-! ## The one-dimensional mean value bound -/

/-- One-dimensional mean-value bound: if `g` is differentiable on `[t,T)` with `‖g'‖ ≤ ε` there
and `g → 0` at `T` from the left, then `‖g t‖ ≤ ε * (T - t)`. -/
private theorem seam_rate {Z : Type v} [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] {g g' : ℝ → Z} {t T ε : ℝ} (hε : 0 ≤ ε) (ht : t < T)
    (hderiv : ∀ s ∈ Set.Ico t T, HasDerivAt g (g' s) s)
    (hbound : ∀ s ∈ Set.Ico t T, ‖g' s‖ ≤ ε)
    (hlim : Tendsto g (nhdsWithin T (Set.Iio T)) (nhds 0)) :
    ‖g t‖ ≤ ε * (T - t) := by
  have key : ∀ s ∈ Set.Ioo t T, ‖g t - g s‖ ≤ ε * (T - t) := by
    intro s hs
    have hsub : Set.Icc t s ⊆ Set.Ico t T := fun x hx => ⟨hx.1, lt_of_le_of_lt hx.2 hs.2⟩
    have h1 : ∀ x ∈ Set.Icc t s, HasDerivWithinAt g (g' x) (Set.Icc t s) x :=
      fun x hx => (hderiv x (hsub hx)).hasDerivWithinAt
    have h2 : ∀ x ∈ Set.Ico t s, ‖g' x‖ ≤ ε :=
      fun x hx => hbound x (hsub ⟨hx.1, le_of_lt hx.2⟩)
    have h3 := norm_image_sub_le_of_norm_deriv_le_segment' h1 h2 s
      (Set.right_mem_Icc.mpr hs.1.le)
    rw [norm_sub_rev] at h3
    exact le_trans h3 (mul_le_mul_of_nonneg_left (by linarith [hs.2]) hε)
  have hlim2 : Tendsto (fun s => ‖g t - g s‖) (nhdsWithin T (Set.Iio T)) (nhds ‖g t‖) := by
    have h1 : Tendsto (fun s => g t - g s) (nhdsWithin T (Set.Iio T)) (nhds (g t - 0)) :=
      hlim.const_sub (g t)
    have h2 := (continuous_norm.tendsto (g t - 0)).comp h1
    simpa [Function.comp_def] using h2
  refine le_of_tendsto hlim2 ?_
  have hmem : Set.Ioo t T ∈ nhdsWithin T (Set.Iio T) :=
    Filter.mem_inf_of_inter (IsOpen.mem_nhds isOpen_Ioi ht)
      (Filter.mem_principal.mpr subset_rfl) (fun x hx => ⟨hx.1, hx.2⟩)
  filter_upwards [hmem] with s hs
  exact key s hs

/-! ## The bridge: jets bounded by the mixed partials in the seam ordering -/

/-- **Bridge lemma** (proved in `Work.Diff.EXT.norm_iteratedFDeriv_le_seamPartials`): the norm of
the `j`-th jet of a smooth function is bounded by the sum of the norms of the mixed partials
`∂_y^{j-k} ∂_t^k` (`j-k` space derivatives outermost, `k` time derivatives innermost).  This is the
only place where the mixed partials entering the hypothesis of the main theorem are connected with
the full jet. -/
private theorem seamBridge {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Z : Type v} [NormedAddCommGroup Z] [NormedSpace ℝ Z] (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (F : ℝ × E → Z) (p : ℝ × E), ContDiffAt ℝ (⊤ : ℕ∞) F p →
      ‖iteratedFDeriv ℝ j F p‖ ≤ C * ∑ k ∈ Finset.range (j + 1),
        ‖iteratedFDeriv ℝ (j - k) (fun y' : E => iteratedDeriv k (fun t : ℝ => F (t, y')) p.1)
          p.2‖ :=
  norm_iteratedFDeriv_le_seamPartials (E := E) (Z := Z) j

/-! ## Derivative of the cut at a seam point -/

/-- The derivative of the time slice is the Fréchet derivative applied to `(1,0)`. -/
private lemma deriv_slice_eq {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Z : Type v} [NormedAddCommGroup Z] [NormedSpace ℝ Z] {F : ℝ × E → Z} {s : ℝ} {x : E}
    (h : DifferentiableAt ℝ F (s, x)) :
    deriv (fun r : ℝ => F (r, x)) s = fderiv ℝ F (s, x) (1, 0) := by
  have h1 : fderiv ℝ (fun r : ℝ => F (r, x)) s
      = (fderiv ℝ F (s, x)).comp (ContinuousLinearMap.inl ℝ ℝ E) := by
    have h2 : HasFDerivAt (fun r : ℝ => F (r, x))
        ((fderiv ℝ F (s, x)).comp (ContinuousLinearMap.inl ℝ ℝ E)) s :=
      (h.hasFDerivAt).comp s (hasFDerivAt_prodMk_left s x)
    exact h2.fderiv
  have h3 := fderiv_apply_one_eq_deriv (𝕜 := ℝ) (f := fun r : ℝ => F (r, x)) (x := s)
  rw [h1] at h3
  simpa using h3.symm

/-- **The cut has derivative `0` at every seam point of the ball.** -/
private theorem seamCut_hasFDerivAt {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Z : Type v} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {T : ℝ} {y₀ : E} {ρ : ℝ} {F : ℝ × E → Z}
    (hsm : ∀ p : ℝ × E, p.1 < T → ‖p.2 - y₀‖ < ρ → ContDiffAt ℝ (⊤ : ℕ∞) F p)
    (h0 : SeamFlatPt T y₀ ρ F 0) (h1 : SeamFlatPt T y₀ ρ F 1) :
    ∀ y : E, ‖y - y₀‖ < ρ → HasFDerivAt (seamCut T F) (0 : (ℝ × E) →L[ℝ] Z) (T, y) := by
  intro y hy
  have hyball : y ∈ Metric.ball y₀ ρ := mem_ball_iff_norm.mpr hy
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro c hc
  obtain ⟨r1, hr1pos, hr1⟩ := h1 y hyball c hc
  set R : ℝ := min r1 ((ρ - ‖y - y₀‖) / 2) with hR
  have hRpos : 0 < R := lt_min hr1pos (by linarith)
  have hRle1 : R ≤ r1 := min_le_left _ _
  have hRle2 : R ≤ ρ - ‖y - y₀‖ := le_trans (min_le_right _ _) (by linarith)
  refine Filter.mem_of_superset (Metric.ball_mem_nhds (0 : ℝ × E) hRpos) ?_
  intro h hh
  rw [Metric.mem_ball, dist_zero_right] at hh
  show ‖seamCut T F ((T, y) + h) - seamCut T F (T, y) - (0 : (ℝ × E) →L[ℝ] Z) h‖ ≤ c * ‖h‖
  have hnorm1 : ‖h.1‖ < r1 := by
    rw [Real.norm_eq_abs]
    exact lt_of_le_of_lt (by simpa using norm_fst_le h) (lt_of_lt_of_le hh hRle1)
  have hnorm2 : ‖h.2‖ < r1 := lt_of_le_of_lt (norm_snd_le h) (lt_of_lt_of_le hh hRle1)
  have hsmall : ‖(y + h.2) - y₀‖ < ρ := by
    have h4 : ‖(y + h.2) - y₀‖ ≤ ‖h.2‖ + ‖y - y₀‖ := by
      rw [show y + h.2 - y₀ = h.2 + (y - y₀) from by abel]
      exact norm_add_le _ _
    have h2lt : ‖h.2‖ < ρ - ‖y - y₀‖ :=
      lt_of_le_of_lt (norm_snd_le h) (lt_of_lt_of_le hh hRle2)
    linarith
  have hsy : ‖(y + h.2) - y‖ < r1 := by
    rw [add_sub_cancel_left]
    exact hnorm2
  rw [show seamCut T F (T, y) = (0 : Z) from seamCut_of_ge (not_lt.mpr le_rfl)]
  by_cases hcase : T + h.1 < T
  · rw [seamCut_of_lt (show ((T, y) + h).1 < T from hcase),
      show ((0 : (ℝ × E) →L[ℝ] Z) h) = (0 : Z) from rfl, sub_zero, sub_zero]
    have hderiv : ∀ s ∈ Set.Ico (T + h.1) T,
        HasDerivAt (fun r : ℝ => F (r, y + h.2)) (fderiv ℝ F (s, y + h.2) (1, 0)) s := by
      intro s hs
      have hsT : s < T := hs.2
      have hdiff : DifferentiableAt ℝ F (s, y + h.2) :=
        ((hsm (s, y + h.2) hsT hsmall).differentiableAt (by simp))
      have hslice : HasFDerivAt (fun r : ℝ => F (r, y + h.2))
          ((fderiv ℝ F (s, y + h.2)).comp (ContinuousLinearMap.inl ℝ ℝ E)) s :=
        (hdiff.hasFDerivAt).comp s (hasFDerivAt_prodMk_left s (y + h.2))
      simpa using hslice.hasDerivAt
    have hbound : ∀ s ∈ Set.Ico (T + h.1) T, ‖fderiv ℝ F (s, y + h.2) (1, 0)‖ ≤ c := by
      intro s hs
      have hsT : s < T := hs.2
      have hans : |s - T| < r1 := by
        have hle : |s - T| ≤ |T + h.1 - T| := by
          rw [abs_of_nonpos (by linarith [hs.1, hsT] : s - T ≤ 0),
            abs_of_nonpos (by linarith [hcase] : T + h.1 - T ≤ 0)]
          linarith [hs.1]
        have hp1T : |T + h.1 - T| < r1 := by
          rw [show T + h.1 - T = h.1 from by abel]
          simpa [Real.norm_eq_abs] using hnorm1
        linarith
      have hb := hr1 (s, y + h.2) hsT hsmall hans hsy
      have hb' : ‖fderiv ℝ F (s, y + h.2)‖ < c := by simpa using hb
      calc ‖fderiv ℝ F (s, y + h.2) (1, 0)‖ ≤ ‖fderiv ℝ F (s, y + h.2)‖ * ‖((1 : ℝ), (0 : E))‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ = ‖fderiv ℝ F (s, y + h.2)‖ := by simp [Prod.norm_def]
        _ ≤ c := le_of_lt hb'
    have hlim : Tendsto (fun r : ℝ => F (r, y + h.2)) (nhdsWithin T (Set.Iio T)) (nhds 0) := by
      rw [Metric.tendsto_nhds]
      intro e he
      obtain ⟨r0, hr0pos, hr0⟩ := h0 (y + h.2) (mem_ball_iff_norm.mpr hsmall) e he
      have hmem : Set.Ioo (T - r0) T ∈ nhdsWithin T (Set.Iio T) :=
        Filter.mem_inf_of_inter (IsOpen.mem_nhds isOpen_Ioi (sub_lt_self T hr0pos))
          (Filter.mem_principal.mpr subset_rfl) (fun x hx => ⟨hx.1, hx.2⟩)
      refine Filter.mem_of_superset hmem (fun s hs => ?_)
      have hs1 : |s - T| < r0 := by
        rw [abs_lt]
        exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
      have hsT : s < T := hs.2
      have hb := hr0 (s, y + h.2) hsT hsmall hs1 (by simpa using hr0pos)
      simpa [dist_eq_norm, norm_iteratedFDeriv_zero] using hb
    have hrate := seam_rate (le_of_lt hc) hcase hderiv hbound hlim
    have hle : T - (T + h.1) ≤ ‖h‖ := by
      have hT : T - (T + h.1) = -h.1 := by ring
      have hneg : h.1 < 0 := by linarith [hcase]
      have hnorm : ‖h.1‖ = -h.1 := by rw [Real.norm_eq_abs, abs_of_neg hneg]
      rw [hT, ← hnorm]
      exact norm_fst_le h
    calc ‖F ((T, y) + h)‖ = ‖(fun r : ℝ => F (r, y + h.2)) (T + h.1)‖ := rfl
      _ ≤ c * (T - (T + h.1)) := hrate
      _ ≤ c * ‖h‖ := mul_le_mul_of_nonneg_left hle (le_of_lt hc)
  · rw [seamCut_of_ge (show ¬ ((T, y) + h).1 < T from hcase)]
    simp only [sub_zero, zero_apply, norm_zero]
    exact mul_nonneg (le_of_lt hc) (norm_nonneg h)

/-! ## Continuity of the cut on the ball -/

private theorem seamCut_continuousOn {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Z : Type v} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {T : ℝ} {y₀ : E} {ρ : ℝ} {F : ℝ × E → Z}
    (hsm : ∀ p : ℝ × E, p.1 < T → ‖p.2 - y₀‖ < ρ → ContDiffAt ℝ (⊤ : ℕ∞) F p)
    (h0 : SeamFlatPt T y₀ ρ F 0) (h1 : SeamFlatPt T y₀ ρ F 1) :
    ContinuousOn (seamCut T F) (Metric.ball (T, y₀) ρ) := by
  intro z hz
  have hzρ : ‖z.2 - y₀‖ < ρ := by
    have h1 : dist z (T, y₀) < ρ := Metric.mem_ball.mp hz
    rw [dist_eq_norm] at h1
    exact lt_of_le_of_lt (norm_snd_le (z - (T, y₀))) h1
  rcases lt_trichotomy z.1 T with hlt | heq | hgt
  · have hmem : {p : ℝ × E | p.1 < T} ∈ 𝓝 z :=
      (isOpen_lt continuous_fst continuous_const).mem_nhds hlt
    have heq1 : seamCut T F =ᶠ[𝓝 z] F := by
      filter_upwards [hmem] with p hp
      exact seamCut_of_lt hp
    have hcont : ContinuousAt (seamCut T F) z :=
      (hsm z hlt hzρ).continuousAt.congr_of_eventuallyEq heq1
    exact hcont.continuousWithinAt
  · have hz' : z = (T, z.2) := Prod.ext heq rfl
    rw [hz']
    exact ((seamCut_hasFDerivAt hsm h0 h1 z.2 hzρ).continuousAt).continuousWithinAt
  · have hmem : {p : ℝ × E | T < p.1} ∈ 𝓝 z :=
      (isOpen_lt continuous_const continuous_fst).mem_nhds hgt
    have heq1 : seamCut T F =ᶠ[𝓝 z] (fun _ : ℝ × E => (0 : Z)) := by
      filter_upwards [hmem] with p hp
      exact seamCut_of_ge (not_lt.mpr hp.le)
    have hcont : ContinuousAt (seamCut T F) z :=
      (continuousAt_const).congr_of_eventuallyEq heq1
    exact hcont.continuousWithinAt

/-! ## The inductive step -/

/-- **The inductive step.**  From the statement at order `n` for all functions (the hypothesis
`ih`) one deduces the statement at order `n+1` for a given `F`, using that `fderiv ℝ F` again
satisfies the same hypotheses, with the levels shifted by one. -/
private theorem seamCut_finish {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Z : Type v} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {T : ℝ} {y₀ : E} {ρ : ℝ} (n : ℕ) (F : ℝ × E → Z)
    (hsm : ∀ p : ℝ × E, p.1 < T → ‖p.2 - y₀‖ < ρ → ContDiffAt ℝ (⊤ : ℕ∞) F p)
    (h0 : SeamFlatPt T y₀ ρ F 0) (h1 : SeamFlatPt T y₀ ρ F 1)
    (hrec : ∃ δ', 0 < δ' ∧ δ' ≤ ρ ∧
      ContDiffOn ℝ (n : ℕ∞) (seamCut T (fderiv ℝ F)) (Metric.ball (T, y₀) δ') ∧
      (∀ y : E, ‖y - y₀‖ < δ' →
        HasFDerivAt (seamCut T (fderiv ℝ F))
          (0 : (ℝ × E) →L[ℝ] ((ℝ × E) →L[ℝ] Z)) (T, y))) :
    ∃ δ, 0 < δ ∧ δ ≤ ρ ∧
      ContDiffOn ℝ ((n + 1 : ℕ) : ℕ∞) (seamCut T F) (Metric.ball (T, y₀) δ) ∧
      (∀ y : E, ‖y - y₀‖ < δ →
        HasFDerivAt (seamCut T F) (0 : (ℝ × E) →L[ℝ] Z) (T, y)) := by
  obtain ⟨δ', hδ'pos, hδ'le, hcont', -⟩ := hrec
  have hderiv : ∀ y : E, ‖y - y₀‖ < δ' →
      HasFDerivAt (seamCut T F) (0 : (ℝ × E) →L[ℝ] Z) (T, y) :=
    fun y hy => seamCut_hasFDerivAt hsm h0 h1 y (lt_of_lt_of_le hy hδ'le)
  have hzsnd : ∀ z : ℝ × E, z ∈ Metric.ball (T, y₀) δ' → ‖z.2 - y₀‖ < δ' := by
    intro z hz
    have h1 : dist z (T, y₀) < δ' := Metric.mem_ball.mp hz
    rw [dist_eq_norm] at h1
    exact lt_of_le_of_lt (norm_snd_le (z - (T, y₀))) h1
  have hzρ : ∀ z : ℝ × E, z ∈ Metric.ball (T, y₀) δ' → ‖z.2 - y₀‖ < ρ :=
    fun z hz => lt_of_lt_of_le (hzsnd z hz) hδ'le
  have hident : ∀ z ∈ Metric.ball (T, y₀) δ', fderiv ℝ (seamCut T F) z =
      seamCut T (fderiv ℝ F) z := by
    intro z hz
    rcases lt_trichotomy z.1 T with hlt | heq | hgt
    · have hmem : {p : ℝ × E | p.1 < T} ∈ 𝓝 z :=
        (isOpen_lt continuous_fst continuous_const).mem_nhds hlt
      have heq1 : seamCut T F =ᶠ[𝓝 z] F := by
        filter_upwards [hmem] with p hp
        exact seamCut_of_lt hp
      rw [heq1.fderiv_eq, seamCut_of_lt hlt]
    · have hzs : ‖z.2 - y₀‖ < δ' := hzsnd z hz
      have h1 : fderiv ℝ (seamCut T F) (T, z.2) = (0 : (ℝ × E) →L[ℝ] Z) := (hderiv z.2 hzs).fderiv
      have h2 : seamCut T (fderiv ℝ F) (T, z.2) = 0 := seamCut_of_ge (not_lt.mpr le_rfl)
      have hz' : z = (T, z.2) := Prod.ext heq rfl
      rw [hz', h1, h2]
    · have hmem : {p : ℝ × E | T < p.1} ∈ 𝓝 z :=
        (isOpen_lt continuous_const continuous_fst).mem_nhds hgt
      have heq1 : seamCut T F =ᶠ[𝓝 z] (fun _ : ℝ × E => (0 : Z)) := by
        filter_upwards [hmem] with p hp
        exact seamCut_of_ge (not_lt.mpr hp.le)
      rw [heq1.fderiv_eq, seamCut_of_ge (not_lt.mpr hgt.le)]
      simp
  have hcont_fderiv : ContDiffOn ℝ (n : ℕ∞) (fderiv ℝ (seamCut T F)) (Metric.ball (T, y₀) δ') :=
    hcont'.congr hident
  have hdiff : DifferentiableOn ℝ (seamCut T F) (Metric.ball (T, y₀) δ') := by
    intro z hz
    rcases lt_trichotomy z.1 T with hlt | heq | hgt
    · have hmem : {p : ℝ × E | p.1 < T} ∈ 𝓝 z :=
        (isOpen_lt continuous_fst continuous_const).mem_nhds hlt
      have heq1 : seamCut T F =ᶠ[𝓝 z] F := by
        filter_upwards [hmem] with p hp
        exact seamCut_of_lt hp
      exact (((hsm z hlt (hzρ z hz)).differentiableAt (by simp)).congr_of_eventuallyEq
        heq1).differentiableWithinAt
    · have hzs : ‖z.2 - y₀‖ < δ' := hzsnd z hz
      rw [show z = (T, z.2) from Prod.ext heq rfl]
      exact ((hderiv z.2 hzs).differentiableAt).differentiableWithinAt
    · have hmem : {p : ℝ × E | T < p.1} ∈ 𝓝 z :=
        (isOpen_lt continuous_const continuous_fst).mem_nhds hgt
      have heq1 : seamCut T F =ᶠ[𝓝 z] (fun _ : ℝ × E => (0 : Z)) := by
        filter_upwards [hmem] with p hp
        exact seamCut_of_ge (not_lt.mpr hp.le)
      exact ((differentiableAt_const (c := (0 : Z))).congr_of_eventuallyEq
        heq1).differentiableWithinAt
  have hstep := (contDiffOn_succ_iff_fderiv_of_isOpen (n := (n : ℕ∞)) Metric.isOpen_ball).mpr
    ⟨hdiff, (fun h => absurd h (by simp)), hcont_fderiv⟩
  exact ⟨δ', hδ'pos, hδ'le, hstep, hderiv⟩

/-- The shifted flatness hypotheses for `fderiv ℝ F`. -/
private theorem seamFlatPt_fderiv {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Z : Type v} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {T : ℝ} {y₀ : E} {ρ : ℝ} {F : ℝ × E → Z}
    (hsm : ∀ p : ℝ × E, p.1 < T → ‖p.2 - y₀‖ < ρ → ContDiffAt ℝ (⊤ : ℕ∞) F p)
    {n : ℕ} (hflat : ∀ j ≤ n + 2, SeamFlatPt T y₀ ρ F j) :
    (∀ p : ℝ × E, p.1 < T → ‖p.2 - y₀‖ < ρ → ContDiffAt ℝ (⊤ : ℕ∞) (fderiv ℝ F) p) ∧
      (∀ j ≤ n + 1, SeamFlatPt T y₀ ρ (fderiv ℝ F) j) :=
  ⟨fun p hp1 hp2 => (hsm p hp1 hp2).fderiv_right (by simp),
    fun j hj y hy ε hε => by
      obtain ⟨δ, hδ, hb⟩ := hflat (j + 1) (by omega) y hy ε hε
      exact ⟨δ, hδ, fun q hq1 hq2 hq3 hq4 => by
        simpa [norm_iteratedFDeriv_fderiv] using hb q hq1 hq2 hq3 hq4⟩⟩

/-- The induction, in the universe-stable form (the target lives in the universe of the CLM tower
over the domain). -/
private theorem seamCut_contDiffOn_aux_stable {E : Type u} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {T : ℝ} {y₀ : E} {ρ : ℝ} (hρ : 0 < ρ) (n : ℕ) :
    ∀ (Z : Type (max u v)) [NormedAddCommGroup Z] [NormedSpace ℝ Z] (F : ℝ × E → Z),
      (∀ p : ℝ × E, p.1 < T → ‖p.2 - y₀‖ < ρ → ContDiffAt ℝ (⊤ : ℕ∞) F p) →
      (∀ j ≤ n + 1, SeamFlatPt T y₀ ρ F j) →
      ∃ δ, 0 < δ ∧ δ ≤ ρ ∧ ContDiffOn ℝ (n : ℕ∞) (seamCut T F) (Metric.ball (T, y₀) δ) ∧
        (∀ y : E, ‖y - y₀‖ < δ →
          HasFDerivAt (seamCut T F) (0 : (ℝ × E) →L[ℝ] Z) (T, y)) := by
  induction n with
  | zero =>
      intro Z instZ instZ2 F hsm hflat
      exact ⟨ρ, hρ, le_rfl,
        (contDiffOn_zero (𝕜 := ℝ) (f := seamCut T F) (s := Metric.ball (T, y₀) ρ)).mpr
          (seamCut_continuousOn hsm (hflat 0 (by omega)) (hflat 1 (by omega))),
        seamCut_hasFDerivAt hsm (hflat 0 (by omega)) (hflat 1 (by omega))⟩
  | succ n ih =>
      intro Z instZ instZ2 F hsm hflat
      obtain ⟨hsm', hflat'⟩ := seamFlatPt_fderiv hsm hflat
      exact seamCut_finish n F hsm (hflat 0 (by omega)) (hflat 1 (by omega))
        (ih ((ℝ × E) →L[ℝ] Z) (fderiv ℝ F) hsm' hflat')

/-- The induction with the target in an arbitrary universe `v`. -/
private theorem seamCut_contDiffOn_aux {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {T : ℝ} {y₀ : E} {ρ : ℝ} (hρ : 0 < ρ) (n : ℕ) :
    ∀ (Z : Type v) [NormedAddCommGroup Z] [NormedSpace ℝ Z] (F : ℝ × E → Z),
      (∀ p : ℝ × E, p.1 < T → ‖p.2 - y₀‖ < ρ → ContDiffAt ℝ (⊤ : ℕ∞) F p) →
      (∀ j ≤ n + 1, SeamFlatPt T y₀ ρ F j) →
      ∃ δ, 0 < δ ∧ δ ≤ ρ ∧ ContDiffOn ℝ (n : ℕ∞) (seamCut T F) (Metric.ball (T, y₀) δ) ∧
        (∀ y : E, ‖y - y₀‖ < δ →
          HasFDerivAt (seamCut T F) (0 : (ℝ × E) →L[ℝ] Z) (T, y)) := by
  induction n with
  | zero =>
      intro Z instZ instZ2 F hsm hflat
      exact ⟨ρ, hρ, le_rfl,
        (contDiffOn_zero (𝕜 := ℝ) (f := seamCut T F) (s := Metric.ball (T, y₀) ρ)).mpr
          (seamCut_continuousOn hsm (hflat 0 (by omega)) (hflat 1 (by omega))),
        seamCut_hasFDerivAt hsm (hflat 0 (by omega)) (hflat 1 (by omega))⟩
  | succ n _ih =>
      intro Z instZ instZ2 F hsm hflat
      obtain ⟨hsm', hflat'⟩ := seamFlatPt_fderiv hsm hflat
      exact seamCut_finish n F hsm (hflat 0 (by omega)) (hflat 1 (by omega))
        (seamCut_contDiffOn_aux_stable.{u, v} (E := E) hρ n ((ℝ × E) →L[ℝ] Z)
          (fderiv ℝ F) hsm' hflat')

/-! ## From the mixed partials to the flatness of the jets -/

/-- The pointwise jet flatness of `G` follows from the hypothesis on the mixed partials, via the
bridge lemma. -/
private theorem seamFlatPt_of_mixed {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Z : Type v} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {T : ℝ} {U : Set E} {G : ℝ × E → Z} {y₀ : E} {ρ : ℝ}
    (hρU : Metric.ball y₀ ρ ⊆ U)
    (hG : ContDiffOn ℝ (⊤ : ℕ∞) G ({p : ℝ × E | p.1 < T} ∩ (Set.univ ×ˢ U)))
    (h : ∀ k m : ℕ, ∀ y ∈ U, Tendsto (fun p : ℝ × E =>
          iteratedFDeriv ℝ m (fun y' : E => iteratedDeriv k (fun s : ℝ => G (s, y')) p.1) p.2)
        (nhdsWithin (T, y) ({p : ℝ × E | p.1 < T} ∩ (Set.univ ×ˢ U))) (nhds 0))
    (j : ℕ) : SeamFlatPt T y₀ ρ G j := by
  intro y hy ε hε
  obtain ⟨C, _, hC⟩ := seamBridge (E := E) (Z := Z) j
  set A : Set (ℝ × E) := {p : ℝ × E | p.1 < T} ∩ (Set.univ ×ˢ Metric.ball y₀ ρ) with hA
  have hAopen : IsOpen A :=
    (isOpen_lt continuous_fst continuous_const).inter (isOpen_univ.prod Metric.isOpen_ball)
  have hAsub : A ⊆ {p : ℝ × E | p.1 < T} ∩ (Set.univ ×ˢ U) :=
    fun p hp => ⟨hp.1, trivial, hρU hp.2.2⟩
  have hG' : ContDiffOn ℝ (⊤ : ℕ∞) G A := hG.mono hAsub
  have hlim : ∀ k ∈ Finset.range (j + 1), Tendsto (fun p : ℝ × E => ‖iteratedFDeriv ℝ (j - k)
        (fun y' : E => iteratedDeriv k (fun s : ℝ => G (s, y')) p.1) p.2‖)
      (nhdsWithin (T, y) A) (nhds 0) := by
    intro k _
    have hyU : y ∈ U := hρU hy
    have h1 : Tendsto (fun p : ℝ × E => iteratedFDeriv ℝ (j - k)
        (fun y' : E => iteratedDeriv k (fun s : ℝ => G (s, y')) p.1) p.2)
        (nhdsWithin (T, y) ({p : ℝ × E | p.1 < T} ∩ (Set.univ ×ˢ U))) (nhds 0) :=
      h k (j - k) y hyU
    have h2 : nhdsWithin (T, y) A ≤ nhdsWithin (T, y)
        ({p : ℝ × E | p.1 < T} ∩ (Set.univ ×ˢ U)) := nhdsWithin_mono _ hAsub
    exact tendsto_zero_iff_norm_tendsto_zero.mp (h1.mono_left h2)
  have hsum : Tendsto (fun p : ℝ × E => C * ∑ k ∈ Finset.range (j + 1), ‖iteratedFDeriv ℝ (j - k)
        (fun y' : E => iteratedDeriv k (fun s : ℝ => G (s, y')) p.1) p.2‖)
      (nhdsWithin (T, y) A) (nhds 0) := by
    have h3 := tendsto_finsetSum (Finset.range (j + 1)) hlim
    have h3' : Tendsto (fun p : ℝ × E => ∑ k ∈ Finset.range (j + 1), ‖iteratedFDeriv ℝ (j - k)
        (fun y' : E => iteratedDeriv k (fun s : ℝ => G (s, y')) p.1) p.2‖)
        (nhdsWithin (T, y) A) (nhds 0) := by simpa using h3
    simpa using h3'.const_mul C
  have hnormlim : Tendsto (fun p : ℝ × E => ‖iteratedFDeriv ℝ j G p‖)
      (nhdsWithin (T, y) A) (nhds 0) := by
    refine squeeze_zero' ?_ ?_ hsum
    · exact Filter.Eventually.of_forall (fun p => norm_nonneg _)
    · filter_upwards [self_mem_nhdsWithin] with p hp
      exact hC G p (hG'.contDiffAt (hAopen.mem_nhds hp))
  have hmem0 : Set.Iio ε ∈ map (fun p : ℝ × E => ‖iteratedFDeriv ℝ j G p‖)
      (nhdsWithin (T, y) A) :=
    Filter.le_def.mp hnormlim _ (IsOpen.mem_nhds isOpen_Iio hε)
  have hmem : {p : ℝ × E | ‖iteratedFDeriv ℝ j G p‖ < ε} ∈ nhdsWithin (T, y) A :=
    Filter.mem_map.mp hmem0
  rw [nhdsWithin, Filter.mem_inf_iff_superset] at hmem
  obtain ⟨u, hu, v, hv, huv⟩ := hmem
  rw [Filter.mem_principal] at hv
  obtain ⟨δ, hδpos, hδsub⟩ := Metric.mem_nhds_iff.mp hu
  refine ⟨δ, hδpos, fun q hq1 hq2 hq3 hq4 => ?_⟩
  have hqu : q ∈ u := hδsub (by
    rw [Metric.mem_ball]
    simpa [dist_eq_norm, Real.norm_eq_abs, Prod.norm_def] using max_lt hq3 hq4)
  have hqv : q ∈ v := hv ⟨hq1, trivial, mem_ball_iff_norm.mpr hq2⟩
  exact huv ⟨hqu, hqv⟩

/-! ## The main theorem -/

/-- **The Heaviside cut of a function that is smooth on the left of a hyperplane and whose mixed
partials tend to `0` at the seam is smooth.**  If `G : ℝ × E → Z` is `C^∞` on the half-space
`{p | p.1 < T}` intersected with `univ ×ˢ U`, and for every `k, m` and every `y ∈ U` the mixed jet
`∂_y^m ∂_t^k G` tends to `0` as `p → (T, y)` from the left, then `p ↦ if p.1 < T then G p else 0`
is `C^∞` at `(T, y₀)`.

NOTE (the reason for `∀ y ∈ U` rather than a single limit at `y₀`): `ContDiffAt` is a
*neighbourhood* condition, so the flatness has to hold at the seam points `(T,y)` for `y` near
`y₀`; with the limit assumed only at `y₀` the statement is false (`G(t,y) = exp(-1/y²)`).  This is
the "flat at the seam" step of the Borel/Whitney construction of a smooth extension of a function
with bounded jets across the endpoint of its interval. -/
theorem heaviside_cut_smooth_at_seam
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]
    {T : ℝ} {y₀ : E} {U : Set E} (hU : U ∈ nhds y₀) {G : ℝ × E → Z}
    (hG : ContDiffOn ℝ (⊤ : ℕ∞) G ({p : ℝ × E | p.1 < T} ∩ (Set.univ ×ˢ U)))
    (h : ∀ k m : ℕ, ∀ y ∈ U, Filter.Tendsto (fun p : ℝ × E =>
          iteratedFDeriv ℝ m (fun y' : E => iteratedDeriv k (fun s : ℝ => G (s, y')) p.1) p.2)
        (nhdsWithin (T, y) ({p : ℝ × E | p.1 < T} ∩ (Set.univ ×ˢ U))) (nhds 0)) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun p : ℝ × E => if p.1 < T then G p else (0 : Z)) (T, y₀) := by
  obtain ⟨ρ, hρpos, hρU⟩ := Metric.mem_nhds_iff.mp hU
  have hG' : ContDiffOn ℝ (⊤ : ℕ∞) G
      ({p : ℝ × E | p.1 < T} ∩ (Set.univ ×ˢ Metric.ball y₀ ρ)) :=
    hG.mono (fun p hp => ⟨hp.1, trivial, hρU hp.2.2⟩)
  have hsm : ∀ p : ℝ × E, p.1 < T → ‖p.2 - y₀‖ < ρ → ContDiffAt ℝ (⊤ : ℕ∞) G p := by
    intro p hp1 hp2
    exact hG'.contDiffAt (((isOpen_lt continuous_fst continuous_const).inter
      (isOpen_univ.prod Metric.isOpen_ball)).mem_nhds
        ⟨hp1, trivial, mem_ball_iff_norm.mpr hp2⟩)
  have hflat : ∀ j : ℕ, SeamFlatPt T y₀ ρ G j := fun j => seamFlatPt_of_mixed hρU hG h j
  rw [contDiffAt_infty]
  intro n
  obtain ⟨δ, hδpos, -, hcont, -⟩ :=
    seamCut_contDiffOn_aux (E := E) (Z := Z) hρpos n G hsm (fun j _ => hflat j)
  exact hcont.contDiffAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hδpos))

end Work.Diff.EXT
