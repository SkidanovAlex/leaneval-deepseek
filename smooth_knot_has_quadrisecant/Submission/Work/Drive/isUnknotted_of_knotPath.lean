import Mathlib
import Submission.Helpers
import Submission.Work.Drive.isUnknotted_of_close
import Submission.Work.Drive.familyRadiusAlt

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

/-!
# `IsUnknotted` from a `C¹` path of analytic knots

Target of this file: `Work.Drive.isUnknotted_of_knotPath`.  Given a knot `r` and a
family `R : ℝ → ℝ → Space` which

* is jointly `C¹` on the parameter slab,
* starts at `r` (`R t 0 = r t`) and ends at the round circle (`R t 1 = standardCircle t`),
* has *analytic* slices `R · s` that are knots, for every `s ∈ [0,1]`,

we must produce an **analytic** isotopy from `r` to `standardCircle` through knots, i.e.
`IsUnknotted r` — note that `ContDiff ℝ ⊤` in this development is analyticity, so the
hypothesis `ContDiff ℝ 1` is *not* enough to conclude directly.

The argument is a connectedness argument along the path of slices, using the two
"one-sided openness" statements for unknottedness:

* `isUnknotted_of_close` (already proved in the workspace): if `r'` is an analytic knot
  that is `C¹`-close to `r` and `r'` is unknotted, then `r` is unknotted;
* `closeRevAux` below (the other half): if `r` is an unknotted analytic knot and `r'` is
  `C¹`-close to `r`, then `r'` is unknotted (correct the isotopy of `r` by the small
  linear correction `(1-s) • (r' - r)` and use `uniformRadiusAlt`).

Both need the slices to vary continuously with the slice parameter, which is
`familyWindowAtC1` below: the `C¹` analogue of `familyWindowAt` (which is stated for
analytic families only).
-/

private lemma periodPos : (0 : ℝ) < period := by unfold period; positivity

/-- The velocity of a sum of curves. -/
private lemma velocity_add' {f g : ℝ → Space} {t : ℝ}
    (hf : DifferentiableAt ℝ f t) (hg : DifferentiableAt ℝ g t) :
    velocity (fun u : ℝ => f u + g u) t = velocity f t + velocity g t := by
  have h : (fun u : ℝ => f u + g u) = f + g := rfl
  unfold velocity
  rw [h, deriv_add hf hg]

/-- The velocity of a difference of curves. -/
private lemma velocity_sub' {f g : ℝ → Space} {t : ℝ}
    (hf : DifferentiableAt ℝ f t) (hg : DifferentiableAt ℝ g t) :
    velocity (fun u : ℝ => f u - g u) t = velocity f t - velocity g t := by
  have h : (fun u : ℝ => f u - g u) = f - g := rfl
  unfold velocity
  rw [h, deriv_sub hf hg]

/-- The velocity of a constant multiple of a curve. -/
private lemma velocity_const_smul' {w : ℝ → Space} (c : ℝ) {t : ℝ}
    (hw : DifferentiableAt ℝ w t) :
    velocity (fun u : ℝ => c • w u) t = c • velocity w t := by
  have h : (fun u : ℝ => c • w u) = c • w := rfl
  unfold velocity
  rw [h, deriv_const_smul c hw]

/-! ## `C¹`-continuity of the slices in the slice parameter -/

/-- The canonical representative of `t` in the fundamental interval `[0, period]`. -/
private noncomputable def fwRed (t : ℝ) : ℝ := t - (⌊t / period⌋ : ℝ) * period

private lemma fwRed_mem (t : ℝ) : fwRed t ∈ Set.Icc (0 : ℝ) period := by
  have hT : 0 < period := periodPos
  have hk1 : ((⌊t / period⌋ : ℤ) : ℝ) ≤ t / period := Int.floor_le _
  have hk2 : t / period < ((⌊t / period⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
  constructor
  · have h : ((⌊t / period⌋ : ℤ) : ℝ) * period ≤ (t / period) * period :=
      mul_le_mul_of_nonneg_right hk1 (le_of_lt hT)
    have ht : (t / period) * period = t := by rw [div_mul_cancel₀ _ (ne_of_gt hT)]
    simp only [fwRed]
    linarith
  · have h : t < (((⌊t / period⌋ : ℤ) : ℝ) + 1) * period := by
      have := mul_lt_mul_of_pos_right hk2 hT
      rwa [div_mul_cancel₀ _ (ne_of_gt hT)] at this
    simp only [fwRed]
    linarith

/-- The `t`-derivative of a slice is the partial derivative of the two-variable map. -/
private lemma deriv_slice_eq_fderiv {R : ℝ → ℝ → Space}
    (hR : ContDiff ℝ 1 (fun p : ℝ × ℝ => R p.1 p.2)) (t s : ℝ) :
    deriv (fun u : ℝ => R u s) t =
      fderiv ℝ (fun p : ℝ × ℝ => R p.1 p.2) (t, s) (1, 0) := by
  have hφ : HasFDerivAt (fun u : ℝ => (u, s)) (ContinuousLinearMap.inl ℝ ℝ ℝ) t :=
    hasFDerivAt_prodMk_left t s
  have hF : HasFDerivAt (fun p : ℝ × ℝ => R p.1 p.2)
      (fderiv ℝ (fun p : ℝ × ℝ => R p.1 p.2) (t, s)) (t, s) :=
    ((hR.differentiable (by decide)).differentiableAt).hasFDerivAt
  have hfd := (hF.comp t hφ).fderiv
  rw [← fderiv_apply_one_eq_deriv (f := fun u : ℝ => R u s) (x := t)]
  change (fderiv ℝ ((fun p : ℝ × ℝ => R p.1 p.2) ∘ fun u : ℝ => (u, s)) t) 1
      = (fderiv ℝ (fun p : ℝ × ℝ => R p.1 p.2) (t, s)) (1, 0)
  rw [hfd]
  simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply]

/-- The partial `t`-derivative of a jointly `C¹` two-variable map is continuous. -/
private lemma continuous_fderiv_partial {R : ℝ → ℝ → Space}
    (hR : ContDiff ℝ 1 (fun p : ℝ × ℝ => R p.1 p.2)) :
    Continuous (fun p : ℝ × ℝ => fderiv ℝ (fun p : ℝ × ℝ => R p.1 p.2) p (1, 0)) := by
  have h := hR.continuous_fderiv_apply (by decide : (1 : WithTop ℕ∞) ≠ 0)
  exact h.comp (continuous_id.prodMk continuous_const)

/-- The velocity of a slice, identified with the partial derivative. -/
private lemma velocity_slice_eq {R : ℝ → ℝ → Space}
    (hR : ContDiff ℝ 1 (fun p : ℝ × ℝ => R p.1 p.2)) (t s : ℝ) :
    velocity (fun u : ℝ => R u s) t
      = fderiv ℝ (fun p : ℝ × ℝ => R p.1 p.2) (t, s) (1, 0) := by
  show deriv (fun u : ℝ => R u s) t = _
  exact deriv_slice_eq_fderiv hR t s

/-- The derivative of a periodic map is periodic. -/
private lemma periodic_deriv {f : ℝ → Space} {c : ℝ} (h : Function.Periodic f c) :
    Function.Periodic (deriv f) c := by
  intro x
  have hx : deriv (fun y : ℝ => f (y + c)) x = deriv f x := by
    rw [show (fun y : ℝ => f (y + c)) = f from funext h]
  rwa [deriv_comp_add_const f c x] at hx

/-- **Two-sided `C¹`-window at an interior parameter, for a merely jointly `C¹`
family.**  For every `s₀ ∈ [0,1]` and every `γ > 0` the slices of the family are
uniformly `C¹`-close to the slice at `s₀` for slice parameters in a neighbourhood
of `s₀`.  This is the `C¹` version of `familyWindowAt` (which assumes
`ContDiff ℝ ⊤` of the family); only joint continuity of the family and of its
`t`-partial derivative is used, and the slices being knots makes them
`period`-periodic, which bounds the curve parameter `t` to a compact interval. -/
theorem familyWindowAtC1 {R : ℝ → ℝ → LeanEval.KnotTheory.Quadrisecant.Space}
    (hR : ContDiff ℝ 1 (fun p : ℝ × ℝ => R p.1 p.2))
    (hslice : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      LeanEval.KnotTheory.Quadrisecant.IsSmoothKnot (fun t : ℝ => R t s))
    {s₀ : ℝ} (hs₀ : s₀ ∈ Set.Icc (0 : ℝ) 1) {γ : ℝ} (hγ : 0 < γ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Set.Icc (0 : ℝ) 1, |s - s₀| ≤ δ → ∀ t : ℝ,
      ‖R t s - R t s₀‖ ≤ γ ∧
      ‖LeanEval.KnotTheory.Quadrisecant.velocity (fun u : ℝ => R u s) t -
        LeanEval.KnotTheory.Quadrisecant.velocity (fun u : ℝ => R u s₀) t‖ ≤ γ := by
  set F : ℝ × ℝ → Space := fun p => R p.1 p.2 with hF
  have hFcont : Continuous F := hR.continuous
  have hDcont : Continuous fun p : ℝ × ℝ => fderiv ℝ F p (1, 0) :=
    continuous_fderiv_partial hR
  have hKcomp : IsCompact (Set.Icc (0 : ℝ) period ×ˢ Set.Icc (0 : ℝ) 1) :=
    isCompact_Icc.prod isCompact_Icc
  obtain ⟨δ₁, hδ₁, hδ₁b⟩ := Metric.uniformContinuousOn_iff_le.mp
    (hKcomp.uniformContinuousOn_of_continuous hFcont.continuousOn) γ hγ
  obtain ⟨δ₂, hδ₂, hδ₂b⟩ := Metric.uniformContinuousOn_iff_le.mp
    (hKcomp.uniformContinuousOn_of_continuous hDcont.continuousOn) γ hγ
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, ?_⟩
  intro s hs hsδ t
  have hδ1 : |s - s₀| ≤ δ₁ := le_trans hsδ (min_le_left _ _)
  have hδ2 : |s - s₀| ≤ δ₂ := le_trans hsδ (min_le_right _ _)
  set t₀ : ℝ := fwRed t with ht₀
  have ht₀mem : t₀ ∈ Set.Icc (0 : ℝ) period := fwRed_mem t
  have ht₀b : t₀ = t - (⌊t / period⌋ : ℝ) * period := by rw [ht₀]; rfl
  have hper_s : R t s = R t₀ s := by
    rw [ht₀b]
    exact ((hslice s hs).periodic.sub_int_mul_eq (⌊t / period⌋)).symm
  have hper_s₀ : R t s₀ = R t₀ s₀ := by
    rw [ht₀b]
    exact ((hslice s₀ hs₀).periodic.sub_int_mul_eq (⌊t / period⌋)).symm
  have hper_vs : velocity (fun u : ℝ => R u s) t = velocity (fun u : ℝ => R u s) t₀ := by
    rw [ht₀b]
    show deriv (fun u : ℝ => R u s) t
      = deriv (fun u : ℝ => R u s) (t - (⌊t / period⌋ : ℝ) * period)
    exact ((periodic_deriv (hslice s hs).periodic).sub_int_mul_eq (⌊t / period⌋)).symm
  have hper_vs₀ : velocity (fun u : ℝ => R u s₀) t = velocity (fun u : ℝ => R u s₀) t₀ := by
    rw [ht₀b]
    show deriv (fun u : ℝ => R u s₀) t
      = deriv (fun u : ℝ => R u s₀) (t - (⌊t / period⌋ : ℝ) * period)
    exact ((periodic_deriv (hslice s₀ hs₀).periodic).sub_int_mul_eq (⌊t / period⌋)).symm
  have hdist1 : dist (t₀, s) (t₀, s₀) ≤ δ₁ := by
    rw [Prod.dist_eq, dist_self, Real.dist_eq, max_eq_right (abs_nonneg _)]
    exact hδ1
  have hdist2 : dist (t₀, s) (t₀, s₀) ≤ δ₂ := by
    rw [Prod.dist_eq, dist_self, Real.dist_eq, max_eq_right (abs_nonneg _)]
    exact hδ2
  constructor
  · rw [hper_s, hper_s₀, ← dist_eq_norm]
    exact hδ₁b (t₀, s) ⟨ht₀mem, hs⟩ (t₀, s₀) ⟨ht₀mem, hs₀⟩ hdist1
  · rw [hper_vs, hper_vs₀, velocity_slice_eq hR t₀ s, velocity_slice_eq hR t₀ s₀,
      ← dist_eq_norm]
    exact hδ₂b (t₀, s) ⟨ht₀mem, hs⟩ (t₀, s₀) ⟨ht₀mem, hs₀⟩ hdist2

/-! ## Unknottedness is open -/

/-- **The other half of the openness of unknottedness.**  If the analytic knot `r`
is unknotted, then every analytic knot `r'` that is `C¹`-close to `r` is unknotted:
correcting an isotopy of `r` by the linear correction `(1-s) • (r' - r)` keeps every
slice a knot (`uniformRadiusAlt`), and realises `r'` at `s = 0` and
`standardCircle` at `s = 1`. -/
private theorem closeRevAux {r : ℝ → LeanEval.KnotTheory.Quadrisecant.Space}
    (hr : LeanEval.KnotTheory.Quadrisecant.IsSmoothKnot r)
    (hun : LeanEval.KnotTheory.Quadrisecant.IsUnknotted r) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ r' : ℝ → LeanEval.KnotTheory.Quadrisecant.Space,
      LeanEval.KnotTheory.Quadrisecant.IsSmoothKnot r' →
      (∀ t : ℝ, ‖r' t - r t‖ < ε ∧
        ‖LeanEval.KnotTheory.Quadrisecant.velocity r' t -
          LeanEval.KnotTheory.Quadrisecant.velocity r t‖ < ε) →
      LeanEval.KnotTheory.Quadrisecant.IsUnknotted r' := by
  obtain ⟨R, hRsm, hR0, hR1, hRslice⟩ := hun
  obtain ⟨ρ, hρpos, hρ⟩ := uniformRadiusAlt hRsm hRslice
  refine ⟨ρ, hρpos, ?_⟩
  intro r' hr' hclose
  refine ⟨fun t s => R t s + (1 - s) • (r' t - r t), ?_, ?_, ?_, ?_⟩
  · -- joint analyticity
    exact hRsm.add (ContDiff.smul (contDiff_const.sub contDiff_snd)
      ((hr'.smooth.sub hr.smooth).comp contDiff_fst))
  · -- starts at `r'`
    intro t
    show R t 0 + (1 - 0) • (r' t - r t) = r' t
    rw [hR0 t, sub_zero, one_smul]
    abel
  · -- ends at the round circle
    intro t
    show R t 1 + (1 - 1) • (r' t - r t) = standardCircle t
    rw [hR1 t, sub_self, zero_smul, add_zero]
  · -- every slice is a knot
    intro s hs
    refine hρ s hs (fun t => (1 - s) • (r' t - r t)) ?_ ?_ ?_ ?_
    · exact ContDiff.const_smul (1 - s) (hr'.smooth.sub hr.smooth)
    · intro t
      simp only [hr'.periodic t, hr.periodic t]
    · -- the correction is small in `C⁰`
      intro t
      rw [norm_smul, Real.norm_eq_abs]
      have h1 : |1 - s| ≤ 1 := by
        rw [abs_le]; exact ⟨by linarith [hs.2], by linarith [hs.1]⟩
      have h2 : ‖r' t - r t‖ < ρ := (hclose t).1
      calc |1 - s| * ‖r' t - r t‖ ≤ 1 * ‖r' t - r t‖ :=
            mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
        _ < ρ := by simpa using h2
    · -- the correction is small in `C¹`
      intro t
      have hd : DifferentiableAt ℝ (fun u : ℝ => r' u - r u) t :=
        ((hr'.smooth.sub hr.smooth).differentiable (by decide)).differentiableAt
      have hveq : velocity (fun u : ℝ => (1 - s) • (r' u - r u)) t
          = (1 - s) • (velocity r' t - velocity r t) := by
        rw [velocity_const_smul' (1 - s) hd,
          velocity_sub' ((hr'.smooth.differentiable (by decide)).differentiableAt)
            ((hr.smooth.differentiable (by decide)).differentiableAt)]
      rw [hveq, norm_smul, Real.norm_eq_abs]
      have h1 : |1 - s| ≤ 1 := by
        rw [abs_le]; exact ⟨by linarith [hs.2], by linarith [hs.1]⟩
      have h2 : ‖velocity r' t - velocity r t‖ < ρ := (hclose t).2
      calc |1 - s| * ‖velocity r' t - velocity r t‖ ≤ 1 * ‖velocity r' t - velocity r t‖ :=
            mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
        _ < ρ := by simpa using h2

/-! ## The main theorem -/

theorem isUnknotted_of_knotPath {r : ℝ → LeanEval.KnotTheory.Quadrisecant.Space}
    (hr : LeanEval.KnotTheory.Quadrisecant.IsSmoothKnot r)
    {R : ℝ → ℝ → LeanEval.KnotTheory.Quadrisecant.Space}
    (hR : ContDiff ℝ 1 (fun p : ℝ × ℝ => R p.1 p.2))
    (h0 : ∀ t : ℝ, R t 0 = r t)
    (h1 : ∀ t : ℝ, R t 1 = LeanEval.KnotTheory.Quadrisecant.standardCircle t)
    (hslice : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      LeanEval.KnotTheory.Quadrisecant.IsSmoothKnot (fun t : ℝ => R t s)) :
    LeanEval.KnotTheory.Quadrisecant.IsUnknotted r := by
  -- the set of slice parameters whose slice is unknotted
  let U : Set (Set.Icc (0 : ℝ) 1) := {x | IsUnknotted (fun t : ℝ => R t x.1)}
  have hU : U = {x : Set.Icc (0 : ℝ) 1 | IsUnknotted (fun t : ℝ => R t x.1)} := rfl
  haveI : PreconnectedSpace (Set.Icc (0 : ℝ) 1) :=
    Subtype.preconnectedSpace (isPreconnected_Icc (a := (0 : ℝ)) (b := 1))
  -- `U` is open: nearby slices of an unknotted slice are unknotted
  have hopen : IsOpen U := by
    rw [hU, Metric.isOpen_iff]
    rintro ⟨x, hx⟩ hxU
    obtain ⟨ε, hεpos, hε⟩ := closeRevAux (hslice x hx) hxU
    obtain ⟨δ, hδpos, hδ⟩ := familyWindowAtC1 hR hslice hx (γ := ε / 2) (by linarith)
    refine ⟨δ, hδpos, ?_⟩
    rintro ⟨y, hy⟩ hyb
    have hyx : |y - x| < δ := by
      rw [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq] at hyb
      exact hyb
    have hwin := hδ y hy (le_of_lt hyx)
    exact hε (fun t : ℝ => R t y) (hslice y hy)
      (fun t => ⟨by linarith [(hwin t).1], by linarith [(hwin t).2]⟩)
  -- `U` is closed: a slice close to an unknotted slice (using the forward direction)
  have hclosed : IsClosed U := by
    rw [hU, ← isOpen_compl_iff, Metric.isOpen_iff]
    rintro ⟨x, hx⟩ hxU
    obtain ⟨ε, hεpos, hε⟩ := isUnknotted_of_close (hslice x hx)
    obtain ⟨δ, hδpos, hδ⟩ := familyWindowAtC1 hR hslice hx (γ := ε / 2) (by linarith)
    refine ⟨δ, hδpos, ?_⟩
    rintro ⟨y, hy⟩ hyb
    have hyx : |y - x| < δ := by
      rw [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq] at hyb
      exact hyb
    intro hyU
    have hclose : ∀ t : ℝ, ‖R t y - R t x‖ < ε ∧
        ‖velocity (fun u : ℝ => R u y) t - velocity (fun u : ℝ => R u x) t‖ < ε := by
      intro t
      have hwin := hδ y hy (le_of_lt hyx) t
      exact ⟨by linarith [hwin.1], by linarith [hwin.2]⟩
    exact hxU (hε (fun t : ℝ => R t y) (hslice y hy) hclose hyU)
  have hclopen : IsClopen U := ⟨hclosed, hopen⟩
  -- `U` is nonempty: the terminal slice is the round circle
  have hne : U.Nonempty := by
    refine ⟨⟨1, by norm_num⟩, ?_⟩
    rw [hU]
    show IsUnknotted (fun t : ℝ => R t 1)
    rw [show (fun t : ℝ => R t 1) = standardCircle from funext h1]
    exact standardCircle_isUnknotted
  have hUniv : U = Set.univ := hclopen.eq_univ hne
  -- hence the initial slice is unknotted too
  have hun : IsUnknotted (fun t : ℝ => R t 0) := by
    have hmem : (⟨0, by norm_num⟩ : Set.Icc (0 : ℝ) 1) ∈ U := by
      rw [hUniv]; exact Set.mem_univ _
    rw [hU] at hmem
    exact hmem
  rwa [show (fun t : ℝ => R t 0) = r from funext h0] at hun

end Work.Drive
