import Mathlib
import Submission.Work.RadialSpace.Basic

/-!
# Smoothness of a parametric interval integral

For a smooth function `k : ℝ → ℝ → ℂ`, the function `u ↦ ∫ t in (0:ℝ)..1, k u t` is smooth.
The proof differentiates under the integral sign and inducts on the order of smoothness; the
derivative of `u ↦ ∫ t in (0:ℝ)..1, k u t` is `u ↦ ∫ t in (0:ℝ)..1, ∂₁ k u t`, which is again
of the same shape.

The main application is the lemma `contDiff_parametric_integral` below.
-/

namespace Work.RadialSpace

open Filter Topology MeasureTheory Set
open scoped Topology ContDiff Interval

/-! ### Elementary facts about derivatives of uncurried maps -/

/-- The derivative of `v ↦ (v, t)`. -/
lemma deriv_prodMk_const (t x : ℝ) : deriv (fun v : ℝ => (v, t)) x = ((1 : ℝ), (0 : ℝ)) := by
  have h : HasDerivAt (fun v : ℝ => (v, t)) (((1 : ℝ), (0 : ℝ)) : ℝ × ℝ) x :=
    (hasDerivAt_id x).prodMk (hasDerivAt_const x t)
  simpa using h.deriv

/-- The derivative in the first variable of an uncurried map, expressed with the Fréchet
derivative of the uncurried map. -/
lemma deriv_fst_eq_fderiv {k : ℝ → ℝ → ℂ} {q : ℝ × ℝ}
    (h : DifferentiableAt ℝ (Function.uncurry k) q) :
    deriv (fun v : ℝ => k v q.2) q.1
      = (fderiv ℝ (Function.uncurry k) q) ((1 : ℝ), (0 : ℝ)) := by
  have hf : DifferentiableAt ℝ (fun v : ℝ => (v, q.2)) q.1 := by fun_prop
  have key := fderiv_comp_deriv (f := fun v : ℝ => (v, q.2))
    (l := Function.uncurry k) (x := q.1) h hf
  rw [deriv_prodMk_const] at key
  simpa [Function.comp_def, Prod.mk.eta] using key

/-- The first partial derivative of a `C^{m+1}` family is `C^m`. -/
lemma contDiffOn_deriv_fst_uncurry {k : ℝ → ℝ → ℂ} {s : Set ℝ} (hs : IsOpen s) {m : ℕ}
    (hk : ContDiffOn ℝ ((m : ℕ∞ω) + 1) (Function.uncurry k) (s ×ˢ univ)) :
    ContDiffOn ℝ (m : ℕ∞ω) (fun q : ℝ × ℝ => deriv (fun v : ℝ => k v q.2) q.1)
      (s ×ˢ univ) := by
  have hopen : IsOpen (s ×ˢ (univ : Set ℝ)) := hs.prod isOpen_univ
  have hfd : ContDiffOn ℝ (m : ℕ∞ω) (fderiv ℝ (Function.uncurry k)) (s ×ˢ univ) :=
    hk.fderiv_of_isOpen hopen le_rfl
  have h2 : ContDiffOn ℝ (m : ℕ∞ω)
      (fun q : ℝ × ℝ => (fderiv ℝ (Function.uncurry k) q) ((1 : ℝ), (0 : ℝ))) (s ×ˢ univ) := by
    have h3 := (ContinuousLinearMap.contDiff
      (ContinuousLinearMap.apply ℝ ℂ ((1 : ℝ), (0 : ℝ)))).comp_contDiffOn hfd
    simpa [Function.comp_def, ContinuousLinearMap.apply_apply] using h3
  refine h2.congr (fun q hq => ?_)
  exact deriv_fst_eq_fderiv
    ((hk.differentiableOn (by simp)).differentiableAt (hopen.mem_nhds hq))

/-- The map `u ↦ k u t` is differentiable at `x ∈ s` for a `C^1` family `k` on `s × univ`. -/
lemma differentiableAt_uncurry_fst {k : ℝ → ℝ → ℂ} {s : Set ℝ} (hs : IsOpen s) {m : ℕ}
    (hk : ContDiffOn ℝ ((m : ℕ∞ω) + 1) (Function.uncurry k) (s ×ˢ univ)) {x t : ℝ}
    (hx : x ∈ s) : DifferentiableAt ℝ (fun u : ℝ => k u t) x := by
  have hopen : IsOpen (s ×ˢ (univ : Set ℝ)) := hs.prod isOpen_univ
  have hq : (x, t) ∈ s ×ˢ univ := ⟨hx, trivial⟩
  have hd : DifferentiableAt ℝ (Function.uncurry k) (x, t) :=
    ((hk.differentiableOn (by simp)) (x, t) hq).differentiableAt (hopen.mem_nhds hq)
  have hf : DifferentiableAt ℝ (fun u : ℝ => (u, t)) x := by fun_prop
  exact hd.comp x hf

/-- Continuity in the second variable at a fixed first variable. -/
lemma continuousOn_snd_fix {g : ℝ × ℝ → ℂ} {s : Set ℝ}
    (hcont : ContinuousOn g (s ×ˢ univ)) {x : ℝ} (hx : x ∈ s) :
    Continuous (fun t : ℝ => g (x, t)) := by
  have h1 : ContinuousOn (fun t : ℝ => (x, t)) univ :=
    (continuous_const.prodMk continuous_id).continuousOn
  have h2 : ContinuousOn (fun t : ℝ => g (x, t)) univ :=
    hcont.comp h1 (fun t _ => ⟨hx, trivial⟩)
  exact continuousOn_univ.mp h2

/-- Continuity in the first variable at a fixed second variable, within `s`. -/
lemma continuousWithinAt_fst_fix {g : ℝ × ℝ → ℂ} {s : Set ℝ}
    (hcont : ContinuousOn g (s ×ˢ univ)) {x t : ℝ} (hx : x ∈ s) :
    ContinuousWithinAt (fun u : ℝ => g (u, t)) s x := by
  have h1 : ContinuousOn (fun u : ℝ => (u, t)) s :=
    (continuous_id.prodMk continuous_const).continuousOn
  exact (hcont.comp h1 (fun u hu => ⟨hu, trivial⟩)).continuousWithinAt hx

/-- An unordered open-closed interval of nonnegative length sits inside the closed interval. -/
lemma uIoc_subset_Icc {a b : ℝ} (h : a ≤ b) : Set.uIoc a b ⊆ Set.Icc a b := by
  rw [← Set.uIcc_of_le h]
  exact Set.uIoc_subset_uIcc

/-! ### Differentiation under the integral sign -/

variable {k : ℝ → ℝ → ℂ} {s : Set ℝ}

/-- **Differentiation under the integral sign**, for the interval `0..1`.

If `k` is `C^{m+1}` on `s × univ`, then `u ↦ ∫ t in (0:ℝ)..1, k u t` is differentiable at every
point of `s`, with derivative `u ↦ ∫ t in (0:ℝ)..1, ∂₁ k u t`. -/
lemma hasDerivAt_intervalIntegral_param (hs : IsOpen s) {m : ℕ}
    (hk : ContDiffOn ℝ ((m : ℕ∞ω) + 1) (Function.uncurry k) (s ×ˢ univ)) {x₀ : ℝ}
    (hx₀ : x₀ ∈ s) :
    HasDerivAt (fun u : ℝ => ∫ t in (0 : ℝ)..1, k u t)
      (∫ t in (0 : ℝ)..1, deriv (fun v : ℝ => k v t) x₀) x₀ := by
  obtain ⟨δ, hδpos, hδ⟩ := Metric.mem_nhds_iff.mp (hs.mem_nhds hx₀)
  set r : ℝ := δ / 2 with hrdef
  have hrpos : 0 < r := by rw [hrdef]; linarith
  have hrsδ : r < δ := by rw [hrdef]; linarith
  have hballs : Metric.ball x₀ r ⊆ s := fun x hx => hδ (Metric.ball_subset_ball hrsδ.le hx)
  have hcloseds : Metric.closedBall x₀ r ⊆ s :=
    fun x hx => hδ (Metric.closedBall_subset_ball hrsδ hx)
  have hcont : ContinuousOn (Function.uncurry k) (s ×ˢ univ) := hk.continuousOn
  have hderivcont : ContinuousOn (fun q : ℝ × ℝ => deriv (fun v : ℝ => k v q.2) q.1)
      (s ×ˢ univ) := (contDiffOn_deriv_fst_uncurry hs hk).continuousOn
  have hcompact : IsCompact (Metric.closedBall x₀ r ×ˢ Set.Icc (0 : ℝ) 1) :=
    (isCompact_closedBall x₀ r).prod isCompact_Icc
  obtain ⟨C', hC'⟩ := hcompact.exists_bound_of_continuousOn
    (hderivcont.mono (Set.prod_mono hcloseds (Set.subset_univ _)))
  have hbint : Integrable (fun _ : ℝ => C') (volume.restrict (Set.uIoc (0 : ℝ) 1)) :=
    intervalIntegrable_iff.mp (intervalIntegrable_const (c := C') (a := (0 : ℝ)) (b := 1))
  have hF_meas : ∀ᶠ x in 𝓝 x₀,
      AEStronglyMeasurable (fun t : ℝ => k x t) (volume.restrict (Set.uIoc (0 : ℝ) 1)) :=
    Filter.Eventually.mono (Metric.ball_mem_nhds x₀ hrpos)
      (fun x hx => (continuousOn_snd_fix hcont (hballs hx)).aestronglyMeasurable)
  have hF_int : Integrable (fun t : ℝ => k x₀ t) (volume.restrict (Set.uIoc (0 : ℝ) 1)) :=
    intervalIntegrable_iff.mp (ContinuousOn.intervalIntegrable
      ((continuousOn_snd_fix hcont hx₀).continuousOn.mono (Set.subset_univ _)))
  have hF'_meas : AEStronglyMeasurable (fun t : ℝ => deriv (fun v : ℝ => k v t) x₀)
      (volume.restrict (Set.uIoc (0 : ℝ) 1)) :=
    ((continuousOn_snd_fix hderivcont hx₀)).aestronglyMeasurable
  have h_bound : ∀ᵐ t ∂(volume.restrict (Set.uIoc (0 : ℝ) 1)),
      ∀ x ∈ Metric.ball x₀ r, ‖deriv (fun v : ℝ => k v t) x‖ ≤ C' := by
    rw [ae_restrict_iff' measurableSet_uIoc]
    refine Filter.Eventually.of_forall (fun t ht => ?_)
    intro x hx
    exact hC' (x, t) ⟨Metric.ball_subset_closedBall hx, uIoc_subset_Icc (by norm_num) ht⟩
  have h_diff : ∀ᵐ t ∂(volume.restrict (Set.uIoc (0 : ℝ) 1)),
      ∀ x ∈ Metric.ball x₀ r,
        HasDerivAt (fun u : ℝ => k u t) (deriv (fun v : ℝ => k v t) x) x := by
    rw [ae_restrict_iff' measurableSet_uIoc]
    refine Filter.Eventually.of_forall (fun t _ => ?_)
    intro x hx
    exact (differentiableAt_uncurry_fst hs hk (hballs hx)).hasDerivAt
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Set.uIoc (0 : ℝ) 1))
    (F := fun u t => k u t) (F' := fun u t => deriv (fun v : ℝ => k v t) u)
    (x₀ := x₀) (s := Metric.ball x₀ r) (bound := fun _ => C')
    (Metric.ball_mem_nhds x₀ hrpos) hF_meas hF_int hF'_meas h_bound hbint h_diff
  have hconv : ∀ f : ℝ → ℂ,
      (∫ t : ℝ, f t ∂(volume.restrict (Set.uIoc (0 : ℝ) 1))) = ∫ t in (0 : ℝ)..1, f t := by
    intro f
    rw [intervalIntegral.intervalIntegral_eq_integral_uIoc]
    simp
  have hfun : (fun u : ℝ => ∫ t in (0 : ℝ)..1, k u t)
      = fun u : ℝ => ∫ t : ℝ, k u t ∂(volume.restrict (Set.uIoc (0 : ℝ) 1)) :=
    funext (fun u => (hconv (fun t => k u t)).symm)
  have hval : (∫ t in (0 : ℝ)..1, deriv (fun v : ℝ => k v t) x₀)
      = ∫ t : ℝ, deriv (fun v : ℝ => k v t) x₀ ∂(volume.restrict (Set.uIoc (0 : ℝ) 1)) :=
    (hconv (fun t => deriv (fun v : ℝ => k v t) x₀)).symm
  rw [hfun, hval]
  exact hmain.2

/-- Continuity under the integral sign, for the interval `0..1`. -/
lemma continuousOn_intervalIntegral_param (hs : IsOpen s)
    (hcont : ContinuousOn (Function.uncurry k) (s ×ˢ univ)) :
    ContinuousOn (fun u : ℝ => ∫ t in (0 : ℝ)..1, k u t) s := by
  intro x₀ hx₀
  obtain ⟨δ, hδpos, hδ⟩ := Metric.mem_nhds_iff.mp (hs.mem_nhds hx₀)
  set r : ℝ := δ / 2 with hrdef
  have hrpos : 0 < r := by rw [hrdef]; linarith
  have hrsδ : r < δ := by rw [hrdef]; linarith
  have hballs : Metric.ball x₀ r ⊆ s := fun x hx => hδ (Metric.ball_subset_ball hrsδ.le hx)
  have hcloseds : Metric.closedBall x₀ r ⊆ s :=
    fun x hx => hδ (Metric.closedBall_subset_ball hrsδ hx)
  have hcompact : IsCompact (Metric.closedBall x₀ r ×ˢ Set.Icc (0 : ℝ) 1) :=
    (isCompact_closedBall x₀ r).prod isCompact_Icc
  obtain ⟨C, hC⟩ := hcompact.exists_bound_of_continuousOn
    (hcont.mono (Set.prod_mono hcloseds (Set.subset_univ _)))
  refine intervalIntegral.continuousWithinAt_of_dominated_interval (μ := volume)
    (bound := fun _ => C) ?_ ?_ ?_ ?_
  · rw [eventually_nhdsWithin_iff]
    filter_upwards [Metric.ball_mem_nhds x₀ hrpos] with x hx _
    exact (continuousOn_snd_fix hcont (hballs hx)).aestronglyMeasurable
  · rw [eventually_nhdsWithin_iff]
    filter_upwards [Metric.ball_mem_nhds x₀ hrpos] with x hx _
    refine Filter.Eventually.of_forall (fun t ht => ?_)
    exact hC (x, t) ⟨Metric.ball_subset_closedBall hx, uIoc_subset_Icc (by norm_num) ht⟩
  · exact intervalIntegrable_const (a := (0 : ℝ)) (b := 1)
  · refine Filter.Eventually.of_forall (fun t _ => ?_)
    exact continuousWithinAt_fst_fix hcont hx₀

/-- **Smoothness under the integral sign.** For a `C^n` family `k` on `s × univ`, the parametric
integral `u ↦ ∫ t in (0:ℝ)..1, k u t` is `C^n` on `s`. -/
theorem contDiffOn_intervalIntegral_param (k : ℝ → ℝ → ℂ) {s : Set ℝ} (hs : IsOpen s) (n : ℕ)
    (hk : ContDiffOn ℝ (n : ℕ∞ω) (Function.uncurry k) (s ×ˢ univ)) :
    ContDiffOn ℝ (n : ℕ∞ω) (fun u : ℝ => ∫ t in (0 : ℝ)..1, k u t) s := by
  induction n generalizing k with
  | zero =>
    rw [Nat.cast_zero, contDiffOn_zero]
    exact continuousOn_intervalIntegral_param hs (contDiffOn_zero.mp hk)
  | succ n ih =>
    have hcast : ((Nat.succ n : ℕ) : ℕ∞ω) = (n : ℕ∞ω) + 1 := by simp [Nat.succ_eq_add_one]
    rw [hcast] at hk ⊢
    refine (contDiffOn_succ_iff_deriv_of_isOpen hs).mpr ⟨?_, ?_, ?_⟩
    · intro x hx
      exact (hasDerivAt_intervalIntegral_param hs hk hx).differentiableAt.differentiableWithinAt
    · intro h
      exact absurd h (by simp)
    · set k' : ℝ → ℝ → ℂ := fun u t => deriv (fun v : ℝ => k v t) u with hk'def
      have hk'' : ContDiffOn ℝ (n : ℕ∞ω) (Function.uncurry k') (s ×ˢ univ) :=
        contDiffOn_deriv_fst_uncurry hs hk
      refine (ih k' hk'').congr (fun x hx => ?_)
      exact (hasDerivAt_intervalIntegral_param hs hk hx).deriv

end Work.RadialSpace

namespace Work.RadialSpace

open Filter Topology MeasureTheory Set
open scoped Topology ContDiff Interval

/-- **Smoothness of the Fourier parametric integral.** If `φ : ℝ → ℂ` is smooth, then
`u ↦ ∫ t in (0:ℝ)..1, φ (u * t)` is smooth. -/
theorem contDiff_parametric_integral (φ : ℝ → ℂ) (hφ : ContDiff ℝ Work.RadialSpace.Smooth φ) :
    ContDiff ℝ Work.RadialSpace.Smooth fun u : ℝ => ∫ t in (0 : ℝ)..1, φ (u * t) := by
  have hφn : ∀ n : ℕ, ContDiff ℝ (n : ℕ∞ω) φ := fun n => (contDiff_infty.mp hφ) n
  rw [← contDiffOn_univ, contDiffOn_infty]
  intro n
  have hk : ContDiffOn ℝ (n : ℕ∞ω) (Function.uncurry (fun u t : ℝ => φ (u * t)))
      (univ ×ˢ univ) := by
    rw [Set.univ_prod_univ]
    exact contDiffOn_univ.mpr ((hφn n).comp (by fun_prop))
  exact contDiffOn_intervalIntegral_param (fun u t : ℝ => φ (u * t)) isOpen_univ n hk

end Work.RadialSpace
