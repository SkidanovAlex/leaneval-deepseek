/-
Copyright: work module for the Elgindi finite-time singularity project.

# Smoothness of the angular integral `s ↦ ∫_θ u(s,θ) φ(θ) dθ`

The integrand depends on the parameter `s` through the function `u`, which is smooth on
a neighbourhood of the closed quadrant, while the angular factor `φ` is only *continuous*
on `Iθ = [0,π/2]`.  Differentiating under the integral sign repeatedly therefore exhibits
the `s`-derivatives of the integral as the integrals of the corresponding `s`-derivatives
of `u`; compactness of `Iθ` and boundedness of `φ` (continuous on a compact interval)
supply the domination needed both for continuity and for the differentiation step.

## Main results

* `continuousOn_integral_Itheta_of_continuousOn` : the parametric integral over `Iθ` of a
  jointly continuous integrand is continuous in the parameter.
* `hasDerivAt_integral_Itheta_of_hasDerivAt` : differentiation under the integral sign
  over `Iθ`.
* `contDiffOn_infty_integral_Itheta` : `s ↦ ∫_θ u s θ · φ θ` is `C^∞` on `(0,∞)`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.PsiStar_ode
import Submission.Work.Spaces.HardyZ
import Submission.Work.Spaces.SmoothCompact_Aux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false

/-! ## The angular interval `Iθ = [0,π/2]` -/

theorem measurableSet_Itheta : MeasurableSet Work.Spaces.Iθ := by
  rw [Work.Spaces.Iθ]; exact measurableSet_Icc

theorem isCompact_Itheta : IsCompact Work.Spaces.Iθ := by
  rw [Work.Spaces.Iθ]; exact isCompact_Icc

theorem isFiniteMeasure_restrict_Itheta : IsFiniteMeasure (volume.restrict Work.Spaces.Iθ) := by
  rw [isFiniteMeasure_restrict]
  exact isCompact_Itheta.measure_ne_top

/-- The `θ`-slice of a function that is jointly continuous on `V ×ˢ Iθ` is continuous in `θ`
on `Iθ`. -/
theorem continuousOn_slice_of_continuousOn_uncurry {g : ℝ → ℝ → ℝ} {V : Set ℝ}
    (hg : ContinuousOn (Function.uncurry g) (V ×ˢ Work.Spaces.Iθ)) {s : ℝ} (hs : s ∈ V) :
    ContinuousOn (fun θ => g s θ) Work.Spaces.Iθ := by
  have h2 : ContinuousOn (fun θ : ℝ => (s, θ)) Work.Spaces.Iθ :=
    continuousOn_const.prodMk continuousOn_id
  have h3 := hg.comp h2 (fun θ hθ => ⟨hs, hθ⟩)
  simpa [Function.comp_def, Function.uncurry] using h3

/-- **Continuity of the parametric integral over `Iθ`.**  If `g` is jointly continuous on
`V ×ˢ Iθ` with `V` open, then `s ↦ ∫_θ g s θ` is continuous on `V`.  (Dominated convergence,
the dominating constant being the sup of `|g|` on a compact neighbourhood of the point crossed
with `Iθ`.) -/
theorem continuousOn_integral_Itheta_of_continuousOn {g : ℝ → ℝ → ℝ} {V : Set ℝ}
    (hV : IsOpen V) (hg : ContinuousOn (Function.uncurry g) (V ×ˢ Work.Spaces.Iθ)) :
    ContinuousOn (fun s => ∫ θ in Work.Spaces.Iθ, g s θ) V := by
  have hslice : ∀ s ∈ V, ContinuousOn (fun θ => g s θ) Work.Spaces.Iθ :=
    fun s hs => continuousOn_slice_of_continuousOn_uncurry hg hs
  intro s₀ hs₀
  have hscont : ∀ θ ∈ Work.Spaces.Iθ, ContinuousAt (fun s => g s θ) s₀ := by
    intro θ hθ
    have h1 : ContinuousWithinAt (Function.uncurry g) (V ×ˢ Work.Spaces.Iθ) (s₀, θ) :=
      hg _ ⟨hs₀, hθ⟩
    have h2 : ContinuousWithinAt (fun s : ℝ => (s, θ)) V s₀ :=
      continuousWithinAt_id.prodMk continuousWithinAt_const
    have h3 := h1.comp (f := fun s : ℝ => (s, θ)) (s := V) (t := V ×ˢ Work.Spaces.Iθ)
      (x := s₀) h2 (fun s hs => ⟨hs, hθ⟩)
    have h4 : ContinuousWithinAt (fun s => g s θ) V s₀ := by
      simpa [Function.comp_def, Function.uncurry] using h3
    exact h4.continuousAt (hV.mem_nhds hs₀)
  obtain ⟨δ, hδpos, hδV⟩ := Metric.mem_nhds_iff.1 (hV.mem_nhds hs₀)
  set K : Set ℝ := Set.Icc (s₀ - δ / 2) (s₀ + δ / 2) with hKdef
  have hKc : IsCompact K := by rw [hKdef]; exact isCompact_Icc
  have hKV : K ⊆ V := by
    intro x hx
    apply hδV
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    refine ⟨?_, ?_⟩ <;> linarith [hx.1, hx.2, hδpos]
  have hcontK : ContinuousOn (Function.uncurry g) (K ×ˢ Work.Spaces.Iθ) :=
    hg.mono (Set.prod_mono hKV (subset_refl _))
  obtain ⟨C, hC⟩ := (hKc.prod isCompact_Itheta).exists_bound_of_continuousOn hcontK
  have hfin := isFiniteMeasure_restrict_Itheta
  have key : ContinuousAt (fun s => ∫ θ in Work.Spaces.Iθ, g s θ) s₀ := by
    refine tendsto_integral_filter_of_norm_le_const (F := fun s θ => g s θ)
      (f := fun θ => g s₀ θ) ?_ ?_ ?_
    · filter_upwards [hV.mem_nhds hs₀] with s hs
      exact (hslice s hs).aestronglyMeasurable measurableSet_Itheta
    · refine ⟨C, ?_⟩
      have hmem : s₀ ∈ Set.Ioo (s₀ - δ / 2) (s₀ + δ / 2) := ⟨by linarith, by linarith⟩
      filter_upwards [isOpen_Ioo.mem_nhds hmem] with s hs
      rw [ae_restrict_iff' measurableSet_Itheta]
      refine Eventually.of_forall fun ω hω => ?_
      simpa [Function.uncurry] using hC (s, ω) ⟨Set.Ioo_subset_Icc_self hs, hω⟩
    · rw [ae_restrict_iff' measurableSet_Itheta]
      exact Eventually.of_forall fun ω hω => (hscont ω hω).tendsto
  exact key.continuousWithinAt

/-- **Differentiation under the integral sign over `Iθ`.**  If `g` and the candidate
`s`-derivative `g'` are jointly continuous on `V ×ˢ Iθ` (`V` open) and `s ↦ g s θ` has
derivative `s ↦ g' s θ` at every `s ∈ V`, for every `θ ∈ Iθ`, then the parametric integral
has derivative the integral of `g'`. -/
theorem hasDerivAt_integral_Itheta_of_hasDerivAt {g g' : ℝ → ℝ → ℝ} {V : Set ℝ}
    (hV : IsOpen V) {s₀ : ℝ} (hs₀ : s₀ ∈ V)
    (hg : ContinuousOn (Function.uncurry g) (V ×ˢ Work.Spaces.Iθ))
    (hg' : ContinuousOn (Function.uncurry g') (V ×ˢ Work.Spaces.Iθ))
    (hdiff : ∀ θ ∈ Work.Spaces.Iθ, ∀ s ∈ V, HasDerivAt (fun s => g s θ) (g' s θ) s) :
    HasDerivAt (fun s => ∫ θ in Work.Spaces.Iθ, g s θ) (∫ θ in Work.Spaces.Iθ, g' s₀ θ) s₀ := by
  have hslice : ∀ s ∈ V, ContinuousOn (fun θ => g s θ) Work.Spaces.Iθ :=
    fun s hs => continuousOn_slice_of_continuousOn_uncurry hg hs
  have hslice' : ∀ s ∈ V, ContinuousOn (fun θ => g' s θ) Work.Spaces.Iθ :=
    fun s hs => continuousOn_slice_of_continuousOn_uncurry hg' hs
  obtain ⟨δ, hδpos, hδV⟩ := Metric.mem_nhds_iff.1 (hV.mem_nhds hs₀)
  set K : Set ℝ := Set.Icc (s₀ - δ / 2) (s₀ + δ / 2) with hKdef
  have hKc : IsCompact K := by rw [hKdef]; exact isCompact_Icc
  have hKV : K ⊆ V := by
    intro x hx
    apply hδV
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    refine ⟨?_, ?_⟩ <;> linarith [hx.1, hx.2, hδpos]
  have hcontK : ContinuousOn (Function.uncurry g') (K ×ˢ Work.Spaces.Iθ) :=
    hg'.mono (Set.prod_mono hKV (subset_refl _))
  obtain ⟨C, hC⟩ := (hKc.prod isCompact_Itheta).exists_bound_of_continuousOn hcontK
  have hfin := isFiniteMeasure_restrict_Itheta
  have hmem : s₀ ∈ Set.Ioo (s₀ - δ / 2) (s₀ + δ / 2) := ⟨by linarith, by linarith⟩
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict Work.Spaces.Iθ) (𝕜 := ℝ)
    (F := fun s θ => g s θ) (F' := fun s θ => g' s θ) (bound := fun _ => C)
    (x₀ := s₀) (s := Set.Ioo (s₀ - δ / 2) (s₀ + δ / 2))
    (isOpen_Ioo.mem_nhds hmem) ?_ ?_ ?_ ?_ ?_ ?_
  · exact key.2
  · filter_upwards [isOpen_Ioo.mem_nhds hmem, hV.mem_nhds hs₀] with x hxW hxV
    exact (hslice x hxV).aestronglyMeasurable measurableSet_Itheta
  · exact (hslice s₀ hs₀).integrableOn_compact isCompact_Itheta
  · exact (hslice' s₀ hs₀).aestronglyMeasurable measurableSet_Itheta
  · rw [ae_restrict_iff' measurableSet_Itheta]
    refine Eventually.of_forall fun a ha x hx => ?_
    have hxs : x ∈ K := Set.Ioo_subset_Icc_self hx
    simpa [Function.uncurry] using hC (x, a) ⟨hxs, ha⟩
  · exact integrable_const C
  · rw [ae_restrict_iff' measurableSet_Itheta]
    refine Eventually.of_forall fun a ha x hx => ?_
    exact hdiff a ha x (hKV (Set.Ioo_subset_Icc_self hx))

theorem contDiffOn_infty_integral_Itheta (u : ℝ → ℝ → ℝ) (φ : ℝ → ℝ)
    (hu : Work.Spaces.SmoothNbhd u) (hφ : ContinuousOn φ Work.Spaces.Iθ) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun s => ∫ θ in Work.Spaces.Iθ, u s θ * φ θ)
      (Set.Ioi 0) := by
  -- joint continuity of `(s,θ) ↦ ∂_s^k u (s,θ) · φ θ` on `(0,∞) × Iθ`
  have hcont : ∀ k : ℕ, ContinuousOn
      (fun p : ℝ × ℝ => Work.Spaces.pzIter k u p.1 p.2 * φ p.2)
      (Set.Ioi 0 ×ˢ Work.Spaces.Iθ) := by
    intro k
    have hsm : Work.Spaces.SmoothNbhd (Work.Spaces.pzIter k u) :=
      Work.Spaces.smoothNbhd_pzIter hu k
    have hsub : Set.Ioi (0 : ℝ) ×ˢ Work.Spaces.Iθ ⊆ Work.Spaces.U :=
      Set.prod_mono (Set.Ioi_subset_Ioi (by norm_num)) (fun θ hθ =>
        ⟨by linarith [hθ.1], by linarith [hθ.2]⟩)
    have h1 : ContinuousOn (Function.uncurry (Work.Spaces.pzIter k u))
        (Set.Ioi 0 ×ˢ Work.Spaces.Iθ) := (hsm.mono hsub).continuousOn
    have h2 : ContinuousOn (fun p : ℝ × ℝ => φ p.2) (Set.Ioi 0 ×ˢ Work.Spaces.Iθ) :=
      hφ.comp continuousOn_snd (fun p hp => hp.2)
    exact (h1.mul h2).congr (fun p hp => rfl)
  -- the derivative of the `k`-th integral is the `(k+1)`-st one
  have hderiv : ∀ (k : ℕ) (s : ℝ), s ∈ Set.Ioi 0 →
      HasDerivAt (fun s => ∫ θ in Work.Spaces.Iθ, Work.Spaces.pzIter k u s θ * φ θ)
        (∫ θ in Work.Spaces.Iθ, Work.Spaces.pzIter (k + 1) u s θ * φ θ) s := by
    intro k s hs
    have h1 : ContinuousOn (Function.uncurry fun s θ => Work.Spaces.pzIter k u s θ * φ θ)
        (Set.Ioi 0 ×ˢ Work.Spaces.Iθ) := hcont k
    have h2 : ContinuousOn (Function.uncurry fun s θ => Work.Spaces.pzIter (k + 1) u s θ * φ θ)
        (Set.Ioi 0 ×ˢ Work.Spaces.Iθ) := hcont (k + 1)
    refine hasDerivAt_integral_Itheta_of_hasDerivAt isOpen_Ioi hs h1 h2 ?_
    intro θ hθ s' hs'
    have hsm : Work.Spaces.SmoothNbhd (Work.Spaces.pzIter k u) :=
      Work.Spaces.smoothNbhd_pzIter hu k
    have hslice := Work.Spaces.hardyZ_contDiffOn_slice (Work.Spaces.pzIter k u) hsm hθ
    have hs'mem : s' ∈ Set.Ioi (-1 : ℝ) := by
      have h0 : (0 : ℝ) < s' := hs'
      show (-1 : ℝ) < s'
      linarith
    have hd' : DifferentiableAt ℝ (fun t => Work.Spaces.pzIter k u t θ) s' :=
      (hslice.contDiffAt (isOpen_Ioi.mem_nhds hs'mem)).differentiableAt (by simp)
    have hkey := hd'.hasDerivAt.mul_const (φ θ)
    simpa [Work.Spaces.pzIter_succ, Work.Spaces.pz] using hkey
  -- `∀ n k, C^n` for all the iterated integrals, by induction on `n`
  have hmain : ∀ n : ℕ, ∀ k : ℕ, ContDiffOn ℝ ((n : ℕ) : WithTop ℕ∞)
      (fun s => ∫ θ in Work.Spaces.Iθ, Work.Spaces.pzIter k u s θ * φ θ) (Set.Ioi 0) := by
    intro n
    induction n with
    | zero =>
      intro k
      exact (contDiffOn_zero (𝕜 := ℝ)).2
        (continuousOn_integral_Itheta_of_continuousOn isOpen_Ioi (hcont k))
    | succ n ih =>
      intro k
      rw [Nat.cast_add, Nat.cast_one]
      refine (contDiffOn_succ_iff_deriv_of_isOpen (𝕜 := ℝ)
        (f := fun s => ∫ θ in Work.Spaces.Iθ, Work.Spaces.pzIter k u s θ * φ θ)
        (n := ((n : ℕ) : WithTop ℕ∞)) (s := Set.Ioi 0) isOpen_Ioi).2 ⟨?_, ?_, ?_⟩
      · exact fun s hs => (hderiv k s hs).differentiableAt.differentiableWithinAt
      · intro h; exact absurd h (by simp)
      · refine (ih (k + 1)).congr (fun s hs => ?_)
        exact (hderiv k s hs).deriv
  rw [contDiffOn_infty]
  intro n
  simpa using hmain n 0

end Work.Coercivity
