/-
Copyright: work module for the Elgindi finite-time singularity project (area `FTS.EllSol`).

# The second angular derivative of the truncated backward solution `Gc`

`Work.FTS.EllSol.ShiftFT.Gc N b u` is the backward particular solution of
`L_b G = χ_N · L_b u` used in the truncation argument for `shiftedFlat_of_nice`
(see `ShiftPrimDefs`):

`Gc N b u t θ = χ_N(t) · u(t,θ) + e^{bt} ∫_s∈[t,2N] e^{-bs} χ_N'(s) · u(s,θ) ds`.

This file computes its angular derivatives:

* `Gc_pth_aux` — the first derivative `∂_θ (Gc N b u)`;
* `Gc_pth_pth` — **the target**, the second derivative `∂_θ² (Gc N b u)`.

Both are obtained by differentiating under the integral sign in the angle variable (`θ`), for
which the general lemma `hasDerivAt_intervalIntegral_pth` below is provided: it says that for a
continuous multiplier `c` and functions `f`, `g` that are jointly continuous on
`univ ×ˢ V` (`V` open) and satisfy `HasDerivAt (fun θ' => f s θ') (g s θ) θ` for every `s` and
every `θ ∈ V`, one has

`HasDerivAt (fun θ => ∫_s∈[a,b] c s · f s θ) (∫_s∈[a,b] c s · g s θ₀) θ₀`.

The domination is supplied by compactness of the rectangle
`[min a b, max a b] × [θ₀ - δ/2, θ₀ + δ/2]` together with joint continuity of `(s,θ) ↦ c s · g s θ`.

Since the hypothesis on `u` is only `ContDiffOn ℝ 2` on `univ ×ˢ (0,π/2)`, the auxiliary
lemmas needed are: `pth` lowers the order of smoothness by one on an open set
(`pth_contDiffOn_uncurry_fin`), the curried slices are differentiable
(`Work.Spaces.differentiableAt_curry_right`), and `∂_θ` is the Fréchet derivative in the
direction `(0,1)` (`Work.Spaces.pth_eq_fderiv`).
-/
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Interval.Basic
import Submission.Work.FTS.EllSol.ShiftFT.ShiftPrimDefs
import Submission.Work.Spaces.CurrySmooth

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.ShiftFT

open MeasureTheory Set Filter
open scoped Real Topology Interval

noncomputable section

set_option autoImplicit false

/-- The open angular interval `(0, π/2)`. -/
abbrev gIθ : Set ℝ := Set.Ioo 0 (Real.pi / 2)

theorem isOpen_gIθ : IsOpen gIθ := isOpen_Ioo

/-! ## Generic calculus lemmas -/

/-- On an open set, the curried `θ`-partial derivative of a function lowers the order of
smoothness by one. -/
theorem pth_contDiffOn_uncurry_fin {n : ℕ} {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : ContDiffOn ℝ (n + 1) (Function.uncurry G) V) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pth G)) V := by
  have hchain : ∀ p ∈ V, Work.Spaces.pth G p.1 p.2
      = fderiv ℝ (Function.uncurry G) p (0, 1) := fun p hp =>
    Work.Spaces.pth_eq_fderiv ((h.differentiableOn (by simp)).differentiableAt (hV.mem_nhds hp))
  have hfd : ContDiffOn ℝ n (fun (p : ℝ × ℝ) => fderiv ℝ (Function.uncurry G) p) V :=
    h.fderiv_of_isOpen hV (m := n) (by simp)
  have hcomp : ContDiffOn ℝ n
      (fun (p : ℝ × ℝ) => (fderiv ℝ (Function.uncurry G) p) (0, 1)) V := by
    simpa using hfd.clm_apply contDiffOn_const
  exact hcomp.congr hchain

/-- **Differentiation under the integral sign in the parameter, over an interval.**  If `c` is
continuous, `f` and `g` are jointly continuous on the product of `univ` with an open set `V`,
and for every `s` the slice `θ ↦ f s θ` has derivative `g s θ` at every `θ ∈ V`, then
`θ ↦ ∫_s∈[a,b] c s · f s θ` has derivative `∫_s∈[a,b] c s · g s θ₀` at `θ₀`. -/
theorem hasDerivAt_intervalIntegral_pth
    {c : ℝ → ℝ} (hc : Continuous c) {f g : ℝ → ℝ → ℝ} {V : Set ℝ} (hV : IsOpen V)
    {a b θ₀ : ℝ} (hθ₀ : θ₀ ∈ V)
    (hf : ContinuousOn (Function.uncurry f) ((Set.univ : Set ℝ) ×ˢ V))
    (hg : ContinuousOn (Function.uncurry g) ((Set.univ : Set ℝ) ×ˢ V))
    (hdiff : ∀ s θ, θ ∈ V → HasDerivAt (fun θ' => f s θ') (g s θ) θ) :
    HasDerivAt (fun θ => ∫ s in a..b, c s * f s θ) (∫ s in a..b, c s * g s θ₀) θ₀ := by
  obtain ⟨δ, hδpos, hδV⟩ := Metric.mem_nhds_iff.1 (hV.mem_nhds hθ₀)
  set K : Set ℝ := Set.Icc (θ₀ - δ / 2) (θ₀ + δ / 2) with hKdef
  set W : Set ℝ := Set.Ioo (θ₀ - δ / 2) (θ₀ + δ / 2) with hWdef
  set J : Set ℝ := Set.Icc (min a b) (max a b) with hJdef
  have hKW : K ⊆ V := by
    intro y hy
    refine hδV ?_
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    exact ⟨by linarith [hy.1, hδpos], by linarith [hy.2, hδpos]⟩
  have hWK : W ⊆ K := Set.Ioo_subset_Icc_self
  have hJc : IsCompact J := by rw [hJdef]; exact isCompact_Icc
  have hKc : IsCompact K := by rw [hKdef]; exact isCompact_Icc
  have hIJ : Set.uIoc a b ⊆ J := by
    rw [hJdef, Set.Icc_min_max]
    exact Set.uIoc_subset_uIcc
  have hWnhds : W ∈ 𝓝 θ₀ := by
    rw [hWdef]
    exact isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩
  have hcontG : ContinuousOn (fun p : ℝ × ℝ => c p.1 * g p.1 p.2) (J ×ˢ K) := by
    have h1 : ContinuousOn (fun p : ℝ × ℝ => c p.1) (J ×ˢ K) :=
      hc.comp_continuousOn continuousOn_fst
    have h2 : ContinuousOn (fun p : ℝ × ℝ => g p.1 p.2) (J ×ˢ K) :=
      hg.mono (Set.prod_mono (subset_univ J) hKW)
    exact h1.mul h2
  obtain ⟨C, hC⟩ := (hJc.prod hKc).exists_bound_of_continuousOn hcontG
  have hJF : ∀ x ∈ V, ContinuousOn (fun s => c s * f s x) J := by
    intro x hx
    have h1 : ContinuousOn (fun s : ℝ => c s) J := hc.comp_continuousOn continuousOn_id
    have h2 : ContinuousOn (fun s : ℝ => f s x) J := by
      have hmap : ContinuousOn (fun s : ℝ => (s, x)) J :=
        continuousOn_id.prodMk (continuousOn_const (s := J) (c := x))
      have hcomp := hf.comp hmap (fun s _ => ⟨trivial, hx⟩)
      simpa [Function.comp_def, Function.uncurry] using hcomp
    exact h1.mul h2
  have hJG : ∀ x ∈ V, ContinuousOn (fun s => c s * g s x) J := by
    intro x hx
    have h1 : ContinuousOn (fun s : ℝ => c s) J := hc.comp_continuousOn continuousOn_id
    have h2 : ContinuousOn (fun s : ℝ => g s x) J := by
      have hmap : ContinuousOn (fun s : ℝ => (s, x)) J :=
        continuousOn_id.prodMk (continuousOn_const (s := J) (c := x))
      have hcomp := hg.comp hmap (fun s _ => ⟨trivial, hx⟩)
      simpa [Function.comp_def, Function.uncurry] using hcomp
    exact h1.mul h2
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (𝕜 := ℝ)
    (F := fun θ s => c s * f s θ) (F' := fun θ s => c s * g s θ) (bound := fun _ => C)
    (x₀ := θ₀) (s := W) hWnhds ?_ ?_ ?_ ?_ ?_ ?_).2
  · filter_upwards [hV.mem_nhds hθ₀] with x hx
    exact ((hJF x hx).mono hIJ).aestronglyMeasurable measurableSet_uIoc
  · refine ContinuousOn.intervalIntegrable ((hJF θ₀ hθ₀).mono ?_)
    rw [← Set.Icc_min_max, hJdef]
  · exact ((hJG θ₀ hθ₀).mono hIJ).aestronglyMeasurable measurableSet_uIoc
  · filter_upwards with t ht x hx
    exact hC (t, x) ⟨hIJ ht, hWK hx⟩
  · exact intervalIntegrable_const
  · filter_upwards with t ht x hx
    exact (hdiff t x (hKW (hWK hx))).const_mul (c t)

/-! ## The angular derivatives of `Gc` -/

/-- The first angular derivative of `Gc`: differentiating the defining formula under the
integral sign.  (This is the `b`-shifted counterpart of the definition; note that the prefactor
`χ_N(t)` and `e^{bt}` do not depend on `θ`.) -/
theorem Gc_pth_aux (N b : ℝ) (u : ℝ → ℝ → ℝ)
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    ∀ t : ℝ, ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      Work.Spaces.pth (Gc N b u) t θ
      = Work.FTS.EllSol.Trunc.chi N t * Work.Spaces.pth u t θ
        + Real.exp (b * t) * ∫ s in t..(2 * N),
            Real.exp (-(b * s)) * deriv (Work.FTS.EllSol.Trunc.chi N) s
              * Work.Spaces.pth u s θ := by
  intro t θ hθ
  have hS : IsOpen ((Set.univ : Set ℝ) ×ˢ gIθ) := isOpen_univ.prod isOpen_Ioo
  have hc : Continuous
      (fun s : ℝ => Real.exp (-(b * s)) * deriv (Work.FTS.EllSol.Trunc.chi N) s) :=
    (Real.continuous_exp.comp ((continuous_const.mul continuous_id).neg)).mul
      ((Work.FTS.EllSol.Trunc.chi_contDiff 2 N).continuous_deriv (by norm_num))
  have hu1 : ContDiffOn ℝ 1 (Function.uncurry u) ((Set.univ : Set ℝ) ×ˢ gIθ) :=
    hu.of_le (by norm_num)
  have hpt1 : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pth u))
      ((Set.univ : Set ℝ) ×ˢ gIθ) := pth_contDiffOn_uncurry_fin hS (n := 1) hu
  have hd_u : ∀ s θ', θ' ∈ gIθ → HasDerivAt (fun θ'' => u s θ'') (Work.Spaces.pth u s θ') θ' := by
    intro s θ' hθ'
    have hmem : (s, θ') ∈ (Set.univ : Set ℝ) ×ˢ gIθ := ⟨trivial, hθ'⟩
    have hdiff : DifferentiableAt ℝ (Function.uncurry u) (s, θ') :=
      (hu.differentiableOn (by simp)).differentiableAt (hS.mem_nhds hmem)
    exact (Work.Spaces.differentiableAt_curry_right hdiff).hasDerivAt
  have hH1 : HasDerivAt (fun θ'' => ∫ s in t..(2 * N),
        Real.exp (-(b * s)) * deriv (Work.FTS.EllSol.Trunc.chi N) s * u s θ'')
      (∫ s in t..(2 * N),
        Real.exp (-(b * s)) * deriv (Work.FTS.EllSol.Trunc.chi N) s * Work.Spaces.pth u s θ) θ :=
    hasDerivAt_intervalIntegral_pth hc isOpen_gIθ hθ hu1.continuousOn hpt1.continuousOn hd_u
  have h1 : HasDerivAt (fun θ'' => Work.FTS.EllSol.Trunc.chi N t * u t θ'')
      (Work.FTS.EllSol.Trunc.chi N t * Work.Spaces.pth u t θ) θ :=
    (hd_u t θ hθ).const_mul _
  have h2 : HasDerivAt (fun θ'' => Real.exp (b * t) * ∫ s in t..(2 * N),
        Real.exp (-(b * s)) * deriv (Work.FTS.EllSol.Trunc.chi N) s * u s θ'')
      (Real.exp (b * t) * ∫ s in t..(2 * N),
        Real.exp (-(b * s)) * deriv (Work.FTS.EllSol.Trunc.chi N) s * Work.Spaces.pth u s θ) θ :=
    hH1.const_mul _
  rw [show Work.Spaces.pth (Gc N b u) t θ
      = deriv (fun θ'' => Gc N b u t θ'') θ from rfl]
  exact (h1.add h2).deriv

theorem Gc_pth_pth (N b : ℝ) (u : ℝ → ℝ → ℝ)
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    ∀ t : ℝ, ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      Work.Spaces.pth (Work.Spaces.pth (Work.FTS.EllSol.ShiftFT.Gc N b u)) t θ
      = Work.FTS.EllSol.Trunc.chi N t * Work.Spaces.pth (Work.Spaces.pth u) t θ
        + Real.exp (b * t) * ∫ s in t..(2 * N),
            Real.exp (-(b * s)) * deriv (Work.FTS.EllSol.Trunc.chi N) s
              * Work.Spaces.pth (Work.Spaces.pth u) s θ := by
  intro t θ hθ
  have hS : IsOpen ((Set.univ : Set ℝ) ×ˢ gIθ) := isOpen_univ.prod isOpen_Ioo
  have hc : Continuous
      (fun s : ℝ => Real.exp (-(b * s)) * deriv (Work.FTS.EllSol.Trunc.chi N) s) :=
    (Real.continuous_exp.comp ((continuous_const.mul continuous_id).neg)).mul
      ((Work.FTS.EllSol.Trunc.chi_contDiff 2 N).continuous_deriv (by norm_num))
  have hpt1 : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pth u))
      ((Set.univ : Set ℝ) ×ˢ gIθ) := pth_contDiffOn_uncurry_fin hS (n := 1) hu
  have hpt2 : ContinuousOn (Function.uncurry (Work.Spaces.pth (Work.Spaces.pth u)))
      ((Set.univ : Set ℝ) ×ˢ gIθ) :=
    (pth_contDiffOn_uncurry_fin hS (n := 0) hpt1).continuousOn
  have hd_pth : ∀ s θ', θ' ∈ gIθ →
      HasDerivAt (fun θ'' => Work.Spaces.pth u s θ'')
        (Work.Spaces.pth (Work.Spaces.pth u) s θ') θ' := by
    intro s θ' hθ'
    have hmem : (s, θ') ∈ (Set.univ : Set ℝ) ×ˢ gIθ := ⟨trivial, hθ'⟩
    have hdiff : DifferentiableAt ℝ (Function.uncurry (Work.Spaces.pth u)) (s, θ') :=
      (hpt1.differentiableOn (by simp)).differentiableAt (hS.mem_nhds hmem)
    exact (Work.Spaces.differentiableAt_curry_right hdiff).hasDerivAt
  -- the function whose derivative we compute is `θ' ↦ ∂_θ(Gc) t θ'`, given by `Gc_pth_aux`
  have heq : (fun θ' => Work.Spaces.pth (Gc N b u) t θ') =ᶠ[𝓝 θ]
      (fun θ' => Work.FTS.EllSol.Trunc.chi N t * Work.Spaces.pth u t θ'
        + Real.exp (b * t) * ∫ s in t..(2 * N),
            Real.exp (-(b * s)) * deriv (Work.FTS.EllSol.Trunc.chi N) s
              * Work.Spaces.pth u s θ') := by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
    exact Gc_pth_aux N b u hu t θ' hθ'
  have hder : deriv (fun θ' => Work.FTS.EllSol.Trunc.chi N t * Work.Spaces.pth u t θ'
        + Real.exp (b * t) * ∫ s in t..(2 * N),
            Real.exp (-(b * s)) * deriv (Work.FTS.EllSol.Trunc.chi N) s
              * Work.Spaces.pth u s θ') θ
      = Work.FTS.EllSol.Trunc.chi N t * Work.Spaces.pth (Work.Spaces.pth u) t θ
        + Real.exp (b * t) * ∫ s in t..(2 * N),
            Real.exp (-(b * s)) * deriv (Work.FTS.EllSol.Trunc.chi N) s
              * Work.Spaces.pth (Work.Spaces.pth u) s θ := by
    have hH2 : HasDerivAt (fun θ' => ∫ s in t..(2 * N),
          Real.exp (-(b * s)) * deriv (Work.FTS.EllSol.Trunc.chi N) s
            * Work.Spaces.pth u s θ')
        (∫ s in t..(2 * N),
          Real.exp (-(b * s)) * deriv (Work.FTS.EllSol.Trunc.chi N) s
            * Work.Spaces.pth (Work.Spaces.pth u) s θ) θ :=
      hasDerivAt_intervalIntegral_pth hc isOpen_gIθ hθ hpt1.continuousOn hpt2 hd_pth
    have h1 : HasDerivAt (fun θ' => Work.FTS.EllSol.Trunc.chi N t * Work.Spaces.pth u t θ')
        (Work.FTS.EllSol.Trunc.chi N t * Work.Spaces.pth (Work.Spaces.pth u) t θ) θ :=
      (hd_pth t θ hθ).const_mul _
    have h2 : HasDerivAt (fun θ' => Real.exp (b * t) * ∫ s in t..(2 * N),
          Real.exp (-(b * s)) * deriv (Work.FTS.EllSol.Trunc.chi N) s
            * Work.Spaces.pth u s θ')
        (Real.exp (b * t) * ∫ s in t..(2 * N),
          Real.exp (-(b * s)) * deriv (Work.FTS.EllSol.Trunc.chi N) s
            * Work.Spaces.pth (Work.Spaces.pth u) s θ) θ :=
      hH2.const_mul _
    exact (h1.add h2).deriv
  rw [show Work.Spaces.pth (Work.Spaces.pth (Work.FTS.EllSol.ShiftFT.Gc N b u)) t θ
      = deriv (fun θ' => Work.Spaces.pth (Work.FTS.EllSol.ShiftFT.Gc N b u) t θ') θ from rfl,
    Filter.EventuallyEq.deriv_eq heq]
  exact hder

end

end Work.FTS.EllSol.ShiftFT
