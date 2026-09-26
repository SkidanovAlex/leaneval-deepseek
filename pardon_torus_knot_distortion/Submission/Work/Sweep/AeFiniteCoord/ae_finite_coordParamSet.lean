import Mathlib
import Submission.Work.Sweep.Defs

/-!
# Almost every coordinate level meets the ball in finitely many points

For a smooth knot `K`, a point `x`, a radius `R` and almost every level `s`, the set
of parameters `t ∈ [0, 2π]` with `K.curve t` in the ball `B(x,R)` and third
coordinate `s` is finite.

The proof is Sard's theorem in dimension one, in the form needed for the count.
Write `g t = (K.curve t) 2` for the third coordinate of the curve and let

  `A_s = {t ∈ [0, 2π] | g t = s}`

be the full level set in the fundamental interval.  If `A_s` were infinite, then
(as `A_s` is compact) it would have an accumulation point `t₀ ∈ A_s`; since `g` is
constant equal to `s` on `A_s`, the derivative of `g` at `t₀` must vanish.  Hence
every `s` with `A_s` infinite is a critical value of `g`, and the set of critical
values has measure zero by Sard's theorem.  So `A_s` is finite for almost every
`s`, and `coordParamSet K x R s ⊆ A_s` is finite as well.

Note that the transversality statement `IsTransverseCoord K x R s` (a.e. `s`, see
`Submission.Work.Sweep.AeTransverseCoord.ae_transverse_coord`) is *not* enough on
its own: it only constrains the points of `coordParamSet`, and an accumulation
point of that set may lie on the boundary of the ball, where `deriv g` may vanish.
The argument above uses the full level set in the fundamental interval, which is
closed, so that every accumulation point is a point of the level set.
-/

noncomputable section

set_option linter.style.haveILetI false

open LeanEval.KnotTheory.PardonDistortion MeasureTheory Set Filter
open scoped ENNReal Topology

namespace Work.Sweep.AeFiniteCoord

/-- **The analytic core.**  If `f` is differentiable at `x`, `f x = y`, and `x` is
an accumulation point of the level set `{t | f t = y}`, then `deriv f x = 0`.

Indeed the slope `(f t - f x)/(t - x)` tends to `deriv f x` as `t → x`, while it
is constantly `0` on the level set, which accumulates at `x`; by uniqueness of
limits `deriv f x = 0`. -/
lemma deriv_eq_zero_of_accPt_level {f : ℝ → ℝ} {x y : ℝ} (hd : HasDerivAt f (deriv f x) x)
    (hxy : f x = y) (h : AccPt x (𝓟 {t : ℝ | f t = y})) : deriv f x = 0 := by
  haveI : NeBot (𝓝[≠] x ⊓ 𝓟 {t : ℝ | f t = y}) := h
  have h1 : Tendsto (slope f x) (𝓝[≠] x ⊓ 𝓟 {t : ℝ | f t = y}) (𝓝 (deriv f x)) :=
    hd.tendsto_slope.mono_left inf_le_left
  have hEq : (fun t => slope f x t) =ᶠ[𝓝[≠] x ⊓ 𝓟 {t : ℝ | f t = y}] (fun _ => 0) :=
    (Filter.eventually_principal.mpr (fun t ht => by
      change slope f x t = 0
      rw [slope_def_field, ht, hxy, sub_self, zero_div])).filter_mono inf_le_right
  have h2 : Tendsto (slope f x) (𝓝[≠] x ⊓ 𝓟 {t : ℝ | f t = y}) (𝓝 0) :=
    Tendsto.congr' hEq.symm tendsto_const_nhds
  exact tendsto_nhds_unique h1 h2

/-- A compact subset of `ℝ` in which no point is an accumulation point of the set
is finite.  (Compactness turns the open cover by the punctured neighbourhoods of
its points into a finite subcover.) -/
lemma finite_of_isCompact_of_no_accPt {K : Set ℝ} (hK : IsCompact K)
    (h : ∀ x ∈ K, ¬ AccPt x (𝓟 K)) : K.Finite := by
  have hmem : (∅ : Set ℝ) ∈ Filter.codiscreteWithin K := by
    rw [mem_codiscreteWithin_accPt]
    intro x hx
    simpa using h x hx
  have := hK.finite_sdiff_of_mem_codiscreteWithin hmem
  simpa using this

/-- **Almost every coordinate level of the knot is finite.**

For almost every `s`, the set of parameters `t` in the fundamental interval
`[0, 2π]` at which the third coordinate of `K.curve t` equals `s` is finite.

The exceptional `s` are exactly the critical values of `t ↦ (K.curve t) 2`, a null
set by Sard's theorem. -/
theorem ae_finite_levelSet (K : Knot) :
    ∀ᵐ y ∂MeasureTheory.volume,
      {t ∈ Set.Icc (0 : ℝ) (2 * Real.pi) | (K.curve t) 2 = y}.Finite := by
  set g : ℝ → ℝ := fun u => (K.curve u) 2 with hgdef
  have hg : ContDiff ℝ (⊤ : ℕ∞) g := by
    have h : ContDiff ℝ (⊤ : ℕ∞)
        (fun u : ℝ => (PiLp.proj 2 (fun _ : Fin 3 => ℝ) 2) (K.curve u)) :=
      ContDiff.continuousLinearMap_comp _ K.smooth
    simpa [g] using h
  have hgd : ∀ t, HasDerivAt g (deriv g t) t := fun t =>
    (hg.differentiable (by simp)).differentiableAt.hasDerivAt
  -- Sard: the set of critical values of `g` is null.
  have hcrit : volume (g '' {t | deriv g t = 0}) = 0 := by
    refine addHaar_image_eq_zero_of_det_fderivWithin_eq_zero (μ := volume)
      (f' := fun t => ContinuousLinearMap.toSpanSingleton ℝ (deriv g t)) ?_ ?_
    · intro t _
      exact (hgd t).hasFDerivAt.hasFDerivWithinAt
    · intro t ht
      rw [ht, ContinuousLinearMap.det_toSpanSingleton]
  rw [MeasureTheory.ae_iff]
  refine measure_mono_null ?_ hcrit
  intro y hy
  -- If the full level set is infinite, `y` is a critical value.
  set A : Set ℝ := {t ∈ Set.Icc (0 : ℝ) (2 * Real.pi) | g t = y} with hAdef
  have hAinf : A.Infinite := hy
  have hAclosed : IsClosed A := by
    rw [hAdef]
    exact isClosed_Icc.inter (isClosed_eq hg.continuous continuous_const)
  have hAcomp : IsCompact A :=
    IsCompact.of_isClosed_subset isCompact_Icc hAclosed (fun t ht => ht.1)
  obtain ⟨t0, ht0A, hacc⟩ := hAinf.exists_accPt_of_subset_isCompact hAcomp Subset.rfl
  refine ⟨t0, deriv_eq_zero_of_accPt_level (hgd t0) ht0A.2 ?_, ht0A.2⟩
  exact hacc.mono (principal_mono.mpr fun t ht => ht.2)

/-- **Almost every coordinate level meets the ball in finitely many points.**

For almost every level `s`, the set of parameters `t ∈ [0, 2π]` at which `K.curve t`
lies in the open ball of centre `x` and radius `R` and has third coordinate `s` is
finite. -/
theorem ae_finite_coordParamSet (K : LeanEval.KnotTheory.PardonDistortion.Knot)
    (x : LeanEval.KnotTheory.PardonDistortion.R3) (R : ℝ) :
    ∀ᵐ s ∂MeasureTheory.volume, (Work.Sweep.coordParamSet K x R s).Finite := by
  filter_upwards [ae_finite_levelSet K] with s hs
  refine hs.subset fun t ht => ⟨ht.2, ?_⟩
  simpa using ht.1.2

end Work.Sweep.AeFiniteCoord
