import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Series of `C^N` functions on a convex set

Mathlib's `Mathlib/Analysis/Calculus/SmoothSeries.lean` differentiates series of functions
term by term on *open* (or `univ`-shaped) domains: `hasFDerivAt_tsum`,
`hasFDerivAt_tsum_of_isPreconnected`, `iteratedFDeriv_tsum`, `contDiff_tsum`.  Here we need the
same statement relative to a convex set `s` which need not be open, with the *within*-derivatives
`iteratedFDerivWithin ℝ k · s`.

The engine is `hasFDerivWithinAt_tsum_of_convex` below: on a convex set, the mean value theorem
`Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le` controls the tails of a series by the tails
of the summable majorant `v`, and an `ε/3` argument (finite initial segment + tail bound) yields
`HasFDerivWithinAt` for the sum, with the sum of the derivatives as derivative.

The main result `hasFTaylorSeriesUpToOn_tsum` then assembles Mathlib's
`ContDiffOn.ftaylorSeriesWithin` with the engine at each order: the `k`-th within-derivative of
`f i` is within-differentiable with derivative the `(k+1)`-st within-derivative curried
(`ContinuousMultilinearMap.curryLeft`), so the engine applies order by order, and
`continuousOn_tsum` gives the continuity of each term.
-/

namespace Work.Diff.EXT

open Filter Asymptotics Set
open scoped Topology ContDiff

/-- **Term-by-term differentiation of a series within a convex set.**

If each `g i` is differentiable within the convex set `s` with within-derivative `g' i`, the
derivatives are dominated by the summable family `v`, and the series `∑ i, g i y` converges at
every point of `s`, then `∑ i, g i` is differentiable within `s` with within-derivative
`∑ i, g' i x`.

This is the within-a-convex-set version of Mathlib's `hasFDerivAt_tsum_of_isPreconnected`
(which requires `s` open).  Convexity is used only for the mean value theorem
`Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le`. -/
theorem hasFDerivWithinAt_tsum_of_convex
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {s : Set E} (hs : Convex ℝ s)
    {g : ℕ → E → F} {g' : ℕ → E → E →L[ℝ] F} {v : ℕ → ℝ}
    (hg : ∀ (i : ℕ) (y : E), y ∈ s → HasFDerivWithinAt (g i) (g' i y) s y)
    (hb : ∀ (i : ℕ) (y : E), y ∈ s → ‖g' i y‖ ≤ v i)
    (hv : Summable v)
    (hsum : ∀ y ∈ s, Summable fun i : ℕ => g i y)
    (x : E) (hx : x ∈ s) :
    HasFDerivWithinAt (fun y : E => ∑' i : ℕ, g i y) (∑' i : ℕ, g' i x) s x := by
  rw [hasFDerivWithinAt_iff_isLittleO, isLittleO_iff]
  intro c hc
  set ε : ℝ := c / 3 with hεdef
  have hε : 0 < ε := by positivity
  -- A finite initial segment `T` whose complement is small, both for `v` and for the derivatives.
  obtain ⟨T, hT⟩ : ∃ T : Finset ℕ, (∑' i : {i // i ∉ T}, v i) ≤ ε :=
    ((tendsto_tsum_compl_atTop_zero v).eventually (Iic_mem_nhds hε)).exists
  have hsumx : Summable fun i : ℕ => g' i x := Summable.of_norm_bounded hv (fun i => hb i x hx)
  have hnorm' : Summable fun i : {i // i ∉ T} => ‖g' i x‖ :=
    Summable.of_norm_bounded (hv.subtype _) (fun i => by simpa using hb i x hx)
  have htail'_bound : ‖∑' i : {i // i ∉ T}, g' i x‖ ≤ ε := by
    calc ‖∑' i : {i // i ∉ T}, g' i x‖ ≤ ∑' i : {i // i ∉ T}, ‖g' i x‖ :=
          norm_tsum_le_tsum_norm hnorm'
      _ ≤ ∑' i : {i // i ∉ T}, v i :=
          Summable.tsum_le_tsum (fun i => hb i x hx) hnorm' (hv.subtype _)
      _ ≤ ε := hT
  have htail'_eq : (∑' i : ℕ, g' i x) = (∑ i ∈ T, g' i x) + ∑' i : {i // i ∉ T}, g' i x :=
    (hsumx.sum_add_tsum_subtype_compl T).symm
  have hnormGx : ‖(∑ i ∈ T, g' i x) - (∑' i : ℕ, g' i x)‖ ≤ ε := by
    have hc' : (∑ i ∈ T, g' i x) - (∑' i : ℕ, g' i x) = -(∑' i : {i // i ∉ T}, g' i x) := by
      rw [htail'_eq]; abel
    rw [hc', norm_neg]; exact htail'_bound
  -- The finite part is within-differentiable at `x`.
  have hS' : HasFDerivWithinAt (fun y : E => ∑ i ∈ T, g i y) (∑ i ∈ T, g' i x) s x :=
    HasFDerivWithinAt.fun_sum (fun i _ => hg i x hx)
  -- The tail is dominated by the mean value estimate, pointwise on `s`.
  have h1 : ∀ y ∈ s, ‖((∑' i : ℕ, g i y) - ∑ i ∈ T, g i y)
      - ((∑' i : ℕ, g i x) - ∑ i ∈ T, g i x)‖ ≤ ε * ‖y - x‖ := by
    intro y hy
    have hty : (∑' i : {i // i ∉ T}, g i y) = (∑' i : ℕ, g i y) - ∑ i ∈ T, g i y := by
      rw [eq_sub_iff_add_eq, add_comm]
      exact (hsum y hy).sum_add_tsum_subtype_compl T
    have htx : (∑' i : {i // i ∉ T}, g i x) = (∑' i : ℕ, g i x) - ∑ i ∈ T, g i x := by
      rw [eq_sub_iff_add_eq, add_comm]
      exact (hsum x hx).sum_add_tsum_subtype_compl T
    rw [← hty, ← htx]
    have hmvt : ∀ i : {i // i ∉ T}, ‖g i y - g i x‖ ≤ v i * ‖y - x‖ := fun i =>
      hs.norm_image_sub_le_of_norm_hasFDerivWithin_le (fun z hz => hg i z hz)
        (fun z hz => hb i z hz) hx hy
    have hnorm : Summable fun i : {i // i ∉ T} => ‖g i y - g i x‖ :=
      Summable.of_norm_bounded ((hv.subtype _).mul_right ‖y - x‖) (fun i => by simpa using hmvt i)
    have hsub : (∑' i : {i // i ∉ T}, g i y) - (∑' i : {i // i ∉ T}, g i x)
        = ∑' i : {i // i ∉ T}, (g i y - g i x) :=
      (Summable.tsum_sub (f := fun i : {i // i ∉ T} => g i y)
        (g := fun i : {i // i ∉ T} => g i x) ((hsum y hy).subtype _) ((hsum x hx).subtype _)).symm
    calc ‖(∑' i : {i // i ∉ T}, g i y) - ∑' i : {i // i ∉ T}, g i x‖
        = ‖∑' i : {i // i ∉ T}, (g i y - g i x)‖ := by rw [hsub]
      _ ≤ ∑' i : {i // i ∉ T}, ‖g i y - g i x‖ := norm_tsum_le_tsum_norm hnorm
      _ ≤ ∑' i : {i // i ∉ T}, v i * ‖y - x‖ :=
          Summable.tsum_le_tsum hmvt hnorm ((hv.subtype _).mul_right ‖y - x‖)
      _ = (∑' i : {i // i ∉ T}, v i) * ‖y - x‖ :=
          Summable.tsum_mul_right (f := fun i : {i // i ∉ T} => v i) ‖y - x‖ (hv.subtype _)
      _ ≤ ε * ‖y - x‖ := mul_le_mul_of_nonneg_right hT (norm_nonneg _)
  have h1' : ∀ᶠ y in 𝓝[s] x, ‖((∑' i : ℕ, g i y) - ∑ i ∈ T, g i y)
      - ((∑' i : ℕ, g i x) - ∑ i ∈ T, g i x)‖ ≤ ε * ‖y - x‖ :=
    (eventually_nhdsWithin_iff).2 (Filter.Eventually.of_forall (fun y hy => h1 y hy))
  have h2' : ∀ᶠ y in 𝓝[s] x, ‖(∑ i ∈ T, g i y) - (∑ i ∈ T, g i x)
      - (∑ i ∈ T, g' i x) (y - x)‖ ≤ ε * ‖y - x‖ := hS'.isLittleO.bound hε
  have h3' : ∀ᶠ y in 𝓝[s] x,
      ‖(∑ i ∈ T, g' i x) (y - x) - (∑' i : ℕ, g' i x) (y - x)‖ ≤ ε * ‖y - x‖ := by
    refine (eventually_nhdsWithin_iff).2 (Filter.Eventually.of_forall (fun y _ => ?_))
    rw [← sub_apply]
    calc ‖((∑ i ∈ T, g' i x) - (∑' i : ℕ, g' i x)) (y - x)‖
        ≤ ‖(∑ i ∈ T, g' i x) - (∑' i : ℕ, g' i x)‖ * ‖y - x‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ε * ‖y - x‖ := mul_le_mul_of_nonneg_right hnormGx (norm_nonneg _)
  filter_upwards [h1', h2', h3'] with y h1y h2y h3y
  have hdecomp : (∑' i : ℕ, g i y) - (∑' i : ℕ, g i x) - (∑' i : ℕ, g' i x) (y - x)
      = (((∑' i : ℕ, g i y) - ∑ i ∈ T, g i y)
          - ((∑' i : ℕ, g i x) - ∑ i ∈ T, g i x))
        + ((∑ i ∈ T, g i y) - (∑ i ∈ T, g i x) - (∑ i ∈ T, g' i x) (y - x))
        + ((∑ i ∈ T, g' i x) (y - x) - (∑' i : ℕ, g' i x) (y - x)) := by abel
  rw [hdecomp]
  have key : ‖(((∑' i : ℕ, g i y) - ∑ i ∈ T, g i y)
          - ((∑' i : ℕ, g i x) - ∑ i ∈ T, g i x))
        + ((∑ i ∈ T, g i y) - (∑ i ∈ T, g i x) - (∑ i ∈ T, g' i x) (y - x))
        + ((∑ i ∈ T, g' i x) (y - x) - (∑' i : ℕ, g' i x) (y - x))‖
      ≤ ε * ‖y - x‖ + (ε * ‖y - x‖ + ε * ‖y - x‖) := by
    refine le_trans (norm_add_le _ _) ?_
    refine le_trans (add_le_add (norm_add_le _ _) le_rfl) ?_
    linarith
  exact le_trans key (le_of_eq (by rw [hεdef]; ring))

/-- **Series of `C^N` functions on a convex set with nonempty interior.**  If `s` is convex with
nonempty interior and each `f i` is `C^N` on `s`, and the (within-)iterated derivatives of the
`f i` are bounded on `s` by summable numbers `v k ·` for every order `k ≤ N`, then the sum
`∑' i, f i` is `C^N` on `s`, with within-`k`-th derivative equal to the sum of the within-`k`-th
derivatives.

This is a version on a (convex, possibly non-open) set of Mathlib's
`contDiff_tsum`/`iteratedFDeriv_tsum` from `Mathlib/Analysis/Calculus/SmoothSeries.lean`
(convexity is used for the mean value estimate that passes differentiation to the uniform limit;
nonempty interior gives `UniqueDiffOn ℝ s`, so `iteratedFDerivWithin` behaves). -/
theorem hasFTaylorSeriesUpToOn_tsum
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {s : Set E} (hs : Convex ℝ s) (hsint : (interior s).Nonempty)
    {N : ℕ} {f : ℕ → E → F} {v : ℕ → ℕ → ℝ}
    (hf : ∀ i : ℕ, ContDiffOn ℝ (N : WithTop ℕ∞) (f i) s)
    (hv : ∀ k : ℕ, k ≤ N → Summable fun i : ℕ => v k i)
    (h'f : ∀ (k i : ℕ), k ≤ N → ∀ x ∈ s, ‖iteratedFDerivWithin ℝ k (f i) s x‖ ≤ v k i) :
    HasFTaylorSeriesUpToOn (N : WithTop ℕ∞) (fun x => ∑' i : ℕ, f i x)
      (fun x k => ∑' i : ℕ, iteratedFDerivWithin ℝ k (f i) s x) s := by
  have hU : UniqueDiffOn ℝ s := uniqueDiffOn_convex hs hsint
  refine ⟨?_, ?_, ?_⟩
  · -- the `0`-th order: `curry0` commutes with the sum
    intro x hx
    have hcurry : (∑' i : ℕ, iteratedFDerivWithin ℝ 0 (f i) s x).curry0
        = ∑' i : ℕ, (iteratedFDerivWithin ℝ 0 (f i) s x).curry0 :=
      (continuousMultilinearCurryFin0 ℝ E F).toContinuousLinearEquiv.map_tsum
        (f := fun i : ℕ => iteratedFDerivWithin ℝ 0 (f i) s x)
        (L := SummationFilter.unconditional ℕ)
    rw [hcurry]
    exact tsum_congr (fun i => by simp [ContinuousMultilinearMap.curry0_apply])
  · -- the derivative of the `m`-th order term is the sum of the `(m+1)`-st derivatives
    intro m hm x hx
    have hmN : m < N := by
      have h1 : ((m : ℕ∞) : WithTop ℕ∞) < ((N : ℕ∞) : WithTop ℕ∞) := hm
      exact_mod_cast h1
    have hm1 : m + 1 ≤ N := hmN
    have hmN' : m ≤ N := le_of_lt hmN
    have hg' : ∀ (i : ℕ) (y : E), y ∈ s →
        HasFDerivWithinAt (iteratedFDerivWithin ℝ m (f i) s)
          ((iteratedFDerivWithin ℝ (m+1) (f i) s y).curryLeft) s y :=
      fun i y hy => ((hf i).ftaylorSeriesWithin hU).fderivWithin m hm y hy
    have hb' : ∀ (i : ℕ) (y : E), y ∈ s →
        ‖(iteratedFDerivWithin ℝ (m+1) (f i) s y).curryLeft‖ ≤ v (m+1) i := by
      intro i y hy
      have h1 : ‖iteratedFDerivWithin ℝ (m+1) (f i) s y‖ ≤ v (m+1) i := h'f (m+1) i hm1 y hy
      rwa [show (iteratedFDerivWithin ℝ (m+1) (f i) s y).curryLeft
          = (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m+1) => E) F)
              (iteratedFDerivWithin ℝ (m+1) (f i) s y) from rfl,
        LinearIsometryEquiv.norm_map]
    have hsumm : ∀ y ∈ s, Summable fun i : ℕ => iteratedFDerivWithin ℝ m (f i) s y :=
      fun y hy => Summable.of_norm_bounded (hv m hmN') (fun i => h'f m i hmN' y hy)
    have hmain := hasFDerivWithinAt_tsum_of_convex hs hg' hb' (hv (m+1) hm1) hsumm x hx
    have hcurryL : (∑' i : ℕ, iteratedFDerivWithin ℝ (m+1) (f i) s x).curryLeft
        = ∑' i : ℕ, (iteratedFDerivWithin ℝ (m+1) (f i) s x).curryLeft :=
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m+1) => E) F).toContinuousLinearEquiv.map_tsum
        (f := fun i : ℕ => iteratedFDerivWithin ℝ (m+1) (f i) s x)
        (L := SummationFilter.unconditional ℕ)
    rw [hcurryL]
    exact hmain
  · -- continuity of each term
    intro m hm
    have hmN : m ≤ N := by
      have h1 : ((m : ℕ∞) : WithTop ℕ∞) ≤ ((N : ℕ∞) : WithTop ℕ∞) := hm
      exact_mod_cast h1
    exact continuousOn_tsum (fun i => (hf i).continuousOn_iteratedFDerivWithin hm hU)
      (hv m hmN) (fun i x hx => h'f m i hmN x hx)

end Work.Diff.EXT
