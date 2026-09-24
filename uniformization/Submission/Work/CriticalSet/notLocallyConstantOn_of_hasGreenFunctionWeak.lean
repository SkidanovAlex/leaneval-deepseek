import Mathlib
import Submission.Work.CriticalSet.Defs
import Submission.Work.CriticalSet.Fundamentals

/-!
# A weak Green function is nowhere locally constant on the punctured surface

The main result of this file is

`Work.CriticalSet.notLocallyConstantOn_of_hasGreenFunctionWeak`:
if `E` is a weak Green function at `z₀` (positive and harmonic off `z₀`, with compact superlevel
sets `{ε ≤ E}` for `ε > 0`), the punctured surface `X ∖ {z₀}` is preconnected and `X` is
non-compact, then `E` is not eventually constant near any point of `X ∖ {z₀}`.

## The proof

Let `A = locallyConstantSet E` be the set of points where `E` is eventually constant.

* `A` is open (`isOpen_locallyConstantSet`) — this holds for any function.
* If `y ∈ X ∖ {z₀}` lies in the closure of `A`, then `y ∈ A`
  (`mem_locallyConstantSet_of_mem_closure`): near `y` the harmonic function `E` is the real part of
  a holomorphic companion `F` on a ball (`exists_analyticOnNhd_ball_re_eq_of_harmonicOnXAt`); at
  every point `z` of `A` close to `y` the derivative `F'` vanishes, so `F'` has zeros accumulating
  at `(chartAt ℂ y) y`, whence `F'` vanishes identically near `(chartAt ℂ y) y` and `F` — and so
  `E` — is locally constant near `y`
  (`Work.CriticalSet.eventually_deriv_ne_zero_of_not_eventually_re_eq`, applied contrapositively).
* Since `X ∖ {z₀}` is preconnected, `A` open, and `(closure A)ᶜ` open and disjoint from `A`, we get
  `X ∖ {z₀} ⊆ A`: `E` is locally constant at every point of the punctured surface.
* A locally constant function on a preconnected space is constant
  (`IsLocallyConstant.apply_eq_of_isPreconnected`), so `E = E x` on `X ∖ {z₀}`.
* Finally `X ∖ {z₀} ⊆ {E x ≤ E}` — a compact set, because `E x > 0` — so
  `X = (X ∖ {z₀}) ∪ {z₀}` is a union of two compact sets, i.e. `X` is compact, contradicting
  `hX`.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

noncomputable section

open Filter Set
open Classical

namespace Work.CriticalSet

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- The set of points at which `u` is eventually constant, i.e. locally constant. -/
def locallyConstantSet (u : X → ℝ) : Set X := {y : X | ∀ᶠ z in 𝓝 y, u z = u y}

theorem mem_locallyConstantSet {u : X → ℝ} {y : X} :
    y ∈ locallyConstantSet u ↔ ∀ᶠ z in 𝓝 y, u z = u y := Iff.rfl

/-- The set of points at which `u` is locally constant is open (for an arbitrary function). -/
theorem isOpen_locallyConstantSet (u : X → ℝ) : IsOpen (locallyConstantSet u) := by
  rw [isOpen_iff_mem_nhds]
  intro y hy
  rw [mem_locallyConstantSet] at hy
  obtain ⟨t, htsub, htopen, hyt⟩ := eventually_nhds_iff.mp hy
  refine Filter.mem_of_superset (htopen.mem_nhds hyt) ?_
  intro z hz
  rw [mem_locallyConstantSet]
  filter_upwards [htopen.mem_nhds hz] with w hw
  rw [htsub w hw, htsub z hz]

/-- **A harmonic function is locally the real part of a holomorphic function.**
There is a ball around `(chartAt ℂ y) y` on which the chart pullback of `u` is the real part of a
holomorphic function `F`. -/
theorem exists_analyticOnNhd_ball_re_eq_of_harmonicOnXAt {u : X → ℝ} {y : X}
    (hu : Submission.HarmonicOnXAt u y) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ F : ℂ → ℂ,
      AnalyticOnNhd ℂ F (Metric.ball ((chartAt ℂ y) y) ρ) ∧
      ∀ w ∈ Metric.ball ((chartAt ℂ y) y) ρ, (F w).re = u ((chartAt ℂ y).symm w) := by
  obtain ⟨ρ, hρ, hρsub⟩ := Metric.isOpen_iff.mp
    (InnerProductSpace.isOpen_setOfPred_harmonicAt (u ∘ (chartAt ℂ y).symm))
    ((chartAt ℂ y) y) hu
  obtain ⟨F, hF, hFre⟩ := InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq
    (f := u ∘ (chartAt ℂ y).symm) (z := (chartAt ℂ y) y) (R := ρ) (fun w hw => hρsub hw)
  exact ⟨ρ, hρ, F, hF, fun w hw => hFre hw⟩

/-- **The local-constancy set of a harmonic function is closed.**
If `u` is harmonic at `y` and `y` is a limit point of the set of points at which `u` is locally
constant, then `u` is locally constant at `y`.

Proof.  Let `F` be a holomorphic companion of `u` on a ball `B` around `(chartAt ℂ y) y`.  At any
point `z` of the local-constancy set inside `B`, the real part of `F` is eventually constant near
`(chartAt ℂ y) z`, hence `deriv F` vanishes there.  Since `y` is a limit point, these zeros
accumulate at `(chartAt ℂ y) y`, so `deriv F` cannot be eventually non-zero; by
`Work.CriticalSet.eventually_deriv_ne_zero_of_not_eventually_re_eq`, this means the real part of
`F` is eventually constant at `(chartAt ℂ y) y`, i.e. `u` is locally constant at `y`. -/
theorem mem_locallyConstantSet_of_mem_closure {u : X → ℝ} {y : X}
    (hu : Submission.HarmonicOnXAt u y) (hcl : y ∈ closure (locallyConstantSet u)) :
    y ∈ locallyConstantSet u := by
  by_contra hyA
  obtain ⟨ρ, hρ, F, hFana, hFre⟩ := exists_analyticOnNhd_ball_re_eq_of_harmonicOnXAt hu
  have hFξ : (F ((chartAt ℂ y) y)).re = u y := by
    rw [hFre _ (Metric.mem_ball_self hρ), (chartAt ℂ y).left_inv (mem_chart_source ℂ y)]
  -- it is not the case that `(F w).re` is eventually constant at `(chartAt ℂ y) y`
  have hnot : ¬ ∀ᶠ w in 𝓝 ((chartAt ℂ y) y), (F w).re = (F ((chartAt ℂ y) y)).re := by
    intro h
    apply hyA
    rw [mem_locallyConstantSet]
    have htend : Tendsto (chartAt ℂ y) (𝓝 y) (𝓝 ((chartAt ℂ y) y)) :=
      (chartAt ℂ y).continuousAt (mem_chart_source ℂ y)
    have hsrc : ∀ᶠ z in 𝓝 y, z ∈ (chartAt ℂ y).source :=
      (chartAt ℂ y).open_source.eventually_mem (mem_chart_source ℂ y)
    have hball : ∀ᶠ z in 𝓝 y, (chartAt ℂ y) z ∈ Metric.ball ((chartAt ℂ y) y) ρ :=
      htend.eventually (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hρ))
    filter_upwards [htend.eventually h, hsrc, hball] with z hz hzs hzb
    rw [← (chartAt ℂ y).left_inv hzs, ← hFre _ hzb, hz, hFξ]
  -- hence `deriv F` does not vanish eventually away from `(chartAt ℂ y) y`
  have hisol : ∀ᶠ w in 𝓝[≠] ((chartAt ℂ y) y), deriv F w ≠ 0 :=
    eventually_deriv_ne_zero_of_not_eventually_re_eq
      (hFana _ (Metric.mem_ball_self hρ)) hnot
  rw [eventually_nhdsWithin_iff] at hisol
  obtain ⟨δ, hδ, hδball⟩ := Metric.eventually_nhds_iff.mp hisol
  -- points of the local-constancy set accumulate at `y`
  have hfreq : ∃ᶠ z in 𝓝 y, z ∈ locallyConstantSet u := mem_closure_iff_frequently.mp hcl
  have hWsrc : ∀ᶠ z in 𝓝 y, z ∈ (chartAt ℂ y).source :=
    (chartAt ℂ y).open_source.eventually_mem (mem_chart_source ℂ y)
  have hWball : ∀ᶠ z in 𝓝 y,
      (chartAt ℂ y) z ∈ Metric.ball ((chartAt ℂ y) y) (min δ ρ) :=
    ((chartAt ℂ y).continuousAt (mem_chart_source ℂ y)).preimage_mem_nhds
      (Metric.ball_mem_nhds _ (lt_min hδ hρ))
  obtain ⟨z, hzA, hzs, hzc⟩ := (hfreq.and_eventually (hWsrc.and hWball)).exists
  have hzy : z ≠ y := fun h => hyA (h ▸ hzA)
  have hczball : (chartAt ℂ y) z ∈ Metric.ball ((chartAt ℂ y) y) ρ :=
    Metric.ball_subset_ball (min_le_right δ ρ) hzc
  have hczballd : (chartAt ℂ y) z ∈ Metric.ball ((chartAt ℂ y) y) δ :=
    Metric.ball_subset_ball (min_le_left δ ρ) hzc
  -- at such a point the derivative of the companion vanishes
  have hzero : deriv F ((chartAt ℂ y) z) = 0 := by
    rw [← fderiv_re_eq_zero_iff (hFana _ hczball)]
    have hev : (fun w : ℂ => (F w).re) =ᶠ[𝓝 ((chartAt ℂ y) z)] fun _ => u z := by
      have hsymm : Tendsto (chartAt ℂ y).symm (𝓝 ((chartAt ℂ y) z)) (𝓝 z) := by
        have h := (chartAt ℂ y).continuousAt_symm ((chartAt ℂ y).map_source hzs)
        simp only [ContinuousAt] at h
        rwa [(chartAt ℂ y).left_inv hzs] at h
      have h1 : ∀ᶠ w in 𝓝 ((chartAt ℂ y) z), u ((chartAt ℂ y).symm w) = u z :=
        hsymm.eventually (mem_locallyConstantSet.mp hzA)
      have h2 : ∀ᶠ w in 𝓝 ((chartAt ℂ y) z), w ∈ Metric.ball ((chartAt ℂ y) y) ρ :=
        Metric.isOpen_ball.mem_nhds hczball
      filter_upwards [h1, h2] with w hw hwb
      rw [hFre w hwb, hw]
    rw [hev.fderiv_eq]
    simp
  -- contradicting the isolation of the zeros of `deriv F`
  have hne : deriv F ((chartAt ℂ y) z) ≠ 0 :=
    hδball (Metric.mem_ball.mp hczballd)
      (fun hcon => hzy ((chartAt ℂ y).injOn hzs (mem_chart_source ℂ y) hcon))
  exact hne hzero

end Work.CriticalSet

namespace Work.CriticalSet

/-- **A Green function is nowhere locally constant on the punctured surface.**

If `E` has the weak Green function data at `z₀` (positive and harmonic off `z₀`, all superlevel sets
`{x | ε ≤ E x}` for `ε > 0` compact), the punctured surface `X ∖ {z₀}` is preconnected and `X` is not
compact, then `E` is not eventually constant near any point of `X ∖ {z₀}`; equivalently `E` is
nonconstant on every connected component of `X ∖ {z₀}`.

Proof strategy.  Write `V := punctured z₀ = univ \ {z₀}`.  Suppose `E` is eventually constant near
`x ∈ V`, say `E x = c > 0`, and put `A := {y ∈ V | ∀ᶠ z in nhds y, E z = E y}`.

* `A` is open in `X` (immediate from the definition).
* `A` is closed in `V`: if `y ∈ V` lies in the closure of `A`, take a chart ball `B` around `y`
  contained in `V` and a holomorphic companion `F` of `E` on `B`
  (`InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq`, using
  `Submission.HarmonicOnXAt_iff_chart` to see that `E ∘ (chartAt ℂ y).symm` is harmonic near
  `(chartAt ℂ y) y`).  For `z ∈ A` near `y`, `E` is eventually constant near `z`, so `F - F z` has
  real part eventually `0` near `z`, hence (commons
  `Commons.Analysis.Complex.Analytic.eventually_eq_of_re_eq_zero`) `F` is locally constant near `z`
  and `deriv F z = 0`.  Thus `deriv F` has zeros frequently near `(chartAt ℂ y) y`, so by
  `AnalyticAt.frequently_zero_iff_eventually_zero` (applied to `AnalyticAt.deriv`) `deriv F` vanishes
  on a ball, and `IsOpen.is_const_of_deriv_eq_zero` makes `F` constant there, hence `E` locally
  constant at `y`.
* Since `V` is preconnected, `A` clopen in `V` and nonempty (`x ∈ A`), we get `A = V`.  So `E` is
  locally constant at every point of `V`.
* Then `E` is constant on `V`: the set `{y ∈ V | E y = c}` is open (local constancy) and closed in
  `V` (`E` is continuous on `V`, being harmonic there), and `V` is preconnected, so it is all of `V`.
* Hence `V ⊆ {x | c ≤ E x}`, which is compact by `hE.2.2`; then `X = V ∪ {z₀}` is the union of two
  compact sets, so `X` is compact, contradicting `hX : ¬ CompactSpace X`. -/
theorem notLocallyConstantOn_of_hasGreenFunctionWeak {X : Type*} [TopologicalSpace X]
    [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] {z₀ : X} {E : X → ℝ}
    (hE : Submission.HasGreenFunctionWeak z₀ E) (hconn : IsPreconnected (punctured z₀))
    (hX : ¬ CompactSpace X) :
    NotLocallyConstantOn E (punctured z₀) := by
  intro x hx hconst
  have hxne : x ≠ z₀ := mem_punctured.mp hx
  have hharm : Submission.HarmonicOnX E (punctured z₀) := hE.2.1
  have hKcomp : ∀ ε : ℝ, 0 < ε → IsCompact {y : X | ε ≤ E y} := hE.2.2
  set A : Set X := locallyConstantSet E with hAdef
  have hAopen : IsOpen A := by rw [hAdef]; exact isOpen_locallyConstantSet E
  have hxmem : x ∈ A := by rw [hAdef]; exact hconst
  -- the local-constancy set is closed inside the punctured surface
  have hclos : ∀ y ∈ punctured z₀, y ∈ closure A → y ∈ A := by
    intro y hy hycl
    rw [hAdef] at hycl ⊢
    exact mem_locallyConstantSet_of_mem_closure (hharm y hy) hycl
  -- hence it is all of the punctured surface
  have hVA : punctured z₀ ⊆ A := by
    rcases IsPreconnected.subset_or_subset hAopen isClosed_closure.isOpen_compl
        (Set.disjoint_left.mpr fun a ha ha' => ha' (subset_closure ha))
        (fun y hy => by
          by_cases h : y ∈ A
          · exact Or.inl h
          · exact Or.inr fun hcl => h (hclos y hy hcl))
        hconn with h | h
    · exact h
    · exact absurd (subset_closure hxmem) (h hx)
  -- a locally constant function on a preconnected space is constant
  have hconstV : ∀ y ∈ punctured z₀, E y = E x := by
    have : PreconnectedSpace ↥(punctured z₀) := isPreconnected_iff_preconnectedSpace.mp hconn
    have hloc : IsLocallyConstant (fun y : ↥(punctured z₀) => E (y : X)) := by
      rw [IsLocallyConstant.iff_eventually_eq]
      intro y'
      have hy'A : (y' : X) ∈ A := hVA y'.2
      rw [hAdef] at hy'A
      exact (continuous_subtype_val.continuousAt).eventually hy'A
    intro y hy
    exact (IsLocallyConstant.apply_eq_of_isPreconnected hloc isPreconnected_univ
      (x := (⟨x, hx⟩ : ↥(punctured z₀))) (y := (⟨y, hy⟩ : ↥(punctured z₀)))
      (mem_univ _) (mem_univ _)).symm
  -- consequently `X = (X ∖ {z₀}) ∪ {z₀}` is compact
  have hcx : 0 < E x := hE.1 x hxne
  have hsub : (univ : Set X) ⊆ {y : X | E x ≤ E y} ∪ {z₀} := by
    intro y _
    by_cases hy : y = z₀
    · exact Or.inr hy
    · exact Or.inl (hconstV y (mem_punctured.mpr hy)).ge
  exact hX (isCompact_univ_iff.mp
    (IsCompact.of_isClosed_subset ((hKcomp (E x) hcx).union isCompact_singleton)
      isClosed_univ hsub))

end Work.CriticalSet
