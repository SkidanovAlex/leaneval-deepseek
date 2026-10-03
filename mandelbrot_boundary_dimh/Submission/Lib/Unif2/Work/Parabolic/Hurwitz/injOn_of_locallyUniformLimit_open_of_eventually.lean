import Mathlib
import Submission.Lib.Unif2.Commons.Analysis.Complex.Analytic.injOn_of_locallyUniformLimit_open

/-!
# Hurwitz's theorem for locally uniform limits, with *eventually* analytic data

`Commons.Analysis.Complex.Analytic.injOn_of_locallyUniformLimit_open` states the Hurwitz-type
injectivity theorem for locally uniform limits of analytic functions on a `ℂ`-charted space when
the members of the sequence are analytic *everywhere* and injective on an open set `U` *along the
whole sequence*.  The version here weakens both hypotheses to an *eventual* statement
(`∀ᶠ n in atTop, …`), and assumes analyticity only at the points of `U`, which is what the
applications in this repository produce (e.g. after extracting a subsequence from a normal family).

The reduction is:

* pick `N` beyond which both the analyticity and the injectivity hold and replace the sequence
  `f` by the sequence `H n = if n < N then f N else f n`.  Then `H` satisfies the strong
  hypotheses of the Hurwitz theorem and converges locally uniformly to the same limit `g`;
* view the open set `U` as a `ℂ`-charted space, with the chart at `x` the restriction of the chart
  of `X` at `x` (obtained by composing the singleton charted space structure of the open embedding
  `U ↪ X` with the charted space structure of `X` over `ℂ`);
* the Hurwitz theorem on that charted space gives injectivity of `g` on `U`.
-/

open Filter Metric Set
open scoped Topology

namespace Work.Parabolic.Hurwitz

theorem injOn_of_locallyUniformLimit_open_of_eventually {X : Type*} [TopologicalSpace X] [T2Space X]
    [ChartedSpace ℂ X] {f : ℕ → X → ℂ} {g : X → ℂ} {U : Set X} (hU : IsOpen U)
    (hf : ∀ᶠ n in Filter.atTop, ∀ x ∈ U,
        AnalyticAt ℂ (f n ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x))
    (hg : ∀ x, AnalyticAt ℂ (g ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x))
    (hconv : TendstoLocallyUniformlyOn f g Filter.atTop Set.univ)
    (hinj : ∀ᶠ n in Filter.atTop, Set.InjOn (f n) U)
    (hloc : ∀ x ∈ U, ¬ Filter.Eventually (fun y => g y = g x) (nhds x)) :
    Set.InjOn g U := by
  by_cases hne : Nonempty U
  swap
  · intro a ha
    exact absurd ⟨a, ha⟩ hne
  haveI : Nonempty U := hne
  -- Replace the sequence by one whose members are analytic on `U` and injective on `U`
  -- for *every* index.
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp hinj
  obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.mp hf
  set N : ℕ := max N₁ N₂ with hNdef
  have hNlea : N₁ ≤ N := le_max_left _ _
  have hNleb : N₂ ≤ N := le_max_right _ _
  let H : ℕ → X → ℂ := fun n => if n < N then f N else f n
  have hH_analytic : ∀ n, ∀ x ∈ U,
      AnalyticAt ℂ (H n ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) := by
    intro n x hx
    by_cases hn : n < N
    · simpa [H, hn] using hN₂ N hNleb x hx
    · simpa [H, hn] using hN₂ n (le_trans hNleb (le_of_not_gt hn)) x hx
  have hH_inj : ∀ n, Set.InjOn (H n) U := by
    intro n
    by_cases hn : n < N
    · simpa [H, hn] using hN₁ N hNlea
    · simpa [H, hn] using hN₁ n (le_trans hNlea (le_of_not_gt hn))
  have hH_conv : TendstoLocallyUniformlyOn H g Filter.atTop Set.univ :=
    hconv.congr_inseparable (by
      filter_upwards [Filter.eventually_ge_atTop N] with n hn x _
      exact Inseparable.of_eq (by simp [H, not_lt.mpr hn]))
  -- View `U` as a `ℂ`-charted space: its charts are the restrictions of the charts of `X`.
  let h : Topology.IsOpenEmbedding (Subtype.val : U → X) := hU.isOpenEmbedding_subtypeVal
  letI : ChartedSpace X U := h.singletonChartedSpace
  letI : ChartedSpace ℂ U := ChartedSpace.comp ℂ X U
  let e : OpenPartialHomeomorph U X := h.toOpenPartialHomeomorph Subtype.val
  have he_apply : ∀ y : U, e y = y.val := fun y => by
    rw [Topology.IsOpenEmbedding.toOpenPartialHomeomorph_apply]
  have hechart : ∀ x : U, (chartAt X x : OpenPartialHomeomorph U X) = e := fun x => by
    rw [OpenPartialHomeomorph.singletonChartedSpace_chartAt_eq]
  -- In the chart of `U` at `y` (which is the restriction of the chart of `X` at `y`),
  -- analyticity of a function on `U` is analyticity of its extension in the chart of `X`.
  have transfer : ∀ (F : X → ℂ) (y : U),
      AnalyticAt ℂ (F ∘ (chartAt ℂ (y : X)).symm) ((chartAt ℂ (y : X)) y) →
      AnalyticAt ℂ ((fun z : U => F z.val) ∘ (chartAt ℂ y).symm) ((chartAt ℂ y) y) := by
    intro F y hFy
    let fchart : OpenPartialHomeomorph X ℂ := chartAt ℂ (y : X)
    have hcx : (chartAt ℂ y : OpenPartialHomeomorph U ℂ) = e.trans fchart := by
      rw [chartAt_comp, hechart y]; rfl
    have hpt : ((chartAt ℂ y : OpenPartialHomeomorph U ℂ) y) = fchart (y : X) := by
      rw [hcx, OpenPartialHomeomorph.trans_apply, he_apply]
    have heq : (F ∘ fchart.symm) =ᶠ[𝓝 ((chartAt ℂ y) y)]
        ((fun z : U => F z.val) ∘ (chartAt ℂ y).symm) := by
      have h1 : (chartAt ℂ y : OpenPartialHomeomorph U ℂ).target ∈ 𝓝 ((chartAt ℂ y) y) :=
        (chartAt ℂ y).open_target.mem_nhds (mem_chart_target ℂ y)
      have h2 : fchart.target ∈ 𝓝 ((chartAt ℂ y) y) := by
        rw [hpt]; exact fchart.open_target.mem_nhds (mem_chart_target ℂ (y : X))
      filter_upwards [h1, h2] with z hz1 hz2
      show F (fchart.symm z) = F ((chartAt ℂ y).symm z).val
      congr 1
      have hzsrc : ((chartAt ℂ y).symm z).val ∈ fchart.source := by
        have hmem : (chartAt ℂ y).symm z ∈ (chartAt ℂ y).source := (chartAt ℂ y).map_target hz1
        rw [hcx, OpenPartialHomeomorph.trans_source] at hmem
        have h2' : e ((e.trans fchart).symm z) ∈ fchart.source := hmem.2
        rwa [he_apply] at h2'
      have hsymsrc : fchart.symm z ∈ fchart.source := fchart.map_target hz2
      have hzcast : (chartAt ℂ y) ((chartAt ℂ y).symm z) = fchart ((chartAt ℂ y).symm z).val := by
        rw [hcx, OpenPartialHomeomorph.trans_apply, he_apply]
      have hfin : fchart ((chartAt ℂ y).symm z).val = fchart (fchart.symm z) := by
        rw [fchart.right_inv hz2, ← hzcast]
        exact OpenPartialHomeomorph.right_inv (chartAt ℂ y) hz1
      exact (fchart.injOn hzsrc hsymsrc hfin).symm
    rw [hpt]
    exact hFy.congr heq
  have hHf' : ∀ (n : ℕ) (x : U),
      AnalyticAt ℂ ((fun y : U => H n y.val) ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) :=
    fun n x => transfer (H n) x (hH_analytic n x.val x.2)
  have hHg' : ∀ (x : U),
      AnalyticAt ℂ ((fun y : U => g y.val) ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) :=
    fun x => transfer g x (hg x.val)
  have hHconv' : TendstoLocallyUniformlyOn (fun n (y : U) => H n y.val)
      (fun y : U => g y.val) Filter.atTop Set.univ :=
    hH_conv.comp Subtype.val (Set.mapsTo_univ _ _) continuous_subtype_val.continuousOn
  have hHinj' : ∀ᶠ n in Filter.atTop, Set.InjOn (fun y : U => H n y.val) Set.univ :=
    Filter.Eventually.of_forall fun n a _ b _ hab => Subtype.ext (hH_inj n a.2 b.2 hab)
  -- `g` is nowhere locally constant, also when viewed on `U` (the coercions `U → X` being open,
  -- a `U`-neighbourhood of `x` is an `X`-neighbourhood of `x`).
  have hloc' : ∀ x : U, ¬ Filter.Eventually (fun y : U => g y.val = g x.val) (nhds x) := by
    intro x hx
    apply hloc x.val x.2
    have hmap : Filter.map Subtype.val (𝓝 x) = 𝓝 (x : X) :=
      hU.isOpenEmbedding_subtypeVal.map_nhds_eq x
    have hx' : ∀ᶠ z in Filter.map Subtype.val (𝓝 x), g z = g x.val :=
      Filter.eventually_map.mpr hx
    rwa [hmap] at hx'
  have hmain : Set.InjOn (fun y : U => g y.val) Set.univ :=
    Commons.Analysis.Complex.Analytic.injOn_of_locallyUniformLimit_open
      (U := Set.univ) isOpen_univ hHf' hHg' hHconv' hHinj' (fun x _ => hloc' x)
  intro a ha b hb hab
  have h2 : (⟨a, ha⟩ : U) = ⟨b, hb⟩ := hmain (mem_univ _) (mem_univ _) (by simpa using hab)
  exact congrArg Subtype.val h2

end Work.Parabolic.Hurwitz
