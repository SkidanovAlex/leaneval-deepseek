import Mathlib.Geometry.Manifold.VectorField.LieBracket
import Mathlib.Order.CompletePartialOrder

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.Geometry.Manifold.VectorField

open scoped _root_.Manifold _root_.ContDiff Topology
open _root_.VectorField
open Set

noncomputable section

/-! ## Helper lemmas for `mvfderivWithin_apply_mlieBracketWithin`

The main theorem is the manifold-level statement that the second directional
derivatives along vector fields commute up to the Lie bracket, *within* a set `s`:
`X(Yf) − Y(Xf) = [X,Y]f`.  We reduce it to its vector-space counterpart
(`fderivWithin_apply_lieBracket`, already in Mathlib) by chart-localising
everything at the basepoint `x`. -/

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- The vector-space (model-space) version of the within-set second-derivative identity. -/
lemma fderivWithin_apply_lieBracketWithin_add
    {f : E → F} {X Y : E → E} {s : Set E} {x : E}
    (hX : DifferentiableWithinAt ℝ X s x) (hY : DifferentiableWithinAt ℝ Y s x)
    (hf2 : ContDiffWithinAt ℝ 2 f s x) (hs : UniqueDiffOn ℝ s)
    (hxs' : x ∈ closure (interior s)) (hxs : x ∈ s) :
    fderivWithin ℝ (fun y : E => fderivWithin ℝ f s y (Y y)) s x (X x) =
      fderivWithin ℝ (fun y : E => fderivWithin ℝ f s y (X y)) s x (Y x)
        + fderivWithin ℝ f s x (VectorField.lieBracketWithin ℝ X Y s x) := by
  have h := VectorField.fderivWithin_apply_lieBracket (𝕜 := ℝ) (E := E) (F := F)
    (f := f) (V := X) (W := Y) (s := s) (x := x) (n := 2) hf2 (by simp) hs hxs' hxs hY hX
  calc
    (fderivWithin ℝ (fun y => fderivWithin ℝ f s y (Y y)) s x (X x))
        = ((fderivWithin ℝ (fun y => fderivWithin ℝ f s y (Y y)) s x (X x))
            - (fderivWithin ℝ (fun y => fderivWithin ℝ f s y (X y)) s x (Y x)))
          + (fderivWithin ℝ (fun y => fderivWithin ℝ f s y (X y)) s x (Y x)) := by abel
    _ = (fderivWithin ℝ f s x (lieBracketWithin ℝ X Y s x))
          + (fderivWithin ℝ (fun y => fderivWithin ℝ f s y (X y)) s x (Y x)) := by
          rw [h]
    _ = _ := by abel

/-- In the model space `E`, `mvfderivWithin` of a vector-valued function coincides with the
usual `fderivWithin`. -/
lemma mvfderivWithin_model_eq_fderivWithin {g : E → F} {t : Set E} {p : E}
    (hg : MDiffAt[t] g p) :
    mvfderivWithin 𝓘(ℝ, E) g t p = fderivWithin ℝ g t p := by
  have hf := MDifferentiableWithinAt.mvfderivWithin (𝕜 := ℝ) (I := 𝓘(ℝ, E)) (E' := F) hg
  simpa [writtenInExtChartAt, chartAt_self_eq] using hf

/-- For a function into a normed space, `mvfderivWithin` only depends on the values of the
function on a set which is eventually equal to the given one. -/
lemma mvfderivWithin_congr_eventually {g g₁ : M → F} {s : Set M} {x : M}
    (hL : g₁ =ᶠ[𝓝[s] x] g) (hx : g₁ x = g x) :
    mvfderivWithin I g₁ s x = mvfderivWithin I g s x := by
  unfold mvfderivWithin
  rw [hx]
  rw [Filter.EventuallyEq.mfderivWithin_eq (I := I) (I' := 𝓘(ℝ, F)) hL hx]
  -- v4.34: unfolding leaves `tangentSpaceCast (g x) (g₁ x)`, definitionally the identity.
  all_goals first | rfl | (ext v; rfl)

lemma mvfderivWithin_congr_eventually_of_mem {g g₁ : M → F} {s : Set M} {x : M}
    (hL : g₁ =ᶠ[𝓝[s] x] g) (hx : x ∈ s) :
    mvfderivWithin I g₁ s x = mvfderivWithin I g s x :=
  mvfderivWithin_congr_eventually hL (mem_of_mem_nhdsWithin hx hL :)

/-- Intersecting the set with a neighborhood of the basepoint does not change the value of
`mvfderivWithin`. -/
lemma mvfderivWithin_inter {f : M → F} {s t : Set M} {x : M} (ht : t ∈ 𝓝 x) :
    mvfderivWithin I f (s ∩ t) x = mvfderivWithin I f s x := by
  unfold mvfderivWithin
  rw [mfderivWithin_inter ht]

/-- `mvfderivWithin` only depends on the set through its germ at the basepoint. -/
lemma mvfderivWithin_congr_set {f : M → F} {s t : Set M} {x : M}
    (h : s =ᶠ[𝓝 x] t) :
    mvfderivWithin I f s x = mvfderivWithin I f t x := by
  unfold mvfderivWithin
  rw [mfderivWithin_congr_set h]

/-- The chart formula for `mvfderivWithin` of a vector-valued function. -/
lemma mvfderivWithin_eq_fderivWithin_chart {f : M → F} {s : Set M} {x : M}
    (hf : MDiffAt[s] f x) :
    mvfderivWithin I f s x =
      fderivWithin ℝ (f ∘ (extChartAt I x).symm)
        ((extChartAt I x).symm ⁻¹' s ∩ range I) (extChartAt I x x) := by
  have hf' := MDifferentiableWithinAt.mvfderivWithin (𝕜 := ℝ) (I := I) (E' := F) hf
  simpa [writtenInExtChartAt, chartAt_self_eq] using hf'

/-- Chain rule for `mvfderivWithin` applied to a vector-valued function composed with a
manifold-valued map. -/
lemma mvfderivWithin_comp_apply_vec {f : M → E} {g : E → F} {s : Set M} {u : Set E} {x : M}
    (hg : MDiffAt[u] g (f x)) (hf : MDiffAt[s] f x) (h : s ⊆ f ⁻¹' u)
    (hxs : UniqueMDiffAt[s] x) (v : TangentSpace I x) :
    mvfderivWithin I (g ∘ f) s x v =
      (mvfderivWithin 𝓘(ℝ, E) g u (f x)) ((mfderiv[s] f x) v) := by
  unfold mvfderivWithin
  rw [mfderivWithin_comp x hg hf h hxs]
  rfl

section IsManifold1

variable [IsManifold I ∞ M] [CompleteSpace E]

/-- The derivative of the extended chart within a set is the inverse of the derivative of the
inverse chart, using any set with the unique-differentiability property. -/
lemma mfderivWithin_extChartAt_eq_inverse {x : M} {s' : Set M} {y : M}
    (hys : y ∈ (extChartAt I x).source) (hs' : UniqueMDiffAt[s'] y) :
    mfderiv[s'] (extChartAt I x) y =
      (mfderiv[range I] (extChartAt I x).symm (extChartAt I x y)).inverse := by
  have hys' : y ∈ (chartAt H x).source := by rwa [extChartAt_source] at hys
  rw [mfderivWithin_eq_mfderiv hs' (mdifferentiableAt_extChartAt hys')]
  exact (ContinuousLinearMap.inverse_eq
    (f := mfderiv[range I] (extChartAt I x).symm (extChartAt I x y))
    (g := mfderiv% (extChartAt I x) y)
    (mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt' hys)
    (mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm' hys)).symm


/-- Pointwise form of the chart reduction of the inner first derivative:
for every point `y` of `s` in the chart source, `mvfderivWithin I f s y (Yin y)` computed on `M`
equals the model derivative of the chart-written function `f ∘ φ⁻¹` applied to the chart-pushforward
of `Yin y`. -/
lemma mvfderivWithin_pullback_apply {f : M → F} {Yin : Π y : M, TangentSpace I y}
    {s : Set M} {x : M} (hs : UniqueMDiff[s]) (hf : CMDiff[s] ∞ f)
    {y : M} (hys : y ∈ s) (hyΩ : y ∈ (extChartAt I x).source) :
    mvfderivWithin I f s y (Yin y) =
      fderivWithin ℝ (f ∘ (extChartAt I x).symm)
        ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s) ((extChartAt I x) y)
        (mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x).symm Yin (range I) ((extChartAt I x) y)) := by
  have hΩ : (extChartAt I x).source ∈ 𝓝 y := (isOpen_extChartAt_source x).mem_nhds hyΩ
  have hys' : y ∈ (chartAt H x).source := by rwa [extChartAt_source] at hyΩ
  -- reduce the set to `s ∩ φ.source`
  rw [← mvfderivWithin_inter (f := f) (s := s) (t := (extChartAt I x).source) (x := y) hΩ]
  -- replace `f` by `f ∘ φ⁻¹ ∘ φ` on this set
  have hfun : f =ᶠ[𝓝[s ∩ (extChartAt I x).source] y]
      ((f ∘ (extChartAt I x).symm) ∘ (extChartAt I x)) :=
    Filter.eventuallyEq_of_mem self_mem_nhdsWithin (fun z hz => by
      simp only [Function.comp_apply]
      rw [(extChartAt I x).left_inv hz.2])
  rw [mvfderivWithin_congr_eventually_of_mem (g := (f ∘ (extChartAt I x).symm) ∘ (extChartAt I x))
    hfun ⟨hys, hyΩ⟩]
  -- the model function is differentiable within `w`
  have hcont : ContDiffWithinAt ℝ ∞ (f ∘ (extChartAt I x).symm)
      ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s) ((extChartAt I x) y) := by
    have h := (contMDiffWithinAt_iff_of_mem_source' (I := I) (I' := 𝓘(ℝ, F))
      (M := M) (M' := F) (x := x) (x' := y) (y := f y) (f := f) (s := s) hys' (by simp)).1
      (hf y hys)
    simpa [chartAt_self_eq] using h.2
  have hg_diff : MDiffAt[(extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s]
      (f ∘ (extChartAt I x).symm) ((extChartAt I x) y) :=
    (hcont.contMDiffWithinAt).mdifferentiableWithinAt (by simp)
  have hφ_diff : MDiffAt[s ∩ (extChartAt I x).source] (extChartAt I x) y :=
    (mdifferentiableAt_extChartAt hys').mdifferentiableWithinAt
  have hsub : s ∩ (extChartAt I x).source ⊆ (extChartAt I x) ⁻¹' ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s) :=
    fun z hz => ⟨(extChartAt I x).map_source hz.2, by
      show (extChartAt I x).symm ((extChartAt I x) z) ∈ s
      rw [(extChartAt I x).left_inv hz.2]; exact hz.1⟩
  have hy_s₀ : UniqueMDiffAt[s ∩ (extChartAt I x).source] y :=
    UniqueMDiffWithinAt.inter (hs y hys) hΩ
  rw [mvfderivWithin_comp_apply_vec (f := extChartAt I x) (g := f ∘ (extChartAt I x).symm)
    (s := s ∩ (extChartAt I x).source) (u := (extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s)
    (x := y) hg_diff hφ_diff hsub hy_s₀ (Yin y)]
  rw [mvfderivWithin_model_eq_fderivWithin hg_diff]
  congr 1
  rw [mfderivWithin_extChartAt_eq_inverse hyΩ hy_s₀]
  simp only [mpullbackWithin_apply]
  rw [(extChartAt I x).left_inv hyΩ]


/-- An `∞`-smooth vector field on `M` pulls back along the chart to an `∞`-smooth function on the
model space. -/
lemma contDiffWithinAt_pullback_field {Xv : Π y : M, TangentSpace I y}
    {s : Set M} {x : M} (hX : CMDiff[s] ∞ (T% Xv)) (hs : UniqueMDiff[s]) (hxs : x ∈ s) :
    ContDiffWithinAt ℝ 1
      (fun z : E => mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x).symm Xv (range I) z)
      ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s) ((extChartAt I x) x) := by
  have hle1 : (1 : ℕ∞ω) ≤ ∞ := WithTop.coe_le_coe.mpr (le_top : (1 : ℕ∞) ≤ ⊤)
  have hle : (1 : ℕ∞ω) + 1 ≤ ∞ := by
    have h2 : ((1 : ℕ∞ω) + 1) = (2 : ℕ∞ω) := by norm_num
    rw [h2]; exact WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤)
  have h := VectorField.contMDiffWithinAt_mpullbackWithin_extChartAt_symm (𝕜 := ℝ) (I := I)
    ((hX x hxs).of_le hle1) hs hxs (m := 1) (n := ∞) hle
  exact (contMDiffWithinAt_vectorSpace_iff_contDiffWithinAt (𝕜 := ℝ) (E := E) (n := 1)
    (V := fun z : E => mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x).symm Xv (range I) z)
    (s := (extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s) (x := (extChartAt I x) x)).1
    (by simpa using h)

/-- The chart-written form of a smooth function on `M` is smooth on the model space. -/
lemma contDiffWithinAt_chart_written {f : M → F} {s : Set M} {x : M}
    (hf : CMDiff[s] ∞ f) (hxs : x ∈ s) :
    ContDiffWithinAt ℝ ∞ (f ∘ (extChartAt I x).symm)
      ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s) ((extChartAt I x) x) := by
  have h := (contMDiffWithinAt_iff_of_mem_source' (I := I) (I' := 𝓘(ℝ, F))
    (M := M) (M' := F) (x := x) (x' := x) (y := f x) (f := f) (s := s)
    (ChartedSpace.mem_chart_source x) (by simp)).1 (hf x hxs)
  simpa [chartAt_self_eq] using h.2

/-- Eventual form of the chart reduction of the inner first derivative. -/
lemma mvfderivWithin_second_eventuallyEq {f : M → F} {Yin : Π y : M, TangentSpace I y}
    {s : Set M} {x : M} (hs : UniqueMDiff[s]) (hxs : x ∈ s)
    (hf : CMDiff[s] ∞ f) (hYin : CMDiff[s] ∞ (T% Yin)) :
    (fun y => mvfderivWithin I f s y (Yin y)) =ᶠ[𝓝[s] x]
      (fun y => fderivWithin ℝ (f ∘ (extChartAt I x).symm)
        ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s) ((extChartAt I x) y)
        (mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x).symm Yin (range I) ((extChartAt I x) y))) := by
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (extChartAt_source_mem_nhds (I := I) x)] with y hys hyΩ
  exact mvfderivWithin_pullback_apply hs hf hys hyΩ

/-- Main chart reduction of the outer (second) derivative term. -/
lemma mvfderivWithin_second_chart {f : M → F} {Xv Yin : Π y : M, TangentSpace I y}
    {s : Set M} {x : M} (hs : UniqueMDiff[s]) (hxs : x ∈ s)
    (hxs' : x ∈ closure (interior s))
    (hf : CMDiff[s] ∞ f) (hYin : CMDiff[s] ∞ (T% Yin)) :
    mvfderivWithin I (fun y => mvfderivWithin I f s y (Yin y)) s x (Xv x)
      = fderivWithin ℝ
          (fun z => fderivWithin ℝ (f ∘ (extChartAt I x).symm)
            ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s) z
            (mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x).symm Yin (range I) z))
          ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s) ((extChartAt I x) x)
          (mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x).symm Xv (range I) ((extChartAt I x) x)) := by
  let H : E → F := fun z => fderivWithin ℝ (f ∘ (extChartAt I x).symm)
      ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s) z
      (mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x).symm Yin (range I) z)
  have hInner : (fun y => mvfderivWithin I f s y (Yin y)) =ᶠ[𝓝[s] x]
      (fun y => H ((extChartAt I x) y)) := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (extChartAt_source_mem_nhds (I := I) x)] with y hys hyΩ
    exact mvfderivWithin_pullback_apply hs hf hys hyΩ
  rw [mvfderivWithin_congr_eventually_of_mem (g := fun y => H ((extChartAt I x) y)) hInner hxs]
  have hΩ : (extChartAt I x).source ∈ 𝓝 x :=
    (isOpen_extChartAt_source x).mem_nhds (mem_extChartAt_source x)
  rw [← mvfderivWithin_inter (f := fun y => H ((extChartAt I x) y)) (s := s)
    (t := (extChartAt I x).source) (x := x) hΩ]
  have hw_unique : UniqueDiffOn ℝ ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s) :=
    hs.uniqueDiffOn_target_inter x
  have hxs_w : (extChartAt I x) x ∈ (extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s := by
    refine ⟨mem_extChartAt_target x, ?_⟩
    show (extChartAt I x).symm ((extChartAt I x) x) ∈ s
    rw [(extChartAt I x).left_inv (mem_extChartAt_source x)]
    exact hxs
  have hf'2 : ContDiffWithinAt ℝ 2 (f ∘ (extChartAt I x).symm)
      ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s) ((extChartAt I x) x) :=
    (contDiffWithinAt_chart_written hf hxs).of_le
      (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
  have hc : DifferentiableWithinAt ℝ
      (fun z => fderivWithin ℝ (f ∘ (extChartAt I x).symm)
        ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s) z)
      ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s) ((extChartAt I x) x) :=
    (hf'2.fderivWithin_right hw_unique (by norm_num) hxs_w).differentiableWithinAt one_ne_zero
  have hY'diff : DifferentiableWithinAt ℝ
      (fun z : E => mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x).symm Yin (range I) z)
      ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s) ((extChartAt I x) x) :=
    (contDiffWithinAt_pullback_field hYin hs hxs).differentiableWithinAt one_ne_zero
  have hHdiff' : DifferentiableWithinAt ℝ H
      ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s) ((extChartAt I x) x) :=
    hc.clm_apply hY'diff
  have hHdiff : MDiffAt[(extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s] H
      ((extChartAt I x) x) :=
    DifferentiableWithinAt.mdifferentiableWithinAt_of_comp_extChartAt_symm (I := 𝓘(ℝ, E))
      (x := (extChartAt I x) x) (by simpa [chartAt_self_eq] using hHdiff')
  have hφdiff : MDiffAt[s ∩ (extChartAt I x).source] (extChartAt I x) x :=
    (mdifferentiableAt_extChartAt (ChartedSpace.mem_chart_source x)).mdifferentiableWithinAt
  have hsub : s ∩ (extChartAt I x).source
      ⊆ (extChartAt I x) ⁻¹' ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s) :=
    fun z hz => ⟨(extChartAt I x).map_source hz.2, by
      show (extChartAt I x).symm ((extChartAt I x) z) ∈ s
      rw [(extChartAt I x).left_inv hz.2]; exact hz.1⟩
  have hx_s₀ : UniqueMDiffAt[s ∩ (extChartAt I x).source] x :=
    UniqueMDiffWithinAt.inter (hs x hxs) hΩ
  change mvfderivWithin I (H ∘ (extChartAt I x)) (s ∩ (extChartAt I x).source) x (Xv x)
      = (fderivWithin ℝ H ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s)
          ((extChartAt I x) x))
        (mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x).symm Xv (range I) ((extChartAt I x) x))
  rw [mvfderivWithin_comp_apply_vec (f := extChartAt I x) (g := H)
    (s := s ∩ (extChartAt I x).source) (u := (extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s)
    (x := x) hHdiff hφdiff hsub hx_s₀ (Xv x)]
  rw [mvfderivWithin_model_eq_fderivWithin hHdiff]
  suffices h : (mfderiv[s ∩ (extChartAt I x).source] (extChartAt I x) x) (Xv x)
      = mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x).symm Xv (range I) ((extChartAt I x) x) by
    rw [h]
    rfl
  rw [mfderivWithin_extChartAt_eq_inverse (mem_extChartAt_source x) hx_s₀,
    mpullbackWithin_apply, (extChartAt I x).left_inv (mem_extChartAt_source x),
    mfderivWithin_range_extChartAt_symm]


/-- Chart reduction of the bracket term. -/
lemma mvfderivWithin_mlieBracketWithin_chart {f : M → F} {Xv Yv : Π y : M, TangentSpace I y}
    {s : Set M} {x : M} (hf : CMDiff[s] ∞ f) (hxs : x ∈ s) :
    mvfderivWithin I f s x (mlieBracketWithin I Xv Yv s x)
      = fderivWithin ℝ (f ∘ (extChartAt I x).symm)
          ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s) ((extChartAt I x) x)
          (lieBracketWithin ℝ
            (fun z : E => mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x).symm Xv (range I) z)
            (fun z : E => mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x).symm Yv (range I) z)
            ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s) ((extChartAt I x) x)) := by
  have hf_diff : MDiffAt[s] f x := (hf x hxs).mdifferentiableWithinAt (by simp)
  rw [mvfderivWithin_eq_fderivWithin_chart hf_diff]
  have hbracket : mlieBracketWithin I Xv Yv s x
      = lieBracketWithin ℝ
          (fun z : E => mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x).symm Xv (range I) z)
          (fun z : E => mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x).symm Yv (range I) z)
          ((extChartAt I x).symm ⁻¹' s ∩ range I) ((extChartAt I x) x) := by
    rw [VectorField.mlieBracketWithin_apply]
    have h1 : (mfderiv% (extChartAt I x) x).inverse
        = (ContinuousLinearMap.id ℝ (TangentSpace 𝓘(ℝ, E) ((extChartAt I x) x))) := by
      rw [mfderiv_extChartAt_self]
      exact ContinuousLinearMap.inverse_id
    rw [h1]
    rfl
  rw [hbracket]
  have hset : ((extChartAt I x).symm ⁻¹' s ∩ range I : Set E)
      =ᶠ[𝓝 ((extChartAt I x) x)] ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s : Set E) := by
    filter_upwards [extChartAt_target_eventuallyEq (I := I) (x := x)] with z hz
    apply propext
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨Eq.mp hz.symm h2, h1⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h2, Eq.mp hz h1⟩
  have hL : lieBracketWithin ℝ
        (fun z : E => mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x).symm Xv (range I) z)
        (fun z : E => mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x).symm Yv (range I) z)
        ((extChartAt I x).symm ⁻¹' s ∩ range I) ((extChartAt I x) x)
      = lieBracketWithin ℝ
        (fun z : E => mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x).symm Xv (range I) z)
        (fun z : E => mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x).symm Yv (range I) z)
        ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s) ((extChartAt I x) x) :=
    lieBracketWithin_congr_set
      (V := fun z : E => (mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x).symm Xv (range I) z : E))
      (W := fun z : E => (mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x).symm Yv (range I) z : E)) hset
  rw [fderivWithin_congr_set hset, hL]
  rfl


end IsManifold1


/-- Second directional derivatives along vector fields commute up to the Lie bracket,
within a set `s`: `X(Yf) - Y(Xf) = [X,Y]f` at a point, expressed with `mvfderivWithin`.
Here `X f := fun x => mvfderivWithin I f s x (X x)`. -/
theorem mvfderivWithin_apply_mlieBracketWithin
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {f : M → F} {X Y : Π x : M, TangentSpace I x} {s : Set M} {x : M}
    (hs : UniqueMDiff[s]) (hxs : x ∈ s) (hxs' : x ∈ closure (interior s))
    (hf : CMDiff[s] ∞ f) (hX : CMDiff[s] ∞ (T% X)) (hY : CMDiff[s] ∞ (T% Y)) :
    mvfderivWithin I (fun y : M => mvfderivWithin I f s y (Y y)) s x (X x) =
      mvfderivWithin I (fun y : M => mvfderivWithin I f s y (X y)) s x (Y x)
        + mvfderivWithin I f s x (VectorField.mlieBracketWithin I X Y s x) := by
  -- hypotheses for the model-space identity
  have hw_unique : UniqueDiffOn ℝ ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s) :=
    hs.uniqueDiffOn_target_inter x
  have hp0w : (extChartAt I x) x ∈ (extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s := by
    refine ⟨mem_extChartAt_target x, ?_⟩
    show (extChartAt I x).symm ((extChartAt I x) x) ∈ s
    rw [(extChartAt I x).left_inv (mem_extChartAt_source x)]
    exact hxs
  have hp0w' : (extChartAt I x) x ∈
      closure (interior ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s)) := by
    simpa only [Set.inter_comm] using
      extChartAt_mem_closure_interior hxs' (mem_extChartAt_source x)
  have hf'2 : ContDiffWithinAt ℝ 2 (f ∘ (extChartAt I x).symm)
      ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s) ((extChartAt I x) x) :=
    (contDiffWithinAt_chart_written hf hxs).of_le
      (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
  have hX'' : DifferentiableWithinAt ℝ
      (fun z : E => (mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x).symm X (range I) z : E))
      ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s) ((extChartAt I x) x) :=
    (contDiffWithinAt_pullback_field hX hs hxs).differentiableWithinAt one_ne_zero
  have hY'' : DifferentiableWithinAt ℝ
      (fun z : E => (mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x).symm Y (range I) z : E))
      ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s) ((extChartAt I x) x) :=
    (contDiffWithinAt_pullback_field hY hs hxs).differentiableWithinAt one_ne_zero
  have hmodel := fderivWithin_apply_lieBracketWithin_add
    (f := f ∘ (extChartAt I x).symm)
    (X := fun z : E => (mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x).symm X (range I) z : E))
    (Y := fun z : E => (mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x).symm Y (range I) z : E))
    (s := (extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s) (x := (extChartAt I x) x)
    hX'' hY'' hf'2 hw_unique hp0w' hp0w
  have hLHS := mvfderivWithin_second_chart (Xv := X) (Yin := Y) hs hxs hxs' hf hY
  have hRHS1 := mvfderivWithin_second_chart (Xv := Y) (Yin := X) hs hxs hxs' hf hX
  have hRHS2 := mvfderivWithin_mlieBracketWithin_chart (Xv := X) (Yv := Y) hf hxs
  rw [hLHS, hRHS1, hRHS2]
  exact hmodel

end

end Commons.Geometry.Manifold.VectorField