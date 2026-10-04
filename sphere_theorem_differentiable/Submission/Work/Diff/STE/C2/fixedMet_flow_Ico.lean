/-
# `Work.Diff.STE.C2.fixedMet_flow_Ico`

The first variation of the **pull-back of a fixed metric along a flow**, for the time set
`Set.Ico a b`:

`d/ds ⟨dφ_s u, dφ_s v⟩_{g} = ⟨∇_{Y_t}(dφ_t u), dφ_t v⟩_{g} + ⟨dφ_t u, ∇_{Y_t}(dφ_t v)⟩_{g}`

at every `t ∈ Set.Ico a b`, i.e. `∂_s (φ_s^* g) = φ_s^*(L_{Y_s} g)` with the Lie derivative of a
metric written with the (torsion-free, metric compatible) Levi-Civita connection `lcOf g` of `hLC`.

This is the interval form of `Work.Diff.STE.C2.hasDerivWithinAt_fixedMet_flow` (the statement with
an arbitrary time set `J`).  The proof is the one of `Work.Diff.STE.C2.fixedMet_flow_hvar`, but the
Clairaut step is taken from the workspace's proved one-sided Clairaut lemma
`Work.Diff.STE.C2.within_slice_clairaut`, transported from `Set.Icc a b` to `Set.Ico a b` (the two
sets have the same within-germ at every point of `Set.Ico a b`, and `Set.Ico a b` is still a
`UniqueDiffOn` set whose points lie in the closure of its interior, so the symmetry of the second
derivative `ContDiffWithinAt.isSymmSndFDerivWithinAt` applies verbatim).

## Route

In the chart at `p := φ t x`,

* the `p`-frame coordinate of `mfderiv I I (φ s) x u` is the `fderiv` of the charted flow
  `y ↦ χ_p (φ s (χ_x^{-1} y))` (`frameVector_coord_eq`), and its `s`-derivative at `t` is the
  `Y t`-coordinate function evaluated at `dφ_t u` (`trivJacobianDeriv_Ico`, the Clairaut step);
* the pairing `g.inner` is the chart Gram matrix `chartGram` of `g` at `p`, whose derivative along
  the flow curve is computed by the within-`J` chart product rule `withinJChartGram` (metric
  compatibility of `lcOf g`);
* the two terms combine into the Christoffel-symbol expression which is the chart form of
  `⟨∇_{dφ_t u}(Y t), dφ_t v⟩ + ⟨dφ_t u, ∇_{dφ_t v}(Y t)⟩` (`Submission.ChartCurv.cov_eq_frameVector_coordFun`
  and the symmetry `Submission.SecondVariation.chrB_comm` of the Christoffel form).
-/

import Mathlib
import Submission.Work.Diff.STE.C2.Kit
import Submission.Work.Diff.STE.C2.ChartKit
import Submission.Work.Diff.STE.C2.hasDerivWithinAt_comp_curve
import Submission.Work.Diff.STE.C2.flow_coord_deriv
import Submission.Work.Diff.STE.C2.withinJChartGram
import Submission.Work.Diff.C.Defs
import Submission.SecondVariation

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

namespace Work.Diff.STE.C2

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M]

noncomputable section

/-! ## Coordinate identifications for the chart at a point -/

/-! ## Coordinate identifications for the chart at a point -/

/-- **The frame vector at the centre of its own chart is the vector itself.** -/
private lemma frameVector_self (x₀ : M) (v : E) :
    Submission.Geodesic.frameVector (I := I) x₀ x₀ v = v := by
  rw [show Submission.Geodesic.frameVector (I := I) x₀ x₀ v
      = (trivializationAt E (TangentSpace I) x₀).symmL ℝ x₀ v from rfl]
  rw [TangentBundle.symmL_trivializationAt_eq_core (I := I) (b₀ := x₀) (b := x₀)
    (mem_chart_source H x₀)]
  exact (tangentBundleCore I M).coordChange_self (achart H x₀) x₀ (mem_chart_source H x₀) v

/-- **The frame vector is the inverse of the chart coordinate**: for `q` in the source of the
chart at `x₀`, the vector whose `x₀`-coordinates are `dχ_{x₀}(q) w` is `w`. -/
private lemma frameVector_mvfderiv_extChartAt {x₀ q : M} (hq : q ∈ (chartAt H x₀).source)
    (w : TangentSpace I q) :
    Submission.Geodesic.frameVector (I := I) x₀ q
      (mvfderiv I (extChartAt I x₀) q w) = w := by
  have hbase : q ∈ (trivializationAt E (TangentSpace I) x₀).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]; exact hq
  have h2 : (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ q w
      = mvfderiv I (extChartAt I x₀) q w := by
    rw [TangentBundle.continuousLinearMapAt_trivializationAt (I := I) (x₀ := x₀) (x := q)
      (𝕜 := ℝ) hq]
    rfl
  rw [show Submission.Geodesic.frameVector (I := I) x₀ q
      (mvfderiv I (extChartAt I x₀) q w)
      = (trivializationAt E (TangentSpace I) x₀).symmL ℝ q
          (mvfderiv I (extChartAt I x₀) q w) from rfl]
  rw [← h2]
  exact Trivialization.symmL_continuousLinearMapAt
    (e := trivializationAt E (TangentSpace I) x₀) (R := ℝ) (b := q) hbase w

/-- **The chart coordinate of a tangent vector at the centre of the chart is the vector itself.** -/
private lemma mvfderiv_extChartAt_self_apply (x₀ : M) (w : TangentSpace I x₀) :
    mvfderiv I (extChartAt I x₀) x₀ w = w :=
  (frameVector_self (I := I) x₀ (mvfderiv I (extChartAt I x₀) x₀ w)).symm.trans
    (frameVector_mvfderiv_extChartAt (I := I) (x₀ := x₀) (q := x₀) (mem_chart_source H x₀) w)

/-- **The chart reading of the manifold derivative**: for a map to the model space, `mvfderiv` is
the ordinary derivative of the charted expression. -/
private lemma mvfderiv_eq_fderiv_symm [I.Boundaryless] {F : M → E} (x : M)
    (hF : MDifferentiableAt I 𝓘(ℝ,E) F x) :
    mvfderiv I F x = fderiv ℝ (fun y : E ↦ F ((extChartAt I x).symm y)) ((extChartAt I x) x) := by
  rw [hF.mvfderiv, ModelWithCorners.Boundaryless.range_eq_univ, fderivWithin_univ]
  congr 1


/-- **Slice differentiability.**  A family which is jointly smooth on `J ×ˢ univ` is smooth in the
space variable, at every time of `J`. -/
private lemma mdifferentiableAt_slice {φ : ℝ → M → M} {J : Set ℝ}
    (hφ : ContMDiffOn ((modelWithCornersSelf ℝ ℝ).prod I) I (⊤ : ℕ∞)
      (fun p : ℝ × M ↦ φ p.1 p.2) (J ×ˢ Set.univ)) {s : ℝ} (hs : s ∈ J) (x : M) :
    MDifferentiableAt I I (fun y : M ↦ φ s y) x := by
  have hmid : ContMDiffWithinAt ((modelWithCornersSelf ℝ ℝ).prod I) I (⊤ : ℕ∞)
      (fun p : ℝ × M ↦ φ p.1 p.2) (J ×ˢ Set.univ) (s, x) := hφ (s, x) ⟨hs, Set.mem_univ x⟩
  have hcon : ContMDiffWithinAt I ((modelWithCornersSelf ℝ ℝ).prod I) (⊤ : ℕ∞)
      (fun y : M ↦ (s, y)) Set.univ x :=
    (contMDiffWithinAt_const (c := s)).prodMk contMDiffWithinAt_id
  have hcomp := hmid.comp x hcon (fun y _ ↦ ⟨hs, Set.mem_univ y⟩)
  exact (hcomp.contMDiffAt Filter.univ_mem).mdifferentiableAt (by simp)


/-- **The chart-coordinate description of the Jacobian of a member of a jointly smooth family.**
For `s ∈ J` and `φ s x` in the source of the chart at `p`, the `p`-frame vector whose coordinates
are those of `dφ_s|_x u` is `dφ_s|_x u`. -/
private lemma frameVector_coord_eq [I.Boundaryless] {φ : ℝ → M → M} {J : Set ℝ} {p x : M} {s : ℝ}
    (hφ : ContMDiffOn ((modelWithCornersSelf ℝ ℝ).prod I) I (⊤ : ℕ∞)
      (fun q : ℝ × M ↦ φ q.1 q.2) (J ×ˢ Set.univ))
    (hs : s ∈ J) (hsrc : φ s x ∈ (chartAt H p).source) (u : TangentSpace I x) :
    Submission.Geodesic.frameVector (I := I) p (φ s x)
      (fderiv ℝ (fun y : E ↦ (extChartAt I p) (φ s ((extChartAt I x).symm y)))
        ((extChartAt I x) x) u)
      = mfderiv I I (φ s) x u := by
  have hslice : MDifferentiableAt I I (φ s) x := mdifferentiableAt_slice (I := I) hφ hs x
  have hχ : MDifferentiableAt I 𝓘(ℝ,E) (extChartAt I p) (φ s x) :=
    mdifferentiableAt_extChartAt (I := I) (x := p) hsrc
  have hF : MDifferentiableAt I 𝓘(ℝ,E) (fun y : M ↦ (extChartAt I p) (φ s y)) x :=
    hχ.comp x hslice
  have h1 : fderiv ℝ (fun y : E ↦ (extChartAt I p) (φ s ((extChartAt I x).symm y)))
        ((extChartAt I x) x) u
      = mvfderiv I (extChartAt I p) (φ s x) (mfderiv I I (φ s) x u) := by
    rw [← mvfderiv_eq_fderiv_symm (I := I) (M := M) x hF]
    exact mfderiv_comp_apply (I := I) (I' := I) (I'' := 𝓘(ℝ,E)) (g := (extChartAt I p))
      (f := (φ s)) (x := x) hχ hslice u
  rw [h1]
  exact frameVector_mvfderiv_extChartAt (I := I) (x₀ := p) (q := φ s x) hsrc _

/-! ## Clairaut (Schwarz) for the slice `fderiv`, on `Set.Ico a b`

The one-sided Clairaut theorem of `Work.Diff.STE.C2.within_slice_clairaut`, restated for the
half-open interval `Set.Ico a b`: `Set.Ico a b` is `UniqueDiffOn` and each of its points lies in the
closure of its interior, so the symmetry of the second derivative within the set
(`ContDiffWithinAt.isSymmSndFDerivWithinAt`) applies exactly as for `Set.Icc a b`. -/

private theorem slice_fderiv_clairaut_Ico_aux
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {Ψ : ℝ × V → G} {a b : ℝ} {U : Set V} {t₀ : ℝ} {y₀ : V}
    (hab : a < b) (hU : U ∈ nhds y₀) (huniq : UniqueDiffOn ℝ U) (ht₀ : t₀ ∈ Set.Ico a b)
    (hΨ : ContDiffWithinAt ℝ 2 Ψ (Set.Ico a b ×ˢ U) (t₀, y₀)) :
    HasDerivWithinAt
      (fun s : ℝ ↦ fderiv ℝ (fun y : V ↦ Ψ (s, y)) y₀)
      (fderiv ℝ (fun y : V ↦ derivWithin (fun s : ℝ ↦ Ψ (s, y)) (Set.Ico a b) t₀) y₀)
      (Set.Ico a b) t₀ := by
  set S : Set (ℝ × V) := Set.Ico a b ×ˢ U with hS
  have hy₀U : y₀ ∈ U := mem_of_mem_nhds hU
  have hmem : (t₀, y₀) ∈ S := by rw [hS]; exact ⟨ht₀, hy₀U⟩
  have huniqS : UniqueDiffOn ℝ S := by rw [hS]; exact (uniqueDiffOn_Ico a b).prod huniq
  have huniqIco : UniqueDiffWithinAt ℝ (Set.Ico a b) t₀ := (uniqueDiffOn_Ico a b) t₀ ht₀
  -- `(t₀,y₀)` lies in the closure of the interior of the strip, so the second derivative within
  -- `S` is symmetric there.
  have hcl : (t₀, y₀) ∈ closure (interior S) := by
    have h₁ : interior S = Set.Ioo a b ×ˢ interior U := by
      rw [hS, interior_prod_eq, interior_Ico]
    rw [h₁, closure_prod_eq, closure_Ioo hab.ne]
    exact ⟨⟨ht₀.1, ht₀.2.le⟩, subset_closure (mem_interior_iff_mem_nhds.mpr hU)⟩
  have hsymm : IsSymmSndFDerivWithinAt ℝ Ψ S (t₀, y₀) :=
    hΨ.isSymmSndFDerivWithinAt (n := 2) (by norm_num) huniqS hcl hmem
  -- The second derivative of `Ψ` within `S` at `(t₀,y₀)`.
  set P : (ℝ × V) →L[ℝ] ((ℝ × V) →L[ℝ] G) :=
    fderivWithin ℝ (fun p : ℝ × V ↦ fderivWithin ℝ Ψ S p) S (t₀, y₀) with hP
  have hA_cd : ContDiffWithinAt ℝ 1 (fun p : ℝ × V ↦ fderivWithin ℝ Ψ S p) S (t₀, y₀) :=
    hΨ.fderivWithin_right huniqS (m := 1) (by norm_num) hmem
  have hA_diff : DifferentiableWithinAt ℝ (fun p : ℝ × V ↦ fderivWithin ℝ Ψ S p) S (t₀, y₀) :=
    hA_cd.differentiableWithinAt (by norm_num)
  have hA_has : HasFDerivWithinAt (fun p : ℝ × V ↦ fderivWithin ℝ Ψ S p) P S (t₀, y₀) := by
    rw [hP]; exact hA_diff.hasFDerivWithinAt
  have hsymm_eq : ∀ v : V, P (0, v) (1, 0) = P (1, 0) (0, v) := by
    intro v
    have h := hsymm.eq (0, v) (1, 0)
    simpa only [hP] using h
  -- The continuous linear map `T ↦ T.comp inr`, extracting the `V`-slot.
  set C : ((ℝ × V) →L[ℝ] G) →L[ℝ] (V →L[ℝ] G) :=
    (ContinuousLinearMap.apply ℝ (V →L[ℝ] G) (ContinuousLinearMap.inr ℝ ℝ V)).comp
      (ContinuousLinearMap.compL ℝ V (ℝ × V) G) with hCdef
  have hC_apply : ∀ T : (ℝ × V) →L[ℝ] G, C T = T.comp (ContinuousLinearMap.inr ℝ ℝ V) := by
    intro T
    rw [hCdef]
    ext v
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.compL_apply,
      ContinuousLinearMap.apply_apply, ContinuousLinearMap.inr_apply]
  -- ## The `s`-derivative of the slice differential at `y₀`.
  have hM : HasDerivWithinAt
      (fun s : ℝ ↦ (fderivWithin ℝ Ψ S (s, y₀)).comp (ContinuousLinearMap.inr ℝ ℝ V))
      ((P (1, 0)).comp (ContinuousLinearMap.inr ℝ ℝ V)) (Set.Ico a b) t₀ := by
    have hφ : HasFDerivWithinAt (fun s : ℝ ↦ (s, y₀))
        (ContinuousLinearMap.inl ℝ ℝ V) (Set.Ico a b) t₀ :=
      (hasFDerivAt_prodMk_left (𝕜 := ℝ) t₀ y₀).hasFDerivWithinAt
    have h1' : HasFDerivWithinAt (fun s : ℝ ↦ fderivWithin ℝ Ψ S (s, y₀))
        (P.comp (ContinuousLinearMap.inl ℝ ℝ V)) (Set.Ico a b) t₀ :=
      hA_has.comp t₀ hφ (by intro s hs; exact ⟨hs, hy₀U⟩)
    have h2 : HasFDerivWithinAt (fun s : ℝ ↦ C (fderivWithin ℝ Ψ S (s, y₀)))
        (C.comp (P.comp (ContinuousLinearMap.inl ℝ ℝ V))) (Set.Ico a b) t₀ :=
      (ContinuousLinearMap.hasFDerivWithinAt C (s := Set.univ)).comp t₀ h1'
        (by intro x _; exact trivial)
    have h3 := h2.hasDerivWithinAt
    have hvalC : (C.comp (P.comp (ContinuousLinearMap.inl ℝ ℝ V))) 1
        = (P (1, 0)).comp (ContinuousLinearMap.inr ℝ ℝ V) := by
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply]
      exact hC_apply (P (1, 0))
    simpa only [hC_apply, hvalC, Function.comp_def] using h3
  -- ## The slice `fderiv` at `y₀` agrees with the within-`fderiv` of `Ψ`.
  have key1 : ∀ s ∈ Set.Ico a b, ContDiffWithinAt ℝ 2 Ψ S (s, y₀) →
      fderiv ℝ (fun y : V ↦ Ψ (s, y)) y₀
        = (fderivWithin ℝ Ψ S (s, y₀)).comp (ContinuousLinearMap.inr ℝ ℝ V) := by
    intro s hs hcont
    have hd : HasFDerivWithinAt Ψ (fderivWithin ℝ Ψ S (s, y₀)) S (s, y₀) :=
      (hcont.differentiableWithinAt (by norm_num)).hasFDerivWithinAt
    have hψ : HasFDerivWithinAt (fun y : V ↦ (s, y))
        (ContinuousLinearMap.inr ℝ ℝ V) U y₀ :=
      (hasFDerivAt_prodMk_right (𝕜 := ℝ) s y₀).hasFDerivWithinAt
    have hge : HasFDerivAt (fun y : V ↦ Ψ (s, y))
        ((fderivWithin ℝ Ψ S (s, y₀)).comp (ContinuousLinearMap.inr ℝ ℝ V)) y₀ := by
      have h := (hd.comp y₀ hψ (by intro y hy; exact ⟨hs, hy⟩)).hasFDerivAt hU
      simpa only [Function.comp_def, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.inr_apply] using h
    exact hge.fderiv
  have hslic : ∀ᶠ s in 𝓝[Set.Ico a b] t₀, ContDiffWithinAt ℝ 2 Ψ S (s, y₀) := by
    have htend : Tendsto (fun s : ℝ ↦ (s, y₀)) (𝓝[Set.Ico a b] t₀) (𝓝[S] (t₀, y₀)) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, ?_⟩
      · exact (continuousAt_id.prodMk continuousAt_const).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with s hs
        exact ⟨hs, hy₀U⟩
    have hev := hΨ.eventually (by norm_num : (2 : ℕ∞ω) ≠ ∞)
    rw [Set.insert_eq_of_mem hmem] at hev
    exact htend.eventually hev
  have hEv : (fun s : ℝ ↦ fderiv ℝ (fun y : V ↦ Ψ (s, y)) y₀)
      =ᶠ[𝓝[Set.Ico a b] t₀]
        (fun s : ℝ ↦ (fderivWithin ℝ Ψ S (s, y₀)).comp
          (ContinuousLinearMap.inr ℝ ℝ V)) := by
    filter_upwards [hslic, self_mem_nhdsWithin] with s hc hs
    exact key1 s hs hc
  have hpt : (fun s : ℝ ↦ fderiv ℝ (fun y : V ↦ Ψ (s, y)) y₀) t₀
      = (fun s : ℝ ↦ (fderivWithin ℝ Ψ S (s, y₀)).comp
          (ContinuousLinearMap.inr ℝ ℝ V)) t₀ :=
    key1 t₀ ht₀ hΨ
  have hF : HasDerivWithinAt (fun s : ℝ ↦ fderiv ℝ (fun y : V ↦ Ψ (s, y)) y₀)
      ((P (1, 0)).comp (ContinuousLinearMap.inr ℝ ℝ V)) (Set.Ico a b) t₀ :=
    hM.congr_of_eventuallyEq hEv hpt
  -- ## The claimed value: the `y`-derivative of the `s`-partial.
  have key2 : ∀ y ∈ U, ContDiffWithinAt ℝ 2 Ψ S (t₀, y) →
      derivWithin (fun s : ℝ ↦ Ψ (s, y)) (Set.Ico a b) t₀
        = (fderivWithin ℝ Ψ S (t₀, y)) (1, 0) := by
    intro y hy hcont
    have hd : HasFDerivWithinAt Ψ (fderivWithin ℝ Ψ S (t₀, y)) S (t₀, y) :=
      (hcont.differentiableWithinAt (by norm_num)).hasFDerivWithinAt
    have hφ : HasFDerivWithinAt (fun s : ℝ ↦ (s, y))
        (ContinuousLinearMap.inl ℝ ℝ V) (Set.Ico a b) t₀ :=
      (hasFDerivAt_prodMk_left (𝕜 := ℝ) t₀ y).hasFDerivWithinAt
    have hd2 := (hd.comp t₀ hφ (by intro s hs; exact ⟨hs, hy⟩)).hasDerivWithinAt
    have hder := hd2.derivWithin huniqIco
    simpa only [Function.comp_def, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.inl_apply] using hder
  have htend2 : Tendsto (fun y : V ↦ (t₀, y)) (𝓝 y₀) (𝓝[S] (t₀, y₀)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · exact continuousAt_const.prodMk continuousAt_id
    · filter_upwards [hU] with y hy
      exact ⟨ht₀, hy⟩
  have hsl : ∀ᶠ y in 𝓝 y₀, ContDiffWithinAt ℝ 2 Ψ S (t₀, y) := by
    have hev := hΨ.eventually (by norm_num : (2 : ℕ∞ω) ≠ ∞)
    rw [Set.insert_eq_of_mem hmem] at hev
    exact htend2.eventually hev
  have hEv' : (fun y : V ↦ derivWithin (fun s : ℝ ↦ Ψ (s, y)) (Set.Ico a b) t₀)
      =ᶠ[𝓝 y₀] (fun y : V ↦ (fderivWithin ℝ Ψ S (t₀, y)) (1, 0)) := by
    filter_upwards [hsl, hU] with y hc hy
    exact key2 y hy hc
  have hR : HasFDerivAt (fun y : V ↦ (fderivWithin ℝ Ψ S (t₀, y)) (1, 0))
      ((ContinuousLinearMap.apply ℝ G (1, 0)).comp
        (P.comp (ContinuousLinearMap.inr ℝ ℝ V))) y₀ := by
    have hψ : HasFDerivWithinAt (fun y : V ↦ (t₀, y))
        (ContinuousLinearMap.inr ℝ ℝ V) U y₀ :=
      (hasFDerivAt_prodMk_right (𝕜 := ℝ) t₀ y₀).hasFDerivWithinAt
    have h1'' : HasFDerivWithinAt (fun y : V ↦ fderivWithin ℝ Ψ S (t₀, y))
        (P.comp (ContinuousLinearMap.inr ℝ ℝ V)) U y₀ :=
      hA_has.comp y₀ hψ (by intro y hy; exact ⟨ht₀, hy⟩)
    have h1a : HasFDerivAt (fun y : V ↦ fderivWithin ℝ Ψ S (t₀, y))
        (P.comp (ContinuousLinearMap.inr ℝ ℝ V)) y₀ := h1''.hasFDerivAt hU
    have h2a := (ContinuousLinearMap.apply ℝ G (1, 0)).hasFDerivAt.comp y₀ h1a
    simpa only [Function.comp_def, ContinuousLinearMap.apply_apply] using h2a
  have hval : fderiv ℝ (fun y : V ↦ derivWithin (fun s : ℝ ↦ Ψ (s, y)) (Set.Ico a b) t₀) y₀
      = (P (1, 0)).comp (ContinuousLinearMap.inr ℝ ℝ V) := by
    rw [hEv'.fderiv_eq, hR.fderiv]
    ext v
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
      ContinuousLinearMap.inr_apply]
    exact hsymm_eq v
  rw [hval]
  exact hF

/-- **The version used in the proof below** (with `U` an arbitrary neighbourhood of `y₀`, as in
`Work.Diff.STE.C2.within_slice_clairaut`). -/

private theorem slice_fderiv_clairaut_Ico_fderiv
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {Ψ : ℝ × V → G} {a b : ℝ} {U : Set V} {t₀ : ℝ} {y₀ : V}
    (hab : a < b) (hU : U ∈ nhds y₀) (ht₀ : t₀ ∈ Set.Ico a b)
    (hΨ : ContDiffWithinAt ℝ 2 Ψ (Set.Ico a b ×ˢ U) (t₀, y₀)) :
    HasDerivWithinAt
      (fun s : ℝ ↦ fderiv ℝ (fun y : V ↦ Ψ (s, y)) y₀)
      (fderiv ℝ (fun y : V ↦ derivWithin (fun s : ℝ ↦ Ψ (s, y)) (Set.Ico a b) t₀) y₀)
      (Set.Ico a b) t₀ := by
  -- Replace `U` by its interior: the conclusion does not mention `U`, and the interior is a
  -- `UniqueDiffOn` neighbourhood of `y₀`.
  have hy₀int : y₀ ∈ interior U := mem_interior_iff_mem_nhds.mpr hU
  have hU' : interior U ∈ nhds y₀ := isOpen_interior.mem_nhds hy₀int
  have hΨ' : ContDiffWithinAt ℝ 2 Ψ (Set.Ico a b ×ˢ interior U) (t₀, y₀) :=
    hΨ.mono (Set.prod_mono_right interior_subset)
  exact slice_fderiv_clairaut_Ico_aux hab hU' isOpen_interior.uniqueDiffOn ht₀ hΨ'


/-- **Clairaut for the slice differential, in the shape used below.**  If `Ψ : ℝ → V → G` is
jointly `C²` within `Set.Ico a b ×ˢ U` at `(t, y₀)` and the `σ`-derivative of every slice at `t`
within `Set.Ico a b` is `B y`, then `σ ↦ fderivWithin ℝ (Ψ σ) U y₀` has within-`Set.Ico a b`
derivative `fderiv ℝ B y₀` at `t`. -/
private theorem slice_fderiv_clairaut_Ico
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (Ψ : ℝ → V → G) (B : V → G) {a b : ℝ} (hab : a < b) (U : Set V) {t : ℝ} {y₀ : V}
    (ht : t ∈ Set.Ico a b) (hU : U ∈ nhds y₀)
    (hΨ : ContDiffWithinAt ℝ 2 (fun p : ℝ × V ↦ Ψ p.1 p.2) (Set.Ico a b ×ˢ U) (t, y₀))
    (hB : ∀ y ∈ U, HasDerivWithinAt (fun σ : ℝ ↦ Ψ σ y) (B y) (Set.Ico a b) t) :
    HasDerivWithinAt (fun σ : ℝ ↦ fderivWithin ℝ (fun y : V ↦ Ψ σ y) U y₀) (fderiv ℝ B y₀)
      (Set.Ico a b) t := by
  have hmain := slice_fderiv_clairaut_Ico_fderiv (Ψ := fun p : ℝ × V ↦ Ψ p.1 p.2)
    (a := a) (b := b) hab hU ht hΨ
  have hval : B =ᶠ[𝓝 y₀] (fun y : V ↦ derivWithin (fun s : ℝ ↦ Ψ s y) (Set.Ico a b) t) := by
    filter_upwards [hU] with y hy
    exact ((hB y hy).derivWithin ((uniqueDiffOn_Ico a b) t ht)).symm
  have hmain' : HasDerivWithinAt (fun s : ℝ ↦ fderiv ℝ (fun y : V ↦ Ψ s y) y₀)
      (fderiv ℝ B y₀) (Set.Ico a b) t := by
    have hderiv : fderiv ℝ (fun y : V ↦ derivWithin (fun s : ℝ ↦ Ψ s y) (Set.Ico a b) t) y₀
        = fderiv ℝ B y₀ := hval.fderiv_eq.symm
    exact hmain.congr_deriv hderiv
  refine hmain'.congr_of_eventuallyEq ?_ ?_
  · filter_upwards with σ
    exact fderivWithin_of_mem_nhds hU
  · exact fderivWithin_of_mem_nhds hU


/-! ## The `s`-derivative of the chart-coordinate Jacobian of the flow, on `Set.Ico a b` -/

/-- **Chart smoothness of the charted flow** (copy of the private lemma of
`Submission.Work.Diff.STE.C2.trivJacobianDeriv`, which itself follows from the joint smoothness
`hφ`). -/

private theorem contDiffWithinAt_chartedFlow_Ico [I.Boundaryless]
    (φ : ℝ → Diffeomorph I I M M (⊤ : ℕ∞)) (J : Set ℝ)
    (hφ : ContMDiffOn ((modelWithCornersSelf ℝ ℝ).prod I) I (⊤ : ℕ∞)
      (fun p : ℝ × M ↦ φ p.1 p.2) (J ×ˢ Set.univ))
    {t : ℝ} (ht : t ∈ J) (x : M) :
    ContDiffWithinAt ℝ 2
      (fun q : ℝ × E ↦ (extChartAt I (φ t x)) (φ q.1 ((extChartAt I x).symm q.2)))
      (J ×ˢ (extChartAt I x).target) (t, (extChartAt I x) x) := by
  have hy₀target : (extChartAt I x) x ∈ (extChartAt I x).target :=
    (extChartAt I x).map_source (mem_extChartAt_source x)
  have hsxy : (extChartAt I x).symm ((extChartAt I x) x) = x :=
    PartialEquiv.left_inv _ (mem_extChartAt_source x)
  have hmid : ContMDiffWithinAt ((modelWithCornersSelf ℝ ℝ).prod I) I (⊤ : ℕ∞)
      (fun r : ℝ × M ↦ φ r.1 r.2) (J ×ˢ (Set.univ : Set M))
      ((fun q : ℝ × E ↦ (q.1, (extChartAt I x).symm q.2)) (t, (extChartAt I x) x)) := by
    rw [show (fun q : ℝ × E ↦ (q.1, (extChartAt I x).symm q.2)) (t, (extChartAt I x) x)
        = (t, x) from by simp [PartialEquiv.left_inv _ (mem_extChartAt_source x)]]
    exact hφ (t, x) ⟨ht, trivial⟩
  have hκ : ContMDiffWithinAt (𝓘(ℝ,ℝ).prod 𝓘(ℝ,E)) ((modelWithCornersSelf ℝ ℝ).prod I) (⊤ : ℕ∞)
      (fun q : ℝ × E ↦ (q.1, (extChartAt I x).symm q.2))
      (J ×ˢ (extChartAt I x).target) (t, (extChartAt I x) x) := by
    refine ContMDiffWithinAt.prodMk ?_ ?_
    · exact contMDiffWithinAt_fst
    · exact ((contMDiffOn_extChartAt_symm (I := I) x) ((extChartAt I x) x) hy₀target).comp
        (t, (extChartAt I x) x) contMDiffWithinAt_snd (fun z hz ↦ hz.2)
  have hmap : Set.MapsTo (fun q : ℝ × E ↦ (q.1, (extChartAt I x).symm q.2))
      (J ×ˢ (extChartAt I x).target) (J ×ˢ (Set.univ : Set M)) :=
    fun z hz ↦ ⟨hz.1, trivial⟩
  have hcomp := hmid.comp (t, (extChartAt I x) x) hκ hmap
  have hout : ContMDiffAt I 𝓘(ℝ,E) (⊤ : ℕ∞) (extChartAt I (φ t x))
      ((fun r : ℝ × M ↦ φ r.1 r.2)
        ((fun q : ℝ × E ↦ (q.1, (extChartAt I x).symm q.2)) (t, (extChartAt I x) x))) := by
    show ContMDiffAt I 𝓘(ℝ,E) (⊤ : ℕ∞) (extChartAt I (φ t x))
      (φ t ((extChartAt I x).symm ((extChartAt I x) x)))
    rw [hsxy]
    exact contMDiffAt_extChartAt
  have hsm := hout.comp_contMDiffWithinAt (t, (extChartAt I x) x) hcomp
  have h1 : ContMDiffWithinAt (modelWithCornersSelf ℝ (ℝ × E)) (modelWithCornersSelf ℝ E) 2
      (fun q : ℝ × E ↦ (extChartAt I (φ t x)) (φ q.1 ((extChartAt I x).symm q.2)))
      (J ×ˢ (extChartAt I x).target) (t, (extChartAt I x) x) := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact hsm.of_le (by simp)
  exact ((contMDiffWithinAt_iff_contDiffWithinAt).mp h1).congr (fun q _ ↦ rfl) rfl

/-- **The `s`-derivative of the chart-coordinate Jacobian of the flow** (interval form of
`Work.Diff.STE.C2.trivJacobianDeriv`, with the Clairaut step taken from
`slice_fderiv_clairaut_Ico`). -/

private theorem trivJacobianDeriv_Ico
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless]
    (φ : ℝ → Diffeomorph I I M M (⊤ : ℕ∞)) (Y : ℝ → (x : M) → TangentSpace I x)
    {a b : ℝ} (hab : a < b)
    (hφ : ContMDiffOn ((modelWithCornersSelf ℝ ℝ).prod I) I (⊤ : ℕ∞)
      (fun p : ℝ × M ↦ φ p.1 p.2) (Set.Ico a b ×ˢ Set.univ))
    (hYsm : ContMDiffOn ((modelWithCornersSelf ℝ ℝ).prod I) I.tangent (⊤ : ℕ∞)
      (fun p : ℝ × M ↦ (⟨p.2, Y p.1 p.2⟩ : TangentBundle I M)) (Set.Ico a b ×ˢ Set.univ))
    (hvel : ∀ t ∈ Set.Ico a b, ∀ x : M,
      HasMFDerivWithinAt (modelWithCornersSelf ℝ ℝ) I (fun s ↦ φ s x) (Set.Ico a b) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (Y t (φ t x))))
    {t : ℝ} (ht : t ∈ Set.Ico a b) {x : M} (u : TangentSpace I x) :
    HasDerivWithinAt
      (fun s : ℝ ↦ fderiv ℝ
        (fun y : E ↦ (extChartAt I (φ t x)) (φ s ((extChartAt I x).symm y)))
        ((extChartAt I x) x) u)
      (mvfderiv I (fun q : M ↦
          (trivializationAt E (TangentSpace I) (φ t x)).continuousLinearMapAt ℝ q (Y t q))
        (φ t x) (mfderiv I I (φ t : M → M) x u))
      (Set.Ico a b) t := by
  classical
  set p : M := φ t x with hp
  set y₀ : E := (extChartAt I x) x with hy₀
  -- ## the chart neighbourhood `U` of `y₀` on which the whole computation lives
  set U : Set E := (extChartAt I x).symm ⁻¹'
        ((φ t) ⁻¹' (chartAt H p).source ∩ (chartAt H x).source)
      ∩ (extChartAt I x).target with hUdef
  have hsxy : (extChartAt I x).symm y₀ = x := by
    rw [hy₀]; exact PartialEquiv.left_inv _ (mem_extChartAt_source x)
  have hy₀target : y₀ ∈ (extChartAt I x).target := by
    rw [hy₀]; exact (extChartAt I x).map_source (mem_extChartAt_source x)
  have hxins : x ∈ (φ t) ⁻¹' (chartAt H p).source ∩ (chartAt H x).source := by
    refine ⟨?_, mem_chart_source H x⟩
    show φ t x ∈ (chartAt H p).source
    rw [← hp]
    exact mem_chart_source H p
  have hpre : (extChartAt I x).symm ⁻¹'
      ((φ t) ⁻¹' (chartAt H p).source ∩ (chartAt H x).source) ∈ nhds y₀ := by
    refine (continuousAt_extChartAt_symm (I := I) x).preimage_mem_nhds ?_
    rw [hsxy]
    exact Filter.inter_mem
      (((φ t).continuous.continuousAt).preimage_mem_nhds
        ((chartAt H p).open_source.mem_nhds (mem_chart_source H p)))
      ((chartAt H x).open_source.mem_nhds (mem_chart_source H x))
  have hUmem : U ∈ nhds y₀ :=
    Filter.inter_mem hpre ((isOpen_extChartAt_target (I := I) x).mem_nhds hy₀target)
  have hsrc : ∀ y ∈ U, φ t ((extChartAt I x).symm y) ∈ (chartAt H p).source :=
    fun y hy ↦ hy.1.1
  -- ## chart smoothness of the flow
  have hsm : ContDiffWithinAt ℝ 2
      (fun q : ℝ × E ↦ (extChartAt I p) (φ q.1 ((extChartAt I x).symm q.2)))
      (Set.Ico a b ×ˢ U) (t, y₀) := by
    have h0 := contDiffWithinAt_chartedFlow_Ico (I := I) (M := M) φ (Set.Ico a b) hφ ht x
    rw [← hp, ← hy₀] at h0
    exact h0.mono (Set.prod_mono_right Set.inter_subset_right)
  -- ## the velocity of the charted flow is the charted velocity of `Y t`
  have hBderiv : ∀ y ∈ U, HasDerivWithinAt
      (fun σ : ℝ ↦ (extChartAt I p) (φ σ ((extChartAt I x).symm y)))
      (mvfderiv I (extChartAt I p) (φ t ((extChartAt I x).symm y))
        (Y t (φ t ((extChartAt I x).symm y)))) (Set.Ico a b) t := by
    intro y hy
    exact hasDerivWithinAt_comp_curve (I := I) (M := M)
      (ψ := extChartAt I p) (γ := fun s : ℝ ↦ φ s ((extChartAt I x).symm y)) (J := Set.Ico a b)
      (v := Y t (φ t ((extChartAt I x).symm y)))
      (hvel t ht ((extChartAt I x).symm y)) (mdifferentiableAt_extChartAt (hsrc y hy))
  -- ## the Clairaut step (transported from `Set.Icc a b` to `Set.Ico a b`)
  have hcore := slice_fderiv_clairaut_Ico
    (fun σ y ↦ (extChartAt I p) (φ σ ((extChartAt I x).symm y)))
    (fun y ↦ mvfderiv I (extChartAt I p) (φ t ((extChartAt I x).symm y))
      (Y t (φ t ((extChartAt I x).symm y))))
    hab U ht hUmem hsm hBderiv
  -- ## `fderivWithin` is `fderiv`, as `U ∈ 𝓝 y₀`
  have hD : (fun σ : ℝ ↦ fderivWithin ℝ
        (fun y : E ↦ (extChartAt I p) (φ σ ((extChartAt I x).symm y))) U y₀)
      = fun σ : ℝ ↦ fderiv ℝ
        (fun y : E ↦ (extChartAt I p) (φ σ ((extChartAt I x).symm y))) y₀ :=
    funext fun σ ↦ fderivWithin_of_mem_nhds hUmem
  rw [hD] at hcore
  -- ## identify the value of the derivative
  have hcentermem : φ t x ∈ (chartAt H p).source := by
    rw [← hp]; exact mem_chart_source H p
  have hEq : (fun y : E ↦ mvfderiv I (extChartAt I p) (φ t ((extChartAt I x).symm y))
        (Y t (φ t ((extChartAt I x).symm y))))
      =ᶠ[nhds y₀] fun y : E ↦ coordT p (Y t) (φ t ((extChartAt I x).symm y)) := by
    filter_upwards [hUmem] with y hy
    exact (coordT_eq_mvfderiv p (Y t) (hsrc y hy)).symm
  have hA : MDifferentiableAt I 𝓘(ℝ,E) (coordT p (Y t)) p := by
    have hYt : ContMDiff I I.tangent (⊤ : ℕ∞)
        (fun q : M ↦ (⟨q, Y t q⟩ : TangentBundle I M)) := by
      intro q
      exact ((hYsm (t, q) ⟨ht, trivial⟩).comp q
        ((contMDiffWithinAt_const (c := t)).prodMk contMDiffWithinAt_id)
        (fun r _ ↦ ⟨ht, trivial⟩)).contMDiffAt Filter.univ_mem
    have hsmooth :=
      Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contMDiffOn_continuousLinearMapAt_section
        (I := I) (M := M) p (W := Y t) (u := Set.univ) (hYt.contMDiffOn)
    exact (((hsmooth p ⟨trivial, mem_chart_source H p⟩).contMDiffAt
      (Filter.inter_mem Filter.univ_mem
        ((chartAt H p).open_source.mem_nhds (mem_chart_source H p))))).mdifferentiableAt
      (by simp)
  have hφt : MDifferentiableAt I I (φ t : M → M) x :=
    (φ t).contMDiff.mdifferentiableAt (by simp)
  have hcompA : MDifferentiableAt I 𝓘(ℝ,E) ((coordT p (Y t)) ∘ (φ t : M → M)) x :=
    hA.comp x hφt
  have hval : fderiv ℝ (fun y : E ↦ mvfderiv I (extChartAt I p)
        (φ t ((extChartAt I x).symm y)) (Y t (φ t ((extChartAt I x).symm y)))) y₀ u
      = mvfderiv I (coordT p (Y t)) p (mfderiv I I (φ t : M → M) x u) := by
    have h2 : fderiv ℝ (fun y : E ↦ mvfderiv I (extChartAt I p)
          (φ t ((extChartAt I x).symm y)) (Y t (φ t ((extChartAt I x).symm y)))) y₀
        = fderiv ℝ (fun y : E ↦ coordT p (Y t) (φ t ((extChartAt I x).symm y))) y₀ :=
      hEq.fderiv_eq
    have h3 : fderiv ℝ (fun y : E ↦ coordT p (Y t) (φ t ((extChartAt I x).symm y))) y₀
        = mvfderiv I ((coordT p (Y t)) ∘ (φ t : M → M)) x :=
      (mvfderiv_eq_fderiv_comp_symm (F := (coordT p (Y t)) ∘ (φ t : M → M)) x hcompA).symm
    have h4 : mvfderiv I ((coordT p (Y t)) ∘ (φ t : M → M)) x u
        = mvfderiv I (coordT p (Y t)) p (mfderiv I I (φ t : M → M) x u) :=
      mvfderiv_comp_apply x hA hφt u
    exact (congrArg (fun (L : E →L[ℝ] E) ↦ L u) (h2.trans h3)).trans h4
  -- ## assembly
  have hmono : HasDerivWithinAt
      (fun σ : ℝ ↦ fderiv ℝ
        (fun y : E ↦ (extChartAt I p) (φ σ ((extChartAt I x).symm y))) y₀)
      (fderiv ℝ (fun y : E ↦ mvfderiv I (extChartAt I p) (φ t ((extChartAt I x).symm y))
        (Y t (φ t ((extChartAt I x).symm y)))) y₀) (Set.Ico a b) t := hcore
  have hfinal := (ContinuousLinearMap.apply (E := E) ℝ E u).hasFDerivAt.comp_hasDerivWithinAt
    t hmono
  have hv : (ContinuousLinearMap.apply (E := E) ℝ E u)
      (fderiv ℝ (fun y : E ↦ mvfderiv I (extChartAt I p) (φ t ((extChartAt I x).symm y))
        (Y t (φ t ((extChartAt I x).symm y)))) y₀)
      = mvfderiv I (coordT p (Y t)) p (mfderiv I I (φ t : M → M) x u) := hval
  exact hv ▸ hfinal

/-! ## The target -/

theorem fixedMet_flow_Ico
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M)
    (φ : ℝ → Diffeomorph I I M M (⊤ : ℕ∞)) (Y : ℝ → Π x : M, TangentSpace I x)
    {a b : ℝ} (hab : a < b)
    (hφ : ContMDiffOn ((modelWithCornersSelf ℝ ℝ).prod I) I (⊤ : ℕ∞)
      (fun p : ℝ × M ↦ φ p.1 p.2) (Set.Ico a b ×ˢ Set.univ))
    (hY : ContMDiffOn ((modelWithCornersSelf ℝ ℝ).prod I) I.tangent (⊤ : ℕ∞)
      (fun p : ℝ × M ↦ (⟨p.2, Y p.1 p.2⟩ : TangentBundle I M)) (Set.Ico a b ×ˢ Set.univ))
    (hvel : ∀ t ∈ Set.Ico a b, ∀ x : M,
      HasMFDerivWithinAt (modelWithCornersSelf ℝ ℝ) I (fun s ↦ φ s x) (Set.Ico a b) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (Y t (φ t x)))) :
    ∀ t ∈ Set.Ico a b, ∀ (x : M) (u v : TangentSpace I x),
      HasDerivWithinAt
        (fun s ↦ g.inner (φ s x) (mfderiv I I (φ s : M → M) x u)
          (mfderiv I I (φ s : M → M) x v))
        (g.inner (φ t x) ((Submission.Diff.lcOf g) (Y t) (φ t x) (mfderiv I I (φ t : M → M) x u))
            (mfderiv I I (φ t : M → M) x v)
          + g.inner (φ t x) (mfderiv I I (φ t : M → M) x u)
            ((Submission.Diff.lcOf g) (Y t) (φ t x) (mfderiv I I (φ t : M → M) x v)))
        (Set.Ico a b) t := by
  intro t ht x u v
  -- ## The metric instance and the Levi-Civita connection
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  obtain ⟨hcovsm, htor, hmetI⟩ := hLC g
  haveI : ContMDiffCovariantDerivative (Submission.Diff.lcOf g) ∞ := hcovsm.some
  set p : M := φ t x with hp
  -- ## The chart-`p` coordinates of the two Jacobian curves
  set h₁ : ℝ → E := fun s ↦ fderiv ℝ
      (fun y : E ↦ (extChartAt I p) (φ s ((extChartAt I x).symm y)))
      ((extChartAt I x) x) u with h₁def
  set h₂ : ℝ → E := fun s ↦ fderiv ℝ
      (fun y : E ↦ (extChartAt I p) (φ s ((extChartAt I x).symm y)))
      ((extChartAt I x) x) v with h₂def
  -- ## The instance-free metric compatibility
  have hmetF : ∀ (Y Z : Π x : M, TangentSpace I x),
      ContMDiff I I.tangent (⊤ : ℕ∞) (fun y : M ↦ (⟨y, Y y⟩ : TangentBundle I M)) →
      ContMDiff I I.tangent (⊤ : ℕ∞) (fun y : M ↦ (⟨y, Z y⟩ : TangentBundle I M)) →
      ∀ (x : M) (v : TangentSpace I x),
        mvfderiv I (fun y : M ↦ g.inner y (Y y) (Z y)) x v =
          g.inner x (Submission.Diff.lcOf g Y x v) (Z x)
            + g.inner x (Y x) (Submission.Diff.lcOf g Z x v) :=
    (Work.Diff.C.isMetricCompatibleFor_iff
      (hamb := (inferInstance : RiemannianBundle (fun x : M ↦ TangentSpace I x)))
      (Submission.Diff.lcOf g)).mp hmetI
  -- ## The claimed derivatives of the coordinate functions (DeTurck: the chart-coordinate form of
  -- the first variation of the flow)
  have hder₁ : HasDerivWithinAt h₁
      (mvfderiv I (Work.Diff.STE.C2.coord p (Y t)) p (mfderiv I I (φ t : M → M) x u)) (Set.Ico a b) t := by
    rw [h₁def]
    exact trivJacobianDeriv_Ico (I := I) (M := M) (a := a) (b := b) φ Y hab hφ hY hvel ht u
  have hder₂ : HasDerivWithinAt h₂
      (mvfderiv I (Work.Diff.STE.C2.coord p (Y t)) p (mfderiv I I (φ t : M → M) x v)) (Set.Ico a b) t := by
    rw [h₂def]
    exact trivJacobianDeriv_Ico (I := I) (M := M) (a := a) (b := b) φ Y hab hφ hY hvel ht v
  -- ## The within-`Set.Ico a b` chart product rule
  have hvelγ : HasMFDerivWithinAt (modelWithCornersSelf ℝ ℝ) I (fun s ↦ φ s x) (Set.Ico a b) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (Y t (φ t x))) := hvel t ht x
  have hsrc : (fun s ↦ φ s x) t ∈ (chartAt H p).source := by
    show φ t x ∈ (chartAt H p).source
    rw [show φ t x = p from hp.symm]
    exact mem_chart_source H p
  have hprod := withinJChartGram (I := I) (M := M) g (Submission.Diff.lcOf g) hmetF
    p hvelγ hsrc hder₁ hder₂
  -- ## The value of the product rule is the right-hand side of the conclusion
  have hval : g.inner p
        (Submission.Geodesic.frameVector (I := I) p p
          ((mvfderiv I (Work.Diff.STE.C2.coord p (Y t)) p (mfderiv I I (φ t : M → M) x u))
            + Submission.Geodesic.christoffelEval (Submission.Diff.lcOf g) p p (h₁ t)
                (Y t (φ t x))))
        (Submission.Geodesic.frameVector (I := I) p p (h₂ t))
      + g.inner p (Submission.Geodesic.frameVector (I := I) p p (h₁ t))
        (Submission.Geodesic.frameVector (I := I) p p
          ((mvfderiv I (Work.Diff.STE.C2.coord p (Y t)) p (mfderiv I I (φ t : M → M) x v))
            + Submission.Geodesic.christoffelEval (Submission.Diff.lcOf g) p p (h₂ t)
                (Y t (φ t x))))
      = g.inner (φ t x) ((Submission.Diff.lcOf g) (Y t) (φ t x) (mfderiv I I (φ t : M → M) x u))
          (mfderiv I I (φ t : M → M) x v)
        + g.inner (φ t x) (mfderiv I I (φ t : M → M) x u)
          ((Submission.Diff.lcOf g) (Y t) (φ t x) (mfderiv I I (φ t : M → M) x v)) := by
    -- the field `Y t` is a globally smooth section
    have hYt : ContMDiff I I.tangent (⊤ : ℕ∞)
        (fun q : M ↦ (⟨q, Y t q⟩ : TangentBundle I M)) := by
      intro q
      have hpt : (t, q) ∈ Set.Ico a b ×ˢ (Set.univ : Set M) := ⟨ht, Set.mem_univ q⟩
      have hcon : ContMDiffWithinAt I ((modelWithCornersSelf ℝ ℝ).prod I) (⊤ : ℕ∞)
          (fun r : M ↦ (t, r)) Set.univ q :=
        (contMDiffWithinAt_const (c := t)).prodMk contMDiffWithinAt_id
      exact ((hY (t, q) hpt).comp q hcon (fun r _ ↦ hpt)).contMDiffAt Filter.univ_mem
    -- the coordinate functions at time `t`
    have h₁t : h₁ t = mfderiv I I (φ t : M → M) x u := by
      show fderiv ℝ (fun y : E ↦ (extChartAt I p) (φ t ((extChartAt I x).symm y)))
          ((extChartAt I x) x) u = mfderiv I I (φ t : M → M) x u
      exact (frameVector_self (I := I) p _).symm.trans
        (frameVector_coord_eq (I := I) (φ := fun t' y ↦ φ t' y) (J := Set.Ico a b) (p := p) (x := x)
          (s := t) hφ ht (mem_chart_source H p) u)
    have h₂t : h₂ t = mfderiv I I (φ t : M → M) x v := by
      show fderiv ℝ (fun y : E ↦ (extChartAt I p) (φ t ((extChartAt I x).symm y)))
          ((extChartAt I x) x) v = mfderiv I I (φ t : M → M) x v
      exact (frameVector_self (I := I) p _).symm.trans
        (frameVector_coord_eq (I := I) (φ := fun t' y ↦ φ t' y) (J := Set.Ico a b) (p := p) (x := x)
          (s := t) hφ ht (mem_chart_source H p) v)
    -- torsion-freeness identifies the two Christoffel conventions
    have hchr : ∀ w : E, Submission.Geodesic.christoffelEval (Submission.Diff.lcOf g) p p w
          (Y t (φ t x))
        = Submission.ChartCurv.chrB (Submission.Diff.lcOf g) p p
            (Submission.ChartCurv.coordFun p (Y t) p) w := by
      intro w
      rw [show Y t (φ t x) = Y t p from rfl,
        ← Submission.ChartCurv.frameVector_coordFun_eq (I := I) (x₀ := p) (W := Y t)
          (q := p) (mem_chart_source H p),
        ← Submission.ChartCurv.chrB_apply (cov := Submission.Diff.lcOf g) (x₀ := p) (p := p)
          (a := w) (b := Submission.ChartCurv.coordFun p (Y t) p),
        Submission.SecondVariation.chrB_comm (cov := Submission.Diff.lcOf g) htor
          (mem_chart_source H p)]
    -- the chart formula for `∇` of the smooth section `Y t`
    have hkey : ∀ w : E,
        (Submission.Diff.lcOf g) (Y t) p w
        = mvfderiv I (Work.Diff.STE.C2.coord p (Y t)) p w
          + Submission.ChartCurv.chrB (Submission.Diff.lcOf g) p p
              (Submission.ChartCurv.coordFun p (Y t) p) w := by
      intro w
      have hcov := Submission.ChartCurv.cov_eq_frameVector_coordFun
        (cov := Submission.Diff.lcOf g) p (W := Y t) hYt (mem_chart_source H p) (v := w)
      simp only [frameVector_self] at hcov
      exact hcov
    -- assemble
    rw [frameVector_self (I := I) p _, frameVector_self (I := I) p _,
      frameVector_self (I := I) p _, frameVector_self (I := I) p _,
      hkey (mfderiv I I (φ t : M → M) x u), hkey (mfderiv I I (φ t : M → M) x v),
      hchr (h₁ t), hchr (h₂ t), ← h₁t, ← h₂t,
      show p = φ t x from hp]
  -- ## The Jacobian curves are described by the coordinate functions, along `Set.Ico a b`
  have hcont : Tendsto (fun s ↦ φ s x) (𝓝[Set.Ico a b] t) (𝓝 p) :=
    hvelγ.continuousWithinAt
  have hkey : ∀ᶠ s in 𝓝[Set.Ico a b] t,
      Submission.Geodesic.frameVector (I := I) p ((fun s ↦ φ s x) s) (h₁ s)
        = mfderiv I I (φ s : M → M) x u ∧
      Submission.Geodesic.frameVector (I := I) p ((fun s ↦ φ s x) s) (h₂ s)
        = mfderiv I I (φ s : M → M) x v := by
    filter_upwards [self_mem_nhdsWithin,
      hcont.eventually ((chartAt H p).open_source.mem_nhds (mem_chart_source H p))]
      with s hsJ hsSrc
    have h1 : Submission.Geodesic.frameVector (I := I) p (φ s x) (h₁ s)
        = mfderiv I I (φ s : M → M) x u := by
      show Submission.Geodesic.frameVector (I := I) p (φ s x)
        (fderiv ℝ (fun y : E ↦ (extChartAt I p) (φ s ((extChartAt I x).symm y)))
          ((extChartAt I x) x) u) = _
      exact frameVector_coord_eq (I := I) (φ := fun t' y ↦ φ t' y) (J := Set.Ico a b) (p := p)
        (x := x) (s := s) hφ hsJ hsSrc u
    have h2 : Submission.Geodesic.frameVector (I := I) p (φ s x) (h₂ s)
        = mfderiv I I (φ s : M → M) x v := by
      show Submission.Geodesic.frameVector (I := I) p (φ s x)
        (fderiv ℝ (fun y : E ↦ (extChartAt I p) (φ s ((extChartAt I x).symm y)))
          ((extChartAt I x) x) v) = _
      exact frameVector_coord_eq (I := I) (φ := fun t' y ↦ φ t' y) (J := Set.Ico a b) (p := p)
        (x := x) (s := s) hφ hsJ hsSrc v
    exact ⟨h1, h2⟩
  -- ## The two functions agree near `t` in `Set.Ico a b`
  have hcongr : (fun s ↦ g.inner (φ s x) (mfderiv I I (φ s : M → M) x u)
        (mfderiv I I (φ s : M → M) x v))
      =ᶠ[𝓝[Set.Ico a b] t] (fun s ↦ g.inner ((fun s ↦ φ s x) s)
        (Submission.Geodesic.frameVector (I := I) p ((fun s ↦ φ s x) s) (h₁ s))
        (Submission.Geodesic.frameVector (I := I) p ((fun s ↦ φ s x) s) (h₂ s))) := by
    filter_upwards [hkey] with s hs
    simp only [hs.1, hs.2]
  -- ## The two functions agree at `t`
  have hpt : g.inner (φ t x) (mfderiv I I (φ t : M → M) x u) (mfderiv I I (φ t : M → M) x v)
      = g.inner ((fun s ↦ φ s x) t)
          (Submission.Geodesic.frameVector (I := I) p ((fun s ↦ φ s x) t) (h₁ t))
          (Submission.Geodesic.frameVector (I := I) p ((fun s ↦ φ s x) t) (h₂ t)) := by
    have h1 : Submission.Geodesic.frameVector (I := I) p (φ t x) (h₁ t)
        = mfderiv I I (φ t : M → M) x u := by
      show Submission.Geodesic.frameVector (I := I) p (φ t x)
        (fderiv ℝ (fun y : E ↦ (extChartAt I p) (φ t ((extChartAt I x).symm y)))
          ((extChartAt I x) x) u) = _
      exact frameVector_coord_eq (I := I) (φ := fun t' y ↦ φ t' y) (J := Set.Ico a b) (p := p)
        (x := x) (s := t) hφ ht (mem_chart_source H p) u
    have h2 : Submission.Geodesic.frameVector (I := I) p (φ t x) (h₂ t)
        = mfderiv I I (φ t : M → M) x v := by
      show Submission.Geodesic.frameVector (I := I) p (φ t x)
        (fderiv ℝ (fun y : E ↦ (extChartAt I p) (φ t ((extChartAt I x).symm y)))
          ((extChartAt I x) x) v) = _
      exact frameVector_coord_eq (I := I) (φ := fun t' y ↦ φ t' y) (J := Set.Ico a b) (p := p)
        (x := x) (s := t) hφ ht (mem_chart_source H p) v
    rw [h1, h2]
  -- ## Conclusion
  refine ((hprod.congr_of_eventuallyEq hcongr hpt).congr_deriv ?_)
  rw [show φ t x = p from hp.symm]
  exact hval

end

end Work.Diff.STE.C2
