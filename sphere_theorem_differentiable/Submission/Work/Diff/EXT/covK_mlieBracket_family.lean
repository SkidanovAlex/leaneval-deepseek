import Mathlib
import Submission.Work.Diff.EXT.curvDefs
import Submission.Work.Diff.EXT.covK_spatialDeriv
import Submission.Commons.Geometry.Manifold.VectorField.mvfderivWithin_apply_mlieBracketWithin

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.EXT

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology Matrix
open Bundle ContDiff Set VectorField CovariantDerivative Metric
open Filter

set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
  [I.Boundaryless] [T2Space M]

/-! ## Slice smoothness of a jointly smooth family -/

/-- The slice `y ↦ X t y` of a jointly smooth family is smooth at every point of `V`. -/
theorem contMDiffAt_slice {X : ℝ → TField (I := I) (M := M)} {V : Set (ℝ × M)}
    (hV : IsOpen V) (hX : JointField X V) {p : ℝ × M} (hp : p ∈ V) :
    CMDiffAt ∞ (T% (X p.1)) p.2 := by
  have h1 : ContMDiffAt ((𝓘(ℝ,ℝ)).prod I) I.tangent ∞
      (fun q : ℝ × M => (⟨q.2, X q.1 q.2⟩ : TangentBundle I M)) p :=
    hX.contMDiffAt (hV.mem_nhds hp)
  have h2 : ContMDiffAt I ((𝓘(ℝ,ℝ)).prod I) ∞ (fun y : M => (p.1, y)) p.2 :=
    contMDiffAt_const.prodMk contMDiffAt_id
  have h3 : ContMDiffAt I I.tangent ∞ (fun y : M => (⟨y, X p.1 y⟩ : TangentBundle I M)) p.2 :=
    h1.comp p.2 h2
  exact h3

/-- The slice of a jointly smooth family is smooth on the corresponding slice of `V`. -/
theorem jointField_slice {X : ℝ → TField (I := I) (M := M)} {V : Set (ℝ × M)}
    (hV : IsOpen V) (hX : JointField X V) (t : ℝ) :
    CMDiff[{y : M | (t, y) ∈ V}] ∞ (T% (X t)) :=
  fun y hy => (contMDiffAt_slice hV hX hy).contMDiffWithinAt

/-! ## The derivation identity for the Lie bracket -/

/-- `[X,Y] f = X(Y f) - Y(X f)`: the Lie bracket acting on a smooth function, at a point.  The
smoothness hypotheses are on an open set `s ∋ x`. -/
theorem mvfderiv_mlieBracket_eq {f : M → ℝ} {X Y : Π y : M, TangentSpace I y}
    {s : Set M} {x : M} (hs : IsOpen s) (hxs : x ∈ s)
    (hf : CMDiff[s] ∞ f) (hX : CMDiff[s] ∞ (T% X)) (hY : CMDiff[s] ∞ (T% Y)) :
    mvfderiv I f x (mlieBracket I X Y x) =
      mvfderiv I (fun y => mvfderiv I f y (Y y)) x (X x)
        - mvfderiv I (fun y => mvfderiv I f y (X y)) x (Y x) := by
  have hxclos : x ∈ closure (interior s) := by rw [hs.interior_eq]; exact subset_closure hxs
  have key := Commons.Geometry.Manifold.VectorField.mvfderivWithin_apply_mlieBracketWithin
    (I := I) (f := f) (X := X) (Y := Y) (s := s) (x := x)
    hs.uniqueMDiffOn hxs hxclos hf hX hY
  rw [mlieBracketWithin_of_isOpen hs hxs] at key
  have hconv : ∀ (g : M → ℝ) (y : M), y ∈ s → mvfderivWithin I g s y = mvfderiv I g y := by
    intro g y hy
    have h := Commons.Geometry.Manifold.VectorField.mvfderivWithin_inter (I := I)
      (f := g) (s := (univ : Set M)) (t := s) (x := y) (hs.mem_nhds hy)
    rw [Set.univ_inter, mvfderivWithin_univ] at h
    exact h
  have hfunY : (fun y => mvfderivWithin I f s y (Y y)) =ᶠ[𝓝 x]
      (fun y => mvfderiv I f y (Y y)) := by
    filter_upwards [hs.mem_nhds hxs] with y hy
    rw [hconv f y hy]
  have hfunX : (fun y => mvfderivWithin I f s y (X y)) =ᶠ[𝓝 x]
      (fun y => mvfderiv I f y (X y)) := by
    filter_upwards [hs.mem_nhds hxs] with y hy
    rw [hconv f y hy]
  have eY : mvfderivWithin I (fun y => mvfderivWithin I f s y (Y y)) s x
      = mvfderiv I (fun y => mvfderiv I f y (Y y)) x := by
    rw [hconv (fun y => mvfderivWithin I f s y (Y y)) x hxs]
    have h := Commons.Geometry.Manifold.VectorField.mvfderivWithin_congr_eventually
      (I := I) (s := (univ : Set M)) (g := fun y => mvfderiv I f y (Y y))
      (g₁ := fun y => mvfderivWithin I f s y (Y y))
      (by simpa only [nhdsWithin_univ] using hfunY) hfunY.eq_of_nhds
    rw [mvfderivWithin_univ, mvfderivWithin_univ] at h
    exact h
  have eX : mvfderivWithin I (fun y => mvfderivWithin I f s y (X y)) s x
      = mvfderiv I (fun y => mvfderiv I f y (X y)) x := by
    rw [hconv (fun y => mvfderivWithin I f s y (X y)) x hxs]
    have h := Commons.Geometry.Manifold.VectorField.mvfderivWithin_congr_eventually
      (I := I) (s := (univ : Set M)) (g := fun y => mvfderiv I f y (X y))
      (g₁ := fun y => mvfderivWithin I f s y (X y))
      (by simpa only [nhdsWithin_univ] using hfunX) hfunX.eq_of_nhds
    rw [mvfderivWithin_univ, mvfderivWithin_univ] at h
    exact h
  rw [eY, eX, hconv f x hxs] at key
  rw [key]
  abel

/-! ## The derivative of the chart and of its coordinates -/

/-- The chart coordinate function has derivative the coordinate functional. -/
theorem mvfderiv_chartCoord_apply (y₀ : M) {y : M} (hy : y ∈ (chartAt H y₀).source)
    (k : Fin (Module.finrank ℝ E)) (v : TangentSpace I y) :
    mvfderiv I (fun y' : M => (Module.finBasis ℝ E).coord k ((extChartAt I y₀) y')) y v
      = (Module.finBasis ℝ E).coord k
          ((trivializationAt E (TangentSpace I) y₀).continuousLinearMapAt ℝ y v) := by
  have hf : MDiffAt (extChartAt I y₀) y := mdifferentiableAt_extChartAt hy
  have hφ : MDiffAt (fun z : E => (Module.finBasis ℝ E).coord k z) (extChartAt I y₀ y) :=
    ((((Module.finBasis ℝ E).coord k).toContinuousLinearMap.contDiff (n := ∞)).contMDiff.contMDiffAt
      ).mdifferentiableAt (by simp)
  have hcomp := mvfderiv_comp_apply (x := y)
    (g := fun z : E => (Module.finBasis ℝ E).coord k z) (f := extChartAt I y₀) hφ hf v
  rw [show ((fun z : E => (Module.finBasis ℝ E).coord k z) ∘ (extChartAt I y₀))
      = (fun y' : M => (Module.finBasis ℝ E).coord k ((extChartAt I y₀) y')) from rfl] at hcomp
  rw [hcomp, mvfderiv_eq_fderiv]
  rw [show (fun z : E => (Module.finBasis ℝ E).coord k z)
      = ⇑(((Module.finBasis ℝ E).coord k).toContinuousLinearMap) from rfl]
  rw [(ContinuousLinearMap.hasFDerivAt
    (((Module.finBasis ℝ E).coord k).toContinuousLinearMap)).fderiv]
  rw [← TangentBundle.continuousLinearMapAt_trivializationAt (I := I) hy]
  rfl


/-! ## The family of Lie brackets -/

/-- The `k`-th coordinate function of the chart at `y₀`. -/
noncomputable def chartCoord (y₀ : M) (k : Fin (Module.finrank ℝ E)) : M → ℝ :=
  fun y' => (Module.finBasis ℝ E).coord k ((extChartAt I y₀) y')

/-- The Lie bracket of two jointly smooth families of tangent fields is jointly smooth. -/
theorem covK_mlieBracket_family
    {V : Set (ℝ × M)} (hV : IsOpen V)
    {X Z : ℝ → TField (I := I) (M := M)} (hX : JointField X V) (hZ : JointField Z V) :
    JointField (fun t ↦ VectorField.mlieBracket I (X t) (Z t)) V := by
  intro p hp
  set y₀ : M := p.2 with hy₀
  have hy₀src : y₀ ∈ (chartAt H y₀).source := mem_chart_source H y₀
  have hy₀bs : y₀ ∈ (trivializationAt E (TangentSpace I) y₀).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]; exact hy₀src
  have hbs : ∀ᶠ q : ℝ × M in 𝓝 p,
      q.2 ∈ (trivializationAt E (TangentSpace I) y₀).baseSet :=
    continuous_snd.continuousAt.preimage_mem_nhds
      ((trivializationAt E (TangentSpace I) y₀).open_baseSet.mem_nhds hy₀bs)
  have hchart : ∀ᶠ q : ℝ × M in 𝓝 p, q.2 ∈ (chartAt H y₀).source :=
    continuous_snd.continuousAt.preimage_mem_nhds ((chartAt H y₀).open_source.mem_nhds hy₀src)
  have hfk_sm : ∀ k, ContMDiffOn I 𝓘(ℝ,ℝ) ∞ (chartCoord (I := I) (M := M) y₀ k)
      (chartAt H y₀).source := by
    intro k
    have houter : ContMDiffOn 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞
        (⇑((Module.finBasis ℝ E).coord k).toContinuousLinearMap) (Set.univ : Set E) :=
      contMDiffOn_univ.mpr
        ((((Module.finBasis ℝ E).coord k).toContinuousLinearMap.contDiff (n := ∞)).contMDiff)
    refine houter.comp contMDiffOn_extChartAt (by intro y hy; exact mem_univ _) |>.congr ?_
    intro y hy
    rfl
  -- the component functions are smooth
  have hcomp : ∀ k : Fin (Module.finrank ℝ E),
      ContMDiffAt ((𝓘(ℝ,ℝ)).prod I) 𝓘(ℝ,ℝ) ∞
        (fun q : ℝ × M => (Module.finBasis ℝ E).coord k
          ((trivializationAt E (TangentSpace I) y₀).continuousLinearMapAt ℝ q.2
            (mlieBracket I (X q.1) (Z q.1) q.2))) p := by
    intro k
    set V' : Set (ℝ × M) := V ∩ (univ ×ˢ (chartAt H y₀).source) with hV'def
    have hV'open : IsOpen V' := hV.inter (isOpen_univ.prod (chartAt H y₀).open_source)
    have hp' : p ∈ V' :=
      ⟨hp, mem_univ _, by rw [← hy₀]; exact hy₀src⟩
    have hfk_joint : ContMDiffOn ((𝓘(ℝ,ℝ)).prod I) 𝓘(ℝ,ℝ) ∞
        (fun q : ℝ × M => chartCoord (I := I) (M := M) y₀ k q.2) V' := by
      have h1 : ContMDiffOn ((𝓘(ℝ,ℝ)).prod I) 𝓘(ℝ,ℝ) ∞
          ((chartCoord (I := I) (M := M) y₀ k) ∘ (Prod.snd : ℝ × M → M))
          (univ ×ˢ (chartAt H y₀).source) :=
        ContMDiffOn.comp (t := (chartAt H y₀).source) (hg := hfk_sm k)
          (hf := contMDiffOn_snd) (by intro q hq; exact hq.2)
      refine h1.mono (by intro q hq; exact ⟨mem_univ _, hq.2.2⟩) |>.congr ?_
      intro q hq
      rfl
    have hX' : JointField X V' := hX.mono inter_subset_left
    have hZ' : JointField Z V' := hZ.mono inter_subset_left
    have hΦ1 : ContMDiffOn ((𝓘(ℝ,ℝ)).prod I) 𝓘(ℝ,ℝ) ∞
        (fun q : ℝ × M => mvfderiv I (chartCoord (I := I) (M := M) y₀ k) q.2 (Z q.1 q.2)) V' :=
      covK_spatialDeriv (I := I) (M := M) (V := V')
        (Φ := fun t y => chartCoord (I := I) (M := M) y₀ k y) hV'open hfk_joint hZ'
    have hΦ2 : ContMDiffOn ((𝓘(ℝ,ℝ)).prod I) 𝓘(ℝ,ℝ) ∞
        (fun q : ℝ × M => mvfderiv I
          (fun y' => mvfderiv I (chartCoord (I := I) (M := M) y₀ k) y' (Z q.1 y')) q.2
          (X q.1 q.2)) V' :=
      covK_spatialDeriv (I := I) (M := M) (V := V')
        (Φ := fun t y => mvfderiv I (chartCoord (I := I) (M := M) y₀ k) y (Z t y)) hV'open hΦ1 hX'
    have hΨ1 : ContMDiffOn ((𝓘(ℝ,ℝ)).prod I) 𝓘(ℝ,ℝ) ∞
        (fun q : ℝ × M => mvfderiv I (chartCoord (I := I) (M := M) y₀ k) q.2 (X q.1 q.2)) V' :=
      covK_spatialDeriv (I := I) (M := M) (V := V')
        (Φ := fun t y => chartCoord (I := I) (M := M) y₀ k y) hV'open hfk_joint hX'
    have hΨ2 : ContMDiffOn ((𝓘(ℝ,ℝ)).prod I) 𝓘(ℝ,ℝ) ∞
        (fun q : ℝ × M => mvfderiv I
          (fun y' => mvfderiv I (chartCoord (I := I) (M := M) y₀ k) y' (X q.1 y')) q.2
          (Z q.1 q.2)) V' :=
      covK_spatialDeriv (I := I) (M := M) (V := V')
        (Φ := fun t y => mvfderiv I (chartCoord (I := I) (M := M) y₀ k) y (X t y)) hV'open hΨ1 hZ'
    have hE : ContMDiffAt ((𝓘(ℝ,ℝ)).prod I) 𝓘(ℝ,ℝ) ∞
        (fun q : ℝ × M => mvfderiv I
            (fun y' => mvfderiv I (chartCoord (I := I) (M := M) y₀ k) y' (Z q.1 y')) q.2
            (X q.1 q.2)
          - mvfderiv I
            (fun y' => mvfderiv I (chartCoord (I := I) (M := M) y₀ k) y' (X q.1 y')) q.2
            (Z q.1 q.2)) p :=
      (hΦ2.sub hΨ2).contMDiffAt (hV'open.mem_nhds hp')
    refine hE.congr_of_eventuallyEq ?_
    filter_upwards [hV.mem_nhds hp, hchart] with q hq hqchart
    rw [← mvfderiv_chartCoord_apply (I := I) y₀ hqchart k (mlieBracket I (X q.1) (Z q.1) q.2)]
    have hVt : IsOpen {y : M | (q.1, y) ∈ V} :=
      hV.preimage (continuous_const.prodMk continuous_id)
    have hsopen : IsOpen ({y : M | (q.1, y) ∈ V} ∩ (chartAt H y₀).source) :=
      hVt.inter (chartAt H y₀).open_source
    have hqs : q.2 ∈ {y : M | (q.1, y) ∈ V} ∩ (chartAt H y₀).source := ⟨hq, hqchart⟩
    exact mvfderiv_mlieBracket_eq (I := I) hsopen hqs
      ((hfk_sm k).mono inter_subset_right)
      ((jointField_slice hV hX q.1).mono inter_subset_left)
      ((jointField_slice hV hZ q.1).mono inter_subset_left)
  -- assemble the trivialised bracket
  have hclm : ContMDiffAt ((𝓘(ℝ,ℝ)).prod I) 𝓘(ℝ,E) ∞
      (fun q : ℝ × M => (trivializationAt E (TangentSpace I) y₀).continuousLinearMapAt ℝ q.2
        (mlieBracket I (X q.1) (Z q.1) q.2)) p := by
    have hterm : ∀ k ∈ (Finset.univ : Finset (Fin (Module.finrank ℝ E))),
        ContMDiffAt ((𝓘(ℝ,ℝ)).prod I) 𝓘(ℝ,E) ∞
          (fun q : ℝ × M => (Module.finBasis ℝ E).coord k
            ((trivializationAt E (TangentSpace I) y₀).continuousLinearMapAt ℝ q.2
              (mlieBracket I (X q.1) (Z q.1) q.2)) • (Module.finBasis ℝ E) k) p :=
      fun k _ => (hcomp k).smul (contMDiffAt_const (c := (Module.finBasis ℝ E) k))
    have hsum : ContMDiffAt ((𝓘(ℝ,ℝ)).prod I) 𝓘(ℝ,E) ∞
        (fun q : ℝ × M => ∑ k : Fin (Module.finrank ℝ E), (Module.finBasis ℝ E).coord k
          ((trivializationAt E (TangentSpace I) y₀).continuousLinearMapAt ℝ q.2
            (mlieBracket I (X q.1) (Z q.1) q.2)) • (Module.finBasis ℝ E) k) p :=
      ContMDiffAt.sum (t := Finset.univ) (fun k hk => hterm k hk)
    refine hsum.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun q => ?_))
    exact (Module.Basis.sum_repr (Module.finBasis ℝ E)
      ((trivializationAt E (TangentSpace I) y₀).continuousLinearMapAt ℝ q.2
        (mlieBracket I (X q.1) (Z q.1) q.2))).symm
  have hAt : ContMDiffAt ((𝓘(ℝ,ℝ)).prod I) I.tangent ∞
      (fun q : ℝ × M => (⟨q.2, mlieBracket I (X q.1) (Z q.1) q.2⟩ : TangentBundle I M)) p := by
    refine (Bundle.Trivialization.contMDiffAt_iff
      (e := trivializationAt E (TangentSpace I) y₀) ?_).mpr ⟨contMDiffAt_snd, ?_⟩
    · rw [Bundle.Trivialization.mem_source]
      exact hy₀bs
    · refine hclm.congr_of_eventuallyEq ?_
      filter_upwards [hbs] with q hq
      exact (Bundle.Trivialization.continuousLinearMapAt_apply_of_mem ℝ _ hq _).symm
  exact hAt.contMDiffWithinAt

end Work.Diff.EXT
