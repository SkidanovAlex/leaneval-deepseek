/-
# Layer C2 (DeTurck pull-back): the pulled-back metric family is jointly smooth

The statement `Work.Diff.STE.C2.formFamJoint_pullMetBilin` says that if `t ↦ φ t` is a family of
diffeomorphisms of `M` that is jointly smooth on `J ×ˢ univ` and `t ↦ A t` is a jointly smooth
family of Riemannian metrics on `J ×ˢ univ`, then the family of pulled-back metrics
`t ↦ pullMetBilin (φ t) (A t)` is jointly smooth on `J ×ˢ univ` as well.

This file develops the (surprisingly non-trivial) analytic core of the statement and then proves
it.

## The analytic core

The `(i,j)`-entry of the frame matrix of the pulled-back metric in the coordinate frame of the
chart at `x₀` is

`(A t).inner (φ t x) (dφ_t|_x σ_i) (dφ_t|_x σ_j)`,   `σ_i = frameVector x₀ x (bB i)`.

So one needs the *joint* smoothness in `(t, x)` of the derivative `dφ_t|_x u` of the family.  The
key point is that the derivative is taken in the `x`-variable only: this is exactly the situation
handled by Mathlib's `ContMDiffWithinAt.mfderivWithin_apply`, whose set is `t ×ˢ u` with `u` the
set on which the derivative is taken (here `univ`, so no `UniqueMDiff` hypothesis is needed on the
time set `J` — which is essential, since `J` is an arbitrary set, e.g. `Set.Ico 0 T`, and points
of `J` need not be non-isolated).

The output of `ContMDiffWithinAt.mfderivWithin_apply` is the *trivialised* derivative
`inTangentCoordinates`.  Reading it back as a tangent vector uses the trivialisation of the
tangent bundle at the target point `y₀ = φ τ x₀`:
`inTangentCoordinates I 𝓘(ℝ,E) Prod.snd Ψ (· ↦ mfderiv (Ψ p.1 ·) p.2) p₀ p (bB i)` is
`L_{y₀}(Φ p) (dφ_{p.1}|_{p.2} σ_i)`, where `L_{y₀}` is the linear part of the trivialisation at
`y₀`.  Feeding this into `Trivialization.contMDiffWithinAt_iff` gives the smoothness of the
tangent-bundle section `p ↦ ⟨Φ p, dφ_{p.1}|_{p.2} σ_i⟩` over `Φ`, and then Mathlib's
`ContMDiffWithinAt.clm_bundle_apply₂` evaluates the (jointly smooth) metric family section on the
two sections, producing the scalar entry.

## Layout

* `contMDiffWithinAt_metric_pairing_fixed`: the pairing of a jointly smooth metric family with two
  smooth fields;
* `contMDiffWithinAt_inTangent_mfderiv` (the crux): joint smoothness of the trivialised derivative;
* `inTangentCoordinates_apply_eq`: the identification of the trivialised derivative with
  `L_{y₀}(Φ p) (V i p)`;
* `contMDiffWithinAt_tangentSection_mfderiv`: smoothness of `p ↦ ⟨Φ p, V i p⟩`;
* `contMDiffWithinAt_inner_mfderiv`: the scalar entry;
* `contMDiffWithinAt_frameMat_pullMetBilin`: the frame matrix;
* `formFamSection_contMDiffWithinAt_of_frameMat` (within-set version of the existing
  `Work.Diff.EXT.formFamSection_contMDiffAt_of_frameMat`);
* the target theorem.
-/
import Mathlib
import Submission.Work.Diff.STE.C2.Defs
import Submission.Work.Diff.EXT.glueDefs
import Submission.Work.Diff.EXT.inCoordinates_tangent_bilin

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1000000
set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.STE.C2

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]

/-! ### Pairing a jointly smooth metric family with two smooth fields -/

/-- **Joint smoothness of a metric pairing along a jointly smooth family (within-set form).**
If `t ↦ A t` is a jointly smooth family of Riemannian metrics on the time set `J` and the sections
`Y`, `Z` are `C^∞` at `y₀`, then `(t, y) ↦ (A t).inner y (Y y) (Z y)` is jointly `C^∞` on
`J ×ˢ univ` at `(τ, y₀)`. -/
theorem contMDiffWithinAt_metric_pairing_fixed
    {A : ℝ → Submission.Diff.SMet I M} {J : Set ℝ} (hA : Submission.Diff.JointSmooth A J)
    {τ : ℝ} {y₀ : M} (hy₀ : (τ, y₀) ∈ J ×ˢ (Set.univ : Set M))
    {Y Z : Π y : M, TangentSpace I y}
    (hY : ContMDiffAt I I.tangent (⊤ : ℕ∞) (T% Y) y₀)
    (hZ : ContMDiffAt I I.tangent (⊤ : ℕ∞) (T% Z) y₀) :
    ContMDiffWithinAt ((modelWithCornersSelf ℝ ℝ).prod I) (modelWithCornersSelf ℝ ℝ)
      (⊤ : ℕ∞) (fun p : ℝ × M ↦ (A p.1).inner p.2 (Y p.2) (Z p.2))
      (J ×ˢ (Set.univ : Set M)) (τ, y₀) := by
  classical
  have hψ : ContMDiffWithinAt ((𝓘(ℝ,ℝ)).prod I)
      (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) (⊤ : ℕ∞)
      (fun m : ℝ × M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
        (Prod.snd m) ((A m.1).inner (Prod.snd m)))
      (J ×ˢ (Set.univ : Set M)) (τ, y₀) := hA (τ, y₀) hy₀
  have hYc : ContMDiffWithinAt ((𝓘(ℝ,ℝ)).prod I) (I.prod 𝓘(ℝ, E)) (⊤ : ℕ∞)
      ((T% Y) ∘ (Prod.snd : ℝ × M → M)) (J ×ˢ (Set.univ : Set M)) (τ, y₀) :=
    hY.contMDiffWithinAt.comp (τ, y₀) contMDiffWithinAt_snd (fun _ _ => Set.mem_univ _)
  have hZc : ContMDiffWithinAt ((𝓘(ℝ,ℝ)).prod I) (I.prod 𝓘(ℝ, E)) (⊤ : ℕ∞)
      ((T% Z) ∘ (Prod.snd : ℝ × M → M)) (J ×ˢ (Set.univ : Set M)) (τ, y₀) :=
    hZ.contMDiffWithinAt.comp (τ, y₀) contMDiffWithinAt_snd (fun _ _ => Set.mem_univ _)
  have hmain : ContMDiffWithinAt ((𝓘(ℝ,ℝ)).prod I) (I.prod 𝓘(ℝ, ℝ)) (⊤ : ℕ∞)
      (fun m : ℝ × M ↦ TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ) (Prod.snd m)
        ((A m.1).inner (Prod.snd m) (Y (Prod.snd m)) (Z (Prod.snd m))))
      (J ×ˢ (Set.univ : Set M)) (τ, y₀) :=
    ContMDiffWithinAt.clm_bundle_apply₂ (𝕜 := ℝ) (B := M) (F₁ := E) (F₂ := E) (F₃ := ℝ)
      (E₁ := fun x : M => TangentSpace I x) (E₂ := fun x : M => TangentSpace I x)
      (E₃ := Bundle.Trivial M ℝ) (b := fun m : ℝ × M => Prod.snd m)
      (v := fun m : ℝ × M => Y (Prod.snd m)) (w := fun m : ℝ × M => Z (Prod.snd m))
      (ψ := fun m : ℝ × M => (A m.1).inner (Prod.snd m))
      (s := J ×ˢ (Set.univ : Set M)) (x := (τ, y₀)) hψ hYc hZc
  simp only [contMDiffWithinAt_totalSpace] at hmain
  exact hmain.2

/-! ### The crux: joint smoothness of the trivialised derivative of the family -/

/-- **Joint smoothness of the trivialised derivative of a family of diffeomorphisms.**
If `p ↦ φ p.1 p.2` is jointly `C^∞` on `J ×ˢ univ` at `p₀` and `y₀ = φ p₀.1 p₀.2`, then
`p ↦ (inTangentCoordinates … p₀ p) (bB i)` is jointly `C^∞` there.  The derivative is taken with
respect to the second variable only, which is why no `UniqueMDiff` hypothesis on `J` is needed. -/
theorem contMDiffWithinAt_inTangent_mfderiv
    {J : Set ℝ} {φ : ℝ → Diffeomorph I I M M (⊤ : ℕ∞)} {p₀ : ℝ × M}
    (hp₀ : p₀ ∈ J ×ˢ (Set.univ : Set M))
    (hφ : ContMDiffWithinAt ((modelWithCornersSelf ℝ ℝ).prod I) I (⊤ : ℕ∞)
      (fun p : ℝ × M ↦ φ p.1 p.2) (J ×ˢ (Set.univ : Set M)) p₀)
    {y₀ : M} (hy₀ : φ p₀.1 p₀.2 = y₀) (i : Fin (Module.finrank ℝ E)) :
    ContMDiffWithinAt ((modelWithCornersSelf ℝ ℝ).prod I) 𝓘(ℝ,E) (⊤ : ℕ∞)
      (fun p : ℝ × M ↦
        (inTangentCoordinates I 𝓘(ℝ,E) (fun q : ℝ × M ↦ q.2)
          (fun q : ℝ × M ↦ (extChartAt I y₀) (φ q.1 q.2))
          (fun q : ℝ × M ↦ mfderiv I 𝓘(ℝ,E)
            (fun y : M ↦ (extChartAt I y₀) (φ q.1 y)) q.2)
          p₀ p) (Work.Diff.EXT.bB (E := E) i))
      (J ×ˢ (Set.univ : Set M)) p₀ := by
  set t : Set (ℝ × M) := (J ×ˢ (Set.univ : Set M))
    ∩ (fun p : ℝ × M ↦ φ p.1 p.2) ⁻¹' ((chartAt H y₀).source) with ht
  have hsrc_nhds : ∀ᶠ p : ℝ × M in 𝓝[J ×ˢ (Set.univ : Set M)] p₀,
      φ p.1 p.2 ∈ (chartAt H y₀).source := by
    refine hφ.continuousWithinAt.preimage_mem_nhdsWithin ?_
    rw [hy₀]
    exact (chartAt H y₀).open_source.mem_nhds (mem_chart_source H y₀)
  have htmem : t ∈ 𝓝[J ×ˢ (Set.univ : Set M)] p₀ := by
    rw [ht]
    exact Filter.inter_mem self_mem_nhdsWithin hsrc_nhds
  have hp_t : p₀ ∈ t := by
    rw [ht]; exact ⟨hp₀, by rw [Set.mem_preimage, hy₀]; exact mem_chart_source H y₀⟩
  -- the graph map
  have hgraph : ContMDiffWithinAt (I := ((𝓘(ℝ,ℝ)).prod I).prod I) (I' := (𝓘(ℝ,ℝ)).prod I)
      (n := (⊤ : ℕ∞)) (f := fun z : (ℝ × M) × M ↦ (z.1.1, z.2))
      (s := t ×ˢ (Set.univ : Set M)) (x := (p₀, p₀.2)) :=
    ((contMDiffWithinAt_fst (s := t ×ˢ (Set.univ : Set M)) (p := (p₀, p₀.2))).fst).prodMk
      (contMDiffWithinAt_snd (s := t ×ˢ (Set.univ : Set M)) (p := (p₀, p₀.2)))
  have hmap1 : MapsTo (fun z : (ℝ × M) × M ↦ (z.1.1, z.2)) (t ×ˢ (Set.univ : Set M))
      (J ×ˢ (Set.univ : Set M)) := by
    intro z hz
    rw [ht] at hz
    exact ⟨hz.1.1.1, Set.mem_univ _⟩
  have hΦcomp : ContMDiffWithinAt (I := ((𝓘(ℝ,ℝ)).prod I).prod I) (I' := I)
      (n := (⊤ : ℕ∞)) (f := fun z : (ℝ × M) × M ↦ φ z.1.1 z.2)
      (s := t ×ˢ (Set.univ : Set M)) (x := (p₀, p₀.2)) :=
    hφ.comp (p₀, p₀.2) hgraph hmap1
  -- restrict to where the chart reading makes sense
  set t2 : Set ((ℝ × M) × M) := (t ×ˢ (Set.univ : Set M))
    ∩ (fun z : (ℝ × M) × M ↦ φ z.1.1 z.2) ⁻¹' ((chartAt H y₀).source) with ht2
  have ht2mem : t2 ∈ 𝓝[t ×ˢ (Set.univ : Set M)] (p₀, p₀.2) := by
    rw [ht2]
    refine Filter.inter_mem self_mem_nhdsWithin ?_
    refine hΦcomp.continuousWithinAt.preimage_mem_nhdsWithin ?_
    rw [hy₀]
    exact (chartAt H y₀).open_source.mem_nhds (mem_chart_source H y₀)
  have hΦcomp2 : ContMDiffWithinAt (I := ((𝓘(ℝ,ℝ)).prod I).prod I) (I' := I)
      (n := (⊤ : ℕ∞)) (f := fun z : (ℝ × M) × M ↦ φ z.1.1 z.2)
      (s := t2) (x := (p₀, p₀.2)) :=
    hΦcomp.mono (by rw [ht2]; exact inter_subset_left)
  have hf2 : ContMDiffWithinAt (I := ((𝓘(ℝ,ℝ)).prod I).prod I) (I' := 𝓘(ℝ,E))
      (n := (⊤ : ℕ∞)) (f := fun z : (ℝ × M) × M ↦ (extChartAt I y₀) (φ z.1.1 z.2))
      (s := t2) (x := (p₀, p₀.2)) := by
    have h2 : ContMDiffWithinAt I 𝓘(ℝ,E) (⊤ : ℕ∞) (extChartAt I y₀)
        (chartAt H y₀).source (φ p₀.1 p₀.2) :=
      (contMDiffOn_extChartAt (I := I) (n := (⊤ : ℕ∞)) (x := y₀)) (φ p₀.1 p₀.2)
        (by rw [hy₀]; exact mem_chart_source H y₀)
    exact h2.comp (p₀, p₀.2) hΦcomp2 (fun z hz => hz.2)
  have hf : ContMDiffWithinAt (I := ((𝓘(ℝ,ℝ)).prod I).prod I) (I' := 𝓘(ℝ,E))
      (n := (⊤ : ℕ∞)) (f := fun z : (ℝ × M) × M ↦ (extChartAt I y₀) (φ z.1.1 z.2))
      (s := t ×ˢ (Set.univ : Set M)) (x := (p₀, p₀.2)) :=
    hf2.mono_of_mem_nhdsWithin ht2mem
  have hf' : ContMDiffWithinAt (I := ((𝓘(ℝ,ℝ)).prod I).prod I) (I' := 𝓘(ℝ,E))
      (n := (⊤ : ℕ∞))
      (f := Function.uncurry (fun q : ℝ × M ↦ fun y : M ↦ (extChartAt I y₀) (φ q.1 y)))
      (s := t ×ˢ (Set.univ : Set M)) (x := (p₀, p₀.2)) := hf
  have hmain := ContMDiffWithinAt.mfderivWithin_apply (𝕜 := ℝ)
    (E := E) (H := H) (I := I) (M := M)
    (E' := E) (H' := E) (I' := 𝓘(ℝ,E)) (M' := E)
    (N := ℝ × M) (N' := ℝ × M) (J := (𝓘(ℝ,ℝ)).prod I) (J' := (𝓘(ℝ,ℝ)).prod I)
    (f := fun q : ℝ × M ↦ fun y : M ↦ (extChartAt I y₀) (φ q.1 y))
    (g := fun q : ℝ × M ↦ q.2)
    (g₁ := fun q : ℝ × M ↦ q)
    (g₂ := fun _ : ℝ × M ↦ Work.Diff.EXT.bB (E := E) i)
    (t := t) (u := (Set.univ : Set M)) (v := t)
    (x₀ := p₀) (n := (⊤ : ℕ∞)) (m := (⊤ : ℕ∞))
    hf'
    (contMDiffWithinAt_snd (s := t) (p := p₀))
    (contMDiffWithinAt_id (s := t) (x := p₀))
    (contMDiffWithinAt_const (I := (𝓘(ℝ,ℝ)).prod I)
      (c := Work.Diff.EXT.bB (E := E) i) (s := t) (x := p₀))
    (le_refl _) (fun _ hz => hz) hp_t (fun _ _ => Set.mem_univ _) uniqueMDiffOn_univ
  have hmain' := hmain.mono_of_mem_nhdsWithin htmem
  simpa only [mfderivWithin_univ] using hmain'

/-! ### The trivialised derivative is `L_{y₀}(Φ p) ∘ dφ` -/

/-- **Identification of the trivialised derivative.**  Applying the trivialised derivative of the
family to `bB i` gives the `y₀`-chart coordinates of the derivative of `φ p.1` at `p.2` applied to
the coordinate-frame vector `frameVector p₀.2 p.2 (bB i)`. -/
theorem inTangentCoordinates_apply_eq
    {y₀ : M} {φ : ℝ → Diffeomorph I I M M (⊤ : ℕ∞)} {p₀ p : ℝ × M}
    (hp : p.2 ∈ (chartAt H p₀.2).source)
    (hΦ : φ p.1 p.2 ∈ (chartAt H y₀).source)
    (i : Fin (Module.finrank ℝ E)) :
    (inTangentCoordinates I 𝓘(ℝ,E) (fun q : ℝ × M ↦ q.2)
      (fun q : ℝ × M ↦ (extChartAt I y₀) (φ q.1 q.2))
      (fun q : ℝ × M ↦ mfderiv I 𝓘(ℝ,E) (fun y : M ↦ (extChartAt I y₀) (φ q.1 y)) q.2)
      p₀ p) (Work.Diff.EXT.bB (E := E) i)
    = (trivializationAt E (TangentSpace I) y₀).continuousLinearMapAt ℝ (φ p.1 p.2)
        (mfderiv I I (φ p.1) p.2
          (Submission.Geodesic.frameVector (I := I) p₀.2 p.2 (Work.Diff.EXT.bB (E := E) i))) := by
  rw [inTangentCoordinates_eq (f := fun q : ℝ × M ↦ q.2)
    (g := fun q : ℝ × M ↦ (extChartAt I y₀) (φ q.1 q.2))
    (ϕ := fun q : ℝ × M ↦ mfderiv I 𝓘(ℝ,E) (fun y : M ↦ (extChartAt I y₀) (φ q.1 y)) q.2)
    hp (Set.mem_univ _)]
  rw [TangentBundle.coordChange_model_space]
  rw [← TangentBundle.symmL_trivializationAt_eq_core (I := I) (b₀ := p₀.2) (b := p.2) hp]
  rw [show Submission.Geodesic.frameVector (I := I) p₀.2 p.2 (Work.Diff.EXT.bB (E := E) i)
      = (trivializationAt E (TangentSpace I) p₀.2).symmL ℝ p.2 (Work.Diff.EXT.bB (E := E) i)
      from rfl]
  show (1 : E →L[ℝ] E) ((mfderiv I 𝓘(ℝ,E) ((extChartAt I y₀) ∘ (φ p.1)) p.2)
      ((trivializationAt E (TangentSpace I) p₀.2).symmL ℝ p.2 (Work.Diff.EXT.bB (E := E) i)))
    = (trivializationAt E (TangentSpace I) y₀).continuousLinearMapAt ℝ (φ p.1 p.2)
        (mfderiv I I (φ p.1) p.2
          ((trivializationAt E (TangentSpace I) p₀.2).symmL ℝ p.2 (Work.Diff.EXT.bB (E := E) i)))
  rw [one_apply_eq_self]
  rw [mfderiv_comp_apply (I := I) (I' := I) (I'' := 𝓘(ℝ,E))
    (g := (extChartAt I y₀)) (f := (φ p.1)) (x := p.2)
    (mdifferentiableAt_extChartAt (I := I) (x := y₀) hΦ)
    (mdifferentiableAt_of_diffeomorph (I := I) (φ p.1) p.2)]
  rw [TangentBundle.continuousLinearMapAt_trivializationAt (I := I) (x₀ := y₀)
    (x := φ p.1 p.2) hΦ]
  rfl

/-! ### The tangent section `p ↦ ⟨Φ p, dφ σ_i⟩` -/

/-- **Joint smoothness of the tangent section `p ↦ (Φ p, dφ_{p.1}|_{p.2} σ_i)`.**  The
`i`-th coordinate-frame vector of the chart at `p₀.2` is pushed forward by the differential of the
family. -/
theorem contMDiffWithinAt_tangentSection_mfderiv
    {J : Set ℝ} {φ : ℝ → Diffeomorph I I M M (⊤ : ℕ∞)} {p₀ : ℝ × M}
    (hp₀ : p₀ ∈ J ×ˢ (Set.univ : Set M))
    (hφ : ContMDiffWithinAt ((modelWithCornersSelf ℝ ℝ).prod I) I (⊤ : ℕ∞)
      (fun p : ℝ × M ↦ φ p.1 p.2) (J ×ˢ (Set.univ : Set M)) p₀)
    {y₀ : M} (hy₀ : φ p₀.1 p₀.2 = y₀) (i : Fin (Module.finrank ℝ E)) :
    ContMDiffWithinAt ((modelWithCornersSelf ℝ ℝ).prod I) I.tangent (⊤ : ℕ∞)
      (fun p : ℝ × M ↦ (⟨φ p.1 p.2,
        mfderiv I I (φ p.1) p.2
          (Submission.Geodesic.frameVector (I := I) p₀.2 p.2 (Work.Diff.EXT.bB (E := E) i))⟩
        : TangentBundle I M))
      (J ×ˢ (Set.univ : Set M)) p₀ := by
  set s : Set (ℝ × M) := ((J ×ˢ (Set.univ : Set M))
    ∩ (fun p : ℝ × M ↦ φ p.1 p.2) ⁻¹' ((chartAt H y₀).source))
    ∩ (fun p : ℝ × M ↦ p.2) ⁻¹' ((chartAt H p₀.2).source) with hs
  have hs_nhds : s ∈ 𝓝[J ×ˢ (Set.univ : Set M)] p₀ := by
    rw [hs]
    refine Filter.inter_mem (Filter.inter_mem self_mem_nhdsWithin ?_) ?_
    · refine hφ.continuousWithinAt.preimage_mem_nhdsWithin ?_
      rw [hy₀]; exact (chartAt H y₀).open_source.mem_nhds (mem_chart_source H y₀)
    · exact continuousWithinAt_snd.preimage_mem_nhdsWithin
        ((chartAt H p₀.2).open_source.mem_nhds (mem_chart_source H p₀.2))
  have hp₀s : p₀ ∈ s := by
    rw [hs]
    exact ⟨⟨hp₀, by rw [Set.mem_preimage, hy₀]; exact mem_chart_source H y₀⟩,
      by rw [Set.mem_preimage]; exact mem_chart_source H p₀.2⟩
  have hsrc : ∀ p ∈ s, φ p.1 p.2 ∈ (chartAt H y₀).source := by
    intro p hp
    simp only [hs, Set.mem_inter_iff, Set.mem_preimage] at hp
    exact hp.1.2
  have hframe : ∀ p ∈ s, p.2 ∈ (chartAt H p₀.2).source := by
    intro p hp
    simp only [hs, Set.mem_inter_iff, Set.mem_preimage] at hp
    exact hp.2
  have hbase : ∀ p ∈ s, φ p.1 p.2 ∈ (trivializationAt E (TangentSpace I) y₀).baseSet := by
    intro p hp
    rw [TangentBundle.trivializationAt_baseSet]
    exact hsrc p hp
  have hbase₀ : y₀ ∈ (trivializationAt E (TangentSpace I) y₀).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    exact mem_chart_source H y₀
  -- the trivialised derivative, on `s`
  have hL_s : ContMDiffWithinAt ((modelWithCornersSelf ℝ ℝ).prod I) 𝓘(ℝ,E) (⊤ : ℕ∞)
      (fun p : ℝ × M ↦ (trivializationAt E (TangentSpace I) y₀).continuousLinearMapAt ℝ
        (φ p.1 p.2)
        (mfderiv I I (φ p.1) p.2
          (Submission.Geodesic.frameVector (I := I) p₀.2 p.2 (Work.Diff.EXT.bB (E := E) i))))
      s p₀ := by
    have hcrux := contMDiffWithinAt_inTangent_mfderiv (I := I) hp₀ hφ hy₀ i
    have hmono := hcrux.mono (show s ⊆ J ×ˢ (Set.univ : Set M) from fun p hp => by
      rw [hs] at hp
      exact hp.1.1)
    exact hmono.congr
      (fun p hp => (inTangentCoordinates_apply_eq (I := I) (φ := φ) (p₀ := p₀) (p := p)
        (hframe p hp) (hsrc p hp) i).symm)
      ((inTangentCoordinates_apply_eq (I := I) (φ := φ) (p₀ := p₀) (p := p₀)
        (hframe p₀ hp₀s) (hsrc p₀ hp₀s) i).symm)
  have he : (⟨φ p₀.1 p₀.2,
      mfderiv I I (φ p₀.1) p₀.2
        (Submission.Geodesic.frameVector (I := I) p₀.2 p₀.2 (Work.Diff.EXT.bB (E := E) i))⟩
      : TangentBundle I M) ∈ (trivializationAt E (TangentSpace I) y₀).source := by
    rw [Trivialization.mem_source]
    rw [show (⟨φ p₀.1 p₀.2, _⟩ : TangentBundle I M).1 = y₀ from hy₀]
    exact hbase₀
  refine (Trivialization.contMDiffWithinAt_iff (e := trivializationAt E (TangentSpace I) y₀)
    (f := fun p : ℝ × M ↦ (⟨φ p.1 p.2, mfderiv I I (φ p.1) p.2
        (Submission.Geodesic.frameVector (I := I) p₀.2 p.2 (Work.Diff.EXT.bB (E := E) i))⟩
      : TangentBundle I M)) (s := J ×ˢ (Set.univ : Set M)) (x₀ := p₀) he).mpr ⟨hφ, ?_⟩
  refine (hL_s.congr (fun p hp => ?_) ?_).mono_of_mem_nhdsWithin hs_nhds
  · exact (Trivialization.continuousLinearMapAt_apply_of_mem
      (e := trivializationAt E (TangentSpace I) y₀) (R := ℝ) (b := φ p.1 p.2)
      (hbase p hp) _).symm
  · rw [hy₀]
    exact (Trivialization.continuousLinearMapAt_apply_of_mem
      (e := trivializationAt E (TangentSpace I) y₀) (R := ℝ) (b := y₀) hbase₀ _).symm

/-! ### The scalar entries of the frame matrix of the pulled-back metric -/

/-- **Joint smoothness of the `(i,j)`-entry of the frame matrix of the pulled-back metric.** -/
theorem contMDiffWithinAt_inner_mfderiv
    {J : Set ℝ} {φ : ℝ → Diffeomorph I I M M (⊤ : ℕ∞)} {A : ℝ → Submission.Diff.SMet I M}
    (hA : Submission.Diff.JointSmooth A J) {p₀ : ℝ × M}
    (hp₀ : p₀ ∈ J ×ˢ (Set.univ : Set M))
    (hφ : ContMDiffWithinAt ((modelWithCornersSelf ℝ ℝ).prod I) I (⊤ : ℕ∞)
      (fun p : ℝ × M ↦ φ p.1 p.2) (J ×ˢ (Set.univ : Set M)) p₀)
    {y₀ : M} (hy₀ : φ p₀.1 p₀.2 = y₀) (i j : Fin (Module.finrank ℝ E)) :
    ContMDiffWithinAt ((modelWithCornersSelf ℝ ℝ).prod I) (modelWithCornersSelf ℝ ℝ)
      (⊤ : ℕ∞)
      (fun p : ℝ × M ↦ (A p.1).inner (φ p.1 p.2)
        (mfderiv I I (φ p.1) p.2
          (Submission.Geodesic.frameVector (I := I) p₀.2 p.2 (Work.Diff.EXT.bB (E := E) i)))
        (mfderiv I I (φ p.1) p.2
          (Submission.Geodesic.frameVector (I := I) p₀.2 p.2 (Work.Diff.EXT.bB (E := E) j))))
      (J ×ˢ (Set.univ : Set M)) p₀ := by
  classical
  have hv := contMDiffWithinAt_tangentSection_mfderiv (I := I) hp₀ hφ hy₀ i
  have hw := contMDiffWithinAt_tangentSection_mfderiv (I := I) hp₀ hφ hy₀ j
  have hψ : ContMDiffWithinAt ((𝓘(ℝ,ℝ)).prod I)
      (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) (⊤ : ℕ∞)
      (fun p : ℝ × M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
        (φ p.1 p.2) ((A p.1).inner (φ p.1 p.2))) (J ×ˢ (Set.univ : Set M)) p₀ := by
    have hχ : ContMDiffWithinAt ((𝓘(ℝ,ℝ)).prod I) ((𝓘(ℝ,ℝ)).prod I) (⊤ : ℕ∞)
        (fun p : ℝ × M ↦ (p.1, φ p.1 p.2)) (J ×ˢ (Set.univ : Set M)) p₀ :=
      (contMDiffWithinAt_fst (s := J ×ˢ (Set.univ : Set M)) (p := p₀)).prodMk hφ
    have hmap : MapsTo (fun p : ℝ × M ↦ (p.1, φ p.1 p.2)) (J ×ˢ (Set.univ : Set M))
        (J ×ˢ (Set.univ : Set M)) := fun p hp => ⟨hp.1, Set.mem_univ _⟩
    exact (hA (p₀.1, φ p₀.1 p₀.2) ⟨hp₀.1, Set.mem_univ _⟩).comp p₀ hχ hmap
  have hmain := ContMDiffWithinAt.clm_bundle_apply₂ (𝕜 := ℝ) (B := M) (F₁ := E) (F₂ := E)
    (F₃ := ℝ)
    (E₁ := fun x : M ↦ TangentSpace I x) (E₂ := fun x : M ↦ TangentSpace I x)
    (E₃ := Bundle.Trivial M ℝ) (b := fun p : ℝ × M ↦ φ p.1 p.2)
    (v := fun p : ℝ × M ↦ mfderiv I I (φ p.1) p.2
      (Submission.Geodesic.frameVector (I := I) p₀.2 p.2 (Work.Diff.EXT.bB (E := E) i)))
    (w := fun p : ℝ × M ↦ mfderiv I I (φ p.1) p.2
      (Submission.Geodesic.frameVector (I := I) p₀.2 p.2 (Work.Diff.EXT.bB (E := E) j)))
    (ψ := fun p : ℝ × M ↦ (A p.1).inner (φ p.1 p.2))
    (s := J ×ˢ (Set.univ : Set M)) (x := p₀) hψ hv hw
  simp only [contMDiffWithinAt_totalSpace] at hmain
  exact hmain.2

/-! ### The frame matrix of the pulled-back metric family -/

/-- **Joint smoothness of the frame matrix of the pulled-back metric family** in the coordinate
frame of the chart at `p₀.2`. -/
theorem contMDiffWithinAt_frameMat_pullMetBilin
    {J : Set ℝ} {φ : ℝ → Diffeomorph I I M M (⊤ : ℕ∞)} {A : ℝ → Submission.Diff.SMet I M}
    (hA : Submission.Diff.JointSmooth A J)
    (hφ : ContMDiffOn ((modelWithCornersSelf ℝ ℝ).prod I) I (⊤ : ℕ∞)
      (fun p : ℝ × M ↦ φ p.1 p.2) (J ×ˢ (Set.univ : Set M)))
    {p₀ : ℝ × M} (hp₀ : p₀ ∈ J ×ˢ (Set.univ : Set M)) :
    ContMDiffWithinAt ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ (Work.Diff.EXT.MatE (E := E))) (⊤ : ℕ∞)
      (fun p : ℝ × M ↦ Work.Diff.EXT.frameMat (I := I) p₀.2 p.2
        (pullMetBilin (φ p.1) (A p.1) p.2)) (J ×ˢ (Set.univ : Set M)) p₀ := by
  refine contMDiffWithinAt_pi_space.mpr fun i ↦ contMDiffWithinAt_pi_space.mpr fun j ↦ ?_
  refine (contMDiffWithinAt_inner_mfderiv (I := I) hA hp₀ (hφ p₀ hp₀) rfl i j).congr
    (fun p hp => ?_) ?_
  · simp only [Work.Diff.EXT.frameMat, pullMetBilin_apply]
  · simp only [Work.Diff.EXT.frameMat, pullMetBilin_apply]

/-! ### From the frame matrix to the section, within a set -/

/-- **Within-set version of `Work.Diff.EXT.formFamSection_contMDiffAt_of_frameMat`.**  If the frame
matrix of a family of bilinear forms is jointly `C^∞` at `(τ, x₀)` on `s`, then so is the family
itself, as a section of the bundle of bilinear forms. -/
theorem formFamSection_contMDiffWithinAt_of_frameMat
    {γ : Work.Diff.EXT.FormFam (I := I) (M := M)} {τ : ℝ} {x₀ : M} {s : Set (ℝ × M)}
    (hp : (τ, x₀) ∈ s)
    (h : ContMDiffWithinAt ((modelWithCornersSelf ℝ ℝ).prod I)
        (modelWithCornersSelf ℝ (Work.Diff.EXT.MatE (E := E))) (⊤ : ℕ∞)
        (fun p : ℝ × M => Work.Diff.EXT.frameMat (I := I) x₀ p.2 (γ p.1 p.2)) s (τ, x₀)) :
    ContMDiffWithinAt ((modelWithCornersSelf ℝ ℝ).prod I)
      (I.prod (modelWithCornersSelf ℝ (E →L[ℝ] E →L[ℝ] ℝ))) (⊤ : ℕ∞)
      (Work.Diff.EXT.formFamSection (I := I) γ) s (τ, x₀) := by
  have hb' : ∀ᶠ p : ℝ × M in 𝓝 (τ, x₀), p.2 ∈ (chartAt H x₀).source :=
    continuous_snd.continuousAt.preimage_mem_nhds
      (IsOpen.mem_nhds (chartAt H x₀).open_source (mem_chart_source H x₀))
  have hb : ∀ᶠ p : ℝ × M in 𝓝[s] (τ, x₀), p.2 ∈ (chartAt H x₀).source :=
    hb'.filter_mono nhdsWithin_le_nhds
  refine (contMDiffWithinAt_hom_bundle (𝕜 := ℝ) (F₁ := E) (F₂ := E →L[ℝ] ℝ)
    (E₁ := fun x : M => TangentSpace I x) (E₂ := fun x : M => TangentSpace I x →L[ℝ] ℝ)
    (B := M) (M := ℝ × M) (IB := I) (IM := (𝓘(ℝ, ℝ)).prod I)
    (f := fun p : ℝ × M => Bundle.TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
      (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) p.2
      (γ p.1 p.2)) (s := s) (x₀ := (τ, x₀))).mpr ?_
  refine ⟨?_, ?_⟩
  · exact contMDiffWithinAt_snd
  · have hlift : ContDiff ℝ (⊤ : ℕ∞)
        (fun A : Work.Diff.EXT.MatE (E := E) => Work.Diff.EXT.matToBilin (E := E) A) :=
      ContinuousLinearMap.contDiff (𝕜 := ℝ) (E := Work.Diff.EXT.MatE (E := E))
        (F := (E →L[ℝ] E →L[ℝ] ℝ)) (n := (⊤ : ℕ∞)) (Work.Diff.EXT.matToBilin (E := E))
    have hmat : ContMDiffWithinAt ((modelWithCornersSelf ℝ ℝ).prod I)
        (modelWithCornersSelf ℝ (E →L[ℝ] E →L[ℝ] ℝ)) (⊤ : ℕ∞)
        (fun p : ℝ × M => Work.Diff.EXT.matToBilin (E := E)
          (Work.Diff.EXT.frameMat (I := I) x₀ p.2 (γ p.1 p.2))) s (τ, x₀) :=
      (hlift.contDiffAt.contMDiffWithinAt).comp (τ, x₀) h (fun p _ => Set.mem_univ _)
    refine hmat.congr_of_eventuallyEq ?_ ?_
    · filter_upwards [hb] with p hp'
      exact Work.Diff.EXT.inCoordinates_tangent_bilin (I := I) (x₀ := x₀) (x := p.2) hp'
        (φ := γ p.1 p.2)
    · exact Work.Diff.EXT.inCoordinates_tangent_bilin (I := I) (x₀ := x₀) (x := x₀)
        (mem_chart_source H x₀) (φ := γ τ x₀)


/-! ### The target theorem -/

/-- **The pulled-back metric family is jointly smooth.**  This is the DeTurck pull-back step of the
short-time existence proof: if `t ↦ φ t` is a jointly smooth family of diffeomorphisms and
`t ↦ A t` a jointly smooth family of metrics on the time set `J`, then so is
`t ↦ pullMetBilin (φ t) (A t)`. -/
theorem formFamJoint_pullMetBilin
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (φ : ℝ → Diffeomorph I I M M (⊤ : ℕ∞)) (A : ℝ → Submission.Diff.SMet I M) (J : Set ℝ)
    (hφ : ContMDiffOn ((modelWithCornersSelf ℝ ℝ).prod I) I (⊤ : ℕ∞)
      (fun p : ℝ × M ↦ φ p.1 p.2) (J ×ˢ Set.univ))
    (hA : Submission.Diff.JointSmooth A J) :
    ContMDiffOn ((modelWithCornersSelf ℝ ℝ).prod I)
      (I.prod (modelWithCornersSelf ℝ (E →L[ℝ] E →L[ℝ] ℝ))) (⊤ : ℕ∞)
      (Work.Diff.EXT.formFamSection
        (fun t x ↦ Work.Diff.STE.C2.pullMetBilin (φ t) (A t) x)) (J ×ˢ Set.univ) := by
  intro p hp
  exact formFamSection_contMDiffWithinAt_of_frameMat (I := I)
    (γ := fun t x ↦ Work.Diff.STE.C2.pullMetBilin (φ t) (A t) x)
    (τ := p.1) (x₀ := p.2) (s := J ×ˢ (Set.univ : Set M)) hp
    (contMDiffWithinAt_frameMat_pullMetBilin (I := I) hA hφ hp)


end Work.Diff.STE.C2
