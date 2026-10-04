import Mathlib
import Submission.Work.Diff.GE.deps
import Submission.Work.Diff.GE.joint_deriv
import Submission.Work.Diff.GE.cGram_eq_sum_gramInv
import Submission.Work.Diff.EXT.contMDiffAt_matrix_inv

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.GE

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
  [IsManifold I (⊤ : ℕ∞) M] [I.Boundaryless]

/-- Joint smoothness of a metric family on a set: the `ContMDiffOn` form of `JointSmooth`. -/
abbrev MetSmoothOn (G : ℝ → SMet I M) (S : Set (ℝ × M)) : Prop :=
  ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
    (fun p : ℝ × M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
      (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) p.2
      ((G p.1).inner p.2)) S

/-- The slices of a jointly smooth family are smooth (within form). -/
theorem slice_contMDiffWithinAt {u : ℝ → M → ℝ} {T t : ℝ} {U : Set M} (ht : t ∈ Ico 0 T)
    (hu : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ (fun p : ℝ × M ↦ u p.1 p.2) (Ico 0 T ×ˢ U))
    {x : M} (hx : x ∈ U) :
    ContMDiffWithinAt I 𝓘(ℝ, ℝ) ∞ (u t) U x := by
  have h1 : ContMDiffOn I (𝓘(ℝ, ℝ).prod I) ∞ (fun x : M ↦ (t, x)) U :=
    ContMDiffOn.prodMk contMDiffOn_const contMDiffOn_id
  have h2 : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun x : M ↦ u t x) U :=
    hu.comp h1 (fun x hx => ⟨ht, hx⟩)
  exact h2 x hx

/-- The coordinate frame vector of a chart is a `C^∞` section at every point of the chart source.

(The proof is the one of `Submission.Geodesic.contMDiffAt_frameSection`; it uses no metric
structure, so we may state it without the Riemannian-bundle instances.) -/
theorem cFrame_contMDiffAt (x₀ : M) (i : Fin (Module.finrank ℝ E)) {x : M}
    (hx : x ∈ (chartAt H x₀).source) :
    ContMDiffAt I I.tangent ∞ (T% (cFrame (I := I) x₀ i)) x := by
  rw [Trivialization.contMDiffAt_section_iff
    (trivializationAt E (TangentSpace I) x₀) (by simpa using hx)]
  refine (contMDiffAt_const (c := cBasis (E := E) i)).congr_of_eventuallyEq ?_
  filter_upwards [(trivializationAt E (TangentSpace I) x₀).open_baseSet.mem_nhds
    (by simpa using hx)] with y hy
  rw [show cFrame (I := I) x₀ i y
      = (trivializationAt E (TangentSpace I) x₀).symmL ℝ y (cBasis (E := E) i) from rfl]
  rw [Trivialization.symmL_apply (e := trivializationAt E (TangentSpace I) x₀) (R := ℝ) hy
    (cBasis (E := E) i)]
  exact congrArg Prod.snd ((trivializationAt E (TangentSpace I) x₀).apply_mk_symm hy
    (cBasis (E := E) i))

/-- The coordinate frame vector of a chart is a `C^∞` section on the chart source. -/
theorem cFrame_contMDiffOn (x₀ : M) (i : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I I.tangent ∞ (T% (cFrame (I := I) x₀ i)) (chartAt H x₀).source :=
  fun _ hx => (cFrame_contMDiffAt (I := I) x₀ i hx).contMDiffWithinAt

/-- The chart reading of a family jointly smooth on `[0,T) × (chart source)`. -/
theorem chartPush_source (x₀ : M) {u : ℝ → M → ℝ} {T : ℝ}
    (hu : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ (fun p : ℝ × M ↦ u p.1 p.2)
      (Ico 0 T ×ˢ (chartAt H x₀).source)) :
    ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, E))) 𝓘(ℝ, ℝ) ∞
      (fun q : ℝ × E ↦ u q.1 ((extChartAt I x₀).symm q.2))
      (Ico 0 T ×ˢ (extChartAt I x₀).target) := by
  have hsymm : ContMDiffOn (𝓘(ℝ, E)) I ∞ (fun z : E ↦ (extChartAt I x₀).symm z)
      (extChartAt I x₀).target := contMDiffOn_extChartAt_symm x₀
  have hmap : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, E))) ((𝓘(ℝ, ℝ)).prod I) ∞
      (fun q : ℝ × E ↦ (q.1, (extChartAt I x₀).symm q.2))
      (Ico 0 T ×ˢ (extChartAt I x₀).target) := by
    intro q hq
    refine ((contMDiffWithinAt_id (s := Ico 0 T ×ˢ (extChartAt I x₀).target) (x := q)).fst).prodMk ?_
    exact (hsymm q.2 hq.2).comp q contMDiffWithinAt_snd (fun p hp => hp.2)
  have hmem : ∀ q ∈ Ico 0 T ×ˢ (extChartAt I x₀).target,
      (extChartAt I x₀).symm q.2 ∈ (chartAt H x₀).source := by
    intro q hq
    rw [← extChartAt_source (I := I) (x := x₀)]
    exact (extChartAt I x₀).map_target hq.2
  exact hu.comp hmap (fun q hq => ⟨hq.1, hmem q hq⟩)

/-- **Joint smoothness of a metric pairing (within form).** -/
theorem metricPair_jointSmoothOn {G : ℝ → SMet I M} {T : ℝ} {U : Set M}
    (hG : MetSmoothOn (I := I) (M := M) G (Ico 0 T ×ˢ U))
    {Y Z : Π x : M, TangentSpace I x}
    (hY : ContMDiffOn I I.tangent ∞ (T% Y) U) (hZ : ContMDiffOn I I.tangent ∞ (T% Z) U) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M ↦ (G p.1).inner p.2 (Y p.2) (Z p.2)) (Ico 0 T ×ˢ U) := by
  intro p hp
  obtain ⟨t, x⟩ := p
  have hYc : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      ((T% Y) ∘ (Prod.snd : ℝ × M → M)) (Ico 0 T ×ˢ U) (t, x) :=
    (hY x hp.2).comp (t, x) contMDiffWithinAt_snd (fun q hq => hq.2)
  have hZc : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      ((T% Z) ∘ (Prod.snd : ℝ × M → M)) (Ico 0 T ×ˢ U) (t, x) :=
    (hZ x hp.2).comp (t, x) contMDiffWithinAt_snd (fun q hq => hq.2)
  have hmain : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, ℝ)) ∞
      (fun m : ℝ × M ↦ TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ) m.2
        ((G m.1).inner m.2 (Y m.2) (Z m.2))) (Ico 0 T ×ˢ U) (t, x) :=
    ContMDiffWithinAt.clm_bundle_apply₂ (𝕜 := ℝ) (B := M) (F₁ := E) (F₂ := E) (F₃ := ℝ)
      (E₁ := fun x : M => TangentSpace I x) (E₂ := fun x : M => TangentSpace I x)
      (E₃ := Bundle.Trivial M ℝ) (b := fun m : ℝ × M => Prod.snd m)
      (v := fun m : ℝ × M => Y (Prod.snd m)) (w := fun m : ℝ × M => Z (Prod.snd m))
      (ψ := fun m : ℝ × M => (G m.1).inner (Prod.snd m)) (s := Ico 0 T ×ˢ U) (x := (t, x))
      (hG (t, x) hp) hYc hZc
  simp only [contMDiffWithinAt_totalSpace] at hmain
  exact hmain.2

/-- **Joint smoothness of the metric coefficients in the coordinate frame (within form).** -/
theorem mComp_jointSmoothOn {G : ℝ → SMet I M} {T : ℝ} (x₀ : M)
    (hG : MetSmoothOn (I := I) (M := M) G (Ico 0 T ×ˢ (chartAt H x₀).source))
    (i j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M ↦ mComp (I := I) G x₀ i j p.1 p.2)
      (Ico 0 T ×ˢ (chartAt H x₀).source) := by
  have h := metricPair_jointSmoothOn (I := I) (M := M) (U := (chartAt H x₀).source) hG
    (cFrame_contMDiffOn (I := I) x₀ i) (cFrame_contMDiffOn (I := I) x₀ j)
  simpa only [mComp] using h

/-- **Joint smoothness of the inverse of a jointly smooth invertible matrix family (within form).** -/
theorem matrixInv_contMDiffWithinAt {n : ℕ} {Mx : ℝ × M → (Fin n → Fin n → ℝ)}
    {s : Set (ℝ × M)} {p : ℝ × M}
    (hM : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, Fin n → Fin n → ℝ) ∞ Mx s p)
    (hdet : (Matrix.of (Mx p)).det ≠ 0) :
    ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, Fin n → Fin n → ℝ) ∞
      (fun p => fun i j => ((Matrix.of (Mx p))⁻¹) i j) s p := by
  have hg : ContDiffWithinAt ℝ ∞
      (fun A : Fin n → Fin n → ℝ => fun i j => (Matrix.of A)⁻¹ i j) univ (Mx p) :=
    (Work.Diff.EXT.contDiffAt_matrix_inv_pi (Mx p) hdet).contDiffWithinAt
  exact hg.comp_contMDiffWithinAt hM (fun _ _ => trivial)

/-- **Joint smoothness of the inverse Gram matrix entries (within form).** -/
theorem gramInv_jointSmoothOn {G : ℝ → SMet I M} {T : ℝ} (x₀ : M)
    (hG : MetSmoothOn (I := I) (M := M) G (Ico 0 T ×ˢ (chartAt H x₀).source))
    (k m : Fin (Module.finrank ℝ E)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M ↦ GramInv (I := I) G x₀ p.1 p.2 k m)
      (Ico 0 T ×ˢ (chartAt H x₀).source) := by
  intro p hp
  obtain ⟨t, y⟩ := p
  have hy : y ∈ (chartAt H x₀).source := hp.2
  have hMx : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I)
      𝓘(ℝ, Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ) ∞
      (fun p : ℝ × M ↦ fun i j ↦ GramM (I := I) G x₀ p.1 p.2 i j)
      (Ico 0 T ×ˢ (chartAt H x₀).source) (t, y) := by
    rw [contMDiffWithinAt_pi_space]
    intro i
    rw [contMDiffWithinAt_pi_space]
    intro j
    simpa only [GramM] using
      mComp_jointSmoothOn (I := I) (M := M) x₀ hG i j (t, y) hp
  have hdet : (Matrix.of (fun i j ↦ GramM (I := I) G x₀ t y i j)).det ≠ 0 := by
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(G t).toRiemannianMetric⟩
    haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
    have hnd := CGramInv.gramBil_nondegenerate (I := I) G x₀ hy t
    have h := (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero (cBasis (E := E))).mp hnd
    rwa [← CGramInv.GramM_eq_toMatrix (I := I) G x₀ y t] at h
  have hcomp : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I)
      𝓘(ℝ, Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ) ∞
      (fun p : ℝ × M ↦ fun i j ↦
        ((Matrix.of (fun i j ↦ GramM (I := I) G x₀ p.1 p.2 i j))⁻¹) i j)
      (Ico 0 T ×ˢ (chartAt H x₀).source) (t, y) :=
    matrixInv_contMDiffWithinAt (I := I) (M := M)
      (n := Module.finrank ℝ E) hMx hdet
  have hkm := (contMDiffWithinAt_pi_space.mp (contMDiffWithinAt_pi_space.mp hcomp k) m)
  exact hkm

/-- The `mvfderiv` of a family along the coordinate frame, in the chart at the point. -/
theorem mvfderiv_cFrame_eq {u : ℝ → M → ℝ} {x₀ : M} {t : ℝ} {x : M}
    (hx : x ∈ (chartAt H x₀).source) (hmd : MDifferentiableAt I 𝓘(ℝ, ℝ) (u t) x)
    (k : Fin (Module.finrank ℝ E)) :
    mvfderiv I (u t) x (cFrame (I := I) x₀ k x)
      = fderiv ℝ (fun z : E ↦ u t ((extChartAt I x₀).symm z)) ((extChartAt I x₀) x)
          (cBasis (E := E) k) := by
  rw [mvfderiv_chart (I := I) x₀ hx hmd (cFrame (I := I) x₀ k x)]
  congr 1
  rw [show cFrame (I := I) x₀ k x
      = (trivializationAt E (TangentSpace I) x₀).symmL ℝ x (cBasis (E := E) k) from rfl]
  exact Trivialization.continuousLinearMapAt_symmL (trivializationAt E (TangentSpace I) x₀)
    (by rw [TangentBundle.trivializationAt_baseSet]; exact hx) (cBasis (E := E) k)

/-- The model-space version of the previous lemma, with a constant direction. -/
theorem partial_fderiv_smooth_const {h : ℝ × E → ℝ} {c : E} {Ω : Set E} {T t₀ : ℝ} {z₀ : E}
    (hΩ : IsOpen Ω) (hz₀ : z₀ ∈ Ω) (ht₀ : t₀ ∈ Ico 0 T)
    (hh : ContMDiffWithinAt ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, E))) 𝓘(ℝ, ℝ) ∞ h
      (Ico 0 T ×ˢ Ω) (t₀, z₀)) :
    ContMDiffWithinAt ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, E))) 𝓘(ℝ, ℝ) ∞
      (fun q : ℝ × E ↦ fderiv ℝ (fun z : E ↦ h (q.1, z)) q.2 c)
      (Ico 0 T ×ˢ Ω) (t₀, z₀) := by
  simpa only using partial_fderiv_smooth (E := E) (c := fun _ : ℝ × E ↦ c) hΩ hz₀ ht₀ hh
    (contMDiffWithinAt_const (c := c))

/-- **The coordinate derivative of a jointly smooth family along the coordinate frame is jointly
smooth (within form).**  This is the analytic core of the smoothness of `rmChartExpr`: only the
*space* variable is differentiated, so the one-sidedness of the time variable is harmless. -/
theorem dOp_cFrame_jointSmoothOn {u : ℝ → M → ℝ} {T : ℝ} (x₀ : M)
    (hu : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ (fun p : ℝ × M ↦ u p.1 p.2)
      (Ico 0 T ×ˢ (chartAt H x₀).source))
    (k : Fin (Module.finrank ℝ E)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M ↦ mvfderiv I (u p.1) p.2 (cFrame (I := I) x₀ k p.2))
      (Ico 0 T ×ˢ (chartAt H x₀).source) := by
  intro p hp
  obtain ⟨t₀, y⟩ := p
  have hy : y ∈ (chartAt H x₀).source := hp.2
  have hsrc : (extChartAt I x₀).source = (chartAt H x₀).source :=
    extChartAt_source (I := I) (x := x₀)
  have hopen : IsOpen (extChartAt I x₀).target := isOpen_extChartAt_target (I := I) x₀
  have hz₀ : (extChartAt I x₀) y ∈ (extChartAt I x₀).target :=
    (extChartAt I x₀).map_source (by rw [hsrc]; exact hy)
  -- the chart reading of the family
  have hh : ContMDiffWithinAt ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, E))) 𝓘(ℝ, ℝ) ∞
      (fun q : ℝ × E ↦ u q.1 ((extChartAt I x₀).symm q.2))
      (Ico 0 T ×ˢ (extChartAt I x₀).target) (t₀, (extChartAt I x₀) y) :=
    (chartPush_source (I := I) x₀ hu) (t₀, (extChartAt I x₀) y) ⟨hp.1, hz₀⟩
  -- the model-space derivative is jointly smooth
  have hmain := partial_fderiv_smooth_const (E := E)
    (h := fun q : ℝ × E ↦ u q.1 ((extChartAt I x₀).symm q.2))
    (c := cBasis (E := E) k)
    (Ω := (extChartAt I x₀).target) (T := T) (t₀ := t₀) (z₀ := (extChartAt I x₀) y)
    hopen hz₀ hp.1 hh
  -- pull back to the manifold along the chart
  have hφ : ContMDiffWithinAt I 𝓘(ℝ, E) ∞ (fun z : M ↦ (extChartAt I x₀) z)
      (extChartAt I x₀).source y := by
    rw [hsrc]
    exact (contMDiffOn_extChartAt (I := I) (n := ∞) (x := x₀)) y hy
  have hθ2 : ContMDiffWithinAt ((𝓘(ℝ, ℝ)).prod I) (𝓘(ℝ, E)) ∞
      (fun p : ℝ × M ↦ (extChartAt I x₀) p.2)
      (Ico 0 T ×ˢ (extChartAt I x₀).source) (t₀, y) :=
    hφ.comp (t₀, y) contMDiffWithinAt_snd (fun q hq => hq.2)
  have hΘ : ContMDiffWithinAt ((𝓘(ℝ, ℝ)).prod I) ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, E))) ∞
      (fun p : ℝ × M ↦ (p.1, (extChartAt I x₀) p.2))
      (Ico 0 T ×ˢ (extChartAt I x₀).source) (t₀, y) :=
    ((contMDiffWithinAt_id (s := Ico 0 T ×ˢ (extChartAt I x₀).source)
      (x := (t₀, y))).fst).prodMk hθ2
  have hmaps : MapsTo (fun p : ℝ × M ↦ (p.1, (extChartAt I x₀) p.2))
      (Ico 0 T ×ˢ (extChartAt I x₀).source) (Ico 0 T ×ˢ (extChartAt I x₀).target) := by
    intro q hq
    exact ⟨hq.1, (extChartAt I x₀).map_source hq.2⟩
  have hcomp := hmain.comp (t₀, y) hΘ hmaps
  rw [hsrc] at hcomp
  -- identify the two functions
  refine hcomp.congr (fun q hq => ?_) ?_
  · obtain ⟨t, x⟩ := q
    have hx : x ∈ (chartAt H x₀).source := hq.2
    have hslice : ContMDiffWithinAt I 𝓘(ℝ, ℝ) ∞ (u t) (chartAt H x₀).source x :=
      slice_contMDiffWithinAt (I := I) (M := M) hq.1 hu hx
    have hmd : MDifferentiableAt I 𝓘(ℝ, ℝ) (u t) x :=
      (hslice.contMDiffAt ((chartAt H x₀).open_source.mem_nhds hx)).mdifferentiableAt (by simp)
    simpa only [Function.comp_apply] using mvfderiv_cFrame_eq (I := I) hx hmd k
  · have hslice : ContMDiffWithinAt I 𝓘(ℝ, ℝ) ∞ (u t₀) (chartAt H x₀).source y :=
      slice_contMDiffWithinAt (I := I) (M := M) hp.1 hu hy
    have hmd : MDifferentiableAt I 𝓘(ℝ, ℝ) (u t₀) y :=
      (hslice.contMDiffAt ((chartAt H x₀).open_source.mem_nhds hy)).mdifferentiableAt (by simp)
    simpa only [Function.comp_apply] using mvfderiv_cFrame_eq (I := I) hy hmd k

/-- The `dOp` form of the previous lemma. -/
theorem dOp_jointSmoothOn {u : ℝ → M → ℝ} {T : ℝ} (x₀ : M)
    (hu : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ (fun p : ℝ × M ↦ u p.1 p.2)
      (Ico 0 T ×ˢ (chartAt H x₀).source))
    (k : Fin (Module.finrank ℝ E)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M ↦ dOp (I := I) x₀ k u p.1 p.2)
      (Ico 0 T ×ˢ (chartAt H x₀).source) := by
  simpa only [dOp] using dOp_cFrame_jointSmoothOn (I := I) (M := M) x₀ hu k

/-- **Joint smoothness of the lowered Christoffel pairings (within form).** -/
theorem koszulPair_jointSmoothOn {G : ℝ → SMet I M} {T : ℝ} (x₀ : M)
    (hG : MetSmoothOn (I := I) (M := M) G (Ico 0 T ×ˢ (chartAt H x₀).source))
    (a b c : Fin (Module.finrank ℝ E)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M ↦ koszulPair (I := I) G x₀ a b c p.1 p.2)
      (Ico 0 T ×ˢ (chartAt H x₀).source) := by
  have h1 := dOp_jointSmoothOn (I := I) (M := M) x₀
    (u := fun t y ↦ mComp (I := I) G x₀ b c t y)
    (mComp_jointSmoothOn (I := I) (M := M) x₀ hG b c) a
  have h2 := dOp_jointSmoothOn (I := I) (M := M) x₀
    (u := fun t y ↦ mComp (I := I) G x₀ c a t y)
    (mComp_jointSmoothOn (I := I) (M := M) x₀ hG c a) b
  have h3 := dOp_jointSmoothOn (I := I) (M := M) x₀
    (u := fun t y ↦ mComp (I := I) G x₀ a b t y)
    (mComp_jointSmoothOn (I := I) (M := M) x₀ hG a b) c
  have hmain : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M ↦ (1 / 2 : ℝ) * (dOp (I := I) x₀ a (fun t y ↦ mComp (I := I) G x₀ b c t y)
            p.1 p.2
          + dOp (I := I) x₀ b (fun t y ↦ mComp (I := I) G x₀ c a t y) p.1 p.2
          - dOp (I := I) x₀ c (fun t y ↦ mComp (I := I) G x₀ a b t y) p.1 p.2))
      (Ico 0 T ×ˢ (chartAt H x₀).source) :=
    (contMDiffOn_const (c := (1 / 2 : ℝ))).mul ((h1.add h2).sub h3)
  simpa only [koszulPair, dOp, mComp] using hmain

/-- **Joint smoothness of the coordinate derivative of a Christoffel pairing (within form).** -/
theorem dOpKoszul_jointSmoothOn {G : ℝ → SMet I M} {T : ℝ} (x₀ : M)
    (hG : MetSmoothOn (I := I) (M := M) G (Ico 0 T ×ˢ (chartAt H x₀).source))
    (i j l k : Fin (Module.finrank ℝ E)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M ↦ dOp (I := I) x₀ i (koszulPair (I := I) G x₀ j l k) p.1 p.2)
      (Ico 0 T ×ˢ (chartAt H x₀).source) :=
  dOp_jointSmoothOn (I := I) (M := M) x₀
    (u := fun t y ↦ koszulPair (I := I) G x₀ j l k t y)
    (koszulPair_jointSmoothOn (I := I) (M := M) x₀ hG j l k) i

end

theorem rmChartExpr_joint_smooth
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    {G : ℝ → SMet I M} {T : ℝ} (hJs : JointSmooth G (Ico 0 T)) (x₀ : M)
    (hder : ∀ {u : ℝ → M → ℝ} {X : Π y : M, TangentSpace I y},
      ContMDiffOn (𝓘(ℝ,ℝ).prod I) 𝓘(ℝ,ℝ) ∞ (fun p : ℝ × M ↦ u p.1 p.2) (Ico 0 T ×ˢ univ) →
      CMDiff ∞ (T% X) →
      ContMDiffOn (𝓘(ℝ,ℝ).prod I) 𝓘(ℝ,ℝ) ∞
        (fun p : ℝ × M ↦ mvfderiv I (u p.1) p.2 (X p.2)) (Ico 0 T ×ˢ univ))
    (i j k l : Fin (Module.finrank ℝ E)) :
    ContMDiffOn (𝓘(ℝ,ℝ).prod I) 𝓘(ℝ,ℝ) ∞
      (fun p : ℝ × M ↦ rmChartExpr (I := I) G x₀ i j k l p.1 p.2)
      (Ico 0 T ×ˢ (chartAt H x₀).source) := by
  have hG : MetSmoothOn (I := I) (M := M) G (Ico 0 T ×ˢ (chartAt H x₀).source) := by
    have h0 : MetSmoothOn (I := I) (M := M) G (Ico 0 T ×ˢ (univ : Set M)) := hJs
    exact h0.mono (fun p hp => ⟨hp.1, mem_univ _⟩)
  intro p hp
  obtain ⟨t, y⟩ := p
  simp only [rmChartExpr]
  refine (((dOpKoszul_jointSmoothOn (I := I) (M := M) x₀ hG i j l k (t, y) hp).sub ?_).sub
    (dOpKoszul_jointSmoothOn (I := I) (M := M) x₀ hG j i l k (t, y) hp)).add ?_
  · exact ContMDiffWithinAt.sum (t := Finset.univ) (fun m _ ↦
      ContMDiffWithinAt.sum (t := Finset.univ) (fun n _ ↦
        ((gramInv_jointSmoothOn (I := I) (M := M) x₀ hG m n (t, y) hp).mul
          (koszulPair_jointSmoothOn (I := I) (M := M) x₀ hG j l m (t, y) hp)).mul
          (koszulPair_jointSmoothOn (I := I) (M := M) x₀ hG i k n (t, y) hp)))
  · exact ContMDiffWithinAt.sum (t := Finset.univ) (fun m _ ↦
      ContMDiffWithinAt.sum (t := Finset.univ) (fun n _ ↦
        ((gramInv_jointSmoothOn (I := I) (M := M) x₀ hG m n (t, y) hp).mul
          (koszulPair_jointSmoothOn (I := I) (M := M) x₀ hG i l m (t, y) hp)).mul
          (koszulPair_jointSmoothOn (I := I) (M := M) x₀ hG j k n (t, y) hp)))

end Work.Diff.GE
