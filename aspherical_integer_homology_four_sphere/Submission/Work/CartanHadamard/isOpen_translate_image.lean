import Mathlib
import Submission.Work.CartanHadamard.Translate
import Submission.Work.CartanHadamard.Basic
import Submission.Work.RiemLib.API

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.CartanHadamard

open scoped Manifold ContDiff Bundle Topology ENNReal in
theorem isOpen_translate_image
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0)
    (hK : ∀ K : ℝ, 0 < K → Submission.RauchK.CurvLe cov K)
    {p y : M} {vt : TangentSpace I p}
    (hvt : Submission.GlobalExp.GExp (cov := cov) hmet p vt = y) {ρ : ℝ} (hρpos : 0 < ρ)
    (hρ : Submission.InjRadius.InjAtLeast hmet y ρ)
    (hcont : ContinuousOn (fun w : TangentSpace I y =>
        translate (cov := cov) hmet htor hK vt w) (Metric.ball (0 : TangentSpace I y) ρ)) :
    IsOpen ((fun w : TangentSpace I y =>
        translate (cov := cov) hmet htor hK vt w) '' Metric.ball (0 : TangentSpace I y) ρ) := by
  classical
  let F : TangentSpace I y → TangentSpace I p :=
    fun w => translate (cov := cov) hmet htor hK vt w
  change IsOpen (F '' Metric.ball (0 : TangentSpace I y) ρ)
  have hFapply : ∀ w : TangentSpace I y,
      Submission.GlobalExp.GExp (cov := cov) hmet p (F w)
        = Submission.GlobalExp.GExp (cov := cov) hmet y w :=
    fun w => translate_apply (cov := cov) hmet htor hK hvt w
  have hGp : IsLocalHomeomorph (fun v : TangentSpace I p =>
      Submission.GlobalExp.GExp (cov := cov) hmet p v) :=
    isLocalHomeomorph_GExp (cov := cov) hmet htor hK p
  have hGy : IsLocalHomeomorph (fun w : TangentSpace I y =>
      Submission.GlobalExp.GExp (cov := cov) hmet y w) :=
    isLocalHomeomorph_GExp (cov := cov) hmet htor hK y
  have hFcont : ContinuousOn F (Metric.ball (0 : TangentSpace I y) ρ) := hcont
  rw [isOpen_iff_mem_nhds]
  intro z hz
  obtain ⟨w₀, hw₀ball, rfl⟩ := hz
  let ψ : OpenPartialHomeomorph M (TangentSpace I p) := hGp.localInverseAt (F w₀)
  have hψ_apply : ∀ {y' : M}, y' ∈ ψ.source →
      Submission.GlobalExp.GExp (cov := cov) hmet p (ψ y') = y' :=
    fun {y'} hy => hGp.apply_localInverseAt_of_mem hy
  have hψ_inj : Set.InjOn (fun v : TangentSpace I p =>
      Submission.GlobalExp.GExp (cov := cov) hmet p v) ψ.target :=
    hGp.injOn_localInverseAt_target
  have hw₀target : F w₀ ∈ ψ.target := hGp.self_mem_localInverseAt_target
  have hw₀src : Submission.GlobalExp.GExp (cov := cov) hmet y w₀ ∈ ψ.source := by
    rw [← hFapply w₀]
    exact hGp.apply_self_mem_localInverseAt_source
  let O : Set (TangentSpace I y) :=
    (Metric.ball (0 : TangentSpace I y) ρ ∩ F ⁻¹' ψ.target) ∩
      (fun w : TangentSpace I y => Submission.GlobalExp.GExp (cov := cov) hmet y w) ⁻¹' ψ.source
  have hOopen : IsOpen O :=
    (hFcont.isOpen_inter_preimage Metric.isOpen_ball ψ.open_target).inter
      (hGy.continuous.isOpen_preimage ψ.source ψ.open_source)
  have hw₀O : w₀ ∈ O := ⟨⟨hw₀ball, hw₀target⟩, hw₀src⟩
  have hF_eq : ∀ w ∈ O, F w = ψ (Submission.GlobalExp.GExp (cov := cov) hmet y w) := by
    intro w hw
    have hwψ : Submission.GlobalExp.GExp (cov := cov) hmet y w ∈ ψ.source := hw.2
    have hFψ : F w ∈ ψ.target := hw.1.2
    refine hψ_inj hFψ (ψ.map_source hwψ) ?_
    exact (hFapply w).trans (hψ_apply hwψ).symm
  have hOball : O ⊆ Metric.ball (0 : TangentSpace I y) ρ := fun w hw => hw.1.1
  have hGyO_open : IsOpen ((fun w : TangentSpace I y =>
      Submission.GlobalExp.GExp (cov := cov) hmet y w) '' O) :=
    hGy.isOpenMap O hOopen
  have hGyO_sub : ((fun w : TangentSpace I y =>
      Submission.GlobalExp.GExp (cov := cov) hmet y w) '' O) ⊆ ψ.source := by
    rintro _ ⟨w, hw, rfl⟩
    exact hw.2
  have hImgOpen : IsOpen (ψ '' ((fun w : TangentSpace I y =>
      Submission.GlobalExp.GExp (cov := cov) hmet y w) '' O)) :=
    ψ.isOpen_image_of_subset_source hGyO_open hGyO_sub
  have hEq : ψ '' ((fun w : TangentSpace I y =>
      Submission.GlobalExp.GExp (cov := cov) hmet y w) '' O) = F '' O := by
    apply Set.Subset.antisymm
    · rintro _ ⟨m, ⟨w, hw, rfl⟩, rfl⟩
      exact ⟨w, hw, hF_eq w hw⟩
    · rintro _ ⟨w, hw, rfl⟩
      exact ⟨_, ⟨w, hw, rfl⟩, (hF_eq w hw).symm⟩
  rw [hEq] at hImgOpen
  refine Filter.mem_of_superset (hImgOpen.mem_nhds ⟨w₀, hw₀O, rfl⟩) ?_
  rintro _ ⟨w, hw, rfl⟩
  exact ⟨w, hOball hw, rfl⟩

end Work.CartanHadamard
