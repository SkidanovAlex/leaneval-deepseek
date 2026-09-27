import Mathlib
import Submission.Work.SimplyConnected.ABS.manifold_smooth_upgrade

/-!
# A finite smooth partition of unity by chart balls

For a compact subset `K` of a second countable complex one-manifold `X` we produce a *finite*
family of chart balls (centres `x i`, radii `ρ i`) covering `K`, each with its model ball inside the
target of the chart, together with a subordinate smooth partition of unity `ψ i`:

* `ψ i ≥ 0` and `∑ i, ψ i y = 1` for `y ∈ K`,
* `ψ i` is `C^∞` for the *real* model `modelWithCornersSelf ℝ ℂ`,
* `tsupport (ψ i) ⊆ (chartAt ℂ (x i)) ⁻¹' Metric.ball ((chartAt ℂ (x i)) (x i)) (ρ i)`.

The proof is the standard one: complex `C^1` charts have holomorphic (hence analytic, hence smooth)
transitions (`Work.SimplyConnected.ABS.isManifold_self_model_real_infty`), so `X` is a smooth real
manifold; a compact set is covered by finitely many small chart balls
(`IsCompact.elim_finite_subcover`), and Mathlib's `SmoothPartitionOfUnity.exists_isSubordinate`
produces a partition of unity subordinate to that finite open cover of the closed set `K`.
-/

open scoped Manifold ContDiff Topology

noncomputable section

namespace Work.Analysis.RiemannSurface

/-- **A radius whose model ball at the centre of a chart lies in the chart target.** -/
lemma exists_pos_ball_chartAt_subset_target {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    (x : X) : ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball ((chartAt ℂ x) x) ρ ⊆ (chartAt ℂ x).target := by
  have hmem : (chartAt ℂ x) x ∈ (chartAt ℂ x).target :=
    (chartAt ℂ x).map_source (mem_chart_source ℂ x)
  obtain ⟨ρ, hρ, hsub⟩ := Metric.isOpen_iff.mp (chartAt ℂ x).open_target _ hmem
  exact ⟨ρ, hρ, hsub⟩

theorem exists_chartBall_smoothPartitionOfUnity {X : Type*} [TopologicalSpace X] [T2Space X]
    [SecondCountableTopology X] [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {K : Set X} (hK : IsCompact K) :
    ∃ (ι : Type) (_ : Fintype ι) (x : ι → X) (ρ : ι → ℝ) (ψ : ι → X → ℝ),
      (∀ i, 0 < ρ i) ∧
      (∀ i, Metric.ball ((chartAt ℂ (x i)) (x i) : ℂ) (ρ i) ⊆ (chartAt ℂ (x i)).target) ∧
      (K ⊆ ⋃ i, (chartAt ℂ (x i)) ⁻¹' (Metric.ball ((chartAt ℂ (x i)) (x i) : ℂ) (ρ i))) ∧
      (∀ i, ContMDiff (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℝ)
        ((⊤ : ℕ∞) : WithTop ℕ∞) (ψ i)) ∧
      (∀ i y, 0 ≤ ψ i y) ∧ (∀ y ∈ K, ∑ i, ψ i y = 1) ∧
      (∀ i, tsupport (ψ i) ⊆
        (chartAt ℂ (x i)) ⁻¹' (Metric.ball ((chartAt ℂ (x i)) (x i) : ℂ) (ρ i))) := by
  classical
  -- `X` is σ-compact, and it is a smooth real manifold
  haveI : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace ℂ X
  haveI : SigmaCompactSpace X := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : IsManifold (modelWithCornersSelf ℝ ℂ) (⊤ : WithTop ℕ∞) X :=
    Work.SimplyConnected.ABS.isManifold_self_model_real_infty
  -- choose a radius at every point
  choose ρ hρpos hρtarget using exists_pos_ball_chartAt_subset_target (X := X)
  -- the corresponding small open chart balls
  let V : X → Set X := fun x =>
    (chartAt ℂ x).symm '' (Metric.ball ((chartAt ℂ x) x) (ρ x))
  have hVopen : ∀ x, IsOpen (V x) := fun x =>
    (chartAt ℂ x).symm.isOpen_image_of_subset_source Metric.isOpen_ball
      (fun y hy => hρtarget x hy)
  have hxV : ∀ x, x ∈ V x := fun x =>
    ⟨(chartAt ℂ x) x, Metric.mem_ball_self (hρpos x),
      (chartAt ℂ x).left_inv (mem_chart_source ℂ x)⟩
  have hVsub : ∀ x,
      V x ⊆ (chartAt ℂ x) ⁻¹' (Metric.ball ((chartAt ℂ x) x) (ρ x)) := by
    intro x y hy
    obtain ⟨w, hw, rfl⟩ := hy
    show (chartAt ℂ x) ((chartAt ℂ x).symm w) ∈ Metric.ball ((chartAt ℂ x) x) (ρ x)
    rw [(chartAt ℂ x).right_inv (hρtarget x hw)]
    exact hw
  -- finitely many of them cover `K`
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover V hVopen fun y _ =>
    Set.mem_iUnion.mpr ⟨y, hxV y⟩
  -- reindex the finite set by `Fin t.card` so that the index type lives in `Type`
  let x : Fin t.card → X := fun i => ((Finset.equivFin t).symm i : X)
  have hx_eq : ∀ i : Fin t.card, x i = (((Finset.equivFin t).symm i : ↥t) : X) := fun _ => rfl
  -- the induced open cover of the closed set `K`
  have hUopen : ∀ i : Fin t.card, IsOpen (V (x i)) := fun i => hVopen (x i)
  have hUcover : K ⊆ ⋃ i : Fin t.card, V (x i) := by
    intro y hy
    obtain ⟨i, hit, hyi⟩ := Set.mem_iUnion₂.mp (ht hy)
    have hxi : x (Finset.equivFin t ⟨i, hit⟩) = (i : X) := by
      rw [hx_eq, Equiv.symm_apply_apply]
    refine Set.mem_iUnion.mpr ⟨Finset.equivFin t ⟨i, hit⟩, ?_⟩
    simp only [hxi]
    exact hyi
  obtain ⟨f, hf⟩ := SmoothPartitionOfUnity.exists_isSubordinate (modelWithCornersSelf ℝ ℂ)
    (s := K) hK.isClosed (fun i : Fin t.card => V (x i)) hUopen hUcover
  refine ⟨Fin t.card, inferInstance, x, fun i => ρ (x i), fun i => f i,
    fun i => hρpos (x i), fun i => hρtarget (x i), ?_, ?_, ?_, ?_, ?_⟩
  · -- `K` is covered by the chart balls
    intro y hy
    obtain ⟨i, hit, hyi⟩ := Set.mem_iUnion₂.mp (ht hy)
    have hxi : x (Finset.equivFin t ⟨i, hit⟩) = (i : X) := by
      rw [hx_eq, Equiv.symm_apply_apply]
    refine Set.mem_iUnion.mpr ⟨Finset.equivFin t ⟨i, hit⟩, ?_⟩
    simp only [hxi]
    exact hVsub i hyi
  · intro i
    exact (f i).contMDiff
  · intro i y
    exact f.nonneg i y
  · intro y hy
    have := SmoothPartitionOfUnity.sum_finsupport' f y hy (Finset.subset_univ (f.finsupport y))
    simpa using this
  · intro i
    exact (hf i).trans (hVsub (x i))

end Work.Analysis.RiemannSurface
