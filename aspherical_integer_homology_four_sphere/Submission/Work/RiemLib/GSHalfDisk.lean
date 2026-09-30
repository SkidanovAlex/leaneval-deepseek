import Submission.Work.RiemLib.GSDisk
import Submission.Work.RiemLib.Commons.Topology.Metric.closedBall_homeo_euclidean_pair

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Small metric balls are topological disks, with their boundary

`GSDisk.exists_pos_homeo_closedBall` provides the exponential-map homeomorphism onto a small metric
ball.  Here we transport it to the standard model `Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1`
(via the commons lemma `Commons.Topology.Metric.closedBall_homeo_euclidean_pair`) and record the
boundary correspondence: the level set `{d(x₀,·) = t}` corresponds to the unit sphere, for every
radius `t` smaller than a fixed `ε₀ > 0`.

This is the first ingredient of the two-disk assembly of the Grove–Shiohama sphere theorem; the
collar between two small spheres is `GSSlab.homeo_level_region_of_diam` (or its formula refinement
`Commons.Topology.homeo_level_times_of_flow_crossing_formula`), and the gluing of the disk with the
collar is `Commons.Topology.Sphere.disk_glue_collar`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal InnerProductSpace
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.Distance
open Submission.EDist
open Submission.GlobalExp

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

namespace Submission.GSHalfDisk

noncomputable section

variable [I.Boundaryless] [Nontrivial E] [CompactSpace M]
variable [PathConnectedSpace M] [RegularSpace M]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]

/-- The subtype of a subtype is (canonically) the subtype. -/
noncomputable def subtypeNestHomeomorph {α : Type*} [TopologicalSpace α] {s t : Set α} (h : t ⊆ s) :
    {x : ↥s // (x : α) ∈ t} ≃ₜ ↥t where
  toFun x := ⟨(x.1 : α), x.2⟩
  invFun y := ⟨⟨(y : α), h y.2⟩, y.2⟩
  left_inv x := rfl
  right_inv y := rfl
  continuous_toFun := Continuous.subtype_mk
    (continuous_subtype_val.comp continuous_subtype_val) _
  continuous_invFun := Continuous.subtype_mk
    (Continuous.subtype_mk continuous_subtype_val _) _

/-- **Every small metric ball around `x₀` is a disk, with its boundary.**  There is `ε₀ > 0` such
that for every radius `t ∈ (0,ε₀)` there is a homeomorphism from the standard closed unit ball onto
`{d(x₀,·) ≤ t}` whose preimage of the level set `{d(x₀,·) = t}` is the unit sphere. -/
theorem exists_homeo_closedBall_pair_of_radius
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (x₀ : M) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ t ∈ Set.Ioo (0 : ℝ) ε₀,
      ∃ e : Metric.closedBall (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) 1 ≃ₜ
          {y : M // Manifold.riemannianEDist I x₀ y ≤ ENNReal.ofReal t},
        e ⁻¹' {y : {y : M // Manifold.riemannianEDist I x₀ y ≤ ENNReal.ofReal t} |
            Manifold.riemannianEDist I x₀ (y : M) = ENNReal.ofReal t}
          = Metric.sphere (0 : Metric.closedBall (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) 1) 1 := by
  haveI hcb : IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x) :=
    Submission.EDist.isContinuousRiemannianBundle_infty (I := I)
  obtain ⟨εG, hεG, eG, heG⟩ :=
    Submission.GSDisk.exists_pos_homeo_closedBall (cov := cov) hmet htor x₀
  obtain ⟨ρ, hρ, hρdist⟩ :=
    Submission.GlobalExp.exists_pos_riemannianEDist_GExp_eq (cov := cov) hmet htor x₀
  refine ⟨min εG ρ, lt_min hεG hρ, ?_⟩
  intro t ht
  have hεpos : 0 < t := ht.1
  have hεεG : t < εG := lt_of_lt_of_le ht.2 (min_le_left εG ρ)
  have hερ : t < ρ := lt_of_lt_of_le ht.2 (min_le_right εG ρ)
  have hdist : ∀ u : TangentSpace I x₀, ‖u‖ ≤ t →
      Manifold.riemannianEDist I x₀ (GExp (cov := cov) hmet x₀ u) = ENNReal.ofReal ‖u‖ := by
    intro u hu
    have hlt : ‖u‖ < ρ := lt_of_le_of_lt hu hερ
    have h := hρdist u hlt
    rw [Submission.GSDisk.chartGram_self_fibre, Real.sqrt_sq (norm_nonneg u)] at h
    exact h
  have hinj : ∀ u v : TangentSpace I x₀, ‖u‖ ≤ εG → ‖v‖ ≤ εG →
      GExp (cov := cov) hmet x₀ u = GExp (cov := cov) hmet x₀ v → u = v := by
    intro u v hu hv huv
    have h1 : eG ⟨u, by simpa only [Metric.mem_closedBall, dist_zero_right] using hu⟩
        = eG ⟨v, by simpa only [Metric.mem_closedBall, dist_zero_right] using hv⟩ := by
      apply Subtype.ext
      rw [heG, heG, huv]
    exact Subtype.ext_iff.mp (eG.injective h1)
  have hiff : ∀ u : Metric.closedBall (0 : TangentSpace I x₀) εG,
      (u : TangentSpace I x₀) ∈ Metric.closedBall (0 : TangentSpace I x₀) t ↔
        (eG u : M) ∈ {y : M | Manifold.riemannianEDist I x₀ y ≤ ENNReal.ofReal t} := by
    intro u
    have huG : ‖(u : TangentSpace I x₀)‖ ≤ εG := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using u.2
    rw [Metric.mem_closedBall, dist_zero_right, Set.mem_ofPred_eq]
    constructor
    · intro hu
      rw [heG u, hdist _ hu]
      exact ENNReal.ofReal_le_ofReal hu
    · intro hy
      obtain ⟨v, hvG, hvd⟩ :=
        Submission.HopfRinow.exists_geodesic_riemannianEDist_eq (cov := cov) hmet htor x₀ (eG u : M)
      have hdy : Manifold.riemannianEDist I x₀ (eG u : M) ≤ ENNReal.ofReal t := hy
      have hvel : ‖v‖ ≤ t := by
        rw [hvd] at hdy
        exact (ENNReal.ofReal_le_ofReal_iff hεpos.le).mp hdy
      have hvu : v = (u : TangentSpace I x₀) := by
        refine hinj v (u : TangentSpace I x₀) (le_trans hvel hεεG.le) huG ?_
        rw [hvG, heG u]
      rw [← hvu]
      exact hvel
  haveI : FiniteDimensional ℝ (TangentSpace I x₀) := ‹FiniteDimensional ℝ E›
  let nestD := subtypeNestHomeomorph (s := Metric.closedBall (0 : TangentSpace I x₀) εG)
    (t := Metric.closedBall (0 : TangentSpace I x₀) t) (fun a ha => le_trans ha hεεG.le)
  let nestC := subtypeNestHomeomorph
    (s := {y : M | Manifold.riemannianEDist I x₀ y ≤ ENNReal.ofReal εG})
    (t := {y : M | Manifold.riemannianEDist I x₀ y ≤ ENNReal.ofReal t})
    (fun a ha => le_trans ha (ENNReal.ofReal_le_ofReal hεεG.le))
  let e1 : Metric.closedBall (0 : TangentSpace I x₀) t ≃ₜ
      {y : M // Manifold.riemannianEDist I x₀ y ≤ ENNReal.ofReal t} :=
    nestD.symm.trans ((eG.subtype (p := fun u : Metric.closedBall (0 : TangentSpace I x₀) εG =>
          (u : TangentSpace I x₀) ∈ Metric.closedBall (0 : TangentSpace I x₀) t)
        (q := fun y : {y : M // Manifold.riemannianEDist I x₀ y ≤ ENNReal.ofReal εG} =>
          (y : M) ∈ {z : M | Manifold.riemannianEDist I x₀ z ≤ ENNReal.ofReal t}) hiff).trans nestC)
  obtain ⟨eM, heM⟩ := Commons.Topology.Metric.closedBall_homeo_euclidean_pair
    (V := TangentSpace I x₀) (n := Module.finrank ℝ E) rfl hεpos
  refine ⟨eM.symm.trans e1, ?_⟩
  ext v
  have hv3 : (v ∈ Metric.sphere (0 : Metric.closedBall
        (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) 1) 1) ↔
      ‖(v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))‖ = 1 := by
    rw [Metric.mem_sphere, Subtype.dist_eq, dist_eq_norm]
    simp
  rw [Set.mem_preimage, Set.mem_ofPred_eq, hv3]
  have hmem : ‖((eM.symm v : Metric.closedBall (0 : TangentSpace I x₀) t) :
      TangentSpace I x₀)‖ ≤ t := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using (eM.symm v).2
  have hv2 : ‖((eM.symm v : Metric.closedBall (0 : TangentSpace I x₀) t) :
      TangentSpace I x₀)‖ = t ↔ ‖(v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))‖ = 1 := by
    have h := heM (eM.symm v)
    rwa [Homeomorph.apply_symm_apply] at h
  have hval : ((eM.symm.trans e1) v : M)
      = GExp (cov := cov) hmet x₀ ((eM.symm v : Metric.closedBall (0 : TangentSpace I x₀) t) :
          TangentSpace I x₀) := by
    show (eG ⟨(eM.symm v : TangentSpace I x₀),
      show (eM.symm v : TangentSpace I x₀) ∈ Metric.closedBall (0 : TangentSpace I x₀) εG from
        le_trans (by simpa only [Metric.mem_closedBall, dist_zero_right] using (eM.symm v).2)
          hεεG.le⟩ : M) = _
    rw [heG]
  rw [hval, hdist _ hmem, ENNReal.ofReal_eq_ofReal_iff (norm_nonneg _) hεpos.le]
  exact hv2

/-- The identity homeomorphism between two subtypes cut out by equivalent predicates. -/
noncomputable def homeoSubtypeOfIff {α : Type*} [TopologicalSpace α] {s t : Set α}
    (h : ∀ a, a ∈ s ↔ a ∈ t) : ↥s ≃ₜ ↥t where
  toFun a := ⟨a.1, (h a).mp a.2⟩
  invFun a := ⟨a.1, (h a).mpr a.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := Continuous.subtype_mk continuous_subtype_val _
  continuous_invFun := Continuous.subtype_mk continuous_subtype_val _

/-- **Every small metric ball around `x₀` is a disk, with its boundary** (`toReal` form).  There is
`ε₀ > 0` such that for every radius `t ∈ (0,ε₀)` there is a homeomorphism from the standard closed
unit ball onto `{d(x₀,·).toReal ≤ t}` whose preimage of the level set `{d(x₀,·).toReal = t}` is the
unit sphere. -/
theorem exists_homeo_closedBall_pair_of_radius_toReal
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (x₀ : M) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ t ∈ Set.Ioo (0 : ℝ) ε₀,
      ∃ e : Metric.closedBall (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) 1 ≃ₜ
          {y : M // (Manifold.riemannianEDist I x₀ y).toReal ≤ t},
        e ⁻¹' {y : {y : M // (Manifold.riemannianEDist I x₀ y).toReal ≤ t} |
            (Manifold.riemannianEDist I x₀ (y : M)).toReal = t}
          = Metric.sphere (0 : Metric.closedBall
            (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) 1) 1 := by
  obtain ⟨ε₀, hε₀, h⟩ := exists_homeo_closedBall_pair_of_radius (cov := cov) hmet htor x₀
  refine ⟨ε₀, hε₀, fun t ht => ?_⟩
  obtain ⟨e, he⟩ := h t ht
  have hfin : ∀ y : M, Manifold.riemannianEDist I x₀ y ≠ ⊤ := fun y =>
    (Submission.HopfRinow.riemannianEDist_lt_top (I := I) (cov := cov) hmet htor x₀ y).ne
  have hiff : ∀ y : M, Manifold.riemannianEDist I x₀ y ≤ ENNReal.ofReal t ↔
      (Manifold.riemannianEDist I x₀ y).toReal ≤ t := fun y =>
    ENNReal.le_ofReal_iff_toReal_le (a := Manifold.riemannianEDist I x₀ y) (hfin y) ht.1.le
  have hsetp : ∀ z : {y : M // Manifold.riemannianEDist I x₀ y ≤ ENNReal.ofReal t},
      ((homeoSubtypeOfIff hiff) z) ∈ {y : {y : M //
          (Manifold.riemannianEDist I x₀ y).toReal ≤ t} |
          (Manifold.riemannianEDist I x₀ (y : M)).toReal = t}
        ↔ z ∈ {y : {y : M // Manifold.riemannianEDist I x₀ y ≤ ENNReal.ofReal t} |
          Manifold.riemannianEDist I x₀ (y : M) = ENNReal.ofReal t} := by
    intro z
    constructor
    · intro hz
      change Manifold.riemannianEDist I x₀ (z : M) = ENNReal.ofReal t
      have hz' : (Manifold.riemannianEDist I x₀ (z : M)).toReal = t := hz
      rw [← ENNReal.ofReal_toReal (hfin (z : M)), hz']
    · intro hz
      change (Manifold.riemannianEDist I x₀ (z : M)).toReal = t
      have hz' : Manifold.riemannianEDist I x₀ (z : M) = ENNReal.ofReal t := hz
      rw [hz', ENNReal.toReal_ofReal ht.1.le]
  refine ⟨e.trans (homeoSubtypeOfIff hiff), ?_⟩
  ext v
  have h1 : (e.trans (homeoSubtypeOfIff hiff)) v = (homeoSubtypeOfIff hiff) (e v) := rfl
  rw [Set.mem_preimage]
  exact (hsetp (e v)).trans (Set.ext_iff.mp he v)

end

end Submission.GSHalfDisk
