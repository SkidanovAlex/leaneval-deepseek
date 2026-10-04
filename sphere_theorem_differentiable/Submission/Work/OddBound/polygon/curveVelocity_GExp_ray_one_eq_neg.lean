import Mathlib
import Submission.Work.OddBound.LiftKit
import Submission.Work.OddBound.polygon.minimiser_unique_of_mem_segmentDomain

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.OddBound.polygon

open scoped ContDiff Manifold Topology
open Bundle

/-- **The reverse of the minimising geodesic from `p` to `q` is the ray of `U`.**  If `U` lies in the
tangential segment domain at `q` (so the ray of `U` is strictly minimising at `‖U‖`, hence the
minimising vector from `q` to `p` is unique), and `GExp p w = q` with `‖w‖ = ‖U‖`, then the velocity
at time `1` of the ray of `U` at `q` is `-w`: the ray of `U` arrives at `p` with velocity `-w`.

Suggested route.  Write `σ s = GExp p (s • w)` (so `σ 0 = p`, `σ 1 = q`) and `σ̃ s = σ (1 - s)`, a
geodesic on an interval containing `[0,2]` (`Submission.HopfRinow2.isGeodesicAt_comp_affine` with
`a = -1`, `b = 1`, plus `Submission.ConjEnergy.contMDiff_GExp_smul`; note `w ≠ 0` as
`‖w‖ = ‖U‖ > 0`, and `Submission.LensLoop.norm_curveVelocity_GExp_smul_ne` gives non-vanishing of
the speeds).  Then

* `Submission.GExpRayIdent.eqOn_Icc_GExp_of_isGeodesicAt` applied to `σ̃` with `V = σ̃'(0)` gives
  `GExp q (σ̃'(0)) = σ̃ 1 = p`; also `‖σ̃'(0)‖ = ‖w‖ = ‖U‖`
  (`Submission.Length.curveVelocity_comp_mul_add` with `c = -1`, `d = 1`, and
  `Submission.LensLoop.norm_curveVelocity_GExp_smul_ne`);
* by uniqueness of the minimising vector from `q` to `p` (the sibling result
  `minimiser_unique_of_mem_segmentDomain` of this folder, or the same argument inline via
  `Submission.SegmentDomain.cutTime_le_of_meet`) one gets `σ̃'(0) = U`;
* applying `eqOn_Icc_GExp_of_isGeodesicAt` again (now with `V = U`) shows `σ̃ = γ` on `[0,2]`, where
  `γ s = GExp q (s • U)`, hence their velocities agree at `1`
  (`Submission.GeodesicExtend.curveVelocity_congr_of_eventuallyEq`);
* finally `σ̃'(1) = -σ'(0) = -w` by `curveVelocity_comp_mul_add` together with
  `Submission.GExpVelocity.curveVelocity_GExp_smul_zero`.

Extra modules the prover will likely need: `Submission.GExpRayIdent`, `Submission.HopfRinow2`. -/
theorem curveVelocity_GExp_ray_one_eq_neg
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M] [RegularSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0)
    {q : M} {U : TangentSpace I q} (hU : U ≠ 0)
    (hseg : U ∈ Submission.SegmentDomain.segmentDomain hmet q)
    {p : M} (hUp : Submission.GlobalExp.GExp (cov := cov) hmet q U = p)
    {w : TangentSpace I p} (hw : Submission.GlobalExp.GExp (cov := cov) hmet p w = q)
    (hwn : ‖w‖ = ‖U‖) :
    Submission.Geodesic.curveVelocity (I := I)
      (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (s • U)) 1 = -w := by
  classical
  have hUpos : 0 < ‖U‖ := norm_pos_iff.mpr hU
  -- `w ≠ 0`
  have hwne : w ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hwn
    exact hUpos.ne' hwn.symm
  -- ## the ray `σ` of `w` at `p` (`σ 0 = p`, `σ 1 = q`)
  set σ : ℝ → M := fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (s • w) with hσdef
  have hσsm : ContMDiff 𝓘(ℝ) I ∞ σ :=
    Submission.ConjEnergy.contMDiff_GExp_smul (cov := cov) hmet p hwne
  have hσgeo : ∀ t : ℝ, Submission.Geodesic.IsGeodesicAt cov σ t := fun t =>
    Submission.GExpRayZero.isGeodesicAt_GExp_smul_all (cov := cov) hmet p hwne t
  have hσ0 : Submission.Geodesic.curveVelocity (I := I) σ 0 = w :=
    Submission.GExpVelocity.curveVelocity_GExp_smul_zero (cov := cov) hmet p hwne
  have hσnorm : ∀ u : ℝ, u ≠ 0 → ‖Submission.Geodesic.curveVelocity (I := I) σ u‖ = ‖w‖ :=
    fun u hu => Submission.LensLoop.norm_curveVelocity_GExp_smul_ne (cov := cov) hmet p hwne hu
  -- ## the reversed ray `τ = σ (1 - ·)`
  set τ : ℝ → M := fun s : ℝ => σ ((-1 : ℝ) * s + 1) with hτdef
  have hτsm : ContMDiff 𝓘(ℝ) I ∞ τ :=
    hσsm.comp ((contMDiff_const.mul contMDiff_id).add contMDiff_const)
  have hτgeo : ∀ r ∈ Set.Ioo (-1 : ℝ) 3, Submission.Geodesic.IsGeodesicAt cov τ r := by
    intro r hr
    have hr' : (-1 : ℝ) * r + 1 ∈ Set.Ioo (-3 : ℝ) 3 :=
      Set.mem_Ioo.mpr ⟨by linarith [hr.2], by linarith [hr.1]⟩
    exact Submission.HopfRinow.isGeodesicAt_comp_affine (cov := cov) (σ := σ)
      (c := -3) (d := 3) (a := -1) (b := 1) (by norm_num)
      hσsm.contMDiffOn (fun y _ => hσgeo y) hr'
  have hτvel : ∀ r : ℝ, Submission.Geodesic.curveVelocity (I := I) τ r
      = (-1 : ℝ) • Submission.Geodesic.curveVelocity (I := I) σ ((-1 : ℝ) * r + 1) := by
    intro r
    exact Submission.Length.curveVelocity_comp_mul_add (I := I) (γ := σ) (c := -1) (d := 1)
      (t := r) ((hσsm ((-1 : ℝ) * r + 1)).mdifferentiableAt (by simp))
  have hτnorm : ∀ r : ℝ, r ≠ 1 → ‖Submission.Geodesic.curveVelocity (I := I) τ r‖ = ‖w‖ := by
    intro r hr
    have h1 : (-1 : ℝ) * r + 1 ≠ 0 := by
      intro h
      exact hr (by linarith)
    rw [hτvel r, norm_smul, hσnorm ((-1 : ℝ) * r + 1) h1]
    simp
  have hτne : ∀ r : ℝ, Submission.Geodesic.curveVelocity (I := I) τ r ≠ 0 := by
    intro r
    by_cases hr : r = 1
    · subst hr
      rw [hτvel 1, show (-1 : ℝ) * 1 + 1 = 0 by norm_num, hσ0]
      intro hz
      rcases (smul_eq_zero.mp hz) with h | h
      · exact absurd h (by norm_num)
      · exact hwne h
    · intro hz
      have h := hτnorm r hr
      rw [hz, norm_zero] at h
      exact (norm_pos_iff.mpr hwne).ne' h.symm
  have hτ0 : τ 0 = q := by
    change Submission.GlobalExp.GExp (cov := cov) hmet p (((-1 : ℝ) * 0 + 1) • w) = q
    rw [show (-1 : ℝ) * 0 + 1 = 1 by norm_num, one_smul]
    exact hw
  have hτ1 : τ 1 = p := by
    change Submission.GlobalExp.GExp (cov := cov) hmet p (((-1 : ℝ) * 1 + 1) • w) = p
    rw [show (-1 : ℝ) * 1 + 1 = 0 by norm_num, zero_smul]
    exact Submission.GlobalExp.GExp_zero (cov := cov) hmet p
  -- ## the (unique) minimising vector of the reversed ray
  set V : TangentSpace I q :=
    Submission.LensLoop.tantransport hτ0 (Submission.Geodesic.curveVelocity (I := I) τ 0) with hVdef
  have hVnormw : ‖V‖ = ‖w‖ := by
    rw [hVdef, Submission.LensLoop.norm_tantransport hτ0]
    exact hτnorm 0 (by norm_num)
  have hVne : V ≠ 0 := by
    intro h0
    have h := hVnormw
    rw [h0, norm_zero] at h
    exact (norm_pos_iff.mpr hwne).ne' h.symm
  -- the reversed ray is the `GExp`-ray of `V` on `[0,2]`
  have hray : ∀ t ∈ Set.Icc (0 : ℝ) 2,
      τ t = Submission.GlobalExp.GExp (cov := cov) hmet q (t • V) :=
    Submission.GExpRayIdent.eqOn_Icc_GExp_of_isGeodesicAt (cov := cov) hmet
      (p := q) (V := V) hVne (a := -1) (b := 3) (T := 2)
      (by norm_num) (by norm_num) (by norm_num)
      (γ := τ) hτsm.contMDiffOn (fun t ht => hτgeo t ht) (fun t _ => hτne t) hτ0
      (Submission.LensLoop.tantransport_eq hτ0
        (Submission.Geodesic.curveVelocity (I := I) τ 0)).symm
  -- so `V` is a minimising vector from `q` to `p` of length `‖U‖`, hence `V = U`
  have hVp : Submission.GlobalExp.GExp (cov := cov) hmet q V = p := by
    have h := hray 1 (by norm_num)
    rw [hτ1, one_smul] at h
    exact h.symm
  have hVnorm : ‖V‖ = ‖U‖ := by
    rw [hVnormw]
    exact hwn
  have hVU : V = U :=
    minimiser_unique_of_mem_segmentDomain (cov := cov) hmet htor hU hseg hUp hVp hVnorm
  -- hence `τ` agrees with the ray of `U` on `[0,2]`
  have hEqOn : Set.EqOn τ
      (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (s • U)) (Set.Icc (0 : ℝ) 2) := by
    intro t ht
    rw [hray t ht, hVU]
  have hev : τ =ᶠ[𝓝 (1 : ℝ)]
      (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (s • U)) :=
    Filter.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds (show (1 : ℝ) ∈ Set.Ioo (0 : ℝ) 2 by norm_num))
      (fun t ht => hEqOn (Set.mem_Icc.mpr ⟨le_of_lt ht.1, le_of_lt ht.2⟩))
  have hvelEq : Submission.Geodesic.curveVelocity (I := I) τ 1
      = Submission.Geodesic.curveVelocity (I := I)
        (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (s • U)) 1 :=
    Submission.GeodesicExtend.curveVelocity_congr_of_eventuallyEq (I := I) hev
  -- and the velocity of `τ` at `1` is `-w`
  have hτvel1 : Submission.Geodesic.curveVelocity (I := I) τ 1 = -w := by
    have h := hτvel 1
    rw [show (-1 : ℝ) * 1 + 1 = 0 by norm_num] at h
    rw [hσ0] at h
    rw [h]
    exact neg_one_smul ℝ w
  rw [← hvelEq, hτvel1]

end Work.OddBound.polygon
