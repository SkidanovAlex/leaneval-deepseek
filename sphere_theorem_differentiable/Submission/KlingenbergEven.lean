import Submission.XuTrap
import Submission.RayConj
import Submission.ConjEnergy
import Submission.HopfRinow2
import Submission.GExpRayZero
import Submission.InjSup
import Submission.GExpRayIdent
import Submission.LensLoop
import Submission.RayChart
import Submission.GlobalExp

set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.GlobalExp
open Submission.InjRadius

/-!
# The even-dimensional Klingenberg estimate (Klingenberg 1959)

See `Submission/Roadmap.lean` §127 for the full plan and the literature reference (Wang's USTC
lecture notes, *The Sphere Theorem*, §1).

The classical proof of Klingenberg's estimate in **even** dimensions avoids the free-loop-space
minimax entirely: at the closest cut point two minimal geodesics arrive with opposite velocities,
they glue to a *smooth closed geodesic* (Synge's setting), Synge gives a periodic parallel normal
field whose second variation is negative, so nearby closed curves are shorter, and **compactness**
(a limiting argument on the minimising geodesics from the farthest point of the shortened curves)
produces a *third* minimal geodesic — contradicting the "exactly two" structure at the closest cut
point.

This module builds the pieces in order.  The first one is the "flushness + smoothness ⟹ periodicity"
step: if the `GExp`-ray of a unit vector returns to the base point at time `2m` **with the same
velocity**, then it is periodic of period `2m`.
-/

namespace Submission.KlingenbergEven

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

variable [I.Boundaryless] [Nontrivial E] [CompactSpace M]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable {K : ℝ}
variable [ContMDiffCovariantDerivative cov ∞]

/-- **Periodicity of a returning ray with matching velocity.**  Let `ξ` be a unit tangent vector at
`p` whose `GExp`-ray returns to `p` at time `2m ≠ 0` **with the same velocity** as at time `0`.
Then the ray is periodic of period `2m`:

`∀ u : ℝ, GExp p ((u + 2m) • ξ) = GExp p (u • ξ)`.

Proof: both `u ↦ GExp p (u • ξ)` and `u ↦ GExp p ((u + 2m) • ξ)` are `C^∞` geodesics (the second is
the first composed with the translation `u ↦ u + 2m`), they have the same position and the same
(unit) velocity at `0`, hence they agree by uniqueness of geodesics. -/
theorem ray_periodic_of_return_and_velocity (hmet : IsMetricCompatible cov)
    {p : M} {m : ℝ} {ξ : TangentSpace I p} (hξ : ‖ξ‖ = 1)
    (hret : GExp (cov := cov) hmet p ((2 * m) • ξ) = p)
    (hvel : curveVelocity (I := I) (fun t : ℝ => GExp (cov := cov) hmet p (t • ξ)) (2 * m)
      = curveVelocity (I := I) (fun t : ℝ => GExp (cov := cov) hmet p (t • ξ)) 0) :
    ∀ u : ℝ, GExp (cov := cov) hmet p ((u + 2 * m) • ξ)
      = GExp (cov := cov) hmet p (u • ξ) := by
  have hξne : ξ ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hξ
    norm_num at hξ
  set β : ℝ → M := fun t : ℝ => GExp (cov := cov) hmet p (t • ξ) with hβ
  have hβsm : ContMDiff 𝓘(ℝ) I ∞ β := by
    rw [hβ]
    exact Submission.ConjEnergy.contMDiff_GExp_smul (cov := cov) hmet p hξne
  have hβgeo : ∀ t : ℝ, IsGeodesicAt cov β t := by
    intro t
    rw [hβ]
    exact Submission.GExpRayZero.isGeodesicAt_GExp_smul_all (cov := cov) hmet p hξne t
  have hβne : ∀ t : ℝ, curveVelocity (I := I) β t ≠ 0 := by
    intro t
    rw [hβ]
    exact Submission.RayChart.curveVelocity_GExp_ne_zero (cov := cov) hmet p hξne t
  have hβvel0 : curveVelocity (I := I) β 0 = ξ := by
    rw [hβ]
    exact Submission.GExpVelocity.curveVelocity_GExp_smul_zero (cov := cov) hmet p hξne
  have hβvel2 : curveVelocity (I := I) β (2 * m) = ξ := by
    rw [hβ] at hvel ⊢
    rw [hvel, hβvel0]
  intro u
  set R : ℝ := |u| + 1 with hRdef
  have hRpos : 0 < R := by rw [hRdef]; positivity
  have huR : u ∈ Ioo (-R) R := by
    refine ⟨?_, ?_⟩
    · rw [hRdef]; linarith [neg_abs_le u, abs_nonneg u]
    · rw [hRdef]; linarith [le_abs_self u]
  -- the shifted ray, written in the `1 * s + 2 * m` shape so that the chain rules apply verbatim
  have hFsm : ContMDiffOn 𝓘(ℝ) I ∞ (fun s : ℝ => β (1 * s + 2 * m)) (Ioo (-R) R) :=
    (hβsm.contMDiffOn : ContMDiffOn 𝓘(ℝ) I ∞ β Set.univ).comp
      (((contMDiff_const (I := 𝓘(ℝ)).mul contMDiff_id).add contMDiff_const).contMDiffOn)
      (fun s _ => Set.mem_univ (1 * s + 2 * m))
  have hFgeo : ∀ s ∈ Ioo (-R) R, IsGeodesicAt cov (fun s : ℝ => β (1 * s + 2 * m)) s := by
    intro s hs
    have h := Submission.HopfRinow.isGeodesicAt_comp_affine (cov := cov) (σ := β)
      (a := 1) (b := 2 * m) (c := s + 2 * m - 1) (d := s + 2 * m + 1) one_ne_zero
      (hβsm.contMDiffOn.mono (Set.subset_univ _)) (fun y _ => hβgeo y) (r := s)
      ⟨by linarith, by linarith⟩
    simpa using h
  have hFvel := fun s : ℝ => Submission.Length.curveVelocity_comp_mul_add (I := I) (γ := β)
    (c := 1) (d := 2 * m) (t := s)
    ((hβsm.contMDiffAt).mdifferentiableAt (by simp))
  have hFne : ∀ s ∈ Ioo (-R) R, curveVelocity (I := I) (fun s : ℝ => β (1 * s + 2 * m)) s ≠ 0 := by
    intro s hs h0
    have hv := hFvel s
    rw [h0, one_smul] at hv
    exact hβne (1 * s + 2 * m) hv.symm
  have hEqOn := eqOn_Ioo_of_isGeodesicAt_of_eq (cov := cov) (a := -R) (b := R)
    hFsm (hβsm.contMDiffOn.mono (Set.subset_univ _)) hFgeo (fun y _ => hβgeo y) hFne
    (fun y _ => hβne y) (show (0 : ℝ) ∈ Ioo (-R) R from ⟨by linarith, by linarith⟩)
    (by
      show β (1 * 0 + 2 * m) = β 0
      rw [one_mul, zero_add, hβ]
      simp only []
      rw [hret, zero_smul, GExp_zero])
    (by
      show curveVelocity (I := I) (fun s : ℝ => β (1 * s + 2 * m)) 0
        = curveVelocity (I := I) β 0
      rw [hFvel 0, one_smul, one_mul, zero_add, hβvel2, hβvel0])
  have hfin := hEqOn huR
  simpa only [hβ, one_mul] using hfin


/-! ## Velocity comparisons: a geodesic on `ℝ` is the `GExp`-ray of its initial data

`GExp_neg_velocity_of_ray` identifies the *reversed* ray with the original ray only on `[0,m]`, i.e.
only one-sidedly at the endpoint `m`, so the velocity at `m` cannot be read off from that
identification by `Filter.EventuallyEq`-congruence.  The tool used instead is **geodesic
uniqueness**: two geodesics on `ℝ` with the same position and velocity at `0` agree on any bounded
interval containing `0` in its interior (`GlobalExp.eqOn_Ioo_of_isGeodesicAt_of_eq`), applied to an
interval chosen around the point where the velocity is wanted. -/

/-- **A geodesic on `ℝ` is the `GExp`-ray of its initial data.** -/
theorem eq_GExp_of_isGeodesicAt (hmet : IsMetricCompatible cov)
    {q : M} {V : TangentSpace I q} (hV : V ≠ 0)
    {σ : ℝ → M} (hσsm : ContMDiff 𝓘(ℝ) I ∞ σ)
    (hσgeo : ∀ t : ℝ, IsGeodesicAt cov σ t) (hσne : ∀ t : ℝ, curveVelocity (I := I) σ t ≠ 0)
    (hσ0 : σ 0 = q) (hσv : curveVelocity (I := I) σ 0 = V) :
    ∀ t : ℝ, σ t = GExp (cov := cov) hmet q (t • V) := by
  intro t
  have hGsm : ContMDiff 𝓘(ℝ) I ∞ (fun s : ℝ => GExp (cov := cov) hmet q (s • V)) :=
    Submission.ConjEnergy.contMDiff_GExp_smul (cov := cov) hmet q hV
  have hGgeo : ∀ s : ℝ, IsGeodesicAt cov (fun s : ℝ => GExp (cov := cov) hmet q (s • V)) s :=
    fun s => Submission.GExpRayZero.isGeodesicAt_GExp_smul_all (cov := cov) hmet q hV s
  have hGne : ∀ s : ℝ, curveVelocity (I := I) (fun s : ℝ => GExp (cov := cov) hmet q (s • V)) s
      ≠ 0 :=
    fun s => Submission.RayChart.curveVelocity_GExp_ne_zero (cov := cov) hmet q hV s
  have ha : min t 0 - 1 < 0 := by have h : min t 0 ≤ 0 := min_le_right _ _; linarith
  have hb : 0 < max t 0 + 1 := by have h : (0:ℝ) ≤ max t 0 := le_max_right _ _; linarith
  have ht : t ∈ Ioo (min t 0 - 1) (max t 0 + 1) := by
    refine ⟨?_, ?_⟩
    · have h : min t 0 ≤ t := min_le_left _ _; linarith
    · have h : t ≤ max t 0 := le_max_left _ _; linarith
  have h := eqOn_Ioo_of_isGeodesicAt_of_eq (cov := cov) (a := min t 0 - 1) (b := max t 0 + 1)
    hσsm.contMDiffOn hGsm.contMDiffOn (fun y _ => hσgeo y) (fun y _ => hGgeo y)
    (fun y _ => hσne y) (fun y _ => hGne y) ⟨ha, hb⟩
    (by rw [hσ0, zero_smul]; exact (GExp_zero (cov := cov) hmet q).symm)
    (by rw [hσv]; exact (Submission.GExpVelocity.curveVelocity_GExp_smul_zero
      (cov := cov) hmet q hV).symm)
  exact h ht

/-- **Velocity form.**  Under the hypotheses of `eq_GExp_of_isGeodesicAt`, the velocity of `σ` at any
time is the velocity of the corresponding `GExp`-ray. -/
theorem curveVelocity_eq_GExp_of_isGeodesicAt (hmet : IsMetricCompatible cov)
    {q : M} {V : TangentSpace I q} (hV : V ≠ 0)
    {σ : ℝ → M} (hσsm : ContMDiff 𝓘(ℝ) I ∞ σ)
    (hσgeo : ∀ t : ℝ, IsGeodesicAt cov σ t) (hσne : ∀ t : ℝ, curveVelocity (I := I) σ t ≠ 0)
    (hσ0 : σ 0 = q) (hσv : curveVelocity (I := I) σ 0 = V) (t : ℝ) :
    curveVelocity (I := I) σ t
      = curveVelocity (I := I) (fun s : ℝ => GExp (cov := cov) hmet q (s • V)) t :=
  Submission.GeodesicExtend.curveVelocity_congr_of_eventuallyEq (I := I)
    (Filter.Eventually.of_forall
      (eq_GExp_of_isGeodesicAt (cov := cov) hmet hV hσsm hσgeo hσne hσ0 hσv))


/-! ## N2: Xu's Theorem B applied at the cut point gives `η = -ξ` -/

/-- **Two `C^∞` geodesics on `ℝ` with non-vanishing velocity and the same initial data have the same
velocity everywhere.**  (Geodesic uniqueness on an interval containing both `0` and the point of
interest in its interior.) -/
theorem curveVelocity_eq_of_isGeodesicAt_eq {σ τ : ℝ → M}
    (hσsm : ContMDiff 𝓘(ℝ) I ∞ σ) (hτsm : ContMDiff 𝓘(ℝ) I ∞ τ)
    (hσgeo : ∀ t : ℝ, IsGeodesicAt cov σ t) (hτgeo : ∀ t : ℝ, IsGeodesicAt cov τ t)
    (hσne : ∀ t : ℝ, curveVelocity (I := I) σ t ≠ 0)
    (hτne : ∀ t : ℝ, curveVelocity (I := I) τ t ≠ 0)
    (h0 : σ 0 = τ 0) (hv : curveVelocity (I := I) σ 0 = curveVelocity (I := I) τ 0) (t : ℝ) :
    curveVelocity (I := I) σ t = curveVelocity (I := I) τ t := by
  have ha : min t 0 - 1 < 0 := by have h : min t 0 ≤ 0 := min_le_right _ _; linarith
  have hb : 0 < max t 0 + 1 := by have h : (0 : ℝ) ≤ max t 0 := le_max_right _ _; linarith
  have ht : t ∈ Ioo (min t 0 - 1) (max t 0 + 1) := by
    refine ⟨?_, ?_⟩
    · have h : min t 0 ≤ t := min_le_left _ _; linarith
    · have h : t ≤ max t 0 := le_max_left _ _; linarith
  have heq : Set.EqOn σ τ (Ioo (min t 0 - 1) (max t 0 + 1)) :=
    eqOn_Ioo_of_isGeodesicAt_of_eq (cov := cov) hσsm.contMDiffOn hτsm.contMDiffOn
      (fun y _ => hσgeo y) (fun y _ => hτgeo y) (fun y _ => hσne y) (fun y _ => hτne y)
      ⟨ha, hb⟩ h0 hv
  exact Submission.GeodesicExtend.curveVelocity_congr_of_eventuallyEq (I := I)
    (Filter.eventuallyEq_iff_exists_mem.mpr ⟨_, isOpen_Ioo.mem_nhds ht, heq⟩)

/-- **The velocity of the reverse parametrisation at its endpoint.**  For a `C^∞` geodesic `β` on `ℝ`
with non-vanishing velocity, the `GExp`-ray from `β m` in the direction `-β'(m)` is the reversal
`s ↦ β (m - s)`, so its velocity at `s = m` is `-β'(0)`.

This is the conversion that turns the one-sided identification
`GeodesicLoop.GExp_neg_velocity_of_ray` (valid on `[0,m]`) into a *velocity* statement at the
endpoint `m`. -/
theorem curveVelocity_reversedRay (hmet : IsMetricCompatible cov)
    {β : ℝ → M} (hβsm : ContMDiff 𝓘(ℝ) I ∞ β) (hβgeo : ∀ t : ℝ, IsGeodesicAt cov β t)
    (hβne : ∀ t : ℝ, curveVelocity (I := I) β t ≠ 0) (m : ℝ) :
    curveVelocity (I := I) (fun s : ℝ => GExp (cov := cov) hmet (β m)
        (s • (-curveVelocity (I := I) β m))) m
      = -curveVelocity (I := I) β 0 := by
  have hwm : curveVelocity (I := I) β m ≠ 0 := hβne m
  have hneg : (-curveVelocity (I := I) β m) ≠ 0 := neg_ne_zero.mpr hwm
  have hσsm : ContMDiff 𝓘(ℝ) I ∞ (fun s : ℝ => GExp (cov := cov) hmet (β m)
      (s • (-curveVelocity (I := I) β m))) :=
    Submission.ConjEnergy.contMDiff_GExp_smul (cov := cov) hmet (β m) hneg
  have hσgeo : ∀ t : ℝ, IsGeodesicAt cov (fun s : ℝ => GExp (cov := cov) hmet (β m)
      (s • (-curveVelocity (I := I) β m))) t :=
    fun t => Submission.GExpRayZero.isGeodesicAt_GExp_smul_all (cov := cov) hmet (β m) hneg t
  have hσne : ∀ t : ℝ, curveVelocity (I := I) (fun s : ℝ => GExp (cov := cov) hmet (β m)
      (s • (-curveVelocity (I := I) β m))) t ≠ 0 :=
    fun t => Submission.RayChart.curveVelocity_GExp_ne_zero (cov := cov) hmet (β m) hneg t
  have hτsm : ContMDiff 𝓘(ℝ) I ∞ (fun s : ℝ => β ((-1) * s + m)) :=
    hβsm.comp (((contMDiff_const (I := 𝓘(ℝ)).mul contMDiff_id).add contMDiff_const))
  have hτgeo : ∀ r : ℝ, IsGeodesicAt cov (fun s : ℝ => β ((-1) * s + m)) r := by
    intro r
    have h := Submission.HopfRinow.isGeodesicAt_comp_affine (cov := cov) (σ := β) (a := -1) (b := m)
      (c := (-1) * r + m - 1) (d := (-1) * r + m + 1) (by norm_num)
      (hβsm.contMDiffOn.mono (Set.subset_univ _)) (fun y _ => hβgeo y) (r := r)
      ⟨by linarith, by linarith⟩
    simpa using h
  have hτne : ∀ r : ℝ, curveVelocity (I := I) (fun s : ℝ => β ((-1) * s + m)) r ≠ 0 := by
    intro r h0
    have hv := Submission.Length.curveVelocity_comp_mul_add (I := I) (γ := β) (c := -1) (d := m)
      (t := r) ((hβsm.contMDiffAt).mdifferentiableAt (by simp))
    rw [h0] at hv
    have h2 : curveVelocity (I := I) β ((-1) * r + m) = 0 := by
      have h1 : (-1 : ℝ) • curveVelocity (I := I) β ((-1) * r + m) = 0 := hv.symm
      exact (smul_eq_zero.mp h1).resolve_left (by norm_num)
    exact hβne _ h2
  have h0 : (fun s : ℝ => GExp (cov := cov) hmet (β m) (s • (-curveVelocity (I := I) β m))) 0
      = (fun s : ℝ => β ((-1) * s + m)) 0 := by
    show GExp (cov := cov) hmet (β m) ((0 : ℝ) • (-curveVelocity (I := I) β m))
      = β ((-1) * (0 : ℝ) + m)
    rw [zero_smul, GExp_zero, show (-1 : ℝ) * 0 + m = m from by ring]
  have hv : curveVelocity (I := I) (fun s : ℝ => GExp (cov := cov) hmet (β m)
        (s • (-curveVelocity (I := I) β m))) 0
      = curveVelocity (I := I) (fun s : ℝ => β ((-1) * s + m)) 0 := by
    rw [Submission.GExpVelocity.curveVelocity_GExp_smul_zero (cov := cov) hmet (β m) hneg,
      Submission.Length.curveVelocity_comp_mul_add (I := I) (γ := β) (c := -1) (d := m) (t := 0)
        ((hβsm.contMDiffAt).mdifferentiableAt (by simp)),
      show (-1 : ℝ) * 0 + m = m from by ring, neg_one_smul]
  have hfin := curveVelocity_eq_of_isGeodesicAt_eq (cov := cov) hσsm hτsm hσgeo hτgeo hσne hτne
    h0 hv m
  rw [hfin, Submission.Length.curveVelocity_comp_mul_add (I := I) (γ := β) (c := -1) (d := m)
    (t := m) ((hβsm.contMDiffAt).mdifferentiableAt (by simp)),
    show (-1 : ℝ) * m + m = 0 from by ring, neg_one_smul]

/-- **N2 — Xu's Theorem B at the cut point.**  In the configuration of the closest cut point
(`m` the maximal injectivity radius at `p`, `InjAllAtLeast hmet m`, `m < π/√K`, two distinct unit
directions `ξ ≠ η` at `p` whose minimising rays meet at the same point `q`), if moreover `InjAtLeast
hmet p m` and the *reversed* pair at `q` is a legitimate pair for Xu's theorem, then the two
directions are **antipodal**:

`η = -ξ`.

*How it is proved.*  Xu at `p` gives `w₁ = -w₂` for the velocities of the two rays at `q`; therefore
the two *unit* directions at `q` given by `-w₁` and `w₁` are antipodal (hence distinct), and the two
minimising rays of length `m` from `q` both end at `p`.  Xu at `q` then compares the velocities of
those two rays at `p`: the ray of `-w₁` is the reversal of the `ξ`-ray (`curveVelocity_reversedRay`),
with velocity `-ξ` at `p`, and the ray of `w₁` is the reversal of the `η`-ray, with velocity `-η`.
Xu's conclusion `-ξ = -(-η)` is exactly `η = -ξ`. -/
theorem eq_neg_of_xuCornerExcluded_at_target (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    (hK : Submission.RauchK.CurvLe cov K) (hKpos : 0 < K) [PathConnectedSpace M] [RegularSpace M]
    {p : M} {m : ℝ} (hm : 0 < m) (hmπ : m < Real.pi / Real.sqrt K)
    (hinjp : InjAtLeast hmet p m) (hmaxp : ∀ r : ℝ, m < r → ¬ InjAtLeast hmet p r)
    (hinjall : InjAllAtLeast hmet m)
    {ξ η : TangentSpace I p} (hξ : ‖ξ‖ = 1) (hη : ‖η‖ = 1) (hξη : ξ ≠ η)
    (hmeet : GExp (cov := cov) hmet p (m • ξ) = GExp (cov := cov) hmet p (m • η))
    (hminξ : Manifold.riemannianEDist I p (GExp (cov := cov) hmet p (m • ξ)) = ENNReal.ofReal m)
    (hminη : Manifold.riemannianEDist I p (GExp (cov := cov) hmet p (m • η)) = ENNReal.ofReal m) :
    η = -ξ := by
  have hξne : ξ ≠ 0 := by intro h0; rw [h0, norm_zero] at hξ; norm_num at hξ
  have hηne : η ≠ 0 := by intro h0; rw [h0, norm_zero] at hη; norm_num at hη
  have hnc : ¬ ConjRadius.IsConjugateTime cov (fun t : ℝ => GExp (cov := cov) hmet p (t • ξ)) m :=
    Submission.ConjCut.not_isConjugateTime_of_lt_pi_div_sqrt (cov := cov) hmet htor hK hKpos hmπ
  have hA : curveVelocity (I := I) (fun t : ℝ => GExp (cov := cov) hmet p (t • ξ)) m
      = -curveVelocity (I := I) (fun t : ℝ => GExp (cov := cov) hmet p (t • η)) m :=
    Submission.XuTrap.xuCornerExcluded (cov := cov) hmet htor p hm hinjp hmaxp ξ η hξ hη hξη
      hminξ hminη hmeet hnc
  -- the two directions at the meeting point `q`, and their basic properties
  obtain ⟨w, hwdef⟩ : ∃ w : TangentSpace I (GExp (cov := cov) hmet p (m • ξ)),
      w = curveVelocity (I := I) (fun t : ℝ => GExp (cov := cov) hmet p (t • ξ)) m :=
    ⟨_, rfl⟩
  have hwne : w ≠ 0 := by
    rw [hwdef]
    exact Submission.RayChart.curveVelocity_GExp_ne_zero (cov := cov) hmet p hξne m
  have hwnorm : ‖w‖ = 1 := by
    rw [hwdef, ← Submission.GeodesicSpeed.curveSpeed_eq_norm,
      Submission.BrokenLength.curveSpeed_GExp_ray (cov := cov) hmet p hξne m, hξ]
  have hA' : w = -curveVelocity (I := I) (fun t : ℝ => GExp (cov := cov) hmet p (t • η)) m := by
    rw [hwdef]; exact hA
  have hw_norm_neg : ‖m • (-w)‖ = m := by
    rw [norm_smul, norm_neg, hwnorm, mul_one, Real.norm_eq_abs, abs_of_pos hm]
  have hw_norm : ‖m • w‖ = m := by
    rw [norm_smul, hwnorm, mul_one, Real.norm_eq_abs, abs_of_pos hm]
  -- the two reversed rays both end at `p`
  have hrevξ : GExp (cov := cov) hmet (GExp (cov := cov) hmet p (m • ξ)) (m • (-w)) = p := by
    have h := GeodesicLoop.GExp_neg_velocity_of_ray (cov := cov) hmet p (ξ := ξ) hξ hm
      (s := m) (le_of_lt hm) le_rfl
    rw [show m - m = (0 : ℝ) from by ring, zero_smul, GExp_zero] at h
    rw [hwdef]
    exact h
  have hrevη : GExp (cov := cov) hmet (GExp (cov := cov) hmet p (m • ξ)) (m • w) = p := by
    have h := GeodesicLoop.GExp_neg_velocity_of_ray (cov := cov) hmet p (ξ := η) hη hm
      (s := m) (le_of_lt hm) le_rfl
    rw [show m - m = (0 : ℝ) from by ring, zero_smul, GExp_zero] at h
    rw [hA', hmeet]
    exact h
  -- the two unit directions at `q` are distinct
  have hne2 : m • (-w) ≠ m • w := by
    intro hEq
    have h4 : m • (-w) = -(m • w) := by rw [smul_neg]
    rw [h4] at hEq
    have h5 : m • w + m • w = 0 := by
      nth_rewrite 1 [hEq.symm]
      exact neg_add_cancel (m • w)
    have h3 : m • w = 0 := by
      have h6 : (2 : ℝ) • (m • w) = 0 := by rw [two_smul]; exact h5
      exact (smul_eq_zero.mp h6).resolve_left (by norm_num)
    have h7 : w = 0 := (smul_eq_zero.mp h3).resolve_left (ne_of_gt hm)
    exact hwne h7
  -- maximality of the injectivity radius at `q`
  have hmaxq : ∀ r : ℝ, m < r → ¬ InjAtLeast hmet (GExp (cov := cov) hmet p (m • ξ)) r := by
    intro r hr hcon
    exact hne2 (hcon (m • (-w)) (m • w) (by rw [hw_norm_neg]; exact hr)
      (by rw [hw_norm]; exact hr) (by rw [hrevξ, hrevη]))
  -- Xu at `q`
  have hncq : ¬ ConjRadius.IsConjugateTime cov
      (fun t : ℝ => GExp (cov := cov) hmet (GExp (cov := cov) hmet p (m • ξ)) (t • (-w))) m :=
    Submission.ConjCut.not_isConjugateTime_of_lt_pi_div_sqrt (cov := cov) hmet htor hK hKpos hmπ
  have hminrevξ : Manifold.riemannianEDist I (GExp (cov := cov) hmet p (m • ξ))
      (GExp (cov := cov) hmet (GExp (cov := cov) hmet p (m • ξ)) (m • (-w))) = ENNReal.ofReal m := by
    rw [hrevξ, Manifold.riemannianEDist_comm, hminξ]
  have hminrevη : Manifold.riemannianEDist I (GExp (cov := cov) hmet p (m • ξ))
      (GExp (cov := cov) hmet (GExp (cov := cov) hmet p (m • ξ)) (m • w)) = ENNReal.ofReal m := by
    rw [hrevη, Manifold.riemannianEDist_comm, hminξ]
  have hxu := Submission.XuTrap.xuCornerExcluded (cov := cov) hmet htor
    (GExp (cov := cov) hmet p (m • ξ)) hm (hinjall _) hmaxq (-w) w
    (by rw [norm_neg, hwnorm]) hwnorm (by
      intro hEq
      have h5 : w + w = 0 := by
        nth_rewrite 1 [hEq.symm]
        exact neg_add_cancel w
      have h6 : (2 : ℝ) • w = 0 := by rw [two_smul]; exact h5
      exact hwne ((smul_eq_zero.mp h6).resolve_left (by norm_num)))
    hminrevξ hminrevη (by rw [hrevξ, hrevη]) hncq
  -- the two velocities at `p`
  have hL : curveVelocity (I := I)
      (fun t : ℝ => GExp (cov := cov) hmet (GExp (cov := cov) hmet p (m • ξ)) (t • (-w))) m
      = -ξ := by
    have h := curveVelocity_reversedRay (cov := cov) hmet
      (β := fun t : ℝ => GExp (cov := cov) hmet p (t • ξ))
      (Submission.ConjEnergy.contMDiff_GExp_smul (cov := cov) hmet p hξne)
      (fun t => Submission.GExpRayZero.isGeodesicAt_GExp_smul_all (cov := cov) hmet p hξne t)
      (fun t => Submission.RayChart.curveVelocity_GExp_ne_zero (cov := cov) hmet p hξne t) m
    rw [← hwdef] at h
    rw [h, Submission.GExpVelocity.curveVelocity_GExp_smul_zero (cov := cov) hmet p hξne]
  have hR : curveVelocity (I := I)
      (fun t : ℝ => GExp (cov := cov) hmet (GExp (cov := cov) hmet p (m • ξ)) (t • w)) m
      = -η := by
    have hβsm : ContMDiff 𝓘(ℝ) I ∞ (fun s : ℝ => GExp (cov := cov) hmet p (s • η)) :=
      Submission.ConjEnergy.contMDiff_GExp_smul (cov := cov) hmet p hηne
    have hβgeo : ∀ s : ℝ, IsGeodesicAt cov (fun s : ℝ => GExp (cov := cov) hmet p (s • η)) s :=
      fun s => Submission.GExpRayZero.isGeodesicAt_GExp_smul_all (cov := cov) hmet p hηne s
    have hβne : ∀ s : ℝ, curveVelocity (I := I) (fun s : ℝ => GExp (cov := cov) hmet p (s • η)) s
        ≠ 0 :=
      fun s => Submission.RayChart.curveVelocity_GExp_ne_zero (cov := cov) hmet p hηne s
    have h := curveVelocity_eq_of_isGeodesicAt_eq (cov := cov)
      (σ := fun t : ℝ => GExp (cov := cov) hmet (GExp (cov := cov) hmet p (m • ξ)) (t • w))
      (τ := fun t : ℝ => GExp (cov := cov) hmet p (((-1) * t + m) • η))
      (Submission.ConjEnergy.contMDiff_GExp_smul (cov := cov) hmet _ hwne)
      (hβsm.comp (f := fun t : ℝ => (-1) * t + m)
        ((contMDiff_const (I := 𝓘(ℝ)).mul contMDiff_id).add contMDiff_const))
      (fun t => Submission.GExpRayZero.isGeodesicAt_GExp_smul_all (cov := cov) hmet _ hwne t)
      (fun t => by
        have hh := Submission.HopfRinow.isGeodesicAt_comp_affine (cov := cov)
          (σ := fun s : ℝ => GExp (cov := cov) hmet p (s • η)) (a := -1) (b := m)
          (c := (-1) * t + m - 1) (d := (-1) * t + m + 1) (by norm_num)
          (hβsm.contMDiffOn.mono (Set.subset_univ _)) (fun y _ => hβgeo y) (r := t)
          ⟨by linarith, by linarith⟩
        simpa using hh)
      (fun t => Submission.RayChart.curveVelocity_GExp_ne_zero (cov := cov) hmet _ hwne t)
      (fun t => by
        intro h0
        have hv := Submission.Length.curveVelocity_comp_mul_add (I := I)
          (γ := fun s : ℝ => GExp (cov := cov) hmet p (s • η)) (c := -1) (d := m) (t := t)
          (hβsm.contMDiffAt.mdifferentiableAt (by simp))
        rw [h0] at hv
        have h1 : (-1 : ℝ) • curveVelocity (I := I)
            (fun s : ℝ => GExp (cov := cov) hmet p (s • η)) ((-1) * t + m) = 0 := hv.symm
        have h2 : curveVelocity (I := I) (fun s : ℝ => GExp (cov := cov) hmet p (s • η))
            ((-1) * t + m) = 0 :=
          (smul_eq_zero.mp h1).resolve_left (by norm_num)
        exact hβne _ h2)
      (by
        show GExp (cov := cov) hmet (GExp (cov := cov) hmet p (m • ξ)) ((0 : ℝ) • w)
          = GExp (cov := cov) hmet p (((-1) * (0 : ℝ) + m) • η)
        rw [zero_smul, GExp_zero, show (-1 : ℝ) * 0 + m = m from by ring]
        exact hmeet)
      (by
        rw [Submission.GExpVelocity.curveVelocity_GExp_smul_zero (cov := cov) hmet _ hwne,
          Submission.Length.curveVelocity_comp_mul_add (I := I)
            (γ := fun s : ℝ => GExp (cov := cov) hmet p (s • η)) (c := -1) (d := m) (t := 0)
            (hβsm.contMDiffAt.mdifferentiableAt (by simp)),
          show (-1 : ℝ) * 0 + m = m from by ring, neg_one_smul]
        exact hA')
      m
    rw [h, Submission.Length.curveVelocity_comp_mul_add (I := I)
      (γ := fun s : ℝ => GExp (cov := cov) hmet p (s • η)) (c := -1) (d := m) (t := m)
      (hβsm.contMDiffAt.mdifferentiableAt (by simp)),
      show (-1 : ℝ) * m + m = 0 from by ring, neg_one_smul,
      Submission.GExpVelocity.curveVelocity_GExp_smul_zero (cov := cov) hmet p hηne]
  rw [hL, hR, neg_neg] at hxu
  exact hxu.symm


/-! ## N3: the closed geodesic of length `2m` -/

/-- **The ray from `β m` in the direction `β'(m)` is `β` itself**, so its velocity at `m` is
`β'(2m)`.  (Both curves are geodesics on `ℝ` with the same position and velocity at `0`.) -/
theorem curveVelocity_ray_shift (hmet : IsMetricCompatible cov)
    {β : ℝ → M} {q : M} {m : ℝ} (hq : β m = q) (hβsm : ContMDiff 𝓘(ℝ) I ∞ β)
    (hβgeo : ∀ t : ℝ, IsGeodesicAt cov β t)
    (hβne : ∀ t : ℝ, curveVelocity (I := I) β t ≠ 0) :
    curveVelocity (I := I) (fun t : ℝ => GExp (cov := cov) hmet q
        (t • curveVelocity (I := I) β m)) m = curveVelocity (I := I) β (2 * m) := by
  have hwm : curveVelocity (I := I) β m ≠ 0 := hβne m
  have h := curveVelocity_eq_of_isGeodesicAt_eq (cov := cov)
    (σ := fun t : ℝ => GExp (cov := cov) hmet q (t • curveVelocity (I := I) β m))
    (τ := fun t : ℝ => β (1 * t + m))
    (Submission.ConjEnergy.contMDiff_GExp_smul (cov := cov) hmet q hwm)
    (hβsm.comp (f := fun t : ℝ => 1 * t + m)
      (((contMDiff_const (I := 𝓘(ℝ)).mul contMDiff_id).add contMDiff_const)))
    (fun t => Submission.GExpRayZero.isGeodesicAt_GExp_smul_all (cov := cov) hmet q hwm t)
    (fun t => by
      have hh := Submission.HopfRinow.isGeodesicAt_comp_affine (cov := cov) (σ := β) (a := 1) (b := m)
        (c := 1 * t + m - 1) (d := 1 * t + m + 1) one_ne_zero
        (hβsm.contMDiffOn.mono (Set.subset_univ _)) (fun y _ => hβgeo y) (r := t)
        ⟨by linarith, by linarith⟩
      simpa using hh)
    (fun t => Submission.RayChart.curveVelocity_GExp_ne_zero (cov := cov) hmet q hwm t)
    (fun t => by
      intro h0
      have hv := Submission.Length.curveVelocity_comp_mul_add (I := I) (γ := β) (c := 1) (d := m)
        (t := t) ((hβsm.contMDiffAt).mdifferentiableAt (by simp))
      rw [h0, one_smul] at hv
      exact hβne _ hv.symm)
    (by
      show GExp (cov := cov) hmet q ((0 : ℝ) • curveVelocity (I := I) β m) = β (1 * (0:ℝ) + m)
      rw [zero_smul, GExp_zero, one_mul, zero_add]
      exact hq.symm)
    (by
      rw [Submission.GExpVelocity.curveVelocity_GExp_smul_zero (cov := cov) hmet q hwm,
        Submission.Length.curveVelocity_comp_mul_add (I := I) (γ := β) (c := 1) (d := m) (t := 0)
          ((hβsm.contMDiffAt).mdifferentiableAt (by simp)),
        one_mul, zero_add, one_smul])
    m
  rw [h, Submission.Length.curveVelocity_comp_mul_add (I := I) (γ := β) (c := 1) (d := m) (t := m)
    ((hβsm.contMDiffAt).mdifferentiableAt (by simp))]
  rw [show (1 : ℝ) * m + m = 2 * m from by ring, one_smul]

/-- **The ray from the meeting point in the direction of the first velocity.**  If `ξ, η` are non-zero
tangent vectors at `p` with `GExp p (m•ξ) = GExp p (m•η)` and the two velocities at the meeting point
are **opposite**, then the ray from the meeting point in the direction of the *first* velocity is the
reversal of the `η`-ray, so its velocity at `m` is `-η'(0)`. -/
theorem curveVelocity_ray_meeting (hmet : IsMetricCompatible cov)
    {p : M} {m : ℝ} (hm : 0 < m)
    {ξ η : TangentSpace I p} (hξne : ξ ≠ 0) (hηne : η ≠ 0)
    (hmeet : GExp (cov := cov) hmet p (m • ξ) = GExp (cov := cov) hmet p (m • η))
    (hA : curveVelocity (I := I) (fun t : ℝ => GExp (cov := cov) hmet p (t • ξ)) m
      = -curveVelocity (I := I) (fun t : ℝ => GExp (cov := cov) hmet p (t • η)) m) :
    curveVelocity (I := I) (fun t : ℝ => GExp (cov := cov) hmet
        (GExp (cov := cov) hmet p (m • ξ)) (t • curveVelocity (I := I)
          (fun t : ℝ => GExp (cov := cov) hmet p (t • ξ)) m)) m
      = -curveVelocity (I := I) (fun t : ℝ => GExp (cov := cov) hmet p (t • η)) 0 := by
  have hwm : curveVelocity (I := I) (fun t : ℝ => GExp (cov := cov) hmet p (t • ξ)) m ≠ 0 :=
    Submission.RayChart.curveVelocity_GExp_ne_zero (cov := cov) hmet p hξne m
  have hβsm : ContMDiff 𝓘(ℝ) I ∞ (fun s : ℝ => GExp (cov := cov) hmet p (s • η)) :=
    Submission.ConjEnergy.contMDiff_GExp_smul (cov := cov) hmet p hηne
  have hβgeo : ∀ s : ℝ, IsGeodesicAt cov (fun s : ℝ => GExp (cov := cov) hmet p (s • η)) s :=
    fun s => Submission.GExpRayZero.isGeodesicAt_GExp_smul_all (cov := cov) hmet p hηne s
  have hβne : ∀ s : ℝ, curveVelocity (I := I) (fun s : ℝ => GExp (cov := cov) hmet p (s • η)) s
      ≠ 0 :=
    fun s => Submission.RayChart.curveVelocity_GExp_ne_zero (cov := cov) hmet p hηne s
  have h := curveVelocity_eq_of_isGeodesicAt_eq (cov := cov)
    (σ := fun t : ℝ => GExp (cov := cov) hmet (GExp (cov := cov) hmet p (m • ξ))
      (t • curveVelocity (I := I) (fun t : ℝ => GExp (cov := cov) hmet p (t • ξ)) m))
    (τ := fun t : ℝ => GExp (cov := cov) hmet p (((-1) * t + m) • η))
    (Submission.ConjEnergy.contMDiff_GExp_smul (cov := cov) hmet _ hwm)
    (hβsm.comp (f := fun t : ℝ => (-1) * t + m)
      ((contMDiff_const (I := 𝓘(ℝ)).mul contMDiff_id).add contMDiff_const))
    (fun t => Submission.GExpRayZero.isGeodesicAt_GExp_smul_all (cov := cov) hmet _ hwm t)
    (fun t => by
      have hh := Submission.HopfRinow.isGeodesicAt_comp_affine (cov := cov)
        (σ := fun s : ℝ => GExp (cov := cov) hmet p (s • η)) (a := -1) (b := m)
        (c := (-1) * t + m - 1) (d := (-1) * t + m + 1) (by norm_num)
        (hβsm.contMDiffOn.mono (Set.subset_univ _)) (fun y _ => hβgeo y) (r := t)
        ⟨by linarith, by linarith⟩
      simpa using hh)
    (fun t => Submission.RayChart.curveVelocity_GExp_ne_zero (cov := cov) hmet _ hwm t)
    (fun t => by
      intro h0
      have hv := Submission.Length.curveVelocity_comp_mul_add (I := I)
        (γ := fun s : ℝ => GExp (cov := cov) hmet p (s • η)) (c := -1) (d := m) (t := t)
        (hβsm.contMDiffAt.mdifferentiableAt (by simp))
      rw [h0] at hv
      have h1 : (-1 : ℝ) • curveVelocity (I := I)
          (fun s : ℝ => GExp (cov := cov) hmet p (s • η)) ((-1) * t + m) = 0 := hv.symm
      have h2 : curveVelocity (I := I) (fun s : ℝ => GExp (cov := cov) hmet p (s • η))
          ((-1) * t + m) = 0 := (smul_eq_zero.mp h1).resolve_left (by norm_num)
      exact hβne _ h2)
    (by
      show GExp (cov := cov) hmet (GExp (cov := cov) hmet p (m • ξ)) ((0 : ℝ) •
          curveVelocity (I := I) (fun t : ℝ => GExp (cov := cov) hmet p (t • ξ)) m)
        = GExp (cov := cov) hmet p (((-1) * (0 : ℝ) + m) • η)
      rw [zero_smul, GExp_zero, show (-1 : ℝ) * 0 + m = m from by ring]
      exact hmeet)
    (by
      rw [Submission.GExpVelocity.curveVelocity_GExp_smul_zero (cov := cov) hmet _ hwm,
        Submission.Length.curveVelocity_comp_mul_add (I := I)
          (γ := fun s : ℝ => GExp (cov := cov) hmet p (s • η)) (c := -1) (d := m) (t := 0)
          (hβsm.contMDiffAt.mdifferentiableAt (by simp)),
        show (-1 : ℝ) * 0 + m = m from by ring, neg_one_smul]
      exact hA)
    m
  rw [h, Submission.Length.curveVelocity_comp_mul_add (I := I)
    (γ := fun s : ℝ => GExp (cov := cov) hmet p (s • η)) (c := -1) (d := m) (t := m)
    (hβsm.contMDiffAt.mdifferentiableAt (by simp)),
    show (-1 : ℝ) * m + m = 0 from by ring, neg_one_smul,
    Submission.GExpVelocity.curveVelocity_GExp_smul_zero (cov := cov) hmet p hηne]

/-- **N3 — the closed geodesic of length `2m`.**  In the configuration of the closest cut point, the
ray of `ξ` is **periodic of period `2m`**:

`∀ u : ℝ, GExp p ((u + 2m) • ξ) = GExp p (u • ξ)`.

The ray is therefore a unit-speed closed geodesic of length `2m` through `p` (and through the cut
point), which is exactly what Synge's argument needs. -/
theorem ray_periodic_of_two_minimising (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    (hK : Submission.RauchK.CurvLe cov K) (hKpos : 0 < K) [PathConnectedSpace M] [RegularSpace M]
    {p : M} {m : ℝ} (hm : 0 < m) (hmπ : m < Real.pi / Real.sqrt K)
    (hinjp : InjAtLeast hmet p m) (hmaxp : ∀ r : ℝ, m < r → ¬ InjAtLeast hmet p r)
    (hinjall : InjAllAtLeast hmet m)
    {ξ η : TangentSpace I p} (hξ : ‖ξ‖ = 1) (hη : ‖η‖ = 1) (hξη : ξ ≠ η)
    (hmeet : GExp (cov := cov) hmet p (m • ξ) = GExp (cov := cov) hmet p (m • η))
    (hminξ : Manifold.riemannianEDist I p (GExp (cov := cov) hmet p (m • ξ)) = ENNReal.ofReal m)
    (hminη : Manifold.riemannianEDist I p (GExp (cov := cov) hmet p (m • η)) = ENNReal.ofReal m) :
    ∀ u : ℝ, GExp (cov := cov) hmet p ((u + 2 * m) • ξ)
      = GExp (cov := cov) hmet p (u • ξ) := by
  have hξne : ξ ≠ 0 := by intro h0; rw [h0, norm_zero] at hξ; norm_num at hξ
  have hηne : η ≠ 0 := by intro h0; rw [h0, norm_zero] at hη; norm_num at hη
  have hnc : ¬ ConjRadius.IsConjugateTime cov (fun t : ℝ => GExp (cov := cov) hmet p (t • ξ)) m :=
    Submission.ConjCut.not_isConjugateTime_of_lt_pi_div_sqrt (cov := cov) hmet htor hK hKpos hmπ
  -- Xu at `p`
  have hA : curveVelocity (I := I) (fun t : ℝ => GExp (cov := cov) hmet p (t • ξ)) m
      = -curveVelocity (I := I) (fun t : ℝ => GExp (cov := cov) hmet p (t • η)) m :=
    Submission.XuTrap.xuCornerExcluded (cov := cov) hmet htor p hm hinjp hmaxp ξ η hξ hη hξη
      hminξ hminη hmeet hnc
  -- N2: the two directions are antipodal
  have hneg : η = -ξ :=
    eq_neg_of_xuCornerExcluded_at_target (cov := cov) hmet htor hK hKpos hm hmπ hinjp hmaxp hinjall
      hξ hη hξη hmeet hminξ hminη
  -- flushness: the ray returns to `p` at `2m`
  have hret : GExp (cov := cov) hmet p ((2 * m) • ξ) = p :=
    GeodesicLoop.GExp_add_two_mul_of_velocity_eq_neg (cov := cov) hmet hξ hη hm hmeet hA
  -- the velocity at the return
  have hβsm : ContMDiff 𝓘(ℝ) I ∞ (fun t : ℝ => GExp (cov := cov) hmet p (t • ξ)) :=
    Submission.ConjEnergy.contMDiff_GExp_smul (cov := cov) hmet p hξne
  have hβgeo : ∀ t : ℝ, IsGeodesicAt cov (fun t : ℝ => GExp (cov := cov) hmet p (t • ξ)) t :=
    fun t => Submission.GExpRayZero.isGeodesicAt_GExp_smul_all (cov := cov) hmet p hξne t
  have hβne : ∀ t : ℝ, curveVelocity (I := I) (fun t : ℝ => GExp (cov := cov) hmet p (t • ξ)) t
      ≠ 0 :=
    fun t => Submission.RayChart.curveVelocity_GExp_ne_zero (cov := cov) hmet p hξne t
  have hvel : curveVelocity (I := I) (fun t : ℝ => GExp (cov := cov) hmet p (t • ξ)) (2 * m)
      = curveVelocity (I := I) (fun t : ℝ => GExp (cov := cov) hmet p (t • ξ)) 0 := by
    have h1 := curveVelocity_ray_shift (cov := cov) hmet
      (β := fun t : ℝ => GExp (cov := cov) hmet p (t • ξ))
      (q := GExp (cov := cov) hmet p (m • ξ)) (m := m) rfl hβsm hβgeo hβne
    have h2 := curveVelocity_ray_meeting (cov := cov) hmet hm hξne hηne hmeet hA
    have h3 : curveVelocity (I := I) (fun t : ℝ => GExp (cov := cov) hmet p (t • η)) 0 = η :=
      Submission.GExpVelocity.curveVelocity_GExp_smul_zero (cov := cov) hmet p hηne
    have h4 : curveVelocity (I := I) (fun t : ℝ => GExp (cov := cov) hmet p (t • ξ)) 0 = ξ :=
      Submission.GExpVelocity.curveVelocity_GExp_smul_zero (cov := cov) hmet p hξne
    rw [← h1, h2, h3, hneg, neg_neg, h4]
  exact ray_periodic_of_return_and_velocity (cov := cov) hmet hξ hret hvel


/-! ## N4: the extraction -/

/-- **N4, step 1: the cut-point sequence.**  If the *global* injectivity radius `m := injSup hmet` is
below the conjugate radius `π/√K`, then there is a sequence of points `p n`, of radii `mr n`
squeezed between `m` and `m + 1/(n+1)` (in particular `mr n → m`) and `mr n` *maximal* at `p n`, and
for each `n` two distinct unit directions `ξ n ≠ η n` at `p n` whose minimising rays of length
`mr n` meet at a common point.

This is the input of the compactness argument: `RayConj.exists_broken_minimising_loop_of_injAtLeast_of_lt_pi_div_sqrt`
applied at `p n` with radius `mr n`. -/
theorem exists_cutPoint_sequence (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    (hK : Submission.RauchK.CurvLe cov K) (hKpos : 0 < K) [PathConnectedSpace M] [RegularSpace M]
    (hmπ : Submission.InjSup.injSup hmet < Real.pi / Real.sqrt K) :
    ∃ (p : ℕ → M) (mr : ℕ → ℝ) (ξ η : (n : ℕ) → TangentSpace I (p n)),
      (∀ n, 0 < mr n) ∧
      (∀ n, Submission.InjSup.injSup hmet ≤ mr n) ∧
      (∀ n, mr n < Real.pi / Real.sqrt K) ∧
      (∀ n, mr n ≤ Submission.InjSup.injSup hmet + 1 / (n + 1 : ℝ)) ∧
      (∀ n, InjAtLeast hmet (p n) (mr n)) ∧
      (∀ n : ℕ, ∀ r : ℝ, mr n < r → ¬ InjAtLeast hmet (p n) r) ∧
      (∀ n, ‖ξ n‖ = 1) ∧ (∀ n, ‖η n‖ = 1) ∧ (∀ n, ξ n ≠ η n) ∧
      (∀ n, GExp (cov := cov) hmet (p n) (mr n • ξ n)
        = GExp (cov := cov) hmet (p n) (mr n • η n)) ∧
      (∀ n, Manifold.riemannianEDist I (p n) (GExp (cov := cov) hmet (p n) (mr n • ξ n))
        = ENNReal.ofReal (mr n)) ∧
      (∀ n, Manifold.riemannianEDist I (p n) (GExp (cov := cov) hmet (p n) (mr n • η n))
        = ENNReal.ofReal (mr n)) := by
  classical
  set m : ℝ := Submission.InjSup.injSup hmet with hmdef
  obtain ⟨ρ, hρ0, hρall⟩ := Submission.UniformInj.exists_pos_injAllAtLeast (cov := cov) hmet
  obtain ⟨x₀⟩ : Nonempty M := inferInstance
  obtain ⟨R, -, hR⟩ := Submission.CutTime.exists_edist_le (I := I) (cov := cov) hmet htor x₀
  have hbdd : BddAbove {r : ℝ | InjAllAtLeast hmet r} :=
    Submission.InjSup.bddAbove_injAllAtLeast_of_diam_le (cov := cov) hmet htor hR
  have hm0 : 0 < m := by
    rw [hmdef]
    exact lt_of_lt_of_le hρ0 (le_csSup hbdd hρall)
  have hinjall : InjAllAtLeast hmet m := by
    rw [hmdef]
    exact Submission.InjSup.injAllAtLeast_injSup hmet
  have hmaxall : ∀ r : ℝ, m < r → ¬ InjAllAtLeast hmet r := by
    intro r hr
    have hr' : Submission.InjSup.injSup hmet < r := by rw [hmdef] at hr; exact hr
    exact Submission.InjSup.not_injAllAtLeast_of_injSup_lt (cov := cov) hmet hbdd hr'
  -- for each `n`: a point and a maximal radius just above `m`
  have hkey : ∀ n : ℕ, ∃ (p : M) (mr : ℝ), 0 < mr ∧ m ≤ mr ∧ mr < Real.pi / Real.sqrt K ∧
      mr ≤ m + 1 / (n + 1 : ℝ) ∧ InjAtLeast hmet p mr ∧
      (∀ r : ℝ, mr < r → ¬ InjAtLeast hmet p r) := by
    intro n
    set δ : ℝ := min (1 / ((n : ℝ) + 1)) ((Real.pi / Real.sqrt K - m) / 2) with hδdef
    have hδ0 : 0 < δ := lt_min (by positivity) (by linarith)
    have hδπ : δ ≤ (Real.pi / Real.sqrt K - m) / 2 := min_le_right _ _
    have hδ1 : δ ≤ 1 / ((n : ℝ) + 1) := min_le_left _ _
    have hδnone : ¬ InjAllAtLeast hmet (m + δ) := hmaxall (m + δ) (by linarith)
    rw [InjAllAtLeast] at hδnone
    push_neg at hδnone
    obtain ⟨p, hp⟩ := hδnone
    obtain ⟨mr, hmr1, hmr2⟩ := Submission.InjRadius.exists_injAtLeast_max (cov := cov) hmet
      (x := p) ⟨m, hinjall p⟩ ⟨m + δ, hp⟩
    have hle : m ≤ mr := by
      by_contra hcon
      exact hmr2 m (lt_of_not_ge hcon) (hinjall p)
    have hlt : mr < m + δ := by
      by_contra hcon
      exact hp (injAtLeast_mono (I := I) hmet hmr1 (le_of_not_gt hcon))
    exact ⟨p, mr, lt_of_lt_of_le hm0 hle, hle, by linarith, by linarith, hmr1, hmr2⟩
  choose p mr h1 h2 h3 h4 h5 h6 using hkey
  -- the cut-point step at each `n`
  have hstep : ∀ n : ℕ, ∃ ξ η : TangentSpace I (p n), ‖ξ‖ = 1 ∧ ‖η‖ = 1 ∧ ξ ≠ η ∧
      GExp (cov := cov) hmet (p n) (mr n • ξ) = GExp (cov := cov) hmet (p n) (mr n • η) ∧
      (∀ t ∈ Icc (0 : ℝ) (mr n),
        Manifold.riemannianEDist I (p n) (GExp (cov := cov) hmet (p n) (t • ξ))
          = ENNReal.ofReal t) ∧
      (∀ t ∈ Icc (0 : ℝ) (mr n),
        Manifold.riemannianEDist I (p n) (GExp (cov := cov) hmet (p n) ((mr n - t) • η))
          = ENNReal.ofReal (mr n - t)) :=
    fun n => by
      obtain ⟨ξ, η, hξ, hη, hne, hmeet, -, -, -, -, -, hmin1, hmin2⟩ :=
        Submission.RayConj.exists_broken_minimising_loop_of_injAtLeast_of_lt_pi_div_sqrt
          (cov := cov) hmet htor hK hKpos (h1 n) (h3 n) (h5 n) (h6 n)
      exact ⟨ξ, η, hξ, hη, hne, hmeet, hmin1, hmin2⟩
  choose ξ η hξ hη hne hmeet hmin1 hmin2 using hstep
  exact ⟨p, mr, ξ, η, h1, h2, h3, h4, h5, h6, hξ, hη, hne, hmeet,
    fun n => hmin1 n (mr n) ⟨(h1 n).le, le_rfl⟩,
    fun n => by
      have h := hmin2 n 0 ⟨le_rfl, (h1 n).le⟩
      rw [sub_zero] at h
      exact h⟩


/-- **The witnesses of a failure of injectivity, in the shape used below.** -/
theorem exists_witness_pair_of_not_injAtLeast (hmet : IsMetricCompatible cov) {p : M} {r : ℝ}
    (h : ¬ InjAtLeast hmet p r) :
    ∃ u v : TangentSpace I p, ‖u‖ < r ∧ ‖v‖ < r ∧ u ≠ v ∧
      GExp (cov := cov) hmet p u = GExp (cov := cov) hmet p v := by
  rw [InjAtLeast] at h
  push_neg at h
  obtain ⟨u, v, hu, hv, hG, huv⟩ := h
  exact ⟨u, v, hu, hv, huv, hG⟩

/-- **The same, with the first vector normalised to be non-zero.**  Given a failure of injectivity at
radius `r > 0` one can always choose the witness pair so that its *first* member is non-zero: if the
given first member vanishes, exchange the two (a non-zero vector cannot have the zero vector as a
partner, since the two are required to be distinct).  This is what makes
`RayConj.locallyInjectiveAtGExp_of_norm_lt_pi_div_sqrt` applicable to the first member later on. -/
theorem exists_witness_pair_ne_zero_of_not_injAtLeast (hmet : IsMetricCompatible cov) {p : M}
    {r : ℝ} (hr : 0 < r) (h : ¬ InjAtLeast hmet p r) :
    ∃ u v : TangentSpace I p, u ≠ 0 ∧ ‖u‖ < r ∧ ‖v‖ < r ∧ u ≠ v ∧
      GExp (cov := cov) hmet p u = GExp (cov := cov) hmet p v := by
  obtain ⟨a, b, ha, hb, hab, hG⟩ := exists_witness_pair_of_not_injAtLeast (cov := cov) hmet h
  by_cases h0 : a = 0
  · have hb0 : b ≠ 0 := fun hb' => hab (by rw [h0, hb'])
    exact ⟨b, a, hb0, hb, ha, hab.symm, hG.symm⟩
  · exact ⟨a, b, h0, ha, hb, hab, hG⟩

end

end Submission.KlingenbergEven
