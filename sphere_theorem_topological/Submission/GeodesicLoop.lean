import Submission.KlingenbergLoop
import Submission.GExpGlob
import Submission.GExpRayZero
import Submission.GExpRayIdent
import Submission.InjRadiusCut
import Submission.CornerStrict
import Submission.Shorten
import Submission.LensLoop
import Submission.KlingenbergLemma

/-!
# Geodesic loops (value-closed) and the Klingenberg–Xu step

Klingenberg's lemma, in the sharp modern form of Xu (*On conjugate points and geodesic loops in a
complete Riemannian manifold*, arXiv:1401.5549, Theorem B), is a statement about **geodesic loops**:

> if `x₀` is a closest cut point of `p` and `p` is not conjugate to `x₀` along some minimising
> geodesic, then the minimal geodesics from `p` to `x₀` form a whole geodesic smoothly passing
> through `x₀`.

Concatenating the two minimal geodesics gives a **geodesic arc** `γ : [0, 2m] → M` with
`γ 0 = γ (2m) = p` — a *geodesic loop at `p`*.  This is strictly more general than the
velocity-matched object `Submission.KlingenbergLemma.IsClosedGeodesicLoopAt`: the velocities need not
match at the base point (Xu's Theorem B acquires the matching only under the extra hypothesis that
`d(p,x₀)` is also a local minimum of `d(x₀,·)` on `C_{x₀}`).

This file introduces the value-closed predicate `IsGeodesicLoopAt`, its basic theory, the
**extremal lens** (the case `v = -u` of the cut-point data, where the loop is obtained from the
`u`-ray directly), and the **flushness lemma** which converts the straightness of the corner at the
cut point into the statement that the ray returns to the base point.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option autoImplicit false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.GlobalExp
open Submission.InjRadius
open Submission.LensLoop
open Submission.GExpRayZero
open Submission.GExpRayIdent
open Submission.GeodesicExtend
open Submission.GExpVelocity
open Submission.HopfRinow
open Submission.Length

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

namespace Submission.GeodesicLoop

noncomputable section

variable [I.Boundaryless] [Nontrivial E] [CompactSpace M]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]

/-- **A geodesic loop at `p` of length `T`** (Xu's notion): a `C^∞` curve `γ : ℝ → M` which is a
geodesic at every parameter, has unit speed, and satisfies `γ 0 = γ T = p`.  Unlike
`Submission.KlingenbergLemma.IsClosedGeodesicLoopAt` **no matching of the velocities at the base
point is required** — this is the object Xu's Theorem B produces. -/
def IsGeodesicLoopAt (hmet : IsMetricCompatible cov) (p : M) (T : ℝ) (γ : ℝ → M) : Prop :=
  0 < T ∧ γ 0 = p ∧ γ T = p ∧ ContMDiffOn 𝓘(ℝ) I ∞ γ univ ∧
    (∀ t : ℝ, IsGeodesicAt cov γ t) ∧ (∀ t : ℝ, ‖curveVelocity (I := I) γ t‖ = 1)

/-- A velocity-matched closed geodesic loop is a geodesic loop. -/
theorem IsClosedGeodesicLoopAt.isGeodesicLoopAt (hmet : IsMetricCompatible cov)
    {p : M} {T : ℝ} {γ : ℝ → M}
    (h : Submission.KlingenbergLemma.IsClosedGeodesicLoopAt hmet p T γ) :
    IsGeodesicLoopAt (I := I) (cov := cov) hmet p T γ :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1⟩

/-- A geodesic loop whose velocity matches at the base point is a closed geodesic loop. -/
theorem IsGeodesicLoopAt.isClosedGeodesicLoopAt (hmet : IsMetricCompatible cov)
    {p : M} {T : ℝ} {γ : ℝ → M} (h : IsGeodesicLoopAt (I := I) (cov := cov) hmet p T γ)
    (hvel : curveVelocity (I := I) γ T = curveVelocity (I := I) γ 0) :
    Submission.KlingenbergLemma.IsClosedGeodesicLoopAt hmet p T γ :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2, hvel⟩

/-- **The `GExp`-ray is a geodesic loop whenever it returns to its base point.** -/
theorem isGeodesicLoopAt_GExp_smul_of_returns (hmet : IsMetricCompatible cov) (p : M)
    {ξ : TangentSpace I p} (hξ : ‖ξ‖ = 1) {T : ℝ} (hT : 0 < T)
    (hret : GExp (cov := cov) hmet p (T • ξ) = p) :
    IsGeodesicLoopAt (I := I) (cov := cov) hmet p T
      (fun s : ℝ => GExp (cov := cov) hmet p (s • ξ)) := by
  have hξne : ξ ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hξ; norm_num at hξ
  refine ⟨hT, ?_, hret, ?_, ?_, ?_⟩
  · show GExp (cov := cov) hmet p (0 • ξ) = p
    rw [zero_smul, GExp_zero]
  · exact Submission.LensLoop.contMDiffOn_GExp_smul (cov := cov) hmet p hξne
  · intro t
    exact isGeodesicAt_GExp_smul_all (cov := cov) hmet p hξne t
  · intro t
    rw [← Submission.GeodesicSpeed.curveSpeed_eq_norm
      (fun s : ℝ => GExp (cov := cov) hmet p (s • ξ)) t]
    rw [Submission.BrokenLength.curveSpeed_GExp_ray (cov := cov) hmet p hξne t]
    exact hξ

/-- **The extremal lens.**  If the unit ray of `ξ` at `p` meets itself again at the parameters `-1`
and `1` (i.e. `GExp p ξ = GExp p (-ξ)`), then the ray between these two parameters is a **geodesic
loop** at `q = GExp p ξ` of length `2`, passing through `p` in the middle. -/
theorem isGeodesicLoopAt_GExp_lens (hmet : IsMetricCompatible cov) (p : M)
    {ξ : TangentSpace I p} (hξ : ‖ξ‖ = 1)
    (heq : GExp (cov := cov) hmet p ξ = GExp (cov := cov) hmet p (-ξ)) :
    IsGeodesicLoopAt (I := I) (cov := cov) hmet (GExp (cov := cov) hmet p ξ) 2
      (fun s : ℝ => GExp (cov := cov) hmet p ((s - 1) • ξ)) := by
  have hξne : ξ ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hξ; norm_num at hξ
  set ρ : ℝ → M := fun r : ℝ => GExp (cov := cov) hmet p (r • ξ) with hρdef
  set γ : ℝ → M := fun s : ℝ => GExp (cov := cov) hmet p ((s - 1) • ξ) with hγdef
  have heq' : γ = fun s : ℝ => GExp (cov := cov) hmet p ((1 * s + (-1)) • ξ) := by
    funext s
    rw [hγdef]
    congr 1
    ring
  have heqρ : (fun s : ℝ => GExp (cov := cov) hmet p ((1 * s + (-1)) • ξ))
      = ρ ∘ (fun s : ℝ => 1 * s + (-1)) := by
    funext s
    rw [hρdef]
    rfl
  have hρsm : ContMDiffOn 𝓘(ℝ) I ∞ ρ univ := by
    rw [hρdef]
    exact Submission.LensLoop.contMDiffOn_GExp_smul (cov := cov) hmet p hξne
  have hρgeo : ∀ y : ℝ, IsGeodesicAt cov ρ y := by
    intro y
    rw [hρdef]
    exact isGeodesicAt_GExp_smul_all (cov := cov) hmet p hξne y
  have hmd : MDifferentiableAt 𝓘(ℝ) I ρ 0 :=
    (hρsm.contMDiffAt Filter.univ_mem).mdifferentiableAt (by simp)
  have haff : ContMDiff 𝓘(ℝ) 𝓘(ℝ) ∞ (fun s : ℝ => 1 * s + (-1)) :=
    (contMDiff_const.mul contMDiff_id).add contMDiff_const
  have hsmγ : ContMDiffOn 𝓘(ℝ) I ∞ γ univ := by
    rw [heq', heqρ]
    exact hρsm.comp haff.contMDiffOn (fun s _ => Set.mem_univ _)
  have hgeoγ : ∀ t : ℝ, IsGeodesicAt cov γ t := by
    intro t
    have hmain : IsGeodesicAt cov (fun s : ℝ => ρ (1 * s + (-1))) t :=
      isGeodesicAt_comp_affine (cov := cov) (σ := ρ) (a := 1) (b := -1)
        (c := 1 * t + (-1) - 1) (d := 1 * t + (-1) + 1) (by norm_num)
        (hρsm.mono (Set.subset_univ _)) (fun y _ => hρgeo y) (r := t)
        (Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩)
    rw [heq', heqρ]
    exact hmain
  have hspeed : ∀ t : ℝ, ‖curveVelocity (I := I) γ t‖ = 1 := by
    intro t
    rw [← Submission.GeodesicSpeed.curveSpeed_eq_norm γ t]
    have hmd' : MDifferentiableAt 𝓘(ℝ) I ρ (1 * t + (-1)) :=
      (hρsm.contMDiffAt Filter.univ_mem).mdifferentiableAt (by simp)
    have h1 : curveSpeed (I := I) γ t
        = curveSpeed (I := I) (fun s : ℝ => ρ (1 * s + (-1))) t := by
      rw [heq', hρdef]
    rw [h1, Submission.LensLoop.curveSpeed_comp_mul_add_abs (I := I) (γ := ρ) (c := 1) (d := -1)
      (t := t) (by norm_num) hmd']
    rw [show |(1 : ℝ)| = 1 from by norm_num, one_mul, hρdef]
    rw [Submission.BrokenLength.curveSpeed_GExp_ray (cov := cov) hmet p hξne (1 * t + (-1))]
    exact hξ
  refine ⟨by norm_num, ?_, ?_, hsmγ, hgeoγ, hspeed⟩
  · show GExp (cov := cov) hmet p ((0 - 1) • ξ) = GExp (cov := cov) hmet p ξ
    rw [show (0 : ℝ) - 1 = -1 from by ring, neg_smul, one_smul]
    exact heq.symm
  · show GExp (cov := cov) hmet p ((2 - 1) • ξ) = GExp (cov := cov) hmet p ξ
    rw [show (2 : ℝ) - 1 = 1 from by ring, one_smul]

/-! ## Flushness: when the two minimal geodesics form a single geodesic

Let `ξ ≠ η` be unit directions at `p` whose rays meet at `q = GExp p (m • ξ) = GExp p (m • η)`.
The concatenation `β` of the two minimal geodesics `p → q → p` is a geodesic at the junction `q`
exactly when the two rays arrive there with **opposite velocities** (`w₁ = -w₂`, where `wᵢ` is the
velocity of the `i`-th ray at time `m`).  In that case `β` is a single geodesic on `[0, 2m]`, so in
particular the first ray **returns to `p`** at time `2m` — and hence is a geodesic loop at `p` of
length `2m`.

This is the "flush at the two ends" step of the fat-case analysis of Klingenberg's theorem
(`Submission/Roadmap.lean` §80.2). -/

/-- **The reversed ray identification.**  If `q = GExp p (s₀ • ξ)` is a point of the ray of `ξ`, then
the reversed ray from `q` in the direction `-w` (where `w` is the velocity of the ray at `s₀`)
traces the ray backwards: `GExp q (s • (-w)) = GExp p ((s₀ - s) • ξ)`. -/
theorem GExp_neg_velocity_of_ray (hmet : IsMetricCompatible cov) (p : M)
    {ξ : TangentSpace I p} (hξ : ‖ξ‖ = 1) {m : ℝ} (hm : 0 < m) {s : ℝ} (hsm : 0 ≤ s)
    (hsle : s ≤ m) :
    GExp (cov := cov) hmet (GExp (cov := cov) hmet p (m • ξ))
        (s • (-curveVelocity (I := I) (fun t : ℝ => GExp (cov := cov) hmet p (t • ξ)) m))
      = GExp (cov := cov) hmet p ((m - s) • ξ) := by
  have hξne : ξ ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hξ; norm_num at hξ
  set ρ : ℝ → M := fun t : ℝ => GExp (cov := cov) hmet p (t • ξ) with hρdef
  set w : TangentSpace I (GExp (cov := cov) hmet p (m • ξ)) := curveVelocity (I := I) ρ m with hwdef
  have hsmρ : ContMDiffOn 𝓘(ℝ) I ∞ ρ univ := by
    rw [hρdef]
    exact Submission.LensLoop.contMDiffOn_GExp_smul (cov := cov) hmet p hξne
  have hgeoρ : ∀ y ∈ Ioo (-1 : ℝ) (m + 1), IsGeodesicAt cov ρ y := by
    intro y _
    rw [hρdef]
    exact isGeodesicAt_GExp_smul_all (cov := cov) hmet p hξne y
  have hsmρ' : ContMDiffOn 𝓘(ℝ) I ∞ ρ (Ioo (-1 : ℝ) (m + 1)) :=
    hsmρ.mono (Set.subset_univ _)
  have hneρ : ∀ y ∈ Ioo (-1 : ℝ) (m + 1), curveVelocity (I := I) ρ y ≠ 0 := by
    intro y _
    rw [hρdef]
    exact Submission.RayChart.curveVelocity_GExp_ne_zero (cov := cov) hmet p hξne y
  have hwne : w ≠ 0 := by
    rw [hwdef]
    exact Submission.RayChart.curveVelocity_GExp_ne_zero (cov := cov) hmet p hξne m
  have hsig : (fun s : ℝ => ρ (m - s)) = fun s : ℝ => GExp (cov := cov) hmet p ((m - s) • ξ) := by
    funext s
    rw [hρdef]
  have h0 : (fun s : ℝ => ρ (m - s)) 0 = GExp (cov := cov) hmet p (m • ξ) := by
    show ρ (m - 0) = GExp (cov := cov) hmet p (m • ξ)
    rw [sub_zero, hρdef]
  have hvel : curveVelocity (I := I) (fun s : ℝ => ρ (m - s)) 0
      = -curveVelocity (I := I) ρ m := by
    rw [Submission.HopfRinow.curveVelocity_comp_sub_neg_at (I := I) (γ := ρ) (t := m) (r := 0)
      ((hsmρ.contMDiffAt Filter.univ_mem).mdifferentiableAt (by simp))]
    rw [sub_zero]
  have hmain := Submission.GExpRayIdent.eqOn_Icc_GExp_of_isGeodesicAt (cov := cov) hmet
    (p := GExp (cov := cov) hmet p (m • ξ)) (V := -curveVelocity (I := I) ρ m) (neg_ne_zero.mpr hwne)
    (a := (-1 : ℝ)) (b := m + 1) (T := m) (by linarith) (le_of_lt hm) (by linarith)
    (γ := fun s : ℝ => ρ (m - s))
    (Submission.HopfRinow.contMDiffOn_comp_sub_neg (I := I) hsmρ' (fun r hr => by
      exact Set.mem_Ioo.mpr ⟨by linarith [hr.2], by linarith [hr.1]⟩))
    (fun y hy => Submission.HopfRinow.isGeodesicAt_comp_sub_neg_at (cov := cov) (γ := ρ)
      (c := (-1 : ℝ)) (d := m + 1) hsmρ' hgeoρ (r := y) (by
        exact Set.mem_Ioo.mpr ⟨by linarith [hy.2], by linarith [hy.1]⟩))
    (fun y hy => by
      rw [Submission.HopfRinow.curveVelocity_comp_sub_neg_at (I := I) (γ := ρ) (t := m) (r := y)
        ((hsmρ.contMDiffAt Filter.univ_mem).mdifferentiableAt (by simp))]
      exact neg_ne_zero.mpr (hneρ (m - y) (by
        exact Set.mem_Ioo.mpr ⟨by linarith [hy.2], by linarith [hy.1]⟩)))
    h0 hvel
  have h := hmain s (Set.mem_Icc.mpr ⟨hsm, hsle⟩)
  simpa only [hwdef, hρdef] using h.symm

/-- **The genuine-corner direction of the corner bound.**  Let `ξ ≠ η` be unit directions at `p`
whose rays meet at `q = GExp p (m • ξ) = GExp p (m • η)`, and suppose the two rays do **not** arrive
at `q` with opposite velocities.  Then for every `0 < ε < min(m, ρ)` (with `ρ` a radius at which
`GExp` is injective at every point) the two points at distance `ε` back along the two rays are
**strictly closer** than `2ε`:

`d (GExp p ((m-ε) • ξ)) (GExp p ((m-ε) • η)) < 2 ε`.

This carries the equality `GExp p (m • ξ) = GExp p (m • η)` downstream: the two reverse directions
live in `TangentSpace I (GExp p (m • ξ))` and `TangentSpace I (GExp p (m • η))`, which are only
*propositionally* equal.  The proof never needs to transport them: `TangentSpace I x` is
definitionally the model space `E`, so a reverse direction computed on either side is accepted where
the other side's tangent space is expected, and — crucially — it is accepted with the *same mutual
instances*, so no `Eq.rec` bookkeeping arises. -/
theorem edist_feet_lt_of_velocity_ne_neg (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    [PathConnectedSpace M] [RegularSpace M]
    {ρ : ℝ} (hInjAll : InjAllAtLeast hmet ρ)
    (p : M) {ξ η : TangentSpace I p} (hξ : ‖ξ‖ = 1) (hη : ‖η‖ = 1) {m : ℝ} (hm : 0 < m)
    (hmeet : GExp (cov := cov) hmet p (m • ξ) = GExp (cov := cov) hmet p (m • η))
    (hw : curveVelocity (I := I) (fun t : ℝ => GExp (cov := cov) hmet p (t • ξ)) m
      ≠ -curveVelocity (I := I) (fun t : ℝ => GExp (cov := cov) hmet p (t • η)) m)
    {ε : ℝ} (hε : 0 < ε) (hεm : ε < m) (hερ : ε < ρ) :
    Manifold.riemannianEDist I (GExp (cov := cov) hmet p ((m - ε) • ξ))
      (GExp (cov := cov) hmet p ((m - ε) • η)) < ENNReal.ofReal (2 * ε) := by
  have hξne : ξ ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hξ; norm_num at hξ
  have hηne : η ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hη; norm_num at hη
  have hnorm1 : ‖(-curveVelocity (I := I) (fun t : ℝ => GExp (cov := cov) hmet p (t • ξ)) m)‖
      = 1 := by
    rw [show (-curveVelocity (I := I) (fun t : ℝ => GExp (cov := cov) hmet p (t • ξ)) m)
        = (-1 : ℝ) • curveVelocity (I := I) (fun t : ℝ => GExp (cov := cov) hmet p (t • ξ)) m
        from by simp]
    rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_one, one_mul,
      Submission.LensLoop.norm_curveVelocity_GExp_smul_ne (cov := cov) hmet p hξne (ne_of_gt hm)]
    exact hξ
  have hnorm2 : ‖(-curveVelocity (I := I) (fun t : ℝ => GExp (cov := cov) hmet p (t • η)) m)‖
      = 1 := by
    rw [show (-curveVelocity (I := I) (fun t : ℝ => GExp (cov := cov) hmet p (t • η)) m)
        = (-1 : ℝ) • curveVelocity (I := I) (fun t : ℝ => GExp (cov := cov) hmet p (t • η)) m
        from by simp]
    rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_one, one_mul,
      Submission.LensLoop.norm_curveVelocity_GExp_smul_ne (cov := cov) hmet p hηne (ne_of_gt hm)]
    exact hη
  have hne : (-curveVelocity (I := I) (fun t : ℝ => GExp (cov := cov) hmet p (t • ξ)) m)
      ≠ -(-curveVelocity (I := I) (fun t : ℝ => GExp (cov := cov) hmet p (t • η)) m) := by
    intro hcon
    rw [neg_neg] at hcon
    exact hw (neg_eq_iff_eq_neg.mp hcon)
  -- move the η-side facts to the common base point `GExp p (m • ξ)`
  rw [hmeet.symm] at hnorm2 hne
  have hcorn := Submission.CornerStrict.edist_GExp_lt_of_unit_ne_neg (cov := cov) hmet htor hInjAll
    (GExp (cov := cov) hmet p (m • ξ))
    (u₁ := -curveVelocity (I := I) (fun t : ℝ => GExp (cov := cov) hmet p (t • ξ)) m)
    (u₂ := -curveVelocity (I := I) (fun t : ℝ => GExp (cov := cov) hmet p (t • η)) m)
    hnorm1 hnorm2 hne hε hερ
  have e1 : GExp (cov := cov) hmet (GExp (cov := cov) hmet p (m • ξ))
      (ε • (-curveVelocity (I := I) (fun t : ℝ => GExp (cov := cov) hmet p (t • ξ)) m))
      = GExp (cov := cov) hmet p ((m - ε) • ξ) :=
    GExp_neg_velocity_of_ray (cov := cov) hmet p (ξ := ξ) hξ hm (s := ε) hε.le hεm.le
  have e2 : GExp (cov := cov) hmet (GExp (cov := cov) hmet p (m • ξ))
      (ε • (-curveVelocity (I := I) (fun t : ℝ => GExp (cov := cov) hmet p (t • η)) m))
      = GExp (cov := cov) hmet p ((m - ε) • η) := by
    have h2 := GExp_neg_velocity_of_ray (cov := cov) hmet p (ξ := η) hη hm (s := ε) hε.le hεm.le
    rw [← hmeet] at h2
    exact h2
  rw [← e1, ← e2]
  exact hcorn

/-- **Flushness.**  If two unit rays from `p` meet at `q` at time `m` and arrive there with opposite
velocities, then the first ray returns to `p` at time `2m`.  Equivalently: the concatenation of the
two minimal geodesics `p → q` and `q → p` is a single geodesic through `q`, of length `2m`. -/
theorem GExp_add_two_mul_of_velocity_eq_neg (hmet : IsMetricCompatible cov)
    {p : M} {ξ η : TangentSpace I p} (hξ : ‖ξ‖ = 1) (hη : ‖η‖ = 1) {m : ℝ} (hm : 0 < m)
    (hmeet : GExp (cov := cov) hmet p (m • ξ) = GExp (cov := cov) hmet p (m • η))
    (hvel : curveVelocity (I := I) (fun t : ℝ => GExp (cov := cov) hmet p (t • ξ)) m
      = -curveVelocity (I := I) (fun t : ℝ => GExp (cov := cov) hmet p (t • η)) m) :
    GExp (cov := cov) hmet p ((2 * m) • ξ) = p := by
  have hadd := Submission.GExpGlob.GExp_add_smul (cov := cov) hmet (p := p) hξ (s := m) (t := m)
    hm (le_of_lt hm)
  have hback := GExp_neg_velocity_of_ray (cov := cov) hmet p (ξ := η) hη hm (s := m)
    (le_of_lt hm) le_rfl
  rw [← hvel] at hback
  have hsub : m - m = (0 : ℝ) := by ring
  rw [hsub, zero_smul, GExp_zero] at hback
  calc GExp (cov := cov) hmet p ((2 * m) • ξ)
      = GExp (cov := cov) hmet p ((m + m) • ξ) := by ring_nf
    _ = GExp (cov := cov) hmet (GExp (cov := cov) hmet p (m • ξ))
          (m • curveVelocity (I := I) (fun t : ℝ => GExp (cov := cov) hmet p (t • ξ)) m) := hadd
    _ = GExp (cov := cov) hmet (GExp (cov := cov) hmet p (m • η))
          (m • curveVelocity (I := I) (fun t : ℝ => GExp (cov := cov) hmet p (t • ξ)) m) := by
        rw [hmeet]
    _ = p := hback

/-- **The Klingenberg–Xu step in the "flush" case.**  If two unit rays from `p` meet at `q` at time
`m` with opposite velocities there, then the ray of `ξ` is a **geodesic loop at `p` of length `2m`**
(in Xu's value-closed sense). -/
theorem isGeodesicLoopAt_of_velocity_eq_neg (hmet : IsMetricCompatible cov)
    {p : M} {ξ η : TangentSpace I p} (hξ : ‖ξ‖ = 1) (hη : ‖η‖ = 1) {m : ℝ} (hm : 0 < m)
    (hmeet : GExp (cov := cov) hmet p (m • ξ) = GExp (cov := cov) hmet p (m • η))
    (hvel : curveVelocity (I := I) (fun t : ℝ => GExp (cov := cov) hmet p (t • ξ)) m
      = -curveVelocity (I := I) (fun t : ℝ => GExp (cov := cov) hmet p (t • η)) m) :
    IsGeodesicLoopAt (I := I) (cov := cov) hmet p (2 * m)
      (fun s : ℝ => GExp (cov := cov) hmet p (s • ξ)) :=
  isGeodesicLoopAt_GExp_smul_of_returns (I := I) (cov := cov) hmet p hξ (by linarith)
    (GExp_add_two_mul_of_velocity_eq_neg (cov := cov) hmet hξ hη hm hmeet hvel)

/-! ## The Klingenberg–Xu step: the two alternatives

Given two unit directions `ξ ≠ η` at `p` whose rays meet at `q` at time `m`, exactly one of the two
situations occurs at the junction `q`:

* either the two rays arrive there with **opposite velocities** (`w₁ = -w₂`) — then the two minimal
  geodesics are the two halves of one whole geodesic, and the first ray is a geodesic loop at `p`
  of length `2m` (`isGeodesicLoopAt_of_velocity_eq_neg`);
* or the corner at `q` is genuine, and the broken loop can be **shortened**
  (`exists_shorter_loop_of_two_minimising`).

Xu's Theorem B (arXiv:1401.5549) is the statement that the second alternative cannot occur when `q`
is the *closest* cut point of `p` and `p` is not conjugate to `q`; it is the remaining input of the
Klingenberg–Xu step. -/

/-! ## A geodesic loop bounds the injectivity radius at its base point

The easy half of Klingenberg's structure theorem, for the *value-closed* predicate:
**`IsGeodesicLoopAt hmet p T γ` and `InjAtLeast hmet p r` imply `r ≤ T/2`.**
The subtlety is that `LensLoop.two_mul_le_of_isGeodesicAt_loop_speed` asks for the *non-reversal*
hypothesis `(T/2) • γ̇ 0 ≠ (T/2) • γ̇(T⁻)`; here it is **discharged** by the observation that a
unit-speed geodesic cannot satisfy `γ̇(T) = -γ̇(0)` when `γ T = γ 0`: such a geodesic would retrace
itself, forcing `γ̇(T/2) = 0`. -/

/-- **A unit-speed geodesic with `γ T = γ 0` never reverses its velocity.**  Otherwise the geodesic
would retrace itself (`γ (T - s) = γ s`, by uniqueness of the geodesic with the initial data at `0`)
and hence satisfy `γ̇(T/2) = -γ̇(T/2) = 0`, contradicting unit speed. -/
theorem curveVelocity_ne_neg_of_loop (hmet : IsMetricCompatible cov)
    {γ : ℝ → M} (hsm : ContMDiffOn 𝓘(ℝ) I ∞ γ univ) (hgeo : ∀ t : ℝ, IsGeodesicAt cov γ t)
    (hsp : ∀ t : ℝ, ‖curveVelocity (I := I) γ t‖ = 1) {T : ℝ} (hT : 0 < T) (hloop : γ T = γ 0) :
    curveVelocity (I := I) γ T ≠ -curveVelocity (I := I) γ 0 := by
  classical
  intro hcon
  have hne0 : curveVelocity (I := I) γ 0 ≠ 0 := by
    have h1 := hsp 0
    intro h0; rw [h0, norm_zero] at h1; norm_num at h1
  -- the ray identifications of `γ` and of its reversal, on `[0,T]`
  have hγid : ∀ t ∈ Icc (0:ℝ) T,
      γ t = GExp (cov := cov) hmet (γ 0) (t • curveVelocity (I := I) γ 0) :=
    Submission.GExpRayIdent.eqOn_Icc_GExp_of_isGeodesicAt (cov := cov) hmet (p := γ 0)
      (V := curveVelocity (I := I) γ 0) hne0 (a := (-1 : ℝ)) (b := T + 1) (T := T)
      (by linarith) hT.le (by linarith) (hsm.mono (Set.subset_univ _))
      (fun t _ => hgeo t)
      (fun t _ => by
        have h1 := hsp t
        intro h0; rw [h0, norm_zero] at h1; norm_num at h1)
      rfl rfl
  have hρsm : ContMDiffOn 𝓘(ℝ) I ∞ (fun s : ℝ => γ (T - s)) univ :=
    hsm.comp (contDiff_const.sub contDiff_id).contMDiff.contMDiffOn (fun s _ => Set.mem_univ _)
  have hρgeo : ∀ t : ℝ, IsGeodesicAt cov (fun s : ℝ => γ (T - s)) t := by
    intro t
    exact Submission.HopfRinow.isGeodesicAt_comp_sub_neg_at (cov := cov) (γ := γ)
      (c := T - t - 1) (d := T - t + 1) (hsm.mono (Set.subset_univ _))
      (fun y _ => hgeo y) (r := t) (Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩)
  have hρne : ∀ t ∈ Ioo (-1 : ℝ) (T + 1),
      curveVelocity (I := I) (fun s : ℝ => γ (T - s)) t ≠ 0 := by
    intro t _
    rw [Submission.HopfRinow.curveVelocity_comp_sub_neg_at (I := I) (γ := γ) (t := T) (r := t)
      ((hsm.contMDiffAt Filter.univ_mem).mdifferentiableAt (by simp))]
    exact neg_ne_zero.mpr (by
      have h1 := hsp (T - t)
      intro h0; rw [h0, norm_zero] at h1; norm_num at h1)
  have hρ0 : (fun s : ℝ => γ (T - s)) 0 = γ 0 := by
    show γ (T - 0) = γ 0
    rw [sub_zero, hloop]
  have hρv : curveVelocity (I := I) (fun s : ℝ => γ (T - s)) 0 = curveVelocity (I := I) γ 0 := by
    rw [Submission.HopfRinow.curveVelocity_comp_sub_neg_at (I := I) (γ := γ) (t := T) (r := 0)
      ((hsm.contMDiffAt Filter.univ_mem).mdifferentiableAt (by simp))]
    rw [sub_zero]
    exact neg_eq_iff_eq_neg.mpr hcon
  have hρid : ∀ t ∈ Icc (0:ℝ) T,
      γ (T - t) = GExp (cov := cov) hmet (γ 0) (t • curveVelocity (I := I) γ 0) :=
    Submission.GExpRayIdent.eqOn_Icc_GExp_of_isGeodesicAt (cov := cov) hmet (p := γ 0)
      (V := curveVelocity (I := I) γ 0) hne0 (a := (-1 : ℝ)) (b := T + 1) (T := T)
      (by linarith) hT.le (by linarith) (hρsm.mono (Set.subset_univ _))
      (fun t _ => hρgeo t) hρne hρ0 hρv
  -- so the reversal agrees with `γ` on `[0,T]`
  have hagg : ∀ t ∈ Icc (0:ℝ) T, γ (T - t) = γ t := fun t ht =>
    (hρid t ht).trans (hγid t ht).symm
  -- hence the velocities at `T/2` agree, and `γ̇(T/2) = -γ̇(T/2)`
  have hmem : Icc (0:ℝ) T ∈ 𝓝 (T / 2) := Icc_mem_nhds (by linarith) (by linarith)
  have hv1 : curveVelocity (I := I) (fun s : ℝ => γ (T - s)) (T / 2)
      = curveVelocity (I := I) γ (T / 2) :=
    Submission.RayJacobi.curveVelocity_congr (I := I) (Filter.eventually_of_mem hmem hagg)
  have hv2 : curveVelocity (I := I) (fun s : ℝ => γ (T - s)) (T / 2)
      = -curveVelocity (I := I) γ (T / 2) := by
    rw [Submission.HopfRinow.curveVelocity_comp_sub_neg_at (I := I) (γ := γ) (t := T) (r := T / 2)
      ((hsm.contMDiffAt Filter.univ_mem).mdifferentiableAt (by simp))]
    rw [show T - T / 2 = T / 2 from by ring]
  have hzero : curveVelocity (I := I) γ (T / 2) = 0 := by
    have hvv : curveVelocity (I := I) γ (T / 2) = -curveVelocity (I := I) γ (T / 2) :=
      hv1.symm.trans hv2
    have h2 : (2 : ℝ) • curveVelocity (I := I) γ (T / 2) = 0 := by
      rw [two_smul]
      nth_rewrite 1 [hvv]
      exact neg_add_cancel _
    exact (smul_eq_zero.mp h2).resolve_left (by norm_num)
  have := hsp (T / 2)
  rw [hzero, norm_zero] at this
  norm_num at this

/-- **A geodesic loop bounds the injectivity radius at its base point.**  If `γ` is a value-closed
geodesic loop at `p` of length `T` (unit speed, `C^∞`) and the exponential map at `p` is injective on
the ball of radius `r`, then `2r ≤ T`. -/
theorem IsGeodesicLoopAt.two_mul_le_injAtLeast (hmet : IsMetricCompatible cov)
    (htor : cov.torsion = 0) {p : M} {T r : ℝ} {γ : ℝ → M}
    (h : IsGeodesicLoopAt (I := I) (cov := cov) hmet p T γ) (hinj : InjAtLeast hmet p r) :
    2 * r ≤ T := by
  obtain ⟨hT, hγ0, hγT, hsm, hgeo, hsp⟩ := h
  have hbase : InjAtLeast hmet (γ 0) r := by rw [hγ0]; exact hinj
  have hvelne : (T / 2) • curveVelocity (I := I) γ 0
      ≠ (T / 2) • curveVelocity (I := I) (fun s : ℝ => γ (T - s)) 0 := by
    rw [show curveVelocity (I := I) (fun s : ℝ => γ (T - s)) 0 = -curveVelocity (I := I) γ T from by
      rw [Submission.HopfRinow.curveVelocity_comp_sub_neg_at (I := I) (γ := γ) (t := T) (r := 0)
        ((hsm.contMDiffAt Filter.univ_mem).mdifferentiableAt (by simp))]
      rw [sub_zero]]
    intro hcon
    have hne0 : (T / 2) ≠ 0 := by linarith
    have h'' : curveVelocity (I := I) γ 0 = -curveVelocity (I := I) γ T :=
      smul_right_injective (TangentSpace I (γ (T / 2))) hne0 hcon
    have h3 : curveVelocity (I := I) γ T = -curveVelocity (I := I) γ 0 :=
      neg_eq_iff_eq_neg.mp h''.symm
    exact curveVelocity_ne_neg_of_loop (cov := cov) hmet hsm hgeo hsp hT (hγT.trans hγ0.symm) h3
  have hmain := Submission.LensLoop.two_mul_le_of_isGeodesicAt_loop_speed (cov := cov) hmet htor
    (c := 1) (a := (-1 : ℝ)) (b := T + 1) (T := T) (r := r)
    one_pos (by linarith) hT (by linarith)
    (hsm.mono (by intro t _; exact Set.mem_univ t))
    (fun t _ => hgeo t)
    (fun t _ => by
      have h1 := hsp t
      intro h0; rw [h0, norm_zero] at h1; norm_num at h1)
    (hsp 0)
    (hsp T)
    (hγT.trans hγ0.symm)
    (by rw [show (T - 0 : ℝ) = T from by ring]; exact hγT.trans hγ0.symm)
    hvelne hbase
  linarith

/-! ## The Klingenberg–Xu step: the two alternatives

Two unit rays from `p` meeting again at time `m` either arrive at the meeting point with **opposite
velocities** — then they are the two halves of one whole geodesic and the first ray is a geodesic loop
at `p` of length `2m` (`isGeodesicLoopAt_of_velocity_eq_neg`) — or the corner there is genuine, and
the broken loop can be **shortened** (`exists_shorter_loop_of_velocity_ne_neg`).

Xu's Theorem B (arXiv:1401.5549) is precisely the assertion that the second alternative cannot occur
when the meeting point is the *closest* cut point of `p` and `p` is not conjugate to it; it is the
remaining input of the Klingenberg–Xu step (`Submission.KlingenbergXu.KlingenbergLoopStep`). -/

/-- **The genuine-corner case can be shortened.**  If two unit rays from `p` meet at time `m` and
arrive there with velocities that are *not* opposite, then there is a closed piecewise smooth path at
`p` of length `< 2m`: cut the corner at the meeting point and come back along the other ray. -/
theorem exists_shorter_loop_of_velocity_ne_neg (hmet : IsMetricCompatible cov)
    (htor : cov.torsion = 0) [PathConnectedSpace M] [RegularSpace M]
    (p : M) {ξ η : TangentSpace I p} (hξ : ‖ξ‖ = 1) (hη : ‖η‖ = 1) {m : ℝ} (hm : 0 < m)
    (hmeet : GExp (cov := cov) hmet p (m • ξ) = GExp (cov := cov) hmet p (m • η))
    (hw : curveVelocity (I := I) (fun t : ℝ => GExp (cov := cov) hmet p (t • ξ)) m
      ≠ -curveVelocity (I := I) (fun t : ℝ => GExp (cov := cov) hmet p (t • η)) m) :
    ∃ P : Submission.Distance.PwPath I p p, P.length < 2 * m := by
  obtain ⟨ρ, hρpos, hInjAll⟩ := Submission.UniformInj.exists_pos_injAllAtLeast (cov := cov) hmet
  set ε : ℝ := min (m / 2) (ρ / 2) with hεdef
  have hεpos : 0 < ε := lt_min (by linarith) (by linarith)
  have hεm : ε < m := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hερ : ε < ρ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hstrict := edist_feet_lt_of_velocity_ne_neg (cov := cov) hmet htor hInjAll p hξ hη hm hmeet
    hw hεpos hεm hερ
  exact Submission.Shorten.exists_shorter_loop_of_lt (cov := cov) hmet htor p hξ hη hm hεpos hεm
    hstrict

/-- **The Klingenberg–Xu step, up to Xu's theorem B.**  Two unit rays from `p` meeting again at time
`m` either form a `GExp`-ray that is a geodesic loop at `p` of length `2m`, or the broken loop can be
shortened.  The first alternative is unconditional (and needs neither minimisation nor curvature);
ruling out the second is exactly Xu's Theorem B. -/
theorem exists_geodesicLoop_or_shorter_loop (hmet : IsMetricCompatible cov)
    (htor : cov.torsion = 0) [PathConnectedSpace M] [RegularSpace M]
    (p : M) {ξ η : TangentSpace I p} (hξ : ‖ξ‖ = 1) (hη : ‖η‖ = 1) {m : ℝ} (hm : 0 < m)
    (hmeet : GExp (cov := cov) hmet p (m • ξ) = GExp (cov := cov) hmet p (m • η)) :
    IsGeodesicLoopAt (I := I) (cov := cov) hmet p (2 * m)
        (fun s : ℝ => GExp (cov := cov) hmet p (s • ξ)) ∨
      ∃ P : Submission.Distance.PwPath I p p, P.length < 2 * m := by
  by_cases hw : curveVelocity (I := I) (fun t : ℝ => GExp (cov := cov) hmet p (t • ξ)) m
      = -curveVelocity (I := I) (fun t : ℝ => GExp (cov := cov) hmet p (t • η)) m
  · exact Or.inl (isGeodesicLoopAt_of_velocity_eq_neg (cov := cov) hmet hξ hη hm hmeet hw)
  · exact Or.inr (exists_shorter_loop_of_velocity_ne_neg (cov := cov) hmet htor p hξ hη hm hmeet hw)

end

end Submission.GeodesicLoop
