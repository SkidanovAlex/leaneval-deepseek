import Submission.GExpJoint
import Submission.GExpRayZero
import Submission.GExpRayIdent
import Submission.GExpVelocity
import Submission.HopfRinow2
import Submission.Length
import Submission.GeodesicSpeed
import Submission.InjRadius

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The closed geodesic loop of an extremal lens

If `u ≠ 0` and `GExp p u = GExp p (-u)`, then the `GExp`-ray through `p` in the direction `u` closes
up at the point `q = GExp p u`: the ray meets `q` at the parameters `1` and `-1`.  Reading the ray
between these two parameters gives a **closed geodesic loop through `q` of length `2‖u‖`**, and the
classical argument then shows that the injectivity radius of the exponential map at `q` is at most
`‖u‖`: the two halves of the loop give two tangent vectors at `q` of norm `‖u‖` with the same
image, and they are distinct exactly when the loop does not "reverse" at `q`.

## Contents

* `contMDiffOn_GExp_smul_nhds_zero`, `contMDiffOn_GExp_smul_Ioo_symm`: the `GExp`-ray is `C^∞`
  on a symmetric neighbourhood of `0` (and hence on every symmetric interval);
* `curveSpeed_GExp_smul_ne`, `norm_curveVelocity_GExp_smul_ne`: the speed of a `GExp`-ray at a
  non-zero parameter is `‖v‖`;
* `two_mul_le_of_isGeodesicAt_loop_speed`: a geodesic loop of length `T` and (constant) speed `c`
  bounds the injectivity radius at its base point by `c T / 2` (only the speeds at the two endpoints
  are needed);
* `curveVelocity_GExp_ne_neg_of_lens`: **the extremal lens does not reverse at the lens point**;
* `two_mul_norm_le_of_GExp_eq_GExp_neg`: **the injectivity radius at the far end of an extremal
  lens is at most the lens length**: `InjAtLeast hmet (GExp p u) r ⟹ r ≤ ‖u‖`.

The last statement is the `u ↔ -u` case of Klingenberg's lemma.
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
open Submission.HopfRinow
open Submission.GExpRay2
open Submission.GExpTwoSided
open Submission.GExpRayIdent
open Submission.GExpFlow
open Submission.ChartConnection
open Submission.GeodesicExtend
open Submission.GExpJoint
open Submission.UniformInj
open Submission.GExpVelocity
open Submission.GExpRayZero
open Submission.Length
open Submission.GeodesicSpeed
open Submission.InjRadius

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

namespace Submission.LensLoop

noncomputable section

variable [I.Boundaryless] [Nontrivial E] [CompactSpace M]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]

theorem contMDiffOn_GExp_smul_nhds_zero (hmet : IsMetricCompatible cov) (x : M)
    {v : TangentSpace I x} (hv : v ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ContMDiffOn 𝓘(ℝ) I ∞ (fun s : ℝ => GExp (cov := cov) hmet x (s • v))
      (Ioo (-ε) ε) := by
  classical
  have hxsrc : x ∈ (chartAt H x).source := mem_chart_source H x
  obtain ⟨D, _⟩ := exists_chartFlowData (cov := cov) (I := I) (z₀ := x) (Z := ({x} : Set M))
    isCompact_singleton (fun q hq => by
      rw [Set.mem_singleton_iff] at hq; subst hq; exact hxsrc)
  have hZsrc : ({x} : Set M) ⊆ (chartAt H x).source := fun q hq => by
    rw [Set.mem_singleton_iff] at hq; subst hq; exact hxsrc
  set u₀ : E := (trivializationAt E (TangentSpace I) x).continuousLinearMapAt ℝ x v with hu₀def
  have hxext : x ∈ (extChartAt I x).source := mem_extChartAt_source x
  have hframe : frameVector (I := I) x x u₀ = v := frameVector_clm (I := I) hxext v
  set η : ℝ := 1 / (2 * flowScale D) with hηdef
  have hηpos : 0 < η := by
    rw [hηdef]; exact div_pos one_pos (by linarith [flowScale_pos (cov := cov) D])
  have hjoint := contMDiffOn_GExp_frameVector (cov := cov) hmet D hZsrc (η := η) le_rfl
  have hφ : ContMDiffOn 𝓘(ℝ, E) (I.prod 𝓘(ℝ, E)) ∞ (fun u : E => (x, u))
      (Metric.closedBall (0 : E) η) :=
    (contMDiff_const (I := 𝓘(ℝ, E)) (I' := I) (c := x)).contMDiffOn.prodMk
      (contMDiff_id (I := 𝓘(ℝ, E))).contMDiffOn
  have hslice : ContMDiffOn 𝓘(ℝ, E) I ∞
      (fun u : E => GExp (cov := cov) hmet x (frameVector (I := I) x x u))
      (Metric.closedBall (0 : E) η) := by
    refine hjoint.comp hφ (fun u hu => ?_)
    exact ⟨Set.mem_singleton x, hu⟩
  set ε : ℝ := η / (‖u₀‖ + 1) with hεdef
  have hεpos : 0 < ε := by
    rw [hεdef]; exact div_pos hηpos (by linarith [norm_nonneg u₀])
  refine ⟨ε, hεpos, ?_⟩
  have hlin : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (fun s : ℝ => s • u₀) (Ioo (-ε) ε) :=
    ((ContinuousLinearMap.contMDiff (𝕜 := ℝ) (n := ∞)
      (ContinuousLinearMap.toSpanSingleton ℝ u₀)).contMDiffOn (s := Ioo (-ε) ε)).congr
      (fun s _ => by simp)
  have hcomp := hslice.comp hlin (fun s hs => ?_)
  · refine hcomp.congr (fun s hs => ?_)
    show GExp (cov := cov) hmet x (s • v)
        = GExp (cov := cov) hmet x (frameVector (I := I) x x (s • u₀))
    rw [frameVector_smul, hframe]
  · rw [Set.mem_Ioo] at hs
    simp only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right]
    have hsa : |s| < ε := abs_lt.mpr hs
    have hu₀nn : 0 ≤ ‖u₀‖ := norm_nonneg _
    rw [norm_smul, Real.norm_eq_abs]
    have h1 : |s| * ‖u₀‖ ≤ ε * ‖u₀‖ := mul_le_mul_of_nonneg_right hsa.le hu₀nn
    have h2 : ε * ‖u₀‖ ≤ η := by
      rw [hεdef, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith [hu₀nn, hηpos]
    linarith

/-- The ray of `GExp` is `C^∞` on every symmetric interval around `0`. -/
theorem contMDiffOn_GExp_smul_Ioo_symm (hmet : IsMetricCompatible cov) (x : M)
    {v : TangentSpace I x} (hv : v ≠ 0) (r : ℝ) :
    ContMDiffOn 𝓘(ℝ) I ∞ (fun s : ℝ => GExp (cov := cov) hmet x (s • v)) (Ioo (-r) r) := by
  classical
  rcases le_or_gt r 0 with hr | hr
  · rw [Ioo_eq_empty (by linarith : ¬ (-r) < r)]
    exact contMDiffOn_empty
  · obtain ⟨ε, hεpos, hε⟩ := contMDiffOn_GExp_smul_nhds_zero (cov := cov) hmet x hv
    set δ : ℝ := min ε r with hδdef
    have hδpos : 0 < δ := lt_min hεpos hr
    have hδε : δ ≤ ε := min_le_left _ _
    have hδr : δ ≤ r := min_le_right _ _
    have hmid : ContMDiffOn 𝓘(ℝ) I ∞ (fun s : ℝ => GExp (cov := cov) hmet x (s • v))
        (Ioo (-δ) δ) :=
      hε.mono (Ioo_subset_Ioo (neg_le_neg hδε) hδε)
    have hnv : -v ≠ 0 := neg_ne_zero.mpr hv
    have h1 : ContMDiffOn 𝓘(ℝ) I ∞ (fun s : ℝ => GExp (cov := cov) hmet x (s • v)) (Ioo 0 r) :=
      contMDiffOn_GExp_smul_Ioo (cov := cov) hmet x hv r
    have h3 : ContMDiffOn 𝓘(ℝ) I ∞ (fun s : ℝ => GExp (cov := cov) hmet x (s • v))
        (Ioo (-r) 0) := by
      have hbase := contMDiffOn_GExp_smul_Ioo (cov := cov) hmet x (v := -v) hnv r
      have hnegmap : ContMDiffOn 𝓘(ℝ) 𝓘(ℝ) ∞ (fun s : ℝ => -s) (Ioo (-r) 0) :=
        (contMDiff_id (I := 𝓘(ℝ))).neg.contMDiffOn
      have hcomp := hbase.comp hnegmap (fun s hs => by
        show -s ∈ Ioo (0 : ℝ) r
        rw [Set.mem_Ioo] at hs ⊢
        exact ⟨by linarith [hs.2], by linarith [hs.1]⟩)
      refine hcomp.congr (fun s hs => ?_)
      show GExp (cov := cov) hmet x (s • v) = GExp (cov := cov) hmet x ((-s) • (-v))
      congr 1
      rw [neg_smul, smul_neg, neg_neg]
    have h23 : ContMDiffOn 𝓘(ℝ) I ∞ (fun s : ℝ => GExp (cov := cov) hmet x (s • v))
        (Ioo (-δ) δ ∪ Ioo (-r) 0) :=
      ContMDiffOn.union_of_isOpen (s := Ioo (-δ) δ) (t := Ioo (-r) 0) hmid h3
        isOpen_Ioo isOpen_Ioo
    have h123 : ContMDiffOn 𝓘(ℝ) I ∞ (fun s : ℝ => GExp (cov := cov) hmet x (s • v))
        (Ioo (0 : ℝ) r ∪ (Ioo (-δ) δ ∪ Ioo (-r) 0)) :=
      ContMDiffOn.union_of_isOpen (s := Ioo (0 : ℝ) r)
        (t := Ioo (-δ) δ ∪ Ioo (-r) 0) h1 h23 isOpen_Ioo (isOpen_Ioo.union isOpen_Ioo)
    have hUnion : Ioo (-r) r = Ioo (0 : ℝ) r ∪ (Ioo (-δ) δ ∪ Ioo (-r) 0) := by
      ext s
      constructor
      · intro hs
        rw [Set.mem_Ioo] at hs
        rcases lt_trichotomy s 0 with h | h | h
        · exact Or.inr (Or.inr ⟨hs.1, h⟩)
        · exact Or.inr (Or.inl ⟨by linarith, by linarith⟩)
        · exact Or.inl ⟨h, hs.2⟩
      · intro hs
        rw [Set.mem_Ioo]
        rcases hs with hs | hs
        · rw [Set.mem_Ioo] at hs
          exact ⟨by linarith [hs.1], hs.2⟩
        · rcases hs with hs | hs
          · rw [Set.mem_Ioo] at hs
            exact ⟨by linarith [hs.1], by linarith [hs.2, hδr]⟩
          · rw [Set.mem_Ioo] at hs
            exact ⟨hs.1, by linarith [hs.2]⟩
    rw [hUnion]
    exact h123

/-- The norm of the negative of a tangent vector. -/
lemma norm_neg_tangent' {x : M} (w : TangentSpace I x) : ‖-w‖ = ‖w‖ := by
  have h : (-1 : ℝ) • w = -w := by simp
  rw [← h]
  simp

/-- The norm of a tangent vector multiplied by `-1`. -/
lemma norm_neg_one_smul' {x : M} (w : TangentSpace I x) : ‖(-1 : ℝ) • w‖ = ‖w‖ := by
  have h : (-1 : ℝ) • w = -w := by simp
  rw [h, norm_neg_tangent']

/-- Multiplication of a tangent vector by `-1`. -/
lemma neg_one_smul' {x : M} (w : TangentSpace I x) : (-1 : ℝ) • w = -w := by simp

/-- Transporting a tangent vector along an equality of base points does not change it. -/
lemma cast_tangent_eq' {x y : M} (h : x = y) (w : TangentSpace I x) : (h ▸ w) = w := by
  cases h; rfl

/-- Norm is preserved by transporting a tangent vector along an equality of base points. -/
lemma norm_cast_tangent' {x y : M} (h : x = y) (w : TangentSpace I x) :
    ‖(h ▸ w)‖ = ‖w‖ := by
  cases h; rfl

/-- Transporting a tangent vector along an equality of base points, packaged as a `def` so that the
elaboration of the transport is fixed once and for all. -/
noncomputable def tantransport {x y : M} (h : x = y) (w : TangentSpace I x) :
    TangentSpace I y :=
  h ▸ w

/-- Transporting a tangent vector along an equality of base points does not change it. -/
lemma tantransport_eq {x y : M} (h : x = y) (w : TangentSpace I x) :
    tantransport h w = w := by
  rw [tantransport]; cases h; rfl

/-- Transporting a tangent vector along an equality of base points preserves its norm. -/
lemma norm_tantransport {x y : M} (h : x = y) (w : TangentSpace I x) :
    ‖tantransport h w‖ = ‖w‖ := by
  rw [tantransport]; cases h; rfl


/-! ## Speed of the rays at non-zero parameters -/

/-- Affine reparametrisation of the speed, for any nonzero factor. -/
lemma curveSpeed_comp_mul_add_abs {γ : ℝ → M} {c d t : ℝ} (hc : c ≠ 0)
    (hd : MDifferentiableAt 𝓘(ℝ) I γ (c * t + d)) :
    curveSpeed (I := I) (fun s : ℝ => γ (c * s + d)) t
      = |c| * curveSpeed (I := I) γ (c * t + d) := by
  rw [curveSpeed_eq_norm, curveSpeed_eq_norm, curveVelocity_comp_mul_add (I := I) hd, norm_smul,
    Real.norm_eq_abs]

/-- **The speed of a `GExp` ray at a non-zero parameter.** -/
theorem curveSpeed_GExp_smul_ne (hmet : IsMetricCompatible cov) (x : M)
    {v : TangentSpace I x} (hv : v ≠ 0) {s : ℝ} (hs : s ≠ 0) :
    curveSpeed (I := I) (fun s : ℝ => GExp (cov := cov) hmet x (s • v)) s = ‖v‖ := by
  rcases lt_or_gt_of_ne hs with h | h
  · have hnv : -v ≠ 0 := neg_ne_zero.mpr hv
    have hpos : (0 : ℝ) < (-1) * s + 0 := by rw [neg_one_mul, add_zero]; linarith
    have hmd : MDifferentiableAt 𝓘(ℝ) I (fun r : ℝ => GExp (cov := cov) hmet x (r • (-v)))
        ((-1) * s + 0) :=
      mdifferentiableAt_GExp_smul (cov := cov) hmet x hnv hpos
    have h1 : curveSpeed (I := I) (fun r : ℝ => GExp (cov := cov) hmet x (r • v)) s
        = curveSpeed (I := I) (fun r : ℝ => GExp (cov := cov) hmet x (((-1) * r + 0) • (-v)))
            s :=
      curveSpeed_congr_of_eventuallyEq (I := I) (Filter.Eventually.of_forall (fun r => by
        show GExp (cov := cov) hmet x (r • v) = GExp (cov := cov) hmet x (((-1) * r + 0) • (-v))
        congr 1
        rw [show ((-1 : ℝ) * r + 0) = -r from by ring]
        rw [neg_smul, smul_neg, neg_neg]))
    rw [h1, curveSpeed_comp_mul_add_abs (c := (-1 : ℝ)) (d := 0) (t := s) (by norm_num) hmd]
    rw [show |(-1 : ℝ)| = 1 from by norm_num, one_mul]
    rw [curveSpeed_eq_norm, norm_curveVelocity_GExp_smul (cov := cov) hmet x hnv hpos]
    exact norm_neg_tangent' v
  · rw [curveSpeed_eq_norm, norm_curveVelocity_GExp_smul (cov := cov) hmet x hv h]

/-- **Norm of the ray velocity at a non-zero parameter.** -/
theorem norm_curveVelocity_GExp_smul_ne (hmet : IsMetricCompatible cov) (x : M)
    {v : TangentSpace I x} (hv : v ≠ 0) {s : ℝ} (hs : s ≠ 0) :
    ‖curveVelocity (I := I) (fun s : ℝ => GExp (cov := cov) hmet x (s • v)) s‖ = ‖v‖ :=
  (curveSpeed_eq_norm (I := I) (fun s : ℝ => GExp (cov := cov) hmet x (s • v)) s).symm.trans
    (curveSpeed_GExp_smul_ne (cov := cov) hmet x hv hs)


lemma GExp_cast_tangent' (hmet : IsMetricCompatible cov) {x y : M} (h : x = y)
    (w : TangentSpace I x) : GExp (cov := cov) hmet y (h ▸ w) = GExp (cov := cov) hmet x w := by
  cases h; rfl

/-- **A geodesic loop bounds the injectivity radius from above** (constant-speed form, with the
speed given only at the two endpoints of the loop). -/
theorem two_mul_le_of_isGeodesicAt_loop_speed
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {a b T r c : ℝ} (hc : 0 < c) (ha : a < 0) (hT : 0 < T) (hTb : T < b)
    {γ : ℝ → M} (hsm : ContMDiffOn 𝓘(ℝ) I ∞ γ (Ioo a b))
    (hgeo : ∀ t ∈ Ioo a b, IsGeodesicAt cov γ t)
    (hne : ∀ t ∈ Ioo a b, curveVelocity (I := I) γ t ≠ 0)
    (hspeed0 : ‖curveVelocity (I := I) γ 0‖ = c)
    (hspeedT : ‖curveVelocity (I := I) γ T‖ = c)
    (hloop : γ T = γ 0) (hbase : γ (T - 0) = γ 0)
    (hvelne : (T / 2) • curveVelocity (I := I) γ 0
      ≠ (T / 2) • curveVelocity (I := I) (fun s : ℝ => γ (T - s)) 0)
    (hinj : InjAtLeast hmet (γ 0) r) : 2 * r ≤ c * T := by
  classical
  by_contra hcon
  rw [not_le] at hcon
  have hhalf : T / 2 * c < r := by nlinarith [hc, hT]
  have hbpos : 0 < b := lt_trans hT hTb
  have h0mem : (0 : ℝ) ∈ Ioo a b := ⟨ha, hbpos⟩
  have hTmem : T ∈ Ioo a b := ⟨lt_trans ha hT, hTb⟩
  have hb0 : T - b < 0 := by linarith
  have h0a : 0 < T - a := by linarith
  -- the reversed curve
  have hrev_sm : ContMDiffOn 𝓘(ℝ) I ∞ (fun s : ℝ => γ (T - s)) (Ioo (T - b) (T - a)) := by
    have hneg : ContMDiffOn 𝓘(ℝ) 𝓘(ℝ) ∞ (fun s : ℝ => T - s) (Ioo (T - b) (T - a)) := by
      have h : ContMDiffOn 𝓘(ℝ) 𝓘(ℝ) ∞ (fun s : ℝ => T + (-1 : ℝ) * s) (Ioo (T - b) (T - a)) :=
        (contMDiff_const.add (contMDiff_const.mul contMDiff_id)).contMDiffOn
      have hfun : (fun s : ℝ => T + (-1 : ℝ) * s) = fun s : ℝ => T - s := by
        funext s; ring
      rwa [hfun] at h
    exact hsm.comp hneg (fun s hs => ⟨by linarith [hs.2], by linarith [hs.1]⟩)
  have hmem' : ∀ t ∈ Ioo (T - b) (T - a), (-1 : ℝ) * t + T ∈ Ioo a b := by
    intro t ht
    exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hrev_geo : ∀ t ∈ Ioo (T - b) (T - a), IsGeodesicAt cov (fun s : ℝ => γ (T - s)) t := by
    intro t ht
    have h := isGeodesicAt_comp_affine (cov := cov) (σ := γ) (c := a) (d := b) (a := -1) (b := T)
      (by norm_num) hsm hgeo (by simpa using hmem' t ht)
    simpa [sub_eq_add_neg, add_comm, mul_comm] using h
  have hrev_md : ∀ t ∈ Ioo (T - b) (T - a), MDifferentiableAt 𝓘(ℝ) I γ (T - t) := by
    intro t ht
    exact (hsm.contMDiffAt (isOpen_Ioo.mem_nhds (show T - t ∈ Ioo a b from
      ⟨by linarith [ht.2], by linarith [ht.1]⟩))).mdifferentiableAt (by simp)
  have hrev_ne : ∀ t ∈ Ioo (T - b) (T - a),
      curveVelocity (I := I) (fun s : ℝ => γ (T - s)) t ≠ 0 := by
    intro t ht hzero
    have h2 := curveVelocity_comp_sub_neg_at (I := I) (γ := γ) (t := T) (r := t) (hrev_md t ht)
    rw [h2] at hzero
    exact hne (T - t) ⟨by linarith [ht.2], by linarith [ht.1]⟩ (neg_eq_zero.mp hzero)
  have hmdT : MDifferentiableAt 𝓘(ℝ) I γ T :=
    (hsm.contMDiffAt (isOpen_Ioo.mem_nhds hTmem)).mdifferentiableAt (by simp)
  have hrev_speed0 : curveSpeed (I := I) (fun s : ℝ => γ (T - s)) 0 = c := by
    have h1 : curveSpeed (I := I) (fun s : ℝ => γ (T - s)) 0
        = curveSpeed (I := I) (fun s : ℝ => γ ((-1) * s + T)) 0 :=
      curveSpeed_congr_of_eventuallyEq (I := I) (Filter.Eventually.of_forall (fun s => by
        show γ (T - s) = γ ((-1) * s + T)
        rw [show (-1 : ℝ) * s + T = T - s from by ring]))
    rw [h1, curveSpeed_comp_mul_add_abs (c := (-1 : ℝ)) (d := T) (t := 0) (by norm_num)
      (by rw [show (-1 : ℝ) * 0 + T = T from by ring]; exact hmdT)]
    rw [show |(-1 : ℝ)| = 1 from by norm_num, one_mul,
      show (-1 : ℝ) * 0 + T = T from by ring]
    exact (curveSpeed_eq_norm (I := I) γ T).trans hspeedT
  have hrev_norm0 : ‖curveVelocity (I := I) (fun s : ℝ => γ (T - s)) 0‖ = c :=
    (curveSpeed_eq_norm (I := I) (fun s : ℝ => γ (T - s)) 0).symm.trans hrev_speed0
  have hVne : curveVelocity (I := I) (fun s : ℝ => γ (T - s)) 0 ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero] at hrev_norm0
    linarith
  -- the two witness vectors at the base point
  have hT2 : T / 2 ∈ Icc (0 : ℝ) T := ⟨by linarith, by linarith⟩
  -- the ray identity for `γ`
  have hγ : ∀ t ∈ Icc (0 : ℝ) T,
      γ t = GExp (cov := cov) hmet (γ 0) (t • curveVelocity (I := I) γ 0) :=
    eqOn_Icc_GExp_of_isGeodesicAt (cov := cov) (p := γ 0) hmet (hne 0 h0mem)
      ha hT.le hTb hsm hgeo hne rfl rfl
  -- the ray identity for the reversed curve, based at `γ 0`
  have hrev : ∀ t ∈ Icc (0 : ℝ) T,
      γ (T - t) = GExp (cov := cov) hmet (γ 0)
        (t • curveVelocity (I := I) (fun s : ℝ => γ (T - s)) 0) := by
    have h := eqOn_Icc_GExp_of_isGeodesicAt (cov := cov) (p := γ 0) hmet
      (V := curveVelocity (I := I) (fun s : ℝ => γ (T - s)) 0) hVne hb0 hT.le
      (by linarith : T < T - a) hrev_sm hrev_geo hrev_ne
      (by show γ (T - 0) = γ 0; exact hbase) rfl
    intro t ht
    exact h t ht
  have hGu : GExp (cov := cov) hmet (γ 0) ((T / 2) • curveVelocity (I := I) γ 0)
      = γ (T / 2) := (hγ (T / 2) hT2).symm
  have hGv : GExp (cov := cov) hmet (γ 0)
      (tantransport hbase ((T / 2) • curveVelocity (I := I) (fun s : ℝ => γ (T - s)) 0))
      = γ (T / 2) := by
    rw [tantransport_eq hbase]
    have h := hrev (T / 2) hT2
    rw [show T - T / 2 = T / 2 from by ring] at h
    exact h.symm
  have hu : ‖(T / 2) • curveVelocity (I := I) γ 0‖ = T / 2 * c := by
    rw [norm_smul, hspeed0, Real.norm_of_nonneg (by linarith : (0:ℝ) ≤ T / 2)]
  have hw : ‖(T / 2) • curveVelocity (I := I) (fun s : ℝ => γ (T - s)) 0‖ = T / 2 * c := by
    rw [norm_smul, hrev_norm0, Real.norm_of_nonneg (by linarith : (0:ℝ) ≤ T / 2)]
  have hW : ‖tantransport hbase ((T / 2) • curveVelocity (I := I) (fun s : ℝ => γ (T - s)) 0)‖
      = T / 2 * c :=
    (norm_tantransport hbase _).trans hw
  have huv : (T / 2) • curveVelocity (I := I) γ 0
      ≠ tantransport hbase ((T / 2) • curveVelocity (I := I) (fun s : ℝ => γ (T - s)) 0) := by
    intro h
    exact hvelne (h.trans (tantransport_eq hbase _))
  exact huv (hinj ((T / 2) • curveVelocity (I := I) γ 0)
    (tantransport hbase ((T / 2) • curveVelocity (I := I) (fun s : ℝ => γ (T - s)) 0))
    (by rw [hu]; exact hhalf) (by rw [hW]; exact hhalf) (by rw [hGu, hGv]))

/-- **The extremal lens does not reverse at the lens point.**  If `GExp p u = GExp p (-u)` for
`u ≠ 0`, then the ray velocity at parameter `-1` is not the negative of the ray velocity at
parameter `1`.  Equivalently, the closed geodesic loop of the extremal lens is not an "out and back"
path. -/
theorem curveVelocity_GExp_ne_neg_of_lens (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {p : M} {u : TangentSpace I p} (hu : u ≠ 0)
    (heq : GExp (cov := cov) hmet p u = GExp (cov := cov) hmet p (-u)) :
    curveVelocity (I := I) (fun s : ℝ => GExp (cov := cov) hmet p (s • u)) (-1)
      ≠ -curveVelocity (I := I) (fun s : ℝ => GExp (cov := cov) hmet p (s • u)) 1 := by
  classical
  intro hcon
  set β : ℝ → M := fun s : ℝ => GExp (cov := cov) hmet p (s • u) with hβdef
  set η : ℝ → M := fun s : ℝ => β (0 - s) with hηdef
  have hsmβ : ContMDiffOn 𝓘(ℝ) I ∞ β (Ioo (-2 : ℝ) 2) := by
    rw [hβdef]; exact contMDiffOn_GExp_smul_Ioo_symm (cov := cov) hmet p hu 2
  have hgeoβ : ∀ t ∈ Ioo (-2 : ℝ) 2, IsGeodesicAt cov β t := by
    intro t ht; rw [hβdef]; exact isGeodesicAt_GExp_smul_all (cov := cov) hmet p hu t
  have hneβ : ∀ t ∈ Ioo (-2 : ℝ) 2, curveVelocity (I := I) β t ≠ 0 := by
    intro t ht hzero
    rcases eq_or_ne t 0 with h | h
    · subst h
      rw [hβdef] at hzero
      rw [curveVelocity_GExp_smul_zero (cov := cov) hmet p hu] at hzero
      exact hu hzero
    · have hnorm := norm_curveVelocity_GExp_smul_ne (cov := cov) hmet p hu h
      rw [hβdef] at hzero
      rw [hzero] at hnorm
      simp at hnorm
      exact (norm_ne_zero_iff.mpr hu) hnorm.symm
  have hsmη : ContMDiffOn 𝓘(ℝ) I ∞ η (Ioo (-2 : ℝ) 2) := by
    have hneg : ContMDiffOn 𝓘(ℝ) 𝓘(ℝ) ∞ (fun s : ℝ => 0 - s) (Ioo (-2 : ℝ) 2) := by
      have h : ContMDiffOn 𝓘(ℝ) 𝓘(ℝ) ∞ (fun s : ℝ => 0 + (-1 : ℝ) * s) (Ioo (-2 : ℝ) 2) :=
        (contMDiff_const.add (contMDiff_const.mul contMDiff_id)).contMDiffOn
      have hfun : (fun s : ℝ => 0 + (-1 : ℝ) * s) = fun s : ℝ => 0 - s := by
        funext s; ring
      rwa [hfun] at h
    exact hsmβ.comp hneg (fun s hs => ⟨by linarith [hs.2], by linarith [hs.1]⟩)
  have hgeoη : ∀ t ∈ Ioo (-2 : ℝ) 2, IsGeodesicAt cov η t := by
    intro t ht
    have hmem : (0 : ℝ) - t ∈ Ioo (-2 : ℝ) 2 := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    exact isGeodesicAt_comp_sub_neg_at (cov := cov) (γ := β) (c := (-2 : ℝ)) (d := 2) (t := 0)
      hsmβ hgeoβ (r := t) hmem
  have hneη : ∀ t ∈ Ioo (-2 : ℝ) 2, curveVelocity (I := I) η t ≠ 0 := by
    intro t ht hzero
    have hmd : MDifferentiableAt 𝓘(ℝ) I β (0 - t) :=
      (hsmβ.contMDiffAt (isOpen_Ioo.mem_nhds (show 0 - t ∈ Ioo (-2 : ℝ) 2 from
        ⟨by linarith [ht.2], by linarith [ht.1]⟩))).mdifferentiableAt (by simp)
    have h2 := curveVelocity_comp_sub_neg_at (I := I) (γ := β) (t := 0) (r := t) hmd
    rw [hηdef] at hzero
    rw [h2] at hzero
    exact hneβ (0 - t) ⟨by linarith [ht.2], by linarith [ht.1]⟩ (neg_eq_zero.mp hzero)
  have hpt : β (-1) = η (-1) := by
    rw [hηdef, hβdef]
    show GExp (cov := cov) hmet p ((-1 : ℝ) • u)
      = GExp (cov := cov) hmet p ((0 - -1) • u)
    rw [show (0 : ℝ) - -1 = 1 from by norm_num, one_smul,
      show (-1 : ℝ) • u = -u from by simp]
    exact heq.symm
  have hvel : curveVelocity (I := I) β (-1) = curveVelocity (I := I) η (-1) := by
    have hmd : MDifferentiableAt 𝓘(ℝ) I β (0 - -1) := by
      rw [show (0 : ℝ) - -1 = 1 from by norm_num]
      exact (hsmβ.contMDiffAt (isOpen_Ioo.mem_nhds (by norm_num : (1:ℝ) ∈ Ioo (-2) 2))).mdifferentiableAt
        (by simp)
    have h2 := curveVelocity_comp_sub_neg_at (I := I) (γ := β) (t := 0) (r := (-1)) hmd
    have h3 : curveVelocity (I := I) β (0 - -1) = curveVelocity (I := I) β 1 := by
      rw [show (0 : ℝ) - -1 = 1 from by norm_num]
    rw [hηdef, h2, h3]
    exact hcon
  have hEqOn : EqOn β η (Ioo (-1 : ℝ) 2) :=
    eqOn_Ioo_right_of_isGeodesicAt_of_eq hsmβ hsmη hgeoβ hgeoη hneβ hneη
      (by norm_num : (-1 : ℝ) ∈ Ioo (-2) 2) hpt hvel
  have hev : β =ᶠ[𝓝 (0 : ℝ)] η := by
    filter_upwards [isOpen_Ioo.mem_nhds (by norm_num : (0 : ℝ) ∈ Ioo (-1) 2)] with s hs
    exact hEqOn hs
  have hv0 : curveVelocity (I := I) β 0 = curveVelocity (I := I) η 0 :=
    curveVelocity_congr_of_eventuallyEq (I := I) hev
  have hη0 : curveVelocity (I := I) η 0 = -curveVelocity (I := I) β 0 := by
    have hmd : MDifferentiableAt 𝓘(ℝ) I β (0 - 0) := by
      rw [sub_zero]
      exact (hsmβ.contMDiffAt (isOpen_Ioo.mem_nhds (by norm_num : (0:ℝ) ∈ Ioo (-2) 2))).mdifferentiableAt
        (by simp)
    have h2 := curveVelocity_comp_sub_neg_at (I := I) (γ := β) (t := 0) (r := 0) hmd
    rw [hηdef, h2, sub_zero]
  have hzero : curveVelocity (I := I) β 0 = 0 := by
    have h2 : curveVelocity (I := I) β 0 = -curveVelocity (I := I) β 0 := hv0.trans hη0
    have h3 : (2 : ℝ) • curveVelocity (I := I) β 0 = 0 := by
      rw [two_smul]
      exact eq_neg_iff_add_eq_zero.mp h2
    exact (smul_eq_zero.mp h3).resolve_left (by norm_num)
  have hu0 : curveVelocity (I := I) β 0 = u := by
    rw [hβdef]; exact curveVelocity_GExp_smul_zero (cov := cov) hmet p hu
  rw [hzero] at hu0
  exact hu hu0.symm

/-- **The injectivity radius at the lens point of an extremal lens is bounded by the lens length.**
If `u ≠ 0` and `GExp p u = GExp p (-u)`, then the exponential map at `q = GExp p u` cannot be
injective on any ball of radius `> ‖u‖`: the extremal lens gives a closed geodesic loop through `q`
of length `2‖u‖`. -/
theorem two_mul_norm_le_of_GExp_eq_GExp_neg (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {p : M} {u : TangentSpace I p} (hu : u ≠ 0)
    (heq : GExp (cov := cov) hmet p u = GExp (cov := cov) hmet p (-u)) {r : ℝ}
    (hinj : InjAtLeast hmet (GExp (cov := cov) hmet p u) r) : r ≤ ‖u‖ := by
  classical
  set ν : ℝ := ‖u‖ with hνdef
  have hνpos : 0 < ν := by rw [hνdef]; exact norm_pos_iff.mpr hu
  set β : ℝ → M := fun s : ℝ => GExp (cov := cov) hmet p (s • u) with hβdef
  set γ : ℝ → M := fun t : ℝ => β ((-1) * t + 1) with hγdef
  -- the ray is smooth, geodesic and non-vanishing on the interval used below
  have hsmβ : ContMDiffOn 𝓘(ℝ) I ∞ β (Ioo (-2 : ℝ) 2) := by
    rw [hβdef]
    exact contMDiffOn_GExp_smul_Ioo_symm (cov := cov) hmet p hu 2
  have hgeoβ : ∀ t ∈ Ioo (-2 : ℝ) 2, IsGeodesicAt cov β t := by
    intro t ht; rw [hβdef]; exact isGeodesicAt_GExp_smul_all (cov := cov) hmet p hu t
  have hneβ : ∀ t ∈ Ioo (-2 : ℝ) 2, curveVelocity (I := I) β t ≠ 0 := by
    intro t ht hzero
    rcases eq_or_ne t 0 with h | h
    · subst h
      rw [hβdef] at hzero
      rw [curveVelocity_GExp_smul_zero (cov := cov) hmet p hu] at hzero
      exact hu hzero
    · have hnn := norm_curveVelocity_GExp_smul_ne (cov := cov) hmet p hu h
      rw [hβdef] at hzero
      rw [hzero] at hnn
      simp at hnn
      exact (norm_ne_zero_iff.mpr hu) hnn.symm
  -- the affine parametrisation of the loop
  have haff : ∀ t ∈ Ioo (-1 : ℝ) 3, (-1) * t + 1 ∈ Ioo (-2 : ℝ) 2 := by
    intro t ht
    exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hsmγ : ContMDiffOn 𝓘(ℝ) I ∞ γ (Ioo (-1 : ℝ) 3) := by
    have hlin : ContMDiffOn 𝓘(ℝ) 𝓘(ℝ) ∞ (fun t : ℝ => (-1) * t + 1) (Ioo (-1 : ℝ) 3) :=
      ((contMDiff_const.mul contMDiff_id).add contMDiff_const).contMDiffOn
    have h := hsmβ.comp hlin haff
    rw [hγdef]; exact h
  have hgeoγ : ∀ t ∈ Ioo (-1 : ℝ) 3, IsGeodesicAt cov γ t := by
    intro t ht
    have h := isGeodesicAt_comp_affine (cov := cov) (σ := β) (c := (-2 : ℝ)) (d := 2)
      (a := (-1 : ℝ)) (b := 1) (by norm_num) hsmβ hgeoβ (r := t) (haff t ht)
    rw [hγdef]; exact h
  have hvelT : ∀ t ∈ Ioo (-1 : ℝ) 3,
      curveVelocity (I := I) γ t = (-1 : ℝ) • curveVelocity (I := I) β ((-1) * t + 1) := by
    intro t ht
    have hmd : MDifferentiableAt 𝓘(ℝ) I β ((-1) * t + 1) :=
      (hsmβ.contMDiffAt (isOpen_Ioo.mem_nhds (haff t ht))).mdifferentiableAt (by simp)
    rw [hγdef]
    exact curveVelocity_comp_mul_add (I := I) (γ := β) (c := (-1 : ℝ)) (d := 1) (t := t) hmd
  have hs0 : (-1 : ℝ) * 0 + 1 ≠ 0 := by norm_num
  have hsT : (-1 : ℝ) * 2 + 1 ≠ 0 := by norm_num
  have hrayNorm0 : ‖curveVelocity (I := I) β ((-1) * 0 + 1)‖ = ν := by
    rw [hβdef]
    rw [norm_curveVelocity_GExp_smul_ne (cov := cov) hmet p hu hs0, hνdef]
  have hrayNormT : ‖curveVelocity (I := I) β ((-1) * 2 + 1)‖ = ν := by
    rw [hβdef]
    rw [norm_curveVelocity_GExp_smul_ne (cov := cov) hmet p hu hsT, hνdef]
  have hspeed0 : ‖curveVelocity (I := I) γ 0‖ = ν := by
    rw [hvelT 0 ⟨by norm_num, by norm_num⟩, norm_neg_one_smul', hrayNorm0]
  have hspeedT : ‖curveVelocity (I := I) γ 2‖ = ν := by
    rw [hvelT 2 ⟨by norm_num, by norm_num⟩, norm_neg_one_smul', hrayNormT]
  have hneγ : ∀ t ∈ Ioo (-1 : ℝ) 3, curveVelocity (I := I) γ t ≠ 0 := by
    intro t ht hzero
    rw [hvelT t ht] at hzero
    rcases eq_or_ne ((-1) * t + 1) 0 with hs | hs
    · have hb0 : curveVelocity (I := I) β 0 = u := by
        rw [hβdef]; exact curveVelocity_GExp_smul_zero (cov := cov) hmet p hu
      rw [hs] at hzero
      rw [hb0] at hzero
      exact (smul_ne_zero (by norm_num) hu) hzero
    · have hbne : curveVelocity (I := I) β ((-1) * t + 1) ≠ 0 := by
        intro hb0
        have hnn := norm_curveVelocity_GExp_smul_ne (cov := cov) hmet p hu hs
        rw [hβdef] at hb0
        rw [hb0] at hnn
        simp at hnn
        exact (norm_ne_zero_iff.mpr hu) hnn.symm
      exact (smul_ne_zero (by norm_num) hbne) hzero
  have hγ0 : γ 0 = GExp (cov := cov) hmet p u := by
    rw [hγdef, hβdef]
    show GExp (cov := cov) hmet p (((-1) * 0 + 1) • u) = GExp (cov := cov) hmet p u
    rw [show (-1 : ℝ) * 0 + 1 = 1 from by norm_num, one_smul]
  have hγT : γ 2 = GExp (cov := cov) hmet p u := by
    rw [hγdef, hβdef]
    show GExp (cov := cov) hmet p (((-1) * 2 + 1) • u) = GExp (cov := cov) hmet p u
    rw [show (-1 : ℝ) * 2 + 1 = -1 from by norm_num,
      show (-1 : ℝ) • u = -u from by simp]
    exact heq.symm
  have hloop : γ 2 = γ 0 := hγT.trans hγ0.symm
  have hbase : γ (2 - 0) = γ 0 := by norm_num; exact hloop
  have hinj' : InjAtLeast hmet (γ 0) r := by rw [hγ0]; exact hinj
  -- the loop does not reverse at its base point
  have hvelne : ((2 : ℝ) / 2) • curveVelocity (I := I) γ 0
      ≠ ((2 : ℝ) / 2) • curveVelocity (I := I) (fun s : ℝ => γ (2 - s)) 0 := by
    intro hfail
    have hkey : curveVelocity (I := I) β (-1) ≠ -curveVelocity (I := I) β 1 := by
      rw [hβdef]
      exact curveVelocity_GExp_ne_neg_of_lens hmet htor hu heq
    have hL : -curveVelocity (I := I) β 1
        = ((2 : ℝ) / 2) • curveVelocity (I := I) γ 0 := by
      rw [hγdef]
      rw [show (2 : ℝ) / 2 = 1 from by norm_num, one_smul]
      have hmd : MDifferentiableAt 𝓘(ℝ) I β ((-1) * 0 + 1) :=
        (hsmβ.contMDiffAt (isOpen_Ioo.mem_nhds (by norm_num : ((-1 : ℝ) * 0 + 1) ∈ Ioo (-2) 2))).mdifferentiableAt
          (by simp)
      rw [curveVelocity_comp_mul_add (I := I) (γ := β) (c := (-1 : ℝ)) (d := 1) (t := 0) hmd]
      rw [show (-1 : ℝ) * 0 + 1 = 1 from by norm_num]
      simp
    have hRc : curveVelocity (I := I) β (-1)
        = ((2 : ℝ) / 2) • curveVelocity (I := I) (fun s : ℝ => γ (2 - s)) 0 := by
      rw [show (2 : ℝ) / 2 = 1 from by norm_num, one_smul]
      have hmd : MDifferentiableAt 𝓘(ℝ) I γ 2 :=
        (hsmγ.contMDiffAt (isOpen_Ioo.mem_nhds (by norm_num : (2:ℝ) ∈ Ioo (-1) 3))).mdifferentiableAt
          (by simp)
      have h2 := curveVelocity_comp_sub_neg_at (I := I) (γ := γ) (t := 2) (r := 0)
        (by rw [sub_zero]; exact hmd)
      rw [sub_zero] at h2
      rw [h2, hvelT 2 ⟨by norm_num, by norm_num⟩,
        show (-1 : ℝ) * 2 + 1 = -1 from by norm_num]
      rw [neg_one_smul']
      exact (neg_neg (curveVelocity (I := I) β (-1))).symm
    exact hkey (hL.trans (hfail.trans hRc.symm)).symm
  refine le_of_not_gt (fun hcon => ?_)
  have hres := two_mul_le_of_isGeodesicAt_loop_speed (cov := cov) hmet htor (a := -1) (b := 3)
    (T := 2) (r := r) (c := ν) hνpos (by norm_num) (by norm_num) (by norm_num)
    hsmγ hgeoγ hneγ hspeed0 hspeedT hloop hbase hvelne hinj'
  rw [hνdef] at hcon
  linarith


/-- **Klingenberg's inequality, base form.**  If two *distinct* tangent vectors at `p` have the same
norm and the same image under the exponential map, then the injectivity radius at `p` is at most that
norm: for every `r` larger than the norm the two vectors are distinct points of the ball of radius
`r` with the same image. -/
theorem injAtLeast_le_of_two_of_norm_eq (hmet : IsMetricCompatible cov) {p : M}
    {u v : TangentSpace I p} (huv : u ≠ v) (hnorm : ‖u‖ = ‖v‖)
    (hG : GExp (cov := cov) hmet p u = GExp (cov := cov) hmet p v) {r : ℝ}
    (hinj : InjAtLeast hmet p r) : r ≤ ‖u‖ :=
  le_of_not_gt fun hr =>
    not_injAtLeast_of_two_of_norm_eq (cov := cov) hmet huv hnorm hG hr hinj

/-- **Klingenberg's lemma, extremal case, at the base point.**  If `GExp p u = GExp p (-u)` with
`u ≠ 0`, then the injectivity radius at `p` is at most `‖u‖`: the vectors `u` and `-u` are distinct,
have the same norm and the same image.  Equivalently: the "out and back" closed geodesic loop
through `p` of length `2‖u‖` bounds the injectivity radius at `p` by half of its length. -/
theorem injAtLeast_le_of_GExp_eq_GExp_neg (hmet : IsMetricCompatible cov) {p : M}
    {u : TangentSpace I p} (hu : u ≠ 0)
    (heq : GExp (cov := cov) hmet p u = GExp (cov := cov) hmet p (-u)) {r : ℝ}
    (hinj : InjAtLeast hmet p r) : r ≤ ‖u‖ := by
  have hne : u ≠ -u := by
    intro h
    have h2 : u + u = 0 := eq_neg_iff_add_eq_zero.mp h
    have h3 : (2 : ℝ) • u = 0 := by rw [two_smul, h2]
    exact hu ((smul_eq_zero.mp h3).resolve_left (by norm_num))
  exact injAtLeast_le_of_two_of_norm_eq (cov := cov) hmet hne (norm_neg_tangent' u).symm heq hinj

/-- **The ray is `C^∞` on the positive half-line.** -/
theorem contMDiffOn_GExp_smul_Ioi (hmet : IsMetricCompatible cov) (x : M)
    {v : TangentSpace I x} (hv : v ≠ 0) :
    ContMDiffOn 𝓘(ℝ) I ∞ (fun s : ℝ => GExp (cov := cov) hmet x (s • v)) (Ioi 0) := by
  refine contMDiffOn_of_locally_contMDiffOn (fun s hs => ?_)
  refine ⟨Ioo (s / 2) (s + 1), isOpen_Ioo, ⟨by linarith [Set.mem_Ioi.mp hs], lt_add_one s⟩, ?_⟩
  refine (contMDiffOn_GExp_smul_Ioo (cov := cov) hmet x hv (s + 1)).mono ?_
  intro t ht
  rw [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Ioo] at ht
  rw [Set.mem_Ioo]
  exact ⟨by linarith [ht.1], ht.2.2⟩

/-- **The ray is `C^∞` on the negative half-line.** -/
theorem contMDiffOn_GExp_smul_Iio (hmet : IsMetricCompatible cov) (x : M)
    {v : TangentSpace I x} (hv : v ≠ 0) :
    ContMDiffOn 𝓘(ℝ) I ∞ (fun s : ℝ => GExp (cov := cov) hmet x (s • v)) (Iio 0) := by
  have hnv : -v ≠ 0 := neg_ne_zero.mpr hv
  have hpos := contMDiffOn_GExp_smul_Ioi (cov := cov) hmet x hnv
  have hnegmap : ContMDiffOn 𝓘(ℝ) 𝓘(ℝ) ∞ (fun s : ℝ => -s) (Iio 0) :=
    (contMDiff_id (I := 𝓘(ℝ))).neg.contMDiffOn
  have hcomp := hpos.comp hnegmap (fun s hs => by
    show -s ∈ Ioi (0 : ℝ)
    rw [Set.mem_Ioi]
    rw [Set.mem_Iio] at hs
    linarith)
  refine hcomp.congr (fun s hs => ?_)
  show GExp (cov := cov) hmet x (s • v) = GExp (cov := cov) hmet x ((-s) • (-v))
  congr 1
  rw [neg_smul, smul_neg, neg_neg]

/-- **The ray of the global exponential map is smooth everywhere.**  For `v ≠ 0`,
`s ↦ GExp x (s • v)` is `C^∞` on `ℝ`: near `0` it agrees with the chart exponential map, on `(0,∞)`
it is a reparametrised chosen geodesic segment and on `(-∞,0)` it is the ray of `-v`, reflected. -/
theorem contMDiffOn_GExp_smul (hmet : IsMetricCompatible cov) (x : M) {v : TangentSpace I x}
    (hv : v ≠ 0) :
    ContMDiffOn 𝓘(ℝ) I ∞ (fun s : ℝ => GExp (cov := cov) hmet x (s • v)) univ := by
  have h1 : ContMDiffOn 𝓘(ℝ) I ∞ (fun s : ℝ => GExp (cov := cov) hmet x (s • v))
      (Ioi 0 ∪ Ioo (-2 : ℝ) 2) :=
    (contMDiffOn_GExp_smul_Ioi (cov := cov) hmet x hv).union_of_isOpen
      (contMDiffOn_GExp_smul_Ioo_symm (cov := cov) hmet x hv 2) isOpen_Ioi isOpen_Ioo
  have h2 : ContMDiffOn 𝓘(ℝ) I ∞ (fun s : ℝ => GExp (cov := cov) hmet x (s • v))
      ((Ioi 0 ∪ Ioo (-2 : ℝ) 2) ∪ Iio 0) :=
    h1.union_of_isOpen (contMDiffOn_GExp_smul_Iio (cov := cov) hmet x hv)
      (isOpen_Ioi.union isOpen_Ioo) isOpen_Iio
  have hcover : ((Ioi 0 ∪ Ioo (-2 : ℝ) 2) ∪ Iio 0) = univ := by
    ext s
    simp only [Set.mem_union, Set.mem_Ioi, Set.mem_Ioo, Set.mem_Iio, Set.mem_univ, iff_true]
    rcases lt_trichotomy s 0 with h | h | h
    · exact Or.inr h
    · exact Or.inl (Or.inr (by rw [h]; norm_num))
    · exact Or.inl (Or.inl h)
  rw [hcover] at h2
  exact h2

/-- **A closed geodesic loop bounds the injectivity radius at its base point by half its length.**
Unit-speed form of `two_mul_le_of_isGeodesicAt_loop_speed` (`c = 1`): a unit-speed closed geodesic
loop `γ` on `Ioo a b` (with `a < 0 < T < b`, `γ T = γ 0`, non-vanishing velocity and no reversal at
the base point) satisfies `InjAtLeast hmet (γ 0) r ⟹ 2 r ≤ T`.

This is the "easy half" of the structure theorem `inj(p) = min{conj(p), ½ℓ(p)}`: a geodesic loop of
length `T` through `p` forces `inj(p) ≤ T/2`. -/
theorem two_mul_le_of_isGeodesicAt_loop
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {a b T r : ℝ} (ha : a < 0) (hT : 0 < T) (hTb : T < b)
    {γ : ℝ → M} (hsm : ContMDiffOn 𝓘(ℝ) I ∞ γ (Ioo a b))
    (hgeo : ∀ t ∈ Ioo a b, IsGeodesicAt cov γ t)
    (hne : ∀ t ∈ Ioo a b, curveVelocity (I := I) γ t ≠ 0)
    (hspeed : ∀ t ∈ Ioo a b, ‖curveVelocity (I := I) γ t‖ = 1)
    (hloop : γ T = γ 0) (hbase : γ (T - 0) = γ 0)
    (hvelne : (T / 2) • curveVelocity (I := I) γ 0
      ≠ (T / 2) • curveVelocity (I := I) (fun s : ℝ => γ (T - s)) 0)
    (hinj : InjAtLeast hmet (γ 0) r) : 2 * r ≤ T :=
  two_mul_le_of_isGeodesicAt_loop_speed (cov := cov) hmet htor (c := 1) one_pos ha hT hTb
    hsm hgeo hne (hspeed 0 ⟨ha, lt_trans hT hTb⟩) (hspeed T ⟨lt_trans ha hT, hTb⟩)
    hloop hbase hvelne hinj |> fun h => by rwa [one_mul] at h

end
end Submission.LensLoop
