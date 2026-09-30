import Submission.Work.RiemLib.FirstVariation
import Submission.Work.RiemLib.JetGapSq
import Submission.Work.RiemLib.JetGapLin
import Submission.Work.RiemLib.GSField

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Strict monotonicity of `d(p,·)` along the flow of an ascent field

`Submission/GSField.lean` defines the ascent predicate `IsAscentAt hmet p x V` (every shortest
direction from `x` to `p` makes an obtuse angle with `V`) and shows that it is exactly the
"gradient-like" condition of Grove–Shiohama's step 3.

Here we extract the *analytic* consequence needed for the flow argument:

* `left_lt_of_isAscentAt` — the exponential ray version: moving from `x` a small time in the
  direction `-V` strictly decreases `d(p,·)`;
* `flow_left_lt` — the flow version, obtained from the ray version by the `O(s²)` jet estimate
  `Submission.JetGapSq.riemannianEDist_le_sq_of_same_velocity`.

The proof of the ray version is the *upper* half of the first variation formula
(`Submission/FirstVariation.firstVariation_upper`): for a unit-speed minimising geodesic `γ` from
`p` to `x` of length `L`, the direction `u := -γ'(L)` is a shortest direction from `x` to `p`, so
`IsAscentAt` gives `⟪V,u⟫ < 0`, i.e. `⟪-V, γ'(L)⟫ < 0`; the first variation formula then upper
bounds `d(p, exp_x(t (-V)))` by `L + t(⟪-V,γ'(L)⟫ + ε) < L`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 2000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal InnerProductSpace
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.ChartConnection
open Submission.ChartBounds
open Submission.GlobalExp
open Submission.GSCritical
open Submission.GSField
open Submission.Distance
open Submission.Gauss
open Submission.FirstVariation
open Submission.JetGapSq
open Submission.JetGapLin
open Submission.Length

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

namespace Submission.GSFlow

noncomputable section

variable [I.Boundaryless] [Nontrivial E] [CompactSpace M]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]

/-- A nonzero model vector gives a nonzero tangent vector at any point. -/
lemma exists_nonzero_tangent (x : M) : ∃ w : TangentSpace I x, w ≠ 0 := by
  obtain ⟨e, he⟩ := exists_ne (0 : E)
  exact ⟨frameVector (I := I) x x e, by
    rw [Submission.Gauss.frameVector_self (I := I) x e]; exact he⟩

/-- **The ascent predicate is never satisfied at the pole itself.** -/
lemma not_isAscentAt_self (hmet : IsMetricCompatible cov) {p : M} {V : TangentSpace I p} :
    ¬ IsAscentAt (cov := cov) hmet p p V := by
  intro h
  obtain ⟨w, hw⟩ := exists_nonzero_tangent (I := I) p
  set u : TangentSpace I p := unitOf w hw with hudef
  have hu1 : ‖u‖ = 1 := unitOf_norm w hw
  have hp : p = GExp (cov := cov) hmet p (0 : TangentSpace I p) :=
    (GExp_zero (cov := cov) hmet p).symm
  have hp' : p = GExp (cov := cov) hmet p ((0:ℝ) • u) := by rw [zero_smul]; exact hp
  have hp'' : p = GExp (cov := cov) hmet p ((0:ℝ) • (-u)) := by rw [zero_smul]; exact hp
  have hd : Manifold.riemannianEDist I p p = ENNReal.ofReal (0:ℝ) := by
    rw [Manifold.riemannianEDist_self, ENNReal.ofReal_zero]
  have h1 : inner ℝ V u < 0 := h 0 u le_rfl hu1 hp' hd
  have h2 : inner ℝ V (-u) < 0 := h 0 (-u) le_rfl (by rw [norm_neg, hu1]) hp'' hd
  rw [inner_neg_right] at h2
  linarith

/-- **The quantitative ascent estimate** (exponential-ray form): there is a *linear* gain in the
distance to `p` when moving from `x` in the direction `-V`.  This is the upper half of the first
variation formula combined with the ascent condition. -/
theorem exists_gap_of_isAscentAt
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (hpinch : QuarterPinched cov)
    [PathConnectedSpace M] [RegularSpace M]
    {p x : M} {V : TangentSpace I x} (hV : IsAscentAt (cov := cov) hmet p x V) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ η : ℝ, 0 < η ∧ ∀ t ∈ Set.Ioo (0 : ℝ) δ,
      (Manifold.riemannianEDist I p (GExp (cov := cov) hmet x ((-t) • V))).toReal
        ≤ (Manifold.riemannianEDist I p x).toReal - η * t := by
  haveI hcb : IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x) :=
    Submission.EDist.isContinuousRiemannianBundle_infty (I := I)
  have hxp : x ≠ p := fun h => not_isAscentAt_self (cov := cov) hmet (h ▸ hV)
  -- Hopf–Rinow: a minimising vector at `p` reaching `x`
  obtain ⟨v, hvG, hvd⟩ :=
    Submission.HopfRinow.exists_geodesic_riemannianEDist_eq (cov := cov) hmet htor p x
  have hdxp : Manifold.riemannianEDist I p x ≠ 0 := fun h0 =>
    hxp (((Submission.EDist.riemannianEDist_eq_zero_iff (I := I)).mp h0).symm)
  have hLpos : 0 < ‖v‖ := by
    by_contra hcon
    push Not at hcon
    have hv0 : ‖v‖ = 0 := le_antisymm hcon (norm_nonneg v)
    rw [hvd, hv0, ENNReal.ofReal_zero] at hdxp
    exact hdxp rfl
  set L : ℝ := ‖v‖ with hLdef
  have hLnn : 0 ≤ L := hLpos.le
  have hvne : v ≠ 0 := by
    intro h
    rw [hLdef, h, norm_zero] at hLpos
    exact lt_irrefl 0 hLpos
  set ξ : TangentSpace I p := unitOf v hvne with hξdef
  have hξ1 : ‖ξ‖ = 1 := unitOf_norm v hvne
  have hLξ : L • ξ = v := by
    rw [hξdef, unitOf, hLdef, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hvne), one_smul]
  set G : ℝ → M := geodCurve (cov := cov) hmet L hLnn p ξ hξ1 with hGdef
  have hGspec := geodCurve_spec (cov := cov) hmet L hLnn p ξ hξ1
  have hG0 : G 0 = p := hGspec.1
  have hGsp : ∀ t ∈ Ioo (-(geodDelta (cov := cov) hmet))
      (L + geodDelta (cov := cov) hmet), ‖curveVelocity (I := I) G t‖ = 1 := by
    intro t ht
    rw [hGdef]
    exact hGspec.2.2.2.2 t ht
  have hGL : G L = x := by
    rw [hGdef, ← Submission.HopfRinow.GExp_eq_geodCurve (cov := cov) hmet (x := p) (u := ξ) hξ1
      (T := L) hLnn (r := L) hLnn le_rfl, hLξ, hvG]
  have hmin : Manifold.riemannianEDist I p (G L) = ENNReal.ofReal L := by rw [hGL, hvd]
  have hLIoo : L ∈ Ioo (-(geodDelta (cov := cov) hmet)) (L + geodDelta (cov := cov) hmet) :=
    ⟨by linarith [geodDelta_pos (cov := cov) hmet], by linarith [geodDelta_pos (cov := cov) hmet]⟩
  -- from now on the base point is `G L`
  subst hGL
  have hw1 : ‖curveVelocity (I := I) G L‖ = 1 := hGsp L hLIoo
  -- the direction from the base point to the far point `p`
  have hGp : GExp (cov := cov) hmet (G L) (L • (-curveVelocity (I := I) G L)) = p := by
    have h := Submission.HopfRinow.GExp_neg_smul_curveVelocity_geodCurve (cov := cov) hmet
      (x := p) (ξ := ξ) hξ1 (T := L) hLnn (t := L) hLnn le_rfl (s := L) hLnn le_rfl
    rw [← hGdef] at h
    rw [sub_self, hG0] at h
    rw [← h]
    congr 1
    rw [neg_smul, smul_neg]
  have hwnorm : ‖-curveVelocity (I := I) G L‖ = 1 := by
    rw [norm_neg]
    exact hw1
  have hdxp' : Manifold.riemannianEDist I (G L) p = ENNReal.ofReal L := by
    rw [Manifold.riemannianEDist_comm, hvd]
  have hasc : inner ℝ V (-curveVelocity (I := I) G L) < 0 :=
    hV L (-curveVelocity (I := I) G L) hLnn hwnorm hGp.symm hdxp'
  have hasc' : (0:ℝ) < inner ℝ V (curveVelocity (I := I) G L) := by
    have h := hasc
    rw [inner_neg_right] at h
    linarith
  -- the slope constant `c = ⟪-V, γ'(L)⟫ < 0`
  have hc : chartGram (I := I) (G L) (G L) (show E from (-V))
      (show E from curveVelocity (I := I) G L) < 0 := by
    have h1 : chartGram (I := I) (G L) (G L) (show E from (-V))
        (show E from curveVelocity (I := I) G L)
        = inner ℝ (show TangentSpace I (G L) from -(V:E))
            (show TangentSpace I (G L) from (curveVelocity (I := I) G L : E)) :=
      chartGram_self_apply (I := I) (G L) _ _
    rw [h1, inner_neg_left]
    have h2 : inner ℝ (show TangentSpace I (G L) from (V:E))
        (show TangentSpace I (G L) from (curveVelocity (I := I) G L : E))
        = inner ℝ V (curveVelocity (I := I) G L) := rfl
    rw [h2]
    linarith
  -- the first variation formula along `G`
  have hfar : ∀ ε > 0, ∀ᶠ t in nhdsWithin (0:ℝ) (Set.Ioi 0),
      (Manifold.riemannianEDist I p (expMap cov (G L) (t • (-(V:E))))).toReal
        ≤ L + t * (chartGram (I := I) (G L) (G L) (show E from (-V))
            (show E from curveVelocity (I := I) G L) + ε) := by
    intro ε hε
    have h := firstVariation_upper_geodCurve (cov := cov) hmet htor hpinch (q := p) (ξ := ξ) hξ1
      (T := L) hLnn hLpos le_rfl hmin (-(V:E)) ε hε
    rw [← hGdef] at h
    exact h
  obtain ⟨ρe, hρe, hagree⟩ := exists_pos_GExp_eq_expMap (cov := cov) hmet (G L)
  set c : ℝ := chartGram (I := I) (G L) (G L) (show E from (-V))
      (show E from curveVelocity (I := I) G L) with hcdef
  have hcneg : c < 0 := hcdef ▸ hc
  have hε0 : (0:ℝ) < -c/2 := by linarith
  have hbound := hfar (-c/2) hε0
  -- the flow stays inside the small ball on which `GExp = expMap`
  have hsmall : ∀ᶠ t in nhdsWithin (0:ℝ) (Set.Ioi 0), ‖(-t) • V‖ < ρe := by
    have hcont : Continuous (fun t : ℝ => ‖(-t) • V‖) :=
      continuous_norm.comp (continuous_id.neg.smul continuous_const)
    have ht := (hcont.tendsto (0:ℝ)).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
    rw [show ‖(-(0:ℝ)) • V‖ = 0 from by simp] at ht
    exact ht.eventually_lt_const hρe
  have hxval : (Manifold.riemannianEDist I p (G L)).toReal = L := by
    rw [hvd, hLdef, ENNReal.toReal_ofReal hLpos.le]
  have hev : ∀ᶠ t in nhdsWithin (0:ℝ) (Set.Ioi 0),
      (Manifold.riemannianEDist I p (GExp (cov := cov) hmet (G L) ((-t) • V))).toReal
        ≤ (Manifold.riemannianEDist I p (G L)).toReal - (-c/2) * t := by
    filter_upwards [hbound, self_mem_nhdsWithin, hsmall] with t ht htpos hsmall'
    rw [Set.mem_Ioi] at htpos
    have hge : GExp (cov := cov) hmet (G L) ((-t) • V) = expMap cov (G L) (t • (-(V:E))) := by
      rw [hagree ((-t) • V) hsmall']
      simp only [smul_neg, neg_smul]
    rw [hge, hxval]
    refine le_trans ht ?_
    have : c + -c/2 = c/2 := by ring
    rw [this]
    have : L - (-c/2) * t = L + t * (c/2) := by ring
    rw [this]
  obtain ⟨δ, hδ, hδsub⟩ := (nhdsGT_basis (0:ℝ)).mem_iff.mp hev
  exact ⟨δ, hδ, -c/2, by linarith, fun t ht => hδsub ht⟩

/-- **Moving in the direction of an ascent vector decreases the distance to `p`** (exponential-ray
form). -/
theorem left_lt_of_isAscentAt
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (hpinch : QuarterPinched cov)
    [PathConnectedSpace M] [RegularSpace M]
    {p x : M} {V : TangentSpace I x} (hV : IsAscentAt (cov := cov) hmet p x V) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t ∈ Set.Ioo (0 : ℝ) δ,
      Manifold.riemannianEDist I p (GExp (cov := cov) hmet x ((-t) • V))
        < Manifold.riemannianEDist I p x := by
  obtain ⟨δ, hδ, η, hη, hgap⟩ :=
    exists_gap_of_isAscentAt (cov := cov) hmet htor hpinch hV
  have hfinx : Manifold.riemannianEDist I p x ≠ ⊤ :=
    (Submission.HopfRinow.riemannianEDist_lt_top (I := I) (cov := cov) hmet htor p x).ne
  refine ⟨δ, hδ, fun t ht => ?_⟩
  have hfina : Manifold.riemannianEDist I p (GExp (cov := cov) hmet x ((-t) • V)) ≠ ⊤ :=
    (Submission.HopfRinow.riemannianEDist_lt_top (I := I) (cov := cov) hmet htor p _).ne
  refine (ENNReal.toReal_lt_toReal hfina hfinx).mp ?_
  have h := hgap t ht
  have : (0:ℝ) < η * t := mul_pos hη ht.1
  linarith


/-- The zero vector is never an ascent direction. -/
lemma not_isAscentAt_zero (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    [PathConnectedSpace M] [RegularSpace M] {p x : M} :
    ¬ IsAscentAt (cov := cov) hmet p x (0 : TangentSpace I x) := by
  haveI hcb : IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x) :=
    Submission.EDist.isContinuousRiemannianBundle_infty (I := I)
  intro h
  rcases eq_or_ne p x with hpx | hpx
  · subst hpx
    obtain ⟨w, hw⟩ := exists_nonzero_tangent (I := I) p
    set u : TangentSpace I p := unitOf w hw with hudef
    have hu1 : ‖u‖ = 1 := unitOf_norm w hw
    have h1 := h 0 u le_rfl hu1 (by rw [zero_smul, GExp_zero])
      (by rw [Manifold.riemannianEDist_self, ENNReal.ofReal_zero])
    simp at h1
  · have hfin : Manifold.riemannianEDist I x p ≠ ⊤ :=
      (Submission.HopfRinow.riemannianEDist_lt_top (I := I) (cov := cov) hmet htor x p).ne
    have hne : Manifold.riemannianEDist I x p ≠ 0 := by
      intro h0
      exact hpx (((Submission.EDist.riemannianEDist_eq_zero_iff (I := I)).mp h0)).symm
    set t : ℝ := (Manifold.riemannianEDist I x p).toReal with htdef
    have htpos : 0 < t := by
      rw [htdef]
      exact ENNReal.toReal_pos hne hfin
    have hdt : Manifold.riemannianEDist I x p = ENNReal.ofReal t := by
      rw [htdef]
      exact (ENNReal.ofReal_toReal hfin).symm
    obtain ⟨u, hu1, hpu⟩ :=
      Submission.GSCritical.exists_unit_of_dist (cov := cov) hmet htor hdt htpos
    have h1 := h t u htpos.le hu1 hpu hdt
    simp at h1

/-- **The exponential ray in the direction `-V` is a geodesic ray.**  For a nonzero tangent vector
`V` at `x` there is a curve through `x`, smooth at `0`, with velocity `-V` at `0` and agreeing
with the global exponential ray `t ↦ GExp x (-t • V)` for `t ∈ (0,1)`. -/
theorem exists_ray_curve (hmet : IsMetricCompatible cov) {x : M} {V : TangentSpace I x}
    (hVne : V ≠ 0) :
    ∃ ray : ℝ → M, ray 0 = x ∧ ContMDiffAt 𝓘(ℝ) I ∞ ray 0 ∧
      curveVelocity (I := I) ray 0 = -V ∧
      ∀ t ∈ Set.Ioo (0:ℝ) 1, ray t = GExp (cov := cov) hmet x ((-t) • V) := by
  set ξ : TangentSpace I x := unitOf V hVne with hξdef
  have hξ1 : ‖ξ‖ = 1 := unitOf_norm V hVne
  have hξ'1 : ‖-ξ‖ = 1 := by rw [norm_neg, hξ1]
  have hTnn : 0 ≤ ‖V‖ := norm_nonneg V
  set G : ℝ → M := geodCurve (cov := cov) hmet ‖V‖ hTnn x (-ξ) hξ'1 with hGdef
  have hGspec := geodCurve_spec (cov := cov) hmet ‖V‖ hTnn x (-ξ) hξ'1
  have hG0 : G 0 = x := hGspec.1
  have hGvel : curveVelocity (I := I) G 0 = -ξ := hGspec.2.1
  have hGsm : ContMDiffOn 𝓘(ℝ) I ∞ G (Ioo (-(geodDelta (cov := cov) hmet))
      (‖V‖ + geodDelta (cov := cov) hmet)) := hGspec.2.2.1
  have hVξ : ‖V‖ • ξ = V := by
    rw [hξdef, unitOf, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hVne), one_smul]
  have hmem : (0:ℝ) ∈ Ioo (-(geodDelta (cov := cov) hmet))
      (‖V‖ + geodDelta (cov := cov) hmet) :=
    ⟨by linarith [geodDelta_pos (cov := cov) hmet],
     by linarith [geodDelta_pos (cov := cov) hmet]⟩
  refine ⟨fun t => G (‖V‖ * t), ?_, ?_, ?_, ?_⟩
  · show G (‖V‖ * 0) = x
    rw [mul_zero, hG0]
  · have hGmd0 : ContMDiffAt 𝓘(ℝ) I ∞ G (‖V‖ * 0) := by
      rw [mul_zero]
      exact hGsm.contMDiffAt (isOpen_Ioo.mem_nhds hmem)
    exact hGmd0.comp 0 (contMDiffAt_const.mul contMDiffAt_id)
  · have hGmd : MDifferentiableAt 𝓘(ℝ) I G 0 :=
      (hGsm.contMDiffAt (isOpen_Ioo.mem_nhds hmem)).mdifferentiableAt (by simp)
    have h := Submission.Length.curveVelocity_comp_mul_add (I := I) (γ := G) (c := ‖V‖) (d := 0) (t := 0)
      (by simpa using hGmd)
    have hfun : (fun t : ℝ => G (‖V‖ * t)) = (fun s : ℝ => G (‖V‖ * s + 0)) := by
      funext s; rw [add_zero]
    rw [hfun, h, mul_zero, zero_add, hGvel]
    show (‖V‖ : ℝ) • (show TangentSpace I x from -ξ) = -V
    rw [smul_neg, hVξ]
  · intro t ht
    show G (‖V‖ * t) = GExp (cov := cov) hmet x ((-t) • V)
    rw [hGdef]
    rw [← Submission.HopfRinow.GExp_eq_geodCurve (cov := cov) hmet (x := x) (u := -ξ) hξ'1
      (T := ‖V‖) hTnn (r := ‖V‖ * t) (by nlinarith [ht.1, norm_nonneg V])
      (by nlinarith [ht.2, norm_nonneg V])]
    congr 1
    calc (‖V‖ * t) • (-ξ) = (t * ‖V‖) • (-ξ) := by rw [mul_comm]
      _ = t • (‖V‖ • (-ξ)) := by rw [mul_smul]
      _ = t • (-(‖V‖ • ξ)) := by rw [smul_neg]
      _ = -(t • (‖V‖ • ξ)) := by rw [smul_neg]
      _ = -(t • V) := by rw [hVξ]
      _ = (-t) • V := by rw [neg_smul]

/-- **The flow of an ascent field strictly decreases `d(p,·)` backwards in time.**

`σ` is any curve through `x` which is `C^∞` at `0` with velocity `-V` there — typically the
reparametrised flow line `t ↦ φ x (-t)` of the field `V`.  Then `d(p, σ t) < d(p, x)` for all small
`t > 0`.  The proof combines the quantitative first-variation estimate `exists_gap_of_isAscentAt`
with the `o(t)` transfer `Submission.JetGapLin.riemannianEDist_le_lin_of_same_velocity` between `σ`
and the geodesic ray in the same direction. -/
theorem flow_left_lt
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (hpinch : QuarterPinched cov)
    [PathConnectedSpace M] [RegularSpace M]
    {p x : M} {V : TangentSpace I x} (hV : IsAscentAt (cov := cov) hmet p x V)
    {σ : ℝ → M} (hσ0 : σ 0 = x)
    (hσsm : ContMDiffAt 𝓘(ℝ) I ∞ σ 0)
    (hσv : curveVelocity (I := I) σ 0 = -V) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t ∈ Set.Ioo (0 : ℝ) δ,
      Manifold.riemannianEDist I p (σ t) < Manifold.riemannianEDist I p x := by
  have hVne : V ≠ 0 := fun h0 => not_isAscentAt_zero (cov := cov) hmet htor (h0 ▸ hV)
  obtain ⟨ray, hray0, hraysm, hrayv, hrayid⟩ := exists_ray_curve (cov := cov) hmet hVne
  obtain ⟨δg, hδg, η, hη, hgap⟩ := exists_gap_of_isAscentAt (cov := cov) hmet htor hpinch hV
  -- the `o(t)` comparison
  have hlin : ∀ ε > 0, ∀ᶠ s in 𝓝 (0:ℝ),
      Manifold.riemannianEDist I (σ s) (ray s) ≤ ENNReal.ofReal (ε * |s|) :=
    Submission.JetGapLin.riemannianEDist_le_lin_of_same_velocity (I := I)
      (hσsm.mdifferentiableAt (by simp)) (hraysm.mdifferentiableAt (by simp))
      (by rw [hσ0, hray0]) (by rw [hσv, hrayv])
  have hlin' : ∀ᶠ t in nhdsWithin (0:ℝ) (Set.Ioi 0),
      Manifold.riemannianEDist I (ray t) (σ t) ≤ ENNReal.ofReal ((η/2) * |t|) :=
    ((hlin (η/2) (by linarith)).filter_mono nhdsWithin_le_nhds).mono (fun t ht => by
      rwa [Manifold.riemannianEDist_comm] at ht)
  have hδfilter : ∀ᶠ t in nhdsWithin (0:ℝ) (Set.Ioi 0), t < δg :=
    (nhdsGT_basis (0:ℝ)).mem_iff.mpr ⟨δg, hδg, fun t ht => ht.2⟩
  have h1filter : ∀ᶠ t in nhdsWithin (0:ℝ) (Set.Ioi 0), t < 1 :=
    (nhdsGT_basis (0:ℝ)).mem_iff.mpr ⟨1, one_pos, fun t ht => ht.2⟩
  have hev : ∀ᶠ t in nhdsWithin (0:ℝ) (Set.Ioi 0),
      (Manifold.riemannianEDist I p (σ t)).toReal
        < (Manifold.riemannianEDist I p x).toReal := by
    filter_upwards [hlin', self_mem_nhdsWithin, hδfilter, h1filter]
      with t hlin_t htpos hgt ht1
    rw [Set.mem_Ioi] at htpos
    have hrayeq : ray t = GExp (cov := cov) hmet x ((-t) • V) := hrayid t ⟨htpos, ht1⟩
    have htri := Manifold.riemannianEDist_triangle (I := I) (x := p) (y := ray t) (z := σ t)
    have hfin1 : Manifold.riemannianEDist I p (ray t) ≠ ⊤ :=
      (Submission.HopfRinow.riemannianEDist_lt_top (I := I) (cov := cov) hmet htor p _).ne
    have hfin2 : Manifold.riemannianEDist I (ray t) (σ t) ≠ ⊤ :=
      (Submission.HopfRinow.riemannianEDist_lt_top (I := I) (cov := cov) hmet htor _ _).ne
    have htri' : (Manifold.riemannianEDist I p (σ t)).toReal
        ≤ (Manifold.riemannianEDist I p (ray t)).toReal
          + (Manifold.riemannianEDist I (ray t) (σ t)).toReal := by
      calc (Manifold.riemannianEDist I p (σ t)).toReal
          ≤ (Manifold.riemannianEDist I p (ray t)
              + Manifold.riemannianEDist I (ray t) (σ t)).toReal :=
            ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hfin1, hfin2⟩) htri
        _ = _ := ENNReal.toReal_add hfin1 hfin2
    have h1 : (Manifold.riemannianEDist I p (ray t)).toReal
        ≤ (Manifold.riemannianEDist I p x).toReal - η * t := by
      rw [hrayeq]
      exact hgap t ⟨htpos, hgt⟩
    have h2 : (Manifold.riemannianEDist I (ray t) (σ t)).toReal ≤ (η/2) * t := by
      have h := ENNReal.toReal_mono (ENNReal.ofReal_ne_top) hlin_t
      rw [ENNReal.toReal_ofReal (by positivity : (0:ℝ) ≤ (η/2) * |t|), abs_of_pos htpos] at h
      exact h
    have h3 : (η/2) * t < η * t := by nlinarith
    linarith
  obtain ⟨δ, hδ, hδsub⟩ := (nhdsGT_basis (0:ℝ)).mem_iff.mp hev
  refine ⟨δ, hδ, fun t ht => ?_⟩
  have hfina : Manifold.riemannianEDist I p (σ t) ≠ ⊤ :=
    (Submission.HopfRinow.riemannianEDist_lt_top (I := I) (cov := cov) hmet htor p _).ne
  have hfinx : Manifold.riemannianEDist I p x ≠ ⊤ :=
    (Submission.HopfRinow.riemannianEDist_lt_top (I := I) (cov := cov) hmet htor p x).ne
  exact (ENNReal.toReal_lt_toReal hfina hfinx).mp (hδsub ht)

end

end Submission.GSFlow
