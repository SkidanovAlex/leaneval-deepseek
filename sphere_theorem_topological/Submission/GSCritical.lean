import Submission.GSBall
import Submission.GSConcave
import Submission.Commons.Geometry.Sphere.modelDist_cos
import Submission.Commons.Geometry.Sphere.modelDist_trig_le_pi_div_two

/-!
# The critical point theory of the distance function `d(p,·)` (Grove–Shiohama, step 1)

This file starts the Grove–Shiohama critical point theory.  Two ingredients:

* **`two_sided_hinge`** — the *two-sided hinge inequality*: if `z` is a point, `x₁` and `x₂` lie on
  opposite geodesic rays from `z` at distances `a₁`, `a₂`, and `p` lies at distance `u` from `z`
  (all three sides minimising, and the sums `a₁+u`, `a₂+u` at most `π`), then

  `cos u · sin (a₁+a₂) ≤ sin a₂ · cos d(x₁,p) + sin a₁ · cos d(x₂,p)`.

  It is the sum of the two hinge comparisons at the apex `z`, the two hinges having the adjacent
  angles `θ` and `π-θ`.  Its main consequence (`not_both_gt_pi_div_two`) is the concavity-type fact
  that if `u ≤ π/2` then `x₁` and `x₂` cannot *both* be at distance `> π/2` from `p` — "a geodesic
  through a point at distance `≤ π/2` from `p` meets the `π/2`-sphere of `p` at most once on each
  side".

* **`IsCrit`** — the notion of a critical point of `f = d(p,·)` (it is the *singular* point of the
  notes' Definition 5.2.11), and the first case of Grove–Shiohama's step 2: a point `x` with
  `d(x,p) ≤ π/2` and `d(x,q) ≤ π/2` is *never* critical when `d(p,q) > π/2` (this is the
  `π/2`-ball lemma `Submission.GSBall.edist_le_pi_div_two_of_hinge`).
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 2000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal InnerProductSpace
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.GlobalExp
open Submission.HingeGlobal
open Submission.HingeKey
open Submission.HingePiece
open Submission.HingeClosed
open Submission.HopfRinow

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

namespace Submission.GSCritical

noncomputable section

variable [I.Boundaryless] [Nontrivial E] [CompactSpace M]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]

/-! ## The two-sided hinge inequality -/

/-- **The two-sided hinge inequality.**  `x₁`, `x₂` are the endpoints of the geodesic through `z`
in the two directions `ux`, `-ux` at distances `a₁`, `a₂`, and `p = GExp z (u • up)`; all three
distances `a₁`, `a₂`, `u` are realised by minimising geodesics and `a₁+u ≤ π`, `a₂+u ≤ π`.
Then `cos u · sin (a₁+a₂) ≤ sin a₂ cos d₁ + sin a₁ cos d₂`, where `dᵢ = d(xᵢ,p)`. -/
theorem two_sided_hinge
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (hpinch : QuarterPinched cov)
    [PathConnectedSpace M] [RegularSpace M]
    {z x₁ x₂ p : M} {a₁ a₂ u d₁ d₂ : ℝ} {ux up : TangentSpace I z}
    (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (hu : 0 < u)
    (hux : ‖ux‖ = 1) (hup : ‖up‖ = 1)
    (ha₁u : a₁ + u ≤ Real.pi) (ha₂u : a₂ + u ≤ Real.pi)
    (hx₁ : x₁ = GExp (cov := cov) hmet z (a₁ • ux))
    (hx₂ : x₂ = GExp (cov := cov) hmet z (a₂ • (-ux)))
    (hp : p = GExp (cov := cov) hmet z (u • up))
    (hzp : Manifold.riemannianEDist I z p = ENNReal.ofReal u)
    (hzx₁ : Manifold.riemannianEDist I z x₁ = ENNReal.ofReal a₁)
    (hzx₂ : Manifold.riemannianEDist I z x₂ = ENNReal.ofReal a₂)
    (hd₁ : Manifold.riemannianEDist I x₁ p = ENNReal.ofReal d₁)
    (hd₂ : Manifold.riemannianEDist I x₂ p = ENNReal.ofReal d₂)
    (hd₁nn : 0 ≤ d₁) (hd₂nn : 0 ≤ d₂) :
    Real.cos u * Real.sin (a₁ + a₂)
      ≤ Real.sin a₂ * Real.cos d₁ + Real.sin a₁ * Real.cos d₂ := by
  have ha₁π : a₁ < Real.pi := by linarith
  have ha₂π : a₂ < Real.pi := by linarith
  have ha₁le : a₁ ≤ Real.pi := ha₁π.le
  have ha₂le : a₂ ≤ Real.pi := ha₂π.le
  have huπ : u < Real.pi := by linarith
  have hule : u ≤ Real.pi := huπ.le
  have hsin₁ : 0 ≤ Real.sin a₁ := Real.sin_nonneg_of_nonneg_of_le_pi ha₁.le ha₁le
  have hsin₂ : 0 ≤ Real.sin a₂ := Real.sin_nonneg_of_nonneg_of_le_pi ha₂.le ha₂le
  -- the first hinge comparison at `z`
  have hH₁ : Manifold.riemannianEDist I (GExp (cov := cov) hmet z (a₁ • ux))
      (GExp (cov := cov) hmet z (u • up))
      ≤ ENNReal.ofReal (modelDist1 (hingeAngle ux up) a₁ u) :=
    gcompHolds_pi_le (cov := cov) hmet htor hpinch (z := z) ha₁ hu ha₁u hux hup
      (by rw [← hx₁]; exact hzx₁) (by rw [← hp]; exact hzp)
  -- the second hinge comparison at `z`, with the direction `-ux`
  have hux' : ‖(-ux : TangentSpace I z)‖ = 1 := by rw [norm_neg]; exact hux
  have hH₂ : Manifold.riemannianEDist I (GExp (cov := cov) hmet z (a₂ • (-ux)))
      (GExp (cov := cov) hmet z (u • up))
      ≤ ENNReal.ofReal (modelDist1 (hingeAngle (-ux) up) a₂ u) :=
    gcompHolds_pi_le (cov := cov) hmet htor hpinch (z := z) ha₂ hu ha₂u hux' hup
      (by rw [← hx₂]; exact hzx₂) (by rw [← hp]; exact hzp)
  have hle₁ : Manifold.riemannianEDist I x₁ p
      ≤ ENNReal.ofReal (modelDist1 (hingeAngle ux up) a₁ u) := by
    rw [hx₁, hp]; exact hH₁
  have hle₂ : Manifold.riemannianEDist I x₂ p
      ≤ ENNReal.ofReal (modelDist1 (hingeAngle (-ux) up) a₂ u) := by
    rw [hx₂, hp]; exact hH₂
  have hr₁ : d₁ ≤ modelDist1 (hingeAngle ux up) a₁ u := by
    have h := hle₁
    rw [hd₁] at h
    exact (ENNReal.ofReal_le_ofReal_iff (modelDist1_nonneg _ _ _)).mp h
  have hr₂ : d₂ ≤ modelDist1 (hingeAngle (-ux) up) a₂ u := by
    have h := hle₂
    rw [hd₂] at h
    exact (ENNReal.ofReal_le_ofReal_iff (modelDist1_nonneg _ _ _)).mp h
  -- the cosine of the two model distances
  have hθmem : hingeAngle ux up ∈ Set.Icc (0 : ℝ) Real.pi :=
    ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩
  have hθ'mem : hingeAngle (-ux) up ∈ Set.Icc (0 : ℝ) Real.pi :=
    ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩
  have hcosmodel₁ : Real.cos (modelDist1 (hingeAngle ux up) a₁ u)
      = Real.cos a₁ * Real.cos u + Real.sin a₁ * Real.sin u * Real.cos (hingeAngle ux up) := by
    rw [modelDist1]
    exact Commons.Geometry.Sphere.modelDist_cos ha₁.le ha₁le hu.le hule hθmem.1 hθmem.2
  have hcosmodel₂ : Real.cos (modelDist1 (hingeAngle (-ux) up) a₂ u)
      = Real.cos a₂ * Real.cos u + Real.sin a₂ * Real.sin u * Real.cos (hingeAngle (-ux) up) := by
    rw [modelDist1]
    exact Commons.Geometry.Sphere.modelDist_cos ha₂.le ha₂le hu.le hule hθ'mem.1 hθ'mem.2
  -- the adjacent angle is `π - θ`
  have hcosθ' : Real.cos (hingeAngle (-ux) up) = -Real.cos (hingeAngle ux up) := by
    have e1 : Real.cos (hingeAngle (-ux) up) = inner ℝ (-ux) up := cos_hingeAngle hux' hup
    have e2 : inner ℝ (-ux) up = -inner ℝ ux up := inner_neg_left _ _
    have e3 : Real.cos (hingeAngle ux up) = inner ℝ ux up := cos_hingeAngle hux hup
    rw [e1, e2, e3]
  -- the two cosine bounds
  have hb₁ : Real.cos a₁ * Real.cos u + Real.sin a₁ * Real.sin u * Real.cos (hingeAngle ux up)
      ≤ Real.cos d₁ := by
    have hm : modelDist1 (hingeAngle ux up) a₁ u ∈ Set.Icc (0 : ℝ) Real.pi :=
      ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩
    have hm₁ : d₁ ∈ Set.Icc (0 : ℝ) Real.pi :=
      ⟨hd₁nn, le_trans hr₁ hm.2⟩
    have h := Real.antitoneOn_cos hm₁ hm hr₁
    rw [hcosmodel₁] at h
    exact h
  have hb₂ : Real.cos a₂ * Real.cos u + Real.sin a₂ * Real.sin u * Real.cos (hingeAngle (-ux) up)
      ≤ Real.cos d₂ := by
    have hm : modelDist1 (hingeAngle (-ux) up) a₂ u ∈ Set.Icc (0 : ℝ) Real.pi :=
      ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩
    have hm₂ : d₂ ∈ Set.Icc (0 : ℝ) Real.pi :=
      ⟨hd₂nn, le_trans hr₂ hm.2⟩
    have h := Real.antitoneOn_cos hm₂ hm hr₂
    rw [hcosmodel₂] at h
    exact h
  -- multiply by the positive sines and add
  have hstep₁ : Real.sin a₂ * (Real.cos a₁ * Real.cos u
      + Real.sin a₁ * Real.sin u * Real.cos (hingeAngle ux up))
      ≤ Real.sin a₂ * Real.cos d₁ := mul_le_mul_of_nonneg_left hb₁ hsin₂
  have hstep₂ : Real.sin a₁ * (Real.cos a₂ * Real.cos u
      + Real.sin a₂ * Real.sin u * Real.cos (hingeAngle (-ux) up))
      ≤ Real.sin a₁ * Real.cos d₂ := mul_le_mul_of_nonneg_left hb₂ hsin₁
  have hfinal : Real.cos u * Real.sin (a₁ + a₂)
      ≤ Real.sin a₂ * Real.cos d₁ + Real.sin a₁ * Real.cos d₂ := by
    have h := add_le_add hstep₁ hstep₂
    have hexp : Real.sin a₂ * (Real.cos a₁ * Real.cos u
          + Real.sin a₁ * Real.sin u * Real.cos (hingeAngle ux up))
        + Real.sin a₁ * (Real.cos a₂ * Real.cos u
          + Real.sin a₂ * Real.sin u * Real.cos (hingeAngle (-ux) up))
        = Real.cos u * Real.sin (a₁ + a₂) := by
      rw [hcosθ', Real.sin_add]; ring
    linarith [h, hexp.symm.le, hexp.le]
  exact hfinal

/-- **A geodesic through a point at distance `≤ π/2` from `p` never leaves the ball on both
sides.**  If `u = d(z,p) ≤ π/2` and the two opposite rays from `z` have endpoints `x₁`, `x₂` at
distances `a₁`, `a₂` with `aᵢ + u ≤ π` and `a₁ + a₂ ≤ π`, then `d(x₁,p) > π/2` and `d(x₂,p) > π/2`
cannot both hold. -/
theorem not_both_gt_pi_div_two
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (hpinch : QuarterPinched cov)
    [PathConnectedSpace M] [RegularSpace M]
    {z x₁ x₂ p : M} {a₁ a₂ u d₁ d₂ : ℝ} {ux up : TangentSpace I z}
    (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (hu : 0 < u)
    (hux : ‖ux‖ = 1) (hup : ‖up‖ = 1)
    (ha₁u : a₁ + u ≤ Real.pi) (ha₂u : a₂ + u ≤ Real.pi) (ha₁₂ : a₁ + a₂ ≤ Real.pi)
    (hu2 : u ≤ Real.pi / 2)
    (hx₁ : x₁ = GExp (cov := cov) hmet z (a₁ • ux))
    (hx₂ : x₂ = GExp (cov := cov) hmet z (a₂ • (-ux)))
    (hp : p = GExp (cov := cov) hmet z (u • up))
    (hzp : Manifold.riemannianEDist I z p = ENNReal.ofReal u)
    (hzx₁ : Manifold.riemannianEDist I z x₁ = ENNReal.ofReal a₁)
    (hzx₂ : Manifold.riemannianEDist I z x₂ = ENNReal.ofReal a₂)
    (hd₁ : Manifold.riemannianEDist I x₁ p = ENNReal.ofReal d₁)
    (hd₂ : Manifold.riemannianEDist I x₂ p = ENNReal.ofReal d₂)
    (hd₁nn : 0 ≤ d₁) (hd₂nn : 0 ≤ d₂)
    (hd₁π : d₁ ≤ Real.pi) (hd₂π : d₂ ≤ Real.pi)
    (hfar₁ : Real.pi / 2 < d₁) (hfar₂ : Real.pi / 2 < d₂) : False := by
  have hmain := two_sided_hinge (cov := cov) hmet htor hpinch ha₁ ha₂ hu hux hup ha₁u ha₂u
    hx₁ hx₂ hp hzp hzx₁ hzx₂ hd₁ hd₂ hd₁nn hd₂nn
  have hsin₁ : 0 < Real.sin a₁ := Real.sin_pos_of_pos_of_lt_pi ha₁ (by linarith)
  have hsin₂ : 0 < Real.sin a₂ := Real.sin_pos_of_pos_of_lt_pi ha₂ (by linarith)
  have hcos₁ : Real.cos d₁ < 0 := Real.cos_neg_of_pi_div_two_lt_of_lt hfar₁ (by linarith)
  have hcos₂ : Real.cos d₂ < 0 := Real.cos_neg_of_pi_div_two_lt_of_lt hfar₂ (by linarith)
  have hRHS : Real.sin a₂ * Real.cos d₁ + Real.sin a₁ * Real.cos d₂ < 0 :=
    add_neg (mul_neg_of_pos_of_neg hsin₂ hcos₁) (mul_neg_of_pos_of_neg hsin₁ hcos₂)
  have hLHS : 0 ≤ Real.cos u * Real.sin (a₁ + a₂) :=
    mul_nonneg (Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith) hu2)
      (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) ha₁₂)
  linarith

/-! ## The critical point predicate -/

/-- **`x` is a critical point of `f = d(p,·)`** (the notes' *singular* point): no tangent direction
`v` is "away" from `p`, i.e. every unit `v` admits a shortest geodesic direction `u` to `p` making
an angle `≤ π/2` with `v` (`⟪v,u⟫ ≥ 0`). -/
def IsCrit (hmet : IsMetricCompatible cov) (p x : M) : Prop :=
  ∀ v : TangentSpace I x, ‖v‖ = 1 → ∃ (r : ℝ) (u : TangentSpace I x),
    0 ≤ r ∧ ‖u‖ = 1 ∧ p = GExp (cov := cov) hmet x (r • u) ∧
    Manifold.riemannianEDist I x p = ENNReal.ofReal r ∧ 0 ≤ inner ℝ v u

/-- A shortest-geodesic direction always exists (Hopf–Rinow). -/
theorem exists_unit_of_dist
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    [PathConnectedSpace M] [RegularSpace M]
    {x p : M} {t : ℝ} (h : Manifold.riemannianEDist I x p = ENNReal.ofReal t) (ht : 0 < t) :
    ∃ u : TangentSpace I x, ‖u‖ = 1 ∧ p = GExp (cov := cov) hmet x (t • u) := by
  obtain ⟨v, hvG, hvd⟩ :=
    Submission.HopfRinow.exists_geodesic_riemannianEDist_eq (cov := cov) hmet htor x p
  have hnorm : ‖v‖ = t := by
    rw [h] at hvd
    exact (ENNReal.ofReal_eq_ofReal_iff (norm_nonneg v) ht.le).mp hvd.symm
  have hvne : v ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hnorm; linarith
  refine ⟨unitOf v hvne, unitOf_norm v hvne, ?_⟩
  rw [← hvG, ← hnorm, unitOf, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hvne), one_smul]

/-- **Grove–Shiohama step 2, first case.**  If `d(p,q) > π/2` then a point `x` which is within
`π/2` of both `p` and `q` is *not* a critical point of `d(p,·)`. -/
theorem not_isCrit_of_le_pi_div_two
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (hpinch : QuarterPinched cov)
    [PathConnectedSpace M] [RegularSpace M]
    {p q x : M} {D : ℝ}
    (hD : Manifold.riemannianEDist I p q = ENNReal.ofReal D) (hDgt : Real.pi / 2 < D)
    (ht : Manifold.riemannianEDist I x p ≤ ENNReal.ofReal (Real.pi / 2))
    (hs : Manifold.riemannianEDist I x q ≤ ENNReal.ofReal (Real.pi / 2)) :
    ¬ IsCrit (cov := cov) hmet p x := by
  intro hcrit
  -- a shortest geodesic from `x` to `p`
  obtain ⟨vp, hpG, hpd⟩ :=
    Submission.HopfRinow.exists_geodesic_riemannianEDist_eq (cov := cov) hmet htor x p
  set t : ℝ := ‖vp‖ with htdef
  have htle : t ≤ Real.pi / 2 := by
    have h := ht
    rw [hpd] at h
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h
  have htnn : 0 ≤ t := norm_nonneg vp
  -- a shortest geodesic from `x` to `q`
  obtain ⟨vq, hqG, hqd⟩ :=
    Submission.HopfRinow.exists_geodesic_riemannianEDist_eq (cov := cov) hmet htor x q
  set s : ℝ := ‖vq‖ with hsdef
  have hsle : s ≤ Real.pi / 2 := by
    have h := hs
    rw [hqd] at h
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h
  have hsnn : 0 ≤ s := norm_nonneg vq
  -- both distances are positive
  have htpos : 0 < t := by
    rcases eq_or_lt_of_le htnn with h0 | h0
    · exfalso
      have hxp : x = p := by
        have h1 : vp = 0 := norm_eq_zero.mp h0.symm
        rw [h1, GExp_zero] at hpG
        exact hpG
      have hpq : Manifold.riemannianEDist I p q ≤ ENNReal.ofReal (Real.pi / 2) := by
        rw [← hxp]; exact hs
      rw [hD] at hpq
      have := (ENNReal.ofReal_le_ofReal_iff (by positivity : (0:ℝ) ≤ Real.pi / 2)).mp hpq
      linarith
    · exact h0
  have hspos : 0 < s := by
    rcases eq_or_lt_of_le hsnn with h0 | h0
    · exfalso
      have hxq : x = q := by
        have h1 : vq = 0 := norm_eq_zero.mp h0.symm
        rw [h1, GExp_zero] at hqG
        exact hqG
      have hpq : Manifold.riemannianEDist I p q ≤ ENNReal.ofReal (Real.pi / 2) := by
        rw [← hxq, Manifold.riemannianEDist_comm]; exact ht
      rw [hD] at hpq
      have := (ENNReal.ofReal_le_ofReal_iff (by positivity : (0:ℝ) ≤ Real.pi / 2)).mp hpq
      linarith
    · exact h0
  -- the unit direction to `q`
  have hvqne : vq ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hsdef; rw [hsdef] at hspos; exact lt_irrefl 0 hspos
  set w : TangentSpace I x := unitOf vq hvqne with hwdef
  have hw1 : ‖w‖ = 1 := unitOf_norm vq hvqne
  have hsw : s • w = vq := by
    rw [hwdef, hsdef, unitOf, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hvqne), one_smul]
  have hGvq : GExp (cov := cov) hmet x vq = GExp (cov := cov) hmet x (s • w) := by rw [hsw]
  have hqw : q = GExp (cov := cov) hmet x (s • w) := hqG.symm.trans hGvq
  -- criticality provides a shortest direction to `p` making an acute angle with `w`
  obtain ⟨r, u₂, hrnn, hu₂1, hpG', hpd', hinner⟩ := hcrit w hw1
  have hr : r = t := by
    have h1 : ENNReal.ofReal r = ENNReal.ofReal t := by
      rw [← hpd', ← hpd]
    exact (ENNReal.ofReal_eq_ofReal_iff hrnn htnn).mp h1
  have hGeq : p = GExp (cov := cov) hmet x (t • u₂) := by rw [← hr]; exact hpG'
  have hrpos : 0 < r := hr ▸ htpos
  -- the hinge comparison at `x`
  have hcmp := gcompHolds_pi_le (cov := cov) hmet htor hpinch (z := x)
    hrpos hspos (by linarith) hu₂1 hw1
    (by rw [← hpG']; exact hpd') (by rw [← hqw]; exact hqd)
  have hfinal : Manifold.riemannianEDist I p q ≤ ENNReal.ofReal (Real.pi / 2) := by
    have hmodel : modelDist1 (hingeAngle u₂ w) r s ≤ Real.pi / 2 := by
      have hα : hingeAngle u₂ w ≤ Real.pi / 2 :=
        Real.arccos_le_pi_div_two.mpr (by rw [real_inner_comm]; exact hinner)
      have := Commons.Geometry.Sphere.modelDist_trig_le_pi_div_two (l₁ := r) (l₂ := s)
        (α := hingeAngle u₂ w) hrpos.le (by rw [hr]; exact htle) hspos.le hsle
        (Real.arccos_nonneg _) hα
      rwa [modelDist1]
    calc Manifold.riemannianEDist I p q
        = Manifold.riemannianEDist I (GExp (cov := cov) hmet x (r • u₂))
            (GExp (cov := cov) hmet x (s • w)) := by rw [hGeq, hqw, hr]
      _ ≤ ENNReal.ofReal (modelDist1 (hingeAngle u₂ w) r s) := hcmp
      _ ≤ ENNReal.ofReal (Real.pi / 2) := ENNReal.ofReal_le_ofReal hmodel
  rw [hD] at hfinal
  have := (ENNReal.ofReal_le_ofReal_iff (by positivity : (0:ℝ) ≤ Real.pi / 2)).mp hfinal
  linarith

/-! ## Grove–Shiohama step 1: uniqueness of the maximum (abstract form) -/

/-- **Grove–Shiohama step 1, abstract form.**  `x₁` and `x₂` are the two ends of a geodesic through
`z` at distance `a` from `z` (so `z` is their midpoint), and `p` is at distance `u` from `z`; all
three points are at distance `D` from `p` (so, with `D = diam`, both are maximal points for
`d(p,·)`).  If `0 < a ≤ π/2`, `a + u ≤ π`, `u ≤ D` and `π/2 < D ≤ π`, this is impossible.

This is the exact contradiction underlying the uniqueness of the maximum of `d(p,·)` at a diameter
pair: `two_sided_hinge` gives `cos u · cos a ≤ cos D`, which is impossible for `u ≤ π/2`
(`cos u, cos a ≥ 0` but `cos D < 0`), while for `u > π/2` the concavity `GSConcave` forces `u = D`,
whence `cos a ≥ 1`, i.e. `a = 0`. -/
theorem step1_no_two_max
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (hpinch : QuarterPinched cov)
    [PathConnectedSpace M] [RegularSpace M]
    {z x₁ x₂ p : M} {a u D : ℝ} {ux up : TangentSpace I z}
    (ha : 0 < a) (ha2 : a ≤ Real.pi / 2) (hu : 0 < u) (haux : a + u ≤ Real.pi)
    (hDgt : Real.pi / 2 < D) (hDle : D ≤ Real.pi) (huD : u ≤ D)
    (hux : ‖ux‖ = 1) (hup : ‖up‖ = 1)
    (hx₁ : x₁ = GExp (cov := cov) hmet z (a • ux))
    (hx₂ : x₂ = GExp (cov := cov) hmet z (a • (-ux)))
    (hp : p = GExp (cov := cov) hmet z (u • up))
    (hz₁ : Manifold.riemannianEDist I z x₁ = ENNReal.ofReal a)
    (hz₂ : Manifold.riemannianEDist I z x₂ = ENNReal.ofReal a)
    (hzp : Manifold.riemannianEDist I z p = ENNReal.ofReal u)
    (h₁ : Manifold.riemannianEDist I x₁ p = ENNReal.ofReal D)
    (h₂ : Manifold.riemannianEDist I x₂ p = ENNReal.ofReal D) : False := by
  have hDnn : 0 ≤ D := le_trans (by linarith [Real.pi_pos]) hDgt.le
  have hcosDneg : Real.cos D < 0 := Real.cos_neg_of_pi_div_two_lt_of_lt hDgt (by linarith)
  have hmain := two_sided_hinge (cov := cov) hmet htor hpinch (z := z)
    ha ha hu hux hup haux haux hx₁ hx₂ hp hzp hz₁ hz₂ h₁ h₂ hDnn hDnn
  -- `cos u · sin (2a) ≤ 2 sin a · cos D`
  have hsin2a : Real.sin (a + a) = 2 * Real.sin a * Real.cos a := by
    rw [Real.sin_add]; ring
  rw [hsin2a] at hmain
  have hsina : 0 < Real.sin a := Real.sin_pos_of_pos_of_lt_pi ha (by linarith)
  have hkey : Real.cos u * Real.cos a ≤ Real.cos D := by
    nlinarith [hmain, hsina]
  rcases lt_or_ge (Real.pi / 2) u with hu2 | hu2
  · -- `u > π/2`: the concavity forces `u = D`
    have hDleu : D ≤ u := by
      have hconc := Submission.GSConcave.edist_add_midpoint_le (cov := cov) hmet htor hpinch
        (m := z) (p := p) (a := a) (r := u) (ux := ux) (up := up)
        ha hu haux hu2.le hux hup (by rw [← hx₁]; exact hz₁) (by rw [← hx₂]; exact hz₂)
        (by rw [← hp]; exact hzp)
      rw [← hx₁, ← hx₂, ← hp, h₁, h₂] at hconc
      rw [← ENNReal.ofReal_add hDnn hDnn] at hconc
      have h2 := (ENNReal.ofReal_le_ofReal_iff (by linarith : (0:ℝ) ≤ 2 * u)).mp hconc
      linarith
    have huD' : u = D := le_antisymm huD hDleu
    have hca : Real.cos a = 1 := by
      have h := hkey
      rw [huD'] at h
      have h2 : (-Real.cos D) * 1 ≤ (-Real.cos D) * Real.cos a := by nlinarith [h]
      have hpos : 0 < -Real.cos D := by linarith
      exact le_antisymm (Real.cos_le_one a) (le_of_mul_le_mul_left h2 hpos)
    have hcos0 : Real.cos a = Real.cos 0 := by rw [Real.cos_zero]; exact hca
    have := Real.injOn_cos (Set.mem_Icc.mpr ⟨ha.le, (by linarith : a ≤ Real.pi)⟩)
      (Set.mem_Icc.mpr ⟨le_refl 0, Real.pi_pos.le⟩) hcos0
    linarith
  · have hcosu : 0 ≤ Real.cos u := Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith) hu2
    have hcosa : 0 ≤ Real.cos a := Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], ha2⟩
    have : 0 ≤ Real.cos D := le_trans (mul_nonneg hcosu hcosa) hkey
    linarith
/-! ## Grove–Shiohama step 1: uniqueness of the maximum (diameter form) -/

/-- **Grove–Shiohama step 1.**  Let `D` be the diameter (all mutual distances are `≤ D`) and suppose
`π/2 < D ≤ 2π/3` and that `d(p,·)` attains its maximum `D` at two *distinct* points `q₁ ≠ q₂`.
This is impossible.

Proof: let `m` be the midpoint of a minimising geodesic from `q₁` to `q₂` (length `ℓ ≤ D`), and
`u = d(m,p) ≤ D`.  The two hinge comparisons at `m` give `cos u · cos (ℓ/2) ≤ cos D`, while
`ℓ/2 + u ≤ ℓ/2 + D ≤ 3D/2 ≤ π` makes the concavity `GSConcave` applicable in the case `u > π/2`.
Hence `u ≤ π/2` (whence `0 ≤ cos u cos (ℓ/2) ≤ cos D < 0`) or `u = D` (whence `cos (ℓ/2) ≥ 1`). -/
theorem step1_diameter_unique
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (hpinch : QuarterPinched cov)
    [PathConnectedSpace M] [RegularSpace M]
    {p q₁ q₂ : M} {D : ℝ}
    (hdiam : ∀ r s : M, Manifold.riemannianEDist I r s ≤ ENNReal.ofReal D)
    (hDgt : Real.pi / 2 < D) (hDle : D ≤ 2 * Real.pi / 3)
    (hq₁ : Manifold.riemannianEDist I p q₁ = ENNReal.ofReal D)
    (hq₂ : Manifold.riemannianEDist I p q₂ = ENNReal.ofReal D)
    (hne : q₁ ≠ q₂) : False := by
  haveI : IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x) :=
    Submission.EDist.isContinuousRiemannianBundle_infty (I := I)
  have hDnn : 0 ≤ D := le_trans (by linarith [Real.pi_pos]) hDgt.le
  have hDleπ : D ≤ Real.pi := by linarith [Real.pi_pos]
  -- the length `ℓ` of a minimising geodesic from `q₁` to `q₂`
  have hqfin : Manifold.riemannianEDist I q₁ q₂ ≠ ⊤ :=
    (lt_of_le_of_lt (hdiam q₁ q₂) ENNReal.ofReal_lt_top).ne
  set ℓ : ℝ := (Manifold.riemannianEDist I q₁ q₂).toReal with hℓdef
  have hℓ : Manifold.riemannianEDist I q₁ q₂ = ENNReal.ofReal ℓ :=
    (ENNReal.ofReal_toReal hqfin).symm
  have hℓle : ℓ ≤ D := by
    rw [hℓdef, ← ENNReal.toReal_ofReal hDnn]
    exact ENNReal.toReal_mono ENNReal.ofReal_ne_top (hdiam q₁ q₂)
  have hℓnn : 0 ≤ ℓ := by rw [hℓdef]; exact ENNReal.toReal_nonneg
  have hℓpos : 0 < ℓ := by
    rcases eq_or_lt_of_le hℓnn with h0 | h0
    · have hz : Manifold.riemannianEDist I q₁ q₂ = 0 := by
        rw [hℓ, ← h0, ENNReal.ofReal_zero]
      exact absurd ((Submission.EDist.riemannianEDist_eq_zero_iff (I := I)).mp hz) hne
    · exact h0
  -- Hopf–Rinow: a unit direction
  obtain ⟨v, hvG, hvd⟩ :=
    Submission.HopfRinow.exists_geodesic_riemannianEDist_eq (cov := cov) hmet htor q₁ q₂
  have hnorm : ‖v‖ = ℓ := by
    rw [hℓ] at hvd
    exact (ENNReal.ofReal_eq_ofReal_iff (norm_nonneg v) hℓnn).mp hvd.symm
  have hvne : v ≠ 0 := by intro h0; rw [h0, norm_zero] at hnorm; linarith
  set ξ : TangentSpace I q₁ := unitOf v hvne with hξdef
  have hξ1 : ‖ξ‖ = 1 := unitOf_norm v hvne
  have hℓξ : ℓ • ξ = v := by
    rw [hξdef, unitOf, show ℓ = ‖v‖ from hnorm.symm, smul_smul,
      mul_inv_cancel₀ (norm_ne_zero_iff.mpr hvne), one_smul]
  -- the minimising geodesic
  set G : ℝ → M := geodCurve (cov := cov) hmet ℓ hℓnn q₁ ξ hξ1 with hGdef
  have hG0 : G 0 = q₁ := (geodCurve_spec (cov := cov) hmet ℓ hℓnn q₁ ξ hξ1).1
  have hGℓ : G ℓ = q₂ := by
    rw [hGdef]
    rw [← GExp_eq_geodCurve (cov := cov) hmet (x := q₁) (u := ξ) hξ1 (T := ℓ) hℓnn
      (r := ℓ) hℓnn le_rfl, hℓξ, hvG]
  have hminℓ : Manifold.riemannianEDist I q₁ (G ℓ) = ENNReal.ofReal ℓ := by rw [hGℓ, hℓ]
  have hsub : ∀ a ∈ Set.Icc (0:ℝ) ℓ, ∀ b ∈ Set.Icc (0:ℝ) ℓ, a ≤ b →
      Manifold.riemannianEDist I (G a) (G b) = ENNReal.ofReal (b - a) := by
    have h := geodCurve_sub_arc_minimising' (cov := cov) hmet (T := ℓ) hℓnn hξ1 (s := ℓ) hℓnn le_rfl hminℓ
    intro a ha b hb hab
    simp only [hGdef]
    exact h a ha b hb hab
  -- the midpoint `m`
  set m : M := G (ℓ / 2) with hmdef
  have hm0 : Manifold.riemannianEDist I q₁ m = ENNReal.ofReal (ℓ / 2) := by
    have h := hsub 0 ⟨le_refl 0, hℓnn⟩ (ℓ / 2) ⟨by linarith, by linarith⟩ (by linarith)
    rw [hG0] at h
    simpa using h
  have hm1 : Manifold.riemannianEDist I m q₂ = ENNReal.ofReal (ℓ / 2) := by
    have h := hsub (ℓ / 2) ⟨by linarith, by linarith⟩ ℓ ⟨hℓnn, le_refl ℓ⟩ (by linarith)
    rw [hGℓ] at h
    rw [show ℓ - ℓ / 2 = ℓ / 2 from by ring] at h
    exact h
  -- Hopf–Rinow from `m` to `p`
  obtain ⟨vp, hpG, hpd⟩ :=
    Submission.HopfRinow.exists_geodesic_riemannianEDist_eq (cov := cov) hmet htor m p
  set u : ℝ := ‖vp‖ with hudef
  have hun : Manifold.riemannianEDist I m p = ENNReal.ofReal u := hpd
  have hunn : 0 ≤ u := norm_nonneg vp
  have huD : u ≤ D := (ENNReal.ofReal_le_ofReal_iff hDnn).mp (hun ▸ hdiam m p)
  -- `u > 0`
  have hupos : 0 < u := by
    rcases eq_or_lt_of_le hunn with h0 | h0
    · exfalso
      have h1 : vp = 0 := norm_eq_zero.mp h0.symm
      have hp0 : m = p := by
        have hm : m = GExp (cov := cov) hmet m vp := by rw [h1, GExp_zero]
        rw [hm, hpG]
      -- `p = m`, so `d(p,q₁) = d(m,q₁) = ℓ/2`
      have h2 : Manifold.riemannianEDist I p q₁ = ENNReal.ofReal (ℓ / 2) := by
        rw [← hp0, Manifold.riemannianEDist_comm]; exact hm0
      rw [hq₁, ENNReal.ofReal_eq_ofReal_iff hDnn (by linarith)] at h2
      linarith
    · exact h0
  have hvpn : vp ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hudef; rw [hudef] at hupos; exact lt_irrefl 0 hupos
  set up : TangentSpace I m := unitOf vp hvpn with hupdef
  have hup1 : ‖up‖ = 1 := unitOf_norm vp hvpn
  have huup : u • up = vp := by
    rw [hupdef, hudef, unitOf, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hvpn), one_smul]
  have hpup : p = GExp (cov := cov) hmet m (u • up) := by rw [huup]; exact hpG.symm
  -- the two directions through `m`
  set velt : TangentSpace I m :=
    curveVelocity (I := I) (geodCurve (cov := cov) hmet ℓ hℓnn q₁ ξ hξ1) (ℓ / 2) with hveltdef
  have hvelt1 : ‖velt‖ = 1 := by
    rw [hveltdef]
    exact norm_curveVelocity_geodCurve (cov := cov) hmet hℓnn q₁ ξ hξ1 (by linarith) (by linarith)
  have hneg1 : ‖-velt‖ = 1 := by rw [norm_neg, hvelt1]
  have hback : GExp (cov := cov) hmet m ((ℓ / 2) • (-velt)) = q₁ := by
    rw [hmdef, hGdef, hveltdef]
    exact (GExp_neg_curveVelocity_geodCurve (cov := cov) hmet hξ1 hℓnn (by linarith) (by linarith)
      (by linarith) le_rfl).trans (by rw [sub_self]; exact hG0)
  have hfwd : GExp (cov := cov) hmet m ((ℓ / 2) • velt) = q₂ := by
    rw [hmdef, hGdef, hveltdef]
    exact (GExp_add_curveVelocity_geodCurve (cov := cov) hmet hξ1 hℓnn (by linarith) (by linarith)
      (by linarith) (by linarith)).trans (by
        rw [show ℓ / 2 + ℓ / 2 = ℓ from by ring]; exact hGℓ)
  -- the length and angle estimates
  have hmq₁ : Manifold.riemannianEDist I m q₁ = ENNReal.ofReal (ℓ / 2) := by
    rw [Manifold.riemannianEDist_comm]; exact hm0
  have a2 : ℓ / 2 ≤ Real.pi / 2 := by linarith
  have haux : ℓ / 2 + u ≤ Real.pi := by linarith
  have e1 : q₂ = GExp (cov := cov) hmet m ((ℓ / 2) • velt) := hfwd.symm
  have e2 : q₁ = GExp (cov := cov) hmet m ((ℓ / 2) • (-velt)) := hback.symm
  have e5 : Manifold.riemannianEDist I q₂ p = ENNReal.ofReal D := by
    rw [Manifold.riemannianEDist_comm]; exact hq₂
  have e6 : Manifold.riemannianEDist I q₁ p = ENNReal.ofReal D := by
    rw [Manifold.riemannianEDist_comm]; exact hq₁
  exact step1_no_two_max (cov := cov) hmet htor hpinch (z := m) (x₁ := q₂) (x₂ := q₁) (p := p)
    (a := ℓ / 2) (u := u) (D := D) (ux := velt) (up := up)
    (by linarith) a2 hupos haux hDgt hDleπ huD hvelt1 hup1
    e1 e2 hpup hm1 hmq₁ hun e5 e6

end

end Submission.GSCritical
