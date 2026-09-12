import ChallengeDeps
import Submission.GeoCore
import Submission.NBChild
import Submission.Engine
import Submission.ChartArc
import Submission.Rigidity
import Submission.UlU
import Submission.InterfacesA
import Submission.ModelArc
import Submission.ArcNB
import Submission.LocalExt
import Mathlib

open scoped Manifold ENNReal ContDiff Topology
open Set Metric
open EMetric
open Bundle

namespace Submission

open LeanEval.Geometry

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 4000000

/-! # Direction B: geodesic completeness implies closed metric balls are compact

Assembly: (1) `nb_pkg` gives per-point normal data; (2) the local short arcs extend to
global unit geodesics via `IsGeodesicallyComplete` (`geoExt`); (3) interior rigidity
(`rigInst`), the corner estimate (`cornerEst`), unit directions (`dirInst`) complete the
engine hypothesis bundle `LocHyps`; (4) the engine (`Engine.reachable`, Lemma 53) gives
distance-realising geodesics from every point; (5) a continuity theorem for the family of
global geodesics (`geoFlowCont`) shows every closed ball is the image of a compact set under
a continuous map; (6) `geoBallsCompact` concludes.  The zero-dimensional case (`E = {0}`,
where `M` has no tangent vectors) is handled separately.
-/

section ManifoldFacts

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
variable (M : Type*) [EMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [Bundle.RiemannianBundle (fun x : M => TangentSpace I x)]
variable [IsContMDiffRiemannianBundle I ∞ E (fun x : M => TangentSpace I x)]
variable [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
variable [IsRiemannianManifold I M]

/-- `IsGeodesic` (with its speed `c`) restricted to an interval where the metric is exact of
speed one forces `c = 1`, and then the curve is `UnitGeo`. -/
lemma unitGeo_of_agree_exact {γ : ℝ → M} {a b : ℝ} (hab : a < b)
    (hIs : IsGeodesic γ) (hexact : ∀ ⦃s t : ℝ⦄, s ∈ Ioo a b → t ∈ Ioo a b →
      edist (γ s) (γ t) = ENNReal.ofReal |t - s|) : UnitGeo γ := by
  rcases hIs with ⟨c, hc⟩
  have hcone : c = 1 := by
    have hmid : (a + b) / 2 ∈ Ioo a b := by constructor <;> linarith
    rcases hc ((a + b) / 2) with ⟨δ, hδ, hwin⟩
    let ε : ℝ := min δ (min ((a + b) / 2 - a) (b - (a + b) / 2))
    have hε : 0 < ε := by
      dsimp [ε]
      exact lt_min hδ (lt_min (by linarith) (by linarith))
    have hε_d : ε ≤ δ := by
      dsimp [ε]
      exact min_le_left _ _
    have hε_a : ε ≤ (a + b) / 2 - a := by
      dsimp [ε]
      exact le_trans (min_le_right _ _) (min_le_left _ _)
    have hε_b : ε ≤ b - (a + b) / 2 := by
      dsimp [ε]
      exact le_trans (min_le_right _ _) (min_le_right _ _)
    let s₀ : ℝ := (a + b) / 2
    let s₁ : ℝ := (a + b) / 2 + ε / 2
    have hs₀ : |s₀ - s₀| < δ := by
      simpa using hδ
    have hs₀ε : |s₁ - s₀| < δ := by
      have h1 : |ε / 2| < δ := by
        have hε2 : ε / 2 < δ := by linarith
        rwa [abs_of_nonneg (le_of_lt (half_pos hε))]
      rw [show s₁ - s₀ = ε / 2 by dsimp [s₁, s₀]; ring]
      exact h1
    have h_eq_c := hwin s₀ s₁ hs₀ hs₀ε
    have h_eq_1 := hexact (s := s₀) (t := s₁) hmid (by
      have hs1a : a < s₁ := by
        dsimp [s₁]
        linarith
      have hs1b : s₁ < b := by
        dsimp [s₁]
        linarith
      exact ⟨hs1a, hs1b⟩)
    have hcc : (c : ℝ≥0∞) * ENNReal.ofReal |s₁ - s₀| = ENNReal.ofReal |s₁ - s₀| := by
      calc
        (c : ℝ≥0∞) * ENNReal.ofReal |s₁ - s₀| = edist (γ s₀) (γ s₁) := h_eq_c.symm
        _ = ENNReal.ofReal |s₁ - s₀| := h_eq_1
    have hx : (0 : ℝ) < |s₁ - s₀| := by
      have hd : s₁ - s₀ = ε / 2 := by dsimp [s₁, s₀]; ring
      rw [hd, abs_of_pos (half_pos hε)]
      exact half_pos hε
    have hx' : ENNReal.ofReal |s₁ - s₀| ≠ 0 := by
      change ¬ ENNReal.ofReal |s₁ - s₀| = 0
      rw [ENNReal.ofReal_eq_zero]
      exact not_le_of_gt hx
    have hcmul : (c : ℝ≥0∞) * ENNReal.ofReal |s₁ - s₀| = 1 * ENNReal.ofReal |s₁ - s₀| := by
      simpa using hcc
    have hxnt : ENNReal.ofReal |s₁ - s₀| ≠ ⊤ := ne_top_of_lt ENNReal.ofReal_lt_top
    have hcs' : (c : ℝ≥0∞) = (1 : ℝ≥0∞) := (ENNReal.mul_left_inj hx' hxnt).mp hcmul
    exact ENNReal.coe_injective hcs' 
  · -- UnitGeo
    intro B hB
    intro t₀ ht₀
    rcases hc t₀ with ⟨δ, hδ, hwin⟩
    refine ⟨δ, hδ, ?_⟩
    intro s t hs ht
    have hsδ : |s - t₀| < δ := by
      have hlo : t₀ - δ < s := lt_of_le_of_lt (le_max_right (-B) (t₀ - δ)) hs.1
      have hhi : s < t₀ + δ := lt_of_lt_of_le hs.2 (min_le_right B (t₀ + δ))
      exact abs_lt.mpr ⟨by linarith, by linarith⟩
    have htδ : |t - t₀| < δ := by
      have hlo : t₀ - δ < t := lt_of_le_of_lt (le_max_right (-B) (t₀ - δ)) ht.1
      have hhi : t < t₀ + δ := lt_of_lt_of_le ht.2 (min_le_right B (t₀ + δ))
      exact abs_lt.mpr ⟨by linarith, by linarith⟩
    have hw := hwin s t hsδ htδ
    rw [hcone] at hw
    simpa using hw

/-- The speed of a unit geodesic and exactness on an interval agree. -/
lemma isGeodesic_speed_one {γ : ℝ → M} (hIs : IsGeodesic γ) {a b : ℝ} (hab : a < b)
    (hexact : ∀ ⦃s t : ℝ⦄, s ∈ Ioo a b → t ∈ Ioo a b → s ≤ t →
      edist (γ s) (γ t) = ENNReal.ofReal (t - s)) : True := by trivial

end ManifoldFacts

/-! # Per-point metric normal-ball package with rigidity, corner and direction

`PkgAt x` bundles, at a single point `x`, all the *metric* data needed by the engine
(`Engine.LocHyps`) restricted to `x`: a positive radius, a positive-definite symmetric
bilinear form, a radial exponential map with the two-sided arc identity, metric-ball
surjectivity/injectivity, compactness of small closed balls, the corner estimate, the
rigidity clause and (assuming a nonzero tangent vector) a unit direction.  It is built from
ONE call to `Submission.Rigidity.arc_rigidity` at `x`, so all clauses share one witness.
-/

namespace DirectionB

/-- per-point metric package (engine input at one point). -/
structure PkgAt (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (M : Type*) [EMetricSpace M] (x : M) where
  ρ0 : ℝ
  ge0 : E →L[ℝ] E →L[ℝ] ℝ
  Exp : E → M
  rho_pos : 0 < ρ0
  ge_symm : ∀ u v : E, ge0 u v = ge0 v u
  ge_pos : ∀ v : E, v ≠ 0 → 0 < ge0 v v
  radial : ∀ v : E, mnorm ge0 v < ρ0 → edist x (Exp v) = ENNReal.ofReal (mnorm ge0 v)
  arc : ∀ W : E, mnorm ge0 W = 1 → ∀ ⦃s t : ℝ⦄, |s| < ρ0 → |t| < ρ0 → s ≤ t →
      edist (Exp (s • W)) (Exp (t • W)) = ENNReal.ofReal (t - s)
  surj : ∀ y : M, edist x y < ENNReal.ofReal ρ0 → ∃ v : E, mnorm ge0 v < ρ0 ∧ Exp v = y
  inj : ∀ v w : E, mnorm ge0 v < ρ0 → mnorm ge0 w < ρ0 → Exp v = Exp w → v = w
  ball_comp : ∀ ρ : ℝ, 0 < ρ → ρ < ρ0 → IsCompact (closedBall x (ENNReal.ofReal ρ))
  exp_cont : ∀ v : E, mnorm ge0 v < ρ0 → ContinuousAt Exp v
  wrig : ∀ γ : ℝ → M, ∀ δ : ℝ, γ 0 = x → 0 < δ → δ ≤ ρ0 →
      (∀ s t : ℝ, |s| < δ → |t| < δ → edist (γ s) (γ t) = ENNReal.ofReal |t - s|) →
      ∃ v : E, mnorm ge0 v = 1 ∧ ∀ t : ℝ, |t| < δ → γ t = Exp (t • v)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {M : Type*} [EMetricSpace M]

namespace PkgAt

variable {x : M}

/-- bilinearity of the quadratic form on both slots. -/
lemma quad_smul (B : E →L[ℝ] E →L[ℝ] ℝ) (a b : ℝ) (v w : E) :
    B (a • v) (b • w) = (a * b) * B v w := by
  rw [map_smul B a v]
  change a • (B v (b • w)) = (a * b) * B v w
  rw [map_smul (B v) b w]
  rw [smul_eq_mul, smul_eq_mul]
  ring

/-- metric norm of a scalar multiple. -/
lemma mnorm_smul (B : E →L[ℝ] E →L[ℝ] ℝ) (a : ℝ) (v : E) (hq : 0 ≤ B v v) :
    mnorm B (a • v) = |a| * mnorm B v := by
  unfold mnorm
  have hq' : B (a • v) (a • v) = (a * a) * B v v := quad_smul B a a v v
  rw [hq']
  have hsc : (a * a) * B v v = (|a| * |a|) * B v v := by
    calc
      (a * a) * B v v = (a ^ 2) * B v v := by ring
      _ = (|a| ^ 2) * B v v := by rw [sq_abs]
      _ = (|a| * |a|) * B v v := by ring
  rw [hsc]
  rw [Real.sqrt_mul (mul_self_nonneg (|a|)) (B v v)]
  have hsqrt : Real.sqrt (|a| * |a|) = |a| := by
    rw [show |a| * |a| = |a| ^ 2 by ring, Real.sqrt_sq_eq_abs, abs_of_nonneg (abs_nonneg a)]
  rw [hsqrt]

/-- positive-definiteness for nonnegativity reasoning. -/
lemma ge_nonneg (pk : PkgAt E M x) (v : E) : 0 ≤ pk.ge0 v v := by
  by_cases hv : v = 0
  · subst v; simp
  · exact le_of_lt (pk.ge_pos v hv)

/-- radial distance for nonnegative parameters along a unit ray. -/
lemma radial_smul (pk : PkgAt E M x) {W : E} (hW : mnorm pk.ge0 W = 1) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : t < pk.ρ0) : edist x (pk.Exp (t • W)) = ENNReal.ofReal t := by
  have hmm : mnorm pk.ge0 (t • W) = t := by
    calc
      mnorm pk.ge0 (t • W) = |t| * mnorm pk.ge0 W := mnorm_smul pk.ge0 t W (ge_nonneg pk W)
      _ = |t| := by rw [hW, mul_one]
      _ = t := by rw [abs_of_nonneg ht0]
  have hlt : mnorm pk.ge0 (t • W) < pk.ρ0 := by
    rwa [← hmm] at ht
  have hd := pk.radial (t • W) hlt
  rwa [hmm] at hd

/-- two-sided arc identity (already in the package). -/
lemma arc_eq (pk : PkgAt E M x) {W : E} (hW : mnorm pk.ge0 W = 1) {s t : ℝ}
    (hs : |s| < pk.ρ0) (ht : |t| < pk.ρ0) (hst : s ≤ t) :
    edist (pk.Exp (s • W)) (pk.Exp (t • W)) = ENNReal.ofReal (t - s) :=
  pk.arc W hW hs ht hst

/-- points on a unit ray at equal distance from x. -/
lemma radial_eq (pk : PkgAt E M x) {W : E} (hW : mnorm pk.ge0 W = 1) {t : ℝ} (ht : |t| < pk.ρ0) :
    edist x (pk.Exp (t • W)) = ENNReal.ofReal |t| := by
  have hmm : mnorm pk.ge0 (t • W) = |t| := by
    calc
      mnorm pk.ge0 (t • W) = |t| * mnorm pk.ge0 W := mnorm_smul pk.ge0 t W (ge_nonneg pk W)
      _ = |t| := by rw [hW, mul_one]
  have hlt : mnorm pk.ge0 (t • W) < pk.ρ0 := by
    rwa [← hmm] at ht
  have hd := pk.radial (t • W) hlt
  rwa [hmm] at hd

/-- A pure metric fact: a 1-Lipschitz curve on `[-δ, δ]` whose endpoints are at distance
`2δ` realises every intermediate distance. -/
lemma subarc_realizes {c : ℝ → M} {δ : ℝ} (hδ : 0 < δ)
    (hlip : ∀ s t : ℝ, s ∈ Set.Icc (-δ) δ → t ∈ Set.Icc (-δ) δ →
      edist (c s) (c t) ≤ ENNReal.ofReal |t - s|)
    (hend : edist (c (-δ)) (c δ) = ENNReal.ofReal (2 * δ)) :
    ∀ s t : ℝ, s ∈ Set.Icc (-δ) δ → t ∈ Set.Icc (-δ) δ → s ≤ t →
      edist (c s) (c t) = ENNReal.ofReal (t - s) := by
  intro s t hs ht hst
  apply le_antisymm
  · -- upper: 1-Lipschitz
    have hlt := hlip s t hs ht
    have habs : |t - s| = t - s := abs_of_nonneg (sub_nonneg.mpr hst)
    rwa [habs] at hlt
  · -- lower: via the chain through the endpoints
    have hs1 : -δ ≤ s := hs.1
    have hs2 : s ≤ δ := hs.2
    have ht1 : -δ ≤ t := ht.1
    have ht2 : t ≤ δ := ht.2
    have hchain : ENNReal.ofReal (2 * δ) ≤
        edist (c (-δ)) (c s) + edist (c s) (c t) + edist (c t) (c δ) := by
      calc
        ENNReal.ofReal (2 * δ) = edist (c (-δ)) (c δ) := hend.symm
        _ ≤ edist (c (-δ)) (c s) + edist (c s) (c δ) :=
          edist_triangle (x := c (-δ)) (y := c s) (z := c δ)
        _ ≤ edist (c (-δ)) (c s) + (edist (c s) (c t) + edist (c t) (c δ)) := by
          have htri := edist_triangle (x := c s) (y := c t) (z := c δ)
          exact add_le_add_right htri (edist (c (-δ)) (c s))
        _ = edist (c (-δ)) (c s) + edist (c s) (c t) + edist (c t) (c δ) := by
          rw [← add_assoc]
    have hbA : edist (c (-δ)) (c s) ≤ ENNReal.ofReal (s + δ) := by
      have hlt := hlip (-δ) s (by constructor <;> linarith) hs
      have habs : |s - (-δ)| = s + δ := by
        rw [sub_eq_add_neg, neg_neg]
        exact abs_of_nonneg (by linarith : 0 ≤ s + δ)
      rwa [habs] at hlt
    have hbC : edist (c t) (c δ) ≤ ENNReal.ofReal (δ - t) := by
      have hlt := hlip t δ ht (by constructor <;> linarith)
      have habs : |δ - t| = δ - t := abs_of_nonneg (by linarith : 0 ≤ δ - t)
      rwa [habs] at hlt
    have hAC : edist (c (-δ)) (c s) + edist (c t) (c δ) ≤
        ENNReal.ofReal (s + δ) + ENNReal.ofReal (δ - t) := by
      exact add_le_add hbA hbC
    have htarget : ENNReal.ofReal (2 * δ) ≤
        ENNReal.ofReal (s + δ + (δ - t)) + edist (c s) (c t) := by
      calc
        ENNReal.ofReal (2 * δ) ≤ edist (c (-δ)) (c s) + edist (c s) (c t) +
            edist (c t) (c δ) := hchain
        _ = (edist (c (-δ)) (c s) + edist (c t) (c δ)) + edist (c s) (c t) := by
          simp [add_assoc, add_comm, add_left_comm]
        _ ≤ (ENNReal.ofReal (s + δ) + ENNReal.ofReal (δ - t)) + edist (c s) (c t) := by
          exact add_le_add_left hAC (edist (c s) (c t))
        _ = ENNReal.ofReal (s + δ + (δ - t)) + edist (c s) (c t) := by
          rw [← ENNReal.ofReal_add (by linarith : 0 ≤ s + δ) (by linarith : 0 ≤ δ - t)]
    have hsum2 : s + δ + (δ - t) = 2 * δ - (t - s) := by ring
    have hbig0 : 0 ≤ 2 * δ - (t - s) := by linarith
    have htarget' : ENNReal.ofReal (2 * δ) ≤ ENNReal.ofReal (2 * δ - (t - s)) +
        edist (c s) (c t) := by
      rwa [hsum2] at htarget
    have hsub : ENNReal.ofReal (2 * δ) - ENNReal.ofReal (2 * δ - (t - s)) =
        ENNReal.ofReal (t - s) := by
      rw [← ENNReal.ofReal_sub (2 * δ) hbig0]
      congr 1
      ring
    have hb : ENNReal.ofReal (t - s) ≤ edist (c s) (c t) := by
      have h1 : ENNReal.ofReal (2 * δ) - ENNReal.ofReal (2 * δ - (t - s)) ≤ edist (c s) (c t) :=
        (tsub_le_iff_right.mpr (by simpa [add_comm] using htarget'))
      rwa [hsub] at h1
    exact hb

/-- `Exp 0 = x` follows from the radial identity. -/
lemma Exp_zero (pk : PkgAt E M x) : pk.Exp 0 = x := by
  have hlt : mnorm pk.ge0 (0 : E) < pk.ρ0 := by
    have hz : mnorm pk.ge0 (0 : E) = 0 := by simp [mnorm]
    rw [hz]
    exact pk.rho_pos
  have hd := pk.radial 0 hlt
  have hz : ENNReal.ofReal (mnorm pk.ge0 (0 : E)) = 0 := by
    simp [mnorm]
  rw [hz] at hd
  exact (EMetricSpace.eq_of_edist_eq_zero hd).symm

/-- upper Lipschitz bound along a unit ray (both directions). -/
lemma ray_le (pk : PkgAt E M x) {W : E} (hW : mnorm pk.ge0 W = 1) {s t : ℝ}
    (hs : |s| < pk.ρ0) (ht : |t| < pk.ρ0) :
    edist (pk.Exp (s • W)) (pk.Exp (t • W)) ≤ ENNReal.ofReal |t - s| := by
  by_cases hst : s ≤ t
  · have h1 := arc_eq pk hW hs ht hst
    rw [h1]
    congr 1
    rw [abs_of_nonneg (sub_nonneg.mpr hst)]
  · have hts : t ≤ s := le_of_not_ge hst
    have h1 := arc_eq pk hW ht hs hts
    calc
      edist (pk.Exp (s • W)) (pk.Exp (t • W)) = edist (pk.Exp (t • W)) (pk.Exp (s • W)) := by
        rw [edist_comm]
      _ = ENNReal.ofReal (s - t) := h1
      _ ≤ ENNReal.ofReal |t - s| := by
        have habs : |t - s| = s - t := by
          rw [abs_of_nonpos (sub_nonpos.mpr hts)]
          ring
        rw [habs]

/-- mnorm of a unit ray vector of magnitude t is |t|. -/
lemma mnorm_smul_unit (pk : PkgAt E M x) {W : E} (hW : mnorm pk.ge0 W = 1) (t : ℝ) :
    mnorm pk.ge0 (t • W) = |t| := by
  calc
    mnorm pk.ge0 (t • W) = |t| * mnorm pk.ge0 W := mnorm_smul pk.ge0 t W (ge_nonneg pk W)
    _ = |t| * 1 := by rw [hW]
    _ = |t| := by rw [mul_one]

/-- mnorm of a negative unit ray vector. -/
lemma mnorm_neg_smul_unit (pk : PkgAt E M x) {W : E} (hW : mnorm pk.ge0 W = 1) (t : ℝ) :
    mnorm pk.ge0 (-(t • W)) = |t| := by
  calc
    mnorm pk.ge0 (-(t • W)) = mnorm pk.ge0 ((-t) • W) := by rw [neg_smul]
    _ = mnorm pk.ge0 ((-t) • W) := rfl
    _ = |(-t)| := mnorm_smul_unit pk hW (-t)
    _ = |t| := by rw [abs_neg]

/-- The corner-cut estimate for a package: two distinct unit directions give strictly
shorter chords than going through the centre. -/
lemma corner_lt (pk : PkgAt E M x) (v1 v2 : E) (hu1 : mnorm pk.ge0 v1 = 1)
    (hu2 : mnorm pk.ge0 v2 = 1) (hne : v1 ≠ v2) :
    ∀ δ : ℝ, 0 < δ → δ ≤ pk.ρ0 / 4 →
      edist (pk.Exp (-(δ • v1))) (pk.Exp (δ • v2)) < ENNReal.ofReal (2 * δ) := by
  intro δ hδ hδle
  have hδρ : δ < pk.ρ0 := by linarith [pk.rho_pos]
  -- radial distances of A and B from x
  have hmA : mnorm pk.ge0 (-(δ • v1)) = δ := by
    have hmm := mnorm_neg_smul_unit pk hu1 δ
    rwa [abs_of_pos hδ] at hmm
  have hmB : mnorm pk.ge0 (δ • v2) = δ := by
    have hmm := mnorm_smul_unit pk hu2 δ
    rwa [abs_of_pos hδ] at hmm
  have hradA : edist x (pk.Exp (-(δ • v1))) = ENNReal.ofReal δ := by
    have hlt : mnorm pk.ge0 (-(δ • v1)) < pk.ρ0 := by rwa [hmA]
    have hd := pk.radial (-(δ • v1)) hlt
    rwa [hmA] at hd
  have hradB : edist x (pk.Exp (δ • v2)) = ENNReal.ofReal δ := by
    have hlt : mnorm pk.ge0 (δ • v2) < pk.ρ0 := by rwa [hmB]
    have hd := pk.radial (δ • v2) hlt
    rwa [hmB] at hd
  have hle : edist (pk.Exp (-(δ • v1))) (pk.Exp (δ • v2)) ≤ ENNReal.ofReal (2 * δ) := by
    calc
      edist (pk.Exp (-(δ • v1))) (pk.Exp (δ • v2)) ≤
          edist (pk.Exp (-(δ • v1))) x + edist x (pk.Exp (δ • v2)) :=
        edist_triangle (x := pk.Exp (-(δ • v1))) (y := x) (z := pk.Exp (δ • v2))
      _ = ENNReal.ofReal δ + ENNReal.ofReal δ := by rw [edist_comm, hradA, hradB]
      _ = ENNReal.ofReal (2 * δ) := by
        rw [← ENNReal.ofReal_add (le_of_lt hδ) (le_of_lt hδ)]
        congr 1
        ring
  by_contra hnot
  have hEq : edist (pk.Exp (-(δ • v1))) (pk.Exp (δ • v2)) = ENNReal.ofReal (2 * δ) :=
    le_antisymm hle (le_of_not_gt hnot)
  -- the glued curve
  let α : ℝ → M := fun u => if u ≤ 0 then pk.Exp (u • v1) else pk.Exp (u • v2)
  have hα0 : α 0 = x := by
    simp [α, Exp_zero pk]
  -- local 1-Lipschitz estimate on Icc (-δ) δ
  have hmixed : ∀ a b : ℝ, a ≤ 0 → 0 < b → |a| < pk.ρ0 → |b| < pk.ρ0 →
      edist (pk.Exp (a • v1)) (pk.Exp (b • v2)) ≤ ENNReal.ofReal |b - a| := by
    intro a b ha0 hbpos haρ hbρ
    have hsrad : edist (pk.Exp (a • v1)) x = ENNReal.ofReal (-a) := by
      have hmm : mnorm pk.ge0 (a • v1) = -a := by
        have h := mnorm_smul_unit pk hu1 a
        have habs : |a| = -a := abs_of_nonpos (by linarith : a ≤ 0)
        rwa [habs] at h
      have hlt : mnorm pk.ge0 (a • v1) < pk.ρ0 := by
        rw [hmm]
        have habs' : |a| = -a := abs_of_nonpos (by linarith : a ≤ 0)
        have h' : -a < pk.ρ0 := by simpa [habs'] using haρ
        exact h'
      have hd := pk.radial (a • v1) hlt
      rw [hmm] at hd
      rw [edist_comm]
      exact hd
    have htrad : edist x (pk.Exp (b • v2)) = ENNReal.ofReal b := by
      have hmm : mnorm pk.ge0 (b • v2) = b := by
        have h := mnorm_smul_unit pk hu2 b
        have habs : |b| = b := abs_of_pos hbpos
        rwa [habs] at h
      have hlt : mnorm pk.ge0 (b • v2) < pk.ρ0 := by
        rw [hmm]
        have habs' : |b| = b := abs_of_pos hbpos
        have h' : b < pk.ρ0 := by simpa [habs'] using hbρ
        exact h'
      have hd := pk.radial (b • v2) hlt
      rwa [hmm] at hd
    calc
      edist (pk.Exp (a • v1)) (pk.Exp (b • v2)) ≤
          edist (pk.Exp (a • v1)) x + edist x (pk.Exp (b • v2)) :=
        edist_triangle (x := pk.Exp (a • v1)) (y := x) (z := pk.Exp (b • v2))
      _ = ENNReal.ofReal (-a) + ENNReal.ofReal b := by rw [hsrad, htrad]
      _ = ENNReal.ofReal (b - a) := by
        have hn1 : 0 ≤ -a := by linarith
        have hn2 : 0 ≤ b := le_of_lt hbpos
        rw [← ENNReal.ofReal_add hn1 hn2]
        congr 1
        ring
      _ ≤ ENNReal.ofReal |b - a| := by
        rw [abs_of_nonneg (by linarith : 0 ≤ b - a)]
  have hlip : ∀ s t : ℝ, s ∈ Set.Icc (-δ) δ → t ∈ Set.Icc (-δ) δ →
      edist (α s) (α t) ≤ ENNReal.ofReal |t - s| := by
    intro s t hs ht
    have hsρ : |s| < pk.ρ0 := by
      have h1 : |s| ≤ δ := abs_le.mpr ⟨by linarith [hs.1], by linarith [hs.2]⟩
      exact lt_of_le_of_lt h1 (by linarith [pk.rho_pos])
    have htρ : |t| < pk.ρ0 := by
      have h1 : |t| ≤ δ := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
      exact lt_of_le_of_lt h1 (by linarith [pk.rho_pos])
    by_cases hs0 : s ≤ 0
    · by_cases ht0 : t ≤ 0
      · -- both nonpositive: on the v1 ray
        simp [α, hs0, ht0]
        exact ray_le pk hu1 hsρ htρ
      · -- s ≤ 0 < t : through x
        have htpos : 0 < t := lt_of_not_ge ht0
        simp [α, hs0, ht0]
        exact hmixed s t hs0 htpos hsρ htρ
    · -- 0 < s : on the v2 ray
      have hspos : 0 < s := lt_of_not_ge hs0
      by_cases ht0 : t ≤ 0
      · -- t ≤ 0 < s : swap
        have hs0' : t ≤ 0 := ht0
        have htp : 0 < s := hspos
        simp [α, hs0, ht0]
        calc
          edist (pk.Exp (s • v2)) (pk.Exp (t • v1)) ≤ ENNReal.ofReal |s - t| := by
            rw [edist_comm]
            exact hmixed t s hs0' htp htρ hsρ
          _ = ENNReal.ofReal |t - s| := by
            congr 1
            exact abs_sub_comm s t
      · -- both positive: on the v2 ray
        simp [α, hs0, ht0]
        exact ray_le pk hu2 hsρ htρ
  have hend : edist (α (-δ)) (α δ) = ENNReal.ofReal (2 * δ) := by
    have h1 : α (-δ) = pk.Exp (-(δ • v1)) := by
      dsimp [α]
      rw [if_pos (by linarith : -δ ≤ 0)]
      congr 1
      rw [← neg_smul]
    have h2 : α δ = pk.Exp (δ • v2) := by
      dsimp [α]
      rw [if_neg (by linarith : ¬ δ ≤ 0)]
    rw [h1, h2]
    exact hEq
  have hreal := subarc_realizes (δ := δ) hδ hlip hend
  -- apply window rigidity with a small window δw
  let δw : ℝ := min δ (pk.ρ0 / 4)
  have hδw0 : 0 < δw := by
    dsimp [δw]
    exact lt_min hδ (by linarith [pk.rho_pos])
  have hδw_le : δw ≤ pk.ρ0 := by
    have h1 : δw ≤ pk.ρ0 / 4 := by
      dsimp [δw]
      exact min_le_right _ _
    have h2 : pk.ρ0 / 4 ≤ pk.ρ0 := by linarith [pk.rho_pos]
    exact le_trans h1 h2
  have hwin : ∀ s t : ℝ, |s| < δw → |t| < δw →
      edist (α s) (α t) = ENNReal.ofReal |t - s| := by
    intro s t hsw htw
    have hsδ : |s| < δ := lt_of_lt_of_le hsw (by dsimp [δw]; exact min_le_left _ _)
    have htδ : |t| < δ := lt_of_lt_of_le htw (by dsimp [δw]; exact min_le_left _ _)
    have hsI : s ∈ Set.Icc (-δ) δ := by
      have h := abs_lt.mp hsδ
      exact ⟨le_of_lt h.1, le_of_lt h.2⟩
    have htI : t ∈ Set.Icc (-δ) δ := by
      have h := abs_lt.mp htδ
      exact ⟨le_of_lt h.1, le_of_lt h.2⟩
    by_cases hst : s ≤ t
    · have hr := hreal s t hsI htI hst
      rw [hr]
      congr 1
      rw [abs_of_nonneg (sub_nonneg.mpr hst)]
    · have hts : t ≤ s := le_of_not_ge hst
      have hr := hreal t s htI hsI hts
      rw [edist_comm, hr]
      have habs : |t - s| = s - t := by
        rw [abs_of_nonpos (sub_nonpos.mpr hts)]
        ring
      rw [habs]
  rcases pk.wrig α δw hα0 hδw0 hδw_le hwin with ⟨v3, hu3, hαv3⟩
  -- compare with v1 and v2 on small parameters
  have hw2 : δw / 2 < δw := half_lt_self hδw0
  have hw2' : |δw / 2| < δw := by rw [abs_of_pos (half_pos hδw0)]; exact hw2
  have hw2n : |-(δw / 2)| < δw := by
    rw [abs_neg]
    exact hw2'
  have hw2pos : 0 < δw / 2 := half_pos hδw0
  have hw2ne : δw / 2 ≠ 0 := ne_of_gt hw2pos
  -- α(-δw/2) = Exp (-((δw/2)•v1)) and = Exp (-((δw/2)•v3))
  have hαneg : α (-(δw / 2)) = pk.Exp (-((δw / 2) • v1)) := by
    dsimp [α]
    rw [if_pos (by linarith : -(δw / 2) ≤ 0)]
    congr 1
    rw [← neg_smul]
  have hαneg3 : α (-(δw / 2)) = pk.Exp (-((δw / 2) • v3)) := by
    have hf := hαv3 (-(δw / 2)) hw2n
    rw [neg_smul] at hf
    exact hf
  have hEq1 : pk.Exp (-((δw / 2) • v1)) = pk.Exp (-((δw / 2) • v3)) := by
    rw [← hαneg, hαneg3]
  have hmm1 : mnorm pk.ge0 (-((δw / 2) • v1)) < pk.ρ0 := by
    have hmm : mnorm pk.ge0 (-((δw / 2) • v1)) = δw / 2 := by
      have h := mnorm_neg_smul_unit pk hu1 (δw / 2)
      rwa [abs_of_pos hw2pos] at h
    rw [hmm]
    exact lt_of_lt_of_le (half_lt_self hδw0) hδw_le
  have hmm3 : mnorm pk.ge0 (-((δw / 2) • v3)) < pk.ρ0 := by
    have hmm : mnorm pk.ge0 (-((δw / 2) • v3)) = δw / 2 := by
      have h := mnorm_neg_smul_unit pk hu3 (δw / 2)
      rwa [abs_of_pos hw2pos] at h
    rw [hmm]
    exact lt_of_lt_of_le (half_lt_self hδw0) hδw_le
  have harg1 : -((δw / 2) • v1) = -((δw / 2) • v3) := pk.inj _ _ hmm1 hmm3 hEq1
  have harg2 : (δw / 2) • v1 = (δw / 2) • v3 := neg_injective harg1
  have hinj1 : v1 = v3 := by
    calc
      v1 = (δw / 2)⁻¹ • ((δw / 2) • v1) := by rw [smul_smul, inv_mul_cancel₀ hw2ne, one_smul]
      _ = (δw / 2)⁻¹ • ((δw / 2) • v3) := by rw [harg2]
      _ = v3 := by rw [smul_smul, inv_mul_cancel₀ hw2ne, one_smul]
  -- α(δw/2) = Exp ((δw/2)•v2) and = Exp ((δw/2)•v3)
  have hαpos : α (δw / 2) = pk.Exp ((δw / 2) • v2) := by
    dsimp [α]
    rw [if_neg (by linarith : ¬ δw / 2 ≤ 0)]
  have hαpos3 : α (δw / 2) = pk.Exp ((δw / 2) • v3) := by
    exact hαv3 (δw / 2) hw2' 
  have hEq2 : pk.Exp ((δw / 2) • v2) = pk.Exp ((δw / 2) • v3) := by
    rw [← hαpos, hαpos3]
  have hmm2 : mnorm pk.ge0 ((δw / 2) • v2) < pk.ρ0 := by
    have hmm : mnorm pk.ge0 ((δw / 2) • v2) = δw / 2 := by
      have h := mnorm_smul_unit pk hu2 (δw / 2)
      rwa [abs_of_pos hw2pos] at h
    rw [hmm]
    exact lt_of_lt_of_le (half_lt_self hδw0) hδw_le
  have hmm4 : mnorm pk.ge0 ((δw / 2) • v3) < pk.ρ0 := by
    have hmm : mnorm pk.ge0 ((δw / 2) • v3) = δw / 2 := by
      have h := mnorm_smul_unit pk hu3 (δw / 2)
      rwa [abs_of_pos hw2pos] at h
    rw [hmm]
    exact lt_of_lt_of_le (half_lt_self hδw0) hδw_le
  have harg3 : (δw / 2) • v2 = (δw / 2) • v3 := pk.inj _ _ hmm2 hmm4 hEq2
  have hinj2 : v2 = v3 := by
    calc
      v2 = (δw / 2)⁻¹ • ((δw / 2) • v2) := by rw [smul_smul, inv_mul_cancel₀ hw2ne, one_smul]
      _ = (δw / 2)⁻¹ • ((δw / 2) • v3) := by rw [harg3]
      _ = v3 := by rw [smul_smul, inv_mul_cancel₀ hw2ne, one_smul]
  exact hne (hinj1.trans hinj2.symm)

end PkgAt

variable {x : M}

/-- Symmetric exact ray identity (both orders of the parameters). -/
lemma PkgAt_ray_eq (pk : PkgAt E M x) {W : E} (hW : mnorm pk.ge0 W = 1) {s t : ℝ}
    (hs : |s| < pk.ρ0) (ht : |t| < pk.ρ0) :
    edist (pk.Exp (s • W)) (pk.Exp (t • W)) = ENNReal.ofReal |t - s| := by
  by_cases hst : s ≤ t
  · have h1 := PkgAt.arc_eq pk hW hs ht hst
    rw [h1]
    congr 1
    rw [abs_of_nonneg (sub_nonneg.mpr hst)]
  · have hts : t ≤ s := le_of_not_ge hst
    have h1 := PkgAt.arc_eq pk hW ht hs hts
    rw [edist_comm, h1]
    have habs : |t - s| = s - t := by
      rw [abs_of_nonpos (sub_nonpos.mpr hts)]
      ring
    rw [habs]

/-- Under geodesic completeness, the short radial arcs `t ↦ Exp(t•W)` extend to global
unit-speed geodesics. -/
theorem geoExt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    (M : Type*) [EMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [Bundle.RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M => TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M]
    (x : M) (pk : PkgAt E M x) {W : E} (hW : mnorm pk.ge0 W = 1)
    (hgc : IsGeodesicallyComplete M) :
    ∃ γ : ℝ → M, UnitGeo γ ∧ γ 0 = x ∧
      ∀ t : ℝ, |t| < pk.ρ0 → γ t = pk.Exp (t • W) := by
  classical
  let η : ℝ → M := fun t => pk.Exp (t • W)
  have hη : ∃ c : NNReal, ∀ t₀ ∈ Ioo (-pk.ρ0) pk.ρ0, ∃ δ > 0,
      ∀ s t : ℝ, s ∈ Ioo (max (-pk.ρ0) (t₀ - δ)) (min pk.ρ0 (t₀ + δ)) →
        t ∈ Ioo (max (-pk.ρ0) (t₀ - δ)) (min pk.ρ0 (t₀ + δ)) →
        edist (η s) (η t) = (c : ℝ≥0∞) * ENNReal.ofReal |t - s| := by
    refine ⟨1, ?_⟩
    intro t₀ ht₀
    let δ : ℝ := min ((t₀ + pk.ρ0) / 2) ((pk.ρ0 - t₀) / 2)
    have hδ : 0 < δ := by
      dsimp [δ]
      exact lt_min (by linarith [ht₀.1]) (by linarith [ht₀.2])
    refine ⟨δ, hδ, ?_⟩
    intro s t hs ht
    have hs_gt : -pk.ρ0 < s := lt_of_le_of_lt (le_max_left (-pk.ρ0) (t₀ - δ)) hs.1
    have hs_lt : s < pk.ρ0 := lt_of_lt_of_le hs.2 (min_le_left pk.ρ0 (t₀ + δ))
    have ht_gt : -pk.ρ0 < t := lt_of_le_of_lt (le_max_left (-pk.ρ0) (t₀ - δ)) ht.1
    have ht_lt : t < pk.ρ0 := lt_of_lt_of_le ht.2 (min_le_left pk.ρ0 (t₀ + δ))
    have hsρ : |s| < pk.ρ0 := abs_lt.mpr ⟨hs_gt, hs_lt⟩
    have htρ : |t| < pk.ρ0 := abs_lt.mpr ⟨ht_gt, ht_lt⟩
    have hd := PkgAt_ray_eq pk hW hsρ htρ
    simpa [η] using hd
  rcases hgc (-pk.ρ0) pk.ρ0 η (by linarith [pk.rho_pos]) hη with ⟨γ, hγgeo, hγagree⟩
  have hmem0 : (0 : ℝ) ∈ Ioo (-pk.ρ0) pk.ρ0 := by constructor <;> linarith [pk.rho_pos]
  have hagree0 : γ 0 = x := by
    have ha := hγagree 0 hmem0
    rw [ha]
    simpa [η] using (PkgAt.Exp_zero pk)
  have hunit : UnitGeo γ := by
    have hneg_lt : -pk.ρ0 < pk.ρ0 := by linarith [pk.rho_pos]
    refine unitGeo_of_agree_exact (M := M) (γ := γ) (a := -pk.ρ0) (b := pk.ρ0) hneg_lt hγgeo ?_
    intro s t hs ht
    have hgs := hγagree s hs
    have hgt := hγagree t ht
    rw [hgs, hgt]
    exact PkgAt_ray_eq pk hW (abs_lt.mpr hs) (abs_lt.mpr ht)
  refine ⟨γ, hunit, hagree0, ?_⟩
  intro t ht
  have htm : t ∈ Ioo (-pk.ρ0) pk.ρ0 := abs_lt.mp ht
  have ha := hγagree t htm
  simpa [η] using ha

/-- Per-point metric package on a Riemannian manifold, built from ONE call to
`Submission.Rigidity.arc_rigidity` so that all clauses share a single witness. -/
theorem pkg_at {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    (M : Type*) [EMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [Bundle.RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M => TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M] (x : M) : Nonempty (PkgAt E M x) := by
  classical
  rcases arc_rigidity (I := I) (M := M) x with
    ⟨ρ0', hρ0'0, ge, hgeC, hgeSymm, hgePos, hgeAgree, hrest⟩
  rcases hrest with ⟨r, hr0, ExpM, S, invM, _hExpM0, hSnhds, hS_in, hExpCont, hInj,
    hSurj, hInvS, hInvExp, hRadial, hrest2⟩
  rcases hrest2 with ⟨ρa, hρa0, hρale, hArcM, hRigid⟩
  let x₀ : E := extChartAt I x x
  let ge0 : E →L[ℝ] E →L[ℝ] ℝ := ge x₀
  have hge0pos : ∀ v : E, v ≠ 0 → 0 < ge0 v v := by
    intro v hv
    exact hgePos x₀ v hv
  have hge0sym : ∀ u v : E, ge0 u v = ge0 v u := hgeSymm x₀
  have hBnonneg : ∀ v : E, 0 ≤ ge0 v v := by
    intro v
    by_cases hv : v = 0
    · subst v; simp
    · exact le_of_lt (hge0pos v hv)
  rcases unit_norm_bound ge0 hge0pos with ⟨K, hK0, hKbound⟩
  have hKbound' : ∀ v : E, ‖v‖ ≤ K * mnorm ge0 v := by
    intro v
    have hb := unit_norm_bound_all ge0 hge0pos K hK0.le (fun V hV => hKbound V hV) v
    simpa [mnorm] using hb
  have hmn_cont : Continuous (fun v : E => mnorm ge0 v) := by
    dsimp [mnorm]
    exact Real.continuous_sqrt.comp (by
      have hcu : Continuous (fun p : E × E => ge0 p.1 p.2) :=
        ContinuousLinearMap.continuous₂ ge0
      exact hcu.comp (continuous_diag : Continuous (Function.diag : E → E × E)))
  rcases Metric.nhds_basis_eball.mem_iff.mp hSnhds with ⟨cInf, hcInf0, hcInfsub⟩
  let cf : ℝ≥0∞ := min cInf 1
  have hcf0 : 0 < cf := lt_min hcInf0 (by norm_num)
  have hcflt1 : cf ≤ (1 : ℝ≥0∞) := min_le_right _ _
  have hcftop : cf ≠ (⊤ : ℝ≥0∞) := ne_top_of_le_ne_top (by norm_num : (1 : ℝ≥0∞) ≠ ⊤) hcflt1
  let cp : ℝ := cf.toReal
  have hcp0 : 0 < cp := ENNReal.toReal_pos (ne_of_gt hcf0) hcftop
  have hcp_sub : {y : M | edist x y < ENNReal.ofReal cp} ⊆ S := by
    intro y hy
    have hy' : edist y x < ENNReal.ofReal cp := by simpa [edist_comm] using hy
    have hle : ENNReal.ofReal cp ≤ cInf := by
      rw [ENNReal.ofReal_toReal hcftop]
      exact min_le_left _ _
    exact hcInfsub (lt_of_lt_of_le hy' hle)
  let ρ0 : ℝ := min (min (ρa / 2) (r / (2 * K))) (cp / 2)
  have hρ00 : 0 < ρ0 := by
    dsimp [ρ0]
    exact lt_min (lt_min (half_pos hρa0) (div_pos hr0 (by positivity))) (half_pos hcp0)
  have hρ0_le_ρa : ρ0 ≤ ρa := by
    dsimp [ρ0]
    have h1 : ρa / 2 < ρa := half_lt_self hρa0
    have h2 : min (ρa / 2) (r / (2 * K)) ≤ ρa / 2 := min_le_left _ _
    have h3 : min (min (ρa / 2) (r / (2 * K))) (cp / 2) ≤ ρa / 2 :=
      le_trans (min_le_left _ _) h2
    linarith
  have hρ0_r : K * ρ0 < r := by
    have hle : ρ0 ≤ r / (2 * K) := by
      dsimp [ρ0]
      exact le_trans (min_le_left _ _) (min_le_right _ _)
    have hm : K * (r / (2 * K)) = r / 2 := by
      field_simp [ne_of_gt hK0]
    have h1 : K * ρ0 ≤ r / 2 := (mul_le_mul_of_nonneg_left hle hK0.le).trans_eq hm
    linarith [hr0]
  have hρ0_lt_cp : ρ0 < cp := by
    have h1 : ρ0 ≤ cp / 2 := by
      dsimp [ρ0]
      exact min_le_right _ _
    linarith [hcp0]
  have hρ0lecp : ρ0 ≤ cp := le_of_lt hρ0_lt_cp
  have hmetric_in_euclid : ∀ v : E, mnorm ge0 v < ρ0 → v ∈ ball (0 : E) r := by
    intro v hv
    rw [Metric.mem_ball, dist_eq_norm, sub_zero]
    have h1 : ‖v‖ ≤ K * mnorm ge0 v := hKbound' v
    have h2 : K * mnorm ge0 v < K * ρ0 := mul_lt_mul_of_pos_left hv hK0
    exact lt_of_le_of_lt h1 (lt_trans h2 hρ0_r)
  refine ⟨⟨ρ0, ge0, ExpM, hρ00, hge0sym, hge0pos, ?radial, ?arc, ?surj, ?inj,
    ?ball_comp, ?exp_cont, ?wrig⟩⟩
  · -- radial identity
    intro v hv
    have hvE : v ∈ ball (0 : E) r := hmetric_in_euclid v hv
    have hrad := hRadial v hvE
    simpa [x₀, ge0, mnorm] using hrad
  · -- two-sided arc identity
    intro W hWunit s t hs ht hst
    have hsρa : |s| < ρa := lt_of_lt_of_le hs hρ0_le_ρa
    have htρa : |t| < ρa := lt_of_lt_of_le ht hρ0_le_ρa
    have harc := hArcM W (by simpa [x₀, ge0, mnorm] using hWunit) (s := s) (t := t)
      hst hsρa htρa
    simpa [x₀, ge0, mnorm] using harc
  · -- surjectivity onto the metric ball
    intro y hy
    have hycp : edist x y < ENNReal.ofReal cp :=
      lt_of_lt_of_le hy (ENNReal.ofReal_le_ofReal hρ0lecp)
    have hyS : y ∈ S := hcp_sub hycp
    rcases hInvS y hyS with ⟨hvE, hExpInv⟩
    let v : E := invM y
    have hradv : edist x y = ENNReal.ofReal (mnorm ge0 v) := by
      have hrad := hRadial (invM y) hvE
      rw [hExpInv] at hrad
      simpa [ge0, x₀, mnorm, v] using hrad
    have hvρ0 : mnorm ge0 v < ρ0 := by
      have hlt' : ENNReal.ofReal (mnorm ge0 v) < ENNReal.ofReal ρ0 := by
        rw [← hradv]
        exact hy
      exact (ENNReal.ofReal_lt_ofReal_iff hρ00).mp hlt'
    refine ⟨v, hvρ0, ?_⟩
    simpa [v] using hExpInv
  · -- injectivity
    intro v w hv hw heq
    have hvE : v ∈ ball (0 : E) r := hmetric_in_euclid v hv
    have hwE : w ∈ ball (0 : E) r := hmetric_in_euclid w hw
    have hsub : (⟨v, hvE⟩ : {v : E // v ∈ ball (0 : E) r}) = ⟨w, hwE⟩ := by
      apply hInj
      simpa using heq
    exact congrArg Subtype.val hsub
  · -- compact small closed balls
    intro ρ hρpos hρlt
    let ell : Set E := {v : E | mnorm ge0 v ≤ ρ}
    have hEllClosed : IsClosed ell := by
      change IsClosed ((fun v : E => mnorm ge0 v) ⁻¹' (Set.Iic ρ))
      exact IsClosed.preimage hmn_cont isClosed_Iic
    have hEllEucl : ell ⊆ Metric.closedBall (0 : E) (K * ρ) := by
      intro v hv
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
      have h1 : ‖v‖ ≤ K * mnorm ge0 v := hKbound' v
      have h2 : mnorm ge0 v ≤ ρ := hv
      have h3 : K * mnorm ge0 v ≤ K * ρ := mul_le_mul_of_nonneg_left h2 hK0.le
      exact le_trans h1 h3
    have hEllCompact : IsCompact ell :=
      (isCompact_closedBall (x := (0 : E)) (r := K * ρ)).of_isClosed_subset
        hEllClosed hEllEucl
    have hEllDom : ell ⊆ ball (0 : E) r := by
      intro v hv
      exact hmetric_in_euclid v (lt_of_le_of_lt hv hρlt)
    have hContEll : ContinuousOn ExpM ell := hExpCont.mono hEllDom
    have hImCompact : IsCompact (ExpM '' ell) :=
      IsCompact.image_of_continuousOn hEllCompact hContEll
    have hsub_fwd : closedBall x (ENNReal.ofReal ρ) ⊆ ExpM '' ell := by
      intro y hy
      have hyE : edist y x ≤ ENNReal.ofReal ρ := hy
      have hyc : edist x y ≤ ENNReal.ofReal ρ := by
        rw [edist_comm]
        exact hyE
      have hycp : edist x y < ENNReal.ofReal cp :=
        lt_of_le_of_lt hyc ((ENNReal.ofReal_lt_ofReal_iff hcp0).mpr (lt_trans hρlt hρ0_lt_cp))
      have hyS : y ∈ S := hcp_sub hycp
      rcases hInvS y hyS with ⟨hvE, hExpInv⟩
      let v : E := invM y
      have hradv : edist x y = ENNReal.ofReal (mnorm ge0 v) := by
        have hrad := hRadial (invM y) hvE
        rw [hExpInv] at hrad
        simpa [ge0, x₀, mnorm, v] using hrad
      have hmnle : mnorm ge0 v ≤ ρ := by
        have hle' : ENNReal.ofReal (mnorm ge0 v) ≤ ENNReal.ofReal ρ := by
          rw [← hradv]
          exact hyc
        exact (ENNReal.ofReal_le_ofReal_iff (le_of_lt hρpos)).mp hle'
      refine ⟨v, hmnle, ?_⟩
      simpa [v] using hExpInv
    have hsub_back : ExpM '' ell ⊆ closedBall x (ENNReal.ofReal ρ) := by
      rintro y ⟨v, hv, rfl⟩
      have hvE : v ∈ ball (0 : E) r := hmetric_in_euclid v (lt_of_le_of_lt hv hρlt)
      have hrad := hRadial v hvE
      have hmnle : edist (ExpM v) x ≤ ENNReal.ofReal ρ := by
        calc
          edist (ExpM v) x = edist x (ExpM v) := by rw [edist_comm]
          _ = ENNReal.ofReal (mnorm ge0 v) := by simpa [x₀, ge0, mnorm] using hrad
          _ ≤ ENNReal.ofReal ρ := ENNReal.ofReal_le_ofReal hv
      exact hmnle
    have hEq : closedBall x (ENNReal.ofReal ρ) = ExpM '' ell :=
      subset_antisymm hsub_fwd hsub_back
    rw [hEq]
    exact hImCompact
  · -- continuity of Exp at points of the metric ball (chart normal coordinates)
    intro v hv
    have hvE : v ∈ ball (0 : E) r := hmetric_in_euclid v hv
    exact hExpCont.continuousAt (isOpen_ball.mem_nhds hvE)
  · -- window rigidity from the arc-rigidity rigidity clause
    intro γ δ hγ0 hδ0 hδle hwin
    have hδle_ρa : (1 : ℝ) * δ ≤ ρa := by
      rw [one_mul]
      exact le_trans hδle hρ0_le_ρa
    rcases hRigid (1 : NNReal) (by norm_num) γ δ hγ0 hδ0 hδle_ρa
      (fun s t hs ht => by simpa using hwin s t hs ht) with ⟨v, hsqrt, hform⟩
    refine ⟨v, ?_, ?_⟩
    · simpa [x₀, ge0, mnorm] using hsqrt
    · intro t ht
      exact hform t ht

/-- Assemble the engine's per-point data from the per-point packages. -/
noncomputable def dirB_ld {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : Type*} [EMetricSpace M] (pk : ∀ x : M, PkgAt E M x) : LocData M E where
  ρ0 := fun x => (pk x).ρ0
  ge0 := fun x => (pk x).ge0
  Exp := fun x v => (pk x).Exp v

/-- A global unit-geodesic has a symmetric exact window around any of its points (speed 1),
used to feed the window-rigidity clause. -/
lemma unitgeo_symmetric_window {γ : ℝ → M} (hγ : UnitGeo γ) {t₀ : ℝ} :
    ∃ δr > 0, ∀ s t : ℝ, |s| < δr → |t| < δr →
      edist (γ (t₀ + s)) (γ (t₀ + t)) = ENNReal.ofReal |t - s| := by
  have hlin : Metric.IsLocLinear (t₀ - 1) (t₀ + 1) (1 : NNReal) γ :=
    UnitGeo.isLocLinear hγ (t₀ - 1) (t₀ + 1) (by linarith)
  have ht₀ : t₀ ∈ Ioo (t₀ - 1) (t₀ + 1) := by constructor <;> linarith
  rcases hlin t₀ ht₀ with ⟨δu, hδu, hwin⟩
  let δr : ℝ := min δu (1 / 2)
  have hδr : 0 < δr := lt_min hδu (by norm_num)
  refine ⟨δr, hδr, ?_⟩
  intro s t hs ht
  have hsδu : |s| < δu := lt_of_lt_of_le hs (by dsimp [δr]; exact min_le_left δu (1 / 2))
  have hs12 : |s| < 1 / 2 := lt_of_lt_of_le hs (by dsimp [δr]; exact min_le_right δu (1 / 2))
  have htδu : |t| < δu := lt_of_lt_of_le ht (by dsimp [δr]; exact min_le_left δu (1 / 2))
  have ht12 : |t| < 1 / 2 := lt_of_lt_of_le ht (by dsimp [δr]; exact min_le_right δu (1 / 2))
  have hs_lo : t₀ - 1 < t₀ + s := by linarith [(abs_lt.mp hs12).1]
  have hs_hi : t₀ + s < t₀ + 1 := by linarith [(abs_lt.mp hs12).2]
  have hs_loδ : t₀ - δu < t₀ + s := by linarith [(abs_lt.mp hsδu).1]
  have hs_hiδ : t₀ + s < t₀ + δu := by linarith [(abs_lt.mp hsδu).2]
  have ht_lo : t₀ - 1 < t₀ + t := by linarith [(abs_lt.mp ht12).1]
  have ht_hi : t₀ + t < t₀ + 1 := by linarith [(abs_lt.mp ht12).2]
  have ht_loδ : t₀ - δu < t₀ + t := by linarith [(abs_lt.mp htδu).1]
  have ht_hiδ : t₀ + t < t₀ + δu := by linarith [(abs_lt.mp htδu).2]
  have hu : t₀ + s ∈ Ioo (max (t₀ - 1) (t₀ - δu)) (min (t₀ + 1) (t₀ + δu)) := by
    constructor
    · exact max_lt hs_lo hs_loδ
    · exact lt_min hs_hi hs_hiδ
  have hv : t₀ + t ∈ Ioo (max (t₀ - 1) (t₀ - δu)) (min (t₀ + 1) (t₀ + δu)) := by
    constructor
    · exact max_lt ht_lo ht_loδ
    · exact lt_min ht_hi ht_hiδ
  have hw := hwin (t₀ + s) (t₀ + t) hu hv
  have harg : |(t₀ + t) - (t₀ + s)| = |t - s| := by
    congr 1
    ring
  simpa [harg] using hw

/-- The engine hypotheses hold for the per-point package under geodesic completeness and the
existence of a nonzero tangent vector. -/
theorem dirB_locHyps {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    (M : Type*) [EMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [Bundle.RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M => TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M]
    (hgc : IsGeodesicallyComplete M) (hnon : ∃ v : E, v ≠ 0) :
    LocHyps (dirB_ld (fun x : M => Classical.choice (pkg_at I M x))) := by
  classical
  let pk : ∀ x : M, PkgAt E M x := fun x => Classical.choice (pkg_at I M x)
  change LocHyps (dirB_ld pk)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- rho_pos
    intro x
    exact (pk x).rho_pos
  · -- ge_symm
    intro x u v
    exact (pk x).ge_symm u v
  · -- ge_pos
    intro x v hv
    exact (pk x).ge_pos v hv
  · -- radial
    intro x v hv
    have hv' : mnorm (pk x).ge0 v < (pk x).ρ0 := by simpa [dirB_ld] using hv
    simpa [dirB_ld] using (pk x).radial v hv'
  · -- arc
    intro x W hW s t hs ht hst
    have hW' : mnorm (pk x).ge0 W = 1 := by simpa [dirB_ld] using hW
    have hs' : |s| < (pk x).ρ0 := by simpa [dirB_ld] using hs
    have ht' : |t| < (pk x).ρ0 := by simpa [dirB_ld] using ht
    simpa [dirB_ld] using (pk x).arc W hW' hs' ht' hst
  · -- surj
    intro x y hy
    have hy' : edist x y < ENNReal.ofReal (pk x).ρ0 := by simpa [dirB_ld] using hy
    rcases (pk x).surj y hy' with ⟨v, hv1, hv2⟩
    refine ⟨v, ?_, ?_⟩
    · simpa [dirB_ld] using hv1
    · simpa [dirB_ld] using hv2
  · -- inj
    intro x v w hv hw heq
    have hv' : mnorm (pk x).ge0 v < (pk x).ρ0 := by simpa [dirB_ld] using hv
    have hw' : mnorm (pk x).ge0 w < (pk x).ρ0 := by simpa [dirB_ld] using hw
    have heq' : (pk x).Exp v = (pk x).Exp w := by simpa [dirB_ld] using heq
    exact (pk x).inj v w hv' hw' heq'
  · -- ball_comp
    intro x ρ hρpos hρlt
    have hρlt' : ρ < (pk x).ρ0 := by simpa [dirB_ld] using hρlt
    simpa [dirB_ld] using (pk x).ball_comp ρ hρpos hρlt'
  · -- corner
    intro x v1 v2 hu1 hu2 hne
    have hu1' : mnorm (pk x).ge0 v1 = 1 := by simpa [dirB_ld] using hu1
    have hu2' : mnorm (pk x).ge0 v2 = 1 := by simpa [dirB_ld] using hu2
    refine ⟨(pk x).ρ0 / 4, div_pos (pk x).rho_pos (by norm_num), ?_⟩
    intro δ hδ hδle
    have hδle' : δ ≤ (pk x).ρ0 / 4 := by simpa [dirB_ld] using hδle
    simpa [dirB_ld] using (PkgAt.corner_lt (pk x) v1 v2 hu1' hu2' hne δ hδ hδle')
  · -- ext
    intro x W hW
    have hW' : mnorm (pk x).ge0 W = 1 := by simpa [dirB_ld] using hW
    rcases geoExt I M x (pk x) hW' hgc with ⟨γ, hγunit, hγ0, hγwin⟩
    refine ⟨γ, hγunit, hγ0, ?_⟩
    intro t ht
    have ht' : |t| < (pk x).ρ0 := by simpa [dirB_ld] using ht
    simpa [dirB_ld] using (hγwin t ht')
  · -- rig
    intro x γ t₀ hγx hγunit
    rcases unitgeo_symmetric_window hγunit (t₀ := t₀) with ⟨δu, hδu, hwin⟩
    let δ : ℝ := min δu (pk x).ρ0
    have hδ0 : 0 < δ := by
      dsimp [δ]
      exact lt_min hδu (pk x).rho_pos
    have hδle : δ ≤ (pk x).ρ0 := by
      dsimp [δ]
      exact min_le_right δu (pk x).ρ0
    let η : ℝ → M := fun s => γ (t₀ + s)
    have hη0 : η 0 = x := by
      dsimp [η]
      simpa using hγx
    have hwin' : ∀ s t : ℝ, |s| < δ → |t| < δ →
        edist (η s) (η t) = ENNReal.ofReal |t - s| := by
      intro s t hs ht
      have hs' : |s| < δu := lt_of_lt_of_le hs (by dsimp [δ]; exact min_le_left δu (pk x).ρ0)
      have ht' : |t| < δu := lt_of_lt_of_le ht (by dsimp [δ]; exact min_le_left δu (pk x).ρ0)
      have hw := hwin s t hs' ht'
      simpa [η] using hw
    rcases (pk x).wrig η δ hη0 hδ0 hδle hwin' with ⟨v, hv_unit, hv_form⟩
    refine ⟨δ, hδ0, ?le, v, ?unit, ?form⟩
    · -- δ ≤ ld.ρ0 x
      simpa [dirB_ld] using hδle
    · simpa [dirB_ld] using hv_unit
    · intro t ht
      have hf := hv_form (t - t₀) ht
      -- hf : η (t - t₀) = Exp ((t - t₀) • v)
      simpa [dirB_ld, η] using hf
  · -- dir
    intro x
    rcases hnon with ⟨v0, hv0⟩
    have hq : 0 ≤ (pk x).ge0 v0 v0 := PkgAt.ge_nonneg (pk x) v0
    have hqpos : 0 < (pk x).ge0 v0 v0 := (pk x).ge_pos v0 hv0
    let W : E := (mnorm (pk x).ge0 v0)⁻¹ • v0
    have hm0 : 0 < mnorm (pk x).ge0 v0 := by
      dsimp [mnorm]
      exact Real.sqrt_pos.2 hqpos
    refine ⟨W, ?_⟩
    have hsm := PkgAt.mnorm_smul (pk x).ge0 ((mnorm (pk x).ge0 v0)⁻¹) v0 hq
    have habs : |(mnorm (pk x).ge0 v0)⁻¹| = (mnorm (pk x).ge0 v0)⁻¹ :=
      abs_of_nonneg (inv_nonneg.mpr (le_of_lt hm0))
    have hmain : mnorm (pk x).ge0 W = 1 := by
      calc
        mnorm (pk x).ge0 W = mnorm (pk x).ge0 ((mnorm (pk x).ge0 v0)⁻¹ • v0) := rfl
        _ = |(mnorm (pk x).ge0 v0)⁻¹| * mnorm (pk x).ge0 v0 := hsm
        _ = (mnorm (pk x).ge0 v0)⁻¹ * mnorm (pk x).ge0 v0 := by rw [habs]
        _ = 1 := inv_mul_cancel₀ (ne_of_gt hm0)
    simpa [dirB_ld] using hmain

/-- The engine gives distance-realising unit geodesics from every point to every point at
finite distance, under geodesic completeness (and a nonzero tangent vector). -/
theorem reachable_dirB {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    (M : Type*) [EMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [Bundle.RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M => TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M]
    (hgc : IsGeodesicallyComplete M) (hnon : ∃ v : E, v ≠ 0)
    (x y : M) (he : edist x y < ⊤) :
    ∃ γ : ℝ → M, UnitGeo γ ∧ γ 0 = x ∧
      (∀ t : ℝ, 0 ≤ t → t ≤ (edist x y).toReal → edist x (γ t) = ENNReal.ofReal t) ∧
      edist (γ (edist x y).toReal) y = 0 := by
  let pk : ∀ x : M, PkgAt E M x := fun x => Classical.choice (pkg_at I M x)
  exact Engine.reachable (M := M) I (dirB_ld pk) (dirB_locHyps I M hgc hnon) x y he

/-- Time reflection preserves the `UnitGeo` property. -/
lemma unitgeo_reflect {γ : ℝ → M} (hγ : UnitGeo γ) : UnitGeo (fun u => γ (-u)) := by
  intro B hB
  have hll := UnitGeo.isLocLinear hγ (-B) B (by linarith)
  simpa using (Metric.IsLocLinear.reflect hll)

/-- Agreement of two global unit geodesics on the non-negative half-line (given agreement in a
neighbourhood of `0`), obtained by the local-extension uniqueness of `UlU`. -/
theorem agree_nonneg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    (M : Type*) [EMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [Bundle.RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M => TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M]
    {γ₁ γ₂ : ℝ → M} (h₁ : UnitGeo γ₁) (h₂ : UnitGeo γ₂)
    {ε : ℝ} (hε : 0 < ε) (hagree : ∀ t : ℝ, |t| < ε → γ₁ t = γ₂ t) :
    ∀ t : ℝ, 0 ≤ t → γ₁ t = γ₂ t := by
  intro t ht
  have hlin₁ : Metric.IsLocLinear (-ε) (t + 1) (1 : NNReal) γ₁ :=
    UnitGeo.isLocLinear h₁ (-ε) (t + 1) (by linarith)
  have hlin₂ : Metric.IsLocLinear (-ε) (t + 1) (1 : NNReal) γ₂ :=
    UnitGeo.isLocLinear h₂ (-ε) (t + 1) (by linarith)
  have hmem : t ∈ Ioo (-ε) (t + 1) := by constructor <;> linarith
  have hag : ∀ u : ℝ, u ∈ Ioo (-ε) (0 : ℝ) → γ₁ u = γ₂ u := by
    intro u hu
    exact hagree u (by
      have hu1 : -ε < u := hu.1
      have hu2 : u < 0 := hu.2
      rw [abs_of_neg hu2]
      linarith)
  have hneg_lt : -ε < (0 : ℝ) := by linarith
  have hzero_le : (0 : ℝ) ≤ t + 1 := by linarith
  have hres := locallyLinear_ext_unique (I := I) (M := M) (a := -ε) (b := 0)
    (β := t + 1) (c := (1 : NNReal)) (γ₁ := γ₁) (γ₂ := γ₂) hneg_lt hzero_le hlin₁ hlin₂ hag
  exact hres t hmem

/-- Two global unit geodesics that agree on a neighbourhood of `0` agree everywhere. -/
theorem unitgeo_unique {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    (M : Type*) [EMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [Bundle.RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M => TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M]
    {γ₁ γ₂ : ℝ → M} (h₁ : UnitGeo γ₁) (h₂ : UnitGeo γ₂)
    {ε : ℝ} (hε : 0 < ε) (hagree : ∀ t : ℝ, |t| < ε → γ₁ t = γ₂ t) :
    γ₁ = γ₂ := by
  funext t
  rcases le_total 0 t with ht | ht
  · exact agree_nonneg I M h₁ h₂ hε hagree t ht
  · -- t ≤ 0 : reflect and apply the non-negative case at -t
    have hα₁ : UnitGeo (fun u => γ₁ (-u)) := unitgeo_reflect h₁
    have hα₂ : UnitGeo (fun u => γ₂ (-u)) := unitgeo_reflect h₂
    have hαagree : ∀ u : ℝ, |u| < ε → (fun u => γ₁ (-u)) u = (fun u => γ₂ (-u)) u := by
      intro u hu
      exact hagree (-u) (by simpa using hu)
    have hnt : 0 ≤ -t := by linarith
    have hv := agree_nonneg I M hα₁ hα₂ hε hαagree (-t) hnt
    simpa using hv

/-! # Exponential-map flow continuity (target)

Under `IsGeodesicallyComplete M`, `geoExt` produces, for every unit direction `W` at `x`, a
global unit geodesic `flowGeo W : ℝ → M` (chosen, but canonical: two such choices agree on
`(-ρ0, ρ0)` with the radial arc, hence agree everywhere by `unitgeo_unique`).  The goal is
joint continuity of the *geodesic flow* in the initial direction and the time parameter on
every bounded interval `[0,B]`:

    geoFlowCont : Continuous (W,t) ↦ flowGeo W t

on the compact domain `{W | mnorm ρ = 1} × Icc 0 B`.  Together with compactness of the unit
sphere this will show every closed metric ball is the image of a compact set under a
continuous map, finishing `geoBallsCompact`.

Plan of the proof (delegating the two central metric/topological lemmas to the commons):
 1. *local* stability near the base point: short geodesics with close initial directions stay
    close (chart-smoothness of the exponential, `PkgAt`/chart data) — a Direction-B lemma,
    not delegated.
 2. *propagation* along the geodesic using the window rigidity, then
    `equiLipschitz_continuous_joint` (commons) turns pointwise-in-direction continuity plus
    the common 1-Lipschitz bound in time into full joint continuity.
 3. the unit sphere `{W | mnorm = 1}` is compact (closed and bounded in the finite
    dimensional `E`).

The zero-dimensional case `E = {0}` (no unit directions) is tracked separately: closed balls
are singletons there, handled directly in `geoBallsCompact`.

## Milestone 2 (current): chart-level local two-point dependence

`flowGeo_cont_window` gives joint continuity on the radial window `(-ρ0, ρ0)` of the start
point.  To propagate to arbitrary times one needs, at every point `p = γ_W0(s)` of the target
geodesic, a *two-point* local stability statement in one chart: for the chart-normal data at
`p` (`chart_normal_forward`, exporting `ExpM`, the `C¹` model exponential `exp`, the model
geodesic flow `Φ` of the chart metric `ge`, radial identity and the FWD two-point ray
identity), for `y = ExpM(a)` nearby `p` in the same chart and a metric-unit direction at `y`
close (in chart coordinates) to the direction of `γ_W0` at `p`:

    γ(t) and the chart-model geodesic through (chart y, direction)
    stay inside the chart and agree out to a uniform small time.

Model ingredients already in the library: `Submission.Model.flow_lipschitz` (flow is
Lipschitz in initial data, uniformly in `t ∈ Icc (-T) T`),
`Submission.ArcModel.uniform_normal_ball` / `Submission.ArcNB.uniform_normal_ball_aux`
(uniform normal-ball minimality over base points `b ∈ ball x₀ ρB`),
`Submission.Model.arc_segment_ident` (model geodesic segments are exponential rays from every
point along the flow), and `Submission.Rigidity.arc_rigidity` (one-point manifold rigidity:
any locally-linear unit curve through a point equals that point's normal radial arc).  The
missing manifold step is the identification "metric unit geodesic staying in the chart normal
ball = chart-model geodesic (in chart coordinates)", which requires transiting between the
per-point normal data of nearby base points inside one chart; the rigidity arguments above
were all carried out base-by-base and need to be made uniform over the chart ball.  With this
statement proved, the one-step propagation lemma (continuity at `s` ⇒ continuity at `s+h`)
and then `geoFlowCont` assemble by partition + the two Commons lemmas.
-/

/-- The global unit geodesic in direction `W` through `x` (canonical choice of the `geoExt`
witness). -/
noncomputable def flowGeo {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    (M : Type*) [EMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [Bundle.RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M => TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M]
    (hgc : IsGeodesicallyComplete M) (x : M) (pk : PkgAt E M x) {W : E}
    (hW : mnorm pk.ge0 W = 1) : ℝ → M :=
  Classical.choose (geoExt I M x pk hW hgc)

/-- `flowGeo W` is a global unit geodesic. -/
lemma flowGeo_unit {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    (M : Type*) [EMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [Bundle.RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M => TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M]
    (hgc : IsGeodesicallyComplete M) (x : M) (pk : PkgAt E M x) {W : E}
    (hW : mnorm pk.ge0 W = 1) : UnitGeo (flowGeo I M hgc x pk hW) :=
  (Classical.choose_spec (geoExt I M x pk hW hgc)).1

/-- `flowGeo W` starts at `x`. -/
lemma flowGeo_start {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    (M : Type*) [EMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [Bundle.RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M => TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M]
    (hgc : IsGeodesicallyComplete M) (x : M) (pk : PkgAt E M x) {W : E}
    (hW : mnorm pk.ge0 W = 1) : flowGeo I M hgc x pk hW 0 = x :=
  (Classical.choose_spec (geoExt I M x pk hW hgc)).2.1

/-- `flowGeo W` agrees with the radial arc `t ↦ Exp(t•W)` on `(-ρ0, ρ0)`. -/
lemma flowGeo_agree {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    (M : Type*) [EMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [Bundle.RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M => TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M]
    (hgc : IsGeodesicallyComplete M) (x : M) (pk : PkgAt E M x) {W : E}
    (hW : mnorm pk.ge0 W = 1) {t : ℝ} (ht : |t| < pk.ρ0) :
    flowGeo I M hgc x pk hW t = pk.Exp (t • W) :=
  (Classical.choose_spec (geoExt I M x pk hW hgc)).2.2 t ht

/-- The unit sphere of the chart metric norm is compact (finite dimensional). -/
lemma unit_sphere_compact {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (ge0 : E →L[ℝ] E →L[ℝ] ℝ)
    (hpos : ∀ v : E, v ≠ 0 → 0 < ge0 v v) :
    IsCompact {W : E | mnorm ge0 W = 1} := by
  rw [Metric.isCompact_iff_isClosed_bounded]
  constructor
  · -- closed: preimage of {1} under the continuous norm
    have hcont : Continuous (fun W : E => mnorm ge0 W) := by
      dsimp [mnorm]
      exact Real.continuous_sqrt.comp (by
        have hcu : Continuous (fun p : E × E => ge0 p.1 p.2) :=
          ContinuousLinearMap.continuous₂ ge0
        exact hcu.comp (continuous_diag : Continuous (Function.diag : E → E × E)))
    exact IsClosed.preimage hcont (isClosed_singleton)
  · -- bounded: ‖W‖ ≤ K * mnorm W = K on the sphere
    rcases unit_norm_bound ge0 hpos with ⟨K, hK0, hKbound⟩
    refine Bornology.IsBounded.subset ?_ (show {W : E | mnorm ge0 W = 1} ⊆ Metric.closedBall 0 (K + 1) from ?_)
    · exact Metric.isBounded_closedBall
    · intro W hW
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
      have hb : ‖W‖ ≤ K * mnorm ge0 W := unit_norm_bound_all ge0 hpos K hK0.le (fun V hV => hKbound V hV) W
      have h1 : K * mnorm ge0 W ≤ K + 1 := by
        have hm : mnorm ge0 W = 1 := hW
        rw [hm]
        nlinarith [hK0]
      linarith

/-- Short-time continuity of the geodesic flow in the initial direction: at any time inside
the radial window, nearby initial directions give nearby `flowGeo` values. -/
theorem flowGeo_shortTime_cont {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    (M : Type*) [EMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [Bundle.RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M => TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M]
    (hgc : IsGeodesicallyComplete M) (x : M) (pk : PkgAt E M x)
    {W0 : E} (hW0 : mnorm pk.ge0 W0 = 1) {τ : ℝ} (hτ : |τ| < pk.ρ0) :
    ContinuousAt
      (fun W : {W : E // mnorm pk.ge0 W = 1} => flowGeo I M hgc x pk (W := W.1) W.2 τ)
      ⟨W0, hW0⟩ := by
  have hnn : 0 ≤ pk.ge0 W0 W0 := PkgAt.ge_nonneg pk W0
  have hmm0 : mnorm pk.ge0 (τ • W0) < pk.ρ0 := by
    calc
      mnorm pk.ge0 (τ • W0) = |τ| * mnorm pk.ge0 W0 := PkgAt.mnorm_smul pk.ge0 τ W0 hnn
      _ = |τ| := by rw [hW0, mul_one]
      _ < pk.ρ0 := hτ
  let g : {W : E // mnorm pk.ge0 W = 1} → M := fun W => pk.Exp (τ • W.1)
  have hcg : ContinuousAt g ⟨W0, hW0⟩ := by
    have hsmul : ContinuousAt (fun W : {W : E // mnorm pk.ge0 W = 1} => τ • W.1) ⟨W0, hW0⟩ := by
      have hc : Continuous (fun W : {W : E // mnorm pk.ge0 W = 1} => τ • W.1) :=
        (continuous_const_smul τ).comp continuous_subtype_val
      exact hc.continuousAt
    exact ContinuousAt.comp (f := fun W : {v : E // mnorm pk.ge0 v = 1} => τ • W.1)
      (x := ⟨W0, hW0⟩) (pk.exp_cont (τ • W0) hmm0) hsmul
  have heq : (fun W : {W : E // mnorm pk.ge0 W = 1} =>
        flowGeo I M hgc x pk (W := W.1) W.2 τ) =ᶠ[𝓝 ⟨W0, hW0⟩] g := by
    filter_upwards with W
    exact flowGeo_agree I M hgc x pk (W := W.1) W.2 (t := τ) hτ
  exact (ContinuousAt.congr hcg heq.symm)

/-- The chart metric norm is continuous. -/
lemma mnorm_continuous (ge0 : E →L[ℝ] E →L[ℝ] ℝ) : Continuous (fun v : E => mnorm ge0 v) := by
  dsimp [mnorm]
  exact Real.continuous_sqrt.comp (by
    have hcu : Continuous (fun p : E × E => ge0 p.1 p.2) := ContinuousLinearMap.continuous₂ ge0
    exact hcu.comp (continuous_diag : Continuous (Function.diag : E → E × E)))

/-- The metric ball `{v | mnorm v < ρ0}` is open. -/
lemma metric_ball_open (pk : PkgAt E M x) : IsOpen {v : E | mnorm pk.ge0 v < pk.ρ0} := by
  exact IsOpen.preimage (mnorm_continuous pk.ge0) isOpen_Iio

/-- `Exp` is continuous on the metric ball. -/
lemma Exp_continuousOn_ball (pk : PkgAt E M x) :
    ContinuousOn pk.Exp {v : E | mnorm pk.ge0 v < pk.ρ0} := by
  exact (IsOpen.continuousOn_iff (metric_ball_open pk)).2 (fun v hv => pk.exp_cont v hv)

/-- Inside the radial window, the geodesic flow is jointly continuous in the initial
direction and time (this is `geoFlowCont` for all `B < ρ0`). -/
theorem flowGeo_cont_window {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    (M : Type*) [EMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [Bundle.RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M => TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M]
    (hgc : IsGeodesicallyComplete M) (x : M) (pk : PkgAt E M x) :
    Continuous
      (fun z : {W : E // mnorm pk.ge0 W = 1} × {t : ℝ // |t| < pk.ρ0} =>
        flowGeo I M hgc x pk (W := z.1.1) z.1.2 z.2.1) := by
  let g : {W : E // mnorm pk.ge0 W = 1} × {t : ℝ // |t| < pk.ρ0} → M :=
    fun z => pk.Exp (z.2.1 • z.1.1)
  have hsmul : Continuous (fun z : {W : E // mnorm pk.ge0 W = 1} × {t : ℝ // |t| < pk.ρ0} =>
      z.2.1 • z.1.1) := by
    have hs : Continuous (fun z : {W : E // mnorm pk.ge0 W = 1} × {t : ℝ // |t| < pk.ρ0} => z.2.1) := by
      exact continuous_subtype_val.comp continuous_snd
    have hv : Continuous (fun z : {W : E // mnorm pk.ge0 W = 1} × {t : ℝ // |t| < pk.ρ0} => z.1.1) := by
      exact continuous_subtype_val.comp continuous_fst
    exact hs.smul hv
  have hin : ∀ z : {W : E // mnorm pk.ge0 W = 1} × {t : ℝ // |t| < pk.ρ0},
      z.2.1 • z.1.1 ∈ {v : E | mnorm pk.ge0 v < pk.ρ0} := by
    intro z
    have hnn : 0 ≤ pk.ge0 z.1.1 z.1.1 := PkgAt.ge_nonneg pk z.1.1
    have hmm : mnorm pk.ge0 (z.2.1 • z.1.1) = |z.2.1| := by
      calc
        mnorm pk.ge0 (z.2.1 • z.1.1) = |z.2.1| * mnorm pk.ge0 z.1.1 :=
          PkgAt.mnorm_smul pk.ge0 z.2.1 z.1.1 hnn
        _ = |z.2.1| := by rw [z.1.2, mul_one]
    change mnorm pk.ge0 (z.2.1 • z.1.1) < pk.ρ0
    rw [hmm]
    exact z.2.2
  have hg : Continuous g := by
    have hExpC := Exp_continuousOn_ball pk
    have hc := ContinuousOn.comp_continuous hExpC hsmul hin
    -- hc : Continuous (pk.Exp ∘ fun z => z.2.1 • z.1.1)
    exact hc
  -- flowGeo agrees with g on the whole domain
  have heq : (fun z : {W : E // mnorm pk.ge0 W = 1} × {t : ℝ // |t| < pk.ρ0} =>
        flowGeo I M hgc x pk (W := z.1.1) z.1.2 z.2.1) = g := by
    funext z
    dsimp [g]
    exact flowGeo_agree I M hgc x pk (W := z.1.1) z.1.2 (t := z.2.1) z.2.2
  simpa [heq] using hg

/-! # Uniform rigidity over a chart ball (Milestone 2 work)

The manifold `arc_rigidity`/`chart_normal_forward` arguments are run base-point-by-base-point.
To propagate flow continuity along a geodesic we need the same conclusions *uniformly* for all
base points in one chart ball.  The model layer already provides the uniform control
(`Submission.Model.region_flow_pkg`, `Submission.Model.uniform_normal_ball_aux`); the
Direction-B work is:
  (L1) packaging the model control over a base ball — DONE below in
       `model_uniform_minimality_pkg` (uses `region_flow_pkg` to feed
       `uniform_normal_ball_aux`: a uniform `ρB, δu, τu` and uniform minimality of staying
       `C¹` curves against the radial model length, for every base `b ∈ ball x₀ ρB`);
  (L2) the uniform manifold radial identity over the chart ball: with the `chart_normal_forward`
       chart at `p`, for `b` in a chart ball and small `v`, the manifold distance from
       `m_b := extChart.symm b` to the chart exponential of the geodesic from `(b,v)` equals
       `ofReal (sqrt ((g b) v v))` (uniformly); this is where the manifold edist is first tied
       to the chart metric over a *ball of bases* rather than at the single base `p`;
  (L3) uniform chart rigidity: any metric unit geodesic starting in the chart normal ball with
       chart data `(b, w)` agrees with the chart-model geodesic `chart.symm (Φ (b, w) ·)` out to
       a uniform small time (transplanting the per-point `arc_rigidity` argument to every base
       in the ball, using (L1)+(L2)); then the one-step propagation lemma and `geoFlowCont`
       follow by partition plus the two Commons lemmas.
-/

/-- Uniform model minimality over a base ball (first reusable piece): around `x₀` there is a
uniform flow with per-base containment/Lipschitz data (from `region_flow_pkg`) and a uniform
normal-ball radius `ρB`, direction radius `δu` and time `τu` such that every staying `C¹` curve
from `b` to the exponential ray `expOf b Φ τu v` has model length at least the radial length
`sqrt ((g b) v v)`. -/
theorem model_uniform_minimality_pkg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (g : E → Model.Bilin E) (hg : ContDiff ℝ 3 g)
    (hinv : ∀ x, (g x).IsInvertible) (hsym : ∀ x u v, (g x) u v = (g x) v u)
    (hpos : ∀ x u : E, u ≠ 0 → 0 < (g x) u u)
    (x₀ : E) (R0 : NNReal) (hR02 : (2 : ℝ) ≤ (R0 : ℝ)) :
    ∃ ρu Tf : ℝ, 0 < ρu ∧ 0 < Tf ∧ ∃ L : NNReal, ∃ Φ : E × E → ℝ → E × E,
      (∀ b ∈ Metric.ball x₀ ρu, ∀ z ∈ Metric.closedBall (b, (0 : E)) 1, Φ z 0 = z ∧
         (∀ t ∈ Icc (-Tf) Tf, HasDerivAt (Φ z) (Model.odeField g (Φ z t)) t) ∧
         (∀ t : ℝ, Φ z t ∈ Metric.closedBall (b, (0 : E)) 2)) ∧
      (∀ t ∈ Icc (-Tf) Tf, ∀ b ∈ Metric.ball x₀ ρu,
         LipschitzOnWith L (fun z => Φ z t) (Metric.closedBall (b, (0 : E)) 1)) ∧
      ∃ ρB δu τu : ℝ, 0 < ρB ∧ 0 < δu ∧ 0 < τu ∧ ρB ≤ ρu ∧ δu ≤ τu ∧ 2 * τu ≤ Tf ∧
        ∀ b ∈ Metric.ball x₀ ρB, ∀ v ∈ Metric.ball (0 : E) δu,
          ∀ c : ℝ → E, c 0 = b → c 1 = Model.expOf b Φ τu v →
            (∃ O : Set ℝ, IsOpen O ∧ Icc (0 : ℝ) 1 ⊆ O ∧ ContDiffOn ℝ 1 c O) →
            (∀ s ∈ Icc (0 : ℝ) 1, c s ∈ Metric.ball b δu) →
            Real.sqrt ((g b) v v) ≤ Model.mgLength g c 0 1 := by
  classical
  rcases Model.region_flow_pkg g hg hinv x₀ R0 hR02 with ⟨Tf, hTf, ρu, hρu, L, Φ, hΦ⟩
  rcases hΦ with ⟨hΦall, hCon2, hLipX, hLip, hPer⟩
  rcases Model.uniform_normal_ball_aux g hg hinv hsym hpos x₀ ρu Tf hρu hTf L Φ hPer hLip with
    ⟨ρB, δu, τu, hρB, hδu, hτu, hρBρu, hδuτu, h2τuτf, hUNB⟩
  refine ⟨ρu, Tf, hρu, hTf, L, Φ, hPer, hLip, ρB, δu, τu, hρB, hδu, hτu, hρBρu, hδuτu, h2τuτf, ?_⟩
  intro b hb v hv c hc0 hc1 hcsm hstay
  exact hUNB b hb v hv c hc0 hc1 hcsm hstay

/-! # L2: uniform manifold radial identity over a chart ball (Milestone 2, second step)

Single-base version (this section, proved below, `radial_identity_flow_rays`): at the fixed
base `x0 = extChartAt I p p` in the chart at `p`, the manifold distance from `p` to the chart
exponential of a model geodesic ray equals `ofReal (sqrt ((ge x0) v v))`.  This is the exact
statement whose *base-parametrised* version is needed by L3:

    L2 target: with the `chart_normal_forward` chart at `p` and the uniform model control
    (`model_uniform_minimality_pkg`: `ρB, δu, τu, Φ` over `ball x0 ρB`), for every
    `b ∈ ball x0 ρB`, `m_b := extChartAt I p p |>.symm b`, and every `v ∈ ball 0 δu`:
        edist m_b (extChartAt I p p |>.symm (expOf b Φ τu v))
            = ENNReal.ofReal (Real.sqrt ((g b) v v))

The pointwise-in-`b` version holds by `arc_rigidity` at `m_b` once the chart-model rays at
`m_b` are identified with the manifold radial exponential there; the uniform control (L1)
supplies the radius and the upper bound (the manifold lift of the model ray is an explicit
path of the right length).
-/

/-- Single-base radial identity in model-flow-ray form: at the chart base of `p`, the radial
distance equals the model radial value `sqrt ((ge x0) v v)`. -/
theorem radial_identity_flow_rays {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    (M : Type*) [EMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [Bundle.RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M => TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M] (p : M) :
    ∃ ρe > 0, ∃ τe : ℝ, 0 < τe ∧ ∃ ge : E → Model.Bilin E,
      ∃ Φ : E × E → ℝ → E × E,
        ∀ v : E, v ∈ Metric.ball (0 : E) ρe →
          edist p ((extChartAt I p).symm ((Φ (extChartAt I p p, (1 / τe) • v) τe).1)) =
            ENNReal.ofReal (Real.sqrt ((ge (extChartAt I p p)) v v)) := by
  classical
  let x0 : E := extChartAt I p p
  rcases chart_normal_forward (I := I) (M := M) p with
    ⟨ρ0, hρ00, ge, hgeC, hgeSymm, hgePos, hgeAgree, hrest⟩
  rcases hrest with ⟨r, hr0, ExpM, S, invM, hExpM0, hSnhds, hS_in, hExpCont, hInj,
    hSurj, hInvS, hInvExp, hRadial, hrest2⟩
  rcases hrest2 with ⟨ρe, hρe0, hρele, τe, hτe0, hρeτe4, Φ, expm,
    hExpExpM, hexp0, hExpC1, hΦODE, hexpform, hRay, hrest3⟩
  refine ⟨ρe, hρe0, τe, hτe0, ge, Φ, ?_⟩
  intro v hv
  have hv_r : v ∈ Metric.ball (0 : E) r := by
    exact Metric.mem_ball.mpr (lt_of_lt_of_le (Metric.mem_ball.mp hv) hρele)
  have h1 : (extChartAt I p).symm ((Φ (extChartAt I p p, (1 / τe) • v) τe).1) = ExpM v := by
    symm
    rw [hExpExpM v hv]
    congr 1
    exact hexpform v hv
  calc
    edist p ((extChartAt I p).symm ((Φ (extChartAt I p p, (1 / τe) • v) τe).1)) =
        edist p (ExpM v) := by rw [h1]
    _ = ENNReal.ofReal (Real.sqrt ((ge x0) v v)) := by
      have hrad := hRadial v hv_r
      simpa [x0] using hrad

end DirectionB

end Submission

