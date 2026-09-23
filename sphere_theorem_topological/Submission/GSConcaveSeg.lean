import Submission.GSCritical
import Submission.GSFar
import Submission.Commons.Analysis.Convex.concaveOn_Icc_of_midpoint

/-!
# Concavity of `d(p,·)` along a far segment (Grove–Shiohama, step 2 case 2)

If the geodesic `γ = geodCurve …` is minimising on `[0,T]`, and `t ↦ d(p, γ t)` is `≥ π/2` and
`≤ D` on `[0,T]`, then this function is **concave** on `[0,T]` — provided `T/2 + D ≤ π`.

The proof feeds the midpoint inequality `GSConcave.edist_add_midpoint_le` (which is exactly the
concavity of `d(p,·)` on `M \ B_{π/2}(p)` in the "antipodal pair" form) into Jensen's theorem
`Commons.Analysis.Convex.concaveOn_Icc_of_midpoint`.  The hypothesis `T/2 + D ≤ π` is what makes
every midpoint admissible (`a + r ≤ π` with `a ≤ T/2`, `r ≤ D`).
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

namespace Submission.GSConcaveSeg

noncomputable section

variable [I.Boundaryless] [Nontrivial E] [CompactSpace M]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]

/-- **Concavity of `d(p,·)` along a far minimising segment.** -/
theorem concaveOn_dist_geodCurve
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (hpinch : QuarterPinched cov)
    [PathConnectedSpace M] [RegularSpace M]
    {p : M} {T D : ℝ} {q : M} {ξ : TangentSpace I q} (hξ : ‖ξ‖ = 1)
    (hT : 0 ≤ T) (hDπ : D ≤ Real.pi) (hTD : T / 2 + D ≤ Real.pi)
    (hmin : Manifold.riemannianEDist I q
      ((geodCurve (cov := cov) hmet T hT q ξ hξ : ℝ → M) T) = ENNReal.ofReal T)
    (hcont : ContinuousOn (fun t : ℝ => (Manifold.riemannianEDist I p
      ((geodCurve (cov := cov) hmet T hT q ξ hξ : ℝ → M) t)).toReal) (Set.Icc 0 T))
    (hfar : ∀ t ∈ Set.Icc (0:ℝ) T, Real.pi / 2 ≤ (Manifold.riemannianEDist I p
      ((geodCurve (cov := cov) hmet T hT q ξ hξ : ℝ → M) t)).toReal)
    (hleD : ∀ t ∈ Set.Icc (0:ℝ) T, (Manifold.riemannianEDist I p
      ((geodCurve (cov := cov) hmet T hT q ξ hξ : ℝ → M) t)).toReal ≤ D) :
    ConcaveOn ℝ (Set.Icc (0:ℝ) T) (fun t : ℝ => (Manifold.riemannianEDist I p
      ((geodCurve (cov := cov) hmet T hT q ξ hξ : ℝ → M) t)).toReal) := by
  haveI hcb : IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x) :=
    Submission.EDist.isContinuousRiemannianBundle_infty (I := I)
  set G : ℝ → M := geodCurve (cov := cov) hmet T hT q ξ hξ with hGdef
  have hsub : ∀ a ∈ Set.Icc (0:ℝ) T, ∀ b ∈ Set.Icc (0:ℝ) T, a ≤ b →
      Manifold.riemannianEDist I (G a) (G b) = ENNReal.ofReal (b - a) := by
    have h := geodCurve_sub_arc_minimising' (cov := cov) hmet (T := T) hT hξ (s := T) hT le_rfl hmin
    intro a ha b hb hab
    exact h a ha b hb hab
  -- the midpoint inequality for `x ≤ y`
  have key : ∀ x ∈ Set.Icc (0:ℝ) T, ∀ y ∈ Set.Icc (0:ℝ) T, x ≤ y →
      ((Manifold.riemannianEDist I p (G x)).toReal
        + (Manifold.riemannianEDist I p (G y)).toReal) / 2
        ≤ (Manifold.riemannianEDist I p (G ((x + y) / 2))).toReal := by
    intro x hx y hy hxy
    set m : ℝ := (x + y) / 2 with hmdef
    set a : ℝ := (y - x) / 2 with hadef
    have hm0 : 0 ≤ m := by rw [hmdef]; linarith [hx.1, hy.1]
    have hmT : m ≤ T := by rw [hmdef]; linarith [hx.2, hy.2]
    have ha0 : 0 ≤ a := by rw [hadef]; linarith
    have ham : a ≤ m := by rw [hadef, hmdef]; linarith [hx.1]
    have hmaT : m + a ≤ T := by rw [hadef, hmdef]; linarith [hy.2]
    rcases eq_or_lt_of_le ha0 with ha0' | hapos
    · have hxy' : x = y := by rw [hadef] at ha0'; linarith
      have hmy : m = y := by rw [hmdef, hxy']; ring
      rw [hxy', hmy]
      linarith
    · have hxm : x = m - a := by rw [hadef, hmdef]; ring
      have hym : y = m + a := by rw [hadef, hmdef]; ring
      have hmem1 : m - a ∈ Set.Icc (0:ℝ) T := ⟨by linarith [hm0, ham], by linarith [hmT, ha0]⟩
      have hmem2 : m + a ∈ Set.Icc (0:ℝ) T := ⟨by linarith [hm0, ha0], hmaT⟩
      -- the velocity at the midpoint
      set vel : TangentSpace I (G m) := curveVelocity (I := I) G m with hveldef
      have hvel1 : ‖vel‖ = 1 := by
        rw [hveldef]
        exact norm_curveVelocity_geodCurve (cov := cov) hmet hT q ξ hξ hm0 hmT
      set ux : TangentSpace I (G m) := -vel with huxdef
      have hux1 : ‖ux‖ = 1 := by rw [huxdef, norm_neg, hvel1]
      have hback : GExp (cov := cov) hmet (G m) (a • ux) = G (m - a) := by
        rw [huxdef, hveldef]
        exact GExp_neg_curveVelocity_geodCurve (cov := cov) hmet hξ hT hm0 hmT ha0 ham
      have hfwd : GExp (cov := cov) hmet (G m) (a • (-ux)) = G (m + a) := by
        rw [huxdef, neg_neg, hveldef]
        exact GExp_add_curveVelocity_geodCurve (cov := cov) hmet hξ hT hm0 hmT ha0 hmaT
      -- Hopf–Rinow at `(G m, p)`
      obtain ⟨vp, hpG, hpd⟩ :=
        Submission.HopfRinow.exists_geodesic_riemannianEDist_eq (cov := cov) hmet htor (G m) p
      set r : ℝ := ‖vp‖ with hrdef
      have hr_eq : Manifold.riemannianEDist I (G m) p = ENNReal.ofReal r := by
        rw [hrdef]; exact hpd
      have hrnn : 0 ≤ r := norm_nonneg vp
      have hrm : (Manifold.riemannianEDist I p (G m)).toReal = r := by
        rw [Manifold.riemannianEDist_comm, hr_eq, ENNReal.toReal_ofReal hrnn]
      have hrD : r ≤ D := by rw [← hrm]; exact hleD m ⟨hm0, hmT⟩
      have hrfar : Real.pi / 2 ≤ r := by rw [← hrm]; exact hfar m ⟨hm0, hmT⟩
      have hrpos : 0 < r := lt_of_lt_of_le (by linarith [Real.pi_pos]) hrfar
      have hvpn : vp ≠ 0 := by
        intro h0; rw [h0, norm_zero] at hrdef; rw [hrdef] at hrpos
        exact lt_irrefl 0 hrpos
      set up : TangentSpace I (G m) := unitOf vp hvpn with hupdef
      have hup1 : ‖up‖ = 1 := unitOf_norm vp hvpn
      have huup : r • up = vp := by
        rw [hupdef, hrdef, unitOf, smul_smul,
          mul_inv_cancel₀ (norm_ne_zero_iff.mpr hvpn), one_smul]
      have hpup : p = GExp (cov := cov) hmet (G m) (r • up) := by rw [huup]; exact hpG.symm
      -- the minimising identities
      have hga : Manifold.riemannianEDist I (G (m - a)) (G m)
          = ENNReal.ofReal (m - (m - a)) := hsub (m - a) hmem1 m ⟨hm0, hmT⟩ (by linarith)
      have hgb : Manifold.riemannianEDist I (G m) (G (m + a))
          = ENNReal.ofReal ((m + a) - m) := hsub m ⟨hm0, hmT⟩ (m + a) hmem2 (by linarith)
      have hminx : Manifold.riemannianEDist I (G m)
          (GExp (cov := cov) hmet (G m) (a • ux)) = ENNReal.ofReal a := by
        rw [hback, Manifold.riemannianEDist_comm, hga, show m - (m - a) = a from by ring]
      have hminy : Manifold.riemannianEDist I (G m)
          (GExp (cov := cov) hmet (G m) (a • (-ux))) = ENNReal.ofReal a := by
        rw [hfwd, hgb, show (m + a) - m = a from by ring]
      have hconc := Submission.GSConcave.edist_add_midpoint_le (cov := cov) hmet htor hpinch
        (m := G m) (p := p) (a := a) (r := r) (ux := ux) (up := up)
        hapos hrpos (by linarith) (by linarith) hux1 hup1 hminx hminy
        (by rw [← hpup]; exact hr_eq)
      rw [hback, hfwd, ← hpup] at hconc
      -- convert to real numbers
      have hfin1 : Manifold.riemannianEDist I p (G (m - a)) ≠ ⊤ :=
        (Submission.HopfRinow.riemannianEDist_lt_top (cov := cov) hmet htor p (G (m - a))).ne
      have hfin2 : Manifold.riemannianEDist I p (G (m + a)) ≠ ⊤ :=
        (Submission.HopfRinow.riemannianEDist_lt_top (cov := cov) hmet htor p (G (m + a))).ne
      have hsum : (Manifold.riemannianEDist I p (G (m - a))).toReal
          + (Manifold.riemannianEDist I p (G (m + a))).toReal
          ≤ 2 * (Manifold.riemannianEDist I p (G m)).toReal := by
        rw [Manifold.riemannianEDist_comm (I := I) (x := G (m - a)) (y := p),
          Manifold.riemannianEDist_comm (I := I) (x := G (m + a)) (y := p),
          (ENNReal.ofReal_toReal hfin1).symm, (ENNReal.ofReal_toReal hfin2).symm] at hconc
        rw [← ENNReal.ofReal_add ENNReal.toReal_nonneg ENNReal.toReal_nonneg] at hconc
        have h2 := (ENNReal.ofReal_le_ofReal_iff (by linarith)).mp hconc
        rw [← hrm] at h2
        linarith
      rw [hxm, hym]
      linarith [hsum]
  refine Commons.Analysis.Convex.concaveOn_Icc_of_midpoint hT hcont ?_
  intro x hx y hy
  rcases le_total x y with h | h
  · exact key x hx y hy h
  · have h' := key y hy x hx h
    rw [show (y + x) / 2 = (x + y) / 2 from by ring] at h'
    linarith [h']

/-- **The midpoint of a far sub-segment is far.**  If the sub-segment `[a,b]` of the minimising
geodesic has both endpoints at distance `> π/2` from `p`, has length `b - a ≤ π`, and all its points
are at distance `≤ D ≤ π` from `p`, then its midpoint is at distance `> π/2` from `p`.

This is `GSCritical.not_both_gt_pi_div_two` in geometric form; it is the induction step of the
"the whole segment `[x,q]` stays outside `B_{π/2}(p)`" argument of Grove–Shiohama step 2. -/
theorem midpoint_far
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (hpinch : QuarterPinched cov)
    [PathConnectedSpace M] [RegularSpace M]
    {p : M} {s D : ℝ} {q : M} {ξ : TangentSpace I q} (hξ : ‖ξ‖ = 1)
    (hs : 0 ≤ s) (hDπ : D ≤ Real.pi)
    (hmin : Manifold.riemannianEDist I q
      ((geodCurve (cov := cov) hmet s hs q ξ hξ : ℝ → M) s) = ENNReal.ofReal s)
    {a b : ℝ} (ha : a ∈ Set.Icc (0:ℝ) s) (hb : b ∈ Set.Icc (0:ℝ) s) (hab : a ≤ b)
    (hdiam : b - a ≤ Real.pi)
    (hbd : ∀ t ∈ Set.Icc a b, (Manifold.riemannianEDist I p
      ((geodCurve (cov := cov) hmet s hs q ξ hξ : ℝ → M) t)).toReal ≤ D)
    (hfa : Real.pi / 2 < (Manifold.riemannianEDist I p
      ((geodCurve (cov := cov) hmet s hs q ξ hξ : ℝ → M) a)).toReal)
    (hfb : Real.pi / 2 < (Manifold.riemannianEDist I p
      ((geodCurve (cov := cov) hmet s hs q ξ hξ : ℝ → M) b)).toReal) :
    Real.pi / 2 < (Manifold.riemannianEDist I p
      ((geodCurve (cov := cov) hmet s hs q ξ hξ : ℝ → M) ((a + b) / 2))).toReal := by
  haveI hcb : IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x) :=
    Submission.EDist.isContinuousRiemannianBundle_infty (I := I)
  set G : ℝ → M := geodCurve (cov := cov) hmet s hs q ξ hξ with hGdef
  have hsub : ∀ u ∈ Set.Icc (0:ℝ) s, ∀ v ∈ Set.Icc (0:ℝ) s, u ≤ v →
      Manifold.riemannianEDist I (G u) (G v) = ENNReal.ofReal (v - u) := by
    have h := geodCurve_sub_arc_minimising' (cov := cov) hmet (T := s) hs hξ (s := s) hs le_rfl hmin
    intro u hu v hv huv
    exact h u hu v hv huv
  set m : ℝ := (a + b) / 2 with hmdef
  have hm0 : 0 ≤ m := by rw [hmdef]; linarith [ha.1, hb.1]
  have hm1 : m ≤ s := by rw [hmdef]; linarith [ha.2, hb.2]
  have hma : a ≤ m := by rw [hmdef]; linarith
  have hmb : m ≤ b := by rw [hmdef]; linarith
  -- the two half-widths
  set a₁ : ℝ := m - a with ha₁def
  set a₂ : ℝ := b - m with ha₂def
  have ha₁nn : 0 ≤ a₁ := by rw [ha₁def]; linarith
  have ha₂nn : 0 ≤ a₂ := by rw [ha₂def]; linarith
  have ha₁₂ : a₁ + a₂ = b - a := by rw [ha₁def, ha₂def]; ring
  rcases eq_or_lt_of_le ha₁nn with ha₁0 | ha₁pos
  · -- `a = b`:
    have hab' : a = b := by rw [ha₁def] at ha₁0; linarith
    have hma' : m = a := by rw [hmdef, hab']; ring
    rw [hma']; exact hfa
  rcases eq_or_lt_of_le ha₂nn with ha₂0 | ha₂pos
  · have hab' : a = b := by rw [ha₂def] at ha₂0; linarith
    have hma' : m = a := by rw [hmdef, hab']; ring
    rw [hma']; exact hfa
  -- the velocity at `m` and the two ray endpoints
  set vel : TangentSpace I (G m) := curveVelocity (I := I) G m with hveldef
  have hvel1 : ‖vel‖ = 1 := by
    rw [hveldef]
    exact norm_curveVelocity_geodCurve (cov := cov) hmet hs q ξ hξ hm0 hm1
  set ux : TangentSpace I (G m) := -vel with huxdef
  have hux1 : ‖ux‖ = 1 := by rw [huxdef, norm_neg, hvel1]
  have hback : GExp (cov := cov) hmet (G m) (a₁ • ux) = G a := by
    rw [show a = m - a₁ from by rw [ha₁def]; ring]
    rw [huxdef, hveldef]
    exact GExp_neg_curveVelocity_geodCurve (cov := cov) hmet hξ hs hm0 hm1 ha₁nn
      (by rw [ha₁def]; linarith [ha.1])
  have hfwd : GExp (cov := cov) hmet (G m) (a₂ • (-ux)) = G b := by
    rw [show b = m + a₂ from by rw [ha₂def]; ring]
    rw [huxdef, neg_neg, hveldef]
    exact GExp_add_curveVelocity_geodCurve (cov := cov) hmet hξ hs hm0 hm1 ha₂nn
      (by rw [ha₂def]; linarith [hb.2])
  -- Hopf–Rinow at `(G m, p)`
  obtain ⟨vp, hpG, hpd⟩ :=
    Submission.HopfRinow.exists_geodesic_riemannianEDist_eq (cov := cov) hmet htor (G m) p
  set r : ℝ := ‖vp‖ with hrdef
  have hr_eq : Manifold.riemannianEDist I (G m) p = ENNReal.ofReal r := by
    rw [hrdef]; exact hpd
  have hrnn : 0 ≤ r := norm_nonneg vp
  have hrm : (Manifold.riemannianEDist I p (G m)).toReal = r := by
    rw [Manifold.riemannianEDist_comm, hr_eq, ENNReal.toReal_ofReal hrnn]
  rw [hrm]
  by_contra hcon
  push Not at hcon
  -- `r ≤ π/2` now
  have hpos : 0 < r := by
    rcases eq_or_lt_of_le hrnn with h0 | h0
    · exfalso
      have hgmp : G m = p := by
        have h1 : vp = 0 := norm_eq_zero.mp h0.symm
        rw [h1, GExp_zero] at hpG
        exact hpG
      have h1 : (Manifold.riemannianEDist I p (G a)).toReal
          ≤ (Manifold.riemannianEDist I (G m) (G a)).toReal := by
        rw [hgmp]
      have h2 : (Manifold.riemannianEDist I (G m) (G a)).toReal = a₁ := by
        rw [Manifold.riemannianEDist_comm, hsub a ha m ⟨hm0, hm1⟩ hma,
          show m - a = a₁ from by rw [ha₁def], ENNReal.toReal_ofReal ha₁nn]
      have h3 : a₁ ≤ (b - a) / 2 := by rw [ha₁def, hmdef]; ring_nf; linarith
      linarith [hfa]
    · exact h0
  have hvpn : vp ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hrdef; rw [hrdef] at hpos; exact lt_irrefl 0 hpos
  set up : TangentSpace I (G m) := unitOf vp hvpn with hupdef
  have hup1 : ‖up‖ = 1 := unitOf_norm vp hvpn
  have huup : r • up = vp := by
    rw [hupdef, hrdef, unitOf, smul_smul,
      mul_inv_cancel₀ (norm_ne_zero_iff.mpr hvpn), one_smul]
  have hpup : p = GExp (cov := cov) hmet (G m) (r • up) := by rw [huup]; exact hpG.symm
  -- the distance identities
  have hga := hsub a ha m ⟨hm0, hm1⟩ hma
  have hgb := hsub m ⟨hm0, hm1⟩ b hb hmb
  have hminx : Manifold.riemannianEDist I (G m)
      (GExp (cov := cov) hmet (G m) (a₁ • ux)) = ENNReal.ofReal a₁ := by
    rw [hback, Manifold.riemannianEDist_comm, hga, show m - a = a₁ from by rw [ha₁def]]
  have hminy : Manifold.riemannianEDist I (G m)
      (GExp (cov := cov) hmet (G m) (a₂ • (-ux))) = ENNReal.ofReal a₂ := by
    rw [hfwd, hgb, show b - m = a₂ from by rw [ha₂def]]
  have hfin1 : Manifold.riemannianEDist I p (G a) ≠ ⊤ :=
    (Submission.HopfRinow.riemannianEDist_lt_top (cov := cov) hmet htor p (G a)).ne
  have hfin2 : Manifold.riemannianEDist I p (G b) ≠ ⊤ :=
    (Submission.HopfRinow.riemannianEDist_lt_top (cov := cov) hmet htor p (G b)).ne
  have hd1 : Manifold.riemannianEDist I (G a) p
      = ENNReal.ofReal ((Manifold.riemannianEDist I p (G a)).toReal) := by
    rw [Manifold.riemannianEDist_comm]; exact (ENNReal.ofReal_toReal hfin1).symm
  have hd2 : Manifold.riemannianEDist I (G b) p
      = ENNReal.ofReal ((Manifold.riemannianEDist I p (G b)).toReal) := by
    rw [Manifold.riemannianEDist_comm]; exact (ENNReal.ofReal_toReal hfin2).symm
  have hbnd1 : (Manifold.riemannianEDist I p (G a)).toReal ≤ D := hbd a ⟨le_rfl, hab⟩
  have hbnd2 : (Manifold.riemannianEDist I p (G b)).toReal ≤ D := hbd b ⟨hab, le_rfl⟩
  have hg := GSCritical.not_both_gt_pi_div_two (cov := cov) hmet htor hpinch
    (z := G m) (x₁ := G a) (x₂ := G b) (p := p)
    (a₁ := a₁) (a₂ := a₂) (u := r)
    (d₁ := (Manifold.riemannianEDist I p (G a)).toReal)
    (d₂ := (Manifold.riemannianEDist I p (G b)).toReal)
    (ux := ux) (up := up)
    ha₁pos ha₂pos hpos hux1 hup1
    (by linarith [ha₁def, hmdef]) (by linarith [ha₂def, hmdef])
    (by rw [ha₁₂]; exact hdiam) hcon
    hback.symm hfwd.symm hpup hr_eq (by rw [← hback]; exact hminx) (by rw [← hfwd]; exact hminy)
    hd1 hd2
    ENNReal.toReal_nonneg ENNReal.toReal_nonneg
    (le_trans hbnd1 hDπ) (le_trans hbnd2 hDπ) hfa hfb
  exact hg

/-- **The whole segment stays outside the `π/2`-ball.**  If the minimising geodesic
`γ = geodCurve hmet s hs q ξ hξ` has length `s ≤ π`, both endpoints at distance `> π/2` from `p`, and
every point of `[0,s]` at distance `≤ D ≤ π` from `p`, then `d(p, γ ·) ≥ π/2` on the whole of
`[0,s]`.

This is the "farness propagation" of Grove–Shiohama step 2 (the dyadic closure of
`midpoint_far`): the set `{t : d(p,γ t) > π/2}` is open, contains the endpoints, and is closed under
midpoints, so by the dyadic argument `Submission.GSFar.le_of_midpoint_of_continuousOn` it is dense,
and by continuity `d(p,γ ·) ≥ π/2` everywhere. -/
theorem far_of_far_endpoints
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (hpinch : QuarterPinched cov)
    [PathConnectedSpace M] [RegularSpace M]
    {p : M} {s D : ℝ} {q : M} {ξ : TangentSpace I q} (hξ : ‖ξ‖ = 1)
    (hs : 0 ≤ s) (hspi : s ≤ Real.pi) (hDπ : D ≤ Real.pi)
    (hmin : Manifold.riemannianEDist I q
      ((geodCurve (cov := cov) hmet s hs q ξ hξ : ℝ → M) s) = ENNReal.ofReal s)
    (hcont : ContinuousOn (fun t : ℝ => (Manifold.riemannianEDist I p
      ((geodCurve (cov := cov) hmet s hs q ξ hξ : ℝ → M) t)).toReal) (Set.Icc 0 s))
    (hbd : ∀ t ∈ Set.Icc (0:ℝ) s, (Manifold.riemannianEDist I p
      ((geodCurve (cov := cov) hmet s hs q ξ hξ : ℝ → M) t)).toReal ≤ D)
    (hfar0 : Real.pi / 2 < (Manifold.riemannianEDist I p
      ((geodCurve (cov := cov) hmet s hs q ξ hξ : ℝ → M) 0)).toReal)
    (hfars : Real.pi / 2 < (Manifold.riemannianEDist I p
      ((geodCurve (cov := cov) hmet s hs q ξ hξ : ℝ → M) s)).toReal) :
    ∀ t ∈ Set.Icc (0:ℝ) s, Real.pi / 2 ≤ (Manifold.riemannianEDist I p
      ((geodCurve (cov := cov) hmet s hs q ξ hξ : ℝ → M) t)).toReal := by
  haveI hcb : IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x) :=
    Submission.EDist.isContinuousRiemannianBundle_infty (I := I)
  refine Submission.GSFar.le_of_midpoint_of_continuousOn hs hcont hfar0 hfars ?_
  intro a b ha hb hab hfa hfb
  exact midpoint_far (cov := cov) hmet htor hpinch hξ hs hDπ hmin ha hb hab.le
    (by linarith [ha.1, hb.2, hspi])
    (fun t ht => hbd t ⟨le_trans ha.1 ht.1, le_trans ht.2 hb.2⟩) hfa hfb

end

end Submission.GSConcaveSeg
