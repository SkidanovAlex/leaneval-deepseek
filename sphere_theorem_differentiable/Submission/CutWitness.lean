import Submission.HopfRinow2
import Submission.GExpRay

set_option backward.isDefEq.respectTransparency.types false

/-!
# The minimal witness of the exponential map, and the two minimising geodesics

For a point `p` of a complete Riemannian manifold, `InjAtLeast hmet p r` says that the exponential
map `GExp p` is injective on the ball of radius `r`.  When it fails, there is a **witness pair**
`u ≠ v` with `GExp p u = GExp p v`, both of norm `< r`; the two geodesics `s ↦ GExp p (s • u)` and
`s ↦ GExp p (s • v)` are two geodesics from `p` to the same point.

This file develops the elementary (compactness-free) core of the classical **cut point** analysis,
namely the *minimality* of the witness:

* `edist_GExp_le_norm`: `d(p, GExp p u) ≤ ‖u‖` always (the map is `1`-Lipschitz in a weak sense);
* `norm_eq_of_minimising_max`: if a witness pair has a **minimising** member of maximal norm, then
  *both* members have the same norm and both are minimising (immediate: the distance of the image
  is `‖·‖` on both);
* `exists_lt_of_not_minimising_ray`: if the exponential ray `s ↦ GExp p (s • η)` (`‖η‖ = 1`) is
  **not** minimising at time `m`, then it already fails to be minimising at some earlier time
  `s ∈ (0,m)`.  This is proved by a pure triangle-inequality argument (no continuity!): if it were
  minimising on all of `[0,m)`, then `m = sup_{s<m} (2s − m) ≤ d(p, GExp p (m • η))`.
* `exists_witness_lt_max`: **the cut-down lemma.**  If a witness pair has a non-minimising member of
  maximal norm `m`, then there is a witness pair whose max-norm is strictly smaller than `m`.
  Indeed, take the earlier non-minimising time `s < m` of the ray, and replace that member of the
  pair by a *minimising* vector to the intermediate point `GExp p (s • η)`.
* `norm_eq_norm_of_isMinWitness`: **a witness of minimal `max`-norm consists of two distinct
  minimising vectors of the *same* norm** — the starting point of Klingenberg's lemma and of the
  broken closed geodesic loop `γ_u ∪ γ_v⁻¹`.

## What is *not* here

The *existence* of a witness of minimal max-norm (the closure/compactness argument) is not proved
here: the set of witnesses is not closed (the condition `u ≠ v` is open), and the degenerate case —
`uₙ ≠ vₙ → u` with `GExp p uₙ = GExp p vₙ` — requires the fact that *a non-conjugate vector is a
local diffeomorphism point of `exp`* (i.e. `d(exp_p)_u` invertible; via
`Submission.FlowJacobi.exists_expMap_mfderiv_eq_jacobiTensor` this is exactly the statement that the
kernel of `d(exp_p)_u` is spanned by `J(1)` for Jacobi fields `J` with `J(0) = 0`).  See
`Submission/Roadmap.lean` §69.
-/

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.GlobalExp
open Submission.HopfRinow
open Submission.GExpRay

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

namespace Submission.CutWitness

noncomputable section

variable [I.Boundaryless] [Nontrivial E] [CompactSpace M]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]

/-- **The exponential map is distance-decreasing along its rays**: `d(p, GExp p u) ≤ ‖u‖`. -/
theorem edist_GExp_le_norm (hmet : IsMetricCompatible cov) {p : M} (u : TangentSpace I p) :
    Manifold.riemannianEDist I p (GExp (cov := cov) hmet p u) ≤ ENNReal.ofReal ‖u‖ := by
  by_cases hu : u = 0
  · subst hu
    simp [Manifold.riemannianEDist_self]
  · have hη : ‖unitOf u hu‖ = 1 := unitOf_norm u hu
    have hscale : ‖u‖ • unitOf u hu = u := by
      show ‖u‖ • unitOf u hu = u
      rw [unitOf, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hu), one_smul]
    have h := edist_GExp_smul_le_zero (cov := cov) hmet p hη (norm_nonneg u)
    rwa [hscale] at h

/-- **A minimising member of a witness pair forces everything.**  If `(u,v)` is a witness pair with
`‖v‖ ≤ ‖u‖` and `u` is minimising (`d(p, GExp p u) = ‖u‖`), then `‖v‖ = ‖u‖` and `v` is minimising
as well. -/
theorem norm_eq_of_minimising_max (hmet : IsMetricCompatible cov)
    {p : M} {u v : TangentSpace I p}
    (hG : GExp (cov := cov) hmet p u = GExp (cov := cov) hmet p v) (hvu : ‖v‖ ≤ ‖u‖)
    (hmin : Manifold.riemannianEDist I p (GExp (cov := cov) hmet p u) = ENNReal.ofReal ‖u‖) :
    ‖v‖ = ‖u‖ ∧
      Manifold.riemannianEDist I p (GExp (cov := cov) hmet p v) = ENNReal.ofReal ‖v‖ := by
  have hdv : Manifold.riemannianEDist I p (GExp (cov := cov) hmet p v) = ENNReal.ofReal ‖u‖ := by
    rw [← hG]; exact hmin
  have hle : ENNReal.ofReal ‖u‖ ≤ ENNReal.ofReal ‖v‖ := by
    rw [← hdv]; exact edist_GExp_le_norm (cov := cov) hmet v
  have hnorm : ‖v‖ = ‖u‖ := le_antisymm hvu ((ENNReal.ofReal_le_ofReal_iff (norm_nonneg v)).mp hle)
  exact ⟨hnorm, by rw [hdv, hnorm]⟩

/-- **If the exponential ray is not minimising at time `m`, it fails earlier.**  For a unit vector
`η` and `m > 0` with `d(p, GExp p (m • η)) < m`, there is `s ∈ (0,m)` with
`d(p, GExp p (s • η)) < s`.

The proof is a pure triangle-inequality argument: the ray gives
`d(p, γ s) ≤ d(p, γ m) + d(γ m, γ s) ≤ d(p, γ m) + (m - s)`, so if the ray were minimising at every
earlier time we would get `d(p, γ m) ≥ 2s - m` for every `s < m`, hence `d(p, γ m) ≥ m`. -/
theorem exists_lt_of_not_minimising_ray (hmet : IsMetricCompatible cov)
    {p : M} {η : TangentSpace I p} (hη : ‖η‖ = 1) {m : ℝ} (hm : 0 < m)
    (hnot : Manifold.riemannianEDist I p (GExp (cov := cov) hmet p (m • η))
      < ENNReal.ofReal m) :
    ∃ s ∈ Ioo (0 : ℝ) m,
      Manifold.riemannianEDist I p (GExp (cov := cov) hmet p (s • η)) < ENNReal.ofReal s := by
  classical
  by_contra hcon
  push Not at hcon
  -- the upper bound from the ray
  have hub : ∀ s ∈ Ioo (0 : ℝ) m,
      Manifold.riemannianEDist I p (GExp (cov := cov) hmet p (s • η)) ≤ ENNReal.ofReal s :=
    fun s hs => edist_GExp_smul_le_zero (cov := cov) hmet p hη hs.1.le
  -- the triangle inequality, chain
  have hmain : ∀ s ∈ Ioo (0 : ℝ) m,
      ENNReal.ofReal s ≤ Manifold.riemannianEDist I p (GExp (cov := cov) hmet p (m • η))
        + ENNReal.ofReal (m - s) := by
    intro s hs
    have h1 : ENNReal.ofReal s
        ≤ Manifold.riemannianEDist I p (GExp (cov := cov) hmet p (s • η)) := hcon s hs
    have h2 : Manifold.riemannianEDist I (GExp (cov := cov) hmet p (m • η))
        (GExp (cov := cov) hmet p (s • η)) ≤ ENNReal.ofReal (m - s) := by
      rw [Manifold.riemannianEDist_comm]
      exact edist_GExp_smul_le (cov := cov) hmet p hη hs.1.le hm.le hs.2.le
    have h3 := Manifold.riemannianEDist_triangle (I := I) (x := p)
      (y := GExp (cov := cov) hmet p (m • η)) (z := GExp (cov := cov) hmet p (s • η))
    exact h1.trans (h3.trans (add_le_add le_rfl h2))
  set D : ℝ≥0∞ := Manifold.riemannianEDist I p (GExp (cov := cov) hmet p (m • η)) with hDdef
  have hDtop : D ≠ ⊤ := by
    rw [hDdef]
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (edist_GExp_smul_le_zero (cov := cov) hmet p hη hm.le)
  -- pass to `toReal`
  have hreal : ∀ s ∈ Ioo (0 : ℝ) m, 2 * s - m ≤ D.toReal := by
    intro s hs
    have h := hmain s hs
    have h4 : (ENNReal.ofReal s).toReal ≤ (D + ENNReal.ofReal (m - s)).toReal :=
      ENNReal.toReal_mono (by simp [hDtop]) h
    rw [ENNReal.toReal_ofReal hs.1.le, ENNReal.toReal_add hDtop ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal (by linarith [hs.2])] at h4
    linarith
  -- `D.toReal ≥ m`
  have hDge : m ≤ D.toReal := by
    by_contra hlt
    push Not at hlt
    set s : ℝ := (D.toReal + 3 * m) / 4 with hsdef
    have hs2 : 0 < s := by rw [hsdef]; linarith [ENNReal.toReal_nonneg (a := D)]
    have hs1 : s < m := by rw [hsdef]; linarith
    have h := hreal s ⟨hs2, hs1⟩
    rw [hsdef] at h
    linarith
  -- contradict the hypothesis
  have hmle : ENNReal.ofReal m ≤ D := by
    calc ENNReal.ofReal m ≤ ENNReal.ofReal D.toReal := ENNReal.ofReal_le_ofReal hDge
      _ = D := ENNReal.ofReal_toReal hDtop
  rw [hDdef] at hmle
  exact absurd hmle (not_le.mpr hnot)

/-- **The cut-down lemma.**  If a witness pair `(u,v)` (with `‖v‖ ≤ ‖u‖`) has a member `u` of
maximal norm which is **not** minimising, then there is a witness pair whose `max`-norm is strictly
smaller than `‖u‖`.

Indeed the ray of `u` fails to be minimising at time `‖u‖`, hence at some earlier time `s`; passing
to the intermediate point `GExp p (s • û)` and replacing `u` by a *minimising* vector to it gives
the pair `(w, s • û)`, of max-norm `s < ‖u‖`. -/
theorem exists_witness_lt_max (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    [PathConnectedSpace M] [RegularSpace M]
    {p : M} {u v : TangentSpace I p} (huv : u ≠ v)
    (hG : GExp (cov := cov) hmet p u = GExp (cov := cov) hmet p v) (hvu : ‖v‖ ≤ ‖u‖)
    (hnot : Manifold.riemannianEDist I p (GExp (cov := cov) hmet p u) < ENNReal.ofReal ‖u‖) :
    ∃ u' v' : TangentSpace I p, u' ≠ v' ∧ GExp (cov := cov) hmet p u' = GExp (cov := cov) hmet p v'
      ∧ max ‖u'‖ ‖v'‖ < ‖u‖ := by
  classical
  have hune : u ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hvu
    have hv0 : v = 0 := norm_le_zero_iff.mp hvu
    exact huv (h0.trans hv0.symm)
  have hm : 0 < ‖u‖ := norm_pos_iff.mpr hune
  set η : TangentSpace I p := unitOf u hune with hηdef
  have hη : ‖η‖ = 1 := unitOf_norm u hune
  have hscale : ‖u‖ • η = u := by
    rw [hηdef]
    show ‖u‖ • unitOf u hune = u
    rw [unitOf, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hune), one_smul]
  have hnot' : Manifold.riemannianEDist I p (GExp (cov := cov) hmet p (‖u‖ • η))
      < ENNReal.ofReal ‖u‖ := by
    rw [hscale]; exact hnot
  obtain ⟨s, hs, hslt⟩ := exists_lt_of_not_minimising_ray (cov := cov) hmet hη hm hnot'
  obtain ⟨w, hwG, hwd⟩ :=
    exists_geodesic_riemannianEDist_eq (cov := cov) hmet htor p
      (GExp (cov := cov) hmet p (s • η))
  have hnormη : ‖s • η‖ = s := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs.1, hη, mul_one]
  have hwlt : ‖w‖ < s := by
    have h' := hwd
    rw [h'] at hslt
    exact (ENNReal.ofReal_lt_ofReal_iff hs.1).mp hslt
  refine ⟨w, s • η, ?_, ?_, ?_⟩
  · -- distinct
    intro hcon
    rw [hcon, hnormη] at hwlt
    exact lt_irrefl _ hwlt
  · rw [hwG]
  · -- the max is `s < ‖u‖`
    rw [hnormη, max_lt_iff]
    exact ⟨lt_trans hwlt hs.2, hs.2⟩

/-- **A witness of minimal `max`-norm consists of two distinct minimising vectors of the same norm.**

`hmin` says that `(u,v)` has minimal `max ‖·‖` among all witness pairs.  Then neither member can be
non-minimising: by `exists_witness_lt_max` such a member would produce a witness pair with strictly
smaller `max`.  Both members are therefore minimising, and then `norm_eq_of_minimising_max` forces
their norms to be equal. -/
theorem norm_eq_norm_of_isMinWitness (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    [PathConnectedSpace M] [RegularSpace M]
    {p : M} {u v : TangentSpace I p} (huv : u ≠ v)
    (hG : GExp (cov := cov) hmet p u = GExp (cov := cov) hmet p v)
    (hmin : ∀ u' v' : TangentSpace I p, u' ≠ v' →
      GExp (cov := cov) hmet p u' = GExp (cov := cov) hmet p v' →
      max ‖u‖ ‖v‖ ≤ max ‖u'‖ ‖v'‖) :
    ‖u‖ = ‖v‖ ∧ Manifold.riemannianEDist I p (GExp (cov := cov) hmet p u) = ENNReal.ofReal ‖u‖ := by
  classical
  rcases le_total ‖u‖ ‖v‖ with hle | hle
  · -- `v` has the maximal norm; show `v` is minimising
    have hvmin : Manifold.riemannianEDist I p (GExp (cov := cov) hmet p v) = ENNReal.ofReal ‖v‖ := by
      by_contra hcon
      have hlt : Manifold.riemannianEDist I p (GExp (cov := cov) hmet p v) < ENNReal.ofReal ‖v‖ :=
        lt_of_le_of_ne (edist_GExp_le_norm (cov := cov) hmet v) hcon
      obtain ⟨u', v', huv', hG', hmax'⟩ :=
        exists_witness_lt_max (cov := cov) hmet htor (p := p) (u := v) (v := u)
          (Ne.symm huv) hG.symm hle hlt
      have h1 : max ‖u‖ ‖v‖ ≤ max ‖u'‖ ‖v'‖ := hmin u' v' huv' hG'
      rw [max_eq_right hle] at h1
      exact absurd h1 (not_le.mpr hmax')
    have hnorm := (norm_eq_of_minimising_max (cov := cov) hmet hG.symm hle hvmin).1
    exact ⟨hnorm, by rw [hG, hnorm]; exact hvmin⟩
  · -- `u` has the maximal norm
    have hmin' : Manifold.riemannianEDist I p (GExp (cov := cov) hmet p u) = ENNReal.ofReal ‖u‖ := by
      by_contra hcon
      have hlt : Manifold.riemannianEDist I p (GExp (cov := cov) hmet p u) < ENNReal.ofReal ‖u‖ :=
        lt_of_le_of_ne (edist_GExp_le_norm (cov := cov) hmet u) hcon
      obtain ⟨u', v', huv', hG', hmax'⟩ :=
        exists_witness_lt_max (cov := cov) hmet htor (p := p) (u := u) (v := v) huv hG hle hlt
      have h1 : max ‖u‖ ‖v‖ ≤ max ‖u'‖ ‖v'‖ := hmin u' v' huv' hG'
      rw [max_eq_left hle] at h1
      exact absurd h1 (not_le.mpr hmax')
    exact ⟨(norm_eq_of_minimising_max (cov := cov) hmet hG hle hmin').1.symm, hmin'⟩

end

end Submission.CutWitness
