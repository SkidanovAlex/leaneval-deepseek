import Mathlib
import Submission.Work.OddBound.PolygonChart
import Submission.ConjEnergy
import Submission.GExpRayZero
import Submission.GExpVelocity
import Submission.GExpRayIdent
import Submission.Work.OddBound.polygon.hasDerivAt_riemannianDist_sq_along
import Submission.Work.OddBound.polygon.riemannianDist_eq_toReal
import Submission.Work.OddBound.polygon.hasDerivAt_gonEnergy_update
import Submission.Work.OddBound.polygon.ray_step
import Submission.BrokenLength
import Submission.GeodesicSpeed

set_option backward.isDefEq.respectTransparency.types false

/-!
# Critical polygons are closed geodesics (first variation on the polygon model)

Main result: `Work.OddBound.polygon.isCritical_gonEnergy_geodesic`.  A critical polygon `w` all of
whose sides are shorter than a uniform injectivity radius `R` is *straight with equal sides*: the
broken geodesic through its vertices is a closed geodesic loop, of length `T = gonLength p w`,
unit speed, with `T ^ 2 = 2 * gonEnergy p w`, and the vertices are the samples `c (i * T / N)`.

The criticality is used only at the *interior* vertices (the vertex `w i` is the vertex `v_{i+1}`
of the polygon); nothing is required at the base point `v_0 = v_N = p`, where the loop may have a
corner.  Consequently the curve is smooth only on `[0,T]` and geodesic only on `(0,T)`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace Work.OddBound.polygon

open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open MeasureTheory
open scoped MeasureTheory Interval
open LeanEval.Geometry.SphereTheorem Submission.Geodesic Submission.JacobiGlobal Submission.GlobalExp Submission.Length Submission.InjRadius

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]
  [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M] [RegularSpace M]
  {cov : CovariantDerivative I E (TangentSpace I (M := M))}
  [CovariantDerivative.ContMDiffCovariantDerivative cov ∞]

/-! ## Elementary facts about the distance and the polygon vertices -/

/-- Symmetry of the Riemannian distance. -/
lemma riemannianDist_symm (x y : M) :
    Submission.Distance.riemannianDist (I := I) x y
      = Submission.Distance.riemannianDist (I := I) y x := by
  rw [riemannianDist_eq_toReal (I := I) x y, riemannianDist_eq_toReal (I := I) y x,
    Manifold.riemannianEDist_comm]

/-- **The exponential-logarithm of a point at distance below the injectivity radius.** -/
lemma exists_GExp_eq_of_dist_lt (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov)
    (htor : cov.torsion = 0) {x y : M} {R : ℝ} (hinj : InjAtLeast hmet x R)
    (hd : Submission.Distance.riemannianDist (I := I) x y < R) :
    ∃ u : TangentSpace I x, GExp (cov := cov) hmet x u = y ∧
      ‖u‖ = Submission.Distance.riemannianDist (I := I) x y := by
  have hRpos : 0 < R := lt_of_le_of_lt (Submission.Distance.riemannianDist_nonneg (I := I) x y) hd
  have hfin : Manifold.riemannianEDist I x y ≠ ⊤ :=
    (Submission.HopfRinow.riemannianEDist_lt_top (cov := cov) hmet htor x y).ne
  have hd' : Manifold.riemannianEDist I x y < ENNReal.ofReal R := by
    rw [← ENNReal.ofReal_toReal hfin, ← riemannianDist_eq_toReal (I := I) x y]
    exact (ENNReal.ofReal_lt_ofReal_iff hRpos).mpr hd
  obtain ⟨u, ⟨huG, hud⟩, -⟩ :=
    Submission.InjRadius.exists_unique_GExp_of_injAtLeast hmet htor hinj hd'
  refine ⟨u, huG, ?_⟩
  have h : Submission.Distance.riemannianDist (I := I) x y = ‖u‖ := by
    rw [riemannianDist_eq_toReal (I := I) x y, hud, ENNReal.toReal_ofReal (norm_nonneg u)]
  exact h.symm

/-- The side length is the distance between consecutive vertices. -/
lemma gonSideLen_def' {N : ℕ} (p : M) (w : Fin (N - 1) → M) (i : ℕ) :
    gonSideLen (I := I) p w i = Submission.Distance.riemannianDist (I := I)
      (gonVert p w i) (gonVert p w (i + 1)) := rfl

/-- The vertex `i+1` of the polygon is the interior vertex `w i`. -/
lemma gonVert_succ_apply {N : ℕ} (p : M) (w : Fin (N - 1) → M) (i : Fin (N - 1)) :
    gonVert p w ((i : ℕ) + 1) = w i := gonVert_succ p w i.2

/-- Updating the interior vertex `w i` does not change the vertex `m` for `m ≠ i + 1`. -/
lemma gonVert_update_of_ne {N : ℕ} (p : M) (w : Fin (N - 1) → M) (i : Fin (N - 1)) (y : M)
    {m : ℕ} (hm : m ≠ (i : ℕ) + 1) :
    gonVert p (Function.update w i y) m = gonVert p w m := by
  unfold gonVert
  by_cases h : m = 0 ∨ N ≤ m
  · rw [dif_pos h, dif_pos h]
  · rw [dif_neg h, dif_neg h]
    rw [Function.update_apply]
    split_ifs with hc
    · exfalso
      have hv : m - 1 = (i : ℕ) := congrArg Fin.val hc
      have hm0 : m ≠ 0 := fun h0 => h (Or.inl h0)
      omega
    · rfl

/-- Updating the interior vertex `w i` sets the vertex `i+1` to the new value. -/
lemma gonVert_update_self {N : ℕ} (p : M) (w : Fin (N - 1) → M) (i : Fin (N - 1)) (y : M) :
    gonVert p (Function.update w i y) ((i : ℕ) + 1) = y := by
  unfold gonVert
  have h : ¬(((i : ℕ) + 1 = 0) ∨ N ≤ (i : ℕ) + 1) := by
    have := i.2
    omega
  rw [dif_neg h, Function.update_apply]
  split_ifs with hc
  · rfl
  · exfalso
    apply hc
    simp

/-! ## The logarithms of the sides -/

/-- The exponential-logarithm of the next vertex, from the vertex `m`. -/
lemma exists_GExp_log {N : ℕ} {p : M} {w : Fin (N - 1) → M} {R : ℝ}
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0)
    (hinj : ∀ x : M, InjAtLeast hmet x R)
    (hsmall : ∀ i : Fin N, gonSideLen (I := I) p w i < R)
    {m : ℕ} (hm : m < N) :
    ∃ u : TangentSpace I (gonVert p w m),
      GExp (cov := cov) hmet (gonVert p w m) u = gonVert p w (m + 1) ∧
      ‖u‖ = Submission.Distance.riemannianDist (I := I) (gonVert p w m) (gonVert p w (m + 1)) :=
  exists_GExp_eq_of_dist_lt hmet htor (hinj _) (hsmall ⟨m, hm⟩)

/-- **The logarithm of the side `m`**: the unique vector of norm `d(v_m, v_{m+1})` at `v_m` whose
exponential is `v_{m+1}` (unique because the side is shorter than the injectivity radius). -/
noncomputable def logVec {N : ℕ} {p : M} {w : Fin (N - 1) → M} {R : ℝ}
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0)
    (hinj : ∀ x : M, InjAtLeast hmet x R)
    (hsmall : ∀ i : Fin N, gonSideLen (I := I) p w i < R)
    (m : ℕ) (hm : m < N) : TangentSpace I (gonVert p w m) :=
  Classical.choose (exists_GExp_log hmet htor hinj hsmall hm)

lemma logVec_spec {N : ℕ} {p : M} {w : Fin (N - 1) → M} {R : ℝ}
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0)
    (hinj : ∀ x : M, InjAtLeast hmet x R)
    (hsmall : ∀ i : Fin N, gonSideLen (I := I) p w i < R)
    {m : ℕ} (hm : m < N) :
    GExp (cov := cov) hmet (gonVert p w m) (logVec hmet htor hinj hsmall m hm)
        = gonVert p w (m + 1) ∧
      ‖logVec hmet htor hinj hsmall m hm‖
        = Submission.Distance.riemannianDist (I := I) (gonVert p w m) (gonVert p w (m + 1)) :=
  Classical.choose_spec (exists_GExp_log hmet htor hinj hsmall hm)

/-- The logarithm does not depend on the proof of the side bound. -/
lemma logVec_congr {N : ℕ} {p : M} {w : Fin (N - 1) → M} {R : ℝ}
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0)
    (hinj : ∀ x : M, InjAtLeast hmet x R)
    (hsmall : ∀ i : Fin N, gonSideLen (I := I) p w i < R)
    {m : ℕ} (h1 h2 : m < N) :
    logVec hmet htor hinj hsmall m h1 = logVec hmet htor hinj hsmall m h2 := by
  have h1s := logVec_spec hmet htor hinj hsmall h1
  have h2s := logVec_spec hmet htor hinj hsmall h2
  have hm1 : ‖logVec hmet htor hinj hsmall m h1‖ < R := by
    rw [h1s.2]
    exact hsmall ⟨m, h1⟩
  have hm2 : ‖logVec hmet htor hinj hsmall m h2‖ < R := by
    rw [h2s.2]
    exact hsmall ⟨m, h2⟩
  have hgg : GExp (cov := cov) hmet (gonVert p w m) (logVec hmet htor hinj hsmall m h1)
      = GExp (cov := cov) hmet (gonVert p w m) (logVec hmet htor hinj hsmall m h2) :=
    calc GExp (cov := cov) hmet (gonVert p w m) (logVec hmet htor hinj hsmall m h1)
        = gonVert p w (m + 1) := h1s.1
      _ = GExp (cov := cov) hmet (gonVert p w m) (logVec hmet htor hinj hsmall m h2) := h2s.1.symm
  exact (hinj (gonVert p w m)) _ _ hm1 hm2 hgg

/-- The norm of the logarithm of a side is the side length. -/
lemma logVec_norm {N : ℕ} {p : M} {w : Fin (N - 1) → M} {R : ℝ}
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0)
    (hinj : ∀ x : M, InjAtLeast hmet x R)
    (hsmall : ∀ i : Fin N, gonSideLen (I := I) p w i < R)
    {m : ℕ} (hm : m < N) :
    ‖logVec hmet htor hinj hsmall m hm‖ = gonSideLen (I := I) p w m := by
  rw [(logVec_spec hmet htor hinj hsmall hm).2, gonSideLen_def']

/-! ## Transport of tangent vectors along an equality of base points -/

/-- The global exponential map is compatible with the transport of the initial vector along an
equality of base points. -/
lemma GExp_cast (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) {x y : M}
    (h : x = y) (v : TangentSpace I x) :
    GExp (cov := cov) hmet y (h ▸ v) = GExp (cov := cov) hmet x v := by
  cases h; rfl

/-- The norm of a transported tangent vector is unchanged. -/
lemma norm_cast_tangent {x y : M} (h : x = y) (v : TangentSpace I x) :
    ‖(h ▸ v : TangentSpace I y)‖ = ‖v‖ := by
  cases h; rfl

/-- Transport commutes with the negation of tangent vectors. -/
lemma neg_cast_tangent {x y : M} (h : x = y) (v : TangentSpace I x) :
    (h ▸ (-v) : TangentSpace I y) = -(h ▸ v) := by
  cases h; rfl

/-- Transport of tangent vectors along an equality of base points is injective. -/
lemma cast_tangent_injective {x y : M} (h : x = y) {a b : TangentSpace I x}
    (hab : (h ▸ a : TangentSpace I y) = (h ▸ b)) : a = b := by
  cases h; exact hab

/-! ## The first variation at an interior vertex -/

/-- **Criticality at an interior vertex makes the polygon straight there.**  At the interior vertex
`v_{i+1} = w i` the incoming and outgoing geodesic directions are opposite, and the two adjacent
sides have equal length. -/
theorem critical_straight' {N : ℕ} (hN : 2 ≤ N) {p : M} {w : Fin (N - 1) → M} {R : ℝ}
    (hR : 0 < R) (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov)
    (htor : cov.torsion = 0)
    (hinj : ∀ x : M, InjAtLeast hmet x R)
    (hsmall : ∀ i : Fin N, gonSideLen (I := I) p w i < R)
    (hcrit : GonCritical (I := I) p w) (i : Fin (N - 1)) (h : (i : ℕ) + 1 < N) :
    GExp (cov := cov) hmet (gonVert p w ((i : ℕ) + 1))
        (-(logVec hmet htor hinj hsmall ((i : ℕ) + 1) h)) = gonVert p w (i : ℕ) ∧
      gonSideLen (I := I) p w (i : ℕ) = gonSideLen (I := I) p w ((i : ℕ) + 1) := by
  classical
  have hNpos : 0 < N := by omega
  have hNne : (N : ℝ) ≠ 0 := by positivity
  have hq : gonVert p w ((i : ℕ) + 1) = w i := gonVert_succ_apply p w i
  -- the two logarithm vectors, in the `gonVert` convention
  have hd1 : Submission.Distance.riemannianDist (I := I) (gonVert p w ((i : ℕ) + 1))
      (gonVert p w ((i : ℕ) + 2)) < R :=
    hsmall ⟨(i : ℕ) + 1, by omega⟩
  obtain ⟨u₁, hu₁exp, hu₁n⟩ :=
    exists_GExp_eq_of_dist_lt hmet htor (hinj (gonVert p w ((i : ℕ) + 1))) hd1
  have hd2 : Submission.Distance.riemannianDist (I := I) (gonVert p w ((i : ℕ) + 1))
      (gonVert p w (i : ℕ)) < R := by
    have h2 : gonSideLen (I := I) p w (i : ℕ) < R := hsmall ⟨(i : ℕ), by omega⟩
    rw [gonSideLen_def',
      riemannianDist_symm (gonVert p w (i : ℕ)) (gonVert p w ((i : ℕ) + 1))] at h2
    exact h2
  obtain ⟨u₂, hu₂exp, hu₂n⟩ :=
    exists_GExp_eq_of_dist_lt hmet htor (hinj (gonVert p w ((i : ℕ) + 1))) hd2
  -- transport along `gonVert p w (i+1) = w i` to apply the first variation at `w i`
  have hup : GExp (cov := cov) hmet (w i) (hq ▸ u₁) = gonVert p w ((i : ℕ) + 2) := by
    rw [GExp_cast (cov := cov) hmet hq u₁]
    exact hu₁exp
  have hupn : ‖(hq ▸ u₁ : TangentSpace I (w i))‖
      = Submission.Distance.riemannianDist (I := I) (w i) (gonVert p w ((i : ℕ) + 2)) := by
    rw [norm_cast_tangent hq u₁, hu₁n, hq]
  have hum : GExp (cov := cov) hmet (w i) (hq ▸ u₂) = gonVert p w (i : ℕ) := by
    rw [GExp_cast (cov := cov) hmet hq u₂]
    exact hu₂exp
  have humn : ‖(hq ▸ u₂ : TangentSpace I (w i))‖
      = Submission.Distance.riemannianDist (I := I) (w i) (gonVert p w (i : ℕ)) := by
    rw [norm_cast_tangent hq u₂, hu₂n, hq]
  -- the first variation kills the component of `hq ▸ u₁ + hq ▸ u₂` in every direction
  have horth : ∀ ξ : TangentSpace I (w i),
      inner ℝ ((hq ▸ u₁) + (hq ▸ u₂)) ξ = 0 := by
    intro ξ
    by_cases hξ : ξ = 0
    · rw [hξ, inner_zero_right]
    · have hsm : ContMDiff 𝓘(ℝ) I ∞
          (fun t : ℝ => GExp (cov := cov) hmet (w i) (t • ξ)) :=
        Submission.ConjEnergy.contMDiff_GExp_smul hmet (w i) hξ
      have h0 : (fun t : ℝ => GExp (cov := cov) hmet (w i) (t • ξ)) 0 = w i := by simp
      have hder := hasDerivAt_gonEnergy_update (I := I) (cov := cov) hmet htor hN hR hinj
        hsmall i hup hupn hum humn hsm h0
      have hcv : curveVelocity (I := I)
          (fun t : ℝ => GExp (cov := cov) hmet (w i) (t • ξ)) 0 = ξ :=
        Submission.GExpVelocity.curveVelocity_GExp_smul_zero hmet (w i) hξ
      rw [hcv] at hder
      have hz : -(N : ℝ) * inner ℝ ((hq ▸ u₁) + (hq ▸ u₂)) ξ = 0 :=
        hder.unique (hcrit i _ hsm h0)
      rcases mul_eq_zero.mp hz with h1 | h1
      · exact absurd h1 (neg_ne_zero.mpr hNne)
      · exact h1
  have hsum : (hq ▸ u₁) + (hq ▸ u₂) = 0 :=
    inner_self_eq_zero.mp (horth ((hq ▸ u₁) + (hq ▸ u₂)))
  have hnegw : -(hq ▸ u₁) = (hq ▸ u₂) := by
    rw [eq_neg_of_add_eq_zero_left hsum, neg_neg]
  -- the same identity in the `gonVert` convention
  have hneg : -u₁ = u₂ := by
    refine cast_tangent_injective hq ?_
    rw [neg_cast_tangent]
    exact hnegw
  -- `logVec` is `u₁`
  have hlog : logVec (I := I) (cov := cov) hmet htor hinj hsmall ((i : ℕ) + 1) h = u₁ := by
    have h1 : ‖logVec (I := I) (cov := cov) hmet htor hinj hsmall ((i : ℕ) + 1) h‖ < R := by
      rw [(logVec_spec (I := I) (cov := cov) hmet htor hinj hsmall h).2]
      exact hd1
    have h2 : ‖u₁‖ < R := by rw [hu₁n]; exact hd1
    refine (hinj (gonVert p w ((i : ℕ) + 1))) _ _ h1 h2 ?_
    rw [(logVec_spec (I := I) (cov := cov) hmet htor hinj hsmall h).1]
    exact hu₁exp.symm
  constructor
  · rw [hlog, hneg]
    exact hu₂exp
  · have hnormeq : ‖u₁‖ = ‖u₂‖ := by rw [← hneg, norm_neg]
    rw [gonSideLen_def', gonSideLen_def',
      riemannianDist_symm (gonVert p w (i : ℕ)) (gonVert p w ((i : ℕ) + 1)), ← hu₂n, ← hu₁n]
    exact hnormeq.symm

/-! ## Equal sides and the length-energy relation -/

/-- The side lengths are constant. -/
lemma sides_eq_of_chain {N : ℕ} (hN : 1 ≤ N) {p : M} {w : Fin (N - 1) → M}
    (hchain : ∀ i : Fin (N - 1),
      gonSideLen (I := I) p w (i : ℕ) = gonSideLen (I := I) p w ((i : ℕ) + 1)) :
    ∀ m : ℕ, m < N → gonSideLen (I := I) p w m = gonSideLen (I := I) p w 0 := by
  intro m
  induction m with
  | zero => intro _; rfl
  | succ m ih =>
      intro hm
      have hm' : m < N - 1 := by omega
      have hch := hchain ⟨m, hm'⟩
      rw [← hch]
      exact ih (by omega)

/-- If all sides are equal then `2 E = L²` for the polygon length `L`. -/
lemma two_mul_gonEnergy_eq_sq {N : ℕ} {p : M} {w : Fin (N - 1) → M}
    (h0 : ∀ m : ℕ, m < N → gonSideLen (I := I) p w m = gonSideLen (I := I) p w 0) :
    2 * gonEnergy (I := I) p w = (gonLength (I := I) p w) ^ 2 := by
  have hsum : ∑ i : Fin N, gonSideLen (I := I) p w (i : ℕ)
      = (N : ℝ) * gonSideLen (I := I) p w 0 := by
    rw [Finset.sum_congr (rfl : (Finset.univ : Finset (Fin N)) = Finset.univ)
      (fun i _ => h0 (i : ℕ) i.2)]
    simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hsum2 : ∑ i : Fin N, (gonSideLen (I := I) p w (i : ℕ)) ^ 2
      = (N : ℝ) * (gonSideLen (I := I) p w 0) ^ 2 := by
    rw [Finset.sum_congr (rfl : (Finset.univ : Finset (Fin N)) = Finset.univ)
      (fun i _ => by rw [h0 (i : ℕ) i.2])]
    simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hlen : gonLength (I := I) p w = (N : ℝ) * gonSideLen (I := I) p w 0 := by
    rw [gonLength]
    exact hsum
  have hge : gonEnergy (I := I) p w
      = (N : ℝ) / 2 * ((N : ℝ) * (gonSideLen (I := I) p w 0) ^ 2) := by
    rw [gonEnergy, hsum2]
  rw [hlen, hge]
  ring

theorem isCritical_gonEnergy_geodesic
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M] [RegularSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0)
    {N : ℕ} (hN : 2 ≤ N) {p : M} {w : Fin (N - 1) → M}
    {R : ℝ} (hR : 0 < R)
    (hinj : ∀ x : M, Submission.InjRadius.InjAtLeast (I := I) (cov := cov) hmet x R)
    (hsmall : ∀ i : Fin N, Work.OddBound.gonSideLen (I := I) p w i < R)
    (hpos : 0 < Work.OddBound.gonEnergy (I := I) p w)
    (hcrit : Work.OddBound.GonCritical (I := I) p w) :
    ∃ (T : ℝ) (c : ℝ → M),
      0 < T ∧ T = Work.OddBound.gonLength (I := I) p w ∧
      2 * Work.OddBound.gonEnergy (I := I) p w = T ^ 2 ∧
      c 0 = p ∧ c T = p ∧
      ContMDiffOn 𝓘(ℝ) I ∞ c (Set.Icc (0 : ℝ) T) ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) T, Submission.Geodesic.IsGeodesicAt (I := I) cov c t) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) T, Submission.Geodesic.curveVelocity (I := I) c t ≠ 0) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) T, Submission.Length.curveSpeed (I := I) c t = 1) ∧
      (∀ i : Fin (N + 1), c (((i : ℕ) : ℝ) * T / (N : ℝ))
        = Work.OddBound.gonVert p w (i : ℕ)) ∧
      Work.OddBound.GonStraight (I := I) (cov := cov) hmet p w (T / (N : ℝ)) := by
  classical
  have hNpos : 0 < N := by omega
  have hN1 : 1 ≤ N := by omega
  have hNne : (N : ℝ) ≠ 0 := by positivity
  -- the straightness data at the interior vertices
  have hlink : ∀ k : ℕ, ∀ hk : k + 1 < N,
      GExp (cov := cov) hmet (gonVert p w (k + 1))
        (-(logVec (I := I) (cov := cov) hmet htor hinj hsmall (k + 1) hk)) = gonVert p w k := by
    intro k hk
    exact (critical_straight' (I := I) (cov := cov) hN hR hmet htor hinj hsmall hcrit
      ⟨k, by omega⟩ hk).1
  have hchain : ∀ i : Fin (N - 1),
      gonSideLen (I := I) p w (i : ℕ) = gonSideLen (I := I) p w ((i : ℕ) + 1) := by
    intro i
    exact (critical_straight' (I := I) (cov := cov) hN hR hmet htor hinj hsmall hcrit i
      (by omega)).2
  have hside : ∀ m : ℕ, m < N → gonSideLen (I := I) p w m = gonSideLen (I := I) p w 0 :=
    sides_eq_of_chain (I := I) hN1 hchain
  -- the length and the energy
  have hE : 2 * gonEnergy (I := I) p w = (gonLength (I := I) p w) ^ 2 :=
    two_mul_gonEnergy_eq_sq (I := I) hside
  have hGL : gonLength (I := I) p w = (N : ℝ) * gonSideLen (I := I) p w 0 := by
    rw [gonLength, Finset.sum_congr (rfl : (Finset.univ : Finset (Fin N)) = Finset.univ)
      (fun i _ => hside (i : ℕ) i.2)]
    simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hTnonneg : 0 ≤ gonLength (I := I) p w := by
    rw [gonLength]
    exact Finset.sum_nonneg (fun i _ => Submission.Distance.riemannianDist_nonneg (I := I) _ _)
  have hTpos : 0 < gonLength (I := I) p w := by
    refine lt_of_le_of_ne hTnonneg ?_
    have hsq : 0 < (gonLength (I := I) p w) ^ 2 := by rw [← hE]; linarith
    exact (sq_pos_iff.mp hsq).symm
  have hLpos : 0 < gonSideLen (I := I) p w 0 := by
    have hposR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
    have hmul : (0 : ℝ) < (N : ℝ) * gonSideLen (I := I) p w 0 := by
      rw [← hGL]; exact hTpos
    nlinarith [hmul]
  have hu0ne : logVec (I := I) (cov := cov) hmet htor hinj hsmall 0 hNpos ≠ 0 := by
    intro h0
    have hn := logVec_norm (I := I) (cov := cov) hmet htor hinj hsmall hNpos
    rw [h0, norm_zero] at hn
    rw [hside 0 hNpos] at hn
    exact hLpos.ne' hn.symm
  -- the ray and its basic properties
  have hray_sm : ContMDiff 𝓘(ℝ) I ∞
      (fun s : ℝ => GExp (cov := cov) hmet (gonVert p w 0) (s • logVec (I := I) (cov := cov) hmet htor hinj hsmall 0 hNpos)) :=
    Submission.ConjEnergy.contMDiff_GExp_smul hmet (gonVert p w 0) hu0ne
  have hray_md : ∀ s : ℝ, MDifferentiableAt 𝓘(ℝ) I
      (fun s : ℝ => GExp (cov := cov) hmet (gonVert p w 0) (s • logVec (I := I) (cov := cov) hmet htor hinj hsmall 0 hNpos)) s :=
    fun s => (hray_sm s).mdifferentiableAt (by simp)
  have hray_geo : ∀ s : ℝ, IsGeodesicAt (I := I) cov
      (fun s : ℝ => GExp (cov := cov) hmet (gonVert p w 0) (s • logVec (I := I) (cov := cov) hmet htor hinj hsmall 0 hNpos)) s :=
    fun s => Submission.GExpRayZero.isGeodesicAt_GExp_smul_all (cov := cov) hmet (gonVert p w 0) hu0ne s
  -- the tail identity, by induction over the vertices
  have htail : ∀ k : ℕ, ∀ hk : k < N, ∀ s ∈ Set.Icc (k : ℝ) (N : ℝ),
      GExp (cov := cov) hmet (gonVert p w 0) (s • logVec (I := I) (cov := cov) hmet htor hinj hsmall 0 hNpos)
        = GExp (cov := cov) hmet (gonVert p w k)
            ((s - (k : ℝ)) • logVec (I := I) (cov := cov) hmet htor hinj hsmall k hk) := by
    intro k
    induction k with
    | zero =>
        intro hk s _
        have hcong := logVec_congr (I := I) (cov := cov) hmet htor hinj hsmall (m := 0) hNpos hk
        simp only [hcong, Nat.cast_zero, sub_zero]
    | succ k ih =>
        intro hk s hs
        have hk' : k < N := by omega
        have hsk : (k : ℝ) ≤ s := by
          have h1 : ((k + 1 : ℕ) : ℝ) ≤ s := hs.1
          push_cast at h1
          linarith
        have hk' : k < N := by omega
        have hkR : (k : ℝ) + 1 < (N : ℝ) := by exact_mod_cast hk
        have hsk1 : (k : ℝ) + 1 ≤ s := by
          have h1 := hs.1
          push_cast at h1
          exact h1
        have hsN : s ≤ (N : ℝ) := hs.2
        have hik := ih hk' s ⟨by linarith [hsk1], hsN⟩
        rw [hik]
        have hl := hlink k hk
        have hul0 : logVec (I := I) (cov := cov) hmet htor hinj hsmall k hk' ≠ 0 := by
          intro h0
          have hn := logVec_norm (I := I) (cov := cov) hmet htor hinj hsmall hk'
          rw [h0, norm_zero] at hn
          rw [hside k hk'] at hn
          exact hLpos.ne' hn.symm
        have hRk : ‖logVec (I := I) (cov := cov) hmet htor hinj hsmall k hk'‖ < R := by
          rw [logVec_norm (I := I) (cov := cov) hmet htor hinj hsmall hk']
          exact hsmall ⟨k, hk'⟩
        have hvn : ‖logVec (I := I) (cov := cov) hmet htor hinj hsmall (k + 1) hk‖
            = ‖logVec (I := I) (cov := cov) hmet htor hinj hsmall k hk'‖ := by
          rw [logVec_norm (I := I) (cov := cov) hmet htor hinj hsmall hk,
            logVec_norm (I := I) (cov := cov) hmet htor hinj hsmall hk',
            hside (k + 1) hk, hside k hk']
        have hstep := ray_step (I := I) (cov := cov) hmet htor
          (x := gonVert p w k) (y := gonVert p w (k + 1))
          (u := logVec (I := I) (cov := cov) hmet htor hinj hsmall k hk')
          (v := logVec (I := I) (cov := cov) hmet htor hinj hsmall (k + 1) hk)
          (R := R) (T := (N : ℝ) - (k : ℝ) - 1)
          hul0 (logVec_spec (I := I) (cov := cov) hmet htor hinj hsmall hk').1 hRk
          (hinj _) hl hvn (by linarith [hkR])
        have hmem : (s - (k : ℝ)) ∈ Set.Icc (1 : ℝ) (((N : ℝ) - (k : ℝ) - 1) + 1) :=
          ⟨by linarith [hsk1], by linarith [hsN]⟩
        have hres := hstep (s - (k : ℝ)) hmem
        rw [hres, show s - (k : ℝ) - 1 = s - ((k + 1 : ℕ) : ℝ) by push_cast; ring]

  -- the vertices of the polygon are the samples of the ray
  have hver_le : ∀ i : ℕ, i ≤ N - 1 →
      GExp (cov := cov) hmet (gonVert p w 0) ((i : ℝ) • logVec (I := I) (cov := cov) hmet htor hinj hsmall 0 hNpos)
        = gonVert p w i := by
    intro i hi
    have hk : i < N := by omega
    have hmem : (i : ℝ) ∈ Set.Icc (i : ℝ) (N : ℝ) :=
      ⟨le_refl _, by exact_mod_cast (by omega : i ≤ N)⟩
    have h := htail i hk (i : ℝ) hmem
    simpa only [sub_self, zero_smul, GExp_zero] using h
  have hver_N : GExp (cov := cov) hmet (gonVert p w 0)
      ((N : ℝ) • logVec (I := I) (cov := cov) hmet htor hinj hsmall 0 hNpos) = gonVert p w N := by
    have hk : N - 1 < N := by omega
    have hmem : (N : ℝ) ∈ Set.Icc ((N - 1 : ℕ) : ℝ) (N : ℝ) :=
      ⟨by exact_mod_cast (by omega : N - 1 ≤ N), le_refl _⟩
    have h := htail (N - 1) hk (N : ℝ) hmem
    have hcast : ((N : ℝ) - ((N - 1 : ℕ) : ℝ)) = 1 := by
      have h1 : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ N)]; norm_num
      rw [h1]; ring
    rw [hcast, one_smul] at h
    rw [h]
    rw [(logVec_spec (I := I) (cov := cov) hmet htor hinj hsmall hk).1]
    congr 1
    omega
  have hver : ∀ i : ℕ, i ≤ N →
      GExp (cov := cov) hmet (gonVert p w 0) ((i : ℝ) • logVec (I := I) (cov := cov) hmet htor hinj hsmall 0 hNpos)
        = gonVert p w i := by
    intro i hi
    rcases lt_or_eq_of_le hi with hlt | heq
    · exact hver_le i (by omega)
    · rw [heq]; exact hver_N
  -- continuity and geodesy of the curve
  have hcont : ContMDiffOn 𝓘(ℝ) I ∞
      (fun t : ℝ => GExp (cov := cov) hmet (gonVert p w 0)
        ((((N : ℝ) / gonLength (I := I) p w) * t) • logVec (I := I) (cov := cov) hmet htor hinj hsmall 0 hNpos))
      (Set.Icc (0 : ℝ) (gonLength (I := I) p w)) := by
    have h2 : ContMDiff 𝓘(ℝ) 𝓘(ℝ) ∞
        (fun t : ℝ => ((N : ℝ) / gonLength (I := I) p w) * t) :=
      contMDiff_const.mul contMDiff_id
    exact (hray_sm.comp h2).contMDiffOn
  have hgeo : ∀ t ∈ Set.Ioo (0 : ℝ) (gonLength (I := I) p w),
      IsGeodesicAt (I := I) cov
        (fun t : ℝ => GExp (cov := cov) hmet (gonVert p w 0)
          ((((N : ℝ) / gonLength (I := I) p w) * t) • logVec (I := I) (cov := cov) hmet htor hinj hsmall 0 hNpos)) t := by
    intro t _
    have hcne : (N : ℝ) / gonLength (I := I) p w ≠ 0 :=
      div_ne_zero hNne hTpos.ne'
    exact Submission.GlobalExp.isGeodesicAt_comp_mul (cov := cov)
      (γ := fun s : ℝ => GExp (cov := cov) hmet (gonVert p w 0) (s • logVec (I := I) (cov := cov) hmet htor hinj hsmall 0 hNpos))
      (c := (N : ℝ) / gonLength (I := I) p w) (t := t) hcne
      (Filter.Eventually.of_forall (fun s => hray_md _)) (hray_geo _)
  -- the speed is one
  have hspeed : ∀ t : ℝ, curveSpeed (I := I)
      (fun t : ℝ => GExp (cov := cov) hmet (gonVert p w 0)
        ((((N : ℝ) / gonLength (I := I) p w) * t) • logVec (I := I) (cov := cov) hmet htor hinj hsmall 0 hNpos)) t = 1 := by
    intro t
    have hcpos : (0 : ℝ) < (N : ℝ) / gonLength (I := I) p w :=
      div_pos (by exact_mod_cast hNpos) hTpos
    have h1 := Submission.Length.curveSpeed_comp_mul_add (I := I)
      (γ := fun s : ℝ => GExp (cov := cov) hmet (gonVert p w 0)
        (s • logVec (I := I) (cov := cov) hmet htor hinj hsmall 0 hNpos))
      (c := (N : ℝ) / gonLength (I := I) p w) (d := 0) (t := t) hcpos (hray_md _)
    simp only [add_zero] at h1
    have h2 : curveSpeed (I := I)
        (fun s : ℝ => GExp (cov := cov) hmet (gonVert p w 0)
          (s • logVec (I := I) (cov := cov) hmet htor hinj hsmall 0 hNpos))
        (((N : ℝ) / gonLength (I := I) p w) * t)
        = ‖logVec (I := I) (cov := cov) hmet htor hinj hsmall 0 hNpos‖ :=
      Submission.BrokenLength.curveSpeed_GExp_ray (cov := cov) hmet (gonVert p w 0) hu0ne
        (((N : ℝ) / gonLength (I := I) p w) * t)
    rw [h1, h2, logVec_norm (I := I) (cov := cov) hmet htor hinj hsmall hNpos, hGL]
    field_simp
  have hvel : ∀ t ∈ Set.Icc (0 : ℝ) (gonLength (I := I) p w),
      curveVelocity (I := I)
        (fun t : ℝ => GExp (cov := cov) hmet (gonVert p w 0)
          ((((N : ℝ) / gonLength (I := I) p w) * t) • logVec (I := I) (cov := cov) hmet htor hinj hsmall 0 hNpos)) t ≠ 0 := by
    intro t _
    intro h0
    have hs := hspeed t
    rw [Submission.GeodesicSpeed.curveSpeed_eq_norm, h0, norm_zero] at hs
    norm_num at hs
  -- the vertices of the curve
  have hvertex : ∀ i : Fin (N + 1),
      (fun t : ℝ => GExp (cov := cov) hmet (gonVert p w 0)
        ((((N : ℝ) / gonLength (I := I) p w) * t) • logVec (I := I) (cov := cov) hmet htor hinj hsmall 0 hNpos))
        (((i : ℕ) : ℝ) * gonLength (I := I) p w / (N : ℝ)) = gonVert p w (i : ℕ) := by
    intro i
    have hscalar : ((N : ℝ) / gonLength (I := I) p w)
        * (((i : ℕ) : ℝ) * gonLength (I := I) p w / (N : ℝ)) = ((i : ℕ) : ℝ) := by
      field_simp
    show GExp (cov := cov) hmet (gonVert p w 0)
      ((((N : ℝ) / gonLength (I := I) p w) * (((i : ℕ) : ℝ) * gonLength (I := I) p w / (N : ℝ)))
        • logVec (I := I) (cov := cov) hmet htor hinj hsmall 0 hNpos) = gonVert p w (i : ℕ)
    rw [hscalar]
    exact hver (i : ℕ) (Nat.lt_succ_iff.mp i.2)
  -- the straightness conclusion
  have hGS : GonStraight (I := I) (cov := cov) hmet p w
      (gonLength (I := I) p w / (N : ℝ)) := by
    refine ⟨?_, ?_⟩
    · intro i
      rw [hside (i : ℕ) i.2, hGL]
      field_simp
    · intro i
      refine ⟨logVec (I := I) (cov := cov) hmet htor hinj hsmall ((i : ℕ) + 1) (by omega), ?_, ?_, ?_⟩
      · rw [logVec_norm (I := I) (cov := cov) hmet htor hinj hsmall (by omega),
          hside ((i : ℕ) + 1) (by omega), hGL]
        field_simp
      · exact (logVec_spec (I := I) (cov := cov) hmet htor hinj hsmall (by omega)).1
      · exact hlink (i : ℕ) (by omega)
  refine ⟨gonLength (I := I) p w,
    fun t : ℝ => GExp (cov := cov) hmet (gonVert p w 0)
      ((((N : ℝ) / gonLength (I := I) p w) * t) • logVec (I := I) (cov := cov) hmet htor hinj hsmall 0 hNpos),
    hTpos, rfl, hE, ?_, ?_, hcont, hgeo, hvel, (fun t _ => hspeed t), hvertex, hGS⟩
  · simp
  · have hNT : ((N : ℝ) / gonLength (I := I) p w) * gonLength (I := I) p w = (N : ℝ) :=
      div_mul_cancel₀ (N : ℝ) hTpos.ne'
    show GExp (cov := cov) hmet (gonVert p w 0)
      ((((N : ℝ) / gonLength (I := I) p w) * gonLength (I := I) p w) • logVec (I := I) (cov := cov) hmet htor hinj hsmall 0 hNpos) = p
    rw [hNT, hver_N]
    exact gonVert_of_le p w (le_refl N)

end Work.OddBound.polygon
