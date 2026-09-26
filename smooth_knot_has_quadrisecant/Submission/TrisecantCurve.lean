import ChallengeDeps
import Submission.Helpers
import Submission.KnotMap
import Submission.CollinearityMap
import Submission.Transversality
import Submission.Commons.Analysis.CrossProduct.cross3_contDiff
import Submission.Commons.Analysis.Calculus.Deriv.continuous_deriv_of_contDiff_one
import Submission.Commons.Analysis.InnerProductSpace.gram_det_ne_zero_of_linearIndependent
import Submission.Commons.LinearAlgebra.Span.surjective_of_two_independent_in_range
import Submission.Commons.Analysis.Calculus.FDeriv.fderiv_along_axis_eq_deriv
import Submission.Commons.LinearAlgebra.LinearIndependent.linearIndependent_pair_prod_of_det_ne_zero
import Submission.Commons.Analysis.InnerProductSpace.eq_zero_of_inner_eq_zero_of_span_top
import Submission.Commons.LinearAlgebra.Span.span_top_of_three_independent
import Mathlib.Topology.Algebra.Module.FiniteDimension

open LeanEval.KnotTheory.Quadrisecant
open scoped Matrix
open Commons.Analysis.Calculus.FDeriv
open Commons.LinearAlgebra.LinearIndependent
set_option maxHeartbeats 800000

/-!
# Layer A (viii) — milestone 1: the local smooth-curve structure of `Φ⁻¹(0)`

**Target (unproved, recorded here precisely).**  Let `r` be a smooth knot and
let `(a, b, m)` be real parameters with

* `Φ(a,b,m) = 0` (the three knot points are collinear), with the three knot
  points pairwise distinct, and
* the knot in **general position at the triple** (`TrisecantGeneralPosition`):
  the velocities `v(a), v(b), v(m)` and the chord direction `Z = r a − r b`
  are positioned so that the directional derivative of `Φ` at `(a,b,m)` has
  rank two — by the rank-two criterion
  (`rank_two_criterion_at_collinearity_zero`, Transversality.lean) exactly:
  two of the velocity-cross vectors `v(pᵢ) × Z` are linearly independent.

Then a neighbourhood of `(a,b,m)` in the *off-diagonal* part of `Φ⁻¹(0)` is
the image of a smooth (injectively parametrised) curve passing through
`(a,b,m)` — the local structure of the trisecant locus with its middle
parameter, from which the 1-manifold structure of `O` is assembled.  The
proof is the constant-rank / implicit-function theorem applied to the two
independent partials of `Φ` (Milestone-1 theorem `LocalSmoothCurveTheorem`
below; its formal proof requires the constant-rank/IFT machinery of
Mathlib's calculus on `RealParamTriple` and is future work).

This module fixes the vocabulary:

* `RealOffDiagonalTriples` — triples whose three knot points are pairwise
  distinct (in real parameters: the three difference vectors are nonzero);
* `TrisecantGeneralPosition` — the genericity predicate (rank-two criterion
  + pairwise distinct images) we can already define and verify;
* `VelocityCrossGeneralPosition` — the geometric form of the criterion (two
  independent velocity-cross vectors), shown equivalent under `Φ = 0`
  (`generalPosition_iff_velocityCrossGeneralPosition` — proved, chaining the
  rank-two criterion);
* `TrisecantLocalCurve` — the precise local-curve statement over a real
  parameter triple (its meaning is spelled out in the doc comment below);
* `LocalSmoothCurveTheorem` — the Milestone-1 target proposition (documented;
  unproved until the IFT/constant-rank application is formalized).

Everything here is elementary and verified (no axioms, no `sorry`).
-/

noncomputable section

namespace LeanEval.KnotTheory.Quadrisecant

/-- A real triple `(a, b, m)` whose three knot points are pairwise distinct
(equivalently the three difference vectors `r a − r b`, `r a − r m`,
`r m − r b` are all nonzero). -/
def RealOffDiagonalTriples (r : ℝ → Space) : Set RealParamTriple :=
  {q | r q.1 - r q.2.1 ≠ 0 ∧ r q.1 - r q.2.2 ≠ 0 ∧ r q.2.2 - r q.2.1 ≠ 0}

/-- **The genericity predicate at a collinear triple**: the three knot
points are pairwise distinct and the rank-two criterion holds — the
velocities and the chord direction are in general position, i.e. the
directional derivative of `Φ` at `(a,b,m)` has rank two. -/
def TrisecantGeneralPosition (r : ℝ → Space) (a b m : ℝ) : Prop :=
  r a - r b ≠ 0 ∧ r a - r m ≠ 0 ∧ r m - r b ≠ 0 ∧ PartialRankTwo r a b m

/-- The geometric form of the criterion: two of the velocity-cross vectors
`v(pᵢ) × (r a − r b)` are linearly independent. -/
def VelocityCrossGeneralPosition (r : ℝ → Space) (a b m : ℝ) : Prop :=
  ∃ i j : Fin 3, i ≠ j ∧
    LinearIndependent ℝ ![cross3 (velocity r (collParam a b m i)) (r a - r b),
      cross3 (velocity r (collParam a b m j)) (r a - r b)]

/-- At a zero of `Φ` with pairwise distinct knot points, general position in
the rank-two sense is exactly general position in the velocity-cross sense:
`generalPosition ∧ Φ = 0 ⟺ the geometric (velocity-cross) form`.  This is
the rank-two criterion of `Transversality.lean` in the genericity language. -/
theorem generalPosition_iff_velocityCrossGeneralPosition {r : ℝ → Space} {a b m : ℝ}
    (hΦ : collinearityValue r a b m = 0) :
    TrisecantGeneralPosition r a b m ↔
      (RealOffDiagonalTriples r (a, (b, m)) ∧ VelocityCrossGeneralPosition r a b m) := by
  constructor
  · intro hGP
    rcases hGP with ⟨hZ, hW, hmb, hrank⟩
    constructor
    · exact ⟨hZ, hW, hmb⟩
    · exact (rank_two_criterion_at_collinearity_zero hZ hW hmb hΦ).mp hrank
  · rintro ⟨hOff, hVC⟩
    rcases hOff with ⟨hZ, hW, hmb⟩
    rcases hVC with ⟨i, j, hij, hLI⟩
    exact ⟨hZ, hW, hmb, (rank_two_criterion_at_collinearity_zero hZ hW hmb hΦ).mpr ⟨i, j, hij, hLI⟩⟩

/-- **The precise local-curve statement** over a real triple `p = (a, b, m)`:
if `p` is a collinear off-diagonal triple, then some open neighbourhood `U`
of `p` meets the off-diagonal zero set of `Φ` exactly in the image of a
`C¹` curve `γ` through `p`; the curve lies inside `U` and inside the
off-diagonal zero set, is injective on its open interval `(lo, hi)`, and
covers all of the off-diagonal zeros of `Φ` in `U`.  (For a *regular* local
curve one further requires `γ'(0) ≠ 0`; the rank-two hypothesis makes this
the transversal part of the trisecant locus with its middle parameter.) -/
def TrisecantLocalCurve (r : ℝ → Space) (p : RealParamTriple) : Prop :=
  collinearityMap r p = 0 ∧ p ∈ RealOffDiagonalTriples r ∧
    ∃ U : Set RealParamTriple, IsOpen U ∧ p ∈ U ∧
      ∃ lo hi : ℝ, lo < 0 ∧ 0 < hi ∧ ∃ γ : ℝ → RealParamTriple,
        ContDiffOn ℝ 1 γ (Set.Ioo lo hi) ∧ Set.InjOn γ (Set.Ioo lo hi) ∧
          γ 0 = p ∧
          (∀ t ∈ Set.Ioo lo hi,
            γ t ∈ U ∧ collinearityMap r (γ t) = 0 ∧ γ t ∈ RealOffDiagonalTriples r) ∧
          ∀ q ∈ U, collinearityMap r q = 0 → q ∈ RealOffDiagonalTriples r →
            ∃ t ∈ Set.Ioo lo hi, γ t = q

/-- **Milestone-1 target proposition** (documented; unproved): a knot in
general position at a collinear off-diagonal triple has, locally at that
triple, the structure of a `C¹` curve of off-diagonal zeros of `Φ`.  The
proof will apply the constant-rank / implicit-function theorem to the
collinearity map `Φ` at the triple, using the rank-two criterion
(`PartialRankTwo_iff_velocityCross_pair`,
`rank_two_criterion_at_collinearity_zero`) as the rank hypothesis. -/
def LocalSmoothCurveTheorem (r : ℝ → Space) : Prop :=
  ∀ (a b m : ℝ), TrisecantGeneralPosition r a b m →
    collinearityValue r a b m = 0 → TrisecantLocalCurve r (a, (b, m))

/-! ### The first constant-rank lemma: rank two persists locally

The IFT/constant-rank application needs the rank condition to hold not just
at `p` but on a whole neighbourhood: if two of the partials of `Φ` are
linearly independent at `p`, the same two partials remain independent on an
open set around `p`.  The proof: independence of two vectors of `ℝ³` is the
non-vanishing of their cross product (the fleet lemma
`cross3_ne_zero_iff_linearIndependent`, in flight), the map
`q ↦ (∂-partials at q) × (∂-partials at q)` is continuous (the partials are
continuous functions of the triple once the velocity is — the fleet lemma
`continuous_deriv_of_contDiff_one`, in flight — and the cross product
operator is continuous), and the non-zero set of a continuous function is
open.  These lemmas are stated with the two fleet facts as explicit
hypotheses so they are provable today; the corollaries discharging the
hypotheses will be added when the fleet lemmas land. -/

/-- The cross product operator on `Space × Space` is continuous (from the
commons `cross3_contDiff`). -/
lemma continuous_cross3 : Continuous (fun p : Space × Space => cross3 p.1 p.2) := by
  simpa [cross3] using (Commons.Analysis.CrossProduct.cross3_contDiff).continuous

/-- The first partial `∂_a`, viewed as a function of the real parameter
triple, is continuous whenever the knot and its velocity are continuous. -/
lemma continuous_collPartialA_of {r : ℝ → Space} (hr : Continuous r)
    (hvel : Continuous (fun t : ℝ => velocity r t)) :
    Continuous (fun q : RealParamTriple => collPartialA r q.1 q.2.1 q.2.2) := by
  unfold collPartialA
  have hcv : Continuous (fun p : Space × Space => cross3 p.1 p.2) := continuous_cross3
  have h1 : Continuous (fun q : RealParamTriple => (velocity r q.1, r q.1 - r q.2.2)) := by
    fun_prop
  have h2 : Continuous (fun q : RealParamTriple => (r q.1 - r q.2.1, velocity r q.1)) := by
    fun_prop
  exact (hcv.comp h1).add (hcv.comp h2)

/-- The middle partial `∂_b`, viewed as a function of the real parameter
triple, is continuous whenever the knot and its velocity are continuous. -/
lemma continuous_collPartialB_of {r : ℝ → Space} (hr : Continuous r)
    (hvel : Continuous (fun t : ℝ => velocity r t)) :
    Continuous (fun q : RealParamTriple => collPartialB r q.1 q.2.1 q.2.2) := by
  unfold collPartialB
  have hcv : Continuous (fun p : Space × Space => cross3 p.1 p.2) := continuous_cross3
  have h1 : Continuous (fun q : RealParamTriple => (r q.1 - r q.2.2, velocity r q.2.1)) := by
    fun_prop
  exact hcv.comp h1

/-- **First constant-rank lemma**: if the first and middle partials of `Φ`
are linearly independent at the triple `(a, b, m)`, then they remain
independent on an open neighbourhood of that triple (the rank-two condition
is open).  Stated with the continuity-of-velocity and the
independence⟺cross-nonzero facts as explicit hypotheses (discharged by the
commons lemmas once they land). -/
theorem exists_isOpen_partialsAB_independent {r : ℝ → Space} (hr : Continuous r)
    (hvel : Continuous (fun t : ℝ => velocity r t))
    (hLI : ∀ (u v : Space), LinearIndependent ℝ ![u, v] ↔ cross3 u v ≠ 0)
    (a b m : ℝ)
    (hAB : LinearIndependent ℝ ![collPartialA r a b m, collPartialB r a b m]) :
    ∃ U : Set RealParamTriple, IsOpen U ∧ (a, (b, m)) ∈ U ∧
      ∀ q ∈ U,
        LinearIndependent ℝ ![collPartialA r q.1 q.2.1 q.2.2, collPartialB r q.1 q.2.1 q.2.2] := by
  let G : RealParamTriple → Space := fun q =>
    cross3 (collPartialA r q.1 q.2.1 q.2.2) (collPartialB r q.1 q.2.1 q.2.2)
  have hc0 : G (a, (b, m)) ≠ 0 := by
    dsimp [G]
    exact (hLI (collPartialA r a b m) (collPartialB r a b m)).mp hAB
  have hG : Continuous G := by
    dsimp [G]
    exact continuous_cross3.comp
      (Continuous.prodMk (continuous_collPartialA_of hr hvel) (continuous_collPartialB_of hr hvel))
  let U : Set RealParamTriple := G ⁻¹' (({0} : Set Space)ᶜ)
  have hU : IsOpen U := by
    dsimp [U]
    exact ((isClosed_singleton (x := (0 : Space))).isOpen_compl).preimage hG
  refine ⟨U, hU, ?_, ?_⟩
  · dsimp [U]
    simpa using hc0
  · intro q hq
    dsimp [U] at hq
    exact (hLI (collPartialA r q.1 q.2.1 q.2.2) (collPartialB r q.1 q.2.1 q.2.2)).mpr hq

/-! ### Discharging the hypotheses (fleet facts landed)

Both fleet facts have landed: `continuous_deriv_of_contDiff_one` (a `C¹`
curve has a continuous derivative, so a smooth knot has a continuous
velocity) and the local cross-product/independence criterion (proved here
self-containedly; the commons copy `cross3_ne_zero_iff_linearIndependent`
is in flight).  The corollary discharges the hypotheses of the openness
lemma and gives the clean statement. -/

/-- In `ℝ³`, two vectors are linearly independent iff their cross product is
nonzero (local version, through the `WithLp` equivalence and Mathlib's
function-space criterion). -/
lemma cross3_ne_zero_iff_linearIndependent_local (u v : Space) :
    cross3 u v ≠ 0 ↔ LinearIndependent ℝ ![u, v] := by
  have h1 : cross3 u v ≠ 0 ↔ WithLp.ofLp u ⨯₃ WithLp.ofLp v ≠ 0 := by
    unfold cross3
    exact (WithLp.toLp_eq_zero (p := 2) (V := Fin 3 → ℝ)
      (x := WithLp.ofLp u ⨯₃ WithLp.ofLp v)).not
  have h2 : WithLp.ofLp u ⨯₃ WithLp.ofLp v ≠ 0 ↔
      LinearIndependent ℝ ![WithLp.ofLp u, WithLp.ofLp v] :=
    crossProduct_ne_zero_iff_linearIndependent (F := ℝ) (v := WithLp.ofLp u)
      (w := WithLp.ofLp v)
  have h3 : LinearIndependent ℝ ![WithLp.ofLp u, WithLp.ofLp v] ↔
      LinearIndependent ℝ ![u, v] := by
    let f : Space →ₗ[ℝ] (Fin 3 → ℝ) := (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).toLinearMap
    have hker : LinearMap.ker f = ⊥ := by
      dsimp [f]
      exact LinearMap.ker_eq_bot.mpr (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).injective
    have hiff : LinearIndependent ℝ (fun i : Fin 2 => f (![u, v] i)) ↔
        LinearIndependent ℝ (fun i : Fin 2 => ![u, v] i) :=
      f.linearIndependent_iff (v := fun i : Fin 2 => ![u, v] i) hker
    have hfam : (fun i : Fin 2 => f (![u, v] i)) =
        fun i : Fin 2 => (![WithLp.ofLp u, WithLp.ofLp v] : Fin 2 → (Fin 3 → ℝ)) i := by
      funext i
      fin_cases i <;> simp [f]
    rw [hfam] at hiff
    simpa using hiff
  exact (h1.trans h2).trans h3

/-- **Open persistence of rank two, clean form**: a smooth knot has a
continuous velocity (`continuous_deriv_of_contDiff_one`, commons) and
independence is cross-nonzero (local criterion), so the two hypotheses of
`exists_isOpen_partialsAB_independent` are discharged: if the first and
middle partials of `Φ` are independent at the triple, they remain
independent on an open neighbourhood. -/
theorem exists_isOpen_partialsAB_independent_smooth {r : ℝ → Space} (h : IsSmoothKnot r)
    (a b m : ℝ)
    (hAB : LinearIndependent ℝ ![collPartialA r a b m, collPartialB r a b m]) :
    ∃ U : Set RealParamTriple, IsOpen U ∧ (a, (b, m)) ∈ U ∧
      ∀ q ∈ U,
        LinearIndependent ℝ ![collPartialA r q.1 q.2.1 q.2.2, collPartialB r q.1 q.2.1 q.2.2] := by
  apply exists_isOpen_partialsAB_independent
  · exact h.smooth.continuous
  · have h1 : ContDiff ℝ 1 r := ContDiff.of_le h.smooth (by exact le_top)
    simpa [velocity] using (Commons.Analysis.Calculus.Deriv.continuous_deriv_of_contDiff_one h1)
  · intro u v
    exact (cross3_ne_zero_iff_linearIndependent_local u v).symm
  · exact hAB

/-! ### Pair-general open persistence of rank two

`PartialRankTwo` witnesses *some* pair of independent partials; for a
constant-rank application the rank-two condition must persist on a
neighbourhood for that same pair.  The generic helper
`exists_isOpen_pair_independent` works for any two continuous partial
selectors, so the Fin-indexed pair from `PartialRankTwo` is handled by
enumeration (`fin_cases`), giving
`partialRankTwo_persists_smooth`: rank two at a triple persists on an open
neighbourhood. -/

/-- Continuity of the third partial `∂_m` as a function of the triple. -/
lemma continuous_collPartialM_of {r : ℝ → Space} (hr : Continuous r)
    (hvel : Continuous (fun t : ℝ => velocity r t)) :
    Continuous (fun q : RealParamTriple => collPartialM r q.1 q.2.1 q.2.2) := by
  unfold collPartialM
  have hcv : Continuous (fun p : Space × Space => cross3 p.1 p.2) := continuous_cross3
  have h1 : Continuous (fun q : RealParamTriple => (velocity r q.2.2, r q.1 - r q.2.1)) := by
    fun_prop
  exact hcv.comp h1

/-- Generic: two continuous partial selectors whose values are independent at
`p` remain independent on an open neighbourhood of `p`. -/
lemma exists_isOpen_pair_independent {f g : RealParamTriple → Space}
    (hf : Continuous f) (hg : Continuous g)
    (hLI : ∀ (u v : Space), LinearIndependent ℝ ![u, v] ↔ cross3 u v ≠ 0)
    (p : RealParamTriple) (hfg : LinearIndependent ℝ ![f p, g p]) :
    ∃ U : Set RealParamTriple, IsOpen U ∧ p ∈ U ∧
      ∀ q ∈ U, LinearIndependent ℝ ![f q, g q] := by
  let G : RealParamTriple → Space := fun q => cross3 (f q) (g q)
  have hc0 : G p ≠ 0 := (hLI (f p) (g p)).mp hfg
  have hG : Continuous G := continuous_cross3.comp (Continuous.prodMk hf hg)
  let U : Set RealParamTriple := G ⁻¹' (({0} : Set Space)ᶜ)
  have hU : IsOpen U := ((isClosed_singleton (x := (0 : Space))).isOpen_compl).preimage hG
  refine ⟨U, hU, ?_, ?_⟩
  · dsimp [U]
    simpa using hc0
  · intro q hq
    dsimp [U] at hq
    exact (hLI (f q) (g q)).mpr hq

/-! ### Rank two persists on a neighbourhood

With the per-index equalities `collPartial_eq_A/B/M` (Transversality) the
`fin_cases` enumeration over the `Fin 3` witness pair reduces cleanly, and
the generic helper `exists_isOpen_pair_independent` applies to whichever
ordered pair of selectors the witness names. -/

/-- **Rank two persists on a neighbourhood (clean, smooth form)**: at a
triple where `PartialRankTwo` holds, the same two partials remain
independent on an open neighbourhood — the open-rank condition the
constant-rank/IFT application to `Φ` requires. -/
theorem partialRankTwo_persists_smooth {r : ℝ → Space} (h : IsSmoothKnot r)
    (a b m : ℝ) (hP : PartialRankTwo r a b m) :
    ∃ U : Set RealParamTriple, IsOpen U ∧ (a, (b, m)) ∈ U ∧
      ∀ q ∈ U, PartialRankTwo r q.1 q.2.1 q.2.2 := by
  have hr : Continuous r := h.smooth.continuous
  have h1c : ContDiff ℝ 1 r := ContDiff.of_le h.smooth (by exact le_top)
  have hvel : Continuous (fun t : ℝ => velocity r t) := by
    simpa [velocity] using (Commons.Analysis.Calculus.Deriv.continuous_deriv_of_contDiff_one h1c)
  have hLI : ∀ (u v : Space), LinearIndependent ℝ ![u, v] ↔ cross3 u v ≠ 0 := by
    intro u v
    exact (cross3_ne_zero_iff_linearIndependent_local u v).symm
  rcases hP with ⟨i, j, hij, hLIij⟩
  fin_cases i <;> fin_cases j
  · exact False.elim (hij rfl)
  · rcases exists_isOpen_pair_independent (f := fun q => collPartialA r q.1 q.2.1 q.2.2)
      (g := fun q => collPartialB r q.1 q.2.1 q.2.2)
      (continuous_collPartialA_of hr hvel) (continuous_collPartialB_of hr hvel)
      hLI (a, (b, m)) (by simpa [collPartial_eq_A r a b m, collPartial_eq_B r a b m] using hLIij)
      with ⟨U, hUo, hUp, hUpersist⟩
    refine ⟨U, hUo, hUp, ?_⟩
    intro q hq
    exact ⟨0, 1, by decide, hUpersist q hq⟩
  · rcases exists_isOpen_pair_independent (f := fun q => collPartialA r q.1 q.2.1 q.2.2)
      (g := fun q => collPartialM r q.1 q.2.1 q.2.2)
      (continuous_collPartialA_of hr hvel) (continuous_collPartialM_of hr hvel)
      hLI (a, (b, m)) (by simpa [collPartial_eq_A r a b m, collPartial_eq_M r a b m] using hLIij)
      with ⟨U, hUo, hUp, hUpersist⟩
    refine ⟨U, hUo, hUp, ?_⟩
    intro q hq
    exact ⟨0, 2, by decide, hUpersist q hq⟩
  · rcases exists_isOpen_pair_independent (f := fun q => collPartialB r q.1 q.2.1 q.2.2)
      (g := fun q => collPartialA r q.1 q.2.1 q.2.2)
      (continuous_collPartialB_of hr hvel) (continuous_collPartialA_of hr hvel)
      hLI (a, (b, m)) (by simpa [collPartial_eq_B r a b m, collPartial_eq_A r a b m] using hLIij)
      with ⟨U, hUo, hUp, hUpersist⟩
    refine ⟨U, hUo, hUp, ?_⟩
    intro q hq
    exact ⟨1, 0, by decide, hUpersist q hq⟩
  · exact False.elim (hij rfl)
  · rcases exists_isOpen_pair_independent (f := fun q => collPartialB r q.1 q.2.1 q.2.2)
      (g := fun q => collPartialM r q.1 q.2.1 q.2.2)
      (continuous_collPartialB_of hr hvel) (continuous_collPartialM_of hr hvel)
      hLI (a, (b, m)) (by simpa [collPartial_eq_B r a b m, collPartial_eq_M r a b m] using hLIij)
      with ⟨U, hUo, hUp, hUpersist⟩
    refine ⟨U, hUo, hUp, ?_⟩
    intro q hq
    exact ⟨1, 2, by decide, hUpersist q hq⟩
  · rcases exists_isOpen_pair_independent (f := fun q => collPartialM r q.1 q.2.1 q.2.2)
      (g := fun q => collPartialA r q.1 q.2.1 q.2.2)
      (continuous_collPartialM_of hr hvel) (continuous_collPartialA_of hr hvel)
      hLI (a, (b, m)) (by simpa [collPartial_eq_M r a b m, collPartial_eq_A r a b m] using hLIij)
      with ⟨U, hUo, hUp, hUpersist⟩
    refine ⟨U, hUo, hUp, ?_⟩
    intro q hq
    exact ⟨2, 0, by decide, hUpersist q hq⟩
  · rcases exists_isOpen_pair_independent (f := fun q => collPartialM r q.1 q.2.1 q.2.2)
      (g := fun q => collPartialB r q.1 q.2.1 q.2.2)
      (continuous_collPartialM_of hr hvel) (continuous_collPartialB_of hr hvel)
      hLI (a, (b, m)) (by simpa [collPartial_eq_M r a b m, collPartial_eq_B r a b m] using hLIij)
      with ⟨U, hUo, hUp, hUpersist⟩
    refine ⟨U, hUo, hUp, ?_⟩
    intro q hq
    exact ⟨2, 1, by decide, hUpersist q hq⟩
  · exact False.elim (hij rfl)

/-! ### Milestone-1 proof plan: local normal form of `Φ⁻¹(0)` near a rank-2 zero

The target `LocalSmoothCurveTheorem` will be proved by an implicit-function
argument in the following shape (recorded here; each step is a separate
formalization task):

* **Functional selection.**  At a general-position zero `(a₀,b₀,m₀)`, two
  partials of `Φ`, say `P₁, P₂ ∈ Space`, are linearly independent
  (`PartialRankTwo`).  The two linear functionals `ℓᵢ := ⟪·, Pᵢ⟫` have
  invertible 2×2 Gram matrix at the partials (`gram_det_ne_zero_of_
  linearIndependent`, delegated to the commons), so the reduced map
  `H := (ℓ₁ ∘ Φ, ℓ₂ ∘ Φ) : ℝ³ → ℝ²` has surjective derivative at the zero
  (its derivative on the `(a,b)` axes is the invertible Gram matrix).
* **Implicit function theorem.**  Mathlib's `ImplicitFunctionData` /
  `implicitFunctionDataOfComplemented` (Analysis/Calculus/Implicit.lean,
  a submersion regular-value theorem) applies to the strict derivative of
  `H` at the zero: locally `H⁻¹(0)` is the graph of a differentiable map
  over the 1-dimensional kernel direction, i.e. a curve through the zero.
* **Identification `Φ⁻¹(0) = H⁻¹(0)` near the zero (the redundancy
  step).**  For every triple `q`, `Φ(q) = (r q₁ − r q₂₁) × (r q₁ − r q₂₂)`
  is *automatically* orthogonal to the chord vector `r q₁ − r q₂₁`
  (`cross3 x y ⊥ x`, the commons `inner_cross3_self_left`).  On `H⁻¹(0)`
  it is also orthogonal to the frozen functionals' vectors `P_A, P_B`.
  At the base triple the three vectors `P_A, P_B, Z := r a − r b` span
  `Space` (3-dimensional): `P_A, P_B` are independent and both orthogonal
  to the nonzero chord `Z`, so `Z ∉ span{P_A,P_B}`; by continuity of the
  chord vector the same spanning holds for `P_A, P_B, r q₁ − r q₂₁` on a
  whole neighbourhood `U` of the triple (an open condition, e.g.
  `⟪cross3 P_A P_B, r q₁ − r q₂₁⟫ ≠ 0`).  For `q ∈ H⁻¹(0) ∩ U` the vector
  `Φ(q)` is then orthogonal to three spanning vectors of `Space`, hence
  `Φ(q) = 0`.  Conversely `Φ(q) = 0 ⇒ H(q) = 0` is trivial, so
  `Φ⁻¹(0) ∩ U = H⁻¹(0) ∩ U`: near a general-position zero the collinearity
  zero set of `Φ` is exactly the zero set of the reduced submersion `H`.
  (Note: this is NOT a constant-rank normal-form statement — no claim that
  `dΦ` stays rank 2 or that some "third component of Φ" vanishes; it is the
  cross-product geometry `Φ(q) ⊥ chord` together with the frozen-partial
  spanning that closes the argument.)
* **Regular-value curve.**  With `H⁻¹(0) = Φ⁻¹(0)` on `U` and `H` a
  submersion on `U` (its derivative keeps rank 2 there — the 2×2 Gram
  submatrix on the two chosen axes is continuous in `q` and invertible at
  `p`, cf. `partialRankTwo_persists_smooth`), Mathlib's
  regular-value/implicit-function layer (`ImplicitFunctionData`,
  Analysis/Calculus/Implicit.lean — a *regular-value* theorem for
  submersions, which does exist, unlike a constant-rank theorem) applies to
  `H` at the zero: `H⁻¹(0) ∩ U` is locally the graph of a differentiable
  map over the 1-dimensional tangent direction `ker dH`, i.e. an
  injectively parametrised `C¹` curve through the zero
  (`TrisecantLocalCurve`), completing `LocalSmoothCurveTheorem`.
  (Mathlib contains the inverse/regular-value and implicit-function layers
  only; the genuinely new analysis to formalize next is the identification
  step above — the spanning/orthogonality argument — and the explicit
  regular-value invocation producing a `C¹` curve parametrisation.)
-/

/-! ### Step 1 of the local-curve proof: the reduced map and its submersion data

At a general-position zero `(a₀,b₀,m₀)` of `Φ`, suppose the first two
partials `P_A = ∂_a Φ(p)`, `P_B = ∂_b Φ(p)` are linearly independent
(`PartialRankTwo`).  Step 1 packages the two linear functionals

    ℓ₁ := ⟪·, P_A⟫ ,  ℓ₂ := ⟪·, P_B⟫

(`collInnerFirst`/`collInnerSecond`) and the reduced map
`H(q) := (ℓ₁(Φ q), ℓ₂(Φ q)) : ℝ³ → ℝ²` (`collinearityInnerPair`, with the
partials frozen at the base point).  The submersion datum is that the
derivative of `H` at the zero is surjective: restricted to the `(a,b)`
coordinate plane it has matrix equal to the 2×2 Gram matrix of `P_A, P_B`
(rows `ℓ₁,ℓ₂`, columns the `a`- and `b`-directions), whose determinant is
nonzero exactly by the (committed commons) Gram-invertibility lemma for an
independent pair (`reducedSubmersion_gram_invertible`).  Steps 2–3
(recorded above) then invoke Mathlib's submersion/regular-value machinery
and the constant-rank redundancy to produce the local curve. -/

/-- The functional `ℓ₁ := ⟪·, P_A⟫` (pairing against the first partial). -/
def collInnerFirst (r : ℝ → Space) (a b m : ℝ) : Space → ℝ :=
  fun u => inner ℝ u (collPartialA r a b m)

/-- The functional `ℓ₂ := ⟪·, P_B⟫` (pairing against the second partial). -/
def collInnerSecond (r : ℝ → Space) (a b m : ℝ) : Space → ℝ :=
  fun u => inner ℝ u (collPartialB r a b m)

/-- **The reduced map** `H(q) = (ℓ₁(Φ q), ℓ₂(Φ q)) : ℝ³ → ℝ²` of the
collinearity map, with the partials `P_A, P_B` frozen at the base triple
`(a, b, m)`.  Its zero set contains the off-diagonal zeros of `Φ`; at a
rank-two zero `H` is a submersion (Step 1), so `H⁻¹(0)` is locally a curve
(Step 2) which the constant-rank redundancy identifies with the
off-diagonal zero set of `Φ` (Step 3). -/
def collinearityInnerPair (r : ℝ → Space) (a b m : ℝ) (q : RealParamTriple) : ℝ × ℝ :=
  (inner ℝ (collinearityMap r q) (collPartialA r a b m),
    inner ℝ (collinearityMap r q) (collPartialB r a b m))

/-- **Step-1 submersion datum**: if `P_A` and `P_B` are linearly independent
at the base triple, the 2×2 matrix of the reduced map's derivative on the
`(a,b)` coordinate plane — the Gram matrix of `P_A, P_B` (rows ℓ₁,ℓ₂,
columns the `a`- and `b`-directions) — is invertible.  (Commons
`gram_det_ne_zero_of_linearIndependent`, instantiated at the two partials.)
-/
lemma reducedSubmersion_gram_invertible {r : ℝ → Space} (a b m : ℝ)
    (hLI : LinearIndependent ℝ ![collPartialA r a b m, collPartialB r a b m]) :
    (Matrix.det ![![inner ℝ (collPartialA r a b m) (collPartialA r a b m),
        inner ℝ (collPartialA r a b m) (collPartialB r a b m)],
      ![inner ℝ (collPartialB r a b m) (collPartialA r a b m),
        inner ℝ (collPartialB r a b m) (collPartialB r a b m)]]) ≠ 0 := by
  exact Commons.Analysis.InnerProductSpace.gram_det_ne_zero_of_linearIndependent hLI

/-! ### Step-2 anchor: the reduced map is smooth

`H(q) = (ℓ₁(Φ q), ℓ₂(Φ q))` is built from the smooth `Φ` and the two
continuous-linear functionals `u ↦ ⟪u, Pᵢ⟫` (real inner product with a
fixed vector, `innerSLFlip`), so `H` is `C^∞` (in particular `C¹` and
differentiable at every triple).  This is the differentiability input the
submersion/regular-value machinery (Mathlib `ImplicitFunctionData`) needs
for Step 2. -/

/-- Pairing with a fixed vector is a smooth linear functional of the first
argument (real inner product). -/
lemma contDiff_inner_fixed (v : Space) : ContDiff ℝ ⊤ (fun u : Space => inner ℝ u v) := by
  exact ((innerSLFlip ℝ v : Space →L[ℝ] ℝ).contDiff)

/-- **The reduced map is smooth**: for fixed base partials `(a, b, m)`,
`q ↦ collinearityInnerPair r a b m q` is `C^∞` (hence `C¹` and
differentiable), the differentiability input of Step 2's implicit-function
application. -/
lemma contDiff_collinearityInnerPair {r : ℝ → Space} (h : IsSmoothKnot r) (a b m : ℝ) :
    ContDiff ℝ ⊤ (fun q : RealParamTriple => collinearityInnerPair r a b m q) := by
  unfold collinearityInnerPair
  have hPhi : ContDiff ℝ ⊤ (fun q : RealParamTriple => collinearityMap r q) :=
    contDiff_collinearityMap h
  have h1 : ContDiff ℝ ⊤ (fun q : RealParamTriple => inner ℝ (collinearityMap r q) (collPartialA r a b m)) :=
    (contDiff_inner_fixed (collPartialA r a b m)).comp hPhi
  have h2 : ContDiff ℝ ⊤ (fun q : RealParamTriple => inner ℝ (collinearityMap r q) (collPartialB r a b m)) :=
    (contDiff_inner_fixed (collPartialB r a b m)).comp hPhi
  exact h1.prodMk h2

/-! ### Step-2(a) move 1: the axis-curve derivatives

The two coordinate-axis derivatives of the collinearity map at the base
triple, instantiated from the P-form directional assembly
(`hasDerivAt_collinearity_directional`, CollinearityMap.lean) with
directions `(1,0,0)` and `(0,1,0)`: the `a`-axis curve
`s ↦ Φ(a + s, b, m)` has derivative `∂_a = collPartialA`, and the `b`-axis
curve `s ↦ Φ(a, b + s, m)` has derivative `∂_b = collPartialB`.  These feed
the inner-product functionals to produce the two Gram-column values of the
derivative of the reduced map `H`. -/

/-- The `a`-axis curve of `Φ` has derivative `∂_a` at the base triple. -/
lemma hasDerivAt_collinearity_a_axis {r : ℝ → Space} (h : IsSmoothKnot r) (a b m : ℝ) :
    HasDerivAt (fun s : ℝ => collinearityValue r (a + s) b m) (collPartialA r a b m) 0 := by
  have hd := hasDerivAt_collinearity_directional (h := h) (a := a) (b := b) (m := m)
    (da := 1) (db := 0) (dm := 0)
  have hd1 : HasDerivAt (fun s : ℝ => collinearityValue r (a + s) b m)
      ((1 : ℝ) • (cross3 (velocity r a) (r a - r m) + cross3 (r a - r b) (velocity r a)) +
        (0 : ℝ) • cross3 (r a - r m) (velocity r b) + (0 : ℝ) • cross3 (velocity r m) (r a - r b)) 0 := by
    apply HasDerivAt.congr_of_eventuallyEq
    · exact hd
    · filter_upwards with s
      simp
  apply HasDerivAt.congr_deriv hd1
  simp [collPartialA]

/-- The `b`-axis curve of `Φ` has derivative `∂_b` at the base triple. -/
lemma hasDerivAt_collinearity_b_axis {r : ℝ → Space} (h : IsSmoothKnot r) (a b m : ℝ) :
    HasDerivAt (fun s : ℝ => collinearityValue r a (b + s) m) (collPartialB r a b m) 0 := by
  have hd := hasDerivAt_collinearity_directional (h := h) (a := a) (b := b) (m := m)
    (da := 0) (db := 1) (dm := 0)
  have hd1 : HasDerivAt (fun s : ℝ => collinearityValue r a (b + s) m)
      ((0 : ℝ) • (cross3 (velocity r a) (r a - r m) + cross3 (r a - r b) (velocity r a)) +
        (1 : ℝ) • cross3 (r a - r m) (velocity r b) + (0 : ℝ) • cross3 (velocity r m) (r a - r b)) 0 := by
    apply HasDerivAt.congr_of_eventuallyEq
    · exact hd
    · filter_upwards with s
      simp
  apply HasDerivAt.congr_deriv hd1
  simp [collPartialB]

/-! ### Step-2(a) move 2: the Gram-column derivative values of the reduced map

Pushing the axis derivatives through the inner functionals
`u ↦ ⟪u, Pᵢ⟫ = innerSLFlip Pᵢ` gives the derivative of the reduced map
`H(q) = (ℓ₁(Φ q), ℓ₂(Φ q))` along the `a`- and `b`-axes at the base triple:
the two columns of the Gram matrix of `P_A, P_B`.  The generic helper
`hasDerivAt_comp_clm` (a derivative curve through a continuous linear map)
carries the axis derivatives of move 1 into the inner-product components. -/

/-- A derivative curve composed with a continuous linear map has the
transported derivative: `(L ∘ g)' = L ∘ g'`. -/
lemma hasDerivAt_comp_clm {g : ℝ → Space} {g' : Space} {t : ℝ} (hg : HasDerivAt g g' t)
    (L : Space →L[ℝ] ℝ) : HasDerivAt (fun s => L (g s)) (L g') t := by
  have hcF : HasFDerivAt g (ContinuousLinearMap.toSpanSingleton ℝ g') t := hg.hasFDerivAt
  have houter : HasFDerivAt (⇑L) L (g t) := L.hasFDerivAt
  have hcomp : HasFDerivAt (fun s => L (g s)) (L.comp (ContinuousLinearMap.toSpanSingleton ℝ g')) t :=
    houter.comp t hcF
  rw [ContinuousLinearMap.comp_toSpanSingleton] at hcomp
  exact (hasDerivAt_iff_hasFDerivAt.mpr hcomp)

/-- The `a`-axis derivative of the reduced map is the first Gram column:
`∂_a H = (⟪P_A, P_A⟫, ⟪P_A, P_B⟫)`. -/
lemma hasDerivAt_reduced_a_axis {r : ℝ → Space} (h : IsSmoothKnot r) (a b m : ℝ) :
    HasDerivAt (fun s : ℝ => collinearityInnerPair r a b m (a + s, (b, m)))
      (inner ℝ (collPartialA r a b m) (collPartialA r a b m),
       inner ℝ (collPartialA r a b m) (collPartialB r a b m)) 0 := by
  have hg : HasDerivAt (fun s : ℝ => collinearityMap r (a + s, (b, m)))
      (collPartialA r a b m) 0 := by
    change HasDerivAt (fun s : ℝ => collinearityValue r (a + s) b m) (collPartialA r a b m) 0
    exact hasDerivAt_collinearity_a_axis h a b m
  have h1 : HasDerivAt (fun s : ℝ => inner ℝ (collinearityMap r (a + s, (b, m))) (collPartialA r a b m))
      (inner ℝ (collPartialA r a b m) (collPartialA r a b m)) 0 :=
    hasDerivAt_comp_clm hg ((innerSLFlip ℝ (collPartialA r a b m) : Space →L[ℝ] ℝ))
  have h2 : HasDerivAt (fun s : ℝ => inner ℝ (collinearityMap r (a + s, (b, m))) (collPartialB r a b m))
      (inner ℝ (collPartialA r a b m) (collPartialB r a b m)) 0 :=
    hasDerivAt_comp_clm hg ((innerSLFlip ℝ (collPartialB r a b m) : Space →L[ℝ] ℝ))
  have hp := h1.prodMk h2
  apply HasDerivAt.congr_of_eventuallyEq
  · exact hp
  · filter_upwards with s
    simp [collinearityInnerPair]

/-- The `b`-axis derivative of the reduced map is the second Gram column:
`∂_b H = (⟪P_B, P_A⟫, ⟪P_B, P_B⟫)`. -/
lemma hasDerivAt_reduced_b_axis {r : ℝ → Space} (h : IsSmoothKnot r) (a b m : ℝ) :
    HasDerivAt (fun s : ℝ => collinearityInnerPair r a b m (a, (b + s, m)))
      (inner ℝ (collPartialB r a b m) (collPartialA r a b m),
       inner ℝ (collPartialB r a b m) (collPartialB r a b m)) 0 := by
  have hg : HasDerivAt (fun s : ℝ => collinearityMap r (a, (b + s, m)))
      (collPartialB r a b m) 0 := by
    change HasDerivAt (fun s : ℝ => collinearityValue r a (b + s) m) (collPartialB r a b m) 0
    exact hasDerivAt_collinearity_b_axis h a b m
  have h1 : HasDerivAt (fun s : ℝ => inner ℝ (collinearityMap r (a, (b + s, m))) (collPartialA r a b m))
      (inner ℝ (collPartialB r a b m) (collPartialA r a b m)) 0 :=
    hasDerivAt_comp_clm hg ((innerSLFlip ℝ (collPartialA r a b m) : Space →L[ℝ] ℝ))
  have h2 : HasDerivAt (fun s : ℝ => inner ℝ (collinearityMap r (a, (b + s, m))) (collPartialB r a b m))
      (inner ℝ (collPartialB r a b m) (collPartialB r a b m)) 0 :=
    hasDerivAt_comp_clm hg ((innerSLFlip ℝ (collPartialB r a b m) : Space →L[ℝ] ℝ))
  have hp := h1.prodMk h2
  apply HasDerivAt.congr_of_eventuallyEq
  · exact hp
  · filter_upwards with s
    simp [collinearityInnerPair]


/-! ### Step-2(a) move 3: the derivative of the reduced map is surjective

The two Gram-column derivative values (move 2) are now identified with the
actual derivative `D := fderiv H p` of the reduced map `H` applied to the
two coordinate-axis directions `e_a = (1,0,0)` and `e_b = (0,1,0)` of the
parameter space `RealParamTriple`.  The bridge is the generic lemma
`fderiv_along_axis_eq_deriv`: the derivative of an affine line
`s ↦ H(p + s • e)` through `p` is `D e`, and `HasDerivAt.unique` equates it
with the axis-curve value of move 2 (the Gram columns).  When `P_A, P_B`
are linearly independent, the Gram matrix of the pair is invertible
(`reducedSubmersion_gram_invertible`, move 1), so the two images
`D e_a, D e_b` are linearly independent vectors of `ℝ²` (a 2×2 determinant
criterion, `linearIndependent_pair_prod_of_det_ne_zero`); two independent
vectors of the two-dimensional space `ℝ × ℝ` lying in the range of `D`
force the range to be the whole space (the fleet lemma
`Commons.LinearAlgebra.Span.surjective_of_two_independent_in_range`):

    range D = ⊤   (i.e. `H` is a submersion at `p`, rank-two derivative)

This is the submersion datum that Step 2's implicit-function application to
`H : ℝ³ → ℝ²` consumes: `H⁻¹(0)` is locally a curve.  -/

lemma fderiv_reduced_a_col {r : ℝ → Space} (h : IsSmoothKnot r) (a b m : ℝ) :
    (fderiv ℝ (fun q : RealParamTriple => collinearityInnerPair r a b m q) (a, (b, m)))
      ((1 : ℝ), ((0 : ℝ), (0 : ℝ))) =
      (inner ℝ (collPartialA r a b m) (collPartialA r a b m),
       inner ℝ (collPartialA r a b m) (collPartialB r a b m)) := by
  let H : RealParamTriple → ℝ × ℝ := fun q => collinearityInnerPair r a b m q
  let p : RealParamTriple := (a, (b, m))
  let e : RealParamTriple := ((1 : ℝ), ((0 : ℝ), (0 : ℝ)))
  have hD : DifferentiableAt ℝ H p := by
    dsimp [H, p]
    have hc : ContDiff ℝ ⊤ (fun q : RealParamTriple => collinearityInnerPair r a b m q) :=
      contDiff_collinearityInnerPair h a b m
    exact (ContDiff.of_le hc le_top).differentiable_one (a, (b, m))
  have hg : HasDerivAt (fun s : ℝ => H (p + s • e)) ((fderiv ℝ H p) e) 0 :=
    fderiv_along_axis_eq_deriv (H := H) (p := p) (e := e) hD
  have hga : HasDerivAt (fun s : ℝ => collinearityInnerPair r a b m (a + s, (b, m)))
      (inner ℝ (collPartialA r a b m) (collPartialA r a b m),
       inner ℝ (collPartialA r a b m) (collPartialB r a b m)) 0 :=
    hasDerivAt_reduced_a_axis h a b m
  have heq : (fun s : ℝ => H (p + s • e)) = fun s : ℝ => collinearityInnerPair r a b m (a + s, (b, m)) := by
    funext s
    dsimp [H, p, e]
    congr 1
    ext <;> simp
  have hg' : HasDerivAt (fun s : ℝ => collinearityInnerPair r a b m (a + s, (b, m)))
      ((fderiv ℝ H p) e) 0 := by
    simpa [heq] using hg
  have huniq := HasDerivAt.unique hga hg'
  dsimp [H, p, e] at huniq
  exact huniq.symm

lemma fderiv_reduced_b_col {r : ℝ → Space} (h : IsSmoothKnot r) (a b m : ℝ) :
    (fderiv ℝ (fun q : RealParamTriple => collinearityInnerPair r a b m q) (a, (b, m)))
      ((0 : ℝ), ((1 : ℝ), (0 : ℝ))) =
      (inner ℝ (collPartialB r a b m) (collPartialA r a b m),
       inner ℝ (collPartialB r a b m) (collPartialB r a b m)) := by
  let H : RealParamTriple → ℝ × ℝ := fun q => collinearityInnerPair r a b m q
  let p : RealParamTriple := (a, (b, m))
  let e : RealParamTriple := ((0 : ℝ), ((1 : ℝ), (0 : ℝ)))
  have hD : DifferentiableAt ℝ H p := by
    dsimp [H, p]
    have hc : ContDiff ℝ ⊤ (fun q : RealParamTriple => collinearityInnerPair r a b m q) :=
      contDiff_collinearityInnerPair h a b m
    exact (ContDiff.of_le hc le_top).differentiable_one (a, (b, m))
  have hg : HasDerivAt (fun s : ℝ => H (p + s • e)) ((fderiv ℝ H p) e) 0 :=
    fderiv_along_axis_eq_deriv (H := H) (p := p) (e := e) hD
  have hgb : HasDerivAt (fun s : ℝ => collinearityInnerPair r a b m (a, (b + s, m)))
      (inner ℝ (collPartialB r a b m) (collPartialA r a b m),
       inner ℝ (collPartialB r a b m) (collPartialB r a b m)) 0 :=
    hasDerivAt_reduced_b_axis h a b m
  have heq : (fun s : ℝ => H (p + s • e)) = fun s : ℝ => collinearityInnerPair r a b m (a, (b + s, m)) := by
    funext s
    dsimp [H, p, e]
    congr 1
    ext <;> simp
  have hg' : HasDerivAt (fun s : ℝ => collinearityInnerPair r a b m (a, (b + s, m)))
      ((fderiv ℝ H p) e) 0 := by
    simpa [heq] using hg
  have huniq := HasDerivAt.unique hgb hg'
  dsimp [H, p, e] at huniq
  exact huniq.symm

theorem reducedMap_fderiv_range_top {r : ℝ → Space} (h : IsSmoothKnot r) (a b m : ℝ)
    (hAB : LinearIndependent ℝ ![collPartialA r a b m, collPartialB r a b m]) :
    LinearMap.range ((fderiv ℝ (fun q : RealParamTriple => collinearityInnerPair r a b m q) (a, (b, m))).toLinearMap) = ⊤ := by
  let H : RealParamTriple → ℝ × ℝ := fun q => collinearityInnerPair r a b m q
  let PA : Space := collPartialA r a b m
  let PB : Space := collPartialB r a b m
  let col_a : ℝ × ℝ := (inner ℝ PA PA, inner ℝ PA PB)
  let col_b : ℝ × ℝ := (inner ℝ PB PA, inner ℝ PB PB)
  have hca_eq : (fderiv ℝ (fun q : RealParamTriple => collinearityInnerPair r a b m q) (a, (b, m)))
      ((1 : ℝ), ((0 : ℝ), (0 : ℝ))) = col_a := by
    simpa [col_a] using fderiv_reduced_a_col h a b m
  have hcb_eq : (fderiv ℝ (fun q : RealParamTriple => collinearityInnerPair r a b m q) (a, (b, m)))
      ((0 : ℝ), ((1 : ℝ), (0 : ℝ))) = col_b := by
    simpa [col_b] using fderiv_reduced_b_col h a b m
  have hGdet0 : (Matrix.det !![inner ℝ PA PA, inner ℝ PA PB; inner ℝ PB PA, inner ℝ PB PB]) ≠ 0 := by
    dsimp [PA, PB]
    exact reducedSubmersion_gram_invertible a b m hAB
  have hD : col_a.1 * col_b.2 - col_a.2 * col_b.1 ≠ 0 := by
    dsimp [col_a, col_b]
    have hEq : (Matrix.det !![inner ℝ PA PA, inner ℝ PA PB; inner ℝ PB PA, inner ℝ PB PB])
        = (inner ℝ PA PA) * (inner ℝ PB PB) - (inner ℝ PA PB) * (inner ℝ PB PA) := by
      rw [Matrix.det_fin_two_of]
    rw [← hEq]
    exact hGdet0
  have hLIp : LinearIndependent ℝ ![col_a, col_b] := linearIndependent_pair_prod_of_det_ne_zero hD
  let T : RealParamTriple →ₗ[ℝ] (ℝ × ℝ) :=
    (fderiv ℝ (fun q : RealParamTriple => collinearityInnerPair r a b m q) (a, (b, m))).toLinearMap
  have hca : col_a ∈ LinearMap.range T := by
    refine ⟨((1 : ℝ), ((0 : ℝ), (0 : ℝ))), ?_⟩
    dsimp [T]
    exact hca_eq
  have hcb : col_b ∈ LinearMap.range T := by
    refine ⟨((0 : ℝ), ((1 : ℝ), (0 : ℝ))), ?_⟩
    dsimp [T]
    exact hcb_eq
  have hfin : Module.finrank ℝ (ℝ × ℝ) = 2 := by
    rw [Module.finrank_prod]
    simp
  have hrange : LinearMap.range T = ⊤ :=
    Commons.LinearAlgebra.Span.surjective_of_two_independent_in_range T hca hcb hLIp hfin
  simpa [T] using hrange

/-! ### Step 3 of the local-curve proof: identification `Φ⁻¹(0) = H⁻¹(0)` near a zero

**Theorem** (`identification_of_reduced_zero`).  Let `(a,b,m)` be a zero of
`Φ` with the first chord `Z := r a − r b` nonzero and the partials
`P_A := ∂_a Φ(p)`, `P_B := ∂_b Φ(p)` linearly independent.  Then on an open
neighbourhood `U` of the triple, the zero set of the reduced map
`H(q) = (⟨Φ q, P_A⟩, ⟨Φ q, P_B⟩)` is exactly the zero set of `Φ` itself:

    ∀ q ∈ U,  H(q) = 0  →  Φ(q) = 0      (and Φ(q)=0 ⇒ H(q)=0 trivially)

Proof ingredients (all proved here):  the cross-product geometry gives
`Φ(q) ⊥ chord(q) := r q₁ − r q₂₁` for *every* triple (`collinearityMap_
orth_chord`); from the collinear factorisation `r a − r m = t • Z` at the
zero, each partial is a scalar multiple of a velocity-cross vector
(`collPartialA_eq_smul`/`_B_eq_smul`, Transversality) and hence orthogonal
to `Z` (`collPartialA_orth_chord`/`_B_orth_chord`); a nonzero vector
orthogonal to two generators is outside their span (`chord_not_mem_span_of_
orth`), so `Z ∉ span{P_A,P_B}`, and — since the chord vector moves
continuously and a finite-dimensional subspace is closed
(`Submodule.closed_of_finiteDimensional`) — the same holds for `chord(q)`
with `q` in an open neighbourhood `U`; three independent vectors in the
3-dimensional `Space` span `⊤` (`finrank_Space` +
`span_top_of_three_independent`, commons).  For `q ∈ U` with `H(q) = 0`,
`Φ(q)` is orthogonal to `P_A, P_B, chord(q)` — three spanning vectors — so
`Φ(q) = 0` (`eq_zero_of_inner_eq_zero_of_span_top`, commons).

This is the identification that completes the regular-value reduction: the
level set of `H` (a submersion on `U`, Step 1-2) is exactly `Φ⁻¹(0) ∩ U`,
so the off-diagonal zeros of `Φ` near a general-position triple form a
`C¹` curve (`LocalSmoothCurveTheorem`, Step 2b — the regular-value
invocation).  -/

lemma collPartialA_orth_chord {r : ℝ → Space} {a b m t : ℝ}
    (hW : r a - r m = t • (r a - r b)) :
    inner ℝ (collPartialA r a b m) (r a - r b) = 0 := by
  rw [collPartialA_eq_smul r a b m hW]
  have hy : inner ℝ (cross3 (velocity r a) (r a - r b)) (r a - r b) = 0 := by
    have hcross : cross3 (velocity r a) (r a - r b) = -(cross3 (r a - r b) (velocity r a)) := by
      simpa using (cross3_anticomm (u := r a - r b) (v := velocity r a))
    rw [hcross]
    rw [inner_neg_left]
    have h0 : inner ℝ (cross3 (r a - r b) (velocity r a)) (r a - r b) = 0 := by
      simpa [cross3] using
        (Commons.Analysis.CrossProduct.inner_cross3_self_left (u := r a - r b) (v := velocity r a))
    rw [h0]
    simp
  rw [inner_smul_left, hy]
  simp

lemma collPartialB_orth_chord {r : ℝ → Space} {a b m t : ℝ}
    (hW : r a - r m = t • (r a - r b)) :
    inner ℝ (collPartialB r a b m) (r a - r b) = 0 := by
  rw [collPartialB_eq_smul r a b m hW]
  have hy : inner ℝ (cross3 (velocity r b) (r a - r b)) (r a - r b) = 0 := by
    have hcross : cross3 (velocity r b) (r a - r b) = -(cross3 (r a - r b) (velocity r b)) := by
      simpa using (cross3_anticomm (u := r a - r b) (v := velocity r b))
    rw [hcross]
    rw [inner_neg_left]
    have h0 : inner ℝ (cross3 (r a - r b) (velocity r b)) (r a - r b) = 0 := by
      simpa [cross3] using
        (Commons.Analysis.CrossProduct.inner_cross3_self_left (u := r a - r b) (v := velocity r b))
    rw [h0]
    simp
  rw [inner_smul_left, hy]
  simp

lemma collinearityMap_orth_chord (r : ℝ → Space) (q : RealParamTriple) :
    inner ℝ (collinearityMap r q) (r q.1 - r q.2.1) = 0 := by
  unfold collinearityMap
  simpa [cross3] using
    (Commons.Analysis.CrossProduct.inner_cross3_self_left
      (u := r q.1 - r q.2.1) (v := r q.1 - r q.2.2))

lemma finrank_Space : Module.finrank ℝ Space = 3 := by
  simp [Space]

/-- If `z` is orthogonal to each of the independent vectors `x, y` and is
nonzero, then `z` is not in their span. -/
lemma chord_not_mem_span_of_orth {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {x y z : E}
    (hxz : inner ℝ z x = 0) (hyz : inner ℝ z y = 0) (hz : z ≠ 0) :
    z ∉ Submodule.span ℝ ({x, y} : Set E) := by
  intro hzspan
  rw [Submodule.mem_span_pair] at hzspan
  rcases hzspan with ⟨α, β, hzEq⟩
  have hz2 : inner ℝ z z = 0 := by
    calc
      inner ℝ z z = inner ℝ (α • x + β • y) z := by rw [hzEq]
      _ = α * inner ℝ x z + β * inner ℝ y z := by
        simp [inner_add_left, inner_smul_left]
      _ = 0 := by
        have hx : inner ℝ x z = 0 := by simpa [real_inner_comm] using hxz
        have hy : inner ℝ y z = 0 := by simpa [real_inner_comm] using hyz
        simp [hx, hy]
  exact hz (inner_self_eq_zero.mp hz2)

/-- The identification (redundancy) step: near a collinear zero triple with
`P_A, P_B` independent, the zero set of the reduced map `H(q) =
(⟨Φ q, P_A⟩, ⟨Φ q, P_B⟩)` coincides with the collinearity zero set of `Φ`
itself.  (Roughly: on `H⁻¹(0)`, `Φ(q)` is orthogonal to `P_A, P_B` and —
always — to the chord `r q₁ − r q₂₁`; those three vectors span `Space` for
`q` in an open neighbourhood of the triple.) -/
theorem identification_of_reduced_zero {r : ℝ → Space} (hr : IsSmoothKnot r) (a b m : ℝ)
    (hΦ : collinearityValue r a b m = 0) (hZ : r a - r b ≠ 0)
    (hAB : LinearIndependent ℝ ![collPartialA r a b m, collPartialB r a b m]) :
    ∃ U : Set RealParamTriple, IsOpen U ∧ (a, (b, m)) ∈ U ∧
      ∀ q ∈ U, collinearityInnerPair r a b m q = (0, 0) → collinearityMap r q = 0 := by
  let PA : Space := collPartialA r a b m
  let PB : Space := collPartialB r a b m
  rcases (chord_parallel_of_collinearity_eq_zero hZ hΦ) with ⟨t, hW⟩
  have hAz : inner ℝ PA (r a - r b) = 0 := by
    simpa [PA] using collPartialA_orth_chord hW
  have hBz : inner ℝ PB (r a - r b) = 0 := by
    simpa [PB] using collPartialB_orth_chord hW
  have hzA : inner ℝ (r a - r b) PA = 0 := by simpa [real_inner_comm] using hAz
  have hzB : inner ℝ (r a - r b) PB = 0 := by simpa [real_inner_comm] using hBz
  have hAB' : LinearIndependent ℝ ![PA, PB] := by simpa [PA, PB] using hAB
  have hZnot : (r a - r b) ∉ Submodule.span ℝ ({PA, PB} : Set Space) :=
    chord_not_mem_span_of_orth hzA hzB hZ
  let K : Submodule ℝ Space := Submodule.span ℝ ({PA, PB} : Set Space)
  let chord : RealParamTriple → Space := fun q => r q.1 - r q.2.1
  have hchord : Continuous chord := by
    have hrc : Continuous r := hr.smooth.continuous
    have h1 : Continuous (fun q : RealParamTriple => r q.1) := hrc.comp continuous_fst
    have h2 : Continuous (fun q : RealParamTriple => r q.2.1) := hrc.comp (continuous_fst.comp continuous_snd)
    dsimp [chord]
    exact h1.sub h2
  have hKclosed : IsClosed (K : Set Space) := by
    dsimp [K]
    exact Submodule.closed_of_finiteDimensional (s := Submodule.span ℝ ({PA, PB} : Set Space))
  let U : Set RealParamTriple := chord ⁻¹' ((K : Set Space)ᶜ)
  refine ⟨U, ?_, ?_, ?_⟩
  · show IsOpen U
    dsimp [U]
    exact hKclosed.isOpen_compl.preimage hchord
  · dsimp [U, K, chord]
    simpa using hZnot
  · intro q hq Hq
    have hqchord' : (r q.1 - r q.2.1) ∉ Submodule.span ℝ ({PA, PB} : Set Space) := by
      dsimp [U, K, chord] at hq
      simpa using hq
    -- {PA, PB, chord q} spans Space
    have hrange : Submodule.span ℝ ({PA, PB, r q.1 - r q.2.1} : Set Space) = ⊤ := by
      have hLI2 : LinearIndependent ℝ (![PA, PB] : Fin 2 → Space) := hAB'
      have hnotmem : (r q.1 - r q.2.1) ∉ Submodule.span ℝ (Set.range (![PA, PB] : Fin 2 → Space)) := by
        -- range ![PA,PB] = {PA,PB}
        rw [Commons.LinearAlgebra.Span.range_matrix_cons_two]
        exact hqchord'
      have hLI3 : LinearIndependent ℝ (![PA, PB, r q.1 - r q.2.1] : Fin 3 → Space) := by
        simpa using (hLI2.finSnoc hnotmem)
      exact Commons.LinearAlgebra.Span.span_top_of_three_independent (E := Space) finrank_Space hLI3
    -- Φ(q) is orthogonal to PA, PB (from H(q) = 0) and to the chord
    have hxPA : inner ℝ (collinearityMap r q) PA = 0 := by
      have hf := congrArg Prod.fst Hq
      simpa [collinearityInnerPair, PA, PB] using hf
    have hxPB : inner ℝ (collinearityMap r q) PB = 0 := by
      have hs := congrArg Prod.snd Hq
      simpa [collinearityInnerPair, PA, PB] using hs
    have hxc : inner ℝ (collinearityMap r q) (r q.1 - r q.2.1) = 0 := collinearityMap_orth_chord r q
    -- G1
    have hzero := Commons.Analysis.InnerProductSpace.eq_zero_of_inner_eq_zero_of_span_top (x := collinearityMap r q)
      ({PA, PB, r q.1 - r q.2.1} : Set Space)
    -- need hx for G1: for each y in the set, inner x y = 0
    have hxy : ∀ y ∈ ({PA, PB, r q.1 - r q.2.1} : Set Space), inner ℝ (collinearityMap r q) y = 0 := by
      intro y hy
      rcases hy with rfl | rfl | rfl
      · exact hxPA
      · exact hxPB
      · exact hxc
    exact hzero hxy hrange
end LeanEval.KnotTheory.Quadrisecant
