import Mathlib
import Submission.Work.WilE3.Taylor.MaximalPsi
import Submission.Work.WilE3.Sep
import Submission.Work.WilE3.Identity.E3_identity_proved
import Submission.Work.WilE3.Taylor.E3_taylor_closure_proved_of_multiplicity
import Submission.Work.WilE3.eaEval_analytic
import Submission.Work.WilE3.Taylor.hasLoj_of_multiplicity
import Submission.Work.WilE3.Realify.MultiplicityBound_of_ET
import Submission.Work.WilE3.MPsi.maximalPsiNode_of_grad_loj

namespace Work.WilE3.Taylor

set_option autoImplicit false
open Classical Topology Filter
open WilkiesDesign.E

/-! ## Elementary facts about the basic EA sets

The first group of lemmas collects the consequences of `y ∈ closure {x | B.holds c x}` that are
pure continuity: the equations vanish at `y`, the strict inequalities are nonnegative at `y`. -/

lemma zero_pow_sq (κ : ℕ) (hκ : 1 ≤ κ) : (0 : ℝ) ^ (κ ^ 2) = 0 :=
  zero_pow (by positivity)

/-- `dist` on `Fin k → ℝ` is the sup-metric (Gabrielov's `|x| = max_i |x_i|`). -/
lemma dist_le_iff {k : ℕ} (x y : Fin k → ℝ) {r : ℝ} (hr : 0 ≤ r) :
    dist x y ≤ r ↔ ∀ i, |x i - y i| ≤ r := by
  rw [dist_pi_le_iff hr]
  exact forall_congr' (fun i => by rw [Real.dist_eq])

/-- Each coordinate is bounded by the sup-distance. -/
lemma abs_sub_le_dist {k : ℕ} (x y : Fin k → ℝ) (i : Fin k) : |x i - y i| ≤ dist x y := by
  have := dist_le_pi_dist x y i
  rwa [Real.dist_eq] at this

/-- Every equation of `B` vanishes at any limit point of `B.holds`. -/
lemma eqs_eq_zero_of_mem_closure {k r : ℕ} (c : EAChain k r) (B : Basic k r) {y : Fin k → ℝ}
    (hy : y ∈ closure {x | B.holds c x}) : ∀ f ∈ B.eqs, eaEval c f y = 0 := by
  intro f hf
  have hcont : Continuous (fun x : Fin k → ℝ => eaEval c f x) :=
    continuous_iff_continuousAt.mpr (fun x => (Work.WilE3.eaEval_analytic c f x).continuousAt)
  have hclosed : IsClosed {x : Fin k → ℝ | eaEval c f x = 0} :=
    isClosed_eq hcont continuous_const
  have hsub : {x | B.holds c x} ⊆ {x | eaEval c f x = 0} := fun x hx => hx.1 f hf
  exact (closure_minimal hsub hclosed) hy

/-- Every strict inequality of `B` is nonnegative at any limit point of `B.holds`. -/
lemma pos_nonneg_of_mem_closure {k r : ℕ} (c : EAChain k r) (B : Basic k r) {y : Fin k → ℝ}
    (hy : y ∈ closure {x | B.holds c x}) : ∀ g ∈ B.pos, 0 ≤ eaEval c g y := by
  intro g hg
  have hcont : Continuous (fun x : Fin k → ℝ => eaEval c g x) :=
    continuous_iff_continuousAt.mpr (fun x => (Work.WilE3.eaEval_analytic c g x).continuousAt)
  have hclosed : IsClosed {x : Fin k → ℝ | 0 ≤ eaEval c g x} :=
    isClosed_le continuous_const hcont
  have hsub : {x | B.holds c x} ⊆ {x | 0 ≤ eaEval c g x} := fun x hx => le_of_lt (hx.2 g hg)
  exact (closure_minimal hsub hclosed) hy

/-- **Trivial case of the maximal-`ψ` node:** if `y` itself satisfies the conditions of the basic
set, then `z = y` witnesses the conclusion for every `ε > 0` and every `κ ≥ 1`. -/
lemma exists_good_point_of_holds {k r : ℕ} (c : EAChain k r) (B : Basic k r) {y : Fin k → ℝ}
    (hholds : B.holds c y) {κ : ℕ} (hκ : 1 ≤ κ) {ε : ℝ} (hε : 0 < ε) :
    ∃ z : Fin k → ℝ, dist z y < ε ∧
      (∀ f ∈ B.eqs, 2 * |eaEval c f z| ≤ dist z y ^ (κ ^ 2)) ∧
      (∀ g ∈ B.pos, 2 * dist z y ^ κ < eaEval c g z) := by
  refine ⟨y, by simpa using hε, ?_, ?_⟩
  · intro f hf
    rw [hholds.1 f hf, abs_zero, mul_zero]
    exact pow_nonneg dist_nonneg _
  · intro g hg
    rw [dist_self, zero_pow (by positivity)]
    simpa using hholds.2 g hg

/-- **The "zero-set" form of the conclusion:** it suffices to produce, for every `ε > 0`, a point
`z` at distance `< ε` from `y` whose coordinates satisfy the equations exactly and whose strict
inequalities exceed the margin `2 * dist z y ^ κ`. -/
lemma exists_good_point_of_zeroSet {k r : ℕ} (c : EAChain k r) (B : Basic k r) (y : Fin k → ℝ)
    {κ : ℕ}
    (hzero : ∀ ε : ℝ, 0 < ε → ∃ z : Fin k → ℝ, dist z y < ε ∧
      (∀ f ∈ B.eqs, eaEval c f z = 0) ∧ (∀ g ∈ B.pos, 2 * dist z y ^ κ < eaEval c g z)) :
    ∀ ε : ℝ, 0 < ε → ∃ z : Fin k → ℝ, dist z y < ε ∧
      (∀ f ∈ B.eqs, 2 * |eaEval c f z| ≤ dist z y ^ (κ ^ 2)) ∧
      (∀ g ∈ B.pos, 2 * dist z y ^ κ < eaEval c g z) := by
  intro ε hε
  obtain ⟨z, hz, heqs, hpos⟩ := hzero ε hε
  refine ⟨z, hz, ?_, hpos⟩
  intro f hf
  rw [heqs f hf, abs_zero, mul_zero]
  exact pow_nonneg dist_nonneg _

/-
  ## Status of the reduction (this file)

  The target `Work.WilE3.MaximalPsiNode F` is Gabrielov 1998, Lemma 2.5/2.6
  (`sources/wilkiesE/vision/gabrielov1998_frontier/p0007.md`–`p0009.md`).  The route implemented
  here is the project lead's *ascent + projection* route, designed and independently reviewed in
  `sources/wilkiesE3mpsi/` (design `wilkies_e3_maximalpsi.md`, skeleton `MPsiRoute.lean`, review
  `wilkies_e3_maximalpsi_REVIEW.md`): it avoids Gabrielov's generic perturbation (Lemma 2.1) and
  his critical-value Lemma 2.3 altogether.

  ### The route

  With `P = ∏_{g ∈ B.pos} g`, `S = ∑_{f ∈ B.eqs} f ^ 2`, `q = K_L.eval B.deg + 1` and
  `Φ = P · (P ^ (4q) − S)` (`Work.WilE3.MPsi.phiPen B (2q)`):

  1. **Ascent** (`Work.WilE3.MPsi.ascent`, PROVED): maximise `Φ ^ (1-θ) − α |x - x₀|²` over the
     compact set `{g ≥ 0} ∩ {P ^ (4q) ≥ S} ∩ closedBall x₀ ρ` containing a point `x₀ ∈ B.holds`.
     An interior maximiser would have vanishing derivative, contradicting the PROVED gradient
     inequality `Work.WilE3.Taylor.ea_grad_of_multiplicity` applied to the EA polynomial `Φ`; so the
     maximiser `z` lies on the sphere and `Φ z ≥ (c ρ) ^ Kexp`.
  2. **Bounds at `z`**: `min g z ≳ ρ ^ Kexp` and `∑ |f z| ≲ (min g z) ^ (2q)`.
  3. **Projection** (`Work.WilE3.MPsi.exists_zero_near`, PROVED): the PROVED residual Łojasiewicz
     inequality `Work.WilE3.Taylor.hasLoj_of_multiplicity` moves `z` to a point `z'` of the common
     zero set of `B.eqs` with `dist z' z ≲ (min g z)²`, and the local Lipschitz bound keeps all
     `g z' ≥ (min g z)/2`.
  4. **Exponent bookkeeping** (`Work.WilE3.MPsi.atomDeg_phiPen_le`, `eval_mono`, PROVED):
     `atomDeg Φ ≤ (4q + 2) · B.deg + 1`, so the thresholds compose to
     `K = K_G.comp ((4(K_L + 1) + 2) · X + 1) + 1`, a polynomial in `B.deg` depending on `F` only.

  Assembled in `Work.WilE3.MPsi.maximalPsiNode_of_grad_loj` (from the two PROVED inequalities) and
  applied below.

  ### Elementary facts proved in this file

  * `dist` on `Fin k → ℝ` is the sup-metric (Gabrielov's `|x| = max_i |x_i|`): `dist_le_iff`,
    `abs_sub_le_dist`.
  * `eqs_eq_zero_of_mem_closure`, `pos_nonneg_of_mem_closure`: at a limit point of `B.holds` the
    equations vanish and the strict inequalities are nonnegative.
  * `exists_good_point_of_holds`, `exists_good_point_of_zeroSet`: the trivial case `y ∈ W` (take
    `z = y`) and the reduction of the conclusion to points of the zero set of the equations where
    every strict inequality beats `2 * dist (·, y) ^ κ`.

  (An earlier, abandoned route -- maximisers + KKT + an order bound along "stationary arcs" -- is
  visible in the workspace as `Work.WilE3.Taylor.{existsMaximiserMin,kktMaxMin,goodAlongArc}`; the
  lead's ruling is in `sources/wilkiesE3mpsi/wilkies_e3_maximalpsi.md` §3.)
-/

/-- **Gabrielov 1998's maximal-`ψ` estimate** (Lemmas 2.3/2.4 and the proof of Lemma 2.5,
`sources/wilkiesE/vision/gabrielov1998_frontier/p0007.md`–`p0008.md`), in the form
`Work.WilE3.MaximalPsiNode`, from the same separable-chain Khovanskii node that
`Work.WilE3.E3_identity_proved` takes.

For every basic EA set `B`, `y ∈ closure {B.holds}` and `κ` above the format threshold, there are
points `z` arbitrarily close to `y` at which every equation is small to order `κ^2` and every strict
inequality exceeds `dist (z,y)^κ`, both with margins (`a = 1/2`, `b = 2`).  With this node,
`Work.WilE3.Taylor.E3_taylor_closure_proved_of_multiplicity` proves the frozen `E3_taylor_closure`
with no hypothesis beyond `hK` (via `Work.WilE3.Realify.MultiplicityBound_of_ET`).

Route (Gabrielov 1998 §2): on the spheres `|x| = max_i |x_i| = const` about `y` the quantity
`ψ = min_j g_j` attains a maximum on `{φ ≤ a ψ^ν, ψ > 0}` (`φ = max_i |f_i|`); his critical-set
argument (Lemma 2.3: critical values of `(f,g)` avoid `Λ = {f = a g^ν}` for `ν > K`) makes these
maximal points effectively nonsingular, and the estimate `ψ (x) > c |x - y|^λ`, `λ ≤ K(n,r,α,β)`,
follows by decomposing the maximal set into effectively nonsingular pieces — that is exactly the
effectively smooth identity theorem `Work.WilE3.E3_identity_proved` (GV Cor. 4.7), applied with `hK`.
The exponent bound is absorbed into `K.eval B.deg`, and `B.deg` dominates the format parameters. -/
theorem maximalPsiNode (hK : ∀ F : ℕ, Work.WilE3.SepKhovanskiiET F) :
    ∀ F : ℕ, Work.WilE3.MaximalPsiNode F :=
  Work.WilE3.MPsi.maximalPsiNode_of_grad_loj
    (Work.WilE3.Taylor.ea_grad_of_multiplicity
      (Work.WilE3.Realify.MultiplicityBound_of_ET hK))
    (Work.WilE3.Taylor.hasLoj_of_multiplicity
      (Work.WilE3.Realify.MultiplicityBound_of_ET hK))

end Work.WilE3.Taylor
