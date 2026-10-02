import Mathlib
import Submission.Work.Serre.ratPairBasic
import Submission.Work.Serre.CWModel.Tower

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The analytic inputs of the rational Serre pair comparison

The proof of `Work.Serre.ratSerrePairComparison` is assembled from four inputs, stated here as
`Prop`-valued definitions (so that the assembly can be written and checked independently of their
proofs):

* `RatCellStepSharp` (`Submission/Work/Serre/ratPairBasic.lean`) — the sharp rational cell step;
* `RatFibreTransport` (same file) — transport of the fibre's rational connectivity along a path;
* `RatPullbackComparison` — the base-change (pullback) comparison: if `g : Γ → B` is an `N`-equivalence
  then the pullback of `p` along `g` has the same relative homology as `p` in degrees `< N`;
* `RatTowerComparison` — the cellular induction over the CW model of `B`: for the twist of `p` over
  the `k`-th stage of `Work.Serre.CWModel.towerA`, the pair comparison
  `(X_k, q⁻¹γ₀) → (Γ_k, γ₀)` (the map `stagePairMapRat`) is an isomorphism in degrees `< b + f`
  and surjective in degree `b + f`.  It takes the sharp cell step as its (only) geometric input; the
  fibre hypotheses are quantified over *all* points of `B`, which is how the assembly supplies them
  (from the hypothesis at `b₀` by transport along paths, and from the connectivity of the fibres).

The last two together with the CW model `Work.Serre.CWModel.exists_model` and the two long exact
sequences of the pairs give the theorem.
-/

open scoped Topology
open CategoryTheory CategoryTheory.Limits

namespace Work.Serre

noncomputable section

/-- **The pullback (base-change) comparison.**  If `g : Γ → B` induces a bijection on `π_i` for all
`i ≤ N` and `p : E → B` is a Serre fibration, then the map of pairs
`(Γ ×_B E, q⁻¹{γ₀}) → (E, p⁻¹{b₀})` induced by the second projection of the pullback is an
isomorphism on rational homology in degrees `< N`. -/
def RatPullbackComparison : Prop :=
  ∀ {Γ B E : Type} [TopologicalSpace Γ] [TopologicalSpace B] [TopologicalSpace E]
    (g : C(Γ, B)) (p : C(E, B)) (γ₀ : Γ) (b₀ : B) (hbase : g γ₀ = b₀)
    (_hp : Work.StemsB.IsSerreFibration p) (N : ℕ)
    (_hg : ∀ i : ℕ, i ≤ N → ∀ x : Γ, Function.Bijective (Work.Serre.piMapN g i x)),
    ∀ i : ℕ, i < N → CategoryTheory.IsIso
      (HomologicalComplex.homologyMap (pullbackPairMapRat g p γ₀ b₀ hbase) i)

/-- **The cellular induction over the CW model of the base.**  For a `(b-1)`-connected base `B`
(`b ≥ 2`), a Serre fibration `p : E → B` whose fibres are rationally acyclic in degrees
`0 < j < f` and rationally connected, and every stage `k` of `Work.Serre.CWModel.towerA`, the map of
pairs `(X_k, q_k⁻¹{γ₀}) → (Γ_k, {γ₀})` (where `X_k = Γ_k ×_B E`) is an isomorphism on rational
homology in degrees `< b + f` and surjective in degree `b + f`. -/
def RatTowerComparison : Prop :=
  RatCellStepSharp →
  ∀ (E B : Type) [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B))
    (_hp : Work.StemsB.IsSerreFibration p) (b₀ : B) (b f : ℕ) (hb : 2 ≤ b)
    (_hconn : ∀ i < b, Subsingleton (HomotopyGroup (Fin i) B b₀))
    (_hfib : ∀ b' : B, ∀ j : ℕ, 0 < j → j < f → CategoryTheory.Limits.IsZero
      (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre p b')) j))
    (_h0 : ∀ b' : B, Nonempty (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre p b')) 0
      ≅ ModuleCat.of ℚ ℚ))
    (k : ℕ),
    (∀ i : ℕ, i < b + f → CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (stagePairMapRat (Work.Serre.CWModel.towerA B b₀ b hb _hconn k).g p
        (Work.Serre.CWModel.towerA B b₀ b hb _hconn k).y₀) i)) ∧
    Function.Surjective (HomologicalComplex.homologyMap
      (stagePairMapRat (Work.Serre.CWModel.towerA B b₀ b hb _hconn k).g p
        (Work.Serre.CWModel.towerA B b₀ b hb _hconn k).y₀) (b + f)).hom

end

end Work.Serre
