import Submission.Work.RankOneUniqueness.Basic
import Submission.Work.RankOneUniqueness.exists_smul_t_eq
import Submission.Work.RankOneUniqueness.qPt_injective
import Submission.Work.RankOneUniqueness.qPt_surjective
import Submission.Work.RankOneUniqueness.smul_qPt
import Submission.Work.RankOneUniqueness.t_smul_qPt
import Submission.Work.RankOneUniqueness.conj_notMem
import Submission.Work.RankOneUniqueness.canon_unique
import Submission.Work.RankOneUniqueness.canon_exists
import Submission.Work.RankOneUniqueness.f_exists
import Submission.Work.RankOneUniqueness.f_unique
import Submission.Work.RankOneUniqueness.gen_top
import Submission.Work.RankOneUniqueness.mulEquiv_of_permEquiv
import Submission.Work.RankOneUniqueness.rankOneUniqueness
import Submission.Work.RankOneUniqueness.rankOneUniquenessFT
import Submission.Work.RankOneUniqueness.Statements
import Submission.Work.RankOneUniqueness.closure_Q_t_eq_top
import Submission.Work.RankOneUniqueness.mulEquiv_of_intertwining
import Submission.Work.RankOneUniqueness.rankOneQUniqueness
import Submission.Work.RankOneUniqueness.recognize
import Submission.Work.RankOneUniqueness.mapSubgroupEquiv

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.RankOneUniqueness` — the area `RankOneUniqueness` of the Bender–Suzuki project

**Deliverable.** `Work.RankOneUniqueness.rankOneUniqueness : RankOneUniquenessProp`
(and `rankOneUniquenessFT (hFT : FeitThompsonProp) : RankOneUniquenessProp`), i.e. Peterfalvi
II Ch. VII §1, Lemma p. 268: a finite group acting faithfully and 2-transitively with a split
BN-pair of rank one is determined up to isomorphism by the data of `H = Q ⋊ D` and of the
`f`-map on `Q#`.  No character theory is used (`hFT` is inert).

## Two targets

**(a) `RankOneUniquenessProp`** (Peterfalvi II Ch. VII §1 Lemma p. 268 in its `H`-form): two
split rank-one groups with isomorphic data `(H = Q ⋊ D, f)` are isomorphic.  Delivered by
`Work.RankOneUniqueness.rankOneUniqueness` (module
`Submission.Work.RankOneUniqueness.rankOneUniqueness`), with `rankOneUniquenessFT` the variant
carrying the (inert) `FeitThompsonProp` hypothesis.

**(b) `RankOneQUniquenessProp`** (the lead's design, S1–S6): recognition of a **simple**
split rank-one group from its `Q`-data `(Q, f)` alone.  This is the form the recognition areas
(`ZassenhausPSL2`, `ZassenhausSuzuki`, `PSU3`) use.

## Import

`import Submission.Work.RankOneUniqueness.All` pulls everything.  Downstream areas need only

* `Submission.Work.RankOneUniqueness.Statements` for the definitions
  `RankOneQUniquenessProp` and `ModelRankOneDatum`;
* `Submission.Work.RankOneUniqueness.recognize` for `recognize` (the recognition lemma);
* `Submission.Work.RankOneUniqueness.rankOneQUniqueness` for `rankOneQUniqueness : RankOneQUniquenessProp`.

## The `(Q, f)` route: statements

* `RankOneQUniquenessProp` (S1, `Statements.lean`): for simple `G`, `G'` with split rank-one
  data and `ψ : Q ≃* Q'` carrying the `f`-relation `(∃ m ∈ H, t x t = m t y)` of the first to
  that of the second, `Nonempty (G ≃* G')`.
* `ModelRankOneDatum Y C fC` (S5, `Statements.lean`): split rank-one data in a simple `Y`,
  `c : C ≃* Q`, `frel : u ≠ 1 → ∃ m ∈ M.H, M.t (c u) M.t = m M.t (c (fC u))`.
* `closure_Q_t_eq_top` (S2): for simple `G` with `IsSplitRankOne H Q t`,
  `Subgroup.closure (Q ∪ {t}) = ⊤`.  (`⟨Q, tQt⟩` is normal and nontrivial.)
* `mulEquiv_of_intertwining` (S3): permutation transport for arbitrary generating sets
  `S`, `S'` matched by a bijection `σ : S ≃ S'` (generalises `mulEquiv_of_permEquiv`).
* `rankOneQUniqueness` (S4): `RankOneQUniquenessProp`.
* `recognize` (S6): `RankOneQUniquenessProp → ModelRankOneDatum Y C fC → (Q ≃* C) →`
  (`FRel` becomes `fC`) `→ Nonempty (G ≃* Y)`.
* `mapSubgroupEquiv`: the restriction of `ψ : H ≃* H'` to corresponding subgroups
  `Q ≃* Q'` (bookkeeping for the recognition areas).

## Vocabulary (`Submission/Work/RankOneUniqueness/Basic.lean`)

* `pt H : G ⧸ H` — the base point `∞` (the coset of `1`); `smul_pt_iff`, `mk_eq_pt_iff` say
  that `H` is exactly the stabiliser of `∞`.
* `qPt H t x = x * t * H = x • (t • ∞)` — the point attached to `x`; for `x ∈ Q` these are
  exactly the points `≠ ∞` (`qPt_ne_pt`, `qPt_injective`, `qPt_surjective`).
* `FRel H t x y := ∃ m ∈ H, t * x * t = m * t * y` — the book's relation "`f(x) = y`".
* `IsCanon H Q t g a q := a ∈ H ∧ q ∈ Q ∧ g = a * t * q` — canonical form of `g ∉ H`.
* `FaithfulCosets H` — faithfulness of the action on `G ⧸ H`.

## Main lemmas (all in namespace `Work.RankOneUniqueness`)

Geometry of `Ω = G ⧸ H`, from `h : IsSplitRankOne H Q t`:

* `exists_smul_t_eq` — `Ω ∖ {∞}` is the `H`-orbit of `t • ∞`.
* `qPt_injective`, `qPt_surjective` — the map `Q → Ω ∖ {∞}`, `x ↦ qPt H t x`, is a bijection.
* `fact_exists`, `fact_unique` (`Basic`) — every `a ∈ H` is uniquely `q * d` with `q ∈ Q`,
  `d ∈ D = twoPoint H t`.
* `smul_qPt` — `a • qPt H t x = qPt H t z` when `a * x = z * d` (`a ∈ H`, `z ∈ Q`, `d ∈ D`).
* `t_smul_qPt` — if `t * x⁻¹ * t = m * t * y` (`x ∈ Q#`, `m ∈ H`, `y ∈ Q`) then
  `t • qPt H t x = qPt H t y⁻¹`.
* `conj_notMem` — `t * x * t ∉ H` for `x ∈ Q#`.
* `canon_exists`, `canon_unique` — `G ∖ H = H·t·Q`, uniquely.
* `f_exists`, `f_unique` — for `x ∈ Q#` there is a unique `y ∈ Q` with `FRel H t x y`.
* `gen_top` — `G = ⟨H, t⟩`.
* `mulEquiv_of_permEquiv` — abstract glue: a bijection `Ω ≃ Ω'` transporting the actions of
  `H` (via `ψ`) and of `t` (via `t'`), together with `G = ⟨H,t⟩`, `G' = ⟨H',t'⟩` and faithful
  actions, yields `G ≃* G'`.
-/

set_option autoImplicit false

namespace Work.RankOneUniqueness

end Work.RankOneUniqueness
