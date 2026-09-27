import Mathlib
import Submission.Work.EKLC6Core.plaquePartitionAux
import Submission.Work.EKLC6Core.atom_generateFrom_range_eq
import Submission.Work.EKLC6Core.exists_desc_subordinate
import Submission.Work.EKLC6Core.exists_gen_plaque_erg
import Submission.Work.EKLC6Core.mem_uminus_of_shadowing
import Submission.Work.EKLC6Core.thin_pattern_partition
import Submission.Work.EKLC6Core.exists_refining_part_seq_borel
import Submission.Work.EKLC6Core.plaqueAlgebra_of_ae_pointwise
import Submission.Work.EKLC6Core.ae_transfer_descending_plaque
import Submission.Work.EKLC6Core.good_time_freq
import Submission.Work.EKLC6Core.ae_eventually_not_mem_VThick
import Submission.Work.EKLC6Core.adapted_partition
import Submission.Work.EKLC6Core.ae_free_orbit_of_contraction
import Submission.Work.EKLC6Core.Uball_uminus_subset_shape_of_avoid
import Submission.Work.EKLC6Core.past_atom_contains_Uball_of_thin_frontier

/-!
# `Work.EKLC6Core.finPart_plaquePast_exists`

The frozen target: for a probability measure `μ` on `X₃ = SL₃(ℝ)/SL₃(ℤ)`, a vector
`t : Fin 3 → ℝ` with `Uminus t ≠ ⊥`, `μ` preserved by `φ = (aDiag t ·)` and ergodic for `φ`,
with `0 < ent μ φ`, there are a *finite* partition `P` and a `μ`-conull set `Z` such that the
past σ-algebra `pastSigFinPart t P = ⨆ₙ comap (φ^[n]) (partSigma P)` is a plaque algebra for
`U = Uminus t` on `Z`.

## Status of the proof (read this first)

Proved here (all sorry-free below the header):

* `pastSigFinPart_countably_generated` — the "countably generated" clause of `IsPlaqueAlgebra`
  is automatic for the past σ-algebra of a finite partition.
* `finPart_plaquePast_exists_of_ae` — the target follows from the three *a.e.* pointwise plaque
  conditions for `A := pastSigFinPart t P`, via `Work.EKLC6Core.plaqueAlgebra_of_ae_pointwise`.
* `ae_orbit_of_positive_measure_plaque` — the a.e. orbit clause and "fatness at `1`" follow from
  `IsPlaqueAlgebra U Y A` on a *single* positive-measure set `Y`
  (`Work.EKLC6Core.ae_transfer_descending_plaque`).
* `atom_pastSigFinPart_subset_uminus_of_room` — **the dynamical half of the target**: if along the
  orbit of a.e. `x` the conjugates `aDiag t^{n k} * g * (aDiag t^{n k})⁻¹` of the group element `g`
  relating an atom mate `y = g • x` to `x` are `V (ε k)`-small with `ε k → 0`, then `g ∈ Uminus t`
  (entrywise squeeze through `boxi_conj_pow_apply` + `mem_uminus_of_entry_form`).
* `ae_room_visits_of_pos_sets` — positivity of the "thin room" sets for every scale turns into the
  visit hypothesis of the previous lemma, by ergodicity (`Work.EKLC6Core.good_time_freq`).

## The corrected chain (stabiliser-safe), and the one input still to come

* `mem_uminus_of_conj_small` — the stabiliser-free core: if the conjugates of `g` are `V (ε k)`-small
  along a sequence of times with `ε k → 0`, then `g ∈ Uminus t`.
* `exists_small_rep_of_thin_cells` — the *point-free* geometric input (at the good times any two
  points of the `partSigma P`-atom of `φ^{n k} x` are related by a `V (ε k)`-element) yields, for
  every atom mate `y` of `x`, a *family* of representatives `u k` with `u k • x = y` whose `n k`-th
  conjugates are `V (ε k)`-small.
* `atom_pastSigFinPart_subset_uminus_of_thin_cells` — that input together with the *pinning*
  statement (below) gives the a.e. atom containment.

**Why the naive formulation was wrong** (found by a reviewer): for every `y ∈ X₃` the stabiliser of
`y` under the left action is the infinite discrete group `g Γ₃ g⁻¹`; every `h` in it satisfies
`h • y = y ∈ [y]_P`.  Hence

* the room set `{g | g • y ∈ [y]_{partSigma P}}` is *never* contained in `V ε` for small `ε`, so the
  hypothesis `∀ g, g • y ∈ [y]_P → g ∈ V ε` is unsatisfiable, and
* the intermediate formula `hroom` of `ae_room_visits_of_pos_sets` (kept above for the record) is
  vacuous; its *conclusion* is instead supplied by the corrected chain below.

**The two inputs being delegated** (they are the only missing pieces):

1. `Work.EKLC6Core.pin_of_finitely_many_reps` — if the family `u k` of representatives of a relation
   `u k • x = y` with `V (ε k)`-small `n k`-th conjugates takes only *finitely many values*, then
   some single element `v ∈ Uminus t` satisfies `v • x = y` (proved from
   `mem_uminus_of_conj_small` by extracting a repeated value).
2. `Work.EKLC6Core.exists_finPart_thin_cells_family` — the geometric existence: a finite partition
   `P` and, for a.e. `x`, for every atom mate `y`, a *finitely valued* family of representatives
   with `V (ε k)`-small conjugates at times `n k → ∞`, `ε k → 0`.  This is the only place where the
   "resolution at all scales" of Pisa 7.53 is still needed; a *finite* partition of "reasonable"
   (smooth) cells cannot supply it (its cells have a fixed size), which is exactly the source's
   remark that the finite-partition form "may not hold" — hence the need for the stabiliser-safe
   formulation and for the fleet.

Note: the target is *not* obstructed by the stabiliser: the a.e. freeness
`∀ᵐ x, ∀ u ∈ Uminus t, u • x = x → u = 1` is available in the workspace and can be intersected
into the conull `Z` (otherwise a non-identity `u ∈ Uminus t ∩ Stab(x)` would lie in `shape(x)` and
violate the entrywise boundedness clause of `IsPlaqueAlgebra`).

## Why the remaining input cannot be split further (analysis, this session)

A sharpened analysis of the last gap, for the record and for whoever picks this up:

* The *expanding* directions are killed by **boundedness alone**: if `g` is fixed (pinned) and its
  `n k`-th conjugate lies in `V ε₀` for a fixed `ε₀` and times `n k → ∞`, then every entry with
  `t i > t j` satisfies `|gᵢⱼ| ≤ ε₀ e^{-n k (tᵢ-tⱼ)} → 0`, hence `gᵢⱼ = 0`.
* The **diagonal** (centraliser) entries satisfy only `|gᵢᵢ - 1| < ε₀`, and `det g = 1` plus the
  triangular shape does not force `gᵢᵢ = 1`.  So a *non-shrinking* resolution `ε k ≤ ε₀` is
  insufficient: the centraliser ambiguity survives, which is exactly the `G⁰`-term in Pisa 7.53.
* Killing it requires `ε k → 0`, and that requires partition elements of *arbitrarily small radius
  along the orbit* — for a finite partition of "reasonable" cells (each of a fixed positive
  V-diameter) the infimum over cells of the relevant diameter is positive, so no finite partition
  supplies the shrinking resolution.  This is precisely the source's caveat in 7.53 ("if only
  finitely many scales occur, the last statement may not hold"), repaired there by passing to a
  *countable* partition — which `FinPart` cannot express.

Consequently the last input is *equivalent to the crux* and is not a splittable piece; it must be
attacked directly (or the statement must be judged false).  The two pieces that *are* independent
have been extracted and one of them (`pin_of_finitely_many_reps`) has been delegated.

## The countable chain (started this session, at the request of the review)

Because `ae_no_thin_scaling_of_finPart` (delegated) shows that *finite* partitions cannot supply the
point-free thin-cell hypothesis with `ε k → 0`, the scale-shrinking input has to come from a
*refining sequence* of partitions, one level per scale — exactly the shape in which Pisa 7.43
obtains its partition.  The two countable lemmas, proved here, are the verbatim analogues of the
finite ones:

* `exists_small_rep_of_refining_seq` — level-`k` thinness of the orbit point's `P k`-cell yields,
  for every atom mate `y` of the join `⨆ k, pastSigFinPart t (P k)`, a family of representatives
  with `V (ε k)`-small `n k`-th conjugates, with `ε k → 0` genuinely available;
* `atom_iSup_pastSigFinPart_subset_uminus_of_thin_levels` — that input plus the pinning statement
  gives the atom containment for the join σ-algebra.

The remaining geometric input for the countable chain is the *existence of the refining sequence
with thin cells at the visit times* (level `k`'s cells of diameter `≤ (k+1)⁻¹` inside the thick
part, whose union has positive measure and is therefore visited infinitely often by ergodicity).
Unlike the finite version this is satisfiable, and it is the next piece to state and delegate.

## Reductions proved here

* `pastSigFinPart_countably_generated` — the clause "`m` countably generated" of
  `IsPlaqueAlgebra` is automatic for the past σ-algebra of a finite partition.
* `finPart_plaquePast_exists_of_ae` — the target follows from the three *almost-everywhere*
  pointwise plaque conditions for `A := pastSigFinPart t P`, by
  `Work.EKLC6Core.plaqueAlgebra_of_ae_pointwise` (which converts a.e. conditions into
  set-theoretic conditions at every point of a conull `A`-measurable `Z` via the code-map hull).
  So the whole difficulty of the target is concentrated in producing a *finite* partition `P`
  with those a.e. conditions.
* `ae_orbit_of_positive_measure_plaque` — the a.e. orbit clause and the a.e. "fatness at `1`" of
  the shape follow from `IsPlaqueAlgebra U Y A` for a *single* set `Y` of positive measure
  (the ergodicity transfer `ae_transfer_descending_plaque`); hence the remaining (hard) input is
  that one positive-measure set.
## The centraliser criterion (proved, this session) and the exact remaining obligation

`movedSet P c = ⋃ i, (P i ∩ c⁻¹'(P i)ᶜ)` is the set of points whose part of `P` is not preserved
by `c • ·` (it is measurable by construction).  The two lemmas

* `ae_not_mem_atom_of_part_moved` : `0 < μ (movedSet P c)` (and `c` commuting with `aDiag t`) ⟹
  `c • x ∉ atom (pastSigFinPart t P) x` for a.e. `x`;
* `ae_mem_atom_of_part_fixed` : `μ (movedSet P c) = 0` ⟹ `c • x ∈ atom (pastSigFinPart t P) x`
  for a.e. `x`

are proved above (with `mem_movedSet_iff`, `mem_atom_pastSigFinPart_iff`,
`mem_atom_partSigma_iff`, `parts_subset_atom` as the supporting atom calculus).  They say that a
*finiteness* obstruction is transparent and *static*: the past atom contains the displacement
`c • x` by a central element `c` **iff** `c` preserves every part of `P` up to a null set.  Hence

* the target's clause `atom (pastSigFinPart t P) x ⊆ Uminus t · x` forces
  `⋂ i {c ∈ SL3 : μ (part i ∩ c⁻¹' part i) = μ (part i)} ⊆` (the elements acting trivially on
  `X₃`) — a condition that a *finite* partition of the non-compact `X₃` can meet only by being
  "transverse" to the centraliser at level `0`;
* by `finPart_plaquePast_exists_of_ae` the target is therefore *equivalent* to: there is a finite
  partition `P` whose levels move every non-trivial central element, and whose `pastSigFinPart`
  atoms are bounded open `Uminus t`-plaques.  The second part is the content of Pisa 7.38 + 7.53
  + 7.54; the source records that for a *finite* partition "the last statement may not hold"
  (Pisa 7.53) and repairs it by refining to a countable partition with pieces at all scales, so
  the finite-partition form must be decided by a direct construction (or a counterexample).

-/


/-! ## STATUS (session 15:0x–15:4x): the `adaptedPart`/thin-inj route is DEAD; the surviving route

### Machine-checked outcomes of the two delegated pieces of this route

* `Work.EKLC6Core.exists_covering_thin_inj_partition` (H80-L1604): **PROVED** (file
  `Submission/Work/EKLC6Core/exists_covering_thin_inj_partition.lean`, sorry-free) — the finite
  partition `Q` with one exceptional piece `μ (Q i₀) < ε`, the other pieces inside `V ρ`-balls
  with the `60 ρ`-injectivity, and a thin boundary.
* `Work.EKLC6Core.shape_subset_Uball_of_inj` (H80-L1594): **declared FALSE by its prover**.  The
  decisive point: for `y ∈ Q ⊆ V ρ • mkX g` the level-`0` shape of the *piece* is literally the
  **return set** `{u ∈ Uminus t : u • y ∈ Q}` of the horospherical orbit into the open cell
  (`atom (partSigma P) y = P.parts k = Q`), and for a generic `y` that set is **unbounded** — the
  `Uminus t`-orbits are recurrent, so they re-enter every open cell arbitrarily far out.  Freeness
  of the `Uminus t`-stabiliser (`hfree`) and the `60 ρ`-injectivity do **not** repair this.
  Consequence: the per-piece boundedness input `hsmall`/`hexc` of
  `ae_isOpen_shape_pastSigFinPart_of_pieces`/`..._of_thin_inj_data` (below) is **unavailable**, and
  with it the *openness* and *boundedness* clauses of this route.  (The *past*-algebra shape is a
  different, smaller set — the return set into the atom, not into the level-`0` cell — so the
  target is not refuted by this, but the level-`0`-margin mechanism is.)
* `Work.EKLC6Core.crescent_mass_pos_of_pieces` (H80-L1603): **declared FALSE by its prover**, by
  `μ = δ_p` with `p` a fixed point of `aDiag t` having a non-trivial centraliser element `c`
  (then `¬ (∀ y, c • y = y)` and `μ (crescent) = 0`).  Note `δ_p` has `ent = 0`, so this does not
  bear on the target's hypotheses; but *any* restatement of that lemma needs an explicit
  non-degeneracy hypothesis (e.g. `0 < ent μ (aDiag t ·)`, or `μ {y | c • y = y} = 0`, plus
  `hmp`/`hqerg`), otherwise it is false.

### The surviving route (this is the one to pursue)

Let `A` be a **countably generated, `aDiag t`-decreasing plaque algebra on a conull set**, i.e.

  `IsPlaqueAlgebra (Uminus t) Z₀ A`,  `μ Z₀ᶜ = 0`,  `comap ((aDiag t)·) A ≤ A`.

Such an `A` is **PROVED to exist, unconditionally** (`hmp` + `hqerg` only) in the workspace:

* `Work.EKLC6Core.desc_plaque_algebra_conull_ergodic_gen` (file
  `Submission/Work/EKLC6Core/desc_plaque_algebra_conull_ergodic_gen.lean`; the whole import
  closure is `sorry`-free — verified textually this session), and
* `Work.EKLC6Core.plaqueAlg_conull_of_erg` (its wrapper with the frozen signature).

Then the target follows from the **single** remaining input

  `(★)  ∃ P : FinPart X3,  A ≤ pastSigFinPart t P`.

Why: `A ≤ A_P := pastSigFinPart t P` makes every `A_P`-atom a subset of an `A`-atom, so

* orbit clause: `atom A_P x ⊆ atom A x ⊆ Uminus t • x` (for `x ∈ Z₀`);
* boundedness: `shape A_P (Uminus t) x ⊆ shape A (Uminus t) x`, the latter entrywise bounded;
* openness: `shape A_P (Uminus t) x` is open in `Uminus t` because for `u₀` in it,
  `atom A (u₀ • x) ⊆ atom A_P (u₀ • x) = atom A_P x`, hence `u₀ · shape A (Uminus t) (u₀ • x)`,
  a `Uminus t`-neighbourhood of `u₀`, lies in `shape A_P (Uminus t) x`.

(★) is equivalent to the *orbit clause* for `P`, i.e. to "the one-sided `P`-itinerary of `x`
determines `x` modulo `Uminus t`": `A_P`'s atoms are exactly the itinerary classes, so
`A ≤ A_P` says every `A`-atom (= a `Uminus t`-plaque) is a union of itinerary classes, i.e. the
itinerary class of `x` lies in the plaque `[x]_A ⊆ Uminus t • x`.

### How the orbit clause splits (and where the crux is)

Write `C(φ)` for the centraliser of `φ = aDiag t` in `SL₃(ℝ)` and
`P_t = {v : v i j = 0 whenever t i > t j}` for the parabolic (the "forward-bounded" elements).
Then:

1. **`atom A_P x ⊆ P_t • x`** — this is *provable* by the following mechanism: if the parts of `P`
   are `V ρ`-balls around centres (all but one), then for `y ∈ atom A_P x` one has `y = v • x` for
   a fixed `v` and, at every time `n` at which the pair `(φⁿ x, φⁿ y)` lies in a *small* part
   (which happens with positive frequency and hence infinitely often, by the itinerary condition
   and the measure of the exceptional part being `< 1`), the conjugate `φⁿ v φ⁻ⁿ` is bounded by a
   fixed `C ρ`; the entries with `t i > t j` therefore satisfy `|v i j| ≤ C ρ e^{-n (t i - t j)}`
   along that sublist, whence `v i j = 0`.  *Care*: the representative `v` is only determined
   modulo `Stab(x)`, so the conjugates are bounded only modulo `φⁿ Stab(x) φ⁻ⁿ`; the argument
   needs the `60 ρ`-injectivity/freeness to control that ambiguity (this is the one subtle step of
   the piece, and the reason the naive `shape_subset_Uball_of_inj` was false).
2. **Killing the centraliser part of `v`.**  `v = c · u` with `c ∈ C(φ) = ` the block-diagonal
   Levi and `u ∈ Uminus t` (Levi decomposition of `P_t`).  A *fixed* `c ∈ C(φ)` is handled: for
   `c` not acting trivially on `X₃`, a.e. `c • z ∉ atom A_P z`.  The two lemmas
   `ae_not_mem_atom_of_part_moved` and `ae_mem_atom_of_part_fixed` (both proved above) show this is
   exactly the dichotomy `μ (movedSet P c) = 0` vs `> 0`, and `movedSet P c > 0` is what a corrected
   crescent lemma must supply (with the non-degeneracy hypothesis flagged above).
   The **remaining crux** is the *varying* case: a priori `y = c_x · u_x • x` with `c_x ∈ C(φ)`
   depending measurably on `x`.  Nothing in the `φ`-ergodicity argument excludes this (each fixed
   `c` has its own null exceptional set, the union over the continuum being invisible to
   `μ`), and this is precisely the case Pisa 7.53 calls out ("the last statement may not hold" for
   a finite partition; the source repairs it by a countable partition with pieces at all scales).
   So the target's remaining obligation is exactly: **show that the varying central displacement
   cannot occur for a suitable finite `P`** (equivalently: run the Pisa 7.53/7.51 construction with
   a *finite* partition, i.e. produce one finite partition whose coding already gives scales
   `ε k → 0` along the orbit — cf. `ae_no_thin_scaling_of_finPart`, which shows that a *fixed*
   finite partition cannot supply that for the naive point-free thin-cell input).

### Other necessary conditions (useful sanity checks for any proposed `P`)

* `hPart μ (aDiag t ·) P = ent μ (aDiag t ·)` is *forced* by the target (Pisa 7.25(i)/7.34:
  the conditional entropy `H_μ (A_P | φ⁻¹ A_P) = hPart μ φ P` equals the entropy contribution
  `h_μ (φ)`); so `P` must be entropy-maximal, and in particular `ent μ φ < ∞` is necessary
  (which is why no contradiction arises from finite entropy, but `0 < ent = ⊤` would refute the
  target outright).  The existence of such a finite `P` is Krieger's finite generator theorem
  (applied to the Pinsker factor of `φ`).
* For every non-trivial `c ∈ C(φ)` acting non-trivially on `X₃`: `μ (movedSet P c) > 0`.

### Where the proof stands in this file

Green (one `sorry`, the frozen target).  Proved here: the atom calculus
(`mem_atom_pastSigFinPart_iff`, `mem_movedSet_iff`, …), the centraliser dichotomy
(`ae_not_mem_atom_of_part_moved`, `ae_mem_atom_of_part_fixed`), the reduction
`finPart_plaquePast_exists_of_ae` (target ⟸ the three a.e. clauses), the conjugation squeeze
(`mem_uminus_of_conj_small`), and the (now dead-route) openness/boundedness wiring through the
cut data `adaptedPart`/`exists_covering_thin_inj_partition`.  The dead parts are kept for the
record; the live obligation is `(★)` above.

### Addendum (same session): the second shape-boundedness delegate is false too

`Work.EKLC6Core.shape_partSigma_subset_Uball_of_piece` (H80-L1657, delegated this session) was
also declared **FALSE** by its prover, for exactly the same reason as H80-L1594: for an open cell
`Q` the shape is the return set `{u ∈ Uminus t : u • y ∈ Q}`, and the `Uminus t`-flow is
measure-preserving on the probability space, so `μ`-a.e. `y` is recurrent and the return set is
unbounded.  The prover's closing remark is the important structural pointer for the next session:
the valid analogues of this boundedness in the workspace (`shape_uball_base`, `atom_MSig2`) do
**not** get boundedness from the *cell* containment but from the **lift-chained / pattern class**
structure of the atom — `u • lift y ∈ V ρ · g`, i.e. from the `CutData.lift_eq` local
`U`-equivariance of the lift — which is precisely the structure that the *countably generated*
cut σ-algebra `MCut S O` has and that a level-`0` piece of a finite partition does not.  This is
one more reason why the surviving route is the `(★)` reduction above (start from the *proved*
countably generated plaque algebra `A` and only ask for a finite partition whose past algebra
contains it).
-/

/-! ## STATUS (session 16): the sharpened reduction, and the exact remaining gap

### 1. `(★)` in the form the proof actually uses

`A` is *proved* to exist (`desc_plaque_algebra_conull_ergodic_gen`): countably generated,
`comap (aDiag t ·) A ≤ A`, `IsPlaqueAlgebra (Uminus t) Z₀ A`, `μ Z₀ᶜ = 0`.  Write
`A = ⨆ₙ comap (φ^[n]) M` for the cut σ-algebra `M = MCut S O`.  Because `comap φ A ≤ A` (so
`comap (φ^[n]) A ≤ A` for every `n`), the input

  `(★)  ∃ P : FinPart X₃,  A ≤ pastSigFinPart t P`

is *equivalent* to the single inclusion

  `(★')  M ≤ pastSigFinPart t P`.

Indeed `(★')` gives `comap (φ^[n]) M ≤ comap (φ^[n]) A_P ≤ A_P`, and conversely `(★')` follows
from `(★)` at `n = 0`.  Since `M` is generated by the cut cells `genCell S O i m` (bounded
diameter!) and `bad`, `(★')` says exactly: *the one-sided `P`-itinerary determines the cut cell
of `x`*, i.e. the itinerary determines the `A`-plaque of `x`.

### 2. What `(★)` buys for free — no centraliser analysis is needed

If `A ≤ A_P` then `A_P` is *finer*, so for every `x`

* `atom A_P x ⊆ atom A x`; combined with `atom A x ⊆ (Uminus t) • x` (the plaque property of `A`,
  valid for `x ∈ Z₀`) this yields the **orbit clause** of the target;
* `shape A_P (Uminus t) x ⊆ shape A (Uminus t) x`, and the latter is entrywise bounded
  (`IsPlaqueAlgebra`), which yields **boundedness**.

In particular the fixed-c centraliser dichotomy (`ae_not_mem_atom_of_part_moved`,
`ae_mem_atom_of_part_fixed`, both proved above) is *not* needed once `(★)` holds: the orbit
clause follows from `A`'s own plaque structure.  This is the one genuine simplification of the
session: the "varying central displacement" crux of the earlier STATUS block is *bypassed* by
the `(★)` route.

### 3. The one gap left by `(★)`: openness of the shape of `A_P`

The naive transfer used in the earlier STATUS block is **invalid**: from `u₀ ∈ shape A_P U x` one
gets `atom A (u₀ • x) = atom A x` and hence `u₀ · (shape A U (u₀ • x)) ⊆ {u : u • x ∈ atom A x}`,
which is *not* `shape A_P U x` — one would need `atom A x ∩ (U • x) ⊆ atom A_P x`, a
"coincidence" of the two atoms on the `U`-directions that `A ≤ A_P` does not give.

What *does* work, and is what the source's 7.31 supplies: if for a.e. `x` the past atom of `P`
contains a `U`-ball at `x` (`∃ δ > 0, Uball (Uminus t) δ ⊆ shape A_P (Uminus t) x`, Pisa 7.31,
for a finite `P` with `μ`-thin frontier), then for `u ∈ shape A_P U x` with `x' := u • x` a
7.31-good point one has `atom A_P x' = atom A_P x` and hence

  `u · Uball (Uminus t) (δ x') ⊆ shape A_P (Uminus t) x`,

i.e. `u` is an interior point of the shape.  Since the 7.31-bad set `N` is `μ`-null and `U` acts
measure preservingly and essentially freely, for `μ`-a.e. `x` the set of `u ∈ U` with
`u • x ∈ N` is Haar-null in `U`; the shape is therefore open *up to a Haar-null set of
directions*.  Making this into the literal a.e. statement

  `∀ᵐ x ∂μ, ∃ O : Set SL3, IsOpen O ∧ shape A_P U x = O ∩ (U : Set SL3)`

is the exact remaining obligation of the reduction; it is the second (and last) occurrence of
the "resolution" problem, and it is *independent* of the centraliser question.

**Both halves are now FORMAL in this file:**

* `transfer_orbit_and_bdd_of_le` — `(★)` gives the orbit clause and the entrywise boundedness of
  the `A_P`-shape (proof: `atom A_P x ⊆ atom A x ⊆ (Uminus t) • x` and
  `shape A_P ⊆ shape A`, with `atom A x ⊆ Z₀` for `x ∈ Z₀`);
* `finPart_plaquePast_exists_of_le` — `(★)` together with the a.e. openness
  (`∀ᵐ x, ∃ O, IsOpen O ∧ shape A_P (Uminus t) x = O ∩ Uminus t`) yields
  `∃ Z, μ Zᶜ = 0 ∧ IsPlaqueAlgebra (Uminus t) Z (pastSigFinPart t P)`,
  by direct application of the proved `finPart_plaquePast_exists_of_ae`.

So after this session the frozen target is equivalent to the conjunction of exactly two named
inputs: `(★')  M ≤ pastSigFinPart t P` for some finite `P`, and the Pisa 7.31 openness
(`past_atom_contains_Uball_of_thin_frontier`, delegated to a colleague: a.e. the past atom of
`P` contains a `Uminus t`-ball at its point — the geometric Borel-Cantelli input
`ae_uncrossed_of_thin_frontier` is already PROVED in the workspace, so only the derivation from
it to the uniform-in-`n` form is missing — **and that derivation is now PROVED too**, by a
colleague, as `Work.EKLC6Core.past_atom_contains_Uball_of_thin_frontier` (imported at the top of
this file): for a.e. `x` there is `δ > 0` with
`∀ u ∈ Uball (Uminus t) δ, ∀ n k, (φ^[n]) x ∈ Q k → (φ^[n]) (u • x) ∈ Q k`.

### 6. The openness gap, sharpened (for the next session)

With §3's argument and the 7.31 input, the shape `shape A_P U x` *is* open at every direction
`u₀` for which the point `u₀ • x` is 7.31-good: `atom A_P (u₀ • x) = atom A_P x` (because
`u₀ ∈ shape A_P U x`) and hence `u₀ • Uball (Uminus t) (δ (u₀ • x)) ⊆ shape A_P U x`.  Since the
7.31-bad set is `μ`-null and `U` acts measure-preservingly and essentially freely, for `μ`-a.e.
`x` the set of *bad directions* `{u ∈ U : u • x ∈ N}` is Haar-null in `U` — but not empty.  So
the remaining point of §3 is exactly:

  `(†)  for μ-a.e. x,  shape A_P U x ∩ {u ∈ U : u • x ∈ 7.31-bad} = ∅`,

i.e. the shape must contain no bad direction.  `(†)` is a *uniformity* statement about the
Borel–Cantelli set `N` along the `U`-orbits inside the shape; together with `(★')` it is the
complete residue of the frozen target, and both are independent of the centraliser question of
the earlier STATUS blocks.

### 4. Why the alternative route (kill the centraliser directly) is not available

The set `Σ_P := {x : ∃ c ∈ C(φ) \ {1}, c • x ∈ atom A_P x}` is *forward* `φ`-invariant (since
`c φⁿ = φⁿ c` for `c ∈ C(φ)`), hence `μ Σ_P ∈ {0,1}` by ergodicity.  Ruling out `μ Σ_P = 1`
requires excluding a *measurable selection* `x ↦ c(x)`, and via the conjugacy-class description
`c • x ∈ atom A_P x ⟹ c ∈ Uminus t · Stab(x) = Uminus t · x Γ₃ x⁻¹` this reduces to

  `(γ)  ∀ γ ∈ Γ₃ \ {1},  μ {x : x γ x⁻¹ ∈ Uminus t · C(φ)} = 0`.

`(γ)` is *not* available from the hypotheses: the set in question is closed with empty interior
but need not be null for a singular, merely `φ`-invariant `μ`.  So the `(★)` route — which uses
only the intrinsic `A` — is the correct one.

### 5. For the record: the target is not refuted

`dim (Uminus t) + dim C(φ) < dim X₃` (e.g. `3 + 2 < 8` for `t` with distinct entries), so for a
finite partition whose atoms are "transversal to the centraliser" the plaque atom meets the
centraliser orbit only in the point; the source's caveat after 7.53 ("the last statement may not
hold") is about *its* construction, whose pieces have a fixed positive transverse size, and not a
refutation of the existential statement.  The fleet's "mis-stated" verdicts in
`GENFINPARTPLAQUE_STATUS.md`, `ENTROPY_GEN_NOTE.md` §2, `Ch_finPart_plaque_generating.lean` and
`ent_le_HcondSig_of_gen_mp_clean.lean` are all of that route-based kind.  Hence the target stays
open, and the two named obligations are `(★')` and §3 above.
-/

/-! ## STATUS (session 17): the central-direction crux reduced to a convexity bridge

### 1. Where the target stands

The target is `∃ P : FinPart X₃, ∃ Z, μ Zᶜ = 0 ∧ IsPlaqueAlgebra (Uminus t) Z (pastSigFinPart t P)`.
By the proved `finPart_plaquePast_exists_of_ae` it suffices to produce a **single finite** `P` with
the three `a.e.` clauses

  (i) `atom (pastSigFinPart t P) x ⊆ Uminus t · x`   (the orbit clause),
  (ii) the shape is open in `Uminus t`,
  (iii) the shape is entrywise bounded.

`transfer_orbit_and_bdd_of_le` + `finPart_plaquePast_exists_of_le` derive (i)+(iii) from

  `(★)  M ≤ pastSigFinPart t P`,   `M = MCut S O` the cut σ-algebra of the proved descending
                                    plaque algebra `A = ⨆ₙ comap (φⁿ) M`,

and (ii) from `(★)` plus the Pisa 7.31 input.  Moreover `(★)` follows from (i) whenever `P`
refines the cut cells: the generators `genCell S O i m` are `U`-saturated conditions intersected
with a *cell*, so on a cell-refining `P` the itinerary class (the `A_P`-atom) cannot cross a
generator boundary.  (Making this formal needs "an open `A_P`-atom-saturated Borel set is
`A_P`-measurable", i.e. `w(C) ∈ Borel` for the coding map `w`; it is absent from Mathlib and is a
candidate `delegate`.)  So the target is the orbit clause (i) for a suitable finite `P`, plus
openness (ii).

### 2. The crux: the *joint* central-direction killing

`ae_not_mem_atom_of_part_moved` (proved above) kills a single central element: `c ∈ C(φ)` and
`0 < μ (movedSet P c)` imply `c • x ∉ atom x` a.e.  The source's caveat after 7.53 says that a
*finite* `P` cannot run its shrinking-resolution argument (which needs pieces at unbounded return
scales), so no published argument kills the central displacements *jointly*; this is the "varying
central displacement" crux of the session-15 block, and (with §5) it is the whole remaining
content of clause (i).

### 3. The shadow-set reformulation (this session, formalised below)

For `c : SL₃(ℝ)`: `fixedSet P c = ⋃ i, (part i ∩ c⁻¹'(part i))` (the points whose part is
preserved) and `shadowSet t P c = ⋂ n, (φ^[n]) ⁻¹' (fixedSet P c)` (the points whose *whole forward
orbit* has its part preserved).  Formalised here:

* `shadowSet t P c` is measurable and forward invariant, hence (`hmp`, `hqerg`)
  `μ (shadowSet t P c) = 0 ∨ μ (shadowSet t P c)ᶜ = 0` (`shadowSet_measure_zero_or_univ`);
* `shadowSet t P c ⊆ fixedSet P c = (movedSet P c)ᶜ`, so `0 < μ (movedSet P c)` forces
  `μ (shadowSet t P c) = 0` (`shadowSet_measure_zero_of_moved`).

So for a fixed `c` the statement is *dichotomic*: either `c` preserves every part up to a null set
(and then `c • x ∈ atom x` a.e. by `ae_mem_atom_of_part_fixed`), or the `c`-shadow is null.  There
is no intermediate case, i.e. the per-`c` result cannot be improved: the target's clause (i) needs
the *joint* statement `∀ᵐ x, ∀ c ∈ C(φ)\{1}, c • x ∉ atom x`, which is exactly where a finite
partition differs from Pisa's countable one.

### 4. The Fubini step and the exact residual gap

Parametrise `C(φ) = {aDiag s : ∑ s = 0}` (a `2`-dimensional subspace ≅ ℝ²) and let `λ` be
Lebesgue measure on it.  If `μ (movedSet P (aDiag s)) > 0` for `λ`-a.e. `s`, then by §3
`μ (shadowSet t P (aDiag s)) = 0` for `λ`-a.e. `s`, and Mathlib's product-Fubini lemma
(`MeasureTheory.Measure.ae_prod_mem_iff_ae_ae_mem`) gives

  `∀ᵐ x, λ {s : x ∈ shadowSet t P (aDiag s)} = 0`.

So the *only* gap in the central half is the upgrade from "`λ`-null" to "`= {0}`" for
`H(x) := {s : ∀ n, aDiag s • (φ^[n] x) ∈ part (φ^[n] x)}`, a closed, Lebesgue-null set containing
`0` — and a null set need not be trivial (it can be a curve).  This is precisely the sense in which
a finite `P` is weaker than Pisa's countable one.  The concrete ways to finish, in increasing order
of work:

* **convexity bridge.**  If every part of `P` meets every `C(φ)`-orbit in a set that is *convex* in
  the `s`-coordinates, then `H(x)` is convex, closed and contains `0`; being `λ`-null it lies in a
  line, and the one-parameter version of the same Fubini argument (Lebesgue measure *on that line*)
  rules the line out, giving `H(x) = {0}`.  What is needed is a finite `P` whose pieces are
  "`C(φ)`-convex wedges" refining the cut cells with thin frontiers — a *geometric* construction,
  independent of the dynamics.
* **one-sided depth.**  For a single direction `ξ` the same argument with the one-parameter family
  `s ↦ aDiag (sξ)` gives `{s : aDiag (sξ) ∈ H(x)} = {0}` for a.e. `x`; over a *countable dense* set
  of directions this gives `H(x) ∩ D = {0}`, which alone is not enough (a curve can avoid `D`), so
  this variant needs the convexity as well.

Either way the residual is a statement about the *geometry of the pieces*, not about the dynamics.

### 5. The expanding directions, and why the Pisa mechanism is unavailable

For `y ∈ atom x` with `y = g • x`: at a time `n` with `φⁿx`, `φⁿy` in a common part of diameter
`ρ`, the conjugate `a^n g a^{-n}` lies in a fixed `V(Cρ)`-box, so the entrywise squeeze
(`mem_uminus_of_conj_small`, `boxi_conj_pow_apply`) kills every entry with `t_i > t_j`: thus
`g ∈ P_t = Uminus t · C(φ)` — the "parabolic" pinning.  Pisa's 7.53 upgrades this to `g ∈ Uminus t`
using its *shrinking* transverse resolution `e^{-αn}` at the return times `n`: the conjugates
`a^n g a^{-n}` then lie in `B_r^{G^-}B_{e^{-αn}/2}^{G⁰}`, whence the `C(φ)`-part of `g` (which is
the limit of the conjugates along the orbit, the `Uminus t`-part contracting to `1`) is `0`.  For a
*finite* `P` the transverse resolution of a piece is a fixed positive number, so this stops at
`h ∈ B_{Cρ}` for the `C(φ)`-part `h`, and the central part must be killed by §4 instead.  In
particular the elementary reduction "if `a^n g a^{-n} ∈ Uminus t` for all large `n` then
`g ∈ Uminus t`" is *available* (take limits; `Uminus t` is closed and
`Uminus t ∩ C(φ) = {1}`), but its hypothesis is exactly what a finite partition fails to supply.

### 6. What is not the issue

Boundedness (iii) and the `Z`-measurability are handled by the existing reductions; the entropy
hypothesis only pins the *number* of parts (`log #P ≥ h_μ(φ)`, and `h_μ(φ) ≤ J < ∞` by Pisa 7.9,
so `ent = ⊤` is not a refutation route); and the target is not refuted.  The residual is one finite
partition with (i) and (ii).
-/

open MeasureTheory Filter
open scoped ENNReal

noncomputable section

set_option linter.unusedVariables false

namespace Work.EKLC6Core

open Work.EKLContract

/-- `pastSigFinPart t P` is countably generated: it is generated by the preimages of the (finitely
many) parts of `P` under the iterates of `φ`. -/
theorem pastSigFinPart_countably_generated (t : Fin 3 → ℝ) (P : FinPart X3) :
    ∃ b : Set (Set X3), b.Countable ∧ pastSigFinPart t P = MeasurableSpace.generateFrom b := by
  refine ⟨Set.range (fun p : ℕ × Fin P.n =>
    ((fun x : X3 => aDiag t • x)^[p.1]) ⁻¹' (P.parts p.2)), Set.countable_range _, ?_⟩
  rw [pastSigFinPart]
  refine le_antisymm (iSup_le fun n => ?_) (MeasurableSpace.generateFrom_le ?_)
  · rw [Work.EKLContract.partSigma, MeasurableSpace.comap_generateFrom]
    refine MeasurableSpace.generateFrom_mono ?_
    rintro s ⟨t, ⟨i, rfl⟩, rfl⟩
    exact ⟨(n, i), rfl⟩
  · rintro s ⟨p, rfl⟩
    exact le_iSup (fun n : ℕ => MeasurableSpace.comap ((fun x : X3 => aDiag t • x)^[n])
      (partSigma P)) p.1 _
      (MeasurableSpace.measurableSet_comap.mpr
        ⟨P.parts p.2, MeasurableSpace.measurableSet_generateFrom ⟨p.2, rfl⟩, rfl⟩)

/-- **The reduction.**  If `P` is a finite partition whose past σ-algebra satisfies the three
pointwise plaque conditions almost everywhere, then `P` and a conull `Z` satisfy the target.

The three conditions are: (i) every atom of `A = pastSigFinPart t P` is contained in the `U`-orbit
of its point; (ii) the shape of the atom is the trace of an open set; (iii) the shape is entrywise
bounded.  The passage from "a.e." to "at every point of a conull `A`-measurable `Z`" is
`Work.EKLC6Core.plaqueAlgebra_of_ae_pointwise`. -/
theorem finPart_plaquePast_exists_of_ae {μ : MeasureTheory.Measure X3}
    [MeasureTheory.IsProbabilityMeasure μ] (t : Fin 3 → ℝ) (P : FinPart X3)
    (horbit : ∀ᵐ x ∂μ, atom (pastSigFinPart t P) x ⊆
      (fun u : SL3 => u • x) '' (Uminus t : Set SL3))
    (hopen : ∀ᵐ x ∂μ, ∃ O : Set SL3, IsOpen O ∧
      shape (pastSigFinPart t P) (Uminus t) x = O ∩ (Uminus t : Set SL3))
    (hbdd : ∀ᵐ x ∂μ, ∃ C : ℝ, ∀ u ∈ shape (pastSigFinPart t P) (Uminus t) x,
      ∀ i j : Fin 3, |u i j| ≤ C) :
    ∃ Z : Set X3, μ Zᶜ = 0 ∧
      IsPlaqueAlgebra (Uminus t) Z (pastSigFinPart t P) :=
  plaqueAlgebra_of_ae_pointwise (pastSigFinPart_le t P)
    (pastSigFinPart_countably_generated t P) horbit hopen hbdd

/-- **The ergodicity transfer, specialised.**  If `IsPlaqueAlgebra U Y A` holds on a set `Y` of
*positive* measure for a `φ`-descending σ-algebra `A`, then a.e. the atom of `A` is inside the
`U`-orbit of its point and the shape contains a neighbourhood of `1`. -/
theorem ae_orbit_of_positive_measure_plaque {μ : MeasureTheory.Measure X3}
    [MeasureTheory.IsProbabilityMeasure μ] (t : Fin 3 → ℝ)
    (hmp : MeasurePreserving (fun x : X3 => aDiag t • x) μ μ)
    (hqerg : ∀ E : Set X3, MeasurableSet E →
      (fun x : X3 => aDiag t • x) ⁻¹' E =ᵐ[μ] E → μ E = 0 ∨ μ Eᶜ = 0)
    (hU : IsHoro (Uminus t)) {A : MeasurableSpace X3} {Y : Set X3}
    (hplq : IsPlaqueAlgebra (Uminus t) Y A)
    (hdesc : MeasurableSpace.comap (fun x : X3 => aDiag t • x) A ≤ A) (hY : 0 < μ Y) :
    (∀ᵐ x ∂μ, atom A x ⊆ (fun u : SL3 => u • x) '' (Uminus t : Set SL3)) ∧
      (∀ᵐ x ∂μ, ∃ O : Set SL3, IsOpen O ∧ (1 : SL3) ∈ O ∧
        O ∩ (Uminus t : Set SL3) ⊆ shape A (Uminus t) x) :=
  ae_transfer_descending_plaque hU t hmp hqerg hplq hdesc hY



/-! ## The conjugation squeeze (stabiliser-free core)

If the conjugates `aDiag t^n * g * (aDiag t^n)⁻¹` of a group element `g` are `V (ε k)`-small along
a sequence of times with `ε k → 0`, then `g ∈ Uminus t`.  This is the *satisfiable* core of the
mechanism: it involves no pointwise "room set" (which would be empty at every point because of the
infinite discrete stabiliser `g Γ₃ g⁻¹`). -/
theorem mem_uminus_of_conj_small {t : Fin 3 → ℝ} {g : SL3} {nseq : ℕ → ℕ} {ε : ℕ → ℝ}
    (hε : Filter.Tendsto ε Filter.atTop (nhds 0))
    (hsmall : ∀ k : ℕ, (aDiag t ^ (nseq k) * g * (aDiag t ^ (nseq k))⁻¹) ∈ V (ε k)) :
    g ∈ Uminus t := by
  have hentry : ∀ k (i j : Fin 3),
      |(aDiag t ^ (nseq k) * g * (aDiag t ^ (nseq k))⁻¹ : SL3) i j
        - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| < ε k := fun k i j => hsmall k i j
  have hdiag : ∀ i : Fin 3, (g : Matrix (Fin 3) (Fin 3) ℝ) i i = 1 := by
    intro i
    have hb : ∀ k : ℕ, |(g : Matrix (Fin 3) (Fin 3) ℝ) i i
        - (1 : Matrix (Fin 3) (Fin 3) ℝ) i i| ≤ ε k := by
      intro k
      have h := hentry k i i
      rw [Work.EKLC6Core.boxi_conj_pow_apply t (nseq k) g i i, sub_self, mul_zero,
        Real.exp_zero, one_mul] at h
      exact le_of_lt h
    have hlim : Filter.Tendsto (fun k : ℕ => |(g : Matrix (Fin 3) (Fin 3) ℝ) i i
        - (1 : Matrix (Fin 3) (Fin 3) ℝ) i i|) Filter.atTop (nhds 0) :=
      squeeze_zero (fun k => abs_nonneg _) hb hε
    have hz : |(g : Matrix (Fin 3) (Fin 3) ℝ) i i
        - (1 : Matrix (Fin 3) (Fin 3) ℝ) i i| = 0 :=
      (tendsto_nhds_unique hlim tendsto_const_nhds).symm
    have hz' : (g : Matrix (Fin 3) (Fin 3) ℝ) i i
        - (1 : Matrix (Fin 3) (Fin 3) ℝ) i i = 0 := abs_eq_zero.mp hz
    have hone : (1 : Matrix (Fin 3) (Fin 3) ℝ) i i = 1 := Matrix.one_apply_eq i
    linarith
  have hzero : ∀ i j : Fin 3, i ≠ j → t j ≤ t i →
      (g : Matrix (Fin 3) (Fin 3) ℝ) i j = 0 := by
    intro i j hij hle
    have hone : (1 : Matrix (Fin 3) (Fin 3) ℝ) i j = 0 := Matrix.one_apply_ne hij
    rcases lt_or_eq_of_le hle with hlt | heq
    · by_contra hg0
      have hgpos : 0 < |(g : Matrix (Fin 3) (Fin 3) ℝ) i j| := abs_pos.mpr hg0
      obtain ⟨k, hk⟩ : ∃ k : ℕ, ε k < |(g : Matrix (Fin 3) (Fin 3) ℝ) i j| := by
        have h : ∀ᶠ k in Filter.atTop, ε k < |(g : Matrix (Fin 3) (Fin 3) ℝ) i j| :=
          hε.eventually (isOpen_Iio.mem_nhds (by simpa using hgpos))
        exact h.exists
      have hk' := hentry k i j
      rw [Work.EKLC6Core.boxi_conj_pow_apply t (nseq k) g i j, hone, sub_zero] at hk'
      have hexp1 : (1 : ℝ) ≤ Real.exp ((nseq k : ℝ) * (t i - t j)) :=
        Real.one_le_exp (by positivity)
      have hkey : |(g : Matrix (Fin 3) (Fin 3) ℝ) i j|
          ≤ |Real.exp ((nseq k : ℝ) * (t i - t j)) * (g : Matrix (Fin 3) (Fin 3) ℝ) i j| := by
        rw [abs_mul, abs_of_pos (Real.exp_pos _)]
        exact le_mul_of_one_le_left (abs_nonneg _) hexp1
      linarith
    · have hb : ∀ k : ℕ, |(g : Matrix (Fin 3) (Fin 3) ℝ) i j
          - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ ε k := by
        intro k
        have h := hentry k i j
        rw [Work.EKLC6Core.boxi_conj_pow_apply t (nseq k) g i j,
          show t i - t j = 0 from by linarith, mul_zero, Real.exp_zero, one_mul] at h
        exact le_of_lt h
      have hlim : Filter.Tendsto (fun k : ℕ => |(g : Matrix (Fin 3) (Fin 3) ℝ) i j
          - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j|) Filter.atTop (nhds 0) :=
        squeeze_zero (fun k => abs_nonneg _) hb hε
      have hz : |(g : Matrix (Fin 3) (Fin 3) ℝ) i j
          - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| = 0 :=
        (tendsto_nhds_unique hlim tendsto_const_nhds).symm
      have hz' : (g : Matrix (Fin 3) (Fin 3) ℝ) i j
          - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j = 0 := abs_eq_zero.mp hz
      rw [hone, sub_zero] at hz'
      exact hz'
  exact mem_uminus_of_entry_form hdiag hzero


/-! ## The dynamical half in stabiliser-safe form

The naive "room set" hypothesis (quantifying over *all* `g` with `g • y ∈ [y]_P`) is unsatisfiable:
the stabiliser `g Γ₃ g⁻¹` of every point is an infinite discrete group, so the room set always
contains elements outside `V ε`.  The corrected input below is *point-free* (it only mentions the
cell of the orbit point); the only remaining place where the stabiliser enters is isolated in the
*pinning* statement `hpin` (delegated as `Work.EKLC6Core.stabiliser_pin_of_varying_family`). -/

/-- **From the thin-cell condition to a family of small representatives.**

If at the good times `n k` any two points of the `partSigma P`-atom of `φ^{n k} x` are related by a
`V (ε k)`-element, then every atom mate `y` of `x` admits a family `u k` of representatives of the
relation `u k • x = y` whose `n k`-th conjugates are `V (ε k)`-small. -/
theorem exists_small_rep_of_thin_cells {t : Fin 3 → ℝ} {P : FinPart X3} {x y : X3}
    {nseq : ℕ → ℕ} {ε : ℕ → ℝ}
    (hy : y ∈ atom (pastSigFinPart t P) x)
    (hthin : ∀ k : ℕ, ∀ y' z' : X3,
      y' ∈ atom (partSigma P) (((fun x : X3 => aDiag t • x)^[nseq k]) x) →
      z' ∈ atom (partSigma P) (((fun x : X3 => aDiag t • x)^[nseq k]) x) →
      ∃ w : SL3, w • y' = z' ∧ w ∈ V (ε k)) :
    ∃ u : ℕ → SL3, (∀ k, u k • x = y) ∧
      ∀ k, (aDiag t ^ (nseq k) * u k * (aDiag t ^ (nseq k))⁻¹) ∈ V (ε k) := by
  have hy' : ∀ n : ℕ, ((fun z : X3 => aDiag t • z)^[n]) y ∈
      atom (partSigma P) (((fun z : X3 => aDiag t • z)^[n]) x) := by
    intro n
    have h := hy
    rw [pastSigFinPart,
      atom_iSup_comap_iterate_eq (partSigma P) (fun z : X3 => aDiag t • z) x] at h
    exact h n
  have hself : ∀ k : ℕ, ((fun z : X3 => aDiag t • z)^[nseq k]) x ∈
      atom (partSigma P) (((fun z : X3 => aDiag t • z)^[nseq k]) x) := by
    intro k
    exact Set.mem_sInter.mpr fun s hs => hs.2
  choose w hw hwV using fun k => hthin k _ _ (hself k) (hy' (nseq k))
  refine ⟨fun k => (aDiag t ^ (nseq k))⁻¹ * w k * aDiag t ^ (nseq k), ?_, ?_⟩
  · intro k
    have hstep : ((aDiag t ^ (nseq k))⁻¹ * w k * aDiag t ^ (nseq k)) • x
        = (aDiag t ^ (nseq k))⁻¹ • (w k • (aDiag t ^ (nseq k) • x)) := by
      rw [mul_smul, mul_smul]
    rw [hstep, ← gen_iterate_aDiag_smul t (nseq k) x, hw k]
    rw [gen_iterate_aDiag_smul t (nseq k) y, ← mul_smul,
      show (aDiag t ^ (nseq k))⁻¹ * aDiag t ^ (nseq k) = 1 from by group, one_smul]
  · intro k
    have hconj : aDiag t ^ (nseq k) * ((aDiag t ^ (nseq k))⁻¹ * w k * aDiag t ^ (nseq k))
        * (aDiag t ^ (nseq k))⁻¹ = w k := by group
    rw [hconj]
    exact hwV k

/-- **The dynamical half of the target, in the corrected (satisfiable) form.**

* `hthin` — the *thin-cell* condition: along the orbit of a.e. `x` there are times `n k` with
  `ε k → 0` at which any two points of the `partSigma P`-atom of `φ^{n k} x` are related by a
  `V (ε k)`-element (point-free, satisfiable: e.g. cells of small diameter modulo the lattice);
* `hpin` — the *pinning* statement: a family of representatives `u k` of a relation `u k • x = y`
  with `V (ε k)`-small `n k`-th conjugates can be replaced by a single element of `Uminus t`.

Conclusion: the atoms of `pastSigFinPart t P` are contained in the `Uminus t`-orbits. -/
theorem atom_pastSigFinPart_subset_uminus_of_thin_cells {μ : MeasureTheory.Measure X3}
    [MeasureTheory.IsProbabilityMeasure μ] (t : Fin 3 → ℝ) (P : FinPart X3)
    (hthin : ∀ᵐ x ∂μ, ∃ (nseq : ℕ → ℕ) (ε : ℕ → ℝ),
      Filter.Tendsto ε Filter.atTop (nhds 0) ∧
      ∀ k : ℕ, ∀ y' z' : X3,
        y' ∈ atom (partSigma P) (((fun x : X3 => aDiag t • x)^[nseq k]) x) →
        z' ∈ atom (partSigma P) (((fun x : X3 => aDiag t • x)^[nseq k]) x) →
        ∃ w : SL3, w • y' = z' ∧ w ∈ V (ε k))
    (hpin : ∀ᵐ x ∂μ, ∀ y : X3, ∀ (nseq : ℕ → ℕ) (ε : ℕ → ℝ),
      Filter.Tendsto ε Filter.atTop (nhds 0) →
      (∃ u : ℕ → SL3, (∀ k, u k • x = y) ∧
        ∀ k, (aDiag t ^ (nseq k) * u k * (aDiag t ^ (nseq k))⁻¹) ∈ V (ε k)) →
      ∃ v : SL3, v • x = y ∧ v ∈ Uminus t) :
    ∀ᵐ x ∂μ, atom (pastSigFinPart t P) x ⊆
      (fun u : SL3 => u • x) '' (Uminus t : Set SL3) := by
  filter_upwards [hthin, hpin] with x hthinx hpinx
  intro y hy
  obtain ⟨nseq, ε, hε, hthin'⟩ := hthinx
  obtain ⟨u, hux, hsmall⟩ := exists_small_rep_of_thin_cells (t := t) (P := P) hy hthin'
  obtain ⟨v, hvx, hvU⟩ := hpinx y nseq ε hε ⟨u, hux, hsmall⟩
  exact ⟨v, hvU, hvx⟩

/-! ## The countable analogue: a refining sequence of partitions

A *finite* partition has finitely many parts of fixed size, so (as `ae_no_thin_scaling_of_finPart`
records) the point-free thinness condition of `exists_small_rep_of_thin_cells` cannot hold with
`ε k → 0`.  The countable analogue below takes one partition per scale (a refining sequence
`P k`), so that thinness at level `k` is available with `ε k → 0`; the atoms are then those of the
*join* σ-algebra `⨆ k, pastSigFinPart t (P k)`.  This is the shape in which the source (Pisa 7.43)
obtains its partition, and the two lemmas below are the verbatim analogues of
`exists_small_rep_of_thin_cells` and `atom_pastSigFinPart_subset_uminus_of_thin_cells`. -/

/-- **The countable analogue of `exists_small_rep_of_thin_cells`.**  Given a refining sequence of
partitions, one level per scale, and the level-`k` thinness of the orbit point's cell, every atom
mate of `x` (in the join) admits a family of representatives with `V (ε k)`-small `n k`-th
conjugates — now with `ε k → 0` genuinely available. -/
theorem exists_small_rep_of_refining_seq {t : Fin 3 → ℝ} {P : ℕ → FinPart X3} {x y : X3}
    {nseq : ℕ → ℕ} {ε : ℕ → ℝ}
    (hy : ∀ k : ℕ, ((fun z : X3 => aDiag t • z)^[nseq k]) y ∈
      atom (partSigma (P k)) (((fun z : X3 => aDiag t • z)^[nseq k]) x))
    (hthin : ∀ k : ℕ, ∀ y' z' : X3,
      y' ∈ atom (partSigma (P k)) (((fun x : X3 => aDiag t • x)^[nseq k]) x) →
      z' ∈ atom (partSigma (P k)) (((fun x : X3 => aDiag t • x)^[nseq k]) x) →
      ∃ w : SL3, w • y' = z' ∧ w ∈ V (ε k)) :
    ∃ u : ℕ → SL3, (∀ k, u k • x = y) ∧
      ∀ k, (aDiag t ^ (nseq k) * u k * (aDiag t ^ (nseq k))⁻¹) ∈ V (ε k) := by
  have hself : ∀ k : ℕ, ((fun z : X3 => aDiag t • z)^[nseq k]) x ∈
      atom (partSigma (P k)) (((fun z : X3 => aDiag t • z)^[nseq k]) x) := by
    intro k
    exact Set.mem_sInter.mpr fun s hs => hs.2
  choose w hw hwV using fun k => hthin k _ _ (hself k) (hy k)
  refine ⟨fun k => (aDiag t ^ (nseq k))⁻¹ * w k * aDiag t ^ (nseq k), ?_, ?_⟩
  · intro k
    have hstep : ((aDiag t ^ (nseq k))⁻¹ * w k * aDiag t ^ (nseq k)) • x
        = (aDiag t ^ (nseq k))⁻¹ • (w k • (aDiag t ^ (nseq k) • x)) := by
      rw [mul_smul, mul_smul]
    rw [hstep, ← gen_iterate_aDiag_smul t (nseq k) x, hw k]
    rw [gen_iterate_aDiag_smul t (nseq k) y, ← mul_smul,
      show (aDiag t ^ (nseq k))⁻¹ * aDiag t ^ (nseq k) = 1 from by group, one_smul]
  · intro k
    have hconj : aDiag t ^ (nseq k) * ((aDiag t ^ (nseq k))⁻¹ * w k * aDiag t ^ (nseq k))
        * (aDiag t ^ (nseq k))⁻¹ = w k := by group
    rw [hconj]
    exact hwV k

/-- **The countable containment (the analogue of the dynamical half).**  With a refining sequence
of partitions `P k`, thin cells at the level-`k` scale with `ε k → 0`, and the pinning statement,
the atoms of the join σ-algebra `⨆ k, pastSigFinPart t (P k)` are contained in the `Uminus t`-orbits. -/
theorem atom_iSup_pastSigFinPart_subset_uminus_of_thin_levels {μ : MeasureTheory.Measure X3}
    [MeasureTheory.IsProbabilityMeasure μ] (t : Fin 3 → ℝ) (P : ℕ → FinPart X3)
    (hthin : ∀ᵐ x ∂μ, ∃ (nseq : ℕ → ℕ) (ε : ℕ → ℝ),
      Filter.Tendsto ε Filter.atTop (nhds 0) ∧
      ∀ k : ℕ, ∀ y' z' : X3,
        y' ∈ atom (partSigma (P k)) (((fun x : X3 => aDiag t • x)^[nseq k]) x) →
        z' ∈ atom (partSigma (P k)) (((fun x : X3 => aDiag t • x)^[nseq k]) x) →
        ∃ w : SL3, w • y' = z' ∧ w ∈ V (ε k))
    (hpin : ∀ᵐ x ∂μ, ∀ y : X3, ∀ (nseq : ℕ → ℕ) (ε : ℕ → ℝ),
      Filter.Tendsto ε Filter.atTop (nhds 0) →
      (∃ u : ℕ → SL3, (∀ k, u k • x = y) ∧
        ∀ k, (aDiag t ^ (nseq k) * u k * (aDiag t ^ (nseq k))⁻¹) ∈ V (ε k)) →
      ∃ v : SL3, v • x = y ∧ v ∈ Uminus t) :
    ∀ᵐ x ∂μ, atom (⨆ k, pastSigFinPart t (P k)) x ⊆
      (fun u : SL3 => u • x) '' (Uminus t : Set SL3) := by
  filter_upwards [hthin, hpin] with x hthinx hpinx
  intro y hy
  obtain ⟨nseq, ε, hε, hthin'⟩ := hthinx
  have hlevel : ∀ k : ℕ, ((fun z : X3 => aDiag t • z)^[nseq k]) y ∈
      atom (partSigma (P k)) (((fun z : X3 => aDiag t • z)^[nseq k]) x) := by
    intro k
    have h1 : y ∈ atom (pastSigFinPart t (P k)) x := by
      have h := hy
      rw [Work.EKLC6Core.atom_iSup_eq (fun k => pastSigFinPart t (P k)) x] at h
      exact h k
    have h2 := h1
    rw [pastSigFinPart,
      atom_iSup_comap_iterate_eq (partSigma (P k)) (fun z : X3 => aDiag t • z) x] at h2
    exact h2 (nseq k)
  obtain ⟨u, hux, hsmall⟩ := exists_small_rep_of_refining_seq (t := t) hlevel hthin'
  obtain ⟨v, hvx, hvU⟩ := hpinx y nseq ε hε ⟨u, hux, hsmall⟩
  exact ⟨v, hvU, hvx⟩

/-- **The countable containment, routed through the finite pinning form.**  This is the same
statement as `atom_iSup_pastSigFinPart_subset_uminus_of_thin_levels`, but the pinning hypothesis is
specialised to the form in which the geometry can supply it — families taking *finitely many*
values — and which is therefore covered by the proved lemma
`Work.EKLC6Core.pin_of_finitely_many_reps` (a corollary of `mem_uminus_of_conj_small`). -/
theorem atom_iSup_pastSigFinPart_subset_uminus_of_fin_valued_families
    {μ : MeasureTheory.Measure X3} [MeasureTheory.IsProbabilityMeasure μ]
    (t : Fin 3 → ℝ) (P : ℕ → FinPart X3)
    (hinput : ∀ᵐ x ∂μ, ∃ (nseq : ℕ → ℕ) (ε : ℕ → ℝ),
      Filter.Tendsto ε Filter.atTop (nhds 0) ∧
      ∀ y : X3, y ∈ atom (⨆ k, pastSigFinPart t (P k)) x →
        ∃ u : ℕ → SL3, (∀ k, u k • x = y) ∧
          (∀ k, (aDiag t ^ (nseq k) * u k * (aDiag t ^ (nseq k))⁻¹) ∈ V (ε k)) ∧
          (Set.range u).Finite)
    (hpinfin : ∀ (x y : X3) (nseq : ℕ → ℕ) (ε : ℕ → ℝ), Filter.Tendsto ε Filter.atTop (nhds 0) →
      (∃ u : ℕ → SL3, (∀ k, u k • x = y) ∧
        (∀ k, (aDiag t ^ (nseq k) * u k * (aDiag t ^ (nseq k))⁻¹) ∈ V (ε k)) ∧
        (Set.range u).Finite) →
      ∃ v : SL3, v • x = y ∧ v ∈ Uminus t) :
    ∀ᵐ x ∂μ, atom (⨆ k, pastSigFinPart t (P k)) x ⊆
      (fun u : SL3 => u • x) '' (Uminus t : Set SL3) := by
  filter_upwards [hinput] with x hx
  obtain ⟨nseq, ε, hε, hfam⟩ := hx
  intro y hy
  obtain ⟨u, hux, hsmall, hfin⟩ := hfam y hy
  obtain ⟨v, hvx, hvU⟩ := hpinfin x y nseq ε hε ⟨u, hux, hsmall, hfin⟩
  exact ⟨v, hvU, hvx⟩

/-! ## From the positivity of the "thin room" sets to visits along the orbit

The geometric input for the target is the existence of a finite partition `P` whose "part-membership
sets" `{g | g • y ∈ [y]_{partSigma P}}` are, for every `k`, `V ((k+1)⁻¹)`-small on a set of
*positive measure* (a "thin room" region).  Ergodicity converts this into the visit property
required by `atom_pastSigFinPart_subset_uminus_of_room`. -/

/-- **Positivity of the thin room sets gives visits along the orbit.** -/
theorem ae_room_visits_of_pos_sets {μ : MeasureTheory.Measure X3}
    [MeasureTheory.IsProbabilityMeasure μ] (t : Fin 3 → ℝ) (P : FinPart X3)
    (hmp : MeasureTheory.MeasurePreserving (fun x : X3 => aDiag t • x) μ μ)
    (hqerg : ∀ E : Set X3, MeasurableSet E →
      (fun x : X3 => aDiag t • x) ⁻¹' E =ᵐ[μ] E → μ E = 0 ∨ μ Eᶜ = 0)
    (hroom : ∀ k : ℕ, ∃ T : Set X3, MeasurableSet T ∧ 0 < μ T ∧
      ∀ y ∈ T, ∀ g : SL3, g • y ∈ atom (partSigma P) y → g ∈ V ((k : ℝ) + 1)⁻¹) :
    ∀ᵐ x ∂μ, ∃ (nseq : ℕ → ℕ), ∀ k : ℕ, ∀ g : SL3,
      g • (((fun x : X3 => aDiag t • x)^[nseq k]) x) ∈
        atom (partSigma P) (((fun x : X3 => aDiag t • x)^[nseq k]) x) →
      g ∈ V ((k : ℝ) + 1)⁻¹ := by
  choose T hTmeas hTpos hTroom using hroom
  have hvisit : ∀ᵐ x ∂μ, ∀ k : ℕ,
      ∃ᶠ n in Filter.atTop, ((fun x : X3 => aDiag t • x)^[n]) x ∈ T k :=
    MeasureTheory.ae_all_iff.mpr fun k =>
      good_time_freq μ _ hmp hqerg (hTmeas k) (hTpos k)
  filter_upwards [hvisit] with x hx
  choose nseq hnseq using fun k => (hx k).exists
  exact ⟨nseq, fun k g hg => hTroom k _ (hnseq k) g hg⟩

/-! ## The centraliser criterion for the past atom

The lemmas below record *exactly* when the atom of `pastSigFinPart t P` contains the displacement
of a point by an element `c` commuting with `aDiag t` (a diagonal matrix, or an element of the
block-diagonal centraliser when `t` has repeated coordinates).  They are the precise form of the
obstruction discussed in the header of this file:

* if `c` *moves* a positive-measure set across the parts of `P` (`c • y ∉ [y]_P`), then `c • x` is
  almost never in the atom of `x`;
* conversely, if every part of `P` is (a.e.) invariant under `c`, then `c • x` lies in the atom of
  `x` for a.e. `x`.

Consequently a *finite* partition `P` can serve the target only if its parts are moved by every
non-trivial element of the centraliser of `aDiag t` (expressed through the levels of `P`); this is
the finiteness obstruction left open by Pisa 7.53. -/

/-- The set of points `y` whose part of `P` is not preserved by `c • ·`. -/
def movedSet (P : FinPart X3) (c : SL3) : Set X3 :=
  ⋃ i : Fin P.n, (P.parts i ∩ (fun y : X3 => c • y) ⁻¹' (P.parts i)ᶜ)

theorem measurableSet_movedSet (P : FinPart X3) (c : SL3) : MeasurableSet (movedSet P c) := by
  refine MeasurableSet.iUnion fun i => ?_
  exact (P.measurable i).inter ((continuous_const_smul c).measurable (P.measurable i).compl)

/-- The atom of the σ-algebra of a *finite* partition, described by the codes of the parts. -/
theorem mem_atom_partSigma_iff (P : FinPart X3) {y z : X3} :
    z ∈ atom (partSigma P) y ↔ ∀ i : Fin P.n, (z ∈ P.parts i ↔ y ∈ P.parts i) := by
  rw [Work.EKLContract.partSigma, mem_atom_generateFrom_iff]
  constructor
  · intro h i
    exact h _ ⟨i, rfl⟩
  · intro h s hs
    obtain ⟨i, rfl⟩ := hs
    exact h i

/-- The part of `P` containing `y` is contained in the atom of `y`. -/
theorem parts_subset_atom (P : FinPart X3) {y : X3} {i : Fin P.n} (hy : y ∈ P.parts i) :
    P.parts i ⊆ atom (partSigma P) y := by
  intro z hz
  rw [mem_atom_partSigma_iff]
  intro j
  constructor
  · intro hzj
    have hji : j = i := by
      by_contra hne
      exact (Set.disjoint_left.mp (P.disjoint (fun h : i = j => hne h.symm)) hz) hzj
    rw [hji]; exact hy
  · intro hyj
    have hji : j = i := by
      by_contra hne
      exact (Set.disjoint_left.mp (P.disjoint (fun h : i = j => hne h.symm)) hy) hyj
    rw [hji]; exact hz

/-- `y` is in `movedSet P c` exactly when the atom of the *finite* partition at `y` does not
contain `c • y`. -/
theorem mem_movedSet_iff (P : FinPart X3) (c : SL3) (y : X3) :
    y ∈ movedSet P c ↔ c • y ∉ atom (partSigma P) y := by
  have hgen : ∀ i : Fin P.n, MeasurableSet[partSigma P] (P.parts i) := fun i =>
    MeasurableSpace.measurableSet_generateFrom (Set.mem_range_self i)
  constructor
  · intro h hc
    simp only [movedSet, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage,
      Set.mem_compl_iff] at h
    obtain ⟨i, hyi, hci⟩ := h
    exact hci (atom_subset_of_mem (m := partSigma P) (hgen i) hyi hc)
  · intro h
    obtain ⟨i, hyi⟩ : ∃ i : Fin P.n, y ∈ P.parts i := by
      have hmem : y ∈ ⋃ i, P.parts i := by rw [P.cover]; exact Set.mem_univ y
      exact Set.mem_iUnion.mp hmem
    simp only [movedSet, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage, Set.mem_compl_iff]
    exact ⟨i, hyi, fun hci => h (parts_subset_atom P hyi hci)⟩

/-- **The atom of the past σ-algebra is the class of equal `P`-itineraries.** -/
theorem mem_atom_pastSigFinPart_iff (t : Fin 3 → ℝ) (P : FinPart X3) (x y : X3) :
    y ∈ atom (pastSigFinPart t P) x ↔
      ∀ (n : ℕ) (i : Fin P.n), ((fun z : X3 => aDiag t • z)^[n]) y ∈ P.parts i ↔
        ((fun z : X3 => aDiag t • z)^[n]) x ∈ P.parts i := by
  have hgen : pastSigFinPart t P = MeasurableSpace.generateFrom
      (Set.range (fun p : ℕ × Fin P.n =>
        ((fun z : X3 => aDiag t • z)^[p.1]) ⁻¹' (P.parts p.2))) := by
    rw [pastSigFinPart]
    refine le_antisymm (iSup_le fun n => ?_) (MeasurableSpace.generateFrom_le ?_)
    · rw [Work.EKLContract.partSigma, MeasurableSpace.comap_generateFrom]
      refine MeasurableSpace.generateFrom_mono ?_
      rintro s ⟨u, ⟨i, rfl⟩, rfl⟩
      exact ⟨(n, i), rfl⟩
    · rintro s ⟨p, rfl⟩
      exact le_iSup (fun n : ℕ => MeasurableSpace.comap ((fun x : X3 => aDiag t • x)^[n])
        (partSigma P)) p.1 _
        (MeasurableSpace.measurableSet_comap.mpr
          ⟨P.parts p.2, MeasurableSpace.measurableSet_generateFrom ⟨p.2, rfl⟩, rfl⟩)
  rw [hgen, mem_atom_generateFrom_iff]
  constructor
  · intro h n i
    exact h _ ⟨(n, i), rfl⟩
  · intro h s hs
    obtain ⟨⟨n, i⟩, rfl⟩ := hs
    exact h n i

/-- **Central displacements are excluded by a part that `c` moves.**  If `c` commutes with
`aDiag t` and the set of points whose part is not preserved by `c` has positive measure, then for
a.e. `x` the point `c • x` is not in the `pastSigFinPart t P`-atom of `x`. -/
theorem ae_not_mem_atom_of_part_moved {μ : MeasureTheory.Measure X3}
    [MeasureTheory.IsProbabilityMeasure μ] {t : Fin 3 → ℝ} {P : FinPart X3} {c : SL3}
    (hmp : MeasureTheory.MeasurePreserving (fun x : X3 => aDiag t • x) μ μ)
    (hqerg : ∀ E : Set X3, MeasurableSet E →
      (fun x : X3 => aDiag t • x) ⁻¹' E =ᵐ[μ] E → μ E = 0 ∨ μ Eᶜ = 0)
    (hc : aDiag t * c = c * aDiag t)
    (hpos : 0 < μ (movedSet P c)) :
    ∀ᵐ x ∂μ, c • x ∉ atom (pastSigFinPart t P) x := by
  classical
  set T : X3 → X3 := fun x => aDiag t • x with hT
  have hTmeas : Measurable T := by
    rw [hT]; exact (continuous_const_smul (aDiag t)).measurable
  have hcx : ∀ x : X3, T (c • x) = c • (T x) := by
    intro x
    simp only [hT]
    rw [← mul_smul, hc, mul_smul]
  have hiter : ∀ (n : ℕ) (x : X3), (T^[n]) (c • x) = c • ((T^[n]) x) := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      calc (T^[k+1]) (c • x) = T ((T^[k]) (c • x)) := Function.iterate_succ_apply' T k (c • x)
        _ = T (c • ((T^[k]) x)) := by simp only [ih]
        _ = c • (T ((T^[k]) x)) := hcx _
        _ = c • ((T^[k+1]) x) := by simp only [Function.iterate_succ_apply' T k x]
  have hSmeas : MeasurableSet (movedSet P c) := measurableSet_movedSet P c
  set A : Set X3 := {x : X3 | ∃ n : ℕ, (T^[n]) x ∈ movedSet P c} with hA
  have hAmeas : MeasurableSet A := by
    have h : A = ⋃ n : ℕ, (T^[n]) ⁻¹' (movedSet P c) := by
      rw [hA]
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_preimage]
    rw [h]
    exact MeasurableSet.iUnion fun n => hSmeas.preimage (hTmeas.iterate n)
  have hsub : movedSet P c ⊆ A := by
    intro y hy
    rw [hA]
    exact ⟨0, by simpa using hy⟩
  have hA_union : A ⊆ movedSet P c ∪ T ⁻¹' A := by
    intro x hx
    rw [hA] at hx
    obtain ⟨n, hn⟩ := hx
    cases n with
    | zero => exact Or.inl (by simpa using hn)
    | succ k =>
      refine Or.inr ?_
      rw [Set.mem_preimage, hA]
      exact ⟨k, by simpa [Function.iterate_succ_apply] using hn⟩
  have hsubTA : T ⁻¹' A ⊆ A := by
    intro x hx
    rw [Set.mem_preimage] at hx
    rw [hA] at hx ⊢
    obtain ⟨n, hn⟩ := hx
    exact ⟨n + 1, by simpa [Function.iterate_succ_apply] using hn⟩
  have hdiff : μ (A \ T ⁻¹' A) = 0 := by
    have h1 := MeasureTheory.measure_sdiff hsubTA
      (hAmeas.preimage hTmeas).nullMeasurableSet (MeasureTheory.measure_ne_top μ _)
    have h2 : μ (T ⁻¹' A) = μ A := hmp.measure_preimage hAmeas.nullMeasurableSet
    rw [h2, tsub_self] at h1
    exact h1
  have hinv : T ⁻¹' A =ᵐ[μ] A :=
    MeasureTheory.ae_eq_set.mpr
      ⟨by rw [Set.sdiff_eq_empty.mpr hsubTA, measure_empty], hdiff⟩
  have hAc : μ Aᶜ = 0 := by
    rcases hqerg A hAmeas hinv with h0 | h1
    · exfalso
      have hlt : 0 < μ A := lt_of_lt_of_le hpos (measure_mono hsub)
      rw [h0] at hlt
      exact absurd hlt (lt_irrefl 0)
    · exact h1
  rw [MeasureTheory.ae_iff]
  refine measure_mono_null ?_ hAc
  intro x hx
  have hxc : c • x ∈ atom (pastSigFinPart t P) x := by simpa using hx
  rw [Set.mem_compl_iff, hA]
  rintro ⟨n, hn⟩
  rw [mem_movedSet_iff] at hn
  rw [mem_atom_pastSigFinPart_iff] at hxc
  exact hn ((mem_atom_partSigma_iff P).mpr fun i => by
    have h3 := hxc n i
    rw [hiter n x] at h3
    exact h3)

/-- **Central displacements always survive when the parts are fixed.**  Conversely to
`ae_not_mem_atom_of_part_moved`: if the set of points whose part of `P` is moved by `c` is
`μ`-null, then `c • x` lies in the `pastSigFinPart t P`-atom of `x` for a.e. `x`. -/
theorem ae_mem_atom_of_part_fixed {μ : MeasureTheory.Measure X3}
    [MeasureTheory.IsProbabilityMeasure μ] {t : Fin 3 → ℝ} {P : FinPart X3} {c : SL3}
    (hmp : MeasureTheory.MeasurePreserving (fun x : X3 => aDiag t • x) μ μ)
    (hc : aDiag t * c = c * aDiag t)
    (hzero : μ (movedSet P c) = 0) :
    ∀ᵐ x ∂μ, c • x ∈ atom (pastSigFinPart t P) x := by
  classical
  set T : X3 → X3 := fun x => aDiag t • x with hT
  have hTmeas : Measurable T := by
    rw [hT]; exact (continuous_const_smul (aDiag t)).measurable
  have hcx : ∀ x : X3, T (c • x) = c • (T x) := by
    intro x
    simp only [hT]
    rw [← mul_smul, hc, mul_smul]
  have hiter : ∀ (n : ℕ) (x : X3), (T^[n]) (c • x) = c • ((T^[n]) x) := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      calc (T^[k+1]) (c • x) = T ((T^[k]) (c • x)) := Function.iterate_succ_apply' T k (c • x)
        _ = T (c • ((T^[k]) x)) := by simp only [ih]
        _ = c • (T ((T^[k]) x)) := hcx _
        _ = c • ((T^[k+1]) x) := by simp only [Function.iterate_succ_apply' T k x]
  have hSmeas : MeasurableSet (movedSet P c) := measurableSet_movedSet P c
  set A : Set X3 := {x : X3 | ∃ n : ℕ, (T^[n]) x ∈ movedSet P c} with hA
  have hnull : μ A = 0 := by
    have h : A = ⋃ n : ℕ, (T^[n]) ⁻¹' (movedSet P c) := by
      rw [hA]
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_preimage]
    rw [h]
    exact measure_iUnion_null fun n => by
      rw [(hmp.iterate n).measure_preimage hSmeas.nullMeasurableSet]
      exact hzero
  rw [MeasureTheory.ae_iff]
  refine measure_mono_null ?_ hnull
  intro x hx
  have hxc : c • x ∉ atom (pastSigFinPart t P) x := by simpa using hx
  rw [hA]
  by_contra hcon
  refine hxc ?_
  rw [mem_atom_pastSigFinPart_iff]
  intro n i
  have hmem : (T^[n]) x ∉ movedSet P c := fun hPn => hcon ⟨n, hPn⟩
  rw [mem_movedSet_iff] at hmem
  have h' : c • ((T^[n]) x) ∈ atom (partSigma P) ((T^[n]) x) := by simpa using hmem
  rw [hiter n x]
  exact (mem_atom_partSigma_iff P).mp h' i

/-! ## The concrete finite partition

`Work.EKLC6Core.thin_boundary_partition` produces finitely many measurable pieces `Q i` that are
pairwise disjoint and *cover* `X₃`, all but one of them inside a `V ρ`-ball around a point, one
piece of measure `< ε`, and — the crucial quantitative input — **globally thin frontiers**,

`μ (⋃ i, VThick η (frontier (Q i))) ≤ c η`   for all `η > 0`.

Passing to the interiors loses only the union of the frontiers, which is `μ`-null, so

`adaptedPart Q hdisj := {interior (Q i)} ∪ {(⋃ i, interior (Q i))ᶜ}`

is a genuine finite partition of `X₃` all of whose parts are open except for the `μ`-null
remainder.  This is the partition `P` of the target: the thin frontiers let the orbit stay "deep"
inside its parts (Borel–Cantelli: `∑ n c (μ₀)^n < ∞` for the margin radius `μ₀ < 1`), which is
what makes the level-`n` shapes open in `Uminus t` and *fat* along the orbit, while the small
diameter of the pieces (and the centraliser criterion `ae_not_mem_atom_of_part_moved`) is what
forces the past atom into the `Uminus t`-orbit. -/

/-- The finite partition with parts the interiors of a finite disjoint family `Q`, together with
the (necessarily small) remainder. -/
noncomputable def adaptedPart {N : ℕ} (Q : Fin N → Set X3)
    (hdisj : ∀ i j, i ≠ j → Disjoint (Q i) (Q j)) : FinPart X3 where
  n := N + 1
  parts := fun i => if h : (i : ℕ) < N then interior (Q ⟨i, h⟩) else (⋃ j, interior (Q j))ᶜ
  measurable := fun i => by
    split_ifs with h
    · exact isOpen_interior.measurableSet
    · exact (MeasurableSet.iUnion fun j => isOpen_interior.measurableSet).compl
  disjoint := fun i j hij => by
    dsimp only
    by_cases hi : (i : ℕ) < N
    · by_cases hj : (j : ℕ) < N
      · rw [dif_pos hi, dif_pos hj]
        refine ((hdisj ⟨i, hi⟩ ⟨j, hj⟩ ?_).mono interior_subset interior_subset)
        intro h
        exact hij (Fin.ext (by have := congrArg (fun k : Fin N => (k : ℕ)) h; simpa using this))
      · rw [dif_pos hi, dif_neg hj]
        refine Set.disjoint_left.mpr fun z hz1 hz2 => hz2 ?_
        exact Set.subset_iUnion (fun j => interior (Q j)) ⟨i, hi⟩ hz1
    · by_cases hj : (j : ℕ) < N
      · rw [dif_neg hi, dif_pos hj]
        refine Set.disjoint_left.mpr fun z hz1 hz2 => hz1 ?_
        exact Set.subset_iUnion (fun j => interior (Q j)) ⟨j, hj⟩ hz2
      · exfalso
        have hi' : (i : ℕ) = N := by
          have := i.isLt; omega
        have hj' : (j : ℕ) = N := by
          have := j.isLt; omega
        exact hij (Fin.ext (by omega))
  cover := by
    ext x
    constructor
    · intro _; exact trivial
    · intro _
      by_cases hx : x ∈ ⋃ j, interior (Q j)
      · obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
        refine Set.mem_iUnion.mpr ⟨⟨j, by omega⟩, ?_⟩
        dsimp only
        rw [dif_pos j.isLt]
        exact hj
      · refine Set.mem_iUnion.mpr ⟨⟨N, Nat.lt_succ_self N⟩, ?_⟩
        dsimp only
        rw [dif_neg (by simp)]
        exact hx

/-- The parts of `adaptedPart` indexed below `N`. -/
theorem adaptedPart_parts_of_lt {N : ℕ} (Q : Fin N → Set X3)
    (hdisj : ∀ i j, i ≠ j → Disjoint (Q i) (Q j)) {i : Fin (N + 1)} (hi : (i : ℕ) < N) :
    (adaptedPart Q hdisj).parts i = interior (Q ⟨i, hi⟩) := dif_pos hi

/-- The remainder part of `adaptedPart`. -/
theorem adaptedPart_parts_last {N : ℕ} (Q : Fin N → Set X3)
    (hdisj : ∀ i j, i ≠ j → Disjoint (Q i) (Q j)) :
    (adaptedPart Q hdisj).parts ⟨N, Nat.lt_succ_self N⟩ = (⋃ j, interior (Q j))ᶜ :=
  dif_neg (by simp)

/-! ## Step 1: the instantiated partition and its recorded facts

`thin_boundary_partition μ ε ρ` (scale-free, for every `ε, ρ > 0`) gives finitely many
pairwise disjoint measurable pieces `Q i` covering `X₃`, a distinguished piece `j₀` with
`μ (Q j₀) < ofReal ε`, every other piece inside a `V ρ`-ball around a point, and the thin-frontier
bound.  Recording these for `P := adaptedPart Q hdisj`: the remainder part is `μ`-null, all other
parts are open, every part other than the remainder and `j₀` lies in a `V ρ`-ball, and `μ` of the
`j₀`-part is `< ε`.  (The frontier-nullity and the collar bound are `measure_iUnion_frontier_eq_zero`
and the thinness clause of `thin_boundary_partition`, in the `Q`-form; they are re-derived from the
`Q`-data whenever needed.) -/

theorem adaptedPart_facts {μ : MeasureTheory.Measure X3}
    [MeasureTheory.IsProbabilityMeasure μ] {N : ℕ} (Q : Fin N → Set X3) (j₀ : Fin N)
    (hQdisj : ∀ i j : Fin N, i ≠ j → Disjoint (Q i) (Q j))
    (hQcov : ⋃ i, Q i = Set.univ) {ρ : ℝ}
    (hQsmall : ∀ i : Fin N, i ≠ j₀ → ∃ x : X3, Q i ⊆ (fun g : SL3 => g • x) '' (V ρ))
    (g : Fin N → SL3)
    (hQball : ∀ i : Fin N, i ≠ j₀ →
      Q i ⊆ (fun v : SL3 => v • mkX (g i)) '' (V ρ))
    (hQinj : ∀ i : Fin N, i ≠ j₀ → ∀ γ : SL3, γ ∈ Γ3 →
      g i * γ * (g i)⁻¹ ∈ V (60 * ρ) → γ = 1)
    (t : Fin 3 → ℝ)
    {ε : ℝ} (hQbig : μ (Q j₀) < ENNReal.ofReal ε)
    (hQfront : μ (⋃ i : Fin N, frontier (Q i)) = 0) :
    (∀ i : Fin (N + 1), i ≠ ⟨N, Nat.lt_succ_self N⟩ →
      IsOpen ((adaptedPart Q hQdisj).parts i)) ∧
    (∀ i : Fin (N + 1), i ≠ ⟨N, Nat.lt_succ_self N⟩ →
      i ≠ ⟨j₀, j₀.isLt.trans (Nat.lt_succ_self N)⟩ →
      ∃ x : X3, (adaptedPart Q hQdisj).parts i ⊆ (fun g : SL3 => g • x) '' (V ρ)) ∧
    (∀ i : Fin (N + 1), (hiN : (i : ℕ) < N) →
      i ≠ ⟨j₀, j₀.isLt.trans (Nat.lt_succ_self N)⟩ →
      (adaptedPart Q hQdisj).parts i ⊆ (fun v : SL3 => v • mkX (g ⟨i, hiN⟩)) '' (V ρ)) ∧
    (∀ i : Fin (N + 1), (hiN : (i : ℕ) < N) →
      i ≠ ⟨j₀, j₀.isLt.trans (Nat.lt_succ_self N)⟩ →
      ∀ γ : SL3, γ ∈ Γ3 →
        g ⟨i, hiN⟩ * γ * (g ⟨i, hiN⟩)⁻¹ ∈ V (60 * ρ) → γ = 1) ∧
    μ ((adaptedPart Q hQdisj).parts ⟨N, Nat.lt_succ_self N⟩) = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    have hiN : (i : ℕ) < N := by
      by_contra hcon
      have hN : (i : ℕ) = N := by omega
      exact hi (Fin.ext hN)
    rw [adaptedPart_parts_of_lt Q hQdisj hiN]
    exact isOpen_interior
  · intro i hi hij
    have hiN : (i : ℕ) < N := by
      by_contra hcon
      have hN : (i : ℕ) = N := by omega
      exact hi (Fin.ext hN)
    rw [adaptedPart_parts_of_lt Q hQdisj hiN]
    have hne : (⟨i, hiN⟩ : Fin N) ≠ j₀ := fun h => hij (Fin.ext (by
      have h' := congrArg (fun k : Fin N => (k : ℕ)) h
      simpa using h'))
    obtain ⟨x, hx⟩ := hQsmall ⟨i, hiN⟩ hne
    exact ⟨x, interior_subset.trans hx⟩
  · intro i hiN hij
    rw [adaptedPart_parts_of_lt Q hQdisj hiN]
    have hne : (⟨i, hiN⟩ : Fin N) ≠ j₀ := fun h => hij (Fin.ext (by
      have h' := congrArg (fun k : Fin N => (k : ℕ)) h
      simpa using h'))
    exact interior_subset.trans (hQball ⟨i, hiN⟩ hne)
  · intro i hiN hij
    have hne : (⟨i, hiN⟩ : Fin N) ≠ j₀ := fun h => hij (Fin.ext (by
      have h' := congrArg (fun k : Fin N => (k : ℕ)) h
      simpa using h'))
    exact hQinj ⟨i, hiN⟩ hne
  · rw [adaptedPart_parts_last Q hQdisj]
    refine measure_mono_null ?_ hQfront
    intro x hx
    simp only [Set.mem_compl_iff, Set.mem_iUnion] at hx
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (by rw [hQcov]; exact Set.mem_univ x)
    refine Set.mem_iUnion.mpr ⟨j, ?_⟩
    by_contra hfront
    exact hfront ⟨subset_closure hj, fun hint => hx ⟨j, hint⟩⟩

/-! ## Item 1(a): the level-wise openness of the shapes

The three lemmas below are exactly the `hopen` hypothesis of
`Work.EKLC6Core.isOpen_shape_pastSig_of_margin` for the concrete partition
`P = adaptedPart Q hdisj`: the atom of `partSigma P` at a point is its part, the shape is the
trace on `U` of the preimage of that part under `u ↦ u • y`, and since every part other than the
`μ`-null remainder is *open*, that preimage is open.  Consequently, on the conull set where the
orbit avoids the remainder, the level-`n` shapes are open in `U`. -/

/-- The atom of `partSigma P` at a point of a part of `P` *is* that part. -/
theorem atom_partSigma_adaptedPart_eq_part {N : ℕ} (Q : Fin N → Set X3)
    (hdisj : ∀ i j : Fin N, i ≠ j → Disjoint (Q i) (Q j)) {k : Fin (N + 1)} {y : X3}
    (hy : y ∈ (adaptedPart Q hdisj).parts k) :
    atom (partSigma (adaptedPart Q hdisj)) y = (adaptedPart Q hdisj).parts k :=
  le_antisymm
    (atom_subset_of_mem (m := partSigma (adaptedPart Q hdisj))
      (MeasurableSpace.measurableSet_generateFrom (Set.mem_range_self k)) hy)
    (parts_subset_atom _ hy)

/-- The shape is the trace on `U` of the preimage of the part. -/
theorem shape_partSigma_adaptedPart_eq {N : ℕ} (Q : Fin N → Set X3)
    (hdisj : ∀ i j : Fin N, i ≠ j → Disjoint (Q i) (Q j)) (U : Subgroup SL3)
    {k : Fin (N + 1)} {y : X3} (hy : y ∈ (adaptedPart Q hdisj).parts k) :
    shape (partSigma (adaptedPart Q hdisj)) U y
      = (fun u : SL3 => u • y) ⁻¹' ((adaptedPart Q hdisj).parts k) ∩ U := by
  ext u
  simp only [shape, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage, SetLike.mem_coe,
    atom_partSigma_adaptedPart_eq_part Q hdisj hy]
  exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

/-- **Level-wise openness of the shapes.**  If the part of `y` is open, the shape of the atom of
`partSigma P` at `y` is the trace on `U` of an open set of `SL₃(ℝ)`. -/
theorem isOpen_shape_partSigma_adaptedPart {N : ℕ} (Q : Fin N → Set X3)
    (hdisj : ∀ i j : Fin N, i ≠ j → Disjoint (Q i) (Q j)) (U : Subgroup SL3)
    {k : Fin (N + 1)} {y : X3} (hy : y ∈ (adaptedPart Q hdisj).parts k)
    (hopen : IsOpen ((adaptedPart Q hdisj).parts k)) :
    ∃ O : Set SL3, IsOpen O ∧
      shape (partSigma (adaptedPart Q hdisj)) U y = O ∩ (U : Set SL3) :=
  ⟨(fun u : SL3 => u • y) ⁻¹' ((adaptedPart Q hdisj).parts k),
    hopen.preimage (by fun_prop), shape_partSigma_adaptedPart_eq Q hdisj U hy⟩

/-! ### Item 1(a), continued: the orbit avoids the null remainder

The level-wise openness lemma above applies at level `n` once `Tⁿx` lies in an *open* part of `P`,
i.e. once the orbit avoids the remainder.  Since the remainder is `μ`-null and the flow preserves
`μ`, the set of `x` whose orbit ever hits it is a countable union of null sets, hence null. -/

theorem ae_orbit_avoids_null_part {μ : MeasureTheory.Measure X3}
    [MeasureTheory.IsProbabilityMeasure μ] {t : Fin 3 → ℝ}
    (hmp : MeasureTheory.MeasurePreserving (fun x : X3 => aDiag t • x) μ μ)
    {N : ℕ} (Q : Fin N → Set X3)
    (hdisj : ∀ i j : Fin N, i ≠ j → Disjoint (Q i) (Q j))
    (hnull : μ ((adaptedPart Q hdisj).parts ⟨N, Nat.lt_succ_self N⟩) = 0) :
    ∀ᵐ x ∂μ, ∀ n : ℕ,
      ((fun x : X3 => aDiag t • x)^[n]) x
        ∉ (adaptedPart Q hdisj).parts ⟨N, Nat.lt_succ_self N⟩ := by
  have hmeas : MeasurableSet ((adaptedPart Q hdisj).parts ⟨N, Nat.lt_succ_self N⟩) :=
    (adaptedPart Q hdisj).measurable _
  have hzero : μ (⋃ n : ℕ, (fun x : X3 => aDiag t • x)^[n] ⁻¹'
      ((adaptedPart Q hdisj).parts ⟨N, Nat.lt_succ_self N⟩)) = 0 := by
    refine measure_iUnion_null fun n => ?_
    rw [(hmp.iterate n).measure_preimage hmeas.nullMeasurableSet]
    exact hnull
  rw [MeasureTheory.ae_iff]
  refine measure_mono_null ?_ hzero
  intro x hx
  rw [Set.mem_iUnion]
  by_contra hcon
  push_neg at hcon
  exact hx hcon

/-- **The level-wise openness along the orbit.**  For a.e. `x` and every `n`, the shape of the
`partSigma P`-atom at `Tⁿx` is the trace on `U` of an open set — the `hopen` hypothesis of
`isOpen_shape_pastSig_of_margin`, discharged for the concrete partition (the orbit avoids the
`μ`-null remainder, so every `Tⁿx` lies in an open part). -/
theorem ae_isOpen_shape_partSigma_adaptedPart {μ : MeasureTheory.Measure X3}
    [MeasureTheory.IsProbabilityMeasure μ] (t : Fin 3 → ℝ)
    (hmp : MeasureTheory.MeasurePreserving (fun x : X3 => aDiag t • x) μ μ)
    {N : ℕ} (Q : Fin N → Set X3)
    (hdisj : ∀ i j : Fin N, i ≠ j → Disjoint (Q i) (Q j))
    (hopenparts : ∀ k : Fin (N + 1), k ≠ ⟨N, Nat.lt_succ_self N⟩ →
      IsOpen ((adaptedPart Q hdisj).parts k))
    (hnull : μ ((adaptedPart Q hdisj).parts ⟨N, Nat.lt_succ_self N⟩) = 0) :
    ∀ᵐ x ∂μ, ∀ n : ℕ, ∃ O : Set SL3, IsOpen O ∧
      shape (partSigma (adaptedPart Q hdisj)) (Uminus t)
        (((fun x : X3 => aDiag t • x)^[n]) x) = O ∩ (Uminus t : Set SL3) := by
  filter_upwards [ae_orbit_avoids_null_part hmp Q hdisj hnull] with x hx
  intro n
  have hmem : ((fun x : X3 => aDiag t • x)^[n]) x ∈
      ⋃ k : Fin (N + 1), (adaptedPart Q hdisj).parts k := by
    have h : ((fun x : X3 => aDiag t • x)^[n]) x ∈ (Set.univ : Set X3) := Set.mem_univ _
    rw [← (adaptedPart Q hdisj).cover] at h
    exact h
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hmem
  have hkne : k ≠ ⟨N, Nat.lt_succ_self N⟩ := fun h => hx n (h ▸ hk)
  exact isOpen_shape_partSigma_adaptedPart Q hdisj (Uminus t) hk (hopenparts k hkne)

/-! ### Item 1(b): the assembly of the openness clause

`isOpen_shape_pastSig_of_margin` applied at `M := partSigma P` on a conull set: the level-wise
`hopen` is `ae_isOpen_shape_partSigma_adaptedPart`, the level-`0` bound `hbdd` and the margin
`hmargin` (with a rate `mu` exceeding the contraction rate `lam` of `Uminus t`) are the two inputs
supplied by `shape_subset_Uball_of_inj` and by `ae_eventually_not_mem_VThick` +
`Uball_uminus_subset_shape_of_avoid` respectively. -/
theorem ae_isOpen_shape_pastSigFinPart_of_margin {μ : MeasureTheory.Measure X3}
    [MeasureTheory.IsProbabilityMeasure μ] (t : Fin 3 → ℝ) (hne : Uminus t ≠ ⊥)
    {N : ℕ} (Q : Fin N → Set X3)
    (hdisj : ∀ i j : Fin N, i ≠ j → Disjoint (Q i) (Q j))
    {c mu : ℝ} (hc : 0 < c) (hmu : 0 < mu) (hmu1 : mu < 1)
    (hlam : ∃ lam : ℝ, 0 < lam ∧ lam < mu ∧
      ∀ i j : Fin 3, t i < t j → Real.exp (t i - t j) ≤ lam)
    (hopen : ∀ᵐ x ∂μ, ∀ n : ℕ, ∃ O : Set SL3, IsOpen O ∧
      shape (partSigma (adaptedPart Q hdisj)) (Uminus t)
        (((fun x : X3 => aDiag t • x)^[n]) x) = O ∩ (Uminus t : Set SL3))
    (hbdd : ∀ᵐ x ∂μ, ∃ ρ : ℝ, 0 < ρ ∧
      shape (partSigma (adaptedPart Q hdisj)) (Uminus t) x
        ⊆ Work.EKLComp.Uball (Uminus t) ρ)
    (hmargin : ∀ᵐ x ∂μ, ∀ᶠ n : ℕ in Filter.atTop,
      Work.EKLComp.Uball (Uminus t) (c * mu ^ n) ⊆
        shape (partSigma (adaptedPart Q hdisj)) (Uminus t)
          (((fun x : X3 => aDiag t • x)^[n]) x)) :
    ∀ᵐ x ∂μ, ∃ O : Set SL3, IsOpen O ∧
      shape (pastSigFinPart t (adaptedPart Q hdisj)) (Uminus t) x
        = O ∩ (Uminus t : Set SL3) := by
  obtain ⟨lam, hlam0, hlammu, hlamle⟩ := hlam
  have hU : IsHoro (Uminus t) := (Work.EKLC6Core.uminus_isHoro t).1
  have hcontr : ∀ u ∈ Uminus t, Filter.Tendsto
      (fun n : ℕ => aDiag t ^ n * u * (aDiag t ^ n)⁻¹) Filter.atTop (nhds 1) :=
    (Work.EKLC6Core.uminus_isHoro t).2
  filter_upwards [hopen, hbdd, hmargin] with x hopenx hbddx hmarginx
  obtain ⟨ρ, hρ, hbddx'⟩ := hbddx
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp hmarginx
  exact Work.EKLC6Core.isOpen_shape_pastSig_of_margin (U := Uminus t) (t := t)
    (M := partSigma (adaptedPart Q hdisj)) (x := x) (c := c) (ρ := ρ) (N := N₀)
    hU (le_of_lt hlam0) hlammu hmu1 hc hρ
    (fun n u _ huR => Work.EKLC6Core.conj_pow_mem_Uball (U := Uminus t) (t := t)
      hU hcontr hlam0 hlamle huR n)
    hopenx hbddx' (fun n hn => hN₀ n hn)

/-! ### Item 1(b): the `hopen` input from covering thin-frontier pieces

Consuming the pieces clause by clause: the cover `⋃ i, Q i = univ` makes the remainder of
`adaptedPart Q hdisj` `μ`-null (a point outside `⋃ i, interior (Q i)` lies in `Q j \ interior (Q j)`
for any `j` with `x ∈ Q j`, hence in `frontier (Q j)`), and the thinness clause gives
`μ (⋃ i, frontier (Q i)) = 0` by `measure_iUnion_frontier_eq_zero`.  Every other part is an
interior, hence open, so `ae_isOpen_shape_partSigma_adaptedPart` applies verbatim. -/
theorem ae_hopen_of_covering_pieces {μ : MeasureTheory.Measure X3}
    [MeasureTheory.IsProbabilityMeasure μ] (t : Fin 3 → ℝ)
    (hmp : MeasureTheory.MeasurePreserving (fun x : X3 => aDiag t • x) μ μ)
    {N : ℕ} (Q : Fin N → Set X3)
    (hdisj : ∀ i j : Fin N, i ≠ j → Disjoint (Q i) (Q j))
    (hcov : ⋃ i, Q i = Set.univ)
    {c : ℝ} (hc : 0 < c)
    (hthin : ∀ η : ℝ, 0 < η →
      μ (⋃ i : Fin N, VThick η (frontier (Q i))) ≤ ENNReal.ofReal (c * η)) :
    ∀ᵐ x ∂μ, ∀ n : ℕ, ∃ O : Set SL3, IsOpen O ∧
      shape (partSigma (adaptedPart Q hdisj)) (Uminus t)
        (((fun x : X3 => aDiag t • x)^[n]) x) = O ∩ (Uminus t : Set SL3) := by
  have hfront : μ (⋃ i : Fin N, frontier (Q i)) = 0 :=
    Work.EKLC6Core.measure_iUnion_frontier_eq_zero Q hc hthin
  have hrem : μ ((adaptedPart Q hdisj).parts ⟨N, Nat.lt_succ_self N⟩) = 0 := by
    rw [adaptedPart_parts_last Q hdisj]
    refine measure_mono_null ?_ hfront
    intro x hx
    simp only [Set.mem_compl_iff, Set.mem_iUnion] at hx
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (by rw [hcov]; exact Set.mem_univ x)
    refine Set.mem_iUnion.mpr ⟨j, ?_⟩
    by_contra hf
    exact hf ⟨subset_closure hj, fun hint => hx ⟨j, hint⟩⟩
  refine ae_isOpen_shape_partSigma_adaptedPart t hmp Q hdisj ?_ hrem
  intro k hk
  have hkN : (k : ℕ) < N := by
    by_contra hcon
    have hN : (k : ℕ) = N := by have := k.isLt; omega
    exact hk (Fin.ext hN)
  rw [adaptedPart_parts_of_lt Q hdisj hkN]
  exact isOpen_interior

/-! ### Item 1(b): the `hbdd` input, glued over the pieces

The mirror image of `ae_hopen_of_covering_pieces`.  The remainder is `μ`-null (cover + thinness),
and a point outside it lies in a part of `P`, i.e. in some `interior (Q k)`; feeding the per-piece
bounds — H80-L1550's conclusion for `k ≠ i₀`, and the `i₀`-piece statement (the short-vector/`λ₁`
argument) for `k = i₀` — gives the level-`0` boundedness almost everywhere.  Both per-piece inputs
are *hypotheses* here, so this is importable independently of the in-flight children. -/
theorem ae_hbdd_of_pieces {μ : MeasureTheory.Measure X3}
    [MeasureTheory.IsProbabilityMeasure μ] (t : Fin 3 → ℝ)
    (hmp : MeasureTheory.MeasurePreserving (fun x : X3 => aDiag t • x) μ μ)
    {N : ℕ} (Q : Fin N → Set X3) (i₀ : Fin N)
    (hdisj : ∀ i j : Fin N, i ≠ j → Disjoint (Q i) (Q j))
    (hcov : ⋃ i, Q i = Set.univ)
    {c : ℝ} (hc : 0 < c)
    (hthin : ∀ η : ℝ, 0 < η →
      μ (⋃ i : Fin N, VThick η (frontier (Q i))) ≤ ENNReal.ofReal (c * η))
    (hsmall : ∀ i : Fin N, i ≠ i₀ → ∀ y : X3, y ∈ interior (Q i) →
      (∀ u : SL3, u ∈ Uminus t → u • y = y → u = 1) →
      ∃ R : ℝ, shape (partSigma (adaptedPart Q hdisj)) (Uminus t) y
        ⊆ Work.EKLComp.Uball (Uminus t) R)
    (hexc : ∀ y : X3, y ∈ interior (Q i₀) →
      (∀ u : SL3, u ∈ Uminus t → u • y = y → u = 1) →
      ∃ R : ℝ, shape (partSigma (adaptedPart Q hdisj)) (Uminus t) y
        ⊆ Work.EKLComp.Uball (Uminus t) R) :
    ∀ᵐ x ∂μ, ∃ R : ℝ, shape (partSigma (adaptedPart Q hdisj)) (Uminus t) x
      ⊆ Work.EKLComp.Uball (Uminus t) R := by
  have hfront : μ (⋃ i : Fin N, frontier (Q i)) = 0 :=
    Work.EKLC6Core.measure_iUnion_frontier_eq_zero Q hc hthin
  have hrem : μ ((adaptedPart Q hdisj).parts ⟨N, Nat.lt_succ_self N⟩) = 0 := by
    rw [adaptedPart_parts_last Q hdisj]
    refine measure_mono_null ?_ hfront
    intro x hx
    simp only [Set.mem_compl_iff, Set.mem_iUnion] at hx
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (by rw [hcov]; exact Set.mem_univ x)
    refine Set.mem_iUnion.mpr ⟨j, ?_⟩
    by_contra hf
    exact hf ⟨subset_closure hj, fun hint => hx ⟨j, hint⟩⟩
  have hae_notrem : ∀ᵐ x ∂μ, x ∈ ⋃ j : Fin N, interior (Q j) := by
    have h : ∀ᵐ x ∂μ, x ∉ (adaptedPart Q hdisj).parts ⟨N, Nat.lt_succ_self N⟩ := by
      rw [MeasureTheory.ae_iff]
      refine measure_mono_null ?_ hrem
      intro x hx
      simpa using hx
    filter_upwards [h] with x hx
    rw [adaptedPart_parts_last Q hdisj] at hx
    simpa using hx
  filter_upwards [Work.EKLC6Core.ae_free_orbit_of_contraction (Uminus t)
      (Work.EKLC6Core.uminus_isHoro t).1 t hmp (Work.EKLC6Core.uminus_isHoro t).2,
    hae_notrem] with x hfreex hxint
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hxint
  by_cases hii : i = i₀
  · exact hexc x (by rwa [hii] at hxi) hfreex
  · exact hsmall i hii x hxi hfreex

/-! ### Item 1(b): the `hmargin` input, glued from Borel–Cantelli plus the shape transfer

The third and last gluing.  The thinness clause (H80-L1531, clause 8) bounds the collar of the
frontier union, hence `ae_eventually_not_mem_VThick` gives, for a.e. `x`, that `Tⁿx` avoids the
`1000 η`-collar for all large `n`; the orbit also avoids the `μ`-null remainder at every `n`
(`ae_orbit_avoids_null_part`), so `Tⁿx` lies in some `interior (Q i)`; the transfer hypothesis
(H80-L1575) then converts avoidance at scale `1000 · η` into the fatness `Uball (Uminus t) η ⊆
shape (partSigma P) (Uminus t) (Tⁿx)` with `η := c μ₀ⁿ`. -/
theorem ae_hmargin_of_avoid {μ : MeasureTheory.Measure X3}
    [MeasureTheory.IsProbabilityMeasure μ] {t : Fin 3 → ℝ}
    (hmp : MeasureTheory.MeasurePreserving (fun x : X3 => aDiag t • x) μ μ)
    {N : ℕ} (Q : Fin N → Set X3)
    (hdisj : ∀ i j : Fin N, i ≠ j → Disjoint (Q i) (Q j))
    (hcov : ⋃ i, Q i = Set.univ)
    {c : ℝ} (hc : 0 < c)
    (hthin : ∀ η : ℝ, 0 < η →
      μ (⋃ i : Fin N, VThick η (frontier (Q i))) ≤ ENNReal.ofReal (c * η))
    {μ₀ : ℝ} (hμ₀0 : 0 < μ₀) (hμ₀1 : μ₀ < 1)
    (hshape : ∀ (η : ℝ), 0 < η → η ≤ 1 → ∀ y : X3,
      y ∉ VThick (1000 * η) (⋃ j : Fin N, frontier (Q j)) →
      ∀ i : Fin N, y ∈ interior (Q i) →
      ∀ (P : @Work.EKLContract.FinPart Work.EKLContract.X3
          Work.EKLContract.instMeasurableSpaceX3) (k : Fin P.n),
        P.parts k = interior (Q i) →
      Work.EKLComp.Uball (Uminus t) η ⊆
        shape (partSigma P) (Uminus t) y) :
    ∀ᵐ x ∂μ, ∀ᶠ n : ℕ in Filter.atTop,
      Work.EKLComp.Uball (Uminus t) (c * μ₀ ^ n) ⊆
        shape (partSigma (adaptedPart Q hdisj)) (Uminus t)
          (((fun x : X3 => aDiag t • x)^[n]) x) := by
  have hfront : μ (⋃ i : Fin N, frontier (Q i)) = 0 :=
    Work.EKLC6Core.measure_iUnion_frontier_eq_zero Q hc hthin
  have hrem : μ ((adaptedPart Q hdisj).parts ⟨N, Nat.lt_succ_self N⟩) = 0 := by
    rw [adaptedPart_parts_last Q hdisj]
    refine measure_mono_null ?_ hfront
    intro x hx
    simp only [Set.mem_compl_iff, Set.mem_iUnion] at hx
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (by rw [hcov]; exact Set.mem_univ x)
    refine Set.mem_iUnion.mpr ⟨j, ?_⟩
    by_contra hf
    exact hf ⟨subset_closure hj, fun hint => hx ⟨j, hint⟩⟩
  have hthinA : ∀ η : ℝ, 0 < η →
      μ (VThick η (⋃ i : Fin N, frontier (Q i)))
        ≤ ENNReal.ofReal ((1000 * c) * η) := by
    intro η hη
    refine le_trans (measure_mono ?_) (le_trans (hthin η hη) (ENNReal.ofReal_le_ofReal ?_))
    · rintro y ⟨p, ⟨hv, hs⟩, rfl⟩
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hs
      exact Set.mem_iUnion.mpr ⟨i, p, ⟨hv, hi⟩, rfl⟩
    · nlinarith [hη, hc]
  have hbc := ae_eventually_not_mem_VThick hmp (⋃ i : Fin N, frontier (Q i))
    (show (0 : ℝ) < 1000 * c by linarith) hμ₀0 hμ₀1 hthinA
  have hμ₀ev : ∀ᶠ n : ℕ in Filter.atTop, c * μ₀ ^ n ≤ 1 := by
    have hlim : Filter.Tendsto (fun n : ℕ => c * μ₀ ^ n) Filter.atTop (nhds 0) := by
      simpa using
        (tendsto_pow_atTop_nhds_zero_of_lt_one (le_of_lt hμ₀0) hμ₀1).const_mul c
    filter_upwards [hlim.eventually (isOpen_Iio.mem_nhds (by norm_num : (0 : ℝ) < 1))]
      with n hn
    exact le_of_lt hn
  filter_upwards [ae_orbit_avoids_null_part hmp Q hdisj hrem, hbc] with x hxavoid hxbc
  filter_upwards [hxbc, hμ₀ev] with n hn hcμ
  intro u hu
  have hmem : ((fun x : X3 => aDiag t • x)^[n]) x ∈
      ⋃ k : Fin (N + 1), (adaptedPart Q hdisj).parts k := by
    have h : ((fun x : X3 => aDiag t • x)^[n]) x ∈ (Set.univ : Set X3) := Set.mem_univ _
    rwa [← (adaptedPart Q hdisj).cover] at h
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hmem
  rcases lt_or_eq_of_le (Nat.le_of_lt_succ k.isLt) with hkN | hkN
  · rw [adaptedPart_parts_of_lt Q hdisj hkN] at hk
    have hAvoid : ((fun x : X3 => aDiag t • x)^[n]) x ∉
        VThick (1000 * (c * μ₀ ^ n)) (⋃ i : Fin N, frontier (Q i)) := by
      convert hn using 2
      ring
    exact hshape (c * μ₀ ^ n) (mul_pos hc (pow_pos hμ₀0 n)) hcμ _ hAvoid ⟨k, hkN⟩ hk
      (adaptedPart Q hdisj) k (adaptedPart_parts_of_lt Q hdisj hkN) hu
  · have hk' : k = ⟨N, Nat.lt_succ_self N⟩ := Fin.ext hkN
    exact absurd (hk' ▸ hk) (hxavoid n)

/-- **Item 1, complete: the openness clause of the target from the covering pieces.**  All three
inputs of `ae_isOpen_shape_pastSigFinPart_of_margin` are produced here from the raw data:

* `hopen` from the cover and the thinness (`ae_hopen_of_covering_pieces`),
* `hbdd` from the per-piece bounds (`ae_hbdd_of_pieces`),
* `hmargin` from the collar-avoidance (`ae_eventually_not_mem_VThick`, proved in the workspace)
  plus the avoidance-to-shape transfer (`ae_hmargin_of_avoid`).

The only remaining inputs are exactly the three external statements: the per-piece boundedness on
non-exceptional pieces, the `i₀`-piece boundedness, and the avoidance-to-shape transfer. -/
theorem ae_isOpen_shape_pastSigFinPart_of_pieces {μ : MeasureTheory.Measure X3}
    [MeasureTheory.IsProbabilityMeasure μ] (t : Fin 3 → ℝ) (hne : Uminus t ≠ ⊥)
    (hmp : MeasureTheory.MeasurePreserving (fun x : X3 => aDiag t • x) μ μ)
    {N : ℕ} (Q : Fin N → Set X3) (i₀ : Fin N)
    (hdisj : ∀ i j : Fin N, i ≠ j → Disjoint (Q i) (Q j))
    (hcov : ⋃ i, Q i = Set.univ)
    {c : ℝ} (hc : 0 < c)
    (hthin : ∀ η : ℝ, 0 < η →
      μ (⋃ i : Fin N, VThick η (frontier (Q i))) ≤ ENNReal.ofReal (c * η))
    {mu : ℝ} (hmu0 : 0 < mu) (hmu1 : mu < 1)
    (hlam : ∃ lam : ℝ, 0 < lam ∧ lam < mu ∧
      ∀ i j : Fin 3, t i < t j → Real.exp (t i - t j) ≤ lam)
    (hsmall : ∀ i : Fin N, i ≠ i₀ → ∀ y : X3, y ∈ interior (Q i) →
      (∀ u : SL3, u ∈ Uminus t → u • y = y → u = 1) →
      ∃ R : ℝ, shape (partSigma (adaptedPart Q hdisj)) (Uminus t) y
        ⊆ Work.EKLComp.Uball (Uminus t) R)
    (hexc : ∀ y : X3, y ∈ interior (Q i₀) →
      (∀ u : SL3, u ∈ Uminus t → u • y = y → u = 1) →
      ∃ R : ℝ, shape (partSigma (adaptedPart Q hdisj)) (Uminus t) y
        ⊆ Work.EKLComp.Uball (Uminus t) R)
    (hshape : ∀ (η : ℝ), 0 < η → η ≤ 1 → ∀ y : X3,
      y ∉ VThick (1000 * η) (⋃ j : Fin N, frontier (Q j)) →
      ∀ i : Fin N, y ∈ interior (Q i) →
      ∀ (P : @Work.EKLContract.FinPart Work.EKLContract.X3
          Work.EKLContract.instMeasurableSpaceX3) (k : Fin P.n),
        P.parts k = interior (Q i) →
      Work.EKLComp.Uball (Uminus t) η ⊆
        shape (partSigma P) (Uminus t) y) :
    ∀ᵐ x ∂μ, ∃ O : Set SL3, IsOpen O ∧
      shape (pastSigFinPart t (adaptedPart Q hdisj)) (Uminus t) x
        = O ∩ (Uminus t : Set SL3) := by
  refine ae_isOpen_shape_pastSigFinPart_of_margin t hne Q hdisj hc hmu0 hmu1 hlam
    (ae_hopen_of_covering_pieces t hmp Q hdisj hcov hc hthin) ?_
    (ae_hmargin_of_avoid hmp Q hdisj hcov hc hthin hmu0 hmu1 hshape)
  filter_upwards [ae_hbdd_of_pieces t hmp Q i₀ hdisj hcov hc hthin hsmall hexc] with x hx
  obtain ⟨R, hR⟩ := hx
  exact ⟨max R 1, lt_of_lt_of_le one_pos (le_max_right _ _),
    hR.trans (Work.EKLComp.Uball_mono (le_max_left _ _))⟩

/-! ## Item 2: the level-`0` atom of a small part is a bounded `V`-ball around its point

The first step of the *expanding-direction* half of the atom containment.  If the part of `y` is
one of the small pieces (contained in a `V ρ`-ball around the centre `mkX g`), then every point of
the level-`0` atom of `y` (which *is* that part) is obtained from `y` by an element of
`V (ρ + 10ρ + 30ρ²)`: both `y` and `z` lie in the same `V ρ`-ball, so `adapted_pair_Vball` applies.
No injectivity hypothesis is needed for this direction. -/
theorem atom_subset_Vball_of_small_part {N : ℕ} (Q : Fin N → Set X3)
    (hdisj : ∀ i j : Fin N, i ≠ j → Disjoint (Q i) (Q j))
    {k : Fin (N + 1)} {i : Fin N}
    (hPk : (adaptedPart Q hdisj).parts k = interior (Q i))
    (g : SL3) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hball : Q i ⊆ (fun v : SL3 => v • mkX g) '' (V ρ))
    {y : X3} (hy : y ∈ interior (Q i)) :
    atom (partSigma (adaptedPart Q hdisj)) y
      ⊆ (fun v : SL3 => v • y) '' (V (ρ + 10 * ρ + 3 * ρ * (10 * ρ))) := by
  have hyk : y ∈ (adaptedPart Q hdisj).parts k := by rw [hPk]; exact hy
  have hyball : y ∈ (fun v : SL3 => v • mkX g) '' (V ρ) :=
    hball (interior_subset (by have h := hyk; rw [hPk] at h; exact h))
  intro z hz
  have hzpart : z ∈ (adaptedPart Q hdisj).parts k := by
    rw [← atom_partSigma_adaptedPart_eq_part Q hdisj hyk]; exact hz
  have hzball : z ∈ (fun v : SL3 => v • mkX g) '' (V ρ) :=
    hball (interior_subset (by have h := hzpart; rw [hPk] at h; exact h))
  exact Work.EKLC6Core.adapted_pair_Vball (x := mkX g) (c := y) (z := z) hρ hρ1 hyball hzball



/-- The `hshape` slot, produced in one application from the proved transfer lemma
`Uball_uminus_subset_shape_of_avoid` (H80-L1575), whose conclusion has exactly this generic
`(P, k, hPk)` shape — so no part index has to be manufactured. -/
theorem hshape_param_of_avoid {N : ℕ} (Q : Fin N → Set X3)
    (hdisj : ∀ i j : Fin N, i ≠ j → Disjoint (Q i) (Q j)) (t : Fin 3 → ℝ) :
    ∀ (η : ℝ), 0 < η → η ≤ 1 → ∀ y : X3,
      y ∉ VThick (1000 * η) (⋃ j : Fin N, frontier (Q j)) →
      ∀ i : Fin N, y ∈ interior (Q i) →
      ∀ (P : @Work.EKLContract.FinPart Work.EKLContract.X3
          Work.EKLContract.instMeasurableSpaceX3) (k : Fin P.n),
        P.parts k = interior (Q i) →
      Work.EKLComp.Uball (Uminus t) η ⊆
        shape (partSigma P) (Uminus t) y := by
  intro η hη hη1 y havoid i hy P k hPk
  exact Work.EKLC6Core.Uball_uminus_subset_shape_of_avoid Q hdisj t hη hη1 hy havoid P k hPk

/-- **Item 1, final wiring.**  The target's openness clause from the covering thin-frontier pieces
of H80-L1531 (`Q`, `i₀`, `g`, disjointness, cover, thinness, `V ρ`-balls, injectivity), the
per-piece bounds of H80-L1594 (with the freeness hypothesis that H80-L1550's counterexample makes
necessary), and the proved transfer `hshape_param_of_avoid`; the rate data are
`exists_contract_rate` at the margin rate `mu := (lam + 1) / 2`. -/
theorem ae_isOpen_shape_pastSigFinPart_of_thin_inj_data {μ : MeasureTheory.Measure X3}
    [MeasureTheory.IsProbabilityMeasure μ] (t : Fin 3 → ℝ) (hne : Uminus t ≠ ⊥)
    (hmp : MeasureTheory.MeasurePreserving (fun x : X3 => aDiag t • x) μ μ)
    {N : ℕ} (Q : Fin N → Set X3) (i₀ : Fin N) (g : Fin N → SL3)
    {ρ c : ℝ} (hρ : 0 < ρ) (hc : 0 < c)
    (hdisj : ∀ i j : Fin N, i ≠ j → Disjoint (Q i) (Q j))
    (hcov : ⋃ i, Q i = Set.univ)
    (hthin : ∀ η : ℝ, 0 < η →
      μ (⋃ i : Fin N, VThick η (frontier (Q i))) ≤ ENNReal.ofReal (c * η))
    (hball : ∀ i : Fin N, i ≠ i₀ →
      Q i ⊆ (fun v : SL3 => v • mkX (g i)) '' (V ρ))
    (hinj : ∀ i : Fin N, i ≠ i₀ → ∀ γ : SL3, γ ∈ Γ3 →
      g i * γ * (g i)⁻¹ ∈ V (60 * ρ) → γ = 1)
    (hsmall : ∀ i : Fin N, i ≠ i₀ → ∀ y : X3, y ∈ interior (Q i) →
      (∀ u : SL3, u ∈ Uminus t → u • y = y → u = 1) →
      ∃ R : ℝ, shape (partSigma (adaptedPart Q hdisj)) (Uminus t) y
        ⊆ Work.EKLComp.Uball (Uminus t) R)
    (hexc : ∀ y : X3, y ∈ interior (Q i₀) →
      (∀ u : SL3, u ∈ Uminus t → u • y = y → u = 1) →
      ∃ R : ℝ, shape (partSigma (adaptedPart Q hdisj)) (Uminus t) y
        ⊆ Work.EKLComp.Uball (Uminus t) R) :
    ∀ᵐ x ∂μ, ∃ O : Set SL3, IsOpen O ∧
      shape (pastSigFinPart t (adaptedPart Q hdisj)) (Uminus t) x
        = O ∩ (Uminus t : Set SL3) := by
  obtain ⟨lam, hlam0, hlam1, hlamle⟩ := Work.EKLC6Core.exists_contract_rate t
  have hmu0' : (0 : ℝ) < (lam + 1) / 2 := by linarith
  have hmu1' : (lam + 1) / 2 < 1 := by linarith
  have hlamm : lam < (lam + 1) / 2 := by linarith
  have hlam' : ∃ lam' : ℝ, 0 < lam' ∧ lam' < (lam + 1) / 2 ∧
      ∀ i j : Fin 3, t i < t j → Real.exp (t i - t j) ≤ lam' :=
    ⟨lam, hlam0, hlamm, hlamle⟩
  exact ae_isOpen_shape_pastSigFinPart_of_pieces t hne hmp Q i₀ hdisj hcov hc hthin
    hmu0' hmu1' hlam' hsmall hexc (hshape_param_of_avoid Q hdisj t)

/-- The union-of-collars bound implies the collar-of-the-union bound with the same constant, which
is the form `thinness_const_le_one` and the margin chain consume. -/
theorem VThick_iUnion_le {N : ℕ} {μ : MeasureTheory.Measure X3} (Q : Fin N → Set X3)
    {c : ℝ} (h : ∀ η : ℝ, 0 < η →
      μ (⋃ i : Fin N, VThick η (frontier (Q i))) ≤ ENNReal.ofReal (c * η)) :
    ∀ η : ℝ, 0 < η →
      μ (VThick η (⋃ i : Fin N, frontier (Q i))) ≤ ENNReal.ofReal (c * η) := by
  intro η hη
  refine le_trans (measure_mono ?_) (h η hη)
  rintro y ⟨p, ⟨hv, hs⟩, rfl⟩
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hs
  exact Set.mem_iUnion.mpr ⟨i, p, ⟨hv, hi⟩, rfl⟩

/-! ## The `(★)` transfer: `A ≤ pastSigFinPart t P` gives the orbit clause and boundedness

These are the two clauses of §2 of the STATUS block above, made formal: if a σ-algebra `A`
that is a `Uminus t`-plaque algebra on a conull set is contained in the past σ-algebra of a
finite `P`, then the past σ-algebra of `P` inherits (i) the orbit clause and (ii) the entrywise
boundedness.  Only the *openness* of the shape is left to the caller (see §3 of the STATUS
block: it needs the Pisa 7.31 input `past_atom_contains_Uball_of_thin_frontier`). -/

/-- Atoms are antitone in the σ-algebra: a *finer* σ-algebra has *smaller* atoms. -/
theorem atom_subset_atom_of_le {A B : MeasurableSpace X3} (h : A ≤ B) (x : X3) :
    atom B x ⊆ atom A x := by
  intro y hy
  refine Set.mem_sInter.mpr ?_
  rintro s ⟨hsA, hxs⟩
  exact hy s ⟨(MeasurableSpace.le_def.mp h) s hsA, hxs⟩

/-- Shapes are antitone in the σ-algebra. -/
theorem shape_subset_shape_of_le {A B : MeasurableSpace X3} (h : A ≤ B) (U : Subgroup SL3)
    (x : X3) : shape B U x ⊆ shape A U x :=
  fun _ hu => ⟨hu.1, atom_subset_atom_of_le h x hu.2⟩

/-- **The `(★)` transfer.**  A plaque algebra `A` for `Uminus t` on a conull set, contained in
the past σ-algebra of a finite partition `P`, forces the orbit clause and the entrywise
boundedness of the `Uminus t`-shape of `pastSigFinPart t P`. -/
theorem transfer_orbit_and_bdd_of_le {μ : MeasureTheory.Measure X3}
    [MeasureTheory.IsProbabilityMeasure μ] {A : MeasurableSpace X3} {Z₀ : Set X3}
    {t : Fin 3 → ℝ} (hplq : IsPlaqueAlgebra (Uminus t) Z₀ A)
    (hZ₀ : μ Z₀ᶜ = 0) (P : @FinPart X3 Work.EKLContract.instMeasurableSpaceX3)
    (hle : A ≤ pastSigFinPart t P) :
    (∀ᵐ x ∂μ, atom (pastSigFinPart t P) x ⊆
      (fun u : SL3 => u • x) '' (Uminus t : Set SL3)) ∧
    (∀ᵐ x ∂μ, ∃ C : ℝ, ∀ u ∈ shape (pastSigFinPart t P) (Uminus t) x,
      ∀ i j : Fin 3, |u i j| ≤ C) := by
  have hpt := hplq.2.2.2
  have h1 : ∀ᵐ x ∂μ, atom (pastSigFinPart t P) x ⊆
      (fun u : SL3 => u • x) '' (Uminus t : Set SL3) := by
    rw [MeasureTheory.ae_iff]
    refine measure_mono_null (fun x hx => ?_) hZ₀
    simp only [Set.mem_setOf_eq] at hx
    exact fun hxZ => hx (fun y hy => (hpt x hxZ).2.1 (atom_subset_atom_of_le hle x hy))
  have h2 : ∀ᵐ x ∂μ, ∃ C : ℝ, ∀ u ∈ shape (pastSigFinPart t P) (Uminus t) x,
      ∀ i j : Fin 3, |u i j| ≤ C := by
    rw [MeasureTheory.ae_iff]
    refine measure_mono_null (fun x hx => ?_) hZ₀
    simp only [Set.mem_setOf_eq] at hx
    exact fun hxZ => hx (by
      obtain ⟨C, hC⟩ := (hpt x hxZ).2.2.2
      exact ⟨C, fun u hu => hC u (shape_subset_shape_of_le hle (Uminus t) x hu)⟩)
  exact ⟨h1, h2⟩

/-- **The reduction.**  `(★)`-data (`A` a `Uminus t`-plaque algebra on a conull set, contained in
`pastSigFinPart t P`) together with the a.e. *openness* of the `Uminus t`-shape of
`pastSigFinPart t P` yield the conclusion of the frozen target for `P`.  The openness is the
Pisa 7.31 input; by §3 of the STATUS block it is the only clause not implied by `(★)`. -/
theorem finPart_plaquePast_exists_of_le {μ : MeasureTheory.Measure X3}
    [MeasureTheory.IsProbabilityMeasure μ] (t : Fin 3 → ℝ)
    {A : MeasurableSpace X3} {Z₀ : Set X3} (hplq : IsPlaqueAlgebra (Uminus t) Z₀ A)
    (hZ₀ : μ Z₀ᶜ = 0) (P : @FinPart X3 Work.EKLContract.instMeasurableSpaceX3)
    (hle : A ≤ pastSigFinPart t P)
    (hopen : ∀ᵐ x ∂μ, ∃ O : Set SL3, IsOpen O ∧
      shape (pastSigFinPart t P) (Uminus t) x = O ∩ (Uminus t : Set SL3)) :
    ∃ Z : Set X3, μ Zᶜ = 0 ∧ IsPlaqueAlgebra (Uminus t) Z (pastSigFinPart t P) :=
  finPart_plaquePast_exists_of_ae t P (transfer_orbit_and_bdd_of_le hplq hZ₀ P hle).1 hopen
    (transfer_orbit_and_bdd_of_le hplq hZ₀ P hle).2

/-! ## The shadow-set form of the centraliser crux (session 17)

See the STATUS block "session 17" at the top of this file.  For a central element `c` the
per-`c` statement is the proved `ae_not_mem_atom_of_part_moved`; the *joint* statement over
`c ∈ C(φ) \ {1}` is the crux.  The lemmas below isolate the measure-theoretic shape of the
per-`c` statement: its "shadow" set is forward invariant, hence null or conull, so the per-`c`
statement has no room for improvement and the joint statement is genuinely new content. -/

/-- The centraliser of `aDiag t` in `SL₃(ℝ)`, as a subgroup. -/
def cenSub (t : Fin 3 → ℝ) : Subgroup SL3 :=
  Subgroup.centralizer ({aDiag t} : Set SL3)

theorem mem_cenSub {t : Fin 3 → ℝ} {c : SL3} :
    c ∈ cenSub t ↔ aDiag t * c = c * aDiag t := by
  rw [cenSub, Subgroup.mem_centralizer_iff]
  constructor
  · intro h
    exact h (aDiag t) (Set.mem_singleton _)
  · intro h g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    exact h

/-- The points whose `P`-part is preserved by the `c`-translate. -/
def fixedSet (P : FinPart X3) (c : SL3) : Set X3 :=
  ⋃ i : Fin P.n, (P.parts i ∩ (fun z : X3 => c • z) ⁻¹' (P.parts i))

theorem measurableSet_fixedSet (P : FinPart X3) (c : SL3) : MeasurableSet (fixedSet P c) :=
  MeasurableSet.iUnion fun i =>
    (P.measurable i).inter ((continuous_const_smul c).measurable (P.measurable i))

/-- The part of `P` containing a point. -/
theorem exists_part_mem (P : FinPart X3) (z : X3) : ∃ i : Fin P.n, z ∈ P.parts i := by
  have hmem : z ∈ ⋃ i : Fin P.n, P.parts i := by rw [P.cover]; exact Set.mem_univ z
  exact Set.mem_iUnion.mp hmem

/-- A point is in `fixedSet P c` exactly when the level-`0` atom of its `P`-part contains
`c • z`. -/
theorem mem_fixedSet_iff (P : FinPart X3) (c : SL3) (z : X3) :
    z ∈ fixedSet P c ↔ c • z ∈ atom (partSigma P) z := by
  have hgen : ∀ i : Fin P.n, MeasurableSet[partSigma P] (P.parts i) := fun i =>
    MeasurableSpace.measurableSet_generateFrom (Set.mem_range_self i)
  constructor
  · intro h
    rw [fixedSet, Set.mem_iUnion] at h
    obtain ⟨i, hi, hci⟩ := h
    exact parts_subset_atom P hi hci
  · intro h
    obtain ⟨i, hi⟩ := exists_part_mem P z
    rw [fixedSet, Set.mem_iUnion]
    exact ⟨i, hi, atom_subset_of_mem (m := partSigma P) (hgen i) hi h⟩

/-- `fixedSet` is the complement of `movedSet`. -/
theorem fixedSet_eq_compl_movedSet (P : FinPart X3) (c : SL3) :
    fixedSet P c = (movedSet P c)ᶜ := by
  ext z
  rw [Set.mem_compl_iff, mem_movedSet_iff, ← mem_fixedSet_iff]
  tauto

/-- **The `c`-shadow set**: the points whose whole forward orbit has its `P`-part preserved by
the `c`-translate. -/
def shadowSet (t : Fin 3 → ℝ) (P : FinPart X3) (c : SL3) : Set X3 :=
  ⋂ n : ℕ, ((fun x : X3 => aDiag t • x)^[n]) ⁻¹' (fixedSet P c)

theorem mem_shadowSet_iff {t : Fin 3 → ℝ} {P : FinPart X3} {c : SL3} {x : X3} :
    x ∈ shadowSet t P c ↔ ∀ n : ℕ, ((fun x : X3 => aDiag t • x)^[n]) x ∈ fixedSet P c := by
  rw [shadowSet, Set.mem_iInter]
  constructor
  · intro h n
    exact h n
  · intro h n
    exact h n

theorem measurableSet_shadowSet (t : Fin 3 → ℝ) (P : FinPart X3) (c : SL3) :
    MeasurableSet (shadowSet t P c) :=
  MeasurableSet.iInter fun n =>
    (measurableSet_fixedSet P c).preimage ((continuous_const_smul (aDiag t)).measurable.iterate n)

theorem shadowSet_subset_fixedSet (t : Fin 3 → ℝ) (P : FinPart X3) (c : SL3) :
    shadowSet t P c ⊆ fixedSet P c := by
  intro x hx
  have h := (mem_shadowSet_iff.mp hx) 0
  simpa using h

/-- The shadow set is **forward invariant**. -/
theorem shadowSet_subset_preimage (t : Fin 3 → ℝ) (P : FinPart X3) (c : SL3) :
    shadowSet t P c ⊆ (fun x : X3 => aDiag t • x) ⁻¹' (shadowSet t P c) := by
  intro x hx
  rw [Set.mem_preimage]
  rw [mem_shadowSet_iff] at hx ⊢
  intro n
  have h := hx (n + 1)
  rw [Function.iterate_succ_apply] at h
  exact h

/-- **The shadow set is invariant up to `μ`-null sets.** -/
theorem shadowSet_ae_invariant {μ : MeasureTheory.Measure X3}
    [MeasureTheory.IsProbabilityMeasure μ] {t : Fin 3 → ℝ} {P : FinPart X3}
    {c : SL3} (hmp : MeasureTheory.MeasurePreserving (fun x : X3 => aDiag t • x) μ μ) :
    (fun x : X3 => aDiag t • x) ⁻¹' (shadowSet t P c) =ᵐ[μ] shadowSet t P c := by
  have hmeas : MeasurableSet (shadowSet t P c) := measurableSet_shadowSet t P c
  have hsub : shadowSet t P c ⊆ (fun x : X3 => aDiag t • x) ⁻¹' (shadowSet t P c) :=
    shadowSet_subset_preimage t P c
  have hdiff : μ ((fun x : X3 => aDiag t • x) ⁻¹' (shadowSet t P c) \ shadowSet t P c) = 0 := by
    have h1 := MeasureTheory.measure_sdiff hsub hmeas.nullMeasurableSet
      (MeasureTheory.measure_ne_top μ _)
    have h2 : μ ((fun x : X3 => aDiag t • x) ⁻¹' (shadowSet t P c)) = μ (shadowSet t P c) :=
      hmp.measure_preimage hmeas.nullMeasurableSet
    rw [h2, tsub_self] at h1
    exact h1
  refine MeasureTheory.ae_eq_set.mpr ⟨hdiff, ?_⟩
  rw [Set.sdiff_eq_empty.mpr hsub, measure_empty]

/-- **The shadow set is null or conull.**  For a fixed `c` there is no intermediate behaviour. -/
theorem shadowSet_measure_zero_or_univ {μ : MeasureTheory.Measure X3}
    [MeasureTheory.IsProbabilityMeasure μ] {t : Fin 3 → ℝ} {P : FinPart X3} {c : SL3}
    (hmp : MeasureTheory.MeasurePreserving (fun x : X3 => aDiag t • x) μ μ)
    (hqerg : ∀ E : Set X3, MeasurableSet E →
      (fun x : X3 => aDiag t • x) ⁻¹' E =ᵐ[μ] E → μ E = 0 ∨ μ Eᶜ = 0) :
    μ (shadowSet t P c) = 0 ∨ μ (shadowSet t P c)ᶜ = 0 :=
  hqerg _ (measurableSet_shadowSet t P c) (shadowSet_ae_invariant hmp)

/-- **A moved part forces a null shadow.**  If `0 < μ (movedSet P c)` — the hypothesis of
`ae_not_mem_atom_of_part_moved` — then the shadow set of `c` is already null. -/
theorem shadowSet_measure_zero_of_moved {μ : MeasureTheory.Measure X3}
    [MeasureTheory.IsProbabilityMeasure μ] {t : Fin 3 → ℝ} {P : FinPart X3} {c : SL3}
    (hmp : MeasureTheory.MeasurePreserving (fun x : X3 => aDiag t • x) μ μ)
    (hqerg : ∀ E : Set X3, MeasurableSet E →
      (fun x : X3 => aDiag t • x) ⁻¹' E =ᵐ[μ] E → μ E = 0 ∨ μ Eᶜ = 0)
    (hpos : 0 < μ (movedSet P c)) :
    μ (shadowSet t P c) = 0 := by
  rcases shadowSet_measure_zero_or_univ hmp hqerg with h | h
  · exact h
  · exfalso
    have hfix : μ (fixedSet P c) = 1 - μ (movedSet P c) := by
      rw [fixedSet_eq_compl_movedSet, MeasureTheory.measure_compl (measurableSet_movedSet P c)
        (MeasureTheory.measure_ne_top μ _), measure_univ]
    have hlt : μ (shadowSet t P c) < 1 := by
      refine lt_of_le_of_lt (MeasureTheory.measure_mono (shadowSet_subset_fixedSet t P c)) ?_
      rw [hfix]
      exact ENNReal.sub_lt_self (by simp) (by simp) (ne_of_gt hpos)
    have hone : μ (shadowSet t P c) = 1 := by
      have hsum := MeasureTheory.measure_add_measure_compl (μ := μ)
        (measurableSet_shadowSet t P c)
      rw [measure_univ, h, add_zero] at hsum
      exact hsum
    rw [hone] at hlt
    exact absurd hlt (lt_irrefl 1)

/-- **The measure-theoretic step of §4 of the session-17 STATUS block.**  If a measurable family of
subsets of `X₃` (indexed by `ℝ`) has `μ`-null members for `lam`-a.e. parameter, then for `μ`-a.e.
point the set of parameters whose member contains it is `lam`-null.  This is Mathlib's product
Fubini; it is the step that turns the per-`c` shadow dichotomy `shadowSet_measure_zero_of_moved`
into a statement about a.e. `x`. -/
theorem ae_fibre_measure_zero_of_ae_measure_zero {lam : MeasureTheory.Measure ℝ}
    [MeasureTheory.SFinite lam] {μ : MeasureTheory.Measure X3} [MeasureTheory.SFinite μ]
    {W : Set (ℝ × X3)} (hWmeas : MeasurableSet W)
    (h : ∀ᵐ s ∂lam, μ {x : X3 | (s, x) ∈ W} = 0) :
    ∀ᵐ x ∂μ, lam {s : ℝ | (s, x) ∈ W} = 0 := by
  have hprod : (lam.prod μ) W = 0 := by
    rw [MeasureTheory.Measure.prod_apply hWmeas]
    refine MeasureTheory.lintegral_eq_zero_of_ae_eq_zero ?_
    filter_upwards [h] with s hs
    rw [show (Prod.mk s) ⁻¹' W = {x : X3 | (s, x) ∈ W} from by ext x; exact Iff.rfl]
    exact hs
  have hW'meas : MeasurableSet (Prod.swap ⁻¹' W) := hWmeas.preimage measurable_swap
  have hswap : (μ.prod lam) (Prod.swap ⁻¹' W) = 0 := by
    have hm : (μ.prod lam) = MeasureTheory.Measure.map Prod.swap (lam.prod μ) :=
      MeasureTheory.Measure.prod_swap.symm
    rw [hm, MeasureTheory.Measure.map_apply measurable_swap hW'meas]
    rw [show Prod.swap ⁻¹' (Prod.swap ⁻¹' W) = W from by ext p; exact Iff.rfl]
    exact hprod
  have hae : ∀ᵐ p ∂(μ.prod lam), p ∉ Prod.swap ⁻¹' W := by
    rw [MeasureTheory.ae_iff]
    have hset : {p : X3 × ℝ | ¬ p ∉ Prod.swap ⁻¹' W} = Prod.swap ⁻¹' W := by
      ext p
      simp
    rw [hset]
    exact hswap
  have hae2 : ∀ᵐ x ∂μ, ∀ᵐ s ∂lam, (s, x) ∉ W := by
    have h2 := (MeasureTheory.Measure.ae_prod_mem_iff_ae_ae_mem hW'meas.compl).mp hae
    refine Filter.Eventually.mono h2 fun x hx => Filter.Eventually.mono hx fun s hs hsW => ?_
    exact hs hsW
  filter_upwards [hae2] with x hx
  rw [MeasureTheory.ae_iff] at hx
  simpa using hx

/-- **The §4 Fubini step along a fixed direction of the centraliser.**  If along the direction
`s₀` of `C(φ)` the parts of `P` are moved for a.e. parameter `a` (Lebesgue measure on `ℝ`), then
for `μ`-a.e. `x` the set of parameters `a` for which the `a`-shadow of `x` holds is
Lebesgue-null.

The joint measurability input `hmeas` holds as soon as `a ↦ aDiag (a • s₀)` is measurable (its
member sets are the level sets of the `fixedSet`-family); it is stated as a hypothesis here
because `aDiag`'s measurability in its argument is not yet in the tree. -/
theorem ae_shadow_family_measure_zero (t : Fin 3 → ℝ) (P : FinPart X3) (s₀ : Fin 3 → ℝ)
    {μ : MeasureTheory.Measure X3} [MeasureTheory.IsProbabilityMeasure μ]
    (hmp : MeasureTheory.MeasurePreserving (fun x : X3 => aDiag t • x) μ μ)
    (hqerg : ∀ E : Set X3, MeasurableSet E →
      (fun x : X3 => aDiag t • x) ⁻¹' E =ᵐ[μ] E → μ E = 0 ∨ μ Eᶜ = 0)
    (hmeas : MeasurableSet {p : ℝ × X3 | p.2 ∈ shadowSet t P (aDiag (p.1 • s₀))})
    (h : ∀ᵐ a ∂(volume : MeasureTheory.Measure ℝ), 0 < μ (movedSet P (aDiag (a • s₀)))) :
    ∀ᵐ x ∂μ, volume {a : ℝ | x ∈ shadowSet t P (aDiag (a • s₀))} = 0 := by
  refine ae_fibre_measure_zero_of_ae_measure_zero hmeas ?_
  filter_upwards [h] with a ha
  exact shadowSet_measure_zero_of_moved hmp hqerg ha

/-- **The frozen target** (statement unchanged). -/

theorem finPart_plaquePast_exists {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ] (t : Fin 3 → ℝ)
    (hne : Work.EKLC6Core.Uminus t ≠ ⊥)
    (hmp : MeasureTheory.MeasurePreserving
      (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) μ μ)
    (hqerg : ∀ E : Set Work.EKLContract.X3, MeasurableSet E →
      (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) ⁻¹' E =ᵐ[μ] E →
      μ E = 0 ∨ μ Eᶜ = 0)
    (hent : 0 < Work.EKLContract.ent μ
      (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x)) :
    ∃ (P : @Work.EKLContract.FinPart Work.EKLContract.X3 Work.EKLContract.instMeasurableSpaceX3)
      (Z : Set Work.EKLContract.X3),
      μ Zᶜ = 0 ∧
      Work.EKLContract.IsPlaqueAlgebra (Work.EKLC6Core.Uminus t) Z
        (Work.EKLC6Core.pastSigFinPart t P) := by sorry

end Work.EKLC6Core

end
