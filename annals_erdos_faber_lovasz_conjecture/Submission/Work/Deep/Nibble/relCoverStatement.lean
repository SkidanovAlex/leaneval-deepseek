import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Nibble.relCoverStatement_of_Kahn
import Submission.Work.Deep.Kahn.Main
import Submission.Work.Deep.Nibble.FamWrap
import Submission.Work.Deep.Nibble.FamCongr
import Submission.Work.Deep.Nibble.WfamTail
import Submission.Work.Deep.Nibble.FamRound
import Submission.Work.Deep.Nibble.RelCover
import Submission.Work.Deep.Nibble.nibble_step
import Submission.Work.Deep.Nibble.nibble_iter
import Submission.Work.Deep.Nibble.nibble_main
import Submission.Work.Deep.Nibble.thinning

namespace Work.Deep.Nibble

/-!
# `RelCoverStatement`: status and proof route

`RelCoverStatement` (`RelCover.lean`) is the interface of the family nibble: an
`r`-uniform linear `(1 ± κ)D`-regular hypergraph with `D ≥ n^{1/100}` and a family
`𝓕` of at most `n^{2 log n}` vertex sets of size `≥ D^{1/20}` admits a matching
covering all but a `3κ`-fraction of every member of `𝓕`.

## The intended (family-nibble) route is blocked

`nibble_round2_fam` (`FamWrap.lean`) is proved, but it *cannot* be iterated from
`(1 ± κ)D`-regular data:

* its hypothesis on the input degrees is `|hd 𝓖 v - D| ≤ ε * D` with
  `ε ≤ θ / 100`, where the schedule needs `θ ≈ κ/(400 r log(1/κ)) ≪ κ`.  So the
  input accuracy `ε = κ` is *inadmissible* already for the first round;
* the per-round accuracy loss is geometric: `nibble_iter` prescribes
  `εs (j+1) = 8 * εs' j` with `εs' j ≥ 100 εs j`, i.e. a factor `≥ 800` per round
  over `T ≈ 4 log(1/κ)/θ` rounds, so an admissible start would need
  `εs 0 ≤ θ/(100 · 800^T)`;
* no regularisation step can repair this.  Sparsification keeps the *relative*
  degree spread (`d ↦ p·d`), and a spanning sub-hypergraph cannot improve it
  either: in a (nearly balanced) complete bipartite `K_{a,b}` every subgraph has
  `avg_A/avg_B = b/a`, so an `ε₀`-regular sub-hypergraph requires `ε₀ ≥ κ`-ish;
  `Work.Deep.Nibble.RegularisationStatement` is therefore false;
* and the iterative process itself can stall on legitimately `(1 ± κ)D`-regular
  data: in the bipartite / layered examples the low-degree part loses its
  residual degree faster than the level, so the residual hypergraph eventually
  has isolated vertices that no later round can cover.

## The route used instead: Kahn + EGJ's construction

The paper derives `cor:sparse_egj` from `thm:egj` (Ehard–Glock–Joos), and *that*
argument works for `(1 ± κ)D` data because the weight function `ω_S(e) = |e ∩ S|`
tracks the degree sum `Σ_{v ∈ S} d(v)`, so no regularisation is needed.  The
quantitative part of Molloy–Reed is *not* needed for our cruder target
(`(1 - 3κ)|S|` instead of `(1 - Δ^{-ε})`): the soft Kahn colouring (proved in
`Work.Deep.Kahn`, used through `ErdosFaberLovaszConjecture.kahn_colorable`)
suffices.

Step 1. Fix `α := κ/4`, `ε' := κ/8`, obtain `D₀ > 0` from `kahn_colorable`, and
choose `p := ⌈C (log(2n))² / κ²⌉ + 1` with `n₀` large enough that
`D ≥ n^{1/100}` dominates `D₀ p^{r-1}/κ`, `6 log(4np) p^{r-1}/ε'²`, and
`3p log(4|𝓕|p)`.

Step 2. Split `V` randomly into `p` parts; linearity makes the `(r-1)`-sets
`e ∖ {v}` (`e ∋ v`) pairwise disjoint, so the part-degree of `v` in its own part
is a sum of `d(v)` independent indicators with mean `d(v)/p^{r-1}`; Chernoff plus
the union bound gives a split `π` with all part-degrees within `(1 ± ε')` of that
mean and `|S ∩ π⁻¹(i)| ≤ 2|S|/p` for every part and every large `S ∈ 𝓕`
(`Work.Deep.Nibble.exists_balancedVertexPartition`).

Step 3. Each induced part `𝓗_i = {e ∈ 𝓗 | e ⊆ π⁻¹(i)}` is linear, `r`-uniform,
has maximum degree `D_i ≥ (1 - κ - ε')D/p^{r-1} ≥ D₀`, so Kahn colours it with
`c_i := ⌈(1+α)D_i⌉` colours; colour classes are matchings.

Step 4. Choose, independently in every part, a uniformly random colour.  The
covered set is `S ∩ V(M) = ⋃_i (S ∩ V(class_i))` and, since a uniformly random
class of part `i` covers `v ∈ S ∩ π⁻¹(i)` with probability `d_i(v)/c_i` exactly,
`E|S ∩ V(M)| = Σ_i (Σ_{v ∈ S ∩ π⁻¹(i)} d_i(v))/c_i ≥ (1 - 2.5κ)|S|`.

Step 5. Changing one colour changes `|S ∩ V(M)|` by at most `|S ∩ π⁻¹(i)|`, so
`Work.Deep.Reed.Prob.hoeffding_bounded_differences` (with
`Σ_i |S ∩ π⁻¹(i)|² ≤ 2|S|²/p` and `t := 0.4κ|S|`) bounds the failure probability
by `2 exp(-κ²p/8)`.  Summed over `𝓕` (of size `≤ n^{2 log n}`) this is `< 1`, so
some choice of colours gives `|S ∩ V(M)| ≥ (1 - 3κ)|S|` for every large `S`.

The delegations are:
* `Work.Deep.Nibble.exists_balancedVertexPartition` — Step 2;
* `Work.Deep.Nibble.relCoverStatement_of_Kahn` and
  `Work.Deep.Nibble.relCoverStatement_of_Kahn_alt` — the whole construction,
  intended to be assembled into the statement below.
-/

-- `RelCoverStatement` (RelCover.lean), by the route analysed above: Kahn's soft colouring
-- (proved in `Work.Deep.Kahn`) plus the EGJ-style random-partition construction.  The two
-- implications `Work.Deep.Nibble.relCoverStatement_of_Kahn[_alt] : KahnStatement →
-- RelCoverStatement` are delegated; the final line below is wired to the guided one as soon as
-- it lands (`Work.Deep.Kahn.kahnStatement` is proved, so the implication is unconditional).
--
-- Until then the statement is recorded here with the module documentation above.
theorem relCoverStatement : Work.Deep.Nibble.RelCoverStatement :=
  relCoverStatement_of_Kahn Work.Deep.Kahn.kahnStatement

end Work.Deep.Nibble
