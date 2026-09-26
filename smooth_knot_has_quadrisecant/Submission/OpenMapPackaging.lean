import Mathlib
import ChallengeDeps
import Submission.SecantSpace
import Submission.TorusCollinearity
import Submission.TrisecantClosed
import Submission.StrictZero
import Submission.TrisecantTransverse
import Submission.MiddleConvergence
import Submission.SheetAssembly
import Submission.OpenMapAssembly
import Submission.Torus1Chart

open LeanEval.KnotTheory.Quadrisecant
open Filter
open scoped Real Topology

noncomputable section

namespace LeanEval.KnotTheory.Quadrisecant

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000

/-!
# Milestone-2 step (iii), assembly item (c) — the topological packaging:
image openness of the class map on strict chart traces

With the analytic core (`OpenMapAssembly.lean`: strict data of class
sequences converging to a strict base class enter the chart, with
parameters converging to the preimage parameter), the open-map lemma of
the `TrisecantTransverse.lean` header is completed by a purely topological
argument:

1. **the band is first countable** (instance): `OpenMobius` is an open
   quotient of `OrderedPairs` by the swap
   (`isQuotientMap_mobiusCover`, `isOpenMap_mobiusCover`), so
   `Topology.IsQuotientMap.secondCountableTopology` makes it second
   countable (from the second countability of `OrderedPairs`), hence first
   countable;
2. **the sequence-⇒-neighbourhood lemma**
   (`exists_open_nhd_subset_of_seq_eventual`): in a first-countable space,
   a set `S` that contains the tail of every sequence (in a family `O`)
   converging to `y₀` contains an open neighbourhood of `y₀` (relative to
   `O`) — proven by contradiction with a decreasing countable basis
   (`Filter.exists_antitone_basis`) and choosing `yₙ` outside `S` in each
   basis element;
3. **per-point openness** (`open_nhd_at_chart_class`): at every strict
   chart point `x`, the class image of any open interval `J` around `x`
   contains the `O`-neighbourhood of the class `f(x)` produced by
   `classes_eventually_in_chart_trace` (OpenMapAssembly) + the bridge (2);
4. **the open-map lemma**
   (`zeroChordClass_image_open_on_strict_J`): on a strict open parameter
   interval `J` the class image `zeroChordClass h '' (chartLift c '' J)`
   is open in `O = trisecantSet r` — it is `O ∩ W` for `W` the union of
   the per-point neighbourhoods (with `f(J) ⊆ O` by strictness).

Together with the injectivity on strict traces
(`StrictZero.zeroChordClass_injective_near_base`, S82) this makes
`zeroChordClass` a local homeomorphism from strict chart data onto its
image in `O` — the local 1-manifold structure of `O` (Milestone-2 (iii)).

Everything here is elementary and verified (no axioms, no `sorry`).
-/

/-! ## 1. The band is first countable -/

/-- The open Möbius band of secants is second countable (it is an open
quotient of `OrderedPairs`, which is second countable as a subspace of the
product of two second-countable circles), hence first countable. -/
instance : SecondCountableTopology OpenMobius :=
  isQuotientMap_mobiusCover.secondCountableTopology isOpenMap_mobiusCover

/-! ## 2. The sequence-⇒-neighbourhood bridge -/

/-- **Sequence-⇒-neighbourhood.**  In a first-countable space, a set `S`
that contains the tail of every sequence in `O` converging to `y₀` contains
an open neighbourhood of `y₀` intersected with `O`.  Proof: if not, a
decreasing countable basis `Bₙ` of `𝓝 y₀` (`Filter.exists_antitone_basis`)
provides a sequence `yₙ ∈ O ∩ Bₙ ∖ S` converging to `y₀`, contradicting
the tail property. -/
lemma exists_open_nhd_subset_of_seq_eventual {Y : Type*} [TopologicalSpace Y]
    [FirstCountableTopology Y] {O S : Set Y} {y₀ : Y}
    (hseq : ∀ y : ℕ → Y, (∀ n : ℕ, y n ∈ O) → Tendsto y atTop (𝓝 y₀) →
      ∀ᶠ n in atTop, y n ∈ S) :
    ∃ W : Set Y, IsOpen W ∧ y₀ ∈ W ∧ O ∩ W ⊆ S := by
  classical
  rcases exists_antitone_basis (𝓝 y₀) with ⟨B, hB⟩
  by_contra hW
  have hW' : ∀ W ∈ 𝓝 y₀, ¬ O ∩ W ⊆ S := by
    intro W hWmem hsub
    rcases (mem_nhds_iff).1 hWmem with ⟨W₀, hW₀sub, hW₀open, hW₀y⟩
    exact hW ⟨W₀, hW₀open, hW₀y, fun z hz => hsub ⟨hz.1, hW₀sub hz.2⟩⟩
  let y : ℕ → Y := fun n => Classical.choose (Set.not_subset.mp (hW' (B n) (hB.mem n)))
  have hy_mem : ∀ n : ℕ, y n ∈ O ∧ y n ∈ B n ∧ y n ∉ S := by
    intro n
    have hspec := Classical.choose_spec (Set.not_subset.mp (hW' (B n) (hB.mem n)))
    -- hspec : y n ∈ O ∩ B n ∧ y n ∉ S
    exact ⟨hspec.1.1, hspec.1.2, hspec.2⟩
  have hyO : ∀ n : ℕ, y n ∈ O := fun n => (hy_mem n).1
  have hytend : Tendsto y atTop (𝓝 y₀) := by
    intro s hs
    rw [mem_map]
    rcases (hB.mem_iff).mp hs with ⟨n₀, hB₀⟩
    filter_upwards [eventually_ge_atTop n₀] with n hn
    exact hB₀ (hB.2 hn (hy_mem n).2.1)
  have hfin := hseq y hyO hytend
  rcases (eventually_atTop.mp hfin) with ⟨N, hN⟩
  exact (hy_mem N).2.2 (hN N le_rfl)

/-! ## 3. Per-point openness at strict chart points -/

/-- The chart preimage of the point `chartLift c x` (with its zero-set and
window memberships) is `x` itself. -/
lemma preimage_chartLift_of_point {r : ℝ → Space} {p : KnotParamTriple}
    (c : ZeroSet1Chart r p) (x : ChartInterval c.lo c.hi) :
    c.homeo.symm ⟨(chartLift c x : KnotParamTriple),
      ⟨(chartLift c x).2, (c.homeo x).2.2⟩⟩ = x := by
  have hval : (chartLift c x : KnotParamTriple) = (c.homeo x).1 := chartLift_val c x
  have hx : (⟨(chartLift c x : KnotParamTriple), ⟨(chartLift c x).2, (c.homeo x).2.2⟩⟩ :
      {q : KnotParamTriple // q ∈ trisecantZeroSet r ∧ q ∈ c.V}) = c.homeo x := by
    apply Subtype.ext
    exact hval
  rw [hx]
  exact c.homeo.symm_apply_apply x

/-- **Per-point openness of the class map.**  At every strict chart point
`x`, the class image of any open parameter interval `J` around `x` contains
a relative-open neighbourhood of the class `f(x)` inside `O`: every class
sequence in `O` converging to `f(x)` is eventually in the image
(`classes_eventually_in_chart_trace`), and in the first-countable band this
tail property upgrades to a neighbourhood
(`exists_open_nhd_subset_of_seq_eventual`). -/
lemma open_nhd_at_chart_class {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    {p : KnotParamTriple} {c : ZeroSet1Chart r p}
    (x : ChartInterval c.lo c.hi) (hstrict : strictZero r (chartLift c x))
    {J : Set (ChartInterval c.lo c.hi)} (hJ : IsOpen J) (hJx : x ∈ J) :
    ∃ W : Set OpenMobius, IsOpen W ∧ zeroChordClass h (chartLift c x) ∈ W ∧
      trisecantSet r ∩ W ⊆ zeroChordClass h '' (chartLift c '' J) := by
  have hzV : (chartLift c x : KnotParamTriple) ∈ c.V := by
    rw [chartLift_val]
    exact (c.homeo x).2.2
  have hpre : c.homeo.symm ⟨(chartLift c x : KnotParamTriple),
      ⟨(chartLift c x).2, hzV⟩⟩ = x := by
    simpa using preimage_chartLift_of_point c x
  have hseq : ∀ y : ℕ → OpenMobius, (∀ n : ℕ, y n ∈ trisecantSet r) →
      Tendsto y atTop (𝓝 (zeroChordClass h (chartLift c x))) →
      ∀ᶠ n in atTop, y n ∈ zeroChordClass h '' (chartLift c '' J) := by
    intro y hyO hy
    exact classes_eventually_in_chart_trace h hqf (p := p) (z₀ := chartLift c x) hstrict hgp
      (c := c) hzV hyO hy hJ (by simpa [hpre] using hJx)
  rcases exists_open_nhd_subset_of_seq_eventual (Y := OpenMobius)
      (O := trisecantSet r) (S := zeroChordClass h '' (chartLift c '' J))
      (y₀ := zeroChordClass h (chartLift c x)) hseq with ⟨W, hWopen, hWy, hsub⟩
  exact ⟨W, hWopen, hWy, hsub⟩

/-! ## 4. The open-map lemma -/

/-- **The class map is open onto its image on strict chart traces (the
open-map lemma, assembly (c)).**  For a `ZeroSet1Chart c` and an open
parameter interval `J` on which all chart points are *strict* data, the
class image `zeroChordClass h '' (chartLift c '' J)` is open in the
trisecant set `O = trisecantSet r`: it equals `O ∩ W` for the open
`W ⊆ OpenMobius` obtained as the union of the per-point relative-open
neighbourhoods of `open_nhd_at_chart_class` (with `f(J) ⊆ O` by
strictness, `strict_hasMiddleOnClass`). -/
theorem zeroChordClass_image_open_on_strict_J {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    {p : KnotParamTriple} {c : ZeroSet1Chart r p}
    {J : Set (ChartInterval c.lo c.hi)} (hJ : IsOpen J)
    (hstrictJ : ∀ x : ChartInterval c.lo c.hi, x ∈ J → strictZero r (chartLift c x)) :
    ∃ W : Set OpenMobius, IsOpen W ∧
      trisecantSet r ∩ W = zeroChordClass h '' (chartLift c '' J) := by
  classical
  have himageO : zeroChordClass h '' (chartLift c '' J) ⊆ trisecantSet r := by
    rintro y ⟨z, hzmem, rfl⟩
    rcases hzmem with ⟨x, hxJ, hzx⟩
    exact strict_hasMiddleOnClass h z (by simpa [hzx] using hstrictJ x hxJ)
  let Wfun : {x : ChartInterval c.lo c.hi // x ∈ J} → Set OpenMobius := fun xx =>
    Classical.choose (open_nhd_at_chart_class h hqf hgp xx.1 (hstrictJ xx.1 xx.2) hJ xx.2)
  have hWspec : ∀ xx : {x : ChartInterval c.lo c.hi // x ∈ J},
      IsOpen (Wfun xx) ∧ zeroChordClass h (chartLift c xx.1) ∈ Wfun xx ∧
        trisecantSet r ∩ Wfun xx ⊆ zeroChordClass h '' (chartLift c '' J) := by
    intro xx
    exact Classical.choose_spec (open_nhd_at_chart_class h hqf hgp xx.1 (hstrictJ xx.1 xx.2) hJ xx.2)
  let W : Set OpenMobius := ⋃ xx : {x : ChartInterval c.lo c.hi // x ∈ J}, Wfun xx
  refine ⟨W, ?_, ?_⟩
  · exact isOpen_iUnion (fun xx => (hWspec xx).1)
  · ext y
    constructor
    · rintro hy
      rcases hy with ⟨hyO, hyW⟩
      have hyWex : ∃ xx : {x : ChartInterval c.lo c.hi // x ∈ J}, y ∈ Wfun xx :=
        Set.mem_iUnion.mp hyW
      rcases hyWex with ⟨xx, hyWx⟩
      exact (hWspec xx).2.2 ⟨hyO, hyWx⟩
    · rintro hy
      rcases hy with ⟨z, hzmem, rfl⟩
      rcases hzmem with ⟨x, hxJ, hzx⟩
      constructor
      · exact himageO ⟨z, ⟨x, hxJ, hzx⟩, rfl⟩
      · rw [Set.mem_iUnion]
        refine ⟨⟨x, hxJ⟩, ?_⟩
        simpa [hzx] using (hWspec ⟨x, hxJ⟩).2.1

end LeanEval.KnotTheory.Quadrisecant
