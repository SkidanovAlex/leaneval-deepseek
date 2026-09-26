import Mathlib
import Submission.Work.Drive.trisecant_defs

/-!
# Local path-connectedness of the trisecant locus `O = trisecantSet r`

`Work.Drive.exists_pathConnected_trace_in_trisecantSet`: for a smooth knot `r` which is
quadrisecant-free and in transverse torus general position, every trisecant class `c ∈ O` and
every open neighbourhood `V ∋ c` of `c` in the band of secants `OpenMobius` admit an open
`W ⊆ V` with `c ∈ W` such that the trace `O ∩ W` is path connected.  Equivalently: `O` is
locally path connected at each of its points, with *arbitrarily small* traces.

The proof is the "shrinking the chart trace" argument.  `O` is locally the image of a chart of
strict zero-set data:

* `strictRep_of_trisecant` produces a strict zero-set representative `z₀` of `c`;
* `zeroSet1Chart_at_general_position` gives a chart `c` of `z₀` (a `ZeroSet1Chart`), whose
  parameter interval `ChartInterval c.lo c.hi` maps to the band by the continuous class map
  `x ↦ zeroChordClass h (chartLift c x)`;
* `exists_convex_strict_cell` produces a radius `δ` around the base parameter `xb` on which
  every chart point is strict;
* continuity of the class map at `xb` (whose value is `c ∈ V`) shrinks `δ` further to a radius
  `δ'` on which the class image is contained in `V`;
* `zeroChordClass_image_open_on_strict_J` (the open-map lemma) makes that class image — the
  image of a path-connected convex cell, hence path connected — the trace `O ∩ W₀` of an open
  `W₀`; intersecting with `V` (using that the class image already lies in `V`) gives the
  required open `W = W₀ ∩ V`.

The stronger "arbitrarily small" form is stated as
`Work.Drive.exists_pathConnected_trace_subset_of_isOpen` and the requested statement is an
immediate consequence of it (the required `W` is the witness of that lemma).
-/

open LeanEval.KnotTheory.Quadrisecant
open Set
open scoped Real Topology

noncomputable section

namespace Work.Drive

set_option maxHeartbeats 800000

/-- **Arbitrarily small open path-connected trace neighbourhoods of `O`.**

For a smooth knot `r` which is quadrisecant-free and in transverse torus general position,
every trisecant class `c₀ ∈ O = trisecantSet r` and every open `V ∋ c₀` in the band admit a
path-connected set `U ⊆ O` with `c₀ ∈ U ⊆ V` which is the trace of an open `W ⊆ V`:
`trisecantSet r ∩ W = U`.  (In particular `O` is locally path connected at `c₀`, with traces
inside any prescribed neighbourhood.) -/
lemma exists_pathConnected_trace_subset_of_isOpen {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (c₀ : OpenMobius) (hc₀ : c₀ ∈ trisecantSet r)
    {V : Set OpenMobius} (hV : IsOpen V) (hc₀V : c₀ ∈ V) :
    ∃ U : Set OpenMobius, IsPathConnected U ∧ c₀ ∈ U ∧ U ⊆ trisecantSet r ∧ U ⊆ V ∧
      ∃ W : Set OpenMobius, IsOpen W ∧ W ⊆ V ∧ trisecantSet r ∩ W = U := by
  have hGP : TorusGeneralPosition r := torusTransverse_monotone hgp
  classical
  -- a strict zero-set representative of `c₀` and a chart of it
  rcases strictRep_of_trisecant h hc₀ with ⟨z₀, hz₀str, hz₀cls⟩
  rcases zeroSet1Chart_at_general_position h hGP (z₀ : KnotParamTriple) z₀.2 with ⟨c⟩
  let xb : ChartInterval c.lo c.hi := ⟨c.x₀, c.x₀_mem⟩
  have hbase_eq : chartLift c xb = z₀ := by
    simpa [xb] using (chartLift_base_eq (c := c) (z := z₀))
  have hbstr : strictZero r (chartLift c xb) := by simpa [hbase_eq] using hz₀str
  -- a strict convex cell around the base parameter
  rcases exists_convex_strict_cell h (x := xb) hbstr with ⟨δ, hδ0, hδlo, hδhi, hδstr⟩
  -- the class map on the chart is continuous and sends the base parameter to `c₀ ∈ V`
  have hf : Continuous (fun x : ChartInterval c.lo c.hi => zeroChordClass h (chartLift c x)) :=
    (continuous_zeroChordClass h).comp (continuous_chartLift c)
  have hmem : zeroChordClass h (chartLift c xb) ∈ V := by rw [hbase_eq, hz₀cls]; exact hc₀V
  have hnhds : (fun x : ChartInterval c.lo c.hi => zeroChordClass h (chartLift c x)) ⁻¹' V ∈ 𝓝 xb :=
    hf.continuousAt (hV.mem_nhds hmem)
  rcases Metric.mem_nhds_iff.mp hnhds with ⟨ε, hε0, hball⟩
  -- shrink the radius so that the class image is inside `V` and still strict
  let δ' : ℝ := min ε δ / 2
  have hminpos : 0 < min ε δ := lt_min hε0 hδ0
  have hδ'0 : 0 < δ' := by dsimp [δ']; positivity
  have hδ'ε : δ' ≤ ε := by
    dsimp [δ']
    calc min ε δ / 2 ≤ min ε δ := le_of_lt (half_lt_self hminpos)
      _ ≤ ε := min_le_left ε δ
  have hδ'δ : δ' ≤ δ := by
    dsimp [δ']
    calc min ε δ / 2 ≤ min ε δ := le_of_lt (half_lt_self hminpos)
      _ ≤ δ := min_le_right ε δ
  let J' : Set (ChartInterval c.lo c.hi) :=
    {x | (x : ℝ) ∈ Set.Ioo ((xb : ℝ) - δ') ((xb : ℝ) + δ')}
  have hJ'open : IsOpen J' := by
    dsimp [J']
    exact isOpen_Ioo.preimage continuous_subtype_val
  have hJ'path : IsPathConnected J' := by
    have hx₀ : (xb : ℝ) ∈ Set.Ioo c.lo c.hi := c.x₀_mem
    have := isPathConnected_convexCell (lo := c.lo) (hi := c.hi) (x₀ := (xb : ℝ)) hx₀
      (δ := δ') hδ'0
    simpa [J'] using this
  have hJ'strict : ∀ x ∈ J', strictZero r (chartLift c x) := by
    intro x hx
    apply hδstr x
    exact ⟨by linarith [hx.1, hδ'δ], by linarith [hx.2, hδ'δ]⟩
  have hxbJ' : xb ∈ J' := by
    dsimp [J']
    constructor <;> linarith
  -- the class image of the small cell: path connected, contains `c₀`, and lies in `V`
  let U : Set OpenMobius := zeroChordClass h '' (chartLift c '' J')
  have hUpath : IsPathConnected U := by
    have h1 : IsPathConnected (chartLift c '' J') := hJ'path.image (continuous_chartLift c)
    dsimp [U]
    exact h1.image (continuous_zeroChordClass h)
  have hc₀U : c₀ ∈ U := by
    dsimp [U]
    refine ⟨chartLift c xb, ⟨xb, hxbJ', rfl⟩, ?_⟩
    rw [hbase_eq, hz₀cls]
  have hUV : U ⊆ V := by
    rintro y ⟨z, hz, rfl⟩
    rcases hz with ⟨x, hxJ', rfl⟩
    refine hball ?_
    rw [Metric.mem_ball]
    change dist (x : ℝ) (xb : ℝ) < ε
    rw [Real.dist_eq, abs_lt]
    exact ⟨by linarith [hxJ'.1, hδ'ε], by linarith [hxJ'.2, hδ'ε]⟩
  -- openness in `O` of the small class image, and the trace identity
  rcases zeroChordClass_image_open_on_strict_J h hqf hgp (c := c) (J := J') hJ'open hJ'strict with
    ⟨W₀, hW₀open, hW₀eq⟩
  have hUsub : U ⊆ trisecantSet r := by
    dsimp [U]
    rw [← hW₀eq]
    intro y hy; exact hy.1
  refine ⟨U, hUpath, hc₀U, hUsub, hUV, W₀ ∩ V, hW₀open.inter hV, Set.inter_subset_right, ?_⟩
  -- `O ∩ (W₀ ∩ V) = (O ∩ W₀) ∩ V = U ∩ V = U` since `U ⊆ V`
  calc trisecantSet r ∩ (W₀ ∩ V) = (trisecantSet r ∩ W₀) ∩ V := (Set.inter_assoc _ _ _).symm
    _ = U ∩ V := by rw [hW₀eq]
    _ = U := Set.inter_eq_left.mpr hUV

/-- **Local path-connectedness of the trisecant locus (open-trace form).**

For a smooth knot `r` which is quadrisecant-free and in transverse torus general position,
every trisecant class `c ∈ O = trisecantSet r` and every open neighbourhood `V ∋ c` in the
band of secants admit an open `W` with `c ∈ W ⊆ V` such that the trace `O ∩ W` is path
connected. -/
theorem exists_pathConnected_trace_in_trisecantSet {r : ℝ → LeanEval.KnotTheory.Quadrisecant.Space}
    (h : LeanEval.KnotTheory.Quadrisecant.IsSmoothKnot r)
    (hqf : LeanEval.KnotTheory.Quadrisecant.QuadrisecantFree r)
    (hgp : LeanEval.KnotTheory.Quadrisecant.TorusGeneralPositionTransverse r)
    {c : LeanEval.KnotTheory.Quadrisecant.OpenMobius}
    (hc : c ∈ LeanEval.KnotTheory.Quadrisecant.trisecantSet r)
    {V : Set LeanEval.KnotTheory.Quadrisecant.OpenMobius}
    (hV : IsOpen V) (hcV : c ∈ V) :
    ∃ W : Set LeanEval.KnotTheory.Quadrisecant.OpenMobius, IsOpen W ∧ c ∈ W ∧ W ⊆ V ∧
      IsPathConnected (LeanEval.KnotTheory.Quadrisecant.trisecantSet r ∩ W) := by
  rcases exists_pathConnected_trace_subset_of_isOpen h hqf hgp c hc hV hcV with
    ⟨U, hUpath, hcU, -, -, W, hWopen, hWV, hWeq⟩
  refine ⟨W, hWopen, ?_, hWV, ?_⟩
  · rw [← hWeq] at hcU
    exact hcU.2
  · rw [hWeq]
    exact hUpath

end Work.Drive
