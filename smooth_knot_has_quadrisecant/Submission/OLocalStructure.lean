import Mathlib
import ChallengeDeps
import Submission.Helpers
import Submission.KnotMap
import Submission.TorusCollinearity
import Submission.SecantSpace
import Submission.TrisecantLocus
import Submission.TrisecantClosed
import Submission.TrisecantStructure
import Submission.StrictZero
import Submission.TrisecantTransverse
import Submission.MiddleConvergence
import Submission.OpenMapAssembly
import Submission.OpenMapPackaging
import Submission.Torus1Chart

open LeanEval.KnotTheory.Quadrisecant
open Filter
open scoped Real Topology unitInterval

noncomputable section

namespace LeanEval.KnotTheory.Quadrisecant

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000

/-!
# Milestone-2 (iv) / Layer C opener — strict representatives and
path-connected trace neighbourhoods of `O`

Milestone-2 (iii) (S86–S92) established the *open-map lemma*: on strict
chart traces the class map `zeroChordClass` is open onto its image in the
trisecant set `O = trisecantSet r`, and (S82) injective on strict
injectivity regions — `O` is locally modelled on open intervals.  This
module turns that into the local *path* vocabulary of `O` that the
component/winding analysis (Milestone-2 (iv), Layer C) consumes:

1. **strict representatives** (`strictRep_of_trisecant`): every class
   `c ∈ O` is the class of a strict zero-set data point `z`
   (`strictZero r z`, `zeroChordClass h z = c`) — take any representative
   chord `p` over `c` and attach the canonical strict middle
   (`classMiddle_middle_on_rep`, `zeroSetPoint_of_classMiddle_on_rep`);
2. **continuity of the class map** (`continuous_chordOfZeroSet`,
   `continuous_zeroChordClass`): the canonical chord of a zero-set point,
   and hence the class map `z ↦ zeroChordClass h z`, are continuous (the
   class is `mobiusCover` of the chord);
3. **interval paths** (`isPathConnected_univ_chartInterval`): the
   parameter interval of a chart (an open interval of the real line) is
   path connected — straight-line paths stay inside by convexity — so the
   continuous class map carries it to a path-connected trace;
4. **open path-connected trace neighbourhoods**
   (`isPathConnected_convexCell`, `exists_convex_strict_cell`,
   `chartLift_base_eq`, `exists_open_pathConnected_nhds_in_O`): every
   class `c₀ ∈ O` lies in an open (relative to `O`), path connected subset
   of `O` — the class image of a small strict convex chart cell (open in
   `O` by the open-map lemma, path connected as a continuous image of the
   cell);
5. **open components** (`isPathConnected_lift_trisecant`,
   `isOpen_component_in_O`): lifting the path-connected neighbourhoods into
   the subtype and running the standard connected-component argument, the
   connected components of the subspace `O` are open (each component
   contains an open neighbourhood of each of its points).

Everything here is elementary and verified (no axioms, no `sorry`).  NEXT
(recorded in ROADMAP S95): the interval/arc/circle classification of the
components of `O` and the once/twice-winding dichotomy feeding the
winding contradictions, then Layer C, Layer B, Routes A2/A3, Layer D.
-/

/-! ## 1. Strict representatives of trisecant classes -/

/-- Every trisecant class is the class of a strict zero-set data point
(attach the canonical strict middle of the class to any of its chord
representatives). -/
lemma strictRep_of_trisecant {r : ℝ → Space} (h : IsSmoothKnot r) {c : OpenMobius}
    (hc : c ∈ trisecantSet r) :
    ∃ z : ZeroSetPoint r, strictZero r z ∧ zeroChordClass h z = c := by
  rcases (mem_MiddlePointsOnClass_iff r c (classMiddle r c hc)).mp
      (classMiddle_mem_middleSet r c hc) with ⟨p, hp, hm⟩
  let z : ZeroSetPoint r := ⟨(p.1.1, (p.1.2, classMiddle r c hc)),
    zeroSetPoint_of_classMiddle_on_rep h c hc p hp⟩
  refine ⟨z, ?_, ?_⟩
  · change IsMiddleOnOpenChord r p.1.1 p.1.2 (classMiddle r c hc)
    simpa [IsMiddleOnOpenChord, IsMiddleOnChord] using (classMiddle_middle_on_rep c hc p hp)
  · have hcl := zeroChordClass_eq_mobiusCover_of_triple h (p.1.1, (p.1.2, classMiddle r c hc))
      (zeroSetPoint_of_classMiddle_on_rep h c hc p hp)
    rw [hcl]
    have hchord : (⟨((p.1.1, (p.1.2, classMiddle r c hc)).1,
        (p.1.1, (p.1.2, classMiddle r c hc)).2.1),
          ((TorusOffDiag_iff_params h (p.1.1, (p.1.2, classMiddle r c hc))).mp
            ((mem_trisecantZeroSet_iff (p.1.1, (p.1.2, classMiddle r c hc))).mp
              (zeroSetPoint_of_classMiddle_on_rep h c hc p hp)).2).1⟩ : OrderedPairs) = p := by
      apply Subtype.ext
      rfl
    rw [hchord]
    exact hp

/-! ## 2. Continuity of the canonical chord and of the class map -/

/-- The canonical chord of a zero-set point depends continuously on the
point. -/
lemma continuous_chordOfZeroSet {r : ℝ → Space} (h : IsSmoothKnot r) :
    Continuous (chordOfZeroSet h : ZeroSetPoint r → OrderedPairs) := by
  have hc1 : Continuous (fun z : ZeroSetPoint r => ((z : KnotParamTriple).1)) :=
    continuous_fst.comp continuous_subtype_val
  have hc2 : Continuous (fun z : ZeroSetPoint r => ((z : KnotParamTriple).2.1)) :=
    continuous_fst.comp (continuous_snd.comp continuous_subtype_val)
  have hpair : Continuous (fun z : ZeroSetPoint r =>
      (((z : KnotParamTriple).1), ((z : KnotParamTriple).2.1))) := hc1.prodMk hc2
  have hcont : Continuous (fun z : ZeroSetPoint r =>
      (⟨(((z : KnotParamTriple).1), ((z : KnotParamTriple).2.1)),
        zeroChord_endpoints_ne h z⟩ : OrderedPairs)) :=
    Continuous.subtype_mk hpair (fun z => zeroChord_endpoints_ne h z)
  have hfun : chordOfZeroSet h = (fun z : ZeroSetPoint r =>
      (⟨(((z : KnotParamTriple).1), ((z : KnotParamTriple).2.1)),
        zeroChord_endpoints_ne h z⟩ : OrderedPairs)) := by
    funext z
    rfl
  rw [hfun]
  exact hcont

/-- The class map on the zero set is continuous (it is the covering map
`mobiusCover` applied to the continuous canonical chord). -/
lemma continuous_zeroChordClass {r : ℝ → Space} (h : IsSmoothKnot r) :
    Continuous (zeroChordClass h : ZeroSetPoint r → OpenMobius) := by
  change Continuous (fun z : ZeroSetPoint r => mobiusCover (chordOfZeroSet h z))
  exact continuous_mobiusCover.comp (continuous_chordOfZeroSet h)

/-! ## 3. Interval paths in chart parameter space -/

/-- The parameter interval of a chart (an open interval of the real line,
path-connected) is path connected: two parameters are joined by the
straight-line path, which stays inside the interval by convexity. -/
lemma isPathConnected_univ_chartInterval {lo hi : ℝ} (h : lo < hi) :
    IsPathConnected (Set.univ : Set (ChartInterval lo hi)) := by
  rw [isPathConnected_iff]
  constructor
  · -- Nonempty: the midpoint of the interval is a parameter
    exact ⟨⟨(lo + hi) / 2, by constructor <;> linarith⟩, trivial⟩
  · intro x hx y hy
    let γ : Path x y := Path.mk
      ⟨fun t : I => ⟨AffineMap.lineMap (x : ℝ) (y : ℝ) (t : ℝ), by
          exact Convex.lineMap_mem (convex_Ioo lo hi) ⟨x.2.1, x.2.2⟩ ⟨y.2.1, y.2.2⟩ t.2⟩,
        by fun_prop⟩
      (by
        apply Subtype.ext
        simp)
      (by
        apply Subtype.ext
        simp)
    exact ⟨γ, fun t => trivial⟩

/-! ## 4. Open path-connected trace neighbourhoods in `O` -/

/-- A convex parameter cell `{x | x ∈ Ioo (x₀−δ) (x₀+δ)}` of a chart is
path connected (straight-line paths stay inside the convex cell). -/
lemma isPathConnected_convexCell {lo hi : ℝ} {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Ioo lo hi)
    {δ : ℝ} (hδ0 : 0 < δ) : IsPathConnected {x : ChartInterval lo hi | (x : ℝ) ∈ Set.Ioo (x₀ - δ) (x₀ + δ)} := by
  rw [isPathConnected_iff]
  constructor
  · exact ⟨⟨x₀, ⟨hx₀.1, hx₀.2⟩⟩, by dsimp; constructor <;> linarith⟩
  · intro x hx y hy
    let γ : Path x y := Path.mk
      ⟨fun t : I => ⟨AffineMap.lineMap (x : ℝ) (y : ℝ) (t : ℝ), by
          exact Convex.lineMap_mem (convex_Ioo lo hi) ⟨x.2.1, x.2.2⟩ ⟨y.2.1, y.2.2⟩ t.2⟩,
        by fun_prop⟩
      (by
        apply Subtype.ext
        simp)
      (by
        apply Subtype.ext
        simp)
    refine ⟨γ, ?_⟩
    intro t
    dsimp [γ]
    exact Convex.lineMap_mem (convex_Ioo (x₀ - δ) (x₀ + δ)) hx hy t.2

/-- The strict-open chart region contains a convex cell around any strict
point: a positive-radius cell around the parameter on which every chart
point is strict. -/
lemma exists_convex_strict_cell {r : ℝ → Space} (h : IsSmoothKnot r)
    {p : KnotParamTriple} {c : ZeroSet1Chart r p} {x : ChartInterval c.lo c.hi}
    (hstrict : strictZero r (chartLift c x)) :
    ∃ δ : ℝ, 0 < δ ∧ c.lo < (x : ℝ) - δ ∧ (x : ℝ) + δ < c.hi ∧
      (∀ y : ChartInterval c.lo c.hi,
        (y : ℝ) ∈ Set.Ioo ((x : ℝ) - δ) ((x : ℝ) + δ) → strictZero r (chartLift c y)) := by
  let S : Set (ChartInterval c.lo c.hi) := {y | strictZero r (chartLift c y)}
  have hSopen : IsOpen S := by
    dsimp [S]
    exact (isOpen_strictZero h).preimage (continuous_chartLift c)
  have hxS : x ∈ S := by
    dsimp [S]
    exact hstrict
  have hnhd : S ∈ 𝓝 x := hSopen.mem_nhds hxS
  rcases (Metric.mem_nhds_iff.mp hnhd) with ⟨ε, hε0, hball⟩
  let δ : ℝ := min ε (min ((x : ℝ) - c.lo) (c.hi - (x : ℝ))) / 2
  have hδ0 : 0 < δ := by
    dsimp [δ]
    exact div_pos (lt_min hε0 (lt_min (sub_pos.mpr x.2.1) (sub_pos.mpr x.2.2))) (by norm_num)
  refine ⟨δ, hδ0, ?_, ?_, ?_⟩
  · dsimp [δ]
    have hm : 0 < min ε (min ((x : ℝ) - c.lo) (c.hi - (x : ℝ))) := by
      exact lt_min hε0 (lt_min (sub_pos.mpr x.2.1) (sub_pos.mpr x.2.2))
    have hle : min ε (min ((x : ℝ) - c.lo) (c.hi - (x : ℝ))) < 2 * ((x : ℝ) - c.lo) := by
      have h1 : min ε (min ((x : ℝ) - c.lo) (c.hi - (x : ℝ))) ≤ (x : ℝ) - c.lo :=
        (min_le_right ε (min ((x : ℝ) - c.lo) (c.hi - (x : ℝ)))).trans
          (min_le_left ((x : ℝ) - c.lo) (c.hi - (x : ℝ)))
      have hpos : 0 < (x : ℝ) - c.lo := sub_pos.mpr x.2.1
      nlinarith
    linarith
  · dsimp [δ]
    have hm : 0 < min ε (min ((x : ℝ) - c.lo) (c.hi - (x : ℝ))) := by
      exact lt_min hε0 (lt_min (sub_pos.mpr x.2.1) (sub_pos.mpr x.2.2))
    have hle : min ε (min ((x : ℝ) - c.lo) (c.hi - (x : ℝ))) < 2 * (c.hi - (x : ℝ)) := by
      have h1 : min ε (min ((x : ℝ) - c.lo) (c.hi - (x : ℝ))) ≤ c.hi - (x : ℝ) :=
        (min_le_right ε (min ((x : ℝ) - c.lo) (c.hi - (x : ℝ)))).trans
          (min_le_right ((x : ℝ) - c.lo) (c.hi - (x : ℝ)))
      have hpos : 0 < c.hi - (x : ℝ) := sub_pos.mpr x.2.2
      nlinarith
    linarith
  · intro y hy
    -- y is inside the metric ball around x (δ ≤ ε), so y ∈ S
    have hδe : δ ≤ ε := by
      dsimp [δ]
      have hpos2 : 0 < min ((x : ℝ) - c.lo) (c.hi - (x : ℝ)) :=
        lt_min (sub_pos.mpr x.2.1) (sub_pos.mpr x.2.2)
      have hm : 0 < min ε (min ((x : ℝ) - c.lo) (c.hi - (x : ℝ))) := lt_min hε0 hpos2
      calc
        min ε (min ((x : ℝ) - c.lo) (c.hi - (x : ℝ))) / 2
            ≤ min ε (min ((x : ℝ) - c.lo) (c.hi - (x : ℝ))) := le_of_lt (half_lt_self hm)
        _ ≤ ε := min_le_left ε (min ((x : ℝ) - c.lo) (c.hi - (x : ℝ)))
    have hyball : y ∈ Metric.ball x ε := by
      rw [Metric.mem_ball]
      have hsub : dist y x < ε := by
        change dist (y : ℝ) (x : ℝ) < ε
        rw [Real.dist_eq, abs_lt]
        constructor <;> linarith [hy.1, hy.2, hδe]
      exact hsub
    exact hball hyball

/-- The chart lift at the base parameter of a chart centred at `z` is `z`
itself. -/
lemma chartLift_base_eq {r : ℝ → Space} {z : ZeroSetPoint r}
    (c : ZeroSet1Chart r (z : KnotParamTriple)) : chartLift c ⟨c.x₀, c.x₀_mem⟩ = z := by
  apply Subtype.ext
  rw [chartLift_val]
  exact c.base

/-- **Open path-connected trace neighbourhoods in `O` (step (4)).**  For a
smooth knot under `QuadrisecantFree` and transverse torus general position,
every trisecant class `c₀ ∈ O` lies in an open (relative to `O`), path
connected subset of `O` — the class image of a small strict convex chart
cell.  Openness is the open-map lemma
(`OpenMapPackaging.zeroChordClass_image_open_on_strict_J`), path
connectedness is the continuous image of the path-connected cell
(`isPathConnected_convexCell` + continuity of the class map), and the cell
exists around a strict representative of `c₀` (`strictRep_of_trisecant`,
`exists_convex_strict_cell`, charts from the general position). -/
theorem exists_open_pathConnected_nhds_in_O {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (c₀ : OpenMobius) (hc₀ : c₀ ∈ trisecantSet r) :
    ∃ U : Set OpenMobius, IsPathConnected U ∧ c₀ ∈ U ∧ U ⊆ trisecantSet r ∧
      ∃ W : Set OpenMobius, IsOpen W ∧ trisecantSet r ∩ W = U := by
  classical
  rcases strictRep_of_trisecant h hc₀ with ⟨z₀, hz₀str, hz₀cls⟩
  have hGP : TorusGeneralPosition r := torusTransverse_monotone hgp
  rcases zeroSet1Chart_at_general_position h hGP (z₀ : KnotParamTriple) z₀.2 with ⟨c⟩
  let xb : ChartInterval c.lo c.hi := ⟨c.x₀, c.x₀_mem⟩
  have hbase_eq : chartLift c xb = z₀ := by
    simpa [xb] using (chartLift_base_eq (c := c) (z := z₀))
  have hbstr : strictZero r (chartLift c xb) := by
    simpa [hbase_eq] using hz₀str
  rcases exists_convex_strict_cell h (x := xb) hbstr with ⟨δ, hδ0, hδlo, hδhi, hδstr⟩
  let J : Set (ChartInterval c.lo c.hi) := {x | (x : ℝ) ∈ Set.Ioo ((xb : ℝ) - δ) ((xb : ℝ) + δ)}
  have hJopen : IsOpen J := by
    dsimp [J]
    exact isOpen_Ioo.preimage continuous_subtype_val
  have hJpath : IsPathConnected J := by
    dsimp [J]
    exact isPathConnected_convexCell (hx₀ := (by simpa [xb] using c.x₀_mem)) hδ0
  have hf : Continuous (fun x : ChartInterval c.lo c.hi => zeroChordClass h (chartLift c x)) :=
    (continuous_zeroChordClass h).comp (continuous_chartLift c)
  let U : Set OpenMobius := zeroChordClass h '' (chartLift c '' J)
  have hUpath : IsPathConnected U := by
    have h1 : IsPathConnected (chartLift c '' J) := hJpath.image (continuous_chartLift c)
    dsimp [U]
    exact h1.image (continuous_zeroChordClass h)
  rcases zeroChordClass_image_open_on_strict_J h hqf hgp (c := c) hJopen
    (fun x hx => hδstr x hx) with ⟨W, hWopen, hWeq⟩
  have hJxb : xb ∈ J := by
    dsimp [J, xb]
    constructor <;> linarith
  have hc₀U : c₀ ∈ U := by
    dsimp [U]
    refine ⟨chartLift c xb, ⟨xb, hJxb, rfl⟩, ?_⟩
    calc
      zeroChordClass h (chartLift c xb) = zeroChordClass h z₀ := by rw [hbase_eq]
      _ = c₀ := hz₀cls
  refine ⟨U, hUpath, hc₀U, ?_, W, hWopen, ?_⟩
  · -- U ⊆ O: U = trisecantSet r ∩ W
    dsimp [U]
    rw [← hWeq]
    intro y hy
    exact hy.1
  · exact hWeq

/-! ## 5. The connected components of `O` are open -/

/-- A path-connected subset of `O` lifts to a path-connected subset of the
trisecant subtype (its preimage under the value map into the band). -/
lemma isPathConnected_lift_trisecant {r : ℝ → Space} {UO : Set OpenMobius}
    (hUO : UO ⊆ trisecantSet r) (hpath : IsPathConnected UO) :
    IsPathConnected {s : {c : OpenMobius // c ∈ trisecantSet r} |
      (s : OpenMobius) ∈ UO} := by
  classical
  rw [isPathConnected_iff]
  constructor
  · rcases (isPathConnected_iff.mp hpath).1 with ⟨u, hu⟩
    exact ⟨⟨u, hUO hu⟩, hu⟩
  · intro x hx y hy
    rcases (isPathConnected_iff.mp hpath).2 (x : OpenMobius) hx (y : OpenMobius) hy with ⟨γ, hγ⟩
    let γS : Path x y := Path.mk
      ⟨fun t : I => (⟨γ t, hUO (hγ t)⟩ : {c : OpenMobius // c ∈ trisecantSet r}), by
        exact Continuous.subtype_mk (f := fun t : I => (γ t : OpenMobius))
          γ.toContinuousMap.continuous (fun t => hUO (hγ t))⟩
      (by
        apply Subtype.ext
        exact γ.source)
      (by
        apply Subtype.ext
        exact γ.target)
    refine ⟨γS, ?_⟩
    intro t
    change (γS t : OpenMobius) ∈ UO
    dsimp [γS]
    exact hγ t

/-- **The connected components of `O` are open (step (5)).**  The subspace
`O = trisecantSet r` of the band has the property that every point carries
an open path connected neighbourhood (`exists_open_pathConnected_nhds_in_O`),
lifted into the subtype (`isPathConnected_lift_trisecant`); hence each
connected component is open (a connected neighbourhood of a point of a
component is contained in the component). -/
theorem isOpen_component_in_O {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (c₀ : {c : OpenMobius // c ∈ trisecantSet r}) :
    IsOpen (connectedComponent c₀) := by
  rw [isOpen_iff_mem_nhds]
  intro a haC
  rcases exists_open_pathConnected_nhds_in_O h hqf hgp (a : OpenMobius) a.2 with
    ⟨UO, hUpath, haUO, hUOsub, W, hWopen, hWeq⟩
  let S : Type := {c : OpenMobius // c ∈ trisecantSet r}
  let U : Set S := {s : S | (s : OpenMobius) ∈ UO}
  have hUopen : IsOpen U := by
    have heq : U = (fun s : S => (s : OpenMobius)) ⁻¹' W := by
      ext s
      constructor
      · intro hs
        have hw : (s : OpenMobius) ∈ trisecantSet r ∩ W := by
          rw [hWeq]
          exact hs
        exact hw.2
      · intro hs
        dsimp [U]
        exact (by
          rw [← hWeq]
          exact ⟨s.2, hs⟩)
    rw [heq]
    exact hWopen.preimage continuous_subtype_val
  have hUpathS : IsPathConnected U := by
    simpa [U] using (isPathConnected_lift_trisecant hUOsub hUpath)
  have hPreU : IsPreconnected U := hUpathS.isConnected.isPreconnected
  have haU : a ∈ U := by
    dsimp [U]
    exact haUO
  have hUsub : U ⊆ connectedComponent c₀ := by
    intro s hs
    have hsComp : s ∈ connectedComponent a :=
      hPreU.subset_connectedComponent haU hs
    -- components are equal for points in one component
    have heq0 : connectedComponent c₀ = connectedComponent a :=
      connectedComponent_eq (x := c₀) (y := a) haC
    simpa [heq0] using hsComp
  have hUin : U ∈ 𝓝 a := hUopen.mem_nhds haU
  exact mem_of_superset hUin hUsub

end LeanEval.KnotTheory.Quadrisecant
