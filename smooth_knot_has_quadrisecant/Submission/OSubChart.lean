import Mathlib
import ChallengeDeps
import Submission.OLocalStructure
import Submission.OpenMapPackaging
import Submission.StrictZero
import Submission.ComponentPath
import Submission.Torus1Chart

open LeanEval.KnotTheory.Quadrisecant
open Filter
open scoped Real Topology unitInterval

noncomputable section

namespace LeanEval.KnotTheory.Quadrisecant

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000

/-!
# Milestone-2 (iv) / Layer C opener — interval charts of the trisecant set
`O` (the local 1-manifold structure of the components)

`OLocalStructure.lean` (S93–S95) proved that every trisecant class lies in
an open path-connected neighbourhood of `O = trisecantSet r`, and that the
connected components of `O` are open and path-connected (`ComponentPath`,
S96).  This module completes the *interval chart* half of the local
1-manifold structure of `O`, the remaining step-(6) brick (a):

1. **the coordinate relabelling** (`cellIntervalHomeo`): an open real
   interval `(lo,hi)` whose endpoints lie strictly inside the chart
   interval `(c.lo,c.hi)` is homeomorphic to the cell
   `{x : ChartInterval c.lo c.hi | (x : ℝ) ∈ Ioo lo hi}` of the chart
   parameter space (the two are the same set of reals, up to the chart
   membership proofs);
2. **the bundled chart structure** (`OSub1Chart r c₀`): a chart of `O` at
   the class `c₀ ∈ O` carries an open real interval `(lo,hi) ∋ x₀`, an
   open band set `W` (`(c₀ : OpenMobius) ∈ W`), and a homeomorphism of the
   interval onto the open trace
   `{c : OSub r | (c : OpenMobius) ∈ W}` of `O` in `W`, sending `x₀` to
   `c₀`;
3. **the chart theorem** (`osub1Chart_at_class`): under
   `QuadrisecantFree` + `TorusGeneralPositionTransverse`, every trisecant
   class `c₀ ∈ O` carries an `OSub1Chart` — the class map
   `x ↦ zeroChordClass h (chartLift c x)` on a small strict convex cell
   around a strict representative of `c₀` (shrunken to lie inside the
   strict region `exists_convex_strict_cell`, the injectivity region
   `zeroChordClass_injective_near_base`, and the chart window) is an
   injective continuous open map whose value image is the open trace
   `O ∩ W` (`zeroChordClass_image_open_on_strict_J`): the assembled
   `Equiv.ofBijective` + `toHomeomorphOfContinuousOpen`.

This is the statement that the components of `O` are 1-dimensional
topological manifolds (Hausdorff — `OpenMobius` is `T2`; second countable —
`OpenMapPackaging` provides the instance): the arc/circle classification of
the components (step-(6) brick (b)) and the once/twice-winding dichotomy
(brick (c), consuming the monodromy parity of `ComponentPath`) are the
next gluing stages.

Everything here is elementary and verified (no axioms, no `sorry`).
-/

/-- A chart of the trisecant set `O` (Kuperberg's set) at a class `c₀`:
an open real interval `(lo,hi) ∋ x₀` homeomorphic to the open trace
`{c : OSub r | (c : OpenMobius) ∈ W}` of an open band set `W`, sending
`x₀` to `c₀`.  This is the interval-chart half of the local 1-manifold
structure of `O`: together with the openness (open-map lemma,
`OpenMapPackaging.zeroChordClass_image_open_on_strict_J`) and the
injectivity (`StrictZero.zeroChordClass_injective_near_base`) of the class
map on strict chart cells it exhibits an open neighbourhood of every
trisecant class homeomorphic to an open interval of `ℝ`. -/
structure OSub1Chart (r : ℝ → Space) (c₀ : OSub r) where
  lo : ℝ
  hi : ℝ
  x₀ : ℝ
  x₀_mem : x₀ ∈ Set.Ioo lo hi
  W : Set OpenMobius
  W_open : IsOpen W
  c₀_mem : (c₀ : OpenMobius) ∈ W
  homeo : ChartInterval lo hi ≃ₜ {c : OSub r // (c : OpenMobius) ∈ W}
  base : ((homeo ⟨x₀, x₀_mem⟩ : {c : OSub r // (c : OpenMobius) ∈ W}) : OSub r) = c₀

/-! ## 1. Coordinate relabelling between an open interval and a chart cell -/

/-- A real parameter lying in `(lo,hi)` (with `lo,hi` inside the chart
interval) lies in the chart interval. -/
private lemma chartParam_in_c {r : ℝ → Space} {p : KnotParamTriple}
    (c : ZeroSet1Chart r p) {lo hi : ℝ} (hlo : c.lo < lo) (hhi : hi < c.hi)
    {t : ℝ} (ht : t ∈ Set.Ioo lo hi) : t ∈ Set.Ioo c.lo c.hi := by
  constructor <;> linarith [hlo, hhi, ht.1, ht.2]

/-- The chart parameter of a relabelled interval parameter. -/
private abbrev cellParam {r : ℝ → Space} {p : KnotParamTriple}
    (c : ZeroSet1Chart r p) {lo hi : ℝ} (hlo : c.lo < lo) (hhi : hi < c.hi)
    (t : ChartInterval lo hi) : ChartInterval c.lo c.hi :=
  ⟨(t : ℝ), chartParam_in_c c hlo hhi t.2⟩

/-- **Relabelling homeo.**  An open real interval `(lo,hi)` with `lo,hi`
strictly inside the chart interval `(c.lo,c.hi)` is homeomorphic (as a
parameter space) to the corresponding cell of the chart interval —
both are the same open set of real parameters, up to the chart membership
proofs. -/
noncomputable def cellIntervalHomeo {r : ℝ → Space} {p : KnotParamTriple}
    (c : ZeroSet1Chart r p) {lo hi : ℝ} (hlo : c.lo < lo) (hhi : hi < c.hi) :
    ChartInterval lo hi ≃ₜ {x : ChartInterval c.lo c.hi // (x : ℝ) ∈ Set.Ioo lo hi} where
  toFun := fun t => ⟨cellParam c hlo hhi t, t.2⟩
  invFun := fun y => ⟨(y.1 : ℝ), y.2⟩
  left_inv := by
    intro t
    rfl
  right_inv := by
    intro y
    apply Subtype.ext
    apply Subtype.ext
    rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-! ## 2. Interval charts of `O` at trisecant classes -/

/-- **Interval charts of `O` (the chart theorem).**  For a smooth knot
under `QuadrisecantFree` and transverse torus general position, every
trisecant class `c₀ ∈ O` carries an `OSub1Chart`: a small strict convex
cell around a strict representative of `c₀` (shrunken into the strict
region, the local injectivity region of the class map, and the chart
window) is mapped by the class map
`x ↦ zeroChordClass h (chartLift c x)` bijectively and continuously onto
its trace in `O` — an open subset by the open-map lemma — so the cell is
homeomorphic to that open trace, and relabelling coordinates gives the
open-interval domain. -/
theorem osub1Chart_at_class {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (c₀ : OSub r) : Nonempty (OSub1Chart r c₀) := by
  classical
  rcases strictRep_of_trisecant h c₀.2 with ⟨z₀, hz₀str, hz₀cls⟩
  have hGP : TorusGeneralPosition r := torusTransverse_monotone hgp
  rcases zeroSet1Chart_at_general_position h hGP (z₀ : KnotParamTriple) z₀.2 with ⟨c⟩
  let xb : ChartInterval c.lo c.hi := ⟨c.x₀, c.x₀_mem⟩
  have hbase_eq : chartLift c xb = z₀ := by
    simpa [xb] using (chartLift_base_eq (c := c) (z := z₀))
  have hbstr : strictZero r (chartLift c xb) := by
    simpa [hbase_eq] using hz₀str
  rcases exists_convex_strict_cell h (x := xb) hbstr with ⟨δ₀, hδ₀pos, hδ₀lo, hδ₀hi, hδ₀str⟩
  rcases zeroChordClass_injective_near_base h hqf c hbstr with ⟨J₁, hJ₁xb, hJ₁open, hJ₁inj⟩
  have hnhd : J₁ ∈ 𝓝 xb := hJ₁open.mem_nhds hJ₁xb
  rcases (Metric.mem_nhds_iff.mp hnhd) with ⟨ε, hεpos, hball⟩
  let δ : ℝ := min δ₀ (ε / 2)
  have hδpos : 0 < δ := by
    dsimp [δ]
    exact lt_min hδ₀pos (half_pos hεpos)
  have hδle₀ : δ ≤ δ₀ := by
    dsimp [δ]
    exact min_le_left δ₀ (ε / 2)
  have hδleε : δ ≤ ε := by
    dsimp [δ]
    exact le_trans (min_le_right δ₀ (ε / 2)) (half_le_self (le_of_lt hεpos))
  let lo : ℝ := (xb : ℝ) - δ
  let hi : ℝ := (xb : ℝ) + δ
  let x₀ : ℝ := (xb : ℝ)
  have hx₀mem : x₀ ∈ Set.Ioo lo hi := by
    dsimp [x₀, lo, hi]
    constructor <;> linarith [hδpos]
  have hloC : c.lo < lo := by
    dsimp [lo]
    linarith [hδ₀lo, hδle₀]
  have hhiC : hi < c.hi := by
    dsimp [hi]
    linarith [hδ₀hi, hδle₀]
  -- the cell (in chart-interval coordinates)
  let cell : Set (ChartInterval c.lo c.hi) := {x | (x : ℝ) ∈ Set.Ioo lo hi}
  have hcellopen : IsOpen cell := by
    dsimp [cell]
    exact isOpen_Ioo.preimage continuous_subtype_val
  have hcellstr : ∀ x : ChartInterval c.lo c.hi, x ∈ cell → strictZero r (chartLift c x) := by
    intro x hx
    apply hδ₀str x
    dsimp [cell, lo, hi] at hx ⊢
    constructor <;> linarith [hδle₀, hx.1, hx.2]
  have hcellball : ∀ x : ChartInterval c.lo c.hi, x ∈ cell → x ∈ Metric.ball xb ε := by
    intro x hx
    rw [Metric.mem_ball]
    have hsub : dist x xb < ε := by
      change dist (x : ℝ) (xb : ℝ) < ε
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith [hδleε, hx.1, hx.2]
    exact hsub
  have hxbc : xb ∈ cell := by
    dsimp [cell, lo, hi]
    constructor <;> linarith [hδpos]
  -- open-map lemma on the whole cell
  rcases zeroChordClass_image_open_on_strict_J h hqf hgp (c := c) (J := cell) hcellopen hcellstr
    with ⟨W, hWopen, hWeq⟩
  -- membership lemmas
  have hOclass : ∀ (z : ZeroSetPoint r), strictZero r z → zeroChordClass h z ∈ trisecantSet r := by
    intro z hz
    change HasMiddleOnClass r (zeroChordClass h z)
    exact strict_hasMiddleOnClass h z hz
  have hclW : ∀ x : ChartInterval c.lo c.hi, (x : ℝ) ∈ Set.Ioo lo hi →
      zeroChordClass h (chartLift c x) ∈ W := by
    intro x hx
    have hxcell : x ∈ cell := by
      dsimp [cell]
      exact hx
    have hcl : zeroChordClass h (chartLift c x) ∈ zeroChordClass h '' (chartLift c '' cell) := by
      refine ⟨chartLift c x, ⟨x, hxcell, rfl⟩, rfl⟩
    have h1 : zeroChordClass h (chartLift c x) ∈ trisecantSet r ∩ W := by
      rw [hWeq]
      exact hcl
    exact h1.2
  have hc₀W : (c₀ : OpenMobius) ∈ W := by
    have hzD : chartLift c xb ∈ chartLift c '' cell := ⟨xb, hxbc, rfl⟩
    have hc₀im : (c₀ : OpenMobius) ∈ zeroChordClass h '' (chartLift c '' cell) := by
      refine ⟨chartLift c xb, hzD, ?_⟩
      simp [hbase_eq, hz₀cls]
    have hc₀OW : (c₀ : OpenMobius) ∈ trisecantSet r ∩ W := by
      rw [hWeq]
      exact hc₀im
    exact hc₀OW.2
  -- the codomain carrier is open in OSub
  have hCopen : IsOpen {c : OSub r | (c : OpenMobius) ∈ W} := by
    exact hWopen.preimage continuous_subtype_val
  -- the map from the cell subtype
  let DSub : Type := {x : ChartInterval c.lo c.hi // (x : ℝ) ∈ Set.Ioo lo hi}
  let fO : DSub → OSub r := fun x =>
    ⟨zeroChordClass h (chartLift c x.1), hOclass (chartLift c x.1)
      (hcellstr x.1 (by simpa [cell] using x.2))⟩
  have hcont_fO : Continuous fO := by
    dsimp [fO]
    have hv : Continuous (fun x : DSub => zeroChordClass h (chartLift c x.1)) :=
      (continuous_zeroChordClass h).comp ((continuous_chartLift c).comp continuous_subtype_val)
    exact Continuous.subtype_mk hv (fun x => hOclass (chartLift c x.1)
      (hcellstr x.1 (by simpa [cell] using x.2)))
  -- injectivity on the cell (all points strict and inside the injectivity region)
  have hinj_fO : Function.Injective fO := by
    intro x y hxy
    have hcl : zeroChordClass h (chartLift c x.1) = zeroChordClass h (chartLift c y.1) := by
      have hv := congrArg (fun s : OSub r => (s : OpenMobius)) hxy
      simpa [fO] using hv
    have hxcell : x.1 ∈ cell := by simpa [cell] using x.2
    have hycell : y.1 ∈ cell := by simpa [cell] using y.2
    have hxJ : x.1 ∈ J₁ := hball (hcellball x.1 hxcell)
    have hyJ : y.1 ∈ J₁ := hball (hcellball y.1 hycell)
    have hxy1 : x.1 = y.1 := hJ₁inj hxJ hyJ (hcellstr x.1 hxcell) (hcellstr y.1 hycell) hcl
    apply Subtype.ext
    exact hxy1
  -- the class trace map on the cell is open onto its image in O
  have hopen_fO : IsOpenMap fO := by
    intro U hU
    have hUval : IsOpen ((Subtype.val : DSub → ChartInterval c.lo c.hi) '' U) :=
      hcellopen.isOpenMap_subtype_val U hU
    have hJstrU : ∀ x : ChartInterval c.lo c.hi,
        x ∈ (Subtype.val : DSub → ChartInterval c.lo c.hi) '' U → strictZero r (chartLift c x) := by
      rintro x ⟨y, hyU, hxy⟩
      rw [← hxy]
      exact hcellstr (y : ChartInterval c.lo c.hi) (by simpa [cell] using y.2)
    rcases zeroChordClass_image_open_on_strict_J h hqf hgp (c := c)
      (J := (Subtype.val : DSub → ChartInterval c.lo c.hi) '' U) hUval hJstrU with ⟨W₀, hW₀open, hW₀eq⟩
    have hvalEq : fO '' U = (fun s : OSub r => (s : OpenMobius)) ⁻¹' W₀ := by
      ext s
      constructor
      · intro hs
        rcases hs with ⟨y, hyU, hyeq⟩
        rw [← hyeq]
        have hcl : ((fO y : OSub r) : OpenMobius) ∈ zeroChordClass h '' (chartLift c ''
            ((Subtype.val : DSub → ChartInterval c.lo c.hi) '' U)) := by
          refine ⟨chartLift c (y : ChartInterval c.lo c.hi), ⟨(y : ChartInterval c.lo c.hi), ⟨y, hyU, rfl⟩, rfl⟩, ?_⟩
          simp [fO]
        have hcl2 : ((fO y : OSub r) : OpenMobius) ∈ trisecantSet r ∩ W₀ := by
          rw [hW₀eq]
          exact hcl
        exact hcl2.2
      · intro hs
        have hsOW : (s : OpenMobius) ∈ trisecantSet r ∩ W₀ := ⟨s.2, hs⟩
        have hscl : (s : OpenMobius) ∈ zeroChordClass h '' (chartLift c ''
            ((Subtype.val : DSub → ChartInterval c.lo c.hi) '' U)) := by
          rw [← hW₀eq]
          exact hsOW
        rcases hscl with ⟨z, hzmem, hzcl⟩
        rcases hzmem with ⟨x, hxU2, hzx⟩
        rcases hxU2 with ⟨y, hyU, hxy⟩
        refine ⟨y, hyU, ?_⟩
        apply Subtype.ext
        calc
          ((fO y : OSub r) : OpenMobius) = zeroChordClass h (chartLift c (y : ChartInterval c.lo c.hi)) := by
            simp [fO]
          _ = zeroChordClass h z := by rw [hxy, hzx]
          _ = (s : OpenMobius) := hzcl
    rw [hvalEq]
    exact hW₀open.preimage continuous_subtype_val
  -- the map into the trace subtype and its homeomorphism properties
  let βmap : DSub → {c : OSub r // (c : OpenMobius) ∈ W} := fun x =>
    ⟨fO x, hclW x.1 x.2⟩
  have hcont_β : Continuous βmap := by
    dsimp [βmap]
    exact Continuous.subtype_mk hcont_fO (fun x => hclW x.1 x.2)
  have hinj_β : Function.Injective βmap := by
    intro x y hxy
    have hf := congrArg (fun s : {c : OSub r // (c : OpenMobius) ∈ W} => (s : OSub r)) hxy
    exact hinj_fO hf
  have hsurj_β : Function.Surjective βmap := by
    rintro ⟨c', hc'W⟩
    have hc'O : (c' : OpenMobius) ∈ trisecantSet r := c'.2
    have hc'OW : (c' : OpenMobius) ∈ trisecantSet r ∩ W := ⟨hc'O, hc'W⟩
    have hc'im : (c' : OpenMobius) ∈ zeroChordClass h '' (chartLift c '' cell) := by
      rw [← hWeq]
      exact hc'OW
    rcases hc'im with ⟨z, hzmem, hzcl⟩
    rcases hzmem with ⟨x, hxcell, hzx⟩
    refine ⟨⟨x, (by simpa [cell] using hxcell)⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    calc
      ((fO ⟨x, (by simpa [cell] using hxcell)⟩ : OSub r) : OpenMobius) =
          zeroChordClass h (chartLift c x) := by simp [fO]
      _ = zeroChordClass h z := by rw [hzx]
      _ = (c' : OpenMobius) := hzcl
  have hopen_β : IsOpenMap βmap := by
    intro U hU
    have hUvalO : IsOpen (fO '' U) := hopen_fO U hU
    have hiff : IsOpen (βmap '' U) ↔
        IsOpen ((Subtype.val : {c : OSub r // (c : OpenMobius) ∈ W} → OSub r) '' (βmap '' U)) := by
      constructor
      · intro hs
        exact hCopen.isOpenMap_subtype_val (βmap '' U) hs
      · intro hs
        have hpre : IsOpen ((Subtype.val : {c : OSub r // (c : OpenMobius) ∈ W} → OSub r) ⁻¹'
            ((Subtype.val : {c : OSub r // (c : OpenMobius) ∈ W} → OSub r) '' (βmap '' U))) :=
          hs.preimage continuous_subtype_val
        simpa [Subtype.val_injective.preimage_image] using hpre
    rw [hiff]
    have hvalEq : (Subtype.val : {c : OSub r // (c : OpenMobius) ∈ W} → OSub r) '' (βmap '' U) = fO '' U := by
      ext s
      constructor
      · rintro ⟨z, hz, rfl⟩
        rcases hz with ⟨y, hyU, rfl⟩
        exact ⟨y, hyU, rfl⟩
      · rintro ⟨y, hyU, rfl⟩
        refine ⟨βmap y, ⟨y, hyU, rfl⟩, rfl⟩
    rw [hvalEq]
    exact hUvalO
  -- assemble the chart
  let α : ChartInterval lo hi ≃ₜ DSub := cellIntervalHomeo c hloC hhiC
  let F : ChartInterval lo hi → {c : OSub r // (c : OpenMobius) ∈ W} := fun t => βmap (α t)
  have hcont_F : Continuous F := hcont_β.comp α.continuous
  have hinj_F : Function.Injective F := by
    intro t₁ t₂ h
    have hαt : α t₁ = α t₂ := hinj_β (by simpa [F] using h)
    exact α.injective hαt
  have hsurj_F : Function.Surjective F := by
    intro c'
    rcases hsurj_β c' with ⟨y, hy⟩
    rcases α.surjective y with ⟨t, ht⟩
    refine ⟨t, ?_⟩
    simpa [F, ht] using hy
  have hopen_F : IsOpenMap F := hopen_β.comp α.isOpenMap
  let e : ChartInterval lo hi ≃ₜ {c : OSub r // (c : OpenMobius) ∈ W} :=
    (Equiv.ofBijective F ⟨hinj_F, hsurj_F⟩).toHomeomorphOfContinuousOpen hcont_F hopen_F
  -- base
  have hbase : ((e ⟨x₀, hx₀mem⟩ : {c : OSub r // (c : OpenMobius) ∈ W}) : OSub r) = c₀ := by
    have hαval : (α ⟨x₀, hx₀mem⟩ : DSub).1 = xb := by
      dsimp [α, cellIntervalHomeo, cellParam, x₀, xb]
    calc
      ((e ⟨x₀, hx₀mem⟩ : {c : OSub r // (c : OpenMobius) ∈ W}) : OSub r)
          = fO (α ⟨x₀, hx₀mem⟩) := by rfl
      _ = c₀ := by
        apply Subtype.ext
        calc
          (fO (α ⟨x₀, hx₀mem⟩) : OpenMobius) =
              zeroChordClass h (chartLift c (α ⟨x₀, hx₀mem⟩).1) := by rfl
          _ = zeroChordClass h (chartLift c xb) := by rw [hαval]
          _ = zeroChordClass h z₀ := by rw [hbase_eq]
          _ = (c₀ : OpenMobius) := hz₀cls
  exact ⟨⟨lo, hi, x₀, hx₀mem, W, hWopen, hc₀W, e, hbase⟩⟩


/-! ## 3. Chart overlap: the transition homeomorphisms of the interval
charts of `O`

Two interval charts of `O` (`OSub1Chart`) whose traces overlap in the band
are *compatible*: on the overlap the change of parameters is a
homeomorphism of open interval subsets, and it preserves the class.  This
is the atlas-compatibility statement of the local 1-manifold structure of
`O` — the elementary glue from which the interval-chart chains along the
path-connected components (the arc/circle classification, brick (b)) are
built.  (Mirror of the `ZeroSet1Chart` transition section of
`Torus1Chart.lean`, at the class level.) -/

/-- The class of a chart parameter (the `OSub` value of the chart
homeo). -/
def oChartLift {r : ℝ → Space} {c₀ : OSub r} (ch : OSub1Chart r c₀)
    (x : ChartInterval ch.lo ch.hi) : OSub r :=
  (ch.homeo x : {c : OSub r // (c : OpenMobius) ∈ ch.W}).1

/-- The class of a chart parameter lies in the trace `W` of the chart. -/
lemma oChartLift_mem_W {r : ℝ → Space} {c₀ : OSub r} (ch : OSub1Chart r c₀)
    (x : ChartInterval ch.lo ch.hi) : (oChartLift ch x : OpenMobius) ∈ ch.W :=
  (ch.homeo x).2

/-- The chart homeo value is the lift paired with its trace membership. -/
lemma oChartHomeo_eq_lift {r : ℝ → Space} {c₀ : OSub r} (ch : OSub1Chart r c₀)
    (x : ChartInterval ch.lo ch.hi) :
    (ch.homeo x : {c : OSub r // (c : OpenMobius) ∈ ch.W}) =
      ⟨oChartLift ch x, oChartLift_mem_W ch x⟩ := by
  apply Subtype.ext
  rfl

/-- The base point of the chart maps to its base class. -/
lemma oChartLift_base {r : ℝ → Space} {c₀ : OSub r} (ch : OSub1Chart r c₀) :
    oChartLift ch ⟨ch.x₀, ch.x₀_mem⟩ = c₀ := ch.base

/-- Applying the inverse chart homeo to a trace class recovers the
parameter with that class. -/
lemma oChartLift_eq_of_homeo {r : ℝ → Space} {c₀ : OSub r} (ch : OSub1Chart r c₀)
    (z : {c : OSub r // (c : OpenMobius) ∈ ch.W}) :
    oChartLift ch (ch.homeo.symm z) = (z : OSub r) := by
  have hz := ch.homeo.apply_symm_apply z
  change ((ch.homeo (ch.homeo.symm z) : {c : OSub r // (c : OpenMobius) ∈ ch.W}) : OSub r) =
    (z : OSub r)
  exact congrArg (fun w : {c : OSub r // (c : OpenMobius) ∈ ch.W} => (w : OSub r)) hz

/-- The **transition domain** of chart `ch₁` into chart `ch₂`: the
parameters of `ch₁` whose class lies in the trace of `ch₂`. -/
abbrev OChartTransitionDomain {r : ℝ → Space} {c₀ c₁ : OSub r}
    (ch₁ : OSub1Chart r c₀) (ch₂ : OSub1Chart r c₁) : Type :=
  {x : ChartInterval ch₁.lo ch₁.hi // (oChartLift ch₁ x : OpenMobius) ∈ ch₂.W}

/-- The transition-domain set is open in the chart interval (it is the
preimage of the open trace set `W₂` under the continuous class map). -/
lemma isOpen_oChartTransitionDomain {r : ℝ → Space} {c₀ c₁ : OSub r}
    (ch₁ : OSub1Chart r c₀) (ch₂ : OSub1Chart r c₁) :
    IsOpen {x : ChartInterval ch₁.lo ch₁.hi |
      (oChartLift ch₁ x : OpenMobius) ∈ ch₂.W} := by
  have hmap0 : Continuous (fun x : ChartInterval ch₁.lo ch₁.hi =>
      (((ch₁.homeo x : {c : OSub r // (c : OpenMobius) ∈ ch₁.W}) : OSub r) : OpenMobius)) :=
    continuous_subtype_val.comp (continuous_subtype_val.comp ch₁.homeo.continuous)
  have hmap : Continuous (fun x : ChartInterval ch₁.lo ch₁.hi =>
      (oChartLift ch₁ x : OpenMobius)) := by
    exact hmap0
  exact ch₂.W_open.preimage hmap

/-- **The forward transition map** `ch₁ → ch₂`: a parameter `x` of `ch₁`
whose class lies in the trace of `ch₂` is sent to the parameter of `ch₂`
describing the same class. -/
noncomputable def oChartTransitionTo {r : ℝ → Space} {c₀ c₁ : OSub r}
    (ch₁ : OSub1Chart r c₀) (ch₂ : OSub1Chart r c₁)
    (x : OChartTransitionDomain ch₁ ch₂) : OChartTransitionDomain ch₂ ch₁ :=
  ⟨ch₂.homeo.symm ⟨oChartLift ch₁ x.1, x.2⟩, by
    have hpt : oChartLift ch₂ (ch₂.homeo.symm ⟨oChartLift ch₁ x.1, x.2⟩) =
        oChartLift ch₁ x.1 := by
      simpa using oChartLift_eq_of_homeo ch₂ (z := ⟨oChartLift ch₁ x.1, x.2⟩)
    rw [hpt]
    exact (ch₁.homeo x.1).2⟩

/-- The value of the forward transition map (no proofs involved). -/
lemma oChartTransitionTo_val {r : ℝ → Space} {c₀ c₁ : OSub r}
    (ch₁ : OSub1Chart r c₀) (ch₂ : OSub1Chart r c₁)
    (x : OChartTransitionDomain ch₁ ch₂) :
    (oChartTransitionTo ch₁ ch₂ x).1 =
      ch₂.homeo.symm ⟨oChartLift ch₁ x.1, x.2⟩ := by
  dsimp [oChartTransitionTo]

/-- The forward transition preserves the class. -/
lemma oChartTransition_preserves {r : ℝ → Space} {c₀ c₁ : OSub r}
    (ch₁ : OSub1Chart r c₀) (ch₂ : OSub1Chart r c₁)
    (x : OChartTransitionDomain ch₁ ch₂) :
    oChartLift ch₂ (oChartTransitionTo ch₁ ch₂ x).1 = oChartLift ch₁ x.1 := by
  rw [oChartTransitionTo_val]
  exact oChartLift_eq_of_homeo ch₂ (z := ⟨oChartLift ch₁ x.1, x.2⟩)

/-- The **backward transition map** (the forward map with the roles of the
two charts swapped). -/
noncomputable def oChartTransitionBack {r : ℝ → Space} {c₀ c₁ : OSub r}
    (ch₁ : OSub1Chart r c₀) (ch₂ : OSub1Chart r c₁)
    (y : OChartTransitionDomain ch₂ ch₁) : OChartTransitionDomain ch₁ ch₂ :=
  oChartTransitionTo ch₂ ch₁ y

/-- Forward and backward transition maps are mutually inverse (the left
half). -/
lemma oChartTransition_leftInverse {r : ℝ → Space} {c₀ c₁ : OSub r}
    (ch₁ : OSub1Chart r c₀) (ch₂ : OSub1Chart r c₁)
    (x : OChartTransitionDomain ch₁ ch₂) :
    oChartTransitionBack ch₁ ch₂ (oChartTransitionTo ch₁ ch₂ x) = x := by
  let T := oChartTransitionTo ch₁ ch₂ x
  apply Subtype.ext
  change (ch₁.homeo.symm ⟨oChartLift ch₂ T.1, T.2⟩ : ChartInterval ch₁.lo ch₁.hi) = x.1
  have hpt : oChartLift ch₂ T.1 = oChartLift ch₁ x.1 :=
    oChartTransition_preserves ch₁ ch₂ x
  let pr : (oChartLift ch₁ x.1 : OpenMobius) ∈ ch₁.W := by
    rw [← hpt]
    exact T.2
  have h₁ : (⟨oChartLift ch₂ T.1, T.2⟩ :
        {c : OSub r // (c : OpenMobius) ∈ ch₁.W}) =
      ⟨oChartLift ch₁ x.1, pr⟩ := by
    apply Subtype.ext
    exact hpt
  have h₂ : (⟨oChartLift ch₁ x.1, pr⟩ :
        {c : OSub r // (c : OpenMobius) ∈ ch₁.W}) = ch₁.homeo x.1 := by
    rw [oChartHomeo_eq_lift ch₁ x.1]
  calc
    (ch₁.homeo.symm ⟨oChartLift ch₂ T.1, T.2⟩ : ChartInterval ch₁.lo ch₁.hi)
        = ch₁.homeo.symm ⟨oChartLift ch₁ x.1, pr⟩ := by rw [h₁]
    _ = ch₁.homeo.symm (ch₁.homeo x.1) := by rw [h₂]
    _ = x.1 := ch₁.homeo.symm_apply_apply x.1

/-- Forward and backward transition maps are mutually inverse (the right
half). -/
lemma oChartTransition_rightInverse {r : ℝ → Space} {c₀ c₁ : OSub r}
    (ch₁ : OSub1Chart r c₀) (ch₂ : OSub1Chart r c₁)
    (y : OChartTransitionDomain ch₂ ch₁) :
    oChartTransitionTo ch₁ ch₂ (oChartTransitionBack ch₁ ch₂ y) = y := by
  let T := oChartTransitionBack ch₁ ch₂ y
  apply Subtype.ext
  change (ch₂.homeo.symm ⟨oChartLift ch₁ T.1, T.2⟩ : ChartInterval ch₂.lo ch₂.hi) = y.1
  have hpt : oChartLift ch₁ T.1 = oChartLift ch₂ y.1 := by
    dsimp [T]
    exact oChartTransition_preserves ch₂ ch₁ y
  let pr : (oChartLift ch₂ y.1 : OpenMobius) ∈ ch₂.W := by
    rw [← hpt]
    exact T.2
  have h₁ : (⟨oChartLift ch₁ T.1, T.2⟩ :
        {c : OSub r // (c : OpenMobius) ∈ ch₂.W}) =
      ⟨oChartLift ch₂ y.1, pr⟩ := by
    apply Subtype.ext
    exact hpt
  have h₂ : (⟨oChartLift ch₂ y.1, pr⟩ :
        {c : OSub r // (c : OpenMobius) ∈ ch₂.W}) = ch₂.homeo y.1 := by
    rw [oChartHomeo_eq_lift ch₂ y.1]
  calc
    (ch₂.homeo.symm ⟨oChartLift ch₁ T.1, T.2⟩ : ChartInterval ch₂.lo ch₂.hi)
        = ch₂.homeo.symm ⟨oChartLift ch₂ y.1, pr⟩ := by rw [h₁]
    _ = ch₂.homeo.symm (ch₂.homeo y.1) := by rw [h₂]
    _ = y.1 := ch₂.homeo.symm_apply_apply y.1

/-- The transition correspondence as an equivalence of the two domains. -/
noncomputable def oChartTransitionEquiv {r : ℝ → Space} {c₀ c₁ : OSub r}
    (ch₁ : OSub1Chart r c₀) (ch₂ : OSub1Chart r c₁) :
    OChartTransitionDomain ch₁ ch₂ ≃ OChartTransitionDomain ch₂ ch₁ where
  toFun := oChartTransitionTo ch₁ ch₂
  invFun := oChartTransitionBack ch₁ ch₂
  left_inv := oChartTransition_leftInverse ch₁ ch₂
  right_inv := oChartTransition_rightInverse ch₁ ch₂

/-- The forward transition map is continuous (its value into `ℝ` is the
inverse chart homeo applied to the continuous lifted class). -/
lemma continuous_oChartTransitionTo {r : ℝ → Space} {c₀ c₁ : OSub r}
    (ch₁ : OSub1Chart r c₀) (ch₂ : OSub1Chart r c₁) :
    Continuous (oChartTransitionTo ch₁ ch₂) := by
  let X₁ : Type := OChartTransitionDomain ch₁ ch₂
  have hid₂ : Topology.IsInducing ((↑) : OChartTransitionDomain ch₂ ch₁ →
      ChartInterval ch₂.lo ch₂.hi) := Topology.IsInducing.subtypeVal
  rw [hid₂.continuous_iff]
  have hid₂ℝ : Topology.IsInducing ((↑) : ChartInterval ch₂.lo ch₂.hi → ℝ) :=
    Topology.IsInducing.subtypeVal
  rw [hid₂ℝ.continuous_iff]
  have hq : Continuous (fun x : X₁ => (oChartLift ch₁ x.1 : OSub r)) := by
    have hval₁ : Continuous (fun x : X₁ => (x.1 : ChartInterval ch₁.lo ch₁.hi)) :=
      continuous_subtype_val
    have hstep : Continuous (fun x : X₁ => (ch₁.homeo (x.1 : ChartInterval ch₁.lo ch₁.hi))) :=
      ch₁.homeo.continuous.comp hval₁
    exact continuous_subtype_val.comp hstep
  let hp : X₁ → {c : OSub r // (c : OpenMobius) ∈ ch₂.W} := fun x =>
    ⟨oChartLift ch₁ x.1, x.2⟩
  have hcontp : Continuous hp := by
    dsimp [hp]
    exact Continuous.subtype_mk hq (fun x => x.2)
  have h2r : Continuous (fun w : {c : OSub r // (c : OpenMobius) ∈ ch₂.W} =>
      ((ch₂.homeo.symm w : ChartInterval ch₂.lo ch₂.hi) : ℝ)) := by
    have hI : Continuous (fun u : ChartInterval ch₂.lo ch₂.hi => (u : ℝ)) :=
      continuous_subtype_val
    exact hI.comp ch₂.homeo.symm.continuous
  have hmain : Continuous (fun x : X₁ =>
      ((ch₂.homeo.symm (hp x) : ChartInterval ch₂.lo ch₂.hi) : ℝ)) :=
    h2r.comp hcontp
  change Continuous (fun x : X₁ => ((oChartTransitionTo ch₁ ch₂ x).1 : ℝ))
  have hfun : (fun x : X₁ => ((oChartTransitionTo ch₁ ch₂ x).1 : ℝ)) =
      (fun x : X₁ => ((ch₂.homeo.symm (hp x) : ChartInterval ch₂.lo ch₂.hi) : ℝ)) := by
    funext x
    simp [oChartTransitionTo, hp]
  rw [hfun]
  exact hmain

/-- The backward transition map is continuous (it is the forward map with
the charts swapped). -/
lemma continuous_oChartTransitionBack {r : ℝ → Space} {c₀ c₁ : OSub r}
    (ch₁ : OSub1Chart r c₀) (ch₂ : OSub1Chart r c₁) :
    Continuous (oChartTransitionBack ch₁ ch₂) := by
  change Continuous (oChartTransitionTo ch₂ ch₁)
  exact continuous_oChartTransitionTo ch₂ ch₁

/-- The transition correspondence of two overlapping interval charts of
`O` is a **homeomorphism of open parameter domains** (subsets of the open
intervals). -/
noncomputable def oChartTransitionHomeo {r : ℝ → Space} {c₀ c₁ : OSub r}
    (ch₁ : OSub1Chart r c₀) (ch₂ : OSub1Chart r c₁) :
    OChartTransitionDomain ch₁ ch₂ ≃ₜ OChartTransitionDomain ch₂ ch₁ :=
  Homeomorph.mk (oChartTransitionEquiv ch₁ ch₂) (continuous_oChartTransitionTo ch₁ ch₂)
    (continuous_oChartTransitionBack ch₁ ch₂)

/-- The transition homeomorphism **preserves the class**: the chart of
`ch₂` at the transported parameter describes the same class as the chart
of `ch₁` at the original parameter. -/
lemma oChartTransition_preserves_class {r : ℝ → Space} {c₀ c₁ : OSub r}
    (ch₁ : OSub1Chart r c₀) (ch₂ : OSub1Chart r c₁)
    (x : OChartTransitionDomain ch₁ ch₂) :
    oChartLift ch₂ ((oChartTransitionHomeo ch₁ ch₂ x : OChartTransitionDomain ch₂ ch₁) :
        ChartInterval ch₂.lo ch₂.hi) = oChartLift ch₁ x.1 := by
  have hval : ((oChartTransitionHomeo ch₁ ch₂ x : OChartTransitionDomain ch₂ ch₁) :
      ChartInterval ch₂.lo ch₂.hi) = (oChartTransitionTo ch₁ ch₂ x).1 := by
    rfl
  rw [hval]
  exact oChartTransition_preserves ch₁ ch₂ x

/-- **The transition lemma of the interval charts of `O`.**  Two interval
charts whose traces overlap in the band are compatible: on the transition
domains the change of parameters is a homeomorphism
(`oChartTransitionHomeo`), and it preserves the trisecant class. -/
theorem oSub1Chart_transition {r : ℝ → Space} {c₀ c₁ : OSub r}
    (ch₁ : OSub1Chart r c₀) (ch₂ : OSub1Chart r c₁) :
    ∃ h : OChartTransitionDomain ch₁ ch₂ ≃ₜ OChartTransitionDomain ch₂ ch₁,
      ∀ x : OChartTransitionDomain ch₁ ch₂,
        oChartLift ch₂ ((h x : OChartTransitionDomain ch₂ ch₁) :
          ChartInterval ch₂.lo ch₂.hi) = oChartLift ch₁ x.1 := by
  refine ⟨oChartTransitionHomeo ch₁ ch₂, ?_⟩
  intro x
  exact oChartTransition_preserves_class ch₁ ch₂ x

/-- **Overlap gives a transition parameter.**  If a trisecant class `b`
lies in the traces of both charts, then `ch₁` has a parameter (the inverse
chart value of `b`) lying in the transition domain `ch₁ → ch₂`, and that
parameter describes the class `b`. -/
lemma exists_oChartTransitionParam_of_mem_both {r : ℝ → Space} {c₀ c₁ : OSub r}
    (ch₁ : OSub1Chart r c₀) (ch₂ : OSub1Chart r c₁) (b : OSub r)
    (hb₁ : (b : OpenMobius) ∈ ch₁.W) (hb₂ : (b : OpenMobius) ∈ ch₂.W) :
    ∃ x : OChartTransitionDomain ch₁ ch₂, oChartLift ch₁ x.1 = b := by
  let z₁ : {c : OSub r // (c : OpenMobius) ∈ ch₁.W} := ⟨b, hb₁⟩
  let x : OChartTransitionDomain ch₁ ch₂ :=
    ⟨ch₁.homeo.symm z₁, by
      have hpt : oChartLift ch₁ (ch₁.homeo.symm z₁) = b := by
        simpa [z₁] using oChartLift_eq_of_homeo ch₁ (z := z₁)
      rw [hpt]
      exact hb₂⟩
  refine ⟨x, ?_⟩
  simpa [x, z₁] using oChartLift_eq_of_homeo ch₁ (z := z₁)


end LeanEval.KnotTheory.Quadrisecant
