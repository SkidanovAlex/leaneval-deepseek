import Mathlib
import Submission.Work.Milnor.MorseFun
import Submission.Work.Milnor.morse_glue
import Submission.Work.Glue.glued_isManifold

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The two-critical-point Morse function on Milnor's `Mk (-2)`

`Submission.Work.Milnor.MorseFun` defines the two chart expressions
`morseChart1 (x, y) = Re(ẋ y)/√(1+‖x‖²)` and `morseChart2 (x', y') = Re(y')/√(1+‖x'‖²)`
of the Morse function on Milnor's exotic sphere `Mk (-2)`, and `Submission.Work.Milnor.morse_glue`
proves that they agree across the gluing `(x, y) ↦ (x/‖x‖², u² y u⁻¹)`.

This file assembles them into a single smooth function `F : Mk (-2) → ℝ`:

* `morseFunAux` packages the two expressions on the disjoint union `MSpace ⊕ MSpace`;
* `morseFunAux_rel` (using `morse_glue`) shows that they respect the gluing relation, so that
  they descend to the quotient `Mk (-2) = (clutchData (-2)).Glued`;
* `morseFunLift` is the descended function, and `morseFunLift_ιX`/`morseFunLift_ιY` compute its
  values on the two charts;
* the smoothness of `morseFunLift` follows from the general gluing criterion
  `contMDiff_of_comp_iota_aux` (a function on a glued manifold is smooth as soon as its
  pullbacks along `ιX` and `ιY` are), applied to the smoothness of the two chart expressions
  `morseChart_smooth`.

The result is `Work.Milnor.morseFun`, the existence of the smooth function used in Milnor's
proof that `Mk (-2)` is homeomorphic to `S⁷`.
-/

open scoped Manifold ContDiff Topology
open TopologicalSpace Set
open Submission.Milnor
open Submission.Glue (Data)

namespace Work.Milnor

noncomputable section

set_option maxHeartbeats 1000000

/-! ## Smoothness of the two chart expressions -/

/-- The auxiliary identification of `ℝ⁴ × ℍ` with the ambient space on which the chart
expressions are defined. -/
abbrev MorseChartSpace : Type := EuclideanSpace ℝ (Fin 4) × Quaternion ℝ

/-- `Re` of a quaternion is smooth (it is a continuous linear map, and `ℍ` is finite
dimensional). -/
theorem morse_contDiff_re : ContDiff ℝ ∞ (fun a : Quaternion ℝ => a.re) := by
  have h := ((show Quaternion ℝ →ₗ[ℝ] ℝ from QuaternionAlgebra.reₗ _ _ _).toContinuousLinearMap).contDiff
      (𝕜 := ℝ) (n := ∞)
  convert h using 1
  ext a
  rfl

/-- `q ↦ ‖q.1‖ ^ 2` is smooth on `ℝ⁴ × ℍ`. -/
theorem morse_contDiff_normSq_fst : ContDiff ℝ ∞ (fun q : MorseChartSpace => ‖q.1‖ ^ 2) := by
  rw [show (fun q : MorseChartSpace => ‖q.1‖ ^ 2) = (fun q : MorseChartSpace => inner ℝ q.1 q.1) from
    funext (fun q => (real_inner_self_eq_norm_sq q.1).symm)]
  exact ContDiff.inner ℝ contDiff_fst contDiff_fst

/-- The denominator `q ↦ √(1 + ‖q.1‖ ^ 2)` of the two chart expressions is smooth (and
positive). -/
theorem morse_contDiff_sqrt :
    ContDiff ℝ ∞ (fun q : MorseChartSpace => Real.sqrt (1 + ‖q.1‖ ^ 2)) :=
  (contDiff_const.add morse_contDiff_normSq_fst).sqrt (fun q => ne_of_gt (by positivity))

theorem morse_sqrt_ne_zero (q : MorseChartSpace) :
    Real.sqrt (1 + ‖q.1‖ ^ 2) ≠ 0 :=
  ne_of_gt (Real.sqrt_pos.mpr (by positivity))

/-- The two chart expressions of the Morse function are smooth functions on the ambient
manifold `MSpace = ℝ⁴ × S³`. -/
theorem morseChart_smooth :
    ContMDiff ((𝓡 4).prod (𝓡 3)) 𝓘(ℝ, ℝ) ∞ morseChart1 ∧
    ContMDiff ((𝓡 4).prod (𝓡 3)) 𝓘(ℝ, ℝ) ∞ morseChart2 := by
  have hmap : ContMDiff ((𝓡 4).prod (𝓡 3)) ((𝓡 4).prod 𝓘(ℝ, Quaternion ℝ)) ∞
      (fun p : MSpace => (p.1, (p.2 : Quaternion ℝ))) :=
    contMDiff_fst.prodMk
      ((contMDiff_coe_sphere (E := Quaternion ℝ) (n := 3) (m := ∞)).comp contMDiff_snd)
  constructor
  · have h1 : ContDiff ℝ ∞ (fun q : MorseChartSpace => Quaternion.linearIsometryEquivTuple.symm q.1) :=
      (Quaternion.linearIsometryEquivTuple.symm.toContinuousLinearEquiv.contDiff).comp contDiff_fst
    have h2 : ContDiff ℝ ∞ (fun q : MorseChartSpace => q.2) := contDiff_snd
    have hnum : ContDiff ℝ ∞
        (fun q : MorseChartSpace => (Quaternion.linearIsometryEquivTuple.symm q.1 * q.2).re) :=
      morse_contDiff_re.comp (h1.mul h2)
    have hPhi : ContDiff ℝ ∞ (fun q : MorseChartSpace =>
        (Quaternion.linearIsometryEquivTuple.symm q.1 * q.2).re / Real.sqrt (1 + ‖q.1‖ ^ 2)) :=
      hnum.div morse_contDiff_sqrt morse_sqrt_ne_zero
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hmap
    exact hPhi.contMDiff.comp hmap
  · have hnum : ContDiff ℝ ∞ (fun q : MorseChartSpace => q.2.re) :=
      morse_contDiff_re.comp contDiff_snd
    have hPhi : ContDiff ℝ ∞ (fun q : MorseChartSpace =>
        q.2.re / Real.sqrt (1 + ‖q.1‖ ^ 2)) :=
      hnum.div morse_contDiff_sqrt morse_sqrt_ne_zero
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hmap
    exact hPhi.contMDiff.comp hmap

/-! ## A smoothness criterion on glued manifolds -/

/-- **A function on a glued manifold is smooth iff its pullbacks to the two pieces are.**

The glued space `D.Glued` is covered by the two open images `range D.ιX` and `range D.ιY`, and
the charts of `D.Glued` are exactly the charts of `X` and `Y` transported along the open
embeddings `D.ιX` and `D.ιY`. Hence smoothness can be tested on the two pieces. -/
theorem contMDiff_of_comp_iota_aux
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I n X]
    {Y : Type*} [TopologicalSpace Y] [ChartedSpace H Y] [IsManifold I n Y]
    [Nonempty X] [Nonempty Y] (D : Data I n X Y)
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] {H' : Type*} [TopologicalSpace H']
    {I' : ModelWithCorners ℝ E' H'} {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
    [IsManifold I' n M']
    {g : D.Glued → M'}
    (hX : ContMDiff I I' n (g ∘ D.ιX)) (hY : ContMDiff I I' n (g ∘ D.ιY)) :
    ContMDiff I I' n g := by
  haveI hM : IsManifold I n D.Glued := Work.Glue.glued_isManifold D
  intro z
  rcases hz : Quotient.out z with x | y
  · have hzx : z = D.ιX x := by rw [← Quotient.out_eq z, hz]; rfl
    subst hzx
    have hcz : chartAt H (D.ιX x) = D.chartOfX x := by
      change D.chartAt (D.ιX x) = D.chartOfX x
      exact D.chartAt_of_out_inl hz
    rw [contMDiffAt_iff_of_mem_maximalAtlas (e := chartAt H (D.ιX x))
      (e' := chartAt H' (g (D.ιX x)))
      (IsManifold.subset_maximalAtlas (ChartedSpace.chart_mem_atlas (H := H) (D.ιX x)))
      (IsManifold.chart_mem_maximalAtlas (g (D.ιX x)))
      (mem_chart_source H (D.ιX x)) (mem_chart_source H' (g (D.ιX x)))]
    rw [hcz]
    have hcomp : ∀ u : H, (D.chartOfX x).symm u = D.ιX ((chartAt H x).symm u) := by
      intro u
      rw [Work.Glue.chartOfX_symm_eq D x, OpenPartialHomeomorph.trans_apply, D.homX_apply]
    constructor
    · have hopen : IsOpen (Set.range D.ιX) := D.isOpenEmbedding_ιX.isOpen_range
      have hcont1 : ContinuousAt (fun w : D.Glued => D.homX.symm w) (D.ιX x) :=
        (D.homX.symm.continuousOn_toFun).continuousAt (by
          rw [OpenPartialHomeomorph.symm_source, D.homX_target]
          exact hopen.mem_nhds ⟨x, rfl⟩)
      have hcontX : ContinuousAt (g ∘ D.ιX) (D.homX.symm (D.ιX x)) := by
        rw [D.homX_symm_apply x]
        exact hX.continuous.continuousAt
      have hcont2 : ContinuousAt ((g ∘ D.ιX) ∘ fun w : D.Glued => D.homX.symm w) (D.ιX x) :=
        hcontX.comp hcont1
      refine hcont2.congr ?_
      filter_upwards [hopen.mem_nhds ⟨x, rfl⟩] with w hw
      obtain ⟨u, rfl⟩ := hw
      simp [Function.comp_apply, D.homX_symm_apply u]
    · have hh : ContMDiffAt I I' n (g ∘ D.ιX) x := hX.contMDiffAt
      have hchart := (contMDiffWithinAt_iff_of_mem_maximalAtlas
        (e := chartAt H x) (e' := chartAt H' (g (D.ιX x))) (s := Set.univ)
        (IsManifold.chart_mem_maximalAtlas x) (IsManifold.chart_mem_maximalAtlas _)
        (mem_chart_source H x) (mem_chart_source H' _)).mp hh.contMDiffWithinAt
      simp only [preimage_univ, univ_inter] at hchart
      have hbase : ((D.chartOfX x).extend I) (D.ιX x) = (chartAt H x).extend I x := by
        simp only [OpenPartialHomeomorph.extend_coe, Function.comp_apply]
        rw [Data.chartOfX, OpenPartialHomeomorph.trans_apply, D.homX_symm_apply x]
      rw [hbase]
      have hfun : ∀ v : E,
          (chartAt H' (g (D.ιX x))).extend I' (g (((D.chartOfX x).extend I).symm v))
            = (chartAt H' (g (D.ιX x))).extend I'
                ((g ∘ D.ιX) (((chartAt H x).extend I).symm v)) := by
        intro v
        simp only [OpenPartialHomeomorph.extend_coe_symm, Function.comp_apply, hcomp]
      exact hchart.2.congr (fun v _ => hfun v) (hfun _)
  · have hzy : z = D.ιY y := by rw [← Quotient.out_eq z, hz]; rfl
    subst hzy
    have hcy : chartAt H (D.ιY y) = D.chartOfY y := by
      change D.chartAt (D.ιY y) = D.chartOfY y
      exact D.chartAt_of_out_inr hz
    rw [contMDiffAt_iff_of_mem_maximalAtlas (e := chartAt H (D.ιY y))
      (e' := chartAt H' (g (D.ιY y)))
      (IsManifold.subset_maximalAtlas (ChartedSpace.chart_mem_atlas (H := H) (D.ιY y)))
      (IsManifold.chart_mem_maximalAtlas (g (D.ιY y)))
      (mem_chart_source H (D.ιY y)) (mem_chart_source H' (g (D.ιY y)))]
    rw [hcy]
    have hcomp : ∀ u : H, (D.chartOfY y).symm u = D.ιY ((chartAt H y).symm u) := by
      intro u
      rw [Work.Glue.chartOfY_symm_eq D y, OpenPartialHomeomorph.trans_apply, D.homY_apply]
    constructor
    · have hopen : IsOpen (Set.range D.ιY) := D.isOpenEmbedding_ιY.isOpen_range
      have hcont1 : ContinuousAt (fun w : D.Glued => D.homY.symm w) (D.ιY y) :=
        (D.homY.symm.continuousOn_toFun).continuousAt (by
          rw [OpenPartialHomeomorph.symm_source, D.homY_target]
          exact hopen.mem_nhds ⟨y, rfl⟩)
      have hcontY : ContinuousAt (g ∘ D.ιY) (D.homY.symm (D.ιY y)) := by
        rw [D.homY_symm_apply y]
        exact hY.continuous.continuousAt
      have hcont2 : ContinuousAt ((g ∘ D.ιY) ∘ fun w : D.Glued => D.homY.symm w) (D.ιY y) :=
        hcontY.comp hcont1
      refine hcont2.congr ?_
      filter_upwards [hopen.mem_nhds ⟨y, rfl⟩] with w hw
      obtain ⟨u, rfl⟩ := hw
      simp [Function.comp_apply, D.homY_symm_apply u]
    · have hh : ContMDiffAt I I' n (g ∘ D.ιY) y := hY.contMDiffAt
      have hchart := (contMDiffWithinAt_iff_of_mem_maximalAtlas
        (e := chartAt H y) (e' := chartAt H' (g (D.ιY y))) (s := Set.univ)
        (IsManifold.chart_mem_maximalAtlas y) (IsManifold.chart_mem_maximalAtlas _)
        (mem_chart_source H y) (mem_chart_source H' _)).mp hh.contMDiffWithinAt
      simp only [preimage_univ, univ_inter] at hchart
      have hbase : ((D.chartOfY y).extend I) (D.ιY y) = (chartAt H y).extend I y := by
        simp only [OpenPartialHomeomorph.extend_coe, Function.comp_apply]
        rw [Data.chartOfY, OpenPartialHomeomorph.trans_apply, D.homY_symm_apply y]
      rw [hbase]
      have hfun : ∀ v : E,
          (chartAt H' (g (D.ιY y))).extend I' (g (((D.chartOfY y).extend I).symm v))
            = (chartAt H' (g (D.ιY y))).extend I'
                ((g ∘ D.ιY) (((chartAt H y).extend I).symm v)) := by
        intro v
        simp only [OpenPartialHomeomorph.extend_coe_symm, Function.comp_apply, hcomp]
      exact hchart.2.congr (fun v _ => hfun v) (hfun _)

/-! ## Construction of the function on `Mk (-2)` -/

/-- The two chart expressions of the Morse function, packaged as a function on the disjoint
union `MSpace ⊕ MSpace` used to build `Mk (-2)`. -/
def morseFunAux : MSpace ⊕ MSpace → ℝ := Sum.elim morseChart1 morseChart2

/-- The two chart expressions agree on the gluing region: `morseFunAux` respects the relation
defining `Mk (-2)`. -/
lemma morseFunAux_rel (a b : MSpace ⊕ MSpace) (h : (clutchData (-2)).rel a b) :
    morseFunAux a = morseFunAux b := by
  rcases a with p | p <;> rcases b with q | q
  · exact congrArg morseChart1 h
  · obtain ⟨hp, hq⟩ := h
    show morseChart1 p = morseChart2 q
    rw [← hq]
    exact morse_glue p hp
  · obtain ⟨hq, hp⟩ := h
    show morseChart2 p = morseChart1 q
    rw [hp]
    exact (morse_glue q hq).symm
  · exact congrArg morseChart2 h

/-- The Morse function `F` on `Mk (-2)`, defined by descent of the two chart expressions
along the quotient map. -/
def morseFunLift : Mk (-2) → ℝ :=
  Quotient.lift morseFunAux morseFunAux_rel

lemma morseFunLift_ιX (p : MSpace) :
    morseFunLift ((clutchData (-2)).ιX p) = morseChart1 p := rfl

lemma morseFunLift_ιY (p : MSpace) :
    morseFunLift ((clutchData (-2)).ιY p) = morseChart2 p := rfl

/-! ## The main statement -/

theorem morseFun :
    ∃ F : Mk (-2) → ℝ,
      ContMDiff ((𝓡 4).prod (𝓡 3)) 𝓘(ℝ, ℝ) ∞ F ∧
      (∀ p : MSpace, F ((clutchData (-2)).ιX p) = morseChart1 p) ∧
      (∀ p : MSpace, F ((clutchData (-2)).ιY p) = morseChart2 p) := by
  refine ⟨morseFunLift, ?_, morseFunLift_ιX, morseFunLift_ιY⟩
  refine contMDiff_of_comp_iota_aux (clutchData (-2)) ?_ ?_
  · exact morseChart_smooth.1.congr morseFunLift_ιX
  · exact morseChart_smooth.2.congr morseFunLift_ιY

end

end Work.Milnor
