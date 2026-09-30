/-
# The inner polar layer is covered by finitely many junction charts

This file proves `Work.RTOwed.jPolar_cover_fin`: there is a *finite* family of junction charts
(`Work.RTOwed.JPin`, the boxes `Work.RTOwed.jBox` and their coordinate inclusions
`Work.RTOwed.jCoordM` of `Submission/Work/RTOwed/FillBigDefs.lean`) covering the whole inner polar
layer `1/24 < ‖p‖∞ < 1/2` of every cusp.

## The reduction

The inner polar layer is the region `1/24 < ‖p‖∞ < 1/2` in each filling piece; its image under
`incW v` must be met by the images of the junction charts.  The junction box conditions are, for a
point `q = ThetaPolarS v c p y`,

* the radial window `1/4 < q 0 < rBig`, which involves only `‖p‖∞` and holds throughout the layer;
* the wedge condition `Int.fract (uqOf v q - c) ∈ (k/4, (k+1)/4)`, which involves only the *direction*
  of `p`;
* the `w`-box condition `wOf v y ∈ W`, which involves only the torus coordinate;
* the horizontal box condition, which involves the direction of `p` and the torus coordinate.

Hence the layer is 'radially saturated': it suffices to cover the compact slice
`{‖p‖∞ = jR0} × (ℝ/ℤ)²` (`jR0 = 1/4`), and the *same* pins then cover the whole layer.  The slice has
two compact factors (the boundary curve of the square and the torus), so a finite subcover of the
family of admissible pins exists by compactness — we do not have to enumerate the (many) horizontal
boxes.

## The construction at one point

At a point `(p₀, D)` of the slice we pick the shift `c` and the wedge index `k` with
`p₀ ∈ wedgeS c k` (`Work.Cusp.wedge_cover`), a lift `y₀` of the torus coordinate, the section box
`W` around `wOf v y₀` (`Work.Cusp.exists_section_box`), and set `kx` to the horizontal coordinate of
the resulting polar point, `δ = 1/2`.  The neighbourhood of the point is the product of

* an open piece `Up` of the `wedgeS c k` around `bnd p₀` on which the shifted lift `uS c` varies by
  less than `jEtaU v`, and
* the open set `V = q2 '' {y₀' | wOf v y₀' ∈ W, ‖y₀' - y₀‖ < jEtaY v}` of torus coordinates on which
  a lift inside the section box stays within `jEtaY v` of `y₀`;

the constants `jEtaU, jEtaY` are chosen so that `jEtaU v * ‖slope v‖ < 1/4` and
`jEtaY v * (‖lam2 v‖ + ‖lam3 v‖) < 1/4`, whence the horizontal box of side `1` around `kx`
(`δ = 1/2`) contains `cuspX v (uS c p) y₀'` whenever `bnd p ∈ Up` and a lift `y₀' ∈ V` is used.  The
set `V` is open because the quotient `E2 → (ℝ/ℤ)²` is an open map; every point of it has a lift in
the chosen section, and the box membership is then purely formal.
-/
import Mathlib
import Submission.Work.RTOwed.FillBigDefs
import Submission.Work.Cusp.wedge_cover
import Submission.Work.Cusp.exists_section_box
import Submission.Work.Cusp.uS_continuousOn_wedgeS
import Submission.Work.Cusp.radial_eq_inner
import Submission.Work.Cusp.nrm_bnd
import Submission.Work.Cusp.smul_bnd
import Submission.Work.Cusp.bndOfU_uPerim
import Submission.Work.Cusp.uPerim_bndOfU
import Submission.Work.Cusp.uS_lift
import Submission.Work.Cusp.bndOfU_u
import Submission.Work.Cusp.slope_ne_zero
import Submission.Work.Cusp.abs_le_nrm
import Submission.Work.Cusp.nrm_continuous
import Submission.Work.Cusp.cuspInvInner_mem_polarStratum

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open Set Topology Function
open scoped RealInnerProductSpace Real

namespace Work.RTOwed

open Work.Cusp

/-! ### The slice of the polar layer -/

/-- The radius of the slice used for the finite polar cover (`1/24 < 1/4 < 1/2`). -/
def jR0 : ℝ := 1/4

theorem jR0_pos : (0 : ℝ) < jR0 := by norm_num [jR0]
theorem jR0_gt : (1/24 : ℝ) < jR0 := by norm_num [jR0]
theorem jR0_lt : jR0 < (1/2 : ℝ) := by norm_num [jR0]
theorem jR0_le_one : jR0 ≤ (1 : ℝ) := by norm_num [jR0]
theorem jR0_ne_zero : jR0 ≠ 0 := ne_of_gt jR0_pos

/-- The two torus coordinates `(ℝ/ℤ)²`. -/
abbrev JTor : Type := (Fin 2 → AddCircle (1:ℝ))

/-- The slice `{p ∈ Sq | ‖p‖∞ = jR0}` of the filling square. -/
abbrev JSlice : Type := {p : Work.Space.SquarePt // nrm (p : E2) = jR0}

instance : CompactSpace JSlice :=
  isCompact_iff_compactSpace.mp
    (isClosed_eq (nrm_continuous.comp continuous_subtype_val) continuous_const).isCompact

/-! ### Elementary geometry of `bnd`, `uS`, `wedgeS` -/

/-- The radial projection depends only on the direction: `u (bnd p) = u p` for `p ≠ 0`. -/
theorem ju_bnd {p : E2} (hp : p ≠ 0) : u (bnd p) = u p := by
  show uPerim (bnd (bnd p)) = uPerim (bnd p)
  rw [bnd, nrm_bnd hp, inv_one, one_smul]

/-- The shifted lift depends only on the direction. -/
theorem juS_bnd (c : ℝ) {p : E2} (hp : p ≠ 0) : uS c (bnd p) = uS c p := by
  rw [uS, uS, ju_bnd hp]

/-- `bnd (r • bnd p) = bnd p` for `r > 0`, `p ≠ 0`. -/
theorem jbnd_smul_bnd {r : ℝ} (hr : 0 < r) {p : E2} (hp : p ≠ 0) :
    bnd (r • bnd p) = bnd p := by
  rw [bnd, nrm_smul, nrm_bnd hp, mul_one, abs_of_pos hr, smul_smul,
    inv_mul_cancel₀ (ne_of_gt hr), one_smul]

/-- `‖r • bnd p‖∞ = r` for `r > 0`, `p ≠ 0`. -/
theorem jnrm_smul_bnd {r : ℝ} (hr : 0 < r) {p : E2} (hp : p ≠ 0) :
    nrm (r • bnd p) = r := by
  rw [nrm_smul, nrm_bnd hp, mul_one, abs_of_pos hr]

/-- `r • bnd p` lies in the square when `0 < r ≤ 1`. -/
theorem jmem_Sq_smul_bnd {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) {p : E2} (hp : p ≠ 0) :
    r • bnd p ∈ Work.Space.Sq := by
  have hn : nrm (bnd p) = 1 := nrm_bnd hp
  constructor
  · have h := abs_le_nrm (bnd p) 0
    calc |(r • bnd p) 0| = r * |(bnd p) 0| := by rw [PiLp.smul_apply, smul_eq_mul, abs_mul, abs_of_pos hr0]
      _ ≤ r * nrm (bnd p) := by gcongr
      _ = r := by rw [hn, mul_one]
      _ ≤ 1 := hr1
  · have h := abs_le_nrm (bnd p) 1
    calc |(r • bnd p) 1| = r * |(bnd p) 1| := by rw [PiLp.smul_apply, smul_eq_mul, abs_mul, abs_of_pos hr0]
      _ ≤ r * nrm (bnd p) := by gcongr
      _ = r := by rw [hn, mul_one]
      _ ≤ 1 := hr1

/-- `wedgeS c k` is a cone: a point lies in it iff its direction does. -/
theorem jwedgeS_cone (c : ℝ) (k : Fin 4) {p : E2} (hp : p ≠ 0) :
    (bnd p ∈ wedgeS c k ↔ p ∈ wedgeS c k) := by
  simp only [wedgeS, Set.mem_ofPred_eq]
  rw [nrm_bnd hp, ju_bnd hp]
  exact ⟨fun h => ⟨nrm_pos hp, h.2⟩, fun h => ⟨by norm_num, h.2⟩⟩

/-- A point `p ≠ 0` of the square lies in one of the eight shifted wedges. -/
theorem jwedge_data {p : E2} (hp : 0 < nrm p) :
    ∃ (c : ℝ) (k : Fin 4), (c = 0 ∨ c = 1/8) ∧ p ∈ wedgeS c k := by
  rcases wedge_cover p hp with h | h
  · obtain ⟨k, hk⟩ := Set.mem_iUnion.mp h
    exact ⟨0, k, Or.inl rfl, hk⟩
  · obtain ⟨k, hk⟩ := Set.mem_iUnion.mp h
    exact ⟨1/8, k, Or.inr rfl, hk⟩

/-- **The horizontal part of `polarToUHS` at a point of the shifted polar chart.** -/
theorem jxOf_polarToUHS_ThetaPolarS (v : Work.Space.Cusp) (c : ℝ) (p y : E2) :
    xOf (polarToUHS v (ThetaPolarS v c p y)) = cuspX v (uS c p) y := by
  have hxyz : xOf (polarToUHS v (ThetaPolarS v c p y))
      = (‖slope v‖ / (2 * π) * (ThetaPolarS v c p y) 1) • frame1 v
        + wOf v y 0 • frame2 v + wOf v y 1 • frame3 v := by
    ext i; fin_cases i <;> rfl
  rw [hxyz]
  have hq1 : (ThetaPolarS v c p y) 1
      = 2 * π * uS c p + 2 * π * inner ℝ (cuspY v y) (slope v) / ‖slope v‖ ^ 2 := by
    simp [ThetaPolarS]
  rw [hq1]
  have hn : ‖slope v‖ ≠ 0 := norm_ne_zero_iff.mpr (slope_ne_zero v)
  have hπ : (2 * π : ℝ) ≠ 0 := by positivity
  have hscalar : ‖slope v‖ / (2 * π)
        * (2 * π * uS c p + 2 * π * inner ℝ (cuspY v y) (slope v) / ‖slope v‖ ^ 2)
      = ‖slope v‖ * uS c p + ‖slope v‖ * (inner ℝ (cuspY v y) (slope v) / ‖slope v‖ ^ 2) := by
    field_simp
  rw [hscalar, add_smul, smul_frame1 v (uS c p),
    smul_frame1 v (inner ℝ (cuspY v y) (slope v) / ‖slope v‖ ^ 2)]
  rw [inner_slope_smul v (cuspY v y)]
  rw [show wOf v y 0 = inner ℝ (cuspY v y) (frame2 v) from rfl,
    show wOf v y 1 = inner ℝ (cuspY v y) (frame3 v) from rfl]
  rw [show ((uS c p • slope v + inner ℝ (cuspY v y) (frame1 v) • frame1 v)
        + inner ℝ (cuspY v y) (frame2 v) • frame2 v) + inner ℝ (cuspY v y) (frame3 v) • frame3 v
      = uS c p • slope v + (inner ℝ (cuspY v y) (frame1 v) • frame1 v
        + inner ℝ (cuspY v y) (frame2 v) • frame2 v
        + inner ℝ (cuspY v y) (frame3 v) • frame3 v) by abel]
  rw [frame_expansion v (cuspY v y)]
  ext i; fin_cases i <;> rfl

/-! ### The two oscillation constants and the horizontal estimate -/

/-- The bound on the oscillation of the shifted lift in the neighbourhood `Up`. -/
def jEtaU (v : Work.Space.Cusp) : ℝ := 1 / (4 * (‖slope v‖ + 1))

/-- The bound on the oscillation of the torus lift in the neighbourhood `V`. -/
def jEtaY (v : Work.Space.Cusp) : ℝ := 1 / (4 * (‖lam2 v‖ + ‖lam3 v‖ + 1))

theorem jEtaU_pos (v : Work.Space.Cusp) : 0 < jEtaU v := by
  rw [jEtaU]; positivity

theorem jEtaY_pos (v : Work.Space.Cusp) : 0 < jEtaY v := by
  rw [jEtaY]; positivity

/-- `cuspX v a Y` as a function of `(a, Y)`: the difference is the difference of the coordinates. -/
theorem jcuspX_sub (v : Work.Space.Cusp) (a a0 : ℝ) (Y Y0 : E2) :
    cuspX v a Y - cuspX v a0 Y0
      = (a - a0) • slope v + (Y 0 - Y0 0) • lam2 v + (Y 1 - Y0 1) • lam3 v := by
  rw [cuspX, cuspX, cuspY, cuspY]
  module

/-- **The horizontal box of side `1` around `kx` contains `cuspX v a Y`** whenever `a` is within
`jEtaU v` of `a0` and `Y` within `jEtaY v` of `Y0`. -/
theorem jcuspX_coord_lt (v : Work.Space.Cusp) {a a0 : ℝ} {Y Y0 : E2} (i : Fin 3)
    (ha : |a - a0| < jEtaU v) (hY : ‖Y - Y0‖ < jEtaY v) :
    |(cuspX v a Y - cuspX v a0 Y0) i| < 1/2 := by
  rw [jcuspX_sub]
  have hcomp : ((a - a0) • slope v + (Y 0 - Y0 0) • lam2 v + (Y 1 - Y0 1) • lam3 v) i
      = (a - a0) * slope v i + (Y 0 - Y0 0) * lam2 v i + (Y 1 - Y0 1) * lam3 v i := by
    simp [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  rw [hcomp]
  have hs : |slope v i| ≤ ‖slope v‖ := by
    have h := PiLp.norm_apply_le (slope v) i
    rwa [Real.norm_eq_abs] at h
  have hl2 : |lam2 v i| ≤ ‖lam2 v‖ := by
    have h := PiLp.norm_apply_le (lam2 v) i
    rwa [Real.norm_eq_abs] at h
  have hl3 : |lam3 v i| ≤ ‖lam3 v‖ := by
    have h := PiLp.norm_apply_le (lam3 v) i
    rwa [Real.norm_eq_abs] at h
  have hd0 : |Y 0 - Y0 0| < jEtaY v := by
    have h := PiLp.norm_apply_le (Y - Y0) 0
    rw [Real.norm_eq_abs, PiLp.sub_apply] at h
    exact lt_of_le_of_lt h hY
  have hd1 : |Y 1 - Y0 1| < jEtaY v := by
    have h := PiLp.norm_apply_le (Y - Y0) 1
    rw [Real.norm_eq_abs, PiLp.sub_apply] at h
    exact lt_of_le_of_lt h hY
  calc |(a - a0) * slope v i + (Y 0 - Y0 0) * lam2 v i + (Y 1 - Y0 1) * lam3 v i|
      ≤ |(a - a0) * slope v i| + |(Y 0 - Y0 0) * lam2 v i|
          + |(Y 1 - Y0 1) * lam3 v i| := abs_add_three _ _ _
    _ = |a - a0| * |slope v i| + |Y 0 - Y0 0| * |lam2 v i|
          + |Y 1 - Y0 1| * |lam3 v i| := by rw [abs_mul, abs_mul, abs_mul]
    _ ≤ jEtaU v * ‖slope v‖ + jEtaY v * ‖lam2 v‖ + jEtaY v * ‖lam3 v‖ := by
      have h1 := mul_le_mul (le_of_lt ha) hs (abs_nonneg _) (le_of_lt (jEtaU_pos v))
      have h2 := mul_le_mul (le_of_lt hd0) hl2 (abs_nonneg _) (le_of_lt (jEtaY_pos v))
      have h3 := mul_le_mul (le_of_lt hd1) hl3 (abs_nonneg _) (le_of_lt (jEtaY_pos v))
      linarith
    _ = jEtaU v * ‖slope v‖ + jEtaY v * (‖lam2 v‖ + ‖lam3 v‖) := by ring
    _ < 1/2 := by
      have hU : jEtaU v * ‖slope v‖ < 1/4 := by
        have hpos : 0 < 4 * (‖slope v‖ + 1) := by positivity
        rw [jEtaU, div_mul_eq_mul_div, div_lt_iff₀ hpos]
        linarith [norm_nonneg (slope v)]
      have hYl : jEtaY v * (‖lam2 v‖ + ‖lam3 v‖) < 1/4 := by
        have hpos : 0 < 4 * (‖lam2 v‖ + ‖lam3 v‖ + 1) := by positivity
        rw [jEtaY, div_mul_eq_mul_div, div_lt_iff₀ hpos]
        linarith [norm_nonneg (lam2 v), norm_nonneg (lam3 v)]
      linarith

/-! ### The quotient map and the lift -/

/-- The quotient map `E2 → (ℝ/ℤ)²` is open. -/
theorem jq2_isOpenMap :
    IsOpenMap (fun y : E2 => fun i : Fin 2 => (y i : AddCircle (1:ℝ))) := by
  have hcoe : ∀ i : Fin 2, IsOpenQuotientMap (fun x : ℝ => (x : AddCircle (1:ℝ))) :=
    fun i => QuotientAddGroup.isOpenQuotientMap_mk
  have h1 : IsOpenQuotientMap
      (Pi.map (fun _ : Fin 2 => (fun x : ℝ => (x : AddCircle (1:ℝ))))) :=
    IsOpenQuotientMap.piMap (fun i => hcoe i)
  have hofLp : IsOpenMap (PiLp.homeomorph 2 (fun _ : Fin 2 => ℝ)) :=
    (PiLp.homeomorph 2 (fun _ : Fin 2 => ℝ)).isOpenMap
  have h := h1.isOpenMap.comp hofLp
  convert h using 1
  ext y i; rfl

/-- Every torus point has a real lift. -/
theorem jlift_exists (Dv : JTor) : ∃ y0 : E2, ∀ i, (y0 i : AddCircle (1:ℝ)) = Dv i := by
  have hsurj : ∀ i : Fin 2, ∃ x : ℝ, (x : AddCircle (1:ℝ)) = Dv i := fun i =>
    ⟨((AddCircle.equivIco (1:ℝ) (0:ℝ)) (Dv i) : ℝ), by rw [AddCircle.coe_equivIco]⟩
  choose f hf using hsurj
  exact ⟨WithLp.toLp 2 (fun i => f i), fun i => hf i⟩

/-- `wOf v` is continuous. -/
theorem jcontinuous_wOf (v : Work.Space.Cusp) : Continuous (wOf v) := by
  rw [← (PiLp.homeomorph 2 (fun _ : Fin 2 => ℝ)).comp_continuous_iff]
  show Continuous (fun y : E2 => fun i : Fin 2 => (wOf v y) i)
  refine continuous_pi (fun i => ?_)
  fin_cases i
  · have h : Continuous (fun y : E2 => inner ℝ (cuspY v y) (frame2 v)) :=
      continuous_inner.comp ((continuous_cuspY v).prodMk continuous_const)
    simpa [wOf] using h
  · have h : Continuous (fun y : E2 => inner ℝ (cuspY v y) (frame3 v)) :=
      continuous_inner.comp ((continuous_cuspY v).prodMk continuous_const)
    simpa [wOf] using h

/-- **The torus neighbourhood `V` is open**: the torus points having a lift inside the section box
`W` and within `η` of `y0`. -/
theorem jisOpen_liftSet (v : Work.Space.Cusp) (y0 : E2) (W : Set E2) (hW : IsOpen W) (η : ℝ) :
    IsOpen {Dv' : JTor | ∃ y0' : E2, (∀ i, (y0' i : AddCircle (1:ℝ)) = Dv' i) ∧
        wOf v y0' ∈ W ∧ ‖y0' - y0‖ < η} := by
  have hset : {Dv' : JTor | ∃ y0' : E2, (∀ i, (y0' i : AddCircle (1:ℝ)) = Dv' i) ∧
        wOf v y0' ∈ W ∧ ‖y0' - y0‖ < η}
      = (fun y : E2 => fun i : Fin 2 => (y i : AddCircle (1:ℝ))) ''
          {y0' : E2 | wOf v y0' ∈ W ∧ ‖y0' - y0‖ < η} := by
    ext Dv'
    constructor
    · rintro ⟨y0', hy, hW', hd⟩
      exact ⟨y0', ⟨hW', hd⟩, funext hy⟩
    · rintro ⟨y0', ⟨hW', hd⟩, hy⟩
      exact ⟨y0', fun i => congrFun hy i, hW', hd⟩
  rw [hset]
  refine jq2_isOpenMap _ ?_
  refine IsOpen.inter (hW.preimage (jcontinuous_wOf v)) ?_
  exact Metric.isOpen_ball

/-- **The oscillation radius of the shifted lift at a point of a wedge.** -/
theorem jexists_ball_uS (c : ℝ) (k : Fin 4) {p0 : E2} (hp0 : p0 ∈ wedgeS c k)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ p' : E2, p' ∈ wedgeS c k → ‖p' - p0‖ < δ → |uS c p' - uS c p0| < ε := by
  have h := uS_continuousOn_wedgeS c k p0 hp0
  have h2 : {x : E2 | dist (uS c x) (uS c p0) < ε} ∈ 𝓝[wedgeS c k] p0 :=
    (Metric.tendsto_nhds.mp h) ε hε
  rw [Metric.mem_nhdsWithin_iff] at h2
  obtain ⟨δ, hδpos, hδ⟩ := h2
  refine ⟨δ, hδpos, fun p' hp' hd => ?_⟩
  have hmem : p' ∈ Metric.ball p0 δ ∩ wedgeS c k :=
    ⟨by rwa [Metric.mem_ball, dist_eq_norm], hp'⟩
  have := hδ hmem
  simpa only [Set.mem_setOf_eq, Real.dist_eq] using this


/-! ### The covering predicate and the pointwise construction -/

/-- A pin covers a point `(p, y)` of the filling piece when the image of its box meets
`a.incW v (p, y)`. -/
def jcov (a : Work.Space.Assembly)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData a v)
    (v : Work.Space.Cusp) (P : JPin a v) (q : Work.Space.SquarePt × a.Torus v) : Prop :=
  a.incW v q ∈ jCoordM a v (D v) P.cU P.k P.W P.kx P.δ ''
    (Set.univ : Set {q : E4 // q ∈ jBox v P.cU P.k P.W P.kx P.δ})

/-- The data attached to a point of the slice: the pin, and the two neighbourhoods (of the
direction in the filling square and of the torus coordinate) that the pin covers. -/
structure JBund (a : Work.Space.Assembly)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData a v)
    (v : Work.Space.Cusp) (z : JSlice × JTor) where
  /-- The pin. -/
  P : JPin a v
  /-- The neighbourhood of the direction `bnd z.1`, inside the wedge of the pin. -/
  Up : Set E2
  /-- The neighbourhood of the torus coordinate `z.2`. -/
  V : Set JTor
  hUp : IsOpen Up
  hbnd : bnd (z.1.1 : E2) ∈ Up
  hV : IsOpen V
  hzV : z.2 ∈ V
  /-- Everything whose direction lies in `Up` and whose torus coordinate lies in `V` is covered by
  the pin, at every layer parameter of the inner polar layer. -/
  hcov : ∀ (q : Work.Space.SquarePt × a.Torus v),
    1/24 < nrm (q.1 : E2) → nrm (q.1 : E2) < 1/2 →
    bnd (q.1 : E2) ∈ Up → (D v).tor q.2 ∈ V → jcov a D v P q

/-- **The pointwise construction.**  Every point of the slice has a pin and neighbourhoods as in
`JBund`. -/
theorem jBund_nonempty (a : Work.Space.Assembly)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData a v)
    (v : Work.Space.Cusp) (z : JSlice × JTor) : Nonempty (JBund a D v z) := by
  classical
  obtain ⟨p0s, Dv⟩ := z
  set p0e : E2 := (p0s.1 : E2) with hp0e
  have hnrm0 : nrm p0e = jR0 := p0s.2
  have hp0pos : 0 < nrm p0e := by rw [hnrm0]; exact jR0_pos
  have hp0ne : p0e ≠ 0 := by intro h; rw [h] at hp0pos; simp [nrm] at hp0pos
  obtain ⟨c, k, hc, hwk⟩ := jwedge_data hp0pos
  obtain ⟨y0, hy0⟩ := jlift_exists Dv
  obtain ⟨W, hW, hWy0, hsec⟩ := exists_section_box v y0
  set kx : E3 := xOf (polarToUHS v (ThetaPolarS v c p0e y0)) with hkx
  have hd0mem : bnd p0e ∈ wedgeS c k := (jwedgeS_cone c k hp0ne).mpr hwk
  obtain ⟨δ1, hδ1pos, hδ1⟩ := jexists_ball_uS c k hd0mem (jEtaU_pos v)
  set Up : Set E2 := wedgeS c k ∩ Metric.ball (bnd p0e) δ1 with hUp
  set V : Set JTor := {Dv' : JTor | ∃ y0' : E2,
      (∀ i, (y0' i : AddCircle (1:ℝ)) = Dv' i) ∧ wOf v y0' ∈ W ∧ ‖y0' - y0‖ < jEtaY v}
    with hV
  set P : JPin a v := ⟨c, k, W, kx, 1/2, by norm_num, hW, hsec⟩ with hP
  refine ⟨⟨P, Up, V, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [hUp]; exact (isOpen_wedgeS c k).inter Metric.isOpen_ball
  · rw [hUp]
    exact ⟨hd0mem, by rw [Metric.mem_ball, dist_self]; exact hδ1pos⟩
  · rw [hV]; exact jisOpen_liftSet v y0 W hW (jEtaY v)
  · rw [hV]
    exact ⟨y0, hy0, hWy0, by rw [sub_self, norm_zero]; exact jEtaY_pos v⟩
  · rintro ⟨p, y⟩ hn1 hn2 hb hVy
    rw [hUp] at hb
    rw [hV] at hVy
    obtain ⟨y0', hy0', hWy0', hdy'⟩ := hVy
    set pe : E2 := (p : E2) with hpe
    have hpe_gt : (1/24 : ℝ) < nrm pe := hn1
    have hpe_lt : nrm pe < 1/2 := hn2
    have hpe_pos : 0 < nrm pe := lt_trans (by norm_num) hpe_gt
    have hpene : pe ≠ 0 := by intro h; rw [h] at hpe_pos; simp [nrm] at hpe_pos
    have hdir : pe ∈ wedgeS c k := (jwedgeS_cone c k hpene).mp hb.1
    set q : E4 := ThetaPolarS v c pe y0' with hq
    have hq0 : q 0 = radial v pe y0' := by rw [hq]; simp [ThetaPolarS]
    have hrad : radial v pe y0' = 2 * rJ * nrm pe := radial_eq_inner v pe y0' (le_of_lt hpe_lt)
    have hq23 : (!₂[q 2, q 3] : E2) = wOf v y0' := by
      rw [hq]; ext i; fin_cases i <;> simp [ThetaPolarS]
    have huq : uqOf v q = uS c pe := by rw [hq]; exact uqOf_ThetaPolarS v c pe y0'
    have hci : cuspInvInner v q = (pe, y0') := by
      rw [hq]; exact cuspInvInner_ThetaPolarS v c pe y0'
    have hqmem : q ∈ jBox v c k W kx (1/2) := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hq0, hrad, rJ]; linarith
      · rw [hq0, hrad, rJ, rBig]; linarith
      · rw [hq23]; exact hWy0'
      · rw [huq, uS]
        have h1 : c + Int.fract (u pe - c) - c = Int.fract (u pe - c) := by ring
        rw [h1]
        exact ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
      · rw [huq, uS]
        have h1 : c + Int.fract (u pe - c) - c = Int.fract (u pe - c) := by ring
        rw [h1, Int.fract_eq_self.mpr ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩]
        exact hdir.2
      · intro i
        have ha : |uS c pe - uS c p0e| < jEtaU v := by
          have h1 : uS c pe = uS c (bnd pe) := (juS_bnd c hpene).symm
          have h2 : uS c p0e = uS c (bnd p0e) := (juS_bnd c hp0ne).symm
          rw [h1, h2]
          exact hδ1 (bnd pe) hb.1 (by simpa [Metric.mem_ball, dist_eq_norm] using hb.2)
        have hkey := jcuspX_coord_lt v i ha hdy'
        rw [hq, jxOf_polarToUHS_ThetaPolarS v c pe y0', hkx,
          jxOf_polarToUHS_ThetaPolarS v c p0e y0]
        simpa only [PiLp.sub_apply] using hkey
    have hq0le : q 0 ≤ rJ := by rw [hq0, hrad, rJ]; linarith
    have hpc : (p : E2) = ((⟨pe, _⟩ : Work.Space.SquarePt) : E2) := rfl
    refine ⟨⟨q, hqmem⟩, Set.mem_univ _, ?_⟩
    show jCoordM a v (D v) c k W kx (1/2) ⟨q, hqmem⟩ = a.incW v (p, y)
    rw [jCoordM, dif_pos hq0le]
    congr 1
    refine Prod.ext ?_ ?_
    · refine Subtype.ext ?_
      have h1 : (cuspInvInner v q).1 = pe := congrArg Prod.fst hci
      rw [hpe] at h1
      exact h1
    · have h2 : (cuspInvInner v q).2 = y0' := congrArg Prod.snd hci
      rw [h2]
      have hfun : (fun i : Fin 2 => (((y0' i : ℝ)) : AddCircle (1:ℝ))) = (D v).tor y :=
        funext hy0'
      rw [hfun, Homeomorph.symm_apply_apply]

/-- The chosen bundle at a point of the slice. -/
noncomputable def jbOf (a : Work.Space.Assembly)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData a v)
    (v : Work.Space.Cusp) (z : JSlice × JTor) : JBund a D v z :=
  Classical.choice (jBund_nonempty a D v z)

/-- The neighbourhood of a point of the slice, in the slice. -/
def jUz (a : Work.Space.Assembly)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData a v)
    (v : Work.Space.Cusp) (z : JSlice × JTor) : Set (JSlice × JTor) :=
  {z' | bnd (z'.1.1 : E2) ∈ (jbOf a D v z).Up ∧ z'.2 ∈ (jbOf a D v z).V}

theorem jUz_isOpen (a : Work.Space.Assembly)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData a v)
    (v : Work.Space.Cusp) (z : JSlice × JTor) : IsOpen (jUz a D v z) := by
  have hbndc : Continuous (fun z' : JSlice × JTor => bnd (z'.1.1 : E2)) := by
    have hc : Continuous (fun z' : JSlice × JTor => ((z'.1.1 : E2))) :=
      continuous_subtype_val.comp (continuous_subtype_val.comp continuous_fst)
    have hEq : (fun z' : JSlice × JTor => bnd (z'.1.1 : E2))
        = fun z' => (jR0)⁻¹ • ((z'.1.1 : E2)) := by
      funext z'
      have hn : nrm (z'.1.1 : E2) = jR0 := z'.1.2
      rw [bnd, hn]
    rw [hEq]; exact hc.const_smul ((jR0)⁻¹)
  exact ((jbOf a D v z).hUp.preimage hbndc).inter ((jbOf a D v z).hV.preimage continuous_snd)

theorem jUz_self (a : Work.Space.Assembly)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData a v)
    (v : Work.Space.Cusp) (z : JSlice × JTor) : z ∈ jUz a D v z :=
  ⟨(jbOf a D v z).hbnd, (jbOf a D v z).hzV⟩

/-- **The inner polar layer of every cusp is covered by finitely many junction charts.** -/
theorem jPolar_cover_fin (a : Work.Space.Assembly)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData a v) :
    ∃ (N : ℕ) (par : Fin N → Σ v : Work.Space.Cusp, Work.RTOwed.JPin a v),
      ∀ (v : Work.Space.Cusp) (q : Work.Space.SquarePt × a.Torus v),
        (1/24 : ℝ) < Work.Cusp.nrm (q.1 : Work.Cusp.E2) → Work.Cusp.nrm (q.1 : Work.Cusp.E2) < 1/2 →
        ∃ i, (par i).1 = v ∧
          a.incW v q ∈ Work.RTOwed.jCoordM a v (D v) (par i).2.cU (par i).2.k (par i).2.W
            (par i).2.kx (par i).2.δ '' (Set.univ : Set {q : Work.Cusp.E4 // q ∈ Work.RTOwed.jBox v (par i).2.cU (par i).2.k (par i).2.W (par i).2.kx (par i).2.δ}) := by
  classical
  have hcover : ∀ v : Work.Space.Cusp, ∃ t : Finset (JSlice × JTor),
      (Set.univ : Set (JSlice × JTor)) ⊆ ⋃ z ∈ t, jUz a D v z := by
    intro v
    exact IsCompact.elim_finite_subcover isCompact_univ (jUz a D v)
      (fun z => jUz_isOpen a D v z)
      (fun z _ => Set.mem_iUnion.mpr ⟨z, jUz_self a D v z⟩)
  choose t ht using hcover
  let S : Finset (Σ v : Work.Space.Cusp, JPin a v) :=
    Finset.univ.biUnion (fun v => (t v).image (fun z => ⟨v, (jbOf a D v z).P⟩))
  refine ⟨S.card, fun i => (S.equivFin.symm i).1, ?_⟩
  intro v q h1 h2
  set pe : E2 := (q.1 : E2) with hpe
  have hn1 : (1/24 : ℝ) < nrm pe := h1
  have hn2 : nrm pe < 1/2 := h2
  have hpe_pos : 0 < nrm pe := lt_trans (by norm_num) hn1
  have hpene : pe ≠ 0 := by intro h; rw [h] at hpe_pos; simp [nrm] at hpe_pos
  let p0 : JSlice :=
    ⟨⟨jR0 • bnd pe, jmem_Sq_smul_bnd jR0_pos jR0_le_one hpene⟩,
      jnrm_smul_bnd jR0_pos hpene⟩
  let z0 : JSlice × JTor := (p0, (D v).tor q.2)
  have hz0mem : z0 ∈ ⋃ z ∈ t v, jUz a D v z := ht v (Set.mem_univ z0)
  obtain ⟨zi, hzi_t, hzi⟩ := Set.mem_iUnion₂.mp hz0mem
  have hzi_t' : zi ∈ t v := Finset.mem_coe.mp hzi_t
  have hbndUp : bnd pe ∈ (jbOf a D v zi).Up := by
    have h := hzi.1
    have hb : bnd (z0.1.1 : E2) = bnd pe := by
      show bnd (jR0 • bnd pe) = bnd pe
      exact jbnd_smul_bnd jR0_pos hpene
    rwa [hb] at h
  have hVy : (D v).tor q.2 ∈ (jbOf a D v zi).V := hzi.2
  have hcov := (jbOf a D v zi).hcov q hn1 hn2 hbndUp hVy
  have hmemS : (⟨v, (jbOf a D v zi).P⟩ : Σ v : Work.Space.Cusp, JPin a v) ∈ S := by
    rw [show S = Finset.univ.biUnion
      (fun v => (t v).image (fun z => ⟨v, (jbOf a D v z).P⟩)) from rfl]
    exact Finset.mem_biUnion.mpr ⟨v, Finset.mem_univ v,
      Finset.mem_image.mpr ⟨zi, hzi_t', rfl⟩⟩
  refine ⟨S.equivFin ⟨⟨v, (jbOf a D v zi).P⟩, hmemS⟩, ?_, ?_⟩
  · show (((S.equivFin.symm (S.equivFin ⟨⟨v, (jbOf a D v zi).P⟩, hmemS⟩)).1 :
        Σ v : Work.Space.Cusp, JPin a v)).1 = v
    rw [Equiv.symm_apply_apply]
  · simp only []
    rw [Equiv.symm_apply_apply]
    exact hcov

end Work.RTOwed
