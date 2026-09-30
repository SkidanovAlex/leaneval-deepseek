/-
# The homotopy equivalence `B ≃ₕ ⊔_v T_v`

This file proves

* `Work.Space.Split.retrB_homotopyEquiv` : the open collar

  `B = M̂ ∖ {‖p‖∞ ≤ 1}`  … more precisely  `B = incY '' {q | sqNorm q.2.1 < 1}`

  deformation retracts onto the union `⊔_{v} T_v` of the five cores of the filling pieces, i.e.
  there is a homotopy equivalence `B ≃ₕ Σ v, T_v`.

The mathematics is elementary, but the point set topology has to be done carefully because `B` is
an open subset of the *quotient* `M̂ = (M̄ ⊔ ⊔_v [-1,1]² × T_v)/~₃`, so a "collapse the collar to
its core" map has to be descended from the filling piece `⊔_v [-1,1]² × T_v`.

The argument proceeds in three steps.

1. *The collar of the filling pieces.*  On `a.Y = Σ v, [-1,1]² × T_v` the layer parameter is
   `sqNorm`, and `innerCore a.Torus = {q | sqNorm q.2.1 < 1}`.  Scaling the square coordinate by
   `s ∈ [0,1]` (`s = 1` the identity, `s = 0` the core `⊔_v T_v`) gives a deformation retraction of
   `innerCore` onto the cores (`scalePtB`, `fillScale`, `collarScale`).  Hence
   `collarHomotopyEquiv : innerCore ≃ₕ Σ v, T_v`.

2. *`incY` identifies the collar of the filling pieces with `B`.*  The map
   `incCollar : innerCore → B`, `q ↦ incY q`, is a continuous bijection; it is an open map because
   `incY` is injective and `incY '' U` is open in `M̂` for every open `U ⊆ innerCore` (its trace on
   the `M̄`-piece is empty, its trace on the filling pieces is `U`).  A continuous *open* bijection
   has a continuous inverse, so `incCollar` is a homeomorphism (`collarHomeo`).

3. Transporting the homotopy equivalence of 1. along the homeomorphism of 2. (contravariantly:
   `collarHomeo.symm.toHomotopyEquiv.trans collarHomotopyEquiv`) yields the theorem.

The only place where the quotient structure of `M̂` is used is the openness of `incCollar`;
everything else happens on `a.Y` and on the cores.
-/
import Mathlib
import Submission.Work.Space.Split

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open Set Topology Function Filter
open scoped Topology unitInterval

namespace Work.Space.Split

namespace RetrB

variable (a : Assembly)

/-! ### Scaling a point of the square

The layer parameter of the filling pieces is the sup norm `sqNorm p = ‖p‖∞` on `[-1,1]²`.  Scaling
`p ↦ s • p` with `s ∈ [0,1]` keeps `p` in the square and multiplies the layer by `s`; at `s = 0`
the point is the core `0`, at `s = 1` it is `p` itself. -/

/-- The sup norm scales by the absolute value of the factor. -/
theorem nrm_smul_abs (c : ℝ) (p : E2) : nrm (c • p) = |c| * nrm p := by
  simp only [nrm, PiLp.smul_apply, smul_eq_mul, abs_mul]
  exact (mul_max_of_nonneg (|p 0|) (|p 1|) (abs_nonneg c)).symm

/-- Scaling a point of the square `[-1,1]²` by a factor in `[0,1]` keeps it in the square. -/
theorem smul_mem_Sq_of_nonneg_le_one {c : ℝ} (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1) {p : E2}
    (hp : p ∈ Sq) : c • p ∈ Sq := by
  rcases hp with ⟨h0, h1⟩
  constructor <;>
  · rw [PiLp.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg hc₀]
    nlinarith [abs_nonneg (p 0), abs_nonneg (p 1)]

/-- Scaling a point of the square by a parameter `s ∈ [0,1]`, as a point of the square. -/
def scalePtB (x : I × SquarePt) : SquarePt :=
  ⟨(x.1 : ℝ) • (x.2 : E2), smul_mem_Sq_of_nonneg_le_one x.1.2.1 x.1.2.2 x.2.2⟩

theorem continuous_scalePtB : Continuous scalePtB :=
  (continuous_subtype_val.comp continuous_fst).smul
    (continuous_subtype_val.comp continuous_snd) |>.subtype_mk _

/-- The layer of a scaled point is the scaled layer. -/
theorem sqNorm_scalePtB (x : I × SquarePt) : sqNorm (scalePtB x) = (x.1 : ℝ) * sqNorm x.2 := by
  show nrm ((x.1 : ℝ) • (x.2 : E2)) = _
  rw [nrm_smul_abs, abs_of_nonneg x.1.2.1]
  rfl

theorem scalePt_zeroB (p : SquarePt) : scalePtB (0, p) = ⟨0, zero_mem_Sq⟩ := by
  refine Subtype.ext ?_
  simp [scalePtB]

theorem scalePt_oneB (p : SquarePt) : scalePtB (1, p) = p := by
  refine Subtype.ext ?_
  simp [scalePtB]

theorem sqNorm_zeroPtB : sqNorm (⟨0, zero_mem_Sq⟩ : SquarePt) = 0 := by
  simp [sqNorm, nrm]

/-! ### Scaling the filling pieces

`fillScale` applies `scalePtB` to the square coordinate of every filling piece, fiberwise in the
torus; `fillSigma` is the same map, written in the "sigma" coordinates
`Σ v, ([-1,1]² × T_v) × [0,1]`, where it is visibly continuous. -/

/-- Fiberwise scaling of the filling pieces. -/
def fillScale (x : I × a.Y) : a.Y :=
  ⟨x.2.1, (scalePtB (x.1, x.2.2.1), x.2.2.2)⟩

/-- The shuffle `[0,1] × Σ v, X v ≃ Σ v, X v × [0,1]` of the product with a disjoint union. -/
def shuf : I × a.Y ≃ₜ (Σ v : Cusp, (SquarePt × a.Torus v) × I) :=
  (Homeomorph.prodComm I a.Y).trans
    (Homeomorph.sigmaProdDistrib (X := fun v : Cusp => SquarePt × a.Torus v) (Y := I))

theorem shuf_apply (x : I × a.Y) : shuf a x = ⟨x.2.1, (x.2.2, x.1)⟩ := rfl

/-- `fillScale` in the shuffled coordinates: a map defined piecewise on a disjoint union. -/
def fillSigma (w : (Σ v : Cusp, (SquarePt × a.Torus v) × I)) : a.Y :=
  ⟨w.1, (scalePtB (w.2.2, w.2.1.1), w.2.1.2)⟩

theorem continuous_fillSigma : Continuous (fillSigma a) := by
  have hkey : Continuous (fun w : (Σ v : Cusp, (SquarePt × a.Torus v) × I) =>
      (Sigma.map (id : Cusp → Cusp)
        (fun (_ : Cusp) (z : (SquarePt × a.Torus _) × I) =>
          (scalePtB (z.2, z.1.1), z.1.2)) w : a.Y)) :=
    Continuous.sigma_map (fun _ =>
      (continuous_scalePtB.comp (continuous_snd.prodMk (continuous_fst.comp continuous_fst))).prodMk
        (continuous_snd.comp continuous_fst))
  have h : (fillSigma a) = (fun w : (Σ v : Cusp, (SquarePt × a.Torus v) × I) =>
      (Sigma.map (id : Cusp → Cusp)
        (fun (_ : Cusp) (z : (SquarePt × a.Torus _) × I) =>
          (scalePtB (z.2, z.1.1), z.1.2)) w : a.Y)) := rfl
  rw [h]
  exact hkey

theorem continuous_fillScale : Continuous (fillScale a) := by
  have h : (fillScale a) = (fillSigma a) ∘ (shuf a) := by
    funext x
    rw [Function.comp_apply, shuf_apply]
    rfl
  rw [h]
  exact (continuous_fillSigma a).comp (shuf a).continuous_toFun

/-! ### The collar and its deformation retraction

`Collar a = {q : a.Y // q ∈ innerCore a.Torus}` is the collar of the filling pieces; the map
`collarScale` is the straight-line (radial in the square coordinate) contraction of the collar onto
its cores, `collarCore` the inclusion of the cores. -/

/-- The collar of the filling pieces: the open set `{‖p‖∞ < 1}` of `a.Y`. -/
abbrev Collar := {q : a.Y // q ∈ innerCore a.Torus}

/-- The contraction of the collar onto its cores. -/
def collarScale (x : I × Collar a) : Collar a :=
  ⟨fillScale a (x.1, x.2.1), by
    change sqNorm (scalePtB (x.1, x.2.1.2.1)) < 1
    rw [sqNorm_scalePtB]
    have h1 : ((x.1 : I) : ℝ) ≤ 1 := x.1.2.2
    have h2 : 0 ≤ sqNorm x.2.1.2.1 := sqNorm_nonneg _
    have h3 : sqNorm x.2.1.2.1 < 1 := x.2.2
    nlinarith⟩

/-- The inclusion of the cores `⊔_v T_v` into the collar. -/
def collarCore (w : Σ v : Cusp, a.Torus v) : Collar a :=
  ⟨⟨w.1, (⟨0, zero_mem_Sq⟩, w.2)⟩, by
    change sqNorm (⟨0, zero_mem_Sq⟩ : SquarePt) < 1
    rw [sqNorm_zeroPtB]
    norm_num⟩

/-- The projection of the collar onto the cores. -/
def collarProj : Collar a → (Σ v : Cusp, a.Torus v) := fun q => ⟨q.1.1, q.1.2.2⟩

theorem continuous_collarProj : Continuous (collarProj a) :=
  (Continuous.sigma_map (fun _ => continuous_snd)).comp continuous_subtype_val

theorem continuous_collarCore : Continuous (collarCore a) := by
  have hkey : Continuous (fun w : (Σ v : Cusp, a.Torus v) =>
      (Sigma.map (id : Cusp → Cusp)
        (fun (_ : Cusp) (t : a.Torus _) => (⟨0, zero_mem_Sq⟩, t)) w : a.Y)) :=
    Continuous.sigma_map (fun _ => continuous_const.prodMk continuous_id)
  have hfun : (fun w : (Σ v : Cusp, a.Torus v) =>
      (Sigma.map (id : Cusp → Cusp)
        (fun (_ : Cusp) (t : a.Torus _) => (⟨0, zero_mem_Sq⟩, t)) w : a.Y))
      = fun w => (collarCore a w : a.Y) := rfl
  rw [hfun] at hkey
  exact hkey.subtype_mk fun _ => by
    change sqNorm (⟨0, zero_mem_Sq⟩ : SquarePt) < 1
    rw [sqNorm_zeroPtB]
    norm_num

theorem continuous_collarScale : Continuous (collarScale a) := by
  have key : Continuous (fun x : I × Collar a => fillScale a (x.1, x.2.1)) :=
    (continuous_fillScale a).comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  exact key.subtype_mk fun x => by
    change sqNorm (scalePtB (x.1, x.2.1.2.1)) < 1
    rw [sqNorm_scalePtB]
    have h1 : ((x.1 : I) : ℝ) ≤ 1 := x.1.2.2
    have h2 : 0 ≤ sqNorm x.2.1.2.1 := sqNorm_nonneg _
    have h3 : sqNorm x.2.1.2.1 < 1 := x.2.2
    nlinarith

theorem collarProj_collarCore (w : Σ v : Cusp, a.Torus v) :
    collarProj a (collarCore a w) = w := rfl

theorem collarScale_zero (q : Collar a) :
    collarScale a ((0 : I), q) = collarCore a (collarProj a q) := by
  refine Subtype.ext ?_
  obtain ⟨⟨v, p, t⟩, -⟩ := q
  simp only [collarScale, collarCore, collarProj, fillScale, scalePt_zeroB]

theorem collarScale_one (q : Collar a) : collarScale a ((1 : I), q) = q := by
  refine Subtype.ext ?_
  obtain ⟨⟨v, p, t⟩, -⟩ := q
  simp only [collarScale, fillScale, scalePt_oneB]

/-- **The collar of the filling pieces deformation retracts onto the cores.**  The homotopy
equivalence is given by `collarProj` (which forgets the square coordinate) and `collarCore`, the
straight-line homotopy between `collarCore ∘ collarProj` and the identity being `collarScale`. -/
theorem collarHomotopyEquiv :
    Nonempty (ContinuousMap.HomotopyEquiv (Collar a) (Σ v : Cusp, a.Torus v)) := by
  refine ⟨ContinuousMap.HomotopyEquiv.mk
    ⟨collarProj a, continuous_collarProj a⟩
    ⟨collarCore a, continuous_collarCore a⟩ ?_ ?_⟩
  · refine ⟨ContinuousMap.Homotopy.mk
      (⟨collarScale a, continuous_collarScale a⟩ :
        ContinuousMap (↑unitInterval × Collar a) (Collar a)) ?_ ?_⟩
    · intro q
      exact collarScale_zero a q
    · intro q
      exact collarScale_one a q
  · have h : ((⟨collarProj a, continuous_collarProj a⟩ :
          ContinuousMap (Collar a) (Σ v : Cusp, a.Torus v)).comp
        (⟨collarCore a, continuous_collarCore a⟩ :
          ContinuousMap (Σ v : Cusp, a.Torus v) (Collar a)))
        = ContinuousMap.id (Σ v : Cusp, a.Torus v) := by
      refine ContinuousMap.ext fun w => ?_
      exact collarProj_collarCore a w
    rw [h]

/-! ### `incY` identifies the collar of the filling pieces with `B`

`a.Bset` is by definition `incY '' innerCore a.Torus`, so `incY` restricts to a bijection
`Collar a → {z : a.Mhat // z ∈ a.Bset}`; the work here is that this bijection is a *homeomorphism*,
i.e. that it is open.  Writing `U ⊆ Collar` open as `V ∩ innerCore` and using the openness
criterion `Assembly.isOpen_iff_sum` for `M̂`, the set `incY '' U` is open in `M̂` (empty trace on the
`M̄`-piece, trace `U` on the filling pieces) and pulls back to the image of `U`. -/

/-- The restriction of `incY` to the collar, as a bijection onto `B`. -/
def incCollar (q : Collar a) : {z : a.Mhat // z ∈ a.Bset} :=
  ⟨a.incY q.1, a.incY_mem_Bset_iff.mpr q.2⟩

theorem continuous_incCollar : Continuous (incCollar a) :=
  (a.continuous_incY.comp continuous_subtype_val).subtype_mk
    (fun q => a.incY_mem_Bset_iff.mpr q.2)

/-- **`incY` restricts to an open map of the collar onto `B`.** -/
theorem isOpenMap_incCollar : IsOpenMap (incCollar a) := by
  intro U hU
  -- `U` open in `Collar` writes as the trace of an open set of `a.Y`.
  obtain ⟨V, hV, hVU⟩ := isOpen_induced_iff.mp hU
  have hUY : IsOpen (Subtype.val '' U) := by
    rw [← hVU, Subtype.image_preimage_coe]
    exact (isOpen_innerCore a.Torus).inter hV
  have hUYmem : ∀ {q : a.Y}, q ∈ Subtype.val '' U → q ∈ innerCore a.Torus := by
    rintro q ⟨q', -, rfl⟩
    exact q'.2
  -- Its image under `incY` is open in `M̂`: the two traces are computed separately.
  have hW : IsOpen (a.incY '' (Subtype.val '' U)) := by
    rw [a.isOpen_iff_sum]
    refine ⟨?_, ?_⟩
    · have hempty : {x : a.Mbar | a.incMbar x ∈ a.incY '' (Subtype.val '' U)} = ∅ := by
        ext x
        simp only [mem_empty_iff_false, iff_false]
        rintro ⟨q, hq, hqx⟩
        have hqin : a.incY q ∈ a.Bset := a.incY_mem_Bset_iff.mpr (hUYmem hq)
        rw [hqx] at hqin
        exact a.incMbar_notMem_Bset x hqin
      rw [hempty]
      exact isOpen_empty
    · have htr : {y : a.Y | a.incY y ∈ a.incY '' (Subtype.val '' U)} = Subtype.val '' U := by
        ext y
        constructor
        · rintro ⟨q, hq, hyq⟩
          have hqy : q = y := a.incY_injective hyq
          rwa [← hqy]
        · intro hy
          exact ⟨y, hy, rfl⟩
      rw [htr]
      exact hUY
  -- `incCollar '' U` is the pull-back of `incY '' U` to the subtype `B`.
  have himg : incCollar a '' U = Subtype.val ⁻¹' (a.incY '' (Subtype.val '' U)) := by
    ext z
    constructor
    · rintro ⟨q, hq, hqz⟩
      exact ⟨q.1, ⟨q, hq, rfl⟩, congrArg Subtype.val hqz⟩
    · rintro ⟨q, hq, hqz⟩
      obtain ⟨q', hq', hq'eq⟩ := hq
      refine ⟨q', hq', Subtype.ext ?_⟩
      show a.incY (q' : a.Y) = z.1
      rw [hq'eq]
      exact hqz
  rw [himg]
  exact hW.preimage continuous_subtype_val

theorem bijective_incCollar : Function.Bijective (incCollar a) := by
  constructor
  · intro q q' h
    refine Subtype.ext ?_
    exact a.incY_injective (Subtype.ext_iff.mp h)
  · intro z
    have hz : ∃ q : a.Y, q ∈ innerCore a.Torus ∧ a.incY q = z.1 := by
      have h := z.2
      change z.1 ∈ (a.incY '' innerCore a.Torus) at h
      exact h
    obtain ⟨q, hq, hqz⟩ := hz
    exact ⟨⟨q, hq⟩, Subtype.ext hqz⟩

/-- A continuous bijection that is an open map has a continuous inverse. -/
theorem continuous_leftInverse_of_isOpenMap {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {f : X → Y} {g : Y → X} (hl : Function.LeftInverse g f)
    (hr : Function.RightInverse g f) (hop : IsOpenMap f) : Continuous g := by
  rw [continuous_def]
  intro U hU
  have h : g ⁻¹' U = f '' U := by
    ext y
    constructor
    · intro hy
      exact ⟨g y, hy, hr y⟩
    · rintro ⟨x, hx, rfl⟩
      show g (f x) ∈ U
      rw [hl x]
      exact hx
  rw [h]
  exact hop U hU

instance instNonemptyCollar : Nonempty (Collar a) := by
  obtain ⟨t⟩ := (inferInstance : ConnectedSpace (a.Torus 0)).toNonempty
  exact ⟨collarCore a ⟨0, t⟩⟩

/-- **`incY` restricts to a homeomorphism of the collar `{‖p‖∞ < 1}` onto `B`.**

The underlying equivalence is `incCollar` with inverse chosen by `Function.invFun`; its continuity
is the general fact that a continuous bijection which is an open map has a continuous inverse. -/
def collarEquiv : Collar a ≃ {z : a.Mhat // z ∈ a.Bset} where
  toFun := incCollar a
  invFun := Function.invFun (incCollar a)
  left_inv := Function.leftInverse_invFun (bijective_incCollar a).1
  right_inv := Function.rightInverse_invFun (bijective_incCollar a).2

def collarHomeo : Collar a ≃ₜ {z : a.Mhat // z ∈ a.Bset} where
  toEquiv := collarEquiv a
  continuous_toFun := continuous_incCollar a
  continuous_invFun := continuous_leftInverse_of_isOpenMap
    (f := incCollar a) (g := Function.invFun (incCollar a))
    (Function.leftInverse_invFun (bijective_incCollar a).1)
    (Function.rightInverse_invFun (bijective_incCollar a).2)
    (isOpenMap_incCollar a)

end RetrB

/-- **`B` deformation retracts onto the cores `⊔_v T_v`.**

`B = M̂ ∖ {‖p‖∞ ≤ 1}` is the union of the open collars `{‖p‖∞ < 1}` of the five filling pieces,
an open subset of the quotient `M̂`; the map which rescales the square coordinate of the collar
linearly to its core `‖p‖∞ = 0` is a deformation retraction of `B` onto `⊔_v T_v`.  Hence there is
a homotopy equivalence between `B` and `Σ v, T_v`.

This is the piece of the Mayer--Vietoris decomposition of `M̂` for the computation of its homology
(the `B`-part of the cover `M̂ = A ∪ B`). -/
theorem retrB_homotopyEquiv (a : Assembly) :
    Nonempty (ContinuousMap.HomotopyEquiv {x : a.Mhat // x ∈ a.Bset}
      (Σ v : Cusp, a.Torus v)) := by
  obtain ⟨h⟩ := RetrB.collarHomotopyEquiv a
  exact ⟨(RetrB.collarHomeo a).symm.toHomotopyEquiv.trans h⟩

end Work.Space.Split
