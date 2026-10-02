import Mathlib
import Submission.Work.Orient.Boundary
import Submission.Work.Orient.Boundary.HalfRestrictIso
import Submission.Work.Orient.Boundary.CoreHomotopyData
import Submission.Work.Cohomology.excision
import Submission.Work.Cohomology.isZero_relSubPunctured

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The localisation isomorphism out of a coordinate half-ball, at any interior point of the ball

`Work.Orient.Boundary.HalfRestrictIso` proves that
`H_{n+1}(W, W∖K) ⟶ H_{n+1}(W, W∖{z})` is an isomorphism for `K = halfBallPiece (n+1) W z r`
(and `z` the centre of the piece).  The Euclidean analogue
`Work.ThomBordism.convexLocalIso` however holds for *every* point `x ∈ K`, and so does the
half-space statement, as long as the whole piece lies in the interior of the model — which is
exactly the hypothesis `hint` recorded in the requested statement
`Work.Orient.Boundary.HalfRestrictIsoAtPoint`.

This file proves that statement.  The proof is the literal adaptation of the two ingredients of
`HalfRestrictIso` to an arbitrary point `x` of the piece:

1. `halfBallPuncturedCore_allDegrees` — the flat model: for the half-space model, an arbitrary
   point `c`, `ρ > 0` and **any** point `x` with `dist x c ≤ ρ`, the pair
   `(H∖{x}, (H∖{x})∖({dist · c ≤ ρ} ∩ {0 < ·}))` has vanishing homology in *every* degree.  This is
   `Work.Orient.Boundary.halfBallPuncturedCore` with the two unused hypotheses dropped and the
   degree made arbitrary (`isZero_relChains_of_homotopyEquiv_incl` is stated in every degree).
2. `halfBallAtPoint_model` — the chart transfer: the resulting vanishing for the punctured pair
   `(W∖{x}, (W∖{x})∖K)` of the charted space, by the two excisions and the chart homeomorphism, as
   in `Work.Orient.Boundary.isZero_punctured_halfBall_of_model`, but with the excluded set `K` (no
   intersection with the interior: this is where `hint` enters, to see that `K` corresponds
   exactly to the model piece `K₀ ∩ {0 < ·}`) and in an arbitrary degree.
3. The triple sequence of `Kᶜ ⊆ {x}ᶜ ⊆ W` then converts the vanishing in degrees `n` and `n+1` into
   the isomorphism, exactly as in `HalfRestrictIso` (and `convexLocalIso`).
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Manifold Topology

namespace Work.Orient.Boundary

noncomputable section

/-! ## 1. The flat model, in every degree and at an arbitrary puncture -/

/-- **The punctured half-ball core of the half-space has vanishing relative homology in every
degree.**

For the half-space model `EuclideanHalfSpace (n+1)`, a point `c` of the half-space, `ρ > 0` and a
point `x ∈ H` with `dist x c ≤ ρ`, the pair consisting of the punctured half-space `{y | y ≠ x}`
and the complement of `K₀ = {y | dist y c ≤ ρ ∧ 0 < y 0}` has vanishing homology in every degree.

This is `Work.Orient.Boundary.halfBallPuncturedCore` with its (unused) hypotheses `c 0 = 0` and
`0 < x 0` removed and the degree `k` arbitrary: the homotopy of `CoreHomotopyData` realises
`Zt ↪ Yt` as a homotopy equivalence of pairs, and `isZero_relChains_of_homotopyEquiv_incl` is
stated in every degree. -/
theorem halfBallPuncturedCore_allDegrees (n : ℕ) (c : EuclideanHalfSpace (n + 1)) (ρ : ℝ)
    (hρ : 0 < ρ) (x : EuclideanHalfSpace (n + 1)) (hx : dist x.1 c.1 ≤ ρ) (k : ℕ) :
    CategoryTheory.Limits.IsZero ((Work.Cohomology.relChains
      (TopCat.of {y : EuclideanHalfSpace (n + 1) | y ≠ x})
      {y : {y : EuclideanHalfSpace (n + 1) | y ≠ x} |
        ¬ (dist y.1.1 c.1 ≤ ρ ∧ 0 < y.1.1 0)}).homology k) := by
  classical
  let Yt : Type := {y : EuclideanHalfSpace (n + 1) | y ≠ x}
  let Zt : Set Yt := {y : Yt | ¬ (dist y.1.1 c.1 ≤ ρ ∧ 0 < y.1.1 0)}
  -- the path stays in the punctured half-space
  have hpath : ∀ (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (y : Yt),
      0 ≤ corePath n ρ c x t y 0 ∧ corePath n ρ c x t y ≠ x.1 :=
    fun t ht0 ht1 y => corePath_mem_halfspace n ρ c x y ht0 ht1
  -- the time-one point lies in the core
  have hend : ∀ y : Yt, ¬ (dist (corePath n ρ c x 1 y) c.1 ≤ ρ ∧
      0 < corePath n ρ c x 1 y 0) :=
    fun y => corePath_one_mem_core n ρ c x hρ hx y
  -- the path as a point of `Yt`
  let toY : (t : ℝ) → 0 ≤ t → t ≤ 1 → Yt → Yt := fun t ht0 ht1 y =>
    ⟨⟨corePath n ρ c x t y, (hpath t ht0 ht1 y).1⟩,
      fun h => (hpath t ht0 ht1 y).2 (congrArg Subtype.val h)⟩
  have htoYcont : ∀ (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1), Continuous (toY t ht0 ht1) := by
    intro t ht0 ht1
    have hbase : Continuous fun y : Yt => corePath n ρ c x t y :=
      (continuous_corePath n ρ c x).comp (continuous_const.prodMk continuous_id)
    have h1 : Continuous fun y : Yt =>
        (⟨corePath n ρ c x t y, (hpath t ht0 ht1 y).1⟩ : EuclideanHalfSpace (n + 1)) :=
      Continuous.subtype_mk hbase (fun y => (hpath t ht0 ht1 y).1)
    exact Continuous.subtype_mk h1
      (fun y => fun h => (hpath t ht0 ht1 y).2 (congrArg Subtype.val h))
  -- the homotopy of the punctured half-space
  let Hmap : C(↑unitInterval × Yt, Yt) :=
    ⟨fun q => toY (q.1 : ℝ) q.1.2.1 q.1.2.2 q.2, by
      have hbase : Continuous fun q : ↑unitInterval × Yt => corePath n ρ c x (q.1 : ℝ) q.2 :=
        (continuous_corePath n ρ c x).comp
          ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
      have h1 : Continuous fun q : ↑unitInterval × Yt =>
          (⟨corePath n ρ c x (q.1 : ℝ) q.2,
            (hpath (q.1 : ℝ) q.1.2.1 q.1.2.2 q.2).1⟩ : EuclideanHalfSpace (n + 1)) :=
        Continuous.subtype_mk hbase (fun q => (hpath (q.1 : ℝ) q.1.2.1 q.1.2.2 q.2).1)
      exact Continuous.subtype_mk h1
        (fun q => fun h => (hpath (q.1 : ℝ) q.1.2.1 q.1.2.2 q.2).2 (congrArg Subtype.val h))⟩
  -- the endpoint map into the core
  let g : TopCat.of Yt ⟶ TopCat.of Zt := TopCat.ofHom
    ⟨fun y => ⟨toY 1 zero_le_one le_rfl y, hend y⟩,
      Continuous.subtype_mk (htoYcont 1 zero_le_one le_rfl) (fun y => hend y)⟩
  have hY : TopCat.Homotopy (𝟙 (TopCat.of Yt))
      (g ≫ Work.Cohomology.subtypeIncl (TopCat.of Yt) Zt) :=
    ContinuousMap.Homotopy.mk Hmap
      (fun y => by
        apply Subtype.ext
        apply Subtype.ext
        exact corePath_zero n ρ c x y)
      (fun y => rfl)
  -- the same homotopy, restricted to the core
  let hZm : C(↑unitInterval × (TopCat.of Zt), TopCat.of Zt) :=
    ⟨fun q => ⟨toY (q.1 : ℝ) q.1.2.1 q.1.2.2 q.2.1,
        corePath_mem_core n ρ c x hx q.2.1 q.2.2 q.1.2.1 q.1.2.2⟩, by
      have hbase : Continuous fun q : ↑unitInterval × (TopCat.of Zt) =>
          toY (q.1 : ℝ) q.1.2.1 q.1.2.2 q.2.1 :=
        Hmap.continuous.comp
          (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
      exact Continuous.subtype_mk hbase
        (fun q => corePath_mem_core n ρ c x hx q.2.1 q.2.2 q.1.2.1 q.1.2.2)⟩
  have hZhom : TopCat.Homotopy (𝟙 (TopCat.of Zt))
      (Work.Cohomology.subtypeIncl (TopCat.of Yt) Zt ≫ g) :=
    ContinuousMap.Homotopy.mk hZm
      (fun z => by
        show hZm (0, z) = z
        apply Subtype.ext
        apply Subtype.ext
        apply Subtype.ext
        exact corePath_zero n ρ c x z.1)
      (fun z => rfl)
  exact isZero_relChains_of_homotopyEquiv_incl g hZhom.symm hY.symm k

/-! ## 2. The chart transfer -/

/-- **Vanishing of the top relative homology of a punctured coordinate half-ball, at any of its
points.**

For a space `W` charted in the half-space model, a centre `y`, a radius `r` with the standard side
condition, a point `x` of the piece `K = halfBallPiece (n+1) W y r` such that **every** point of `K`
is a non-boundary point of `W`, and any degree `k`: if the flat model statement holds for the
transported data, then `H_k(W∖{x}, (W∖{x})∖K) = 0`.

The proof is the chart transfer of `Work.Orient.Boundary.isZero_punctured_halfBall_of_model`:
closed-set excision (`Work.Cohomology.excision`) shrinks `W∖{x}` to the chart source, the chart
identifies the two pair-chain complexes, and a second excision inside the half-space expands the
chart target back to the whole half-space.  The difference from the existing lemma is that the
excluded set is `K` itself rather than `K ∩ W°`: the hypothesis `hint` is used exactly to see that
under the chart `K` corresponds to `K₀ ∩ {0 < ·}`. -/
theorem halfBallAtPoint_model (n : ℕ) (W : TopCat) [T2Space W]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    (y : W) (r : ℝ) (hr : 0 < r) (hgood : Work.Orient.halfBallGood (n + 1) W y r)
    (x : W) (hx : x ∈ Work.Orient.halfBallPiece (n + 1) W y r)
    (hint : ∀ w ∈ Work.Orient.halfBallPiece (n + 1) W y r,
      w ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)
    (k : ℕ)
    (hmodel : CategoryTheory.Limits.IsZero ((Work.Cohomology.relChains
      (TopCat.of {v : EuclideanHalfSpace (n + 1) | v ≠ (chartAt (EuclideanHalfSpace (n + 1)) y) x})
      {v : {v : EuclideanHalfSpace (n + 1) | v ≠ (chartAt (EuclideanHalfSpace (n + 1)) y) x} |
        ¬ (dist (v.1.1 : EuclideanSpace ℝ (Fin (n + 1)))
              (((chartAt (EuclideanHalfSpace (n + 1)) y) y).1 : EuclideanSpace ℝ (Fin (n + 1))) ≤ r / 2 ∧
           0 < v.1.1 0)}).homology k)) :
    CategoryTheory.Limits.IsZero ((Work.Cohomology.relChains (TopCat.of {z : W | z ≠ x})
      {z : {z : W | z ≠ x} |
        (z : W) ∉ Work.Orient.halfBallPiece (n + 1) W y r}).homology k) := by
  classical
  let e := chartAt (EuclideanHalfSpace (n + 1)) y
  have hxsrc : x ∈ e.source := hx.2
  have hKclosed : IsClosed (Work.Orient.halfBallPiece (n + 1) W y r) :=
    (IsCoordHalfBall.isCompact (n := n + 1) ⟨y, r, hr, hgood, rfl⟩).isClosed
  have hKsrc : Work.Orient.halfBallPiece (n + 1) W y r ⊆ e.source := fun w hw => hw.2
  -- the model core, and the correspondence between it and `K`
  let K0 : Set (EuclideanHalfSpace (n + 1)) :=
    Work.Orient.halfIncl (n + 1) ⁻¹'
      Metric.closedBall (Work.Orient.halfIncl (n + 1) (e y)) (r / 2)
  let D : Set (EuclideanHalfSpace (n + 1)) :=
    K0 ∩ {v : EuclideanHalfSpace (n + 1) | 0 < v.1 0}
  have hK0target : K0 ⊆ e.target :=
    fun v hv => hgood (Metric.closedBall_subset_ball (by linarith) hv)
  have hDK0 : D ⊆ K0 := fun v hv => hv.1
  have hK0closed : IsClosed K0 :=
    (Metric.isClosed_closedBall (x := Work.Orient.halfIncl (n + 1) (e y)) (ε := r / 2)).preimage
      continuous_subtype_val
  have hcorr : ∀ w : W, w ∈ e.source →
      (w ∈ Work.Orient.halfBallPiece (n + 1) W y r ↔ e w ∈ D) := by
    intro w hw
    have h1 : w ∈ Work.Orient.halfBallPiece (n + 1) W y r ↔ e w ∈ K0 :=
      ⟨fun h => h.1, fun h => ⟨h, hw⟩⟩
    refine ⟨fun hwK => ⟨h1.mp hwK, ?_⟩, fun hwD => h1.mpr hwD.1⟩
    exact chartAt_interior_pos (n := n) (W := W) (z := y) hw (hint w hwK)
  -- ### Step 1: excise `W∖{x}` down to the chart source
  let X : TopCat := TopCat.of {z : W | z ≠ x}
  let A : Set X := {z : X | (z : W) ∉ Work.Orient.halfBallPiece (n + 1) W y r}
  let Z : Set X := {z : X | (z : W) ∉ e.source}
  have hZclosed : IsClosed Z := by
    have heq : Z = (fun z : X => (z : W)) ⁻¹' (e.source)ᶜ := by ext z; exact Iff.rfl
    rw [heq]
    exact e.open_source.isClosed_compl.preimage continuous_subtype_val
  have hsub : closure Z ⊆ interior A := by
    intro z hz
    rw [hZclosed.closure_eq] at hz
    have hzW : (z : W) ∉ e.source := hz
    have hzK : (z : W) ∉ Work.Orient.halfBallPiece (n + 1) W y r := fun h => hzW (hKsrc h)
    have hnbhd : ({z' : X | (z' : W) ∉ Work.Orient.halfBallPiece (n + 1) W y r} ∈ 𝓝 z) :=
      (hKclosed.isOpen_compl.preimage continuous_subtype_val).mem_nhds hzK
    exact mem_interior_iff_mem_nhds.mpr
      (Filter.mem_of_superset hnbhd (fun z' hz' => hz'))
  obtain ⟨e0⟩ := Work.Cohomology.excision X A Z hsub k
  -- ### The model side
  let XH : TopCat := TopCat.of {v : EuclideanHalfSpace (n + 1) | v ≠ e x}
  let AH : Set XH := {v : XH | (v : EuclideanHalfSpace (n + 1)) ∉ D}
  let ZH : Set XH := {v : XH | (v : EuclideanHalfSpace (n + 1)) ∉ e.target}
  have hmod : CategoryTheory.Limits.IsZero ((Work.Cohomology.relChains XH AH).homology k) := hmodel
  have hZHclosed : IsClosed ZH := by
    have heq : ZH = (fun v : XH => (v : EuclideanHalfSpace (n + 1))) ⁻¹' (e.target)ᶜ := by
      ext v; exact Iff.rfl
    rw [heq]
    exact e.open_target.isClosed_compl.preimage continuous_subtype_val
  have hsubH : closure ZH ⊆ interior AH := by
    intro v hv
    rw [hZHclosed.closure_eq] at hv
    have hvK0 : (v : EuclideanHalfSpace (n + 1)) ∉ K0 := fun h => hv (hK0target h)
    have hnbhd : ({v' : XH | (v' : EuclideanHalfSpace (n + 1)) ∉ K0} ∈ 𝓝 v) :=
      (hK0closed.preimage continuous_subtype_val).isOpen_compl.mem_nhds hvK0
    exact mem_interior_iff_mem_nhds.mpr
      (Filter.mem_of_superset hnbhd (fun v' hv' h => hv' (hDK0 h)))
  obtain ⟨e2⟩ := Work.Cohomology.excision XH AH ZH hsubH k
  -- ### The chart homeomorphism between the two chart sources
  let U1 : Type := {z : X | z ∉ Z}
  let A1 : Set U1 := {z : U1 | (z : X) ∈ A}
  let U2 : Type := {v : XH | v ∉ ZH}
  let A2 : Set U2 := {v : U2 | (v : XH) ∈ AH}
  have hnn : ∀ {p : Prop}, ¬¬p → p := fun h => Classical.byContradiction h
  let φ : U1 ≃ₜ U2 :=
    { toFun := fun z =>
        ⟨⟨e (((z : U1) : X) : W), fun heq =>
            ((z : U1) : X).2 (e.injOn (hnn z.2) hxsrc heq)⟩,
          fun h => h (e.map_source (hnn z.2))⟩
      invFun := fun v =>
        ⟨⟨e.symm (((v : U2) : XH) : EuclideanHalfSpace (n + 1)), fun heq =>
            ((v : U2) : XH).2 (by
              have hv : (((v : U2) : XH) : EuclideanHalfSpace (n + 1)) ∈ e.target := hnn v.2
              rw [← e.right_inv hv, heq])⟩,
          fun h => h (e.map_target (hnn v.2))⟩
      left_inv := fun z => by
        apply Subtype.ext
        apply Subtype.ext
        exact e.left_inv (hnn z.2)
      right_inv := fun v => by
        apply Subtype.ext
        apply Subtype.ext
        exact e.right_inv (hnn v.2)
      continuous_toFun := Continuous.subtype_mk (Continuous.subtype_mk
        (e.continuousOn.comp_continuous (continuous_subtype_val.comp continuous_subtype_val)
          (fun z => hnn z.2)) _) _
      continuous_invFun := Continuous.subtype_mk (Continuous.subtype_mk
        (e.symm.continuousOn.comp_continuous (continuous_subtype_val.comp continuous_subtype_val)
          (fun v => hnn v.2)) _) _ }
  have hA1 : ∀ z : U1, z ∈ A1 ↔ φ z ∈ A2 := by
    intro z
    have hw : (((z : U1) : X) : W) ∈ e.source := hnn z.2
    show (((z : U1) : X) : W) ∉ Work.Orient.halfBallPiece (n + 1) W y r ↔
      e (((z : U1) : X) : W) ∈ D → False
    exact not_congr (hcorr (((z : U1) : X) : W) hw)
  obtain ⟨e1⟩ := homeoRelChainsIso φ A1 A2 hA1 k
  exact IsZero.of_iso (IsZero.of_iso (IsZero.of_iso hmod e2.symm) e1) e0

/-! ## 3. The isomorphism -/

/-- **`Work.Orient.Boundary.HalfRestrictIsoAtPoint`**: for a coordinate half-ball
`K = halfBallPiece (n+1) W z r` all of whose points are non-boundary points of `W`, and **any** point
`x ∈ K`, the restriction `H_{n+1}(W, W∖K) ⟶ H_{n+1}(W, W∖{x})` is an isomorphism.

This is the half-space analogue of `Work.ThomBordism.convexLocalIso` (which holds for any `x ∈ K`),
and the sharpening of `Work.Orient.Boundary.HalfRestrictIso` (the case `x = z`). -/
theorem HalfRestrictIsoAtPoint (n : ℕ) (W : TopCat) [CompactSpace W] [T2Space W]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W] (z : W) (r : ℝ) (hr : 0 < r)
    (hball : Work.Orient.halfBallGood (n + 1) W z r)
    (hint : ∀ y ∈ Work.Orient.halfBallPiece (n + 1) W z r,
      y ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)
    (x : W) (hx : x ∈ Work.Orient.halfBallPiece (n + 1) W z r) :
    CategoryTheory.IsIso (HomologicalComplex.homologyMap (Work.Cohomology.relCokerMap W
      (Work.Orient.halfBallPiece (n + 1) W z r)ᶜ ({x} : Set W)ᶜ
      (Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr hx))) (n + 1)) := by
  classical
  have hsub : (Work.Orient.halfBallPiece (n + 1) W z r)ᶜ ⊆ ({x} : Set W)ᶜ :=
    Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr hx)
  -- the punctured vanishing, in the honest subspace model, in degrees `n+1` and `n`
  have hdist : dist (((chartAt (EuclideanHalfSpace (n + 1)) z) x).1 : EuclideanSpace ℝ (Fin (n + 1)))
      (((chartAt (EuclideanHalfSpace (n + 1)) z) z).1 : EuclideanSpace ℝ (Fin (n + 1))) ≤ r / 2 :=
    Metric.mem_closedBall.mp hx.1
  have hvanish : ∀ k : ℕ, IsZero ((Work.Cohomology.relChains (TopCat.of {w : W | w ≠ x})
      {w : {w : W | w ≠ x} |
        (w : W) ∉ Work.Orient.halfBallPiece (n + 1) W z r}).homology k) := by
    intro k
    refine halfBallAtPoint_model n W z r hr hball x hx hint k ?_
    exact halfBallPuncturedCore_allDegrees n
      ((chartAt (EuclideanHalfSpace (n + 1)) z) z) (r / 2) (by linarith)
      ((chartAt (EuclideanHalfSpace (n + 1)) z) x) hdist k
  -- the triple `Kᶜ ⊆ {x}ᶜ ⊆ W`
  let S : ShortComplex (ChainComplex (ModuleCat ℤ) ℕ) :=
    Work.Cohomology.tripleShort W (Work.Orient.halfBallPiece (n + 1) W z r)ᶜ
      ({x} : Set W)ᶜ hsub
  have hSEX : S.ShortExact :=
    Work.Cohomology.relChains_triple_shortExact W _ _ hsub
  have hSg : S.g = Work.Cohomology.relCokerMap W (Work.Orient.halfBallPiece (n + 1) W z r)ᶜ
      ({x} : Set W)ᶜ hsub :=
    Work.Cohomology.tripleShort_g W _ _ hsub
  have hz0 : IsZero (S.X₁.homology (n + 1)) := by
    obtain ⟨eiso⟩ := Work.Cohomology.relSubPunctured_homology_iso W x
      (Work.Orient.halfBallPiece (n + 1) W z r) hx (n + 1)
    exact IsZero.of_iso (hvanish (n + 1)) eiso
  have hz1 : IsZero (S.X₁.homology ((n + 1) - 1)) := by
    obtain ⟨eiso⟩ := Work.Cohomology.relSubPunctured_homology_iso W x
      (Work.Orient.halfBallPiece (n + 1) W z r) hx ((n + 1) - 1)
    exact IsZero.of_iso (hvanish ((n + 1) - 1)) eiso
  have hinj : Function.Injective
      (ModuleCat.Hom.hom (HomologicalComplex.homologyMap S.g (n + 1))) := by
    have hf0 : HomologicalComplex.homologyMap S.f (n + 1) = 0 :=
      IsZero.eq_zero_of_src hz0 _
    have hr2 : (ModuleCat.Hom.hom (HomologicalComplex.homologyMap S.f (n + 1))).range =
        (ModuleCat.Hom.hom (HomologicalComplex.homologyMap S.g (n + 1))).ker :=
      ShortComplex.Exact.moduleCat_range_eq_ker (hSEX.homology_exact₂ (n + 1))
    rw [hf0, ModuleCat.hom_zero, LinearMap.range_zero] at hr2
    exact LinearMap.ker_eq_bot.mp hr2.symm
  have hsurj : Function.Surjective
      (ModuleCat.Hom.hom (HomologicalComplex.homologyMap S.g (n + 1))) := by
    have hij : (ComplexShape.down ℕ).Rel (n + 1) ((n + 1) - 1) :=
      Nat.sub_add_cancel (by omega)
    have hδ0 : hSEX.δ (n + 1) ((n + 1) - 1) hij = 0 := IsZero.eq_zero_of_tgt hz1 _
    have hr3 : (ModuleCat.Hom.hom (HomologicalComplex.homologyMap S.g (n + 1))).range =
        (ModuleCat.Hom.hom (hSEX.δ (n + 1) ((n + 1) - 1) hij)).ker :=
      ShortComplex.Exact.moduleCat_range_eq_ker
        (hSEX.homology_exact₃ (n + 1) ((n + 1) - 1) hij)
    rw [hδ0, ModuleCat.hom_zero, LinearMap.ker_zero] at hr3
    exact LinearMap.range_eq_top.mp hr3
  have hbij : Function.Bijective (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
      (Work.Cohomology.relCokerMap W (Work.Orient.halfBallPiece (n + 1) W z r)ᶜ
        ({x} : Set W)ᶜ hsub) (n + 1))) := by
    rw [← hSg]
    exact ⟨hinj, hsurj⟩
  exact (ConcreteCategory.isIso_iff_bijective _).mpr hbij

end

end Work.Orient.Boundary
