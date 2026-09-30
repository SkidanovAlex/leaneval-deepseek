/-
# The boundary of the filling square is a circle

The filling piece of the Ratcliffe--Tschantz assembly is the square `Sq = [-1,1]²`
(`Work.Space.Sq`), whose layer parameter is the sup norm `sqNorm p = max |p 0| |p 1|`.  Its
*gluing boundary* `sqBoundary = {p | sqNorm p = 1}` is the closed curve along which the filling
piece is attached to the cusped boundary of the hyperbolic piece `M̄`; as a topological space it
must be a circle, and this is what the present file proves:

`{p : SquarePt // sqNorm p = 1} ≃ₜ AddCircle 1`.

The proof does not reparametrise the square: the chapter `Work.Cusp` already contains the
parametrisation `bndOfU : ℝ → ∂Sq` of the boundary by the normalised perimeter parameter
(`(1,1)` at `u = 0`, counterclockwise, one lap per unit), and the homeomorphism
`BarS : ℝ/ℤ → ∂Sq`, `θ ↦ bndOfU θ`, of `Work.Cusp.isOpenEmbedding_layerPtSq` (there it is the
first factor of the layer chart `layerPtSq = t • bndOfU u`).  So the work here is to identify the
subtype `{p : SquarePt // sqNorm p = 1}` of the *assembly* (a subtype of the square subtype)
with the subtype `Sph = {q : E2 // nrm q = 1}` of the plane used in `Work.Cusp`:

* `Sph` and `{p : SquarePt // sqNorm p = 1}` carry the *same* points, and the two maps
  `bdryToSph` and `sphToBdry` back and forth are continuous inverse bijections, so they are
  homeomorphisms (`Continuous.homeoOfEquivCompactToT2`: the source is compact, the target is
  Hausdorff);
* `BarS` is a continuous bijection out of the compact circle, hence a homeomorphism
  `AddCircle 1 ≃ₜ Sph`.

Composing the second with the inverse of the first gives the claim.
-/
import Mathlib
import Submission.Work.Cusp.isOpenEmbedding_layerPtSq
import Submission.Work.Space.Assembly
import Submission.Work.Cusp.abs_le_nrm

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.RTOwed

open Set Topology Function

/-! ### The two descriptions of the boundary of the square

`Work.Cusp.Sph = {q : E2 // nrm q = 1}` is the boundary of the square as a subspace of the plane
(the target of `Work.Cusp.BarS`), while `{p : Work.Space.SquarePt // Work.Space.sqNorm p = 1}`
is the same set as a subspace of the (compact) square.  The two lemmas below pass between the
defining conditions: a point of the plane with `nrm q = 1` is in the square `Sq` because each
coordinate is bounded by the sup norm (`abs_le_nrm`). -/

theorem sq_mem_of_nrm_eq_one {q : Work.Cusp.E2} (h : Work.Cusp.nrm q = 1) :
    q ∈ Work.Space.Sq := by
  constructor
  · show |q 0| ≤ 1
    have := Work.Cusp.abs_le_nrm q 0
    rw [h] at this; exact this
  · show |q 1| ≤ 1
    have := Work.Cusp.abs_le_nrm q 1
    rw [h] at this; exact this

theorem sqNorm_eq_one_of_nrm {q : Work.Cusp.E2} (h : Work.Cusp.nrm q = 1)
    (hmem : q ∈ Work.Space.Sq) : Work.Space.sqNorm (⟨q, hmem⟩ : Work.Space.SquarePt) = 1 := by
  show Work.Cusp.nrm q = 1
  exact h

/-! ### `{p : SquarePt // sqNorm p = 1}` and `Sph` are homeomorphic -/

/-- Forget the square: a point of the gluing boundary of the filling piece, read as a point of the
plane of sup norm `1`. -/
noncomputable def bdryToSph (p : {p : Work.Space.SquarePt // Work.Space.sqNorm p = 1}) :
    Work.Cusp.Sph :=
  ⟨p.1.1, by show Work.Cusp.nrm p.1.1 = 1; exact p.2⟩

theorem bdryToSph_continuous : Continuous bdryToSph := by
  exact Continuous.subtype_mk
    (continuous_subtype_val.comp continuous_subtype_val) (fun p => by
      show Work.Cusp.nrm p.1.1 = 1
      exact p.2)

theorem bdryToSph_injective : Injective bdryToSph := by
  intro p p' h
  have h1 : (bdryToSph p : Work.Cusp.E2) = bdryToSph p' := congrArg Subtype.val h
  have h2 : p.1.1 = p'.1.1 := h1
  exact Subtype.ext (Subtype.ext h2)

theorem bdryToSph_surjective : Surjective bdryToSph := by
  intro q
  refine ⟨⟨⟨q.1, sq_mem_of_nrm_eq_one q.2⟩, sqNorm_eq_one_of_nrm q.2 _⟩, ?_⟩
  exact Subtype.ext rfl

/-- The gluing boundary `{p : SquarePt // sqNorm p = 1}` of the filling piece is compact: it is a
closed subset of the compact square. -/
instance : CompactSpace {p : Work.Space.SquarePt // Work.Space.sqNorm p = 1} :=
  isCompact_iff_compactSpace.mp (Work.Space.isClosed_sqBoundary.isCompact)

/-- **The two descriptions of the boundary of the square are homeomorphic**: forgetting the
ambient square is a continuous bijection from the compact gluing boundary onto the Hausdorff
subspace `Sph` of the plane. -/
noncomputable def bdryHomeoSph :
    {p : Work.Space.SquarePt // Work.Space.sqNorm p = 1} ≃ₜ Work.Cusp.Sph :=
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective bdryToSph ⟨bdryToSph_injective, bdryToSph_surjective⟩)
    bdryToSph_continuous

/-! ### `Sph` is a circle -/

/-- `Work.Cusp.BarS` is continuous: it is the lift of the `1`-periodic function `bndOfU` to
`ℝ/ℤ`, and a lift of a continuous periodic function is continuous. -/
theorem continuous_BarS : Continuous Work.Cusp.BarS :=
  Continuous.subtype_mk
    (AddCircle.liftIco_zero_continuous (by
      simpa using (Work.Cusp.bndOfU_add_int (0:ℝ) 1).symm) Work.Cusp.continuous_bndOfU.continuousOn)
    Work.Cusp.Bar_mem

/-- **The circle `ℝ/ℤ` is homeomorphic to the boundary `Sph` of the square**: `BarS` is a
continuous bijection out of a compact space into a Hausdorff space. -/
noncomputable def barS_homeo : AddCircle (1:ℝ) ≃ₜ Work.Cusp.Sph :=
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective Work.Cusp.BarS ⟨Work.Cusp.BarS_inj, Work.Cusp.BarS_surj⟩)
    continuous_BarS

/-- **The gluing boundary of the filling square is a circle.** -/
theorem sqBoundary_homeo_circle :
    Nonempty ({p : Work.Space.SquarePt // Work.Space.sqNorm p = 1} ≃ₜ
      AddCircle (1 : ℝ)) :=
  ⟨bdryHomeoSph.trans barS_homeo.symm⟩

end Work.RTOwed
