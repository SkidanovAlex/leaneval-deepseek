/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Area CH — `GalCharts.toCharts`: COV over `k'` from COV′ over `k`

This is §6 of `Submission/Work/NOTES_LEAD_jacobian_charts3.md`: the passage from the
Galois-equivariant covering `GalCharts C R P0` (COV′, consumed by area `DS`) to the covering
`Charts (C_{k'}) R' P0'` of the base-changed curve over `k'` (COV, consumed by area `GC`).

The comparison of symmetric powers is *not* proved here (it is area `SY`'s `Sym.baseChangeIso`,
delivered in the shape of the structure `Work.Charts.SymBC` of `SymBC.lean`).  What this file
does is *derive* the covering.  Given the `SymBC` bundle `B` for the extension `k'/k`:

* the Brill–Noether chart `d` over `k` base-changes to the chart `d'` over `k'` by
  `d'.chart = B.β ⁻¹ᵁ d.V` and `d'.δ = 1`, so `d'.V = B.β ⁻¹ᵁ d.V`
  (`SymBC.landsIn_preimage`, `Scheme.basicOpen_one`), and `d'.i_eq_zero_of_landsIn` is
  `d.i_eq_zero_of_landsIn` transported along `B.pts` (`SymBC.pic0Map`, `SymBC.pts_divOf`,
  `SymBC.ell_eq`); the chart is nonempty because `B.β` is surjective and `d.V ≠ ⊥`;
* the centres of `Charts` are `B.pts.symm ∘ E`, and the covering property follows from
  `GalCharts.orbit_cov` on the *one* orbit of a covering centre, using that `SymBC.pic0Map` is
  injective on degree-zero classes (`SymBC.pic0Map_injective`) and commutes with the chart
  classes (`SymBC.pic0Map_chartClass`).

**Convention (fields).**  `Charts` over `k'` requires the covering for every field extension
`F ⊇ k'` (with *no* reference to `k`), while `GalCharts.orbit_cov` supplies it for field
extensions `F ⊇ k` receiving a `k`-embedding `k' → F`.  Given `F ⊇ k'` we therefore install
*locally*, inside the proof of `cov`, the `k`-algebra structure `k → k' → F` of the composite
(`compAlgebra`) together with its compatibility `IsScalarTower k k' F`; this is exactly the
structure under which `orbit_cov` speaks.  Nothing is added to the statement.
-/
import Submission.Work.Charts.SymBC
import Submission.Work.Charts.Step3Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open scoped Classical AlgebraicGeometry MonoidalCategory
open scoped Work.GCBasics

namespace Work.Charts

open Work.CurveBasics
open Work.GCBasics

noncomputable section

variable {K : Type u} [Field K] {C : Curve K} [Work.SpecLin.DivBase C]

/-! ### The algebra structure of a tower of field extensions -/

/-- The `K`-algebra structure on a `k'`-algebra `F` obtained from the composite
`K → k' → F`.  It is used in the proof of `GalCharts.toCharts` to make a `k'`-algebra `F` into a
`K`-algebra, so that `GalCharts.orbit_cov` — which speaks about `k'`-algebras over `k` — applies
to it. -/
abbrev compAlgebra (K : Type u) [Field K] (k' : Type u) [Field k'] [Algebra K k']
    (F : Type u) [Field F] [Algebra k' F] : Algebra K F :=
  Algebra.compHom F (algebraMap K k')

/-- The two algebra structures of a tower agree: `IsScalarTower K k' F` for the `K`-algebra
structure `compAlgebra` of the composite `K → k' → F` and the given `Algebra k' F`. -/
theorem isScalarTower_compAlgebra (K : Type u) [Field K] (k' : Type u) [Field k']
    [Algebra K k'] (F : Type u) [Field F] [Algebra k' F] :
    letI : Algebra K F := compAlgebra K k' F
    IsScalarTower K k' F := by
  letI : Algebra K F := compAlgebra K k' F
  exact ⟨fun x y z => by
    simp only [Algebra.smul_def]
    rw [show (algebraMap K F) x = algebraMap k' F (algebraMap K k' x) from rfl, map_mul]
    ring⟩

variable {R : RochData C} [Work.SpecLin.SymGeom C R.g]
variable {L : Type u} [Field L] [Algebra K L] [Work.SpecLin.DivBase (C.baseChange L)]
variable {R' : RochData (C.baseChange L)} [Work.SpecLin.SymGeom (C.baseChange L) R'.g]

/-! ### Transport of the chart along the comparison `β : Sym^g(C_L) ⟶ Sym^g C` -/

namespace SymBC

variable (B : SymBC R L R')

/-- **`SymBC.pic0Map` commutes with the chart classes**: the class of `divOf y - divOf E` on
`C_L` is transported to the class of `divOf (pts y) - divOf (pts E)` on `C`.  This is
`SymBC.pts_divOf` together with additivity of `SymBC.bcDiv`. -/
theorem pic0Map_chartClass {F : Type u} [Field F] [Algebra L F] [Algebra K F]
    [IsScalarTower K L F] (y E : FPt (Sym (C.baseChange L) R'.g) F) :
    B.pic0Map (chartClass y E) = chartClass (B.pts y) (B.pts E) := by
  have h1 : chartClass y E =
      ((⟨divOf y - divOf E, Ddeg_divOf_sub y E⟩ : div0 (C.baseChange L) F)
        : Pic0 (C.baseChange L) F) := rfl
  have h2 : chartClass (B.pts y) (B.pts E) =
      ((⟨divOf (B.pts y) - divOf (B.pts E), Ddeg_divOf_sub (B.pts y) (B.pts E)⟩ : div0 C F)
        : Pic0 C F) := rfl
  rw [h1, h2, B.pic0Map_mk']
  congr 1
  apply Subtype.ext
  change B.bcDiv (divOf y - divOf E) = divOf (B.pts y) - divOf (B.pts E)
  rw [map_sub, B.pts_divOf y, B.pts_divOf E]

/-- **The preimage of the Brill–Noether chart along `β`**: a point of `Sym^g(C_L)` lands in
`β ⁻¹ᵁ V` exactly when its image under `SymBC.pts` lands in `V`. -/
theorem landsIn_preimage (d : BNData C R) {F : Type u} [Field F] [Algebra L F] [Algebra K F]
    [IsScalarTower K L F] (p : FPt (Sym (C.baseChange L) R'.g) F) :
    p.LandsIn (B.β ⁻¹ᵁ d.V) ↔ (B.pts p).LandsIn d.V := by
  show p.left (IsLocalRing.closedPoint F) ∈ (B.β ⁻¹ᵁ d.V)
    ↔ (B.pts p).left (IsLocalRing.closedPoint F) ∈ d.V
  rw [B.pts_left, Scheme.Hom.mem_preimage]
  exact Iff.rfl

/-- **Base change of the field commutes with `SymBC.pts`**, in the orientation used by the
covering: the `pts`-image of the base change of `pts.symm q` is the base change of `q`. -/
theorem pts_symm_map {F : Type u} [Field F] [Algebra L F] [Algebra K F] [IsScalarTower K L F]
    (q : FPt (Sym C R.g) L) :
    B.pts (RPt.map (IsScalarTower.toAlgHom L L F) ((B.pts (F := L)).symm q))
      = RPt.map (IsScalarTower.toAlgHom K L F) q := by
  have h : AlgHom.restrictScalars K (IsScalarTower.toAlgHom L L F)
      = IsScalarTower.toAlgHom K L F :=
    AlgHom.ext fun x => by
      rw [AlgHom.restrictScalars_apply, IsScalarTower.toAlgHom_apply,
        IsScalarTower.toAlgHom_apply]
  simp only [B.pts_map, Equiv.apply_symm_apply, h]

end SymBC

/-! ### `GalCharts.toCharts` -/

namespace GalCharts

variable {P0 : unitSch K ⟶ C.toOver}

/-- **COV over `k'` from COV′ over `k`.**  Given the Galois-equivariant covering `D` of `Pic⁰`
for the curve `C` over `K` and the base-change comparison `B` of symmetric powers for the finite
Galois extension `D.k' / K`, there is a covering of `Pic⁰` of the base-changed curve
`C_{k'}` over `D.k'` by translates of the base-changed Brill–Noether chart.

The base-changed chart `d'` has `d'.chart = B.β ⁻¹ᵁ d.V` and `d'.δ = 1` (so `d'.V` is that
affine open), and its centres are `B.pts.symm ∘ E`.  All the content is in `SymBC`: the
comparison `B.pts` identifies the two `Sym^g`'s, `B.pic0Map` identifies the two `Pic⁰`'s
(compatibly with the chart classes), and `GalCharts.orbit_cov` provides the covering on a single
Galois orbit of a centre. -/
theorem toCharts (D : GalCharts C R P0) (db : Work.SpecLin.DivBase (C.baseChange D.k'))
    (R' : RochData (C.baseChange D.k')) (sg : Work.SpecLin.SymGeom (C.baseChange D.k') R'.g)
    (P0' : unitSch D.k' ⟶ (C.baseChange D.k').toOver)
    (B : @SymBC K _ C _ R _ D.k' _ _ db R' sg) :
    Nonempty (@Charts D.k' _ (C.baseChange D.k') db R' sg P0') := by
  letI : Work.SpecLin.DivBase (C.baseChange D.k') := db
  letI : Work.SpecLin.SymGeom (C.baseChange D.k') R'.g := sg
  haveI hβ : IsAffineHom B.β := B.isAffineHom_β
  -- the base-changed chart: `chart = β ⁻¹ᵁ V`, `δ = 1`
  let chart : (Sym (C.baseChange D.k') R'.g).left.Opens := B.β ⁻¹ᵁ D.d.V
  have hchart : IsAffineOpen chart := IsAffineOpen.preimage D.d.isAffineOpen_V B.β
  have hii : ∀ {F : Type u} [Field F] [Algebra D.k' F]
      (p : FPt (Sym (C.baseChange D.k') R'.g) F),
      RPt.LandsIn p ((Sym (C.baseChange D.k') R'.g).left.basicOpen
        (1 : Γ((Sym (C.baseChange D.k') R'.g).left, chart))) →
      iOf (C.baseChange D.k') R'.W (divOf p) = 0 := by
    intro F _ _ p hp
    letI : Algebra K F := compAlgebra K D.k' F
    haveI hST : IsScalarTower K D.k' F := isScalarTower_compAlgebra K D.k' F
    rw [Scheme.basicOpen_one] at hp
    have hp' : (B.pts p).LandsIn D.d.V := (B.landsIn_preimage D.d p).mp hp
    have h1 : ell (C.baseChange D.k') (divOf p) = 1 := by
      rw [B.ell_eq (divOf p), B.pts_divOf p]
      exact D.d.ell_eq_one_of_landsIn (B.pts p) hp'
    exact (R'.i_eq_zero_iff_ell_eq_one (Ddeg_divOf p)).mpr h1
  have hne : (Sym (C.baseChange D.k') R'.g).left.basicOpen
      (1 : Γ((Sym (C.baseChange D.k') R'.g).left, chart)) ≠ ⊥ := by
    rw [Scheme.basicOpen_one]
    change B.β ⁻¹ᵁ D.d.V ≠ ⊥
    intro hbot
    apply D.d.ne_bot
    rw [← le_bot_iff]
    intro x hx
    obtain ⟨y, hy⟩ := B.surjective_β x
    have hy' : y ∈ (B.β ⁻¹ᵁ D.d.V :
        (Sym (C.baseChange D.k') R'.g).left.Opens) := by
      rw [Scheme.Hom.mem_preimage, hy]
      exact hx
    rw [hbot] at hy'
    exact (TopologicalSpace.Opens.mem_bot.mp hy').elim
  let d' : BNData (C.baseChange D.k') R' :=
    BNData.mk B.Q' B.U' B.hU' B.h' B.h_mem' B.h_span' chart hchart
      (1 : Γ((Sym (C.baseChange D.k') R'.g).left, chart)) hii hne
  have hV : d'.V = B.β ⁻¹ᵁ D.d.V := by
    rw [BNData.V]
    exact Scheme.basicOpen_one _
  refine ⟨Charts.mk d' D.ι (fintype := D.fintype)
    (fun i => (B.pts (F := D.k')).symm (D.E i)) ?_⟩
  intro F _ _ c
  -- install the `K`-algebra structure `K → k' → F` under which `orbit_cov` speaks
  letI : Algebra K F := compAlgebra K D.k' F
  haveI hST : IsScalarTower K D.k' F := isScalarTower_compAlgebra K D.k' F
  obtain ⟨i, hi⟩ := D.orbit_cov (IsScalarTower.toAlgHom K D.k' F) (B.pic0Map c)
  have hi1 : InChart D.d (RPt.map (IsScalarTower.toAlgHom K D.k' F) (D.E i))
      (B.pic0Map c) := by simpa using hi 1
  obtain ⟨y, hy, hyc⟩ := hi1
  refine ⟨i, (B.pts (F := F)).symm y, ?_, ?_⟩
  · rw [hV, B.landsIn_preimage D.d, Equiv.apply_symm_apply]
    exact hy
  · apply B.pic0Map_injective
    rw [B.pic0Map_chartClass, Equiv.apply_symm_apply, B.pts_symm_map (D.E i)]
    exact hyc

/-- **The chart datum of area `GC` over `k'`, from COV′ over `k`**: the composition of
`GalCharts.toCharts` with `Charts.toChartDatum`, so that a consumer of area `GC` does not have
to chain the two. -/
theorem toChartDatum (D : GalCharts C R P0) (db : Work.SpecLin.DivBase (C.baseChange D.k'))
    (R' : RochData (C.baseChange D.k')) (sg : Work.SpecLin.SymGeom (C.baseChange D.k') R'.g)
    (P0' : unitSch D.k' ⟶ (C.baseChange D.k').toOver)
    (B : @SymBC K _ C _ R _ D.k' _ _ db R' sg) :
    Nonempty (@ChartDatum D.k' _ (C.baseChange D.k') db R' sg P0') := by
  obtain ⟨Dc⟩ := D.toCharts db R' sg P0' B
  exact ⟨@Charts.toChartDatum D.k' _ (C.baseChange D.k') db R' sg P0' Dc⟩

end GalCharts

end

end Work.Charts
