import Mathlib
import Submission.Work.Milnor.Construction
import Submission.Work.Milnor.glue2_diffeomorph
import Submission.Work.Glue.Basic
import Submission.Work.Glue.glued_isManifold
import Submission.Work.Glue.mem_groupoid_of_contMDiffOn
import Submission.Work.Model.prod_transfer

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Milnor's `M_k` as a two-chart clutching construction

Milnor (*On manifolds homeomorphic to the 7-sphere*, Ann. of Math. **64** (1956), 399–405)
constructs, for each integer `k`, the closed smooth 7-manifold
`M_k = (D⁴ × S³) ∪_f (D⁴ × S³)` where `f(x, y) = (x, x^k * y * x⁻¹)` (unit quaternions).
This is the total space of the `S³`-bundle over `S⁴ = ℍP¹` with clutching function
`u ↦ (y ↦ u^k y u⁻¹)`.

The purpose of this file is to realise `M_k` as a *gluing of two open pieces* in the sense of
`Submission.Glue.Data`, which immediately provides it with a `ChartedSpace` and `IsManifold`
structure (and, through `Work.Model.prod_transfer`, with one modelled on `ℝ⁷`).

## The two-chart description

Write `S⁴ = ℝ⁴ ∪_{ℝ⁴∖{0}} ℝ⁴`, where the two copies of `ℝ⁴` are glued along `ℝ⁴ ∖ {0}` by the
inversion `x ↦ x / ‖x‖²`.  Pulling the `S³`-bundle back to the two hemispheres exhibits `M_k` as
the quotient of two copies of `ℝ⁴ × S³` glued along `(ℝ⁴ ∖ {0}) × S³` by

`φ(x, y) = (x / ‖x‖²,  u^{-k} y u^{-1})`,   where `u = x / ‖x‖ ∈ S³`.

Thus `M_k` is `Glue.Data.Glued` for `X = Y = ℝ⁴ × S³`, `U = V = {x ≠ 0}` and `φ` as above; only
*one* gluing is required (the two "pieces" are two copies of the same ambient manifold, which is
allowed).  This is considerably simpler than glueing the disc bundles themselves, and it avoids
manifolds with boundary altogether.

## Conventions

With `clutchMap k` using `clutch (-k)`, the clutching function is `u ↦ u^{-k} y u⁻¹`, whose class
in `π₃(SO(4)) ≅ ℤ ⊕ ℤ` is `(-k, -1)`; the Euler number of the bundle is `-k - 1`.  The choice
`k = -2` gives Euler number `1`, i.e. a homotopy `7`-sphere, and corresponds to Milnor's `M_1`
(the first exotic sphere).
-/

open scoped Manifold ContDiff Topology
open Metric (sphere)
open TopologicalSpace Set

namespace Submission.Milnor

noncomputable section

/-! ## The inversion `x ↦ x / ‖x‖²` of `ℝ⁴` -/

/-- The inversion of `ℝ⁴`, `x ↦ x / ‖x‖²`, written as a scalar multiple so that it is defined
everywhere (it is `0` at `0`). -/
def invBase (x : EuclideanSpace ℝ (Fin 4)) : EuclideanSpace ℝ (Fin 4) :=
  ((‖x‖ : ℝ) ^ 2)⁻¹ • x

/-- The norm of the inversion is the inverse of the norm (also at `0`, where `0⁻¹ = 0`). -/
lemma norm_invBase (x : EuclideanSpace ℝ (Fin 4)) : ‖invBase x‖ = (‖x‖)⁻¹ := by
  rw [invBase, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity), ← inv_pow, pow_two,
    mul_assoc]
  rcases eq_or_ne (‖x‖) 0 with h | h
  · simp [h]
  · rw [inv_mul_cancel₀ h, mul_one]

lemma invBase_ne_zero {x : EuclideanSpace ℝ (Fin 4)} (hx : x ≠ 0) : invBase x ≠ 0 := by
  rw [← norm_ne_zero_iff, norm_invBase]
  exact inv_ne_zero (norm_ne_zero_iff.mpr hx)

/-- The inversion is an involution away from `0`. -/
lemma invBase_invBase {x : EuclideanSpace ℝ (Fin 4)} (hx : x ≠ 0) : invBase (invBase x) = x := by
  have h1 : ‖invBase x‖ = (‖x‖)⁻¹ := norm_invBase x
  show ((‖invBase x‖ ^ 2)⁻¹) • invBase x = x
  rw [h1, invBase, smul_smul, inv_pow, inv_inv,
    mul_inv_cancel₀ (pow_ne_zero 2 (norm_ne_zero_iff.mpr hx)), one_smul]

/-- The inversion is smooth away from the origin. -/
lemma contMDiffOn_invBase :
    ContMDiffOn (𝓡 4) (𝓡 4) ∞ invBase {x : EuclideanSpace ℝ (Fin 4) | x ≠ 0} := by
  rw [contMDiffOn_iff_contDiffOn]
  have hs : ContDiffOn ℝ ∞ (fun x : EuclideanSpace ℝ (Fin 4) => ‖x‖ ^ 2) {x | x ≠ 0} :=
    (ContDiffOn.norm ℝ (f := id) contDiff_id.contDiffOn (fun x hx => hx)).pow 2
  have hinv : ContDiffOn ℝ ∞ (fun x : EuclideanSpace ℝ (Fin 4) => (‖x‖ ^ 2)⁻¹) {x | x ≠ 0} :=
    hs.inv (fun x hx => pow_ne_zero 2 (norm_ne_zero_iff.mpr hx))
  exact ContDiffOn.smul (𝕜' := ℝ) (F := EuclideanSpace ℝ (Fin 4)) hinv contDiff_id.contDiffOn

/-! ## The gluing map -/

/-- The gluing map `φ` of the two-chart description of `M_k`:
`φ(x, y) = (x/‖x‖², clutch (-k) (x/‖x‖, y))`. -/
def clutchMap (k : ℤ) (p : MSpace) : MSpace :=
  (invBase p.1, clutch (-k) (unitDir p.1, p.2))

/-- The inverse of `clutchMap k`: `φ⁻¹(x, y) = (x/‖x‖², u^k y u)` with `u = x/‖x‖`. -/
def clutchMapInv (k : ℤ) (p : MSpace) : MSpace :=
  (invBase p.1, Work.Milnor.invTwist k (unitDir p.1, p.2))

/-- The open set `{x ≠ 0} × S³ ⊆ ℝ⁴ × S³` along which the two charts are glued. -/
def clutchOpens : Opens MSpace where
  carrier := {p : MSpace | p.1 ≠ 0}
  is_open' := isOpen_ne_fun continuous_fst continuous_const

lemma mem_clutchOpens {p : MSpace} : p ∈ clutchOpens ↔ p.1 ≠ 0 := Iff.rfl

/-- The inversion does not change the direction `unitDir`. -/
lemma unitDir_invBase (x : EuclideanSpace ℝ (Fin 4)) (hx : x ≠ 0) :
    unitDir (invBase x) = unitDir x := by
  have hix : invBase x ≠ 0 := invBase_ne_zero hx
  refine Subtype.ext ?_
  rw [Work.Milnor.unitDir_coe _ hix, Work.Milnor.unitDir_coe _ hx, Work.Milnor.dirVal,
    Work.Milnor.dirVal, norm_invBase, invBase, map_smul, smul_smul]
  have hscal : (‖x‖⁻¹)⁻¹ * (‖x‖ ^ 2)⁻¹ = ‖x‖⁻¹ := by
    rw [inv_inv, ← inv_pow, pow_two, ← mul_assoc,
      mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx), one_mul]
  rw [hscal]


/-- `p ↦ unitDir p.1` is smooth on any open set avoiding the origin of `ℝ⁴` (a generalisation,
to arbitrary open sets, of `Work.Milnor.unitDir_contMDiffOn`). -/
lemma unitDir_contMDiffOn_of (U : Opens MSpace) (hU : ∀ p ∈ U, p.1 ≠ 0) :
    ContMDiffOn ((𝓡 4).prod (𝓡 3)) (𝓡 3) ∞ (fun p : MSpace => unitDir p.1)
      (U : Set MSpace) := by
  have hdirOn : ContMDiffOn ((𝓡 4).prod (𝓡 3)) 𝓘(ℝ, Quaternion ℝ) ∞
      (fun p : MSpace => Work.Milnor.dirVal p.1) (U : Set MSpace) := by
    have hfst : ContMDiffOn ((𝓡 4).prod (𝓡 3)) (𝓡 4) ∞
        (Prod.fst : MSpace → EuclideanSpace ℝ (Fin 4)) (U : Set MSpace) :=
      contMDiff_fst.contMDiffOn
    exact (Work.Milnor.dirVal_contMDiffOn.comp hfst (fun p hp => hU p hp)).congr (fun _ _ => rfl)
  have hcoe : ContMDiffOn ((𝓡 4).prod (𝓡 3)) 𝓘(ℝ, Quaternion ℝ) ∞
      (fun p : MSpace => ((unitDir p.1 : QS3) : Quaternion ℝ)) (U : Set MSpace) :=
    hdirOn.congr (fun p hp => Work.Milnor.unitDir_coe p.1 (hU p hp))
  have hglob : ContMDiff ((𝓡 4).prod (𝓡 3)) 𝓘(ℝ, Quaternion ℝ) ∞
      (fun p : ↥U => ((unitDir (p : MSpace).1 : QS3) : Quaternion ℝ)) := by
    intro p
    exact (contMDiffAt_subtype_iff (U := U)
      (f := fun q : MSpace => ((unitDir q.1 : QS3) : Quaternion ℝ)) (x := p)).mpr
      (hcoe.contMDiffAt (U.2.mem_nhds p.2))
  have hmem : ∀ p : ↥U,
      ((unitDir (p : MSpace).1 : QS3) : Quaternion ℝ) ∈ sphere (0 : Quaternion ℝ) 1 :=
    fun p => (unitDir (p : MSpace).1).2
  have hsphere : ContMDiff ((𝓡 4).prod (𝓡 3)) (𝓡 3) ∞
      (fun p : ↥U => unitDir (p : MSpace).1) :=
    (ContMDiff.codRestrict_sphere hglob hmem).congr (fun p => Subtype.ext rfl)
  intro p hp
  exact ((contMDiffAt_subtype_iff (U := U)
    (f := fun q : MSpace => unitDir q.1) (x := ⟨p, hp⟩)).mp (hsphere ⟨p, hp⟩)).contMDiffWithinAt

/-- The gluing map is smooth on `{x ≠ 0}`. -/
lemma contMDiffOn_clutchMap (k : ℤ) :
    ContMDiffOn ((𝓡 4).prod (𝓡 3)) ((𝓡 4).prod (𝓡 3)) ∞ (clutchMap k) (clutchOpens : Set MSpace) := by
  have hfst : ContMDiffOn ((𝓡 4).prod (𝓡 3)) (𝓡 4) ∞
      (fun p : MSpace => invBase p.1) (clutchOpens : Set MSpace) :=
    contMDiffOn_invBase.comp contMDiff_fst.contMDiffOn (fun p hp => hp)
  have hdir : ContMDiffOn ((𝓡 4).prod (𝓡 3)) (𝓡 3) ∞
      (fun p : MSpace => unitDir p.1) (clutchOpens : Set MSpace) :=
    unitDir_contMDiffOn_of clutchOpens (fun p hp => hp)
  have hsnd : ContMDiffOn ((𝓡 4).prod (𝓡 3)) (𝓡 3) ∞
      (fun p : MSpace => clutch (-k) (unitDir p.1, p.2)) (clutchOpens : Set MSpace) :=
    (Work.Quaternion.clutch_smooth (-k)).comp_contMDiffOn
      (hdir.prodMk contMDiff_snd.contMDiffOn)
  exact hfst.prodMk hsnd

/-- The inverse gluing map is smooth on `{x ≠ 0}`. -/
lemma contMDiffOn_clutchMapInv (k : ℤ) :
    ContMDiffOn ((𝓡 4).prod (𝓡 3)) ((𝓡 4).prod (𝓡 3)) ∞ (clutchMapInv k)
      (clutchOpens : Set MSpace) := by
  have hfst : ContMDiffOn ((𝓡 4).prod (𝓡 3)) (𝓡 4) ∞
      (fun p : MSpace => invBase p.1) (clutchOpens : Set MSpace) :=
    contMDiffOn_invBase.comp contMDiff_fst.contMDiffOn (fun p hp => hp)
  have hdir : ContMDiffOn ((𝓡 4).prod (𝓡 3)) (𝓡 3) ∞
      (fun p : MSpace => unitDir p.1) (clutchOpens : Set MSpace) :=
    unitDir_contMDiffOn_of clutchOpens (fun p hp => hp)
  have hsnd : ContMDiffOn ((𝓡 4).prod (𝓡 3)) (𝓡 3) ∞
      (fun p : MSpace => Work.Milnor.invTwist k (unitDir p.1, p.2)) (clutchOpens : Set MSpace) :=
    (Work.Milnor.contMDiff_invTwist k).comp_contMDiffOn
      (hdir.prodMk contMDiff_snd.contMDiffOn)
  exact hfst.prodMk hsnd

/-- `clutchMapInv k` is a left inverse of `clutchMap k` on `{x ≠ 0}`. -/
lemma clutchMapInv_clutchMap (k : ℤ) (p : MSpace) (hp : p.1 ≠ 0) :
    clutchMapInv k (clutchMap k p) = p := by
  rw [clutchMapInv, clutchMap]
  refine Prod.ext ?_ ?_
  · exact invBase_invBase hp
  · rw [unitDir_invBase p.1 hp]
    exact Work.Milnor.invTwist_clutch k (unitDir p.1) p.2

/-- `clutchMapInv k` is a right inverse of `clutchMap k` on `{x ≠ 0}`. -/
lemma clutchMap_clutchMapInv (k : ℤ) (p : MSpace) (hp : p.1 ≠ 0) :
    clutchMap k (clutchMapInv k p) = p := by
  rw [clutchMapInv, clutchMap]
  refine Prod.ext ?_ ?_
  · exact invBase_invBase hp
  · rw [unitDir_invBase p.1 hp]
    exact Work.Milnor.clutch_invTwist k (unitDir p.1) p.2

/-! ## The gluing data -/

/-- The gluing map as an open partial homeomorphism of `ℝ⁴ × S³`. -/
def clutchPartialHomeomorph (k : ℤ) : OpenPartialHomeomorph MSpace MSpace where
  toFun := clutchMap k
  invFun := clutchMapInv k
  source := clutchOpens
  target := clutchOpens
  map_source' := fun _ hp => invBase_ne_zero hp
  map_target' := fun _ hp => invBase_ne_zero hp
  left_inv' := fun p hp => clutchMapInv_clutchMap k p hp
  right_inv' := fun p hp => clutchMap_clutchMapInv k p hp
  continuousOn_toFun := (contMDiffOn_clutchMap k).continuousOn
  continuousOn_invFun := (contMDiffOn_clutchMapInv k).continuousOn
  open_source := clutchOpens.2
  open_target := clutchOpens.2

/-- The gluing data whose `Glued` space is Milnor's `M_k`. -/
noncomputable def clutchData (k : ℤ) :
    Submission.Glue.Data ((𝓡 4).prod (𝓡 3)) ∞ MSpace MSpace where
  U := clutchOpens
  V := clutchOpens
  isOpen_U := clutchOpens.2
  isOpen_V := clutchOpens.2
  φ := clutchPartialHomeomorph k
  source_φ := rfl
  target_φ := rfl
  mem_groupoid :=
    Work.Glue.mem_groupoid_of_contMDiffOn (contMDiffOn_clutchMap k) (contMDiffOn_clutchMapInv k)

/-- **Milnor's manifold `M_k`**, as a quotient of two copies of `ℝ⁴ × S³`. -/
abbrev Mk (k : ℤ) : Type := (clutchData k).Glued

instance instNonemptyMSpace : Nonempty MSpace :=
  ⟨(0, ⟨(1 : Quaternion ℝ), by simp⟩)⟩

instance (k : ℤ) : TopologicalSpace (Mk k) :=
  Submission.Glue.Data.instTopologicalSpace (clutchData k)

instance (k : ℤ) : ChartedSpace (ModelProd (EuclideanSpace ℝ (Fin 4)) (EuclideanSpace ℝ (Fin 3)))
    (Mk k) :=
  Submission.Glue.Data.instChartedSpace (clutchData k)

instance (k : ℤ) : IsManifold ((𝓡 4).prod (𝓡 3)) ∞ (Mk k) :=
  Work.Glue.glued_isManifold (clutchData k)

/-! ## Re-charting over `ℝ⁷` -/

/-- **Milnor's `M_k` is a closed smooth `7`-manifold**: the first four conjuncts of the challenge
statement, for the specific manifold `M_k`. -/
theorem exists_mk_manifold (k : ℤ) :
    ∃ (M : Type) (_ : TopologicalSpace M)
      (_ : ChartedSpace (EuclideanSpace ℝ (Fin 7)) M)
      (_ : IsManifold (𝓡 7) ∞ M), True := by
  obtain ⟨c, hc⟩ := Work.Model.prod_transfer (m := 4) (n := 3) (M := Mk k)
  exact ⟨Mk k, inferInstance, c, hc, trivial⟩

end

end Submission.Milnor
