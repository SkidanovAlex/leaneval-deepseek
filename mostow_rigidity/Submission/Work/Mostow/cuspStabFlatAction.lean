import Mathlib
import Submission.Work.Mostow.QIDefs
import Submission.Work.Mostow.cuspCorrDefs
import Submission.Work.Mostow.horSpec
import Submission.Work.Mostow.hptOf_yc
import Submission.Work.Mostow.hptOf_level
import Submission.Work.Mostow.finite_translates_inter_compact

/-!
# The flat action of the cusp stabiliser on `ξ^⊥`

For a boundary point `ξ ∈ Sph n` and a level `D > 0`, the horosphere `{lev ξ = D}` of `ξ` is
identified with the orthocomplement `ξ^⊥ ⊆ E n` by the normalised flat coordinate
`u ↦ yc ξ u` (the inverse identification is `y ↦ hptOf ξ y D`, `hptOf_yc`).  An isometry
`g : PO n 1` with `bd g ξ = ξ` that preserves the level function `lev ξ` (`hlev`) then acts on the
flat space `ξ^⊥` by a Euclidean isometry

`flatMap hξ D g y = yc ξ (g • hptOf ξ y D)`

(`horSpec` supplies the isometry property: two points of the same horosphere are at hyperbolic
distance `arcosh (1 + (D ‖y - y'‖)²/2)`, and `g` is a hyperbolic isometry, so the flat distance is
preserved).  `flatMap` is a group action: `flatMap 1 = id` and
`flatMap (g * h) = flatMap g ∘ flatMap h`.

Transporting along an isometric identification `flatPhi ξ : ξ^⊥ ≃ᵢ E (flatDim ξ)` turns the action
of the cusp stabiliser `Γ_ξ = cuspStab Γ ξ` into a monoid homomorphism

`rhoHom : Γ_ξ →* (E (flatDim ξ) ≃ᵢ E (flatDim ξ))`

which acts properly discontinuously (discreteness of `Γ` via `finite_translates_inter_compact`),
cocompactly (the hypothesis `hcoc` at the level `D`) and with kernel acting trivially on the
level-`D` horosphere.  This is exactly `Work.Mostow.cuspStabFlatAction`.
-/

set_option maxHeartbeats 1600000

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory
open scoped Topology

noncomputable section

variable {n : ℕ}

/-! ## The flat space `ξ^⊥` -/

/-- The orthocomplement of `ξ` in the chart `E n`: the space in which the flat (horospherical)
coordinates at `ξ` live. -/
noncomputable def horoSub (ξ : E n) : Submodule ℝ (E n) := (Submodule.span ℝ {ξ})ᗮ

lemma mem_horoSub {ξ y : E n} : y ∈ horoSub ξ ↔ inner ℝ ξ y = 0 := by
  rw [horoSub]
  exact Submodule.mem_orthogonal_singleton_iff_inner_right

lemma mem_horoSub_comm {ξ y : E n} : y ∈ horoSub ξ ↔ inner ℝ y ξ = 0 := by
  rw [mem_horoSub, real_inner_comm]

/-- For a unit vector `ξ`, the `ξ^⊥`-component of `u` is orthogonal to `ξ`. -/
lemma inner_xi_wc {ξ : E n} (hξ : ξ ∈ Sph n) (u : E n) : inner ℝ ξ (wc ξ u) = 0 := by
  have h1 : inner ℝ ξ ξ = 1 := hptOf_level_aux_inner_self hξ
  rw [wc, inner_sub_right, real_inner_smul_right, h1, mul_one, real_inner_comm ξ u, sub_self]

lemma yc_mem_horoSub {ξ : E n} (hξ : ξ ∈ Sph n) (u : E n) : yc ξ u ∈ horoSub ξ := by
  rw [mem_horoSub, yc, real_inner_smul_right, inner_xi_wc hξ u, mul_zero]

/-- The normalised flat coordinate of `u` at `ξ`, as an element of `ξ^⊥`. -/
noncomputable def ycH {ξ : E n} (hξ : ξ ∈ Sph n) (u : E n) : ↥(horoSub ξ) :=
  ⟨yc ξ u, yc_mem_horoSub hξ u⟩

lemma ycH_coe {ξ : E n} (hξ : ξ ∈ Sph n) (u : E n) :
    ((ycH hξ u : ↥(horoSub ξ)) : E n) = yc ξ u := rfl

/-- The map induced by `g` on the flat space `ξ^⊥`, in the horospherical (`yc`) coordinates at
level `D`. -/
noncomputable def flatMap {ξ : E n} (hξ : ξ ∈ Sph n) (D : ℝ) (g : PO n 1)
    (y : ↥(horoSub ξ)) : ↥(horoSub ξ) :=
  ycH hξ (g • hptOf ξ (y : E n) D)

lemma flatMap_one {ξ : E n} (hA : POBasic n) (hξ : ξ ∈ Sph n) (D : ℝ) (hD : 0 < D)
    (y : ↥(horoSub ξ)) : flatMap hξ D 1 y = y := by
  apply Subtype.ext
  show yc ξ ((1 : PO n 1) • hptOf ξ ((y : ↥(horoSub ξ)) : E n) D) = (y : E n)
  rw [hA.one_smul]
  exact (hptOf_level ξ hξ D hD (y : E n) (mem_horoSub_comm.mp y.2)).2

lemma flatMap_mul {ξ : E n} (hA : POBasic n) (hξ : ξ ∈ Sph n) (D : ℝ) (hD : 0 < D)
    (g : PO n 1) (h : PO n 1) (hlevg : ∀ u : E n, lev ξ (g • u) = lev ξ u)
    (hlevh : ∀ u : E n, lev ξ (h • u) = lev ξ u) (y : ↥(horoSub ξ)) :
    flatMap hξ D (g * h) y = flatMap hξ D g (flatMap hξ D h y) := by
  have hy : inner ℝ (y : E n) ξ = 0 := mem_horoSub_comm.mp y.2
  have hEq : h • hptOf ξ (y : E n) D = hptOf ξ (yc ξ (h • hptOf ξ (y : E n) D)) D := by
    have hlv : lev ξ (h • hptOf ξ (y : E n) D) = D := by
      rw [hlevh, (hptOf_level ξ hξ D hD (y : E n) hy).1]
    exact (hptOf_yc ξ hξ D hD (h • hptOf ξ (y : E n) D) hlv).symm
  apply Subtype.ext
  show yc ξ ((g * h) • hptOf ξ ((y : ↥(horoSub ξ)) : E n) D)
    = yc ξ (g • hptOf ξ (yc ξ (h • hptOf ξ ((y : ↥(horoSub ξ)) : E n) D)) D)
  rw [show (g * h) • hptOf ξ ((y : ↥(horoSub ξ)) : E n) D
      = g • hptOf ξ (yc ξ (h • hptOf ξ ((y : ↥(horoSub ξ)) : E n) D)) D from by
    rw [hA.mul_smul]
    exact congrArg (fun z => g • z) hEq]

/-- The flat action of a level-preserving isometry fixing `ξ` is a Euclidean isometry of `ξ^⊥`. -/
lemma flatMap_isometry (hA : POActionProp n) (hI : HypIsometryProp n) (hn : 1 ≤ n)
    {ξ : E n} (hξ : ξ ∈ Sph n) (D : ℝ) (hD : 0 < D) (g : PO n 1)
    (hg : bd g ξ = ξ) (hlevg : ∀ u : E n, lev ξ (g • u) = lev ξ u) :
    Isometry (flatMap hξ D g) := by
  obtain ⟨-, -, -, ρ, hρ1, hρ2, -⟩ := horSpec n hn hA hI ξ hξ D hD g hg hlevg
  intro y y'
  rw [edist_dist, edist_dist, Subtype.dist_eq, Subtype.dist_eq, dist_eq_norm, dist_eq_norm]
  have hy : inner ℝ (y : E n) ξ = 0 := mem_horoSub_comm.mp y.2
  have hy' : inner ℝ (y' : E n) ξ = 0 := mem_horoSub_comm.mp y'.2
  have e3 : ρ (y : E n) = yc ξ (g • hptOf ξ (y : E n) D) := by
    rw [← (hρ1 (y : E n) hy).2]
    exact (hptOf_level ξ hξ D hD (ρ (y : E n)) (hρ1 (y : E n) hy).1).2.symm
  have e4 : ρ (y' : E n) = yc ξ (g • hptOf ξ (y' : E n) D) := by
    rw [← (hρ1 (y' : E n) hy').2]
    exact (hptOf_level ξ hξ D hD (ρ (y' : E n)) (hρ1 (y' : E n) hy').1).2.symm
  have h2 := hρ2 (y : E n) (y' : E n) hy hy'
  rw [e3, e4] at h2
  exact congrArg ENNReal.ofReal h2

/-- The flat action of `g`, bundled as an isometry equivalence of `ξ^⊥`. -/
noncomputable def flatIso (hA : POActionProp n) (hI : HypIsometryProp n) (hn : 1 ≤ n)
    {ξ : E n} (hξ : ξ ∈ Sph n) (D : ℝ) (hD : 0 < D) (g : PO n 1)
    (hg : bd g ξ = ξ) (hlevg : ∀ u : E n, lev ξ (g • u) = lev ξ u)
    (hg' : bd g⁻¹ ξ = ξ) (hlevg' : ∀ u : E n, lev ξ (g⁻¹ • u) = lev ξ u) :
    ↥(horoSub ξ) ≃ᵢ ↥(horoSub ξ) :=
  IsometryEquiv.mk
    { toFun := flatMap hξ D g
      invFun := flatMap hξ D g⁻¹
      left_inv := by
        intro y
        rw [← flatMap_mul (POBasic.ofProp hA) hξ D hD (g⁻¹) g hlevg' hlevg y,
          inv_mul_cancel, flatMap_one (POBasic.ofProp hA) hξ D hD y]
      right_inv := by
        intro y
        rw [← flatMap_mul (POBasic.ofProp hA) hξ D hD g (g⁻¹) hlevg hlevg' y,
          mul_inv_cancel, flatMap_one (POBasic.ofProp hA) hξ D hD y] }
    (flatMap_isometry hA hI hn hξ D hD g hg hlevg)

/-! ## The standard Euclidean model of the flat space -/

/-- The dimension of the flat space at `ξ`. -/
noncomputable def flatDim (ξ : E n) : ℕ := Module.finrank ℝ ↥(horoSub ξ)

/-- An isometric identification of the flat space `ξ^⊥` with the standard Euclidean space
`E (flatDim ξ)`. -/
noncomputable def flatPhi (ξ : E n) : ↥(horoSub ξ) ≃ᵢ E (flatDim ξ) :=
  (stdOrthonormalBasis ℝ ↥(horoSub ξ)).repr.toIsometryEquiv

lemma flatPhi_zero (ξ : E n) : flatPhi ξ (0 : ↥(horoSub ξ)) = 0 := by
  show (stdOrthonormalBasis ℝ ↥(horoSub ξ)).repr (0 : ↥(horoSub ξ)) = (0 : E (flatDim ξ))
  exact map_zero _

lemma norm_flatPhi (ξ : E n) (z : ↥(horoSub ξ)) : ‖flatPhi ξ z‖ = ‖(z : E n)‖ := by
  have h := (flatPhi ξ).dist_eq z 0
  rw [dist_zero_right, flatPhi_zero ξ, dist_zero_right] at h
  rwa [show ‖z‖ = ‖(z : E n)‖ from rfl] at h

/-! ## The induced flat action of the cusp stabiliser -/

lemma cuspStab_bd (hA : POActionProp n) {Γ : Subgroup (PO n 1)} {ξ : E n} {hξ : ξ ∈ Sph n}
    (g : cuspStab (POBasic.ofProp hA) Γ ξ hξ) : bd (((g : Γ)) : PO n 1) ξ = ξ := g.2

lemma cuspStab_lev (hA : POActionProp n) {Γ : Subgroup (PO n 1)} {ξ : E n} {hξ : ξ ∈ Sph n}
    (hlev : ∀ (γ : Γ) (u : E n), bd (γ : PO n 1) ξ = ξ → lev ξ ((γ : PO n 1) • u) = lev ξ u)
    (g : cuspStab (POBasic.ofProp hA) Γ ξ hξ) :
    ∀ u : E n, lev ξ ((((g : Γ)) : PO n 1) • u) = lev ξ u :=
  fun u => hlev (g : Γ) u (cuspStab_bd hA g)

lemma cuspStab_bd_inv (hA : POActionProp n) {Γ : Subgroup (PO n 1)} {ξ : E n} {hξ : ξ ∈ Sph n}
    (g : cuspStab (POBasic.ofProp hA) Γ ξ hξ) :
    bd ((((g⁻¹ : cuspStab (POBasic.ofProp hA) Γ ξ hξ) : Γ)) : PO n 1) ξ = ξ := by
  have hP : POBasic n := POBasic.ofProp hA
  have hcoe : ((((g⁻¹ : cuspStab (POBasic.ofProp hA) Γ ξ hξ) : Γ)) : PO n 1)
      = (((g : Γ)) : PO n 1)⁻¹ := by simp
  have h1 : bd ((((g : Γ)) : PO n 1)⁻¹) (bd (((g : Γ)) : PO n 1) ξ)
      = bd (((((g : Γ)) : PO n 1)⁻¹) * (((g : Γ)) : PO n 1)) ξ :=
    (hP.bd_mul _ _ ξ hξ).symm
  rw [cuspStab_bd hA g, inv_mul_cancel, hP.bd_one ξ hξ] at h1
  rw [hcoe]
  exact h1

lemma cuspStab_lev_inv (hA : POActionProp n) {Γ : Subgroup (PO n 1)} {ξ : E n} {hξ : ξ ∈ Sph n}
    (hlev : ∀ (γ : Γ) (u : E n), bd (γ : PO n 1) ξ = ξ → lev ξ ((γ : PO n 1) • u) = lev ξ u)
    (g : cuspStab (POBasic.ofProp hA) Γ ξ hξ) :
    ∀ u : E n, lev ξ ((((g⁻¹ : cuspStab (POBasic.ofProp hA) Γ ξ hξ) : Γ) : PO n 1) • u)
      = lev ξ u := by
  have hP : POBasic n := POBasic.ofProp hA
  have hcoe : ((((g⁻¹ : cuspStab (POBasic.ofProp hA) Γ ξ hξ) : Γ) : PO n 1))
      = ((((g : Γ)) : PO n 1))⁻¹ := by simp
  have hlevg : ∀ u : E n, lev ξ ((((g : Γ)) : PO n 1) • u) = lev ξ u := cuspStab_lev hA hlev g
  intro u
  have h1 : lev ξ ((((g⁻¹ : cuspStab (POBasic.ofProp hA) Γ ξ hξ) : Γ) : PO n 1) • u)
      = lev ξ ((((g : Γ)) : PO n 1)
          • ((((g⁻¹ : cuspStab (POBasic.ofProp hA) Γ ξ hξ) : Γ) : PO n 1) • u)) :=
    (hlevg _).symm
  rw [h1, ← hP.mul_smul, hcoe, mul_inv_cancel, hP.one_smul]

/-- The flat action of an element of the cusp stabiliser, as an isometry of `E (flatDim ξ)`. -/
noncomputable def rhoIso (hA : POActionProp n) (hI : HypIsometryProp n) (hn : 1 ≤ n)
    {Γ : Subgroup (PO n 1)} {ξ : E n} {hξ : ξ ∈ Sph n} (D : ℝ) (hD : 0 < D)
    (hlev : ∀ (γ : Γ) (u : E n), bd (γ : PO n 1) ξ = ξ → lev ξ ((γ : PO n 1) • u) = lev ξ u)
    (g : cuspStab (POBasic.ofProp hA) Γ ξ hξ) : E (flatDim ξ) ≃ᵢ E (flatDim ξ) :=
  (flatPhi ξ).symm.trans ((flatIso hA hI hn hξ D hD (((g : Γ)) : PO n 1) (cuspStab_bd hA g)
    (cuspStab_lev hA hlev g) (cuspStab_bd_inv hA g)
    (cuspStab_lev_inv hA hlev g)).trans (flatPhi ξ))

lemma rhoIso_apply (hA : POActionProp n) (hI : HypIsometryProp n) (hn : 1 ≤ n)
    {Γ : Subgroup (PO n 1)} {ξ : E n} {hξ : ξ ∈ Sph n} (D : ℝ) (hD : 0 < D)
    (hlev : ∀ (γ : Γ) (u : E n), bd (γ : PO n 1) ξ = ξ → lev ξ ((γ : PO n 1) • u) = lev ξ u)
    (g : cuspStab (POBasic.ofProp hA) Γ ξ hξ) (x : E (flatDim ξ)) :
    rhoIso hA hI hn D hD hlev g x
      = flatPhi ξ (flatMap hξ D (((g : Γ)) : PO n 1) ((flatPhi ξ).symm x)) :=
  rfl

/-- The flat action of the cusp stabiliser, as a monoid homomorphism. -/
noncomputable def rhoHom (hA : POActionProp n) (hI : HypIsometryProp n) (hn : 1 ≤ n)
    {Γ : Subgroup (PO n 1)} {ξ : E n} {hξ : ξ ∈ Sph n} (D : ℝ) (hD : 0 < D)
    (hlev : ∀ (γ : Γ) (u : E n), bd (γ : PO n 1) ξ = ξ → lev ξ ((γ : PO n 1) • u) = lev ξ u) :
    cuspStab (POBasic.ofProp hA) Γ ξ hξ →* (E (flatDim ξ) ≃ᵢ E (flatDim ξ)) :=
  MonoidHom.mk' (rhoIso hA hI hn D hD hlev) (fun g g' => by
    apply IsometryEquiv.ext
    intro x
    show rhoIso hA hI hn D hD hlev (g * g') x
      = rhoIso hA hI hn D hD hlev g (rhoIso hA hI hn D hD hlev g' x)
    simp only [rhoIso_apply]
    rw [IsometryEquiv.symm_apply_apply,
      show (((g * g' : cuspStab (POBasic.ofProp hA) Γ ξ hξ) : Γ) : PO n 1)
        = (((g : Γ)) : PO n 1) * (((g' : Γ)) : PO n 1) from by simp [Subgroup.coe_mul],
      flatMap_mul (POBasic.ofProp hA) hξ D hD (((g : Γ)) : PO n 1) (((g' : Γ)) : PO n 1)
        (cuspStab_lev hA hlev g) (cuspStab_lev hA hlev g') ((flatPhi ξ).symm x)])

lemma rhoHom_apply (hA : POActionProp n) (hI : HypIsometryProp n) (hn : 1 ≤ n)
    {Γ : Subgroup (PO n 1)} {ξ : E n} {hξ : ξ ∈ Sph n} (D : ℝ) (hD : 0 < D)
    (hlev : ∀ (γ : Γ) (u : E n), bd (γ : PO n 1) ξ = ξ → lev ξ ((γ : PO n 1) • u) = lev ξ u)
    (g : cuspStab (POBasic.ofProp hA) Γ ξ hξ) (x : E (flatDim ξ)) :
    rhoHom hA hI hn D hD hlev g x
      = flatPhi ξ (flatMap hξ D (((g : Γ)) : PO n 1) ((flatPhi ξ).symm x)) :=
  rfl

/-! ## Continuity of the flat coordinate -/

lemma continuous_yc {ξ : E n} (hξ : ξ ∈ Sph n) : Continuous (fun u : E n => yc ξ u) := by
  have h1 : Continuous (fun u : E n => Real.sqrt (1 + ‖u‖ ^ 2)) :=
    Real.continuous_sqrt.comp (continuous_const.add (continuous_norm.pow 2))
  have h2 : Continuous (fun u : E n => inner ℝ u ξ) := continuous_id.inner continuous_const
  have hlev : Continuous (fun u : E n => lev ξ u) := by
    change Continuous (fun u : E n => Real.sqrt (1 + ‖u‖ ^ 2) - inner ℝ u ξ)
    exact h1.sub h2
  have hwc : Continuous (fun u : E n => wc ξ u) := by
    change Continuous (fun u : E n => u - inner ℝ u ξ • ξ)
    exact continuous_id.sub (h2.smul continuous_const)
  have hinv : Continuous (fun u : E n => (lev ξ u)⁻¹) :=
    hlev.inv₀ (fun u => ne_of_gt (lev_pos ξ hξ u))
  change Continuous (fun u : E n => (lev ξ u)⁻¹ • wc ξ u)
  exact hinv.smul hwc

lemma continuous_ycH {ξ : E n} (hξ : ξ ∈ Sph n) :
    Continuous (fun u : E n => (ycH hξ u : ↥(horoSub ξ))) :=
  Continuous.subtype_mk (continuous_yc hξ) (fun u => yc_mem_horoSub hξ u)

/-! ## The main theorem -/

theorem cuspStabFlatAction {n : ℕ} (hA : Submission.Mostow.POActionProp n)
    (hI : Submission.Mostow.HypIsometryProp n)
    (Γ : Subgroup (LeanEval.Geometry.MostowRigidity.PO n 1))
    (ξ : Submission.Mostow.E n) (hξ : ξ ∈ Submission.Mostow.Sph n)
    (D : ℝ) (hD : 0 < D)
    (hlev : ∀ (γ : Γ) (u : Submission.Mostow.E n),
      Submission.Mostow.bd (γ : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = ξ →
        Work.Mostow.lev ξ ((γ : LeanEval.Geometry.MostowRigidity.PO n 1) • u) = Work.Mostow.lev ξ u)
    (hdisc : IsDiscrete (SetLike.coe Γ))
    (hcoc : ∃ K : Set (Submission.Mostow.E n), IsCompact K ∧ ∀ u : Submission.Mostow.E n,
      Work.Mostow.lev ξ u = D → ∃ γ : Γ,
        Submission.Mostow.bd (γ : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = ξ ∧
          (γ : LeanEval.Geometry.MostowRigidity.PO n 1) • u ∈ K) :
    ∃ (m : ℕ) (ρ : Work.Mostow.cuspStab (Work.Mostow.POBasic.ofProp hA) Γ ξ hξ →*
        (Submission.Mostow.E m ≃ᵢ Submission.Mostow.E m)),
      (∀ K : Set (Submission.Mostow.E m), IsCompact K →
        {g : Work.Mostow.cuspStab (Work.Mostow.POBasic.ofProp hA) Γ ξ hξ |
          ((ρ g) '' K ∩ K).Nonempty}.Finite) ∧
      (∃ K : Set (Submission.Mostow.E m), IsCompact K ∧ ∀ x : Submission.Mostow.E m,
        ∃ g : Work.Mostow.cuspStab (Work.Mostow.POBasic.ofProp hA) Γ ξ hξ, ρ g x ∈ K) ∧
      (∀ g : Work.Mostow.cuspStab (Work.Mostow.POBasic.ofProp hA) Γ ξ hξ,
        (∀ x : Submission.Mostow.E m, ρ g x = x) →
        ∀ u : Submission.Mostow.E n, Work.Mostow.lev ξ u = D → (g : Γ) • u = u) := by
  have hn : 1 ≤ n := by
    by_contra hlt
    have h0 : n = 0 := by omega
    subst h0
    have hξ1 : ‖ξ‖ = 1 := (mem_Sph_iff ξ).mp hξ
    have hsub : ξ = (0 : E 0) := Subsingleton.elim _ _
    rw [hsub, norm_zero] at hξ1
    exact one_ne_zero hξ1.symm
  refine ⟨flatDim ξ, rhoHom hA hI hn D hD hlev, ?_, ?_, ?_⟩
  · intro K hK
    by_cases hKe : K = ∅
    · subst hKe; simp
    obtain ⟨R, hR⟩ := exists_norm_le_of_isCompact hK
    set R' : ℝ := Real.arcosh (1 + (D * (2 * max R 0)) ^ 2 / 2) with hR'def
    let uD : E n := hptOf ξ (0 : E n) D
    have huDlev : lev ξ uD = D := (hptOf_level ξ hξ D hD 0 (by simp)).1
    have hT : ({γ : Γ | (((fun u : E n => (γ : PO n 1) • u) '' ({uD} : Set (E n))) ∩
        {v : E n | hdist uD v ≤ R'}).Nonempty}).Finite :=
      finite_translates_inter_compact n hA hI hdisc isCompact_singleton
        ((HypIsoData.ofProp hI).ball_compact uD R')
    refine (hT.preimage (f := fun g : cuspStab (POBasic.ofProp hA) Γ ξ hξ => (g : Γ))
      (fun a _ b _ hab => Subtype.ext hab)).subset ?_
    rintro g ⟨w, hw, hwK⟩
    obtain ⟨x, hxK, hxw⟩ := hw
    have hxR : ‖x‖ ≤ R := hR x hxK
    have hwR : ‖w‖ ≤ R := hR w hwK
    obtain ⟨y, hyx⟩ : ∃ y : ↥(horoSub ξ), flatPhi ξ y = x :=
      ⟨(flatPhi ξ).symm x, (flatPhi ξ).apply_symm_apply x⟩
    have hyn : ‖(y : E n)‖ ≤ R := by rw [(norm_flatPhi ξ y).symm, hyx]; exact hxR
    have hfixg : bd (((g : Γ)) : PO n 1) ξ = ξ := cuspStab_bd hA g
    have hlevg : ∀ u : E n, lev ξ ((((g : Γ)) : PO n 1) • u) = lev ξ u := cuspStab_lev hA hlev g
    have hy_symm : (flatPhi ξ).symm x = y := (flatPhi ξ).symm_apply_eq.mpr hyx.symm
    have hρx : (flatPhi ξ) (flatMap hξ D (((g : Γ)) : PO n 1) y)
        = rhoHom hA hI hn D hD hlev g x := by
      rw [rhoHom_apply hA hI hn D hD hlev g x, hy_symm]
    have hfn : ‖(flatMap hξ D (((g : Γ)) : PO n 1) y : E n)‖ = ‖w‖ := by
      rw [← hxw, ← hρx, norm_flatPhi ξ (flatMap hξ D (((g : Γ)) : PO n 1) y)]
    have hbase : ‖(flatMap hξ D (((g : Γ)) : PO n 1) (0 : ↥(horoSub ξ)) : E n)‖
        ≤ 2 * max R 0 := by
      have hisom := (flatMap_isometry hA hI hn hξ D hD (((g : Γ)) : PO n 1) hfixg hlevg).dist_eq
        (0 : ↥(horoSub ξ)) y
      rw [Subtype.dist_eq, Subtype.dist_eq, dist_eq_norm, dist_eq_norm] at hisom
      have hy0 : ‖((0 : ↥(horoSub ξ)) : E n) - (y : E n)‖ = ‖(y : E n)‖ := by
        rw [show ((0 : ↥(horoSub ξ)) : E n) = 0 from rfl, zero_sub, norm_neg]
      have htri : ‖(flatMap hξ D (((g : Γ)) : PO n 1) (0 : ↥(horoSub ξ)) : E n)‖
          ≤ ‖(flatMap hξ D (((g : Γ)) : PO n 1) (0 : ↥(horoSub ξ)) : E n)
              - (flatMap hξ D (((g : Γ)) : PO n 1) y : E n)‖
            + ‖(flatMap hξ D (((g : Γ)) : PO n 1) y : E n)‖ := by
        simpa [dist_eq_norm] using dist_triangle
          (flatMap hξ D (((g : Γ)) : PO n 1) (0 : ↥(horoSub ξ)) : E n)
          (flatMap hξ D (((g : Γ)) : PO n 1) y : E n) (0 : E n)
      calc ‖(flatMap hξ D (((g : Γ)) : PO n 1) (0 : ↥(horoSub ξ)) : E n)‖
          ≤ ‖(flatMap hξ D (((g : Γ)) : PO n 1) (0 : ↥(horoSub ξ)) : E n)
              - (flatMap hξ D (((g : Γ)) : PO n 1) y : E n)‖
            + ‖(flatMap hξ D (((g : Γ)) : PO n 1) y : E n)‖ := htri
        _ = ‖(y : E n)‖ + ‖w‖ := by rw [hisom, hy0, hfn]
        _ ≤ R + R := add_le_add hyn hwR
        _ ≤ 2 * max R 0 := by linarith [le_max_left R 0]
    have hlevgD : lev ξ ((((g : Γ)) : PO n 1) • uD) = D := by rw [hlevg uD, huDlev]
    have horthD : inner ℝ (yc ξ ((((g : Γ)) : PO n 1) • uD)) ξ = 0 := yc_inner_orth hξ
    have hptD : hptOf ξ (yc ξ ((((g : Γ)) : PO n 1) • uD)) D = (((g : Γ)) : PO n 1) • uD :=
      hptOf_yc ξ hξ D hD _ hlevgD
    have hcoe0 : (flatMap hξ D (((g : Γ)) : PO n 1) (0 : ↥(horoSub ξ)) : E n)
        = yc ξ ((((g : Γ)) : PO n 1) • uD) := rfl
    have hdistu : hdist (hptOf ξ 0 D) ((((g : Γ)) : PO n 1) • uD) ≤ R' := by
      rw [← hptD, hptOf_hdist ξ hξ D hD 0 (yc ξ ((((g : Γ)) : PO n 1) • uD))
        (by simp) horthD, hR'def]
      rw [Real.arcosh_le_arcosh (by positivity) (by positivity)]
      have hb : ‖(0 : E n) - yc ξ ((((g : Γ)) : PO n 1) • uD)‖ ≤ 2 * max R 0 := by
        rw [zero_sub, norm_neg, ← hcoe0]
        exact hbase
      have h1 : D * ‖(0 : E n) - yc ξ ((((g : Γ)) : PO n 1) • uD)‖ ≤ D * (2 * max R 0) :=
        mul_le_mul_of_nonneg_left hb (le_of_lt hD)
      have h2 : (D * ‖(0 : E n) - yc ξ ((((g : Γ)) : PO n 1) • uD)‖) ^ 2
          ≤ (D * (2 * max R 0)) ^ 2 :=
        pow_le_pow_left₀ (mul_nonneg (le_of_lt hD) (norm_nonneg _)) h1 2
      linarith
    exact ⟨(((g : Γ)) : PO n 1) • uD, ⟨⟨uD, by simp, rfl⟩, hdistu⟩⟩
  · obtain ⟨K₀, hK₀c, hK₀⟩ := hcoc
    refine ⟨(flatPhi ξ) '' ((fun w : E n => (ycH hξ w : ↥(horoSub ξ))) '' K₀), ?_, ?_⟩
    · exact (hK₀c.image (continuous_ycH hξ)).image (flatPhi ξ).continuous
    · intro x
      obtain ⟨y, hyx⟩ : ∃ y : ↥(horoSub ξ), flatPhi ξ y = x :=
        ⟨(flatPhi ξ).symm x, (flatPhi ξ).apply_symm_apply x⟩
      have hlevu : lev ξ (hptOf ξ (y : E n) D) = D :=
        (hptOf_level ξ hξ D hD (y : E n) (mem_horoSub_comm.mp y.2)).1
      obtain ⟨γ, hγfix, hγmem⟩ := hK₀ (hptOf ξ (y : E n) D) hlevu
      refine ⟨(⟨γ, hγfix⟩ : cuspStab (POBasic.ofProp hA) Γ ξ hξ), ?_⟩
      rw [rhoHom_apply hA hI hn D hD hlev (⟨γ, hγfix⟩ : cuspStab (POBasic.ofProp hA) Γ ξ hξ) x,
        show (flatPhi ξ).symm x = y from (flatPhi ξ).symm_apply_eq.mpr hyx.symm]
      exact ⟨flatMap hξ D (γ : PO n 1) y,
        ⟨(γ : PO n 1) • hptOf ξ (y : E n) D, hγmem, rfl⟩, rfl⟩
  · intro g hgtriv u hu
    have hy : inner ℝ (yc ξ u) ξ = 0 := yc_inner_orth hξ
    have hptu : hptOf ξ (yc ξ u) D = u := hptOf_yc ξ hξ D hD u hu
    have hlevg : ∀ w : E n, lev ξ ((((g : Γ)) : PO n 1) • w) = lev ξ w := cuspStab_lev hA hlev g
    have hkey : flatMap hξ D (((g : Γ)) : PO n 1) (ycH hξ u) = ycH hξ u := by
      have h2 := hgtriv (flatPhi ξ (ycH hξ u))
      rw [rhoHom_apply hA hI hn D hD hlev g (flatPhi ξ (ycH hξ u))] at h2
      simp only [IsometryEquiv.symm_apply_apply] at h2
      exact (flatPhi ξ).injective h2
    show (((g : Γ)) : PO n 1) • u = u
    have hlevgD : lev ξ ((((g : Γ)) : PO n 1) • hptOf ξ (yc ξ u) D) = D := by
      rw [hlevg, (hptOf_level ξ hξ D hD (yc ξ u) hy).1]
    have hgoal : (((g : Γ)) : PO n 1) • hptOf ξ (yc ξ u) D = hptOf ξ (yc ξ u) D := by
      rw [← hptOf_yc ξ hξ D hD ((((g : Γ)) : PO n 1) • hptOf ξ (yc ξ u) D) hlevgD,
        show yc ξ ((((g : Γ)) : PO n 1) • hptOf ξ (yc ξ u) D)
          = ((flatMap hξ D (((g : Γ)) : PO n 1) (ycH hξ u) : ↥(horoSub ξ)) : E n) from rfl,
        hkey,
        show hptOf ξ (((ycH hξ u : ↥(horoSub ξ)) : E n)) D = hptOf ξ (yc ξ u) D from rfl]
    rwa [hptu] at hgoal

end

end Work.Mostow
