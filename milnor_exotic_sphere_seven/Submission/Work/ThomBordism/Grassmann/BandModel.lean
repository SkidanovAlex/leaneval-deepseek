import Mathlib
import Submission.Work.ThomBordism.Grassmann.FibreModel
import Submission.Work.ThomBordism.Grassmann.SphereCover

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-!
# The equatorial band of the sphere bundle as `band × fibre`

The intersection `bandSet k m = upSet k m ∩ downSet k m` of the two halves of the incidence space is
homeomorphic to the product of the equatorial band `bandSph k m` of the unit sphere of `Amb (k+m)`
with the fibre `fibreVec k m`: a point is described by the direction of its vector and by the point
obtained by rotating that direction to `baseVec`.
-/

open scoped Topology
open unitInterval CategoryTheory

namespace Work.ThomBordism.Grassmann

noncomputable section

variable {k m : ℕ}

/-! ## Composition of linear isometries, and the composition of `planeAct` -/

/-- The composition of two linear isometries. -/
def liComp (R S : Amb (k+m) →ₗᵢ[ℝ] Amb (k+m)) : Amb (k+m) →ₗᵢ[ℝ] Amb (k+m) where
  toLinearMap := R.toLinearMap.comp S.toLinearMap
  norm_map' y := by
    show ‖R (S y)‖ = ‖y‖
    rw [R.norm_map, S.norm_map]

@[simp] theorem liComp_apply (R S : Amb (k+m) →ₗᵢ[ℝ] Amb (k+m)) (y : Amb (k+m)) :
    liComp R S y = R (S y) := rfl

/-- **`planeAct` is compatible with composition of isometries.** -/
theorem planeAct_comp (R S : Amb (k+m) →ₗᵢ[ℝ] Amb (k+m)) (P : OG k m) :
    planeAct R (planeAct S P) = planeAct (liComp R S) P := by
  obtain ⟨f, rfl⟩ := Quotient.exists_rep P
  rw [planeAct_mk, planeAct_mk, planeAct_mk]
  congr 1

/-- `planeAct R (planeAct S P) = P` when `R ∘ S = id` pointwise. -/
theorem planeAct_comp_eq_self {R S : Amb (k+m) →ₗᵢ[ℝ] Amb (k+m)} (h : ∀ y, R (S y) = y)
    (P : OG k m) : planeAct R (planeAct S P) = P := by
  rw [planeAct_comp]
  exact (planeAct_congr (fun y => by simpa using h y) P).trans (planeAct_one P)

/-! ## The model band -/

/-- The equatorial band of the unit sphere of `Amb (k+m)` in the direction of `baseVec`. -/
abbrev bandSph (k m : ℕ) : Set (Amb (k+m)) :=
  {u | ‖u‖ = 1 ∧ -(1/2 : ℝ) < inner ℝ u (baseVec k m) ∧ inner ℝ u (baseVec k m) < 1/2}

/-- **The band of the sphere bundle is the set of points whose direction lies in `bandSph`.** -/
theorem mem_bandSet_iff_dirVec {x : ↥(incZero k m)} :
    x ∈ bandSet k m ↔ dirVec x ∈ bandSph k m := by
  have hn : 0 < ‖evalVec x.1‖ :=
    norm_pos_iff.mpr (evalVec_ne_zero_of_mem_zeroComplement _ x.2)
  have hsm : evalVec x.1 = ‖evalVec x.1‖ • dirVec x := (dirVec_smul x).symm
  have hkey : 2 * heightVec k m x.1 + ‖evalVec x.1‖
      = ‖evalVec x.1‖ * (2 * inner ℝ (dirVec x) (baseVec k m) + 1) := by
    rw [heightVec, hsm, inner_smul_left, starRingEnd_apply, star_trivial, norm_smul,
      Real.norm_eq_abs, abs_of_pos hn, norm_dirVec, mul_one]
    ring
  have hkey' : ‖evalVec x.1‖ - 2 * heightVec k m x.1
      = ‖evalVec x.1‖ * (1 - 2 * inner ℝ (dirVec x) (baseVec k m)) := by
    rw [heightVec, hsm, inner_smul_left, starRingEnd_apply, star_trivial, norm_smul,
      Real.norm_eq_abs, abs_of_pos hn, norm_dirVec, mul_one]
    ring
  have hup : (x ∈ upSet k m) ↔ -(1/2 : ℝ) < inner ℝ (dirVec x) (baseVec k m) := by
    rw [upSet, Set.mem_ofPred_eq, hkey]
    constructor
    · intro h; nlinarith
    · intro h; nlinarith [hn]
  have hdown : (x ∈ downSet k m) ↔ inner ℝ (dirVec x) (baseVec k m) < 1/2 := by
    rw [downSet, Set.mem_ofPred_eq, hkey']
    constructor
    · intro h; nlinarith
    · intro h; nlinarith [hn]
  rw [bandSet, Set.mem_inter_iff, hup, hdown, bandSph, Set.mem_ofPred_eq]
  exact ⟨fun h => ⟨norm_dirVec x, h.1, h.2⟩, fun h => ⟨h.2.1, h.2.2⟩⟩

theorem mem_upSet_of_mem_bandSet {x : ↥(incZero k m)} (hx : x ∈ bandSet k m) :
    x ∈ upSet k m := (Set.mem_inter_iff _ _ _).mp hx |>.1

/-- A point of the fibre whose direction lies in the band lies in the band. -/
theorem mem_bandSet_of_dirVec_mem {x : ↥(incZero k m)} (h : dirVec x ∈ bandSph k m) :
    x ∈ bandSet k m := (mem_bandSet_iff_dirVec).mpr h


/-! ## The composite of two opposite rotations is the identity -/

/-- A point of the incidence space is determined by its plane and the vector of its plane. -/
theorem ext_plane_evalVec {y z : ↥(incZero k m)} (h1 : y.1.1 = z.1.1)
    (h2 : evalVec y.1 = evalVec z.1) : y = z :=
  (toE_self y).symm.trans
    ((toE_congr h1 h2 (evalVec_ne_zero_of_mem_zeroComplement y.1 y.2) (evalVec_memPlane y.1)
      (evalVec_ne_zero_of_mem_zeroComplement z.1 z.2) (evalVec_memPlane z.1)).trans (toE_self z))

/-- **`rotE` of opposite rotations**: if `R ∘ S = id` pointwise then `rotE R (rotE S x) = x`. -/
theorem rotE_rotE_eq_self {R S : Amb (k+m) →ₗᵢ[ℝ] Amb (k+m)} (h : ∀ y, R (S y) = y)
    (x : ↥(incZero k m)) : rotE R (rotE S x) = x := by
  refine ext_plane_evalVec ?_ ?_
  · rw [rotE_proj, rotE_proj]
    exact planeAct_comp_eq_self h x.1.1
  · rw [evalVec_rotE, evalVec_rotE]
    exact h (evalVec x.1)

/-! ## The band trivialisation -/

/-- The direction map `bandSet k m → bandSph k m`. -/
def bandDir (x : ↥(bandSet k m)) : ↥(bandSph k m) :=
  ⟨dirVec x.1, mem_bandSet_iff_dirVec.mp x.2⟩

theorem continuous_bandDir : Continuous (bandDir (k := k) (m := m)) :=
  Continuous.subtype_mk (continuous_dirVec.comp continuous_subtype_val) _

theorem dirVec_bandInv_apply (hk : 1 ≤ k) (q : ↥(bandSph k m) × ↥(fibreVec k m)) :
    dirVec (rotE (rotLI (baseVec k m) q.1.1 (norm_baseVec (by omega)) q.1.2.1
      (by
        have h := q.1.2.2.1
        rw [real_inner_comm] at h
        intro h0
        linarith)) (q.2.1 : ↥(incZero k m))) = q.1.1 := by
  rw [dirVec_rotE, rotLI_apply, mem_fibreVec_iff.mp q.2.2,
    rotMap_self (norm_baseVec (by omega)) q.1.2.1]

/-- The nondegeneracy of the rotation used in the band trivialisation. -/
theorem bandInv_nondeg (q : ↥(bandSph k m) × ↥(fibreVec k m)) :
    1 + inner ℝ (baseVec k m) q.1.1 ≠ 0 := by
  have h := q.1.2.2.1
  rw [real_inner_comm] at h
  intro h0
  linarith

/-- The inverse of the band trivialisation. -/
def bandInv (hk : 1 ≤ k) (q : ↥(bandSph k m) × ↥(fibreVec k m)) : ↥(bandSet k m) :=
  ⟨rotE (rotLI (baseVec k m) q.1.1 (norm_baseVec (by omega)) q.1.2.1 (bandInv_nondeg q))
    (q.2.1 : ↥(incZero k m)),
   mem_bandSet_iff_dirVec.mpr (by rw [dirVec_bandInv_apply hk q]; exact q.1.2)⟩

/-- The band trivialisation: a point of the band is described by the direction of its vector and by
the point obtained by rotating that direction to `baseVec`. -/
def bandMap (hk : 1 ≤ k) (x : ↥(bandSet k m)) :
    ↥(bandSph k m) × ↥(fibreVec k m) :=
  (bandDir x, sPlusFibre hk ⟨x.1, mem_upSet_of_mem_bandSet x.2⟩)

theorem bandInv_angle (hk : 1 ≤ k) (q : ↥(bandSph k m) × ↥(fibreVec k m)) :
    1 + inner ℝ (dirVec (bandInv hk q).1) (baseVec k m) ≠ 0 := by
  have h := dirVec_bandInv_apply hk q
  rw [show dirVec (bandInv hk q).1 = dirVec (rotE (rotLI (baseVec k m) q.1.1
      (norm_baseVec (by omega)) q.1.2.1 (bandInv_nondeg q)) (q.2.1 : ↥(incZero k m))) from rfl,
    h, real_inner_comm]
  exact bandInv_nondeg q

/-- `bandInv hk q` is the point obtained from the fibre point `q.2` by the rotation of `q.1`. -/
theorem bandInv_eq (hk : 1 ≤ k) (q : ↥(bandSph k m) × ↥(fibreVec k m)) :
    (bandInv hk q : ↥(incZero k m))
      = rotE (rotLI (baseVec k m) q.1.1 (norm_baseVec (by omega)) q.1.2.1 (bandInv_nondeg q))
        (q.2.1 : ↥(incZero k m)) := rfl

/-! ## Remaining: the two inverse laws of the band trivialisation

The proofs of `bandMap_inv` and `bandInv_map` (which need the composite
`rotE_rotE_eq_self` applied after a restricted rewrite of the *point* but not of the direction
inside the rotation) are left for the next session; the maps `bandDir`, `bandInv`, `bandMap`,
`bandInv_nondeg`, `bandInv_angle`, `bandInv_eq`, `dirVec_bandInv_apply` and the composite lemma
`rotE_rotE_eq_self` are in place. -/

end

end Work.ThomBordism.Grassmann