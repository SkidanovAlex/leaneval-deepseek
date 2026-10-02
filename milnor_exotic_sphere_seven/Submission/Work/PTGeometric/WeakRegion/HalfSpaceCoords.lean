import Mathlib
import Submission.Work.PTGeometric.WeakRegion.Basic
import Submission.Work.PTGeometric.WeakRegion.exists_graph_halfSpace

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# PTGeometric/WeakRegion: coordinates adapted to the half-space

This file sets up the `C^∞` half-space graph result
(`Work.PTGeometric.WeakRegion.exists_graph_halfSpace_cinf`).  Everything is proved in the coordinates
`ℝⁿ = T × ℝ` where `T` is the *tangential hyperplane* `{z | z 0 = 0}`; the map

`hsConn : T × ℝ → ℝⁿ,  (u, s) ↦ u + s • e 0 = consVec s u`

is a linear homeomorphism (`hsConn_mk` shows that `(hsMk z, z 0)` is the inverse pair), and it
identifies the half-space `{0 ≤ z 0}` with `{0 ≤ s}`.

## Main definitions

* `Work.PTGeometric.WeakRegion.hsTang`: the tangential hyperplane.
* `Work.PTGeometric.WeakRegion.hsMk`: the projection `ℝⁿ → T`, `z ↦ tail z`.
* `Work.PTGeometric.WeakRegion.hsConn`: the inverse of `(u,s) ↦ (hsMk u, s)`.
-/

open scoped Manifold ContDiff Topology
open Function Set Topology Manifold Filter

namespace Work.PTGeometric.WeakRegion

noncomputable section

variable {n : ℕ} [NeZero n]

/-! ## The tangential hyperplane -/

/-- The **tangential hyperplane** of `ℝⁿ`: the vectors with vanishing `0`-th coordinate. -/
def hsTang (n : ℕ) [NeZero n] : Submodule ℝ (EuclideanSpace ℝ (Fin n)) where
  carrier := {z | z.ofLp 0 = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    rw [PiLp.add_apply, hx, hy, add_zero]
  smul_mem' := by
    intro c x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    rw [PiLp.smul_apply, hx, smul_eq_mul, mul_zero]

@[simp] theorem mem_hsTang {z : EuclideanSpace ℝ (Fin n)} :
    z ∈ hsTang n ↔ z.ofLp 0 = 0 := Iff.rfl

/-! ## The projection onto the tangential hyperplane -/

/-- The projection `z ↦ tailVec z` onto the tangential hyperplane, as a continuous linear map. -/
def hsMk : EuclideanSpace ℝ (Fin n) →L[ℝ] hsTang n :=
  ContinuousLinearMap.codRestrict (tailVecCLM (n := n)) (hsTang n) fun z => by
    show (tailVecCLM z).ofLp 0 = 0
    rw [tailVecCLM_apply, tailVec_apply_zero]

theorem hsMk_coe (z : EuclideanSpace ℝ (Fin n)) :
    ((hsMk z : hsTang n) : EuclideanSpace ℝ (Fin n)) = tailVec z := rfl

theorem hsMk_coe_zero (z : EuclideanSpace ℝ (Fin n)) :
    ((hsMk z : hsTang n) : EuclideanSpace ℝ (Fin n)).ofLp 0 = 0 := by
  rw [hsMk_coe, tailVec_apply_zero]

theorem hsMk_tailVec (z : EuclideanSpace ℝ (Fin n)) : hsMk (tailVec z) = hsMk z := by
  apply Subtype.ext
  rw [hsMk_coe, hsMk_coe, tailVec_idem]

theorem hsMk_eq_mk (z : EuclideanSpace ℝ (Fin n)) (hz : z.ofLp 0 = 0) :
    hsMk z = (⟨z, hz⟩ : hsTang n) := by
  apply Subtype.ext
  rw [hsMk_coe]
  exact tailVec_self_of_apply_zero hz

/-! ## The `(u,s) ↦ consVec s u` linear map -/

/-- The continuous linear map `(u,s) ↦ u + s • e 0` (`= consVec s u`). -/
def hsConn : hsTang n × ℝ →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  (Submodule.subtypeL (hsTang n)).comp (ContinuousLinearMap.fst ℝ (hsTang n) ℝ) +
    (ContinuousLinearMap.smulRight (ContinuousLinearMap.snd ℝ (hsTang n) ℝ) (eZero (n := n)))

theorem hsConn_apply (x : hsTang n × ℝ) :
    hsConn x = ((x.1 : hsTang n) : EuclideanSpace ℝ (Fin n)) + x.2 • eZero := rfl

theorem hsConn_apply_pair (u : hsTang n) (s : ℝ) :
    hsConn (u, s) = ((u : hsTang n) : EuclideanSpace ℝ (Fin n)) + s • eZero := rfl

theorem hsConn_mk (z : EuclideanSpace ℝ (Fin n)) : hsConn (hsMk z, z.ofLp 0) = z := by
  show ((hsMk z : hsTang n) : EuclideanSpace ℝ (Fin n)) + z.ofLp 0 • eZero = z
  rw [hsMk_coe, tailVec]
  abel

theorem hsConn_ofLp_zero (x : hsTang n × ℝ) : (hsConn x).ofLp 0 = x.2 := by
  show (((x.1 : hsTang n) : EuclideanSpace ℝ (Fin n)) + x.2 • eZero).ofLp 0 = x.2
  have h1 : ((x.1 : hsTang n) : EuclideanSpace ℝ (Fin n)).ofLp 0 = 0 := x.1.2
  simp [PiLp.add_apply, PiLp.smul_apply, h1, eZero_apply]

theorem hsConn_preimage_coord (s : Set ℝ) :
    hsConn ⁻¹' {z : EuclideanSpace ℝ (Fin n) | z.ofLp 0 ∈ s} =
      {x : hsTang n × ℝ | x.2 ∈ s} := by
  ext x
  rw [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_setOf_eq, hsConn_ofLp_zero]

theorem hsConn_preimage_half :
    hsConn ⁻¹' (Set.range (modelWithCornersEuclideanHalfSpace n)) =
      {x : hsTang n × ℝ | 0 ≤ x.2} := by
  have h := hsConn_preimage_coord (n := n) (Set.Ici (0 : ℝ))
  rw [range_modelWithCornersEuclideanHalfSpace]
  simpa only [Set.mem_Ici] using h

theorem norm_hsConn_sub_le (x y : hsTang n × ℝ) :
    ‖hsConn x - hsConn y‖ ≤ ‖x.1 - y.1‖ + |x.2 - y.2| := by
  have hxy : hsConn x - hsConn y = hsConn (x - y) := by rw [map_sub]
  rw [hxy]
  show ‖(((x - y).1 : hsTang n) : EuclideanSpace ℝ (Fin n)) + (x - y).2 • eZero‖
    ≤ ‖x.1 - y.1‖ + |x.2 - y.2|
  calc ‖(((x - y).1 : hsTang n) : EuclideanSpace ℝ (Fin n)) + (x - y).2 • eZero‖
      ≤ ‖(((x - y).1 : hsTang n) : EuclideanSpace ℝ (Fin n))‖ + ‖(x - y).2 • eZero‖ :=
        norm_add_le _ _
    _ = ‖x.1 - y.1‖ + |x.2 - y.2| := by
        rw [norm_smul, Real.norm_eq_abs, eZero_norm, mul_one]
        rfl

/-- The point `(hsMk z, z 0)` of `T × ℝ` corresponding to `z`. -/
def hsSplit (z : EuclideanSpace ℝ (Fin n)) : hsTang n × ℝ := (hsMk z, z.ofLp 0)

theorem hsConn_hsSplit (z : EuclideanSpace ℝ (Fin n)) : hsConn (hsSplit z) = z := hsConn_mk z

theorem hsMk_hsConn (x : hsTang n × ℝ) : hsMk (hsConn x) = x.1 := by
  apply Subtype.ext
  rw [hsMk_coe]
  show tailVec (hsConn x) = x.1
  rw [tailVec]
  show hsConn x - (hsConn x).ofLp 0 • eZero = ((x.1 : hsTang n) : EuclideanSpace ℝ (Fin n))
  rw [hsConn_ofLp_zero, hsConn_apply]
  abel

theorem hsSplit_ofLp (x : hsTang n × ℝ) : hsSplit (hsConn x) = x := by
  show (hsMk (hsConn x), (hsConn x).ofLp 0) = x
  rw [hsMk_hsConn, hsConn_ofLp_zero]

theorem continuous_hsSplit : Continuous (hsSplit (n := n)) := by
  unfold hsSplit
  fun_prop

end

end Work.PTGeometric.WeakRegion
