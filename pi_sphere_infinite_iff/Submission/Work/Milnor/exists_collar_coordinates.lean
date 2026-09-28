import Mathlib
import Submission.Work.Milnor.Collar
import Submission.Work.Milnor.VBundle
import Submission.Work.Milnor.mk_to_vk
import Submission.Work.Milnor.fibreNorm
import Submission.Work.Milnor.ScaleDefs
import Submission.Work.Milnor.UnitSphere
import Submission.Work.Milnor.CollarHomotopy

/-!
# The collar `{1/2 < ν}` of the disc bundle is a product `Mk k × (1/2, ∞)`

The collar `collar k = {p : Vk k | 1/2 < fibreNormFun k p}` of the disc bundle of the rank-`4`
vector bundle `ξ` over `S⁴` consists of the fibres of `ξ` whose norm is `> 1/2`.  Since the fibre
norm is positive there, every point of the collar can be written uniquely as its normalisation on
the unit sphere bundle `{ν = 1} ≅ Mk k` times its fibre norm:

  `p ↦ (p / ν(p), ν(p))`.

The normalisation is the retraction `Work.Milnor.collarPsi` (which lands in `Mk k` by composing the
fibrewise scaling `vScale` with the inverse `unitInv` of the inclusion `mkToVkFun`), so the map

`collarCoordFun k p = (collarPsi k p, ⟨ν p, ·⟩)`

is a homeomorphism from the collar onto `Mk k × (1/2, ∞)` whose second component is the fibre
norm.  This is the "cylindrical coordinate" description of the collar used when the disc bundle is
glued to the complement of a ball in `ℝ⁸` (`Submission/NOTES.md` §9.3).
-/

namespace Work.Milnor

open scoped Manifold ContDiff Topology
open Submission.Milnor

noncomputable section

/-! ## The fibre norm of a fibrewise multiple of a point of `Mk k` -/

/-- Scaling a point of the unit sphere bundle `Mk k` by `c ≥ 0` multiplies its fibre norm by
`c` (in particular the fibre norm is `c`). -/
theorem fibreNormFun_vScale_mkToVkFun (k : ℤ) (c : ℝ) (hc : 0 ≤ c) (z : Mk k) :
    fibreNormFun k (vScale k c (mkToVkFun k z)) = c := by
  rw [fibreNormFun_vScale, fibreNormFun_mkToVkFun, mul_one, abs_of_nonneg hc]

/-- Scaling a point of `Mk k` by `c > 1/2` keeps it in the collar. -/
theorem lt_fibreNormFun_vScale_mkToVkFun (k : ℤ) (c : ℝ) (z : Mk k) (hc : 1 / 2 < c) :
    1 / 2 < fibreNormFun k (vScale k c (mkToVkFun k z)) := by
  rw [fibreNormFun_vScale_mkToVkFun k c (le_of_lt (by linarith)) z]
  exact hc

/-! ## The normalisation, read back on `Mk k` -/

/-- The normalisation of a point of the collar, included back into `Vk k`, is the fibrewise
scaling by the inverse of the fibre norm. -/
theorem mkToVkFun_collarPsi (k : ℤ) (p : ↥(collar k)) :
    mkToVkFun k (collarPsi k p) = vScale k ((fibreNormFun k (p : Vk k))⁻¹) (p : Vk k) := by
  rw [collarPsi_apply, mkToVkFun_unitInv, collarNorm_coe]

/-- The point of `Mk k` corresponding to an explicitly scaled point of the unit sphere bundle. -/
theorem unitInv_mkToVkFun (k : ℤ) (z : Mk k) :
    unitInv k ⟨mkToVkFun k z, fibreNormFun_mkToVkFun k z⟩ = z :=
  mkToVkFun_injective k (by rw [mkToVkFun_unitInv])

/-! ## The coordinate map and its inverse -/

/-- **The collar coordinates**: the normalisation of the point of `Mk k` together with the fibre
norm. -/
noncomputable def collarCoordFun (k : ℤ) :
    ↥(collar k) → Mk k × Set.Ioi (1 / 2 : ℝ) :=
  fun p => (collarPsi k p, ⟨fibreNormFun k p.1, p.2⟩)

/-- **The inverse of the collar coordinates**: scale the given point of `Mk k` by the given
radius. -/
noncomputable def collarCoordInv (k : ℤ) :
    Mk k × Set.Ioi (1 / 2 : ℝ) → ↥(collar k) :=
  fun q => ⟨vScale k (q.2 : ℝ) (mkToVkFun k q.1),
    lt_fibreNormFun_vScale_mkToVkFun k (q.2 : ℝ) q.1 q.2.2⟩

/-- The two collar coordinate constructions are mutually inverse. -/
theorem collarCoordInv_collarCoordFun (k : ℤ) :
    Function.LeftInverse (collarCoordInv k) (collarCoordFun k) := by
  intro p
  refine Subtype.ext ?_
  show vScale k (fibreNormFun k (p : Vk k)) (mkToVkFun k (collarPsi k p)) = (p : Vk k)
  rw [mkToVkFun_collarPsi]
  have hne : fibreNormFun k (p : Vk k) ≠ 0 := by
    have := mem_collar.mp p.2
    linarith
  rw [vScale_mul, mul_inv_cancel₀ hne, vScale_one]
  rfl

/-- The two collar coordinate constructions are mutually inverse. -/
theorem collarCoordFun_collarCoordInv (k : ℤ) :
    Function.RightInverse (collarCoordInv k) (collarCoordFun k) := by
  intro q
  have hw : 0 < (q.2 : ℝ) := by
    have h : (1 : ℝ) / 2 < (q.2 : ℝ) := q.2.2
    linarith
  have hX : ((collarCoordInv k q : ↥(collar k)) : Vk k)
      = vScale k (q.2 : ℝ) (mkToVkFun k q.1) := rfl
  have hnorm : fibreNormFun k ((collarCoordInv k q : ↥(collar k)) : Vk k) = (q.2 : ℝ) := by
    rw [hX]
    exact fibreNormFun_vScale_mkToVkFun k (q.2 : ℝ) (le_of_lt hw) q.1
  refine Prod.ext ?_ ?_
  · show collarPsi k (collarCoordInv k q) = q.1
    have hCN : collarNorm k (collarCoordInv k q)
        = ⟨mkToVkFun k q.1, fibreNormFun_mkToVkFun k q.1⟩ := by
      refine Subtype.ext ?_
      rw [collarNorm_coe, hnorm, hX, vScale_mul, inv_mul_cancel₀ (ne_of_gt hw), vScale_one]
      rfl
    rw [collarPsi_apply, hCN, unitInv_mkToVkFun]
  · show (⟨fibreNormFun k ((collarCoordInv k q : ↥(collar k)) : Vk k),
        (collarCoordInv k q).2⟩ : Set.Ioi (1 / 2 : ℝ)) = q.2
    exact Subtype.ext hnorm

/-! ## Continuity, and the homeomorphism -/

theorem continuous_collarCoordFun (k : ℤ) : Continuous (collarCoordFun k) := by
  refine Continuous.prodMk ?_ ?_
  · exact (collarPsi k).continuous
  · exact Continuous.subtype_mk
      ((continuous_fibreNormFun k).comp continuous_subtype_val) (fun p => p.2)

theorem continuous_collarCoordInv (k : ℤ) : Continuous (collarCoordInv k) := by
  have hf : Continuous (fun q : Mk k × Set.Ioi (1 / 2 : ℝ) =>
      vScale k (q.2 : ℝ) (mkToVkFun k q.1)) :=
    (continuous_vScale_uncurry k).comp
      (Continuous.prodMk (continuous_subtype_val.comp continuous_snd)
        ((continuous_mkToVkFun k).comp continuous_fst))
  have hp : ∀ q : Mk k × Set.Ioi (1 / 2 : ℝ),
      vScale k (q.2 : ℝ) (mkToVkFun k q.1) ∈ collar k :=
    fun q => lt_fibreNormFun_vScale_mkToVkFun k (q.2 : ℝ) q.1 q.2.2
  exact hf.subtype_mk hp

/-- **The collar is homeomorphic to `Mk k × (1/2, ∞)`** by the collar coordinates. -/
noncomputable def collarCoordHomeomorph (k : ℤ) :
    ↥(collar k) ≃ₜ (Mk k × Set.Ioi (1 / 2 : ℝ)) where
  toFun := collarCoordFun k
  invFun := collarCoordInv k
  left_inv := collarCoordInv_collarCoordFun k
  right_inv := collarCoordFun_collarCoordInv k
  continuous_toFun := continuous_collarCoordFun k
  continuous_invFun := continuous_collarCoordInv k

/-! ## The requested lemma -/

/-- **Coordinates on the collar**: there is a continuous bijection (indeed a homeomorphism) from
the collar `{1/2 < ν}` of the disc bundle onto `Mk k × (1/2, ∞)` whose second component is the
fibre norm.  The map sends `p` to `(p / ν(p), ν(p))`, and its inverse scales a point of `Mk k` by
the prescribed radius. -/
theorem exists_collar_coordinates (k : ℤ) :
    ∃ f : ↥(Work.Milnor.collar k) → Submission.Milnor.Mk k × Set.Ioi (1 / 2 : ℝ),
      Function.Bijective f ∧ Continuous f ∧ IsOpenMap f ∧
      (∀ p : ↥(Work.Milnor.collar k), (f p).2 = ⟨Work.Milnor.fibreNormFun k p.1, p.2⟩) :=
  ⟨collarCoordFun k, (collarCoordHomeomorph k).bijective, (collarCoordHomeomorph k).continuous,
    (collarCoordHomeomorph k).isOpenMap, fun _ => rfl⟩

end

end Work.Milnor
