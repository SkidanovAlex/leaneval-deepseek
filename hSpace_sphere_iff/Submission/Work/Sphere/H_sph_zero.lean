/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: hSpace_sphere_iff team

# The cohomology of `S⁰`

The sphere `S⁰ = Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1` is the two point space
`{p, q}`, `p = polePt 0`, `q = negPolePt 0`, so it is discrete: every singular simplex of `S⁰` is
constant.  Consequently the cochain complex of the singular simplicial set of `S⁰` is isomorphic
to the cochain complex of a constant (discrete) simplicial set, whose cohomology is
`H⁰ = ℚ × ℚ` (one copy of `ℚ` per point) and `Hᵏ = 0` for `k > 0`.

This is the base case of the computation of the cohomology of the spheres: the two-cap
Mayer–Vietoris computation of `Submission/Work/Sphere/Suspension.lean` shifts degrees by one and
starts from `S¹`, and its induction starts at `S⁰`.

The main statement is `Work.Sphere.H_sph_zero`.
-/
import Mathlib
import Submission.Work.Sphere.Suspension
import Submission.Work.Cohomology.Hzero
import Submission.Work.Sphere.SphZeroDefs
import Submission.Work.Sphere.SphZeroTwoPoints
import Submission.Work.Sphere.SphZeroSimplexConst
import Submission.Work.Sphere.ConstSSetCohomology

open CategoryTheory Simplicial Opposite

set_option backward.isDefEq.respectTransparency.types false

namespace Work.Sphere

noncomputable section

/-! ## The two points of `S⁰` and the isomorphism `(S⁰ → ℚ) ≃ₗ ℚ × ℚ` -/

/-- The `ℚ`-vector space of functions on the two point space `S⁰` is `ℚ × ℚ`, by evaluation at
the two points `polePt 0` and `negPolePt 0`. -/
theorem funEquiv_exists
    (hclass : ∀ x : Submission.Sphere.Sph 0,
      x = Submission.Sphere.polePt 0 ∨ x = Submission.Sphere.negPolePt 0) :
    Nonempty ((Submission.Sphere.Sph 0 → ℚ) ≃ₗ[ℚ] ℚ × ℚ) := by
  have hpq : Submission.Sphere.polePt 0 ≠ Submission.Sphere.negPolePt 0 :=
    Submission.Sphere.polePt_ne_negPolePt 0
  let φ : (Submission.Sphere.Sph 0 → ℚ) →ₗ[ℚ] ℚ × ℚ :=
    { toFun := fun f => (f (Submission.Sphere.polePt 0), f (Submission.Sphere.negPolePt 0))
      map_add' := fun f g => rfl
      map_smul' := fun r f => rfl }
  have hφ : ∀ f, φ f = (f (Submission.Sphere.polePt 0), f (Submission.Sphere.negPolePt 0)) :=
    fun f => rfl
  refine ⟨LinearEquiv.ofBijective φ ⟨?_, ?_⟩⟩
  · intro f g hfg
    funext x
    rcases hclass x with h | h <;> rw [h]
    · exact congrArg Prod.fst hfg
    · exact congrArg Prod.snd hfg
  · intro a
    refine ⟨fun x => if x = Submission.Sphere.polePt 0 then a.1 else a.2, ?_⟩
    rw [hφ, Prod.mk.injEq]
    constructor
    · rw [if_pos rfl]
    · rw [if_neg (fun h : Submission.Sphere.negPolePt 0 = Submission.Sphere.polePt 0 => hpq h.symm)]

/-! ## The cohomology of `S⁰` -/

/-- **The cohomology of `S⁰`.**  Rational singular cohomology of the zero sphere `S⁰ = {±1}`:
all positive cohomology groups vanish, and `H⁰(S⁰; ℚ) ≅ ℚ × ℚ`. -/
theorem H_sph_zero :
    (∀ k : ℕ, 0 < k → Subsingleton (Submission.Cohomology.H (Submission.Sphere.singSph 0) ℚ k)) ∧
    Nonempty (Submission.Cohomology.H (Submission.Sphere.singSph 0) ℚ 0 ≃ₗ[ℚ] ℚ × ℚ) := by
  have hclass : ∀ x : Submission.Sphere.Sph 0,
      x = Submission.Sphere.polePt 0 ∨ x = Submission.Sphere.negPolePt 0 := SphZeroTwoPoints
  have hconst : ∀ (n : ℕ)
      (σ : (Submission.Sphere.singSph 0).obj (Opposite.op (SimplexCategory.mk n))),
      constSimplex n (simplexVal n σ) = σ := fun n σ => (SphZeroSimplexConst hclass n σ).symm
  obtain ⟨hpos, hzer⟩ := ConstSSetCohomology (Submission.Sphere.singSph 0)
    (Submission.Sphere.Sph 0) (fun n x => constSimplex n x) (fun n σ => simplexVal n σ)
    simplexVal_constSimplex hconst face_constSimplex
  obtain ⟨e⟩ := hzer
  obtain ⟨e₂⟩ := funEquiv_exists hclass
  exact ⟨hpos, ⟨e.trans e₂⟩⟩

end

end Work.Sphere
