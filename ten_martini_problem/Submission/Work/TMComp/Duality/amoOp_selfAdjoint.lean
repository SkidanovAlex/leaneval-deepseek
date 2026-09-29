import Mathlib
import Submission.Work.TMComp.Duality.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The almost Mathieu operator is self-adjoint

The almost Mathieu operator `amoOp α lam θ` on `ℓ²(ℤ)` is
`(H u) n = u (n+1) + u (n-1) + 2 λ cos (2π (θ + nα)) u n`,
i.e. the sum of the two shifts and a real diagonal potential. Each of these three
pieces is self-adjoint (the shifts are adjoint to one another, the potential is real),
hence so is `H`.

The only coordinate computation needed is that of the adjoint of a general coordinate
operator `f ↦ (i ↦ b i * f (e i))`; we obtain it by pairing with the `ℓ²` basis vector
`lp.single`.
-/

open LeanEval.Analysis.TenMartini

namespace Work.TMComp.Duality

noncomputable section

/-! ## The adjoint of a coordinate operator -/

/-- Coordinates of the adjoint of a coordinate operator: the adjoint of
`f ↦ (i ↦ b i * f (e i))` has coordinates `i ↦ conj (b (e⁻¹ i)) * g (e⁻¹ i)`. -/
theorem adjoint_coordOp {ι : Type*} [DecidableEq ι] (b : ι → ℂ) (e : ι ≃ ι) (K : ℝ)
    (hK0 : 0 ≤ K) (hK : ∀ i, ‖b i‖ ≤ K) (g : lp (fun _ : ι => ℂ) 2) (i : ι) :
    (coordOp b e K hK0 hK).adjoint g i = star (b (e.symm i)) * g (e.symm i) := by
  have hT : (coordOp b e K hK0 hK) (lp.single 2 i (1 : ℂ))
      = lp.single 2 (e.symm i) (b (e.symm i)) := by
    apply lp.ext; funext j
    simp only [coordOp_coord, lp.single_apply]
    by_cases h : j = e.symm i
    · subst h; simp
    · have hej : e j ≠ i := fun hc => h (by rw [← hc]; simp)
      rw [Pi.single_eq_of_ne hej, Pi.single_eq_of_ne h]
      simp
  rw [show (coordOp b e K hK0 hK).adjoint g i
        = inner ℂ (lp.single 2 i (1 : ℂ)) ((coordOp b e K hK0 hK).adjoint g) from ?_,
      ContinuousLinearMap.adjoint_inner_right, hT, lp.inner_single_left, RCLike.inner_apply]
  · rw [mul_comm, starRingEnd_apply]
  · rw [lp.inner_single_left, RCLike.inner_apply]; simp

/-- The complex conjugate of a real number, viewed in `ℂ`. -/
theorem star_ofReal_complex (r : ℝ) : star ((r : ℝ) : ℂ) = (r : ℂ) := by
  rw [RCLike.star_def]; exact RCLike.conj_ofReal r

/-! ## The three pieces are self-adjoint -/

/-- The adjoint of the shift `S n = n + k` is the shift by `-k`. -/
theorem star_shiftZ (k : ℤ) : star (shiftZ k) = shiftZ (-k) := by
  show (shiftZ k).adjoint = shiftZ (-k)
  apply coord_ext
  intro f n
  simp only [shiftZ]
  rw [adjoint_coordOp, coordOp_coord]
  simp [Equiv.addRight]

/-- The (real) almost Mathieu potential is self-adjoint. -/
theorem star_amoPotOp (α lam θ : ℝ) : star (amoPotOp α lam θ) = amoPotOp α lam θ := by
  show (amoPotOp α lam θ).adjoint = amoPotOp α lam θ
  apply coord_ext
  intro f n
  simp only [amoPotOp, diagZ]
  rw [adjoint_coordOp, coordOp_coord]
  rw [show (Equiv.refl ℤ).symm n = n from rfl, show (Equiv.refl ℤ) n = n from rfl]
  rw [star_ofReal_complex]

/-- The almost Mathieu operator is self-adjoint. -/
theorem amoOp_selfAdjoint (α lam θ : ℝ) : IsSelfAdjoint (Work.TMComp.Duality.amoOp α lam θ) := by
  change star (shiftZ (1 : ℤ) + shiftZ (-1) + amoPotOp α lam θ)
      = shiftZ (1 : ℤ) + shiftZ (-1) + amoPotOp α lam θ
  have h1 : star (shiftZ (1 : ℤ)) = shiftZ (-1) := star_shiftZ 1
  have h2 : star (shiftZ (-1 : ℤ)) = shiftZ 1 := by
    simpa using star_shiftZ (-1 : ℤ)
  rw [StarRing.star_add, StarRing.star_add, h1, h2, star_amoPotOp]
  abel

end

end Work.TMComp.Duality
