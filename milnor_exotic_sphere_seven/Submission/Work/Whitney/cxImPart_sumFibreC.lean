import Mathlib
import Submission.Work.Whitney.Basic

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

/-!
# `cxImPart` commutes with the direct-sum splitting

The explicit splitting `Work.Whitney.sumFibreC m₁ m₂` of `ℂ^{m₁} × ℂ^{m₂}` onto `ℂ^{m₁+m₂}` is
the coordinate shuffle `EuclideanSpace.finAddEquivProd.symm`, which acts on the *labels* of the
coordinates and is insensitive to the coefficient field.  Consequently taking imaginary parts
commutes with it: on the nose it is the real splitting `Work.Whitney.sumFibreR k₁ k₂`.

This is the imaginary-part sibling of `Work.Whitney.cxRePart_sumFibreC`, and is the coordinate
computation underlying `Work.Whitney.sumFibreC_cxOfReal` (and its imaginary-part form), and through
them the bundle-level statement `Work.Whitney.complexificationCore_whitneySumR`.
-/

namespace Work.Whitney

noncomputable section

open Work.Thom

/-- **`cxImPart` commutes with the coordinate shuffle `EuclideanSpace.finAddEquivProd.symm`.**
Because the shuffle only permutes coordinates, the imaginary part of the shuffled complex vector is
the shuffle of the imaginary parts, computed with the real splitting. -/
theorem cxImPart_finAddEquivProd_symm {n m : ℕ}
    (x : EuclideanSpace ℂ (Fin n)) (y : EuclideanSpace ℂ (Fin m)) :
    cxImPart ((EuclideanSpace.finAddEquivProd (𝕜 := ℂ) (n := n) (m := m)).symm (x, y))
      = (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := m)).symm
          (cxImPart x, cxImPart y) := by
  ext t
  obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective t
  rcases s with i | j
  · simp only [cxImPart, LinearMap.coe_mk, AddHom.coe_mk, WithLp.ofLp_toLp]
    rw [finAddEquivProd_symm_apply_inl, finAddEquivProd_symm_apply_inl]
  · simp only [cxImPart, LinearMap.coe_mk, AddHom.coe_mk, WithLp.ofLp_toLp]
    rw [finAddEquivProd_symm_apply_inr, finAddEquivProd_symm_apply_inr]

/-- **The imaginary part commutes with the complex Whitney-sum splitting**: `cxImPart` of the direct
sum is the direct sum of the imaginary parts.  Both `Work.Whitney.sumFibreC` and
`Work.Whitney.sumFibreR` are `EuclideanSpace.finAddEquivProd.symm`, so this is the coordinate shuffle
computation `cxImPart_finAddEquivProd_symm`. -/
theorem cxImPart_sumFibreC (k₁ k₂ : ℕ)
    (w : EuclideanSpace ℂ (Fin k₁) × EuclideanSpace ℂ (Fin k₂)) :
    Work.Thom.cxImPart (Work.Whitney.sumFibreC k₁ k₂ w) =
      Work.Whitney.sumFibreR k₁ k₂ (Work.Thom.cxImPart w.1, Work.Thom.cxImPart w.2) := by
  exact cxImPart_finAddEquivProd_symm w.1 w.2

end

end Work.Whitney
