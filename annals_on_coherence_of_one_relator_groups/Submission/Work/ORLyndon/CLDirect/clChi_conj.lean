import Mathlib
import Submission.Work.ORLyndon.CLDirect.cldDefs
import Submission.Work.ORLyndon.CLDirect.conj_pow_eq

namespace Work.ORLyndon.CLDirect

/-- `clChi` is `1` on every conjugate of `u`. Sketch: `conj_pow_eq D f 1` gives `⟨f*u*f⁻¹, hf⟩ = m * D.e (of q) * m⁻¹` (`Subtype.ext`, `pow_one`); then `map_mul`, `map_inv`, `mul_inv_cancel_comm` (the target `Multiplicative (ZMod l)` is commutative), and `clChi D l (D.e (of q)) = FreeGroup.lift _ (of q) = ofAdd 1` by `MulEquiv.symm_apply_apply` and `FreeGroup.lift.of`. -/
theorem clChi_conj {X : Type*} {u : FreeGroup X} (D : Work.ORLyndon.CLDirect.CLData u)
    (l : ℕ) (f : FreeGroup X)
    (hf : f * u * f⁻¹ ∈ Subgroup.normalClosure ({u} : Set (FreeGroup X))) :
    Work.ORLyndon.CLDirect.clChi D l ⟨f * u * f⁻¹, hf⟩ =
      Multiplicative.ofAdd (1 : ZMod l) := by
  -- Split `f` along the Cohen--Lyndon section: `f * u * f⁻¹ = m * e (of q) * m⁻¹` in `M`.
  obtain ⟨m, _hm, heq⟩ := conj_pow_eq D f 1
  simp only [pow_one] at heq
  have hsub : (⟨f * u * f⁻¹, hf⟩ : ↥(Subgroup.normalClosure ({u} : Set (FreeGroup X)))) =
      (m * D.e (FreeGroup.of (QuotientGroup.mk f)) * m⁻¹ :
        ↥(Subgroup.normalClosure ({u} : Set (FreeGroup X)))) := by
    apply Subtype.ext
    exact heq
  rw [hsub]
  -- `clChi` sends `e (of q)` to `ofAdd 1`; conjugating is trivial since the target is commutative.
  simp only [Work.ORLyndon.CLDirect.clChi, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    map_mul, map_inv, MulEquiv.symm_apply_apply, mul_inv_cancel_comm]
  rw [FreeGroup.lift_apply_of]

end Work.ORLyndon.CLDirect
