import Mathlib
import Submission.Work.Cohomology.CompatTrans.prodSphereDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# `B1set p q` is homotopy equivalent to `Sᵖ`

Inside `Yset p q = (Sᵖ × Sᵍ) \ {(Nₚ,N_q)}` we have

`B1set p q = {z | z.2 ≠ N_q} = Sᵖ × (Sᵍ \ {N_q})`,

the second factor being the sphere with its north pole removed.  The latter is contractible
(`Work.Cohomology.contractible_compl_sphN`), hence `B1set p q` is homotopy equivalent to
`Sᵖ = sphSet (p+1)`; this is the content of `homotopyEquiv_B1set`.

The proof decomposes as
`B1set p q ≃ₜ Sᵖ × (Sᵍ \ {N_q}) ≃ₕ Sᵖ × pt ≃ₜ Sᵖ`,
the middle equivalence being `prodCongr` of the identity with the homotopy equivalence between a
contractible space and a point.
-/

namespace Work.Cohomology

noncomputable section

/-- `B1set p q`, which is `Sᵖ × (Sᵍ \ {N_q})` seen inside `Yset p q`, is homeomorphic to the
honest product `sphSet (p+1) × (sphSet (q+1) \ {sphN q})`. -/
def B1Homeo (p q : ℕ) :
    ↥(B1set p q) ≃ₜ (↥(sphSet (p+1)) × {y : ↥(sphSet (q+1)) // y ≠ sphN q}) where
  toFun z := (z.1.1.1, ⟨z.1.1.2, z.2⟩)
  invFun w := ⟨⟨(w.1, w.2.1), by intro h; exact w.2.2 (congrArg Prod.snd h)⟩, w.2.2⟩
  left_inv z := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext <;> rfl
  right_inv w := by
    apply Prod.ext
    · rfl
    · apply Subtype.ext; rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- `B1set p q = Sᵖ × (Sᵍ \ {N_q})` is homotopy equivalent to `Sᵖ`: the second factor is
contractible. -/
theorem homotopyEquiv_B1set (p q : ℕ) :
    Nonempty (ContinuousMap.HomotopyEquiv ↥(B1set p q) ↥(sphSet (p+1))) := by
  haveI : ContractibleSpace {y : ↥(sphSet (q+1)) // y ≠ sphN q} := contractible_compl_sphN q
  refine ⟨(B1Homeo p q).toHomotopyEquiv.trans ?_⟩
  exact (((ContinuousMap.HomotopyEquiv.refl ↥(sphSet (p+1))).prodCongr
    (ContractibleSpace.hequiv_unit {y : ↥(sphSet (q+1)) // y ≠ sphN q}).some).trans
    (Homeomorph.prodUnique ↥(sphSet (p+1)) Unit).toHomotopyEquiv)

end

end Work.Cohomology
