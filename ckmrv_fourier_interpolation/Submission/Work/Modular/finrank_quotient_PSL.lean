import Mathlib
import Submission.Work.Modular.PSLTransfer
import Submission.Work.Modular.quotient_basis
import Submission.Work.Modular.presentedGroup_equiv_PSL

namespace Work.Modular

open Work.Modular
open scoped MonoidAlgebra MatrixGroups

noncomputable section

/-!
## Transferring the six-dimensional quotient `ℂ[Γ]/I` to `ℂ[PSL(2,ℤ)]`

`quotient_basis` computes the dimension of `ℂ[Γ]/I` for the abstract presented group
`Γ = ⟨S, T | S² = (ST)³ = 1⟩`.  The element `-1` acts trivially on `ℍ`, so the group
algebra that acts on functions on `ℍ` is `ℂ[PSL(2, ℤ)]`, and the ideal of the paper lives
there as `idealPSL`.  The bridge is the classical presentation isomorphism
`Γ ≅ PSL(2, ℤ)` (proved in `presentedGroup_equiv_PSL`); transporting `idealI` along the
induced algebra isomorphism gives `idealPSL`, hence an isomorphism of quotients and the
same dimension count.
-/

/-- The explicit isomorphism `Γ = ⟨S, T | S² = (ST)³ = 1⟩ → PSL(2, ℤ)` of
`presentedGroup_equiv_PSL`, exposed so that its values on the generators can be computed.
It sends the generators `S`, `T` of the presentation to the classes of the classical
generators `S`, `T`. -/
def pslQuotEquiv : Gamma ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) ℤ :=
  PresGroup.gammaEquivFP.trans PresGroup.PsiEquiv

/-- The induced isomorphism of group algebras `ℂ[Γ] ≃ₐ[ℂ] ℂ[PSL(2, ℤ)]`. -/
def pslQuotAlgEquiv : GroupRing ≃ₐ[ℂ] PSLGroupRing :=
  MonoidAlgebra.domCongr ℂ ℂ pslQuotEquiv

theorem pslQuotEquiv_genS : pslQuotEquiv genS = pslS := by
  rw [show pslQuotEquiv genS = PresGroup.Psi PresGroup.gC2 from rfl, PresGroup.Psi_gC2']
  rfl

theorem pslQuotEquiv_genT : pslQuotEquiv genT = pslT := by
  rw [show pslQuotEquiv genT = PresGroup.Psi (PresGroup.gC2 * PresGroup.gC3) from rfl,
    map_mul, PresGroup.Psi_gC2', PresGroup.Psi_gC3', ← PresGroup.psl_T_eq]
  rfl

theorem pslQuotAlgEquiv_tR : pslQuotAlgEquiv tR = pslTR := by
  simp only [pslQuotAlgEquiv, tR, pslTR, MonoidAlgebra.of_apply,
    MonoidAlgebra.domCongr_single]
  rw [pslQuotEquiv_genT]

theorem pslQuotAlgEquiv_sR : pslQuotAlgEquiv sR = pslSR := by
  simp only [pslQuotAlgEquiv, sR, pslSR, MonoidAlgebra.of_apply,
    MonoidAlgebra.domCongr_single]
  rw [pslQuotEquiv_genS]

/-- The algebra isomorphism `ℂ[Γ] ≃ₐ[ℂ] ℂ[PSL(2, ℤ)]` carries the right ideal
`I = (T - 1)² ℂ[Γ] + S (T - 1)² ℂ[Γ]` onto the right ideal
`idealPSL = (T - 1)² ℂ[PSL(2,ℤ)] + S (T - 1)² ℂ[PSL(2,ℤ)]`. -/
theorem pslQuotAlgEquiv_map_idealI :
    Submodule.map (pslQuotAlgEquiv : GroupRing →ₗ[ℂ] PSLGroupRing) idealI = idealPSL := by
  have key_t : ∀ x : GroupRing,
      pslQuotAlgEquiv ((tR - 1) ^ 2 * x) = (pslTR - 1) ^ 2 * pslQuotAlgEquiv x := by
    intro x; rw [map_mul, map_pow, map_sub, map_one, pslQuotAlgEquiv_tR]
  have key_s : ∀ x : GroupRing,
      pslQuotAlgEquiv (sR * (tR - 1) ^ 2 * x) =
        pslSR * (pslTR - 1) ^ 2 * pslQuotAlgEquiv x := by
    intro x
    rw [map_mul, map_mul, map_pow, map_sub, map_one, pslQuotAlgEquiv_sR, pslQuotAlgEquiv_tR]
  rw [idealI, idealPSL, Submodule.map_span]
  rw [show ((pslQuotAlgEquiv : GroupRing →ₗ[ℂ] PSLGroupRing) : GroupRing → PSLGroupRing) =
    ⇑pslQuotAlgEquiv from rfl]
  congr 1
  ext y
  constructor
  · rintro ⟨x, (⟨r, rfl⟩ | ⟨r, rfl⟩), hxy⟩
    · exact Or.inl ⟨pslQuotAlgEquiv r, by rw [← hxy, key_t]⟩
    · exact Or.inr ⟨pslQuotAlgEquiv r, by rw [← hxy, key_s]⟩
  · rintro (⟨r, rfl⟩ | ⟨r, rfl⟩)
    · exact ⟨(tR - 1) ^ 2 * pslQuotAlgEquiv.symm r,
        Or.inl ⟨pslQuotAlgEquiv.symm r, rfl⟩, by rw [key_t, AlgEquiv.apply_symm_apply]⟩
    · exact ⟨sR * (tR - 1) ^ 2 * pslQuotAlgEquiv.symm r,
        Or.inr ⟨pslQuotAlgEquiv.symm r, rfl⟩, by rw [key_s, AlgEquiv.apply_symm_apply]⟩

/-- The isomorphism of quotients `ℂ[Γ]/I ≃ₗ[ℂ] ℂ[PSL(2, ℤ)]/idealPSL` induced by the
presentation isomorphism. -/
def pslQuotLinearEquiv :
    (GroupRing ⧸ idealI) ≃ₗ[ℂ] (PSLGroupRing ⧸ idealPSL) :=
  Submodule.Quotient.equiv idealI idealPSL
    (pslQuotAlgEquiv : GroupRing ≃ₗ[ℂ] PSLGroupRing) pslQuotAlgEquiv_map_idealI

/-- `dim_ℂ ℂ[PSL(2, ℤ)]/I = 6` for the right ideal `I = (T - 1)^2 · ℂ[PSL(2, ℤ)] +
S (T - 1)^2 · ℂ[PSL(2, ℤ)]`. -/
theorem finrank_quotient_PSL : Module.finrank ℂ (PSLGroupRing ⧸ idealPSL) = 6 := by
  obtain ⟨b, _hb⟩ := quotient_basis
  have h := Module.finrank_eq_card_basis (b.map pslQuotLinearEquiv)
  simpa using h

end

end Work.Modular
