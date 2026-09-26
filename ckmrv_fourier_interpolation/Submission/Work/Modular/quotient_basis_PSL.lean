import Mathlib
import Submission.Work.Modular.PSLTransfer
import Submission.Work.Modular.quotient_basis
import Submission.Work.Modular.presentedGroup_equiv_PSL

namespace Work.Modular

open Work.Modular
open scoped MonoidAlgebra MatrixGroups

/-- The classical presentation isomorphism `Γ = ⟨S, T | S ^ 2 = (S * T) ^ 3 = 1⟩ ≅ PSL(2, ℤ)`
of `presentedGroup_equiv_PSL`, chosen so that it carries the abstract generators `genS`, `genT`
of `Γ` to the classes `pslS`, `pslT` of `S` and `T` in `PSL(2, ℤ)`. -/
theorem exists_equiv_gens_PSL :
    ∃ e : Gamma ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) ℤ,
      e genS = pslS ∧ e genT = pslT := by
  refine ⟨PresGroup.gammaEquivFP.trans PresGroup.PsiEquiv, ?_, ?_⟩
  · show PresGroup.Psi (PresGroup.toFree genS) = pslS
    rw [PresGroup.toFree_genS, PresGroup.Psi_gC2']
    simp only [PresGroup.psl, pslS, QuotientGroup.mk'_apply]
  · show PresGroup.Psi (PresGroup.toFree genT) = pslT
    rw [PresGroup.toFree_genT, map_mul, PresGroup.Psi_gC2', PresGroup.Psi_gC3',
      ← PresGroup.psl_T_eq]
    simp only [PresGroup.psl, pslT, QuotientGroup.mk'_apply]

/-- **Proposition 3.3 of the paper in its own setting**: the images of the six elements
`1, T, TS, S, ST, STS` form a basis of `ℂ[PSL(2, ℤ)] / I` for the right ideal
`I = (T - 1)^2 · ℂ[PSL(2, ℤ)] + S (T - 1)^2 · ℂ[PSL(2, ℤ)]`.  In particular
`dim_ℂ ℂ[PSL(2, ℤ)]/I = 6`. -/
theorem quotient_basis_PSL : ∃ b : Module.Basis (Fin 6) ℂ (PSLGroupRing ⧸ idealPSL),
    ∀ i, b i = Submodule.mkQ idealPSL (pslBasisElem i) := by
  -- The classical presentation theorem, in the form in which the generators match.
  obtain ⟨e, hS, hT⟩ := exists_equiv_gens_PSL
  -- The six-dimensionality result of `quotient_basis`, proved inside `ℂ[Γ]`.
  obtain ⟨b₀, hb₀⟩ := quotient_basis
  -- Transport along the induced algebra isomorphism `ℂ[Γ] ≅ ℂ[PSL(2, ℤ)]`.
  let E : GroupRing ≃ₐ[ℂ] PSLGroupRing := MonoidAlgebra.domCongr ℂ ℂ e
  have hEs : E sR = pslSR := by
    simp only [E, sR, pslSR, MonoidAlgebra.of_apply, MonoidAlgebra.domCongr_single, hS]
  have hEt : E tR = pslTR := by
    simp only [E, tR, pslTR, MonoidAlgebra.of_apply, MonoidAlgebra.domCongr_single, hT]
  have hEb : ∀ i, E (basisElem i) = pslBasisElem i := by
    intro i
    fin_cases i <;> simp [basisElem, pslBasisElem, hEs, hEt]
  -- `E` carries the two generators of the ideal `I` onto the two generators of `idealPSL`.
  have hmem1 : ∀ r : GroupRing, E ((tR - 1) ^ 2 * r) = (pslTR - 1) ^ 2 * E r := by
    intro r
    rw [map_mul, map_pow, map_sub, map_one, hEt]
  have hmem2 : ∀ r : GroupRing, E (sR * (tR - 1) ^ 2 * r) = pslSR * (pslTR - 1) ^ 2 * E r := by
    intro r
    rw [map_mul, map_mul, map_pow, map_sub, map_one, hEt, hEs]
  have hsymm_t : E.symm pslTR = tR := by rw [← hEt, AlgEquiv.symm_apply_apply]
  have hsymm_s : E.symm pslSR = sR := by rw [← hEs, AlgEquiv.symm_apply_apply]
  have hmem1' : ∀ r : PSLGroupRing,
      E.symm ((pslTR - 1) ^ 2 * r) = (tR - 1) ^ 2 * E.symm r := by
    intro r
    rw [map_mul, map_pow, map_sub, map_one, hsymm_t]
  have hmem2' : ∀ r : PSLGroupRing,
      E.symm (pslSR * (pslTR - 1) ^ 2 * r) = sR * (tR - 1) ^ 2 * E.symm r := by
    intro r
    rw [map_mul, map_mul, map_pow, map_sub, map_one, hsymm_t, hsymm_s]
  -- Hence `E` maps the right ideal `idealI` onto `idealPSL`.
  have hmap : Submodule.map (E.toLinearEquiv : GroupRing →ₗ[ℂ] PSLGroupRing) idealI =
      idealPSL := by
    rw [idealI, idealPSL, Submodule.map_span]
    congr 1
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rcases hx with ⟨r, rfl⟩ | ⟨r, rfl⟩
      · exact Or.inl ⟨E r, hmem1 r⟩
      · exact Or.inr ⟨E r, hmem2 r⟩
    · intro hy
      refine ⟨E.symm y, ?_, ?_⟩
      · rcases hy with ⟨r, rfl⟩ | ⟨r, rfl⟩
        · exact Or.inl ⟨E.symm r, hmem1' r⟩
        · exact Or.inr ⟨E.symm r, hmem2' r⟩
      · simp
  -- The induced linear isomorphism of the quotients.
  let Q : (GroupRing ⧸ idealI) ≃ₗ[ℂ] (PSLGroupRing ⧸ idealPSL) :=
    Submodule.Quotient.equiv idealI idealPSL E.toLinearEquiv hmap
  refine ⟨b₀.map Q, fun i => ?_⟩
  rw [Module.Basis.map_apply, hb₀ i]
  simp only [Q, Submodule.Quotient.equiv_apply, Submodule.mapQ_apply, Submodule.mkQ_apply]
  congr 1
  exact hEb i

end Work.Modular
