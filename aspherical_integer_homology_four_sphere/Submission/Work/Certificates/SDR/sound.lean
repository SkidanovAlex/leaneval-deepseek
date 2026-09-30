import Mathlib
import Submission.Work.Certificates.SDR
import Submission.Work.Certificates.SDR.homotopy_exists
import Submission.Work.Certificates.SDR.section_chainMap
import Submission.Work.Certificates.SDR.retract_chainMap
import Submission.Work.Certificates.FinChainCx.zeroDiff_homology
import Submission.Work.Certificates.exists_iso_of_subsingleton
import Submission.Work.Certificates.ChainCx

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Soundness of the `SDR` certificate: `H_k(C) ≅ ℤ^{(b k)}`

An `SDR C` certificate supplies, in every degree, maps `Z k : ℤ^{(b k)} → C_k`,
`ρ k : C_k → ℤ^{(b k)}` and `h k : C_k → C_{k+1}` with

`∂Z = 0`,  `ρ∂ = 0`,  `ρZ = 1`,  `1 - Zρ = ∂h + h∂`,

decided *sparsely* by `S.check` in every degree below the bound `S.N`.  These are exactly the
equations of a strong deformation retract of `C` onto the complex with `b k` generators in
degree `k` and zero differentials, so `ρ` and `Z` assemble into a homotopy equivalence

`C.toChainComplex ≃ (zeroDiff S.b).toChainComplex`

(`section_chainMap`, `retract_chainMap`, `homotopy_exists`), which induces an isomorphism on
homology in every degree (`HomotopyEquiv.toHomologyIso`).  Composing with
`zeroDiff_homology` -- the homology of a complex with zero differentials is the complex itself,
`H_k(zeroDiff b) ≅ ℤ^{(b k)}` -- gives the stated isomorphism `H_k(C) ≅ ℤ^{(b k)}`.
-/

namespace Work.Certificates.SDR

open CategoryTheory

variable {C : FinChainCx}

/-- `ρ k` composed with `Z k` is the identity of `ℤ^{(b k)}`, in *every* degree: for `k < S.N`
this is one of the equations read off from `S.check` (`check_implies`), and for `k ≥ S.N` the
matrix is a matrix over `Fin (S.b k) = Fin 0`, hence a subsingleton type. -/
theorem rho_mul_Z_eq_one (S : SDR C) (h : S.check = true) (k : ℕ) :
    (S.ρ k).toMatrix * (S.Z k).toMatrix = 1 := by
  by_cases hk : k < S.N
  · exact (check_implies S h k hk).2.2.1
  · have hb : S.b k = 0 := S.b_zero k (not_lt.mp hk)
    have hsub : Subsingleton (Matrix (Fin (S.b k)) (Fin (S.b k)) ℤ) := by
      rw [hb]
      infer_instance
    exact @Subsingleton.elim _ hsub _ _

/-- The section `Z` and the retraction `ρ` of an `SDR` certificate are mutually inverse chain
maps: `Z ≫ ρ = 𝟙` on the complex with zero differentials.  This is `rho_mul_Z_eq_one` read
degreewise through the chain-map components. -/
theorem section_comp_retract
    (S : SDR C) (h : S.check = true)
    (Zc : ChainHom (FinChainCx.zeroDiff S.b).toChainComplex C.toChainComplex)
    (hZc : ∀ k, Zc.f k = ModuleCat.ofHom (Matrix.toLin' ((S.Z k).toMatrix)))
    (Rc : ChainHom C.toChainComplex (FinChainCx.zeroDiff S.b).toChainComplex)
    (hRc : ∀ k, Rc.f k = ModuleCat.ofHom (Matrix.toLin' ((S.ρ k).toMatrix))) :
    Zc ≫ Rc = 𝟙 (FinChainCx.zeroDiff S.b).toChainComplex := by
  apply HomologicalComplex.Hom.ext
  funext i
  rw [HomologicalComplex.comp_f, HomologicalComplex.id_f, hZc i, hRc i]
  change ofMat ((S.Z i).toMatrix) ≫ ofMat ((S.ρ i).toMatrix)
    = 𝟙 (ModuleCat.of ℤ (Fin (S.b i) → ℤ))
  rw [ofMat_comp, rho_mul_Z_eq_one S h i, ofMat_id]

/-- **Soundness of the `SDR` certificate**: a passing sparse check yields an isomorphism
`H_k(C) ≅ ℤ^{(b k)}` in every degree. -/
theorem sound (S : SDR C) (h : S.check = true) :
    ∀ k, Nonempty (C.homology k ≅ ModuleCat.of ℤ (Fin (S.b k) → ℤ)) := by
  intro k
  -- The section, the retraction and the homotopy supplied by the certificate ...
  obtain ⟨Zc, hZc⟩ := section_chainMap S h
  obtain ⟨Rc, hRc⟩ := retract_chainMap S h
  obtain ⟨H⟩ := homotopy_exists S h Zc hZc Rc hRc
  -- ... combine into a homotopy equivalence `C ≃ zeroDiff S.b` ...
  have hEq : HomotopyEquiv C.toChainComplex (FinChainCx.zeroDiff S.b).toChainComplex :=
    { hom := Rc
      inv := Zc
      homotopyHomInvId := H
      homotopyInvHomId := Homotopy.ofEq (section_comp_retract S h Zc hZc Rc hRc) }
  -- ... which induces an isomorphism on homology, and `H_k(zeroDiff b) ≅ ℤ^{(b k)}`.
  obtain ⟨e⟩ := FinChainCx.zeroDiff_homology S.b k
  exact ⟨(hEq.toHomologyIso k).trans e⟩

end Work.Certificates.SDR
