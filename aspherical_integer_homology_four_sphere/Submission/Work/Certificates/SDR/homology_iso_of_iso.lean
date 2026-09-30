import Mathlib
import Submission.Work.Certificates.SDR
import Submission.Work.Certificates.SDR.homotopy_exists
import Submission.Work.Certificates.SDR.section_chainMap
import Submission.Work.Certificates.SDR.retract_chainMap
import Submission.Work.Certificates.FinChainCx.zeroDiff_homology
import Submission.Work.Certificates.exists_iso_of_subsingleton
import Submission.Work.Certificates.FinChainCx.subsingleton_homology_of_dim_zero

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Homology of a complex isomorphic to the one certified by an `SDR`

An `SDR C` certificate (`Submission/Work/Certificates/SDR.lean`) packages the data of a strong
deformation retract of the free chain complex `C` onto the complex with `b k` generators in
degree `k` and zero differentials, and `SDR.check` decides the four retract equations sparsely.

Two ingredients are assembled here:

* `homotopyEquiv_of_check` -- a passing check turns the section `Z` and the retraction `ρ` into
  an honest *homotopy equivalence* of chain complexes
  `(zeroDiff S.b).toChainComplex ≃ C.toChainComplex` (the certificate's homotopy `h` supplies
  the homotopy `ρ ≫ Z ≃ 1`, while `ρ Z = 1` already holds on the nose);
* `homology_iso_of_iso` -- homology is an invariant of isomorphism (indeed of homotopy
  equivalence) of chain complexes, so the homology of *any* complex isomorphic to `C` is
  `ℤ^{(S.b k)}`, by combining the homotopy equivalence with the computation
  `H_k(zeroDiff b) ≅ ℤ^{(b k)}` of `FinChainCx.zeroDiff_homology`.

The explicit `ChainComplex.of` presentations `zeroCx`/`cxOf` of `retract_chainMap` are used
throughout: under them the objects reduce to `ℤ^{(b k)}`, so the degreewise matrix identities
can be rewritten directly.
-/

namespace Work.Certificates.SDR

set_option linter.style.haveILetI false

open CategoryTheory

variable {C : FinChainCx}

/-- `ρ Z = 1` in every degree.  For `k < S.N` this is the third equation of `SDR.check`
(`SDR.check_implies`); for `k ≥ S.N` the module `ℤ^{(b k)}` has rank zero, so it is the only
matrix of its shape and the identity holds trivially. -/
theorem rho_mul_Z_eq_one (S : SDR C) (h : S.check = true) (k : ℕ) :
    (S.ρ k).toMatrix * (S.Z k).toMatrix = 1 := by
  by_cases hk : k < S.N
  · exact (check_implies S h k hk).2.2.1
  · have hb : S.b k = 0 := S.b_zero k (not_lt.mp hk)
    haveI : Subsingleton (Matrix (Fin (S.b k)) (Fin (S.b k)) ℤ) := by
      rw [hb]
      infer_instance
    exact Subsingleton.elim _ _

/-- The section `Z` followed by the retraction `ρ` is the identity of the complex
`(zeroDiff S.b).toChainComplex` with zero differentials: degreewise it is the matrix identity
`ρ_k · Z_k = 1`. -/
theorem Z_comp_rho_eq_id (S : SDR C) (h : S.check = true)
    (Zc : ChainHom (zeroCx S.b) (cxOf C))
    (hZc : ∀ k, Zc.f k = ModuleCat.ofHom (Matrix.toLin' ((S.Z k).toMatrix)))
    (Rc : ChainHom (cxOf C) (zeroCx S.b))
    (hRc : ∀ k, Rc.f k = ModuleCat.ofHom (Matrix.toLin' ((S.ρ k).toMatrix))) :
    Zc ≫ Rc = 𝟙 (zeroCx S.b) := by
  apply HomologicalComplex.Hom.ext
  funext k
  rw [HomologicalComplex.comp_f, hZc k, hRc k, HomologicalComplex.id_f]
  rw [← ModuleCat.ofHom_comp, ← Matrix.toLin'_mul, rho_mul_Z_eq_one S h k,
    Matrix.toLin'_one, ModuleCat.ofHom_id]

/-- A passing `SDR` check exhibits `C` as homotopy equivalent to the complex with zero
differentials and Betti numbers `S.b`: the section `Z` and the retraction `ρ` are mutually
inverse up to the certificate's homotopy `h`. -/
theorem homotopyEquiv_of_check (S : SDR C) (h : S.check = true) :
    Nonempty (HomotopyEquiv (zeroCx S.b) (cxOf C)) := by
  obtain ⟨Zc, hZc⟩ := section_chainMap S h
  obtain ⟨Rc, hRc⟩ := retract_chainMap S h
  obtain ⟨H⟩ := homotopy_exists S h Zc hZc Rc hRc
  exact ⟨{ hom := Zc, inv := Rc,
           homotopyHomInvId := Homotopy.ofEq (Z_comp_rho_eq_id S h Zc hZc Rc hRc),
           homotopyInvHomId := H }⟩

/-- The homology of any chain complex isomorphic to the one certified by `S` is
`ℤ^{(S.b k)}` in degree `k`. -/
theorem homology_iso_of_iso (S : SDR C) (h : S.check = true)
    {K : ChainComplex (ModuleCat ℤ) ℕ} (e : C.toChainComplex ≅ K) (k : ℕ) :
    Nonempty (K.homology k ≅ ModuleCat.of ℤ (Fin (S.b k) → ℤ)) := by
  obtain ⟨H⟩ := homotopyEquiv_of_check S h
  obtain ⟨z⟩ := FinChainCx.zeroDiff_homology S.b k
  exact ⟨((HomotopyEquiv.ofIso e).toHomologyIso k).symm.trans
    ((H.toHomologyIso k).symm.trans z)⟩

end Work.Certificates.SDR
