import Mathlib
import Submission.Work.Certificates.SDR
import Submission.Work.Certificates.SDR.check_implies
import Submission.Work.Certificates.subsingleton_hom_of_subsingleton
import Submission.Work.Certificates.FinChainCx.zeroDiff_homology

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


/-!
# The section of an `SDR` certificate is a chain map

An `SDR C` certificate exhibits `C` as a strong deformation retract of the free complex with
`b k` generators in degree `k` and zero differentials: `Z k : ℤ^{(b k)} → C_k` is the section,
`ρ k : C_k → ℤ^{(b k)}` the retraction and `h k` the homotopy, and `S.check` decides the four
equations of a deformation retract *sparsely*, in all degrees below the bound `S.N`.

This file turns the certificate into an honest chain map.  The degreewise maps `Z k` assemble
into a chain map `φ : (zeroDiff b).toChainComplex ⟶ C.toChainComplex`: the only obstruction is
the identity `∂_{k+1} ∘ Z_k = 0` (the differential of `zeroDiff b` is zero, so no condition
involves `Z_{k+1}`), which is the first of the four equations for `k < S.N` and holds
vacuously for `k ≥ S.N`, where `Z_k` lands in degree `k ≥ N`, i.e. in the zero module.

`bd_mul_Z_eq_zero` records that identity in every degree, `rho_mul_bd_eq_zero` the dual identity
`ρ_k ∘ ∂_{k-1} = 0` used to assemble `ρ` into the retraction `C.toChainComplex ⟶
(zeroDiff b).toChainComplex`, and `section_chainMap` is the existence of the section chain map.
-/

namespace Work.Certificates.SDR

variable {C : FinChainCx}

/-- `∂Z = 0` in every degree: for `k < S.N` this is part of the `checkDeg` certificate, and for
`k ≥ S.N` the target `ℤ^{(b (k+1))}` of the composite has rank zero, so every matrix into it
vanishes. -/
theorem bd_mul_Z_eq_zero (S : SDR C) (h : S.check = true) (k : ℕ) :
    (C.bd k).toMatrix * (S.Z (k+1)).toMatrix = 0 := by
  by_cases hk : k < S.N
  · exact (check_implies S h k hk).1
  · have hb : S.b (k+1) = 0 := S.b_zero (k+1) (by omega)
    have hsub : Subsingleton (Matrix (Fin (C.dim k)) (Fin (S.b (k+1))) ℤ) := by
      rw [hb]
      infer_instance
    exact @Subsingleton.elim _ hsub _ _

/-- `ρ∂ = 0` in every degree, the dual of `bd_mul_Z_eq_zero`: for `k < S.N` this is part of the
`checkDeg` certificate, and for `k ≥ S.N` the source `ℤ^{(b k)}` of the composite has rank
zero. -/
theorem rho_mul_bd_eq_zero (S : SDR C) (h : S.check = true) (k : ℕ) :
    (S.ρ k).toMatrix * (C.bd k).toMatrix = 0 := by
  by_cases hk : k < S.N
  · exact (check_implies S h k hk).2.1
  · have hb : S.b k = 0 := S.b_zero k (by omega)
    have hsub : Subsingleton (Matrix (Fin (S.b k)) (Fin (C.dim (k+1))) ℤ) := by
      rw [hb]
      infer_instance
    exact @Subsingleton.elim _ hsub _ _

/-- The degreewise maps `Z k : ℤ^{(b k)} → C_k` of an `SDR` certificate, viewed as morphisms of
the underlying chain modules, assemble into a chain map `(zeroDiff b).toChainComplex ⟶
C.toChainComplex`.  This is the section of the strong deformation retract. -/
theorem section_chainMap (S : SDR C) (h : S.check = true) :
    ∃ φ : ChainHom (FinChainCx.zeroDiff S.b).toChainComplex C.toChainComplex,
      ∀ k, φ.f k = ModuleCat.ofHom (Matrix.toLin' ((S.Z k).toMatrix)) := by
  refine ⟨HomologicalComplex.Hom.mk
    (fun k => ModuleCat.ofHom (Matrix.toLin' ((S.Z k).toMatrix))) ?_, fun k => rfl⟩
  intro i j hij
  -- The only shape relation is `j + 1 = i`, so `i` may be replaced by `j + 1`.
  subst hij
  -- The differential of `zeroDiff b` vanishes, so the right hand side is a zero morphism.
  erw [FinChainCx.zeroDiff_toChainComplex_d S.b (j+1) j, CategoryTheory.Limits.zero_comp]
  -- On the left, the composite of `Z_{j+1}` with `∂_{j+1}` is the map of the matrix product.
  simp only [FinChainCx.toChainComplex, ChainComplex.of_d]
  rw [← ModuleCat.ofHom_comp]
  erw [← Matrix.toLin'_mul, bd_mul_Z_eq_zero S h j]
  erw [map_zero, ModuleCat.ofHom_zero]
  rfl

end Work.Certificates.SDR
