import Mathlib
import Submission.Work.Certificates.SDR
import Submission.Work.Certificates.SDR.check_implies
import Submission.Work.Certificates.subsingleton_hom_of_subsingleton

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The retraction chain map of an `SDR` certificate

`SDR.check S` contains, in every degree, the sparse equation `ρ∂ = 0`: the retraction `ρ k` kills
boundaries.  Since the target complex `(zeroDiff S.b).toChainComplex` has *zero* differentials,
that equation is exactly the commutativity of the degreewise maps `ρ k` with the differentials,
i.e. it says that the family `(ρ k)` is a chain map

  `C.toChainComplex ⟶ (zeroDiff S.b).toChainComplex`.

This file constructs that chain map (`ChainComplex.ofHom`), the commutativity being the matrix
identity `ρ_k · ∂_{k+1} = 0` extracted from `SDR.check_implies` for `k < S.N` and, for `k ≥ S.N`,
from the triviality `S.b k = 0` (the matrix product then has no rows).

The two complexes are displayed in their explicit `ChainComplex.of` presentations (`cxOf`, and
`zeroCx` for `zeroDiff`) so that their objects are `ℤ^{(C.dim k)}` and `ℤ^{(S.b k)}` on the nose:
the categorical rewriting is done at those types, and the resulting chain map is transported back
to the requested complexes by definitional equality (`cxOf C = C.toChainComplex` and
`zeroCx b = (zeroDiff b).toChainComplex` are both `rfl`).
-/

namespace Work.Certificates.SDR

variable {C : FinChainCx}

/-- `C.toChainComplex`, in its explicit `ChainComplex.of` presentation.  It is the same complex
(`cxOf C = C.toChainComplex` is `rfl`), but as an `abbrev` its objects reduce to `ℤ^{(C.dim k)}`
under any transparency, which the categorical rewriting below relies on. -/
abbrev cxOf (C : FinChainCx) : ChainComplex (ModuleCat ℤ) ℕ :=
  ChainComplex.of (fun k => ModuleCat.of ℤ (Fin (C.dim k) → ℤ))
    (fun k => ModuleCat.ofHom (Matrix.toLin' ((C.bd k).toMatrix)))
    (fun k => by
      rw [← ModuleCat.ofHom_comp, ← Matrix.toLin'_mul, C.bd_comp k]
      simp)

/-- The complex with `b k` free generators in degree `k` and zero boundary maps, in its explicit
`ChainComplex.of` presentation.  It is the same complex as `(zeroDiff b).toChainComplex`
(`zeroCx b = (zeroDiff b).toChainComplex` is `rfl`); see `cxOf` for why the explicit form is
used. -/
abbrev zeroCx (b : ℕ → ℕ) : ChainComplex (ModuleCat ℤ) ℕ :=
  ChainComplex.of (fun k => ModuleCat.of ℤ (Fin (b k) → ℤ))
    (fun k => ModuleCat.ofHom (Matrix.toLin' ((SOp.zero (b k) (b (k + 1))).toMatrix)))
    (fun _ => by
      simp only [SOp.toMatrix_zero, map_zero, ModuleCat.ofHom_zero,
        CategoryTheory.Limits.zero_comp])

/-- `ρ k` kills the boundary `∂_{k+1}` in every degree: `(ρ k) * (bd k) = 0`.

For `k < S.N` this is the second equation read off from `SDR.check` by `SDR.check_implies`; for
`k ≥ S.N` the matrix product has no rows because `S.b k = 0`. -/
lemma rho_mul_bd_zero (S : SDR C) (h : S.check = true) (k : ℕ) :
    (S.ρ k).toMatrix * (C.bd k).toMatrix = 0 := by
  by_cases hk : k < S.N
  · exact (check_implies S h k hk).2.1
  · have hb : S.b k = 0 := S.b_zero k (not_lt.mp hk)
    ext i j
    exact Fin.elim0 (hb ▸ i)

/-- The retraction `ρ` of an `SDR` certificate is a chain map, in the explicit presentations of
the source and target complexes. -/
theorem exists_retract_chainMap_explicit (S : SDR C) (h : S.check = true) :
    ∃ φ : ChainHom (cxOf C) (zeroCx S.b),
      ∀ k, φ.f k = ModuleCat.ofHom (Matrix.toLin' ((S.ρ k).toMatrix)) := by
  refine ⟨ChainComplex.ofHom
    (fun k => ModuleCat.ofHom (Matrix.toLin' ((S.ρ k).toMatrix))) ?_, fun k => rfl⟩
  intro i
  -- The commutativity `f (i+1) ≫ ∂^{target}_{i+1,i} = ∂^{C}_{i+1,i} ≫ f i`.  The target
  -- differential is zero, so the left hand side vanishes, and the right hand side is the
  -- matrix product `ρ_i * ∂_{i+1} = 0`.
  simp only [zeroCx, ChainComplex.of_d, SOp.toMatrix_zero, map_zero, ModuleCat.ofHom_zero,
    CategoryTheory.Limits.comp_zero, cxOf]
  rw [← ModuleCat.ofHom_comp, ← Matrix.toLin'_mul, rho_mul_bd_zero S h i]
  simp

/-- The retraction `ρ` of an `SDR` certificate is a chain map from `C` to the complex with zero
boundary maps and the Betti numbers `S.b` of the certificate.  Its `k`-th component is the linear
map with matrix `(S.ρ k).toMatrix`. -/
theorem retract_chainMap (S : SDR C) (h : S.check = true) :
    ∃ φ : ChainHom C.toChainComplex (FinChainCx.zeroDiff S.b).toChainComplex,
      ∀ k, φ.f k = ModuleCat.ofHom (Matrix.toLin' ((S.ρ k).toMatrix)) := by
  obtain ⟨φ, hφ⟩ := exists_retract_chainMap_explicit S h
  exact ⟨φ, hφ⟩

end Work.Certificates.SDR
