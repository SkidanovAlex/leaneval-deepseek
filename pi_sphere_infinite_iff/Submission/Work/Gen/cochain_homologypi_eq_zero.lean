import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# A cocycle of vanishing cohomology class is a coboundary (cochain complexes)

The cochain (as opposed to chain) analogue of `Work.RatHurewicz.Bridge.chain_homologypi_eq_zero`
(`Submission/Work/RatHurewicz/Bridge/chainBoundary.lean`): for a cochain complex `K` of `ℤ`-modules
and a cycle `z ∈ Z^{n+1}(K)` whose cohomology class vanishes, the underlying cochain is the
coboundary of an `n`-chain.

Both statements are the elementary "cycles modulo boundaries" computation, obtained from the
exactness of the short complex `K.sc (n+1)`: the projection `pOpcycles` of the cycle is zero, and
`ShortComplex.moduleCat_pOpcycles_eq_zero_iff` identifies this with membership in the range of the
differential `K.d n (n+1)`.
-/

open CategoryTheory

namespace Work.Gen

noncomputable section

/-- **A cocycle of a cochain complex of `ℤ`-modules whose class vanishes is a coboundary.** -/
theorem cochain_homologypi_eq_zero (K : CochainComplex (ModuleCat ℤ) ℕ) [∀ i, K.HasHomology i]
    (n : ℕ) (z : K.cycles (n + 1)) (h : K.homologyπ (n + 1) z = 0) :
    ∃ y : K.X n, (K.d n (n + 1)).hom y = (K.iCycles (n + 1)).hom z := by
  have hprev : (ComplexShape.up ℕ).prev (n + 1) = n := by
    rw [ComplexShape.prev_eq']
    rfl
  let z' : (K.sc (n + 1)).cycles := z
  have hkey : ∃ w : (K.sc (n + 1)).X₁,
      (K.sc (n + 1)).f.hom w = (K.sc (n + 1)).iCycles.hom z' := by
    have hzero : (K.sc (n + 1)).homologyι ((K.sc (n + 1)).homologyπ z') = 0 := by
      rw [show (K.sc (n + 1)).homologyπ z' = 0 from h, map_zero]
    have hpop : (K.sc (n + 1)).pOpcycles ((K.sc (n + 1)).iCycles.hom z') = 0 := by
      have hh := congrArg (fun (g : (K.sc (n + 1)).cycles ⟶ (K.sc (n + 1)).opcycles) => g z')
        (ShortComplex.homology_π_ι (K.sc (n + 1)))
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hh
      rw [← hh]
      exact hzero
    have hmem := (ShortComplex.moduleCat_pOpcycles_eq_zero_iff (K.sc (n + 1))
      ((K.sc (n + 1)).iCycles.hom z')).mp hpop
    obtain ⟨w, hw⟩ := LinearMap.mem_range.mp hmem
    exact ⟨w, hw⟩
  obtain ⟨w, hw⟩ := hkey
  refine ⟨(K.XIsoOfEq hprev).hom w, ?_⟩
  have hh : (K.d n (n + 1)).hom ((K.XIsoOfEq hprev).hom w) =
      (K.d ((ComplexShape.up ℕ).prev (n + 1)) (n + 1)).hom w := by
    have h1 : (K.XIsoOfEq hprev).hom ≫ K.d n (n + 1) =
        K.d ((ComplexShape.up ℕ).prev (n + 1)) (n + 1) :=
      HomologicalComplex.XIsoOfEq_hom_comp_d K hprev (n + 1)
    calc (K.d n (n + 1)).hom ((K.XIsoOfEq hprev).hom w)
        = ((K.XIsoOfEq hprev).hom ≫ K.d n (n + 1)).hom w := by
          rw [ModuleCat.hom_comp]
          rfl
      _ = (K.d ((ComplexShape.up ℕ).prev (n + 1)) (n + 1)).hom w := by rw [h1]
  rw [hh]
  exact hw

end

end Work.Gen
