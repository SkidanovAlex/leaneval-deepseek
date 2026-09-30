import Mathlib
import Submission.Work.HomologyExtra.Basic
import Submission.Work.HomologyExtra.simplexNorthCap_contractible
import Submission.Work.HomologyExtra.simplexSouthCap_contractible
import Submission.Work.HomologyExtra.simplexBand_reducedH0_one

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# `H₁(∂Δ²; ℤ) ≅ ℤ`

The boundary `∂Δ²` of the standard `2`-simplex is a circle, so its first singular
homology with `ℤ`-coefficients is `ℤ`.  This is the base case (`n = 1`, `k = 1`) of
the computation of the homology of `∂Δⁿ⁺¹`.

The proof is the Mayer–Vietoris base case for the cover of `∂Δ²` by the two caps
`simplexNorthCap 1 = {w_last > 0}` and `simplexSouthCap 1 = {w_last < 1}`, whose
intersection is the band `simplexBand 1`:

`H₁(∂Δ²) ≅ ker(H₀(band) ⟶ H₀(cap) ⊕ H₀(cap)) ≅ ker(ε_band) ≅ ℤ`,

the last step because the band has exactly two contractible components
(`simplexBand_reducedH0_one`).
-/

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

set_option linter.style.haveILetI false

namespace Work.HomologyExtra

noncomputable section

/-- The north cap `{w_last > 0}` of `∂Δⁿ⁺¹` is open. -/
theorem isOpen_simplexNorthCap (n : ℕ) : IsOpen (simplexNorthCap n) := by
  have h : Continuous (fun x : boundarySpace (n + 1) =>
      (x : simplex (n + 1)).weights (Fin.last (n + 1))) :=
    (Convexity.StdSimplex.continuous_weights_apply ℝ (Fin.last (n + 1))).comp
      continuous_subtype_val
  exact isOpen_lt continuous_const h

/-- The south cap `{w_last < 1}` of `∂Δⁿ⁺¹` is open. -/
theorem isOpen_simplexSouthCap (n : ℕ) : IsOpen (simplexSouthCap n) := by
  have h : Continuous (fun x : boundarySpace (n + 1) =>
      (x : simplex (n + 1)).weights (Fin.last (n + 1))) :=
    (Convexity.StdSimplex.continuous_weights_apply ℝ (Fin.last (n + 1))).comp
      continuous_subtype_val
  exact isOpen_lt h continuous_const

/-- The two caps cover `∂Δⁿ⁺¹`. -/
theorem simplexNorthCap_union_simplexSouthCap (n : ℕ) :
    simplexNorthCap n ∪ simplexSouthCap n = Set.univ := by
  ext x
  simp only [Set.mem_union, Set.mem_univ, iff_true, simplexNorthCap, simplexSouthCap,
    Set.mem_ofPred_eq]
  rcases lt_or_ge 0 ((x : simplex (n + 1)).weights (Fin.last (n + 1))) with h | h
  · exact Or.inl h
  · refine Or.inr ?_
    have hnn : 0 ≤ (x : simplex (n + 1)).weights (Fin.last (n + 1)) :=
      Convexity.StdSimplex.weights_nonneg (w := (x : simplex (n + 1))) _
    linarith

/-- **`H₁(∂Δ²; ℤ) ≅ ℤ`.** -/
theorem simplexBoundary_homologyOne :
    Nonempty (Work.Homology.singHomology Work.Homology.ZMod 1
      (Work.HomologyExtra.boundarySpace (0 + 2)) ≅ Work.Homology.ZMod) := by
  have hN : ContractibleSpace ↥(simplexNorthCap 1) := simplexNorthCap_contractible 1
  have hS : ContractibleSpace ↥(simplexSouthCap 1) := simplexSouthCap_contractible 1
  haveI := hN
  haveI := hS
  -- the two caps are open and cover the boundary
  have hU : IsOpen (simplexNorthCap 1) := isOpen_simplexNorthCap 1
  have hV : IsOpen (simplexSouthCap 1) := isOpen_simplexSouthCap 1
  have hcov : simplexNorthCap 1 ∪ simplexSouthCap 1 = Set.univ :=
    simplexNorthCap_union_simplexSouthCap 1
  -- Mayer--Vietoris: `H₁(∂Δ²)` is the kernel of the zeroth MV map
  obtain ⟨e1⟩ := Work.Cohomology.mvδX_zero_iso (simplexNorthCap 1) (simplexSouthCap 1)
    hU hV hcov
  -- ... which is the kernel of the augmentation of the band
  have hker : LinearMap.ker (ModuleCat.Hom.hom
        (HomologicalComplex.homologyMap (Work.Cohomology.mvLeft (simplexNorthCap 1)
          (simplexSouthCap 1)) 0))
      = LinearMap.ker (ModuleCat.Hom.hom (TopCat.singularHomology₀ε
          (TopCat.of ↥((simplexNorthCap 1) ∩ (simplexSouthCap 1))) (ModuleCat.of ℤ ℤ))) :=
    Work.Cohomology.ker_mvLeft_zero_eq_ker_eps (simplexNorthCap 1) (simplexSouthCap 1)
  have e2 : Work.Cohomology.kerMod (ModuleCat.Hom.hom
        (HomologicalComplex.homologyMap (Work.Cohomology.mvLeft (simplexNorthCap 1)
          (simplexSouthCap 1)) 0))
      ≅ Work.Cohomology.kerMod (ModuleCat.Hom.hom (TopCat.singularHomology₀ε
          (TopCat.of ↥((simplexNorthCap 1) ∩ (simplexSouthCap 1)))
          (ModuleCat.of ℤ ℤ))) :=
    LinearEquiv.toModuleIso (LinearEquiv.ofEq _ _ hker)
  -- the reduced `H₀` of the band is `ℤ`
  obtain ⟨e3⟩ := simplexBand_reducedH0_one
  exact ⟨e1 ≪≫ e2 ≪≫ e3⟩

end

end Work.HomologyExtra
