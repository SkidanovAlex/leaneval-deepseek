import Mathlib
import Submission.Work.Homology.Spheres
import Submission.Work.Homology.StdSimplexHomology
import Submission.Work.DeltaHomology.RealizationDefs
import Submission.Work.DeltaHomology.PunctSimplex
import Submission.Work.HomologyExtra.SimplexDisk
import Submission.Work.HomologyExtra.exists_cornerDiskHomeo
import Submission.Work.HomologyExtra.isIso_relHomologyMap_pairHomOfHomeomorph
import Submission.Work.HomologyExtra.relHomology_simplexPair

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.DeltaHomology

open CategoryTheory AlgebraicTopology CategoryTheory.Limits Work.Homology

noncomputable section

/-! ## The singular chains of an empty space

The relative chain complex of a pair `(X, A)` is the cokernel of the inclusion
`C_*(A) ⟶ C_*(X)`.  For the empty subspace `A = ∅` the source `C_*(∅)` is the zero complex
(the singular simplicial set of an empty space has no simplices at all), so the inclusion is the
zero map and the cokernel is `C_*(X)` itself.  Consequently `H_k(X, ∅) ≅ H_k(X)`.

This is the input needed for the `n = 0` case of the relative homology of `(Δⁿ, ∂Δⁿ)`, where the
boundary is empty. -/

/-- **The singular chain complex of an empty space is the zero complex.**  The singular simplicial
set of an empty space has no simplices in any degree, so it is an empty simplicial set and
Mathlib's `SSet.isZero_chainComplex` applies. -/
theorem isZero_singChain_of_isEmpty (R : ModuleCat ℤ) (X : TopCat) [IsEmpty X] :
    IsZero (singChain R X) := by
  have hne : ¬ (TopCat.toSSet.obj X).Nonempty := by
    rintro ⟨x⟩
    have hpt : Nonempty (Convexity.StdSimplex ℝ (Fin (0 + 1))) := inferInstance
    have h1 : IsEmpty C(Convexity.StdSimplex ℝ (Fin (0 + 1)), X) :=
      Function.isEmpty (fun f : C(Convexity.StdSimplex ℝ (Fin (0 + 1)), X) =>
        f (Classical.arbitrary _))
    exact h1.false ((TopCat.toSSetObjEquiv X (Opposite.op (SimplexCategory.mk 0))) x)
  haveI : (TopCat.toSSet.obj X).HasDimensionLT 0 :=
    (SSet.notNonempty_iff_hasDimensionLT_zero (TopCat.toSSet.obj X)).mp hne
  exact SSet.isZero_chainComplex (X := TopCat.toSSet.obj X) (R := R)

/-- **The inclusion of the empty subspace is the zero map** on singular chains. -/
theorem inclChain_empty_eq_zero (R : ModuleCat ℤ) (X : TopCat) :
    inclChain R X (∅ : Set X) = 0 := by
  haveI : IsEmpty ↥(∅ : Set X) := ⟨fun x => x.2⟩
  exact (isZero_singChain_of_isEmpty R (TopCat.of (∅ : Set X))).eq_of_src _ _

/-- **Relative homology with respect to the empty subspace is absolute homology**:
`H_k(X, ∅; R) ≅ H_k(X; R)`. -/
theorem relHomology_empty (R : ModuleCat ℤ) (k : ℕ) (X : TopCat) :
    Nonempty (relHomology R k X (∅ : Set X) ≅ singHomology R k X) := by
  have h0 : inclChain R X (∅ : Set X) = 0 := inclChain_empty_eq_zero R X
  let e₁ : cokernel (inclChain R X (∅ : Set X)) ≅
      cokernel (0 : singChain R (TopCat.of (∅ : Set X)) ⟶ singChain R X) :=
    cokernelIsoOfEq h0
  let e₂ : cokernel (0 : singChain R (TopCat.of (∅ : Set X)) ⟶ singChain R X) ≅
      singChain R X := cokernelZeroIsoTarget
  let φ : relChain R X (∅ : Set X) ≅ singChain R X := e₁ ≪≫ e₂
  refine ⟨⟨HomologicalComplex.homologyMap φ.hom k, HomologicalComplex.homologyMap φ.inv k,
    ?_, ?_⟩⟩
  · rw [← HomologicalComplex.homologyMap_comp, φ.hom_inv_id,
      HomologicalComplex.homologyMap_id]
  · rw [← HomologicalComplex.homologyMap_comp, φ.inv_hom_id,
      HomologicalComplex.homologyMap_id]

/-! ## The case `n = 0` -/

/-- The boundary of the `0`-simplex is empty: the only barycentric coordinate of a point of
`Δ⁰` equals `1`. -/
theorem stdSimplexBoundary_zero :
    StdSimplexBoundary 0 = (∅ : Set (Convexity.StdSimplex ℝ (Fin 1))) := by
  ext w
  constructor
  · rintro ⟨i, hi⟩
    have h1 : w.weights 0 = 1 := by
      have h := w.total_of_fintype
      rwa [Fin.sum_univ_one] at h
    have hi0 : i = 0 := Fin.ext (by omega)
    rw [hi0] at hi
    linarith
  · intro h
    exact absurd h (Set.notMem_empty w)

/-- **The relative homology of `(Δ⁰, ∂Δ⁰) = (pt, ∅)`** is `ℤ` in degree `0` and `0` otherwise. -/
theorem relHomology_stdSimplexBoundary_zero (m : ℕ) :
    Nonempty (relHomology ZMod m (TopCat.of (Convexity.StdSimplex ℝ (Fin 1)))
        (StdSimplexBoundary 0) ≅
      (if m = 0 then ZMod else ModuleCat.of ℤ PUnit)) := by
  rw [stdSimplexBoundary_zero]
  have hX : relHomology ZMod m (TopCat.of (Convexity.StdSimplex ℝ (Fin 1)))
      (∅ : Set (Convexity.StdSimplex ℝ (Fin 1))) ≅
      singHomology ZMod m (TopCat.of (Convexity.StdSimplex ℝ (Fin 1))) :=
    (relHomology_empty ZMod m (TopCat.of (Convexity.StdSimplex ℝ (Fin 1)))).some
  haveI : ContractibleSpace (TopCat.of (Convexity.StdSimplex ℝ (Fin 1))) :=
    contractibleSpace_stdSimplex 0
  have hY : singHomology ZMod m (TopCat.of (Convexity.StdSimplex ℝ (Fin 1))) ≅
      (if m = 0 then ZMod else ModuleCat.of ℤ PUnit) := by
    rcases m with _ | m
    · simpa using
        singHomologyZeroIsoOfPathConnected ZMod (TopCat.of (Convexity.StdSimplex ℝ (Fin 1)))
    · have h0 : IsZero
          (singHomology ZMod (m + 1) (TopCat.of (Convexity.StdSimplex ℝ (Fin 1)))) :=
        isZero_singHomology_succ_of_contractible ZMod _ m
      simpa using h0.iso (isZero_moduleCat_of_subsingleton (ModuleCat.of ℤ PUnit))
  exact ⟨hX ≪≫ hY⟩

/-- **Relative homology of the standard simplex pair `(Δⁿ, ∂Δⁿ)`.**  For the standard `n`-simplex
`Δⁿ = StdSimplex ℝ (Fin (n+1))` and its boundary `∂Δⁿ = StdSimplexBoundary n = {w | ∃ i,
w.weights i = 0}`, the relative homology `H_m(Δⁿ, ∂Δⁿ; ℤ)` is `ℤ` in degree `n` and `0` in every
other degree.  (For `n = 0` this is `H_m(pt, ∅) = H_m(pt)`; for `n = 1` it is the disc pair
`(D¹, S⁰)`.)  This is the local model for the relative homology of a cell of a realized
`Δ`-complex.

For `n ≥ 1` this is `Work.HomologyExtra.relHomology_simplexPair`, obtained by transporting the
disc pair computation `Work.Homology.relHomology_disc_sphere` along the homeomorphism of pairs
`(Δⁿ, ∂Δⁿ) ≅ (Dⁿ, Sⁿ⁻¹)`; for `n = 0` the boundary is empty and the statement is
`H_m(pt, ∅) ≅ H_m(pt)` together with the contractibility of `Δ⁰`. -/
theorem relHomology_stdSimplexBoundary (n m : ℕ) :
    Nonempty (relHomology ZMod m (TopCat.of (Convexity.StdSimplex ℝ (Fin (n + 1))))
        (StdSimplexBoundary n) ≅
      (if m = n then ZMod else ModuleCat.of ℤ PUnit)) := by
  rcases n with _ | n
  · exact relHomology_stdSimplexBoundary_zero m
  · exact Work.HomologyExtra.relHomology_simplexPair (n + 1) m (by omega)

end

end Work.DeltaHomology
