import Mathlib
import Submission.Work.Cohomology.Subdivision
import Submission.Work.Cohomology.linSimplex_boundary

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# `toChain` is a chain map for `boundaryLC`

The affine-chain chain map `toChain N k : LinChain N k → C_k(Δᴺ)` sends a vertex family
`v : Fin (k+1) → Δᴺ` to the singular chain of the affine simplex `linSimplex v`.  This file
identifies the differential of the latter with the affine boundary `boundaryLC`, i.e. proves that
`toChain` intertwines `boundaryLC` with the differential of the simplicial chain complex of `Δᴺ`:

`toChain N k (boundaryLC N k c) = d (toChain N (k+1) c)`.

The proof is by checking the identity on the generators `Finsupp.single v 1` of the free
`ℤ`-module `LinChain N (k+1)` (via `Finsupp.basisSingleOne`), where it is the boundary formula
`linSimplex_boundary` for linear simplices together with the computation of `boundaryLC` on a
generator.
-/

namespace Work.Cohomology

noncomputable section

/-- **`toChain` on a generator.**  The chain associated with the affine simplex `v`, scaled by the
integer `a`. -/
lemma toChain_apply_single (N k : ℕ)
    (v : Fin (k + 1) → stdSimplex ℝ (Fin (N + 1))) (a : ℤ) :
    toChain N k (Finsupp.single v a) =
      a • (((TopCat.toSSet.obj (Delta N)).ιChainComplex (R := ModuleCat.of ℤ ℤ)
            (linSimplex v)).hom (1 : ℤ)) := by
  show Finsupp.linearCombination ℤ _ (Finsupp.single v a) = _
  rw [Finsupp.linearCombination_single]
  exact Int.cast_smul_eq_zsmul ℤ a _

/-- **`boundaryLC` on a generator.**  The alternating sum of the faces of the vertex family `v`. -/
lemma boundaryLC_apply_single (N j : ℕ)
    (v : Fin (j + 2) → stdSimplex ℝ (Fin (N + 1))) (a : ℤ) :
    boundaryLC N j (Finsupp.single v a) =
      ∑ i : Fin (j + 2), ((-1 : ℤ) ^ (i : ℕ)) • Finsupp.single (faceVF (N := N) i v) a := by
  simp only [boundaryLC, LinearMap.sum_apply, LinearMap.smul_apply, Finsupp.lmapDomain_apply,
    Finsupp.mapDomain_single]

/-- **`toChain` commutes with the boundary.**  On affine `(k+1)`-chains of `Δᴺ` the affine
boundary `boundaryLC` is carried by `toChain` to the differential of the simplicial chain complex
of `Δᴺ`. -/
theorem toChain_boundaryLC (N k : ℕ) (c : LinChain N (k + 1)) :
    toChain N k (boundaryLC N k c) =
      (((TopCat.toSSet.obj (Delta N)).chainComplex (ModuleCat.of ℤ ℤ)).d (k + 1) k).hom
        (toChain N (k + 1) c) := by
  have key : (toChain N k) ∘ₗ (boundaryLC N k)
      = (ModuleCat.Hom.hom (((TopCat.toSSet.obj (Delta N)).chainComplex (ModuleCat.of ℤ ℤ)).d
          (k + 1) k)) ∘ₗ (toChain N (k + 1)) := by
    refine Finsupp.basisSingleOne.ext fun v => ?_
    simp only [LinearMap.comp_apply, Finsupp.coe_basisSingleOne]
    rw [boundaryLC_apply_single, map_sum]
    simp only [LinearMap.map_smul, toChain_apply_single]
    simp only [one_zsmul]
    rw [linSimplex_boundary (R := ℤ) v]
    apply Finset.sum_congr rfl
    intro i _
    exact Int.cast_smul_eq_zsmul ℤ ((-1 : ℤ) ^ (i : ℕ)) _
  exact LinearMap.congr_fun key c

end

end Work.Cohomology
