import Mathlib
import Submission.Work.Cohomology.Affine

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The boundary formula for linear simplices of `Δⁿ`

This file proves the boundary formula

`d (linSimplex v) = ∑ᵢ (-1)ⁱ • linSimplex (v ∘ Fin.succAbove i)`

for a *linear* `(k+1)`-simplex `v : Fin (k+2) → Δⁿ` of the standard simplex `Δⁿ`, where the
differential is that of the simplicial chain complex of the singular simplicial set of `Δⁿ`.

The two ingredients are

* `linSimplex_δ` — the `i`-th face of a linear simplex is the linear simplex with vertex family
  `v ∘ Fin.succAbove i` (which rests on the functoriality `affineSimplex_stdSimplex_map` of the
  affine simplex in its vertex family), and
* `chainComplex_d_ι_apply` — Mathlib's `SSet.ιChainComplex_d`, evaluated at the generator `1` of
  the coefficient ring.

This is what makes the subdivision chain maps of `Δⁿ` well defined: it is precisely the statement
that the boundary of a small (linear) simplex is a sum of small simplices.
-/

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

/-- **Functoriality of the affine simplex in its vertex family.**  For `f : Fin (l+1) → Fin (k+1)`
the affine simplex on `v` evaluated on the push-forward `stdSimplex.map f t` of `t` is the affine
simplex on the reindexed family `v ∘ f` evaluated at `t`. -/
theorem affineSimplex_stdSimplex_map {n k l : ℕ}
    (v : Fin (k + 1) → stdSimplex ℝ (Fin (n + 1)))
    (f : Fin (l + 1) → Fin (k + 1)) (t : stdSimplex ℝ (Fin (l + 1))) :
    affineSimplex v (stdSimplex.map f t) = affineSimplex (fun i => v (f i)) t := by
  ext p
  rw [affineSimplex_apply, affineSimplex_apply]
  simp only [stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply]
  simp only [Finset.sum_mul]
  trans ∑ x, ∑ i with f i = x, t i * (v (f i)) p
  · apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_filter] at hi
    rw [hi.2]
  · rw [Finset.sum_fiberwise Finset.univ f (fun i => t i * (v (f i)) p)]

/-- **The faces of a linear simplex are linear.**  The `i`-th face of the singular simplex
`linSimplex v` of `Δⁿ` is the linear simplex whose vertex family is `v ∘ Fin.succAbove i`. -/
theorem linSimplex_δ {n k : ℕ} (v : Fin (k + 2) → stdSimplex ℝ (Fin (n + 1)))
    (i : Fin (k + 2)) :
    (TopCat.toSSet.obj (Delta n)).δ i (linSimplex v)
      = linSimplex (fun j => v (Fin.succAbove i j)) := by
  apply (TopCat.toSSetObjEquiv (Delta n) (Opposite.op ⦋k⦌)).injective
  ext z : 1
  rw [TopCat.toSSetObjEquiv_δ_apply, toSSetObjEquiv_linSimplex, toSSetObjEquiv_linSimplex]
  show affineSimplex v (stdSimplexHomeomorph _ (Convexity.StdSimplex.map i.succAbove z))
    = affineSimplex _ (stdSimplexHomeomorph _ z)
  rw [stdSimplexHomeomorph_map]
  exact affineSimplex_stdSimplex_map v i.succAbove _

/-- **The differential on a generator of the singular chain complex.**  For a simplicial set `X`
and an `(n+1)`-simplex `x`, the differential of the chain `1 • x` is the alternating sum of the
faces of `x`.  This is Mathlib's `SSet.ιChainComplex_d` evaluated at the unit `1` of the
coefficient ring. -/
theorem chainComplex_d_ι_apply (R : Type) [CommRing R] {X : SSet} {n : ℕ} (x : X _⦋n + 1⦌) :
    ((X.chainComplex (ModuleCat.of R R)).d (n + 1) n)
        ((X.ιChainComplex (R := ModuleCat.of R R) x) (1 : R))
      = ∑ i : Fin (n + 2), ((-1 : ℤ) ^ (i : ℕ)) •
          (X.ιChainComplex (R := ModuleCat.of R R) (X.δ i x)) (1 : R) := by
  have h := SSet.ιChainComplex_d X (ModuleCat.of R R) x
  have h2 := congrArg
    (fun (f : ModuleCat.of R R ⟶ (X.chainComplex (ModuleCat.of R R)).X n) => f (1 : R)) h
  simp only [ModuleCat.hom_comp, ModuleCat.hom_sum, ModuleCat.hom_zsmul,
    LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply] at h2
  exact h2

/-- **The boundary formula for linear simplices.**  The boundary of the singular `(k+1)`-simplex of
`Δⁿ` which is linear with vertex family `v` is the alternating sum of the linear `k`-simplices
obtained by restricting `v` to the faces of `Δ^{k+1}`. -/
theorem linSimplex_boundary (R : Type) [CommRing R] {n k : ℕ}
    (v : Fin (k + 2) → stdSimplex ℝ (Fin (n + 1))) :
    ((TopCat.toSSet.obj (Delta n)).chainComplex (ModuleCat.of R R)).d (k + 1) k
        (((TopCat.toSSet.obj (Delta n)).ιChainComplex (R := ModuleCat.of R R)
          (linSimplex v)).hom 1)
      = ∑ i : Fin (k + 2), ((-1 : ℤ) ^ (i : ℕ)) •
          ((TopCat.toSSet.obj (Delta n)).ιChainComplex (R := ModuleCat.of R R)
            (linSimplex (fun j => v (Fin.succAbove i j)))).hom 1 := by
  rw [chainComplex_d_ι_apply R (X := TopCat.toSSet.obj (Delta n)) (n := k) (linSimplex v)]
  apply Finset.sum_congr rfl
  intro i _
  rw [linSimplex_δ]

end

end Work.Cohomology
