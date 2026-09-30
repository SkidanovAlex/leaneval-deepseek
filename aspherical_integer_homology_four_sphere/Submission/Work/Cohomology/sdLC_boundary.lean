import Mathlib
import Submission.Work.Cohomology.Subdivision
import Submission.Work.Cohomology.boundaryLC_coneLC
import Submission.Work.Cohomology.embedLC_boundary
import Submission.Work.Cohomology.sum_embedLC_comp_zero
import Submission.Work.Cohomology.sdLC_one_boundary

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The boundary of the barycentric subdivision of the standard simplices

`sdLC` (in `Submission/Work/Cohomology/Subdivision.lean`) is the barycentric subdivision of the
identity `n`-simplex of `Δⁿ`, defined recursively by

`sdLC (n+1) = coneLC (barycentre) (Σᵢ (-1)ⁱ • embedLCᵢ (sdLC n))`.

The present file proves the key structural identity

`∂ (sdLC (n+1)) = Σᵢ (-1)ⁱ • embedLCᵢ (sdLC n)`

("the boundary of the subdivision of the identity simplex is the signed sum of the subdivisions of
its faces"), which is what makes the subdivision a chain map.

The proof is by induction on `n`.  Writing `D n := Σᵢ (-1)ⁱ • embedLCᵢ (sdLC n)` for the right
hand side, `sdLC (n+1) = coneLC (barycentre) (D n)`, so the sign-free cone formula
`boundaryLC_coneLC` gives `∂ (sdLC (n+1)) = D n - coneLC_b (∂ (D n))`.  It therefore suffices to
know that `D n` is a cycle.  For `n = m+1` that is

`∂ (D (m+1)) = Σᵢ (-1)ⁱ • embedLCᵢ (∂ (sdLC (m+1))) = Σᵢ (-1)ⁱ • embedLCᵢ (D m)`,

and expanding `D m` turns this into the alternating double sum `Σ_{i,j} (-1)^{i+j} δᵢ δⱼ`
applied to `sdLC m`, which vanishes by the simplicial identity (`sum_embedLC_comp_zero`).

The two auxiliary results used here, proved separately, are

* `embedLC_boundary` — `embedLC` is a chain map (`∂ ∘ embedLC = embedLC ∘ ∂`);
* `sum_embedLC_comp_zero` — the alternating double sum of composed face embeddings is `0`.
-/

open Finset

namespace Work.Cohomology

noncomputable section

/-- The (still-embedded) subdivided boundary of `Δ^{n+1}`: the right hand side of
`sdLC_boundary`, isolated here to make the induction statement readable. -/
abbrev sdLCbdryD (n : ℕ) : LinChain (n + 1) n :=
  ∑ i : Fin (n + 2), ((-1 : ℤ) ^ (i : ℕ)) • embedLC n n i (sdLC n)

/-- **`D (m+1)` is a cycle**, given that `∂ (sdLC (m+1)) = D m`.  The boundary of
`D (m+1) = Σᵢ (-1)ⁱ • embedLCᵢ (sdLC (m+1))` is `Σᵢ (-1)ⁱ • embedLCᵢ (D m)` (`embedLC` is a chain
map), and expanding `D m` turns this into the alternating double sum `Σ_{i,j} (-1)^{i+j} δᵢ δⱼ`,
which cancels by the simplicial identity. -/
theorem sdLCbdryD_boundary (m : ℕ)
    (h : boundaryLC (m+1) m (sdLC (m+1)) = sdLCbdryD m) :
    boundaryLC (m+2) m (sdLCbdryD (m+1)) = 0 := by
  have stepA : boundaryLC (m+2) m (sdLCbdryD (m+1))
      = ∑ i : Fin (m+3), ((-1:ℤ)^(i:ℕ)) • embedLC (m+1) m i (sdLCbdryD m) := by
    rw [show sdLCbdryD (m+1) =
        (∑ i : Fin (m+3), ((-1:ℤ)^(i:ℕ)) • embedLC (m+1) (m+1) i (sdLC (m+1))) from rfl]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, embedLC_boundary, h]
  have stepB : (∑ i : Fin (m+3), ((-1:ℤ)^(i:ℕ)) • embedLC (m+1) m i (sdLCbdryD m)) = 0 := by
    rw [show sdLCbdryD m =
        (∑ j : Fin (m+2), ((-1:ℤ)^(j:ℕ)) • embedLC m m j (sdLC m)) from rfl]
    have e1 : (∑ i : Fin (m+3), ((-1:ℤ)^(i:ℕ)) • embedLC (m+1) m i
          (∑ j : Fin (m+2), ((-1:ℤ)^(j:ℕ)) • embedLC m m j (sdLC m)))
        = (∑ p : Fin (m+3) × Fin (m+2),
            ((-1:ℤ)^((p.1:ℕ)+(p.2:ℕ))) • (embedLC (m+1) m p.1 ∘ₗ embedLC m m p.2) (sdLC m)) := by
      simp only [map_sum, map_smul, Finset.smul_sum, smul_smul, ← pow_add]
      conv_rhs => rw [← Finset.univ_product_univ, Finset.sum_product]
      simp only [LinearMap.comp_apply]
    have e2 : (∑ p : Fin (m+3) × Fin (m+2),
            ((-1:ℤ)^((p.1:ℕ)+(p.2:ℕ))) • (embedLC (m+1) m p.1 ∘ₗ embedLC m m p.2) (sdLC m))
        = (∑ p : Fin (m+3) × Fin (m+2),
            ((-1:ℤ)^((p.1:ℕ)+(p.2:ℕ))) • (embedLC (m+1) m p.1 ∘ₗ embedLC m m p.2)) (sdLC m) := by
      rw [LinearMap.sum_apply]
      simp only [LinearMap.smul_apply, LinearMap.comp_apply]
    rw [e1, e2, sum_embedLC_comp_zero m, LinearMap.zero_apply]
  rw [stepA, stepB]

/-- The simultaneous induction behind `sdLC_boundary`: `D (m+1)` is a cycle, and `∂ (sdLC (m+1))`
equals `D m`.  (`m = 0` is the base case, where the cone point is `Δ⁰`-valent and the naive cone
formula for `∂` no longer applies; it is supplied by `sdLC_one_boundary`.) -/
theorem sdLC_boundary_aux : ∀ m : ℕ,
    boundaryLC (m+2) m (sdLCbdryD (m+1)) = 0 ∧
    boundaryLC (m+1) m (sdLC (m+1)) = sdLCbdryD m := by
  intro m
  induction m with
  | zero =>
      refine ⟨?_, sdLC_one_boundary⟩
      exact sdLCbdryD_boundary 0 sdLC_one_boundary
  | succ n ih =>
      have h2 : boundaryLC (n+2) (n+1) (sdLC (n+2)) = sdLCbdryD (n+1) := by
        show boundaryLC (n+2) (n+1)
          (coneLC (n+2) (n+1) (bary (idVert (n+2))) (sdLCbdryD (n+1))) = sdLCbdryD (n+1)
        rw [boundaryLC_coneLC (n+2) n (bary (idVert (n+2))) (sdLCbdryD (n+1)), ih.1]
        simp
      exact ⟨sdLCbdryD_boundary (n+1) h2, h2⟩

theorem sdLC_boundary (n : ℕ) :
    boundaryLC (n + 1) n (sdLC (n + 1)) =
      ∑ i : Fin (n + 2), ((-1 : ℤ) ^ (i : ℕ)) • embedLC n n i (sdLC n) :=
  (sdLC_boundary_aux n).2

end

end Work.Cohomology
