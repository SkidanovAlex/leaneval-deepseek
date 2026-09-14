import Mathlib
import Submission.Subspace.MaxRankFinite
import Submission.Subspace.PermReindex
import Submission.Commons.LinearAlgebra.FiniteDim.finrank_comap_of_linearEquiv
import Submission.Commons.LinearAlgebra.Matrix.inv_submatrix_perm

/-!
# The charted chain contradiction

`no_long_chain` is the contradiction obtained from a chain of `m` approximation sets whose
spaces are hyperplanes `ker (b h ·)` with the distinguished chart `(0, 1)`: the pivot is the
coordinate `0` (so `b h 0 ≠ 0`) and the height certificate is on `-(b h 1) / (b h 0)`.

The outer finiteness argument (the maximal-rank case of Schmidt's subspace theorem) produces,
for each `Q`, a hyperplane `V(Q) = approxSpace L γ Q` together with a normal `b` and a chart
`(a,j)` for which the height certificate holds; pigeonholing over the finitely many charts
`(a,j)` (`a ≠ j`) leaves one fixed chart, and one then applies the chain contradiction after
reindexing the coordinates by a permutation `σ` with `σ 0 = a`, `σ 1 = j`.

`no_long_chain_chart` is exactly that reindexed form.  Its proof reindexes `L` to
`L.submatrix σ σ` and `γ` to `γ ∘ σ`, and applies `no_long_chain`.  Note that the Siegel input
`hCbound` is stated for the *reindexed* matrix `lambdaMat K (L.submatrix σ σ) (hLK ∘ σ)`, which
is what the outer argument produces (instantiate the Siegel lemma at the fixed chart); stating
it for the original matrix instead would force the elaborator into an expensive defeq check
(`Matrix.submatrix` versus `Matrix.inv`).
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false

open scoped BigOperators
open MvPolynomial

namespace Submission.Subspace

/-- **The charted chain contradiction.**  Same as `no_long_chain`, but with a permutation `σ` of
the coordinates: the distinguished chart is `(σ 0, σ 1)` rather than `(0,1)`.  This is the form
in which the outer finiteness argument is applied (after a pigeonhole over the finitely many
possible charts). -/
theorem no_long_chain_chart {n : ℕ} (hn : 1 ≤ n) {m : ℕ} (hm : 2 ≤ m)
    (L : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) (hL : L.det ≠ 0) (hLa : ∀ i j, IsAlgebraic ℚ (L i j))
    (γ : Fin (n+1) → ℝ) (hγ1 : ∀ i, γ i ≤ 1) (hsum : ∑ i, γ i < 0)
    (ε S : ℝ) (hεeq : ε = -∑ i, γ i) (hSeqq : S = ∑ i, |γ i|)
    (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (MΛ : ℝ) (hMΛ1 : 1 ≤ MΛ)
    (K : IntermediateField ℚ ℂ) (hKfin : FiniteDimensional ℚ K) (hLK : ∀ i j, L i j ∈ K)
    (hMΛ : ∀ i j, ‖lambdaMatC K L hLK i j‖ ≤ MΛ)
    (cc : ℕ) (hcc : 0 < cc) (hint : ∀ i j, IsIntegral ℤ ((cc : ↥K) * lambdaMat K L hLK i j))
    (σ : Equiv.Perm (Fin (n+1)))
    (C : ℝ) (hC1 : 1 ≤ C)
    (hCbound : SiegelBound K (lambdaMat K (L.submatrix σ σ) (fun i j => hLK (σ i) (σ j)))
      MΛ C)
    (hW : 2 * (Module.finrank ℚ ↥K) ≤ (m : ℝ) * (mrTheta n ε S) ^ 2)
    (R : ℝ) (hR : 2 ≤ R * mrEta n ε S ^ (2 ^ (m - 1)))
    (Q : Fin m → ℝ) (hQ1 : ∀ h, 1 ≤ Q h)
    (hQbig : ∀ h, mrA n ε S θ MΛ C m ≤ Real.log (Q h))
    (hgap : ∀ i j : Fin m, i ≤ j → (Q j) ^ (R ^ ((j : ℕ) - (i : ℕ))) ≤ Q i)
    (b : Fin m → Fin (n+1) → ℤ) (hb0 : ∀ h, b h (σ 0) ≠ 0)
    (hker : ∀ h (x : Fin (n+1) → ℚ),
      x ∈ approxSpace L γ (Q h) ↔ ∑ j, (b h j : ℚ) * x j = 0)
    (hfr : ∀ h, Module.finrank ℚ (approxSpace L γ (Q h)) = n)
    (hcert : ∀ h, θ * Real.log (Q h) ≤
      Height.logHeight₁ (-((b h (σ 1) : ℤ) : ℚ) / ((b h (σ 0) : ℤ) : ℚ))) :
    False := by
  classical
  haveI : FiniteDimensional ℚ ↥K := hKfin
  let Τe : (Fin (n+1) → ℚ) ≃ₗ[ℚ] (Fin (n+1) → ℚ) :=
    { toFun := fun x i => x (σ.symm i)
      invFun := fun x i => x (σ i)
      left_inv := fun x => by funext i; simp
      right_inv := fun x => by funext i; simp
      map_add' := fun a b => by funext i; simp
      map_smul' := fun c a => by funext i; simp }
  have hker' : ∀ h (x : Fin (n+1) → ℚ),
      x ∈ approxSpace (fun i k => L (σ i) (σ k)) (fun i => γ (σ i)) (Q h)
        ↔ ∑ j, (((b h) (σ j) : ℤ) : ℚ) * x j = 0 := by
    intro h x
    rw [mem_approxSpace_perm σ L γ (Q h) x, hker h (fun i => x (σ.symm i))]
    have hsum' : (∑ j, (b h j : ℚ) * x (σ.symm j)) = ∑ j, (b h (σ j) : ℚ) * x j := by
      rw [← Equiv.sum_comp σ (fun j => (b h j : ℚ) * x (σ.symm j))]
      simp
    rw [hsum']
  have hfr' : ∀ h, Module.finrank ℚ
      (approxSpace (fun i k => L (σ i) (σ k)) (fun i => γ (σ i)) (Q h)) = n := by
    intro h
    have hV : approxSpace (fun i k => L (σ i) (σ k)) (fun i => γ (σ i)) (Q h)
        = (approxSpace L γ (Q h)).comap (Τe : (Fin (n+1) → ℚ) →ₗ[ℚ] (Fin (n+1) → ℚ)) := by
      ext x
      rw [Submodule.mem_comap]
      exact mem_approxSpace_perm σ L γ (Q h) x
    rw [hV, Commons.LinearAlgebra.FiniteDim.finrank_comap_of_linearEquiv Τe (approxSpace L γ (Q h))]
    exact hfr h
  have hL' : (L.submatrix σ σ).det ≠ 0 := by
    rw [Matrix.det_submatrix_equiv_self σ L]
    exact hL
  have hcoeff : coeffMatrix K (L.submatrix σ σ) (fun i j => hLK (σ i) (σ j))
      = (coeffMatrix K L hLK).submatrix σ σ := by
    ext i j; rfl
  have hlam : lambdaMat K (L.submatrix σ σ) (fun i j => hLK (σ i) (σ j))
      = (lambdaMat K L hLK).submatrix σ σ := by
    simp only [lambdaMat]
    rw [hcoeff, Commons.LinearAlgebra.Matrix.inv_submatrix_perm, Matrix.transpose_submatrix]
  have hlamC : lambdaMatC K (L.submatrix σ σ) (fun i j => hLK (σ i) (σ j))
      = (lambdaMatC K L hLK).submatrix σ σ := by
    simp only [lambdaMatC, hlam]
    ext i j
    rfl
  have hMΛ' : ∀ i j, ‖lambdaMatC K (L.submatrix σ σ) (fun i j => hLK (σ i) (σ j)) i j‖ ≤ MΛ := by
    intro i j
    have h1 : lambdaMatC K (L.submatrix σ σ) (fun i j => hLK (σ i) (σ j)) i j
        = lambdaMatC K L hLK (σ i) (σ j) := by
      rw [hlamC]; rfl
    rw [h1]; exact hMΛ (σ i) (σ j)
  have hint' : ∀ i j, IsIntegral ℤ
      ((cc : ↥K) * lambdaMat K (L.submatrix σ σ) (fun i j => hLK (σ i) (σ j)) i j) := by
    intro i j
    have h1 : lambdaMat K (L.submatrix σ σ) (fun i j => hLK (σ i) (σ j)) i j
        = lambdaMat K L hLK (σ i) (σ j) := by
      rw [hlam]; rfl
    rw [h1]; exact hint (σ i) (σ j)
  refine no_long_chain hn hm (L.submatrix σ σ) hL'
    (fun i j => by simpa using hLa (σ i) (σ j))
    (fun i => γ (σ i)) (fun i => hγ1 (σ i))
    ?_ ε S ?_ ?_ θ hθ0 hθ1 MΛ hMΛ1 K hKfin (fun i j => hLK (σ i) (σ j)) hMΛ'
    cc hcc hint' C hC1 hCbound hW R hR Q hQ1 hQbig hgap (fun h i => b h (σ i))
    (fun h => hb0 h) hker' hfr' hcert
  · rw [Equiv.sum_comp σ γ]; exact hsum
  · rw [hεeq, Equiv.sum_comp σ γ]
  · rw [hSeqq]; exact (Equiv.sum_comp σ (fun i => |γ i|)).symm

end Submission.Subspace
