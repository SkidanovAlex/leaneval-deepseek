import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Submission.Commons.LinearAlgebra.Matrix.exists_maximalRank_kernel

namespace Commons.LinearAlgebra.Matrix

/-- **A maximal-rank kernel basis for a nonzero row vector over an arbitrary finite index type.**
If `ρ : ι → K` is nonzero (`ι` finite), there is a matrix `ϑ : Matrix ι (Fin (card ι - 1)) K`
whose columns are linearly independent and which is annihilated by `ρ` (i.e. `ρ ᵥ* ϑ = 0`). -/
theorem exists_maximalRank_kernel_fintype {K : Type*} [Field K] {ι : Type*} [Fintype ι]
    [DecidableEq ι] (h2 : 2 ≤ Fintype.card ι) {ρ : ι → K} (hρ : ρ ≠ 0) :
    ∃ ϑ : Matrix ι (Fin (Fintype.card ι - 1)) K,
      LinearIndependent K (fun i : Fin (Fintype.card ι - 1) => fun j : ι => ϑ j i) ∧
      Matrix.vecMul ρ ϑ = 0 := by
  classical
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let ρ' : Fin (Fintype.card ι) → K := fun i => ρ (e.symm i)
  have hρ' : ρ' ≠ 0 := by
    intro h
    apply hρ
    funext j
    have := congrFun h (e j)
    simpa [ρ'] using this
  obtain ⟨ϑ', hLI, hvec⟩ :=
    exists_maximalRank_kernel (K := K) (ℓ := Fintype.card ι) h2 hρ'
  let ϑ : Matrix ι (Fin (Fintype.card ι - 1)) K := fun j k => ϑ' (e j) k
  refine ⟨ϑ, ?_, ?_⟩
  · have hw : LinearIndependent K (fun i k => ϑ' k i) := hLI
    let φ : (Fin (Fintype.card ι) → K) →ₗ[K] (ι → K) :=
      { toFun := fun v => v ∘ e
        map_add' := by intro a b; ext j; rfl
        map_smul' := by intro c a; ext j; rfl }
    have hφ : Function.Injective φ := by
      intro a b hab
      funext k
      have := congrFun hab (e.symm k)
      simpa [φ] using this
    have hres := hw.map' φ (LinearMap.ker_eq_bot_of_injective hφ)
    simpa [φ, ϑ, Function.comp_def] using hres
  · funext i
    have hsum : (∑ j : ι, ρ j * ϑ' (e j) i)
        = ∑ k : Fin (Fintype.card ι), ρ' k * ϑ' k i :=
      Fintype.sum_equiv e (fun j : ι => ρ j * ϑ' (e j) i)
        (fun k : Fin (Fintype.card ι) => ρ' k * ϑ' k i) (fun j => by simp [ρ'])
    calc (Matrix.vecMul ρ ϑ) i = ∑ j : ι, ρ j * ϑ' (e j) i := rfl
      _ = ∑ k : Fin (Fintype.card ι), ρ' k * ϑ' k i := hsum
      _ = (Matrix.vecMul ρ' ϑ') i := rfl
      _ = 0 := by rw [hvec]; rfl

end Commons.LinearAlgebra.Matrix