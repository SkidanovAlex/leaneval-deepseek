import Mathlib.Analysis.InnerProductSpace.PiL2

namespace Commons.Analysis.InnerProductSpace

open scoped Real Topology InnerProductSpace

noncomputable section

/-- Evaluation at the unique element `0 : Fin 1` is a linear isometric equivalence
`EuclideanSpace ℝ (Fin 1) ≃ₗᵢ[ℝ] ℝ`. -/
def finOneIso : EuclideanSpace ℝ (Fin 1) ≃ₗᵢ[ℝ] ℝ where
  toLinearEquiv :=
    (WithLp.linearEquiv 2 ℝ (Fin 1 → ℝ)).trans (LinearEquiv.funUnique (Fin 1) ℝ ℝ)
  norm_map' := by
    intro x
    have hnn : ‖x‖₊ = ‖x (0 : Fin 1)‖₊ := by
      rw [PiLp.nnnorm_eq_of_L2]
      rw [Finset.sum_eq_single (0 : Fin 1)]
      · simp
      · intro b _ hb
        exact absurd (Subsingleton.elim b 0) hb
      · intro h
        exact absurd (Finset.mem_univ _) h
    have hnorm : ‖x (0 : Fin 1)‖ = ‖x‖ := by
      calc ‖x (0 : Fin 1)‖ = ↑‖x (0 : Fin 1)‖₊ := (coe_nnnorm _).symm
        _ = ↑‖x‖₊ := by rw [← hnn]
        _ = ‖x‖ := coe_nnnorm _
    change ‖(LinearEquiv.funUnique (Fin 1) ℝ ℝ)
      ((WithLp.linearEquiv 2 ℝ (Fin 1 → ℝ)) x)‖ = ‖x‖
    rw [LinearEquiv.funUnique_apply]
    simp only [WithLp.coe_linearEquiv]
    rw [Fin.default_eq_zero]
    exact hnorm

/-- `EuclideanSpace ℝ (Fin (n+1))` splits as the `L²`-product `EuclideanSpace ℝ (Fin n) × ℝ`
(splitting off the last coordinate).  Equivalently: `(Fin (n+1) → ℝ)` with the Euclidean norm is
isometric to `ℝ × (Fin n → ℝ)` with the `L²`-product norm.

Suggested construction: `EuclideanSpace ℝ (Fin (n+1)) = WithLp 2 (Fin (n+1) → ℝ)`; reindex
`Fin (n+1) ≃ Fin 1 ⊕ Fin n` (`Fin.sumEquivSucc` or similar), use
`PiLp.sumPiLpEquivProdLpPiLp 2 (fun _ ↦ ℝ)` to split the product into
`WithLp 2 (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin n))`, and transport along
`EuclideanSpace ℝ (Fin 1) ≃ₗᵢ[ℝ] ℝ` plus the swap isometry
(`LinearIsometryEquiv.withLpProdCongr`, `LinearIsometryEquiv.prodComm`). -/
theorem euclidean_split_isometry (n : ℕ) :
    Nonempty (EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ]
      WithLp 2 (EuclideanSpace ℝ (Fin n) × ℝ)) := by
  refine ⟨?_⟩
  let e : Fin (n + 1) ≃ Fin n ⊕ Fin 1 := (finSumFinEquiv (m := n) (n := 1)).symm
  let reindex : EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n ⊕ Fin 1) :=
    LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e
  let split : EuclideanSpace ℝ (Fin n ⊕ Fin 1) ≃ₗᵢ[ℝ]
      WithLp 2 (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin 1)) :=
    PiLp.sumPiLpEquivProdLpPiLp 2 (fun _ : Fin n ⊕ Fin 1 => ℝ)
  let congr : WithLp 2 (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin 1)) ≃ₗᵢ[ℝ]
      WithLp 2 (EuclideanSpace ℝ (Fin n) × ℝ) :=
    LinearIsometryEquiv.withLpProdCongr 2
      (LinearIsometryEquiv.refl ℝ (EuclideanSpace ℝ (Fin n))) finOneIso
  exact (reindex.trans split).trans congr

end

end Commons.Analysis.InnerProductSpace