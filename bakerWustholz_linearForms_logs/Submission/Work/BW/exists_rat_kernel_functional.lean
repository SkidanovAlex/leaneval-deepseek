import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- If an integral vector `u` is not a rational combination of the rows of `M : Fin ρ → Fin N → ℤ`,
then there is a rational vector `ξ` killed by `M` whose pairing with `u` is nonzero.
(Suggested route: let `Mᵀ : ℚ^ρ →ₗ ℚ^N` be the row map, `L` the functional `ξ ↦ ⟨u, ξ⟩`; if `L`
vanished on `ker Mᵀ` then `L ∈ (ker Mᵀ).dualAnnihilator = Mᵀ.dualMap.range`
(`LinearMap.range_dualMap_eq_dualAnnihilator_ker`), so `L = φ ∘ Mᵀ` for some `φ`, and evaluating at
the basis vectors `Pi.single m 1` writes `u` as a rational combination of the rows, contradicting
`hu`; use `LinearMap.pi_apply_eq_sum_univ`.) -/
theorem exists_rat_kernel_functional {N ρ : ℕ} (M : Fin ρ → Fin N → ℤ) (u : Fin N → ℤ)
    (hu : ¬ ∃ c : Fin ρ → ℚ, ∀ m, (u m : ℚ) = ∑ r, c r * (M r m : ℚ)) :
    ∃ ξ : Fin N → ℚ, (∀ j, ∑ m, (M j m : ℚ) * ξ m = 0) ∧ (∑ m, (u m : ℚ) * ξ m) ≠ 0 := by
  classical
  -- The transpose of `M` as a linear map `ℚ^N →ₗ ℚ^ρ`; its `r`-th component is row `r` of `M`.
  let MT : (Fin N → ℚ) →ₗ[ℚ] (Fin ρ → ℚ) := (Matrix.of (fun r m => (M r m : ℚ))).toLin'
  -- The functional `ξ ↦ ⟨u, ξ⟩`.
  let L : (Fin N → ℚ) →ₗ[ℚ] ℚ :=
    { toFun := fun ξ => ∑ m, (u m : ℚ) * ξ m
      map_add' := by intro a b; simp [mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro a b
        simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, RingHom.id_apply]
        apply Finset.sum_congr rfl; intro m _; ring }
  have hMT : ∀ (ξ : Fin N → ℚ) (j : Fin ρ), MT ξ j = ∑ m, (M j m : ℚ) * ξ m := by
    intro ξ j
    simp only [MT, Matrix.toLin'_apply, Matrix.mulVec, Matrix.of_apply, dotProduct]
  -- Suppose no such `ξ` exists.
  by_contra hcon
  -- Then `L` annihilates the kernel of `MT`.
  have hL : L ∈ MT.ker.dualAnnihilator := by
    rw [Submodule.mem_dualAnnihilator]
    intro ξ hξ
    have hξ0 : MT ξ = 0 := LinearMap.mem_ker.mp hξ
    have hξ' : ∀ j, ∑ m, (M j m : ℚ) * ξ m = 0 := by
      intro j
      have := congrFun hξ0 j
      rwa [hMT] at this
    show (∑ m, (u m : ℚ) * ξ m) = 0
    by_contra hne
    exact hcon ⟨ξ, hξ', hne⟩
  -- So `L` factors through `MT`: `L = φ ∘ MT`.
  rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker] at hL
  obtain ⟨φ, hφ⟩ := hL
  have hφ' : ∀ ξ : Fin N → ℚ, φ (MT ξ) = L ξ := by
    intro ξ
    have h := congrFun (congrArg DFunLike.coe hφ) ξ
    rwa [LinearMap.dualMap_apply] at h
  -- Evaluating at the basis vectors writes `u` as a rational combination of the rows of `M`.
  refine absurd ?_ hu
  refine ⟨fun r => φ (fun k => if r = k then (1:ℚ) else 0), fun m => ?_⟩
  have h1 : (u m : ℚ) = L (fun k => if m = k then (1:ℚ) else 0) := by
    simp only [L]
    simp
  rw [h1, ← hφ']
  have h2 : MT (fun k => if m = k then (1:ℚ) else 0) = fun j => (M j m : ℚ) := by
    funext j
    rw [hMT]
    simp
  rw [h2]
  rw [LinearMap.pi_apply_eq_sum_univ]
  simp only [smul_eq_mul]
  apply Finset.sum_congr rfl
  intro r _
  rw [mul_comm]

end Work.BW
