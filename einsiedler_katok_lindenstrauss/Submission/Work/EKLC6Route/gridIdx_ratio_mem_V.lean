import Mathlib
import Submission.Work.EKLC6Route.Defs
import Submission.Work.EKLC6Core.abs_sub_lt_of_floor_div_eq
import Submission.Work.EKLC6Core.mul_inv_mem_V_of_entrywise_close

namespace Work.EKLC6Route

/-- Two group elements of `V ρ` (`ρ ≤ 1`) with the same grid index at level `L` differ entrywise
by less than `ρ / 2 ^ L`. -/
theorem gridIdx_entry_close {ρ : ℝ} (hρ : 0 < ρ) {L : ℕ} {k k' : Work.EKLContract.SL3}
    (hgrid : Work.EKLC6Route.gridIdx ρ L k = Work.EKLC6Route.gridIdx ρ L k') :
    ∀ i j : Fin 3,
      |(k' : Matrix (Fin 3) (Fin 3) ℝ) i j - (k : Matrix (Fin 3) (Fin 3) ℝ) i j| < ρ / 2 ^ L := by
  have h2L : (0 : ℝ) < 2 ^ L := by positivity
  have hη : (0 : ℝ) < ρ / 2 ^ L := div_pos hρ h2L
  -- `X * 2^L / ρ = X / (ρ / 2^L)`, so the grid index is a floor of `(k - 1)_{ij} / η`.
  have hdiv : ∀ X : ℝ, X / (ρ / 2 ^ L) = X * 2 ^ L / ρ := by
    intro X
    rw [div_eq_mul_inv, inv_div]
    ring
  have hfloor : ∀ i j : Fin 3,
      ⌊((k : Matrix (Fin 3) (Fin 3) ℝ) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j) / (ρ / 2 ^ L)⌋
        = ⌊((k' : Matrix (Fin 3) (Fin 3) ℝ) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j)
            / (ρ / 2 ^ L)⌋ := by
    intro i j
    rw [hdiv, hdiv]
    exact congrFun (congrFun hgrid i) j
  intro i j
  have h := Work.EKLC6Core.abs_sub_lt_of_floor_div_eq hη (hfloor i j)
  rw [show ((k : Matrix (Fin 3) (Fin 3) ℝ) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j)
      - ((k' : Matrix (Fin 3) (Fin 3) ℝ) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j)
      = ((k : Matrix (Fin 3) (Fin 3) ℝ) i j - (k' : Matrix (Fin 3) (Fin 3) ℝ) i j)
      from by ring] at h
  rwa [abs_sub_comm] at h

theorem gridIdx_ratio_mem_V {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) {L : ℕ} {k k' : Work.EKLContract.SL3}
    (hk : k ∈ Work.EKLContract.V ρ) (hk' : k' ∈ Work.EKLContract.V ρ)
    (hgrid : Work.EKLC6Route.gridIdx ρ L k = Work.EKLC6Route.gridIdx ρ L k') :
    k' * k⁻¹ ∈ Work.EKLContract.V (100 * (1 / 2 : ℝ) ^ L * ρ) := by
  have h2L : (0 : ℝ) < 2 ^ L := by positivity
  have hη : (0 : ℝ) < ρ / 2 ^ L := div_pos hρ h2L
  -- `k` lies in the closed box `{|· - 1| ≤ 1}` around the identity because `k ∈ V ρ` and `ρ ≤ 1`.
  have hbox : ∀ i j : Fin 3,
      |(k : Matrix (Fin 3) (Fin 3) ℝ) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ 1 := by
    intro i j
    linarith [hk i j, hρ1]
  -- the grid index pins `k'` down entrywise to within `ρ / 2 ^ L` of `k`
  have hcl := gridIdx_entry_close hρ hgrid
  have hmain : k' * k⁻¹ ∈ Work.EKLContract.V (24 * (ρ / 2 ^ L)) :=
    Work.EKLC6Core.mul_inv_mem_V_of_entrywise_close (η := ρ / 2 ^ L) k' k hbox hη hcl
  intro i j
  refine lt_of_lt_of_le (hmain i j) ?_
  have hhalf : (1 / 2 : ℝ) ^ L = 1 / 2 ^ L := by rw [div_pow, one_pow]
  have ht : (0 : ℝ) < ρ * (2 ^ L)⁻¹ := by positivity
  have h24 : (24 : ℝ) * (ρ * (2 ^ L)⁻¹) ≤ 100 * (ρ * (2 ^ L)⁻¹) :=
    mul_le_mul_of_nonneg_right (by norm_num : (24 : ℝ) ≤ 100) (le_of_lt ht)
  calc 24 * (ρ / 2 ^ L) = 24 * (ρ * (2 ^ L)⁻¹) := by rw [div_eq_mul_inv]
    _ ≤ 100 * (ρ * (2 ^ L)⁻¹) := h24
    _ = 100 * (1 / 2 : ℝ) ^ L * ρ := by rw [hhalf, div_eq_mul_inv, one_mul]; ring

end Work.EKLC6Route
