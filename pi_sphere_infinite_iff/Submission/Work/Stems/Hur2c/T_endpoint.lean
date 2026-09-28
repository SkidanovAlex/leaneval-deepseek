import Submission.Work.Stems.Hur2c.T_mul
import Submission.Work.Stems.Hur2c.T_loop

/-!
# The endpoint formula for `T`

`Work.Stems.Hur2c.T_endpoint : T x₀ 0 δ = φ (δ 1) - φ (δ 0)` where `φ v := T x₀ 0 (cubeOfPath (K₀ x₀ v))`.

The loop `ℓ := (K₀ x₀ (δ 0)) · δ · (K₀ x₀ (δ 1))⁻¹` at `x₀` has `T x₀ 0 ℓ = 0` by `T_loop`; `T_mul`
splits it into `T x₀ 0 (K₀ (δ 0)) + T x₀ 0 δ + T x₀ 0 ((K₀ (δ 1))⁻¹)`, and for a reversed path
`T x₀ 0 κ⁻¹ = -T x₀ 0 κ` (apply `T_mul` to the loop `κ · κ⁻¹` and use `T_loop`).  Hence
`T x₀ 0 δ = φ (δ 1) - φ (δ 0)`.  — the sign here is the one that makes `T_mul` consistent (with
`T x₀ 1 = -T x₀ 0`).
-/

open scoped unitInterval Topology

namespace Work.Stems.Hur2c

open Work.Stems.Cubical
open Work.Stems.Hur2

noncomputable section

variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]

/-- `cubeOfPath (edgePath δ) = δ`. -/
theorem cubeOfPath_edgePath (δ : C(IC 1, X)) : cubeOfPath (Hur2.edgePath δ) = δ := by
  ext t
  show δ (Hur2.iota (t 0)) = δ t
  congr 1
  exact Hur2.iota_eq t

/-- **The reverse of a path**: `T x₀ 0 κ⁻¹ = -T x₀ 0 κ`. -/
theorem T_symm (x₀ : X) {p q : X} (κ : Path p q) :
    T x₀ 0 (cubeOfPath κ.symm) = - T x₀ 0 (cubeOfPath κ) := by
  letI : CommGroup (HomotopyGroup (Fin 2) X x₀) := HomotopyGroup.commGroup
  have hloop : T x₀ 0 (cubeOfPath (κ.trans κ.symm)) = 0 :=
    T_loop x₀ 0 (cubeOfPath (κ.trans κ.symm)) (by
      show (cubeOfPath (κ.trans κ.symm)) 0 = (cubeOfPath (κ.trans κ.symm)) 1
      simp [cubeOfPath])
  rw [T_mul x₀ 0 κ κ.symm] at hloop
  have h' : T x₀ 0 (cubeOfPath κ.symm) + T x₀ 0 (cubeOfPath κ) = 0 := by
    rw [add_comm]; exact hloop
  exact eq_neg_of_add_eq_zero_left h'

/-- **The endpoint formula**: `T x₀ 0 δ = φ (δ 1) - φ (δ 0)`,
`φ v := T x₀ 0 (cubeOfPath (K₀ x₀ v))`. -/
theorem T_endpoint (x₀ : X) (δ : C(IC 1, X)) :
    T x₀ 0 δ = T x₀ 0 (cubeOfPath (Hur2.K₀ x₀ (δ 1)))
      - T x₀ 0 (cubeOfPath (Hur2.K₀ x₀ (δ 0))) := by
  letI : CommGroup (HomotopyGroup (Fin 2) X x₀) := HomotopyGroup.commGroup
  -- the loop `K₀ (δ 0) · δ · (K₀ (δ 1))⁻¹`
  have hloop : T x₀ 0 (cubeOfPath (((Hur2.K₀ x₀ (δ 0)).trans (Hur2.edgePath δ)).trans
      ((Hur2.K₀ x₀ (δ 1)).symm))) = 0 :=
    T_loop x₀ 0 _ (by
      show (cubeOfPath _) 0 = (cubeOfPath _) 1
      simp [cubeOfPath])
  -- split it
  have h1 : T x₀ 0 (cubeOfPath (Hur2.K₀ x₀ (δ 0))) + T x₀ 0 δ
      = T x₀ 0 (cubeOfPath (Hur2.K₀ x₀ (δ 1))) := by
    have h := hloop
    rw [T_mul x₀ 0 ((Hur2.K₀ x₀ (δ 0)).trans (Hur2.edgePath δ))
      ((Hur2.K₀ x₀ (δ 1)).symm)] at h
    rw [T_mul x₀ 0 (Hur2.K₀ x₀ (δ 0)) (Hur2.edgePath δ), cubeOfPath_edgePath] at h
    rw [T_symm x₀ (Hur2.K₀ x₀ (δ 1))] at h
    have h' := add_eq_zero_iff_eq_neg.mp h
    rw [neg_neg] at h'
    exact h'
  rw [← h1]
  abel

end

end Work.Stems.Hur2c
