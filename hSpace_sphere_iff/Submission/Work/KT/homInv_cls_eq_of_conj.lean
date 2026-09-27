import Mathlib
import Submission.Work.KT.Defs

namespace Work.KT

/-- **Conjugate idempotents have the same `K₀`-class.**  If `p`, `q` are idempotent `n × n`
matrices over a ring `R` and there is a unit `u` with `u * q = p * u` (equivalently
`q = u⁻¹ * p * u`), then `p` and `q` are Murray–von Neumann equivalent, hence `[p] = [q]`
in `K₀ R`.

The Murray–von Neumann witnesses are `a = u⁻¹ * p`, `b = p * u`: then
`b * a = p * u * u⁻¹ * p = p * p = p` and `a * b = u⁻¹ * p * p * u = u⁻¹ * p * u = q`. -/
theorem homInv_cls_eq_of_conj {R : Type} [Ring R] {n : ℕ} (p q : Matrix (Fin n) (Fin n) R)
    (hp : p * p = p) (hq : q * q = q) (u : (Matrix (Fin n) (Fin n) R)ˣ)
    (hu : (u : Matrix (Fin n) (Fin n) R) * q = p * (u : Matrix (Fin n) (Fin n) R)) :
    cls (⟨n, p⟩ : Mat R) = cls ⟨n, q⟩ := by
  -- `q = u⁻¹ * p * u`, obtained from `u * q = p * u` by multiplying on the left by `u⁻¹`.
  have hq_eq : q = (↑(u⁻¹) : Matrix (Fin n) (Fin n) R) * p * (u : Matrix (Fin n) (Fin n) R) := by
    calc q = (↑u⁻¹ : Matrix (Fin n) (Fin n) R) * ((u : Matrix (Fin n) (Fin n) R) * q) := by
          rw [← Matrix.mul_assoc, Units.inv_mul, one_mul]
      _ = (↑u⁻¹ : Matrix (Fin n) (Fin n) R) * (p * (u : Matrix (Fin n) (Fin n) R)) := by rw [hu]
      _ = (↑u⁻¹ : Matrix (Fin n) (Fin n) R) * p * (u : Matrix (Fin n) (Fin n) R) := by
          rw [Matrix.mul_assoc]
  -- The two Murray–von Neumann equations for the witnesses `a = u⁻¹ * p`, `b = p * u`.
  have hba : (p * (u : Matrix (Fin n) (Fin n) R)) *
      ((↑(u⁻¹) : Matrix (Fin n) (Fin n) R) * p) = p := by
    rw [Matrix.mul_assoc p (u : Matrix (Fin n) (Fin n) R)
        ((↑u⁻¹ : Matrix (Fin n) (Fin n) R) * p),
      ← Matrix.mul_assoc (u : Matrix (Fin n) (Fin n) R) (↑u⁻¹ : Matrix (Fin n) (Fin n) R) p,
      Units.mul_inv, one_mul, hp]
  have hab : ((↑(u⁻¹) : Matrix (Fin n) (Fin n) R) * p) *
      (p * (u : Matrix (Fin n) (Fin n) R)) = q := by
    rw [hq_eq]
    rw [Matrix.mul_assoc (↑u⁻¹ : Matrix (Fin n) (Fin n) R) p (p * (u : Matrix (Fin n) (Fin n) R)),
      ← Matrix.mul_assoc p p (u : Matrix (Fin n) (Fin n) R), hp,
      ← Matrix.mul_assoc (↑u⁻¹ : Matrix (Fin n) (Fin n) R) p (u : Matrix (Fin n) (Fin n) R)]
  have hMvN : Mat.MvN (⟨n, p⟩ : Mat R) ⟨n, q⟩ :=
    ⟨(↑(u⁻¹) : Matrix (Fin n) (Fin n) R) * p, p * (u : Matrix (Fin n) (Fin n) R), hba, hab⟩
  -- `[p] - [q] ∈ K0Rel`, hence the classes agree.
  have hmem : FreeAbelianGroup.of (⟨n, p⟩ : Mat R) - FreeAbelianGroup.of (⟨n, q⟩ : Mat R) ∈
      K0Rel R :=
    AddSubgroup.subset_closure (Or.inl (Or.inr ⟨⟨n, p⟩, ⟨n, q⟩, hp, hq, hMvN, rfl⟩))
  unfold cls
  rw [QuotientAddGroup.eq_iff_sub_mem]
  simpa using hmem

end Work.KT
