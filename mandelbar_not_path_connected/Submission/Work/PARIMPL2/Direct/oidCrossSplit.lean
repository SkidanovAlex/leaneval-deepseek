import Mathlib
import Submission.Work.PARIMPL2.Direct.oidAux

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.PARIMPL2.Direct

theorem oidCrossSplit (A C : ℕ → ℝ) (n j0 : ℕ) (hj0 : j0 < n)
    (hC : ∀ i, 1 + C i ≠ 0) :
    (∑ j ∈ Finset.range n, A j * ∏ i ∈ Finset.Ico (j + 1) n, (1 + C i))
      = (∏ i ∈ Finset.Ico (j0 + 1) n, (1 + C i))
        * ((∑ j ∈ Finset.range n, A j)
          + ∑ j ∈ Finset.range j0, A j * (∏ i ∈ Finset.Ico (j + 1) (j0 + 1), (1 + C i) - 1)
          + ∑ j ∈ Finset.Ico j0 n, A j * ((∏ i ∈ Finset.Ico (j0 + 1) (j + 1), (1 + C i))⁻¹ - 1)) := by
  have hj0le : j0 ≤ n := le_of_lt hj0
  set Pf := ∏ i ∈ Finset.Ico (j0 + 1) n, (1 + C i) with hPf
  -- key product identities
  have hfacL : ∀ j ∈ Finset.range j0,
      Pf * (∏ i ∈ Finset.Ico (j + 1) (j0 + 1), (1 + C i))
        = ∏ i ∈ Finset.Ico (j + 1) n, (1 + C i) := by
    intro j hj
    rw [hPf]
    have h1 : j + 1 ≤ j0 + 1 := by have := Finset.mem_range.mp hj; omega
    have h2 : j0 + 1 ≤ n := by omega
    have h := Finset.prod_Ico_consecutive (fun i => (1 : ℝ) + C i) h1 h2
    calc (∏ i ∈ Finset.Ico (j0 + 1) n, (1 + C i)) * (∏ i ∈ Finset.Ico (j + 1) (j0 + 1), (1 + C i))
        = (∏ i ∈ Finset.Ico (j + 1) (j0 + 1), (1 + C i)) * (∏ i ∈ Finset.Ico (j0 + 1) n, (1 + C i)) := by
          ring
      _ = ∏ i ∈ Finset.Ico (j + 1) n, (1 + C i) := h
  have hfacR : ∀ j ∈ Finset.Ico j0 n,
      Pf * (∏ i ∈ Finset.Ico (j0 + 1) (j + 1), (1 + C i))⁻¹
        = ∏ i ∈ Finset.Ico (j + 1) n, (1 + C i) := by
    intro j hj
    rw [hPf]
    obtain ⟨hj1, hj2⟩ := Finset.mem_Ico.mp hj
    have h1 : j0 + 1 ≤ j + 1 := by omega
    have h2 : j + 1 ≤ n := by omega
    have h := Finset.prod_Ico_consecutive (fun i => (1 : ℝ) + C i) h1 h2
    have hne : (∏ i ∈ Finset.Ico (j0 + 1) (j + 1), (1 + C i)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun i _ => hC i)
    rw [← h, mul_assoc, mul_comm (∏ i ∈ Finset.Ico (j + 1) n, (1 + C i))
      (∏ i ∈ Finset.Ico (j0 + 1) (j + 1), (1 + C i))⁻¹, ← mul_assoc,
      mul_inv_cancel₀ hne, one_mul]
  -- distribute the prefactor
  have hdist : Pf * ((∑ j ∈ Finset.range n, A j)
        + ∑ j ∈ Finset.range j0, A j * (∏ i ∈ Finset.Ico (j + 1) (j0 + 1), (1 + C i) - 1)
        + ∑ j ∈ Finset.Ico j0 n, A j * ((∏ i ∈ Finset.Ico (j0 + 1) (j + 1), (1 + C i))⁻¹ - 1))
      = Pf * (∑ j ∈ Finset.range n, A j)
        + Pf * (∑ j ∈ Finset.range j0, A j * (∏ i ∈ Finset.Ico (j + 1) (j0 + 1), (1 + C i) - 1))
        + Pf * (∑ j ∈ Finset.Ico j0 n,
            A j * ((∏ i ∈ Finset.Ico (j0 + 1) (j + 1), (1 + C i))⁻¹ - 1)) := by
    rw [mul_add, mul_add]
  -- push the prefactor into each sum
  have hX : Pf * (∑ j ∈ Finset.range n, A j)
      = (∑ j ∈ Finset.range j0, Pf * A j) + ∑ j ∈ Finset.Ico j0 n, Pf * A j := by
    rw [Finset.mul_sum]
    simp only [Finset.range_eq_Ico]
    exact (Finset.sum_Ico_consecutive (fun j => Pf * A j) (Nat.zero_le j0) hj0le).symm
  have hY : Pf * (∑ j ∈ Finset.range j0, A j * (∏ i ∈ Finset.Ico (j + 1) (j0 + 1), (1 + C i) - 1))
      = ∑ j ∈ Finset.range j0, Pf * (A j * (∏ i ∈ Finset.Ico (j + 1) (j0 + 1), (1 + C i) - 1)) := by
    rw [Finset.mul_sum]
  have hZ : Pf * (∑ j ∈ Finset.Ico j0 n,
        A j * ((∏ i ∈ Finset.Ico (j0 + 1) (j + 1), (1 + C i))⁻¹ - 1))
      = ∑ j ∈ Finset.Ico j0 n,
          Pf * (A j * ((∏ i ∈ Finset.Ico (j0 + 1) (j + 1), (1 + C i))⁻¹ - 1)) := by
    rw [Finset.mul_sum]
  -- recombine region by region
  have hL : (∑ j ∈ Finset.range j0, Pf * A j)
        + (∑ j ∈ Finset.range j0, Pf * (A j * (∏ i ∈ Finset.Ico (j + 1) (j0 + 1), (1 + C i) - 1)))
      = ∑ j ∈ Finset.range j0, A j * ∏ i ∈ Finset.Ico (j + 1) n, (1 + C i) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    rw [← hfacL j hj]
    ring
  have hR : (∑ j ∈ Finset.Ico j0 n, Pf * A j)
        + (∑ j ∈ Finset.Ico j0 n,
            Pf * (A j * ((∏ i ∈ Finset.Ico (j0 + 1) (j + 1), (1 + C i))⁻¹ - 1)))
      = ∑ j ∈ Finset.Ico j0 n, A j * ∏ i ∈ Finset.Ico (j + 1) n, (1 + C i) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    rw [← hfacR j hj]
    ring
  have hcomb : (∑ j ∈ Finset.range j0, A j * ∏ i ∈ Finset.Ico (j + 1) n, (1 + C i))
        + (∑ j ∈ Finset.Ico j0 n, A j * ∏ i ∈ Finset.Ico (j + 1) n, (1 + C i))
      = ∑ j ∈ Finset.range n, A j * ∏ i ∈ Finset.Ico (j + 1) n, (1 + C i) := by
    simp only [Finset.range_eq_Ico]
    exact Finset.sum_Ico_consecutive (fun j => A j * ∏ i ∈ Finset.Ico (j + 1) n, (1 + C i))
      (Nat.zero_le j0) hj0le
  rw [hdist, hX, hY, hZ]
  have hrearr : (∑ j ∈ Finset.range j0, Pf * A j) + (∑ j ∈ Finset.Ico j0 n, Pf * A j)
        + (∑ j ∈ Finset.range j0, Pf * (A j * (∏ i ∈ Finset.Ico (j + 1) (j0 + 1), (1 + C i) - 1)))
        + (∑ j ∈ Finset.Ico j0 n,
            Pf * (A j * ((∏ i ∈ Finset.Ico (j0 + 1) (j + 1), (1 + C i))⁻¹ - 1)))
      = ((∑ j ∈ Finset.range j0, Pf * A j)
          + (∑ j ∈ Finset.range j0, Pf * (A j * (∏ i ∈ Finset.Ico (j + 1) (j0 + 1), (1 + C i) - 1))))
        + ((∑ j ∈ Finset.Ico j0 n, Pf * A j)
          + (∑ j ∈ Finset.Ico j0 n,
              Pf * (A j * ((∏ i ∈ Finset.Ico (j0 + 1) (j + 1), (1 + C i))⁻¹ - 1)))) := by
    ring
  rw [hrearr, hL, hR]
  exact hcomb.symm

end Work.PARIMPL2.Direct
