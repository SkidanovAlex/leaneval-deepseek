import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PSU3.StageB

/-- Helper: `(X + C c)^m - X^m` has degree `< m`.

The point is that the degree-`m` terms cancel; the difference is
`(X + C c - X) * ∑ i < m, (X + C c)^i * X^(m-1-i) = C c * G`, and
`G` has degree `≤ m - 1`. -/
theorem natDegree_X_add_C_pow_sub_X_pow_lt {R : Type*} [CommRing R]
    (c : R) {m : ℕ} (hm : 1 ≤ m) :
    ((Polynomial.X + Polynomial.C c : Polynomial R) ^ m
      - Polynomial.X ^ m).natDegree < m := by
  set f : Polynomial R := Polynomial.X + Polynomial.C c with hf
  set G : Polynomial R :=
    ∑ i ∈ Finset.range m, f ^ i * Polynomial.X ^ (m - 1 - i) with hG
  have hsub : f - Polynomial.X = Polynomial.C c := by
    rw [hf, add_sub_cancel_left]
  have hcomm : (f - Polynomial.X) * G = f ^ m - Polynomial.X ^ m := by
    rw [hG]
    exact (Commute.all f Polynomial.X).mul_geom_sum₂ m
  have hCc : Polynomial.C c * G = f ^ m - Polynomial.X ^ m := by
    rw [← hsub]; exact hcomm
  have hfdeg : f.natDegree ≤ 1 := by
    rw [hf, Polynomial.natDegree_add_C]
    exact Polynomial.natDegree_X_le
  have hGdeg : G.natDegree ≤ m - 1 := by
    rw [hG]
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro i hi
    rw [Finset.mem_range] at hi
    have hi_le : i ≤ m - 1 := Nat.le_sub_one_of_lt hi
    calc (f ^ i * Polynomial.X ^ (m - 1 - i)).natDegree
        ≤ (f ^ i).natDegree + (Polynomial.X ^ (m - 1 - i)).natDegree :=
          Polynomial.natDegree_mul_le
      _ ≤ i * f.natDegree + (m - 1 - i) * Polynomial.X.natDegree :=
          add_le_add Polynomial.natDegree_pow_le Polynomial.natDegree_pow_le
      _ ≤ i * 1 + (m - 1 - i) * 1 :=
          add_le_add (Nat.mul_le_mul_left i hfdeg)
            (Nat.mul_le_mul_left (m - 1 - i) Polynomial.natDegree_X_le)
      _ = m - 1 := by rw [mul_one, mul_one, Nat.add_sub_cancel' hi_le]
  rw [← hCc]
  calc (Polynomial.C c * G).natDegree
      ≤ G.natDegree := Polynomial.natDegree_C_mul_le c G
    _ ≤ m - 1 := hGdeg
    _ < m := Nat.sub_one_lt (by omega)

theorem natDegree_X_add_C_pow_sub_X_pow_sub_C_lt {R : Type*} [CommRing R]
    (c α : R) {m : ℕ} (hm : 1 ≤ m) :
    ((Polynomial.X + Polynomial.C c : Polynomial R) ^ m - Polynomial.X ^ m
      - Polynomial.C α).natDegree < m := by
  rw [Polynomial.natDegree_sub_C]
  exact natDegree_X_add_C_pow_sub_X_pow_lt c hm

end Work.PSU3.StageB
