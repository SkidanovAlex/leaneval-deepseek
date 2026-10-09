import Mathlib
import Submission.Commons.NumberTheory.Totient.totient_bound_K
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped NumberField

namespace Commons.NumberTheory.NumberField

/-- If `n.totient ≤ 2` then `n ≤ 6`.  The only `n` with `φ n ≤ 2` are
`1, 2, 3, 4, 6`; we use the elementary lower bound `15 n ≤ 4 * φ n * (n + 4)`. -/
private lemma le_six_of_totient_le_two {n : ℕ} (h : n.totient ≤ 2) : n ≤ 6 := by
  by_cases hn2 : n = 2
  · omega
  by_cases hn6 : n = 6
  · omega
  have hb := Commons.NumberTheory.Totient.totient_bound_K n hn2 hn6
  have h4 : 4 * n.totient ≤ 8 := by omega
  have h8 : (4 * n.totient) * (n + 4) ≤ 8 * (n + 4) := Nat.mul_le_mul_right _ h4
  have : 15 * n ≤ 8 * (n + 4) := le_trans hb h8
  omega

theorem torsionOrder_le_six_of_finrank_two (K : Type*) [Field K] [NumberField K]
    (h2 : Module.finrank ℚ K = 2) :
    NumberField.Units.torsionOrder K ≤ 6 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := NumberField.Units.torsion K)
  have hord : orderOf ((g : (𝓞 K)ˣ)) = NumberField.Units.torsionOrder K := by
    rw [Subgroup.orderOf_coe, hg, NumberField.Units.torsionOrder]
  have hu : IsPrimitiveRoot ((g : (𝓞 K)ˣ)) (NumberField.Units.torsionOrder K) := by
    rw [← hord]
    exact IsPrimitiveRoot.orderOf _
  have hμ : IsPrimitiveRoot (((g : (𝓞 K)ˣ) : 𝓞 K)) (NumberField.Units.torsionOrder K) :=
    IsPrimitiveRoot.coe_units_iff.mpr hu
  have htot : Nat.totient (NumberField.Units.torsionOrder K) ≤
      (minpoly ℤ (((g : (𝓞 K)ˣ) : 𝓞 K))).natDegree :=
    IsPrimitiveRoot.totient_le_degree_minpoly hμ
  have hle1 : (minpoly ℤ (((g : (𝓞 K)ˣ) : 𝓞 K))).natDegree ≤ Module.finrank ℤ (𝓞 K) :=
    minpoly.natDegree_le _
  have hrank : Module.finrank ℤ (𝓞 K) = 2 := by
    rw [NumberField.RingOfIntegers.rank, h2]
  have hphi : Nat.totient (NumberField.Units.torsionOrder K) ≤ 2 :=
    calc Nat.totient (NumberField.Units.torsionOrder K)
        ≤ (minpoly ℤ (((g : (𝓞 K)ˣ) : 𝓞 K))).natDegree := htot
      _ ≤ Module.finrank ℤ (𝓞 K) := hle1
      _ = 2 := hrank
  exact le_six_of_totient_le_two hphi

end Commons.NumberTheory.NumberField
