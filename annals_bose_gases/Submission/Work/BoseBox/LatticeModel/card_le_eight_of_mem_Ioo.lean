import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Data.Int.Interval
import Mathlib.Algebra.Order.Archimedean.Real.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBox.LatticeModel

theorem card_le_eight_of_mem_Ioo {N : ℕ} {A : Finset (Fin N)} {a L : ℝ} (hL : L ≤ 7)
    (hA : ∀ i ∈ A, a < ((i : ℕ) : ℝ) ∧ ((i : ℕ) : ℝ) < a + L) : A.card ≤ 8 := by
  -- The elements of `A`, viewed as integers, all lie in the block `{⌊a⌋+1, …, ⌊a⌋+7}`,
  -- which has 7 elements.
  set k : ℤ := ⌊a⌋ + 1 with hk
  have hmem : ∀ i ∈ A, ((i : ℕ) : ℤ) ∈ Finset.Icc k (k + 6) := by
    intro i hi
    obtain ⟨h1, h2⟩ := hA i hi
    rw [Finset.mem_Icc]
    constructor
    · -- lower bound: `⌊a⌋ < i`
      have hh : ⌊a⌋ < ((i : ℕ) : ℤ) := Int.floor_lt.mpr h1
      omega
    · -- upper bound: `i < a + L ≤ a + 7 < ⌊a⌋ + 8`
      have h5 : ((i : ℕ) : ℝ) < ((⌊a⌋ + 8 : ℤ) : ℝ) := by
        have h6 : a + L ≤ a + 7 := by linarith
        have h7 : a < ((⌊a⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one a
        push_cast
        linarith
      have h3 : ((i : ℕ) : ℤ) < ⌊a⌋ + 8 := by exact_mod_cast h5
      omega
  have hinj : Set.InjOn (fun i : Fin N => ((i : ℕ) : ℤ)) ↑A := by
    intro x _ y _ h
    exact Fin.ext (Int.ofNat_inj.mp h)
  have hIcc : (Finset.Icc k (k + 6) : Finset ℤ).card = 7 := by
    rw [Int.card_Icc]
    have : k + 6 + 1 - k = (7 : ℤ) := by ring
    rw [this]
    simp
  calc A.card ≤ (Finset.Icc k (k + 6) : Finset ℤ).card :=
        Finset.card_le_card_of_injOn _ hmem hinj
    _ ≤ 8 := by omega

end Work.BoseBox.LatticeModel
