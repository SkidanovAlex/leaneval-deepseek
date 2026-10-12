import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Star
import Mathlib.Order.Lattice.Nat
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Algebra.Order.Ring.Cast
import Mathlib.Algebra.Order.Ring.Star
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

open Finset

noncomputable section

/-- The sup-norm of a lattice vector `m : Fin 3 → ℤ`, as a natural number. -/
def K (m : Fin 3 → ℤ) : ℕ := Finset.univ.sup fun i => (m i).natAbs

/-- The integer box `[-k,k]³` of multi-indices. -/
def box (k : ℕ) : Finset (Fin 3 → ℤ) :=
  Fintype.piFinset fun _ : Fin 3 => Finset.Icc (-(k : ℤ)) (k : ℤ)

/-- The `k`-th shell: the multi-indices whose sup-norm is exactly `k`. -/
def shell (k : ℕ) : Finset (Fin 3 → ℤ) := box k \ box (k - 1)

lemma natAbs_le_iff (z : ℤ) (k : ℕ) : z.natAbs ≤ k ↔ -(k : ℤ) ≤ z ∧ z ≤ k := by
  constructor
  · intro h
    refine ⟨?_, le_trans Int.le_natAbs (by exact_mod_cast h)⟩
    have h1 : -z ≤ (z.natAbs : ℤ) := by
      simpa using Int.le_natAbs (a := -z)
    have h2 : ((z.natAbs : ℕ) : ℤ) ≤ (k : ℤ) := by exact_mod_cast h
    linarith
  · intro ⟨h1, h2⟩
    have h3 : |z| ≤ (k : ℤ) := abs_le.mpr ⟨h1, h2⟩
    rw [Int.abs_eq_natAbs] at h3
    exact_mod_cast h3

lemma mem_box_iff (k : ℕ) (m : Fin 3 → ℤ) :
    m ∈ box k ↔ ∀ i, (m i).natAbs ≤ k := by
  rw [box, Fintype.mem_piFinset]
  exact forall_congr' fun i => by rw [Finset.mem_Icc, natAbs_le_iff]

lemma box_mono {k l : ℕ} (h : k ≤ l) : box k ⊆ box l := by
  intro m hm
  rw [mem_box_iff] at hm ⊢
  exact fun i => le_trans (hm i) h

lemma K_spec (m : Fin 3 → ℤ) (i : Fin 3) : (m i).natAbs ≤ K m :=
  Finset.le_sup (s := Finset.univ) (f := fun j : Fin 3 => (m j).natAbs) (Finset.mem_univ i)

lemma mem_box_of_K_eq (m : Fin 3 → ℤ) (k : ℕ) (h : K m = k) : m ∈ box k := by
  rw [mem_box_iff]
  intro i
  rw [← h]
  exact K_spec m i

lemma K_le_of_mem_box (m : Fin 3 → ℤ) (k : ℕ) (h : m ∈ box k) : K m ≤ k := by
  rw [K, Finset.sup_le_iff]
  intro i _
  exact (mem_box_iff k m).mp h i

lemma not_mem_box_pred_of_K_eq {m : Fin 3 → ℤ} {k : ℕ} (hk : 1 ≤ k) (h : K m = k) :
    m ∉ box (k - 1) := by
  intro hmem
  have h1 : K m ≤ k - 1 := K_le_of_mem_box m (k - 1) hmem
  rw [h] at h1
  omega

lemma eq_zero_of_K_eq_zero {m : Fin 3 → ℤ} (h : K m = 0) : m = 0 := by
  funext i
  have h1 : (m i).natAbs ≤ K m := K_spec m i
  rw [h] at h1
  exact Int.natAbs_eq_zero.mp (Nat.le_zero.mp h1)

end

end Work.BoseBoxFock
