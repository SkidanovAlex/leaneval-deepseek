import Mathlib
import Submission.Work.BW.subgroup_rayDegAux
import Submission.Work.BW.boxPts_eq_Icc

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- Membership in the exponent box `degBox N d`: the exponent vectors `b` with `b i ≤ d i`
for every `i`. -/
lemma mem_degBox {N : ℕ} (d : Fin (N + 1) →₀ ℕ) (b : Fin (N + 1) → ℕ) :
    b ∈ degBox N d ↔ ∀ i, b i ≤ d i := by
  classical
  rw [degBox, Finset.mem_image]
  constructor
  · rintro ⟨c, hc, rfl⟩ i
    have hci : c i (Finset.mem_univ i) < d i + 1 := by
      have := Finset.mem_pi.mp hc i (Finset.mem_univ i)
      rwa [Finset.mem_range] at this
    exact Nat.le_of_lt_succ hci
  · intro h
    refine ⟨fun i _ => b i, ?_, ?_⟩
    · rw [Finset.mem_pi]
      intro i _
      rw [Finset.mem_range]
      exact Nat.lt_succ_of_le (h i)
    · rfl

/-- Membership in the lattice box `boxPts N m`: the lattice points `z` with
`0 ≤ z i ≤ m i` for every `i`. -/
lemma mem_boxPts {N : ℕ} (m : Fin N → ℕ) (z : Fin N → ℤ) :
    z ∈ boxPts N m ↔ ∀ i, 0 ≤ z i ∧ z i ≤ m i := by
  classical
  rw [boxPts, Finset.mem_image]
  constructor
  · rintro ⟨c, hc, rfl⟩ i
    have hci : c i (Finset.mem_univ i) < m i + 1 := by
      have := Finset.mem_pi.mp hc i (Finset.mem_univ i)
      rwa [Finset.mem_range] at this
    exact ⟨Int.natCast_nonneg _, Int.ofNat_le.mpr (Nat.le_of_lt_succ hci)⟩
  · intro h
    refine ⟨fun i _ => (z i).toNat, ?_, ?_⟩
    · rw [Finset.mem_pi]
      intro i _
      rw [Finset.mem_range, Nat.lt_succ_iff, Int.toNat_le]
      exact (h i).2
    · funext i
      exact Int.toNat_of_nonneg (h i).1

theorem torPart_image_filter_degBox {N : ℕ} (d : Fin (N + 1) →₀ ℕ) :
    (((degBox N d).filter (fun b => b 0 = 0)).image (fun b => torPart b))
      = boxPts N (fun i => d i.succ) := by
  classical
  ext z
  rw [Finset.mem_image, mem_boxPts]
  constructor
  · rintro ⟨b, hb, rfl⟩ i
    rw [Finset.mem_filter] at hb
    obtain ⟨hbdeg, _⟩ := hb
    have hb' := (mem_degBox d b).mp hbdeg
    exact ⟨Int.natCast_nonneg _, by
      show ((b i.succ : ℕ) : ℤ) ≤ ((fun i => d i.succ) i : ℤ)
      exact_mod_cast hb' i.succ⟩
  · intro h
    refine ⟨Fin.cons 0 (fun i => (z i).toNat), ?_, ?_⟩
    · rw [Finset.mem_filter, mem_degBox]
      refine ⟨?_, Fin.cons_zero _ _⟩
      intro i
      induction i using Fin.cases with
      | zero => simp
      | succ j =>
          rw [Fin.cons_succ, Int.toNat_le]
          exact (h j).2
    · funext i
      rw [torPart, Fin.cons_succ]
      exact Int.toNat_of_nonneg (h i).1

end Work.BW
