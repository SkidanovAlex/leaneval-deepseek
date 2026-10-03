import Mathlib
import Submission.Work.Peluse.Basic

/-!
# Elementary window facts for the `lemma51P 2 → lemma51P 1` transfer

Local helpers (`Work.Peluse.Pel51`, the area of the node `Work.Peluse.ucontrol_of_concat`) about
`symIcc`, `arithIcc` and `SupportIn`, kept separate so that the assembly file stays readable.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Peluse.Pel51

open Work.Peluse

/-- `SupportIn f N` is exactly "`f` vanishes off `symIcc N`". -/
theorem supportIn_iff_notMem {N : ℕ} {f : ℤ → ℂ} (h : SupportIn f N) :
    ∀ x : ℤ, x ∉ symIcc N → f x = 0 := by
  intro x hx
  apply h
  by_contra hcon
  push_neg at hcon
  exact hx (by
    rw [symIcc, Finset.mem_Icc]
    have h' : |x| ≤ (N : ℤ) := by
      rw [← Int.natCast_natAbs]
      exact_mod_cast hcon
    exact abs_le.mp h')

/-- `symIcc` is monotone. -/
theorem symIcc_subset {N N' : ℕ} (h : N ≤ N') : symIcc N ⊆ symIcc N' := by
  intro x hx
  rw [symIcc, Finset.mem_Icc] at hx ⊢
  obtain ⟨h1, h2⟩ := hx
  have hZ : (N : ℤ) ≤ (N' : ℤ) := by exact_mod_cast h
  exact ⟨by linarith, by linarith⟩

/-- The cardinality of the symmetric box. -/
theorem card_symIcc (N : ℕ) : (symIcc N).card = 2 * N + 1 := by
  rw [symIcc, Int.card_Icc]
  have h : ((N : ℤ) + 1 - (-(N : ℤ))) = (((2 * N + 1 : ℕ)) : ℤ) := by push_cast; ring
  rw [h, Int.toNat_natCast]

/-- The arithmetic progression `arithIcc d L` is nonempty as soon as `1 ≤ L`. -/
theorem arithIcc_nonempty {d : ℤ} {L : ℕ} (hL : 1 ≤ L) : (arithIcc d L).Nonempty :=
  ⟨d * 1, Finset.mem_image.mpr ⟨1, by simp only [Finset.mem_Icc]; omega, by norm_num⟩⟩

/-- Every element of `arithIcc d L` is bounded by `|d| * L`. -/
theorem abs_le_of_mem_arithIcc {d : ℤ} {L : ℕ} {z : ℤ} (hz : z ∈ arithIcc d L) :
    |z| ≤ |d| * (L : ℤ) := by
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hz
  rw [abs_mul]
  have hn1 : (n : ℤ) ≤ (L : ℤ) := by
    exact_mod_cast (Finset.mem_Icc.mp hn).2
  have hn0 : 0 ≤ (n : ℤ) := Nat.cast_nonneg n
  have hle : |(n : ℤ)| ≤ (L : ℤ) := by rw [abs_of_nonneg hn0]; exact hn1
  exact mul_le_mul_of_nonneg_left hle (abs_nonneg d)

end Work.Peluse.Pel51
