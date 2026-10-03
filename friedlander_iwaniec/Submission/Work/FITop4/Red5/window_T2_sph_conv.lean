/-
# `Work.FITop4.Red5` — sphere-fibre conversion helpers for the `T2` shell

Shared low-level lemmas used by the `T2`-shell count: membership in the norm-`m`
sphere `wSph m`, and the domination of the fibre sum over an `m`-window by the
`gBox` sum filtered by the norm range.
-/
import Mathlib
import Submission.Work.FITop4.Red5.piecesSetup
import Submission.Work.FITop4.Red5.assembly_helpers
import Submission.Work.FITop4.Red5.primary_setup

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.FITop4.Red5

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- Membership in the norm-`m` sphere. -/
lemma mem_wSph_iff {m : ℕ} {w : GaussianInt} : w ∈ wSph m ↔ Work.FIPlan.gnorm w = m := by
  rw [wSph, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨mem_gBox_of_gnorm_eq h, h⟩⟩

/-- The window sum over one `m`-fibre is dominated by the sum over all Gaussian integers in the
box `gBox (2Mn)` with norm in `[A,B]`. -/
lemma sum_Icc_wSph_le_box (z : GaussianInt) {Mn A B : ℕ} (hMn : 1 ≤ Mn) (hA : 1 ≤ A)
    (hB : B ≤ 2 * Mn) :
    (∑ m ∈ Finset.Icc A B, ∑ w ∈ wSph m, (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ))
      ≤ ∑ w ∈ (Work.FIPlan.gBox (2 * (Mn : ℤ))).filter
          (fun w => A ≤ Work.FIPlan.gnorm w ∧ Work.FIPlan.gnorm w ≤ B),
          (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ) := by
  set S : Finset GaussianInt := (Work.FIPlan.gBox (2 * (Mn : ℤ))).filter
      (fun w => A ≤ Work.FIPlan.gnorm w ∧ Work.FIPlan.gnorm w ≤ B) with hS
  have hcast : (((2 * Mn : ℕ)) : ℤ) = 2 * (Mn : ℤ) := by push_cast; ring
  have hmaps : ∀ w ∈ S, Work.FIPlan.gnorm w ∈ Finset.Icc A B := by
    intro w hw
    rw [hS, Finset.mem_filter] at hw
    exact Finset.mem_Icc.mpr ⟨hw.2.1, hw.2.2⟩
  have hsub : ∀ m ∈ Finset.Icc A B, wSph m ⊆ S.filter (fun w => Work.FIPlan.gnorm w = m) := by
    intro m hm w hw
    rw [mem_wSph_iff] at hw
    rw [Finset.mem_filter]
    refine ⟨?_, hw⟩
    rw [hS, Finset.mem_filter]
    refine ⟨?_, ?_, ?_⟩
    · rw [← hcast]
      exact mem_gBox_of_norm_sq hw (by
        have hm2 : m ≤ 2 * Mn := le_trans (Finset.mem_Icc.mp hm).2 hB
        calc m ≤ 2 * Mn := hm2
          _ ≤ (2 * Mn) * (2 * Mn) := by
              calc 2 * Mn = (2 * Mn) * 1 := (mul_one _).symm
                _ ≤ (2 * Mn) * (2 * Mn) := Nat.mul_le_mul_left _ (by omega)
          _ = (2 * Mn) ^ 2 := (pow_two _).symm)
    · rw [hw]; exact (Finset.mem_Icc.mp hm).1
    · rw [hw]; exact (Finset.mem_Icc.mp hm).2
  calc (∑ m ∈ Finset.Icc A B, ∑ w ∈ wSph m, (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ))
      ≤ ∑ m ∈ Finset.Icc A B,
          ∑ w ∈ S.filter (fun w => Work.FIPlan.gnorm w = m),
            (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ) :=
        Finset.sum_le_sum (fun m hm =>
          Finset.sum_le_sum_of_subset_of_nonneg (hsub m hm) (fun w _ _ => Zint_nonneg _))
    _ = ∑ w ∈ S, (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ) :=
        Finset.sum_fiberwise_of_maps_to hmaps
          (fun w => (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ))

end

end Work.FITop4.Red5
