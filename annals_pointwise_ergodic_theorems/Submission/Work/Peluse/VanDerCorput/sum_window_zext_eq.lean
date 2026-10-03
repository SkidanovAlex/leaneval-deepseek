import Mathlib
import Submission.Work.Peluse.VanDerCorput.Defs

/-!
# The window count for the van der Corput inequality (Peluse, Lemma 4.1)

For every `y` in the window `I = [1, M]` there are exactly `H` pairs `(u, h)` with
`u ∈ [1 - H, M - 1]` and `h ∈ [1, H]` such that `u + h = y` (namely `h ∈ [1, H]` and
`u = y - h`).  Consequently, summing the zero extension `zext I g` over the window of
shifts `u + h` reproduces `H` copies of `∑_{y ∈ I} g y`.

This is the bookkeeping identity that lets the van der Corput argument average over the
shift parameter `h ∈ [1, H]` without losing the original window.
-/

namespace Work.Peluse.VanDerCorput

open scoped BigOperators

theorem sum_window_zext_eq {M H : ℕ} (g : ℤ → ℂ) :
    ∑ u ∈ Finset.Icc (1 - (H : ℤ)) ((M : ℤ) - 1),
        ∑ h ∈ Finset.Icc (1 : ℤ) (H : ℤ), Work.Peluse.VanDerCorput.zext (Finset.Icc (1 : ℤ) (M : ℤ)) g (u + h) =
      (H : ℂ) * ∑ y ∈ Finset.Icc (1 : ℤ) (M : ℤ), g y := by
  -- Swap the order of summation: for each shift `h` the inner sum becomes a translate of
  -- the window, which then contains the whole window `I = [1, M]`.
  rw [Finset.sum_comm]
  have key : ∀ h ∈ Finset.Icc (1 : ℤ) (H : ℤ),
      ∑ u ∈ Finset.Icc (1 - (H : ℤ)) ((M : ℤ) - 1),
          zext (Finset.Icc (1 : ℤ) (M : ℤ)) g (u + h)
        = ∑ y ∈ Finset.Icc (1 : ℤ) (M : ℤ), g y := by
    intro h hh
    have h1 : (1 : ℤ) ≤ h := (Finset.mem_Icc.mp hh).1
    have h2 : h ≤ (H : ℤ) := (Finset.mem_Icc.mp hh).2
    -- the translated shift window contains `I`
    have hsub : Finset.Icc (1 : ℤ) (M : ℤ) ⊆
        Finset.Icc (1 - (H : ℤ) + h) ((M : ℤ) - 1 + h) := by
      intro y hy
      rw [Finset.mem_Icc] at hy ⊢
      obtain ⟨hy1, hy2⟩ := hy
      constructor <;> omega
    -- and `zext I g` vanishes off `I`
    have hvan : ∀ y ∈ Finset.Icc (1 - (H : ℤ) + h) ((M : ℤ) - 1 + h),
        y ∉ Finset.Icc (1 : ℤ) (M : ℤ) → zext (Finset.Icc (1 : ℤ) (M : ℤ)) g y = 0 :=
      fun y _ hy => zext_of_notMem hy
    calc ∑ u ∈ Finset.Icc (1 - (H : ℤ)) ((M : ℤ) - 1),
            zext (Finset.Icc (1 : ℤ) (M : ℤ)) g (u + h)
        = ∑ u ∈ Finset.Icc (1 - (H : ℤ)) ((M : ℤ) - 1),
            zext (Finset.Icc (1 : ℤ) (M : ℤ)) g ((addRightEmbedding h) u) := by
            simp [addRightEmbedding_apply]
      _ = ∑ y ∈ (Finset.Icc (1 - (H : ℤ)) ((M : ℤ) - 1)).map (addRightEmbedding h),
            zext (Finset.Icc (1 : ℤ) (M : ℤ)) g y :=
            (Finset.sum_map _ (addRightEmbedding h) _).symm
      _ = ∑ y ∈ Finset.Icc (1 - (H : ℤ) + h) ((M : ℤ) - 1 + h),
            zext (Finset.Icc (1 : ℤ) (M : ℤ)) g y := by
            rw [Finset.map_add_right_Icc]
      _ = ∑ y ∈ Finset.Icc (1 : ℤ) (M : ℤ), zext (Finset.Icc (1 : ℤ) (M : ℤ)) g y :=
            (Finset.sum_subset hsub hvan).symm
      _ = ∑ y ∈ Finset.Icc (1 : ℤ) (M : ℤ), g y :=
            Finset.sum_congr rfl (fun y hy => zext_of_mem hy)
  calc ∑ h ∈ Finset.Icc (1 : ℤ) (H : ℤ),
          ∑ u ∈ Finset.Icc (1 - (H : ℤ)) ((M : ℤ) - 1),
              zext (Finset.Icc (1 : ℤ) (M : ℤ)) g (u + h)
      = ∑ h ∈ Finset.Icc (1 : ℤ) (H : ℤ), ∑ y ∈ Finset.Icc (1 : ℤ) (M : ℤ), g y :=
          Finset.sum_congr rfl key
    _ = (H : ℂ) * ∑ y ∈ Finset.Icc (1 : ℤ) (M : ℤ), g y := by
          rw [Finset.sum_const, nsmul_eq_mul, Int.card_Icc]
          norm_num

end Work.Peluse.VanDerCorput
