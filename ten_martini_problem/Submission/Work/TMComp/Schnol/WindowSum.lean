import Mathlib
import Submission.Work.TMComp.Schnol.Defs
import Submission.Work.TMComp.Schnol.Basic
import Submission.Work.TMComp.Schnol.FiniteVolume

/-!
# Component C15 (`P_Schnol`): index bookkeeping for the window `[-M, M]`

The window `[-M, M]` is indexed by `Fin (2*M+1)` (index `i` ↔ site `i - M`); we collect the
correspondence with sums over finsets of sites, and the finite Cauchy–Schwarz inequality used
to bound the coefficients of a spectral vector along the support.
-/

open scoped ENNReal
open LeanEval.Analysis.TenMartini

noncomputable section

namespace Work.TMComp.Schnol

/-- Cauchy–Schwarz for finite sums of products of complex numbers. -/
theorem norm_sum_mul_sq_le {ι : Type*} (F : Finset ι) (f g : ι → ℂ) :
    ‖∑ i ∈ F, f i * g i‖ ^ 2 ≤ (∑ i ∈ F, ‖f i‖ ^ 2) * (∑ i ∈ F, ‖g i‖ ^ 2) := by
  have h1 : ‖∑ i ∈ F, f i * g i‖ ≤ ∑ i ∈ F, ‖f i‖ * ‖g i‖ := by
    calc ‖∑ i ∈ F, f i * g i‖ ≤ ∑ i ∈ F, ‖f i * g i‖ := norm_sum_le _ _
      _ = ∑ i ∈ F, ‖f i‖ * ‖g i‖ := by simp [norm_mul]
  have h3 : (∑ i ∈ F, ‖f i‖ * ‖g i‖) ^ 2 ≤ (∑ i ∈ F, ‖f i‖ ^ 2) * (∑ i ∈ F, ‖g i‖ ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq F (fun i => ‖f i‖) (fun i => ‖g i‖)
  exact le_trans (pow_le_pow_left₀ (norm_nonneg _) h1 2) h3

/-- The window `[-M, M]` as a finset of sites, indexed by `Fin (2*M+1)` via `i ↦ i - M`. -/
def winFinset (M : ℕ) : Finset ℤ :=
  Finset.univ.image (fun i : Fin (2 * M + 1) => (i : ℤ) - (M : ℤ))

theorem mem_winFinset {M : ℕ} {m : ℤ} :
    m ∈ winFinset M ↔ -(M : ℤ) ≤ m ∧ m ≤ (M : ℤ) := by
  constructor
  · intro hm
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hm
    exact ⟨by push_cast; omega, by push_cast; omega⟩
  · intro hm
    refine Finset.mem_image.mpr ⟨⟨(m + (M : ℤ)).toNat, ?_⟩, Finset.mem_univ _, ?_⟩
    · rw [Int.toNat_lt (by omega)]; omega
    · show ((((m + (M : ℤ)).toNat : ℕ)) : ℤ) - (M : ℤ) = m
      rw [Int.toNat_of_nonneg (by omega)]
      ring

theorem mem_winFinset_of_le {M : ℕ} {m : ℤ} (h1 : -(M : ℤ) ≤ m) (h2 : m ≤ (M : ℤ)) :
    m ∈ winFinset M :=
  mem_winFinset.mpr ⟨h1, h2⟩

theorem winFinset_subset_Icc (M : ℕ) : winFinset M ⊆ Finset.Icc (-(M : ℤ)) (M : ℤ) := by
  intro m hm
  obtain ⟨h1, h2⟩ := mem_winFinset.mp hm
  rw [Finset.mem_Icc]
  exact ⟨h1, h2⟩

theorem sum_winFinset_wt_le (M : ℕ) : ∑ m ∈ winFinset M, wt m ≤ Wtot :=
  le_trans (Finset.sum_le_sum_of_subset_of_nonneg (winFinset_subset_Icc M)
    (fun i _ _ => wt_nonneg i)) (sum_window_wt_le M)

/-- The index of the window: a sum over `Fin (2*M+1)` equals a sum over `winFinset M`. -/
theorem sum_window_eq_sum_fin {A : Type*} [AddCommMonoid A] (M : ℕ) (g : ℤ → A) :
    (∑ i : Fin (2 * M + 1), g ((i : ℤ) - (M : ℤ))) = ∑ m ∈ winFinset M, g m := by
  have hinj : Set.InjOn (fun i : Fin (2 * M + 1) => (i : ℤ) - (M : ℤ))
      ((Finset.univ : Finset (Fin (2 * M + 1))) : Set (Fin (2 * M + 1))) := by
    intro x _ y _ hxy
    have h : ((x : ℕ) : ℤ) = ((y : ℕ) : ℤ) := by linarith [hxy]
    exact Fin.ext (by exact_mod_cast h)
  rw [winFinset]
  exact (Finset.sum_image hinj).symm

/-- A sum over a sub-finset `s` of the window, rewritten as a sum over the corresponding
indices of `Fin (2*M+1)`. -/
theorem sum_subset_window {A : Type*} [AddCommMonoid A] (M : ℕ) (s : Finset ℤ)
    (hs : ∀ m ∈ s, m ∈ winFinset M) (g : ℤ → A) :
    ∑ m ∈ s, g m
      = ∑ i ∈ Finset.univ.filter (fun i : Fin (2 * M + 1) => ((i : ℤ) - (M : ℤ)) ∈ s),
          g ((i : ℤ) - (M : ℤ)) := by
  have hR : (∑ m ∈ winFinset M, (if m ∈ s then g m else 0)) = ∑ m ∈ s, g m := by
    rw [← Finset.sum_subset hs (fun m _ hm => by rw [if_neg hm])]
    exact Finset.sum_congr rfl (fun m hm => if_pos hm)
  have hkey := sum_window_eq_sum_fin M (fun m : ℤ => if m ∈ s then g m else 0)
  have hfilter :
      (∑ i ∈ Finset.univ.filter (fun i : Fin (2 * M + 1) => ((i : ℤ) - (M : ℤ)) ∈ s),
          g ((i : ℤ) - (M : ℤ)))
        = ∑ i : Fin (2 * M + 1),
            if ((i : ℤ) - (M : ℤ)) ∈ s then g ((i : ℤ) - (M : ℤ)) else 0 := by
    rw [Finset.sum_filter]
  exact hR.symm.trans (hkey.symm.trans hfilter.symm)

end Work.TMComp.Schnol
