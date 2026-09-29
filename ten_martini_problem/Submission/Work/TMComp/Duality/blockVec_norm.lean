import Mathlib
import Submission.Work.TMComp.Duality.Defs

namespace Work.TMComp.Duality

/-- The squared norm of a vector of `ℓ²` whose support is contained in a finite set is the
finite sum of the squared norms of its coordinates over that set. -/
theorem lp_norm_sq_eq_sum {α : Type*} (f : lp (fun _ : α => ℂ) 2) (s : Finset α)
    (hf : ∀ a, a ∉ s → f a = 0) : ‖f‖ ^ 2 = ∑ a ∈ s, ‖f a‖ ^ 2 := by
  have h := lp.norm_rpow_eq_tsum (E := fun _ : α => ℂ) (p := 2) (by norm_num) f
  norm_num at h
  rw [h, tsum_eq_sum]
  intro b hb
  rw [hf b hb, norm_zero]
  simp

theorem blockVec_norm (u : LeanEval.Analysis.TenMartini.EllTwo) (s : Finset ℤ) (hs : ∀ n : ℤ, n ∉ s → (u : ℤ → ℂ) n = 0) {N : ℕ} (hN : 0 < N) : ‖Work.TMComp.Duality.blockVec (u : ℤ → ℂ) s N‖ ^ 2 = ‖u‖ ^ 2 / (N : ℝ) := by
  have hsupp : ∀ p : ℤ × ℤ, p ∉ Finset.Ico (0 : ℤ) (N : ℤ) ×ˢ s →
      Work.TMComp.Duality.blockVec (u : ℤ → ℂ) s N p = 0 := by
    intro p hp
    rw [Work.TMComp.Duality.blockVec_coord, if_neg]
    intro h
    exact hp (Finset.mem_product.mpr ⟨Finset.mem_Ico.mpr ⟨h.1, h.2.1⟩, h.2.2⟩)
  rw [lp_norm_sq_eq_sum (Work.TMComp.Duality.blockVec (u : ℤ → ℂ) s N) _ hsupp,
      lp_norm_sq_eq_sum u s hs, Finset.sum_product]
  have hterm : ∀ m ∈ Finset.Ico (0 : ℤ) (N : ℤ),
      (∑ n ∈ s, ‖Work.TMComp.Duality.blockVec (u : ℤ → ℂ) s N (m, n)‖ ^ 2)
        = (∑ n ∈ s, ‖(u : ℤ → ℂ) n‖ ^ 2) / (N : ℝ) ^ 2 := by
    intro m hm
    obtain ⟨hm1, hm2⟩ := Finset.mem_Ico.mp hm
    rw [Finset.sum_congr rfl (fun n hn => by
      rw [Work.TMComp.Duality.blockVec_coord, if_pos ⟨hm1, hm2, hn⟩, norm_div,
        Complex.norm_natCast, div_pow])]
    exact (Finset.sum_div s (fun n => ‖(u : ℤ → ℂ) n‖ ^ 2) ((N : ℝ) ^ 2)).symm
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, Int.card_Ico]
  simp only [sub_zero, Int.toNat_natCast, nsmul_eq_mul]
  have hNne : (N : ℝ) ≠ 0 := by positivity
  field_simp

end Work.TMComp.Duality
