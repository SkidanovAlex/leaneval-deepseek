import Mathlib
import Submission.Work.EKLContract.Defs
import Submission.Work.EKLComp.Misiurewicz.Defs
import Submission.Work.Misiurewicz.exists_null_frontier_Vball_radius
import Submission.Work.Misiurewicz.exists_V_mul_inv_subset
import Submission.Work.Misiurewicz.V_mul_Vbar_subset
import Submission.Work.EKLComp.inv_mem_V
import Submission.Work.EKLComp.X3Background

namespace Work.EKLC6Core

open Work.EKLContract Work.EKLComp

/-- Product estimate: `V p · V q ⊆ V (q + 3 (1 + q) p)` for `p > 0`. -/
theorem mul_mem_V_bound {p q : ℝ} (hp : 0 < p) {g h : SL3}
    (hg : g ∈ V p) (hh : h ∈ V q) :
    g * h ∈ V (q + 3 * (1 + q) * p) := by
  have hbound : p + q + 3 * p * q < q + 3 * (1 + q) * p := by nlinarith [hp]
  intro i j
  rw [Matrix.SpecialLinearGroup.coe_mul]
  exact Work.Misiurewicz.matrix_mul_entry_bound hp hbound (fun i j => hg i j)
    (fun i j => le_of_lt (hh i j)) i j

theorem smul_frontier_Vball_subset (x : Work.EKLContract.X3) {r : ℝ} (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ η : ℝ, 0 < η → η ≤ 1 →
      (fun p : Work.EKLContract.SL3 × Work.EKLContract.X3 => p.1 • p.2) ''
          ((Work.EKLContract.V η) ×ˢ frontier (Work.EKLComp.Vball r x)) ⊆
        Work.EKLComp.Vball (r + C * η) x \ Work.EKLComp.Vball (r - C * η) x := by
  refine ⟨30 * (1 + r) + 1, by linarith, ?_⟩
  intro η hη hη1 z hz
  rcases hz with ⟨⟨g, y⟩, ⟨hg, hy⟩, rfl⟩
  have hy_notin : y ∉ Vball r x :=
    (Work.Misiurewicz.frontier_Vball_subset x hr (by linarith : r < r + 1) hy).2
  have hycl : y ∈ closure (Vball r x) := frontier_subset_closure hy
  refine ⟨?_, ?_⟩
  · -- upper bound
    obtain ⟨w, hw, hwy⟩ :=
      Work.Misiurewicz.closure_Vball_subset x (by linarith : r < r + η) hycl
    have hwy' : w • x = y := hwy
    refine ⟨g * w, Work.Misiurewicz.V_mono (le_of_lt ?_) (mul_mem_V_bound hη hg hw), ?_⟩
    · nlinarith [mul_le_mul_of_nonneg_left hη1 (le_of_lt hη)]
    · show (g * w) • x = g • y
      rw [mul_smul, hwy']
  · -- lower bound
    intro hmem
    obtain ⟨w, hw, hwy⟩ := hmem
    have hwy' : w • x = g • y := hwy
    have hqpos : 0 < r - (30 * (1 + r) + 1) * η := by
      have h00 : |(w : Matrix (Fin 3) (Fin 3) ℝ) 0 0 - 1| < r - (30 * (1 + r) + 1) * η := by
        simpa using hw 0 0
      linarith [abs_nonneg ((w : Matrix (Fin 3) (Fin 3) ℝ) 0 0 - 1)]
    have hginv : g⁻¹ ∈ V (10 * η) := Work.EKLComp.inv_mem_V hη hη1 hg
    have hprod : g⁻¹ * w ∈ V ((r - (30 * (1 + r) + 1) * η)
        + 3 * (1 + (r - (30 * (1 + r) + 1) * η)) * (10 * η)) :=
      mul_mem_V_bound (by linarith : 0 < 10 * η) hginv hw
    have hlt : (r - (30 * (1 + r) + 1) * η)
        + 3 * (1 + (r - (30 * (1 + r) + 1) * η)) * (10 * η) < r := by
      have hCeta : 0 < (30 * (1 + r) + 1) * η := by positivity
      have hq_lt_r : r - (30 * (1 + r) + 1) * η < r := by linarith
      have h1q : 1 + (r - (30 * (1 + r) + 1) * η) < 1 + r := by linarith
      have h30 : 0 < 30 * η := by positivity
      have hstep := mul_lt_mul_of_pos_left h1q h30
      have h2 : 30 * η * (1 + r) < (30 * (1 + r) + 1) * η := by nlinarith [hη]
      nlinarith [hstep, h2, hCeta]
    have hy_r : y ∈ Vball r x :=
      ⟨g⁻¹ * w, Work.Misiurewicz.V_mono (le_of_lt hlt) hprod, by
        show (g⁻¹ * w) • x = y
        rw [mul_smul, hwy', ← mul_smul, inv_mul_cancel, one_smul]⟩
    exact hy_notin hy_r

end Work.EKLC6Core
