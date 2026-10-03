import Mathlib
import Submission.Work.Pert.Ksub2.Setup
import Submission.Work.Pert.Ksub2.exists_lipschitzOn_of_compact
import Submission.Work.Interfaces.Parabolic

namespace Work.PertCrux

open Set Metric
open scoped Topology

theorem exists_orbit_nhd {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (hd : MandelDim.IsParabolicGerm f₀ D₀)
    (d : MandelDim.ParabData f₀ D₀) {K' : Set ℂ} (hK'c : IsCompact K') (hK' : K' ⊆ d.Dφ) (N : ℕ) :
    ∃ V : Set ℂ, IsCompact V ∧ V ⊆ D₀ ∧ ∃ R : ℝ, 0 < R ∧ ∃ Lf : ℝ, 1 ≤ Lf ∧
      (∀ z ∈ V, ∀ z' ∈ V, ‖f₀ z - f₀ z'‖ ≤ Lf * ‖z - z'‖) ∧
      ∀ w ∈ K', ∀ m : ℕ, 1 ≤ m → m ≤ N → Metric.closedBall (d.φ (w - (m : ℂ))) R ⊆ V := by
  obtain ⟨hD0open, -, hf0diff, -⟩ := hd
  -- (1) the backward translates `w - m` of a point of `K'` stay in the maximal domain `d.Dφ`
  have htrans : ∀ (m : ℕ) (w : ℂ), w ∈ K' → w - (m : ℂ) ∈ d.Dφ := by
    intro m
    induction m with
    | zero => intro w hw; simpa using hK' hw
    | succ k ih =>
      intro w hw
      have h1 : w - (k : ℂ) ∈ d.Dφ := ih w hw
      have h2 : w - (k : ℂ) - 1 ∈ d.Dφ := d.left_inv _ h1
      have heq : w - ((k + 1 : ℕ) : ℂ) = w - (k : ℂ) - 1 := by push_cast; ring
      rw [heq]; exact h2
  -- (2) the finite set of image points
  set S : ℕ → Set ℂ := fun m => d.φ '' ((fun w : ℂ => w - (m : ℂ)) '' K') with hSdef
  set E : Set ℂ := ⋃ m ∈ ((Finset.Icc 1 N : Finset ℕ) : Set ℕ), S m with hEdef
  -- (3) each `S m` is compact
  have hScomp : ∀ m ∈ ((Finset.Icc 1 N : Finset ℕ) : Set ℕ), IsCompact (S m) := by
    intro m _
    have hsub : (fun w : ℂ => w - (m : ℂ)) '' K' ⊆ d.Dφ := by
      rintro _ ⟨w, hw, rfl⟩; exact htrans m w hw
    exact (hK'c.image (continuous_id.sub continuous_const)).image_of_continuousOn
      ((d.φ_holo.continuousOn).mono hsub)
  -- (4) hence `E` is compact
  have hEc : IsCompact E := by
    rw [hEdef]
    exact (Finset.finite_toSet (Finset.Icc 1 N)).isCompact_biUnion hScomp
  -- (5) `E ⊆ D₀`: `φ (w - m) ∈ D₀` for `1 ≤ m`, by `succ_iff` at `w - m`
  have hED : E ⊆ D₀ := by
    intro x hx
    rw [hEdef] at hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨m, hm, y, ⟨w, hw, rfl⟩, rfl⟩ := hx
    rw [Finset.mem_coe, Finset.mem_Icc] at hm
    obtain ⟨hm1, hmN⟩ := hm
    have h1 : w - (m : ℂ) ∈ d.Dφ := htrans m w hw
    have h2 : w - (m : ℂ) + 1 ∈ d.Dφ := by
      have heq : w - (m : ℂ) + 1 = w - (((m - 1 : ℕ)) : ℂ) := by
        rw [Nat.cast_pred (by omega)]; ring
      rw [heq]; exact htrans (m - 1) w hw
    exact (d.succ_iff _ h1).mp h2
  -- (6) a uniform radius inside the open set `D₀`
  obtain ⟨R, hRpos, hRsub⟩ := hEc.exists_cthickening_subset_open hD0open hED
  -- (7) `f₀` is Lipschitz on the compact thickening
  have hVc : IsCompact (cthickening R E) := hEc.cthickening
  have hVD : cthickening R E ⊆ D₀ := hRsub
  obtain ⟨L, hLnn, hLip⟩ := Work.Pert.Ksub2.exists_lipschitzOn_of_compact hD0open hVc hVD hf0diff
  refine ⟨cthickening R E, hVc, hVD, R, hRpos, max L 1, le_max_right L 1, ?_, ?_⟩
  · intro z hz z' hz'
    exact le_trans (hLip z hz z' hz')
      (mul_le_mul_of_nonneg_right (le_max_left L 1) (norm_nonneg _))
  · intro w hwK' m hm1 hmN
    have hm : m ∈ ((Finset.Icc 1 N : Finset ℕ) : Set ℕ) := by
      rw [Finset.mem_coe, Finset.mem_Icc]; exact ⟨hm1, hmN⟩
    have hmem : d.φ (w - (m : ℂ)) ∈ E := by
      rw [hEdef]
      exact Set.mem_iUnion.mpr ⟨m, Set.mem_iUnion.mpr ⟨hm, Set.mem_image_of_mem _
        (Set.mem_image_of_mem _ hwK')⟩⟩
    exact Metric.closedBall_subset_cthickening hmem R

end Work.PertCrux
