import Mathlib
import Submission.Work.Pert.Ksub2.Setup
import Submission.Work.Pert.Ksub2.deriv_phi_bounds_walk

/-!
# `Work.Pert.Ksub2.orbit_region`

The z-plane orbit region of a compact `K' ⊆ Dφ` for the first `N` backward steps.

For `w ∈ K'` and `1 ≤ m ≤ N` the point `w - m` lies in `Dφ` (iterated `ParabData.left_inv`) and its
successor `w - (m - 1)` lies in `Dφ` as well; `ParabData.succ_iff` then gives `d.φ (w - m) ∈ D₀`
(the last point of an orbit already belongs to the domain of definition of `f₀`).  Hence the finite
union `Z = ⋃_{1 ≤ m ≤ N} d.φ '' (K' - m)` is a compact subset of the open set `D₀`, and some closed
thickening of it is still contained in `D₀` (`IsCompact.exists_cthickening_subset_open`).
-/

namespace Work.Pert.Ksub2

theorem orbit_region {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    (hD0 : IsOpen D₀) {K' : Set ℂ} (hK'c : IsCompact K') (hK' : K' ⊆ d.Dφ)
    {ρe : ℝ} (hρe : 0 < ρe) (hcth : Metric.cthickening ρe K' ⊆ d.Dφ) (N : ℕ) :
    ∃ Z : Set ℂ, IsCompact Z ∧ Z ⊆ D₀ ∧
      (∀ w ∈ K', ∀ m : ℕ, 1 ≤ m → m ≤ N → d.φ (w - (m : ℂ)) ∈ Z) ∧
      ∃ R : ℝ, 0 < R ∧ R ≤ ρe ∧ Metric.cthickening R Z ⊆ D₀ := by
  have _hcth : Metric.cthickening ρe K' ⊆ d.Dφ := hcth
  -- the `m`-th slice of the orbit region
  let S : ℕ → Set ℂ := fun m => d.φ '' ((fun z : ℂ => z - (m : ℂ)) '' K')
  let Z : Set ℂ := ⋃ m ∈ ((Finset.Icc 1 N : Finset ℕ) : Set ℕ), S m
  -- every slice lies in `D₀`: `succ_iff` read at the backward translate `w - m`
  have hSsub : ∀ m ∈ ((Finset.Icc 1 N : Finset ℕ) : Set ℕ), S m ⊆ D₀ := by
    intro m hm
    rw [Finset.mem_coe, Finset.mem_Icc] at hm
    rintro z ⟨u, ⟨w, hw, rfl⟩, rfl⟩
    have hu : w - (m : ℂ) ∈ d.Dφ := Work.Pert.sub_nat_mem_Dφ d (hK' hw) m
    have hu1 : w - (m : ℂ) + 1 ∈ d.Dφ := by
      have hm_eq : (m : ℂ) = ((m - 1 : ℕ) : ℂ) + 1 := by
        rw [Nat.cast_sub hm.1]; ring
      have hshift : w - (m : ℂ) + 1 = w - ((m - 1 : ℕ) : ℂ) := by rw [hm_eq]; ring
      rw [hshift]
      exact Work.Pert.sub_nat_mem_Dφ d (hK' hw) (m - 1)
    exact (d.succ_iff (w - (m : ℂ)) hu).mp hu1
  -- the orbit region is a finite union of compact slices
  have hZc : IsCompact Z := by
    refine Set.Finite.isCompact_biUnion (Finset.finite_toSet _) (fun m hm => ?_)
    have hmK : IsCompact ((fun z : ℂ => z - (m : ℂ)) '' K') :=
      hK'c.image (continuous_id.sub continuous_const)
    refine hmK.image_of_continuousOn ?_
    exact d.φ_holo.continuousOn.mono (fun z hz => by
      obtain ⟨w, hw, rfl⟩ := hz
      exact Work.Pert.sub_nat_mem_Dφ d (hK' hw) m)
  have hZD0 : Z ⊆ D₀ := by
    intro z hz
    simp only [Z, Set.mem_iUnion] at hz
    obtain ⟨m, hm, hzm⟩ := hz
    exact hSsub m hm hzm
  refine ⟨Z, hZc, hZD0, ?_, ?_⟩
  · intro w hw m hm1 hmN
    show d.φ (w - ↑m) ∈ ⋃ m ∈ ((Finset.Icc 1 N : Finset ℕ) : Set ℕ), S m
    rw [Set.mem_iUnion₂]
    exact ⟨m, by rw [Finset.mem_coe, Finset.mem_Icc]; exact ⟨hm1, hmN⟩,
      ⟨w - ↑m, ⟨w, hw, rfl⟩, rfl⟩⟩
  · -- a closed thickening of a compact subset of an open set stays in the open set
    obtain ⟨δ, hδpos, hδsub⟩ := hZc.exists_cthickening_subset_open hD0 hZD0
    exact ⟨min δ ρe, lt_min hδpos hρe, min_le_right _ _,
      (Metric.cthickening_mono (min_le_left _ _) Z).trans hδsub⟩

end Work.Pert.Ksub2
