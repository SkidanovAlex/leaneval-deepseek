import Mathlib
import Submission.Work.Diff.STE.CSq_periodization_le_of_sup_bound
import Submission.Work.Diff.STE.periodization_contDiff_periodic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.B3

/-- The translate of the half-open unit cube `(0,1]^ι` by the lattice vector `iVec k` is the
half-open box `∏ᵢ (kᵢ, kᵢ + 1]`. -/
lemma mem_image_iVec_unitCube {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ι → ℤ) (x : ι → ℝ) :
    x ∈ (fun y : ι → ℝ => y + Work.Diff.STE.iVec k) '' Work.Diff.STE.unitCube ↔
      ∀ i, x i ∈ Set.Ioc ((k i : ℝ)) ((k i : ℝ) + 1) := by
  constructor
  · rintro ⟨y, hy, rfl⟩ i
    have hyi : y i ∈ Set.Ioc (0 : ℝ) 1 := Set.mem_pi.mp hy i (Set.mem_univ i)
    rw [Set.mem_Ioc] at hyi ⊢
    simp only [Pi.add_apply, Work.Diff.STE.iVec_apply]
    exact ⟨by linarith [hyi.1], by linarith [hyi.2]⟩
  · intro hx
    refine ⟨x - Work.Diff.STE.iVec k, ?_, ?_⟩
    · rw [Work.Diff.STE.unitCube, Set.mem_pi]
      intro i _
      rw [Set.mem_Ioc]
      have hi := hx i
      rw [Set.mem_Ioc] at hi
      simp only [Pi.sub_apply, Work.Diff.STE.iVec_apply]
      exact ⟨by linarith [hi.1], by linarith [hi.2]⟩
    · funext i
      simp only [Pi.add_apply, Pi.sub_apply, Work.Diff.STE.iVec_apply]
      ring

/-- The boxes `∏ᵢ (kᵢ, kᵢ+1]` for `k ∈ {-1,0}^ι` tile `(-1,1]^ι`: the union over the lattice
vectors of the box of `csqp_boxIdx` is the half-open cube `∏ᵢ (-1, 1]`. -/
theorem boxIdx_iUnion {ι : Type*} [Fintype ι] [DecidableEq ι] :
    (⋃ k ∈ Work.Diff.STE.csqp_boxIdx ι,
        (fun y : ι → ℝ => y + Work.Diff.STE.iVec k) '' Work.Diff.STE.unitCube)
      = Set.pi Set.univ (fun _ : ι => Set.Ioc (-1 : ℝ) 1) := by
  ext x
  simp only [Set.mem_iUnion, exists_prop, mem_image_iVec_unitCube, Set.mem_pi, Set.mem_univ,
    true_implies, Work.Diff.STE.csqp_mem_boxIdx]
  constructor
  · rintro ⟨k, hk, hxk⟩ i
    have hki := hk i
    rw [Finset.mem_Icc] at hki
    obtain ⟨h1, h2⟩ := hxk i
    rw [Set.mem_Ioc]
    have h1' : (-1 : ℝ) ≤ (k i : ℝ) := by exact_mod_cast hki.1
    have h2' : (k i : ℝ) ≤ 0 := by exact_mod_cast hki.2
    exact ⟨by linarith, by linarith⟩
  · intro hx
    refine ⟨fun i => if (0 : ℝ) < x i then 0 else -1, ?_, ?_⟩
    · intro i
      dsimp only
      rw [Finset.mem_Icc]
      split_ifs <;> norm_num
    · intro i
      dsimp only
      rw [Set.mem_Ioc]
      have hi := hx i
      rw [Set.mem_Ioc] at hi
      split_ifs with h
      · norm_num
        exact ⟨h, hi.2⟩
      · norm_num
        have hle : x i ≤ 0 := le_of_not_gt h
        exact ⟨by linarith [hi.1], by linarith [hle]⟩

end Work.Diff.STE.B3
