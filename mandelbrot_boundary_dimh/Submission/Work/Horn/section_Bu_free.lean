import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Horn.top_section_exists
import Submission.Work.Horn.deep_branch_bu
import Submission.Work.L62.lift_section
import Submission.Work.L62.section_unique

namespace Work.Horn

open Complex Filter Topology Metric
open scoped Topology

noncomputable section

set_option linter.unusedVariables false

/-- A function which is `ε`-small on every half-plane `{R < Im ·}` tends to `0` at the upper end
`upperEnd = comap im atTop`. -/
theorem tendsto_upperEnd_of_forall_im {f : ℂ → ℂ}
    (h : ∀ ε > 0, ∃ R : ℝ, ∀ w : ℂ, R < w.im → ‖f w‖ < ε) :
    Filter.Tendsto f MandelDim.upperEnd (nhds 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨R, hR⟩ := h ε hε
  rw [MandelDim.upperEnd, Filter.eventually_comap, Filter.eventually_atTop]
  refine ⟨R + 1, fun a ha u hu => ?_⟩
  have hlt : R < u.im := by rw [hu]; linarith
  have hsmall := hR u hlt
  rwa [dist_zero_right]

theorem section_Bu_free {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    {Bu : Set ℂ} {η : ℝ} {v : ℂ}
    (hBuO : IsOpen Bu) (hBuS : SimplyConnectedSpace Bu)
    (hBuT : MandelDim.IsTInvariant Bu)
    (hup : {w : ℂ | η < w.im} ⊆ Bu)
    (hsub : Bu ⊆ d.DE)
    (hcov : IsCoveringMapOn (fun z : Bu => d.E z) {y : ℂ | ∀ k : ℤ, y ≠ v + k})
    (havoid : ∀ w ∈ Bu, ∀ k : ℤ, w ≠ v + k) :
    ∃ σ : ℂ → ℂ, DifferentiableOn ℂ σ Bu ∧ (∀ y ∈ Bu, σ y ∈ Bu ∧ d.E (σ y) = y) ∧
      (∀ y ∈ Bu, σ (y + 1) = σ y + 1) ∧
      Filter.Tendsto (fun w => σ w - w) MandelDim.upperEnd (nhds 0) := by
  -- `E = Φ ∘ φ` is holomorphic on `Bu ⊆ DE`
  have hE_diff : DifferentiableOn ℂ d.E Bu :=
    d.Φ_holo.comp (d.φ_holo.mono fun w hw => (hsub hw).1) fun w hw => (hsub hw).2
  -- and `T`-equivariant there
  have hE_one : ∀ w ∈ Bu, d.E (w + 1) = d.E w + 1 := E_add_one_of_subset_DE d hsub
  -- the covering over the whole of `Bu` (which misses the critical value class)
  have hcovBu : IsCoveringMapOn (fun z : Bu => d.E z) Bu := hcov.mono havoid
  -- the deep inverse branch of `E` in `Bu`
  obtain ⟨y', hy'η, H, hHdiff, hHsec, _hHbd, hHper, hHasym⟩ := deep_branch_bu d hup
  set W : Set ℂ := {w : ℂ | y' < w.im} with hWdef
  have hWopen : IsOpen W := by
    rw [hWdef]; exact isOpen_lt continuous_const Complex.continuous_im
  have hWmem : ∀ w : ℂ, w ∈ W ↔ y' < w.im := by
    intro w; rw [hWdef]; exact Iff.rfl
  have hWpc : IsPreconnected W := by
    rw [hWdef]; exact (convex_halfSpace_im_gt y').isPreconnected
  have hWBu : W ⊆ Bu := by
    intro w hw
    exact hup (by have h := (hWmem w).mp hw; show η < w.im; linarith)
  -- a deep base point of `Bu` and its lift
  set y₀ : ℂ := ((y' + 1 : ℝ) : ℂ) * I with hy₀def
  have hy₀im : y₀.im = y' + 1 := by rw [hy₀def]; simp [Complex.mul_im]
  have hy₀W : y₀ ∈ W := (hWmem y₀).mpr (by rw [hy₀im]; linarith)
  have hy₀Bu : y₀ ∈ Bu := hWBu hy₀W
  have hy₀deep : y' < y₀.im := (hWmem y₀).mp hy₀W
  have hx₀Bu : H y₀ ∈ Bu := (hHsec y₀ hy₀deep).1
  have hEy₀ : d.E (H y₀) = y₀ := (hHsec y₀ hy₀deep).2
  -- the global holomorphic section of `E` over `Bu`
  obtain ⟨σ, hσdiff, hσy₀, hσsec⟩ :=
    Work.L62.lift_section hBuO hE_diff hBuO hBuS hcovBu hy₀Bu hx₀Bu hEy₀
  -- `σ` agrees with the deep branch `H` on the deep half-plane `W`
  have hσH : ∀ w ∈ W, σ w = H w :=
    Work.L62.section_unique hBuO hWopen hWpc hWBu hE_diff (hσdiff.mono hWBu) hHdiff
      (fun y hy => hσsec y (hWBu hy)) (fun y hy => hHsec y ((hWmem y).mp hy)) hy₀W hσy₀
  -- `Bu` is preconnected (it is simply connected)
  have hBu_pc : IsPreconnected Bu := by
    have h : IsPreconnected (Set.univ : Set Bu) := preconnectedSpace_iff_univ.mp inferInstance
    have h2 := h.image (Subtype.val : Bu → ℂ) continuous_subtype_val.continuousOn
    rwa [Set.image_univ, Subtype.range_val] at h2
  -- `T`-equivariance of `σ`, by uniqueness of sections over `Bu`
  have hσ1_diff : DifferentiableOn ℂ (fun y => σ (y + 1) - 1) Bu :=
    (hσdiff.comp (differentiableOn_id.add_const 1) (fun y hy => (hBuT y).mp hy)).sub_const 1
  have hσ1_sec : ∀ y ∈ Bu, (fun y => σ (y + 1) - 1) y ∈ Bu ∧ d.E ((fun y => σ (y + 1) - 1) y) = y := by
    intro y hy
    have hy1 : y + 1 ∈ Bu := (hBuT y).mp hy
    have hsy1 : σ (y + 1) ∈ Bu := (hσsec (y + 1) hy1).1
    have hE1 : d.E (σ (y + 1)) = y + 1 := (hσsec (y + 1) hy1).2
    have hmem : σ (y + 1) - 1 ∈ Bu := (hBuT (σ (y + 1) - 1)).mpr (by simpa using hsy1)
    refine ⟨hmem, ?_⟩
    have hcanon := hE_one (σ (y + 1) - 1) hmem
    rw [sub_add_cancel, hE1] at hcanon
    exact (add_right_cancel hcanon).symm
  have hagree : (fun y => σ (y + 1) - 1) y₀ = σ y₀ := by
    have hy₀1W : y₀ + 1 ∈ W := by
      rw [hWmem] at hy₀W ⊢
      simpa using hy₀W
    change σ (y₀ + 1) - 1 = σ y₀
    rw [hσH (y₀ + 1) hy₀1W, hσH y₀ hy₀W, hHper y₀ hy₀deep]
    ring
  have hTeq : ∀ y ∈ Bu, σ (y + 1) = σ y + 1 := by
    have hEq := Work.L62.section_unique hBuO hBuO hBu_pc (fun _ h => h) hE_diff
      hσ1_diff hσdiff hσ1_sec hσsec hy₀Bu hagree
    intro y hy
    exact sub_eq_iff_eq_add.mp (hEq y hy)
  -- asymptotics: `σ = H` deep in the upper half-plane, where `H w - w → 0`
  have hasym : ∀ ε > 0, ∃ R : ℝ, ∀ w : ℂ, R < w.im → ‖σ w - w‖ < ε := by
    intro ε hε
    obtain ⟨R, hR⟩ := hHasym ε hε
    refine ⟨max R y', fun w hw => ?_⟩
    have hwW : w ∈ W := (hWmem w).mpr (lt_of_le_of_lt (le_max_right R y') hw)
    rw [hσH w hwW]
    exact hR w (lt_of_le_of_lt (le_max_left R y') hw)
  exact ⟨σ, hσdiff, hσsec, hTeq, tendsto_upperEnd_of_forall_im hasym⟩

end

end Work.Horn
