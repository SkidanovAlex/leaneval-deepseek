import Mathlib
import Submission.Work.Horn.basic
import Submission.Work.Horn.gholo
import Submission.Work.L62.lift_section
import Submission.Work.L62.section_unique_on
import Submission.Work.L62.branch_unique
import Submission.Work.L62.model_deep_branch
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Horn.deep_branch_bu

namespace Work.Horn

open Complex Filter Topology Metric
open scoped Topology

noncomputable section

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

variable {f₀ : ℂ → ℂ} {D₀ : Set ℂ}

/-- The parabolic basin is contained in the domain of `f₀`. -/
theorem basin_subset_D₀ : MandelDim.ParabolicBasin f₀ D₀ ⊆ D₀ := by
  intro z hz
  obtain ⟨U, hU, hmap, hconv⟩ := hz
  have hzU : z ∈ U := mem_of_mem_nhds hU
  have h0 := hmap 0
  exact (by simpa using h0 hzU : z ∈ D₀)

/-- The lifted horn map is `T`-equivariant on every set contained in `DE`. -/
theorem E_add_one_of_subset_DE {D : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    (hD : D ⊆ d.DE) : ∀ w ∈ D, d.E (w + 1) = d.E w + 1 := by
  intro w hw
  have hwDE : w ∈ d.DE := hD hw
  rw [MandelDim.ParabData.mem_DE] at hwDE
  have hw1 : w + 1 ∈ d.Dφ := (d.succ_iff w hwDE.1).mpr (basin_subset_D₀ hwDE.2)
  simp only [MandelDim.ParabData.E]
  rw [d.φ_abel w hwDE.1 hw1, d.Φ_abel (d.φ w) hwDE.2]

theorem top_section_exists {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀) (Bu : Set ℂ)
    (η : ℝ) (v : ℂ) (hη : 0 < η) (hBuO : IsOpen Bu) (hBuS : SimplyConnectedSpace Bu)
    (htBu : MandelDim.IsTInvariant Bu)
    (hup : {w : ℂ | η < w.im} ⊆ Bu) (hlow : ∀ w ∈ Bu, -η ≤ w.im)
    (hsub : Bu ⊆ d.DE)
    (hcov : IsCoveringMapOn (fun x : Bu => d.E x) {y | ∀ k : ℤ, y ≠ v + k})
    (hnoV : ∀ k : ℤ, v + k ∉ Bu)
    (hinf : ∀ y : ℂ, (MandelDim.piExp '' {w : ℂ | w ∈ Bu ∧ d.E w = y}).Infinite) :
    ∃ s : ℂ → ℂ, DifferentiableOn ℂ s Bu ∧ (∀ y ∈ Bu, s y ∈ Bu ∧ d.E (s y) = y) ∧
      (∀ y ∈ Bu, s (y + 1) = s y + 1) ∧
      (∀ ε > 0, ∃ R : ℝ, ∀ y ∈ Bu, R < y.im → ‖s y - y‖ < ε) := by
  -- `E = Φ ∘ φ` is holomorphic on `Bu`
  have hE_diff : DifferentiableOn ℂ d.E Bu :=
    d.Φ_holo.comp (d.φ_holo.mono fun w hw => (hsub hw).1) fun w hw => (hsub hw).2
  -- `E` is `T`-equivariant on `Bu`
  have hE_one : ∀ w ∈ Bu, d.E (w + 1) = d.E w + 1 := E_add_one_of_subset_DE d hsub
  -- the covering over `Bu`
  have hcovBu : IsCoveringMapOn (fun z : Bu => d.E z) Bu :=
    hcov.mono fun y hy k h => hnoV k (h ▸ hy)
  -- the deep branch
  obtain ⟨y', hηy', H, hHdiff, hHsec, _, hHper, hHasym⟩ := deep_branch_bu d hup
  set W : Set ℂ := {w : ℂ | y' < Complex.im w} with hWdef
  have hWmem : ∀ w : ℂ, w ∈ W ↔ y' < Complex.im w := by
    intro w; rw [hWdef]; rfl
  have hWopen : IsOpen W := by rw [hWdef]; exact isOpen_lt continuous_const Complex.continuous_im
  have hWBu : W ⊆ Bu := fun w hw => hup (by have := (hWmem w).mp hw; show η < Complex.im w; linarith)
  -- a deep base point
  set y₀ : ℂ := ((y' + 1 : ℝ) : ℂ) * Complex.I with hy₀def
  have hy₀im : Complex.im y₀ = y' + 1 := by
    rw [hy₀def]; simp [Complex.mul_im]
  have hy₀W : y₀ ∈ W := (hWmem y₀).mpr (by rw [hy₀im]; linarith)
  have hy₀Bu : y₀ ∈ Bu := hup (by show η < Complex.im y₀; rw [hy₀im]; linarith)
  have hx₀Bu : H y₀ ∈ Bu := (hHsec y₀ ((hWmem y₀).mp hy₀W)).1
  have hE_x₀ : d.E (H y₀) = y₀ := (hHsec y₀ ((hWmem y₀).mp hy₀W)).2
  -- the global section
  obtain ⟨s, hsdiff, hs0, hssec⟩ :=
    Work.L62.lift_section hBuO hE_diff hBuO hBuS hcovBu hy₀Bu hx₀Bu hE_x₀
  -- `s` agrees with the deep branch on the deep half-plane (uniqueness of lifts)
  have hWconv : Convex ℝ W := by rw [hWdef]; exact convex_halfSpace_im_gt y'
  haveI : ContractibleSpace ↥W := hWconv.contractibleSpace ⟨y₀, hy₀W⟩
  haveI : SimplyConnectedSpace ↥W := SimplyConnectedSpace.ofContractible ↥W
  haveI : LocallyPathConnectedSpace ↥W := hWopen.locallyPathConnectedSpace
  have hcovW : IsCoveringMapOn (fun z : Bu => d.E z) W := hcovBu.mono hWBu
  have hcs : Continuous fun w : ↥W => s w.1 :=
    hsdiff.continuousOn.comp_continuous continuous_subtype_val (fun w => hWBu w.2)
  have hcH : Continuous fun w : ↥W => H w.1 :=
    hHdiff.continuousOn.comp_continuous continuous_subtype_val (fun w => w.2)
  have huniq := hcovW.existsUnique_continuousMap_lifts
      (⟨Subtype.val, continuous_subtype_val⟩ : C(↥W, ℂ))
      (a₀ := (⟨y₀, hy₀W⟩ : ↥W)) (e₀ := (⟨H y₀, hx₀Bu⟩ : ↥Bu))
      (by simpa using hE_x₀) (fun a => a.2)
  obtain ⟨F, hFmem, hFuniq⟩ := huniq
  let G₁ : C(↥W, ↥Bu) := ⟨fun w => ⟨s w.1, (hssec w.1 (hWBu w.2)).1⟩,
    Continuous.subtype_mk hcs (fun w => (hssec w.1 (hWBu w.2)).1)⟩
  let G₂ : C(↥W, ↥Bu) := ⟨fun w => ⟨H w.1, (hHsec w.1 ((hWmem w.1).mp w.2)).1⟩,
    Continuous.subtype_mk hcH (fun w => (hHsec w.1 ((hWmem w.1).mp w.2)).1)⟩
  have hG₁mem : G₁ (⟨y₀, hy₀W⟩ : ↥W) = (⟨H y₀, hx₀Bu⟩ : ↥Bu) ∧
      (fun z : ↥Bu => d.E z) ∘ ⇑G₁ = ⇑(⟨Subtype.val, continuous_subtype_val⟩ : C(↥W, ℂ)) := by
    refine ⟨?_, ?_⟩
    · ext
      exact hs0
    · funext w
      exact (hssec w.1 (hWBu w.2)).2
  have hG₂mem : G₂ (⟨y₀, hy₀W⟩ : ↥W) = (⟨H y₀, hx₀Bu⟩ : ↥Bu) ∧
      (fun z : ↥Bu => d.E z) ∘ ⇑G₂ = ⇑(⟨Subtype.val, continuous_subtype_val⟩ : C(↥W, ℂ)) := by
    refine ⟨?_, ?_⟩
    · ext
      rfl
    · funext w
      exact (hHsec w.1 ((hWmem w.1).mp w.2)).2
  have hGG : G₁ = G₂ := (hFuniq G₁ hG₁mem).trans (hFuniq G₂ hG₂mem).symm
  have hsH : ∀ w ∈ W, s w = H w := by
    intro w hw
    have h := congrArg (fun (f : C(↥W, ↥Bu)) => (f (⟨w, hw⟩ : ↥W) : ↥Bu)) hGG
    exact congrArg (fun z : ↥Bu => (z : ℂ)) h
  -- `s (y+1) - 1` is again a section, and the two agree on the deep half-plane
  have hs1_diff : DifferentiableOn ℂ (fun y => s (y + 1) - 1) Bu :=
    (hsdiff.comp (differentiableOn_id.add_const 1) (fun y hy => (htBu y).mp hy)).sub_const 1
  have hs1_agree : ∀ w ∈ W, s (w + 1) - 1 = s w := by
    intro w hw
    have hw' : y' < Complex.im w := (hWmem w).mp hw
    have hw1W : w + 1 ∈ W := (hWmem (w + 1)).mpr (by
      have : Complex.im (w + 1) = Complex.im w := by simp
      rw [this]; exact hw')
    rw [hsH (w + 1) hw1W, hsH w hw, hHper w hw']
    ring
  have hBu_pc : IsPreconnected Bu := by
    have h : IsPreconnected (Set.univ : Set Bu) := preconnectedSpace_iff_univ.mp inferInstance
    have h2 := h.image (Subtype.val : Bu → ℂ) continuous_subtype_val.continuousOn
    rwa [Set.image_univ, Subtype.range_val] at h2
  have hs_ana : AnalyticOnNhd ℂ s Bu := hsdiff.analyticOnNhd hBuO
  have hs1_ana : AnalyticOnNhd ℂ (fun y => s (y + 1) - 1) Bu := hs1_diff.analyticOnNhd hBuO
  have hev : (fun y : ℂ => s (y + 1) - 1) =ᶠ[𝓝 y₀] s :=
    Filter.eventually_of_mem (hWopen.mem_nhds hy₀W) (fun w hw => hs1_agree w hw)
  have hEqOn := hs1_ana.eqOn_of_preconnected_of_eventuallyEq hs_ana hBu_pc hy₀Bu hev
  refine ⟨s, hsdiff, hssec, ?_, ?_⟩
  · intro y hy
    exact (sub_eq_iff_eq_add).mp (hEqOn hy)
  · intro ε hε
    obtain ⟨R, hR⟩ := hHasym ε hε
    refine ⟨max R y', fun y hy hyR => ?_⟩
    have hyW : y ∈ W := (hWmem y).mpr (lt_of_le_of_lt (le_max_right R y') hyR)
    rw [hsH y hyW]
    exact hR y (lt_of_le_of_lt (le_max_left R y') hyR)

end

end Work.Horn
