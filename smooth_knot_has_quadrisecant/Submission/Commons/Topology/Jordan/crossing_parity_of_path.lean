import Mathlib.Analysis.Calculus.Deriv.Shift
import Submission.Commons.Topology.Jordan.local_sides_of_transverse_curve

namespace Commons.Topology.Jordan

/-- A continuous path `ψ` on `[0,1]` that meets a Jordan curve `γ` exactly once, transversally at
that point, has its two endpoints in different connected components of the complement of `γ`. -/
theorem crossing_parity_of_path
    (γ : ℝ → ℂ) (hγcont : Continuous γ) (hγper : Function.Periodic γ 1)
    (hγinj : Set.InjOn γ (Set.Ico (0:ℝ) 1))
    (hfront : ∀ y : ℂ, y ∈ (Set.range γ)ᶜ →
      frontier (connectedComponentIn (Set.range γ)ᶜ y) = Set.range γ)
    (hne : ∃ y : ℂ, y ∈ (Set.range γ)ᶜ ∧
      connectedComponentIn (Set.range γ)ᶜ y ≠ (Set.range γ)ᶜ)
    (t₀ : ℝ) (v : ℂ) (hv : v ≠ 0) (hγder : ContDiffAt ℝ 1 γ t₀) (hγv : deriv γ t₀ = v)
    (ψ : ℝ → ℂ) (hψcont : Continuous ψ) (hψ0 : ψ 0 ∉ Set.range γ) (hψ1 : ψ 1 ∉ Set.range γ)
    (s₀ : ℝ) (hs₀0 : 0 < s₀) (hs₀1 : s₀ < 1) (hmeet : ψ s₀ = γ t₀)
    (honly : ∀ s ∈ Set.Icc (0:ℝ) 1, ψ s ∈ Set.range γ → s = s₀)
    (w : ℂ) (hψder : HasDerivAt ψ w s₀) (hw : (w / v).im ≠ 0) :
    connectedComponentIn (Set.range γ)ᶜ (ψ 0) ≠
      connectedComponentIn (Set.range γ)ᶜ (ψ 1) := by
  -- Local transverse behaviour of the path `ψ (s₀ + ·)` through `γ t₀`.
  have hη : HasDerivAt (fun s : ℝ => ψ (s₀ + s)) w 0 := by
    have h2 : HasDerivAt ψ w (s₀ + 0) := by simpa using hψder
    exact HasDerivAt.comp_const_add s₀ 0 h2
  obtain ⟨ε, hεpos, hε⟩ :=
    local_sides_of_transverse_curve γ hγcont hγper hγinj hfront hne t₀ v hv hγder hγv
      (fun s : ℝ => ψ (s₀ + s)) (by simpa using hmeet) w hη hw
  -- A small positive `s` such that both `ψ (s₀ - s)` and `ψ (s₀ + s)` lie inside `[0,1]`.
  set s : ℝ := min ε (min s₀ (1 - s₀)) / 2 with hsdef
  have hspos : 0 < s := by
    rw [hsdef]
    have : 0 < min ε (min s₀ (1 - s₀)) := lt_min hεpos (lt_min hs₀0 (by linarith))
    linarith
  have hsltε : s < ε := by
    have hle : min ε (min s₀ (1 - s₀)) ≤ ε := min_le_left _ _
    rw [hsdef]; linarith
  have hslt_s₀ : s < s₀ := by
    have hle : min ε (min s₀ (1 - s₀)) ≤ s₀ :=
      le_trans (min_le_right _ _) (min_le_left _ _)
    rw [hsdef]; linarith
  have hslt_1ms₀ : s < 1 - s₀ := by
    have hle : min ε (min s₀ (1 - s₀)) ≤ 1 - s₀ :=
      le_trans (min_le_right _ _) (min_le_right _ _)
    rw [hsdef]; linarith
  have hleft_nonneg : 0 ≤ s₀ - s := by linarith
  have hright_le_one : s₀ + s ≤ 1 := by linarith
  -- `ψ 0` and `ψ (s₀ - s)` lie in the same component.
  have hT1pc : IsPreconnected (ψ '' Set.Icc (0:ℝ) (s₀ - s)) :=
    isPreconnected_Icc.image ψ hψcont.continuousOn
  have hT1sub : ψ '' Set.Icc (0:ℝ) (s₀ - s) ⊆ (Set.range γ)ᶜ := by
    rintro y ⟨x, hx, rfl⟩
    simp only [Set.mem_compl_iff, Set.mem_range, not_exists]
    intro t ht
    have hx01 : x ∈ Set.Icc (0:ℝ) 1 := ⟨hx.1, by linarith [hx.2, hslt_s₀]⟩
    have hxs : x = s₀ := honly x hx01 ⟨t, ht⟩
    linarith [hx.2, hspos, hxs]
  have h0mem : ψ 0 ∈ ψ '' Set.Icc (0:ℝ) (s₀ - s) := ⟨0, ⟨le_refl 0, hleft_nonneg⟩, rfl⟩
  have hsmem_left : ψ (s₀ - s) ∈ ψ '' Set.Icc (0:ℝ) (s₀ - s) :=
    ⟨s₀ - s, ⟨hleft_nonneg, le_refl _⟩, rfl⟩
  have hsub1 : ψ '' Set.Icc (0:ℝ) (s₀ - s) ⊆
      connectedComponentIn (Set.range γ)ᶜ (ψ 0) :=
    hT1pc.subset_connectedComponentIn h0mem hT1sub
  have hcomp1 : connectedComponentIn (Set.range γ)ᶜ (ψ 0) =
      connectedComponentIn (Set.range γ)ᶜ (ψ (s₀ - s)) :=
    connectedComponentIn_eq (hsub1 hsmem_left)
  -- `ψ 1` and `ψ (s₀ + s)` lie in the same component.
  have hT2pc : IsPreconnected (ψ '' Set.Icc (s₀ + s) 1) :=
    isPreconnected_Icc.image ψ hψcont.continuousOn
  have hT2sub : ψ '' Set.Icc (s₀ + s) 1 ⊆ (Set.range γ)ᶜ := by
    rintro y ⟨x, hx, rfl⟩
    simp only [Set.mem_compl_iff, Set.mem_range, not_exists]
    intro t ht
    have hx01 : x ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith [hx.1, hspos], hx.2⟩
    have hxs : x = s₀ := honly x hx01 ⟨t, ht⟩
    linarith [hx.1, hspos, hxs]
  have h1mem : ψ 1 ∈ ψ '' Set.Icc (s₀ + s) 1 := ⟨1, ⟨hright_le_one, le_refl 1⟩, rfl⟩
  have hsmem_right : ψ (s₀ + s) ∈ ψ '' Set.Icc (s₀ + s) 1 :=
    ⟨s₀ + s, ⟨le_refl _, hright_le_one⟩, rfl⟩
  have hsub2 : ψ '' Set.Icc (s₀ + s) 1 ⊆
      connectedComponentIn (Set.range γ)ᶜ (ψ 1) :=
    hT2pc.subset_connectedComponentIn h1mem hT2sub
  have hcomp2 : connectedComponentIn (Set.range γ)ᶜ (ψ 1) =
      connectedComponentIn (Set.range γ)ᶜ (ψ (s₀ + s)) :=
    connectedComponentIn_eq (hsub2 hsmem_right)
  -- The two nearby points on the path are in different components.
  have hloc := hε s hspos hsltε
  have hne' : connectedComponentIn (Set.range γ)ᶜ (ψ (s₀ + s)) ≠
      connectedComponentIn (Set.range γ)ᶜ (ψ (s₀ - s)) := by
    have := hloc.2.2
    simpa [sub_eq_add_neg, add_comm] using this
  intro h
  apply hne'
  rw [← hcomp2, ← h]
  exact hcomp1

end Commons.Topology.Jordan