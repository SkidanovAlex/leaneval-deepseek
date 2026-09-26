import Mathlib
import Submission.Commons.Topology.Jordan.crossing_lemma_rect
import Submission.Commons.Topology.Jordan.square_sets_top_bottom_continuum

open Set

namespace Commons.Topology.Jordan

/-- **A continuum joining the bottom and top edges of the square meets every left–right path.**

This is the *continuum* (not just path) form of Maehara's crossing lemma: it is the two-dimensional
Brouwer/Janiszewski statement that a connected compact set joining the two horizontal edges of a
square is a barrier for paths joining the two vertical edges. -/
theorem top_bottom_continuum_meets_left_right_path {C : Set ℂ}
    (hC : C ⊆ {z : ℂ | z.re ∈ Set.Icc (-1:ℝ) 1 ∧ z.im ∈ Set.Icc (-1:ℝ) 1})
    (hCpre : IsPreconnected C)
    (hCbot : (C ∩ {z : ℂ | z.im = -1}).Nonempty)
    (hCtop : (C ∩ {z : ℂ | z.im = 1}).Nonempty)
    {γ : C(Set.Icc (0:ℝ) 1, ℂ)}
    (hγ : ∀ t, γ t ∈ {z : ℂ | z.re ∈ Set.Icc (-1:ℝ) 1 ∧ z.im ∈ Set.Icc (-1:ℝ) 1})
    (hγ0 : (γ 0).re = -1) (hγ1 : (γ 1).re = 1) :
    ∃ t : Set.Icc (0:ℝ) 1, γ t ∈ C := by
  classical
  by_contra hcon
  push Not at hcon
  -- `K` is the compact image of the left–right path.
  set K : Set ℂ := Set.range γ with hK
  have hKcl : IsClosed K := by
    rw [hK]
    exact (isCompact_range γ.continuous).isClosed
  have hCK : ∀ z ∈ C, z ∉ K := by
    intro z hzC hzK
    rw [hK] at hzK
    obtain ⟨t, ht⟩ := hzK
    exact hcon t (ht ▸ hzC)
  -- points of `C` on the bottom and top edges
  obtain ⟨p, hpC, hpim⟩ := hCbot
  obtain ⟨q, hqC, hqim⟩ := hCtop
  -- join them inside the square while avoiding `K`, using local path connectedness
  have hLPC : LocallyPathConnectedSpace ↥Qsq :=
    LocallyPathConnectedSpace.of_convex convex_Qsq
  have hTpre : IsPreconnected (Subtype.val ⁻¹' C : Set ↥Qsq) :=
    isPreconnected_subtype_preimage hCpre hC
  have hUopen : IsOpen (Subtype.val ⁻¹' (Kᶜ) : Set ↥Qsq) :=
    hKcl.isOpen_compl.preimage continuous_subtype_val
  have hTU : (Subtype.val ⁻¹' C : Set ↥Qsq) ⊆ Subtype.val ⁻¹' (Kᶜ) := by
    intro x hx
    exact hCK x.1 hx
  have hpT : (⟨p, hC hpC⟩ : ↥Qsq) ∈ (Subtype.val ⁻¹' C : Set ↥Qsq) := hpC
  have hqT : (⟨q, hC hqC⟩ : ↥Qsq) ∈ (Subtype.val ⁻¹' C : Set ↥Qsq) := hqC
  have hJ : JoinedIn (Subtype.val ⁻¹' (Kᶜ) : Set ↥Qsq)
      (⟨p, hC hpC⟩ : ↥Qsq) (⟨q, hC hqC⟩ : ↥Qsq) :=
    IsPreconnected.joinedIn_of_isOpen_subset hTpre hUopen hTU hpT hqT
  -- the bottom-to-top path inside the square, avoiding `K`
  let β : C(Set.Icc (0:ℝ) 1, ℂ) :=
    ⟨fun t => ((hJ.somePath t : ↥Qsq) : ℂ),
      continuous_subtype_val.comp hJ.somePath.continuous⟩
  have hβ0 : β 0 = p := by
    change ((hJ.somePath (0 : Set.Icc (0:ℝ) 1) : ↥Qsq) : ℂ) = p
    rw [hJ.somePath.source]
  have hβ1 : β 1 = q := by
    change ((hJ.somePath (1 : Set.Icc (0:ℝ) 1) : ↥Qsq) : ℂ) = q
    rw [hJ.somePath.target]
  have hβK : ∀ t, β t ∉ K := by
    intro t
    change ((hJ.somePath t : ↥Qsq) : ℂ) ∉ K
    exact hJ.somePath_mem t
  -- reparametrise to maps on `ℝ` and apply the crossing lemma
  set ρ : ℝ → Set.Icc (0:ℝ) 1 := Set.projIcc 0 1 (by norm_num) with hρ
  have hρ0 : ρ (-1) = 0 := by apply Subtype.ext; simp [ρ]
  have hρ1 : ρ 1 = 1 := by apply Subtype.ext; simp [ρ]
  let H : C(ℝ, ℂ) := ⟨fun t => γ (ρ t), γ.continuous.comp continuous_projIcc⟩
  let V : C(ℝ, ℂ) := ⟨fun t => β (ρ t), β.continuous.comp continuous_projIcc⟩
  have hhmem : ∀ t : ℝ, t ∈ Set.Icc (-1:ℝ) 1 →
      (H t).re ∈ Set.Icc (-1:ℝ) 1 ∧ (H t).im ∈ Set.Icc (-1:ℝ) 1 := by
    intro t _
    exact hγ (ρ t)
  have hvmem : ∀ t : ℝ, t ∈ Set.Icc (-1:ℝ) 1 →
      (V t).re ∈ Set.Icc (-1:ℝ) 1 ∧ (V t).im ∈ Set.Icc (-1:ℝ) 1 := by
    intro t _
    exact (hJ.somePath (ρ t)).2
  have hH0 : (H (-1)).re = (-1:ℝ) := by
    change (γ (ρ (-1))).re = -1
    rw [hρ0]; exact hγ0
  have hH1 : (H 1).re = (1:ℝ) := by
    change (γ (ρ 1)).re = 1
    rw [hρ1]; exact hγ1
  have hV0 : (V (-1)).im = (-1:ℝ) := by
    change (β (ρ (-1))).im = -1
    rw [hρ0, hβ0]; exact hpim
  have hV1 : (V 1).im = (1:ℝ) := by
    change (β (ρ 1)).im = 1
    rw [hρ1, hβ1]; exact hqim
  obtain ⟨s, -, t, -, hst⟩ :=
    crossing_lemma_rect H V hhmem hvmem hH0 hH1 hV0 hV1
  -- contradiction: `γ (ρ s) ∈ K` but `β (ρ t) ∉ K`, and they are equal
  have hmemK : γ (ρ s) ∈ K := by rw [hK]; exact ⟨ρ s, rfl⟩
  have heq : γ (ρ s) = β (ρ t) := hst
  rw [heq] at hmemK
  exact hβK (ρ t) hmemK

end Commons.Topology.Jordan
