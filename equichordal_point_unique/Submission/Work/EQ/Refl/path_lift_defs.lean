import Mathlib
import Submission.Work.EQ.DefsCore
import Submission.Work.EQ.H0_structure

/-! # Definitions and uniqueness for the path-lifting lemma

This module sets up the notion `HasLift` used by `Work.EQ.Refl.path_lift_component` and proves
the uniqueness of lifts (a `ψ₁`-lift of a path into `⁰H` on a connected interval is determined by
its value at a single point), which is the key input of the "closedness" half of the path-lifting
argument. -/

namespace Work.EQ.Refl

open Filter _root_.Topology Set Metric

noncomputable section

/-- `γ` lifts to a continuous path in `H0 a h` on `[0,s]`, starting at `p`. -/
def HasLift (a : ℝ) (h : ℂ → ℂ) (p : ChainData) (γ : ℝ → ℂ) (s : ℝ) : Prop :=
  ∃ G : ℝ → ChainData, ContinuousOn G (Set.Icc 0 s) ∧ G 0 = p ∧
    ∀ t ∈ Set.Icc 0 s, G t ∈ H0 a h ∧ (G t).2.1 = γ t

/-- **Uniqueness of `ψ₁`-lifts into `⁰H`.**  Two continuous lifts of the same path `γ`, both
landing in `H0` and agreeing at a point of the connected interval `[0,s]`, coincide there. -/
theorem H0_lift_unique {a : ℝ} {h : ℂ → ℂ} {p : ChainData} {γ : ℝ → ℂ} {s : ℝ}
    (hlo : IsLocalHomeomorph (fun q : H0 a h => (q : ChainData).2.1))
    (hs : s ∈ Set.Icc 0 1) {G₁ G₂ : ℝ → ChainData}
    (h₁ : ContinuousOn G₁ (Set.Icc 0 s))
    (hm₁ : ∀ t ∈ Set.Icc 0 s, G₁ t ∈ H0 a h ∧ (G₁ t).2.1 = γ t) (h₁0 : G₁ 0 = p)
    (h₂ : ContinuousOn G₂ (Set.Icc 0 s))
    (hm₂ : ∀ t ∈ Set.Icc 0 s, G₂ t ∈ H0 a h ∧ (G₂ t).2.1 = γ t) (h₂0 : G₂ 0 = p) :
    ∀ t ∈ Set.Icc 0 s, G₁ t = G₂ t := by
  have h0mem : (0 : ℝ) ∈ Set.Icc 0 s := ⟨le_rfl, hs.1⟩
  have hp₁ : G₁ 0 ∈ H0 a h := (hm₁ 0 h0mem).1
  have hp₂ : G₂ 0 ∈ H0 a h := (hm₂ 0 h0mem).1
  let g₁ : ℝ → H0 a h := fun t =>
    if ht : t ∈ Set.Icc 0 s then ⟨G₁ t, (hm₁ t ht).1⟩ else ⟨G₁ 0, hp₁⟩
  let g₂ : ℝ → H0 a h := fun t =>
    if ht : t ∈ Set.Icc 0 s then ⟨G₂ t, (hm₂ t ht).1⟩ else ⟨G₂ 0, hp₂⟩
  have hg₁val : ∀ t ∈ Set.Icc 0 s, (g₁ t : ChainData) = G₁ t := by
    intro t ht; simp only [g₁, dif_pos ht]
  have hg₂val : ∀ t ∈ Set.Icc 0 s, (g₂ t : ChainData) = G₂ t := by
    intro t ht; simp only [g₂, dif_pos ht]
  have hc₁ : ContinuousOn g₁ (Set.Icc 0 s) :=
    (IsInducing.continuousOn_iff IsInducing.subtypeVal).mpr
      (h₁.congr (fun t ht => (hg₁val t ht)))
  have hc₂ : ContinuousOn g₂ (Set.Icc 0 s) :=
    (IsInducing.continuousOn_iff IsInducing.subtypeVal).mpr
      (h₂.congr (fun t ht => (hg₂val t ht)))
  have heq : Set.EqOn ((fun q : H0 a h => (q : ChainData).2.1) ∘ g₁)
      ((fun q : H0 a h => (q : ChainData).2.1) ∘ g₂) (Set.Icc 0 s) := by
    intro t ht
    simp only [Function.comp_apply]
    rw [hg₁val t ht, hg₂val t ht]
    exact ((hm₁ t ht).2).trans ((hm₂ t ht).2).symm
  have hgc : IsPreconnected (Set.Icc 0 s) := isPreconnected_Icc
  have hagree : g₁ 0 = g₂ 0 := by
    apply Subtype.ext
    rw [hg₁val 0 h0mem, hg₂val 0 h0mem, h₁0, h₂0]
  have hEqOn := IsSeparatedMap.eqOn_of_comp_eqOn
    (p := fun q : H0 a h => (q : ChainData).2.1)
    (T2Space.isSeparatedMap (fun q : H0 a h => (q : ChainData).2.1))
    hlo.isLocallyInjective hgc hc₁ hc₂ heq h0mem hagree
  intro t ht
  have hgt : g₁ t = g₂ t := hEqOn ht
  rw [← hg₁val t ht, ← hg₂val t ht]
  exact congrArg Subtype.val hgt

/-- Restriction of a lift to a smaller interval. -/
theorem HasLift.mono {a : ℝ} {h : ℂ → ℂ} {p : ChainData} {γ : ℝ → ℂ} {s s' : ℝ}
    (hL : HasLift a h p γ s) (hss' : s' ≤ s) : HasLift a h p γ s' := by
  obtain ⟨G, hcont, h0, hm⟩ := hL
  exact ⟨G, hcont.mono (Set.Icc_subset_Icc_right hss'), h0,
    fun t ht => hm t (Set.Icc_subset_Icc_right hss' ht)⟩

end

end Work.EQ.Refl
