import Mathlib
import Submission.Work.Interfaces.Fatou

/-!
# FATOU continuity (`Work.FatouCH`): geometric scaffolding

Shishikura's region `Qreg b₁ b₂` is the complement of (at most) two closed right cones: for a vertex
`a ∈ b₁` the bad set is the leftward cone `K₁ a = {Re (z-a) + |Im (z-a)| ≤ 0}`, for `b ∈ b₂` it is the
rightward cone `K₂ b = {Re (z-b) ≥ |Im (z-b)|}`.

This file collects the explicit numerical data used by the Koebe-chain argument for
`MandelDim.FatouContinuity`:

* `spineRe b₁ b₂` — a real number `m` such that the whole vertical line `{m + it : t ∈ ℝ}` lies in
  `Qreg b₁ b₂` with *uniformly* positive safe radius,
* `srad b₁ b₂ z` — an explicit lower bound for the distance of `z` to the complement of
  `Qreg b₁ b₂`.
-/

namespace Work.FatouCH

open Set Metric Complex
open scoped Topology

noncomputable section

/-- The vertical "spine" height of `Qreg b₁ b₂`: an explicit real number `m` with `a.re < m` for
`a ∈ b₁` and `m < b.re` for `b ∈ b₂`. -/
def spineRe (b₁ b₂ : Option ℂ) : ℝ :=
  match b₁, b₂ with
  | some a, some b => (a.re + b.re) / 2
  | some a, none => a.re + 2
  | none, some b => b.re - 2
  | none, none => 0

/-- Explicit lower bound for the distance of `z` to the complement of `Qreg b₁ b₂`.  For a vertex
`a ∈ b₁` we use `(Re (z-a) + |Im (z-a)|)/2` (a lower bound for the distance to the leftward cone),
for `b ∈ b₂` the analogous `(|Im (z-b)| - Re (z-b))/2`.  When a vertex is omitted the corresponding
term is dropped; when both are omitted the region is all of `ℂ` and we use `1 + ‖z‖`. -/
def srad (b₁ b₂ : Option ℂ) (z : ℂ) : ℝ :=
  match b₁, b₂ with
  | none, none => 1 + ‖z‖
  | none, some b => (1 / 2) * (|(z - b).im| - (z - b).re)
  | some a, none => (1 / 2) * ((z - a).re + |(z - a).im|)
  | some a, some b =>
      min ((1 / 2) * ((z - a).re + |(z - a).im|)) ((1 / 2) * (|(z - b).im| - (z - b).re))


/-- `srad` is continuous in `z`. -/
lemma continuous_srad (b₁ b₂ : Option ℂ) : Continuous (srad b₁ b₂) := by
  rcases b₁ with _ | a <;> rcases b₂ with _ | b
  · change Continuous (fun z : ℂ => 1 + ‖z‖); fun_prop
  · change Continuous (fun z : ℂ => (1 / 2) * (|(z - b).im| - (z - b).re)); fun_prop
  · change Continuous (fun z : ℂ => (1 / 2) * ((z - a).re + |(z - a).im|)); fun_prop
  · change Continuous (fun z : ℂ =>
      min ((1 / 2) * ((z - a).re + |(z - a).im|))
        ((1 / 2) * (|(z - b).im| - (z - b).re)))
    fun_prop

/-- The safe radius is positive on the region. -/
lemma srad_pos_of_mem {b₁ b₂ : Option ℂ} {z : ℂ} (hz : z ∈ MandelDim.Qreg b₁ b₂) :
    0 < srad b₁ b₂ z := by
  rcases b₁ with _ | a <;> rcases b₂ with _ | b
  · change 0 < 1 + ‖z‖; positivity
  · have h := hz.2 b (by simp)
    change 0 < (1 / 2) * (|(z - b).im| - (z - b).re)
    linarith
  · have h := hz.1 a (by simp)
    change 0 < (1 / 2) * ((z - a).re + |(z - a).im|)
    linarith
  · have h₁ := hz.1 a (by simp)
    have h₂ := hz.2 b (by simp)
    change 0 < min ((1 / 2) * ((z - a).re + |(z - a).im|))
        ((1 / 2) * (|(z - b).im| - (z - b).re))
    rw [lt_min_iff]
    exact ⟨by linarith, by linarith⟩

/-- A compact subset of the region has a positive uniform lower bound for `srad`. -/
lemma exists_min_srad_of_isCompact {b₁ b₂ : Option ℂ} {K : Set ℂ} (hKc : IsCompact K)
    (hKQ : K ⊆ MandelDim.Qreg b₁ b₂) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ K, δ ≤ srad b₁ b₂ z := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, one_pos, by simp⟩
  · obtain ⟨z₀, hz₀, hmin⟩ :=
      hKc.exists_isMinOn hne (continuous_srad b₁ b₂).continuousOn
    exact ⟨srad b₁ b₂ z₀, srad_pos_of_mem (hKQ hz₀), fun z hz => hmin hz⟩

end

end Work.FatouCH
