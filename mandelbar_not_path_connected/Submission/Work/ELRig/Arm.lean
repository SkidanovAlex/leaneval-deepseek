/-
# ELRig — the arms of the tripod and the cut points of the nest at `b₂`

Two consequences of the input structures `TripodSides` (T8) and `B2Data` that the rigidity
argument (R-f) uses:

* `B2Data.subset_arm_of`: a preconnected subset of `K c` avoiding the tripod curve lies in one of
  the three arms;
* `B2Data.cut_mem_of`: the **cut point crossing lemma** — a preconnected subset of `K c` inside an
  arm, meeting the nest `Δ n` and leaving its closure, contains the cut point `cut Z n` of that
  arm (`frontier (Δ n) ∩ K c ∩ armZ = {cut Z n}`).
-/
import Submission.Work.ELRig.Sides
import Submission.Work.ELRig.Inputs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

set_option linter.unusedVariables false

noncomputable section

namespace Work.EL

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-- **A preconnected subset of `K c` avoiding the tripod curve lies in one of the three arms.** -/
theorem B2Data.subset_arm_of {c : ℂ} {φ : ℂ → ℂ} {hN : DynB c φ} {z₁ : ℂ}
    (tr : B2Data hN z₁) {S : Set ℂ} (hconn : IsPreconnected S)
    (hav : S ⊆ (tripodCurve hN tr.b₂)ᶜ) :
    S ⊆ armOf tr.tripod ArmIdx.A ∨ S ⊆ armOf tr.tripod ArmIdx.B ∨
      S ⊆ armOf tr.tripod ArmIdx.C := by
  rcases tr.tripod.subset_of_preconnected hconn hav with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

/-- **The cut point crossing lemma.**  A preconnected subset of `K c` inside an arm of the tripod
which meets the nest `Δ n` and leaves its closure contains the cut point `cut Z n` of that arm. -/
theorem B2Data.cut_mem_of {c : ℂ} {φ : ℂ → ℂ} {hN : DynB c φ} {z₁ : ℂ}
    (tr : B2Data hN z₁) {Z : ArmIdx} {n : ℕ} {S : Set ℂ} (hS : S ⊆ K c)
    (hconn : IsPreconnected S) (harm : S ⊆ armOf tr.tripod Z)
    (hΔ : ∃ z ∈ S, z ∈ tr.Δ n) (hout : ∃ z ∈ S, z ∉ closure (tr.Δ n)) :
    tr.cut Z n ∈ S := by
  obtain ⟨xin, hxinS, hxinΔ⟩ := hΔ
  obtain ⟨xout, hxoutS, hxoutc⟩ := hout
  obtain ⟨z, hzS, hzfr⟩ := meets_frontier_of (tr.isOpen_Δ n) hconn hxinS hxinΔ hxoutS hxoutc
  have hzmem : z ∈ frontier (tr.Δ n) ∩ K c ∩ armOf tr.tripod Z :=
    ⟨⟨hzfr, hS hzS⟩, harm hzS⟩
  rw [tr.cut_unique Z n] at hzmem
  exact (Set.mem_singleton_iff.mp hzmem) ▸ hzS

end Work.EL
