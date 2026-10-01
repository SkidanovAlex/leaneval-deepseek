import Mathlib
import Submission.Work.LinnikAreas.sum_mul_exp_neg_le_of_count
import Submission.Work.LinnikAreas.pairCountHeight_dom
import Submission.Work.LinnikAreas.siegelRestHigh
import Submission.Work.LinnikAreas.boxMaxZero

/-!
# `Work.SiegelAbsorb.windowMassRegion` — Abel summation on one `λ`-window

A finite set `S` of zero-pairs of level `q`, all of height `|Im ρ|·𝓛 ≤ H·𝓛`, none of them the
exceptional pair, whose `λ = (1 - Re ρ)·𝓛` all lie in a window `[Λ, L]` with `Λ > 0`, and a
height-count hypothesis `pairCountHeight χ₁ β₁ t (H·𝓛) ≤ C·e^{ct}·H^{3/2}` valid for
`0 < t ≤ L`: then the exponentially weighted multiplicity sum over `S` is at most
`C·H^{3/2}·e^{c}·e^{(c-a₀)Λ}/(1 - e^{c-a₀})`.

This is `Work.LinnikAreas.sum_mul_exp_neg_le_of_count` fed by
`Work.LinnikAreas.pairCountHeight_dom`; it isolates the composition so that the two windows of
`Work.SiegelAbsorb.windowMassFree2` (below `θ·𝓛` and above it) can be handled separately. -/

namespace Work.SiegelAbsorb

open scoped Classical BigOperators

/-- **Abel summation on one window.** -/
lemma windowMassRegion {q : ℕ} [NeZero q] (hq : 1 < q) (χ₁ : DirichletCharacter ℂ q) (β₁ : ℂ)
    {C H a₀ c Λ L : ℝ} (hC : 0 < C) (hH : 0 < H) (ha₀ : 0 < a₀) (hc0 : 0 ≤ c) (hca₀ : c < a₀)
    (hΛ : 0 < Λ)
    (hcnt : ∀ t : ℝ, 0 < t → t ≤ L →
      Work.LinnikAreas.Siegel.pairCountHeight χ₁ β₁ t (H * Real.log (q : ℝ))
        ≤ C * Real.exp (c * t) * H ^ (3 / 2 : ℝ))
    (S : Finset (DirichletCharacter ℂ q × ℂ))
    (hzm : ∀ z ∈ S, Work.LinnikContract.zeroMult z.1 z.2 ≠ 0)
    (hexc : ∀ z ∈ S, ¬(z.1 = χ₁ ∧ z.2 = β₁))
    (him : ∀ z ∈ S, |z.2.im| * Real.log (q : ℝ) ≤ H * Real.log (q : ℝ))
    (hfloor : ∀ z ∈ S, Λ ≤ Work.LinnikContract.lamOf q z.2)
    (hlamL : ∀ z ∈ S, Work.LinnikContract.lamOf q z.2 ≤ L) :
    (∑ z ∈ S, (Work.LinnikContract.zeroMult z.1 z.2 : ℝ)
        * Real.exp (-a₀ * Work.LinnikContract.lamOf q z.2))
      ≤ C * H ^ (3 / 2 : ℝ) * Real.exp c * Real.exp ((c - a₀) * Λ)
          / (1 - Real.exp (c - a₀)) := by
  have hcount : ∀ t : ℝ, Λ ≤ t → t ≤ L →
      (∑ z ∈ S.filter (fun z => Work.LinnikContract.lamOf q z.2 ≤ t),
          (Work.LinnikContract.zeroMult z.1 z.2 : ℝ))
        ≤ C * H ^ (3 / 2 : ℝ) * Real.exp (c * t) := by
    intro t hΛt htL
    have htpos : 0 < t := lt_of_lt_of_le hΛ hΛt
    calc (∑ z ∈ S.filter (fun z => Work.LinnikContract.lamOf q z.2 ≤ t),
            (Work.LinnikContract.zeroMult z.1 z.2 : ℝ))
        ≤ Work.LinnikAreas.Siegel.pairCountHeight χ₁ β₁ t (H * Real.log (q : ℝ)) :=
          Work.LinnikAreas.pairCountHeight_dom hq χ₁ β₁ _
            (fun z hz => hzm z (Finset.mem_filter.mp hz).1)
            (fun z hz => (Finset.mem_filter.mp hz).2)
            (fun z hz => him z (Finset.mem_filter.mp hz).1)
            (fun z hz => hexc z (Finset.mem_filter.mp hz).1)
      _ ≤ C * Real.exp (c * t) * H ^ (3 / 2 : ℝ) := hcnt t htpos htL
      _ = C * H ^ (3 / 2 : ℝ) * Real.exp (c * t) := by ring
  exact Work.LinnikAreas.sum_mul_exp_neg_le_of_count (S := S)
    (m := fun z : DirichletCharacter ℂ q × ℂ => (Work.LinnikContract.zeroMult z.1 z.2 : ℝ))
    (lam := fun z : DirichletCharacter ℂ q × ℂ => Work.LinnikContract.lamOf q z.2)
    (a₀ := a₀) (Λ := Λ) (L := L) (D := C) (lam₁ := H ^ (3 / 2 : ℝ)) (c := c)
    ha₀ hc0 hca₀ hC hΛ (Real.rpow_pos_of_pos hH _) (fun z _ => Nat.cast_nonneg _)
    hfloor hlamL hcount

end Work.SiegelAbsorb
