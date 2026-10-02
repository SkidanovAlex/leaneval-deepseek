import Mathlib
import Submission.Work.RatHurewicz.ExcisionSetup
import Submission.Work.RatHurewicz.excisionDefs
import Submission.Work.RatHurewicz.Triad.Rule
import Submission.Work.RatHurewicz.Triad.Assembly
import Submission.Work.RatHurewicz.Triad.Stage
import Submission.Work.RatHurewicz.Triad.Convert
import Submission.Work.RatHurewicz.Triad.Translate
import Submission.Work.RatHurewicz.Triad.Urysohn
import Submission.Work.RatHurewicz.twoSetLabel

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.RatHurewicz

theorem triadCompression {X : Type} [TopologicalSpace X] {B C : Set X}
    (hB : IsOpen B) (hC : IsOpen C) (hBC : B ∪ C = Set.univ) (x₀ : ↥(B ∩ C)) (p q : ℕ)
    (hBc : ∀ d, 1 ≤ d → d ≤ p + 1 → CompressRelBd
      {y : ↥B | (y : X) ∈ B ∩ C}
      {y : ↥B | (y : X) ∈ B ∩ C ∧ (y : X) ∈ pathComponent (x₀ : X)} d)
    (hCc : ∀ d, 1 ≤ d → d ≤ q + 1 → CompressRelBd
      {y : ↥C | (y : X) ∈ B ∩ C}
      {y : ↥C | (y : X) ∈ B ∩ C ∧ (y : X) ∈ pathComponent (x₀ : X)} d)
    (hB0 : ∀ b : ↥B, (b : X) ∈ pathComponent (x₀ : X) →
      ∃ a : ↥(B ∩ C), Nonempty (Path ⟨a.1, a.2.1⟩ b))
    (hC0 : ∀ c : ↥C, (c : X) ∈ pathComponent (x₀ : X) →
      ∃ a : ↥(B ∩ C), Nonempty (Path ⟨a.1, a.2.2⟩ c)) :
    ∀ n, n ≤ p + q + 1 →
      CompressRel (homotopyFibre (setIncl C) ⟨x₀.1, x₀.2.2⟩)
        (Set.range (excisionComparison B C x₀)) n := by
  intro n hn
  exact Work.RatHurewicz.Triad.triadCompressionAux hB hC hBC x₀ p q hBc hCc hB0 hC0 hn

end Work.RatHurewicz
