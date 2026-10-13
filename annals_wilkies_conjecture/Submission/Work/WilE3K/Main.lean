/-
  annals_wilkies_conjecture, AREA E3K (`Submission.Work.WilE3K`): **the deliverable**.

  `Work.WilE3K.SepKhovanskiiET_of_E2` is the corrected separable Khovanskii bound for exp/tan
  chains (`Submission/Work/WilE3K/Defs.lean`, the frozen statement of the design file
  `sources/wilkiesE3E9/wilkies_E3E9_gaps.lean`) derived from the frozen `E2_khovanskii` and E2's
  Sard input.

  The derivation is the composition of the nodes of the design's §GAP 1 route:

  * K1 (`exists_lift`): lift each `tan` chain function to a coordinate `t_j` with the arctan graph
    equation `arctan t_j - ℓ_j(x) + k_j π = 0`; nondegeneracy and degrees are preserved.
  * K2 (`ET_step`, from `ET_sphere` + `ET_good_exists` + `ET_rolle_step` + `newData_degree`): one
    sphere-and-Rolle elimination step per `tan` coordinate for the lifted (`ETData`) systems,
    including the degree bookkeeping.
  * K3 (`ET_all_tight`, base case `ET_base` from `hE2`): induction on the number of `tan`
    coordinates; `ETB_le_poly` dominates the recursion bound by a polynomial in the degree sum.
  * `SepKhovanskiiET_of_parts`: the assembly (chain splitting bookkeeping, the degenerate case
    `n = 0`, and the passage from the ET bound to the frozen form).
-/
import Submission.Work.WilE3K.Elim
import Submission.Work.WilE3K.SepKhovanskiiET_of_parts
import Submission.Work.WilE3K.exists_lift
import Submission.Work.WilE3K.ET_all_tight
import Submission.Work.WilE3K.ETB_le_poly

set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open Classical Topology Filter
namespace Work.WilE3K
open WilkiesConjecture WilkiesDesign WilkiesDesign.E

/-- **The deliverable.**  The corrected separable Khovanskii bound for exp/tan chains, derived
from the frozen `E2_khovanskii` (`hE2`) and the density of regular values of a rectangular `C²` map
(`hSard`, E2's `regular_values_dense` input).

Proved and axiom-clean (`#print axioms` gives `[propext, Classical.choice, Quot.sound]`). -/
theorem SepKhovanskiiET_of_E2
    (hE2 : ∀ F : ℕ, ∃ p : Polynomial ℕ, ∀ (k r : ℕ) (c : EAChain k r)
      (f : Fin k → EAPoly k r) (s : Finset (Fin k → ℝ)), k + r ≤ F →
      (∀ x ∈ s, (∀ i, eaEval c (f i) x = 0) ∧
        (Matrix.of fun i j => eaEval c (eaD c j (f i)) x).det ≠ 0) →
      s.card ≤ p.eval (∑ i, atomDeg (f i)))
    (hSard : ∀ (m : ℕ) (G : (Fin (m + 1) → ℝ) → (Fin m → ℝ)), ContDiff ℝ 2 G →
      ∀ (y₀ : Fin m → ℝ) (ε : ℝ), 0 < ε → ∃ y : Fin m → ℝ, dist y y₀ < ε ∧
        ∀ z, G z = y → LinearIndependent ℝ (fun a => fderiv ℝ (fun w => G w a) z)) :
    ∀ F : ℕ, SepKhovanskiiET F :=
  SepKhovanskiiET_of_parts hE2 exists_lift ET_all_tight ETB_le_poly

end Work.WilE3K
