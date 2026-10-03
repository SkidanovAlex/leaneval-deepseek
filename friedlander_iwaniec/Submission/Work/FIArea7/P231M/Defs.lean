import Mathlib
import Submission.Work.FIArea7.P231Defs

set_option autoImplicit false

namespace Work.FIArea7.P231M

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The primary *primitive* Gaussian integers of norm `≤ M` (a subset of the box `gBox M`). -/
def primDisc (M : ℕ) : Finset GaussianInt :=
  (Work.FIArea7.primaryDisc M).filter (fun w => IsCoprime w.re w.im)

/-- Restriction of a coefficient function to `primDisc M`. -/
def restrPrim (M : ℕ) (A : GaussianInt → ℂ) : GaussianInt → ℂ :=
  fun w => if w ∈ primDisc M then A w else 0

/-- Restriction of a coefficient function to `primaryDisc M`. -/
def restrDisc (M : ℕ) (A : GaussianInt → ℂ) : GaussianInt → ℂ :=
  fun w => if w ∈ Work.FIArea7.primaryDisc M then A w else 0

@[simp] lemma mem_primDisc {M : ℕ} {w : GaussianInt} :
    w ∈ primDisc M ↔ Work.FIPlan.IsPrimary w ∧ IsCoprime w.re w.im ∧ Work.FIPlan.gnorm w ≤ M := by
  rw [primDisc, Finset.mem_filter, Work.FIArea7.mem_primaryDisc]
  exact ⟨fun h => ⟨h.1.1, h.2, h.1.2⟩, fun h => ⟨⟨h.1, h.2.2⟩, h.2.1⟩⟩

end

end Work.FIArea7.P231M
