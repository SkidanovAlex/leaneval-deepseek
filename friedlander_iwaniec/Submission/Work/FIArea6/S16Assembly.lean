/-
# `Submission.Work.FIArea6.S16Assembly` — the §16 main-term bound

The wire from *FI* Lemma 16.2 (`Work.FITop4.Area5_6`) to the character sums `S_χ^k(β)` of the
(16.11) expansion: `chiOf (4d) χ` is an `IsCharMod4d` character of `ℤ[i]` (built directly from the
component lemmas of `Work.FIArea7.addChar_extends_charMod4d`), so `Area5_6` bounds every
`S_χ^k(β) = Σ_{z ∈ boxN} β z·χ(z)·(z/|z|)^k` that the expansion produces.
-/
import Mathlib
import Submission.Work.FIArea6.S16UDefs
import Submission.Work.FIArea7.addChar_extends_charMod4d

set_option autoImplicit false

namespace Work.FIArea6

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- **`chiOf (4d) χ` is a character to modulus `4d`** on `ℤ[i]` (`IsCharMod4d`), assembled from
the component laws of `Work.FIArea7.addChar_extends_charMod4d`. -/
theorem chiOf_isCharMod4d (d : ℕ) (hd : 1 ≤ d)
    (χ : AddChar (Additive (Work.FIArea7.GaussUnit (4 * d))) ℂ) :
    Work.FITop3.IsCharMod4d d (Work.FIArea7.chiOf (4 * d) χ) := by
  haveI hn : NeZero (4 * d) := ⟨by omega⟩
  haveI hf : Fact (1 < 4 * d) := ⟨by omega⟩
  exact ⟨Work.FIArea7.chiOf_one χ, fun z w => Work.FIArea7.chiOf_mul χ z w,
    fun z => Work.FIArea7.chiOf_norm_le χ z,
    fun z w hzw => Work.FIArea7.chiOf_periodic χ hzw,
    fun z hz => Work.FIArea7.chiOf_eq_zero_of_dvd χ hz⟩

end

end Work.FIArea6
