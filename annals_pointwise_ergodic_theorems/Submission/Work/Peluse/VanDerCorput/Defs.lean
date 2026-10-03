import Mathlib
import Submission.Work.Peluse.Basic

/-!
# Auxiliary definitions for the van der Corput inequality (Peluse, Lemma 4.1)

The zero extension `zext I g` of a function `g : ℤ → ℂ` off a finset `I ⊆ ℤ`.  This is the
device that turns the *filtered* sums of Peluse's Lemma 4.1 into sums over all of `ℤ`, so that
the change of variables `y ↦ y + h` in the van der Corput argument becomes a translation.
-/

namespace Work.Peluse.VanDerCorput

open scoped BigOperators

noncomputable section

/-- The zero extension of `g` off the finset `I`: `zext I g z = g z` for `z ∈ I` and `0` for
`z ∉ I`. -/
def zext (I : Finset ℤ) (g : ℤ → ℂ) : ℤ → ℂ := fun z => if z ∈ I then g z else 0

lemma zext_of_mem {I : Finset ℤ} {g : ℤ → ℂ} {z : ℤ} (hz : z ∈ I) : zext I g z = g z := by
  simp [zext, hz]

lemma zext_of_notMem {I : Finset ℤ} {g : ℤ → ℂ} {z : ℤ} (hz : z ∉ I) : zext I g z = 0 := by
  simp [zext, hz]

end

end Work.Peluse.VanDerCorput
