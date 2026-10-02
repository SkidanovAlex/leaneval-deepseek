import Mathlib
import Submission.Work.Thom.chernClass

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-!
# The top Chern class vanishes in the presence of a nowhere-zero section

The top Chern class `c_m(V) ∈ H^{2m}(B;ℤ)` of a rank-`m` complex vector bundle is, by the
definition of the recursion (`Work.Thom.chernClass_succ_top'`), the Euler class of the
realification `V_ℝ` of `V`:

  `c_m(V) = e(V_ℝ)`,  `e(V_ℝ) = z^*(𝔱(V_ℝ)) ∈ H^{2m}(B;ℤ)`.

A continuous nowhere-zero section of `V_ℝ` is exactly a continuous section of `V` that never
vanishes, and the Euler class of an oriented real bundle admitting such a section is zero: the
image of the section lies in the complement `V_ℝ ∖ 0` of the zero section, over which the relative
Thom class restricts to zero, while the section is homotopic to the zero section through the
fibrewise rescaling.  This is the classical statement `e(V_ℝ) = 0`, i.e. the top Chern class is
the obstruction to a nowhere-zero section.

The two ingredients are thus the top equation of the recursion
(`Work.Thom.chernClass_succ_top'`) and the vanishing of the Euler class
(`Work.Thom.ThomClass.eulerClass_eq_zero_of_nowhereZeroSection`).
-/

namespace Work.Thom

open Work.TangentClasses

noncomputable section

variable {B : Type} [TopologicalSpace B] {ι : Type} [Fintype ι]

/-- **The top Chern class of a complex bundle with a nowhere-zero section is zero.**

Here `σ` is a continuous section of the realification `V_ℝ` of `V` (`(σ x).1 = x` for all `x`),
nowhere zero in the fibre (`(σ x).2 ≠ 0`).  The conclusion is `c_m(V) = 0` in `H^{2m}(B;ℤ)`.

The proof is a two-line reduction: write `m = k + 1` (so that `m ≥ 1` is the top index of the
recursion), identify `c_m(V)` with the Euler class `e(V_ℝ)` of the realification by the top equation
`Work.Thom.chernClass_succ_top'`, and apply the classical vanishing
`Work.Thom.ThomClass.eulerClass_eq_zero_of_nowhereZeroSection`. -/
theorem chernClass_top_eq_zero_of_nowhereZeroSection {m : ℕ} (hm : 1 ≤ m)
    {B : Type} [TopologicalSpace B] {ι : Type} [Fintype ι]
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (σ : C(B, (Work.Thom.realification Z).TotalSpace))
    (hσ : ∀ x, (σ x).1 = x) (hσ0 : ∀ x, (σ x).2 ≠ 0) :
    Work.Thom.chernClass m m Z = 0 := by
  -- `m = k + 1`, so that `m` is the top degree of the recursion.
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  -- The top equation of the recursion: `c_{k+1}` is the Euler class of the realification.
  rw [Work.Thom.chernClass_succ_top']
  -- A nowhere-zero section forces the Euler class to vanish.
  exact Work.Thom.ThomClass.eulerClass_eq_zero_of_nowhereZeroSection _ σ hσ hσ0

end

end Work.Thom
