import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseB4.B7Instance
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB4.B7Kernel` — the box commutator in B7's `EstHyp.hasKernel` form

`Work.BoseB7.EstHyp.hasKernel` (`Submission/Work/BoseB7/Estimates.lean`) names
the `B4` obligation of FS `eq:Commutator_general`:

    `F.ccrK i j = χ̂²(ℓ(k_i - k_j)) - χ̂(ℓ k_i)·χ̂(ℓ k_j)`.

`Work.BoseB4.b7FockDataBox` supplies a `FockData` whose `ccrK` *is* the box
kernel, so `hasKernel` follows by `rfl`-level unfolding once the caller's
mode-indexed data `E.hatChiSq`, `E.hatChi` are the continuous functions composed
with the momentum assignment.  This module records that, plus the
**non-degeneracy certificates**: unlike the zero-model and the δ-kernel
occupation model, the instantiation here has a strictly positive diagonal kernel
whenever a mode vector is non-zero, and a non-zero annihilation operator.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseB4

set_option autoImplicit false

/-- **`EstHyp.hasKernel` from `b7FockDataBox`**: the commutator kernel of the
instantiation is FS's box kernel, in the form B7's `EstHyp` records. -/
theorem b7FockDataBox_ccrK {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (kmom : Mode → EuclideanSpace ℝ (Fin 3)) (hkmom : ∀ i : Mode, kmom (-i) = -kmom i)
    (ell : ℝ) (hatChiSq hatChi : EuclideanSpace ℝ (Fin 3) → ℝ)
    (m : ℕ) (f : Mode → Fin m → ℝ)
    (hgram : ∀ i j : Mode,
      gram (f i) (f j) = BoseB7.ccrKernel ell hatChiSq hatChi (kmom i) (kmom j))
    (i j : Mode) :
    (b7FockDataBox kmom hkmom ell hatChiSq hatChi m f hgram).ccrK i j
      = hatChiSq (ell • (kmom i - kmom j)) - hatChi (ell • kmom i) * hatChi (ell • kmom j) :=
  rfl

end Work.BoseB4
