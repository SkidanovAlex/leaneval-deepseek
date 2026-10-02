import Mathlib
import Submission.Work.Thom.sumStableMain

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-!
# Stability of the Chern classes: the usable corollaries

`Work.Thom.chernClass_sumEps` (`Submission/Work/Thom/sumStableMain.lean`) is *stability* at the level
at which the Chern recursion is stated:

  `c_j(Z ⊕ ε¹) = c_j(Z)`   for `Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι`,

where `Z ⊕ ε¹` is presented by `Work.Thom.sumEps ι₀ Z` (`Z ⊕ ε¹` transported to the *standard*
fibre `ℂ^{m+1}` along `Work.Thom.prodFinEquiv`, so that `chernClass (m+1) j` applies to it).

This module records the two corollaries a caller needs:

* `Work.Thom.chernClass_eq_of_bundleIso_sumEps` — the **presentation-independent** form: if a bundle
  `W` of standard fibre `ℂ^{m+1}` is isomorphic to `sumEps ι₀ Z`, then `c_j(W) = c_j(Z)`.  This is
  how a caller applies stability to *their* presentation of `Z ⊕ ε¹` (for instance
  `bundleSum Z ε¹`, which is isomorphic to `sumEps ι₀ Z` by
  `Work.Thom.nonempty_bundleIso_sumEps`, or the complexification of a real sum).
* `Work.Thom.chernClass_sumEps_sumEps` — two trivial summands, by applying stability twice; the
  general `k` is the same induction (`c_j(Z ⊕ ε^k) = c_j(Z)`).
-/

namespace Work.Thom

open Work.TangentClasses

noncomputable section

variable {m : ℕ} {B : Type} [TopologicalSpace B] {ι : Type} {ι₀ : Type} [Inhabited ι₀]

/-- **Stability, presentation-independently**: a bundle of rank `m + 1` isomorphic to
`Z ⊕ ε¹` (presented in the standard fibre) has the Chern classes of `Z`. -/
theorem chernClass_eq_of_bundleIso_sumEps [Fintype ι] [Fintype ι₀]
    {ι' : Type} [Fintype ι']
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (W : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m + 1))) ι')
    (e : BundleIso W (sumEps ι₀ Z)) (j : ℕ) :
    chernClass (m + 1) j W = chernClass m j Z := by
  rw [chernClass_BundleIso (j := j) W (sumEps ι₀ Z) e]
  exact chernClass_sumEps Z j

/-- **Stability, twice**: `c_j(Z ⊕ ε¹ ⊕ ε¹) = c_j(Z)`. -/
theorem chernClass_sumEps_sumEps [Fintype ι] [Fintype ι₀] {ι₁ : Type} [Inhabited ι₁]
    [Fintype ι₁]
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (j : ℕ) :
    chernClass (m + 2) j (sumEps ι₁ (sumEps ι₀ Z)) = chernClass m j Z := by
  rw [chernClass_sumEps (sumEps ι₀ Z) j, chernClass_sumEps Z j]

/-- **The top Chern class of a bundle with a trivial summand vanishes**, in the standard-fibre
presentation: `c_{m+1}(Z ⊕ ε¹) = 0` (a nowhere-zero section, as in
`Work.Thom.chernClass_top_eq_zero_of_nowhereZeroSection`). -/
theorem chernClass_sumEps_top [Fintype ι] [Fintype ι₀]
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) :
    chernClass (m + 1) (m + 1) (sumEps ι₀ Z) = 0 :=
  chernClass_top_eq_zero_of_nowhereZeroSection (m := m + 1) (by omega) (sumEps ι₀ Z)
    ((subtypeMap (zeroComplement (realification (sumEps ι₀ Z)))).comp (sumSection ι₀ Z))
    (fun x => rfl) (fun x => sumPoint_ne_zero ι₀ Z x)

end

end Work.Thom
