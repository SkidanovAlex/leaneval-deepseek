/-
# Section 8 of CKMRV re-plumbed onto the paper-faithful rigidity lemma

`Submission/Work/FunctionalEquations/Rigidity.lean` reduces the construction of the two
interpolation bases of the CKMRV paper to the uniqueness statement
`Work.FE.HomogeneousRigidity n c`, which drops the paper's moderate-growth hypothesis
`f ∈ 𝒫` and is consequently **false**:
`Submission/Work/Rigidity/Counterexample.lean` exhibits a nonzero holomorphic `f₄` of
weight `4`, annihilated by `(T − I)²` and by `S + I`, of size `o(1)` in the strip
`-1 ≤ Re τ ≤ 1`, but blowing up super-polynomially at the rational cusps.

This file re-runs the same reduction with the corrected, paper-faithful hypothesis
`Work.Rigidity.HomogeneousRigidityP n c` — the same conclusion, with the extra hypotheses
`∀ x, Work.Kernels.InP (fun τ : ℍ => g τ x)` and the same for `g̃` — and obtains the two
target theorems:

* `Work.Section8P.interpolationBasis_of_functionalEquations_of_rigidityP` : the `E₈` case
  (`HomogeneousRigidityP n 0` ⟹ `InterpolationBasis n 1`);
* `Work.Section8P.interpolationBasis_two_of_rigidityP_and_decay` : the Leech case
  (`HomogeneousRigidityP n 1` plus the strip decay of the generating functions ⟹
  `InterpolationBasis n 2`).

The two Section 8 halves are
`Work.Section8P.Section8ValueDataGen_of_rigidityP`
(`Submission/Work/Section8P/ValueData.lean`) and
`Work.Section8P.Section8FourierDataGen_of_rigidityP`
(`Submission/Work/Section8P/FourierData.lean`), and everything after the rigidity input —
Steps 1--2 (`Work.FE.expansionData_of_functionalEquations`), the delta pattern
(`Work.FE.interpolationBasis_of_data`, `…_gen`) and the `m = 1` vanishing under the decay
hypothesis (`Work.FE.ExpansionDataTwoOfDecay`) — is imported unchanged.

## Main results

* `Work.Section8P.section8DataGen_of_rigidityP` : the Section 8 data (value normalisations
  and Fourier-transform relations) from `HomogeneousRigidityP n (k₀ - 1)`.
* `Work.Section8P.interpolationBasis_of_functionalEquations_of_rigidityP`
* `Work.Section8P.interpolationBasis_two_of_rigidityP_and_decay`
* `Work.Section8P.interpolationBasis_eight_of_functionalEquations`,
  `Work.Section8P.interpolationBasis_twentyfour_of_functionalEquations` : the two
  theorems with the rigidity input discharged by the *proved* instances
  `Work.Rigidity.homogeneousRigidityP_eight`, `…_twentyfour`
  (`Submission/Work/Rigidity/Assembly.lean`).
-/
import Mathlib
import Submission.Work.Rigidity.All
import Submission.Work.FunctionalEquations.All
import Submission.Work.Kernels.All
import Submission.Work.Section8P.InPExpansion
import Submission.Work.Section8P.ValueData
import Submission.Work.Section8P.FourierData

namespace Work.Section8P

open LeanEval.Analysis.CKMRVInterpolation Work.Core Work.FE Work.FunctionalEquations
open Filter Topology
open scoped FourierTransform SchwartzMap UpperHalfPlane

noncomputable section

/-- **Section 8 from the paper-faithful rigidity lemma.**  The value normalisations and
the Fourier-transform relations of Section 8 follow from
`Work.Rigidity.HomogeneousRigidityP n (k₀ - 1)` and the Fourier expansions of Steps 1--2
(the moderate-growth hypotheses of the rigidity lemma are discharged by the expansion data
through `Work.Section8P.InP_dirichletExpansion`). -/
theorem section8DataGen_of_rigidityP {n : ℕ} [NeZero n] {k₀ : ℕ} {c : ℝ} (hk : 1 ≤ k₀)
    (hc : (k₀ : ℝ) - 1 = c) (hR : Work.Rigidity.HomogeneousRigidityP n c)
    (S : FunctionalEquationSolution n) (basis : SampleIdx k₀ → RSch n)
    (hExp : ExpansionDataGen n k₀ S basis) :
    Section8DataGen n k₀ S basis :=
  section8DataGen_of (Section8ValueDataGen_of_rigidityP hk hc hR S basis hExp)
    (Section8FourierDataGen_of_rigidityP hk hc hR S basis hExp)

/-- The same, with the rigidity hypothesis already in the normalisation `(k₀ - 1)`. -/
theorem section8DataGen_of_rigidityP' {n : ℕ} [NeZero n] {k₀ : ℕ} (hk : 1 ≤ k₀)
    (hR : Work.Rigidity.HomogeneousRigidityP n ((k₀ : ℝ) - 1))
    (S : FunctionalEquationSolution n) (basis : SampleIdx k₀ → RSch n)
    (hExp : ExpansionDataGen n k₀ S basis) :
    Section8DataGen n k₀ S basis :=
  section8DataGen_of_rigidityP hk rfl hR S basis hExp

/-- **The `E₈` case.**  A solution of the functional equations, together with the paper's
uniqueness input at weight `4` (`c = 0`, with the moderate-growth hypothesis),
yields the interpolation basis starting at `m = 1`. -/
theorem interpolationBasis_of_functionalEquations_of_rigidityP {n : ℕ} [NeZero n]
    (hR : Work.Rigidity.HomogeneousRigidityP n 0) (S : FunctionalEquationSolution n) :
    Nonempty (Work.Core.InterpolationBasis n 1) := by
  obtain ⟨basis, hExp⟩ := expansionData_of_functionalEquations S
  exact interpolationBasis_of_data S basis hExp
    (section8DataGen_of_rigidityP (c := 0) (by norm_num) (by norm_num) hR S basis hExp)

/-- **The Leech case.**  If in addition the generating functions decay like
`o(e^{-2π Im τ})`, the `m = 1` coefficients vanish, the expansions start at `m = 2`, and
the paper's uniqueness input at weight `12` (`c = 1`, with the moderate-growth hypothesis)
yields the interpolation basis starting at `m = 2`. -/
theorem interpolationBasis_two_of_rigidityP_and_decay {n : ℕ} [NeZero n]
    (hR : Work.Rigidity.HomogeneousRigidityP n 1) (S : FunctionalEquationSolution n)
    (basis : SampleIdx 1 → RSch n) (hExp : ExpansionData n S basis)
    (hdec : TendsToZeroInStrip n 1 S.F) (hdecT : TendsToZeroInStrip n 1 S.Ftilde) :
    Nonempty (Work.Core.InterpolationBasis n 2) := by
  obtain ⟨basis₂, hExp₂⟩ := ExpansionDataTwoOfDecay S basis hExp hdec hdecT
  exact interpolationBasis_of_data_gen (by norm_num) S basis₂ hExp₂
    (section8DataGen_of_rigidityP (c := 1) (by norm_num) (by norm_num) hR S basis₂ hExp₂)

/-- **The general-`k₀` form.**  Steps 1--2 together with the paper-faithful uniqueness
input at the matching decay exponent produce the interpolation basis starting at `k₀`
(`k₀ = 1` is the `E₈` normalisation, `k₀ = 2` the Leech one). -/
theorem interpolationBasis_of_dataGen_of_rigidityP {n : ℕ} [NeZero n] {k₀ : ℕ} (hk : 1 ≤ k₀)
    (hR : Work.Rigidity.HomogeneousRigidityP n ((k₀ : ℝ) - 1))
    (S : FunctionalEquationSolution n) (basis : SampleIdx k₀ → RSch n)
    (hExp : ExpansionDataGen n k₀ S basis) :
    Nonempty (Work.Core.InterpolationBasis n k₀) :=
  interpolationBasis_of_data_gen hk S basis hExp
    (section8DataGen_of_rigidityP hk rfl hR S basis hExp)

/-- The same with the decay exponent named: `c` must be `k₀ - 1`. -/
theorem interpolationBasis_of_dataGen_of_rigidityP_of_c {n : ℕ} [NeZero n] {k₀ : ℕ} {c : ℝ}
    (hk : 1 ≤ k₀) (hc : (k₀ : ℝ) - 1 = c) (hR : Work.Rigidity.HomogeneousRigidityP n c)
    (S : FunctionalEquationSolution n) (basis : SampleIdx k₀ → RSch n)
    (hExp : ExpansionDataGen n k₀ S basis) :
    Nonempty (Work.Core.InterpolationBasis n k₀) :=
  interpolationBasis_of_data_gen hk S basis hExp
    (section8DataGen_of_rigidityP hk hc hR S basis hExp)

/-! ## The Section 8 data in the `k₀ = 1` normalisation used by the interpolation basis -/

/-- The value normalisations at `k₀ = 1` (the `Work.FE.Section8ValueData` normalisation). -/
theorem Section8ValueData_of_rigidityP {n : ℕ} [NeZero n] {S : FunctionalEquationSolution n}
    (hR : Work.Rigidity.HomogeneousRigidityP n 0) (basis : SampleIdx 1 → RSch n)
    (hExp : ExpansionData n S basis) : Section8ValueData n S basis :=
  Section8ValueDataGen_of_rigidityP (k₀ := 1) (by norm_num) (by norm_num) hR S basis hExp

/-- The Fourier-transform relations at `k₀ = 1` (the `Work.FE.Section8FourierData`
normalisation). -/
theorem Section8FourierData_of_rigidityP {n : ℕ} [NeZero n] {S : FunctionalEquationSolution n}
    (hR : Work.Rigidity.HomogeneousRigidityP n 0) (basis : SampleIdx 1 → RSch n)
    (hExp : ExpansionData n S basis) : Section8FourierData n S basis :=
  Section8FourierDataGen_of_rigidityP (k₀ := 1) (by norm_num) (by norm_num) hR S basis hExp

/-- The Section 8 data in the normalisation consumed by `Work.FE.interpolationBasis_of_data`. -/
theorem Section8Data_of_rigidityP {n : ℕ} [NeZero n] {S : FunctionalEquationSolution n}
    (hR : Work.Rigidity.HomogeneousRigidityP n 0) (basis : SampleIdx 1 → RSch n)
    (hExp : ExpansionData n S basis) : Section8Data n S basis :=
  section8DataGen_of_rigidityP (k₀ := 1) (c := 0) (by norm_num) (by norm_num) hR S basis hExp

/-! ## The two theorems with the rigidity input discharged -/

/-- **The `E₈` interpolation basis from hypotheses (i)--(v) alone.**  The rigidity input is
the proved `Work.Rigidity.homogeneousRigidityP_eight`. -/
theorem interpolationBasis_eight_of_functionalEquations (S : FunctionalEquationSolution 8) :
    Nonempty (Work.Core.InterpolationBasis 8 1) :=
  interpolationBasis_of_functionalEquations_of_rigidityP
    Work.Rigidity.homogeneousRigidityP_eight S

/-- **The Leech interpolation basis from hypotheses (i)--(v) plus the strip decay.**  The
rigidity input is the proved `Work.Rigidity.homogeneousRigidityP_twentyfour`. -/
theorem interpolationBasis_twentyfour_of_functionalEquations (S : FunctionalEquationSolution 24)
    (basis : SampleIdx 1 → RSch 24) (hExp : ExpansionData 24 S basis)
    (hdec : TendsToZeroInStrip 24 1 S.F) (hdecT : TendsToZeroInStrip 24 1 S.Ftilde) :
    Nonempty (Work.Core.InterpolationBasis 24 2) :=
  interpolationBasis_two_of_rigidityP_and_decay
    Work.Rigidity.homogeneousRigidityP_twentyfour S basis hExp hdec hdecT

/-! ## Compatibility with the `𝒫`-free statements

`Work.Rigidity.HomogeneousRigidity ⟹ Work.Rigidity.HomogeneousRigidityP`
(`Work.Rigidity.homogeneousRigidityP_of_homogeneousRigidity`), so the corrected theorems
below subsume the statements of `Submission/Work/FunctionalEquations/Rigidity.lean`.  The
latter have an unprovable hypothesis (the `𝒫`-free form is false, see
`Submission/Work/Rigidity/Counterexample.lean`), but a caller who has it in hand (or who is
adapting existing code) gets the same conclusion. -/

/-- The statement of `Work.FE.interpolationBasis_of_functionalEquations_of_rigidity`,
recovered from the corrected theorem. -/
theorem interpolationBasis_of_functionalEquations_of_rigidity {n : ℕ} [NeZero n]
    (hR : HomogeneousRigidity n 0) (S : FunctionalEquationSolution n) :
    Nonempty (Work.Core.InterpolationBasis n 1) :=
  interpolationBasis_of_functionalEquations_of_rigidityP
    (Work.Rigidity.homogeneousRigidityP_of_homogeneousRigidity hR) S

/-- The statement of `Work.FE.interpolationBasis_two_of_rigidity_and_decay`, recovered from
the corrected theorem. -/
theorem interpolationBasis_two_of_rigidity_and_decay {n : ℕ} [NeZero n]
    (hR : HomogeneousRigidity n 1) (S : FunctionalEquationSolution n)
    (basis : SampleIdx 1 → RSch n) (hExp : ExpansionData n S basis)
    (hdec : TendsToZeroInStrip n 1 S.F) (hdecT : TendsToZeroInStrip n 1 S.Ftilde) :
    Nonempty (Work.Core.InterpolationBasis n 2) :=
  interpolationBasis_two_of_rigidityP_and_decay
    (Work.Rigidity.homogeneousRigidityP_of_homogeneousRigidity hR) S basis hExp hdec hdecT

end

end Work.Section8P
