import Mathlib
import Submission.Work.ShafarevichKoch.sqrtField_kSupported_iff
import Submission.Work.ShafarevichKoch.VTwo_eq_VTwoUnramified_sup_neg_one_Kc

/-!
# `Work.ShafarevichKoch.sqrtField_ne_kSupported_iff_neg_mem_VTwoUnramified`

**The `κ`-map criterion in the sharp form**: for `x ∈ V_∅ = VTwo Kc`,

  `K_∅(√x) ≠ K_∅  ↔  -x ∈ V^{unr}`,

i.e. the Kummer extension `K_∅(√x)/K_∅` is non-trivial exactly when `-x` is a square in the
maximal unramified pro-`2` extension `K_∅ = kSupported Kc 2 ∅`.

Since `Kc(√-1)/Kc` is ramified, `-1` is not a square in `K_∅`; a single element of `V_∅` therefore
has exactly one of `x`, `-x` unramified (`sqrtField_eq_kSupported_or`), which is the elementary
content of the `κ`-route of the Shafarevich--Koch chapter (README §32/§33).

## Proof

* `⟹`: `sqrtField_eq_kSupported_or` says that for `x ∈ V_∅` at least one of `K_∅(√x) = K_∅`,
  `K_∅(√-x) = K_∅` holds; non-triviality of the first forces the second, and
  `mem_VTwoUnramified_kEmpty_iff_sqrtField_eq` converts it into `-x ∈ V^{unr}`.
* `⟸`: a nontriviality contradiction.  If also `K_∅(√x) = K_∅` then `x ∈ V^{unr}` as well, so
  `V^{unr}` being a subgroup contains `(-x) * x⁻¹ = -1`, contradicting
  `neg_one_not_mem_VTwoUnramified_Kc`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

noncomputable section

namespace Work.ShafarevichKoch

open Work.ClassFieldTower

theorem sqrtField_ne_kSupported_iff_neg_mem_VTwoUnramified
    (x : Work.ClassFieldTower.Kcˣ) (hx : x ∈ Work.ShafarevichKoch.VTwo Work.ClassFieldTower.Kc) :
    (Work.ShafarevichKoch.sqrtField ((x : Work.ClassFieldTower.Kcˣ) : Work.ClassFieldTower.Kc) ≠
        Work.ShafarevichKoch.kSupported Work.ClassFieldTower.Kc 2 (∅ : Finset ℕ)) ↔
      (-(x : Work.ClassFieldTower.Kcˣ) : Work.ClassFieldTower.Kcˣ) ∈
        Work.ShafarevichKoch.VTwoUnramified Work.ClassFieldTower.Kc
          (Work.ShafarevichKoch.kEmptyMaximalProP Work.ClassFieldTower.Kc) := by
  constructor
  · intro hne
    rcases sqrtField_eq_kSupported_or x hx with h | h
    · exact absurd h hne
    · exact (mem_VTwoUnramified_kEmpty_iff_sqrtField_eq (-(x : Kcˣ))).mpr h
  · intro hmem heq
    have hxmem : x ∈ VTwoUnramified Kc (kEmptyMaximalProP Kc) :=
      (mem_VTwoUnramified_kEmpty_iff_sqrtField_eq x).mpr heq
    have hneg : (-1 : Kcˣ) ∈ VTwoUnramified Kc (kEmptyMaximalProP Kc) := by
      have h1 : (-(x : Kcˣ)) * x⁻¹ = (-1 : Kcˣ) := by rw [neg_mul, mul_inv_cancel]
      rw [← h1]
      exact mul_mem hmem (inv_mem hxmem)
    exact neg_one_not_mem_VTwoUnramified_Kc (kEmptyMaximalProP Kc) hneg

end Work.ShafarevichKoch
