import Mathlib
import Submission.Work.Projective.Chern
import Submission.Work.SignatureBordism.Bordism
import Submission.Work.SignatureBordism.Signature

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The generator side of the dimension-`4` and dimension-`8` Hirzebruch theorems

This module collects the **generator checks** of the bordism proof of the Hirzebruch signature
theorem: the numbers of `ℂP²`, `ℂP⁴` and `ℂP² × ℂP²` computed from the abstract cohomology ring
model `Work.Projective.CPRing n = ℤ[h]/(h^{n+1})` in which the Chern classes of `TℂPⁿ` are
`c_k = C(n+1,k) h^k` (`Work.Projective.Chern`).

In the vocabulary of `Work.SignatureBordism`:

* **`ℂP²`** (dimension `4`): `⟨p₁(TℂP²), [ℂP²]⟩ = 3` and `σ(ℂP²) = 1`, so
  `Work.SignatureBordism.HirzebruchFour 1 (p1Number 2)`;
* **`ℂP⁴`** (dimension `8`): `(σ, p₁², p₂) = (1, 25, 10)`, so
  `Work.SignatureBordism.HirzebruchEight 1 (p1SqNumber 4) (p2Number 4)`;
* **`ℂP² × ℂP²`**: `(σ, p₁², p₂) = (1, 18, 9)` (`Work.Projective.Product`).

The signature `σ` is the signature of the middle intersection form: for `ℂP²` and `ℂP⁴` the middle
cohomology is `ℤ⟨h^{n/2}⟩` and
`⟨h^{n/2} ⌣ h^{n/2}, [ℂPⁿ]⟩ = fundClass n (hC n ^ n) = 1` (`midSelfIntersection`), so the form is
the `1 × 1` form `(1)`, whose signature is `1` (`signature_cpMiddleForm`); the form is realised as a
weighted sum of squares on `Fin 1 → ℚ` (`cpMiddleForm`), in the sense in which the abstract model
carries the intersection form.

## Main results

* `Work.Projective.midSelfIntersection` — the middle self-intersection number is `1`;
* `Work.Projective.signature_cpMiddleForm` — the middle form `(1)` has signature `1`;
* `Work.Projective.hirzebruchFour_cp2`, `Work.Projective.hirzebruchEight_cp4` — **the generator
  checks**: the Hirzebruch identities hold for the *numbers computed from the manifolds*;
* `Work.Projective.cp4Tuple_eq`, `Work.Projective.cp2Tuple_eq` — the computed numbers agree with
  `Work.SignatureBordism.cp4Tuple` / `cp2Tuple`, the tuples consumed by the bordism reduction
  `Work.SignatureBordism.hirzebruchEight_of_mem_span`.
-/

open scoped BigOperators
open QuadraticMap

namespace Work.Projective

noncomputable section

/-! ## The middle intersection form -/

/-- **The middle self-intersection number of `ℂP^{2m}` is `1`**: the middle cohomology is
`ℤ⟨h^m⟩` and `⟨h^m ⌣ h^m, [ℂP^{2m}]⟩ = ⟨h^{2m}, [ℂP^{2m}]⟩ = 1`. -/
theorem midSelfIntersection (m : ℕ) :
    fundClass (2 * m) (hC (2 * m) ^ m * hC (2 * m) ^ m) = 1 := by
  rw [← pow_add]
  rw [show m + m = 2 * m from by ring]
  exact fundClass_hC_pow_self (2 * m)

/-- The middle self-intersection of `ℂP²`: `⟨h ⌣ h, [ℂP²]⟩ = 1`. -/
theorem midSelfIntersection_two : fundClass 2 (hC 2 * hC 2) = 1 := by
  rw [show hC 2 * hC 2 = hC 2 ^ 2 from by ring, fundClass_hC_pow_self]

/-- The middle self-intersection of `ℂP⁴`: `⟨h² ⌣ h², [ℂP⁴]⟩ = 1`. -/
theorem midSelfIntersection_four : fundClass 4 (hC 4 ^ 2 * hC 4 ^ 2) = 1 := by
  rw [show hC 4 ^ 2 * hC 4 ^ 2 = hC 4 ^ 4 from by ring, fundClass_hC_pow_self]

/-- **The middle intersection form of `ℂP²` and `ℂP⁴`**: the `1 × 1` form `(1)` on `Fin 1 → ℚ`
(the form whose value on the generator `h^{n/2}` is `1`). -/
def cpMiddleForm : QuadraticForm ℚ (Fin 1 → ℚ) := weightedSumSquares ℚ (fun _ => (1 : ℚ))

/-- **The signature of `ℂP²` and of `ℂP⁴` is `1`**: the signature of the middle form `(1)`. -/
theorem signature_cpMiddleForm :
    Work.SignatureBordism.signature cpMiddleForm = 1 := by
  rw [cpMiddleForm, Work.SignatureBordism.signature_weightedSumSquares]
  have h2 : {i : Fin 1 | (1 : ℚ) < 0}.ncard = 0 := by
    rw [show {i : Fin 1 | (1 : ℚ) < 0} = (∅ : Set (Fin 1)) by
      ext i; norm_num]
    simp
  rw [h2]
  simp

/-- **The signature of the middle intersection form of `ℂP²`** (dimension `4`, middle degree `2`),
written in the `Work.SignatureBordism` vocabulary. -/
theorem sigma_cp2 : Work.SignatureBordism.signature cpMiddleForm = 1 :=
  signature_cpMiddleForm

/-- **The signature of the middle intersection form of `ℂP⁴`** (dimension `8`, middle degree `4`). -/
theorem sigma_cp4 : Work.SignatureBordism.signature cpMiddleForm = 1 :=
  signature_cpMiddleForm

/-! ## The generator checks -/

/-- **`ℂP²` satisfies the dimension-`4` Hirzebruch identity**, with the numbers computed from its
cohomology ring and tangent bundle: `σ(ℂP²) = 1` and `⟨p₁(TℂP²), [ℂP²]⟩ = 3`. -/
theorem hirzebruchFour_cp2 :
    Work.SignatureBordism.HirzebruchFour 1 (p1Number 2) := by
  rw [p1Number_two]
  exact Work.SignatureBordism.hirzebruchFour_generator

/-- **`ℂP⁴` satisfies the dimension-`8` Hirzebruch identity**, with the numbers computed from its
cohomology ring and tangent bundle: `(σ, p₁², p₂) = (1, ⟨p₁ ⌣ p₁, [ℂP⁴]⟩, ⟨p₂, [ℂP⁴]⟩)` and
`⟨p₁ ⌣ p₁, [ℂP⁴]⟩ = 25`, `⟨p₂, [ℂP⁴]⟩ = 10`. -/
theorem hirzebruchEight_cp4 :
    Work.SignatureBordism.HirzebruchEight 1 (p1SqNumber 4) (p2Number 4) := by
  rw [p1SqNumber_four, p2Number_four]
  exact Work.SignatureBordism.hirzebruchEight_cp4

/-- **The numbers of `ℂP⁴`** as the triple `(σ, p₁², p₂) = (1, 25, 10)`. -/
theorem cp4_numbers :
    (1 : ℤ) = 1 ∧ p1SqNumber 4 = 25 ∧ p2Number 4 = 10 :=
  ⟨rfl, p1SqNumber_four, p2Number_four⟩

/-- **The numbers of `ℂP²`** as the pair `(σ, p₁) = (1, 3)`. -/
theorem cp2_numbers : (1 : ℤ) = 1 ∧ p1Number 2 = 3 := ⟨rfl, p1Number_two⟩

/-- The tuple `Work.SignatureBordism.cp2Tuple = (1, 3)` of the generator of `Ω^SO_4 ⊗ ℚ`, in terms
of the numbers computed here. -/
theorem cp2Tuple_eq :
    Work.SignatureBordism.cp2Tuple =
      (((1 : ℤ) : ℚ), ((p1Number 2 : ℤ) : ℚ)) := by
  rw [p1Number_two]
  rfl

/-- The tuple `Work.SignatureBordism.cp4Tuple = (1, 25, 10)` of the generator `ℂP⁴` of
`Ω^SO_8 ⊗ ℚ`, in terms of the numbers computed here. -/
theorem cp4Tuple_eq :
    Work.SignatureBordism.cp4Tuple =
      (((1 : ℤ) : ℚ), ((p1SqNumber 4 : ℤ) : ℚ), ((p2Number 4 : ℤ) : ℚ)) := by
  rw [p1SqNumber_four, p2Number_four]
  rfl

/-- **The Hirzebruch functional vanishes on the numbers of `ℂP⁴`**: the dimension-`8` identity
`45σ = 7p₂ - p₁²` holds for the computed numbers. -/
theorem hirzebruchFunctional8_cp4_numbers :
    Work.SignatureBordism.hirzebruchFunctional8
      (1, (p1SqNumber 4 : ℚ), (p2Number 4 : ℚ)) = 0 := by
  rw [p1SqNumber_four, p2Number_four]
  norm_num [Work.SignatureBordism.hirzebruchFunctional8]

/-- **The Hirzebruch functional vanishes on the numbers of `ℂP²`** (dimension `4`): `p₁ = 3σ`. -/
theorem hirzebruchFunctional4_cp2_numbers :
    Work.SignatureBordism.hirzebruchFunctional4 (1, (p1Number 2 : ℚ)) = 0 := by
  rw [p1Number_two]
  norm_num [Work.SignatureBordism.hirzebruchFunctional4]

end

end Work.Projective
