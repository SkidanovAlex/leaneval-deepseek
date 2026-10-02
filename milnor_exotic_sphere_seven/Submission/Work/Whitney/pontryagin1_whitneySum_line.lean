import Mathlib
import Submission.Work.Whitney.Basic
import Submission.Work.Whitney.Cup
import Submission.Work.Whitney.chernClass_whitneySum_top
import Submission.Work.Whitney.pontryagin1_line
import Submission.Work.Whitney.conjComplexification
import Submission.Work.Whitney.complexificationCore_whitneySumR
import Submission.Work.Thom.chernClass_eq_zero_of_lt
import Submission.Work.Thom.manifoldP1

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-!
# Additivity of `p₁` for real line bundles (an unconditional instance of deliverable item 3)

`Work.Thom.pontryagin1` is the first Pontryagin class in the normalisation `p₁(E) = -c₂(E ⊗_ℝ ℂ)`.
For two real **line** bundles `E`, `F` the complexified pair has ranks `(1,1)`, so the Whitney sum
formula in degree `2` is the *top* degree and is available unconditionally
(`Work.Whitney.chernClass_whitneySum_top`, i.e. `(T)`).  This gives the sharp form of the additivity

  `2 • p₁(E ⊕ F) = 2 • (p₁E + p₁F)`

in this smallest case; the factor `2` is forced (see `README.md`, ADDENDUM W3.4: the integral
identity fails in general, and here `p₁E = p₁F = 0` while `p₁(E⊕F) = -c₁E_ℂ ⌣ c₁F_ℂ` is a 2-torsion
class which need not vanish).

The two ingredients are `(T)` and the fact that **odd Chern classes of a complexified real bundle
are 2-torsion** (`Work.Whitney.chernClass_complexification_add_self`).
-/

namespace Work.Whitney

open Work.TangentClasses Work.Thom

noncomputable section

variable {B : Type} [TopologicalSpace B]

/-! ## Bilinearity of the graded cup product -/

/-- **The graded cup product is additive in its first argument.** -/
theorem cupChern_add_left (a b : ℕ) (x x' : Coh ℤ (2 * a) B) (y : Coh ℤ (2 * b) B) :
    cupChern a b (x + x') y = cupChern a b x y + cupChern a b x' y := by
  rw [cupChern_def, cupChern_def, cupChern_def]
  rw [Work.Cohomology.cupH'_add_left]
  exact (Work.Thom.cohTransportLM (Nat.mul_add 2 a b).symm).map_add _ _

/-- **The graded cup product vanishes on `0` in its first argument.** -/
theorem cupChern_zero_left (a b : ℕ) (y : Coh ℤ (2 * b) B) :
    cupChern a b (0 : Coh ℤ (2 * a) B) y = 0 := by
  rw [cupChern_def]
  rw [Work.Cohomology.cupH'_zero_left]
  exact (Work.Thom.cohTransportLM (Nat.mul_add 2 a b).symm).map_zero

/-! ## `p₁` of a real line bundle vanishes -/

/-- **The first Pontryagin class of a real line bundle vanishes**: `p₁(E) = -c₂(E ⊗_ℝ ℂ)` and
`E ⊗_ℝ ℂ` has complex rank `1`. -/
theorem pontryagin1_line_eq_zero {ι : Type} [Fintype ι]
    (E : VectorBundleCore ℝ B (EuclideanSpace ℝ (Fin 1)) ι) :
    pontryagin1 E = 0 := by
  rw [pontryagin1_def]
  have h : chernClass 1 2 (complexificationCore E) = 0 :=
    chernClass_eq_zero_of_lt (complexificationCore E) (by norm_num)
  rw [h, neg_zero]

/-! ## The additivity in the ranks `(1,1)` -/

/-- **Additivity of `p₁` for real line bundles** (`2 • p₁(E⊕F) = 2 • (p₁E + p₁F)`).

Both `p₁E` and `p₁F` vanish, so the claim is `2 • p₁(E⊕F) = 0`; the sum `E ⊕ F` complexifies to the
direct sum of two complex line bundles, whose second Chern class is the cup product of the two first
Chern classes by `(T)` — and each of those is 2-torsion because it is the first Chern class of the
complexification of a *real* bundle. -/
theorem two_smul_pontryagin1_whitneySumR_line {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
    (E : VectorBundleCore ℝ B (EuclideanSpace ℝ (Fin 1)) ι₁)
    (F : VectorBundleCore ℝ B (EuclideanSpace ℝ (Fin 1)) ι₂) :
    (2 : ℤ) • pontryagin1 (whitneySumR E F)
      = (2 : ℤ) • (pontryagin1 E + pontryagin1 F) := by
  have hx : chernClass 1 1 (complexificationCore E)
      + chernClass 1 1 (complexificationCore E) = 0 :=
    chernClass_complexification_add_self (B := B) (k := 1) (j := 1) (by decide) E
  have h2 : (2 : ℤ) • cupChern 1 1 (chernClass 1 1 (complexificationCore E))
      (chernClass 1 1 (complexificationCore F)) = 0 := by
    rw [show (2 : ℤ) • cupChern 1 1 (chernClass 1 1 (complexificationCore E))
          (chernClass 1 1 (complexificationCore F))
        = cupChern 1 1 (chernClass 1 1 (complexificationCore E)
            + chernClass 1 1 (complexificationCore E))
          (chernClass 1 1 (complexificationCore F)) from by
      rw [cupChern_add_left]
      exact two_zsmul _]
    rw [hx, cupChern_zero_left]
  rw [pontryagin1_line_eq_zero E, pontryagin1_line_eq_zero F, add_zero]
  rw [pontryagin1_def, complexificationCore_whitneySumR]
  rw [Work.Whitney.chernClass_whitneySum_top (complexificationCore E) (complexificationCore F)]
  -- goal: `2 • -(z) = 2 • 0` with `z = cupChern 1 1 (c₁E_ℂ) (c₁F_ℂ)`; reduce both sides additively
  have hz : cupChern 1 1 (chernClass 1 1 (complexificationCore E))
      (chernClass 1 1 (complexificationCore F))
      + cupChern 1 1 (chernClass 1 1 (complexificationCore E))
        (chernClass 1 1 (complexificationCore F)) = 0 := by
    rw [← two_zsmul]
    exact h2
  rw [two_zsmul, two_zsmul]
  simp only [add_zero]
  rw [← neg_add, hz, neg_zero]

end

end Work.Whitney
