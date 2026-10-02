import Mathlib
import Submission.Work.Whitney.ConjDet
import Submission.Work.Whitney.ConjTopology
import Submission.Work.Whitney.eulerClass_eq_of_realIso_det_pos
import Submission.Work.Gen.eulerClass_neg_of_realIso
import Submission.Work.Thom.chernClass

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-!
# The top Chern class of the conjugate bundle

The fibrewise conjugation is a **real** bundle isomorphism
`Work.Whitney.conjRealIso Z : realification Z ≅ realification Z̄` whose fibrewise determinant is
`(-1)^m` (`Work.Whitney.det_conjC`).  Since the top Chern class of a rank-`m` complex bundle is the
Euler class of its realification (`Work.Thom.chernClass_succ_top'`), the two orientation lemmas for
real bundle isomorphisms give the top degree of the sign rule:

* `Work.Whitney.chernClass_conjCore_top` — `c_m(Z̄) = (-1)^m c_m(Z)`,

using `Work.Whitney.eulerClass_eq_of_realIso_det_pos` when `m` is even (the gauge is then
orientation preserving) and `Work.Gen.eulerClass_neg_of_realIso` when `m` is odd.
-/

namespace Work.Whitney

open Work.TangentClasses Work.Thom

noncomputable section

variable {B : Type} [TopologicalSpace B] {ι : Type}

/-- **The conjugation as a real bundle isomorphism** `realification Z ≅ realification Z̄`: the
fibrewise map is `conjC`, whose real determinant is `(-1)^m`. -/
def conjRealIso {m : ℕ} (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) :
    Work.Thom.BundleIso (realification Z) (realification (conjCore Z)) where
  hom _ := conjC m
  inv _ := conjC m
  left_inv _ x := by
    show conjC m (conjC m x) = x
    exact conjC_involutive m x
  right_inv _ y := by
    show conjC m (conjC m y) = y
    exact conjC_involutive m y
  continuous_hom := continuous_conjRealTotalSpace Z
  continuous_inv := continuous_conjRealTotalSpace_symm Z

/-- **The top Chern class of the conjugate bundle**: `c_m(Z̄) = (-1)^m c_m(Z)`, for a complex bundle
`Z` of rank `m ≥ 1`. -/
theorem chernClass_conjCore_top {m : ℕ} (hm : 1 ≤ m) {B : Type} [TopologicalSpace B]
    {ι : Type} [Fintype ι] (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) :
    Work.Thom.chernClass m m (conjCore Z) = ((-1 : ℤ) ^ m) • Work.Thom.chernClass m m Z := by
  obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  have htop : ∀ (W : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m' + 1))) ι),
      Work.Thom.chernClass (m' + 1) (m' + 1) W
        = (Work.Thom.thomClassRank (m' + 1) (Nat.succ_le_succ (Nat.zero_le m')) W).eulerClass :=
    fun W => Work.Thom.chernClass_succ_top' W
  rw [htop (conjCore Z), htop Z]
  have hdet : ∀ b : B, LinearMap.det ((conjRealIso (Z := Z)).hom b) = (-1 : ℝ) ^ (m' + 1) :=
    fun b => det_conjC (m' + 1)
  rcases Nat.even_or_odd (m' + 1) with hev | hodd
  · have hpos : ∀ b : B, 0 < LinearMap.det ((conjRealIso (Z := Z)).hom b) := by
      intro b
      rw [hdet b, hev.neg_one_pow]
      norm_num
    rw [Work.Whitney.eulerClass_eq_of_realIso_det_pos (m := m' + 1)
      (Nat.succ_le_succ (Nat.zero_le m')) Z (conjCore Z) (conjRealIso Z) hpos,
      hev.neg_one_pow]
    simp
  · have hneg : ∀ b : B, LinearMap.det ((conjRealIso (Z := Z)).hom b) < 0 := by
      intro b
      rw [hdet b, hodd.neg_one_pow]
      norm_num
    rw [Work.Gen.eulerClass_neg_of_realIso (m := m' + 1)
      (Nat.succ_le_succ (Nat.zero_le m')) Z (conjCore Z) (conjRealIso Z) hneg,
      hodd.neg_one_pow]
    simp

/-- **The rank-one case of the sign rule**: for a complex line bundle `L`,
`c₁(L̄) = - c₁(L)`. -/
theorem chernClass_one_conjCore {B : Type} [TopologicalSpace B] {ι : Type} [Fintype ι]
    (L : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι) :
    Work.Thom.chernClass 1 1 (conjCore L) = - Work.Thom.chernClass 1 1 L := by
  rw [chernClass_conjCore_top (m := 1) le_rfl L]
  simp

end

end Work.Whitney
