import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The cardinality of `PSL(2, F)` over a field of characteristic two

For a finite field `F` of characteristic `2` the projective special linear group
`PSL(2, F) = SL(2, F) / Z(SL(2, F))` has cardinality `|F| (|F|² - 1)`.

The proof proceeds in three steps.

* The determinant `GL(2, F) → Fˣ` is surjective with kernel isomorphic to `SL(2, F)`, so
  `|GL(2, F)| = |Fˣ| · |SL(2, F)|`; together with the formula for `|GL(n, F)|` this gives
  `|SL(2, F)| = |F| (|F|² - 1)`.
* In characteristic two the only root of unity of order `2` in a field is `1`, so the center
  of `SL(2, F)` is trivial.
* Hence `|PSL(2, F)| = |SL(2, F)|`.
-/

open Matrix

namespace Commons.GroupTheory.SL2

/-- The special linear group is the kernel of the determinant homomorphism
`GL(n, R) → Rˣ`. -/
noncomputable def specialLinearGroupEquivKerDet {n : Type*} [DecidableEq n] [Fintype n]
    {R : Type*} [CommRing R] :
    Matrix.SpecialLinearGroup n R ≃
      MonoidHom.ker (Matrix.GeneralLinearGroup.det (n := n) (R := R)) where
  toFun g := ⟨Matrix.SpecialLinearGroup.toGL g,
    by rw [MonoidHom.mem_ker, Matrix.SpecialLinearGroup.coeToGL_det]⟩
  invFun x := ⟨(x : GL n R).val,
    by
      have hx : Matrix.GeneralLinearGroup.det (x : GL n R) = 1 :=
        (MonoidHom.mem_ker).mp x.property
      have := congrArg Units.val hx
      simpa using this⟩
  left_inv g := by
    refine Subtype.ext ?_
    rfl
  right_inv x := by
    refine Subtype.ext ?_
    exact Units.ext rfl

/-- In characteristic two the center of `SL(2, F)` is trivial. -/
lemma center_specialLinearGroup_two_eq_bot {F : Type*} [Field F] (hchar : CharP F 2) :
    Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro A hA
  obtain ⟨r, hr2, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  rw [Fintype.card_fin] at hr2
  have hr1 : r = 1 := CharTwo.sq_inj.mp (by rw [hr2, one_pow])
  refine Subtype.ext ?_
  rw [← hrA, hr1]
  simp

/-- The cardinality of `SL(2, F)` over a finite field `F`. -/
theorem card_specialLinearGroup_two {F : Type*} [Field F] [Fintype F] :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) =
      Nat.card F * (Nat.card F ^ 2 - 1) := by
  set q := Nat.card F with _hq
  have hunits : Nat.card Fˣ = q - 1 := by
    rw [Nat.card_units]
  have hGL : Nat.card (GL (Fin 2) F) = (q ^ 2 - 1) * (q ^ 2 - q) := by
    rw [Matrix.card_GL_field 2, Fin.prod_univ_two]
    have hFC : Fintype.card F = q := by rw [← Nat.card_eq_fintype_card]
    simp [hFC]
  have hker : Nat.card (MonoidHom.ker (Matrix.GeneralLinearGroup.det (n := Fin 2) (R := F)))
      = Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) :=
    (Nat.card_congr specialLinearGroupEquivKerDet).symm
  have hdet_surj : Function.Surjective
      (Matrix.GeneralLinearGroup.det (n := Fin 2) (R := F)) :=
    Matrix.GeneralLinearGroup.det_surjective
  have hrel : Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) * (q - 1) =
      Nat.card (GL (Fin 2) F) := by
    have h1 := Subgroup.card_mul_index
      (MonoidHom.ker (Matrix.GeneralLinearGroup.det (n := Fin 2) (R := F)))
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hdet_surj, Subgroup.card_top] at h1
    rw [← hunits, ← hker]
    exact h1
  have hq2 : 2 ≤ q := by
    have : 1 < Fintype.card F := Fintype.one_lt_card
    rw [← Nat.card_eq_fintype_card, _hq.symm] at this
    omega
  have hsub : q ^ 2 - q = q * (q - 1) := by
    rw [sq, Nat.mul_sub_left_distrib, mul_one]
  have key : Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) * (q - 1)
      = (q * (q ^ 2 - 1)) * (q - 1) := by
    rw [hrel, hGL, hsub]
    ring
  rw [Nat.mul_right_cancel (by omega : 0 < q - 1) key]

/-- The cardinality of `PSL(2, F)` over a finite field `F` of characteristic two. -/
theorem card_projectiveSpecialLinearGroup {F : Type*} [Field F] [Fintype F] (hchar : CharP F 2) :
    Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) =
      Nat.card F * (Nat.card F ^ 2 - 1) := by
  have hcenter := center_specialLinearGroup_two_eq_bot hchar
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F))
  rw [hcenter, Subgroup.card_bot, mul_one] at hcard
  change Nat.card (Matrix.SpecialLinearGroup (Fin 2) F ⧸
    Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) = _
  rw [hcenter, ← hcard]
  exact card_specialLinearGroup_two

end Commons.GroupTheory.SL2