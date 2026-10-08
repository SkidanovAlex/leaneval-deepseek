import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Data.Fintype.EquivFin

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Commons.LinearAlgebra.Matrix

/-- `|GL(2,q)| = (q²−1)(q²−q)` — a finite field has `q = |F|` elements. -/
private lemma card_GL2 {F : Type*} [Field F] [Fintype F] :
    Nat.card (GL (Fin 2) F) =
      ((Fintype.card F)^2 - 1) * ((Fintype.card F)^2 - Fintype.card F) := by
  rw [Matrix.card_GL_field (𝔽 := F) (n := 2)]
  simp [Fin.prod_univ_two]

/-- The units of a finite field form a group of size `q−1`. -/
private lemma card_units_sub_one {F : Type*} [Field F] [Fintype F] :
    Nat.card Fˣ = Fintype.card F - 1 := by
  have h := Nat.card_eq_card_units_add_one F
  have hq : Nat.card F = Fintype.card F := by exact Nat.card_eq_fintype_card
  rw [hq] at h
  omega

/-- `SL(2,F)` has the same cardinality as the kernel of `det : GL(2,F) → Fˣ`. -/
private lemma card_SL_eq_card_ker {F : Type*} [Field F] :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) =
      Nat.card (Matrix.GeneralLinearGroup.det : GL (Fin 2) F →* Fˣ).ker := by
  have e : Matrix.SpecialLinearGroup (Fin 2) F ≃*
      ↥(Matrix.SpecialLinearGroup.toGL : Matrix.SpecialLinearGroup (Fin 2) F →* GL (Fin 2) F).range :=
    MonoidHom.ofInjective Matrix.SpecialLinearGroup.toGL_injective
  have hk : (Matrix.GeneralLinearGroup.det : GL (Fin 2) F →* Fˣ).ker =
      (Matrix.SpecialLinearGroup.toGL : Matrix.SpecialLinearGroup (Fin 2) F →* GL (Fin 2) F).range := by
    ext x
    constructor
    · intro hx
      refine ⟨⟨(x : Matrix (Fin 2) (Fin 2) F), ?_⟩, ?_⟩
      · have h := congrArg (fun u : Fˣ => (u : F)) (MonoidHom.mem_ker.mp hx)
        simpa using h
      · ext i j; rfl
    · rintro ⟨s, rfl⟩
      exact MonoidHom.mem_ker.mpr (Matrix.SpecialLinearGroup.coeToGL_det s)
  rw [hk]
  exact Nat.card_congr e.toEquiv

/-- `|GL(2,F)| = |SL(2,F)| · (q−1)`: the determinant is surjective onto `Fˣ`
and its kernel is `SL(2,F)`. -/
private lemma card_GL_eq_card_SL_mul {F : Type*} [Field F] [Fintype F]
    (hsurj : Function.Surjective (Matrix.GeneralLinearGroup.det : GL (Fin 2) F →* Fˣ)) :
    Nat.card (GL (Fin 2) F) =
      Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) * (Fintype.card F - 1) := by
  let ker := (Matrix.GeneralLinearGroup.det : GL (Fin 2) F →* Fˣ).ker
  have h1 := Subgroup.card_mul_index ker
  have h2 := card_SL_eq_card_ker (F := F)
  rw [← h2] at h1
  have hind : ker.index = Fintype.card F - 1 := by
    rw [Subgroup.index_eq_card]
    calc
      Nat.card (GL (Fin 2) F ⧸ ker) =
          Nat.card ↥(Matrix.GeneralLinearGroup.det : GL (Fin 2) F →* Fˣ).range := by
        exact Nat.card_congr
          (QuotientGroup.quotientKerEquivRange (Matrix.GeneralLinearGroup.det : GL (Fin 2) F →* Fˣ)).toEquiv
      _ = Nat.card Fˣ := by
        have htop : (Matrix.GeneralLinearGroup.det : GL (Fin 2) F →* Fˣ).range = ⊤ :=
          MonoidHom.range_eq_top_of_surjective _ hsurj
        simp [htop]
      _ = Fintype.card F - 1 := card_units_sub_one (F := F)
  rw [hind] at h1
  exact h1.symm

/-- **Order of `SL(2,q)`**: `|SL(2,F)| = q(q²−1)`, where `q = |F|`. -/
theorem card_SL2_field {F : Type*} [Field F] [Fintype F] :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) =
      Fintype.card F * ((Fintype.card F) ^ 2 - 1) := by
  let q := Fintype.card F
  have hsurj : Function.Surjective (Matrix.GeneralLinearGroup.det : GL (Fin 2) F →* Fˣ) :=
    Matrix.GeneralLinearGroup.det_surjective
  have hGL := card_GL2 (F := F)
  have hEq := card_GL_eq_card_SL_mul (F := F) hsurj
  have hmul : Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) * (q - 1) =
      (q^2 - 1) * (q^2 - q) := by
    rw [← hEq, hGL]
  have hfac2 : (q^2 - q) = q * (q - 1) := by
    have h := Nat.mul_sub_left_distrib q q 1
    simpa [pow_two] using h.symm
  have hmul2 : Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) * (q - 1) =
      ((q^2 - 1) * q) * (q - 1) := by
    rw [hfac2] at hmul
    rw [← mul_assoc] at hmul
    exact hmul
  have hqpos : 0 < q - 1 := by
    have hlt : 1 < q := Fintype.one_lt_card
    omega
  have hres := Nat.mul_right_cancel hqpos hmul2
  simpa [q, mul_comm, mul_left_comm, mul_assoc] using hres

end Commons.LinearAlgebra.Matrix
