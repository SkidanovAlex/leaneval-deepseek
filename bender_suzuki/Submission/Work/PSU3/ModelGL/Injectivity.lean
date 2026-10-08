/-
# Injectivity of the matrix model `SZ E → PGL(3,E)`

The map `Work.PSU3.pglHom : SZ E →* PGL(3,E)`, `p ↦ A(p.x,p.y)`, is injective: a
unitriangular matrix is a scalar matrix only if it is the identity, and `A(x,y) = 1` forces
`x = y = 0`.
-/
import Submission.Work.PSU3.ModelGL
import Submission.Work.PSU3.Model.matOfXY_eq_one_iff

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false

open Matrix

namespace Work.PSU3

variable {E : Type*} [Field E] [FrobeniusInvolution E]

/-- The matrix model `SZ E → PGL(3,E)` is injective. -/
theorem pglHom_injective : Function.Injective (pglHom (E := E)) := by
  intro p q hpq
  obtain ⟨u, hu⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp hpq
  have h00 : (u : E) = 1 := by
    have h := congrArg (fun g : GL (Fin 3) E => (g : Matrix (Fin 3) (Fin 3) E) 0 0) hu
    simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, matGL_coe, matFun_apply,
      matOfXY_apply_00, matOfXY_apply_01, matOfXY_apply_02, matOfXY_apply_10,
      matOfXY_apply_11, matOfXY_apply_12, matOfXY_apply_20, matOfXY_apply_21,
      matOfXY_apply_22] at h
    simpa using h
  have hu1 : u = 1 := Units.ext h00
  rw [hu1, map_one, mul_one] at hu
  have hmat : matFun p = matFun q := by
    simpa [matFun_apply] using
      congrArg (fun g : GL (Fin 3) E => (g : Matrix (Fin 3) (Fin 3) E)) hu
  refine SZ.ext ?_ ?_
  · have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) E => M 0 1) hmat
    simpa only [matFun_apply, matOfXY_apply_01] using h
  · have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) E => M 0 2) hmat
    simpa only [matFun_apply, matOfXY_apply_02] using h

end Work.PSU3
