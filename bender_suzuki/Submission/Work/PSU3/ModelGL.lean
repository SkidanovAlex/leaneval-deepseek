/-
# The matrix model of `SZ E`: the homomorphisms to `GL` and to `PGL`

The map `p ↦ A(p.x,p.y)` is multiplicative (`Work.PSU3.Model.matOfXY_mul`), has
determinant `1` and preserves the anti-diagonal Hermitian form (`Work.PSU3.Model.matFun_herm`).
This file packages it as

* `Work.PSU3.matHom : SZ E →* Matrix (Fin 3) (Fin 3) E`,
* `Work.PSU3.matGL : SZ E →* GL (Fin 3) E`,
* `Work.PSU3.pglHom : SZ E →* ProjGenLinGroup (Fin 3) E`.

For `E = GaloisField 2 (2n)` the image of `pglHom` lies in `PSU3Model n`
(the special-unitary group modulo scalars), which is the identification of the
Bender–Suzuki group of "case c" with the unipotent part of `PSU(3,2ⁿ)`; see
`Work.PSU3.toPSU3Model`.
-/
import Submission.Work.PSU3.Model
import Submission.Work.PSU3.Model.matOfXY_mul
import Submission.Work.PSU3.Model.matOfXY_det

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false

namespace Work.PSU3

open Matrix

variable {E : Type*} [Field E] [FrobeniusInvolution E]

/-- The unitriangular matrices of `SZ E` as a multiplicative map. -/
noncomputable def matHom : SZ E →* Matrix (Fin 3) (Fin 3) E where
  toFun := matFun
  map_one' := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [matFun]
  map_mul' := by
    intro p q
    simp only [matFun, SZ.mul_x, SZ.mul_y, Model.matOfXY_mul]

/-- The unitriangular matrices of `SZ E` as elements of `GL (Fin 3) E`. -/
noncomputable def matGL : SZ E →* GL (Fin 3) E where
  toFun p :=
    GeneralLinearGroup.mkOfDetNeZero (matFun p) (by
      simp only [matFun_apply, Model.matOfXY_det]
      exact one_ne_zero)
  map_one' := by
    ext i j
    exact congrFun (congrFun (matHom.map_one) i) j
  map_mul' := by
    intro p q
    ext i j
    exact congrFun (congrFun (matHom.map_mul p q) i) j

/-- The composite of `matGL` with the projection `GL → PGL`, i.e. the image of the
case-c Suzuki group in the projective general linear group. -/
noncomputable def pglHom : SZ E →* ProjGenLinGroup (Fin 3) E :=
  ProjGenLinGroup.mk.comp matGL

@[simp] lemma matHom_apply (p : SZ E) : matHom p = matFun p := rfl

@[simp] lemma matGL_coe (p : SZ E) : (matGL p : Matrix (Fin 3) (Fin 3) E) = matFun p := rfl

@[simp] lemma pglHom_apply (p : SZ E) : pglHom p = ProjGenLinGroup.mk (matGL p) := rfl

end Work.PSU3
