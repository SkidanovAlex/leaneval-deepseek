import Mathlib
import Submission.Work.MotK.TwRuling.TwFivetenDefs
import Submission.Work.MotK.TwRuling.SdWNdeg
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Shared vocabulary for `Work.MotK.TwRuling.sdTF5_span`

Let `R` be a field, `E` a Weierstrass curve over `R`, `Om := E.FunctionField`, and
`x := genX E`, `y := genY E`.

* `gx E`, `gy E` are `x` and `y` (abbreviations, for readability);
* `Tsp E` is the `R`-span of the 25 fivefold products `b₁b₂b₃b₄b₅` of the basis
  `sdBas E = ![1, x, y, x², xy]` of `L(5·O)`;
* `Ssp E` is the `R`-span of `sdTF5 E = (1, x, …, x¹²; y, xy, …, x¹¹y)`, i.e. of `L(25·O)`.

The target theorem `Work.MotK.TwRuling.sdTF5_span` is `Tsp E = Ssp E`.

The two inclusions are proved by two independent arguments:

* `Tsp E ≤ Ssp E`: each fivefold product is a monomial `x^a y^b` of pole order `≤ 25`
  (weight `wt x = 2`, `wt y = 3`), and every monomial of weight `≤ 25` lies in `Ssp E`
  by strong induction on `b`, using the Weierstrass relation `y² = x³ + a₂x² + a₄x + a₆ − a₁xy − a₃y`
  to lower the `y`-degree.  (This is the statement `mono_mem_Ssp`.)
* `Ssp E ≤ Tsp E`: every monomial `x^a y^b` with `a + b ≤ 10`, `b ≤ 5` is *literally* a fivefold
  product of basis elements, and the four "top" monomials `x¹¹`, `x¹⁰y`, `x¹²`, `x¹¹y` are obtained
  from the Weierstrass relation.
-/

open WeierstrassCurve WeierstrassCurve.Affine

namespace Work.MotK.TwRuling

noncomputable section

variable {R : Type} [Field R]

/-- `x = genX E` in the function field. -/
abbrev gx (E : WeierstrassCurve R) : Affine.FunctionField E := Work.MotV.genX E

/-- `y = genY E` in the function field. -/
abbrev gy (E : WeierstrassCurve R) : Affine.FunctionField E := Work.MotV.genY E

/-- The span of the 25 fivefold products of the basis `1, x, y, x², xy`. -/
def Tsp (E : WeierstrassCurve R) : Submodule R (Affine.FunctionField E) :=
  Submodule.span R (Set.range (fun q : Fin 5 × Fin 5 × Fin 5 × Fin 5 × Fin 5 =>
    sdBas E q.1 * sdBas E q.2.1 * sdBas E q.2.2.1 * sdBas E q.2.2.2.1 * sdBas E q.2.2.2.2))

/-- The span of `sdTF5 E`, i.e. of the 25 monomials of `L(25·O)`. -/
def Ssp (E : WeierstrassCurve R) : Submodule R (Affine.FunctionField E) :=
  Submodule.span R (Set.range (sdTF5 E))

/-- A fivefold product of basis elements lies in `Tsp E`. -/
theorem mem5 (E : WeierstrassCurve R) (i1 i2 i3 i4 i5 : Fin 5) :
    sdBas E i1 * sdBas E i2 * sdBas E i3 * sdBas E i4 * sdBas E i5 ∈ Tsp E :=
  Submodule.subset_span ⟨(i1, i2, i3, i4, i5), rfl⟩

/-- `Ssp E` is closed under multiplication by scalars. -/
theorem hsmS (E : WeierstrassCurve R) (c : R) {v : Affine.FunctionField E}
    (hv : v ∈ Ssp E) : algebraMap R (Affine.FunctionField E) c * v ∈ Ssp E := by
  rw [← Algebra.smul_def]
  exact Submodule.smul_mem _ c hv

/-- `Tsp E` is closed under multiplication by scalars. -/
theorem hsmT (E : WeierstrassCurve R) (c : R) {v : Affine.FunctionField E}
    (hv : v ∈ Tsp E) : algebraMap R (Affine.FunctionField E) c * v ∈ Tsp E := by
  rw [← Algebra.smul_def]
  exact Submodule.smul_mem _ c hv

/-- The Weierstrass relation, solved for `y²`. -/
theorem hrel' (E : WeierstrassCurve R) :
    (gy E) ^ 2 = (gx E) ^ 3 + algebraMap R (Affine.FunctionField E) E.a₂ * (gx E) ^ 2
      + algebraMap R (Affine.FunctionField E) E.a₄ * (gx E)
      + algebraMap R (Affine.FunctionField E) E.a₆
      - algebraMap R (Affine.FunctionField E) E.a₁ * ((gx E) * (gy E))
      - algebraMap R (Affine.FunctionField E) E.a₃ * (gy E) := by
  have h := sdWeierstrass E
  linear_combination (norm := first | refl_ring1 | ring1) h

end

end Work.MotK.TwRuling
