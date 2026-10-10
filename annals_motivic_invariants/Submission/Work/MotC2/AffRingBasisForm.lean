import Mathlib
import Submission.Work.MotC2.Defs
import Submission.Work.MotC2.Relations
import Submission.Work.MotC2.affRing_eq_adjoin
import Submission.Work.MotC2.algebraMap_smul_eq_aeval

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotC2

/-- Every element of the affine coordinate ring `affRing E = L[x,y] ⊆ L(E)` is of the form
`P(x) + Q(x)·y` with `P, Q ∈ L[X]`.

Route.  `affRing E` is the range of the `L`-algebra map `Coord E = L[X,Y]/(W) → L(E)`; use
`WeierstrassCurve.Affine.CoordinateRing.exists_smul_basis_eq`: every `a : Coord E` is
`p • 1 + q • mk E X`; its image in `L(E)` is
`Polynomial.aeval (genX E) p + Polynomial.aeval (genX E) q * genY E` by
`Work.MotC2.algebraMap_smul_eq_aeval`. -/
theorem AffRingBasisForm (L : Type*) [Field L] (E : WeierstrassCurve L) :
    ∀ z : Func E, z ∈ affRing E →
      ∃ P Q : Polynomial L,
        z = Polynomial.aeval (genX E) P + Polynomial.aeval (genX E) Q * genY E := by
  intro z hz
  have key : ∃ a : Coord E, algebraMap (Coord E) (Func E) a = z := by
    rw [affRing] at hz
    induction hz using Algebra.adjoin_induction with
    | mem y hy =>
        obtain ⟨a, rfl⟩ := hy
        exact ⟨a, rfl⟩
    | algebraMap c =>
        exact ⟨algebraMap L (Coord E) c, by
          rw [← IsScalarTower.algebraMap_apply L (Coord E) (Func E)]⟩
    | add x y hx hy px py =>
        obtain ⟨a, ha⟩ := px
        obtain ⟨b, hb⟩ := py
        exact ⟨a + b, by rw [map_add, ha, hb]⟩
    | mul x y hx hy px py =>
        obtain ⟨a, ha⟩ := px
        obtain ⟨b, hb⟩ := py
        exact ⟨a * b, by rw [map_mul, ha, hb]⟩
  obtain ⟨a, ha⟩ := key
  obtain ⟨P, Q, hPQ⟩ :=
    WeierstrassCurve.Affine.CoordinateRing.exists_smul_basis_eq (W' := E) a
  refine ⟨P, Q, ?_⟩
  rw [← ha, ← hPQ, map_add, (algebraMap_smul_eq_aeval L E P).1,
    (algebraMap_smul_eq_aeval L E Q).2]

end Work.MotC2
