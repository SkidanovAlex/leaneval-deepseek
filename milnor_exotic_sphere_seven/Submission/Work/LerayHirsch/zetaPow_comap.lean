import Mathlib
import Submission.Work.LerayHirsch.Naturality
import Submission.Work.LerayHirsch.LH
import Submission.Work.LerayHirsch.nonempty_bundleIso_tautLine_comap

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Naturality of the powers `ζ^i` of the hyperplane class

The projectivisation is functorial: a continuous map `f : B' → B` induces
`P(f) = Work.LerayHirsch.projMapComap Z f : P(f^*E) → P(E)`
(`Submission/Work/LerayHirsch/Naturality.lean`), and the tautological line bundle is natural along it
(`bundleComap_tautLine_eq_tautLine_bundleComap`, `nonempty_bundleIso_tautLine_comap`).  Hence the
hyperplane class `ζ = c₁(ℓ)` is natural, and so are all its powers `ζ^i`:

`P(f)^*(ζ_Z^i) = ζ_{f^*Z}^i     in  H^{2i}(P(f^*E); ℤ)`.

This is the naturality of `zetaPow` that the Mayer–Vietoris step of the Leray–Hirsch induction
(`Work.LerayHirsch.LerayHirschGlue`) needs in order to identify the restricted powers of `ζ` on the
pieces of an open cover.

The proof is the two inputs plus induction on `i`:

* `i = 0`: `ζ^0 = 1` is the unit class, fixed by pullback (`Work.Thom.CohMap_oneH`);
* `i+1`: `ζ^{i+1} = ζ^i ⌣ ζ` and the graded product is natural (`Work.Whitney.cupChern_CohMap`).

Everything here is `sorry`-free and axiom-clean.
-/

namespace Work.LerayHirsch

open Work.TangentClasses Work.Thom

noncomputable section

variable {B B' : Type} [TopologicalSpace B] [TopologicalSpace B'] {ι : Type} [Fintype ι] {m : ℕ}

/-- **Naturality of `ζ`**: the hyperplane class of `P(f^*E)` is the pullback of the hyperplane class
of `P(E)` along the functorial map `P(f) : P(f^*E) → P(E)`. -/
theorem zeta_projMapComap (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (f : C(B', B)) :
    (CohMap (projMapComap Z f) ℤ 2).hom (zeta Z) = zeta (bundleComap Z f) := by
  rw [zeta_comap (Z := Z) (f := projMapComap Z f), zeta,
    bundleComap_tautLine_eq_tautLine_bundleComap Z f]

/-- **Naturality of the powers of the hyperplane class**: `P(f)^*(ζ_Z^i) = ζ_{f^*Z}^i` in
`H^{2i}(P(f^*E);ℤ)`. -/
theorem zetaPow_comap {B B' : Type} [TopologicalSpace B] [TopologicalSpace B']
    {ι : Type} [Fintype ι] {m : ℕ} (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (f : C(B', B)) (i : ℕ) :
    (Work.Thom.CohMap (Work.LerayHirsch.projMapComap Z f) ℤ (2 * i)).hom
      (Work.LerayHirsch.zetaPow Z i)
      = Work.LerayHirsch.zetaPow (Work.Thom.bundleComap Z f) i := by
  induction i with
  | zero =>
    rw [zetaPow_zero, Work.Whitney.cohTransport_CohMap, CohMap_oneH, zetaPow_zero]
  | succ i ih =>
    rw [zetaPow_succ, zetaPow_succ, Work.Whitney.cupChern_CohMap, ih, zeta_projMapComap]

end

end Work.LerayHirsch
