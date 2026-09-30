/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The point of `Symⁿ C` determined by a ring homomorphism of the chart ring (area SY)

To construct the point `p_D` of `Symⁿ C` attached to an effective divisor of degree `n`
(`Submission/Work/NOTES_LEAD_jacobian_divof.md` §5), one produces an `F`-algebra homomorphism
`Φ` on the chart ring `Γ(Cⁿ, Vⁿ)^{S_n}` of an invariant affine open `Vⁿ ⊆ Cⁿ`, and must then
convert it into a point `Spec F ⟶ Symⁿ C`.  This file performs that conversion:

* `chartOf` — the chart of `Vⁿ` as an element of the cover used to build `Symⁿ C`;
* `ptOfChartHom` — the point `Spec F ⟶ Symⁿ C` given by `Φ` (together with the compatibility
  `Φ (chartConst k) = algebraMap K F k`, which says that `Φ` is a `K`-algebra map on the
  constants).

The proof of the defining factorisation `ptOfChartHom_evalAlg` (the "mirror of the key lemma")
is proved downstream.
-/
import Submission.Work.SymQuot.DivOf.Complete.Setup
import Submission.Work.SymQuot.DivOf.Complete.chartIota_comp_hom

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.SymQuot.DivOf.Complete

open Work.CurveBasics

variable {K : Type u} [Field K] {C : Curve K} {n : ℕ} [NeZero n] [CurveAffineCover C]

/-- The chart of `Vⁿ ⊆ Cⁿ` as an element of the cover of `Cⁿ` used to build `Symⁿ C`. -/
noncomputable def chartOf (C : Curve K) (n : ℕ) [NeZero n] [CurveAffineCover C]
    {V : C.left.Opens} (hV : IsAffineOpen V) : (symData C n).Chart :=
  ⟨piOpen C.toOver V n, Prod.isAffineOpen_piOpen C.toOver n V hV, symPiOpen_invariant C n V⟩

/-- **The point of `Symⁿ C` determined by a ring homomorphism `Φ` of the chart ring** of the
chart `Spec Γ(Cⁿ,Vⁿ)^{S_n}`: the composite `Spec F ⟶ Spec Γ(Cⁿ,Vⁿ)^{S_n} ⟶ Symⁿ C`.  The
hypothesis `hΦ` says that `Φ` is compatible with the structure maps on the constant functions
(equivalently, that `Spec.map Φ` is a morphism of `K`-schemes). -/
noncomputable def ptOfChartHom (C : Curve K) (n : ℕ) [NeZero n] [CurveAffineCover C]
    {F : Type u} [Field F] [Algebra K F] {V : C.left.Opens} (hV : IsAffineOpen V)
    (Φ : ↥(chartInvariants (C := C) (n := n) (piOpen C.toOver V n)
      (symPiOpen_invariant C n V)) →+* F)
    (hΦ : ∀ k : K, Φ (chartConst C n (chartOf C n hV) k) = algebraMap K F k) :
    Work.SpecLin.FPt (Sym C n) F :=
  Over.homMk (Spec.map (CommRingCat.ofHom Φ) ≫ (symData C n).chartι (chartOf C n hV)) (by
    rw [Category.assoc, chartIota_comp_hom, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 1
    ext k
    exact hΦ k)

/-- **The ring homomorphism of the chart ring induced by `n` points of the affine open `V`**:
the evaluation of an invariant function on `Vⁿ` at the `n`-tuple `y`. -/
noncomputable def chartEval (C : Curve K) (n : ℕ) [NeZero n] [CurveAffineCover C]
    {L : Type u} [Field L] [Algebra K L] {V : C.left.Opens}
    (y : Fin n → Work.SpecLin.CurveFPt C L)
    (h : ⊤ ≤ (Limits.Pi.lift y : Work.SpecLin.specOf (K := K) L ⟶
      prod C.toOver n).left ⁻¹ᵁ piOpen C.toOver V n) :
    ↥(chartInvariants (C := C) (n := n) (piOpen C.toOver V n)
      (symPiOpen_invariant C n V)) →+* L :=
  (evalAlg C V n y h).comp
    (Subring.subtype (chartInvariants (C := C) (n := n) (piOpen C.toOver V n)
      (symPiOpen_invariant C n V)))

end Work.SymQuot.DivOf.Complete
