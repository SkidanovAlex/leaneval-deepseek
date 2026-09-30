/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The value at a lift of an `F''`-combination of chart sections lies in `charIdealGen.map bcSec`

Let `C` be a curve over `K`, `d` a chart of `Symⁿ C` and `x` a lift of the point `p` to a family of
`F''`-points of `C` (over a field extension `F''` of `F`).  For a family of chart sections
`b : Fin r → Γ(C, V)` and coefficients `f : Fin r → F''`, the product

`∏_m ( Σ_i f_i · secAlpha b_i - Σ_i f_i · b_i(x_m) )`

— the value at the lifted points of the `F''`-combination `Σ_i f_i b_i`, written with a constant
section for the value at each `x_m` — lies in the base change `(charIdealGen F d).map bcSec` of the
generic divisor ideal.  This is the easy inclusion of the hub lemma `charIdealGen_map_eq`: the
product is the evaluation of the mapped generic generator `map bcSec (genGenerator b)`
(`eval₂Hom_map_genGenerator`), and every coefficient of that polynomial lies in
`(charIdealGen F d).map bcSec` because it is the image under `bcSec` of a coefficient of
`genGenerator b`, which by definition generates `charIdealGen F d`.
-/
import Mathlib
import Submission.Work.SymQuot.DivOf.CharIdealGenMapDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.SymQuot.DivOf

open Work.CurveBasics

universe u

/-- **Evaluation at coefficients in an ideal.**  If every coefficient of `h ∈ R[σ]` lies in an
ideal `J ≤ R`, then the value of `h` under any `R`-linear substitution (here written with the
identity as the coefficient map) still lies in `J`. -/
theorem eval₂Hom_mem_of_coeff_mem {R : Type*} [CommRing R] {σ : Type*} (J : Ideal R)
    (f : σ → R) {h : MvPolynomial σ R} (hh : ∀ α, h.coeff α ∈ J) :
    MvPolynomial.eval₂Hom (RingHom.id R) f h ∈ J := by
  rw [MvPolynomial.as_sum (p := h), map_sum]
  refine Ideal.sum_mem _ fun α _ => ?_
  rw [MvPolynomial.eval₂Hom_monomial, RingHom.id_apply]
  exact Ideal.mul_mem_right _ J (hh α)

theorem prod_sub_mem_charIdealGen_map {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    {n : ℕ} [NeZero n] [Work.SymQuot.CurveAffineCover C] {F : Type u} [Field F] [Algebra K F]
    {p : Work.SpecLin.FPt (Work.SymQuot.Sym C n) F}
    (d : Work.SymQuot.DivOf.ChartPt C n p) {F'' : Type u} [Field F''] [Algebra K F'']
    [Algebra F F''] [IsScalarTower K F F''] (x : Fin n → Work.SpecLin.CurveFPt C F'')
    (hx : Work.SymQuot.Sym.powMap C n x =
      Work.SpecLin.RPt.map (IsScalarTower.toAlgHom K F F'') p)
    {r : ℕ} (b : Fin r → C.left.presheaf.obj (Opposite.op d.V)) (f : Fin r → F'') :
    (∏ m, ((∑ i, Work.SymQuot.DivOf.secConst C F'' d.V (f i) *
          Work.SymQuot.DivOf.secAlpha C F'' d.V (b i)) -
        Work.SymQuot.DivOf.secConst C F'' d.V
          (∑ i, f i * Work.SymQuot.DivOf.valAtLift d x
            (Work.SymQuot.DivOf.lift_mem_V d x hx) m (b i)))) ∈
      (Work.SymQuot.DivOf.charIdealGen F d).map
        (Work.SymQuot.DivOf.bcSec (C := C) F F'' d.V) := by
  rw [← eval₂Hom_map_genGenerator d x hx b f]
  apply eval₂Hom_mem_of_coeff_mem
  intro α
  rw [MvPolynomial.coeff_map]
  exact Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨r, b, α, rfl⟩)

end Work.SymQuot.DivOf
