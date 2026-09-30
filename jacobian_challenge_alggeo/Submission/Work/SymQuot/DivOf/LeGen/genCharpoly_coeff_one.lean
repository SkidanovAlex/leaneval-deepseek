import Mathlib
import Submission.Work.SymQuot.DivOf.GenCharpoly
import Submission.Work.SymQuot.DivOf.SymChart

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.unusedSectionVars false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.SymQuot.DivOf.LeGen

/-- The `k`-th coefficient of `∏ i∈s (X - C (c i * Y))` is the `k`-th coefficient of
`∏ i∈s (X - C (c i))` multiplied by `Y ^ (#s - k)`: the product `∏ (X - c i * Y)` is the
"homogenization" of `∏ (X - c i)`, and the coefficient of `X ^ k` is homogeneous of degree
`#s - k` in `Y`. -/
private lemma prod_sub_C_mul_coeff {R : Type*} [CommRing R] {ι : Type*}
    (s : Finset ι) (c : ι → R) (Y : R) {k : ℕ} (h : k ≤ s.card) :
    (∏ i ∈ s, (Polynomial.X - Polynomial.C (c i * Y))).coeff k =
      (∏ i ∈ s, (Polynomial.X - Polynomial.C (c i))).coeff k * Y ^ (s.card - k) := by
  rw [show (∏ i ∈ s, (Polynomial.X - Polynomial.C (c i * Y))) =
      ∏ i ∈ s, (Polynomial.X + Polynomial.C (-(c i * Y))) from
    Finset.prod_congr rfl (fun i _ => by rw [Polynomial.C_neg, sub_eq_add_neg])]
  rw [Finset.prod_X_add_C_coeff s (fun i => -(c i * Y)) h]
  rw [show (∏ i ∈ s, (Polynomial.X - Polynomial.C (c i))) =
      ∏ i ∈ s, (Polynomial.X + Polynomial.C (-(c i))) from
    Finset.prod_congr rfl (fun i _ => by rw [Polynomial.C_neg, sub_eq_add_neg])]
  rw [Finset.prod_X_add_C_coeff s (fun i => -(c i)) h]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro t ht
  rw [Finset.mem_powersetCard] at ht
  rw [show (∏ i ∈ t, -(c i * Y)) = ∏ i ∈ t, (-(c i)) * Y from
    Finset.prod_congr rfl (fun i _ => by ring)]
  rw [Finset.prod_mul_distrib, Finset.prod_const, ht.2]

theorem genCharpoly_coeff_one {K : Type u} [Field K] {C : Work.CurveBasics.Curve K} {n : ℕ} [NeZero n] [Work.SymQuot.CurveAffineCover C] (V : C.left.Opens) (b : C.left.presheaf.obj (Opposite.op V)) {k : ℕ} (hk : k ≤ n) : (Work.SymQuot.DivOf.genCharpoly C n V (fun _ : Fin 1 => b)).coeff k = MvPolynomial.C ((Work.SymQuot.DivOf.charpoly C n V b).coeff k) * MvPolynomial.X 0 ^ (n - k) := by
  rw [show Work.SymQuot.DivOf.genCharpoly C n V (fun _ : Fin 1 => b) =
      ∏ m : Fin n, (Polynomial.X - Polynomial.C
        (MvPolynomial.C (Work.SymQuot.DivOf.coordPullbackAt C n V m b) *
          (MvPolynomial.X (0 : Fin 1) :
            MvPolynomial (Fin 1)
              Γ((Work.SymQuot.prod C.toOver n).left, Work.SymQuot.piOpen C.toOver V n)))) from by
    simp only [Work.SymQuot.DivOf.genCharpoly, Fin.sum_univ_one]]
  rw [prod_sub_C_mul_coeff Finset.univ
      (fun m => MvPolynomial.C (Work.SymQuot.DivOf.coordPullbackAt C n V m b))
      (MvPolynomial.X (0 : Fin 1)) (by simpa using hk)]
  rw [Finset.card_univ, Fintype.card_fin]
  congr 1
  rw [show (∏ m : Fin n, (Polynomial.X - Polynomial.C
        (MvPolynomial.C (Work.SymQuot.DivOf.coordPullbackAt C n V m b)))) =
      Polynomial.map (MvPolynomial.C :
        Γ((Work.SymQuot.prod C.toOver n).left, Work.SymQuot.piOpen C.toOver V n) →+*
          MvPolynomial (Fin 1)
            Γ((Work.SymQuot.prod C.toOver n).left, Work.SymQuot.piOpen C.toOver V n))
        (Work.SymQuot.DivOf.charpoly C n V b) from by
    rw [Work.SymQuot.DivOf.charpoly, Polynomial.map_prod]
    apply Finset.prod_congr rfl
    intro m _
    rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]]
  rw [Polynomial.coeff_map]

end Work.SymQuot.DivOf.LeGen
