import Mathlib
import Submission.Work.MotTDG.Defs
import Submission.Work.MotTDG.TenAux
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotTDG
noncomputable section

open WeierstrassCurve WeierstrassCurve.Affine

/-!
**TDG-a**: the ten monomials `1, x, y, x², xy, x³, x²y, x⁴, x³y, x²y²` of `L(10·O)` are
`L`-independent, for an ARBITRARY Weierstrass curve `E` over a field `L` (no `IsElliptic`).

`Work.MotTDG.tenMon E = goodMon (basE E)` is the family
`(1, x, y, x², xy, x³, x²y, x⁴, x³y, x²y²)` in `FunctionField E = L(E)`, where
`x = Work.MotV.genX E` and `y = Work.MotV.genY E`.  It is a black-box input of node TDG-d
(`Work.MotTDG.rhoVW_eq_zero`): from `∑ t, rhoVW … t • tenMon E t = 0` it yields `rhoVW … t = 0`.
The statement is identical to the (still `sorry`) `Work.MotTDG.tenMon_linearIndependent`; it is
re-stated under a new name so that TDG-d can be assembled against a proved module.

PROOF ROUTE.
* Step 1.  Work in `A = WeierstrassCurve.Affine.CoordinateRing E` with
  `xA = CoordinateRing.mk E (Polynomial.C Polynomial.X)` (`Work.MotC2.coordX_eq_mk` identifies it
  with `Work.MotC2.coordX E`) and `yA = CoordinateRing.mk E Polynomial.X` (= `coordY E`).  The ten
  elements of `A` are `tenMonA = (1, xA, yA, xA², xA·yA, xA³, xA²yA, xA⁴, xA³yA, xA²yA²)`.  Since
  `algebraMap A (FunctionField E) (tenMonA i) = Work.MotTDG.tenMon E i` and `algebraMap` is
  injective (`IsFractionRing.injective`; `CoordinateRing E` is a domain when `E` is over a field),
  it suffices to prove the independence in `A`.
* Step 2.  Every element of `A` is `p(xA) + q(xA)·yA` with `p, q ∈ L[X]`
  (`CoordinateRing.exists_smul_basis_eq` plus `CoordinateRing.smul`); conversely
  `CoordinateRing.smul_basis_eq_zero` says: `p(xA) + q(xA)·yA = 0` implies `p = q = 0`.
* Step 3.  Apply Step 2 to `∑ i, c i • tenMonA i = 0`.  The `x`-parts of the ten elements are
  `1, X, 0, X², 0, X³, 0, X⁴, 0, X⁵+a₂X⁴+a₄X³+a₆X²` and the `y`-parts are
  `0, 0, 1, 0, X, 0, X², 0, X³, -(a₁X³+a₃X²)`; the last one uses the relation in `A`
  `yA² = xA³ + a₂xA² + a₄xA + a₆ - (a₁xA + a₃)yA` (`Work.MotC2.coord_relation`), multiplied by
  `xA²`, to rewrite `xA²yA²`.  (`CoordinateRing.smul_basis_mul_C` and
  `CoordinateRing.smul_basis_mul_Y` are the relevant rewriting API.)
* Step 4.  Comparing coefficients in the two polynomial identities
  `∑ c i · (x-part i) = 0` and `∑ c i · (y-part i) = 0` (`Polynomial.funext`,
  `Polynomial.coeff_X_pow`, `Finset.sum_eq_single`) yields, in the order `c 0, c 1, c 9, c 3,
  c 5, c 7` from the `x`-parts (the `X⁵`-coefficient is `c 9`) and then `c 2, c 4, c 6, c 8` from
  the `y`-parts, that every `c i = 0`.
* Step 5.  Conclude with `Fintype.linearIndependent_iff`.
-/

/-! ## §1 The coefficients of `tenP` and `tenQ` -/

private lemma tenP_coeff_zero {L : Type} [Field L] (a₂ a₄ a₆ : L) (c : Fin 10 → L) :
    (tenP a₂ a₄ a₆ c).coeff 0 = c 0 := by
  simp [tenP, Polynomial.coeff_X_pow, Fin.isValue]

private lemma tenP_coeff_one {L : Type} [Field L] (a₂ a₄ a₆ : L) (c : Fin 10 → L) :
    (tenP a₂ a₄ a₆ c).coeff 1 = c 1 := by
  simp [tenP, Polynomial.coeff_X_pow, Fin.isValue]

private lemma tenP_coeff_two {L : Type} [Field L] (a₂ a₄ a₆ : L) (c : Fin 10 → L) :
    (tenP a₂ a₄ a₆ c).coeff 2 = c 3 + c 9 * a₆ := by
  simp [tenP, Polynomial.coeff_X_pow, Fin.isValue]

private lemma tenP_coeff_three {L : Type} [Field L] (a₂ a₄ a₆ : L) (c : Fin 10 → L) :
    (tenP a₂ a₄ a₆ c).coeff 3 = c 5 + c 9 * a₄ := by
  simp [tenP, Polynomial.coeff_X_pow, Fin.isValue]

private lemma tenP_coeff_four {L : Type} [Field L] (a₂ a₄ a₆ : L) (c : Fin 10 → L) :
    (tenP a₂ a₄ a₆ c).coeff 4 = c 7 + c 9 * a₂ := by
  simp [tenP, Polynomial.coeff_X_pow, Fin.isValue]

private lemma tenP_coeff_five {L : Type} [Field L] (a₂ a₄ a₆ : L) (c : Fin 10 → L) :
    (tenP a₂ a₄ a₆ c).coeff 5 = c 9 := by
  simp [tenP, Polynomial.coeff_X_pow, Fin.isValue]

private lemma tenQ_coeff_zero {L : Type} [Field L] (a₁ a₃ : L) (c : Fin 10 → L) :
    (tenQ a₁ a₃ c).coeff 0 = c 2 := by
  simp [tenQ, Polynomial.coeff_X_pow, Fin.isValue]

private lemma tenQ_coeff_one {L : Type} [Field L] (a₁ a₃ : L) (c : Fin 10 → L) :
    (tenQ a₁ a₃ c).coeff 1 = c 4 := by
  simp [tenQ, Polynomial.coeff_X_pow, Fin.isValue]

private lemma tenQ_coeff_two {L : Type} [Field L] (a₁ a₃ : L) (c : Fin 10 → L) :
    (tenQ a₁ a₃ c).coeff 2 = c 6 - c 9 * a₃ := by
  simp [tenQ, Polynomial.coeff_X_pow, Fin.isValue]

private lemma tenQ_coeff_three {L : Type} [Field L] (a₁ a₃ : L) (c : Fin 10 → L) :
    (tenQ a₁ a₃ c).coeff 3 = c 8 - c 9 * a₁ := by
  simp [tenQ, Polynomial.coeff_X_pow, Fin.isValue]

/-! ## §2 The `L[X]`-module structure of the coordinate ring -/

/-- The `L`-algebra homomorphism `L[X] → L[X,Y]/(W_E)`, `X ↦ x`, is `Polynomial.aeval x`. -/
private lemma aeval_coordX_eq_smul {L : Type} [Field L] (E : WeierstrassCurve L)
    (P : Polynomial L) :
    Polynomial.aeval (Work.MotC2.coordX E) P = P • (1 : CoordinateRing E) := by
  have h1 : (algebraMap (Polynomial L) (CoordinateRing E)) (Polynomial.X)
      = Work.MotC2.coordX E := by
    have h := CoordinateRing.smul (W' := E) (Polynomial.X : Polynomial L) (1 : CoordinateRing E)
    rw [mul_one] at h
    rw [Work.MotC2.coordX_eq_mk, ← h, Algebra.smul_def, mul_one]
  have h2 : IsScalarTower.toAlgHom L (Polynomial L) (CoordinateRing E)
      = Polynomial.aeval (Work.MotC2.coordX E) := by
    apply Polynomial.algHom_ext
    rw [IsScalarTower.toAlgHom_apply, Polynomial.aeval_X]
    exact h1
  rw [Algebra.smul_def, mul_one, ← h2]
  rfl

/-! ## §3 Independence in the coordinate ring -/

/-- **TDG-a in the affine coordinate ring**: the ten monomials
`1, x, y, x², xy, x³, x²y, x⁴, x³y, x²y²` of `A = L[X,Y]/(W_E)` are `L`-independent. -/
private theorem goodMon_basA_linearIndependent {L : Type} [Field L] (E : WeierstrassCurve L) :
    LinearIndependent L (fun i : Fin 10 => goodMon
      ![1, Work.MotC2.coordX E, Work.MotC2.coordY E, Work.MotC2.coordX E ^ 2,
        Work.MotC2.coordX E * Work.MotC2.coordY E] i) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  -- the Weierstrass relation in the coordinate ring, in the shape needed by `tenMon_expansion`
  have hrel : (Work.MotC2.coordY E) ^ 2
        + algebraMap L (CoordinateRing E) E.a₁ * Work.MotC2.coordX E * Work.MotC2.coordY E
        + algebraMap L (CoordinateRing E) E.a₃ * Work.MotC2.coordY E =
      (Work.MotC2.coordX E) ^ 3 + algebraMap L (CoordinateRing E) E.a₂ * (Work.MotC2.coordX E) ^ 2
        + algebraMap L (CoordinateRing E) E.a₄ * Work.MotC2.coordX E
        + algebraMap L (CoordinateRing E) E.a₆ := by
    have h := Work.MotC2.coordY_sq_relation E
    linear_combination (norm := first | refl_ring1 | ring1) h
  -- normal form of the ten monomials
  have hexp := tenMon_expansion (R := CoordinateRing E) E.a₁ E.a₂ E.a₃ E.a₄ E.a₆
    (Work.MotC2.coordX E) (Work.MotC2.coordY E) c hrel
  have hzero : Polynomial.aeval (Work.MotC2.coordX E) (tenP E.a₂ E.a₄ E.a₆ c)
      + Polynomial.aeval (Work.MotC2.coordX E) (tenQ E.a₁ E.a₃ c)
        * Work.MotC2.coordY E = 0 := by
    rw [← hexp]
    exact hc
  -- rewrite `aeval` as the `L[X]`-action and apply the basis lemma
  rw [aeval_coordX_eq_smul, aeval_coordX_eq_smul, Algebra.smul_mul_assoc, one_mul] at hzero
  obtain ⟨hP, hQ⟩ := CoordinateRing.smul_basis_eq_zero (W' := E)
    (p := tenP E.a₂ E.a₄ E.a₆ c) (q := tenQ E.a₁ E.a₃ c) hzero
  have h9 : c 9 = 0 := by
    have h := congrArg (fun p : Polynomial L => p.coeff 5) hP
    simpa [tenP_coeff_five] using h
  have h7 : c 7 = 0 := by
    have h := congrArg (fun p : Polynomial L => p.coeff 4) hP
    simp only [tenP_coeff_four, Polynomial.coeff_zero] at h
    rw [h9, zero_mul, add_zero] at h
    exact h
  have h5 : c 5 = 0 := by
    have h := congrArg (fun p : Polynomial L => p.coeff 3) hP
    simp only [tenP_coeff_three, Polynomial.coeff_zero] at h
    rw [h9, zero_mul, add_zero] at h
    exact h
  have h3 : c 3 = 0 := by
    have h := congrArg (fun p : Polynomial L => p.coeff 2) hP
    simp only [tenP_coeff_two, Polynomial.coeff_zero] at h
    rw [h9, zero_mul, add_zero] at h
    exact h
  have h1 : c 1 = 0 := by
    have h := congrArg (fun p : Polynomial L => p.coeff 1) hP
    simpa [tenP_coeff_one] using h
  have h0 : c 0 = 0 := by
    have h := congrArg (fun p : Polynomial L => p.coeff 0) hP
    simpa [tenP_coeff_zero] using h
  have h2 : c 2 = 0 := by
    have h := congrArg (fun p : Polynomial L => p.coeff 0) hQ
    simpa [tenQ_coeff_zero] using h
  have h4 : c 4 = 0 := by
    have h := congrArg (fun p : Polynomial L => p.coeff 1) hQ
    simpa [tenQ_coeff_one] using h
  have h6 : c 6 = 0 := by
    have h := congrArg (fun p : Polynomial L => p.coeff 2) hQ
    simp only [tenQ_coeff_two, Polynomial.coeff_zero] at h
    rw [h9, zero_mul, sub_zero] at h
    exact h
  have h8 : c 8 = 0 := by
    have h := congrArg (fun p : Polynomial L => p.coeff 3) hQ
    simp only [tenQ_coeff_three, Polynomial.coeff_zero] at h
    rw [h9, zero_mul, sub_zero] at h
    exact h
  intro i
  fin_cases i <;> assumption

/-! ## §4 Transfer to the function field -/

/-- The coordinate ring basis `(1, x, y, x², xy)` maps to the function field basis
`(1, x, y, x², xy)` of `L(5·O)`. -/
private lemma algebraMap_basA_eq_basE {L : Type} [Field L] (E : WeierstrassCurve L) :
    (fun m : Fin 5 => algebraMap (CoordinateRing E) (FunctionField E)
        (![1, Work.MotC2.coordX E, Work.MotC2.coordY E, Work.MotC2.coordX E ^ 2,
          Work.MotC2.coordX E * Work.MotC2.coordY E] m)) = basE E := by
  funext m
  fin_cases m <;> simp [basE, Work.MotC2.genX, Work.MotC2.genY, Work.MotTDG.genX_eq,
    Work.MotTDG.genY_eq]

theorem TenMonLI {L : Type} [Field L] (E : WeierstrassCurve L) :
    LinearIndependent L (Work.MotTDG.tenMon E) := by
  -- transfer the coordinate-ring independence along the injective map to the function field
  have hmap' : LinearIndependent L (fun i => algebraMap (CoordinateRing E) (FunctionField E)
      (goodMon ![1, Work.MotC2.coordX E, Work.MotC2.coordY E, Work.MotC2.coordX E ^ 2,
        Work.MotC2.coordX E * Work.MotC2.coordY E] i)) :=
    (goodMon_basA_linearIndependent E).map'
      (IsScalarTower.toAlgHom L (CoordinateRing E) (FunctionField E)).toLinearMap
      (LinearMap.ker_eq_bot.mpr (IsFractionRing.injective (CoordinateRing E) (FunctionField E)))
  have hfun : (fun i => algebraMap (CoordinateRing E) (FunctionField E)
      (goodMon ![1, Work.MotC2.coordX E, Work.MotC2.coordY E, Work.MotC2.coordX E ^ 2,
        Work.MotC2.coordX E * Work.MotC2.coordY E] i)) = tenMon E := by
    funext i
    rw [tenMon, map_goodMon, algebraMap_basA_eq_basE]
  rw [hfun] at hmap'
  exact hmap'

end
end Work.MotTDG
