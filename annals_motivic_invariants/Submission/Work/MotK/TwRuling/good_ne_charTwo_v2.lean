import Mathlib
import Submission.Work.MotV.Defs
import Submission.Work.MotT.Defs
import Submission.Work.MotT.KleinParamData
import Submission.Work.MotT.kpE_invariants
import Submission.Work.MotT.kpData_klein_eq
import Submission.Work.MotT.kpData_spans_good
import Submission.Work.MotT.kpData_coord0_ne
import Submission.Work.MotT.exists_kleinData_kleinParam
import Submission.Work.MotK.TwRuling.exists_algEquiv_of_same_ab_v3
import Submission.Work.MotK.TwRuling.j_eq_of_funcAlgEquiv_v2
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotK.TwRuling.good_ne_charTwo_v2` — characteristic two, the `kpData` route

An **alternative proof** of `Work.MotK.TwRuling.good_ne_charTwo` (`ringChar K = 2 → D.a⁵ ≠ D.b⁵`)
that does **not** go through `Work.MotK.TwRuling.kleinC4_cube_of_good` (the general characteristic
`≠ 5` invariant identity), and therefore avoids the `kpW`-locus trap documented in
`NOTE_kpData_kpW_locus.md`.

Suppose `D.Good` with `ringChar K = 2` and `D.a⁵ = D.b⁵`.  Put `u := D.a / D.b`; then `u⁵ = 1`,
and the parametric model `kpE K u` is non-degenerate (`kpW K u ≠ 0`, `kpDelta K u ≠ 0`) and has
`j = 0` (its `c₄`-numerator `kpC4Num` vanishes at every fifth root of unity in characteristic `2`).
The datum `D₁ := {D with a := u, b := 1}` has the same `(a,b)` as the parametric datum
`Work.MotT.kpData K u`, so `Work.MotK.TwRuling.exists_algEquiv_of_same_ab` (minimal hypotheses only:
`ab ≠ 0`, `klein_eq`, `spans` — no `Good`, no `kpW ≠ 0` on `D`) gives an isomorphism of function
fields, and `Work.MotK.TwRuling.j_eq_of_funcAlgEquiv_v2` transports `j = 0` to `D.E`.  This
contradicts `hD.j_ne_zero`.

The only unproved ingredient is `Work.MotK.TwRuling.exists_algEquiv_of_same_ab`; everything else
(`j_eq_of_funcAlgEquiv_v2`, and the characteristic-two arithmetic reproduced below) is proved.

⚠ The characteristic-two arithmetic of `Submission/Work/MotK/TwRuling/kpE_charTwo.lean` is
**reproduced here** (in the private namespace `GoodNeCharTwoV2Aux`) rather than imported, because at
the time of writing that file does not parse: its `namespace KpECharTwoAux` is preceded by a
doc comment, which this Lean version rejects ("unexpected token 'namespace'").  Once that
one-character defect is repaired (replace the doc-comment opener by a plain comment opener) the
copies below can be replaced by `Work.MotK.TwRuling.KpECharTwoAux.*`.

⚠ `Work.MotK.TwRuling.coeff_disjunction` may switch its characteristic-`2` branch to this statement
at any time; `Work.MotK.TwRuling.good_ne_charTwo` itself (a different proof, through
`kleinC4_cube_of_good`) is left untouched.
-/

set_option autoImplicit false

namespace Work.MotK.TwRuling

open Polynomial WeierstrassCurve WeierstrassCurve.Affine

/-
Characteristic-two arithmetic for `good_ne_charTwo_v2` (a copy of `KpECharTwoAux`).
-/
namespace GoodNeCharTwoV2Aux

variable {K : Type} [Field K]

lemma two_eq_zero_of_ringChar_two (h2 : ringChar K = 2) : (2 : K) = 0 := by
  haveI hch : CharP K 2 := ringChar.eq_iff.mp h2
  exact CharP.cast_eq_zero K 2

lemma eleven_eq_one_of_ringChar_two (h2 : ringChar K = 2) : (11 : K) = 1 := by
  have h20 : (2 : K) = 0 := two_eq_zero_of_ringChar_two h2
  have h : (11 : K) = (2 : K) * 5 + 1 := by norm_num
  rw [h, h20, zero_mul, zero_add]

lemma eval_kpC4f1 (u : K) :
    (Work.MotT.kpC4f1 K).eval u = u ^ 4 + 3 * u ^ 3 - u ^ 2 - 3 * u + 1 := by
  rw [Work.MotT.kpC4f1]
  simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_ofNat, eval_one]

lemma eval_kpC4f2 (u : K) :
    (Work.MotT.kpC4f2 K).eval u =
      u ^ 8 + u ^ 7 + 7 * u ^ 6 - 7 * u ^ 5 + 7 * u ^ 3 + 7 * u ^ 2 - u + 1 := by
  rw [Work.MotT.kpC4f2]
  simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_ofNat, eval_one]

lemma eval_kpC4f3 (u : K) :
    (Work.MotT.kpC4f3 K).eval u =
      u ^ 8 - 4 * u ^ 7 + 7 * u ^ 6 - 2 * u ^ 5 + 15 * u ^ 4 + 2 * u ^ 3 + 7 * u ^ 2 + 4 * u + 1 := by
  rw [Work.MotT.kpC4f3]
  simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_ofNat, eval_one]

lemma eval_kpC4Num (u : K) :
    (Work.MotT.kpC4Num K).eval u = (Work.MotT.kpC4f1 K).eval u * (Work.MotT.kpC4f2 K).eval u *
      (Work.MotT.kpC4f3 K).eval u := by
  rw [Work.MotT.kpC4Num, eval_mul, eval_mul]

/-- The certificate `f₁·f₂·f₃ = (X⁵+1)⁴ + 2·(112X¹⁵ + 244X¹⁰ - 116X⁵)`. -/
lemma kpC4f_prod_certificate (u : K) :
    (u ^ 4 + 3 * u ^ 3 - u ^ 2 - 3 * u + 1) *
        (u ^ 8 + u ^ 7 + 7 * u ^ 6 - 7 * u ^ 5 + 7 * u ^ 3 + 7 * u ^ 2 - u + 1) *
      (u ^ 8 - 4 * u ^ 7 + 7 * u ^ 6 - 2 * u ^ 5 + 15 * u ^ 4 + 2 * u ^ 3 + 7 * u ^ 2 + 4 * u + 1)
    = (u ^ 5 + 1) ^ 4 + (2 : K) * (112 * u ^ 15 + 244 * u ^ 10 - 116 * u ^ 5) := by
  first | refl_ring1 | ring

/-- **The `c₄`-numerator vanishes at every fifth root of unity in characteristic two.** -/
theorem kpC4Num_eval_eq_zero_of_pow_five_eq_one (h2 : ringChar K = 2) {u : K} (hu : u ^ 5 = 1) :
    (Work.MotT.kpC4Num K).eval u = 0 := by
  have h20 : (2 : K) = 0 := two_eq_zero_of_ringChar_two h2
  have hu10 : u ^ 10 = 1 := by
    rw [show (10 : ℕ) = 5 * 2 by norm_num, pow_mul, hu, one_pow]
  have hu15 : u ^ 15 = 1 := by
    rw [show (15 : ℕ) = 5 * 3 by norm_num, pow_mul, hu, one_pow]
  rw [eval_kpC4Num, eval_kpC4f1, eval_kpC4f2, eval_kpC4f3, kpC4f_prod_certificate u]
  rw [hu10, hu15, hu, show (1 : K) + 1 = (2 : K) by norm_num, h20]
  first | refl_ring1 | ring

lemma ne_zero_of_pow_five_eq_one {u : K} (hu : u ^ 5 = 1) : u ≠ 0 := by
  intro h0
  rw [h0, zero_pow (by norm_num : (5 : ℕ) ≠ 0)] at hu
  exact zero_ne_one hu

/-- In characteristic two, `kpW u = 2u⁵ - 1` is nonzero at every fifth root of unity. -/
lemma kpW_ne_zero_of_pow_five_eq_one (h2 : ringChar K = 2) {u : K} (hu : u ^ 5 = 1) :
    Work.MotT.kpW K u ≠ 0 := by
  have h20 : (2 : K) = 0 := two_eq_zero_of_ringChar_two h2
  rw [Work.MotT.kpW, hu, h20, zero_mul, zero_sub]
  exact neg_ne_zero.mpr one_ne_zero

/-- In characteristic two, `kpDelta u = u¹⁰ - 11u⁵ - 1` is nonzero at every fifth root of unity. -/
lemma kpDelta_ne_zero_of_pow_five_eq_one (h2 : ringChar K = 2) {u : K} (hu : u ^ 5 = 1) :
    Work.MotT.kpDelta K u ≠ 0 := by
  have h11 : (11 : K) = 1 := eleven_eq_one_of_ringChar_two h2
  have h10 : u ^ 10 = 1 := by
    rw [show (10 : ℕ) = 5 * 2 by norm_num, pow_mul, hu, one_pow]
  rw [Work.MotT.kpDelta, h10, h11, hu, mul_one, show (1 : K) - 1 - 1 = -1 by ring]
  exact neg_ne_zero.mpr one_ne_zero

end GoodNeCharTwoV2Aux

/-- In characteristic `2`, `D.Good` forces `D.a⁵ ≠ D.b⁵` (alternative proof via the parametric
Klein model). -/
theorem good_ne_charTwo_v2 (K : Type) [Field K] (D : Work.MotV.KleinData K) (hD : D.Good)
    (h2 : ringChar K = 2) : D.a ^ 5 ≠ D.b ^ 5 := by
  have hk5 : ringChar K ≠ 5 := by rw [h2]; norm_num
  have hDa : D.a ≠ 0 := (mul_ne_zero_iff.mp hD.ab_ne).1
  have hDb : D.b ≠ 0 := (mul_ne_zero_iff.mp hD.ab_ne).2
  intro hab
  -- the parameter `u = D.a / D.b` is a fifth root of unity
  have hu5 : (D.a / D.b) ^ 5 = 1 := by
    rw [div_pow, hab, div_self (pow_ne_zero 5 hDb)]
  have hu : D.a / D.b ≠ 0 := div_ne_zero hDa hDb
  -- the parametric model at `u` is non-degenerate and has `j = 0`
  have hw : Work.MotT.kpW K (D.a / D.b) ≠ 0 :=
    GoodNeCharTwoV2Aux.kpW_ne_zero_of_pow_five_eq_one h2 hu5
  have hΔ : Work.MotT.kpDelta K (D.a / D.b) ≠ 0 :=
    GoodNeCharTwoV2Aux.kpDelta_ne_zero_of_pow_five_eq_one h2 hu5
  have hnum : (Work.MotT.kpC4Num K).eval (D.a / D.b) = 0 :=
    GoodNeCharTwoV2Aux.kpC4Num_eval_eq_zero_of_pow_five_eq_one h2 hu5
  haveI hEll : (Work.MotT.kpE K (D.a / D.b)).IsElliptic :=
    (Work.MotT.kpE_invariants K hk5 (D.a / D.b) hu hw hΔ).1
  haveI hEll' : (Work.MotT.kpData K (D.a / D.b)).E.IsElliptic := hEll
  haveI hEllD : D.E.IsElliptic := hD.elliptic
  -- the rescaled datum with `b = 1` (same `E` and `coord` as `D`)
  let D₁ : Work.MotV.KleinData K := { D with a := D.a / D.b, b := 1 }
  have hD1a : D₁.a = (Work.MotT.kpData K (D.a / D.b)).a := rfl
  have hD1b : D₁.b = (Work.MotT.kpData K (D.a / D.b)).b := rfl
  have hab1 : (Work.MotT.kpData K (D.a / D.b)).a * (Work.MotT.kpData K (D.a / D.b)).b ≠ 0 := by
    show D.a / D.b * 1 ≠ 0
    rw [mul_one]
    exact hu
  -- `klein_eq` for `D₁`, from the homogeneity of `kleinP` in `(a, b)`
  have hkl1 : ∀ (L : Type) [Field L] [Algebra K L] (k : Fin 5),
      Work.MotK.kleinP (algebraMap K _ D₁.a) (algebraMap K _ D₁.b)
        (Work.MotV.kleinCoord D₁ L) k = 0 := by
    intro L _ _ k
    change Work.MotK.kleinP
      (algebraMap K (WeierstrassCurve.Affine.FunctionField (D.E.baseChange L)) (D.a / D.b))
      (algebraMap K (WeierstrassCurve.Affine.FunctionField (D.E.baseChange L)) (1 : K))
      (Work.MotV.kleinCoord D L) k = 0
    have ha' : algebraMap K (WeierstrassCurve.Affine.FunctionField (D.E.baseChange L)) (D.a / D.b)
        = algebraMap K (WeierstrassCurve.Affine.FunctionField (D.E.baseChange L)) D.b⁻¹ *
          algebraMap K (WeierstrassCurve.Affine.FunctionField (D.E.baseChange L)) D.a := by
      rw [div_eq_mul_inv, map_mul, map_inv₀, mul_comm]
    have hb' : algebraMap K (WeierstrassCurve.Affine.FunctionField (D.E.baseChange L)) (1 : K)
        = algebraMap K (WeierstrassCurve.Affine.FunctionField (D.E.baseChange L)) D.b⁻¹ *
          algebraMap K (WeierstrassCurve.Affine.FunctionField (D.E.baseChange L)) D.b := by
      rw [map_one, ← map_mul, inv_mul_cancel₀ hDb, map_one]
    rw [ha', hb', Work.MotT.kleinP_smul_ab, hD.klein_eq L k, mul_zero]
  have hkl2 : ∀ (L : Type) [Field L] [Algebra K L] (k : Fin 5),
      Work.MotK.kleinP (algebraMap K _ (Work.MotT.kpData K (D.a / D.b)).a)
        (algebraMap K _ (Work.MotT.kpData K (D.a / D.b)).b)
        (Work.MotV.kleinCoord (Work.MotT.kpData K (D.a / D.b)) L) k = 0 :=
    Work.MotT.kpData_klein_eq K hk5 (D.a / D.b) hu hw hΔ
  have h01 : ∀ (L : Type) [Field L] [Algebra K L], Work.MotV.kleinCoord D₁ L 0 ≠ 0 := hD.coord0_ne
  have hsp1 : ∃ e : Fin 5 → Fin 5 → K, ∀ (L : Type) [Field L] [Algebra K L] (m : Fin 5),
      Work.MotV.kleinBas D₁ L m =
        ∑ i, algebraMap L _ (algebraMap K L (e m i)) * Work.MotV.kleinCoord D₁ L i := hD.spans
  have hsp2 : ∃ e : Fin 5 → Fin 5 → K, ∀ (L : Type) [Field L] [Algebra K L] (m : Fin 5),
      Work.MotV.kleinBas (Work.MotT.kpData K (D.a / D.b)) L m =
        ∑ i, algebraMap L _ (algebraMap K L (e m i)) *
          Work.MotV.kleinCoord (Work.MotT.kpData K (D.a / D.b)) L i :=
    Work.MotT.kpData_spans_good K hk5 (D.a / D.b) hu hw hΔ
  -- same Klein parameters ⟹ isomorphic function fields
  obtain ⟨Θ⟩ := Work.MotK.TwRuling.exists_algEquiv_of_same_ab_v3 K D₁
    (Work.MotT.kpData K (D.a / D.b)) hD1a hD1b hab1 hkl1 hkl2 h01 hsp1 hsp2
  -- `j(D.E) = j(kpE K u) = 0`
  have hjEq : (Work.MotT.kpE K (D.a / D.b)).j = D.E.j := by
    have h := Work.MotK.TwRuling.j_eq_of_funcAlgEquiv_v2 K
      (Work.MotT.kpData K (D.a / D.b)).E D.E Θ
    simpa only [Work.MotT.kpData_E] using h
  have hj0 : (Work.MotT.kpE K (D.a / D.b)).j = 0 := by
    obtain ⟨-, -, hc4⟩ := Work.MotT.kpE_invariants K hk5 (D.a / D.b) hu hw hΔ
    have hc40 : (Work.MotT.kpE K (D.a / D.b)).c₄ = 0 := by
      rw [hc4, ← GoodNeCharTwoV2Aux.eval_kpC4f1 (D.a / D.b),
        ← GoodNeCharTwoV2Aux.eval_kpC4f2 (D.a / D.b),
        ← GoodNeCharTwoV2Aux.eval_kpC4f3 (D.a / D.b),
        ← GoodNeCharTwoV2Aux.eval_kpC4Num (D.a / D.b), hnum, zero_div]
    rw [WeierstrassCurve.j_eq, hc40]
    first | refl_ring1 | ring
  exact hD.j_ne_zero (hjEq.symm.trans hj0)

end Work.MotK.TwRuling
