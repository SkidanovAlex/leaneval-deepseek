import Mathlib
import Submission.Work.MotC.WireU.CharTwoDefs
import Submission.Work.MotC.WireU.ord_charTwo_weierstrass_pole
import Submission.Work.MotC.WireU.ordInf_charTwo_weierstrass_pole
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace Work.MotC.WireU

open Polynomial

section CharTwoOrder

variable {K : Type*} [Field K] [CharP K 2]

/-! ### The `2`-torsion point: the residue computation -/

/-- **The residue computation as a divisibility.**  In characteristic two, the polynomial
`a₁⁴ Φ - Δ` vanishes at `a₃/a₁`, i.e. `(X - a₃/a₁) ∣ (a₁⁴ Φ - Δ)`. -/
theorem dvd_X_sub_C_phiPoly_sub (E : WeierstrassCurve K) (ha1 : E.a₁ ≠ 0) :
    (X - C (E.a₃ / E.a₁)) ∣ (C (E.a₁ ^ 4) * phiPoly E - C E.Δ) :=
  Polynomial.dvd_iff_isRoot.mpr (by
    rw [IsRoot, eval_sub, eval_mul, eval_C, a1_pow_four_phiPoly_eval_div_eq_delta E ha1, eval_C,
      sub_self])

/-! ### `W = a₁ x + a₃` is regular where `x` is -/

theorem ord_wOf_nonneg (E : WeierstrassCurve K) {x : RatFunc K} {π : Polynomial K}
    (hπ : Irreducible π) (hx : 0 ≤ Work.Genus.ord π x) :
    0 ≤ Work.Genus.ord π (wOf E x) := by
  rcases eq_or_ne E.a₁ 0 with h1 | h1
  · rw [wOf_eq, h1, map_zero, zero_mul, zero_add, ord_algebraMap_eq_zero]
  rcases eq_or_ne x 0 with hx0 | hx0
  · rw [wOf_eq, hx0, mul_zero, zero_add, ord_algebraMap_eq_zero]
  rcases eq_or_ne E.a₃ 0 with h3 | h3
  · rw [wOf_eq, h3, map_zero, add_zero, Work.Genus.Order.ord_C_mul h1 x]; exact hx
  · by_cases hw0 : wOf E x = 0
    · rw [hw0, Work.Genus.Order.ord_zero]
    · have hne : algebraMap K (RatFunc K) E.a₁ * x ≠ 0 :=
        mul_ne_zero (by rw [algebraMap_ratFunc_ne_zero_iff]; exact h1) hx0
      have hne3 : algebraMap K (RatFunc K) E.a₃ ≠ 0 := by
        rw [algebraMap_ratFunc_ne_zero_iff]; exact h3
      have hmm := Work.Genus.Order.min_ord_le_ord_add hπ hne hne3 hw0
      rw [Work.Genus.Order.ord_C_mul h1 x, ord_algebraMap_eq_zero] at hmm
      rw [min_eq_right hx] at hmm
      exact hmm

theorem ordInf_wOf_nonneg (E : WeierstrassCurve K) {x : RatFunc K}
    (hx : 0 ≤ Work.Genus.ordInf x) : 0 ≤ Work.Genus.ordInf (wOf E x) := by
  rcases eq_or_ne E.a₁ 0 with h1 | h1
  · rw [wOf_eq, h1, map_zero, zero_mul, zero_add, ordInf_algebraMap_eq_zero]
  rcases eq_or_ne x 0 with hx0 | hx0
  · rw [wOf_eq, hx0, mul_zero, zero_add, ordInf_algebraMap_eq_zero]
  rcases eq_or_ne E.a₃ 0 with h3 | h3
  · rw [wOf_eq, h3, map_zero, add_zero, Work.Genus.OrderInf.ordInf_C_mul h1 x]; exact hx
  · by_cases hw0 : wOf E x = 0
    · rw [hw0, Work.Genus.ordInf, RatFunc.intDegree_zero, neg_zero]
    · have hne : algebraMap K (RatFunc K) E.a₁ * x ≠ 0 :=
        mul_ne_zero (by rw [algebraMap_ratFunc_ne_zero_iff]; exact h1) hx0
      have hne3 : algebraMap K (RatFunc K) E.a₃ ≠ 0 := by
        rw [algebraMap_ratFunc_ne_zero_iff]; exact h3
      have hmm := Work.Genus.OrderInf.min_ordInf_le_ordInf_add hne hne3 hw0
      rw [Work.Genus.OrderInf.ordInf_C_mul h1 x, ordInf_algebraMap_eq_zero] at hmm
      rw [min_eq_right hx] at hmm
      exact hmm

/-! ### The factorisation of the Weierstrass equation -/

theorem y_mul_y_add_w (E : WeierstrassCurve K) {x y : RatFunc K} (h : Work.Genus.CharP.WEqn E x y) :
    y * (y + wOf E x) = aeval x (cubicA E) := by
  rw [wOf_eq, aeval_cubicA]
  unfold Work.Genus.CharP.WEqn at h
  linear_combination (norm := first | refl_ring1 | ring1) h

/-! ### Poles of `y` are poles of `x` -/

theorem ord_add_nonneg {π : Polynomial K} (hπ : Irreducible π) {u v : RatFunc K}
    (hu : 0 ≤ Work.Genus.ord π u) (hv : 0 ≤ Work.Genus.ord π v) :
    0 ≤ Work.Genus.ord π (u + v) := by
  by_cases h : u + v = 0
  · rw [h, Work.Genus.Order.ord_zero]
  by_cases hu0 : u = 0
  · rw [hu0, zero_add]; exact hv
  by_cases hv0 : v = 0
  · rw [hv0, add_zero]; exact hu
  · exact le_trans (le_min hu hv) (Work.Genus.Order.min_ord_le_ord_add hπ hu0 hv0 h)

theorem ordInf_add_nonneg {u v : RatFunc K}
    (hu : 0 ≤ Work.Genus.ordInf u) (hv : 0 ≤ Work.Genus.ordInf v) :
    0 ≤ Work.Genus.ordInf (u + v) := by
  by_cases h : u + v = 0
  · rw [h, Work.Genus.ordInf, RatFunc.intDegree_zero, neg_zero]
  by_cases hu0 : u = 0
  · rw [hu0, zero_add]; exact hv
  by_cases hv0 : v = 0
  · rw [hv0, add_zero]; exact hu
  · exact le_trans (le_min hu hv) (Work.Genus.OrderInf.min_ordInf_le_ordInf_add hu0 hv0 h)

theorem ord_y_nonneg_of_ord_x_nonneg (E : WeierstrassCurve K) {x y : RatFunc K}
    (h : Work.Genus.CharP.WEqn E x y) {π : Polynomial K} (hπ : Irreducible π)
    (hx : 0 ≤ Work.Genus.ord π x) : 0 ≤ Work.Genus.ord π y := by
  have h2 : (2 : RatFunc K) = 0 := CharP.cast_eq_zero _ _
  have hw : 0 ≤ Work.Genus.ord π (wOf E x) := ord_wOf_nonneg E hπ hx
  have hAy : 0 ≤ Work.Genus.ord π (aeval x (cubicA E)) :=
    Work.Genus.Order.ord_aeval_nonneg hπ hx
  have hkey := y_mul_y_add_w E h
  rcases eq_or_ne y 0 with hy0 | hy0
  · rw [hy0, Work.Genus.Order.ord_zero]
  rcases eq_or_ne (y + wOf E x) 0 with hyw | hyw
  · have : y = wOf E x := by linear_combination hyw - (wOf E x) * h2
    rw [this]; exact hw
  · have hmul := Work.Genus.Order.ord_mul hπ hy0 hyw
    rw [hkey] at hmul
    by_contra hcon
    push Not at hcon
    have hlt : Work.Genus.ord π y < Work.Genus.ord π (wOf E x) := lt_of_lt_of_le hcon hw
    have hadd := Work.Genus.Order.ord_add_eq_of_lt hπ hy0 hlt
    rw [hadd] at hmul
    linarith

theorem ordInf_y_nonneg_of_ordInf_x_nonneg (E : WeierstrassCurve K) {x y : RatFunc K}
    (h : Work.Genus.CharP.WEqn E x y) (hx : 0 ≤ Work.Genus.ordInf x) :
    0 ≤ Work.Genus.ordInf y := by
  have h2 : (2 : RatFunc K) = 0 := CharP.cast_eq_zero _ _
  have hw : 0 ≤ Work.Genus.ordInf (wOf E x) := ordInf_wOf_nonneg E hx
  have hAy : 0 ≤ Work.Genus.ordInf (aeval x (cubicA E)) :=
    Work.Genus.OrderInf.ordInf_aeval_nonneg hx
  have hkey := y_mul_y_add_w E h
  rcases eq_or_ne y 0 with hy0 | hy0
  · rw [hy0, Work.Genus.ordInf, RatFunc.intDegree_zero, neg_zero]
  rcases eq_or_ne (y + wOf E x) 0 with hyw | hyw
  · have : y = wOf E x := by linear_combination hyw - (wOf E x) * h2
    rw [this]; exact hw
  · have hmul := Work.Genus.OrderInf.ordInf_mul hy0 hyw
    rw [hkey] at hmul
    by_contra hcon
    push Not at hcon
    have hlt : Work.Genus.ordInf y < Work.Genus.ordInf (wOf E x) := lt_of_lt_of_le hcon hw
    have hadd := Work.Genus.OrderInf.ordInf_add_eq_of_lt hy0 hlt
    rw [hadd] at hmul
    linarith

end CharTwoOrder

end Work.MotC.WireU

namespace Work.MotC.WireU

open Polynomial

section CharTwoEta

variable {K : Type*} [Field K] [CharP K 2]

theorem cubicA_ne_zero (E : WeierstrassCurve K) : cubicA E ≠ 0 := by
  intro h
  have := cubicA_natDegree E
  rw [h] at this
  simp at this

/-- The factorisation `W = a₁ (x - a₃/a₁)` of `wOf`. -/
theorem wOf_eq_mul_sub (E : WeierstrassCurve K) (ha1 : E.a₁ ≠ 0) (x : RatFunc K) :
    wOf E x = algebraMap K (RatFunc K) E.a₁
      * (x - algebraMap K (RatFunc K) (E.a₃ / E.a₁)) := by
  have h2 : (2 : RatFunc K) = 0 := CharP.cast_eq_zero _ _
  have hdiv : E.a₁ * (E.a₃ / E.a₁) = E.a₃ := by rw [mul_comm, div_mul_cancel₀ _ ha1]
  have hkey' : algebraMap K (RatFunc K) E.a₁ * algebraMap K (RatFunc K) (E.a₃ / E.a₁)
      = algebraMap K (RatFunc K) E.a₃ := by rw [← map_mul, hdiv]
  rw [wOf_eq]
  linear_combination (norm := first | refl_ring1 | ring1) (algebraMap K (RatFunc K) E.a₃) * h2 + hkey'

/-- **`y ≠ 0` when `W` has positive order at a place.**  Otherwise `x` would be a root of the cubic
`A`, hence a constant, and `W` would be a constant with order `0`. -/
theorem y_ne_zero_of_ord_wOf_pos (E : WeierstrassCurve K) {x y : RatFunc K}
    (h : Work.Genus.CharP.WEqn E x y) {π : Polynomial K} (hw : 0 < Work.Genus.ord π (wOf E x)) :
    y ≠ 0 := by
  intro h0
  have hA0 : aeval x (cubicA E) = 0 := by
    have hk := y_mul_y_add_w E h
    rw [h0, zero_mul] at hk
    exact hk.symm
  obtain ⟨c, hc⟩ := Work.Genus.Main.exists_algebraMap_eq_of_isAlgebraic (F := K)
    ⟨cubicA E, cubicA_ne_zero E, hA0⟩
  have hw' : wOf E (algebraMap K (RatFunc K) c) = algebraMap K (RatFunc K) (E.a₁ * c + E.a₃) := by
    rw [wOf_eq, ← map_mul, ← map_add]
  rw [hc, hw', ord_algebraMap_eq_zero] at hw
  exact lt_irrefl 0 hw

theorem y_ne_zero_of_ordInf_wOf_pos (E : WeierstrassCurve K) {x y : RatFunc K}
    (h : Work.Genus.CharP.WEqn E x y) (hw : 0 < Work.Genus.ordInf (wOf E x)) : y ≠ 0 := by
  intro h0
  have hA0 : aeval x (cubicA E) = 0 := by
    have hk := y_mul_y_add_w E h
    rw [h0, zero_mul] at hk
    exact hk.symm
  obtain ⟨c, hc⟩ := Work.Genus.Main.exists_algebraMap_eq_of_isAlgebraic (F := K)
    ⟨cubicA E, cubicA_ne_zero E, hA0⟩
  have hw' : wOf E (algebraMap K (RatFunc K) c) = algebraMap K (RatFunc K) (E.a₁ * c + E.a₃) := by
    rw [wOf_eq, ← map_mul, ← map_add]
  rw [hc, hw', ordInf_algebraMap_eq_zero] at hw
  exact lt_irrefl 0 hw

/-- **`W` has no pole where `x` has none, and a zero of `W` is a zero of `x`.**  `W = a₁ (x - a₃/a₁)`,
so `ord π (x - a₃/a₁) = ord π W` whenever `W` does not vanish identically. -/
theorem ord_sub_div_eq_ord_wOf (E : WeierstrassCurve K) (ha1 : E.a₁ ≠ 0) {x : RatFunc K}
    {π : Polynomial K} (hπ : Irreducible π) (hw : wOf E x ≠ 0) :
    Work.Genus.ord π (x - algebraMap K (RatFunc K) (E.a₃ / E.a₁)) = Work.Genus.ord π (wOf E x) := by
  have hC : algebraMap K (RatFunc K) E.a₁ ≠ 0 := by
    rw [algebraMap_ratFunc_ne_zero_iff]; exact ha1
  have hxr : x - algebraMap K (RatFunc K) (E.a₃ / E.a₁) ≠ 0 := by
    intro h0
    rw [wOf_eq_mul_sub E ha1 x, h0, mul_zero] at hw
    exact hw rfl
  have := Work.Genus.Order.ord_mul hπ hC hxr
  rw [wOf_eq_mul_sub E ha1 x, this, ord_algebraMap_eq_zero, zero_add]

theorem ordInf_sub_div_eq_ordInf_wOf (E : WeierstrassCurve K) (ha1 : E.a₁ ≠ 0) {x : RatFunc K}
    (hw : wOf E x ≠ 0) :
    Work.Genus.ordInf (x - algebraMap K (RatFunc K) (E.a₃ / E.a₁))
      = Work.Genus.ordInf (wOf E x) := by
  have hC : algebraMap K (RatFunc K) E.a₁ ≠ 0 := by
    rw [algebraMap_ratFunc_ne_zero_iff]; exact ha1
  have hxr : x - algebraMap K (RatFunc K) (E.a₃ / E.a₁) ≠ 0 := by
    intro h0
    rw [wOf_eq_mul_sub E ha1 x, h0, mul_zero] at hw
    exact hw rfl
  have := Work.Genus.OrderInf.ordInf_mul hC hxr
  rw [wOf_eq_mul_sub E ha1 x, this, ordInf_algebraMap_eq_zero, zero_add]

/-- **The order of `η` at a pole of `x`.**  `η = a₁y + x² + a₄`; the dominant term is `x²` since
`ord π y = 3/2 ord π x`. -/
theorem ord_eta_eq_of_ord_x_neg (E : WeierstrassCurve K) {x y : RatFunc K}
    (h : Work.Genus.CharP.WEqn E x y) {π : Polynomial K} (hπ : Irreducible π)
    (hx : Work.Genus.ord π x < 0) :
    Work.Genus.ord π (etaOf E x y) = 2 * Work.Genus.ord π x := by
  have hpole := ord_charTwo_weierstrass_pole (K := K) E.a₁ E.a₂ E.a₃ E.a₄ E.a₆
    (x := x) (y := y) h hπ hx
  have hy : 2 * Work.Genus.ord π y = 3 * Work.Genus.ord π x := hpole.2
  have hx0 : x ≠ 0 := by
    intro h0; rw [h0, Work.Genus.Order.ord_zero] at hx; exact absurd hx (lt_irrefl 0)
  have hy0 : y ≠ 0 := by
    intro h0; rw [h0, Work.Genus.Order.ord_zero] at hy; linarith
  have hx2 : Work.Genus.ord π (x ^ 2) = 2 * Work.Genus.ord π x := by
    rw [Work.Genus.Order.ord_pow hπ hx0 2]; ring
  have hxa : Work.Genus.ord π (x ^ 2 + algebraMap K (RatFunc K) E.a₄) = 2 * Work.Genus.ord π x := by
    by_cases h4 : E.a₄ = 0
    · rw [h4, map_zero, add_zero]; exact hx2
    · have hlt : Work.Genus.ord π (x ^ 2) < Work.Genus.ord π (algebraMap K (RatFunc K) E.a₄) := by
        rw [hx2, ord_algebraMap_eq_zero]; linarith
      exact (Work.Genus.Order.ord_add_eq_of_lt hπ (pow_ne_zero 2 hx0) hlt).trans hx2
  rcases eq_or_ne E.a₁ 0 with h1 | h1
  · rw [etaOf_eq, h1, map_zero, zero_mul, zero_add]; exact hxa
  · rw [etaOf_eq, add_comm (algebraMap K (RatFunc K) E.a₁ * y) (x ^ 2)]
    have h1y : Work.Genus.ord π (algebraMap K (RatFunc K) E.a₁ * y) = Work.Genus.ord π y :=
      Work.Genus.Order.ord_C_mul h1 y
    have hlt1 : Work.Genus.ord π (x ^ 2) < Work.Genus.ord π (algebraMap K (RatFunc K) E.a₁ * y) := by
      rw [hx2, h1y]; linarith
    have hsum : Work.Genus.ord π (x ^ 2 + algebraMap K (RatFunc K) E.a₁ * y)
        = 2 * Work.Genus.ord π x :=
      (Work.Genus.Order.ord_add_eq_of_lt hπ (pow_ne_zero 2 hx0) hlt1).trans hx2
    have hsumne : x ^ 2 + algebraMap K (RatFunc K) E.a₁ * y ≠ 0 := by
      intro h0; rw [h0, Work.Genus.Order.ord_zero] at hsum; linarith
    have hlt2 : Work.Genus.ord π (x ^ 2 + algebraMap K (RatFunc K) E.a₁ * y)
        < Work.Genus.ord π (algebraMap K (RatFunc K) E.a₄) := by
      rw [hsum, ord_algebraMap_eq_zero]; linarith
    exact (Work.Genus.Order.ord_add_eq_of_lt hπ hsumne hlt2).trans hsum

theorem ordInf_eta_eq_of_ordInf_x_neg (E : WeierstrassCurve K) {x y : RatFunc K}
    (h : Work.Genus.CharP.WEqn E x y) (hx : Work.Genus.ordInf x < 0) :
    Work.Genus.ordInf (etaOf E x y) = 2 * Work.Genus.ordInf x := by
  have hpole := ordInf_charTwo_weierstrass_pole (K := K) E.a₁ E.a₂ E.a₃ E.a₄ E.a₆
    (x := x) (y := y) h hx
  have hy : 2 * Work.Genus.ordInf y = 3 * Work.Genus.ordInf x := hpole.2
  have hx0 : x ≠ 0 := by
    intro h0; rw [h0, Work.Genus.ordInf, RatFunc.intDegree_zero, neg_zero] at hx
    exact absurd hx (lt_irrefl 0)
  have hy0 : y ≠ 0 := by
    intro h0; rw [h0, Work.Genus.ordInf, RatFunc.intDegree_zero, neg_zero] at hy; linarith
  have hx2 : Work.Genus.ordInf (x ^ 2) = 2 * Work.Genus.ordInf x := by
    rw [Work.Genus.OrderInf.ordInf_pow hx0 2]; ring
  have hxa : Work.Genus.ordInf (x ^ 2 + algebraMap K (RatFunc K) E.a₄)
      = 2 * Work.Genus.ordInf x := by
    by_cases h4 : E.a₄ = 0
    · rw [h4, map_zero, add_zero]; exact hx2
    · have hlt : Work.Genus.ordInf (x ^ 2) < Work.Genus.ordInf (algebraMap K (RatFunc K) E.a₄) := by
        rw [hx2, ordInf_algebraMap_eq_zero]; linarith
      exact (Work.Genus.OrderInf.ordInf_add_eq_of_lt (pow_ne_zero 2 hx0) hlt).trans hx2
  rcases eq_or_ne E.a₁ 0 with h1 | h1
  · rw [etaOf_eq, h1, map_zero, zero_mul, zero_add]; exact hxa
  · rw [etaOf_eq, add_comm (algebraMap K (RatFunc K) E.a₁ * y) (x ^ 2)]
    have h1y : Work.Genus.ordInf (algebraMap K (RatFunc K) E.a₁ * y) = Work.Genus.ordInf y :=
      Work.Genus.OrderInf.ordInf_C_mul h1 y
    have hlt1 : Work.Genus.ordInf (x ^ 2) < Work.Genus.ordInf (algebraMap K (RatFunc K) E.a₁ * y) := by
      rw [hx2, h1y]; linarith
    have hsum : Work.Genus.ordInf (x ^ 2 + algebraMap K (RatFunc K) E.a₁ * y)
        = 2 * Work.Genus.ordInf x :=
      (Work.Genus.OrderInf.ordInf_add_eq_of_lt (pow_ne_zero 2 hx0) hlt1).trans hx2
    have hsumne : x ^ 2 + algebraMap K (RatFunc K) E.a₁ * y ≠ 0 := by
      intro h0
      rw [h0, Work.Genus.ordInf, RatFunc.intDegree_zero, neg_zero] at hsum
      linarith
    have hlt2 : Work.Genus.ordInf (x ^ 2 + algebraMap K (RatFunc K) E.a₁ * y)
        < Work.Genus.ordInf (algebraMap K (RatFunc K) E.a₄) := by
      rw [hsum, ordInf_algebraMap_eq_zero]; linarith
    exact (Work.Genus.OrderInf.ordInf_add_eq_of_lt hsumne hlt2).trans hsum

end CharTwoEta

end Work.MotC.WireU

namespace Work.MotC.WireU

open Polynomial

section CharTwoSmoothness

variable {K : Type*} [Field K] [CharP K 2]

/-- **`η` does not vanish at a zero of `W`** (characteristic two).  `W = a₁x + a₃` and
`η = a₁y + x² + a₄` are the two partial derivatives of the Weierstrass equation; they have no common
zero because the curve is non-singular (`Δ ≠ 0`, via the residue `a₁⁴Φ(a₃/a₁) = Δ`). -/
theorem ord_eta_eq_zero_of_ord_wOf_pos (E : WeierstrassCurve K) (hΔ : E.Δ ≠ 0) {x y : RatFunc K}
    (h : Work.Genus.CharP.WEqn E x y) {π : Polynomial K} (hπ : Irreducible π)
    (hx : 0 ≤ Work.Genus.ord π x) (hw : 0 < Work.Genus.ord π (wOf E x)) :
    Work.Genus.ord π (etaOf E x y) = 0 := by
  have ha1 : E.a₁ ≠ 0 := by
    intro h1
    rw [wOf_eq, h1, map_zero, zero_mul, zero_add, ord_algebraMap_eq_zero] at hw
    exact lt_irrefl 0 hw
  have hy : 0 ≤ Work.Genus.ord π y := ord_y_nonneg_of_ord_x_nonneg E h hπ hx
  have hy0 : y ≠ 0 := y_ne_zero_of_ord_wOf_pos E h hw
  have hwne : wOf E x ≠ 0 := fun h0 => by
    rw [h0, Work.Genus.Order.ord_zero] at hw; exact lt_irrefl 0 hw
  have hnonneg : 0 ≤ Work.Genus.ord π (etaOf E x y) := by
    rw [etaOf_eq]
    refine ord_add_nonneg hπ (ord_add_nonneg hπ ?_ ?_) ?_
    · rw [Work.Genus.Order.ord_C_mul ha1 y]; exact hy
    · rcases eq_or_ne x 0 with h0 | h0
      · rw [h0, pow_two, mul_zero, Work.Genus.Order.ord_zero]
      · rw [Work.Genus.Order.ord_pow hπ h0 2]; nlinarith
    · exact le_of_eq (ord_algebraMap_eq_zero π E.a₄).symm
  refine le_antisymm ?_ hnonneg
  by_contra hcon
  push Not at hcon
  have hne : etaOf E x y ≠ 0 := fun h0 => by
    rw [h0, Work.Genus.Order.ord_zero] at hcon; exact lt_irrefl 0 hcon
  have heta2 : 0 < Work.Genus.ord π (etaOf E x y ^ 2) := by
    rw [Work.Genus.Order.ord_pow hπ hne 2]
    exact mul_pos (by norm_num : (0 : ℤ) < 2) hcon
  have h1sq_ne : algebraMap K (RatFunc K) (E.a₁ ^ 2) ≠ 0 := by
    rw [algebraMap_ratFunc_ne_zero_iff]; exact pow_ne_zero 2 ha1
  have hWy : 0 < Work.Genus.ord π (algebraMap K (RatFunc K) (E.a₁ ^ 2) * wOf E x * y) := by
    rw [Work.Genus.Order.ord_mul hπ (mul_ne_zero h1sq_ne hwne) hy0,
      Work.Genus.Order.ord_C_mul (pow_ne_zero 2 ha1) (wOf E x)]
    linarith
  have hWyne : algebraMap K (RatFunc K) (E.a₁ ^ 2) * wOf E x * y ≠ 0 :=
    mul_ne_zero (mul_ne_zero h1sq_ne hwne) hy0
  obtain ⟨Z, hZ⟩ := dvd_X_sub_C_phiPoly_sub E ha1
  have heval : aeval x (C (E.a₁ ^ 4) * phiPoly E - C E.Δ)
      = (x - algebraMap K (RatFunc K) (E.a₃ / E.a₁)) * aeval x Z := by
    rw [hZ, map_mul, map_sub, aeval_X, aeval_C]
  have hxr : 0 < Work.Genus.ord π (x - algebraMap K (RatFunc K) (E.a₃ / E.a₁)) := by
    rw [ord_sub_div_eq_ord_wOf E ha1 hπ hwne]; exact hw
  have hxrne : x - algebraMap K (RatFunc K) (E.a₃ / E.a₁) ≠ 0 := fun h0 => by
    rw [h0, Work.Genus.Order.ord_zero] at hxr; exact lt_irrefl 0 hxr
  have hCΔne : algebraMap K (RatFunc K) E.Δ ≠ 0 := (algebraMap_ratFunc_ne_zero_iff).mpr hΔ
  have h1four_ne : algebraMap K (RatFunc K) (E.a₁ ^ 4) ≠ 0 := by
    rw [algebraMap_ratFunc_ne_zero_iff]; exact pow_ne_zero 4 ha1
  have hPhine : aeval x (phiPoly E) ≠ 0 := by
    intro h0
    have hQeq : aeval x (C (E.a₁ ^ 4) * phiPoly E - C E.Δ)
        = algebraMap K (RatFunc K) E.Δ := by
      simp only [map_sub, map_mul, aeval_C, h0, mul_zero, zero_sub]
      have h2 : (2 : RatFunc K) = 0 := CharP.cast_eq_zero _ _
      linear_combination (norm := first | refl_ring1 | ring1) (-(algebraMap K (RatFunc K) E.Δ)) * h2
    rcases eq_or_ne (aeval x Z) 0 with hZx | hZx
    · rw [heval, hZx, mul_zero] at hQeq
      exact hCΔne hQeq.symm
    · have hone : 0 < Work.Genus.ord π (aeval x (C (E.a₁ ^ 4) * phiPoly E - C E.Δ)) := by
        rw [heval, Work.Genus.Order.ord_mul hπ hxrne hZx]
        have hZnn : 0 ≤ Work.Genus.ord π (aeval x Z) :=
          Work.Genus.Order.ord_aeval_nonneg hπ hx
        linarith
      rw [hQeq, ord_algebraMap_eq_zero] at hone
      exact lt_irrefl 0 hone
  have hPhi0 : Work.Genus.ord π (aeval x (phiPoly E)) = 0 := by
    rw [← Work.Genus.Order.ord_C_mul (pow_ne_zero 4 ha1) (aeval x (phiPoly E))]
    by_cases hZx : aeval x Z = 0
    · have hkey : algebraMap K (RatFunc K) (E.a₁ ^ 4) * aeval x (phiPoly E)
          = algebraMap K (RatFunc K) E.Δ := by
        have hh : aeval x (C (E.a₁ ^ 4) * phiPoly E - C E.Δ) = 0 := by rw [heval, hZx, mul_zero]
        simp only [map_sub, map_mul, aeval_C, sub_eq_zero] at hh
        exact hh
      rw [hkey, ord_algebraMap_eq_zero]
    · have hQgt : 0 < Work.Genus.ord π (aeval x (C (E.a₁ ^ 4) * phiPoly E - C E.Δ)) := by
        rw [heval, Work.Genus.Order.ord_mul hπ hxrne hZx]
        have hZnn : 0 ≤ Work.Genus.ord π (aeval x Z) :=
          Work.Genus.Order.ord_aeval_nonneg hπ hx
        linarith
      have hkey2 : algebraMap K (RatFunc K) (E.a₁ ^ 4) * aeval x (phiPoly E)
          = algebraMap K (RatFunc K) E.Δ
            + aeval x (C (E.a₁ ^ 4) * phiPoly E - C E.Δ) := by
        simp only [map_sub, map_mul, aeval_C]; ring
      rw [hkey2, Work.Genus.Order.ord_add_eq_of_lt hπ hCΔne
        (by rw [ord_algebraMap_eq_zero]; exact hQgt), ord_algebraMap_eq_zero]
  have hPhi_ne : etaOf E x y ^ 2 + algebraMap K (RatFunc K) (E.a₁ ^ 2) * wOf E x * y ≠ 0 := by
    rw [← aeval_phiPoly_eq E h]; exact hPhine
  have hcontra := Work.Genus.Order.min_ord_le_ord_add hπ (pow_ne_zero 2 hne) hWyne hPhi_ne
  rw [← aeval_phiPoly_eq E h, hPhi0] at hcontra
  exact absurd (lt_of_lt_of_le (lt_min heta2 hWy) hcontra) (lt_irrefl 0)

theorem ordInf_eta_eq_zero_of_ordInf_wOf_pos (E : WeierstrassCurve K) (hΔ : E.Δ ≠ 0)
    {x y : RatFunc K} (h : Work.Genus.CharP.WEqn E x y)
    (hx : 0 ≤ Work.Genus.ordInf x) (hw : 0 < Work.Genus.ordInf (wOf E x)) :
    Work.Genus.ordInf (etaOf E x y) = 0 := by
  have ha1 : E.a₁ ≠ 0 := by
    intro h1
    rw [wOf_eq, h1, map_zero, zero_mul, zero_add, ordInf_algebraMap_eq_zero] at hw
    exact lt_irrefl 0 hw
  have hy : 0 ≤ Work.Genus.ordInf y := ordInf_y_nonneg_of_ordInf_x_nonneg E h hx
  have hy0 : y ≠ 0 := y_ne_zero_of_ordInf_wOf_pos E h hw
  have hwne : wOf E x ≠ 0 := fun h0 => by
    rw [h0, Work.Genus.ordInf, RatFunc.intDegree_zero, neg_zero] at hw; exact lt_irrefl 0 hw
  have hnonneg : 0 ≤ Work.Genus.ordInf (etaOf E x y) := by
    rw [etaOf_eq]
    refine ordInf_add_nonneg (ordInf_add_nonneg ?_ ?_) ?_
    · rw [Work.Genus.OrderInf.ordInf_C_mul ha1 y]; exact hy
    · rcases eq_or_ne x 0 with h0 | h0
      · rw [h0, pow_two, mul_zero, Work.Genus.ordInf, RatFunc.intDegree_zero, neg_zero]
      · rw [Work.Genus.OrderInf.ordInf_pow h0 2]; nlinarith
    · exact le_of_eq (ordInf_algebraMap_eq_zero E.a₄).symm
  refine le_antisymm ?_ hnonneg
  by_contra hcon
  push Not at hcon
  have hne : etaOf E x y ≠ 0 := fun h0 => by
    rw [h0, Work.Genus.ordInf, RatFunc.intDegree_zero, neg_zero] at hcon
    exact lt_irrefl 0 hcon
  have heta2 : 0 < Work.Genus.ordInf (etaOf E x y ^ 2) := by
    rw [Work.Genus.OrderInf.ordInf_pow hne 2]
    exact mul_pos (by norm_num : (0 : ℤ) < 2) hcon
  have h1sq_ne : algebraMap K (RatFunc K) (E.a₁ ^ 2) ≠ 0 := by
    rw [algebraMap_ratFunc_ne_zero_iff]; exact pow_ne_zero 2 ha1
  have hWy : 0 < Work.Genus.ordInf (algebraMap K (RatFunc K) (E.a₁ ^ 2) * wOf E x * y) := by
    rw [Work.Genus.OrderInf.ordInf_mul (mul_ne_zero h1sq_ne hwne) hy0,
      Work.Genus.OrderInf.ordInf_C_mul (pow_ne_zero 2 ha1) (wOf E x)]
    linarith
  have hWyne : algebraMap K (RatFunc K) (E.a₁ ^ 2) * wOf E x * y ≠ 0 :=
    mul_ne_zero (mul_ne_zero h1sq_ne hwne) hy0
  obtain ⟨Z, hZ⟩ := dvd_X_sub_C_phiPoly_sub E ha1
  have heval : aeval x (C (E.a₁ ^ 4) * phiPoly E - C E.Δ)
      = (x - algebraMap K (RatFunc K) (E.a₃ / E.a₁)) * aeval x Z := by
    rw [hZ, map_mul, map_sub, aeval_X, aeval_C]
  have hxr : 0 < Work.Genus.ordInf (x - algebraMap K (RatFunc K) (E.a₃ / E.a₁)) := by
    rw [ordInf_sub_div_eq_ordInf_wOf E ha1 hwne]; exact hw
  have hxrne : x - algebraMap K (RatFunc K) (E.a₃ / E.a₁) ≠ 0 := fun h0 => by
    rw [h0, Work.Genus.ordInf, RatFunc.intDegree_zero, neg_zero] at hxr
    exact lt_irrefl 0 hxr
  have hCΔne : algebraMap K (RatFunc K) E.Δ ≠ 0 := (algebraMap_ratFunc_ne_zero_iff).mpr hΔ
  have h1four_ne : algebraMap K (RatFunc K) (E.a₁ ^ 4) ≠ 0 := by
    rw [algebraMap_ratFunc_ne_zero_iff]; exact pow_ne_zero 4 ha1
  have hPhine : aeval x (phiPoly E) ≠ 0 := by
    intro h0
    have hQeq : aeval x (C (E.a₁ ^ 4) * phiPoly E - C E.Δ)
        = algebraMap K (RatFunc K) E.Δ := by
      simp only [map_sub, map_mul, aeval_C, h0, mul_zero, zero_sub]
      have h2 : (2 : RatFunc K) = 0 := CharP.cast_eq_zero _ _
      linear_combination (norm := first | refl_ring1 | ring1) (-(algebraMap K (RatFunc K) E.Δ)) * h2
    rcases eq_or_ne (aeval x Z) 0 with hZx | hZx
    · rw [heval, hZx, mul_zero] at hQeq
      exact hCΔne hQeq.symm
    · have hone : 0 < Work.Genus.ordInf (aeval x (C (E.a₁ ^ 4) * phiPoly E - C E.Δ)) := by
        rw [heval, Work.Genus.OrderInf.ordInf_mul hxrne hZx]
        have hZnn : 0 ≤ Work.Genus.ordInf (aeval x Z) :=
          Work.Genus.OrderInf.ordInf_aeval_nonneg hx
        linarith
      rw [hQeq, ordInf_algebraMap_eq_zero] at hone
      exact lt_irrefl 0 hone
  have hPhi0 : Work.Genus.ordInf (aeval x (phiPoly E)) = 0 := by
    rw [← Work.Genus.OrderInf.ordInf_C_mul (pow_ne_zero 4 ha1) (aeval x (phiPoly E))]
    by_cases hZx : aeval x Z = 0
    · have hkey : algebraMap K (RatFunc K) (E.a₁ ^ 4) * aeval x (phiPoly E)
          = algebraMap K (RatFunc K) E.Δ := by
        have hh : aeval x (C (E.a₁ ^ 4) * phiPoly E - C E.Δ) = 0 := by rw [heval, hZx, mul_zero]
        simp only [map_sub, map_mul, aeval_C, sub_eq_zero] at hh
        exact hh
      rw [hkey, ordInf_algebraMap_eq_zero]
    · have hQgt : 0 < Work.Genus.ordInf (aeval x (C (E.a₁ ^ 4) * phiPoly E - C E.Δ)) := by
        rw [heval, Work.Genus.OrderInf.ordInf_mul hxrne hZx]
        have hZnn : 0 ≤ Work.Genus.ordInf (aeval x Z) :=
          Work.Genus.OrderInf.ordInf_aeval_nonneg hx
        linarith
      have hkey2 : algebraMap K (RatFunc K) (E.a₁ ^ 4) * aeval x (phiPoly E)
          = algebraMap K (RatFunc K) E.Δ
            + aeval x (C (E.a₁ ^ 4) * phiPoly E - C E.Δ) := by
        simp only [map_sub, map_mul, aeval_C]; ring
      rw [hkey2, Work.Genus.OrderInf.ordInf_add_eq_of_lt hCΔne
        (by rw [ordInf_algebraMap_eq_zero]; exact hQgt), ordInf_algebraMap_eq_zero]
  have hPhi_ne : etaOf E x y ^ 2 + algebraMap K (RatFunc K) (E.a₁ ^ 2) * wOf E x * y ≠ 0 := by
    rw [← aeval_phiPoly_eq E h]; exact hPhine
  have hcontra := Work.Genus.OrderInf.min_ordInf_le_ordInf_add (pow_ne_zero 2 hne) hWyne hPhi_ne
  rw [← aeval_phiPoly_eq E h, hPhi0] at hcontra
  exact absurd (lt_of_lt_of_le (lt_min heta2 hWy) hcontra) (lt_irrefl 0)

end CharTwoSmoothness

end Work.MotC.WireU
