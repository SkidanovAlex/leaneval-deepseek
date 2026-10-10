import Mathlib
import Submission.Work.MotC.WireU.CharTwoDefs
import Submission.Work.MotC.WireU.CharTwoOrder
import Submission.Work.Genus.CharP.isConst_of_isConst_abscissa
import Submission.Work.Genus.CharP.equation_rootTwist
import Submission.Work.Genus.CharP.rootTwist_discriminant
import Submission.Work.Genus.CharP.exists_pow_eq_of_deriv_eq_zero
import Submission.Work.Genus.CharP.natDegree_num_pow
import Submission.Work.Genus.CharP.natDegree_denom_pow
import Submission.Work.Genus.CharP.size_lt_of_pow_eq
import Submission.Work.Genus.Main.exists_algebraMap_eq_of_isAlgebraic
import Submission.Work.Wire123.RatFuncCoeff
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

/-!
# A non-singular Weierstrass curve has no non-constant `K(t)`-point, in characteristic two

This is the characteristic-two case of `E(K(t)) = E(K)` ("an elliptic curve is not uniruled").
The characteristic-`p ≠ 2` argument (`Work.Genus.CharP.exists_algebraMap_of_weierstrass_charP`)
completes the square, `w = 2y + a₁x + a₃`, obtains `w² = A(x)` for a squarefree cubic `A` and applies
Riemann–Hurwitz.  In characteristic two the completion of the square degenerates (`A` becomes a
quadratic modulo squares), so the argument below uses a different regular differential,

  `ω = dx / W = dy / η`,   `W = a₁x + a₃`, `η = a₁y + x² + a₄`,

the two partial derivatives of the Weierstrass equation.  These have **no common zero** on the curve
(`Δ ≠ 0` gives the residue identity `a₁⁴Φ(a₃/a₁) = Δ`), which is what replaces the squarefree-cubic
input.  The pullback `(x'/W) dt` is then regular on `ℙ¹` and hence zero, forcing `x' = y' = 0`; the
Frobenius descent (the root twist `E^{(1/2)}`) finishes exactly as in the `p ≠ 2` chapter.
-/

namespace Work.MotC.WireU

open Polynomial
open Work.Wire123

section Main

variable {K : Type*} [Field K] [CharP K 2]

theorem deriv_algebraMap_eq_zero (c : K) :
    Work.Genus.deriv (algebraMap K (RatFunc K) c) = 0 := by
  rw [RatFunc.algebraMap_eq_C, ← RatFunc.algebraMap_C, Work.Genus.Deriv.deriv_algebraMap,
    Polynomial.derivative_C, map_zero]

theorem deriv_zero_ratFunc : Work.Genus.deriv (0 : RatFunc K) = 0 := by
  simp [Work.Genus.deriv]

/-- A rational function of size zero is a constant. -/
theorem isConst_of_size_eq_zero {x : RatFunc K} (h : Work.Genus.CharP.Size x = 0) :
    Work.Genus.CharP.IsConst x := by
  have hn : x.num.natDegree = 0 := by
    have := h; simp only [Work.Genus.CharP.Size] at this; omega
  have hd : x.denom.natDegree = 0 := by
    have := h; simp only [Work.Genus.CharP.Size] at this; omega
  have hnum : x.num = Polynomial.C (x.num.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hn
  have hden : x.denom = Polynomial.C (x.denom.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hd
  have hx' : algebraMap (Polynomial K) (RatFunc K) x.num
        / algebraMap (Polynomial K) (RatFunc K) x.denom
      = algebraMap K (RatFunc K) (x.num.coeff 0 / x.denom.coeff 0) := by
    conv_lhs => rw [hnum, hden]
    rw [RatFunc.algebraMap_C, RatFunc.algebraMap_C, ← map_div₀ RatFunc.C,
      ← RatFunc.algebraMap_eq_C]
  refine ⟨x.num.coeff 0 / x.denom.coeff 0, ?_⟩
  rw [← hx']
  exact (RatFunc.num_div_denom x).symm

/-- **If `η = 0`, then `x` is constant.**  Then `a₁y = x² + a₄ =: P`, and the Weierstrass equation,
multiplied by `a₁²`, reads `P² + (a₁²x + a₁a₃)P = a₁²A(x)`: a monic quartic equation for `x`. -/
theorem isConst_of_eta_eq_zero (E : WeierstrassCurve K) {x y : RatFunc K}
    (h : Work.Genus.CharP.WEqn E x y) (heta : etaOf E x y = 0) :
    Work.Genus.CharP.IsConst x := by
  rcases eq_or_ne E.a₁ 0 with h1 | h1
  · refine Work.Genus.Main.exists_algebraMap_eq_of_isAlgebraic ⟨X ^ 2 + C E.a₄, ?_, ?_⟩
    · intro hq
      have hc := congrArg (fun p : Polynomial K => p.coeff 2) hq
      simp at hc
    · rw [etaOf_eq, h1, map_zero, zero_mul, zero_add] at heta
      simpa only [map_add, map_pow, aeval_X, aeval_C] using heta
  · have hkey : algebraMap K (RatFunc K) E.a₁ * y
        = x ^ 2 + algebraMap K (RatFunc K) E.a₄ := by
      have h2 : (2 : RatFunc K) = 0 := CharP.cast_eq_zero _ _
      rw [etaOf_eq] at heta
      linear_combination (norm := first | refl_ring1 | ring1) heta - (x ^ 2 + algebraMap K (RatFunc K) E.a₄) * h2
    have hsq : (algebraMap K (RatFunc K) E.a₁) ^ 2 * y ^ 2
        = (x ^ 2 + algebraMap K (RatFunc K) E.a₄) ^ 2 := by
      rw [← mul_pow, hkey]
    have hmix : (algebraMap K (RatFunc K) E.a₁) ^ 2
          * (algebraMap K (RatFunc K) E.a₁ * x * y)
        = ((algebraMap K (RatFunc K) E.a₁) ^ 2 * x)
          * (x ^ 2 + algebraMap K (RatFunc K) E.a₄) := by
      linear_combination (norm := first | refl_ring1 | ring1) (algebraMap K (RatFunc K) E.a₁ ^ 2 * x) * hkey
    have hlin : (algebraMap K (RatFunc K) E.a₁) ^ 2 * (algebraMap K (RatFunc K) E.a₃ * y)
        = (algebraMap K (RatFunc K) E.a₁ * algebraMap K (RatFunc K) E.a₃)
          * (x ^ 2 + algebraMap K (RatFunc K) E.a₄) := by
      linear_combination (norm := first | refl_ring1 | ring1) (algebraMap K (RatFunc K) E.a₁ * algebraMap K (RatFunc K) E.a₃) * hkey
    have hrel : (x ^ 2 + algebraMap K (RatFunc K) E.a₄) ^ 2
          + ((algebraMap K (RatFunc K) E.a₁) ^ 2 * x
              + algebraMap K (RatFunc K) E.a₁ * algebraMap K (RatFunc K) E.a₃)
            * (x ^ 2 + algebraMap K (RatFunc K) E.a₄)
        = (algebraMap K (RatFunc K) E.a₁) ^ 2 * aeval x (cubicA E) := by
      have hEq : (algebraMap K (RatFunc K) E.a₁) ^ 2
            * (y ^ 2 + algebraMap K (RatFunc K) E.a₁ * x * y + algebraMap K (RatFunc K) E.a₃ * y)
          = (algebraMap K (RatFunc K) E.a₁) ^ 2 * aeval x (cubicA E) := by
        have hh := h
        unfold Work.Genus.CharP.WEqn at hh
        rw [aeval_cubicA]
        exact congrArg (fun z => (algebraMap K (RatFunc K) E.a₁) ^ 2 * z) hh
      have hexp : (algebraMap K (RatFunc K) E.a₁) ^ 2
            * (y ^ 2 + algebraMap K (RatFunc K) E.a₁ * x * y + algebraMap K (RatFunc K) E.a₃ * y)
          = (x ^ 2 + algebraMap K (RatFunc K) E.a₄) ^ 2
            + ((algebraMap K (RatFunc K) E.a₁) ^ 2 * x)
              * (x ^ 2 + algebraMap K (RatFunc K) E.a₄)
            + (algebraMap K (RatFunc K) E.a₁ * algebraMap K (RatFunc K) E.a₃)
              * (x ^ 2 + algebraMap K (RatFunc K) E.a₄) := by
        rw [mul_add, mul_add, hsq, hmix, hlin]
      rw [hexp] at hEq
      linear_combination (norm := first | refl_ring1 | ring1) hEq
    have hq0 : aeval x ((X ^ 2 + C E.a₄) ^ 2
        + (C (E.a₁ ^ 2) * X + C E.a₁ * C E.a₃) * (X ^ 2 + C E.a₄)
        + C (E.a₁ ^ 2) * cubicA E) = 0 := by
      have h2 : (2 : RatFunc K) = 0 := CharP.cast_eq_zero _ _
      simp only [map_add, map_mul, map_pow, aeval_X, aeval_C]
      linear_combination (norm := first | refl_ring1 | ring1) hrel + ((algebraMap K (RatFunc K) E.a₁) ^ 2 * aeval x (cubicA E)) * h2
    have hqne : (X ^ 2 + C E.a₄) ^ 2
        + (C (E.a₁ ^ 2) * X + C E.a₁ * C E.a₃) * (X ^ 2 + C E.a₄)
        + C (E.a₁ ^ 2) * cubicA E ≠ 0 := by
      have hmonic : ((X ^ 2 + C E.a₄) ^ 2
          + (C (E.a₁ ^ 2) * X + C E.a₁ * C E.a₃) * (X ^ 2 + C E.a₄)
          + C (E.a₁ ^ 2) * cubicA E).Monic := by
        rw [cubicA_eq]; monicity!
      exact hmonic.ne_zero
    exact Work.Genus.Main.exists_algebraMap_eq_of_isAlgebraic ⟨_, hqne, hq0⟩

/-- **`y' = 0` unless `η = 0`.**  The pullback `(y'/η) dt` of the invariant differential is regular
on `ℙ¹` (its order is `≥ 0` at every finite place and `≥ 2` at infinity), hence vanishes. -/
theorem deriv_y_eq_zero_of_eta_ne_zero (E : WeierstrassCurve K) (hΔ : E.Δ ≠ 0) {x y : RatFunc K}
    (h : Work.Genus.CharP.WEqn E x y) (heta : etaOf E x y ≠ 0) :
    Work.Genus.deriv y = 0 := by
  by_cases hw0 : wOf E x = 0
  · have hx : Work.Genus.CharP.IsConst x := by
      have ha1 : E.a₁ ≠ 0 := by
        intro h1
        rw [wOf_eq, h1, map_zero, zero_mul, zero_add] at hw0
        have ha3 : E.a₃ = 0 := (algebraMap K (RatFunc K)).injective (by rw [hw0, map_zero])
        exact (a1_ne_zero_or_a3_ne_zero E hΔ).elim (fun hh => hh h1) (fun hh => hh ha3)
      refine ⟨E.a₃ / E.a₁, ?_⟩
      have ha1' : algebraMap K (RatFunc K) E.a₁ ≠ 0 := (algebraMap_ratFunc_ne_zero_iff).mpr ha1
      have h2 : (2 : RatFunc K) = 0 := CharP.cast_eq_zero _ _
      have h2' : algebraMap K (RatFunc K) E.a₁ * x = algebraMap K (RatFunc K) E.a₃ := by
        rw [wOf_eq] at hw0
        linear_combination (norm := first | refl_ring1 | ring1) hw0 - (algebraMap K (RatFunc K) E.a₃) * h2
      rw [map_div₀, eq_div_iff ha1', mul_comm]
      exact h2'
    obtain ⟨c, hc⟩ := Work.Genus.CharP.isConst_of_isConst_abscissa E h hx
    rw [hc, deriv_algebraMap_eq_zero]
  · by_contra hdy'
    set g : RatFunc K := Work.Genus.deriv y / etaOf E x y with hg
    have hg0 : g ≠ 0 := by rw [hg]; exact div_ne_zero hdy' heta
    have hgy : etaOf E x y * g = Work.Genus.deriv y := by
      rw [hg]; field_simp
    have hdx : Work.Genus.deriv x = wOf E x * g := by
      have hid := deriv_identity E h
      rw [← hgy] at hid
      have h2 : etaOf E x y * (wOf E x * g) = etaOf E x y * Work.Genus.deriv x := by
        linear_combination (norm := first | refl_ring1 | ring1) hid
      exact (mul_left_cancel₀ heta h2).symm
    have hord : ∀ π : Polynomial K, Irreducible π → 0 ≤ Work.Genus.ord π g := by
      intro π hπ
      have hdiv : Work.Genus.ord π g = Work.Genus.ord π (Work.Genus.deriv y)
          - Work.Genus.ord π (etaOf E x y) := by
        rw [hg]; exact Work.Genus.Order.ord_div_rat hπ hdy' heta
      rcases lt_or_ge (Work.Genus.ord π x) 0 with hxneg | hxnn
      · have hpole := ord_charTwo_weierstrass_pole (K := K) E.a₁ E.a₂ E.a₃ E.a₄ E.a₆
          (x := x) (y := y) h hπ hxneg
        have hη := ord_eta_eq_of_ord_x_neg E h hπ hxneg
        have hy0 : y ≠ 0 := by
          intro h0
          rw [h0, Work.Genus.Order.ord_zero] at hpole
          linarith [hpole.2, hxneg]
        have hge := Work.Genus.Order.ord_deriv_ge hπ hy0 hdy'
        obtain ⟨k, hk⟩ := hpole.1
        have hyk : Work.Genus.ord π y = 3 * k := by linarith [hpole.2]
        have hk1 : k ≤ -1 := by linarith [hk, hxneg]
        rw [hdiv, hη]
        linarith
      · have hy := ord_y_nonneg_of_ord_x_nonneg E h hπ hxnn
        have hw := ord_wOf_nonneg E hπ hxnn
        rcases lt_or_eq_of_le hw with hwpos | hwzero
        · have hη := ord_eta_eq_zero_of_ord_wOf_pos E hΔ h hπ hxnn hwpos
          have hy0 : y ≠ 0 := y_ne_zero_of_ord_wOf_pos E h hwpos
          have hge := Work.Genus.Order.ord_deriv_nonneg hπ hy0 hdy' hy
          rw [hdiv, hη, sub_zero]
          exact hge
        · have hwz : Work.Genus.ord π (wOf E x) = 0 := hwzero.symm
          have hdxne : Work.Genus.deriv x ≠ 0 := by
            intro h0
            rw [hdx] at h0
            rcases mul_eq_zero.mp h0 with hh | hh
            · exact hw0 hh
            · exact hg0 hh
          have hx0 : x ≠ 0 := fun h0 => hdxne (by rw [h0, deriv_zero_ratFunc])
          have hmul := Work.Genus.Order.ord_mul hπ hw0 hg0
          rw [← hdx] at hmul
          have hdnn := Work.Genus.Order.ord_deriv_nonneg hπ hx0 hdxne hxnn
          rw [hwz] at hmul
          linarith
    have hinf : 2 ≤ Work.Genus.ordInf g := by
      have hdiv : Work.Genus.ordInf g = Work.Genus.ordInf (Work.Genus.deriv y)
          - Work.Genus.ordInf (etaOf E x y) := by
        rw [hg]; exact Work.Genus.OrderInf.ordInf_div hdy' heta
      rcases lt_or_ge (Work.Genus.ordInf x) 0 with hxneg | hxnn
      · have hpole := ordInf_charTwo_weierstrass_pole (K := K) E.a₁ E.a₂ E.a₃ E.a₄ E.a₆
          (x := x) (y := y) h hxneg
        have hη := ordInf_eta_eq_of_ordInf_x_neg E h hxneg
        have hy0 : y ≠ 0 := by
          intro h0
          have hz : Work.Genus.ordInf (0 : RatFunc K) = 0 := by
            rw [Work.Genus.ordInf, RatFunc.intDegree_zero, neg_zero]
          rw [h0, hz] at hpole
          linarith [hpole.2, hxneg]
        have hge := Work.Genus.OrderInf.ordInf_deriv_ge hy0 hdy'
        obtain ⟨k, hk⟩ := hpole.1
        have hyk : Work.Genus.ordInf y = 3 * k := by linarith [hpole.2]
        have hk1 : k ≤ -1 := by linarith [hk, hxneg]
        rw [hdiv, hη]
        linarith
      · have hy := ordInf_y_nonneg_of_ordInf_x_nonneg E h hxnn
        have hw := ordInf_wOf_nonneg E hxnn
        rcases lt_or_eq_of_le hw with hwpos | hwzero
        · have hη := ordInf_eta_eq_zero_of_ordInf_wOf_pos E hΔ h hxnn hwpos
          have hy0 : y ≠ 0 := y_ne_zero_of_ordInf_wOf_pos E h hwpos
          have h2le := Work.Genus.OrderInf.two_le_ordInf_deriv hy0 hdy' hy
          rw [hdiv, hη, sub_zero]
          exact h2le
        · have hwz : Work.Genus.ordInf (wOf E x) = 0 := hwzero.symm
          have hdxne : Work.Genus.deriv x ≠ 0 := by
            intro h0
            rw [hdx] at h0
            rcases mul_eq_zero.mp h0 with hh | hh
            · exact hw0 hh
            · exact hg0 hh
          have hx0 : x ≠ 0 := fun h0 => hdxne (by rw [h0, deriv_zero_ratFunc])
          have hmul := Work.Genus.OrderInf.ordInf_mul hw0 hg0
          rw [← hdx] at hmul
          have h2le := Work.Genus.OrderInf.two_le_ordInf_deriv hx0 hdxne hxnn
          rw [hwz] at hmul
          linarith
    obtain ⟨p, hp⟩ := Work.Genus.Order.exists_algebraMap_eq_of_ord_nonneg hord
    rw [hp, Work.Genus.OrderInf.ordInf_polynomial] at hinf
    have hnn := Int.natCast_nonneg p.natDegree
    linarith

/-- `y' = 0` or `η = 0`. -/
theorem deriv_y_eq_zero_or_eta_eq_zero (E : WeierstrassCurve K) (hΔ : E.Δ ≠ 0) {x y : RatFunc K}
    (h : Work.Genus.CharP.WEqn E x y) :
    Work.Genus.deriv y = 0 ∨ etaOf E x y = 0 := by
  by_cases heta : etaOf E x y = 0
  · exact Or.inr heta
  · exact Or.inl (deriv_y_eq_zero_of_eta_ne_zero E hΔ h heta)

/-- If `y' = 0` then `x' = 0` or `η = 0`. -/
theorem deriv_x_eq_zero_or_eta_eq_zero (E : WeierstrassCurve K) {x y : RatFunc K}
    (h : Work.Genus.CharP.WEqn E x y) (hdy : Work.Genus.deriv y = 0) :
    Work.Genus.deriv x = 0 ∨ etaOf E x y = 0 := by
  have hid := deriv_identity E h
  rw [hdy, mul_zero] at hid
  by_cases heta : etaOf E x y = 0
  · exact Or.inr heta
  · left
    rcases mul_eq_zero.mp hid.symm with hh | hh
    · exact absurd hh heta
    · exact hh

/-- **The genus chapter in characteristic two, over a perfect field.** -/
theorem isConst_of_weqn_charTwo_perfect [PerfectField K] (E : WeierstrassCurve K) (hΔ : E.Δ ≠ 0)
    {x y : RatFunc K} (h : Work.Genus.CharP.WEqn E x y) :
    Work.Genus.CharP.IsConst x ∧ Work.Genus.CharP.IsConst y := by
  suffices H : ∀ n : ℕ, ∀ (E : WeierstrassCurve K), E.Δ ≠ 0 → ∀ x y : RatFunc K,
      Work.Genus.CharP.Size x = n → Work.Genus.CharP.WEqn E x y →
      Work.Genus.CharP.IsConst x ∧ Work.Genus.CharP.IsConst y from H _ E hΔ x y rfl h
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro E hΔ x y hsize h
    rcases eq_or_ne n 0 with hn0 | hnpos
    · have hx : Work.Genus.CharP.IsConst x := isConst_of_size_eq_zero (by rw [hsize, hn0])
      exact ⟨hx, Work.Genus.CharP.isConst_of_isConst_abscissa E h hx⟩
    · have hnpos' : 0 < n := Nat.pos_of_ne_zero hnpos
      rcases deriv_y_eq_zero_or_eta_eq_zero E hΔ h with hdy | heta
      · rcases deriv_x_eq_zero_or_eta_eq_zero E h hdy with hdx | heta
        · obtain ⟨X, hX⟩ := Work.Genus.CharP.exists_pow_eq_of_deriv_eq_zero (p := 2) hdx
          obtain ⟨Y, hY⟩ := Work.Genus.CharP.exists_pow_eq_of_deriv_eq_zero (p := 2) hdy
          have h' : (Y ^ 2) ^ 2 + algebraMap K (RatFunc K) E.a₁ * X ^ 2 * Y ^ 2
                + algebraMap K (RatFunc K) E.a₃ * Y ^ 2
              = (X ^ 2) ^ 3 + algebraMap K (RatFunc K) E.a₂ * (X ^ 2) ^ 2
                + algebraMap K (RatFunc K) E.a₄ * X ^ 2 + algebraMap K (RatFunc K) E.a₆ := by
            rw [← hX, ← hY]; exact h
          have hΔ' : (Work.Genus.rootTwist (p := 2) E).Δ ≠ 0 := by
            intro h0
            have hh := Work.Genus.CharP.rootTwist_discriminant (p := 2) E
            rw [h0, zero_pow (Fact.out : (2:ℕ).Prime).ne_zero] at hh
            exact hΔ hh.symm
          have hrt : Work.Genus.CharP.WEqn (Work.Genus.rootTwist (p := 2) E) X Y :=
            Work.Genus.CharP.equation_rootTwist (p := 2) E h'
          have hlt : Work.Genus.CharP.Size X < n := by
            have hn : 0 < Work.Genus.CharP.Size x := by rw [hsize]; exact hnpos'
            have hlt' := Work.Genus.CharP.size_lt_of_pow_eq (p := 2) hX hn
            rwa [hsize] at hlt'
          obtain ⟨hXc, hYc⟩ :=
            ih (Work.Genus.CharP.Size X) hlt (Work.Genus.rootTwist (p := 2) E) hΔ' X Y rfl hrt
          refine ⟨?_, ?_⟩
          · obtain ⟨X₀, hX₀⟩ := hXc
            exact ⟨X₀ ^ 2, by rw [hX, hX₀, ← map_pow]⟩
          · obtain ⟨Y₀, hY₀⟩ := hYc
            exact ⟨Y₀ ^ 2, by rw [hY, hY₀, ← map_pow]⟩
        · have hx : Work.Genus.CharP.IsConst x := isConst_of_eta_eq_zero E h heta
          exact ⟨hx, Work.Genus.CharP.isConst_of_isConst_abscissa E h hx⟩
      · have hx : Work.Genus.CharP.IsConst x := isConst_of_eta_eq_zero E h heta
        exact ⟨hx, Work.Genus.CharP.isConst_of_isConst_abscissa E h hx⟩

/-- **The genus chapter in characteristic two.**  Every `K(t)`-point of a non-singular Weierstrass
curve over a field `K` of characteristic `2` is constant (no non-constant morphism `ℙ¹ → E`).

The general case is reduced to a perfect field by passing to the algebraic closure
(`RatFunc K →+* RatFunc M`, `Work.Wire123.ratFuncCoeffMap`). -/
theorem exists_algebraMap_of_weierstrass_ratFunc_charTwo {K : Type*} [Field K] [CharP K 2]
    (E : WeierstrassCurve K) (hΔ : E.Δ ≠ 0) {x y : RatFunc K}
    (h : y ^ 2 + algebraMap K (RatFunc K) E.a₁ * x * y + algebraMap K (RatFunc K) E.a₃ * y
      = x ^ 3 + algebraMap K (RatFunc K) E.a₂ * x ^ 2 + algebraMap K (RatFunc K) E.a₄ * x
        + algebraMap K (RatFunc K) E.a₆) :
    (∃ x₀ : K, x = algebraMap K (RatFunc K) x₀) ∧ (∃ y₀ : K, y = algebraMap K (RatFunc K) y₀) := by
  let M := AlgebraicClosure K
  haveI : PerfectField M := inferInstance
  haveI : CharP M 2 := inferInstance
  set E' : WeierstrassCurve M := E.baseChange M with hE'
  have hΔ' : E'.Δ ≠ 0 := by
    rw [hE', WeierstrassCurve.baseChange, WeierstrassCurve.map_Δ]
    intro hh
    exact hΔ ((algebraMap K M).injective (by rw [hh, map_zero]))
  set x' : RatFunc M := ratFuncCoeffMap K M x with hx'
  set y' : RatFunc M := ratFuncCoeffMap K M y with hy'
  have h' : y' ^ 2 + algebraMap M (RatFunc M) E'.a₁ * x' * y' + algebraMap M (RatFunc M) E'.a₃ * y'
        = x' ^ 3 + algebraMap M (RatFunc M) E'.a₂ * x' ^ 2 + algebraMap M (RatFunc M) E'.a₄ * x'
          + algebraMap M (RatFunc M) E'.a₆ := by
    have hh := congrArg (ratFuncCoeffMap K M) h
    simp only [map_add, map_mul, map_pow] at hh
    rw [← hx', ← hy'] at hh
    simp only [ratFuncCoeffMap_algebraMap] at hh
    rw [hE', WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
      WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆]
    exact hh
  obtain ⟨hxc, hyc⟩ := isConst_of_weqn_charTwo_perfect (K := M) E' hΔ' h'
  refine ⟨?_, ?_⟩
  · obtain ⟨m, hm⟩ := hxc
    exact exists_algebraMap_of_ratFuncCoeffMap_eq_algebraMap (hx'.symm.trans hm)
  · obtain ⟨m, hm⟩ := hyc
    exact exists_algebraMap_of_ratFuncCoeffMap_eq_algebraMap (hy'.symm.trans hm)

end Main

end Work.MotC.WireU
