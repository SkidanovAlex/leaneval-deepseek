import Mathlib
import Submission.Work.C17.lead_defs

/-!
# Tools for the local expansion data at `x = 0` (`Work.C17.local_base`)

Self-contained helpers used by `Work.C17.local_base` and by the lemmas
`Work.C17.lead2_rhoQ`, `Work.C17.lead2_dRat_rhoQ`, `Work.C17.lead2_ratio`:

* `xQ_eq_algP`, `xQ_ne_zero_local_tools`, `ordAtT_xQ_local_tools`: the basic facts about `xQ` as the image of `X`;
* `algQ_eq_algP`: the scalar `ℚ`-algebra map into `ℚ(X)` factors through `ℚ[X]`;
* `algP_inj_iff`: injectivity of `ℚ[X] → ℚ(X)`;
* `reg_algebraMap_local_tools`, `reg_div_algebraMap_local_tools`: `Reg` (order `≥ 0` at `0`) of polynomial images
  and of quotients whose denominator does not vanish at `0`;
* `lead2At_of_eq`: the master reduction: to prove `Lead2At f e l m` it suffices to exhibit a
  *regular* `g` with `f * x^{-e} - l - m x = x² g`.
-/

namespace Work.C17

open Commons.FieldTheory.RatFunc

noncomputable section

local notation "algP" => algebraMap (Polynomial ℚ) (RatFunc ℚ)

/-- `xQ` is (definitionally) the image of `Polynomial.X`. -/
lemma xQ_eq_algP : (xQ : RatFunc ℚ) = algP Polynomial.X := rfl

lemma xQ_ne_zero_local_tools : (xQ : RatFunc ℚ) ≠ 0 := by
  rw [xQ_eq_algP]
  exact RatFunc.algebraMap_ne_zero Polynomial.X_ne_zero

/-- The scalar `ℚ`-algebra map into `ℚ(X)` is the polynomial one composed with `C`. -/
lemma algQ_eq_algP (c : ℚ) :
    algebraMap ℚ (RatFunc ℚ) c = algP (Polynomial.C c) := by
  rw [Polynomial.C_eq_algebraMap]
  exact IsScalarTower.algebraMap_apply ℚ (Polynomial ℚ) (RatFunc ℚ) c

/-- Injectivity of `ℚ[X] → ℚ(X)`, as an `iff` for rewriting. -/
lemma algP_inj_iff {p q : Polynomial ℚ} : algP p = algP q ↔ p = q :=
  (RatFunc.algebraMap_injective ℚ).eq_iff

lemma algP_ne_zero {p : Polynomial ℚ} (hp : p ≠ 0) : algP p ≠ 0 :=
  RatFunc.algebraMap_ne_zero hp

lemma ordAtT_xQ_local_tools : ordAtT (0 : ℚ) (xQ : RatFunc ℚ) = 1 := by
  rw [xQ_eq_algP, ordAtT_algebraMap Polynomial.X_ne_zero]
  rw [show (Polynomial.X : Polynomial ℚ) = Polynomial.X - Polynomial.C 0 by simp,
    Polynomial.rootMultiplicity_X_sub_C_self]
  norm_num

lemma rootMultiplicity_zero_eq_zero_local_tools {p : Polynomial ℚ} (hp : p.coeff 0 ≠ 0) :
    p.rootMultiplicity (0 : ℚ) = 0 := by
  rw [Polynomial.rootMultiplicity_eq_natTrailingDegree']
  exact Polynomial.natTrailingDegree_eq_zero.mpr (Or.inr hp)

/-- Polynomial images are regular at `0`. -/
lemma reg_algebraMap_local_tools (p : Polynomial ℚ) : Reg (algP p) := by
  rw [Reg]
  rcases eq_or_ne p 0 with h | h
  · rw [h, map_zero, ordAtT]; simp
  · rw [ordAtT_algebraMap h]
    exact WithTop.coe_le_coe.mpr (Int.natCast_nonneg _)

/-- A quotient of polynomial images whose denominator does not vanish at `0` is regular. -/
lemma reg_div_algebraMap_local_tools {p q : Polynomial ℚ} (hq : q.coeff 0 ≠ 0) :
    Reg (algP p / algP q) := by
  rw [Reg]
  rcases eq_or_ne q 0 with h | h
  · exact absurd (by rw [h, Polynomial.coeff_zero]) hq
  rcases eq_or_ne p 0 with hp | hp
  · rw [hp, map_zero, zero_div, ordAtT]; simp
  rw [ordAtT_div (0 : ℚ) (algP_ne_zero hp) (algP_ne_zero h), ordAtT_algebraMap hp,
    ordAtT_algebraMap h, rootMultiplicity_zero_eq_zero_local_tools hq]
  simp only [Nat.cast_zero, WithTop.coe_zero, sub_zero]
  exact WithTop.coe_le_coe.mpr (Int.natCast_nonneg _)

/-- **Master reduction.**  To prove `Lead2At f e l m` it suffices to write
`f * x^{-e} = l + m x + x² g` with `g` regular at `0`. -/
lemma lead2At_of_eq (f : RatFunc ℚ) (e : ℤ) (l m : ℚ) (hl : l ≠ 0) {g : RatFunc ℚ}
    (hg : Reg g)
    (h : f * xQ ^ (-e) - algebraMap ℚ (RatFunc ℚ) l - algebraMap ℚ (RatFunc ℚ) m * xQ
      = xQ ^ 2 * g) : Lead2At f e l m := by
  refine ⟨hl, ?_⟩
  rw [h]
  rcases eq_or_ne g 0 with h0 | h0
  · rw [h0, mul_zero, ordAtT]; simp
  · rw [ordAtT_mul (0 : ℚ) (pow_ne_zero 2 xQ_ne_zero_local_tools) h0, ordAtT_pow (0 : ℚ) xQ_ne_zero_local_tools 2,
      ordAtT_xQ_local_tools]
    rw [Reg] at hg
    simpa using le_add_of_nonneg_right hg

end

end Work.C17
