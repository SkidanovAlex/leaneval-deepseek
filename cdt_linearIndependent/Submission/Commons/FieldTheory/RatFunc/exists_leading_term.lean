import Mathlib
import Submission.Commons.FieldTheory.RatFunc.ordAtT_adjoint_eq_of_indicial

namespace Commons.FieldTheory.RatFunc

open Classical
open Commons.FieldTheory.RatFunc

set_option maxHeartbeats 800000
set_option linter.unusedVariables false

/-- Splitting off a power of the linear factor `X - α` from an algebra-map of a polynomial. -/
private lemma algebraMap_mul_X_sub_C_pow {K : Type*} [Field K] (α : K) (m : ℕ) (u : Polynomial K) :
    algebraMap (Polynomial K) (RatFunc K) ((Polynomial.X - Polynomial.C α) ^ m * u)
      = linFactor (K := K) α ^ (m : ℤ) * algebraMap (Polynomial K) (RatFunc K) u := by
  rw [map_mul, map_pow, ← zpow_natCast]
  rfl

/-- **Every nonzero rational function has a leading term at `α`.**  With `N = ordAt α b`, there is
`r ≠ 0` (the "leading coefficient" of `b` at `α`) such that `b - r·(X − α)^N` has order at least
`N + 1`.  This is the "principal part" input of the local/indicial analysis. -/
theorem exists_leading_term {K : Type*} [Field K] (α : K) {b : RatFunc K} (hb : b ≠ 0) :
    ∃ r : K, r ≠ 0 ∧ (((ordAt α b) + 1 : ℤ) : WithTop ℤ) ≤ ordAtT α
      (b - algebraMap (Polynomial K) (RatFunc K) (Polynomial.C r)
        * linFactor (K := K) α ^ (ordAt α b)) := by
  classical
  -- Write `b = num/denom` and split off the maximal power of `X - α` from each of them.
  set N : ℤ := ordAt α b with hNdef
  set mp : ℕ := Polynomial.rootMultiplicity α b.num with hmpdef
  set mq : ℕ := Polynomial.rootMultiplicity α b.denom with hmqdef
  set p₁ : Polynomial K := b.num /ₘ (Polynomial.X - Polynomial.C α) ^ mp with hp₁def
  set q₁ : Polynomial K := b.denom /ₘ (Polynomial.X - Polynomial.C α) ^ mq with hq₁def
  have hp : b.num ≠ 0 := RatFunc.num_ne_zero hb
  have hq : b.denom ≠ 0 := RatFunc.denom_ne_zero b
  have hN : N = (mp : ℤ) - (mq : ℤ) := by
    rw [hNdef, ordAt_def, hmpdef, hmqdef]
  -- The two "unit parts" `p₁, q₁` do not vanish at `α`, so they have order `0` there.
  have hp₁eval : Polynomial.eval α p₁ ≠ 0 := by
    rw [hp₁def, hmpdef]
    exact Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero (p := b.num) α hp
  have hq₁eval : Polynomial.eval α q₁ ≠ 0 := by
    rw [hq₁def, hmqdef]
    exact Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero (p := b.denom) α hq
  have hp₁ne : p₁ ≠ 0 := fun h => hp₁eval (by rw [h, Polynomial.eval_zero])
  have hq₁ne : q₁ ≠ 0 := fun h => hq₁eval (by rw [h, Polynomial.eval_zero])
  have hnum_eq : (Polynomial.X - Polynomial.C α) ^ mp * p₁ = b.num := by
    rw [hp₁def, hmpdef]
    exact Polynomial.pow_mul_divByMonic_rootMultiplicity_eq b.num α
  have hden_eq : (Polynomial.X - Polynomial.C α) ^ mq * q₁ = b.denom := by
    rw [hq₁def, hmqdef]
    exact Polynomial.pow_mul_divByMonic_rootMultiplicity_eq b.denom α
  have hL : linFactor (K := K) α ≠ 0 := linFactor_ne_zero α
  have hA : algebraMap (Polynomial K) (RatFunc K) p₁ ≠ 0 := RatFunc.algebraMap_ne_zero hp₁ne
  have hB : algebraMap (Polynomial K) (RatFunc K) q₁ ≠ 0 := RatFunc.algebraMap_ne_zero hq₁ne
  -- The decomposition `b = (X - α)^N · p₁/q₁`.
  have hbdecomp : b = linFactor (K := K) α ^ N *
      (algebraMap (Polynomial K) (RatFunc K) p₁ / algebraMap (Polynomial K) (RatFunc K) q₁) := by
    conv_lhs => rw [← RatFunc.num_div_denom b]
    rw [← hnum_eq, ← hden_eq, algebraMap_mul_X_sub_C_pow, algebraMap_mul_X_sub_C_pow,
      ← div_mul_div_comm, ← zpow_sub₀ hL, ← hN]
  -- The candidate leading coefficient is the value of `p₁/q₁` at `α`.
  refine ⟨Polynomial.eval α p₁ / Polynomial.eval α q₁, div_ne_zero hp₁eval hq₁eval, ?_⟩
  set r : K := Polynomial.eval α p₁ / Polynomial.eval α q₁ with hrdef
  set P : Polynomial K := p₁ - Polynomial.C r * q₁ with hPdef
  set w : RatFunc K := b - algebraMap (Polynomial K) (RatFunc K) (Polynomial.C r)
      * linFactor (K := K) α ^ N with hwdef
  -- `p₁/q₁ - r = P/q₁`.
  have hbr : algebraMap (Polynomial K) (RatFunc K) p₁ / algebraMap (Polynomial K) (RatFunc K) q₁
      - algebraMap (Polynomial K) (RatFunc K) (Polynomial.C r)
      = algebraMap (Polynomial K) (RatFunc K) P / algebraMap (Polynomial K) (RatFunc K) q₁ := by
    rw [hPdef, map_sub, map_mul]
    conv_rhs => rw [sub_div, mul_div_cancel_right₀ _ hB]
  have hwdecomp : w = linFactor (K := K) α ^ N *
      (algebraMap (Polynomial K) (RatFunc K) p₁ / algebraMap (Polynomial K) (RatFunc K) q₁
        - algebraMap (Polynomial K) (RatFunc K) (Polynomial.C r)) := by
    rw [hwdef, hbdecomp]; ring
  rcases eq_or_ne w 0 with hw0 | hwne
  · -- The residual is zero: its order is `⊤`.
    rw [hw0, show ordAtT α (0 : RatFunc K) = ⊤ from by simp [ordAtT]]
    exact le_top
  · have hbrne : algebraMap (Polynomial K) (RatFunc K) p₁ / algebraMap (Polynomial K) (RatFunc K) q₁
        - algebraMap (Polynomial K) (RatFunc K) (Polynomial.C r) ≠ 0 := by
      intro h0
      exact hwne (by rw [hwdecomp, h0, mul_zero])
    have hPne : P ≠ 0 := by
      intro h0
      refine hbrne ?_
      rw [hbr, h0, map_zero, zero_div]
    -- `P` vanishes at `α`, hence `X - α ∣ P`, hence `ord_α P ≥ 1`.
    have heval : Polynomial.eval α P = 0 := by
      rw [hPdef, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, hrdef]
      field_simp
      ring
    have hroot : 1 ≤ Polynomial.rootMultiplicity α P := by
      rw [Polynomial.le_rootMultiplicity_iff hPne, pow_one, Polynomial.dvd_iff_isRoot,
        Polynomial.IsRoot.def]
      exact heval
    have hPmap : algebraMap (Polynomial K) (RatFunc K) P ≠ 0 := RatFunc.algebraMap_ne_zero hPne
    have hq1root : Polynomial.rootMultiplicity α q₁ = 0 :=
      Polynomial.rootMultiplicity_eq_zero (fun h => hq₁eval (Polynomial.IsRoot.def.mp h))
    have hbrge : (1 : ℤ) ≤ ordAt α (algebraMap (Polynomial K) (RatFunc K) p₁
        / algebraMap (Polynomial K) (RatFunc K) q₁
        - algebraMap (Polynomial K) (RatFunc K) (Polynomial.C r)) := by
      rw [hbr, ordAt_div α hPmap hB, ordAt_algebraMap, ordAt_algebraMap,
        show (Polynomial.rootMultiplicity α q₁ : ℤ) = 0 from by rw [hq1root]; norm_num, sub_zero]
      exact_mod_cast hroot
    have hLpow : ordAt α (linFactor (K := K) α ^ N) = N := by
      have hne : linFactor (K := K) α ^ N ≠ 0 := zpow_ne_zero N hL
      have h := ordAtT_linFactor_zpow (K := K) α N
      rw [ordAtT_def α hne] at h
      exact_mod_cast h
    have hword : ordAt α w = N + ordAt α (algebraMap (Polynomial K) (RatFunc K) p₁
        / algebraMap (Polynomial K) (RatFunc K) q₁
        - algebraMap (Polynomial K) (RatFunc K) (Polynomial.C r)) := by
      rw [hwdecomp, ordAt_mul α (zpow_ne_zero N hL) hbrne, hLpow]
    rw [ordAtT_def α hwne]
    have : (N + 1 : ℤ) ≤ ordAt α w := by rw [hword]; linarith
    exact_mod_cast this

end Commons.FieldTheory.RatFunc
