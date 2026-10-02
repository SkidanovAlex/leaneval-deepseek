/-
# ZeroFreeTables/OffAxis/HBLemma9_1_rep_engine_H3

**HB Lemma 9.1 at a repeated zero, at rectangle height `H` with room `W ≥ 3H + 1`.**

For `a, K, ε > 0`, `1 ≤ H` and `3H + 1 ≤ W` there is `q₀` such that for `q ≥ q₀`, a pair
`(χ₁, ρ₁)` with `H ≤ log q`, the wide minimality `IsMinWideAt H W χ₁ ρ₁`, not the real-real case
(`¬(χ₁² = 1 ∧ Im ρ₁ = 0)`), a multiple zero `2 ≤ zeroMult χ₁ ρ₁` and the side condition
`cond913 λ₁ λ₁ a K` satisfies HB's inequality `ineq913 λ₁ λ₁ a K ε`.

The proof splits on the order of `χ₁`:

* `χ₁² ≠ 1`, `χ₁³ ≠ 1` — the *generic* case, done in `OffAxis.rectRepGeneric` (HB §9's diagonal
  four-point combination at `σ, σ+iγ, σ+2iγ, σ+3iγ` with all near sums dropped);
* `χ₁² ≠ 1`, `χ₁³ = 1` — the *order-3* case (`rectRepOrder3H` below): the point `σ+3iγ` carries
  the principal character, so its pole term `Re P₃(α/(a+3iγlog q))` is controlled either by the
  conjugate zero `ρ̄₁` of `χ₁²` (near case, `OffAxis.RectRepOrder3`) or by its smallness (far
  case, same lemma);
* `χ₁² = 1` — the *order-2* case (`rectRepOrder2H` below): the point `σ+2iγ` carries the
  principal character, controlled by the conjugate zero `ρ̄₁` of `χ₁` (near case,
  `OffAxis.RectRepCaseCNear`) or by its smallness (far case, `OffAxis.RectRepCaseCFar`).

The point bounds used are `OffAxis.pointBoundWide` (non-principal `χ`, heights `≤ 3H`, constant
`1/6`), `OffAxis.RectRepPrincipal` (principal character, heights `≤ 3H`), the double-zero bound
`Rep9.nearSumDoubleH`, the near-sum non-negativity `OffAxis.RectRepNearSum` and the diagonal
combination `OffAxis.RectRepComb`; the algebraic endgame is
`Rep9.ineq913_diag_of_derived_poly`.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.OffAxis.WideDefs
import Submission.Work.ZeroFreeTables.Engine
import Submission.Work.ZeroFreeTables.Rep9.Assembly
import Submission.Work.ZeroFreeTables.OffAxis.RectRepDefs
import Submission.Work.ZeroFreeTables.OffAxis.RectRepComb
import Submission.Work.ZeroFreeTables.OffAxis.RectRepDiag
import Submission.Work.ZeroFreeTables.OffAxis.RectRepPoint
import Submission.Work.ZeroFreeTables.OffAxis.RectRepPrincipal
import Submission.Work.ZeroFreeTables.OffAxis.RectRepNearSum
import Submission.Work.ZeroFreeTables.OffAxis.RectRepCaseCNear
import Submission.Work.ZeroFreeTables.OffAxis.RectRepCaseCFar
import Submission.Work.ZeroFreeTables.OffAxis.RectRepOrder3
import Submission.Work.ZeroFreeTables.OffAxis.RectRepInput
import Submission.Work.ZeroFreeTables.P3.DefsL
import Submission.Work.ZeroFreeTables.P9.Defs
import Submission.Work.ZeroFreeTables.P9.lDiffExplicit_gen
import Submission.Work.ZeroFreeTables.P9.invNearSum_eq_tsum
import Submission.Work.ZeroFreeTables.P9.P3NearSumL_eq_nearP3sum
import Submission.Work.ZeroFreeTables.P9.prim.masterP3_zero
import Submission.Work.ZeroFreeTables.P9.prim.parityBound
import Submission.Work.ZeroFreeTables.P9.prim.invSqSum_bound
import Submission.Work.LinnikAreas.FarRepel.zeroMult_eq_analyticOrderNatAt_of_isPrimitive
import Submission.Work.ZeroFreeTables.OffAxis.RepHMaster
import Submission.Work.ZeroFreeTables.HB94.Lam0GeEngine
import Submission.Work.ZeroFreeTables.Rep9.nearSum_primitive_le
import Submission.Work.LinnikAreas2.D2Aux
import Submission.Work.ZeroFreeTables.OffAxis.RectRepGeneric
import Submission.Work.ZeroFreeTables.OffAxis.RepHNear
import Submission.Work.ZeroFreeTables.Rep9.P3_div_le

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroFreeTables.OffAxis

open Work.ZeroFreeTables Work.LinnikContract

/-- `(x + y : ℂ) = x + y` (used to match the two normal forms of a shifted argument). -/
private lemma ofReal_add_local {x y : ℝ} : ((x + y : ℝ) : ℂ) = (x : ℂ) + (y : ℂ) :=
  Complex.ofReal_add x y


/-! ## The linear-algebraic budgets of the two remaining cases -/

/-- Norm of a real number seen in `ℂ`. -/
private lemma norm_ofReal_local (x : ℝ) : ‖((x : ℝ) : ℂ)‖ = |x| := RCLike.norm_ofReal x

/-- **Budget of the order-2 near branch.**  With `e ≤ 1/(768K)` and `e₀ = e/2`,
`C₂ = (K²+K+½)e₀ + (K²+2K+¾)(1/6+e) + (K+½)e₀ + ¼(1/6+e)` satisfies `C₂·48K ≤ (12K+½)S`. -/
private lemma order2_budget {K e : ℝ} (hK : 0 < K) (he : e ≤ 1 / (768 * K)) :
    ((K ^ 2 + K + 1 / 2) * (e / 2) + (K ^ 2 + 2 * K + 3 / 4) * (1 / 6 + e)
        + (K + 1 / 2) * (e / 2) + (1 / 4) * (1 / 6 + e)) * (48 * K)
      ≤ (12 * K + 1 / 2) * (K ^ 2 + 3 * K + 3 / 2) := by
  have h1 : (K ^ 2 + K + 1 / 2) * (e / 2) + (K ^ 2 + 2 * K + 3 / 4) * (1 / 6 + e)
      + (K + 1 / 2) * (e / 2) + (1 / 4) * (1 / 6 + e)
      = (K + 1) ^ 2 * (1 / 6 + 3 * e / 2) := by ring
  rw [h1]
  have he' : 72 * K * e ≤ 3 / 32 := by
    have h := mul_le_mul_of_nonneg_left he (by positivity : (0 : ℝ) ≤ 72 * K)
    have h2 : (72 * K) * (1 / (768 * K)) = 3 / 32 := by field_simp; ring
    linarith [h, h2.le, h2.ge]
  have hkey : ((K + 1) ^ 2 * (1 / 6 + 3 * e / 2)) * (48 * K)
      = 8 * K * (K + 1) ^ 2 + (K + 1) ^ 2 * (72 * K * e) := by ring
  have hb : (K + 1) ^ 2 * (72 * K * e) ≤ (K + 1) ^ 2 * (3 / 32) :=
    mul_le_mul_of_nonneg_left he' (sq_nonneg _)
  have hpoly : 8 * K * (K + 1) ^ 2 + (K + 1) ^ 2 * (3 / 32)
      ≤ (12 * K + 1 / 2) * (K ^ 2 + 3 * K + 3 / 2) := by
    nlinarith only [hK, sq_nonneg K, pow_nonneg hK.le 3, sq_nonneg (K + 1), sq_nonneg (K - 1)]
  linarith [hb, hpoly]

/-- **Budget of the order-2 far branch.**  The extra error `eₓ = (K+½)e/(a S)` costs at most
`S/2` in the `48K`-normalised budget. -/
private lemma order2_budget_ex {K a e S : ℝ} (ha : 0 < a) (hK : 0 < K) (hS : 0 < S)
    (he : e ≤ a * S / (96 * K * (K + 1 / 2))) :
    48 * K * ((K + 1 / 2) * e / (a * S) * S) ≤ S / 2 := by
  have h1 : (K + 1 / 2) * e / (a * S) * S = (K + 1 / 2) * (e / a) := by
    field_simp
  have hfin : 48 * K * (K + 1 / 2) * e ≤ a * S / 2 := by
    have hmul := mul_le_mul_of_nonneg_left he (by positivity : (0 : ℝ) ≤ 48 * K * (K + 1 / 2))
    have hval : (48 * K * (K + 1 / 2)) * (a * S / (96 * K * (K + 1 / 2))) = a * S / 2 := by
      field_simp; ring
    linarith [hmul, hval.le, hval.ge]
  rw [h1, show 48 * K * ((K + 1 / 2) * (e / a)) = (48 * K * (K + 1 / 2) * e) / a by ring,
    div_le_iff₀ ha]
  linarith [hfin]

/-- **Budget of the order-3 branch.**  With `e ≤ 1/(768K)` and `e₀ = e/2`,
`C₃ = (K²+K+½)e₀ + (K²+2K+¾)(1/6+e) + (K+½)(1/6+e) + ¼e₀` satisfies
`C₃·48K ≤ (12K + 63/64)S`. -/
private lemma order3_budget {K e : ℝ} (hK : 0 < K) (he : e ≤ 1 / (768 * K)) :
    ((K ^ 2 + K + 1 / 2) * (e / 2) + (K ^ 2 + 2 * K + 3 / 4) * (1 / 6 + e)
        + (K + 1 / 2) * (1 / 6 + e) + (1 / 4) * (e / 2)) * (48 * K)
      ≤ (12 * K + 63 / 64) * (K ^ 2 + 3 * K + 3 / 2) := by
  have he' : 48 * K * e ≤ 1 / 16 := by
    have h := mul_le_mul_of_nonneg_left he (by positivity : (0 : ℝ) ≤ 48 * K)
    have h2 : (48 * K) * (1 / (768 * K)) = 1 / 16 := by field_simp; ring
    linarith [h, h2.le, h2.ge]
  have he'' : 24 * K * e ≤ 1 / 32 := by
    have h := mul_le_mul_of_nonneg_left he (by positivity : (0 : ℝ) ≤ 24 * K)
    have h2 : (24 * K) * (1 / (768 * K)) = 1 / 32 := by field_simp; ring
    linarith [h, h2.le, h2.ge]
  have hkey : ((K ^ 2 + K + 1 / 2) * (e / 2) + (K ^ 2 + 2 * K + 3 / 4) * (1 / 6 + e)
      + (K + 1 / 2) * (1 / 6 + e) + (1 / 4) * (e / 2)) * (48 * K)
      = 8 * K * (K ^ 2 + 3 * K + 5 / 4) + (K ^ 2 + K + 3 / 4) * (24 * K * e)
        + (K ^ 2 + 3 * K + 5 / 4) * (48 * K * e) := by
    ring
  rw [hkey]
  have hA : (K ^ 2 + K + 3 / 4) * (24 * K * e) ≤ (K ^ 2 + K + 3 / 4) * (1 / 32) :=
    mul_le_mul_of_nonneg_left he'' (by positivity)
  have hB : (K ^ 2 + 3 * K + 5 / 4) * (48 * K * e) ≤ (K ^ 2 + 3 * K + 5 / 4) * (1 / 16) :=
    mul_le_mul_of_nonneg_left he' (by positivity)
  have hpoly : 8 * K * (K ^ 2 + 3 * K + 5 / 4) + (K ^ 2 + K + 3 / 4) * (1 / 32)
      + (K ^ 2 + 3 * K + 5 / 4) * (1 / 16)
      ≤ (12 * K + 63 / 64) * (K ^ 2 + 3 * K + 3 / 2) := by
    nlinarith only [hK, sq_nonneg K, pow_nonneg hK.le 3, sq_nonneg (K + 1), sq_nonneg (K - 1)]
  linarith [hA, hB, hpoly]

/-- **Budget of the generic case.**  With `e ≤ 1/(768K)` and `e₀ = e/2`,
`C = (K²+K+½)e₀ + (K²+2K+¾)(1/6+e) + (K+½)(1/6+e) + ¼(1/6+e)` satisfies
`C·48K ≤ (12K+1)(K²+3K+3/2)`. -/
private lemma generic_budget {K e : ℝ} (hK : 0 < K) (he : e ≤ 1 / (768 * K)) :
    ((K ^ 2 + K + 1 / 2) * (e / 2) + (K ^ 2 + 2 * K + 3 / 4) * (1 / 6 + e)
        + (K + 1 / 2) * (1 / 6 + e) + (1 / 4) * (1 / 6 + e)) * (48 * K)
      ≤ (12 * K + 1) * (K ^ 2 + 3 * K + 3 / 2) := by
  have hkey : ((K ^ 2 + K + 1 / 2) * (e / 2) + (K ^ 2 + 2 * K + 3 / 4) * (1 / 6 + e)
      + (K + 1 / 2) * (1 / 6 + e) + (1 / 4) * (1 / 6 + e)) * (48 * K)
      = 8 * K ^ 3 + 24 * K ^ 2 + 12 * K + (72 * K ^ 3 + 168 * K ^ 2 + 84 * K) * e := by
    ring
  have h1 : (72 * K ^ 3 + 168 * K ^ 2 + 84 * K) * e ≤ (6 * K ^ 2 + 14 * K + 7) / 64 := by
    have h := mul_le_mul_of_nonneg_left he (by positivity : (0 : ℝ) ≤ 72 * K ^ 3 + 168 * K ^ 2 + 84 * K)
    have h2 : (72 * K ^ 3 + 168 * K ^ 2 + 84 * K) * (1 / (768 * K))
        = (6 * K ^ 2 + 14 * K + 7) / 64 := by
      field_simp; ring
    linarith [h, h2.le, h2.ge]
  have h3 : 8 * K ^ 3 + 24 * K ^ 2 + 12 * K + (6 * K ^ 2 + 14 * K + 7) / 64
      ≤ (12 * K + 1) * (K ^ 2 + 3 * K + 3 / 2) := by
    nlinarith only [hK, sq_nonneg K, pow_nonneg hK.le 3, sq_nonneg (K + 1), sq_nonneg (K - 1)]
  rw [hkey]
  linarith [h1, h3]

/-- **Budget of the order-3 far branch.**  The extra error `eₓ = e/(4aS)` costs at most `S/64`. -/
private lemma order3_budget_ex {K a e S : ℝ} (ha : 0 < a) (hK : 0 < K) (hS : 0 < S)
    (he : e ≤ a * S / (768 * K)) :
    48 * K * (e / (4 * a * S) * S) ≤ S / 64 := by
  have h1 : e / (4 * a * S) * S = e / (4 * a) := by
    field_simp
  have hfin : 48 * K * e ≤ a * S / 16 := by
    have hmul := mul_le_mul_of_nonneg_left he (by positivity : (0 : ℝ) ≤ 48 * K)
    have hval : (48 * K) * (a * S / (768 * K)) = a * S / 16 := by field_simp; ring
    linarith [hmul, hval.le, hval.ge]
  rw [h1, show 48 * K * (e / (4 * a)) = (48 * K * e) / (4 * a) by ring,
    div_le_iff₀ (by positivity : (0 : ℝ) < 4 * a)]
  linarith [hfin]


/-! ## The analytic inputs: masters bound and per-point bound at height `3H`

`pointBoundWideLocal` is the composition (k1 input → master bound → imprimitive reduction) that
`OffAxis.RectRepPoint.pointBoundWide` performs, with the master bound `masterWide_local` (the
wide form of HB §9's `P₃` master bound, `|Im s| ≤ 10 log q`) in place of the master bound of
`OffAxis.RectRepMaster`.  The earlier `T`-free development of the present file used the latter,
which is not proved; `masterWide_local` is proved by `OffAxis.masterP3Wide3H`. -/
/-- **The absorption of the `P₃` error bracket** (copy of the private `error_bound` of
`OffAxis/RepHMaster`, which cannot be imported). -/
private lemma error_bound_local {A Amax k2 k3 C Ct J T2r T3r L e : ℝ}
    (hA : 0 ≤ A) (hAle : A ≤ Amax) (hAmax : 0 ≤ Amax) (hk2 : 0 ≤ k2) (hk3 : 0 ≤ k3)
    (hC : 0 ≤ C) (hCt : 0 ≤ Ct) (hJ : J ≤ C * (L + 2)) (hT2 : -T2r ≤ Ct) (hT3 : -T3r ≤ Ct)
    (hL2 : 2 ≤ L) (hLpos : 0 < L) (hae : 0 < A * e)
    (hK : 2 * Amax ^ 2 * (k2 * C + Ct) + (4 / 3) * Amax ^ 3 * (k3 * C + Ct) ≤ A * e * L) :
    (A / L) ^ 2 * (k2 * J - T2r) + (2 / 3) * (A / L) ^ 3 * (k3 * J - T3r) ≤ A * e := by
  have hB2 : k2 * J + Ct ≤ (k2 * C + Ct) * (L + 2) := by
    have h1 : k2 * J ≤ k2 * (C * (L + 2)) := mul_le_mul_of_nonneg_left hJ hk2
    have h2 : Ct ≤ Ct * (L + 2) := le_mul_of_one_le_right hCt (by linarith)
    have heq : (k2 * C + Ct) * (L + 2) = k2 * (C * (L + 2)) + Ct * (L + 2) := by ring
    linarith [h1, h2, heq.le, heq.ge]
  have hB3 : k3 * J + Ct ≤ (k3 * C + Ct) * (L + 2) := by
    have h1 : k3 * J ≤ k3 * (C * (L + 2)) := mul_le_mul_of_nonneg_left hJ hk3
    have h2 : Ct ≤ Ct * (L + 2) := le_mul_of_one_le_right hCt (by linarith)
    have heq : (k3 * C + Ct) * (L + 2) = k3 * (C * (L + 2)) + Ct * (L + 2) := by ring
    linarith [h1, h2, heq.le, heq.ge]
  have hin2 : k2 * J - T2r ≤ (k2 * C + Ct) * (L + 2) := by linarith [hB2, hT2]
  have hin3 : k3 * J - T3r ≤ (k3 * C + Ct) * (L + 2) := by linarith [hB3, hT3]
  have hC2nn : 0 ≤ k2 * C + Ct := by positivity
  have hC3nn : 0 ≤ k3 * C + Ct := by positivity
  have hC2L2nn : 0 ≤ (k2 * C + Ct) * (L + 2) := mul_nonneg hC2nn (by linarith)
  have hC3L2nn : 0 ≤ (k3 * C + Ct) * (L + 2) := mul_nonneg hC3nn (by linarith)
  have hnum : A ^ 2 ≤ Amax ^ 2 := pow_le_pow_left₀ hA hAle 2
  have hnum3 : A ^ 3 ≤ Amax ^ 3 := pow_le_pow_left₀ hA hAle 3
  have hA2eq : (A / L) ^ 2 = A ^ 2 / L ^ 2 := by rw [div_pow]
  have hA3eq : (A / L) ^ 3 = A ^ 3 / L ^ 3 := by rw [div_pow]
  have hL2' : (L + 2) / L ^ 2 ≤ 2 / L := by
    rw [div_le_div_iff₀ (pow_pos hLpos 2) hLpos]
    nlinarith only [mul_le_mul_of_nonneg_left hL2 hLpos.le]
  have hL3' : (L + 2) / L ^ 3 ≤ 2 / L := by
    rw [div_le_div_iff₀ (pow_pos hLpos 3) hLpos]
    nlinarith only [mul_le_mul_of_nonneg_left hL2 (sq_nonneg L), mul_le_mul_of_nonneg_left hL2 hLpos.le, hLpos]
  have herr2 : (A / L) ^ 2 * (k2 * J - T2r) ≤ Amax ^ 2 * (k2 * C + Ct) * (2 / L) := by
    rw [hA2eq]
    calc A ^ 2 / L ^ 2 * (k2 * J - T2r)
        ≤ A ^ 2 / L ^ 2 * ((k2 * C + Ct) * (L + 2)) :=
          mul_le_mul_of_nonneg_left hin2 (by positivity)
      _ ≤ Amax ^ 2 / L ^ 2 * ((k2 * C + Ct) * (L + 2)) := by
          apply mul_le_mul_of_nonneg_right _ hC2L2nn
          exact div_le_div_of_nonneg_right hnum (pow_pos hLpos 2).le
      _ = Amax ^ 2 * (k2 * C + Ct) * ((L + 2) / L ^ 2) := by ring
      _ ≤ Amax ^ 2 * (k2 * C + Ct) * (2 / L) :=
          mul_le_mul_of_nonneg_left hL2' (mul_nonneg (pow_nonneg hAmax 2) hC2nn)
  have herr3 : (2 / 3) * (A / L) ^ 3 * (k3 * J - T3r)
      ≤ (2 / 3) * Amax ^ 3 * (k3 * C + Ct) * (2 / L) := by
    rw [hA3eq]
    calc (2 / 3) * (A ^ 3 / L ^ 3) * (k3 * J - T3r)
        ≤ (2 / 3) * (A ^ 3 / L ^ 3) * ((k3 * C + Ct) * (L + 2)) :=
          mul_le_mul_of_nonneg_left hin3 (by positivity)
      _ ≤ (2 / 3) * (Amax ^ 3 / L ^ 3) * ((k3 * C + Ct) * (L + 2)) := by
          apply mul_le_mul_of_nonneg_right _ hC3L2nn
          exact mul_le_mul_of_nonneg_left
            (div_le_div_of_nonneg_right hnum3 (pow_pos hLpos 3).le) (by norm_num)
      _ = (2 / 3) * Amax ^ 3 * (k3 * C + Ct) * ((L + 2) / L ^ 3) := by ring
      _ ≤ (2 / 3) * Amax ^ 3 * (k3 * C + Ct) * (2 / L) :=
          mul_le_mul_of_nonneg_left hL3' (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hAmax 3)) hC3nn)
  have hsum : Amax ^ 2 * (k2 * C + Ct) * (2 / L) + (2 / 3) * Amax ^ 3 * (k3 * C + Ct) * (2 / L)
      = (2 * Amax ^ 2 * (k2 * C + Ct) + (4 / 3) * Amax ^ 3 * (k3 * C + Ct)) / L := by ring
  have hKL : (2 * Amax ^ 2 * (k2 * C + Ct) + (4 / 3) * Amax ^ 3 * (k3 * C + Ct)) / L ≤ A * e := by
    rw [div_le_iff₀ hLpos]; linarith [hK]
  linarith [herr2, herr3, hsum, hKL]

set_option maxHeartbeats 8000000 in
/-- **HB §9's `P₃` master bound on the wide range `|Im s| ≤ 10 log q`** (the form needed by the
diagonal argument at `σ, σ+iγ, σ+2iγ, σ+3iγ` with `H ≤ log q`, where the input is available on
`|Im s| ≤ 10 log q` from HB Lemma 3.1).  Transfer of the proved `OffAxis.masterP3H`: the two
height-dependent steps (`hs3 : |s.im| ≤ L` fed to the log-derivative input, and
`‖s‖ ≤ L + 5` fed to the uniform inverse-square zero-sum bound) are replaced by
`|s.im| ≤ 10 L` and by the unrestricted `HB94.Lam0GeEngine.invSqSum_uniform`. -/
private theorem masterWide_local {a δ c e M : ℝ} (ha : 0 < a) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (he : 0 < e) :
    ∃ L₀ : ℝ, ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
      (hprim : χ.IsPrimitive) {L lam₁ : ℝ}, L₀ ≤ L → Real.log (N : ℝ) ≤ L → 0 ≤ lam₁ →
      lam₁ ≤ M → Work.ZeroFreeTables.OffAxis.WideLogDerivHyp χ δ L c →
      ∀ s : ℂ, s.re = 1 + a / L → |s.im| ≤ 10 * L →
        Work.ZeroFreeTables.SigmaP3L N L χ s a lam₁
          ≤ -Work.ZeroFreeTables.P3NearSumL N L χ s a lam₁ δ + (a + lam₁) * (c + e) := by
  obtain ⟨Cq, hCqpos, hCq⟩ := Work.ZeroFreeTables.HB94.Lam0GeEngine.invSqSum_uniform
  set C : ℝ := (5 + Real.log 11) * Cq with hCdef
  have hCpos : 0 < C := by
    rw [hCdef]
    have : 0 < Real.log 11 := Real.log_pos (by norm_num)
    positivity
  obtain ⟨Ct, hCtpos, hCt⟩ := Work.ZeroFreeTables.P9.paritySum_re_bound
  have hC2pos : 0 < (1 + 4 / δ ^ 2) * C + Ct := by
    have : (0 : ℝ) ≤ 4 / δ ^ 2 := div_nonneg (by norm_num) (sq_nonneg δ)
    positivity
  have hC3pos : 0 < (2 / δ) * (1 + 4 / δ ^ 2) * C + Ct := by
    have h1 : (0 : ℝ) ≤ 1 + 4 / δ ^ 2 := by
      have : (0 : ℝ) ≤ 4 / δ ^ 2 := div_nonneg (by norm_num) (sq_nonneg δ)
      linarith
    have : 0 < (2 / δ) := by positivity
    positivity
  set K : ℝ := 2 * (a + M) ^ 2 * ((1 + 4 / δ ^ 2) * C + Ct)
    + (4 / 3) * (a + M) ^ 3 * ((2 / δ) * (1 + 4 / δ ^ 2) * C + Ct) with hKdef
  refine ⟨max 4 (max (a + 2) (max (2 * a / δ)
    (max (Real.exp (max a a⁻¹) + 4) (K / (a * e))))), ?_⟩
  intro N _ χ hχ hprim L lam₁ hL hlogN hlam₁ hM hwd s hsre hsim
  have hX : max (a + 2) (max (2 * a / δ) (max (Real.exp (max a a⁻¹) + 4) (K / (a * e)))) ≤ L :=
    le_trans (le_max_right 4 _) hL
  have hY : max (2 * a / δ) (max (Real.exp (max a a⁻¹) + 4) (K / (a * e))) ≤ L :=
    le_trans (le_max_right (a + 2) _) hX
  have hZ : max (Real.exp (max a a⁻¹) + 4) (K / (a * e)) ≤ L :=
    le_trans (le_max_right (2 * a / δ) _) hY
  have hLge4 : 4 ≤ L := le_trans (le_max_left 4 _) hL
  have hLge2 : 2 ≤ L := by linarith
  have hLpos : 0 < L := by linarith
  have hLge1 : 1 ≤ L := by linarith
  have ha2 : a + 2 ≤ L := le_trans (le_max_left (a + 2) _) hX
  have haL : a ≤ L := by linarith
  have h2aδ : 2 * a ≤ δ * L := by
    have h := le_trans (le_max_left (2 * a / δ) _) hY
    rw [div_le_iff₀ hδ0] at h
    linarith
  have hlogL_ge : max a a⁻¹ ≤ Real.log L := by
    have hexp : Real.exp (max a a⁻¹) ≤ L := by linarith [le_trans (le_max_left _ _) hZ]
    have h := Real.log_le_log (Real.exp_pos (max a a⁻¹)) hexp
    rwa [Real.log_exp] at h
  have hmpos : 0 < max a a⁻¹ := lt_of_lt_of_le ha (le_max_left a a⁻¹)
  have hlogL_pos : 0 < Real.log L := lt_of_lt_of_le hmpos hlogL_ge
  have hKe : K ≤ a * e * L := by
    have h := le_trans (le_max_right _ _) hZ
    rw [div_le_iff₀ (mul_pos ha he)] at h
    linarith
  -- facts at `s`
  have hsre_gt : 1 < s.re := by rw [hsre]; linarith [div_pos ha hLpos]
  have hsδ : s.re ≤ 1 + δ / 2 := by
    rw [hsre]
    have h : a / L ≤ δ / 2 := by rw [div_le_iff₀ hLpos]; linarith
    linarith
  have hα : 0 ≤ a + lam₁ := by linarith
  obtain ⟨par, hpar0, hpar1⟩ : ∃ par : ℕ, (χ.Even → par = 0) ∧ (χ.Odd → par = 1) := by
    rcases χ.even_or_odd with hE | hO
    · exact ⟨0, fun _ => rfl, fun hO => absurd hO hE.not_odd⟩
    · exact ⟨1, fun hE => absurd hE hO.not_even, fun _ => rfl⟩
  have hpar_le : par ≤ 1 := by
    rcases χ.even_or_odd with hE | hO
    · rw [hpar0 hE]; exact zero_le_one
    · rw [hpar1 hO]
  obtain ⟨hsum2, _⟩ := Work.ZeroFreeTables.P9.lDiffExplicit_gen χ hχ hprim 1 (by norm_num) par
    hpar0 hpar1 hsre_gt
  obtain ⟨hsum3, _⟩ := Work.ZeroFreeTables.P9.lDiffExplicit_gen χ hχ hprim 2 (by norm_num) par
    hpar0 hpar1 hsre_gt
  have hmain := Work.ZeroFreeTables.P9.prim.SigmaP3L_le_nearP3sum_add χ hχ hprim hα hLpos hδ0 hδ1
    hsre_gt hsδ par hpar0 hpar1 hsum2 hsum3
  -- the `(L'/L)` slot
  have hbridge := Work.ZeroFreeTables.P9.invNearSum_eq_tsum_gen χ hχ hprim s hδ0 (le_of_lt hδ1)
  have hs1 : 1 + 1 / (L * Real.log L) ≤ s.re := by
    rw [hsre]
    have h1 : 1 ≤ a * Real.log L := by
      have h := mul_le_mul_of_nonneg_left (le_trans (le_max_right a a⁻¹) hlogL_ge) (le_of_lt ha)
      rwa [mul_inv_cancel₀ (ne_of_gt ha)] at h
    have : 1 / (L * Real.log L) ≤ a / L := by
      rw [div_le_div_iff₀ (by positivity : 0 < L * Real.log L) hLpos]
      nlinarith only [mul_le_mul_of_nonneg_left h1 hLpos.le]
    linarith
  have hs2 : s.re ≤ 1 + Real.log L / L := by
    rw [hsre]
    have h2 : a ≤ Real.log L := le_trans (le_max_left a a⁻¹) hlogL_ge
    have : a / L ≤ Real.log L / L := by
      rw [div_le_div_iff₀ hLpos hLpos]; nlinarith only [mul_le_mul_of_nonneg_right h2 hLpos.le]
    linarith
  have hs3 : |s.im| ≤ 10 * L := hsim
  have hlog := hwd s hs1 hs2 hs3
  have hlog' : (-logDeriv (DirichletCharacter.LFunction χ) s).re
      + Work.ZeroFreeTables.P9.nearInvSum N χ s δ ≤ c * L := by
    rw [← hbridge]; exact hlog
  have hterm1 : ((a + lam₁) / L) *
      ((-logDeriv (DirichletCharacter.LFunction χ) s).re
        + Work.ZeroFreeTables.P9.nearInvSum N χ s δ) ≤ (a + lam₁) * c := by
    have h := mul_le_mul_of_nonneg_left hlog' (div_nonneg hα (le_of_lt hLpos))
    have heq : (a + lam₁) / L * (c * L) = (a + lam₁) * c := by field_simp
    linarith [heq.le, heq.ge]
  -- far zeros and parity
  have hlogLle : Real.log L ≤ L := by
    have := Real.log_le_sub_one_of_pos hLpos; linarith
  have hnorm_s : ‖s‖ ≤ 10 * L + 2 := by
    have h := Complex.norm_le_abs_re_add_abs_im s
    rw [abs_of_pos (lt_trans zero_lt_one hsre_gt)] at h
    calc ‖s‖ ≤ s.re + |s.im| := h
      _ = 1 + a / L + |s.im| := by rw [hsre]
      _ ≤ 1 + a / L + 10 * L := by linarith [hsim]
      _ ≤ 10 * L + 2 := by
          have hdiv : a / L ≤ 1 := (div_le_one hLpos).mpr haL
          linarith
  have hlog2s : Real.log (2 + ‖s‖) ≤ Real.log 11 + 2 * L := by
    have h1 : (0 : ℝ) < 2 + ‖s‖ := by positivity
    have h2 : 2 + ‖s‖ ≤ 11 * L ^ 2 := by
      nlinarith only [hnorm_s, hLge4, mul_le_mul_of_nonneg_right hLge4 (le_trans (by norm_num) hLge4)]
    calc Real.log (2 + ‖s‖) ≤ Real.log (11 * L ^ 2) := Real.log_le_log h1 h2
      _ = Real.log 11 + 2 * Real.log L := by
          rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]; push_cast; ring
      _ ≤ Real.log 11 + 2 * L := by linarith [hlogLle]
  have hJ : Work.ZeroFreeTables.P9.invSqSum N χ s ≤ C * (L + 2) := by
    have h := hCq χ hχ hprim s
    have hlog11 : 0 < Real.log 11 := Real.log_pos (by norm_num)
    have hsum : Real.log (N : ℝ) + Real.log (2 + ‖s‖) + 2 ≤ 3 * L + Real.log 11 + 2 := by
      linarith [hlogN, hlog2s]
    have h2 : Cq * (Real.log (N : ℝ) + Real.log (2 + ‖s‖) + 2) ≤ Cq * (3 * L + Real.log 11 + 2) :=
      mul_le_mul_of_nonneg_left hsum hCqpos.le
    have h3 : Cq * (3 * L + Real.log 11 + 2) ≤ C * (L + 2) := by
      rw [hCdef]
      have h4 : 3 * L + Real.log 11 + 2 ≤ (5 + Real.log 11) * (L + 2) := by
        nlinarith only [mul_nonneg hLpos.le hlog11.le, hLpos.le, hlog11.le]
      calc Cq * (3 * L + Real.log 11 + 2) ≤ Cq * ((5 + Real.log 11) * (L + 2)) :=
            mul_le_mul_of_nonneg_left h4 hCqpos.le
        _ = (5 + Real.log 11) * Cq * (L + 2) := by ring
    linarith [h, h2, h3]
  obtain ⟨hT2abs, hT3abs⟩ := hCt s (by linarith) par hpar_le
  have hnegT2 : -(∑' n : ℕ, (1 / (s + ((par + 2 * n : ℕ) : ℂ))) ^ 2).re ≤ Ct := by
    linarith [(abs_le.mp hT2abs).1]
  have hnegT3 : -(∑' n : ℕ, (1 / (s + ((par + 2 * n : ℕ) : ℂ))) ^ 3).re ≤ Ct := by
    linarith [(abs_le.mp hT3abs).1]
  have hAle : a + lam₁ ≤ a + M := by linarith
  have hAe_pos : 0 < (a + lam₁) * e := mul_pos (by linarith) he
  have hKL : K ≤ (a + lam₁) * e * L := by
    have h1 : a * e ≤ (a + lam₁) * e :=
      mul_le_mul_of_nonneg_right (by linarith only [hlam₁]) he.le
    have h2 : a * e * L ≤ (a + lam₁) * e * L := mul_le_mul_of_nonneg_right h1 hLpos.le
    linarith [hKe, h2]
  have herr := error_bound_local (A := a + lam₁) (Amax := a + M) (k2 := 1 + 4 / δ ^ 2)
    (k3 := (2 / δ) * (1 + 4 / δ ^ 2)) (C := C) (Ct := Ct)
    (J := Work.ZeroFreeTables.P9.invSqSum N χ s)
    (T2r := (∑' n : ℕ, (1 / (s + ((par + 2 * n : ℕ) : ℂ))) ^ 2).re)
    (T3r := (∑' n : ℕ, (1 / (s + ((par + 2 * n : ℕ) : ℂ))) ^ 3).re)
    (L := L) (e := e)
    hα hAle (by linarith) (by positivity) (by positivity) hCpos.le hCtpos.le hJ hnegT2 hnegT3
    hLge2 hLpos hAe_pos (by rw [← hKdef]; exact hKL)
  have hbridge2 := Work.ZeroFreeTables.P9.P3NearSumL_eq_nearP3sum (s := s) (a := a)
    (lam₁ := lam₁) (L := L) χ hχ hprim hδ0 (le_of_lt hδ1)
  rw [← hbridge2] at hmain
  linarith [hmain, hterm1, herr]

/-- **HB §9's point bound at height `≤ 3H`** (the per-point analytic input of the diagonal
argument at a repeated zero): `Σ(s,χ) ≤ −P3NearSumL + (a+λ₁)(1/6 + e)` for every non-principal
`χ` of level `q` and every point of the line `Re s = 1 + a/log q` with `|Im s| ≤ 3H`. -/
private theorem pointBoundWideLocal {a e M H : ℝ} (ha : 0 < a) (he : 0 < e) (hM : 0 ≤ M)
    (hH1 : 1 ≤ H) :
    ∃ q₀ : ℕ, ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
      (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {lam₁ : ℝ}, 0 ≤ lam₁ → lam₁ ≤ M →
      H ≤ Real.log (q : ℝ) →
      ∀ s : ℂ, s.re = 1 + a / Real.log (q : ℝ) → |s.im| ≤ 3 * H →
        Work.ZeroFreeTables.SigmaP3L q (Real.log q) χ s a lam₁
          ≤ -Work.ZeroFreeTables.P3NearSumL q (Real.log q) χ s a lam₁ δ + (a + lam₁) * (1 / 6 + e) := by
  obtain ⟨L₀i, δ, hδ0, hδ1, hin⟩ := RectRepInput (e / 3) (by positivity)
  obtain ⟨L₀m, hmast⟩ := masterWide_local (a := a) (δ := δ) (c := 1 / 6 + e / 3) (e := e / 3)
    (M := M) ha hδ0 hδ1 (by positivity)
  obtain ⟨L₀c, himp⟩ := Work.ZeroFreeTables.Rep9.imprimCorrBoundedH (a := a) (H := 3 * H)
    (e := e / 3) (M := M) ha (by positivity) hM
  refine ⟨max (max (Nat.ceil (Real.exp L₀i)) (Nat.ceil (Real.exp L₀m)))
      (max (Nat.ceil (Real.exp L₀c)) 5) + 1, δ, hδ0, hδ1, ?_⟩
  intro q hq inst χ hχ lam₁ hlam0 hlamM hHL s hsre hsim
  haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  set L : ℝ := Real.log (q : ℝ) with hLdef
  have hq1 : 1 < q := by omega
  have hq2 : 2 ≤ q := by omega
  have hLpos : 0 < L := by rw [hLdef]; exact Real.log_pos (by exact_mod_cast hq1)
  have hceL : Nat.ceil (Real.exp L₀i) ≤ q := by omega
  have hceM : Nat.ceil (Real.exp L₀m) ≤ q := by omega
  have hceI : Nat.ceil (Real.exp L₀c) ≤ q := by omega
  have hexpL : Real.exp L₀i ≤ (q : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast hceL)
  have hexpM : Real.exp L₀m ≤ (q : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast hceM)
  have hexpI : Real.exp L₀c ≤ (q : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast hceI)
  have hLL : L₀i ≤ L := by
    rw [hLdef]
    calc L₀i = Real.log (Real.exp L₀i) := (Real.log_exp L₀i).symm
      _ ≤ Real.log (q : ℝ) := Real.log_le_log (Real.exp_pos _) hexpL
  have hLm : L₀m ≤ L := by
    rw [hLdef]
    calc L₀m = Real.log (Real.exp L₀m) := (Real.log_exp L₀m).symm
      _ ≤ Real.log (q : ℝ) := Real.log_le_log (Real.exp_pos _) hexpM
  have hLi : L₀c ≤ L := by
    rw [hLdef]
    calc L₀c = Real.log (Real.exp L₀c) := (Real.log_exp L₀c).symm
      _ ≤ Real.log (q : ℝ) := Real.log_le_log (Real.exp_pos _) hexpI
  have hHL' : H ≤ L := by rw [hLdef]; exact hHL
  have hχprim : χ.primitiveCharacter.IsPrimitive :=
    DirichletCharacter.primitiveCharacter_isPrimitive χ
  have hχprimne : χ.primitiveCharacter ≠ 1 := by
    intro h1
    refine hχ ?_
    have h2 := χ.changeLevel_primitiveCharacter
    rw [h1, DirichletCharacter.changeLevel_one χ.conductor_dvd_level] at h2
    exact h2.symm
  have hlogN : Real.log ((χ.conductor : ℕ) : ℝ) ≤ L := by
    have hle : χ.conductor ≤ q :=
      Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) χ.conductor_dvd_level
    rw [hLdef]
    exact Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne χ.conductor))
      (by exact_mod_cast hle)
  have hN3 : 3 ≤ χ.conductor := Work.LinnikAreas2.three_le_conductor χ hχ
  have hlogd : Work.ZeroFreeTables.OffAxis.WideLogDerivHyp χ.primitiveCharacter δ L (1 / 6 + e / 3) :=
    hin χ.primitiveCharacter hχprimne hχprim hN3 hLL hlogN
  have hsim10 : |s.im| ≤ 10 * L := by
    have h1 : 3 * H ≤ 3 * L := by linarith
    linarith
  have hm := hmast χ.primitiveCharacter hχprimne hχprim hLm hlogN hlam0 hlamM hlogd s
    (by rw [hLdef]; exact hsre) hsim10
  have hi := himp χ hχ hLi (le_of_eq hLdef.symm) hlam0 hlamM s hsre (by
    have : H ≤ 3 * H := by linarith
    linarith)
  have hn := Work.ZeroFreeTables.Rep9.nearSum_primitive_le hq2 χ hχ L s a lam₁ δ hδ0.le hδ1
  have hkey : (a + lam₁) * ((1 / 6 + e / 3) + e / 3) + (a + lam₁) * (e / 3)
      = (a + lam₁) * (1 / 6 + e) := by ring
  have hsre' : s.re = 1 + a / L := by rw [hLdef]; exact hsre
  linarith [hm, hi, hn, hkey]


/-- **The generic case of HB Lemma 9.1 at a repeated zero at height `H`** (`χ₁² ≠ 1`,
`χ₁³ ≠ 1`), with the diagonal four-point combination and all near sums dropped. -/
theorem rectRepGenericLocal {a K ε H W : ℝ} (ha : 0 < a) (hK : 0 < K) (hε : 0 < ε)
    (hH1 : 1 ≤ H) (hHW : 3 * H + 1 ≤ W) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      H ≤ Real.log (q : ℝ) → Work.ZeroFreeTables.IsMinWideAt H W χ₁ ρ₁ →
      2 ≤ Work.LinnikContract.zeroMult χ₁ ρ₁ → χ₁ ^ 2 ≠ 1 → χ₁ ^ 3 ≠ 1 →
      Work.ZeroFreeTables.cond913 (Work.LinnikContract.lamOf q ρ₁)
        (Work.LinnikContract.lamOf q ρ₁) a K →
      Work.ZeroFreeTables.ineq913 (Work.LinnikContract.lamOf q ρ₁)
        (Work.LinnikContract.lamOf q ρ₁) a K ε := by
  set S : ℝ := K ^ 2 + 3 * K + 3 / 2 with hSdef
  have hSpos : 0 < S := by rw [hSdef]; positivity
  set e : ℝ := min (1 / (768 * K)) (a * S / (96 * K)) with hedef
  have hepos : 0 < e := by
    rw [hedef]; exact lt_min (by positivity) (by positivity)
  have he1 : e ≤ 1 / (768 * K) := min_le_left _ _
  have he2 : e ≤ a * S / (96 * K) := min_le_right _ _
  set e0 : ℝ := e / 2 with he0def
  have he0pos : 0 < e0 := by rw [he0def]; linarith
  set M : ℝ := a * (Kond K + 1) with hMdef
  have hMnn : 0 ≤ M := by
    rw [hMdef]
    exact mul_nonneg ha.le (by linarith [Work.ZeroFreeTables.Rep9.Kond_pos hK])
  obtain ⟨q0b, δ, hδ0, hδ1, hpb⟩ :=
    pointBoundWideLocal (a := a) (e := e) (M := M) (H := H) ha hepos hMnn hH1
  obtain ⟨q0p, hprinc⟩ :=
    RectRepPrincipal (a := a) (e := e0) (M := M) (H := H) ha he0pos hMnn hH1
  refine ⟨max (max q0b q0p) (max (Nat.ceil (Real.exp (max (M / δ) 10))) 5), ?_⟩
  intro q hq inst χ₁ ρ₁ hHlog hmin hmult hχ2 hχ3 hcond
  have hqb : q0b ≤ q := by omega
  have hqp : q0p ≤ q := by omega
  have hq1 : 1 < q := by omega
  have hq2 : 2 ≤ q := by omega
  have hlogqpos : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast hq1)
  have hce : Nat.ceil (Real.exp (max (M / δ) 10)) ≤ q := by omega
  have hLnb : Real.exp (max (M / δ) 10) ≤ (q : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast hce)
  have hMδ : M / δ ≤ Real.log (q : ℝ) :=
    calc M / δ ≤ max (M / δ) 10 := le_max_left _ _
      _ = Real.log (Real.exp (max (M / δ) 10)) := (Real.log_exp _).symm
      _ ≤ Real.log (q : ℝ) := Real.log_le_log (Real.exp_pos _) hLnb
  have hMlt : M ≤ δ * Real.log (q : ℝ) := by
    have h' := hMδ
    rw [div_le_iff₀ hδ0] at h'
    linarith [h']
  have hlam0 : 0 ≤ lamOf q ρ₁ := IsMinWideAt.lam_nonneg hmin
  have hlamM : lamOf q ρ₁ ≤ M := by
    rw [hMdef]
    exact Work.ZeroFreeTables.Rep9.lam_le_of_cond913 ha hK hlam0 hcond
  have hδlam : lamOf q ρ₁ / Real.log (q : ℝ) ≤ δ := by
    rw [div_le_iff₀ hlogqpos]
    exact le_trans hlamM hMlt
  have hγ : |ρ₁.im| ≤ H := hmin.2.2.1
  have hχ1ne : χ₁ ≠ 1 := hmin.1
  have hcube : ((a + lamOf q ρ₁) / a) ^ 3 ≤ Kond K + 1 :=
    Work.ZeroFreeTables.Rep9.cond913_cube_le ha hlam0 hcond
  set al : ℝ := a + lamOf q ρ₁ with hal
  have halpos : 0 < al := by rw [hal]; linarith
  set σ : ℂ := ((1 + a / Real.log (q : ℝ) : ℝ) : ℂ) with hσ
  have hre_of : ∀ θ : ℝ, (σ + ((θ : ℝ) : ℂ) * Complex.I).re = 1 + a / Real.log (q : ℝ) := by
    intro θ
    rw [hσ, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  have him_of : ∀ θ : ℝ, (σ + ((θ : ℝ) : ℂ) * Complex.I).im = θ := by
    intro θ
    rw [hσ, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  have hσim : |σ.im| ≤ 3 * H := by
    have h : σ.im = 0 := by rw [hσ]; exact Complex.ofReal_im _
    rw [h, abs_zero]; linarith [hH1]
  have hσre : σ.re = 1 + a / Real.log (q : ℝ) := by
    rw [hσ]; exact Complex.ofReal_re _
  -- (0) the principal character at `σ`
  have hS0 : SigmaP3L q (Real.log (q : ℝ)) (1 : DirichletCharacter ℂ q) σ a (lamOf q ρ₁)
      ≤ P3R (al / a) + al * e0 := by
    have h := hprinc q hqp hlam0 hlamM hHlog σ hσre hσim
    have hz : (↑a + ↑(lamOf q ρ₁) : ℂ)
          / ((σ - 1) * ((Real.log (q : ℝ) : ℝ) : ℂ)) = ((al / a : ℝ) : ℂ) := by
      have hσ1 : σ - 1 = (((a / Real.log (q : ℝ) : ℝ)) : ℂ) := by
        have hcast : (((1 + a / Real.log (q : ℝ) : ℝ)) : ℂ) - 1
            = (((1 + a / Real.log (q : ℝ)) - 1 : ℝ) : ℂ) := by
          rw [← Complex.ofReal_one, ← Complex.ofReal_sub]
        rw [hσ, hcast]
        congr 1
        ring
      have hσ2 : (σ - 1) * ((Real.log (q : ℝ) : ℝ) : ℂ) = ((a : ℝ) : ℂ) := by
        rw [hσ1, ← Complex.ofReal_mul]
        congr 1
        exact div_mul_cancel₀ a (ne_of_gt hlogqpos)
      rw [hσ2, ← Complex.ofReal_add, ← Complex.ofReal_div, hal]
    have hP : (P3 ((↑a + ↑(lamOf q ρ₁)) / ((σ - 1) * ((Real.log (q : ℝ) : ℝ) : ℂ)))).re
        = P3R (al / a) := by
      rw [hz]; exact Work.ZeroFreeTables.Rep9.P3_ofReal_re (al / a)
    rw [hP] at h
    simpa only [hal] using h
  -- (1) `χ₁` at `σ + iγ`: the double zero gives `−2 P₃(1)`
  have hS1 : SigmaP3L q (Real.log (q : ℝ)) χ₁
      (σ + ((ρ₁.im : ℝ) : ℂ) * Complex.I) a (lamOf q ρ₁)
      ≤ -(2 * P3R 1) + al * (1 / 6 + e) := by
    have hsim : |(σ + ((ρ₁.im : ℝ) : ℂ) * Complex.I).im| ≤ 3 * H := by
      rw [him_of ρ₁.im]; linarith [hγ, hH1]
    have h1 := hpb q hqb χ₁ hχ1ne hlam0 hlamM hHlog _ (hre_of ρ₁.im) hsim
    have h3 : (2 : ℝ) * P3R 1 ≤ P3NearSumL q (Real.log (q : ℝ)) χ₁
        (σ + ((ρ₁.im : ℝ) : ℂ) * Complex.I) a (lamOf q ρ₁) δ := by
      have h := Work.ZeroFreeTables.Rep9.nearSumDoubleH (q := q) χ₁ ρ₁ hq2 hmin
        (by linarith only [hH1, hHW]) hmult ha hδ0 hδ1 hδlam
      have hs : ((((1 + a / Real.log (q : ℝ) : ℝ)) : ℂ) + ((ρ₁.im : ℝ) : ℂ) * Complex.I)
          = σ + ((ρ₁.im : ℝ) : ℂ) * Complex.I := by rw [hσ]
      rw [hs] at h
      exact h
    linarith [h1, h3]
  -- (2) `χ₁²` at `σ + 2iγ`: the near sum is dropped
  have hS2 : SigmaP3L q (Real.log (q : ℝ)) (χ₁ ^ 2)
      (σ + ((2 * ρ₁.im : ℝ) : ℂ) * Complex.I) a (lamOf q ρ₁) ≤ al * (1 / 6 + e) := by
    have hsim : |(σ + ((2 * ρ₁.im : ℝ) : ℂ) * Complex.I).im| ≤ 3 * H := by
      rw [him_of (2 * ρ₁.im), abs_mul, show |(2 : ℝ)| = 2 by norm_num]
      linarith [hγ, hH1]
    have h1 := hpb q hqb (χ₁ ^ 2) (fun hcon => hχ2 hcon) hlam0 hlamM hHlog _
      (hre_of (2 * ρ₁.im)) hsim
    have h3 : (0 : ℝ) ≤ P3NearSumL q (Real.log (q : ℝ)) (χ₁ ^ 2)
        (σ + ((2 * ρ₁.im : ℝ) : ℂ) * Complex.I) a (lamOf q ρ₁) δ := by
      have h := RectRepNearSum χ₁ (χ₁ ^ 2) ρ₁ hq2 hmin hHW (fun hcon => hχ2 hcon) hlam0 ha
        hδ0 hδ1 (hre_of (2 * ρ₁.im)) hsim
      simpa only using h
    linarith [h1, h3]
  -- (3) `χ₁³` at `σ + 3iγ`: the near sum is dropped
  have hS3 : SigmaP3L q (Real.log (q : ℝ)) (χ₁ ^ 3)
      (σ + ((3 * ρ₁.im : ℝ) : ℂ) * Complex.I) a (lamOf q ρ₁) ≤ al * (1 / 6 + e) := by
    have hsim : |(σ + ((3 * ρ₁.im : ℝ) : ℂ) * Complex.I).im| ≤ 3 * H := by
      rw [him_of (3 * ρ₁.im), abs_mul, show |(3 : ℝ)| = 3 by norm_num]
      linarith [hγ, hH1]
    have h1 := hpb q hqb (χ₁ ^ 3) (fun hcon => hχ3 hcon) hlam0 hlamM hHlog _
      (hre_of (3 * ρ₁.im)) hsim
    have h3 : (0 : ℝ) ≤ P3NearSumL q (Real.log (q : ℝ)) (χ₁ ^ 3)
        (σ + ((3 * ρ₁.im : ℝ) : ℂ) * Complex.I) a (lamOf q ρ₁) δ := by
      have h := RectRepNearSum χ₁ (χ₁ ^ 3) ρ₁ hq2 hmin hHW (fun hcon => hχ3 hcon) hlam0 ha
        hδ0 hδ1 (hre_of (3 * ρ₁.im)) hsim
      simpa only using h
    linarith [h1, h3]
  -- the endgame
  have hD : 0 ≤ (K ^ 2 + K + 1 / 2) * P3R (al / a) - (2 * K ^ 2 + 4 * K + 3 / 2) * P3R 1
      + al * ((K ^ 2 + K + 1 / 2) * e0 + (K ^ 2 + 2 * K + 3 / 4) * (1 / 6 + e)
        + (K + 1 / 2) * (1 / 6 + e) + (1 / 4) * (1 / 6 + e)) := by
    have hA0 : (0 : ℝ) ≤ K ^ 2 + K + 1 / 2 := by positivity
    have hA1 : (0 : ℝ) ≤ K ^ 2 + 2 * K + 3 / 4 := by positivity
    have hA2 : (0 : ℝ) ≤ K + 1 / 2 := by linarith
    have hA3 : (0 : ℝ) ≤ 1 / 4 := by norm_num
    have i0 := mul_le_mul_of_nonneg_left hS0 hA0
    have i1 := mul_le_mul_of_nonneg_left hS1 hA1
    have i2 := mul_le_mul_of_nonneg_left hS2 hA2
    have i3 := mul_le_mul_of_nonneg_left hS3 hA3
    have hsum : (K ^ 2 + K + 1 / 2) * (P3R (al / a) + al * e0)
        + (K ^ 2 + 2 * K + 3 / 4) * (-(2 * P3R 1) + al * (1 / 6 + e))
        + (K + 1 / 2) * (al * (1 / 6 + e)) + (1 / 4) * (al * (1 / 6 + e))
        = (K ^ 2 + K + 1 / 2) * P3R (al / a) - (2 * K ^ 2 + 4 * K + 3 / 2) * P3R 1
          + al * ((K ^ 2 + K + 1 / 2) * e0 + (K ^ 2 + 2 * K + 3 / 4) * (1 / 6 + e)
            + (K + 1 / 2) * (1 / 6 + e) + (1 / 4) * (1 / 6 + e)) := by
      ring
    have hcomb := RectRepComb χ₁ (a := a) (lam₁ := lamOf q ρ₁) (γ := ρ₁.im) (K := K) (H := H)
      hq2 ha hK hγ hlam0 hχ1ne
    have hcomb' : 0 ≤ (K ^ 2 + K + 1 / 2) * SigmaP3L q (Real.log (q : ℝ)) 1 σ a (lamOf q ρ₁)
        + (K ^ 2 + 2 * K + 3 / 4) * SigmaP3L q (Real.log (q : ℝ)) χ₁
            (σ + ((ρ₁.im : ℝ) : ℂ) * Complex.I) a (lamOf q ρ₁)
        + (K + 1 / 2) * SigmaP3L q (Real.log (q : ℝ)) (χ₁ ^ 2)
            (σ + ((2 * ρ₁.im : ℝ) : ℂ) * Complex.I) a (lamOf q ρ₁)
        + (1 / 4) * SigmaP3L q (Real.log (q : ℝ)) (χ₁ ^ 3)
            (σ + ((3 * ρ₁.im : ℝ) : ℂ) * Complex.I) a (lamOf q ρ₁) := by
      simpa only [hσ] using hcomb
    linarith only [hcomb', i0, i1, i2, i3, hsum.le, hsum.ge]
  have hc : ((K ^ 2 + K + 1 / 2) * e0 + (K ^ 2 + 2 * K + 3 / 4) * (1 / 6 + e)
      + (K + 1 / 2) * (1 / 6 + e) + (1 / 4) * (1 / 6 + e)) * (48 * K)
      ≤ (12 * K + 1) * S := by
    have h := generic_budget hK he1
    have hbud : ((K ^ 2 + K + 1 / 2) * (e / 2) + (K ^ 2 + 2 * K + 3 / 4) * (1 / 6 + e)
        + (K + 1 / 2) * (1 / 6 + e) + (1 / 4) * (1 / 6 + e)) * (48 * K)
        ≤ (12 * K + 1) * (K ^ 2 + 3 * K + 3 / 2) := h
    have hCv : (K ^ 2 + K + 1 / 2) * e0 + (K ^ 2 + 2 * K + 3 / 4) * (1 / 6 + e)
        + (K + 1 / 2) * (1 / 6 + e) + (1 / 4) * (1 / 6 + e)
        = (K ^ 2 + K + 1 / 2) * (e / 2) + (K ^ 2 + 2 * K + 3 / 4) * (1 / 6 + e)
          + (K + 1 / 2) * (1 / 6 + e) + (1 / 4) * (1 / 6 + e) := by rw [he0def]
    rw [hCv, hSdef]
    exact hbud
  exact Work.ZeroFreeTables.Rep9.ineq913_diag_of_derived_poly (a := a) (K := K)
    (C := (K ^ 2 + K + 1 / 2) * e0 + (K ^ 2 + 2 * K + 3 / 4) * (1 / 6 + e)
      + (K + 1 / 2) * (1 / 6 + e) + (1 / 4) * (1 / 6 + e))
    (ε := ε) (lam := lamOf q ρ₁) ha hK hε hlam0 (by simpa only [hal] using hcube)
    hc (by simpa only [hal] using hD)

/-! ## The order-2 case (`χ₁² = 1`, the real character with `Im ρ₁ ≠ 0`) -/

/-- **HB Lemma 9.1 at a repeated zero, order-2 case.** -/
theorem rectRepOrder2H {a K ε H W : ℝ} (ha : 0 < a) (hK : 0 < K) (hε : 0 < ε)
    (hH1 : 1 ≤ H) (hHW : 3 * H + 1 ≤ W) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      H ≤ Real.log (q : ℝ) → Work.ZeroFreeTables.IsMinWideAt H W χ₁ ρ₁ →
      2 ≤ Work.LinnikContract.zeroMult χ₁ ρ₁ → χ₁ ^ 2 = 1 → ρ₁.im ≠ 0 →
      Work.ZeroFreeTables.cond913 (Work.LinnikContract.lamOf q ρ₁)
        (Work.LinnikContract.lamOf q ρ₁) a K →
      Work.ZeroFreeTables.ineq913 (Work.LinnikContract.lamOf q ρ₁)
        (Work.LinnikContract.lamOf q ρ₁) a K ε := by
  set S : ℝ := K ^ 2 + 3 * K + 3 / 2 with hSdef
  have hSpos : 0 < S := by rw [hSdef]; positivity
  set e : ℝ := min (1 / (768 * K)) (a * S / (96 * K * (K + 1 / 2))) with hedef
  have hepos : 0 < e := by
    rw [hedef]; exact lt_min (by positivity) (by positivity)
  have he1 : e ≤ 1 / (768 * K) := min_le_left _ _
  have he2 : e ≤ a * S / (96 * K * (K + 1 / 2)) := min_le_right _ _
  set e0 : ℝ := e / 2 with he0def
  have he0pos : 0 < e0 := by rw [he0def]; linarith
  set M : ℝ := a * (Kond K + 1) with hMdef
  have hMnn : 0 ≤ M := by
    rw [hMdef]
    exact mul_nonneg ha.le (by linarith [Work.ZeroFreeTables.Rep9.Kond_pos hK])
  obtain ⟨q0b, δ, hδ0, hδ1, hpb⟩ :=
    pointBoundWideLocal (a := a) (e := e) (M := M) (H := H) ha hepos hMnn hH1
  obtain ⟨q0p, hprinc⟩ :=
    RectRepPrincipal (a := a) (e := e0) (M := M) (H := H) ha he0pos hMnn hH1
  obtain ⟨q0c, hnearC⟩ := RectRepCaseCNear (a := a) (δ := δ) ha hδ0 hδ1
  obtain ⟨q0f, hfarC⟩ := RectRepCaseCFar (a := a) (δ := δ) (e := e) (M := M) ha hδ0 hδ1 hepos hMnn
  refine ⟨max (max (max q0b q0p) (max q0c q0f))
      (max (Nat.ceil (Real.exp (max (M / δ) 10))) 5), ?_⟩
  intro q hq inst χ₁ ρ₁ hHlog hmin hmult hsq him hcond
  have hqb : q0b ≤ q := by omega
  have hqp : q0p ≤ q := by omega
  have hqc : q0c ≤ q := by omega
  have hqf : q0f ≤ q := by omega
  have hq1 : 1 < q := by omega
  have hq2 : 2 ≤ q := by omega
  have hlogqpos : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast hq1)
  have hlogqne : Real.log (q : ℝ) ≠ 0 := ne_of_gt hlogqpos
  have hce : Nat.ceil (Real.exp (max (M / δ) 10)) ≤ q := by omega
  have hLnb : Real.exp (max (M / δ) 10) ≤ (q : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast hce)
  have hMδ : M / δ ≤ Real.log (q : ℝ) :=
    calc M / δ ≤ max (M / δ) 10 := le_max_left _ _
      _ = Real.log (Real.exp (max (M / δ) 10)) := (Real.log_exp _).symm
      _ ≤ Real.log (q : ℝ) := Real.log_le_log (Real.exp_pos _) hLnb
  have hMlt : M ≤ δ * Real.log (q : ℝ) := by
    have h' := hMδ
    rw [div_le_iff₀ hδ0] at h'
    linarith [h']
  -- ## facts about the pair
  have hlam0 : 0 ≤ lamOf q ρ₁ := IsMinWideAt.lam_nonneg hmin
  have hlamM : lamOf q ρ₁ ≤ M := by
    rw [hMdef]
    exact Work.ZeroFreeTables.Rep9.lam_le_of_cond913 ha hK hlam0 hcond
  have hδlam : lamOf q ρ₁ / Real.log (q : ℝ) ≤ δ := by
    rw [div_le_iff₀ hlogqpos]
    exact le_trans hlamM hMlt
  have hγ : |ρ₁.im| ≤ H := hmin.2.2.1
  have hχ1ne : χ₁ ≠ 1 := hmin.1
  have hcube : ((a + lamOf q ρ₁) / a) ^ 3 ≤ Kond K + 1 :=
    Work.ZeroFreeTables.Rep9.cond913_cube_le ha hlam0 hcond
  set al : ℝ := a + lamOf q ρ₁ with hal
  have halpos : 0 < al := by rw [hal]; linarith
  have hale : a ≤ al := by rw [hal]; linarith
  have hW : H + 2 ≤ W := by linarith [hH1, hHW]
  set σ : ℂ := ((1 + a / Real.log (q : ℝ) : ℝ) : ℂ) with hσ
  have hre_of : ∀ θ : ℝ, (σ + ((θ : ℝ) : ℂ) * Complex.I).re = 1 + a / Real.log (q : ℝ) := by
    intro θ
    rw [hσ, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  have him_of : ∀ θ : ℝ, (σ + ((θ : ℝ) : ℂ) * Complex.I).im = θ := by
    intro θ
    rw [hσ, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  have hσim : |σ.im| ≤ 3 * H := by
    have h : σ.im = 0 := by rw [hσ]; exact Complex.ofReal_im _
    rw [h, abs_zero]; linarith [hH1]
  have hσre : σ.re = 1 + a / Real.log (q : ℝ) := by
    rw [hσ]; exact Complex.ofReal_re _
  set W1 : ℝ := P3NearSumL q (Real.log (q : ℝ)) χ₁
    (σ + ((ρ₁.im : ℝ) : ℂ) * Complex.I) a (lamOf q ρ₁) δ with hW1def
  set Φ2 : ℝ := (P3 ((↑a + ↑(lamOf q ρ₁)) / ((↑a + ↑(lamOf q ρ₁))
    + ((2 * ρ₁.im * Real.log (q : ℝ) : ℝ) : ℂ) * Complex.I))).re with hΦ2def
  set Ψ2 : ℝ := (P3 ((↑a + ↑(lamOf q ρ₁)) / ((a : ℂ)
    + ((2 * ρ₁.im * Real.log (q : ℝ) : ℝ) : ℂ) * Complex.I))).re with hΨ2def
  -- ## (0) the principal character at `σ`
  have hS0 : SigmaP3L q (Real.log (q : ℝ)) (1 : DirichletCharacter ℂ q) σ a (lamOf q ρ₁)
      ≤ P3R (al / a) + al * e0 := by
    have h := hprinc q hqp hlam0 hlamM hHlog σ hσre hσim
    have hz : (↑a + ↑(lamOf q ρ₁) : ℂ)
          / ((σ - 1) * ((Real.log (q : ℝ) : ℝ) : ℂ)) = ((al / a : ℝ) : ℂ) := by
      have hσ1 : σ - 1 = (((a / Real.log (q : ℝ) : ℝ)) : ℂ) := by
        have hcast : (((1 + a / Real.log (q : ℝ) : ℝ)) : ℂ) - 1
            = (((1 + a / Real.log (q : ℝ)) - 1 : ℝ) : ℂ) := by
          rw [← Complex.ofReal_one, ← Complex.ofReal_sub]
        rw [hσ, hcast]
        congr 1
        ring
      have hσ2 : (σ - 1) * ((Real.log (q : ℝ) : ℝ) : ℂ) = ((a : ℝ) : ℂ) := by
        rw [hσ1, ← Complex.ofReal_mul]
        congr 1
        exact div_mul_cancel₀ a hlogqne
      rw [hσ2, ← Complex.ofReal_add, ← Complex.ofReal_div, hal]
    have hP : (P3 ((↑a + ↑(lamOf q ρ₁)) / ((σ - 1) * ((Real.log (q : ℝ) : ℝ) : ℂ)))).re
        = P3R (al / a) := by
      rw [hz]; exact Work.ZeroFreeTables.Rep9.P3_ofReal_re (al / a)
    rw [hP] at h
    simpa only [hal] using h
  -- ## (1) `χ₁` at `σ + iγ`, near sum kept
  have hS1w : SigmaP3L q (Real.log (q : ℝ)) χ₁
      (σ + ((ρ₁.im : ℝ) : ℂ) * Complex.I) a (lamOf q ρ₁)
      ≤ -W1 + al * (1 / 6 + e) := by
    have hsim : |(σ + ((ρ₁.im : ℝ) : ℂ) * Complex.I).im| ≤ 3 * H := by
      rw [him_of ρ₁.im]; linarith [hγ, hH1]
    have h1 := hpb q hqb χ₁ hχ1ne hlam0 hlamM hHlog _
      (hre_of ρ₁.im) hsim
    simpa only [hW1def, hal] using h1
  -- ## (2) `χ₁² = χ₀` at `σ + 2iγ` (principal)
  have hS2 : SigmaP3L q (Real.log (q : ℝ)) (χ₁ ^ 2)
      (σ + ((2 * ρ₁.im : ℝ) : ℂ) * Complex.I) a (lamOf q ρ₁)
      ≤ Ψ2 + al * e0 := by
    rw [hsq]
    have hsim : |(σ + ((2 * ρ₁.im : ℝ) : ℂ) * Complex.I).im| ≤ 3 * H := by
      rw [him_of (2 * ρ₁.im), abs_mul, show |(2 : ℝ)| = 2 by norm_num]
      linarith [hγ, hH1]
    have h := hprinc q hqp hlam0 hlamM hHlog _ (hre_of (2 * ρ₁.im)) hsim
    have hz : (↑a + ↑(lamOf q ρ₁) : ℂ)
          / (((σ + ((2 * ρ₁.im : ℝ) : ℂ) * Complex.I) - 1) * ((Real.log (q : ℝ) : ℝ) : ℂ))
        = (↑a + ↑(lamOf q ρ₁) : ℂ)
          / ((a : ℂ) + ((2 * ρ₁.im * Real.log (q : ℝ) : ℝ) : ℂ) * Complex.I) := by
      have h1 : (σ + ((2 * ρ₁.im : ℝ) : ℂ) * Complex.I) - 1
          = (((a / Real.log (q : ℝ) : ℝ)) : ℂ) + ((2 * ρ₁.im : ℝ) : ℂ) * Complex.I := by
        rw [hσ]
        push_cast
        ring_nf
      have h2 : ((((a / Real.log (q : ℝ) : ℝ)) : ℂ) + ((2 * ρ₁.im : ℝ) : ℂ) * Complex.I)
            * ((Real.log (q : ℝ) : ℝ) : ℂ)
          = ((a : ℂ) + ((2 * ρ₁.im * Real.log (q : ℝ) : ℝ) : ℂ) * Complex.I) := by
        rw [add_mul, ← Complex.ofReal_mul, div_mul_cancel₀ a hlogqne]
        rw [show ((2 * ρ₁.im : ℝ) : ℂ) * Complex.I * ((Real.log (q : ℝ) : ℝ) : ℂ)
            = (((2 * ρ₁.im * Real.log (q : ℝ) : ℝ)) : ℂ) * Complex.I by push_cast; ring]
      rw [h1, h2]
    have hP : (P3 ((↑a + ↑(lamOf q ρ₁)) / (((σ + ((2 * ρ₁.im : ℝ) : ℂ) * Complex.I) - 1)
        * ((Real.log (q : ℝ) : ℝ) : ℂ)))).re = Ψ2 := by
      rw [hz, hΨ2def]
    rw [hP] at h
    simpa only [hal] using h
  -- ## (3) `χ₁³ = χ₁` at `σ + 3iγ`, near sum dropped
  have hχ3ne : χ₁ ^ 3 ≠ 1 := by
    intro hcon
    exact hχ1ne (by
      have h2 : χ₁ ^ 3 = χ₁ ^ 2 * χ₁ := by rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ]
      rw [h2, hsq, one_mul] at hcon
      exact hcon)
  have hS3 : SigmaP3L q (Real.log (q : ℝ)) (χ₁ ^ 3)
      (σ + ((3 * ρ₁.im : ℝ) : ℂ) * Complex.I) a (lamOf q ρ₁)
      ≤ 0 + al * (1 / 6 + e) := by
    have hsim : |(σ + ((3 * ρ₁.im : ℝ) : ℂ) * Complex.I).im| ≤ 3 * H := by
      rw [him_of (3 * ρ₁.im), abs_mul, show |(3 : ℝ)| = 3 by norm_num]
      linarith [hγ, hH1]
    have h1 := hpb q hqb (χ₁ ^ 3) (fun hcon => hχ3ne hcon) hlam0 hlamM hHlog _
      (hre_of (3 * ρ₁.im)) hsim
    have h2 : (0 : ℝ) ≤ P3NearSumL q (Real.log (q : ℝ)) (χ₁ ^ 3)
        (σ + ((3 * ρ₁.im : ℝ) : ℂ) * Complex.I) a (lamOf q ρ₁) δ :=
      RectRepNearSum χ₁ (χ₁ ^ 3) ρ₁ hq2 hmin hHW (fun hcon => hχ3ne hcon) hlam0 ha hδ0 hδ1
        (hre_of (3 * ρ₁.im)) hsim
    linarith [h1, h2]
  -- ## the double zero at `σ + iγ` gives `2 P₃(1) ≤ W1`
  have hW1ge : (2 : ℝ) * P3R 1 ≤ W1 := by
    have h := Work.ZeroFreeTables.Rep9.nearSumDoubleH (q := q) χ₁ ρ₁ hq2 hmin hW hmult
      ha hδ0 hδ1 hδlam
    have hs : ((((1 + a / Real.log (q : ℝ) : ℝ)) : ℂ) + ((ρ₁.im : ℝ) : ℂ) * Complex.I)
        = σ + ((ρ₁.im : ℝ) : ℂ) * Complex.I := by rw [hσ]
    rw [hs] at h
    simpa only [hW1def] using h
  -- ## the diagonal combination
  have hcomb := RectRepComb χ₁ (a := a) (lam₁ := lamOf q ρ₁) (γ := ρ₁.im) (K := K) (H := H)
    hq2 ha hK hγ hlam0 hχ1ne
  have hcomb' : 0 ≤ (K ^ 2 + K + 1 / 2) * SigmaP3L q (Real.log (q : ℝ)) 1 σ a (lamOf q ρ₁)
      + (K ^ 2 + 2 * K + 3 / 4) * SigmaP3L q (Real.log (q : ℝ)) χ₁
          (σ + ((ρ₁.im : ℝ) : ℂ) * Complex.I) a (lamOf q ρ₁)
      + (K + 1 / 2) * SigmaP3L q (Real.log (q : ℝ)) (χ₁ ^ 2)
          (σ + ((2 * ρ₁.im : ℝ) : ℂ) * Complex.I) a (lamOf q ρ₁)
      + (1 / 4) * SigmaP3L q (Real.log (q : ℝ)) (χ₁ ^ 3)
          (σ + ((3 * ρ₁.im : ℝ) : ℂ) * Complex.I) a (lamOf q ρ₁) := by
    simpa only [hσ] using hcomb
  -- ## the pair `(K+½)Ψ₂ ≤ 2(K²+2K+¾)Φ₂`
  have hΦ2nn : 0 ≤ Φ2 := by
    have h := Work.ZeroFreeTables.P9.PhiG_nonneg (x := al) (y := al)
      (t := 2 * ρ₁.im * Real.log (q : ℝ)) halpos le_rfl
    simp only [Work.ZeroFreeTables.P9.PhiG] at h
    rw [hal, ofReal_add_local] at h
    simpa only [hΦ2def] using h
  have hpair : (K + 1 / 2) * Ψ2 ≤ 2 * (K ^ 2 + 2 * K + 3 / 4) * Φ2 := by
    have hKd := Work.ZeroFreeTables.Rep9.A2_mul_Kond_le hK
    have h0 := Work.ZeroFreeTables.Rep9.P3_div_le (x := al) (y := a)
      (t := 2 * ρ₁.im * Real.log (q : ℝ)) ha hale
    rw [hal, ofReal_add_local] at h0
    have hΨle : Ψ2 ≤ (al / a) ^ 3 * Φ2 := by
      simpa only [hΨ2def, hΦ2def] using h0
    have h1 : (K + 1 / 2) * ((al / a) ^ 3) ≤ (K + 1 / 2) * (Kond K + 1) :=
      mul_le_mul_of_nonneg_left (by simpa only [hal] using hcube) (by linarith)
    calc (K + 1 / 2) * Ψ2 ≤ (K + 1 / 2) * ((al / a) ^ 3 * Φ2) :=
          mul_le_mul_of_nonneg_left hΨle (by linarith)
      _ = ((K + 1 / 2) * (al / a) ^ 3) * Φ2 := by ring
      _ ≤ ((K + 1 / 2) * (Kond K + 1)) * Φ2 := mul_le_mul_of_nonneg_right h1 hΦ2nn
      _ ≤ (2 * (K ^ 2 + 2 * K + 3 / 4)) * Φ2 := mul_le_mul_of_nonneg_right hKd hΦ2nn
      _ = 2 * (K ^ 2 + 2 * K + 3 / 4) * Φ2 := by ring
  by_cases hnear : ‖(1 : ℂ) + ((ρ₁.im : ℝ) : ℂ) * Complex.I - (starRingEnd ℂ) ρ₁‖ ≤ δ
  · -- ## NEAR: the conjugate zero dominates the pole term
    have hnc : (2 : ℝ) * P3R 1 + 2 * Φ2 ≤ W1 := by
      have h := hnearC q hqc χ₁ ρ₁ hmin hHW hmult hsq him hδlam hnear
      have hs : ((((1 + a / Real.log (q : ℝ) : ℝ)) : ℂ) + ((ρ₁.im : ℝ) : ℂ) * Complex.I)
          = σ + ((ρ₁.im : ℝ) : ℂ) * Complex.I := by rw [hσ]
      rw [hs] at h
      simpa only [hW1def, hΦ2def] using h
    have hS1 : SigmaP3L q (Real.log (q : ℝ)) χ₁ (σ + ((ρ₁.im : ℝ) : ℂ) * Complex.I)
        a (lamOf q ρ₁) ≤ -(2 * P3R 1) - 2 * Φ2 + al * (1 / 6 + e) := by
      linarith only [hS1w, hnc]
    set CN : ℝ := (K ^ 2 + K + 1 / 2) * e0 + (K ^ 2 + 2 * K + 3 / 4) * (1 / 6 + e)
      + (K + 1 / 2) * e0 + (1 / 4) * (1 / 6 + e) with hCNdef
    have hD : 0 ≤ (K ^ 2 + K + 1 / 2) * P3R (al / a)
        - (2 * K ^ 2 + 4 * K + 3 / 2) * P3R 1 + al * CN := by
      have hA0 : (0 : ℝ) ≤ K ^ 2 + K + 1 / 2 := by positivity
      have hA1 : (0 : ℝ) ≤ K ^ 2 + 2 * K + 3 / 4 := by positivity
      have hA2 : (0 : ℝ) ≤ K + 1 / 2 := by linarith
      have hA3 : (0 : ℝ) ≤ 1 / 4 := by norm_num
      have i0 := mul_le_mul_of_nonneg_left hS0 hA0
      have i1 := mul_le_mul_of_nonneg_left hS1 hA1
      have i2 := mul_le_mul_of_nonneg_left hS2 hA2
      have i3 := mul_le_mul_of_nonneg_left hS3 hA3
      have hsum : (K ^ 2 + K + 1 / 2) * (P3R (al / a) + al * e0)
          + (K ^ 2 + 2 * K + 3 / 4) * (-(2 * P3R 1) - 2 * Φ2 + al * (1 / 6 + e))
          + (K + 1 / 2) * (Ψ2 + al * e0) + (1 / 4) * (0 + al * (1 / 6 + e))
          = (K ^ 2 + K + 1 / 2) * P3R (al / a) - (2 * K ^ 2 + 4 * K + 3 / 2) * P3R 1
            + al * CN + ((K + 1 / 2) * Ψ2 - 2 * (K ^ 2 + 2 * K + 3 / 4) * Φ2) := by
        rw [hCNdef]; ring
      have hlow : 0 ≤ (K ^ 2 + K + 1 / 2) * P3R (al / a) - (2 * K ^ 2 + 4 * K + 3 / 2) * P3R 1
          + al * CN + ((K + 1 / 2) * Ψ2 - 2 * (K ^ 2 + 2 * K + 3 / 4) * Φ2) := by
        linarith only [hcomb', i0, i1, i2, i3, hsum.le, hsum.ge]
      linarith only [hlow, hpair]
    have hcN : CN * (48 * K) ≤ (12 * K + 1) * S := by
      have h := order2_budget hK he1
      have hbud : ((K ^ 2 + K + 1 / 2) * (e / 2) + (K ^ 2 + 2 * K + 3 / 4) * (1 / 6 + e)
          + (K + 1 / 2) * (e / 2) + (1 / 4) * (1 / 6 + e)) * (48 * K)
          ≤ (12 * K + 1 / 2) * (K ^ 2 + 3 * K + 3 / 2) := by
        simpa only [hSdef] using h
      have hmid : (12 * K + 1 / 2) * (K ^ 2 + 3 * K + 3 / 2) ≤ (12 * K + 1) * S := by
        have h2 : (0 : ℝ) ≤ K ^ 2 + 3 * K + 3 / 2 := by positivity
        rw [hSdef]
        nlinarith only [h2]
      have hCNv : CN = (K ^ 2 + K + 1 / 2) * (e / 2) + (K ^ 2 + 2 * K + 3 / 4) * (1 / 6 + e)
          + (K + 1 / 2) * (e / 2) + (1 / 4) * (1 / 6 + e) := by
        rw [hCNdef, he0def]
      rw [hCNv]
      linarith only [hbud, hmid]
    exact Work.ZeroFreeTables.Rep9.ineq913_diag_of_derived_poly (a := a) (K := K) (C := CN)
      (ε := ε) (lam := lamOf q ρ₁) ha hK hε hlam0 (by simpa only [hal] using hcube)
      hcN (by simpa only [hal] using hD)
  · -- ## FAR: the pole term is small
    have hfar : Ψ2 ≤ e := by
      have h := hfarC q hqf χ₁ ρ₁ hlam0 hlamM him hnear
      simpa only [hΨ2def] using h
    have hS1 : SigmaP3L q (Real.log (q : ℝ)) χ₁ (σ + ((ρ₁.im : ℝ) : ℂ) * Complex.I)
        a (lamOf q ρ₁) ≤ -(2 * P3R 1) + al * (1 / 6 + e) := by
      linarith only [hS1w, hW1ge]
    have hS2' : SigmaP3L q (Real.log (q : ℝ)) (χ₁ ^ 2)
        (σ + ((2 * ρ₁.im : ℝ) : ℂ) * Complex.I) a (lamOf q ρ₁) ≤ e + al * e0 := by
      linarith only [hS2, hfar]
    set ex : ℝ := (K + 1 / 2) * e / (a * S) with hexdef
    have hexb : (K + 1 / 2) * e ≤ al * (ex * S) := by
      have h1 : al * (ex * S) = al * (K + 1 / 2) * e / a := by
        rw [hexdef]
        first | (field_simp; ring) | (field_simp)
      have h2 : a * (K + 1 / 2) * e / a ≤ al * (K + 1 / 2) * e / a := by
        apply div_le_div_of_nonneg_right _ ha.le
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hale (by linarith)) hepos.le
      have h3 : a * (K + 1 / 2) * e / a = (K + 1 / 2) * e := by
        first | (field_simp; ring) | (field_simp)
      linarith only [h1.le, h1.ge, h2, h3.le, h3.ge]
    set CN : ℝ := (K ^ 2 + K + 1 / 2) * e0 + (K ^ 2 + 2 * K + 3 / 4) * (1 / 6 + e)
      + (K + 1 / 2) * e0 + (1 / 4) * (1 / 6 + e) with hCNdef
    have hD : 0 ≤ (K ^ 2 + K + 1 / 2) * P3R (al / a)
        - (2 * K ^ 2 + 4 * K + 3 / 2) * P3R 1 + al * (CN + ex * S) := by
      have hA0 : (0 : ℝ) ≤ K ^ 2 + K + 1 / 2 := by positivity
      have hA1 : (0 : ℝ) ≤ K ^ 2 + 2 * K + 3 / 4 := by positivity
      have hA2 : (0 : ℝ) ≤ K + 1 / 2 := by linarith
      have hA3 : (0 : ℝ) ≤ 1 / 4 := by norm_num
      have i0 := mul_le_mul_of_nonneg_left hS0 hA0
      have i1 := mul_le_mul_of_nonneg_left hS1 hA1
      have i2 := mul_le_mul_of_nonneg_left hS2' hA2
      have i3 := mul_le_mul_of_nonneg_left hS3 hA3
      have hsum : (K ^ 2 + K + 1 / 2) * (P3R (al / a) + al * e0)
          + (K ^ 2 + 2 * K + 3 / 4) * (-(2 * P3R 1) + al * (1 / 6 + e))
          + (K + 1 / 2) * (e + al * e0) + (1 / 4) * (0 + al * (1 / 6 + e))
          = (K ^ 2 + K + 1 / 2) * P3R (al / a) - (2 * K ^ 2 + 4 * K + 3 / 2) * P3R 1
            + al * CN + (K + 1 / 2) * e := by
        rw [hCNdef]; ring
      have hlow : 0 ≤ (K ^ 2 + K + 1 / 2) * P3R (al / a) - (2 * K ^ 2 + 4 * K + 3 / 2) * P3R 1
          + al * CN + (K + 1 / 2) * e := by
        linarith only [hcomb', i0, i1, i2, i3, hsum.le, hsum.ge]
      have hsum2 : al * (CN + ex * S) = al * CN + al * (ex * S) := by ring
      rw [hsum2]
      linarith only [hlow, hexb]
    have hcN : (CN + ex * S) * (48 * K) ≤ (12 * K + 1) * S := by
      have h := order2_budget hK he1
      have hbud : ((K ^ 2 + K + 1 / 2) * (e / 2) + (K ^ 2 + 2 * K + 3 / 4) * (1 / 6 + e)
          + (K + 1 / 2) * (e / 2) + (1 / 4) * (1 / 6 + e)) * (48 * K)
          ≤ (12 * K + 1 / 2) * (K ^ 2 + 3 * K + 3 / 2) := by
        simpa only [hSdef] using h
      have hmid : (12 * K + 1 / 2) * (K ^ 2 + 3 * K + 3 / 2) + S / 2 ≤ (12 * K + 1) * S := by
        have h2 : (0 : ℝ) ≤ K ^ 2 + 3 * K + 3 / 2 := by positivity
        rw [hSdef]
        nlinarith only [h2, hK]
      have hex : 48 * K * (ex * S) ≤ S / 2 := by
        rw [hexdef]
        exact order2_budget_ex ha hK hSpos he2
      have hCNv : CN = (K ^ 2 + K + 1 / 2) * (e / 2) + (K ^ 2 + 2 * K + 3 / 4) * (1 / 6 + e)
          + (K + 1 / 2) * (e / 2) + (1 / 4) * (1 / 6 + e) := by
        rw [hCNdef, he0def]
      rw [show (CN + ex * S) * (48 * K) = CN * (48 * K) + 48 * K * (ex * S) by ring, hCNv]
      linarith only [hbud, hmid, hex]
    exact Work.ZeroFreeTables.Rep9.ineq913_diag_of_derived_poly (a := a) (K := K)
      (C := CN + ex * S) (ε := ε) (lam := lamOf q ρ₁) ha hK hε hlam0
      (by simpa only [hal] using hcube) hcN (by simpa only [hal] using hD)

/-! ## The order-3 case (`χ₁³ = 1`, `χ₁² ≠ 1`) -/

/-- **HB Lemma 9.1 at a repeated zero, order-3 case.** -/
theorem rectRepOrder3H {a K ε H W : ℝ} (ha : 0 < a) (hK : 0 < K) (hε : 0 < ε)
    (hH1 : 1 ≤ H) (hHW : 3 * H + 1 ≤ W) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      H ≤ Real.log (q : ℝ) → Work.ZeroFreeTables.IsMinWideAt H W χ₁ ρ₁ →
      2 ≤ Work.LinnikContract.zeroMult χ₁ ρ₁ → χ₁ ^ 2 ≠ 1 → χ₁ ^ 3 = 1 →
      Work.ZeroFreeTables.cond913 (Work.LinnikContract.lamOf q ρ₁)
        (Work.LinnikContract.lamOf q ρ₁) a K →
      Work.ZeroFreeTables.ineq913 (Work.LinnikContract.lamOf q ρ₁)
        (Work.LinnikContract.lamOf q ρ₁) a K ε := by
  set S : ℝ := K ^ 2 + 3 * K + 3 / 2 with hSdef
  have hSpos : 0 < S := by rw [hSdef]; positivity
  set e : ℝ := min (1 / (768 * K)) (a * S / (768 * K)) with hedef
  have hepos : 0 < e := by
    rw [hedef]; exact lt_min (by positivity) (by positivity)
  have he1 : e ≤ 1 / (768 * K) := min_le_left _ _ 
  have he2 : e ≤ a * S / (768 * K) := min_le_right _ _ 
  set e0 : ℝ := e / 2 with he0def
  have he0pos : 0 < e0 := by rw [he0def]; linarith
  set M : ℝ := a * (Kond K + 1) with hMdef
  have hMnn : 0 ≤ M := by
    rw [hMdef]
    exact mul_nonneg ha.le (by linarith [Work.ZeroFreeTables.Rep9.Kond_pos hK])
  obtain ⟨q0b, δ, hδ0, hδ1, hpb⟩ :=
    pointBoundWideLocal (a := a) (e := e) (M := M) (H := H) ha hepos hMnn hH1
  obtain ⟨q0p, hprinc⟩ :=
    RectRepPrincipal (a := a) (e := e0) (M := M) (H := H) ha he0pos hMnn hH1
  obtain ⟨q0x, hx⟩ := RectRepOrder3 (a := a) (δ := δ) (e := e) (M := M)
    ha hδ0 hδ1 hepos hMnn
  refine ⟨max (max (max q0b q0p) q0x)
      (max (Nat.ceil (Real.exp (max (M / δ) 10))) 5), ?_⟩
  intro q hq inst χ₁ ρ₁ hHlog hmin hmult hχ2 hχ3 hcond
  have hqb : q0b ≤ q := by omega
  have hqp : q0p ≤ q := by omega
  have hqx : q0x ≤ q := by omega
  have hq1 : 1 < q := by omega
  have hq2 : 2 ≤ q := by omega
  have hlogqpos : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast hq1)
  have hlogqne : Real.log (q : ℝ) ≠ 0 := ne_of_gt hlogqpos
  have hce : Nat.ceil (Real.exp (max (M / δ) 10)) ≤ q := by omega
  have hLnb : Real.exp (max (M / δ) 10) ≤ (q : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast hce)
  have hMδ : M / δ ≤ Real.log (q : ℝ) :=
    calc M / δ ≤ max (M / δ) 10 := le_max_left _ _
      _ = Real.log (Real.exp (max (M / δ) 10)) := (Real.log_exp _).symm
      _ ≤ Real.log (q : ℝ) := Real.log_le_log (Real.exp_pos _) hLnb
  have hMlt : M ≤ δ * Real.log (q : ℝ) := by
    have h' := hMδ
    rw [div_le_iff₀ hδ0] at h'
    linarith [h']
  -- ## facts about the pair
  have hlam0 : 0 ≤ lamOf q ρ₁ := IsMinWideAt.lam_nonneg hmin
  have hlamM : lamOf q ρ₁ ≤ M := by
    rw [hMdef]
    exact Work.ZeroFreeTables.Rep9.lam_le_of_cond913 ha hK hlam0 hcond
  have hδlam : lamOf q ρ₁ / Real.log (q : ℝ) ≤ δ := by
    rw [div_le_iff₀ hlogqpos]
    exact le_trans hlamM hMlt
  have hγ : |ρ₁.im| ≤ H := hmin.2.2.1
  have hχ1ne : χ₁ ≠ 1 := hmin.1
  have hcube : ((a + lamOf q ρ₁) / a) ^ 3 ≤ Kond K + 1 :=
    Work.ZeroFreeTables.Rep9.cond913_cube_le ha hlam0 hcond
  set al : ℝ := a + lamOf q ρ₁ with hal
  have halpos : 0 < al := by rw [hal]; linarith
  have hale : a ≤ al := by rw [hal]; linarith
  have hW : H + 2 ≤ W := by linarith [hH1, hHW]
  set σ : ℂ := ((1 + a / Real.log (q : ℝ) : ℝ) : ℂ) with hσ
  have hre_of : ∀ θ : ℝ, (σ + ((θ : ℝ) : ℂ) * Complex.I).re = 1 + a / Real.log (q : ℝ) := by
    intro θ
    rw [hσ, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  have him_of : ∀ θ : ℝ, (σ + ((θ : ℝ) : ℂ) * Complex.I).im = θ := by
    intro θ
    rw [hσ, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  have hσim : |σ.im| ≤ 3 * H := by
    have h : σ.im = 0 := by rw [hσ]; exact Complex.ofReal_im _
    rw [h, abs_zero]; linarith [hH1]
  have hσre : σ.re = 1 + a / Real.log (q : ℝ) := by
    rw [hσ]; exact Complex.ofReal_re _
  set W1 : ℝ := P3NearSumL q (Real.log (q : ℝ)) χ₁
    (σ + ((ρ₁.im : ℝ) : ℂ) * Complex.I) a (lamOf q ρ₁) δ with hW1def
  set W2 : ℝ := P3NearSumL q (Real.log (q : ℝ)) (χ₁ ^ 2)
    (σ + ((2 * ρ₁.im : ℝ) : ℂ) * Complex.I) a (lamOf q ρ₁) δ with hW2def
  set Φ2 : ℝ := (P3 ((↑a + ↑(lamOf q ρ₁)) / ((↑a + ↑(lamOf q ρ₁))
    + ((3 * ρ₁.im * Real.log (q : ℝ) : ℝ) : ℂ) * Complex.I))).re with hΦ2def
  set Φa : ℝ := (P3 ((↑a + ↑(lamOf q ρ₁)) / ((a : ℂ)
    + ((3 * ρ₁.im * Real.log (q : ℝ) : ℝ) : ℂ) * Complex.I))).re with hΦadef
  -- ## (0) the principal character at `σ`
  have hS0 : SigmaP3L q (Real.log (q : ℝ)) (1 : DirichletCharacter ℂ q) σ a (lamOf q ρ₁)
      ≤ P3R (al / a) + al * e0 := by
    have h := hprinc q hqp hlam0 hlamM hHlog σ hσre hσim
    have hz : (↑a + ↑(lamOf q ρ₁) : ℂ)
          / ((σ - 1) * ((Real.log (q : ℝ) : ℝ) : ℂ)) = ((al / a : ℝ) : ℂ) := by
      have hσ1 : σ - 1 = (((a / Real.log (q : ℝ) : ℝ)) : ℂ) := by
        have hcast : (((1 + a / Real.log (q : ℝ) : ℝ)) : ℂ) - 1
            = (((1 + a / Real.log (q : ℝ)) - 1 : ℝ) : ℂ) := by
          rw [← Complex.ofReal_one, ← Complex.ofReal_sub]
        rw [hσ, hcast]
        congr 1
        ring
      have hσ2 : (σ - 1) * ((Real.log (q : ℝ) : ℝ) : ℂ) = ((a : ℝ) : ℂ) := by
        rw [hσ1, ← Complex.ofReal_mul]
        congr 1
        exact div_mul_cancel₀ a hlogqne
      rw [hσ2, ← Complex.ofReal_add, ← Complex.ofReal_div, hal]
    have hP : (P3 ((↑a + ↑(lamOf q ρ₁)) / ((σ - 1) * ((Real.log (q : ℝ) : ℝ) : ℂ)))).re
        = P3R (al / a) := by
      rw [hz]; exact Work.ZeroFreeTables.Rep9.P3_ofReal_re (al / a)
    rw [hP] at h
    simpa only [hal] using h
  -- ## (1) `χ₁` at `σ + iγ`
  have hS1w : SigmaP3L q (Real.log (q : ℝ)) χ₁
      (σ + ((ρ₁.im : ℝ) : ℂ) * Complex.I) a (lamOf q ρ₁)
      ≤ -W1 + al * (1 / 6 + e) := by
    have hsim : |(σ + ((ρ₁.im : ℝ) : ℂ) * Complex.I).im| ≤ 3 * H := by
      rw [him_of ρ₁.im]; linarith [hγ, hH1]
    have h1 := hpb q hqb χ₁ hχ1ne hlam0 hlamM hHlog _ (hre_of ρ₁.im) hsim
    simpa only [hW1def, hal] using h1
  have hW1ge : (2 : ℝ) * P3R 1 ≤ W1 := by
    have h := Work.ZeroFreeTables.Rep9.nearSumDoubleH (q := q) χ₁ ρ₁ hq2 hmin hW hmult
      ha hδ0 hδ1 hδlam
    have hs : ((((1 + a / Real.log (q : ℝ) : ℝ)) : ℂ) + ((ρ₁.im : ℝ) : ℂ) * Complex.I)
        = σ + ((ρ₁.im : ℝ) : ℂ) * Complex.I := by rw [hσ]
    rw [hs] at h
    simpa only [hW1def] using h
  have hS1 : SigmaP3L q (Real.log (q : ℝ)) χ₁ (σ + ((ρ₁.im : ℝ) : ℂ) * Complex.I)
      a (lamOf q ρ₁) ≤ -(2 * P3R 1) + al * (1 / 6 + e) := by
    linarith only [hS1w, hW1ge]
  -- ## (2) `χ₁²` at `σ + 2iγ` (non-principal), near sum kept
  have hS2w : SigmaP3L q (Real.log (q : ℝ)) (χ₁ ^ 2)
      (σ + ((2 * ρ₁.im : ℝ) : ℂ) * Complex.I) a (lamOf q ρ₁)
      ≤ -W2 + al * (1 / 6 + e) := by
    have hsim : |(σ + ((2 * ρ₁.im : ℝ) : ℂ) * Complex.I).im| ≤ 3 * H := by
      rw [him_of (2 * ρ₁.im), abs_mul, show |(2 : ℝ)| = 2 by norm_num]
      linarith [hγ, hH1]
    have h1 := hpb q hqb (χ₁ ^ 2) (fun hcon => hχ2 hcon) hlam0 hlamM hHlog _
      (hre_of (2 * ρ₁.im)) hsim
    simpa only [hW2def, hal] using h1
  have hW2ge : (0 : ℝ) ≤ W2 := by
    have h := RectRepNearSum χ₁ (χ₁ ^ 2) ρ₁ hq2 hmin hHW (fun hcon => hχ2 hcon) hlam0 ha
      hδ0 hδ1 (s := σ + ((2 * ρ₁.im : ℝ) : ℂ) * Complex.I)
      (hre_of (2 * ρ₁.im)) (by
        rw [him_of (2 * ρ₁.im), abs_mul, show |(2 : ℝ)| = 2 by norm_num]
        linarith [hγ, hH1])
    simpa only [hW2def] using h
  -- ## (3) `χ₁³ = χ₀` at `σ + 3iγ` (principal): the pole term `Φa`
  have hS3 : SigmaP3L q (Real.log (q : ℝ)) (χ₁ ^ 3)
      (σ + ((3 * ρ₁.im : ℝ) : ℂ) * Complex.I) a (lamOf q ρ₁)
      ≤ Φa + al * e0 := by
    have hsim : |(σ + ((3 * ρ₁.im : ℝ) : ℂ) * Complex.I).im| ≤ 3 * H := by
      rw [him_of (3 * ρ₁.im), abs_mul, show |(3 : ℝ)| = 3 by norm_num]
      linarith [hγ, hH1]
    have h := hprinc q hqp hlam0 hlamM hHlog _ (hre_of (3 * ρ₁.im)) hsim
    have hz : (↑a + ↑(lamOf q ρ₁) : ℂ)
          / (((σ + ((3 * ρ₁.im : ℝ) : ℂ) * Complex.I) - 1) * ((Real.log (q : ℝ) : ℝ) : ℂ))
        = (↑a + ↑(lamOf q ρ₁) : ℂ)
          / ((a : ℂ) + ((3 * ρ₁.im * Real.log (q : ℝ) : ℝ) : ℂ) * Complex.I) := by
      have h1 : (σ + ((3 * ρ₁.im : ℝ) : ℂ) * Complex.I) - 1
          = (((a / Real.log (q : ℝ) : ℝ)) : ℂ) + ((3 * ρ₁.im : ℝ) : ℂ) * Complex.I := by
        rw [hσ]
        push_cast
        ring_nf
      have h2 : ((((a / Real.log (q : ℝ) : ℝ)) : ℂ) + ((3 * ρ₁.im : ℝ) : ℂ) * Complex.I)
            * ((Real.log (q : ℝ) : ℝ) : ℂ)
          = ((a : ℂ) + ((3 * ρ₁.im * Real.log (q : ℝ) : ℝ) : ℂ) * Complex.I) := by
        rw [add_mul, ← Complex.ofReal_mul, div_mul_cancel₀ a hlogqne]
        rw [show ((3 * ρ₁.im : ℝ) : ℂ) * Complex.I * ((Real.log (q : ℝ) : ℝ) : ℂ)
            = (((3 * ρ₁.im * Real.log (q : ℝ) : ℝ)) : ℂ) * Complex.I by push_cast; ring]
      rw [h1, h2]
    have hP : (P3 ((↑a + ↑(lamOf q ρ₁)) / (((σ + ((3 * ρ₁.im : ℝ) : ℂ) * Complex.I) - 1)
        * ((Real.log (q : ℝ) : ℝ) : ℂ)))).re = Φa := by
      rw [hz, hΦadef]
    rw [hP] at h
    simpa only [hal, hχ3] using h
  -- ## the combination and the pair `(1/4)Φa ≤ 2(K+½)Φ2`
  have hcomb := RectRepComb χ₁ (a := a) (lam₁ := lamOf q ρ₁) (γ := ρ₁.im) (K := K) (H := H)
    hq2 ha hK hγ hlam0 hχ1ne
  have hcomb' : 0 ≤ (K ^ 2 + K + 1 / 2) * SigmaP3L q (Real.log (q : ℝ)) 1 σ a (lamOf q ρ₁)
      + (K ^ 2 + 2 * K + 3 / 4) * SigmaP3L q (Real.log (q : ℝ)) χ₁
          (σ + ((ρ₁.im : ℝ) : ℂ) * Complex.I) a (lamOf q ρ₁)
      + (K + 1 / 2) * SigmaP3L q (Real.log (q : ℝ)) (χ₁ ^ 2)
          (σ + ((2 * ρ₁.im : ℝ) : ℂ) * Complex.I) a (lamOf q ρ₁)
      + (1 / 4) * SigmaP3L q (Real.log (q : ℝ)) (χ₁ ^ 3)
          (σ + ((3 * ρ₁.im : ℝ) : ℂ) * Complex.I) a (lamOf q ρ₁) := by
    simpa only [hσ] using hcomb
  have hΦ2nn : 0 ≤ Φ2 := by
    have h := Work.ZeroFreeTables.P9.PhiG_nonneg (x := al) (y := al)
      (t := 3 * ρ₁.im * Real.log (q : ℝ)) halpos le_rfl
    simp only [Work.ZeroFreeTables.P9.PhiG] at h
    rw [hal, ofReal_add_local] at h
    simpa only [hΦ2def] using h
  have hpair : (1 / 4) * Φa ≤ 2 * (K + 1 / 2) * Φ2 := by
    have h0 := Work.ZeroFreeTables.Rep9.P3_div_le (x := al) (y := a)
      (t := 3 * ρ₁.im * Real.log (q : ℝ)) ha hale
    rw [hal, ofReal_add_local] at h0
    have hΦle : Φa ≤ (al / a) ^ 3 * Φ2 := by
      simpa only [hΦadef, hΦ2def] using h0
    have hKd : Kond K ≤ 4 * K := min_le_right _ _
    have h1 : (1 / 4 : ℝ) * ((al / a) ^ 3) ≤ 2 * (K + 1 / 2) := by
      have h2 : (1 / 4 : ℝ) * (Kond K + 1) ≤ 2 * (K + 1 / 2) := by linarith only [hKd, hK]
      have h3 : (1 / 4 : ℝ) * ((al / a) ^ 3) ≤ (1 / 4 : ℝ) * (Kond K + 1) := by
        have := (by simpa only [hal] using hcube : ((al / a) ^ 3) ≤ Kond K + 1)
        linarith only [this]
      linarith only [h2, h3]
    calc (1 / 4) * Φa ≤ (1 / 4) * ((al / a) ^ 3 * Φ2) :=
          mul_le_mul_of_nonneg_left hΦle (by norm_num)
      _ = ((1 / 4) * (al / a) ^ 3) * Φ2 := by ring
      _ ≤ (2 * (K + 1 / 2)) * Φ2 := mul_le_mul_of_nonneg_right h1 hΦ2nn
      _ = 2 * (K + 1 / 2) * Φ2 := by ring
  by_cases hnear : ‖(1 : ℂ) + (((2 * ρ₁.im : ℝ)) : ℂ) * Complex.I - (starRingEnd ℂ) ρ₁‖ ≤ δ
  · -- ## NEAR: the conjugate zero `ρ̄₁` of `χ₁²` dominates the pole term
    have hnc : (2 : ℝ) * Φ2 ≤ W2 := by
      have h := (hx q hqx χ₁ ρ₁ hmin hHW hmult hχ3 hδlam hlamM).1 hnear
      have hs : ((((1 + a / Real.log (q : ℝ) : ℝ)) : ℂ) + (((2 * ρ₁.im : ℝ)) : ℂ) * Complex.I)
          = σ + ((2 * ρ₁.im : ℝ) : ℂ) * Complex.I := by rw [hσ]
      rw [hs] at h
      simpa only [hW2def, hΦ2def] using h
    have hS2 : SigmaP3L q (Real.log (q : ℝ)) (χ₁ ^ 2)
        (σ + ((2 * ρ₁.im : ℝ) : ℂ) * Complex.I) a (lamOf q ρ₁)
        ≤ -(2 * Φ2) + al * (1 / 6 + e) := by
      linarith only [hS2w, hnc]
    set CN : ℝ := (K ^ 2 + K + 1 / 2) * e0 + (K ^ 2 + 2 * K + 3 / 4) * (1 / 6 + e)
      + (K + 1 / 2) * (1 / 6 + e) + (1 / 4) * e0 with hCNdef
    have hD : 0 ≤ (K ^ 2 + K + 1 / 2) * P3R (al / a)
        - (2 * K ^ 2 + 4 * K + 3 / 2) * P3R 1 + al * CN := by
      have hA0 : (0 : ℝ) ≤ K ^ 2 + K + 1 / 2 := by positivity
      have hA1 : (0 : ℝ) ≤ K ^ 2 + 2 * K + 3 / 4 := by positivity
      have hA2 : (0 : ℝ) ≤ K + 1 / 2 := by linarith
      have hA3 : (0 : ℝ) ≤ 1 / 4 := by norm_num
      have i0 := mul_le_mul_of_nonneg_left hS0 hA0
      have i1 := mul_le_mul_of_nonneg_left hS1 hA1
      have i2 := mul_le_mul_of_nonneg_left hS2 hA2
      have i3 := mul_le_mul_of_nonneg_left hS3 hA3
      have hsum : (K ^ 2 + K + 1 / 2) * (P3R (al / a) + al * e0)
          + (K ^ 2 + 2 * K + 3 / 4) * (-(2 * P3R 1) + al * (1 / 6 + e))
          + (K + 1 / 2) * (-(2 * Φ2) + al * (1 / 6 + e)) + (1 / 4) * (Φa + al * e0)
          = (K ^ 2 + K + 1 / 2) * P3R (al / a) - (2 * K ^ 2 + 4 * K + 3 / 2) * P3R 1
            + al * CN + ((1 / 4) * Φa - 2 * (K + 1 / 2) * Φ2) := by
        rw [hCNdef]; ring
      have hlow : 0 ≤ (K ^ 2 + K + 1 / 2) * P3R (al / a) - (2 * K ^ 2 + 4 * K + 3 / 2) * P3R 1
          + al * CN + ((1 / 4) * Φa - 2 * (K + 1 / 2) * Φ2) := by
        linarith only [hcomb', i0, i1, i2, i3, hsum.le, hsum.ge]
      linarith only [hlow, hpair]
    have hcN : CN * (48 * K) ≤ (12 * K + 1) * S := by
      have h := order3_budget hK he1
      have hbud : ((K ^ 2 + K + 1 / 2) * (e / 2) + (K ^ 2 + 2 * K + 3 / 4) * (1 / 6 + e)
          + (K + 1 / 2) * (1 / 6 + e) + (1 / 4) * (e / 2)) * (48 * K)
          ≤ (12 * K + 63 / 64) * (K ^ 2 + 3 * K + 3 / 2) := by
        simpa only [hSdef] using h
      have hmid : (12 * K + 63 / 64) * (K ^ 2 + 3 * K + 3 / 2) ≤ (12 * K + 1) * S := by
        have h2 : (0 : ℝ) ≤ K ^ 2 + 3 * K + 3 / 2 := by positivity
        rw [hSdef]
        nlinarith only [h2]
      have hCNv : CN = (K ^ 2 + K + 1 / 2) * (e / 2) + (K ^ 2 + 2 * K + 3 / 4) * (1 / 6 + e)
          + (K + 1 / 2) * (1 / 6 + e) + (1 / 4) * (e / 2) := by
        rw [hCNdef, he0def]
      rw [hCNv]
      linarith only [hbud, hmid]
    exact Work.ZeroFreeTables.Rep9.ineq913_diag_of_derived_poly (a := a) (K := K) (C := CN)
      (ε := ε) (lam := lamOf q ρ₁) ha hK hε hlam0 (by simpa only [hal] using hcube)
      hcN (by simpa only [hal] using hD)
  · -- ## FAR: the pole term is small
    have hfar : Φa ≤ e := (hx q hqx χ₁ ρ₁ hmin hHW hmult hχ3 hδlam hlamM).2 hnear
    have hS2' : SigmaP3L q (Real.log (q : ℝ)) (χ₁ ^ 2)
        (σ + ((2 * ρ₁.im : ℝ) : ℂ) * Complex.I) a (lamOf q ρ₁) ≤ 0 + al * (1 / 6 + e) := by
      linarith only [hS2w, hW2ge]
    set ex : ℝ := e / (4 * a * S) with hexdef
    have hexb : (1 / 4 : ℝ) * e ≤ al * (ex * S) := by
      have h1 : al * (ex * S) = al * e / (4 * a) := by
        rw [hexdef]
        first | (field_simp; ring) | (field_simp)
      have h2 : a * e / (4 * a) ≤ al * e / (4 * a) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_right hale hepos.le
      have h3 : a * e / (4 * a) = e / 4 := by
        first | (field_simp; ring) | (field_simp)
      linarith only [h1.le, h1.ge, h2, h3.le, h3.ge]
    set CN : ℝ := (K ^ 2 + K + 1 / 2) * e0 + (K ^ 2 + 2 * K + 3 / 4) * (1 / 6 + e)
      + (K + 1 / 2) * (1 / 6 + e) + (1 / 4) * e0 with hCNdef
    have hD : 0 ≤ (K ^ 2 + K + 1 / 2) * P3R (al / a)
        - (2 * K ^ 2 + 4 * K + 3 / 2) * P3R 1 + al * (CN + ex * S) := by
      have hA0 : (0 : ℝ) ≤ K ^ 2 + K + 1 / 2 := by positivity
      have hA1 : (0 : ℝ) ≤ K ^ 2 + 2 * K + 3 / 4 := by positivity
      have hA2 : (0 : ℝ) ≤ K + 1 / 2 := by linarith
      have hA3 : (0 : ℝ) ≤ 1 / 4 := by norm_num
      have i0 := mul_le_mul_of_nonneg_left hS0 hA0
      have i1 := mul_le_mul_of_nonneg_left hS1 hA1
      have i2 := mul_le_mul_of_nonneg_left hS2' hA2
      have i3 := mul_le_mul_of_nonneg_left hS3 hA3
      have hsum : (K ^ 2 + K + 1 / 2) * (P3R (al / a) + al * e0)
          + (K ^ 2 + 2 * K + 3 / 4) * (-(2 * P3R 1) + al * (1 / 6 + e))
          + (K + 1 / 2) * (0 + al * (1 / 6 + e)) + (1 / 4) * (Φa + al * e0)
          = (K ^ 2 + K + 1 / 2) * P3R (al / a) - (2 * K ^ 2 + 4 * K + 3 / 2) * P3R 1
            + al * CN + (1 / 4) * Φa := by
        rw [hCNdef]; ring
      have hlow : 0 ≤ (K ^ 2 + K + 1 / 2) * P3R (al / a) - (2 * K ^ 2 + 4 * K + 3 / 2) * P3R 1
          + al * CN + (1 / 4) * Φa := by
        linarith only [hcomb', i0, i1, i2, i3, hsum.le, hsum.ge]
      have hup : (1 / 4 : ℝ) * Φa ≤ (1 / 4) * e := by linarith only [hfar]
      have hsum2 : al * (CN + ex * S) = al * CN + al * (ex * S) := by ring
      rw [hsum2]
      linarith only [hlow, hup, hexb]
    have hcN : (CN + ex * S) * (48 * K) ≤ (12 * K + 1) * S := by
      have h := order3_budget hK he1
      have hbud : ((K ^ 2 + K + 1 / 2) * (e / 2) + (K ^ 2 + 2 * K + 3 / 4) * (1 / 6 + e)
          + (K + 1 / 2) * (1 / 6 + e) + (1 / 4) * (e / 2)) * (48 * K)
          ≤ (12 * K + 63 / 64) * (K ^ 2 + 3 * K + 3 / 2) := by
        simpa only [hSdef] using h
      have hmid : (12 * K + 63 / 64) * (K ^ 2 + 3 * K + 3 / 2) + S / 64 ≤ (12 * K + 1) * S := by
        have h2 : (0 : ℝ) ≤ K ^ 2 + 3 * K + 3 / 2 := by positivity
        rw [hSdef]
        nlinarith only [h2, hK]
      have hex : 48 * K * (ex * S) ≤ S / 64 := by
        rw [hexdef]
        exact order3_budget_ex ha hK hSpos he2
      have hCNv : CN = (K ^ 2 + K + 1 / 2) * (e / 2) + (K ^ 2 + 2 * K + 3 / 4) * (1 / 6 + e)
          + (K + 1 / 2) * (1 / 6 + e) + (1 / 4) * (e / 2) := by
        rw [hCNdef, he0def]
      rw [show (CN + ex * S) * (48 * K) = CN * (48 * K) + 48 * K * (ex * S) by ring, hCNv]
      linarith only [hbud, hmid, hex]
    exact Work.ZeroFreeTables.Rep9.ineq913_diag_of_derived_poly (a := a) (K := K)
      (C := CN + ex * S) (ε := ε) (lam := lamOf q ρ₁) ha hK hε hlam0
      (by simpa only [hal] using hcube) hcN (by simpa only [hal] using hD)

/-! ## The target -/

/-- **HB Lemma 9.1 at a multiple zero, at rectangle height `H`** (the statement as requested):
for `a, K, ε > 0`, `1 ≤ H` and `3H + 1 ≤ W` there is `q₀` such that for `q ≥ q₀`, a pair
`(χ₁, ρ₁)` with `H ≤ log q`, the wide minimality `IsMinWideAt H W χ₁ ρ₁`, not the real-real case
(`¬(χ₁² = 1 ∧ Im ρ₁ = 0)`), a multiple zero `2 ≤ zeroMult χ₁ ρ₁` and the side condition
`cond913 λ₁ λ₁ a K` satisfies HB's inequality `ineq913 λ₁ λ₁ a K ε`. -/
theorem HBLemma9_1_rep_engine_H3 : ∀ (a K ε : ℝ), 0 < a → 0 < K → 0 < ε →
    ∀ H W : ℝ, 1 ≤ H → 3 * H + 1 ≤ W →
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
      (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      H ≤ Real.log (q : ℝ) →
      Work.ZeroFreeTables.IsMinWideAt H W χ₁ ρ₁ →
      ¬ (χ₁ ^ 2 = 1 ∧ ρ₁.im = 0) →
      2 ≤ Work.LinnikContract.zeroMult χ₁ ρ₁ →
      Work.ZeroFreeTables.cond913 (Work.LinnikContract.lamOf q ρ₁)
        (Work.LinnikContract.lamOf q ρ₁) a K →
      Work.ZeroFreeTables.ineq913 (Work.LinnikContract.lamOf q ρ₁)
        (Work.LinnikContract.lamOf q ρ₁) a K ε := by
  intro a K ε ha hK hε H W hH1 hHW
  obtain ⟨q₁, hq₁⟩ := rectRepGenericLocal (a := a) (K := K) (ε := ε) (H := H) (W := W)
    ha hK hε hH1 hHW
  obtain ⟨q₂, hq₂⟩ := rectRepOrder2H (a := a) (K := K) (ε := ε) (H := H) (W := W)
    ha hK hε hH1 hHW
  obtain ⟨q₃, hq₃⟩ := rectRepOrder3H (a := a) (K := K) (ε := ε) (H := H) (W := W)
    ha hK hε hH1 hHW
  refine ⟨max (max q₁ q₂) q₃, ?_⟩
  intro q hq inst χ₁ ρ₁ hHlog hmin hnr hmult hcond
  have hle1 : q₁ ≤ q := by omega
  have hle2 : q₂ ≤ q := by omega
  have hle3 : q₃ ≤ q := by omega
  by_cases hχ2 : χ₁ ^ 2 = 1
  · have him : ρ₁.im ≠ 0 := by
      intro h0
      exact hnr ⟨hχ2, h0⟩
    exact hq₂ q hle2 χ₁ ρ₁ hHlog hmin hmult hχ2 him hcond
  · by_cases hχ3 : χ₁ ^ 3 = 1
    · exact hq₃ q hle3 χ₁ ρ₁ hHlog hmin hmult hχ2 hχ3 hcond
    · exact hq₁ q hle1 χ₁ ρ₁ hHlog hmin hmult hχ2 hχ3 hcond

end Work.ZeroFreeTables.OffAxis


