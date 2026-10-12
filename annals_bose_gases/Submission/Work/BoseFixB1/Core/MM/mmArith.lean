import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1.Core.MM.mmExistsPowLe
import Submission.Work.BoseFixB1.Core.MM.mmGeomBoundPow
import Submission.Work.BoseFixB1.Core.MM.mmIneq2OfCoreB
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.Core.MM.mmArith` — the mean-mismatch arithmetic

For a fixed interaction `v` with `a v > 0` and fixed nonnegative constants
`Cq, Ce, Cm`, both mean-mismatch error terms are dominated by the (tiny)
Neumann gap term `bValue/(16 ℓ²)` once the diluteness `t = μ (a v)³` is small
enough:

```
Cq ℓ⁻² · Cm G³ (ℓd)⁻³                       ≤ bValue/(16 ℓ²)
2 √(Cq ℓ⁻²) · √(Cm G³ (ℓd)⁻³ (2π)³ Ce)      ≤ bValue/(16 ℓ²)
```

with `ℓ = sideAt μ (a v)` the FS box side, `d = (paramsAt μ (a v)).d` and
`G = 1 + (ℓd)⁻¹ + |log d|`.

## The mathematics

At the diluteness `t = μ A³ ∈ (0,1]` (`A = a v`) the parameters are the closed
monomials

`ℓ = A t^{-163/323}` (`Work.BoseBox.sideAt_eq_rpow`),
`d = t^{6/323}` (`Work.BoseFixB1.d_eq_fsXp`),
`ℓd = A t^{-157/323}` (`Work.BoseFixB1.d_mul_sideAt_eq`),

so `G ≤ (7 + A⁻¹) t^{-1/323}`: the three pieces are `1 ≤ t^{-1/323}`,
`A⁻¹t^{157/323} ≤ A⁻¹t^{-1/323}` (as `t ≤ 1`), and
`|log d| = (6/323)|log t| ≤ 6 t^{-1/323}`, the last from the elementary bound
`log(1/x) ≤ (1/x)^ε/ε` (`Real.log_le_rpow_div`) at `ε = 1/323`, i.e.
`|log t| ≤ 323 t^{-1/323}`.  Cubing and multiplying by
`(ℓd)⁻³ = A⁻³t^{471/323}` gives

`G³(ℓd)⁻³ ≤ A⁻³ (7+A⁻¹)³ t^{468/323}`   (`mmGeomBoundPow`),

and one further factor `ℓ² = A²t^{-326/323}` gives

`ℓ²G³(ℓd)⁻³ ≤ A⁻¹ (7+A⁻¹)³ t^{142/323}`.

Both right-hand sides are of the form `K t^p` with `p > 0` (the exponents
`468/323`, `142/323` are *positive*: the logarithmic growth of `|log t|` is
more than paid for by the polynomial smallness of `(ℓd)⁻³`), so
`mmExistsPowLe` (applied twice, `K` a product of the fixed constants and
`A^{±1}`) yields thresholds `x₁, x₂` with `K t^p ≤ 1` for `t ≤ x_i`.  The two
thresholds and the cut-off `1` combine into `ε₀`.

The passage from these "core" bounds to the two displayed inequalities is pure
algebra: `ineq1Aux` below clears the common factor `ℓ⁻²` (both sides carry it,
so the statement is `256 Cq Cm G³(ℓd)⁻³ ≤ 1`, and `bValue/16 = 1/256`), while
`mmIneq2OfCoreB` distributes the square roots
(`√(Cq ℓ⁻²) = √Cq · ℓ⁻¹`, `√(Cm G³(ℓd)⁻³(2π)³Ce)`) and reduces the claim, by
squaring, to exactly the hypothesis `262144 (2π)³ Ce Cq Cm ℓ²G³(ℓd)⁻³ ≤ 1`
(the constant is `262144 = 4·256²`).

`Cq, Ce, Cm` are whatever finite constants the (fixed) interaction and the
cut-off produce; the bound is uniform in them because `ε₀` may depend on them.
-/

namespace Work.BoseFixB1.Core.MM

open Work.BoseBox

set_option linter.unusedVariables false

/-! ## The first inequality from its core bound

Clearing the common factor `ℓ⁻²` (both sides carry it), the statement is
`256 Cq Cm G³(ℓd)⁻³ ≤ 1` times the nonnegative factor `ℓ⁻²/256`; note
`bValue = 1/16` and `16·16 = 256`.  (The accompanying square-root inequality is
`Work.BoseFixB1.Core.MM.mmIneq2OfCoreB`.) -/
private lemma ineq1Aux {A μ Cq Cm : ℝ} (hA : 0 < A) (hμ : 0 < μ)
    (hCq : 0 ≤ Cq) (hCm : 0 ≤ Cm)
    (hcore : 256 * Cq * Cm *
        (1 + ((sideAt μ A) * (paramsAt μ A).d)⁻¹
            + |Real.log ((paramsAt μ A).d)|) ^ 3
        * (((sideAt μ A) * (paramsAt μ A).d) ^ 3)⁻¹ ≤ 1) :
    Cq * ((sideAt μ A)⁻¹) ^ 2 *
        (Cm * (1 + ((sideAt μ A) * (paramsAt μ A).d)⁻¹
                + |Real.log ((paramsAt μ A).d)|) ^ 3
          * (((sideAt μ A) * (paramsAt μ A).d) ^ 3)⁻¹)
      ≤ bValue / (16 * (sideAt μ A) ^ 2) := by
  have hℓ : 0 < sideAt μ A := by
    rw [Work.BoseBox.sideAt_eq_rpow hA hμ]
    exact mul_pos hA (Real.rpow_pos_of_pos (by positivity) _)
  set G : ℝ := 1 + ((sideAt μ A) * (paramsAt μ A).d)⁻¹ + |Real.log ((paramsAt μ A).d)| with hG
  set S : ℝ := (((sideAt μ A) * (paramsAt μ A).d) ^ 3)⁻¹ with hS
  have hcore' : 256 * Cq * Cm * G ^ 3 * S ≤ 1 := hcore
  have hle : Cq * Cm * G ^ 3 * S ≤ 1 / 256 := by linarith
  have key : (Cq * Cm * G ^ 3 * S) * ((sideAt μ A) ^ 2)⁻¹
      ≤ (1 / 256) * ((sideAt μ A) ^ 2)⁻¹ :=
    mul_le_mul_of_nonneg_right hle (inv_nonneg.mpr (sq_nonneg _))
  calc Cq * ((sideAt μ A)⁻¹) ^ 2 * (Cm * G ^ 3 * S)
      = (Cq * Cm * G ^ 3 * S) * ((sideAt μ A) ^ 2)⁻¹ := by
        field_simp
    _ ≤ (1 / 256) * ((sideAt μ A) ^ 2)⁻¹ := key
    _ = bValue / (16 * (sideAt μ A) ^ 2) := by
        rw [bValue]; field_simp; norm_num

/-! ## The assembly -/

theorem mmArith {v : EuclideanSpace ℝ (Fin 3) → ℝ} (hav : 0 < _root_.BoseGases.a v)
    {Cq Ce Cm : ℝ} (hCq : 0 ≤ Cq) (hCe : 0 ≤ Ce) (hCm : 0 ≤ Cm) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, 0 < μ → μ * (_root_.BoseGases.a v) ^ 3 ≤ ε₀ →
      (Cq * ((Work.BoseBox.sideAt μ (_root_.BoseGases.a v))⁻¹) ^ 2 *
          (Cm * (1 + ((Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                          * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)⁻¹
                  + |Real.log ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)|) ^ 3
            * (((Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) ^ 3)⁻¹)
        ≤ Work.BoseBox.bValue / (16 * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 2))
      ∧ (2 * Real.sqrt (Cq * ((Work.BoseBox.sideAt μ (_root_.BoseGases.a v))⁻¹) ^ 2) *
          Real.sqrt (Cm * (1 + ((Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                          * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)⁻¹
                  + |Real.log ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)|) ^ 3
            * (((Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) ^ 3)⁻¹
            * (2 * Real.pi) ^ 3 * Ce)
        ≤ Work.BoseBox.bValue / (16 * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 2)) := by
  -- the two smallness thresholds `K₁ t^{468/323} ≤ 1` and `K₂ t^{142/323} ≤ 1`
  obtain ⟨x1, hx1pos, hx1⟩ :=
    mmExistsPowLe
      (K := 256 * Cq * Cm * (((_root_.BoseGases.a v) ^ 3)⁻¹ * (7 + (_root_.BoseGases.a v)⁻¹) ^ 3))
      (p := 468 / 323) (by positivity) (by norm_num)
  obtain ⟨x2, hx2pos, hx2⟩ :=
    mmExistsPowLe
      (K := 262144 * (2 * Real.pi) ^ 3 * Ce * Cq * Cm *
        ((_root_.BoseGases.a v)⁻¹ * (7 + (_root_.BoseGases.a v)⁻¹) ^ 3))
      (p := 142 / 323) (by positivity) (by norm_num)
  refine ⟨min 1 (min x1 x2), lt_min one_pos (lt_min hx1pos hx2pos), ?_⟩
  intro μ hμ ht
  set A : ℝ := _root_.BoseGases.a v with hAdef
  have hA : 0 < A := by rw [hAdef]; exact hav
  have ht1 : μ * A ^ 3 ≤ 1 := le_trans ht (min_le_left _ _)
  have htx1 : μ * A ^ 3 ≤ x1 := le_trans ht (le_trans (min_le_right _ _) (min_le_left _ _))
  have htx2 : μ * A ^ 3 ≤ x2 := le_trans ht (le_trans (min_le_right _ _) (min_le_right _ _))
  have ht0 : 0 < μ * A ^ 3 := by positivity
  -- the geometric bound at the `t^{468/323}` threshold, and the two smallness conditions
  have hG := mmGeomBoundPow hA hμ ht1
  have hK1 := hx1 (μ * A ^ 3) ht0 htx1
  have hK2 := hx2 (μ * A ^ 3) ht0 htx2
  -- `ℓ² = A² t^{-326/323}`
  have hℓsq : (sideAt μ A) ^ 2 = A ^ 2 * (μ * A ^ 3) ^ (-(326 / 323) : ℝ) := by
    rw [Work.BoseBox.sideAt_eq_rpow hA hμ, mul_pow]
    congr 1
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht0.le]
    norm_num
  have hAinv : A ^ 2 * (A ^ 3)⁻¹ = A⁻¹ := by
    rw [← inv_pow]; field_simp
  have hpos : (0:ℝ) ≤ (sideAt μ A) ^ 2 := sq_nonneg _
  -- the geometric bound multiplied by `ℓ²`, giving the `t^{142/323}` threshold
  have hG2 : (sideAt μ A) ^ 2 *
      (1 + ((sideAt μ A) * (paramsAt μ A).d)⁻¹ + |Real.log ((paramsAt μ A).d)|) ^ 3
      * (((sideAt μ A) * (paramsAt μ A).d) ^ 3)⁻¹
      ≤ A⁻¹ * (7 + A⁻¹) ^ 3 * (μ * A ^ 3) ^ (142 / 323 : ℝ) := by
    have h1 : ((1 + ((sideAt μ A) * (paramsAt μ A).d)⁻¹
          + |Real.log ((paramsAt μ A).d)|) ^ 3
        * (((sideAt μ A) * (paramsAt μ A).d) ^ 3)⁻¹) * (sideAt μ A) ^ 2
        ≤ ((A ^ 3)⁻¹ * (7 + A⁻¹) ^ 3 * (μ * A ^ 3) ^ (468 / 323 : ℝ)) * (sideAt μ A) ^ 2 :=
      mul_le_mul_of_nonneg_right hG hpos
    calc (sideAt μ A) ^ 2 *
          (1 + ((sideAt μ A) * (paramsAt μ A).d)⁻¹ + |Real.log ((paramsAt μ A).d)|) ^ 3
        * (((sideAt μ A) * (paramsAt μ A).d) ^ 3)⁻¹
        = ((1 + ((sideAt μ A) * (paramsAt μ A).d)⁻¹
              + |Real.log ((paramsAt μ A).d)|) ^ 3
            * (((sideAt μ A) * (paramsAt μ A).d) ^ 3)⁻¹) * (sideAt μ A) ^ 2 := by ring
      _ ≤ ((A ^ 3)⁻¹ * (7 + A⁻¹) ^ 3 * (μ * A ^ 3) ^ (468 / 323 : ℝ)) * (sideAt μ A) ^ 2 := h1
      _ = A⁻¹ * (7 + A⁻¹) ^ 3 * (μ * A ^ 3) ^ (142 / 323 : ℝ) := by
          rw [hℓsq]
          rw [show ((A ^ 3)⁻¹ * (7 + A⁻¹) ^ 3 * (μ * A ^ 3) ^ (468 / 323 : ℝ))
                * (A ^ 2 * (μ * A ^ 3) ^ (-(326 / 323) : ℝ))
              = (A ^ 2 * (A ^ 3)⁻¹) * (7 + A⁻¹) ^ 3
                * ((μ * A ^ 3) ^ (468 / 323 : ℝ) * (μ * A ^ 3) ^ (-(326 / 323) : ℝ)) by ring]
          rw [← Real.rpow_add ht0 (468 / 323) (-(326 / 323))]
          rw [show (468 / 323 : ℝ) + (-(326 / 323)) = 142 / 323 by norm_num]
          rw [hAinv]
  -- the two core bounds
  have hcore1 : 256 * Cq * Cm *
      (1 + ((sideAt μ A) * (paramsAt μ A).d)⁻¹ + |Real.log ((paramsAt μ A).d)|) ^ 3
      * (((sideAt μ A) * (paramsAt μ A).d) ^ 3)⁻¹ ≤ 1 := by
    have hc : (0:ℝ) ≤ 256 * Cq * Cm := by positivity
    calc 256 * Cq * Cm *
          (1 + ((sideAt μ A) * (paramsAt μ A).d)⁻¹ + |Real.log ((paramsAt μ A).d)|) ^ 3
        * (((sideAt μ A) * (paramsAt μ A).d) ^ 3)⁻¹
        = 256 * Cq * Cm *
          ((1 + ((sideAt μ A) * (paramsAt μ A).d)⁻¹
              + |Real.log ((paramsAt μ A).d)|) ^ 3
            * (((sideAt μ A) * (paramsAt μ A).d) ^ 3)⁻¹) := by ring
      _ ≤ 256 * Cq * Cm * ((A ^ 3)⁻¹ * (7 + A⁻¹) ^ 3 * (μ * A ^ 3) ^ (468 / 323 : ℝ)) :=
          mul_le_mul_of_nonneg_left hG hc
      _ = 256 * Cq * Cm * ((A ^ 3)⁻¹ * (7 + A⁻¹) ^ 3) * (μ * A ^ 3) ^ (468 / 323 : ℝ) := by ring
      _ ≤ 1 := hK1
  have hcore2 : 262144 * (2 * Real.pi) ^ 3 * Ce * Cq * Cm * (sideAt μ A) ^ 2 *
      (1 + ((sideAt μ A) * (paramsAt μ A).d)⁻¹ + |Real.log ((paramsAt μ A).d)|) ^ 3
      * (((sideAt μ A) * (paramsAt μ A).d) ^ 3)⁻¹ ≤ 1 := by
    have hc : (0:ℝ) ≤ 262144 * (2 * Real.pi) ^ 3 * Ce * Cq * Cm := by positivity
    calc 262144 * (2 * Real.pi) ^ 3 * Ce * Cq * Cm * (sideAt μ A) ^ 2 *
          (1 + ((sideAt μ A) * (paramsAt μ A).d)⁻¹ + |Real.log ((paramsAt μ A).d)|) ^ 3
        * (((sideAt μ A) * (paramsAt μ A).d) ^ 3)⁻¹
        = (262144 * (2 * Real.pi) ^ 3 * Ce * Cq * Cm) *
          ((sideAt μ A) ^ 2 *
            (1 + ((sideAt μ A) * (paramsAt μ A).d)⁻¹
                + |Real.log ((paramsAt μ A).d)|) ^ 3
            * (((sideAt μ A) * (paramsAt μ A).d) ^ 3)⁻¹) := by ring
      _ ≤ (262144 * (2 * Real.pi) ^ 3 * Ce * Cq * Cm) *
          (A⁻¹ * (7 + A⁻¹) ^ 3 * (μ * A ^ 3) ^ (142 / 323 : ℝ)) :=
          mul_le_mul_of_nonneg_left hG2 hc
      _ = 262144 * (2 * Real.pi) ^ 3 * Ce * Cq * Cm * (A⁻¹ * (7 + A⁻¹) ^ 3)
          * (μ * A ^ 3) ^ (142 / 323 : ℝ) := by ring
      _ ≤ 1 := hK2
  exact ⟨ineq1Aux hA hμ hCq hCm hcore1, mmIneq2OfCoreB hA hμ hCq hCe hCm hcore2⟩

end Work.BoseFixB1.Core.MM
