import ChallengeDeps
import Submission.Work.BoseFixB1.RegimeAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.corner_regime` — the corner case `μa³ ≤ (1/100)^{969/166}`

At FS's parameter block `paramsAt μ A = fsParams (μA³)` the box side is the
monomial `ℓ = sideAt μ A = A·t^{−163/323}` in the diluteness `t = μA³`
(`Work.BoseBox.sideAt_eq_rpow`, `Work.BoseFixB1.sideAt_eq_fsXp`), and the mean
interparticle spacing is `μ^{-1/3} = A·t^{−1/3}` (`Work.BoseFixB1.mu_inv_third_eq`).
The scattering length `A = a v` *cancels* in both ratios, which is what makes the
statements below sharp at the explicit threshold `(1/100)^{969/166}`:

    ℓ / μ^{-1/3}      = t^{−166/969}   ≥ 100  ⟺  t ≤ (1/100)^{969/166},
    ℓ·d / μ^{-1/3}    = t^{−148/969}   ≥ 1    ⟺  t ≤ 1

(`ℓ·d` is the small-box side of App. `SmallBoxes`, `d = t^{6/323}`).  So on the
corner regime `μa³ ≤ (1/100)^{969/166}` — the *smallest* of the diluteness
thresholds used by the `B1` node, `(1/100)^{969/166} ≈ 10^{-11.7}` — the box side
dominates both one hundred times the interparticle spacing and the small-box side
`dℓ` at least once.  This is the elementary input that excludes the degenerate
corner of `NodeB1B` when only the sharpest diluteness bound is available.

Everything here is pure monomial bookkeeping in `fsXp t c = t^{c/323}`.
-/

noncomputable section
open scoped Real Topology BigOperators

namespace Work.BoseFixB1

open Work.BoseBox

/-! ## 1. The two monomial comparisons at diluteness `t` -/

/-- `t^{−1/3} ≤ t^{−163/323}/100` for `t ≤ (1/100)^{969/166}`: the box-side factor
`t^{−163/323}` dominates one hundred interparticle spacings `t^{−1/3}` as soon as
the diluteness is below `(1/100)^{969/166}` (the ratio is `t^{−166/969}`). -/
lemma fsXp_corner_hundred {t : ℝ} (ht0 : 0 < t)
    (ht : t ≤ ((1 : ℝ) / 100) ^ ((969 : ℝ) / 166)) :
    fsXp t (-(323 / 3)) ≤ fsXp t (-163) / 100 := by
  -- `100 ≤ t^{-166/969}`
  have h100 : (100 : ℝ) ≤ t ^ (-(166 / 969) : ℝ) := by
    have hle : t ^ (166 / 969 : ℝ) ≤ (1 : ℝ) / 100 := by
      calc t ^ (166 / 969 : ℝ)
          ≤ (((1 : ℝ) / 100) ^ ((969 : ℝ) / 166)) ^ (166 / 969 : ℝ) :=
            Real.rpow_le_rpow ht0.le ht (by norm_num)
        _ = ((1 : ℝ) / 100) ^ (((969 : ℝ) / 166) * (166 / 969)) :=
            (Real.rpow_mul (by norm_num) _ _).symm
        _ = (1 : ℝ) / 100 := by
            rw [show ((969 : ℝ) / 166) * (166 / 969) = 1 by norm_num, Real.rpow_one]
    have hp : (0 : ℝ) < t ^ (166 / 969 : ℝ) := Real.rpow_pos_of_pos ht0 _
    have h3 : ((1 : ℝ) / 100)⁻¹ ≤ (t ^ (166 / 969 : ℝ))⁻¹ :=
      (inv_le_inv₀ (by norm_num : (0 : ℝ) < 1 / 100) hp).mpr hle
    rw [Real.rpow_neg ht0.le]
    simpa using h3
  -- `t^{−163/323} = t^{−1/3}·t^{−166/969}`
  have hfac : fsXp t (-163) = fsXp t (-(323 / 3)) * fsXp t (-(166 / 3)) := by
    rw [fsXp_mul ht0]
    norm_num
  have hval : fsXp t (-(166 / 3)) = t ^ (-(166 / 969) : ℝ) := by
    rw [fsXp]
    norm_num
  rw [hfac, hval, le_div_iff₀ (by norm_num : (0 : ℝ) < 100),
    mul_le_mul_iff_right₀ (show (0 : ℝ) < fsXp t (-(323 / 3)) from fsXp_pos ht0)]
  exact h100

/-- `t^{−1/3} ≤ t^{−163/323}·t^{6/323} = t^{−157/323}` for `t ≤ 1`: the small-box
side `dℓ` is at least one interparticle spacing (here `d = fsXp t 6 = t^{6/323}`). -/
lemma fsXp_corner_d {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    fsXp t (-(323 / 3)) ≤ fsXp t (-163) * fsXp t 6 := by
  rw [fsXp_mul ht0]
  exact fsXp_le_fsXp ht0 ht1 (by norm_num)

/-! ## 2. The two conjuncts at the parameters `paramsAt μ A` -/

/-- **The box side dominates `100·μ^{-1/3}`** in the corner regime. -/
lemma sideAt_div_hundred {A μ : ℝ} (hA : 0 < A) (hμ : 0 < μ)
    (ht : μ * A ^ 3 ≤ ((1 : ℝ) / 100) ^ ((969 : ℝ) / 166)) :
    μ ^ (-(1 / 3) : ℝ) ≤ sideAt μ A / 100 := by
  have ht0 : (0 : ℝ) < μ * A ^ 3 := by positivity
  rw [mu_inv_third_eq hA hμ, sideAt_eq_fsXp hA hμ]
  calc A * fsXp (μ * A ^ 3) (-(323 / 3))
      ≤ A * (fsXp (μ * A ^ 3) (-163) / 100) :=
        mul_le_mul_of_nonneg_left (fsXp_corner_hundred ht0 ht) hA.le
    _ = A * fsXp (μ * A ^ 3) (-163) / 100 := by ring

/-- **The small-box side `dℓ` dominates `μ^{-1/3}`** in the corner regime. -/
lemma sideAt_mul_d_ge {A μ : ℝ} (hA : 0 < A) (hμ : 0 < μ)
    (ht1 : μ * A ^ 3 ≤ 1) :
    μ ^ (-(1 / 3) : ℝ) ≤ sideAt μ A * (paramsAt μ A).d := by
  have ht0 : (0 : ℝ) < μ * A ^ 3 := by positivity
  rw [mu_inv_third_eq hA hμ, sideAt_eq_fsXp hA hμ, d_eq_fsXp]
  calc A * fsXp (μ * A ^ 3) (-(323 / 3))
      ≤ A * (fsXp (μ * A ^ 3) (-163) * fsXp (μ * A ^ 3) 6) :=
        mul_le_mul_of_nonneg_left (fsXp_corner_d ht0 ht1) hA.le
    _ = A * fsXp (μ * A ^ 3) (-163) * fsXp (μ * A ^ 3) 6 := by ring

/-! ## 3. The requested lemma -/

theorem corner_regime {v : EuclideanSpace ℝ (Fin 3) → ℝ} (hav : 0 < _root_.BoseGases.a v) {μ : ℝ} (hμ : 0 < μ)
    {ε₀' : ℝ} (hε : ε₀' ≤ ((1 : ℝ) / 100) ^ ((969 : ℝ) / 166))
    (ht : μ * (_root_.BoseGases.a v) ^ 3 ≤ ε₀') :
    (0 < μ ^ (-(1 / 3 : ℝ))) ∧
      (μ ^ (-(1 / 3 : ℝ)) ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v) / 100) ∧
      (μ ^ (-(1 / 3 : ℝ)) ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
        * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) := by
  have htle : μ * (_root_.BoseGases.a v) ^ 3 ≤ ((1 : ℝ) / 100) ^ ((969 : ℝ) / 166) :=
    le_trans ht hε
  have ht1 : μ * (_root_.BoseGases.a v) ^ 3 ≤ 1 :=
    le_trans htle
      (Real.rpow_le_one (by norm_num : (0 : ℝ) ≤ 1 / 100) (by norm_num) (by norm_num))
  exact ⟨Real.rpow_pos_of_pos hμ _, sideAt_div_hundred hav hμ htle,
    sideAt_mul_d_ge hav hμ ht1⟩

end Work.BoseFixB1
