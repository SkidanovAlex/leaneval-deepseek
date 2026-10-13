import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.Construction.Defs
import Submission.Work.FTS.EpsEngine.Theta_Fstar_ops

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real

namespace Work.FTS.EpsEngine

/-- `(1/4)·min z 1 + 1/(1+z) ≤ 1` for `z > 0`: the arithmetic core of the `Rop`-slot bound.
In the regime `z ≤ 1` it reads `z/4 ≤ z/(1+z)`, i.e. `1 + z ≤ 4`, i.e. `z ≤ 3`; in the regime
`z ≥ 1` (`min z 1 = 1`) it reads `1/4 + 1/(1+z) ≤ 1`, i.e. `1 ≤ 3z`. -/
private lemma quarter_min_add_inv_le_one {z : ℝ} (hz : 0 < z) :
    (1 / 4 : ℝ) * min z 1 + 1 / (1 + z) ≤ 1 := by
  have h1z : (0 : ℝ) < 1 + z := by linarith
  have hkey : (1 / 4 : ℝ) * min z 1 ≤ z / (1 + z) := by
    rcases lt_or_ge z 1 with h | h
    · rw [min_eq_left (le_of_lt h), le_div_iff₀ h1z]
      nlinarith [hz, h]
    · rw [min_eq_right h, le_div_iff₀ h1z]
      nlinarith [hz, h]
  have h2 : z / (1 + z) + 1 / (1 + z) = 1 := by
    field_simp
    ring
  linarith [hkey, h2]

/-- The `Rop` slot of the `EpsDecay` clause of `EpsUniformMem`, in absolute value.  With the
decomposition `PhiTil α f (Φs + E f) = PhiTil α f (E f) + PhiTil α F_* Φs + Theta α F_*` (the
affineness of `PhiTil` in its second argument plus additivity of `Rop`, `Rop_Uop_Vop_add`), the
three pieces are bounded by

* the `EllPkgGo` piece: `|Rop α (PhiTil α f (E f))| ≤ Cpt · Ce · C₀α² · min z 1` (from `HQo α 4`
  and `hkMem_pointwise_min`; `Cpt` its constant),
* the star piece: `|Rop α (PhiTil α F_* Φs)| ≤ Cs α · z/(1+z)` (from `StarPkgo2.R`, whose `WDp 4`
  bound gives `|(z+1)/z · Rop α (PhiTil α F_* Φs)| ≤ Cs α`),
* the explicit piece: `Rop α (Theta α F_*) = 1/(1+z) − α sin²θ z/(1+z)² ∈ [0, 1/(1+z)]`
  (`Work.FTS.EpsEngine.Theta_Fstar_ops`).

The first two bounds are the two inputs here; the conclusion `|·| ≤ 1` holds as soon as
`Cpt·Ce·C₀α² + Cs α ≤ 1/4`: for `z ≥ 1` the three pieces are `≤ 1/4, 1/4, 1/2`; for `0 < z ≤ 1`
the sum is `≤ S·z + 1/(1+z)` with `S ≤ 1/4 ≤ 1/(1+z)`. -/
theorem Rop_block_abs_le_one {α Cpt Ce Cs C₀ : ℝ} {f Φs : ℝ → ℝ → ℝ} {E : (ℝ → ℝ → ℝ) → ℝ → ℝ → ℝ}
    {z θ : ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2))
    (hCpt : 0 ≤ Cpt) (hCe : 0 ≤ Ce) (hCs : 0 ≤ Cs) (hC₀ : 0 ≤ C₀)
    (hsmall : Cpt * (Ce * (C₀ * α ^ 2)) + Cs * α ≤ 1 / 4)
    (hdec : Work.Construction.Rop α (Work.Construction.PhiTil α f
          (fun z θ => Φs z θ + E f z θ)) z θ
        = Work.Construction.Rop α (Work.Construction.PhiTil α f (E f)) z θ
          + Work.Construction.Rop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
          + Work.Construction.Rop α (Work.Construction.Theta α (Work.Construction.Fstar α)) z θ)
    (hE : |Work.Construction.Rop α (Work.Construction.PhiTil α f (E f)) z θ|
        ≤ Cpt * (Ce * (C₀ * α ^ 2)) * min z 1)
    (hS : |Work.Construction.Rop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ|
        ≤ Cs * α * z / (1 + z)) :
    |Work.Construction.Rop α (Work.Construction.PhiTil α f
        (fun z θ => Φs z θ + E f z θ)) z θ| ≤ 1 := by
  -- The explicit piece: its closed form (`Theta_Fstar_ops`), at the given `(z,θ)`.
  have hCeq : Work.Construction.Rop α (Work.Construction.Theta α (Work.Construction.Fstar α)) z θ
      = 1 / (1 + z) - α * (Real.sin θ) ^ 2 * z / (1 + z) ^ 2 :=
    (Theta_Fstar_ops hα hα1).1 z θ hz hθ.1 hθ.2
  have h1z : (0 : ℝ) < 1 + z := by linarith
  have hsin0 : (0 : ℝ) ≤ (Real.sin θ) ^ 2 := sq_nonneg _
  have hsin1 : (Real.sin θ) ^ 2 ≤ 1 := Real.sin_sq_le_one θ
  have hαsin : α * (Real.sin θ) ^ 2 ≤ 1 := by
    calc α * (Real.sin θ) ^ 2 ≤ 1 * (Real.sin θ) ^ 2 := mul_le_mul_of_nonneg_right hα1 hsin0
      _ = (Real.sin θ) ^ 2 := one_mul _
      _ ≤ 1 := hsin1
  have hkey : α * (Real.sin θ) ^ 2 * z ≤ 1 + z := by nlinarith [hαsin, hz]
  have hfrac : α * (Real.sin θ) ^ 2 * z / (1 + z) ^ 2 ≤ 1 / (1 + z) := by
    rw [div_le_iff₀ (pow_pos h1z 2)]
    have hh : 1 / (1 + z) * (1 + z) ^ 2 = 1 + z := by
      rw [div_mul_eq_mul_div, one_mul, pow_two]
      exact mul_div_cancel_left₀ (1 + z) (ne_of_gt h1z)
    rw [hh]
    exact hkey
  -- the explicit piece lies in `[0, 1/(1+z)]`
  have hCnn : 0 ≤ Work.Construction.Rop α (Work.Construction.Theta α (Work.Construction.Fstar α)) z θ := by
    rw [hCeq]
    linarith
  have hCle : Work.Construction.Rop α (Work.Construction.Theta α (Work.Construction.Fstar α)) z θ
      ≤ 1 / (1 + z) := by
    rw [hCeq]
    have h0 : (0 : ℝ) ≤ α * (Real.sin θ) ^ 2 * z / (1 + z) ^ 2 :=
      div_nonneg (mul_nonneg (mul_nonneg hα.le hsin0) hz.le) (sq_nonneg _)
    linarith
  have hCabs : |Work.Construction.Rop α (Work.Construction.Theta α (Work.Construction.Fstar α)) z θ|
      ≤ 1 / (1 + z) :=
    abs_le.mpr ⟨by
      have h0 : (0 : ℝ) ≤ 1 / (1 + z) := div_nonneg zero_le_one h1z.le
      linarith, hCle⟩
  -- the star piece is bounded by a multiple of `min z 1`
  have hmin0 : (0 : ℝ) ≤ min z 1 := le_min hz.le zero_le_one
  have hzdiv : z / (1 + z) ≤ min z 1 := by
    rw [le_min_iff]
    refine ⟨?_, ?_⟩
    · rw [div_le_iff₀ h1z]
      nlinarith [sq_nonneg z, hz]
    · rw [div_le_one h1z]
      linarith
  have hB2 : |Work.Construction.Rop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ|
      ≤ Cs * α * min z 1 := by
    have h := mul_le_mul_of_nonneg_left hzdiv (mul_nonneg hCs hα.le)
    rw [← mul_div_assoc] at h
    exact le_trans hS h
  -- assemble the three bounds
  rw [hdec]
  calc |Work.Construction.Rop α (Work.Construction.PhiTil α f (E f)) z θ
        + Work.Construction.Rop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
        + Work.Construction.Rop α (Work.Construction.Theta α (Work.Construction.Fstar α)) z θ|
      ≤ |Work.Construction.Rop α (Work.Construction.PhiTil α f (E f)) z θ|
        + |Work.Construction.Rop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ|
        + |Work.Construction.Rop α (Work.Construction.Theta α (Work.Construction.Fstar α)) z θ| :=
        abs_add_three _ _ _
    _ ≤ Cpt * (Ce * (C₀ * α ^ 2)) * min z 1 + Cs * α * min z 1 + 1 / (1 + z) := by
        linarith [hE, hB2, hCabs]
    _ = (Cpt * (Ce * (C₀ * α ^ 2)) + Cs * α) * min z 1 + 1 / (1 + z) := by ring
    _ ≤ 1 / 4 * min z 1 + 1 / (1 + z) := by
        have hm := mul_le_mul_of_nonneg_right hsmall hmin0
        linarith
    _ ≤ 1 := quarter_min_add_inv_le_one hz

end Work.FTS.EpsEngine
