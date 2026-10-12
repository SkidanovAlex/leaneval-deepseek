import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseB7A.Statements
import Submission.Work.BoseB7A.smallness_conj8
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB7A.absz_bounds` — the size of the `c`-number `z` and its two consequences

At FS's parameter point (`FSParamsView E`) the substituted condensate density is
`ρ_z = z²/ℓ³` (`Q3Env.rho`, FS `thm:Kafz`) and FS's `eq:Close` holds in the crude
form `|ρ_z - μ| ≤ μ/2`, i.e. `ρ_z ≤ (3/2)μ`.  Hence

  `z² = ρ_z ℓ³ ≤ (3/2)·μℓ³ = (3/2)·X^{-166}`,

because `μℓ³ = K_ℓ³(μa³)^{-1/2} = X^{-9/2}X^{-323/2} = X^{-166}`
(`Work.BoseB7.mue_val`).  Taking square roots,

  `|z| ≤ √(3/2)·X^{-83}`   (`absz_le_sqrt` below),

and since `√(3/2) ≤ 5/4` this gives the first conjunct of `absz_bounds`.

The other two conjuncts are the "errors involving `z`" that the arithmetic leg of
`thm:Control3Q` needs; both are consequences of the bound above and of the exact
identity `a/ℓ = X^{163}` (`Work.BoseB7A.aScat_div_ell`):

* `√(ρ_zℓ³)/ℓ³·a³ = |z|·(a/ℓ)³ = |z|·X^{489} ≤ (5/4)X^{-83+489} = (5/4)X^{406}`;
* `a³ρ_z|z| = (a/ℓ)³·|z|³ ≤ X^{489}·(√(3/2))³·X^{-249} = (3/2)√(3/2)·X^{240}`,
  the constant being *exact*: `(√(3/2))³ = (3/2)√(3/2)`.

(`X = fsXp t 1 = (μa³)^{1/323}`; exponents are in the `fsXp` normal form.)
-/

noncomputable section

namespace Work.BoseB7A

open Work.BoseB7
open Work.BoseBox

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]

/-- `√(3/2) ≤ 5/4` (since `3/2 ≤ 25/16`). -/
private lemma sqrt_three_halves_le : Real.sqrt (3 / 2) ≤ (5 / 4 : ℝ) := by
  have h := Real.sqrt_le_sqrt (show (3 / 2 : ℝ) ≤ (5 / 4) ^ 2 by norm_num)
  rwa [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 5 / 4)] at h

/-- `(√(3/2))³ = (3/2)√(3/2)`. -/
private lemma sqrt_three_halves_cube :
    (Real.sqrt (3 / 2)) ^ 3 = (3 / 2) * Real.sqrt (3 / 2) := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3 / 2)]

/-- **The size of the `c`-number `z`.**  `z² = ρ_zℓ³ ≤ (3/2)μℓ³ = (3/2)X^{-166}`
(FS `eq:Close` and `μℓ³ = X^{-166}`), hence `|z| ≤ √(3/2)·X^{-83}`. -/
lemma absz_le_sqrt (E : Q3Env Mode) (hv : FSParamsView E) :
    |E.z| ≤ Real.sqrt (3 / 2) * fsXp hv.t (-83) := by
  have ht : 0 < hv.t := hv.t_pos
  have hE : 0 < E.ell ^ 3 := pow_pos (ell_pos E hv) 3
  -- `z² ≤ (3/2)·μℓ³`
  have hz2 : E.z ^ 2 ≤ (3 / 2) * fsXp hv.t (-166) := by
    calc E.z ^ 2 = E.rho * E.ell ^ 3 := zsq_eq E hv
      _ ≤ (3 / 2) * (E.mu * E.ell ^ 3) := by nlinarith [rho_le E hv, hE]
      _ = (3 / 2) * fsXp hv.t (-166) := by rw [mue_val E hv]
  -- `(X^{-83})² = X^{-166}`
  have hsq : (fsXp hv.t (-83)) ^ 2 = fsXp hv.t (-166) := by
    rw [fsXp_pow ht.le]
    norm_num
  refine abs_le_of_sq_le_sq ?_ (mul_nonneg (Real.sqrt_nonneg _) (fsXp_nonneg ht.le))
  calc E.z ^ 2 ≤ (3 / 2) * fsXp hv.t (-166) := hz2
    _ = (Real.sqrt (3 / 2) * fsXp hv.t (-83)) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3 / 2), hsq]

/-- `(a/ℓ)³ = X^{489}` (from `a/ℓ = X^{163}`). -/
private lemma aScat_div_ell_cube (E : Q3Env Mode) (hv : FSParamsView E) :
    (E.aScat / E.ell) ^ 3 = fsXp hv.t 489 := by
  rw [aScat_div_ell E hv, fsXp_pow hv.t_pos.le]
  norm_num

/-- The second conjunct of `absz_bounds`: `√(ρ_zℓ³)/ℓ³·a³ = |z|(a/ℓ)³ ≤ (5/4)X^{406}`. -/
lemma sqrt_rho_cube_div_ell_cube_le (E : Q3Env Mode) (hv : FSParamsView E)
    (hz : |E.z| ≤ Real.sqrt (3 / 2) * fsXp hv.t (-83)) :
    Real.sqrt (E.rho * E.ell ^ 3) / E.ell ^ 3 * E.aScat ^ 3 ≤
      (5 / 4) * fsXp hv.t 406 := by
  have ht : 0 < hv.t := hv.t_pos
  have hellne : E.ell ^ 3 ≠ 0 := pow_ne_zero 3 (ne_of_gt (ell_pos E hv))
  have hsqrt : Real.sqrt (E.rho * E.ell ^ 3) = |E.z| := by
    rw [← zsq_eq E hv, Real.sqrt_sq_eq_abs]
  have hz' : |E.z| ≤ (5 / 4) * fsXp hv.t (-83) :=
    le_trans hz (mul_le_mul_of_nonneg_right sqrt_three_halves_le (fsXp_nonneg ht.le))
  have hrew : Real.sqrt (E.rho * E.ell ^ 3) / E.ell ^ 3 * E.aScat ^ 3
      = |E.z| * (E.aScat / E.ell) ^ 3 := by
    rw [hsqrt, div_pow]
    field_simp
  calc Real.sqrt (E.rho * E.ell ^ 3) / E.ell ^ 3 * E.aScat ^ 3
      = |E.z| * (E.aScat / E.ell) ^ 3 := hrew
    _ = |E.z| * fsXp hv.t 489 := by rw [aScat_div_ell_cube E hv]
    _ ≤ ((5 / 4) * fsXp hv.t (-83)) * fsXp hv.t 489 :=
        mul_le_mul_of_nonneg_right hz' (fsXp_nonneg ht.le)
    _ = (5 / 4) * fsXp hv.t 406 := by
        rw [mul_assoc, fsXp_mul ht]
        norm_num

/-- The third conjunct of `absz_bounds`: `a³ρ_z|z| = (a/ℓ)³|z|³ ≤ (3/2)√(3/2)X^{240}`. -/
lemma aScat_cube_rho_absz_le (E : Q3Env Mode) (hv : FSParamsView E)
    (hz : |E.z| ≤ Real.sqrt (3 / 2) * fsXp hv.t (-83)) :
    E.aScat ^ 3 * E.rho * |E.z| ≤ (3 / 2) * Real.sqrt (3 / 2) * fsXp hv.t 240 := by
  have ht : 0 < hv.t := hv.t_pos
  have hellne : E.ell ^ 3 ≠ 0 := pow_ne_zero 3 (ne_of_gt (ell_pos E hv))
  -- `ρ_z = z²/ℓ³`, so `a³ρ_z|z| = (a/ℓ)³|z|³`
  have hrho : E.rho = E.z ^ 2 / E.ell ^ 3 := by
    rw [eq_div_iff hellne]
    exact (zsq_eq E hv).symm
  have hrew : E.aScat ^ 3 * E.rho * |E.z| = (E.aScat / E.ell) ^ 3 * |E.z| ^ 3 := by
    rw [hrho, div_pow, ← sq_abs E.z]
    field_simp
  have hcube3 : (Real.sqrt (3 / 2) * fsXp hv.t (-83)) ^ 3
      = (3 / 2) * Real.sqrt (3 / 2) * fsXp hv.t (-249) := by
    rw [mul_pow, sqrt_three_halves_cube, fsXp_pow ht.le]
    norm_num
  have hfs : fsXp hv.t 489 * fsXp hv.t (-249) = fsXp hv.t 240 := by
    rw [fsXp_mul ht]
    norm_num
  have hz3 : |E.z| ^ 3 ≤ (Real.sqrt (3 / 2) * fsXp hv.t (-83)) ^ 3 :=
    pow_le_pow_left₀ (abs_nonneg E.z) hz 3
  calc E.aScat ^ 3 * E.rho * |E.z|
      = (E.aScat / E.ell) ^ 3 * |E.z| ^ 3 := hrew
    _ = fsXp hv.t 489 * |E.z| ^ 3 := by rw [aScat_div_ell_cube E hv]
    _ ≤ fsXp hv.t 489 * (Real.sqrt (3 / 2) * fsXp hv.t (-83)) ^ 3 :=
        mul_le_mul_of_nonneg_left hz3 (fsXp_nonneg ht.le)
    _ = fsXp hv.t 489 * ((3 / 2) * Real.sqrt (3 / 2) * fsXp hv.t (-249)) := by rw [hcube3]
    _ = (3 / 2) * Real.sqrt (3 / 2) * (fsXp hv.t 489 * fsXp hv.t (-249)) := by ring
    _ = (3 / 2) * Real.sqrt (3 / 2) * fsXp hv.t 240 := by rw [hfs]

theorem absz_bounds {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (E : Work.BoseB7.Q3Env Mode) (hv : Work.BoseB7.FSParamsView E) :
    |E.z| ≤ (5 / 4) * Work.BoseBox.fsXp hv.t (-83) ∧
    (Real.sqrt (E.rho * E.ell ^ 3) / E.ell ^ 3 * E.aScat ^ 3 ≤
      (5 / 4) * Work.BoseBox.fsXp hv.t 406) ∧
    (E.aScat ^ 3 * E.rho * |E.z| ≤ (3 / 2) * Real.sqrt (3 / 2) * Work.BoseBox.fsXp hv.t 240) := by
  have hz := absz_le_sqrt E hv
  refine ⟨?_, sqrt_rho_cube_div_ell_cube_le E hv hz, aScat_cube_rho_absz_le E hv hz⟩
  exact le_trans hz
    (mul_le_mul_of_nonneg_right sqrt_three_halves_le (fsXp_nonneg (c := -83) hv.t_pos.le))

end Work.BoseB7A
