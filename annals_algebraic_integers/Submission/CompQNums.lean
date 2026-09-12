import Submission.Bclps
import Submission.ChebSerre
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Numerical constants of the complementary-polynomial construction (CompQ)

Single-interval instance of Smith's `defn:comp_Q` (adjust.tex).  With
`D = Bclps.Dconst` (≥ 256/(κ−1), so κ^r/64 spacing fits D+1 levels in every
bracket gap of the Bclps polynomial) and `C1 := 32` (so that
`D·levelStep r = κ^r/64` equals the lower bound `|T(bracket)| ≥ κ^r/64`
established in `Bclps.bclps_forcing`), we fix:

* `levelStep r = κ^r/(64·D)` — the level spacing (paper: `κ^r/(2DC1)`, C1 = 32);
* `factorCenter r j = (2j+1)·levelStep r / 2` — the factors of `Q0`
  (paper: `(2j+1)·κ^r/(4DC1)`);
* `C2val = 8·(128·D)^D = 8·(4DC1)^D` — the pigeonhole constant of the paper.

Pure-ℝ lemmas: level values are positive, the top level equals `κ^r/64`,
factor centers lie below `κ^r/64`, the distance from any level point `j·u` to
any factor center is ≥ `u/2` (so `|Q0(v)| ≥ (u/2)^D = κ^{Dr}·(128D)^{−D}` at
level points), geometric-sum bounds for the ε-perturbation, and the
"large r" inequality that makes the sign-transfer of `lem:comp_Q_roots`
work: `4·κ^{1−r}/(κ−1) < 6/C2val` for all `r ≥ C`.
-/

noncomputable section

open scoped Real
open Polynomial

namespace Submission.CompQNums

open Submission.SerreExample
open Submission.ChebSerre
open Submission.Bclps

/-- The integer `D` of the construction (same as `Bclps.Dconst`). -/
noncomputable def D : ℕ := Bclps.Dconst

/-- `D ≥ 1`. -/
lemma D_pos : 1 ≤ D := by
  unfold D
  exact Bclps.Dconst_pos

/-- `D > 0` as a real. -/
lemma D_real_pos : (0 : ℝ) < (D : ℝ) := by
  have h : 1 ≤ (D : ℝ) := by exact_mod_cast D_pos
  linarith

/-- κ > 0. -/
lemma kappa_pos : (0 : ℝ) < kappaC := Bclps.kappaC_pos'

/-- κ ≥ 1. -/
lemma kappa_ge_one : (1 : ℝ) ≤ kappaC := Bclps.kappaC_ge_one

/-- Level spacing: `u_r = κ^r / (64·D)`. -/
noncomputable def levelStep (r : ℕ) : ℝ := kappaC ^ r / (64 * (D : ℝ))

/-- Q0-factor centers: `c_{r,j} = (2j+1)·u_r/2`. -/
noncomputable def factorCenter (r j : ℕ) : ℝ := (2 * j + 1) * levelStep r / 2

/-- The pigeonhole constant `C2 = 8·(4·D·C1)^D = 8·(128·D)^D`. -/
noncomputable def C2val : ℝ := 8 * (128 * (D : ℝ)) ^ D

/-- `u_r > 0`. -/
lemma levelStep_pos (r : ℕ) : 0 < levelStep r := by
  unfold levelStep
  exact div_pos (pow_pos kappa_pos r) (mul_pos (by norm_num) D_real_pos)

/-- Top level value: `D·u_r = κ^r/64`. -/
lemma level_top (r : ℕ) : (D : ℝ) * levelStep r = kappaC ^ r / 64 := by
  unfold levelStep
  have hDne : (D : ℝ) ≠ 0 := ne_of_gt D_real_pos
  field_simp [hDne]

/-- factor centers are positive. -/
lemma factorCenter_pos (r j : ℕ) : 0 < factorCenter r j := by
  unfold factorCenter
  exact div_pos (mul_pos (by positivity) (levelStep_pos r)) (by norm_num)

/-- factor centers (j < D) lie below `κ^r/64`. -/
lemma factor_center_lt {r j : ℕ} (hj : j < D) : factorCenter r j < kappaC ^ r / 64 := by
  rw [← level_top r]
  have hu : 0 < levelStep r := levelStep_pos r
  have hjs : (j : ℝ) + 1 ≤ (D : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hj)
  unfold factorCenter
  have hltfrac : (2 * (j : ℝ) + 1) / 2 < (j : ℝ) + 1 := by
    have hq : (2 * (j : ℝ) + 1) / 2 = (j : ℝ) + 1 / 2 := by ring
    rw [hq]
    have hjnn : (0 : ℝ) ≤ (j : ℝ) := by positivity
    nlinarith
  calc
    ((2 * (j : ℝ) + 1) * levelStep r) / 2 = ((2 * (j : ℝ) + 1) / 2) * levelStep r := by ring
    _ < ((j : ℝ) + 1) * levelStep r := mul_lt_mul_of_pos_right hltfrac hu
    _ ≤ (D : ℝ) * levelStep r := mul_le_mul_of_nonneg_right hjs (le_of_lt hu)

/-- any level point is at distance ≥ `u/2` from every factor center:
`|j·u − c_{j′}| ≥ u/2` for all naturals `j, j′`. -/
lemma level_gap (r j j' : ℕ) : levelStep r / 2 ≤ |(j : ℝ) * levelStep r - factorCenter r j'| := by
  have hu : 0 < levelStep r := levelStep_pos r
  have hu' : 0 ≤ levelStep r := le_of_lt hu
  have hx : |(j : ℝ) * levelStep r - factorCenter r j'| =
      levelStep r * |(j : ℝ) - ((2 * (j' : ℝ) + 1) / 2)| := by
    unfold factorCenter
    have hinner : (j : ℝ) * levelStep r - ((2 * (j' : ℝ) + 1) * levelStep r) / 2 =
        ((j : ℝ) - (2 * (j' : ℝ) + 1) / 2) * levelStep r := by ring
    rw [hinner]
    rw [abs_mul, abs_of_nonneg hu']
    ring
  rw [hx]
  have hhalf : (1 / 2 : ℝ) ≤ |(j : ℝ) - ((2 * (j' : ℝ) + 1) / 2)| := by
    by_cases hle : j ≤ j'
    · have hleR : (j : ℝ) ≤ (j' : ℝ) := by exact_mod_cast hle
      have hx' : (j : ℝ) - ((2 * (j' : ℝ) + 1) / 2) < 0 := by
        have hc : (2 * (j' : ℝ) + 1) / 2 = (j' : ℝ) + 1 / 2 := by ring
        rw [hc]
        nlinarith
      rw [abs_of_neg hx']
      have hc : (2 * (j' : ℝ) + 1) / 2 = (j' : ℝ) + 1 / 2 := by ring
      rw [hc]
      nlinarith
    · have hgt : j' < j := Nat.lt_of_not_ge hle
      have hgtR : (j' : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hgt)
      have hx' : 0 < (j : ℝ) - ((2 * (j' : ℝ) + 1) / 2) := by
        have hc : (2 * (j' : ℝ) + 1) / 2 = (j' : ℝ) + 1 / 2 := by ring
        rw [hc]
        nlinarith
      rw [abs_of_pos hx']
      have hc : (2 * (j' : ℝ) + 1) / 2 = (j' : ℝ) + 1 / 2 := by ring
      rw [hc]
      nlinarith
  calc
    levelStep r / 2 = levelStep r * (1 / 2) := by ring
    _ ≤ levelStep r * |(j : ℝ) - ((2 * (j' : ℝ) + 1) / 2)| := by
      exact mul_le_mul_of_nonneg_left hhalf hu'

/-- at a level point the product over the factors of `Q0` is ≥ `(u/2)^D`:
`(u/2)^D ≤ ∏_{j′ < D} |j·u − c_{j′}|`. -/
lemma prod_level_lower (r j : ℕ) :
    (levelStep r / 2) ^ D ≤ ∏ j' ∈ Finset.range D, |(j : ℝ) * levelStep r - factorCenter r j'| := by
  have hu : 0 < levelStep r := levelStep_pos r
  have hu2 : 0 < levelStep r / 2 := by positivity
  calc
    (levelStep r / 2) ^ D = ∏ _j' ∈ Finset.range D, (levelStep r / 2) := by
      rw [Finset.prod_const]
      rw [Finset.card_range]
    _ ≤ ∏ j' ∈ Finset.range D, |(j : ℝ) * levelStep r - factorCenter r j'| := by
      exact Finset.prod_le_prod (fun j' hj' => le_of_lt hu2)
        (fun j' hj' => level_gap r j j')

/-- geometric-sum bound used for the ε-perturbation:
`Σ_{t < r} 4κ^t ≤ 4κ^r/(κ−1)`. -/
lemma geom4 (r : ℕ) : (∑ t ∈ Finset.range r, 4 * kappaC ^ t) ≤ 4 * kappaC ^ r / (kappaC - 1) := by
  calc
    (∑ t ∈ Finset.range r, 4 * kappaC ^ t) = 4 * (∑ t ∈ Finset.range r, kappaC ^ t) := by
      rw [Finset.mul_sum]
    _ ≤ 4 * (kappaC ^ r / (kappaC - 1)) := by
      exact mul_le_mul_of_nonneg_left (Submission.Bclps.geom_sum_le r) (by norm_num)
    _ = 4 * kappaC ^ r / (kappaC - 1) := by ring

/-- C2val > 0. -/
lemma C2val_pos : 0 < C2val := by
  unfold C2val
  have hD : (0 : ℝ) < (D : ℝ) := D_real_pos
  have hbase : (0 : ℝ) < 128 * (D : ℝ) := by positivity
  exact mul_pos (by norm_num) (pow_pos hbase D)

/-- the "large r" inequality of `lem:comp_Q_roots`:
`4/((κ−1)·κ^(r−1)) < 6/C2val` for all `r ≥ C`
(i.e. `4·κ^{1−r}/(κ−1) < 6·C2val⁻¹`). -/
lemma large_r : ∃ C : ℕ, ∀ r : ℕ, C ≤ r →
    (4 : ℝ) / ((kappaC - 1) * kappaC ^ (r - 1)) < 6 / C2val := by
  have hk1 : (1 : ℝ) < kappaC := kappaC_gt_one
  have hkpos : 0 < kappaC - 1 := by linarith
  have hc2pos : 0 < C2val := C2val_pos
  have hunb := pow_unbounded_of_one_lt (4 * C2val / (6 * (kappaC - 1))) hk1
  rcases hunb with ⟨N, hN⟩
  refine ⟨N + 1, ?_⟩
  intro r hr
  have hmono : kappaC ^ N ≤ kappaC ^ (r - 1) := by
    apply pow_le_pow_right₀ (le_of_lt hk1)
    omega
  have hbound : (4 * C2val) / (6 * (kappaC - 1)) < kappaC ^ (r - 1) := lt_of_lt_of_le hN hmono
  have hpos6 : 0 < (6 : ℝ) * (kappaC - 1) := by positivity
  have hgt0a : 0 < (kappaC - 1) * kappaC ^ (r - 1) :=
    mul_pos hkpos (pow_pos (lt_trans zero_lt_one hk1) (r - 1))
  have hstep : 4 * C2val < (6 * (kappaC - 1)) * kappaC ^ (r - 1) := by
    calc
      4 * C2val < kappaC ^ (r - 1) * (6 * (kappaC - 1)) := (div_lt_iff₀ hpos6).mp hbound
      _ = (6 * (kappaC - 1)) * kappaC ^ (r - 1) := by ring
  have hmain : (4 : ℝ) < (6 / C2val) * ((kappaC - 1) * kappaC ^ (r - 1)) := by
    calc
      (4 : ℝ) < (6 * (kappaC - 1) * kappaC ^ (r - 1)) / C2val := by
        exact (lt_div_iff₀ hc2pos).mpr hstep
      _ = (6 / C2val) * ((kappaC - 1) * kappaC ^ (r - 1)) := by ring
  exact (div_lt_iff₀ hgt0a).mpr hmain

end Submission.CompQNums
