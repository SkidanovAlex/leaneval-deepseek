import Mathlib.Tactic.Have
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Submission.ChiWitness
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `dℓ`-scale cosine-`M`-th-power bump `chiSmall` (FS eq:Def_chi transcription)

This module lays down the corpus object that FS `final_v2.tex` §SmallBoxes +
Appendix `sec:chiproperties` use at the small-box (`dℓ`) scale — the explicit
**cosine-`M`-th-power** localisation

    χ_M(x) = C_M · (ζ(x₁)·ζ(x₂)·ζ(x₃))^M ,  ζ(y) = cos(πy)·1_{|y| ≤ 1/2} ,
    C_M = 1/√∫(ζζζ)^{2M}  (so ∫χ_M² = 1),

whose **M-th-power face decay** (`|χ_M(z)| ≤ C_M·(1/2 − |z_j|)₊^M` per
coordinate) is the load-bearing content of the small-box geometry
(eq:chiBsupgeneral/eq:chiBsupspecial → eq:Iintegral → eq:badset in the a
priori chain).  The generic smooth `ContDiffBump`-based corpus `chi`
(`CubicChi`) cannot supply this decay (its Mathlib interface has no boundary
control), so this object is a fresh, self-contained Work-layer module
(imports only Mathlib; no corpus dependency).

Contents (namespace `Submission.BoseGases`):
- `zeta1d` — the 1D cosine profile `ζ`; nonneg, ≤ 1, even, continuous,
  `ζ(y) ≤ 4·(1/2 − |y|)₊` (face decay at unit scale).
- `chiSmallBase M` — `(ζ(z₁)ζ(z₂)ζ(z₃))^M`.
- `chiSmall M` — the L²-normalised bump (`chiSmallBase / √∫base²`);
  `chiSmallNormSq`, `chiSmallNormFactor`, `chiSmallDecay`.
- Support containment in the unit box (faces at ±1/2), coordinatewise
  **M-th-power boundary decay** of `chiSmallBase` and of the normalised
  `chiSmall` (`chiSmall_decay_coord`), L²-normalisation `chiSmall_L2`.

Next stage (recorded in SmallBoxDesignNote.md): scale to the box faces
(`χ_M(x/ℓ)`, cut boxes) and assemble the bad-band bound `(g2)`.
-/

noncomputable section

open MeasureTheory Metric
open scoped Real BigOperators ENNReal Topology ContDiff

namespace Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 600000

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- FS 1D cosine profile: `ζ(y) = cos(π y)` for `|y| ≤ 1/2`, `0` outside. -/
noncomputable def zeta1d (y : ℝ) : ℝ :=
  if |y| ≤ 1 / 2 then Real.cos (Real.pi * y) else 0

lemma zeta1d_of_abs_le {y : ℝ} (hy : |y| ≤ 1 / 2) : zeta1d y = Real.cos (Real.pi * y) := by
  unfold zeta1d
  rw [if_pos hy]

lemma zeta1d_of_one_half_lt {y : ℝ} (hy : 1 / 2 < |y|) : zeta1d y = 0 := by
  unfold zeta1d
  rw [if_neg (not_le_of_gt hy)]

lemma zeta1d_ne_zero_abs_le {y : ℝ} (h : zeta1d y ≠ 0) : |y| ≤ 1 / 2 := by
  by_contra hb
  exact h (zeta1d_of_one_half_lt (lt_of_not_ge hb))

lemma zeta1d_nonneg (y : ℝ) : 0 ≤ zeta1d y := by
  by_cases hy : |y| ≤ 1 / 2
  · rw [zeta1d_of_abs_le hy]
    have hπ : 0 ≤ Real.pi := le_of_lt Real.pi_pos
    have hm : |Real.pi * y| ≤ Real.pi / 2 := by
      calc
        |Real.pi * y| = Real.pi * |y| := by rw [abs_mul, abs_of_nonneg hπ]
        _ ≤ Real.pi * (1 / 2) := mul_le_mul_of_nonneg_left hy hπ
        _ = Real.pi / 2 := by ring
    exact Real.cos_nonneg_of_neg_pi_div_two_le_of_le (abs_le.mp hm).1 (abs_le.mp hm).2
  · rw [zeta1d_of_one_half_lt (lt_of_not_ge hy)]

lemma zeta1d_le_one (y : ℝ) : zeta1d y ≤ 1 := by
  by_cases hy : |y| ≤ 1 / 2
  · rw [zeta1d_of_abs_le hy]
    exact Real.cos_le_one _
  · rw [zeta1d_of_one_half_lt (lt_of_not_ge hy)]
    norm_num

lemma abs_zeta1d_le_one (y : ℝ) : |zeta1d y| ≤ 1 := by
  rw [abs_of_nonneg (zeta1d_nonneg y)]
  exact zeta1d_le_one y

/-- cos (π y) = cos (π |y|) — cosine is even. -/
lemma cos_pi_mul_eq_cos_pi_abs (y : ℝ) : Real.cos (Real.pi * y) = Real.cos (Real.pi * |y|) := by
  by_cases hy : 0 ≤ y
  · rw [abs_of_nonneg hy]
  · have hneg : |y| = -y := abs_of_neg (lt_of_not_ge hy)
    rw [hneg]
    rw [mul_neg]
    exact (Real.cos_neg (Real.pi * y)).symm

lemma zeta1d_neg (y : ℝ) : zeta1d (-y) = zeta1d y := by
  by_cases hy : |y| ≤ 1 / 2
  · rw [zeta1d_of_abs_le (by simpa using hy), zeta1d_of_abs_le hy]
    rw [mul_neg]
    exact Real.cos_neg (Real.pi * y)
  · have hb : 1 / 2 < |-y| := by simpa using (lt_of_not_ge hy)
    rw [zeta1d_of_one_half_lt hb, zeta1d_of_one_half_lt (lt_of_not_ge hy)]

/-- 1D face decay: on `|y| ≤ 1/2`, `ζ(y) ≤ 4(1/2 − |y|)`. -/
lemma zeta1d_le_four_mul_sub (y : ℝ) (hy : |y| ≤ 1 / 2) :
    zeta1d y ≤ 4 * (1 / 2 - |y|) := by
  rw [zeta1d_of_abs_le hy]
  rw [cos_pi_mul_eq_cos_pi_abs y]
  have hsub : 0 ≤ 1 / 2 - |y| := by linarith
  have hu : 0 ≤ Real.pi / 2 - Real.pi * |y| := by nlinarith [Real.pi_pos]
  calc
    Real.cos (Real.pi * |y|) = Real.sin (Real.pi / 2 - Real.pi * |y|) := by
        exact (Real.sin_pi_div_two_sub (Real.pi * |y|)).symm
    _ ≤ Real.pi / 2 - Real.pi * |y| := Real.sin_le hu
    _ = Real.pi * (1 / 2 - |y|) := by ring
    _ ≤ 4 * (1 / 2 - |y|) := by
        exact mul_le_mul_of_nonneg_right Real.pi_le_four hsub

/-- 1D face decay with positive part, valid everywhere. -/
lemma zeta1d_le_four_max (y : ℝ) : zeta1d y ≤ 4 * max (1 / 2 - |y|) 0 := by
  by_cases hy : |y| ≤ 1 / 2
  · calc
      zeta1d y ≤ 4 * (1 / 2 - |y|) := zeta1d_le_four_mul_sub y hy
      _ ≤ 4 * max (1 / 2 - |y|) 0 := by
          exact mul_le_mul_of_nonneg_left (le_max_left _ _) (by norm_num)
  · rw [zeta1d_of_one_half_lt (lt_of_not_ge hy)]
    positivity

-- ============ continuity of zeta1d (for the L²-normalisation) ============

lemma zeta1d_continuous : Continuous zeta1d := by
  unfold zeta1d
  refine Continuous.if ?_ ?_ continuous_zero
  · intro a ha
    have hset : {y : ℝ | |y| ≤ 1 / 2} = closedBall (0 : ℝ) (1 / 2) := by
      ext y
      simp [dist_eq_norm, Real.norm_eq_abs, sub_eq_add_neg]
    have hfront : a ∈ frontier (closedBall (0 : ℝ) (1 / 2)) := by
      rw [← hset]
      exact ha
    rw [frontier_closedBall' (0 : ℝ) (1 / 2)] at hfront
    have habs : |a| = 1 / 2 := by
      simpa [dist_eq_norm, Real.norm_eq_abs, sub_eq_add_neg] using hfront
    calc
      Real.cos (Real.pi * a) = Real.cos (Real.pi * |a|) := cos_pi_mul_eq_cos_pi_abs a
      _ = Real.cos (Real.pi / 2) := by
          rw [habs]
          congr 1
          ring
      _ = 0 := Real.cos_pi_div_two
  · exact Real.continuous_cos.comp (continuous_const.mul continuous_id)



-- ============ 3D M-th-power product profile ============

/-- Unnormalised M-th-power product `(ζ(z₁)ζ(z₂)ζ(z₃))^M`. -/
noncomputable def chiSmallBase (M : ℕ) (z : ℝ³) : ℝ :=
  (zeta1d (z.ofLp 0) * zeta1d (z.ofLp 1) * zeta1d (z.ofLp 2)) ^ M

/-- `∫ (chiSmallBase M)²`, the normalisation integral. -/
noncomputable def chiSmallNormSq (M : ℕ) : ℝ :=
  ∫ z : ℝ³, (chiSmallBase M z) ^ 2

/-- L²-normalised M-th-power bump: `χ_M := (ζζζ)^M / √∫(ζζζ)^{2M}`. -/
noncomputable def chiSmall (M : ℕ) (z : ℝ³) : ℝ :=
  chiSmallBase M z / Real.sqrt (chiSmallNormSq M)

/-- `1/√∫base²`, the normalisation factor of `chiSmall`. -/
noncomputable def chiSmallNormFactor (M : ℕ) : ℝ :=
  (Real.sqrt (chiSmallNormSq M))⁻¹

/-- The decay constant of `chiSmall` at power `M` (depends only on `M`). -/
noncomputable def chiSmallDecay (M : ℕ) : ℝ :=
  chiSmallNormFactor M * 4 ^ M

lemma chiSmallBase_nonneg (M : ℕ) (z : ℝ³) : 0 ≤ chiSmallBase M z := by
  exact pow_nonneg (mul_nonneg (mul_nonneg (zeta1d_nonneg _) (zeta1d_nonneg _)) (zeta1d_nonneg _)) M

lemma chiSmall_nonneg (M : ℕ) (z : ℝ³) : 0 ≤ chiSmall M z := by
  dsimp [chiSmall]
  exact div_nonneg (chiSmallBase_nonneg M z) (Real.sqrt_nonneg _)

-- coordinates are continuous
lemma coord_continuous (j : Fin 3) : Continuous (fun z : ℝ³ => z.ofLp j) := by
  simpa using (PiLp.continuous_apply (p := 2) (β := fun _ : Fin 3 => ℝ) j)

lemma chiSmallBase_continuous (M : ℕ) : Continuous (fun z : ℝ³ => chiSmallBase M z) := by
  unfold chiSmallBase
  have h0 : Continuous (fun z : ℝ³ => zeta1d (z.ofLp 0)) := zeta1d_continuous.comp (coord_continuous 0)
  have h1 : Continuous (fun z : ℝ³ => zeta1d (z.ofLp 1)) := zeta1d_continuous.comp (coord_continuous 1)
  have h2 : Continuous (fun z : ℝ³ => zeta1d (z.ofLp 2)) := zeta1d_continuous.comp (coord_continuous 2)
  have hprod : Continuous (fun z : ℝ³ => zeta1d (z.ofLp 0) * zeta1d (z.ofLp 1) * zeta1d (z.ofLp 2)) :=
    (h0.mul h1).mul h2
  exact hprod.pow M

-- support containment per coordinate (unit box faces), M ≥ 1
lemma chiSmallBase_factors_ne_zero {M : ℕ} (hM : 1 ≤ M) {z : ℝ³}
    (hz : chiSmallBase M z ≠ 0) :
    zeta1d (z.ofLp 0) ≠ 0 ∧ zeta1d (z.ofLp 1) ≠ 0 ∧ zeta1d (z.ofLp 2) ≠ 0 := by
  have habc : zeta1d (z.ofLp 0) * zeta1d (z.ofLp 1) * zeta1d (z.ofLp 2) ≠ 0 := by
    intro hprod
    apply hz
    change (zeta1d (z.ofLp 0) * zeta1d (z.ofLp 1) * zeta1d (z.ofLp 2)) ^ M = 0
    rw [hprod]
    exact zero_pow (ne_of_gt (lt_of_lt_of_le zero_lt_one hM))
  refine ⟨?_, ?_, ?_⟩
  · intro h0
    exact habc (by rw [h0]; simp)
  · intro h1
    exact habc (by rw [h1]; simp)
  · intro h2
    exact habc (by rw [h2]; simp)

lemma chiSmallBase_factor_ne_zero {M : ℕ} (hM : 1 ≤ M) {z : ℝ³}
    (hz : chiSmallBase M z ≠ 0) (j : Fin 3) : zeta1d (z.ofLp j) ≠ 0 := by
  fin_cases j
  · exact (chiSmallBase_factors_ne_zero hM hz).1
  · exact (chiSmallBase_factors_ne_zero hM hz).2.1
  · exact (chiSmallBase_factors_ne_zero hM hz).2.2

lemma chiSmallBase_support_mem_abs_le {M : ℕ} (hM : 1 ≤ M) {z : ℝ³}
    (hz : chiSmallBase M z ≠ 0) (j : Fin 3) : |z.ofLp j| ≤ 1 / 2 := by
  exact zeta1d_ne_zero_abs_le (chiSmallBase_factor_ne_zero hM hz j)

lemma zeta1d_zero : zeta1d 0 = 1 := by
  rw [zeta1d_of_abs_le (by norm_num)]
  norm_num

lemma chiSmallBase_zero (M : ℕ) : chiSmallBase M 0 = 1 := by
  dsimp [chiSmallBase]
  have hz : ∀ j : Fin 3, zeta1d ((0 : ℝ³).ofLp j) = 1 := by
    intro j
    have h : (0 : ℝ³).ofLp j = (0 : ℝ) := by simp
    rw [h, zeta1d_zero]
  change (zeta1d ((0 : ℝ³).ofLp 0) * zeta1d ((0 : ℝ³).ofLp 1) * zeta1d ((0 : ℝ³).ofLp 2)) ^ M = 1
  rw [hz 0, hz 1, hz 2]
  simp

lemma chiSmallBase_ne_zero_zero {M : ℕ} (hM : 1 ≤ M) : chiSmallBase M 0 ≠ 0 := by
  rw [chiSmallBase_zero M]
  norm_num
-- ============ boundary decay: M-th power in the face distance ============

lemma abs_zeta1d_le_four_max (y : ℝ) : |zeta1d y| ≤ 4 * max (1 / 2 - |y|) 0 := by
  rw [abs_of_nonneg (zeta1d_nonneg y)]
  exact zeta1d_le_four_max y

/-- pointwise bounds on a product of three absolute values imply the bound on
the M-th power of the product. -/
lemma abs_prod3_pow_le {r₁ r₂ r₃ b₁ b₂ b₃ : ℝ} (M : ℕ)
    (h₁ : |r₁| ≤ b₁) (h₂ : |r₂| ≤ b₂) (h₃ : |r₃| ≤ b₃)
    (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂) (hb₃ : 0 ≤ b₃) :
    |(r₁ * r₂ * r₃) ^ M| ≤ (b₁ * b₂ * b₃) ^ M := by
  calc
    |(r₁ * r₂ * r₃) ^ M| = |r₁ * r₂ * r₃| ^ M := by rw [abs_pow]
    _ = (|r₁| * |r₂| * |r₃|) ^ M := by rw [abs_mul, abs_mul]
    _ ≤ (b₁ * b₂ * b₃) ^ M := by
      have h12 : |r₁| * |r₂| ≤ b₁ * b₂ := mul_le_mul h₁ h₂ (abs_nonneg _) hb₁
      have hm : (|r₁| * |r₂|) * |r₃| ≤ (b₁ * b₂) * b₃ :=
        mul_le_mul h12 h₃ (abs_nonneg _) (mul_nonneg hb₁ hb₂)
      exact pow_le_pow_left₀ (mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (abs_nonneg _)) hm M

/-- **Boundary decay of `chiSmallBase`, coordinatewise with the M-th power**:
`|χ̃_M(z)| ≤ 4^M·((1/2 − |z_j|)₊)^M` for every coordinate `j`. -/
lemma chiSmallBase_decay_coord (M : ℕ) (z : ℝ³) (j : Fin 3) :
    |chiSmallBase M z| ≤ (4 ^ M) * (max (1 / 2 - |z.ofLp j|) 0) ^ M := by
  fin_cases j
  · let p : ℝ := max (1 / 2 - |z.ofLp 0|) 0
    have hb : |chiSmallBase M z| ≤ ((4 * p) * 1 * 1) ^ M := by
      simpa [chiSmallBase, p] using
        (abs_prod3_pow_le (r₁ := zeta1d (z.ofLp 0)) (r₂ := zeta1d (z.ofLp 1)) (r₃ := zeta1d (z.ofLp 2))
          (b₁ := 4 * p) (b₂ := 1) (b₃ := 1) M
          (by simpa [p] using abs_zeta1d_le_four_max (z.ofLp 0))
          (abs_zeta1d_le_one (z.ofLp 1)) (abs_zeta1d_le_one (z.ofLp 2))
          (mul_nonneg (by norm_num) (le_max_right _ _)) (by norm_num) (by norm_num))
    calc
      |chiSmallBase M z| ≤ ((4 * p) * 1 * 1) ^ M := hb
      _ = (4 * p) ^ M := by simp
      _ = 4 ^ M * p ^ M := by rw [mul_pow]
      _ = (4 ^ M) * (max (1 / 2 - |z.ofLp 0|) 0) ^ M := by rfl
  · let p : ℝ := max (1 / 2 - |z.ofLp 1|) 0
    have hb : |chiSmallBase M z| ≤ ((1 * (4 * p)) * 1) ^ M := by
      simpa [chiSmallBase, p] using
        (abs_prod3_pow_le (r₁ := zeta1d (z.ofLp 0)) (r₂ := zeta1d (z.ofLp 1)) (r₃ := zeta1d (z.ofLp 2))
          (b₁ := 1) (b₂ := 4 * p) (b₃ := 1) M
          (abs_zeta1d_le_one (z.ofLp 0))
          (by simpa [p] using abs_zeta1d_le_four_max (z.ofLp 1))
          (abs_zeta1d_le_one (z.ofLp 2))
          (by norm_num) (mul_nonneg (by norm_num) (le_max_right _ _)) (by norm_num))
    calc
      |chiSmallBase M z| ≤ ((1 * (4 * p)) * 1) ^ M := hb
      _ = (4 * p) ^ M := by simp
      _ = 4 ^ M * p ^ M := by rw [mul_pow]
      _ = (4 ^ M) * (max (1 / 2 - |z.ofLp 1|) 0) ^ M := by rfl
  · let p : ℝ := max (1 / 2 - |z.ofLp 2|) 0
    have hb : |chiSmallBase M z| ≤ ((1 * 1) * (4 * p)) ^ M := by
      simpa [chiSmallBase, p] using
        (abs_prod3_pow_le (r₁ := zeta1d (z.ofLp 0)) (r₂ := zeta1d (z.ofLp 1)) (r₃ := zeta1d (z.ofLp 2))
          (b₁ := 1) (b₂ := 1) (b₃ := 4 * p) M
          (abs_zeta1d_le_one (z.ofLp 0)) (abs_zeta1d_le_one (z.ofLp 1))
          (by simpa [p] using abs_zeta1d_le_four_max (z.ofLp 2))
          (by norm_num) (by norm_num) (mul_nonneg (by norm_num) (le_max_right _ _)))
    calc
      |chiSmallBase M z| ≤ ((1 * 1) * (4 * p)) ^ M := hb
      _ = (4 * p) ^ M := by simp
      _ = 4 ^ M * p ^ M := by rw [mul_pow]
      _ = (4 ^ M) * (max (1 / 2 - |z.ofLp 2|) 0) ^ M := by rfl

-- ============ L²-normalisation and the normalised decay ============

/-- support of `chiSmallBase M` (M ≥ 1) is contained in the unit ball. -/
lemma chiSmallBase_support_norm_le {M : ℕ} (hM : 1 ≤ M) {z : ℝ³}
    (hz : chiSmallBase M z ≠ 0) : ‖z‖ ≤ 1 := by
  have hcoord : ∀ j : Fin 3, |z.ofLp j| ≤ 1 / 2 := chiSmallBase_support_mem_abs_le hM hz
  have hsq : ‖z‖ ^ 2 = ∑ j : Fin 3, |z.ofLp j| ^ 2 := by
    simpa using (PiLp.norm_sq_eq_of_L2 (β := fun _ : Fin 3 => ℝ) z)
  have hsum : (∑ j : Fin 3, |z.ofLp j| ^ 2) ≤ 3 * (1 / 2) ^ 2 := by
    calc
      (∑ j : Fin 3, |z.ofLp j| ^ 2) ≤ ∑ _j : Fin 3, (1 / 2) ^ 2 := by
          refine Finset.sum_le_sum ?_
          intro j hj
          exact pow_le_pow_left₀ (abs_nonneg _) (hcoord j) 2
      _ = 3 * (1 / 2) ^ 2 := by simp
  have hsq1 : ‖z‖ ^ 2 ≤ 1 := by
    rw [hsq]
    have hc : 3 * (1 / 2) ^ 2 ≤ 1 := by norm_num
    nlinarith
  have hx0 : 0 ≤ ‖z‖ := norm_nonneg z
  have habs : |‖z‖| ≤ |(1 : ℝ)| := by
    exact sq_le_sq.mp (by simpa using hsq1)
  simpa [abs_of_nonneg hx0] using habs

lemma chiSmallBase_hasCompactSupport {M : ℕ} (hM : 1 ≤ M) :
    HasCompactSupport (chiSmallBase M) := by
  change IsCompact (tsupport (chiSmallBase M))
  change IsCompact (closure (Function.support (chiSmallBase M)))
  refine IsCompact.of_isClosed_subset (isCompact_closedBall (0 : ℝ³) 1) isClosed_closure ?_
  calc
    closure (Function.support (chiSmallBase M)) ⊆ closure (closedBall (0 : ℝ³) 1) := by
        apply closure_mono
        intro z hz
        have hb : chiSmallBase M z ≠ 0 := Function.mem_support.mp hz
        simpa [Metric.mem_closedBall, dist_eq_norm, sub_eq_add_neg] using (chiSmallBase_support_norm_le hM hb)
    _ = closedBall (0 : ℝ³) 1 := closure_closedBall

lemma chiSmallNormSq_pos {M : ℕ} (hM : 1 ≤ M) : 0 < chiSmallNormSq M := by
  dsimp [chiSmallNormSq]
  have hcont2 : Continuous (fun z : ℝ³ => (chiSmallBase M z) ^ 2) := by
    have hc := chiSmallBase_continuous M
    fun_prop
  have hsup2 : HasCompactSupport (fun z : ℝ³ => (chiSmallBase M z) ^ 2) := by
    have hsqsup : Function.support (fun z : ℝ³ => (chiSmallBase M z) ^ 2) ⊆
        Function.support (chiSmallBase M) := by
      intro x hx
      have hx' : (chiSmallBase M x) ^ 2 ≠ 0 := Function.mem_support.mp hx
      exact Function.mem_support.mpr (by
        intro hb
        exact hx' (by simp [hb]))
    exact HasCompactSupport.mono (chiSmallBase_hasCompactSupport hM) hsqsup
  have hnonneg : 0 ≤ fun z : ℝ³ => (chiSmallBase M z) ^ 2 := by
    intro z
    exact sq_nonneg (chiSmallBase M z)
  have hzero : (fun z : ℝ³ => (chiSmallBase M z) ^ 2) 0 ≠ 0 := by
    exact pow_ne_zero 2 (chiSmallBase_ne_zero_zero hM)
  exact Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    (f := fun z : ℝ³ => (chiSmallBase M z) ^ 2) (x := 0) hcont2 hsup2 hnonneg hzero

lemma chiSmall_L2 {M : ℕ} (hM : 1 ≤ M) : (∫ z : ℝ³, (chiSmall M z) ^ 2) = 1 := by
  have hSpos : 0 < chiSmallNormSq M := chiSmallNormSq_pos hM
  have hS : (Real.sqrt (chiSmallNormSq M)) ^ 2 = chiSmallNormSq M :=
    Real.sq_sqrt (le_of_lt hSpos)
  calc
    (∫ z : ℝ³, (chiSmall M z) ^ 2) = ∫ z : ℝ³, (chiSmallBase M z) ^ 2 / chiSmallNormSq M := by
      apply integral_congr_ae
      refine ae_of_all _ ?_
      intro z
      dsimp [chiSmall]
      rw [div_pow, hS]
    _ = (∫ z : ℝ³, (chiSmallBase M z) ^ 2) / chiSmallNormSq M := by
      rw [integral_div]
    _ = 1 := by
      dsimp [chiSmallNormSq]
      exact div_self (ne_of_gt hSpos)

lemma chiSmallNormFactor_nonneg (M : ℕ) : 0 ≤ chiSmallNormFactor M := by
  dsimp [chiSmallNormFactor]
  exact inv_nonneg.mpr (Real.sqrt_nonneg _)

lemma chiSmall_abs_eq {M : ℕ} (hM : 1 ≤ M) (z : ℝ³) :
    |chiSmall M z| = |chiSmallBase M z| * chiSmallNormFactor M := by
  have hSpos : 0 < chiSmallNormSq M := chiSmallNormSq_pos hM
  have hs : 0 < Real.sqrt (chiSmallNormSq M) := Real.sqrt_pos.mpr hSpos
  dsimp [chiSmallNormFactor]
  calc
    |chiSmall M z| = |chiSmallBase M z / Real.sqrt (chiSmallNormSq M)| := rfl
    _ = |chiSmallBase M z| / Real.sqrt (chiSmallNormSq M) := by
        rw [abs_div, abs_of_nonneg (le_of_lt hs)]
    _ = |chiSmallBase M z| * (Real.sqrt (chiSmallNormSq M))⁻¹ := by
        field_simp [ne_of_gt hs]
    _ = |chiSmallBase M z| * (Real.sqrt (chiSmallNormSq M))⁻¹ := rfl

/-- **Boundary decay of the normalised `chiSmall`, coordinatewise with the
M-th power**: `|χ_M(z)| ≤ chiSmallDecay M · ((1/2 − |z_j|)₊)^M`. -/
lemma chiSmall_decay_coord {M : ℕ} (hM : 1 ≤ M) (z : ℝ³) (j : Fin 3) :
    |chiSmall M z| ≤ chiSmallDecay M * (max (1 / 2 - |z.ofLp j|) 0) ^ M := by
  calc
    |chiSmall M z| = |chiSmallBase M z| * chiSmallNormFactor M := chiSmall_abs_eq hM z
    _ ≤ (4 ^ M * (max (1 / 2 - |z.ofLp j|) 0) ^ M) * chiSmallNormFactor M := by
        exact mul_le_mul_of_nonneg_right (chiSmallBase_decay_coord M z j) (chiSmallNormFactor_nonneg M)
    _ = chiSmallDecay M * (max (1 / 2 - |z.ofLp j|) 0) ^ M := by
        dsimp [chiSmallDecay]
        ring

/-- support containment of the normalised bump in the unit box. -/
lemma chiSmall_support_mem_abs_le {M : ℕ} (hM : 1 ≤ M) {z : ℝ³}
    (hz : chiSmall M z ≠ 0) (j : Fin 3) : |z.ofLp j| ≤ 1 / 2 := by
  have hb : chiSmallBase M z ≠ 0 := by
    intro hb0
    apply hz
    dsimp [chiSmall]
    rw [hb0]
    simp
  exact chiSmallBase_support_mem_abs_le hM hb j


-- ============ box-face-scaled corollaries (χ_M(x/c), c > 0) ============

/-- scaled support containment: `χ_M(x/c) ≠ 0` forces every coordinate into
the face slab `|x_j| ≤ c/2` of the box of half-side `c/2`. -/
lemma chiSmall_scale_support_mem_abs_le {M : ℕ} (hM : 1 ≤ M) {c : ℝ} (hc : 0 < c) {x : ℝ³}
    (hz : chiSmall M ((c⁻¹) • x) ≠ 0) (j : Fin 3) : |x.ofLp j| ≤ c / 2 := by
  have hz' := chiSmall_support_mem_abs_le hM hz j
  have hlin : ((c⁻¹) • x).ofLp j = c⁻¹ * x.ofLp j := by simp
  have hcabs : |((c⁻¹) • x).ofLp j| = c⁻¹ * |x.ofLp j| := by
    rw [hlin, abs_mul, abs_of_nonneg (inv_nonneg.mpr (le_of_lt hc))]
  rw [hcabs] at hz'
  have hm := mul_le_mul_of_nonneg_left hz' (le_of_lt hc)
  calc
    |x.ofLp j| = c * (c⁻¹ * |x.ofLp j|) := by field_simp [hc.ne']
    _ ≤ c * (1 / 2) := hm
    _ = c / 2 := by ring

/-- scaled boundary decay: `|χ_M(x/c)| ≤ chiSmallDecay M·((1/2 − |x_j|/c)₊)^M`. -/
lemma chiSmall_scale_decay {M : ℕ} (hM : 1 ≤ M) {c : ℝ} (hc : 0 < c) (x : ℝ³) (j : Fin 3) :
    |chiSmall M ((c⁻¹) • x)| ≤ chiSmallDecay M * (max (1 / 2 - |x.ofLp j| / c) 0) ^ M := by
  have h0 := chiSmall_decay_coord hM ((c⁻¹) • x) j
  have hlin : ((c⁻¹) • x).ofLp j = c⁻¹ * x.ofLp j := by simp
  have hcabs : |((c⁻¹) • x).ofLp j| = c⁻¹ * |x.ofLp j| := by
    rw [hlin, abs_mul, abs_of_nonneg (inv_nonneg.mpr (le_of_lt hc))]
  rw [hcabs] at h0
  have hhalf : (1 / 2 - c⁻¹ * |x.ofLp j|) = (1 / 2 - |x.ofLp j| / c) := by
    rw [div_eq_mul_inv]
    ring
  rwa [hhalf] at h0

-- ============ face-slab decay of the product form (dℓ-scale box cutoff) ============

lemma chiSmallDecay_nonneg (M : ℕ) : 0 ≤ chiSmallDecay M := by
  dsimp [chiSmallDecay]
  exact mul_nonneg (chiSmallNormFactor_nonneg M) (pow_nonneg (by norm_num) M)

/-- absolute bound: `|χ_M(z)| ≤ chiSmallDecay M` everywhere. -/
lemma chiSmall_decay_coord_le_decay {M : ℕ} (hM : 1 ≤ M) (z : ℝ³) :
    |chiSmall M z| ≤ chiSmallDecay M := by
  have h0 := chiSmall_decay_coord hM z 0
  let p : ℝ := max (1 / 2 - |z.ofLp 0|) 0
  have hp0 : 0 ≤ p := by dsimp [p]; exact le_max_right _ _
  have hp1 : p ≤ 1 := by
    dsimp [p]
    exact max_le (by linarith [abs_nonneg (z.ofLp 0)]) (by norm_num)
  have hpow : p ^ M ≤ 1 := pow_le_one₀ hp0 hp1
  calc
    |chiSmall M z| ≤ chiSmallDecay M * p ^ M := by
        simpa [p] using h0
    _ ≤ chiSmallDecay M * 1 := mul_le_mul_of_nonneg_left hpow (chiSmallDecay_nonneg M)
    _ = chiSmallDecay M := by ring

/-- `max a b / c = max (a/c) (b/c)` for `0 < c`. -/
lemma max_div_eq_div_max {a b c : ℝ} (hc : 0 < c) :
    max a b / c = max (a / c) (b / c) := by
  by_cases hab : a ≤ b
  · rw [max_eq_right hab, max_eq_right (div_le_div_of_nonneg_right hab (le_of_lt hc))]
  · have hba : b ≤ a := le_of_not_ge hab
    rw [max_eq_left hba, max_eq_left (div_le_div_of_nonneg_right hba (le_of_lt hc))]

/-- **face-slab decay in `c/2 − |x_j|`-form**: `|χ_M(x/c)| ≤ chiSmallDecay
M·((c/2 − |x_j|)₊/c)^M` — the M-th power of the (normalised) distance of the
coordinate `x_j` to the face plane `|x_j| = c/2`. -/
lemma chiSmall_slab_decay {M : ℕ} (hM : 1 ≤ M) {c : ℝ} (hc : 0 < c) (x : ℝ³) (j : Fin 3) :
    |chiSmall M (c⁻¹ • x)| ≤ chiSmallDecay M * (max (c / 2 - |x.ofLp j|) 0 / c) ^ M := by
  have h0 := chiSmall_scale_decay hM hc x j
  have hident : max (1 / 2 - |x.ofLp j| / c) 0 = max (c / 2 - |x.ofLp j|) 0 / c := by
    rw [show max (1 / 2 - |x.ofLp j| / c) 0 = max ((c / 2 - |x.ofLp j|) / c) (0 / c) by
      congr 1
      · field_simp [hc.ne']
      · rw [zero_div]]
    rw [← max_div_eq_div_max hc]
  rwa [hident] at h0

/-- The absolute sup of the corpus bump: `|χ(x)| ≤ chiSupAbs` (`χ = chiBase/√chiNormSq`
with `0 ≤ chiBase ≤ 1`).  This is the *only* quantitative information about the corpus bump
that is available: its explicit formula is hidden behind `Classical.choice` (a `ContDiffBump`
gets its `toFun` from `Nonempty.some`), so **no boundary decay of `χ` is provable** — unlike the
cosine bump `chiSmall M`, whose explicit formula is `(ζζζ)^M`. -/
noncomputable def chiSupAbs : ℝ := (Real.sqrt chiNormSq)⁻¹

lemma chiSupAbs_nonneg : 0 ≤ chiSupAbs := inv_nonneg.mpr (Real.sqrt_nonneg _)

lemma chi_abs_le_sup (x : ℝ³) : |chi x| ≤ chiSupAbs := by
  have hs : 0 < Real.sqrt chiNormSq := Real.sqrt_pos.mpr chiNormSq_pos
  have hb : |chiBase x| ≤ 1 := by
    rw [abs_of_nonneg (chiBase_nonneg x)]
    exact chiBase_le_one x
  have h := div_le_div_of_nonneg_right hb (le_of_lt hs)
  rw [one_div] at h
  have h2 : |chi x| = |chiBase x| / Real.sqrt chiNormSq := by
    rw [chi, abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [h2]
  simpa [chiSupAbs] using h

lemma chiScale_abs_le_sup (ℓ : ℝ) (x : ℝ³) : |chiScale ℓ x| ≤ chiSupAbs :=
  chi_abs_le_sup (ℓ⁻¹ • x)

/-- The repointed bad-band decay constant of the two-factor cutoff:
`chiSupAbs²·(chiSmallDecay M)²·(d⁻¹)^{2M}` — it replaces the corpus `(chiSmallDecay M)⁴`
(the `ℓ`-scale factor is now the corpus bump, whose boundary decay is *not* available, so the
`M`-th-power smallness is supplied by the `ℓd`-scale factor; see `chiSmallB_slab_decay`). -/
noncomputable def chiSmallBandDecay (M : ℕ) (d : ℝ) : ℝ :=
  chiSupAbs ^ 2 * (chiSmallDecay M) ^ 2 * (d⁻¹) ^ (2 * M)

lemma chiSmallBandDecay_nonneg (M : ℕ) {d : ℝ} (hd : 0 < d) : 0 ≤ chiSmallBandDecay M d := by
  refine mul_nonneg (mul_nonneg (pow_nonneg chiSupAbs_nonneg 2)
    (pow_nonneg (chiSmallDecay_nonneg M) 2)) ?_
  exact pow_nonneg (inv_nonneg.mpr (le_of_lt hd)) _

/-- the corpus bump vanishes on the closed complement of the ball of radius `1/2`. -/
lemma chi_eq_zero_of_half_le_norm (x : ℝ³) (hx : 1 / 2 ≤ ‖x‖) : chi x = 0 := by
  have h : chiBump x = 0 :=
    chiBump.zero_of_le_dist (c := 0) (x := x) (by simpa [chiBump, dist_eq_norm] using hx)
  rw [chi, chiBase, h]
  ring

/-- The `dℓ`-scale two-factor small-box cutoff (FS eq:chiBdefinition) **at the repointed
cutoff**: the `ℓ`-scale factor is the *corpus* bump `χ(x/ℓ)` — the same bump the corpus global
word `wPairC ℓ` uses — and the `ℓd`-scale factor is the cosine bump:

    χ_{B(u)}(x) = χ(x/ℓ)·χ_M(x/(ℓd) − u) . -/
noncomputable def chiSmallB (M : ℕ) (ℓ d : ℝ) (u x : ℝ³) : ℝ :=
  chiScale ℓ x * chiSmall M ((ℓ * d)⁻¹ • x - u)

/-- **Face-slab decay of the product form at the repointed cutoff**: the `ℓd`-scale factor
`χ_M(x/(ℓd) − u)` vanishes to order `M` in the distance of the *small-box* coordinate
`(x − (ℓd)u)_j` to the small-box face `|(x − (ℓd)u)_j| = (ℓd)/2`, while the `ℓ`-scale factor
is the corpus bump, bounded only by its absolute sup `chiSupAbs`:

    |χ(x/ℓ)·χ_M(x/(ℓd) − u)| ≤ chiSupAbs · chiSmallDecay M · ((ℓd/2 − |(x−(ℓd)u)_j|)₊/(ℓd))^M .

(The `M`-th-power smallness is supplied by the *small-box* factor: the corpus bump's formula is
inaccessible — see `chiSupAbs` — so the big-box factor carries no decay.) -/
lemma chiSmallB_slab_decay {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (u x : ℝ³) (j : Fin 3) :
    |chiSmallB M ℓ d u x|
      ≤ chiSupAbs * chiSmallDecay M *
        (max (ℓ * d / 2 - |(x - (ℓ * d) • u).ofLp j|) 0 / (ℓ * d)) ^ M := by
  have hc : 0 < ℓ * d := mul_pos hℓ hd
  have hrew : (ℓ * d)⁻¹ • x - u = (ℓ * d)⁻¹ • (x - (ℓ * d) • u) := by
    rw [smul_sub, smul_smul, inv_mul_cancel₀ (ne_of_gt hc), one_smul]
  have hA : |chiScale ℓ x| ≤ chiSupAbs := chiScale_abs_le_sup ℓ x
  have hB : |chiSmall M ((ℓ * d)⁻¹ • x - u)| ≤
      chiSmallDecay M * (max (ℓ * d / 2 - |(x - (ℓ * d) • u).ofLp j|) 0 / (ℓ * d)) ^ M := by
    rw [hrew]
    exact chiSmall_slab_decay hM hc (x - (ℓ * d) • u) j
  have hp0 : 0 ≤ (max (ℓ * d / 2 - |(x - (ℓ * d) • u).ofLp j|) 0 / (ℓ * d)) ^ M :=
    pow_nonneg (div_nonneg (le_max_right _ _) (le_of_lt hc)) M
  calc
    |chiSmallB M ℓ d u x| = |chiScale ℓ x| * |chiSmall M ((ℓ * d)⁻¹ • x - u)| := by
        dsimp [chiSmallB]
        rw [abs_mul]
    _ ≤ chiSupAbs * (chiSmallDecay M *
          (max (ℓ * d / 2 - |(x - (ℓ * d) • u).ofLp j|) 0 / (ℓ * d)) ^ M) :=
        mul_le_mul hA hB (abs_nonneg _) chiSupAbs_nonneg
    _ = chiSupAbs * chiSmallDecay M *
          (max (ℓ * d / 2 - |(x - (ℓ * d) • u).ofLp j|) 0 / (ℓ * d)) ^ M := by ring

/-- **Support of the product in the big box**: `χ_{B(u)}(x) ≠ 0` forces `|x_j| ≤ ℓ/2` — now a
consequence of the *ball* support of the corpus bump (`χ(x/ℓ) ≠ 0 → ‖x‖ < ℓ/2`), which is
strictly sharper than the cube containment of the cosine bump. -/
lemma chiSmallB_support_big_box {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ)
    {u x : ℝ³} (hx : chiSmallB M ℓ d u x ≠ 0) (j : Fin 3) : |x.ofLp j| ≤ ℓ / 2 := by
  have h1 : chiScale ℓ x ≠ 0 := by
    intro h
    exact hx (by dsimp [chiSmallB]; rw [h, zero_mul])
  have h2 : chi (ℓ⁻¹ • x) ≠ 0 := h1
  have hlt : ‖ℓ⁻¹ • x‖ < 1 / 2 := by
    by_contra hcon
    exact h2 (chi_eq_zero_of_half_le_norm _ (le_of_not_gt hcon))
  have hnx : ‖x‖ < ℓ / 2 := by
    have hnorm : ‖ℓ⁻¹ • x‖ = ‖x‖ / ℓ := by
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hℓ, div_eq_inv_mul, mul_comm]
    rw [hnorm] at hlt
    have := (div_lt_iff₀ hℓ).mp hlt
    linarith
  have hcoord : |x.ofLp j| ≤ ‖x‖ := by
    simpa using PiLp.norm_apply_le (p := 2) (β := fun _ : Fin 3 => ℝ) x j
  linarith

/-- support of the product in the small box: `χ_{B(u)}(x) ≠ 0` forces
`|x_j/(ℓd) − u_j| ≤ 1/2` (small-box face containment). -/
lemma chiSmallB_support_small_box {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ}
    {u x : ℝ³} (hx : chiSmallB M ℓ d u x ≠ 0) (j : Fin 3) :
    |((ℓ * d)⁻¹ • x - u).ofLp j| ≤ 1 / 2 := by
  have h2 : chiSmall M ((ℓ * d)⁻¹ • x - u) ≠ 0 := by
    intro h
    apply hx
    dsimp [chiSmallB]
    rw [h]
    simp
  exact chiSmall_support_mem_abs_le hM h2 j

/-- **`chiSmallB` band → face-slab (the twin of
`SlidingSum.chiB_band_support_slab`)**: on the `μ ↦ 4μ` bad band — some
coordinate of `w := (ℓd)•u` reaches
`≥ ½ℓ(1+d) − 2μ^{-1/3}` — the support of the two-factor cutoff lies in the
face-slab of the big box:

    chiSmallB M ℓ d u x ≠ 0  ∧  (∃ j, ½ℓ(1+d) − 2μ^{-1/3} ≤ |w_j|)
        ⟹  ∃ j, ℓ/2 − 2μ^{-1/3} ≤ |x_j| ∧ |x_j| ≤ ℓ/2 .

Route: the two support containments (`chiSmallB_support_big_box`:
`|x_j| ≤ ℓ/2`; `chiSmallB_support_small_box`: `|x_j/(ℓd) − u_j| ≤ 1/2`,
multiplied by `ℓd > 0` giving `|(x−w)_j| ≤ (ℓd)/2`) plus the coordinate
triangle inequality, `nlinarith` closing the algebra
`½ℓ(1+d) − 2μ^{-1/3} − (ℓd)/2 = ℓ/2 − 2μ^{-1/3}`. -/
lemma chiSmallB_band_support_slab {M : ℕ} (hM : 1 ≤ M) {ℓ d μ : ℝ} (hℓ : 0 < ℓ)
    (hd : 0 < d) (u x : ℝ³) (hx : chiSmallB M ℓ d u x ≠ 0)
    (hband : ∃ j : Fin 3,
      (1 / 2) * ℓ * (1 + d) - 2 * μ ^ (-1 / 3 : ℝ) ≤ |((ℓ * d) • u).ofLp j|) :
    ∃ j : Fin 3, ℓ / 2 - 2 * μ ^ (-1 / 3 : ℝ) ≤ |x.ofLp j| ∧ |x.ofLp j| ≤ ℓ / 2 := by
  let w : ℝ³ := (ℓ * d) • u
  rcases hband with ⟨j, hj⟩
  have hbig : |x.ofLp j| ≤ ℓ / 2 := chiSmallB_support_big_box hM hℓ hx j
  have hsmall : |((ℓ * d)⁻¹ • x - u).ofLp j| ≤ 1 / 2 := chiSmallB_support_small_box hM hx j
  have hc : 0 < ℓ * d := mul_pos hℓ hd
  -- convert the small-box support to |(x − w)_j| ≤ (ℓd)/2
  have hco : ((ℓ * d)⁻¹ • x - u).ofLp j = ((x - w).ofLp j) / (ℓ * d) := by
    have hw : w.ofLp j = (ℓ * d) * u.ofLp j := by simp [w]
    have hu : u.ofLp j = w.ofLp j / (ℓ * d) := by
      rw [hw]
      field_simp [mul_ne_zero (ne_of_gt hℓ) (ne_of_gt hd)]
    calc
      ((ℓ * d)⁻¹ • x - u).ofLp j = ((ℓ * d)⁻¹ • x).ofLp j - u.ofLp j := by simp
      _ = (ℓ * d)⁻¹ * x.ofLp j - u.ofLp j := by simp
      _ = (ℓ * d)⁻¹ * x.ofLp j - w.ofLp j / (ℓ * d) := by rw [hu]
      _ = ((x - w).ofLp j) / (ℓ * d) := by
          change (ℓ * d)⁻¹ * x.ofLp j - w.ofLp j / (ℓ * d) =
            (x.ofLp j - w.ofLp j) / (ℓ * d)
          field_simp [mul_ne_zero (ne_of_gt hℓ) (ne_of_gt hd)]
  have hwd : |((x - w).ofLp j)| ≤ (ℓ * d) / 2 := by
    have h1 : |((x - w).ofLp j) / (ℓ * d)| ≤ 1 / 2 := by
      rwa [hco] at hsmall
    calc
      |((x - w).ofLp j)| = (ℓ * d) * |((x - w).ofLp j) / (ℓ * d)| := by
          rw [abs_div, abs_of_nonneg (le_of_lt hc)]
          field_simp [mul_ne_zero (ne_of_gt hℓ) (ne_of_gt hd)]
      _ ≤ (ℓ * d) * (1 / 2) := mul_le_mul_of_nonneg_left h1 (le_of_lt hc)
      _ = (ℓ * d) / 2 := by ring
  -- triangle inequality for coordinate j
  have htri : |w.ofLp j| ≤ |x.ofLp j| + |((x - w).ofLp j)| := by
    calc
      |w.ofLp j| = |x.ofLp j + ((w - x).ofLp j)| := by
          congr 1
          change w.ofLp j = x.ofLp j + (w.ofLp j - x.ofLp j)
          ring
      _ ≤ |x.ofLp j| + |((w - x).ofLp j)| := abs_add_le _ _
      _ = |x.ofLp j| + |((x - w).ofLp j)| := by
          have hco2 : ((w - x).ofLp j) = - ((x - w).ofLp j) := by
            change (w.ofLp j - x.ofLp j) = - (x.ofLp j - w.ofLp j)
            ring
          rw [hco2, abs_neg]
  have hj' : (1 / 2) * ℓ * (1 + d) - 2 * μ ^ (-1 / 3 : ℝ) ≤ |(w.ofLp j)| := by
    simpa [w] using hj
  refine ⟨j, ?_, hbig⟩
  nlinarith [hj', htri, hwd]

-- ============ continuity & compact support of the normalised bump ============

lemma chiSmall_continuous {M : ℕ} (hM : 1 ≤ M) : Continuous (fun z : ℝ³ => chiSmall M z) := by
  have hS : 0 < chiSmallNormSq M := chiSmallNormSq_pos hM
  have hc := chiSmallBase_continuous M
  have hg : Continuous (fun _z : ℝ³ => Real.sqrt (chiSmallNormSq M)) := continuous_const
  have hg0 : ∀ z : ℝ³, Real.sqrt (chiSmallNormSq M) ≠ 0 := fun _ => ne_of_gt (Real.sqrt_pos.mpr hS)
  have hdiv : Continuous (fun z : ℝ³ => chiSmallBase M z / Real.sqrt (chiSmallNormSq M)) := hc.div hg hg0
  simpa [chiSmall] using hdiv

lemma chiSmall_hasCompactSupport {M : ℕ} (hM : 1 ≤ M) : HasCompactSupport (chiSmall M) := by
  have hsqsup : Function.support (chiSmall M) ⊆ Function.support (chiSmallBase M) := by
    intro z hz
    have hz' : chiSmall M z ≠ 0 := Function.mem_support.mp hz
    exact Function.mem_support.mpr (by
      intro hb
      have hS : 0 < chiSmallNormSq M := chiSmallNormSq_pos hM
      apply hz'
      dsimp [chiSmall]
      rw [hb]
      simp)
  exact HasCompactSupport.mono (chiSmallBase_hasCompactSupport hM) hsqsup

/-- the small-box support in the coordinate-distance form: `χ_{B(u)}(x) ≠ 0`
forces `|(x − (ℓd)•u)_j| ≤ (ℓd)/2` for every coordinate. -/
lemma chiSmallB_support_small_box_dist {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ)
    (hd : 0 < d) {u x : ℝ³} (hx : chiSmallB M ℓ d u x ≠ 0) (j : Fin 3) :
    |((x - (ℓ * d) • u).ofLp j)| ≤ (ℓ * d) / 2 := by
  let w : ℝ³ := (ℓ * d) • u
  have hsmall : |((ℓ * d)⁻¹ • x - u).ofLp j| ≤ 1 / 2 := chiSmallB_support_small_box hM hx j
  have hc : 0 < ℓ * d := mul_pos hℓ hd
  have hco : ((ℓ * d)⁻¹ • x - u).ofLp j = ((x - w).ofLp j) / (ℓ * d) := by
    have hw : w.ofLp j = (ℓ * d) * u.ofLp j := by simp [w]
    have hu : u.ofLp j = w.ofLp j / (ℓ * d) := by
      rw [hw]
      field_simp [mul_ne_zero (ne_of_gt hℓ) (ne_of_gt hd)]
    calc
      ((ℓ * d)⁻¹ • x - u).ofLp j = ((ℓ * d)⁻¹ • x).ofLp j - u.ofLp j := by simp
      _ = (ℓ * d)⁻¹ * x.ofLp j - u.ofLp j := by simp
      _ = (ℓ * d)⁻¹ * x.ofLp j - w.ofLp j / (ℓ * d) := by rw [hu]
      _ = ((x - w).ofLp j) / (ℓ * d) := by
          change (ℓ * d)⁻¹ * x.ofLp j - w.ofLp j / (ℓ * d) =
            (x.ofLp j - w.ofLp j) / (ℓ * d)
          field_simp [mul_ne_zero (ne_of_gt hℓ) (ne_of_gt hd)]
  have h1 : |((x - w).ofLp j) / (ℓ * d)| ≤ 1 / 2 := by
    rwa [hco] at hsmall
  calc
    |((x - w).ofLp j)| = (ℓ * d) * |((x - w).ofLp j) / (ℓ * d)| := by
        rw [abs_div, abs_of_nonneg (le_of_lt hc)]
        field_simp [mul_ne_zero (ne_of_gt hℓ) (ne_of_gt hd)]
    _ ≤ (ℓ * d) * (1 / 2) := mul_le_mul_of_nonneg_left h1 (le_of_lt hc)
    _ = (ℓ * d) / 2 := by ring

-- ============ evenness of the cosine-M bump (for the u-partition integrals) ============

lemma chiSmallBase_even (M : ℕ) (z : ℝ³) : chiSmallBase M (-z) = chiSmallBase M z := by
  dsimp [chiSmallBase]
  rw [zeta1d_neg (z.ofLp 0), zeta1d_neg (z.ofLp 1), zeta1d_neg (z.ofLp 2)]

lemma chiSmall_even {M : ℕ} (hM : 1 ≤ M) (z : ℝ³) : chiSmall M (-z) = chiSmall M z := by
  dsimp [chiSmall]
  rw [chiSmallBase_even M z]


-- ============ the corpus bump's convolution: lower bound on the chi-regime ball ============

/-- the corpus bump's self-convolution is bounded below by `1/2` on the ball of radius `ℓ·chiR0`
(`Submission.ChiWitness.chiR0_half`) — the existence of a *positive* lower bound on the
`ℓ`-scale renormalisation denominator is what makes the repointed localised kernels bounded. -/
lemma convScale_ge_half_of_le {ℓ R : ℝ} (hℓ : 0 < ℓ) (hRℓ : R ≤ ℓ * chiR0) {z : ℝ³}
    (hz : ‖z‖ ≤ R) : 1 / 2 ≤ convScale ℓ z := by
  dsimp [convScale]
  refine chiR0_half ((ℓ⁻¹) • z) ?_
  have h1 : ‖(ℓ⁻¹) • z‖ = ℓ⁻¹ * ‖z‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hℓ]
  rw [h1]
  calc
    ℓ⁻¹ * ‖z‖ ≤ ℓ⁻¹ * R := mul_le_mul_of_nonneg_left hz (le_of_lt (inv_pos.mpr hℓ))
    _ ≤ chiR0 := by
        have h := (inv_mul_le_iff₀ hℓ).mpr hRℓ
        simpa [mul_comm] using h

/-- dilation normalisation of the corpus bump: `∫_x χ(x/ℓ)² dx = ℓ³` (from `∫χ² = 1`). -/
lemma integral_chiScale_sq {ℓ : ℝ} (hℓ : 0 < ℓ) :
    (∫ x : ℝ³, (chiScale ℓ x) ^ 2) = ℓ ^ 3 := by
  have h := Measure.integral_comp_inv_smul_of_nonneg (volume : Measure ℝ³)
    (fun z : ℝ³ => (chi z) ^ 2) (R := ℓ) (le_of_lt hℓ)
  rw [show ℓ ^ Module.finrank ℝ ℝ³ = ℓ ^ 3 by rw [finrank_euclideanSpace]; norm_num] at h
  have hpt : (fun x : ℝ³ => (chi ((ℓ⁻¹) • x)) ^ 2) = fun x : ℝ³ => (chiScale ℓ x) ^ 2 := rfl
  rw [hpt] at h
  rw [h, chi_L2]
  ring

/-- the corpus analogue of `integral_chiSmall_sub_sq_eq_one`. -/
lemma integral_chiScale_sub_sq_eq_one {ℓ : ℝ} (hℓ : 0 < ℓ) (a : ℝ³) :
    (∫ u : ℝ³, (chiScale ℓ (a - u)) ^ 2) = ℓ ^ 3 := by
  rw [integral_sub_left_eq_self (fun v : ℝ³ => (chiScale ℓ v) ^ 2) volume a,
    integral_chiScale_sq hℓ]

/-- the reciprocal of the `ℓ`-scale renormalisation denominator is bounded by `2` on the
`chiR0`-regime ball. -/
lemma abs_inv_convScale_le_two {ℓ R : ℝ} (hℓ : 0 < ℓ) (hRℓ : R ≤ ℓ * chiR0) {z : ℝ³}
    (hz : ‖z‖ ≤ R) : |(convScale ℓ z)⁻¹| ≤ 2 := by
  have hh := convScale_ge_half_of_le hℓ hRℓ hz
  have hpos : 0 < convScale ℓ z := lt_of_lt_of_le (by norm_num) hh
  rw [abs_of_nonneg (inv_nonneg.mpr (le_of_lt hpos))]
  calc
    (convScale ℓ z)⁻¹ = 1 / convScale ℓ z := by rw [one_div]
    _ ≤ 1 / (1 / 2 : ℝ) := one_div_le_one_div_of_le (by norm_num) hh
    _ = 2 := by norm_num
end BoseGases

end Submission
