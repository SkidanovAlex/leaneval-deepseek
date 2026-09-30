import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.vk_L_lower
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_zeroFree_offAxis_uniform
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_zeroFree_uniform_realAxis
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_realZero_siegel_uniform
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_norm_half_plane
import Submission.Commons.Analysis.Complex.logDeriv_zeroFree_ball_bound_analytic
import Submission.Work.BMF.LFunction_lower_one_add

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! Guidance from the project lead (the requester):

LEAD NOTE: read Submission/Work/BMF/DESIGN.md 'Addendum: vk_prime_sums detail' (the lead's sub-design
for N10).  REUSE the previous owner's proved modules, and the Commons assets in ASSETS.md; chen's
generic engine `borelCaratheodory_deriv_le`, `jensenCarleman_main` and
`completedL_diskZeroCount_explicit` is reusable for `L(s,χ)`.

Layout of this file (V5 of the N10 sub-design, "low height `|t| ≤ 4`"):

* `lowWidthInv ε a b Cd N` / `lowWidth ε a b Cd N = 1 / lowWidthInv ε a b Cd N` — the zero-free
  half-width in the strip `|Im s| ≤ 6` that is proved here (see `BMF/LowWidth_zero_free`);
  `a` is an off-axis constant, `b` a real-axis constant and `Cd` a Siegel constant for `ε/2`.
* `LFunction_norm_ball_bound` — the crude growth bound `‖L(w,χ)‖ ≤ 28 N` on the balls used.
* `LFunction_logDeriv_lowHeight` — the logarithmic derivative bound, by the
  Borel–Carathéodory ball estimate `logDeriv_zeroFree_ball_bound_analytic` applied to the ball
  centred just above the zero-free boundary.
* `LFunction_lowHeight` — the target. -/

set_option maxHeartbeats 2000000

namespace Work.BMF

/-- The reciprocal of the zero-free half-width: the effective denominator
`2 + log(8N)/a + log(2N)/b + N^{ε/2}/Cd`. -/
noncomputable def lowWidthInv (ε a b Cd : ℝ) (N : ℕ) : ℝ :=
  2 + Real.log (8 * (N : ℝ)) / a + Real.log (2 * (N : ℝ)) / b + (N : ℝ) ^ (ε / 2) / Cd

/-- The zero-free half-width used in this file: for `χ` primitive non-principal mod `N` there are
no zeros of `L(·,χ)` with `|Im s| ≤ 6` and `Re s > 1 - lowWidth ε a b Cd N`.  Written as a
reciprocal so that `1 / lowWidth = lowWidthInv` has a usable (sum) shape. -/
noncomputable def lowWidth (ε a b Cd : ℝ) (N : ℕ) : ℝ := 1 / lowWidthInv ε a b Cd N

lemma one_div_lowWidth (ε a b Cd : ℝ) (N : ℕ) :
    1 / lowWidth ε a b Cd N = lowWidthInv ε a b Cd N := by
  rw [lowWidth, one_div_one_div]

lemma lowWidthInv_pos (ε a b Cd : ℝ) (ha : 0 < a) (hb : 0 < b) (hCd : 0 < Cd)
    (N : ℕ) [NeZero N] : 0 < lowWidthInv ε a b Cd N := by
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have h1 : 0 ≤ Real.log (8 * (N : ℝ)) := le_of_lt (Real.log_pos (by linarith))
  have h2 : 0 ≤ Real.log (2 * (N : ℝ)) := le_of_lt (Real.log_pos (by linarith))
  have h3 : 0 ≤ (N : ℝ) ^ (ε / 2) := Real.rpow_nonneg (by linarith) _
  have h4 : 0 ≤ Real.log (8 * (N : ℝ)) / a := div_nonneg h1 ha.le
  have h5 : 0 ≤ Real.log (2 * (N : ℝ)) / b := div_nonneg h2 hb.le
  have h6 : 0 ≤ (N : ℝ) ^ (ε / 2) / Cd := div_nonneg h3 hCd.le
  simp only [lowWidthInv]
  linarith

lemma lowWidthInv_ge_two (ε a b Cd : ℝ) (ha : 0 < a) (hb : 0 < b) (hCd : 0 < Cd)
    (N : ℕ) [NeZero N] : 2 ≤ lowWidthInv ε a b Cd N := by
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have h1 : 0 ≤ Real.log (8 * (N : ℝ)) := le_of_lt (Real.log_pos (by linarith))
  have h2 : 0 ≤ Real.log (2 * (N : ℝ)) := le_of_lt (Real.log_pos (by linarith))
  have h3 : 0 ≤ (N : ℝ) ^ (ε / 2) := Real.rpow_nonneg (by linarith) _
  have h4 : 0 ≤ Real.log (8 * (N : ℝ)) / a := div_nonneg h1 ha.le
  have h5 : 0 ≤ Real.log (2 * (N : ℝ)) / b := div_nonneg h2 hb.le
  have h6 : 0 ≤ (N : ℝ) ^ (ε / 2) / Cd := div_nonneg h3 hCd.le
  simp only [lowWidthInv]
  linarith

lemma lowWidth_pos (ε a b Cd : ℝ) (ha : 0 < a) (hb : 0 < b) (hCd : 0 < Cd)
    (N : ℕ) [NeZero N] : 0 < lowWidth ε a b Cd N :=
  one_div_pos.mpr (lowWidthInv_pos ε a b Cd ha hb hCd N)

lemma lowWidth_le_half (ε a b Cd : ℝ) (ha : 0 < a) (hb : 0 < b) (hCd : 0 < Cd)
    (N : ℕ) [NeZero N] : lowWidth ε a b Cd N ≤ 1 / 2 := by
  have hD := lowWidthInv_pos ε a b Cd ha hb hCd N
  have h2 := lowWidthInv_ge_two ε a b Cd ha hb hCd N
  rw [lowWidth, div_le_iff₀ hD]
  linarith


/-- `lowWidth ≤ a / log (8N)`, the off-axis half-width at height `6`. -/
lemma lowWidth_le_log8_div_a_sub (ε a b Cd : ℝ) (ha : 0 < a) (hb : 0 < b) (hCd : 0 < Cd)
    (N : ℕ) [NeZero N] : lowWidth ε a b Cd N ≤ a / Real.log (8 * (N : ℝ)) := by
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hlog8 : 0 < Real.log (8 * (N : ℝ)) := Real.log_pos (by linarith)
  have hlog2 : 0 ≤ Real.log (2 * (N : ℝ)) := le_of_lt (Real.log_pos (by linarith))
  have hrpow : 0 ≤ (N : ℝ) ^ (ε / 2) := Real.rpow_nonneg (by positivity) _
  have h2 : 0 ≤ Real.log (2 * (N : ℝ)) / b := div_nonneg hlog2 hb.le
  have h3 : 0 ≤ (N : ℝ) ^ (ε / 2) / Cd := div_nonneg hrpow hCd.le
  have hle : Real.log (8 * (N : ℝ)) / a ≤ lowWidthInv ε a b Cd N := by
    simp only [lowWidthInv]; linarith
  have hpos : 0 < Real.log (8 * (N : ℝ)) / a := div_pos hlog8 ha
  calc lowWidth ε a b Cd N = 1 / lowWidthInv ε a b Cd N := rfl
    _ ≤ 1 / (Real.log (8 * (N : ℝ)) / a) := one_div_le_one_div_of_le hpos hle
    _ = a / Real.log (8 * (N : ℝ)) := one_div_div _ _

/-- `lowWidth ≤ b / log (2N)`, the real-axis half-width. -/
lemma lowWidth_le_log2_div_b_sub (ε a b Cd : ℝ) (ha : 0 < a) (hb : 0 < b) (hCd : 0 < Cd)
    (N : ℕ) [NeZero N] : lowWidth ε a b Cd N ≤ b / Real.log (2 * (N : ℝ)) := by
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hlog8 : 0 ≤ Real.log (8 * (N : ℝ)) := le_of_lt (Real.log_pos (by linarith))
  have hlog2 : 0 < Real.log (2 * (N : ℝ)) := Real.log_pos (by linarith)
  have hrpow : 0 ≤ (N : ℝ) ^ (ε / 2) := Real.rpow_nonneg (by positivity) _
  have h1 : 0 ≤ Real.log (8 * (N : ℝ)) / a := div_nonneg hlog8 ha.le
  have h3 : 0 ≤ (N : ℝ) ^ (ε / 2) / Cd := div_nonneg hrpow hCd.le
  have hle : Real.log (2 * (N : ℝ)) / b ≤ lowWidthInv ε a b Cd N := by
    simp only [lowWidthInv]; linarith
  have hpos : 0 < Real.log (2 * (N : ℝ)) / b := div_pos hlog2 hb
  calc lowWidth ε a b Cd N = 1 / lowWidthInv ε a b Cd N := rfl
    _ ≤ 1 / (Real.log (2 * (N : ℝ)) / b) := one_div_le_one_div_of_le hpos hle
    _ = b / Real.log (2 * (N : ℝ)) := one_div_div _ _

/-- `lowWidth ≤ Cd * N^{-ε/2}`, the Siegel half-width. -/
lemma lowWidth_le_Cd_rpow_sub (ε a b Cd : ℝ) (ha : 0 < a) (hb : 0 < b) (hCd : 0 < Cd)
    (N : ℕ) [NeZero N] : lowWidth ε a b Cd N ≤ Cd * (N : ℝ) ^ (-(ε / 2)) := by
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hlog8 : 0 ≤ Real.log (8 * (N : ℝ)) := le_of_lt (Real.log_pos (by linarith))
  have hlog2 : 0 ≤ Real.log (2 * (N : ℝ)) := le_of_lt (Real.log_pos (by linarith))
  have h1 : 0 ≤ Real.log (8 * (N : ℝ)) / a := div_nonneg hlog8 ha.le
  have h2 : 0 ≤ Real.log (2 * (N : ℝ)) / b := div_nonneg hlog2 hb.le
  have hle : (N : ℝ) ^ (ε / 2) / Cd ≤ lowWidthInv ε a b Cd N := by
    simp only [lowWidthInv]; linarith
  have hrpow : 0 < (N : ℝ) ^ (ε / 2) := Real.rpow_pos_of_pos hNpos _
  calc lowWidth ε a b Cd N = 1 / lowWidthInv ε a b Cd N := rfl
    _ ≤ 1 / ((N : ℝ) ^ (ε / 2) / Cd) := one_div_le_one_div_of_le (div_pos hrpow hCd) hle
    _ = Cd / (N : ℝ) ^ (ε / 2) := one_div_div _ _
    _ = Cd * (N : ℝ) ^ (-(ε / 2)) := by rw [Real.rpow_neg hNpos.le]; ring

/-- **Zero-free half-width for `L(·,χ)` in the bounded strip `|Im s| ≤ 6`.**
Let `a > 0` be a valid off-axis constant (`LFunction_zeroFree_offAxis_uniform`), `b > 0` a valid
real-axis constant (`LFunction_zeroFree_uniform_realAxis`) and `Cd > 0` a valid Siegel constant for
`ε/2` (`LFunction_realZero_siegel_uniform`), all fed in as hypotheses.  Then for `χ` primitive and
non-principal modulo `N` every zero `ρ` of `L(·,χ)` with `|Im ρ| ≤ 6` satisfies
`Re ρ ≤ 1 - lowWidth ε a b Cd N`, where `lowWidth = 1 / (2 + log(8N)/a + log(2N)/b + N^{ε/2}/Cd)`
(see `Work.BMF.lowWidth` in `Submission/Work/BMF/LFunction_lowHeight.lean`).

Proof sketch (elementary case analysis, no analysis): if `Im ρ ≠ 0` use the off-axis hypothesis with
`t = Im ρ`, noting `log (N (|t|+2)) ≤ log (8N)`; if `Im ρ = 0` then either `1 ≤ Re ρ` (contradiction
with non-vanishing on `Re ≥ 1`, `LFunction_ne_zero_of_one_le_re`), or `Re ρ < 1` and `χ*χ ≠ 1` (use
the real-axis hypothesis), or `χ*χ = 1` (Siegel: a zero in `Re > 1 - lowWidth` would give
`1 - ρ.re < lowWidth ≤ Cd N^{-ε/2} ≤ 1 - ρ.re`).  The bounds `lowWidth ≤ 1/2`,
`lowWidth ≤ a/log(8N)`, `lowWidth ≤ b/log(2N)`, `lowWidth ≤ Cd N^{-ε/2}` all follow from
`lowWidth = 1/lowWidthInv` with `lowWidthInv = 2 + log(8N)/a + log(2N)/b + N^{ε/2}/Cd`. -/
theorem lowWidth_zero_free_sub (ε a b Cd : ℝ) (ha : 0 < a) (hb : 0 < b) (hCd : 0 < Cd)
    (hOff : ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → χ ≠ 1 →
      ∀ σ t : ℝ, t ≠ 0 → 1 - a / Real.log ((N : ℝ) * (|t| + 2)) ≤ σ →
      DirichletCharacter.LFunction χ ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0)
    (hReal : ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → χ ≠ 1 →
      χ * χ ≠ 1 → ∀ σ : ℝ, 1 - b / Real.log (2 * (N : ℝ)) ≤ σ →
      DirichletCharacter.LFunction χ (σ : ℂ) ≠ 0)
    (hSieg : ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → χ ≠ 1 →
      χ * χ = 1 → ∀ β : ℝ, 0 < β → β < 1 → DirichletCharacter.LFunction χ (β : ℂ) = 0 →
      Cd * (N : ℝ) ^ (-(ε / 2)) ≤ 1 - β) :
    ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → χ ≠ 1 → ∀ ρ : ℂ,
      DirichletCharacter.LFunction χ ρ = 0 → |ρ.im| ≤ 6 → ρ.re ≤ 1 - lowWidth ε a b Cd N := by
  intro N hN χ hprim hχne ρ hzero him
  -- Suppose for contradiction that `ρ` lies to the right of `1 - lowWidth`.
  by_contra hcon
  push Not at hcon
  have hwhalf := lowWidth_le_half ε a b Cd ha hb hCd N
  -- hence `0 < ρ.re`.
  have hre_pos : 0 < ρ.re := by linarith
  by_cases him0 : ρ.im = 0
  · -- real zero
    have hρ : ρ = (ρ.re : ℂ) := by
      rw [← Complex.re_add_im ρ, him0]; simp
    have hzero' : DirichletCharacter.LFunction χ (ρ.re : ℂ) = 0 := by
      rw [← hρ]; exact hzero
    by_cases hge : (1 : ℝ) ≤ ρ.re
    · -- non-vanishing on `Re s ≥ 1`
      exact (DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχne) (s := ρ) hge) hzero
    · push Not at hge
      by_cases hsq : χ * χ = 1
      · -- Siegel zero
        have hs := hSieg χ hprim hχne hsq ρ.re hre_pos hge hzero'
        have hw := lowWidth_le_Cd_rpow_sub ε a b Cd ha hb hCd N
        linarith
      · -- real-axis (non-quadratic) zero-free region
        have hr := hReal χ hprim hχne hsq ρ.re (by
          have hw := lowWidth_le_log2_div_b_sub ε a b Cd ha hb hCd N
          linarith)
        exact hr hzero'
  · -- off-axis zero: `Im ρ ≠ 0`, use the off-axis region at height `|Im ρ| ≤ 6`
    have himne : ρ.im ≠ 0 := him0
    have hNpos : 0 < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
    have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
    -- `N (|Im ρ| + 2) ≤ 8 N`, and both sides are `> 1`
    have hle_abs : |ρ.im| + 2 ≤ 8 := by linarith
    have hmul : (N : ℝ) * (|ρ.im| + 2) ≤ 8 * (N : ℝ) := by
      have := mul_le_mul_of_nonneg_left hle_abs hNpos.le
      linarith
    have hpos1 : 0 < (N : ℝ) * (|ρ.im| + 2) := mul_pos hNpos (by linarith [abs_nonneg ρ.im])
    have hlogmono : Real.log ((N : ℝ) * (|ρ.im| + 2)) ≤ Real.log (8 * (N : ℝ)) :=
      Real.log_le_log hpos1 hmul
    have hlogpos : 0 < Real.log ((N : ℝ) * (|ρ.im| + 2)) := by
      refine Real.log_pos ?_
      have h2 : (1 : ℝ) * (|ρ.im| + 2) ≤ (N : ℝ) * (|ρ.im| + 2) :=
        mul_le_mul_of_nonneg_right hN1 (by linarith [abs_nonneg ρ.im])
      linarith [abs_nonneg ρ.im]
    -- `lowWidth ≤ a / log (N (|Im ρ| + 2))`
    have hwa := lowWidth_le_log8_div_a_sub ε a b Cd ha hb hCd N
    have hstep : a / Real.log (8 * (N : ℝ)) ≤ a / Real.log ((N : ℝ) * (|ρ.im| + 2)) :=
      div_le_div_of_nonneg_left ha.le hlogpos hlogmono
    have hσ : 1 - a / Real.log ((N : ℝ) * (|ρ.im| + 2)) ≤ ρ.re := by linarith
    have hoff := hOff χ hprim hχne ρ.re ρ.im himne hσ
    rw [Complex.re_add_im ρ] at hoff
    exact hoff hzero


/-! ## Two elementary bounds on `lowWidthInv`

These are the two real-variable ingredients of `LowWidth_arith`:
* `lowWidthInv_le_scale`: `lowWidthInv ε a b Cd N ≤ C₁ (N^{ε/2} + log(N+2))`;
* `log_two_lowWidthInv_le`: `log (2 * lowWidthInv ε a b Cd N) ≤ C₂ log(N+2)`.

Both are proved here directly (constants `2 + 2/a + 2/b + 1/Cd` and `max(ε/2,1) + log C₀/log 3`
respectively). -/

/-- `lowWidthInv` is bounded by a constant multiple of `N^{ε/2} + log(N+2)`. -/
lemma lowWidthInv_le_scale_sub (ε a b Cd : ℝ) (hε : 0 < ε) (ha : 0 < a) (hb : 0 < b)
    (hCd : 0 < Cd) :
    ∃ C1 : ℝ, 0 < C1 ∧ ∀ (N : ℕ) [NeZero N],
      lowWidthInv ε a b Cd N ≤ C1 * ((N : ℝ) ^ (ε / 2) + Real.log ((N : ℝ) + 2)) := by
  refine ⟨2 + 2/a + 2/b + 1/Cd, ?_, ?_⟩
  · have h1 : 0 < 2/a := by positivity
    have h2 : 0 < 2/b := by positivity
    have h3 : 0 < 1/Cd := by positivity
    linarith
  · intro N hNe
    have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hNe.out
    set L : ℝ := Real.log ((N:ℝ)+2) with hLdef
    have hLpos : 0 < L := by rw [hLdef]; exact Real.log_pos (by linarith)
    have hL0 : 0 ≤ L := hLpos.le
    have hx1 : 1 ≤ (N:ℝ)^(ε/2) := Real.one_le_rpow hN1 (by linarith)
    have hlog8 : Real.log (8*(N:ℝ)) ≤ 2*L := by
      have hle : 8*(N:ℝ) ≤ ((N:ℝ)+2)^2 := by nlinarith [sq_nonneg ((N:ℝ) - 2)]
      calc Real.log (8*(N:ℝ)) ≤ Real.log (((N:ℝ)+2)^2) := Real.log_le_log (by linarith) hle
        _ = 2*L := by rw [Real.log_pow, ← hLdef]; push_cast; ring
    have hlog2 : Real.log (2*(N:ℝ)) ≤ 2*L := by
      have hle : 2*(N:ℝ) ≤ ((N:ℝ)+2)^2 := by nlinarith [sq_nonneg ((N:ℝ) + 1)]
      calc Real.log (2*(N:ℝ)) ≤ Real.log (((N:ℝ)+2)^2) := Real.log_le_log (by linarith) hle
        _ = 2*L := by rw [Real.log_pow, ← hLdef]; push_cast; ring
    have h1 : Real.log (8*(N:ℝ))/a ≤ (2/a)*L := by
      have := div_le_div_of_nonneg_right hlog8 ha.le
      rwa [show (2*L)/a = (2/a)*L by ring] at this
    have h2 : Real.log (2*(N:ℝ))/b ≤ (2/b)*L := by
      have := div_le_div_of_nonneg_right hlog2 hb.le
      rwa [show (2*L)/b = (2/b)*L by ring] at this
    have h3 : (N:ℝ)^(ε/2)/Cd ≤ (1/Cd)*((N:ℝ)^(ε/2)) := by
      rw [show (1/Cd)*((N:ℝ)^(ε/2)) = (N:ℝ)^(ε/2)/Cd by ring]
    have h2x : 2 ≤ 2*(N:ℝ)^(ε/2) := by linarith
    have hx0 : 0 ≤ (N:ℝ)^(ε/2) := le_trans zero_le_one hx1
    have hA : 0 ≤ 2/a := by positivity
    have hB : 0 ≤ 2/b := by positivity
    have hC : 0 ≤ 1/Cd := by positivity
    rw [lowWidthInv]
    nlinarith [h1, h2, h3, h2x, hL0, hx0, hA, hB, hC]

/-- `log (2 * lowWidthInv ε a b Cd N)` is bounded by a constant multiple of `log(N+2)`. -/
lemma log_two_lowWidthInv_le_sub (ε a b Cd : ℝ) (hε : 0 < ε) (ha : 0 < a) (hb : 0 < b)
    (hCd : 0 < Cd) :
    ∃ C2 : ℝ, 0 < C2 ∧ ∀ (N : ℕ) [NeZero N],
      Real.log (2 * lowWidthInv ε a b Cd N) ≤ C2 * Real.log ((N : ℝ) + 2) := by
  set M0 : ℝ := max (ε/2) 1 with hM0def
  have hM0ge1 : 1 ≤ M0 := by rw [hM0def]; exact le_max_right _ _
  have hM0nn : 0 ≤ M0 := le_trans zero_le_one hM0ge1
  set C0 : ℝ := 4 + 4/a + 4/b + 2/Cd with hC0def
  have hC0gt1 : 1 < C0 := by
    rw [hC0def]
    have h1 : 0 < 4/a := by positivity
    have h2 : 0 < 4/b := by positivity
    have h3 : 0 < 2/Cd := by positivity
    linarith
  have hC0pos : 0 < C0 := lt_trans zero_lt_one hC0gt1
  have hlogC0 : 0 < Real.log C0 := Real.log_pos hC0gt1
  refine ⟨M0 + Real.log C0 / Real.log 3, ?_, ?_⟩
  · have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
    have h1 : 0 ≤ Real.log C0 / Real.log 3 := div_nonneg hlogC0.le h3.le
    linarith
  · intro N hNe
    have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hNe.out
    have hNpos : 0 < (N:ℝ) := by linarith
    set L : ℝ := Real.log ((N:ℝ)+2) with hLdef
    have hLpos : 0 < L := by rw [hLdef]; exact Real.log_pos (by linarith)
    have hL0 : 0 ≤ L := hLpos.le
    have hL3 : Real.log 3 ≤ L := by
      rw [hLdef]; exact Real.log_le_log (by norm_num : (0:ℝ) < 3) (by linarith)
    set M : ℝ := ((N:ℝ)+2)^M0 with hMdef
    have hbase1 : 1 ≤ (N:ℝ)+2 := by linarith
    have hMge1 : 1 ≤ M := by rw [hMdef]; exact Real.one_le_rpow hbase1 hM0nn
    have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hMge1
    have hlog8 : Real.log (8*(N:ℝ)) ≤ 2*L := by
      have hle : 8*(N:ℝ) ≤ ((N:ℝ)+2)^2 := by nlinarith [sq_nonneg ((N:ℝ) - 2)]
      calc Real.log (8*(N:ℝ)) ≤ Real.log (((N:ℝ)+2)^2) := Real.log_le_log (by linarith) hle
        _ = 2*L := by rw [Real.log_pow, ← hLdef]; push_cast; ring
    have hlog2 : Real.log (2*(N:ℝ)) ≤ 2*L := by
      have hle : 2*(N:ℝ) ≤ ((N:ℝ)+2)^2 := by nlinarith [sq_nonneg ((N:ℝ) + 1)]
      calc Real.log (2*(N:ℝ)) ≤ Real.log (((N:ℝ)+2)^2) := Real.log_le_log (by linarith) hle
        _ = 2*L := by rw [Real.log_pow, ← hLdef]; push_cast; ring
    have hLM : L ≤ M := by
      have h := Real.log_le_self (by linarith : (0:ℝ) ≤ (N:ℝ)+2)
      rw [hLdef]
      have h2 : (N:ℝ)+2 ≤ M := by
        rw [hMdef]
        have hh := Real.rpow_le_rpow_of_exponent_le hbase1 hM0ge1
        rwa [Real.rpow_one] at hh
      linarith
    have hxM : (N:ℝ)^(ε/2) ≤ M := by
      have h1 : (N:ℝ)^(ε/2) ≤ ((N:ℝ)+2)^(ε/2) :=
        Real.rpow_le_rpow (by linarith) (by linarith) (by linarith)
      have h2 : ((N:ℝ)+2)^(ε/2) ≤ ((N:ℝ)+2)^M0 :=
        Real.rpow_le_rpow_of_exponent_le hbase1 (le_max_left _ _)
      rw [hMdef]; linarith
    have h2D : 2 * lowWidthInv ε a b Cd N ≤ C0 * M := by
      have hl8M : Real.log (8*(N:ℝ)) ≤ 2*M := by linarith [hlog8, hLM]
      have hl2M : Real.log (2*(N:ℝ)) ≤ 2*M := by linarith [hlog2, hLM]
      have h1 : 2 * (Real.log (8*(N:ℝ))/a) ≤ (4/a)*M := by
        have h := div_le_div_of_nonneg_right hl8M ha.le
        have h' : 2 * (Real.log (8*(N:ℝ))/a) ≤ 2 * ((2*M)/a) := by linarith
        have hd : 2 * ((2*M)/a) = (4/a)*M := by ring
        linarith
      have h2 : 2 * (Real.log (2*(N:ℝ))/b) ≤ (4/b)*M := by
        have h := div_le_div_of_nonneg_right hl2M hb.le
        have h' : 2 * (Real.log (2*(N:ℝ))/b) ≤ 2 * ((2*M)/b) := by linarith
        have hd : 2 * ((2*M)/b) = (4/b)*M := by ring
        linarith
      have h3 : 2 * ((N:ℝ)^(ε/2)/Cd) ≤ (2/Cd)*M := by
        have h := div_le_div_of_nonneg_right hxM hCd.le
        have h' : 2 * ((N:ℝ)^(ε/2)/Cd) ≤ 2 * (M/Cd) := by linarith
        have hd : 2 * (M/Cd) = (2/Cd)*M := by ring
        linarith
      have h4 : 4 ≤ 4*M := by linarith
      have hsum : 4*M + (4/a)*M + (4/b)*M + (2/Cd)*M = (4 + 4/a + 4/b + 2/Cd)*M := by ring
      have hlow : 2 * lowWidthInv ε a b Cd N
          = 4 + 2*(Real.log (8*(N:ℝ))/a) + 2*(Real.log (2*(N:ℝ))/b)
            + 2*((N:ℝ)^(ε/2)/Cd) := by
        rw [lowWidthInv]; ring
      rw [hlow, hC0def]
      linarith [h1, h2, h3, h4, hsum]
    have hDpos : 0 < lowWidthInv ε a b Cd N := lowWidthInv_pos ε a b Cd ha hb hCd N
    have hlog2D : Real.log (2 * lowWidthInv ε a b Cd N) ≤ Real.log (C0*M) :=
      Real.log_le_log (by linarith) h2D
    have hCM : Real.log (C0 * M) = Real.log C0 + M0 * L := by
      rw [Real.log_mul (ne_of_gt hC0pos) (ne_of_gt hMpos)]
      have : Real.log M = M0 * L := by
        rw [hMdef, Real.log_rpow (by linarith : (0:ℝ) < (N:ℝ)+2), hLdef]
      rw [this]
    have hcmp : Real.log C0 ≤ (Real.log C0 / Real.log 3) * L := by
      have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
      have hpos : 0 ≤ Real.log C0 / Real.log 3 := div_nonneg hlogC0.le h3.le
      calc Real.log C0 = (Real.log C0 / Real.log 3) * Real.log 3 := by field_simp
        _ ≤ (Real.log C0 / Real.log 3) * L := mul_le_mul_of_nonneg_left hL3 hpos
    linarith [hlog2D, hCM, hcmp]

/-- **The real-arithmetic step of the low-height log-derivative bound.**
For `ε > 0`, `a, b, Cd > 0` there is `K > 0` such that for every `N ≥ 1` and every real `B` with
`B ≤ 80 * (log (56N) + log (2 * lowWidthInv ε a b Cd N))` one has
`B * lowWidthInv ε a b Cd N ≤ K * (N^ε + log(N+2)^2)`.

Here `lowWidthInv ε a b Cd N = 2 + log(8N)/a + log(2N)/b + N^{ε/2}/Cd` (`Work.BMF.lowWidthInv`, in
`Submission/Work/BMF/LFunction_lowHeight.lean`).  This is a pure `ℝ`-arithmetic estimate:
`lowWidthInv ≤ (3 + 2/a + 2/b + 1/Cd)·(N^{ε/2} + log(N+2))`,
`log(2·lowWidthInv) ≤ C(ε,a,b,Cd)·log(N+2)`, and `N^{ε/2} log(N+2) ≤ C(ε) N^ε` (from
`log y ≤ y`, i.e. `log(N+2) ≤ (2/ε)(N+2)^{ε/2}`, plus `(N+2)^{ε/2} ≤ 2^{ε/2}N^{ε/2}` for `N ≥ 2`
and a separate elementary bound for the small-`N` cases). -/
theorem lowWidth_arith_sub (ε a b Cd : ℝ) (hε : 0 < ε) (ha : 0 < a) (hb : 0 < b) (hCd : 0 < Cd) :
    ∃ K : ℝ, 0 < K ∧ ∀ (N : ℕ) [NeZero N] (B : ℝ),
      B ≤ 80 * (Real.log (56 * (N : ℝ)) + Real.log (2 * lowWidthInv ε a b Cd N)) →
      B * lowWidthInv ε a b Cd N ≤ K * ((N : ℝ) ^ ε + Real.log ((N : ℝ) + 2) ^ 2) := by
  obtain ⟨C1, hC1pos, hC1⟩ := lowWidthInv_le_scale_sub ε a b Cd hε ha hb hCd
  obtain ⟨C2, hC2pos, hC2⟩ := log_two_lowWidthInv_le_sub ε a b Cd hε ha hb hCd
  refine ⟨80 * C1 * (C2 + (Real.log 56 / Real.log 3 + 1)) * (3 / 2), ?_, ?_⟩
  · positivity
  · intro N hNe B hB
    have hNpos : (0:ℝ) < (N:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hNe.out
    have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hNe.out
    set L : ℝ := Real.log ((N:ℝ) + 2) with hLdef
    set D : ℝ := lowWidthInv ε a b Cd N with hDdef
    have hLpos : 0 < L := by rw [hLdef]; exact Real.log_pos (by linarith)
    have hL0 : 0 ≤ L := hLpos.le
    have hL3 : Real.log 3 ≤ L := by
      rw [hLdef]; exact Real.log_le_log (by norm_num : (0:ℝ) < 3) (by linarith)
    have hDpos : 0 < D := by rw [hDdef]; exact lowWidthInv_pos ε a b Cd ha hb hCd N
    have hD0 : 0 ≤ D := hDpos.le
    -- the two bounds supplied by the auxiliary lemmas
    have hC1N : D ≤ C1 * ((N:ℝ)^(ε/2) + L) := by
      have := hC1 N; rw [← hDdef, ← hLdef] at this; exact this
    have hC2N : Real.log (2*D) ≤ C2 * L := by
      have := hC2 N; rw [← hDdef, ← hLdef] at this; exact this
    -- `log (56 N) ≤ (log 56 / log 3 + 1) * L`
    have hC3N : Real.log (56*(N:ℝ)) ≤ (Real.log 56 / Real.log 3 + 1) * L := by
      have hlogmul : Real.log (56*(N:ℝ)) = Real.log 56 + Real.log (N:ℝ) :=
        Real.log_mul (by norm_num) (by exact_mod_cast hNe.out)
      have hlogN : Real.log (N:ℝ) ≤ L := by
        rw [hLdef]; exact Real.log_le_log hNpos (by linarith)
      have h1 : Real.log 56 ≤ (Real.log 56 / Real.log 3) * L := by
        have hpos : 0 < Real.log 56 / Real.log 3 := by positivity
        calc Real.log 56 = (Real.log 56 / Real.log 3) * Real.log 3 := by field_simp
          _ ≤ (Real.log 56 / Real.log 3) * L := mul_le_mul_of_nonneg_left hL3 hpos.le
      linarith [hlogmul, h1, hlogN]
    -- `N^ε = (N^{ε/2})^2`
    have hxsq : (N:ℝ)^ε = ((N:ℝ)^(ε/2))^2 := by
      have h := Real.rpow_mul hNpos.le (ε/2) (2:ℝ)
      rw [Real.rpow_two] at h
      rw [show ε / 2 * 2 = ε by ring] at h
      exact h
    -- AM–GM: `L * N^{ε/2} ≤ (N^ε + L^2)/2`
    have hE : L * (N:ℝ)^(ε/2) + L^2 ≤ ((N:ℝ)^ε + L^2)/2 + L^2 := by
      nlinarith [sq_nonneg (L - (N:ℝ)^(ε/2)), hxsq]
    have hA : B * D ≤ 80 * (Real.log (56*(N:ℝ)) + Real.log (2*D)) * D := by
      have := mul_le_mul_of_nonneg_right hB hD0; linarith
    have hB2 : 80 * (Real.log (56*(N:ℝ)) + Real.log (2*D)) * D
        ≤ 80 * ((Real.log 56/Real.log 3 + 1)*L + C2*L) * D := by
      have hle : Real.log (56*(N:ℝ)) + Real.log (2*D) ≤ (Real.log 56/Real.log 3 + 1)*L + C2*L := by
        linarith [hC3N, hC2N]
      have h1 : 80 * (Real.log (56*(N:ℝ)) + Real.log (2*D))
          ≤ 80 * ((Real.log 56/Real.log 3 + 1)*L + C2*L) := by linarith
      exact mul_le_mul_of_nonneg_right h1 hD0
    have hC2' : 80 * ((Real.log 56/Real.log 3 + 1)*L + C2*L) * D
        ≤ 80 * ((Real.log 56/Real.log 3 + 1)*L + C2*L) * (C1*((N:ℝ)^(ε/2)+L)) := by
      have hnn : 0 ≤ 80 * ((Real.log 56/Real.log 3 + 1)*L + C2*L) := by
        have h1 : 0 ≤ (Real.log 56/Real.log 3 + 1)*L := mul_nonneg (by positivity) hL0
        have h2 : 0 ≤ C2*L := mul_nonneg hC2pos.le hL0
        nlinarith
      exact mul_le_mul_of_nonneg_left hC1N hnn
    have hD2 : 80 * ((Real.log 56/Real.log 3 + 1)*L + C2*L) * (C1*((N:ℝ)^(ε/2)+L))
        = 80 * C1 * (C2 + (Real.log 56/Real.log 3 + 1)) * (L*(N:ℝ)^(ε/2) + L^2) := by ring
    have hF : 80 * C1 * (C2 + (Real.log 56/Real.log 3 + 1)) * (L*(N:ℝ)^(ε/2)+L^2)
        ≤ 80 * C1 * (C2 + (Real.log 56/Real.log 3 + 1)) * (((N:ℝ)^ε+L^2)/2 + L^2) := by
      have hnn : 0 ≤ 80 * C1 * (C2 + (Real.log 56/Real.log 3 + 1)) := by positivity
      exact mul_le_mul_of_nonneg_left hE hnn
    have hG : 80 * C1 * (C2 + (Real.log 56/Real.log 3 + 1)) * (((N:ℝ)^ε+L^2)/2 + L^2)
        ≤ 80 * C1 * (C2 + (Real.log 56/Real.log 3 + 1)) * (3/2) * ((N:ℝ)^ε + L^2) := by
      have hnn : 0 ≤ 80 * C1 * (C2 + (Real.log 56/Real.log 3 + 1)) := by positivity
      have h32 : ((N:ℝ)^ε+L^2)/2 + L^2 ≤ (3/2)*((N:ℝ)^ε+L^2) := by
        have hNe0 : 0 ≤ (N:ℝ)^ε := Real.rpow_nonneg hNpos.le _
        nlinarith
      nlinarith [mul_le_mul_of_nonneg_left h32 hnn]
    linarith [hA, hB2, hC2', hD2.le, hD2.ge, hF, hG]

/-- Crude growth bound for `L(·,χ)` on the balls used below: `‖L(w,χ)‖ ≤ 28 N` whenever
`1/2 ≤ Re w` and `‖w‖ ≤ 7` (so `M := 28N` in the Borel–Carathéodory estimate). -/
lemma LFunction_norm_ball_bound {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    {w : ℂ} (hre : 1 / 2 ≤ w.re) (hn : ‖w‖ ≤ 7) :
    ‖DirichletCharacter.LFunction χ w‖ ≤ 28 * (N : ℝ) := by
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := by positivity
  have hpos : 0 < w.re := lt_of_lt_of_le (by norm_num) hre
  have h1 := Commons.NumberTheory.DirichletCharacter.LFunction_norm_half_plane χ hχ hpos
  have h2 : 2 * (N : ℝ) * ‖w‖ / w.re ≤ 28 * (N : ℝ) := by
    rw [div_le_iff₀ hpos]
    nlinarith [norm_nonneg w, hN0]
  linarith

lemma norm_ofReal_eq_abs (r : ℝ) : ‖((r : ℝ) : ℂ)‖ = |r| := by
  have h : ‖((r : ℝ) : ℂ)‖ ^ 2 = r ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]; ring
  calc ‖((r : ℝ) : ℂ)‖ = Real.sqrt (‖((r : ℝ) : ℂ)‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ = Real.sqrt (r ^ 2) := by rw [h]
    _ = |r| := Real.sqrt_sq_eq_abs r

theorem LFunction_logDeriv_lowHeight (ε a b Cd : ℝ) (hε : 0 < ε) (ha : 0 < a) (hb : 0 < b)
    (hCd : 0 < Cd)
    (hwide : ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → χ ≠ 1 → ∀ ρ : ℂ,
      DirichletCharacter.LFunction χ ρ = 0 → |ρ.im| ≤ 6 → ρ.re ≤ 1 - lowWidth ε a b Cd N)
    (c : ℝ) (hc : 0 < c)
    (hcW : ∀ (N : ℕ) [NeZero N], c * (N : ℝ) ^ (-ε) ≤ lowWidth ε a b Cd N / 2) :
    ∃ K : ℝ, 0 < K ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
      χ.IsPrimitive → χ ≠ 1 → ∀ σ t : ℝ, |t| ≤ 4 →
        1 - c * (N : ℝ) ^ (-ε) ≤ σ → σ ≤ 2 →
        ‖logDeriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
          K * ((N : ℝ) ^ ε + Real.log ((N : ℝ) + 2) ^ 2) := by
  obtain ⟨Kar, hKarpos, hArith⟩ := lowWidth_arith_sub ε a b Cd hε ha hb hCd
  refine ⟨Kar, hKarpos, ?_⟩
  intro N hN χ hprim hχne σ t ht hσlo hσhi
  set W : ℝ := lowWidth ε a b Cd N with hWdef
  have hWpos : 0 < W := by rw [hWdef]; exact lowWidth_pos ε a b Cd ha hb hCd N
  have hWhalf : W ≤ 1 / 2 := by rw [hWdef]; exact lowWidth_le_half ε a b Cd ha hb hCd N
  have hDpos : 0 < lowWidthInv ε a b Cd N := lowWidthInv_pos ε a b Cd ha hb hCd N
  have hinvW : 1 / W = lowWidthInv ε a b Cd N := by rw [hWdef]; exact one_div_lowWidth ε a b Cd N
  have hcW' : c * (N : ℝ) ^ (-ε) ≤ W / 2 := by rw [hWdef]; exact hcW N
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hzf : ∀ ρ : ℂ, DirichletCharacter.LFunction χ ρ = 0 → |ρ.im| ≤ 6 → ρ.re ≤ 1 - W := by
    intro ρ hz him
    rw [hWdef]; exact hwide N χ hprim hχne ρ hz him
  have hσlow2 : 1 - W / 2 ≤ σ := by linarith
  have hCnn : 0 ≤ Real.log (56 * (N : ℝ)) + Real.log (2 * lowWidthInv ε a b Cd N) := by
    have h1 : 0 ≤ Real.log (56 * (N : ℝ)) := Real.log_nonneg (by linarith)
    have h2 : 0 ≤ Real.log (2 * lowWidthInv ε a b Cd N) :=
      Real.log_nonneg (by have := lowWidthInv_ge_two ε a b Cd ha hb hCd N; linarith)
    linarith
  have hCeq : Real.log (2 * (28 * (N : ℝ))) - Real.log (W / 2)
      = Real.log (56 * (N : ℝ)) + Real.log (2 * lowWidthInv ε a b Cd N) := by
    have hlogarg : Real.log (2 * (28 * (N : ℝ))) = Real.log (56 * (N : ℝ)) := by
      congr 1; ring
    have hW2 : W / 2 = (2 * lowWidthInv ε a b Cd N)⁻¹ := by
      have hWinv : W = (lowWidthInv ε a b Cd N)⁻¹ := by rw [← hinvW, one_div, inv_inv]
      rw [hWinv, div_eq_mul_inv, mul_comm, ← mul_inv]
    have hlogW : Real.log (W / 2) = -Real.log (2 * lowWidthInv ε a b Cd N) := by
      rw [hW2, Real.log_inv]
    rw [hlogarg, hlogW]; ring
  have hkey : ‖logDeriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      80 * (Real.log (56 * (N : ℝ)) + Real.log (2 * lowWidthInv ε a b Cd N)) *
        lowWidthInv ε a b Cd N := by
    by_cases hcase : σ ≤ 1 + W
    · -- centre `1 + W + it`
      set c₀ : ℂ := ((1 + W : ℝ) : ℂ) + (t : ℂ) * Complex.I with hc₀def
      set R : ℝ := 2 * W with hRdef
      have hRpos : 0 < R := by rw [hRdef]; linarith
      set s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I with hsdef
      have hdist : ‖s - c₀‖ = 1 + W - σ := by
        have h1 : s - c₀ = ((σ - (1 + W) : ℝ) : ℂ) := by
          apply Complex.ext <;> simp [hsdef, hc₀def]
        rw [h1, norm_ofReal_eq_abs, abs_of_nonpos (by linarith)]
        ring
      have hmem : s ∈ Metric.ball c₀ R := by
        rw [Metric.mem_ball, dist_eq_norm, hdist, hRdef]; linarith
      have hrew : ∀ w : ℂ, w ∈ Metric.ball c₀ R → 1 - W < w.re := by
        intro w hw
        have hwd : ‖w - c₀‖ < R := by simpa [Metric.mem_ball, dist_eq_norm] using hw
        have h1 : |(w - c₀).re| ≤ ‖w - c₀‖ := Complex.abs_re_le_norm _
        have h2 : (w - c₀).re = w.re - (1 + W) := by simp [hc₀def]
        rw [h2] at h1
        have h3 : -(w.re - (1 + W)) < R := by
          have h4 := neg_le_abs (w.re - (1 + W))
          linarith
        rw [hRdef] at h3; linarith
      have himw : ∀ w : ℂ, w ∈ Metric.ball c₀ R → |w.im| ≤ 5 := by
        intro w hw
        have hwd : ‖w - c₀‖ < R := by simpa [Metric.mem_ball, dist_eq_norm] using hw
        have h1 : |(w - c₀).im| ≤ ‖w - c₀‖ := Complex.abs_im_le_norm _
        have h2 : (w - c₀).im = w.im - t := by simp [hc₀def]
        rw [h2] at h1
        have h3 : |w.im| ≤ |t| + R := by
          have h4 := abs_sub_abs_le_abs_sub w.im t
          linarith
        rw [hRdef] at h3
        linarith [(abs_le.mp ht).2]
      have hball_ne : ∀ w : ℂ, w ∈ Metric.ball c₀ R → DirichletCharacter.LFunction χ w ≠ 0 := by
        intro w hw hzero
        have h2 := hzf w hzero (by have := himw w hw; linarith)
        have h3 := hrew w hw
        linarith
      have hball_M : ∀ w : ℂ, w ∈ Metric.ball c₀ R →
          ‖DirichletCharacter.LFunction χ w‖ ≤ 28 * (N : ℝ) := by
        intro w hw
        have hre := hrew w hw
        have him := himw w hw
        have hwd : ‖w - c₀‖ < R := by simpa [Metric.mem_ball, dist_eq_norm] using hw
        have hup : w.re ≤ 5 / 2 := by
          have h1 : |(w - c₀).re| ≤ ‖w - c₀‖ := Complex.abs_re_le_norm _
          have h2 : (w - c₀).re = w.re - (1 + W) := by simp [hc₀def]
          rw [h2] at h1
          have h3 : w.re - (1 + W) ≤ R := by
            have h4 := le_abs_self (w.re - (1 + W))
            linarith
          rw [hRdef] at h3; linarith
        have h1 : 1 / 2 ≤ w.re := by linarith
        have h2 : ‖w‖ ≤ 7 := by
          have hsq : ‖w‖ ^ 2 ≤ 49 := by
            rw [Complex.sq_norm, Complex.normSq_apply]
            nlinarith [abs_le.mp him]
          nlinarith [norm_nonneg w]
        exact LFunction_norm_ball_bound χ hχne h1 h2
      have hcenter : W / 2 ≤ ‖DirichletCharacter.LFunction χ c₀‖ := by
        have h := LFunction_lower_one_add χ hχne W t hWpos (by linarith)
        simpa [hc₀def] using h
      have hana : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) (Metric.ball c₀ R) :=
        ((DirichletCharacter.differentiable_LFunction hχne).differentiableOn).analyticOnNhd
          Metric.isOpen_ball
      set g : ℝ := R - ‖s - c₀‖ with hgdef
      have hgg : W / 2 ≤ g := by rw [hgdef, hdist, hRdef]; linarith
      set ρ : ℝ := g / 2 with hρdef
      have hρpos : 0 < ρ := by rw [hρdef]; linarith
      have hρlt : ρ < R - ‖s - c₀‖ := by rw [hρdef, hgdef]; linarith
      have hballb := Commons.Analysis.Complex.logDeriv_zeroFree_ball_bound_analytic hRpos
        (by linarith : 0 < W / 2) (by linarith : W / 2 ≤ 28 * (N : ℝ)) hana hball_ne hball_M
        hcenter hmem ρ hρpos hρlt
      rw [logDeriv_apply]
      refine le_trans hballb ?_
      rw [hCeq]
      have hnum : ‖s - c₀‖ + ρ ≤ 5 * W / 2 := by
        rw [hρdef, hgdef, hdist, hRdef]
        linarith
      have hden_eq : (R - ‖s - c₀‖ - ρ) * ρ = g ^ 2 / 4 := by
        rw [hρdef, hgdef]; ring
      have hdenpos : 0 < (R - ‖s - c₀‖ - ρ) * ρ := by
        rw [hden_eq]; nlinarith [hgg, hWpos]
      have hden : W ^ 2 / 16 ≤ (R - ‖s - c₀‖ - ρ) * ρ := by
        rw [hden_eq]; nlinarith
      have hfrac : (‖s - c₀‖ + ρ) / ((R - ‖s - c₀‖ - ρ) * ρ) ≤
          40 * lowWidthInv ε a b Cd N := by
        have hstep : (‖s - c₀‖ + ρ) / ((R - ‖s - c₀‖ - ρ) * ρ) ≤ (5 * W / 2) / (W ^ 2 / 16) :=
          div_le_div₀ (by linarith : (0:ℝ) ≤ 5 * W / 2) hnum
            (by positivity : (0:ℝ) < W ^ 2 / 16) hden
        have hval : (5 * W / 2) / (W ^ 2 / 16) = 40 / W := by
          field_simp; ring
        rw [hval] at hstep
        have h2 : 40 / W = 40 * lowWidthInv ε a b Cd N := by
          rw [← hinvW]; field_simp
        linarith [hstep, h2.le]
      calc 2 * (Real.log (56 * (N : ℝ)) + Real.log (2 * lowWidthInv ε a b Cd N)) *
            (‖s - c₀‖ + ρ) / ((R - ‖s - c₀‖ - ρ) * ρ)
          = 2 * (Real.log (56 * (N : ℝ)) + Real.log (2 * lowWidthInv ε a b Cd N)) *
            ((‖s - c₀‖ + ρ) / ((R - ‖s - c₀‖ - ρ) * ρ)) := by ring
        _ ≤ 2 * (Real.log (56 * (N : ℝ)) + Real.log (2 * lowWidthInv ε a b Cd N)) *
              (40 * lowWidthInv ε a b Cd N) :=
              mul_le_mul_of_nonneg_left hfrac (by linarith)
        _ = 80 * (Real.log (56 * (N : ℝ)) + Real.log (2 * lowWidthInv ε a b Cd N)) *
              lowWidthInv ε a b Cd N := by ring
    · push Not at hcase
      set s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I with hsdef
      set R : ℝ := W with hRdef
      have hRpos : 0 < R := by rw [hRdef]; exact hWpos
      have hrew : ∀ w : ℂ, w ∈ Metric.ball s R → 1 < w.re := by
        intro w hw
        have hwd : ‖w - s‖ < R := by simpa [Metric.mem_ball, dist_eq_norm] using hw
        have h1 : |(w - s).re| ≤ ‖w - s‖ := Complex.abs_re_le_norm _
        have h2 : (w - s).re = w.re - σ := by simp [hsdef]
        rw [h2] at h1
        have h3 : -(w.re - σ) < R := by
          have h4 := neg_le_abs (w.re - σ)
          linarith
        rw [hRdef] at h3; linarith
      have himw : ∀ w : ℂ, w ∈ Metric.ball s R → |w.im| ≤ 5 := by
        intro w hw
        have hwd : ‖w - s‖ < R := by simpa [Metric.mem_ball, dist_eq_norm] using hw
        have h1 : |(w - s).im| ≤ ‖w - s‖ := Complex.abs_im_le_norm _
        have h2 : (w - s).im = w.im - t := by simp [hsdef]
        rw [h2] at h1
        have h3 : |w.im| ≤ |t| + R := by
          have h4 := abs_sub_abs_le_abs_sub w.im t
          linarith
        rw [hRdef] at h3
        linarith [(abs_le.mp ht).2]
      have hball_ne : ∀ w : ℂ, w ∈ Metric.ball s R → DirichletCharacter.LFunction χ w ≠ 0 := by
        intro w hw
        exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχne)
          (by have := hrew w hw; linarith)
      have hball_M : ∀ w : ℂ, w ∈ Metric.ball s R →
          ‖DirichletCharacter.LFunction χ w‖ ≤ 28 * (N : ℝ) := by
        intro w hw
        have hre := hrew w hw
        have him := himw w hw
        have hwd : ‖w - s‖ < R := by simpa [Metric.mem_ball, dist_eq_norm] using hw
        have hup : w.re ≤ 5 / 2 := by
          have h1 : |(w - s).re| ≤ ‖w - s‖ := Complex.abs_re_le_norm _
          have h2 : (w - s).re = w.re - σ := by simp [hsdef]
          rw [h2] at h1
          have h3 : w.re - σ ≤ R := by
            have h4 := le_abs_self (w.re - σ)
            linarith
          rw [hRdef] at h3; linarith
        have h1 : 1 / 2 ≤ w.re := by linarith
        have h2 : ‖w‖ ≤ 7 := by
          have hsq : ‖w‖ ^ 2 ≤ 49 := by
            rw [Complex.sq_norm, Complex.normSq_apply]
            nlinarith [abs_le.mp him]
          nlinarith [norm_nonneg w]
        exact LFunction_norm_ball_bound χ hχne h1 h2
      have hcenter : W / 2 ≤ ‖DirichletCharacter.LFunction χ s‖ := by
        have h := LFunction_lower_one_add χ hχne (σ - 1) t (by linarith) (by linarith)
        have h1 : (1 : ℝ) + (σ - 1) = σ := by ring
        rw [h1] at h
        have h2 : W ≤ σ - 1 := by linarith
        linarith
      have hana : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) (Metric.ball s R) :=
        ((DirichletCharacter.differentiable_LFunction hχne).differentiableOn).analyticOnNhd
          Metric.isOpen_ball
      set ρ : ℝ := W / 2 with hρdef
      have hρpos : 0 < ρ := by rw [hρdef]; linarith
      have hρlt : ρ < R - ‖s - s‖ := by rw [hρdef, hRdef, sub_self, norm_zero]; linarith
      have hballb := Commons.Analysis.Complex.logDeriv_zeroFree_ball_bound_analytic hRpos
        (by linarith : 0 < W / 2) (by linarith : W / 2 ≤ 28 * (N : ℝ)) hana hball_ne hball_M
        hcenter (Metric.mem_ball_self hRpos) ρ hρpos hρlt
      rw [logDeriv_apply]
      refine le_trans hballb ?_
      rw [hCeq]
      have hWne : W ≠ 0 := ne_of_gt hWpos
      have hfrac : (‖s - s‖ + ρ) / ((R - ‖s - s‖ - ρ) * ρ) ≤
          4 * lowWidthInv ε a b Cd N := by
        have h2 : (‖s - s‖ + ρ) / ((R - ‖s - s‖ - ρ) * ρ) = 2 * (1 / W) := by
          rw [sub_self, norm_zero, hρdef, hRdef]
          field_simp
          rw [show 0 * 2 + W = W by ring, show 2 * (W - 0) - W = W by ring, div_self hWne]
        rw [h2, hinvW]
        have hD1 : (1 : ℝ) ≤ lowWidthInv ε a b Cd N :=
          le_trans (by norm_num) (lowWidthInv_ge_two ε a b Cd ha hb hCd N)
        linarith
      calc 2 * (Real.log (56 * (N : ℝ)) + Real.log (2 * lowWidthInv ε a b Cd N)) *
            (‖s - s‖ + ρ) / ((R - ‖s - s‖ - ρ) * ρ)
          = 2 * (Real.log (56 * (N : ℝ)) + Real.log (2 * lowWidthInv ε a b Cd N)) *
            ((‖s - s‖ + ρ) / ((R - ‖s - s‖ - ρ) * ρ)) := by ring
        _ ≤ 2 * (Real.log (56 * (N : ℝ)) + Real.log (2 * lowWidthInv ε a b Cd N)) *
              (4 * lowWidthInv ε a b Cd N) :=
              mul_le_mul_of_nonneg_left hfrac (by linarith)
        _ = 8 * (Real.log (56 * (N : ℝ)) + Real.log (2 * lowWidthInv ε a b Cd N)) *
              lowWidthInv ε a b Cd N := by ring
        _ ≤ 80 * (Real.log (56 * (N : ℝ)) + Real.log (2 * lowWidthInv ε a b Cd N)) *
              lowWidthInv ε a b Cd N := by nlinarith [hCnn]
  exact le_trans hkey (hArith N (80 * (Real.log (56 * (N : ℝ)) + Real.log (2 * lowWidthInv ε a b Cd N))) le_rfl)

/-- **The constant comparison `c * N^{-ε} ≤ lowWidth / 2`.**  With
`c ≤ min (1/16) (min (εa/(8·8^ε)) (min (εb/(8·2^ε)) (Cd/8)))` one has
`2 (c N^{-ε}) (2 + log(8N)/a + log(2N)/b + N^{ε/2}/Cd) ≤ 1` for every `N ≥ 1`. -/
lemma lowHeight_cW_sub (ε a b Cd c : ℝ) (hε : 0 < ε) (ha : 0 < a) (hb : 0 < b) (hCd : 0 < Cd)
    (hc1 : c ≤ 1 / 16) (hc2 : c ≤ ε * a / (8 * 8 ^ ε)) (hc3 : c ≤ ε * b / (8 * 2 ^ ε))
    (hc4 : c ≤ Cd / 8) :
    ∀ (N : ℕ) [NeZero N],
      2 * (c * (N : ℝ) ^ (-ε)) *
        (2 + Real.log (8 * (N : ℝ)) / a + Real.log (2 * (N : ℝ)) / b + (N : ℝ) ^ (ε / 2) / Cd)
        ≤ 1 := by
  intro N hN
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hlog8nn : 0 ≤ Real.log (8 * (N : ℝ)) := Real.log_nonneg (by linarith)
  have hlog2nn : 0 ≤ Real.log (2 * (N : ℝ)) := Real.log_nonneg (by linarith)
  have hrpnn : 0 ≤ (N : ℝ) ^ (ε / 2) := Real.rpow_nonneg hNpos.le _
  have hD2 : (0 : ℝ) < 2 + Real.log (8 * (N : ℝ)) / a + Real.log (2 * (N : ℝ)) / b +
      (N : ℝ) ^ (ε / 2) / Cd := by
    have h1 : 0 ≤ Real.log (8 * (N : ℝ)) / a := div_nonneg hlog8nn ha.le
    have h2 : 0 ≤ Real.log (2 * (N : ℝ)) / b := div_nonneg hlog2nn hb.le
    have h3 : 0 ≤ (N : ℝ) ^ (ε / 2) / Cd := div_nonneg hrpnn hCd.le
    linarith
  by_cases hc0 : 0 ≤ c
  · have hNne : (N : ℝ) ^ (-ε) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
    have hNne2 : (N : ℝ) ^ (-(ε / 2)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
    have hNmul : (N : ℝ) ^ (-ε) * (N : ℝ) ^ ε = 1 := by
      have h := (Real.rpow_add hNpos (-ε) ε).symm
      rw [show -ε + ε = 0 by ring, Real.rpow_zero] at h
      exact h
    have hNmul2 : (N : ℝ) ^ (-ε) * (N : ℝ) ^ (ε / 2) = (N : ℝ) ^ (-(ε / 2)) := by
      rw [← Real.rpow_add hNpos]
      congr 1
      ring
    have hT1 : 2 * (c * (N : ℝ) ^ (-ε)) * 2 ≤ 1 / 4 := by
      have h0 : 4 * c * (N : ℝ) ^ (-ε) ≤ 4 * c := by nlinarith [hNne, hc0]
      nlinarith [h0, hc1]
    have hlog8 : ε * Real.log (8 * (N : ℝ)) ≤ 8 ^ ε * (N : ℝ) ^ ε := by
      have h1 : Real.log ((8 * (N : ℝ)) ^ ε) ≤ (8 * (N : ℝ)) ^ ε :=
        Real.log_le_self (by positivity)
      rw [Real.log_rpow (by linarith : (0 : ℝ) < 8 * (N : ℝ)) ε,
        Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 8) hNpos.le] at h1
      exact h1
    have hlog2 : ε * Real.log (2 * (N : ℝ)) ≤ 2 ^ ε * (N : ℝ) ^ ε := by
      have h1 : Real.log ((2 * (N : ℝ)) ^ ε) ≤ (2 * (N : ℝ)) ^ ε :=
        Real.log_le_self (by positivity)
      rw [Real.log_rpow (by linarith : (0 : ℝ) < 2 * (N : ℝ)) ε,
        Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hNpos.le] at h1
      exact h1
    have hT2 : 2 * (c * (N : ℝ) ^ (-ε)) * (Real.log (8 * (N : ℝ)) / a) ≤ 1 / 4 := by
      have hlog : Real.log (8 * (N : ℝ)) ≤ 8 ^ ε * (N : ℝ) ^ ε / ε := by
        rw [le_div_iff₀ hε]; linarith
      have h1 : (N : ℝ) ^ (-ε) * Real.log (8 * (N : ℝ)) ≤ 8 ^ ε / ε := by
        have h2 : (N : ℝ) ^ (-ε) * Real.log (8 * (N : ℝ)) ≤
            (N : ℝ) ^ (-ε) * (8 ^ ε * (N : ℝ) ^ ε / ε) :=
          mul_le_mul_of_nonneg_left hlog (Real.rpow_nonneg hNpos.le _)
        have h3 : (N : ℝ) ^ (-ε) * (8 ^ ε * (N : ℝ) ^ ε / ε) = 8 ^ ε / ε := by
          rw [show (N : ℝ) ^ (-ε) * (8 ^ ε * (N : ℝ) ^ ε / ε) =
            ((N : ℝ) ^ (-ε) * (N : ℝ) ^ ε) * (8 ^ ε / ε) by ring, hNmul, one_mul]
        linarith [h2, h3.le, h3.ge]
      calc 2 * (c * (N : ℝ) ^ (-ε)) * (Real.log (8 * (N : ℝ)) / a)
          = (2 * c / a) * ((N : ℝ) ^ (-ε) * Real.log (8 * (N : ℝ))) := by ring
        _ ≤ (2 * c / a) * (8 ^ ε / ε) := by
            exact mul_le_mul_of_nonneg_left h1 (div_nonneg (by linarith) ha.le)
        _ = 2 * c * 8 ^ ε / (ε * a) := by ring
        _ ≤ 2 * (ε * a / (8 * 8 ^ ε)) * 8 ^ ε / (ε * a) := by
            have h5 : 2 * c * 8 ^ ε ≤ 2 * (ε * a / (8 * 8 ^ ε)) * 8 ^ ε := by
              have h6 : c * 8 ^ ε ≤ (ε * a / (8 * 8 ^ ε)) * 8 ^ ε :=
                mul_le_mul_of_nonneg_right hc2 (by positivity)
              linarith
            exact div_le_div_of_nonneg_right h5 (by positivity)
        _ = 1 / 4 := by field_simp; ring
    have hT3 : 2 * (c * (N : ℝ) ^ (-ε)) * (Real.log (2 * (N : ℝ)) / b) ≤ 1 / 4 := by
      have hlog : Real.log (2 * (N : ℝ)) ≤ 2 ^ ε * (N : ℝ) ^ ε / ε := by
        rw [le_div_iff₀ hε]; linarith
      have h1 : (N : ℝ) ^ (-ε) * Real.log (2 * (N : ℝ)) ≤ 2 ^ ε / ε := by
        have h2 : (N : ℝ) ^ (-ε) * Real.log (2 * (N : ℝ)) ≤
            (N : ℝ) ^ (-ε) * (2 ^ ε * (N : ℝ) ^ ε / ε) :=
          mul_le_mul_of_nonneg_left hlog (Real.rpow_nonneg hNpos.le _)
        have h3 : (N : ℝ) ^ (-ε) * (2 ^ ε * (N : ℝ) ^ ε / ε) = 2 ^ ε / ε := by
          rw [show (N : ℝ) ^ (-ε) * (2 ^ ε * (N : ℝ) ^ ε / ε) =
            ((N : ℝ) ^ (-ε) * (N : ℝ) ^ ε) * (2 ^ ε / ε) by ring, hNmul, one_mul]
        linarith [h2, h3.le, h3.ge]
      calc 2 * (c * (N : ℝ) ^ (-ε)) * (Real.log (2 * (N : ℝ)) / b)
          = (2 * c / b) * ((N : ℝ) ^ (-ε) * Real.log (2 * (N : ℝ))) := by ring
        _ ≤ (2 * c / b) * (2 ^ ε / ε) := by
            exact mul_le_mul_of_nonneg_left h1 (div_nonneg (by linarith) hb.le)
        _ = 2 * c * 2 ^ ε / (ε * b) := by ring
        _ ≤ 2 * (ε * b / (8 * 2 ^ ε)) * 2 ^ ε / (ε * b) := by
            have h5 : 2 * c * 2 ^ ε ≤ 2 * (ε * b / (8 * 2 ^ ε)) * 2 ^ ε := by
              have h6 : c * 2 ^ ε ≤ (ε * b / (8 * 2 ^ ε)) * 2 ^ ε :=
                mul_le_mul_of_nonneg_right hc3 (by positivity)
              linarith
            exact div_le_div_of_nonneg_right h5 (by positivity)
        _ = 1 / 4 := by field_simp; ring
    have hT4 : 2 * (c * (N : ℝ) ^ (-ε)) * ((N : ℝ) ^ (ε / 2) / Cd) ≤ 1 / 4 := by
      have h1 : (N : ℝ) ^ (-ε) * (N : ℝ) ^ (ε / 2) ≤ 1 := by
        rw [hNmul2]; exact hNne2
      have h2 : 2 * (c * (N : ℝ) ^ (-ε)) * ((N : ℝ) ^ (ε / 2) / Cd)
          = (2 * c / Cd) * ((N : ℝ) ^ (-ε) * (N : ℝ) ^ (ε / 2)) := by ring
      rw [h2]
      have h3 : (2 * c / Cd) * ((N : ℝ) ^ (-ε) * (N : ℝ) ^ (ε / 2)) ≤ (2 * c / Cd) * 1 :=
        mul_le_mul_of_nonneg_left h1 (div_nonneg (by linarith) hCd.le)
      have h4 : 2 * c / Cd ≤ 2 * (Cd / 8) / Cd := by
        exact div_le_div_of_nonneg_right (by linarith) hCd.le
      have h5 : 2 * (Cd / 8) / Cd = 1 / 4 := by field_simp; ring
      linarith [h3, h4, h5.le, h5.ge]
    have hexp : 2 * (c * (N : ℝ) ^ (-ε)) *
        (2 + Real.log (8 * (N : ℝ)) / a + Real.log (2 * (N : ℝ)) / b + (N : ℝ) ^ (ε / 2) / Cd)
        = 2 * (c * (N : ℝ) ^ (-ε)) * 2 +
          2 * (c * (N : ℝ) ^ (-ε)) * (Real.log (8 * (N : ℝ)) / a) +
          2 * (c * (N : ℝ) ^ (-ε)) * (Real.log (2 * (N : ℝ)) / b) +
          2 * (c * (N : ℝ) ^ (-ε)) * ((N : ℝ) ^ (ε / 2) / Cd) := by ring
    rw [hexp]
    linarith [hT1, hT2, hT3, hT4]
  · push Not at hc0
    have h1 : c * (N : ℝ) ^ (-ε) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hc0.le (Real.rpow_nonneg hNpos.le _)
    have h2 : 2 * (c * (N : ℝ) ^ (-ε)) *
        (2 + Real.log (8 * (N : ℝ)) / a + Real.log (2 * (N : ℝ)) / b + (N : ℝ) ^ (ε / 2) / Cd)
        ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) hD2.le
    linarith

/-- **V5. Low heights `|t| ≤ 4`: classical `q`-aspect region with Siegel.** For every `ε > 0`
(ineffective constants): if `χ ≠ 1` is primitive mod `N`, `|t| ≤ 4` and
`σ ∈ [1 − c N^{-ε}, 2]`, then `L(σ+it, χ) ≠ 0` and `‖L'/L‖ ≤ C (N^ε + log²(N+2))`.
Uses the owned `LFunction_zeroFree_offAxis_uniform`, `LFunction_zeroFree_uniform_realAxis` and
`LFunction_realZero_siegel_uniform`, plus the chen Borel–Carathéodory / Jensen template. -/
theorem LFunction_lowHeight (ε : ℝ) (hε : 0 < ε) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
      χ.IsPrimitive → χ ≠ 1 → ∀ σ t : ℝ, |t| ≤ 4 →
        1 - c * (N : ℝ) ^ (-ε) ≤ σ → σ ≤ 2 →
        DirichletCharacter.LFunction χ ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 ∧
        ‖logDeriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
          C * ((N : ℝ) ^ ε + Real.log ((N : ℝ) + 2) ^ 2) := by
  obtain ⟨a, ha, hOff⟩ :=
    Commons.NumberTheory.DirichletCharacter.LFunction_zeroFree_offAxis_uniform
  obtain ⟨b, hb, hReal⟩ :=
    Commons.NumberTheory.DirichletCharacter.LFunction_zeroFree_uniform_realAxis
  obtain ⟨Cd, hCd, hSieg⟩ :=
    Commons.NumberTheory.DirichletCharacter.LFunction_realZero_siegel_uniform (ε / 2)
      (by linarith)
  set c : ℝ := min (1 / 16)
    (min (ε * a / (8 * 8 ^ ε)) (min (ε * b / (8 * 2 ^ ε)) (Cd / 8))) with hcdef
  have hcpos : 0 < c := by
    rw [hcdef]
    exact lt_min (by norm_num)
      (lt_min (div_pos (mul_pos hε ha) (by positivity))
        (lt_min (div_pos (mul_pos hε hb) (by positivity)) (by positivity)))
  have hc1 : c ≤ 1 / 16 := by rw [hcdef]; exact min_le_left _ _
  have hc2 : c ≤ ε * a / (8 * 8 ^ ε) := by
    rw [hcdef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hc3 : c ≤ ε * b / (8 * 2 ^ ε) := by
    rw [hcdef]; exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hc4 : c ≤ Cd / 8 := by
    rw [hcdef]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  have hReal' : ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → χ ≠ 1 →
      χ * χ ≠ 1 → ∀ σ : ℝ, 1 - b / Real.log (2 * (N : ℝ)) ≤ σ →
      DirichletCharacter.LFunction χ (σ : ℂ) ≠ 0 :=
    fun {N} _inst χ h1 h2 h3 σ h4 => hReal N χ h1 h2 h3 σ h4
  have hSieg' : ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → χ ≠ 1 →
      χ * χ = 1 → ∀ β : ℝ, 0 < β → β < 1 → DirichletCharacter.LFunction χ (β : ℂ) = 0 →
      Cd * (N : ℝ) ^ (-(ε / 2)) ≤ 1 - β :=
    fun {N} _inst χ h1 h2 h3 β h4 h5 h6 => hSieg N χ h1 h2 h3 β h4 h5 h6
  have hOff' : ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → χ ≠ 1 →
      ∀ σ t : ℝ, t ≠ 0 → 1 - a / Real.log ((N : ℝ) * (|t| + 2)) ≤ σ →
      DirichletCharacter.LFunction χ ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 :=
    fun {N} _inst χ h1 h2 σ t h3 h4 => hOff χ h1 h2 σ t h3 h4
  have hwide := lowWidth_zero_free_sub ε a b Cd ha hb hCd hOff' hReal' hSieg'
  have hcW : ∀ (N : ℕ) [NeZero N], c * (N : ℝ) ^ (-ε) ≤ lowWidth ε a b Cd N / 2 := by
    intro N hN
    have hDpos : 0 < lowWidthInv ε a b Cd N := lowWidthInv_pos ε a b Cd ha hb hCd N
    have hmain : 2 * (c * (N : ℝ) ^ (-ε)) * lowWidthInv ε a b Cd N ≤ 1 := by
      have h := lowHeight_cW_sub ε a b Cd c hε ha hb hCd hc1 hc2 hc3 hc4 N
      simpa only [lowWidthInv] using h
    rw [lowWidth, le_div_iff₀ (by norm_num : (0 : ℝ) < 2), le_div_iff₀ hDpos]
    linarith [hmain]
  obtain ⟨C, hCpos, hbound⟩ :=
    LFunction_logDeriv_lowHeight ε a b Cd hε ha hb hCd hwide c hcpos hcW
  refine ⟨C, c, hCpos, hcpos, ?_⟩
  intro N hN χ hprim hχne σ t ht hσlo hσhi
  refine ⟨?_, hbound N χ hprim hχne σ t ht hσlo hσhi⟩
  have hWpos : 0 < lowWidth ε a b Cd N := lowWidth_pos ε a b Cd ha hb hCd N
  have hle : c * (N : ℝ) ^ (-ε) ≤ lowWidth ε a b Cd N / 2 := hcW N
  have him : |(((σ : ℂ) + (t : ℂ) * Complex.I)).im| ≤ 6 := by
    have h : (((σ : ℂ) + (t : ℂ) * Complex.I)).im = t := by simp
    rw [h]; linarith [(abs_le.mp ht).2]
  intro hzero
  have h0 := hwide N χ hprim hχne ((σ : ℂ) + (t : ℂ) * Complex.I) hzero him
  have hre : (((σ : ℂ) + (t : ℂ) * Complex.I)).re = σ := by simp
  rw [hre] at h0
  linarith

end Work.BMF
