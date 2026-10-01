/-
# The uniform zero-free region: the input that ties the Deuring--Heilbronn repulsion to reality

This module defines the **zero-free region** that the formalisation of the
Benli--Goel--Twiss--Zaman repulsion (see `Submission/Work/LinnikAreas/BGTZSetup.lean` and
`Submission/Work/LinnikAreas/BGTZ/`) takes as its input, in the two forms in which it is used:

* `Work.LinnikAreas.BGTZ.ZFRInput cZ` — the form in terms of the contract's `zeroMult` (zeros of
  the *completed* `L`-functions of the primitive characters inducing the characters mod `q`);
  this is the form consumed by the modified high-zero bound
  (`Work.LinnikAreas.BGTZ.RestHighBGTZGen`), where the zeros below the exceptional one's `λ` must
  be excluded by a zero-free region rather than by the repulsion;

* `Work.LinnikAreas.BGTZ.ZFRInputL cZ` — the same statement with the hypothesis `L(ρ,χ) = 0 ∨
  L(ρ,χχ₁) = 0`; this is the form consumed by the assembly of BGTZ's Theorem 1.3
  (`Work.LinnikAreas.BGTZ.RepulsionFromPieces`), whose detector argument is applied to a zero of
  an ordinary `L`-function.

Both are *true*, classical statements: for every zero `ρ` with `Re ρ > 1/2` other than the
exceptional real zero `β₁`, the zero-free region

`1 - Re ρ ≥ c/log (q·max 4 |Im ρ|)`

holds, with an absolute `c > 0` and for `q ≥ q₀(c)`.  The sources of the proof are

* `Commons.NumberTheory.DirichletCharacter.LFunction_zeroFree_offAxis_uniform` (the off-axis
  region, uniform in the conductor and the height, for primitive `χ ≠ 1`) — used for `ρ.im ≠ 0`;
* `Commons.NumberTheory.Zeta.zeta_zeroFreeRegion_largeHeight` and
  `Commons.NumberTheory.Zeta.zeta_zeroFree_near_axis` (the `ζ`-region, used when the primitive
  character inducing `χ` is trivial), plus a compact-height gap (finitely many `ζ`-zeros in a
  bounded box);
* `Commons.NumberTheory.DirichletCharacter.LFunction_zeroFree_uniform_realAxis` (the real axis for
  primitive `χ` with `χ² ≠ 1`) and the Deuring--Heilbronn repulsion `Work.ZeroDensity.RepulsionWith`
  (7/16) for the remaining real zeros (real characters), which pushes every real zero other than
  `β₁` to `λ(ρ) ≥ (7/16) log (1/λ₁) ≫ 1`.

The second form is obtained from the first by the bridge between `L`-function zeros and
`zeroMult`-zeros (`Work.LinnikAreas.BGTZ.LFunction_eq_zero_imp_zeroMult`).
-/

import Mathlib
import Submission.Work.LinnikAreas.SiegelBase

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.LinnikAreas

open Work.LinnikContract

namespace BGTZ

/-- **The uniform zero-free region for the zeros of the completed `L`-functions of the characters
mod `q`**, in the `zeroMult` form.

For every `q ≥ q₀(cZ)`, every real character `χ₁ ≠ 1` mod `q` with an exceptional real zero `β₁`
satisfying `1 - 1/(10 log q) < β₁` (so `λ₁ = λ(β₁) ≤ 1/10`), every zero `ρ ≠ β₁` with
`Re ρ > 1/2` of the completed `L`-function of any character mod `q` satisfies

`1 - Re ρ ≥ cZ / log (q · max 4 |Im ρ|)`.

The constant `cZ` is absolute (independent of `q`); its value is irrelevant below (any positive
constant works for `q` large enough, which is all the users of this statement need). -/
def ZFRInput (cZ : ℝ) : Prop :=
  ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (β₁ : ℝ),
    χ₁ ≠ 1 → χ₁ ^ 2 = 1 → β₁ < 1 → zeroMult χ₁ (β₁ : ℂ) ≠ 0 →
    1 - 1 / (10 * Real.log q) < β₁ →
    ∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), zeroMult χ ρ ≠ 0 →
      (1 / 2 : ℝ) < ρ.re → ρ ≠ (β₁ : ℂ) →
      cZ / Real.log ((q : ℝ) * max 4 |ρ.im|) ≤ 1 - ρ.re

/-- **The uniform zero-free region in the `L`-function form**: the hypothesis of
`Work.LinnikAreas.BGTZ.RepulsionFromPieces`.  For every zero `ρ` with `Re ρ > 1/2`, `ρ ≠ β₁`, of
`L(s,χ)` or of `L(s,χχ₁)`, `1 - Re ρ ≥ cZ/log (q·max 4 |Im ρ|)`. -/
def ZFRInputL (cZ : ℝ) : Prop :=
  ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (β₁ : ℝ),
    χ₁ ≠ 1 → χ₁ ^ 2 = 1 → β₁ < 1 → zeroMult χ₁ (β₁ : ℂ) ≠ 0 →
    1 - 1 / (10 * Real.log q) < β₁ →
    ∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ),
      (DirichletCharacter.LFunction χ ρ = 0 ∨ DirichletCharacter.LFunction (χ * χ₁) ρ = 0) →
      (1 / 2 : ℝ) < ρ.re → ρ ≠ (β₁ : ℂ) →
      cZ / Real.log ((q : ℝ) * max 4 |ρ.im|) ≤ 1 - ρ.re

/-- `ZFRInput` is monotone in the constant. -/
theorem ZFRInput_mono {cZ cZ' : ℝ} (h : ZFRInput cZ) (hcZ' : 0 < cZ') (hle : cZ' ≤ cZ) :
    ZFRInput cZ' := by
  obtain ⟨q₀, hq⟩ := h
  refine ⟨max q₀ 2, ?_⟩
  intro q hq' nq χ₁ β₁ hχ hsq hβ hz hβ1 χ ρ hzm hre hne
  have hq₀ : q₀ ≤ q := le_trans (le_max_left _ _) hq'
  have h2 : 2 ≤ q := le_trans (le_max_right _ _) hq'
  have hq1 : (1 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 1 < q)
  have hlog : 0 < Real.log (q : ℝ) := Real.log_pos hq1
  have hm4 : (0 : ℝ) < max 4 |ρ.im| :=
    lt_of_lt_of_le (show (0 : ℝ) < 4 by norm_num) (le_max_left 4 |ρ.im|)
  have hm4' : (1 : ℝ) < max 4 |ρ.im| :=
    lt_of_lt_of_le (show (1 : ℝ) < 4 by norm_num) (le_max_left 4 |ρ.im|)
  have hprod : (1 : ℝ) < (q : ℝ) * max 4 |ρ.im| := by
    have h1 : (q : ℝ) * 1 < (q : ℝ) * max 4 |ρ.im| :=
      mul_lt_mul_of_pos_left hm4' (by linarith : (0 : ℝ) < (q : ℝ))
    have h2 : (1 : ℝ) ≤ (q : ℝ) * 1 := by linarith
    linarith
  have hlogpos : 0 < Real.log ((q : ℝ) * max 4 |ρ.im|) := Real.log_pos hprod
  have h := hq q hq₀ χ₁ β₁ hχ hsq hβ hz hβ1 χ ρ hzm hre hne
  have hquot : cZ' / Real.log ((q : ℝ) * max 4 |ρ.im|)
      ≤ cZ / Real.log ((q : ℝ) * max 4 |ρ.im|) :=
    div_le_div_of_nonneg_right hle hlogpos.le
  linarith

/-- **The `λ`-form of the zero-free region.**  Every zero `ρ` other than `β₁` with `Re ρ > 1/2`
satisfies `λ(ρ) ≥ cZ·log q / (log q + log (max 4 |Im ρ|))`.  This is the shape in which the
high-zero bound splits the zeros of large height. -/
theorem lamOf_floor_of_ZFRInput {cZ : ℝ} (h : ZFRInput cZ) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (β₁ : ℝ),
      χ₁ ≠ 1 → χ₁ ^ 2 = 1 → β₁ < 1 → zeroMult χ₁ (β₁ : ℂ) ≠ 0 →
      1 - 1 / (10 * Real.log q) < β₁ →
      ∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), zeroMult χ ρ ≠ 0 →
        (1 / 2 : ℝ) < ρ.re → ρ ≠ (β₁ : ℂ) →
        cZ * Real.log q / (Real.log q + Real.log (max 4 |ρ.im|)) ≤ lamOf q ρ := by
  obtain ⟨q₀, hq⟩ := h
  refine ⟨max q₀ 2, ?_⟩
  intro q hq' nq χ₁ β₁ hχ hsq hβ hz hβ1 χ ρ hzm hre hne
  have hq₀ : q₀ ≤ q := le_trans (le_max_left _ _) hq'
  have h2 : 2 ≤ q := le_trans (le_max_right _ _) hq'
  have hq1 : (1 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 1 < q)
  have hlog : 0 < Real.log (q : ℝ) := Real.log_pos hq1
  have hm4 : (0 : ℝ) < max 4 |ρ.im| :=
    lt_of_lt_of_le (show (0 : ℝ) < 4 by norm_num) (le_max_left 4 |ρ.im|)
  have hm4' : (1 : ℝ) < max 4 |ρ.im| :=
    lt_of_lt_of_le (show (1 : ℝ) < 4 by norm_num) (le_max_left 4 |ρ.im|)
  have hprod : (1 : ℝ) < (q : ℝ) * max 4 |ρ.im| := by
    have h1 : (q : ℝ) * 1 < (q : ℝ) * max 4 |ρ.im| :=
      mul_lt_mul_of_pos_left hm4' (by linarith : (0 : ℝ) < (q : ℝ))
    have h2 : (1 : ℝ) ≤ (q : ℝ) * 1 := by linarith
    linarith
  have h := hq q hq₀ χ₁ β₁ hχ hsq hβ hz hβ1 χ ρ hzm hre hne
  have hlogeq : Real.log ((q : ℝ) * max 4 |ρ.im|)
      = Real.log q + Real.log (max 4 |ρ.im|) :=
    Real.log_mul (by positivity) (by positivity)
  have hpos : 0 < Real.log q + Real.log (max 4 |ρ.im|) := by
    rw [← hlogeq]; exact Real.log_pos hprod
  rw [hlogeq] at h
  have h' : cZ ≤ (1 - ρ.re) * (Real.log q + Real.log (max 4 |ρ.im|)) := by
    rw [div_le_iff₀ hpos] at h
    exact h
  have hmul : cZ * Real.log q / (Real.log q + Real.log (max 4 |ρ.im|))
      ≤ (1 - ρ.re) * Real.log q := by
    rw [div_le_iff₀ hpos]
    calc cZ * Real.log q ≤ ((1 - ρ.re) * (Real.log q + Real.log (max 4 |ρ.im|)))
          * Real.log q := mul_le_mul_of_nonneg_right h' hlog.le
      _ = (1 - ρ.re) * Real.log q * (Real.log q + Real.log (max 4 |ρ.im|)) := by ring
  rwa [lamOf]

end BGTZ

end Work.LinnikAreas
