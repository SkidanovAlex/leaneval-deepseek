import Mathlib
import Submission.Work.LinnikContract.Defs
import Submission.Work.LinnikAreas.DhCapped.twoRealZeroRepelCore
import Submission.Work.LinnikAreas.DhCapped.twoRealZeroRepelArith
import Submission.Work.LinnikAreas.OtherCharRepel.zeroMultStripPos

/-!
# `Work.LinnikAreas.OtherCharRepel.sameCharRepelConst`

Same-character repulsion at an *absolute* threshold: a real character `χ₀` with a real zero `ρ₀`
satisfying `λ(ρ₀) ≤ 1/100` has no *other* real zero with `λ ≤ 1/100`.

The mathematical content is the classical "at most one exceptional real zero" phenomenon: two
distinct real zeros `β₀ ≠ β₂` of `L(s,χ*)` for a non-principal `χ` cannot both be that close to
`s = 1`.  This is proved from the Hadamard partial-fraction inequality at two real zeros
(`Work.LinnikAreas.DhCapped.twoRealZeroRepelCore`, an analytic statement about the logarithmic
derivative of the completed `L`-function) together with the elementary arithmetic
(`Work.LinnikAreas.DhCapped.twoRealZeroRepelArith`): a first zero with `λ ≤ 1/100` forces any
second one to have `λ ≥ 87/230 > 1/4`.

Instantiating `λ ≥ 1/4` at `λ ≥ 1/100` and converting the hypothesis `ρ.im = 0` into the real
coordinate `ρ.re` gives the requested constant-threshold repulsion.

The hypothesis `IsMin1 χ₀ ρ₀` (global minimality of `λ(ρ₀)` in the working region) is carried by
the contract but is *not* needed: the repulsion between two real zeros of the same character is
self-contained.
-/

namespace Work.LinnikAreas.OtherCharRepel

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

set_option maxHeartbeats 2000000
set_option linter.style.haveILetI false

/-- **Two distinct real zeros of a non-principal character repel each other**: if the first has
`λ(β₀) ≤ 1/100` then the second has `λ(β₂) ≥ 1/4`. -/
theorem twoRealZerosRepel : ∃ q₀ : ℕ,
    ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
    (χ : DirichletCharacter ℂ q) (β₀ β₂ : ℝ), χ ≠ 1 →
    Work.LinnikContract.zeroMult χ (β₀ : ℂ) ≠ 0 → Work.LinnikContract.zeroMult χ (β₂ : ℂ) ≠ 0 →
    β₂ ≠ β₀ → Work.LinnikContract.lamOf q (β₀ : ℂ) ≤ 1 / 100 →
      (1 / 4 : ℝ) ≤ Work.LinnikContract.lamOf q (β₂ : ℂ) := by
  obtain ⟨C, hCpos, hcore⟩ := DhCapped.twoRealZeroRepelCore
  refine ⟨max 3 ⌈Real.exp (11 * (C + 1))⌉₊, ?_⟩
  intro q hq hqne χ β₀ β₂ hχ hz₀ hz₂ hne hlam
  haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hq3 : 3 ≤ q := le_trans (le_max_left _ _) hq
  have hqe : ⌈Real.exp (11 * (C + 1))⌉₊ ≤ q := le_trans (le_max_right _ _) hq
  have hq1 : 1 < q := by omega
  have hLpos : 0 < Real.log (q:ℝ) := Real.log_pos (by exact_mod_cast hq1)
  -- delegated: a `zeroMult`-zero of a non-principal character lies in the strip, `λ > 0`
  have hstr₀ := zeroMultStripPos (q := q) (by omega : 2 ≤ q) hχ hz₀
  have hstr₂ := zeroMultStripPos (q := q) (by omega : 2 ≤ q) hχ hz₂
  have hlampos : 0 < Work.LinnikContract.lamOf q (β₀:ℂ) := hstr₀.2.2
  have hlam2pos : 0 < Work.LinnikContract.lamOf q (β₂:ℂ) := hstr₂.2.2
  have hH := hcore q hq3 χ hχ β₀ β₂ hz₀ hz₂ hne hlampos
  have hlim₀ : (1 + Real.sqrt (Work.LinnikContract.lamOf q (β₀:ℂ)) / Real.log (q:ℝ)) - β₀
      = Real.sqrt (Work.LinnikContract.lamOf q (β₀:ℂ)) / Real.log (q:ℝ)
        + Work.LinnikContract.lamOf q (β₀:ℂ) / Real.log (q:ℝ) := by
    have h : Work.LinnikContract.lamOf q (β₀:ℂ) / Real.log (q:ℝ) = 1 - β₀ := by
      simp only [Work.LinnikContract.lamOf, Complex.ofReal_re]
      exact mul_div_cancel_right₀ _ (ne_of_gt hLpos)
    rw [h]; ring
  have hlim₂ : (1 + Real.sqrt (Work.LinnikContract.lamOf q (β₀:ℂ)) / Real.log (q:ℝ)) - β₂
      = Real.sqrt (Work.LinnikContract.lamOf q (β₀:ℂ)) / Real.log (q:ℝ)
        + Work.LinnikContract.lamOf q (β₂:ℂ) / Real.log (q:ℝ) := by
    have h : Work.LinnikContract.lamOf q (β₂:ℂ) / Real.log (q:ℝ) = 1 - β₂ := by
      simp only [Work.LinnikContract.lamOf, Complex.ofReal_re]
      exact mul_div_cancel_right₀ _ (ne_of_gt hLpos)
    rw [h]; ring
  rw [hlim₀, hlim₂] at hH
  have hLbig : 11 * (C + 1) ≤ Real.log (q:ℝ) := by
    have h1 : Real.exp (11 * (C + 1)) ≤ (⌈Real.exp (11 * (C + 1))⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (⌈Real.exp (11 * (C + 1))⌉₊ : ℝ) ≤ (q:ℝ) := by exact_mod_cast hqe
    have h3 : Real.exp (11 * (C + 1)) ≤ (q:ℝ) := le_trans h1 h2
    rw [← Real.log_exp (11 * (C + 1))]
    exact Real.log_le_log (Real.exp_pos _) h3
  have hNle : Real.log ((χ.conductor : ℕ) : ℝ) ≤ Real.log (q:ℝ) := by
    apply Real.log_le_log
    · exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne χ.conductor)
    · exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) χ.conductor_dvd_level
  have hN1 : (1:ℝ) ≤ (χ.conductor : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne χ.conductor)
  have hquarter := DhCapped.twoRealZeroRepelArith (lam0 := Work.LinnikContract.lamOf q (β₀:ℂ))
    (lam2 := Work.LinnikContract.lamOf q (β₂:ℂ)) (L := Real.log (q:ℝ))
    (N := (χ.conductor : ℝ)) (C := C) hCpos.le hlampos hlam hlam2pos hLpos hN1 hNle hLbig hH
  linarith

/-- **Constant-threshold same-character repulsion** (Heath-Brown (1992), Principle 1 / Landau's
"at most one exceptional real zero"): there is `q₀` such that for every `q ≥ q₀`, whenever `χ₀` is a
real character with a real zero `ρ₀` of `λ(ρ₀) ≤ 1/100`, every *other* real zero `ρ` of `χ₀` has
`λ(ρ) ≥ 1/100`.  (`IsMin1 χ₀ ρ₀` is part of the contract but is not used.) -/
theorem sameCharRepelConst : ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
    (χ₀ : DirichletCharacter ℂ q) (ρ₀ : ℂ),
    Work.LinnikContract.IsMin1 χ₀ ρ₀ → χ₀ ^ 2 = 1 → ρ₀.im = 0 →
    Work.LinnikContract.lamOf q ρ₀ ≤ 1 / 100 →
    ∀ ρ : ℂ, Work.LinnikContract.zeroMult χ₀ ρ ≠ 0 → ρ.im = 0 → ρ ≠ ρ₀ →
      (1/100 : ℝ) ≤ Work.LinnikContract.lamOf q ρ := by
  obtain ⟨q₀, hrep⟩ := twoRealZerosRepel
  refine ⟨q₀, ?_⟩
  intro q hq hqne χ₀ ρ₀ hmin _hsq him0 hlam ρ hzm him hne
  have hχ0 : χ₀ ≠ 1 := hmin.1.1
  -- both real points are their own real coordinate
  have hρ₀ : ρ₀ = ((ρ₀.re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [him0]
  have hρ : ρ = ((ρ.re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [him]
  have hβne : ρ.re ≠ ρ₀.re := fun hh => hne (by rw [hρ, hρ₀, hh])
  -- apply the two-real-zeros repulsion
  have h2 := hrep q hq χ₀ ρ₀.re ρ.re hχ0
    (by rw [← hρ₀]; exact hmin.1.2.1) (by rw [← hρ]; exact hzm) hβne
    (by rw [← hρ₀]; exact hlam)
  rw [← hρ] at h2
  linarith

end

end Work.LinnikAreas.OtherCharRepel
