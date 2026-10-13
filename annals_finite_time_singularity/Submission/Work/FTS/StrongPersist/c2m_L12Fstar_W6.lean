/-
# `𝒲^{6,∞}`-bound for `c2m · L₁₂(F_*)`

T. M. Elgindi, *Finite-time singularity formation for `C^{1,α}` solutions to the
incompressible Euler equations on `ℝ³`*, Annals of Math. **194** (2021).

The angular coefficient `c2m(θ) = cos 2θ - sin²θ` of the second and sixth terms of `N₀`
(and of the transport term of `𝓛_Γ^T`) multiplies the *radial* function `L₁₂(F_*)`, and
for the profile `F_*` the operator `L₁₂` collapses to an elementary function,
`L₁₂(F_*)(z) = 2α/(1+z)` (`Work.Construction.L12_Fstar_eq`).  Hence

  `f_α(z,θ) = c2m(θ) · L₁₂(F_*)(z) = c2m(θ) · 2α/(1+z)`

on the whole half-line `z > -1`, and this file proves

  `f_α ∈ 𝒲^{6,∞}`  and  `|f_α|_{𝒲^{6,∞}} ≤ C α`,  `C` universal, for every `0 < α ≤ 1`.

This is the level-`6` analogue of `Work.FTS.Nonlinear.FstarPkg.c2m_L12Fstar_W` (level `4`),
which is the form consumed by the level-`3`/`4` rows of `N₀` (`NonlinRows.NRow7`,
`Nonlinear.Pieces.rowsN0Q`).  The level-six use enters through the `ℋ⁶` product rule of the
strong-solution route (`FTS/StrongPersist`), where the transport coefficient `c2m·L₁₂(F_*)`
has to be controlled at order six.

## The two pointwise inputs

The level-six statement needs the two pointwise estimates with the bounds `4 ↦ 6`:

* **radial.** `|(z+1)^k ∂_z^k (c2m(θ)·2α/(1+z))| ≤ 4 α k!` for `z ≥ 0`.  The proof of
  `c2mInv_points` never used its hypothesis `k ≤ 4` (it works for every `k`); the general
  form is re-proved here as `c2mSix_inv_points`.
* **angular × radial.** `(z+1)^k ∂_z^k D_θ^j (c2m(θ)·2α/(1+z)) · sin(2θ)^{-α/5}/(α+sin 2θ)`
  is `≤ C α`, for `1 ≤ j ≤ 6`, `k ≤ 6`.  This factors into the angular bound
  `|D_θ^j c2m| ≤ C₀ sin(2θ)²` for `1 ≤ j ≤ 6` -- the lemma
  `Work.FTS.StrongPersist.dthU_c2m_bound6`, proved in the sibling module
  `dthU_c2m_bound6` -- and the radial bound `c2mInv_radial` (`≤ 2α k!`, every `k`),
  together with the elementary weight inequality `sin²(2θ)·sin(2θ)^{-α/5}/(α+sin 2θ) ≤ 1`
  (`sinWeight_le_one`).  The resulting lemma is `c2mSix_inv_mixed`.

## The transfers and the assembly

`c2mSix_bound_z` and `c2mSix_bound_mixed` transfer the two pointwise bounds from the explicit
function `c2m·2α/(1+z)` to `c2m · L₁₂(F_*)`, using the identity `L₁₂(F_*) = 2α/(1+z)` on
`(-1,∞)` (`FstarPkg.eqOn_L12_invH`) and the derivative transfer lemmas
`FstarPkg.pzIter_c2m_mul_eq` / `FstarPkg.pzIter_DthIter_c2m_mul_eq`.

The assembly `c2mSix_WlInfMem` / `c2mSix_WlInf_le` is then summand-by-summand
(`Work.Spaces.supAbs_le`) exactly as in the level-four file, with `range 5 ↦ range 7` and
`k + j ≤ 4 ↦ k + j ≤ 6`; the final theorem `c2m_L12Fstar_W6` is the requested statement.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.IntervalCases
import Submission.Work.FTS.Nonlinear.FstarPkg.c2m_L12Fstar_W
import Submission.Work.FTS.StrongPersist.dthU_c2m_bound6

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The radial pointwise bound, at every order `k` -/

/-- The weighted `z`-derivative bound for the explicit function `c2m(θ)·2α/(1+z)`:
`|(z+1)^k ∂_z^k (c2m(θ)·2α/(1+z))| ≤ 4 α k!` for `z ≥ 0`, **every** `k : ℕ` and every
`α > 0`.  (The level-four statement `FstarPkg.c2mInv_points` carried the extra hypotheses
`α ≤ 1` and `k ≤ 4`; its proof used neither.) -/
theorem c2mSix_inv_points (α z θ : ℝ) (hα : 0 < α) (hz : 0 ≤ z) (k : ℕ) :
    |(z + 1) ^ k * Work.Spaces.pzIter k
        (fun z θ => Work.Construction.c2m θ * (2 * α / (1 + z))) z θ|
      ≤ 4 * α * (k.factorial : ℝ) := by
  have hz1 : -1 < z := by linarith
  have hα2 : (0 : ℝ) ≤ 2 * α := by linarith
  have hc2m : |Work.Construction.c2m θ| ≤ 2 :=
    Work.FTS.Nonlinear.FstarPkg.abs_c2m_le_two θ
  rw [Work.FTS.Nonlinear.FstarPkg.pzIter_c2m_inv α k z θ hz1]
  rw [show (z + 1) ^ k *
        (Work.Construction.c2m θ * (2 * α * Work.FTS.Nonlinear.FstarPkg.nInvClosed k z))
      = Work.Construction.c2m θ *
        (2 * α * ((z + 1) ^ k * Work.FTS.Nonlinear.FstarPkg.nInvClosed k z)) by ring]
  rw [abs_mul, abs_mul, abs_of_nonneg hα2]
  calc |Work.Construction.c2m θ| *
        (2 * α * |(z + 1) ^ k * Work.FTS.Nonlinear.FstarPkg.nInvClosed k z|)
      ≤ 2 * (2 * α * (k.factorial : ℝ)) := by
        apply mul_le_mul hc2m
        · exact mul_le_mul_of_nonneg_left
            (Work.FTS.Nonlinear.FstarPkg.nInvClosed_weighted k z hz) hα2
        · exact mul_nonneg hα2 (abs_nonneg _)
        · norm_num
    _ = 4 * α * (k.factorial : ℝ) := by ring

/-! ## The mixed pointwise bound at order six -/

/-- The mixed weighted bound for the explicit function `c2m(θ)·2α/(1+z)` at order six:
`(z+1)^k ∂_z^k D_θ^j (c2m(θ)·2α/(1+z)) · sin(2θ)^{-α/5}/(α+sin 2θ)` is bounded by `C α`,
uniformly for `0 < α ≤ 1`, `z ≥ 0`, `θ ∈ Iθ`, `1 ≤ j ≤ 6`, `k ≤ 6`. -/
theorem c2mSix_inv_mixed :
    ∃ C : ℝ, 0 < C ∧ ∀ (α z θ : ℝ), 0 < α → α ≤ 1 → 0 ≤ z → θ ∈ Work.Spaces.Iθ →
      ∀ (j k : ℕ), 1 ≤ j → j ≤ 6 → k ≤ 6 →
      |(z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter j
          (fun z θ => Work.Construction.c2m θ * (2 * α / (1 + z)))) z θ
        * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))| ≤ C * α := by
  obtain ⟨C0, hC0pos, hC0⟩ := dthU_c2m_bound6
  refine ⟨max C0 1 * 1440, ?_, ?_⟩
  · have h : (0 : ℝ) < max C0 1 := lt_max_of_lt_right one_pos
    positivity
  intro α z θ hα hα1 hz hθ j k hj1 hj6 hk
  set s : ℝ := Real.sin (2 * θ) with hs
  set B : ℝ → ℝ := fun z => 2 * α / (1 + z) with hB
  set g : ℝ → ℝ := (Work.Spaces.dthU^[j] Work.Construction.c2m) with hg
  have hDth : Work.Spaces.DthIter j (fun z θ => Work.Construction.c2m θ * (2 * α / (1 + z)))
      = fun z θ => g θ * B z := by
    funext z θ
    exact Work.Spaces.DthIter_decomp j Work.Construction.c2m B z θ
  rw [hDth]
  rw [Work.Spaces.pzIter_decomp k g B z θ]
  have hs0 : 0 ≤ s := by
    rw [hs]
    exact Real.sin_nonneg_of_mem_Icc
      ⟨by linarith [(Set.mem_Icc.mp hθ).1], by linarith [(Set.mem_Icc.mp hθ).2, Real.pi_pos]⟩
  have hs1 : s ≤ 1 := by rw [hs]; exact Real.sin_le_one _
  have hA : |g θ| ≤ max C0 1 * s ^ 2 := by
    rw [hg]
    exact le_trans (hC0 j hj1 hj6 θ)
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg s))
  have hBnd : |(z + 1) ^ k * deriv^[k] B z| ≤ 2 * α * (k.factorial : ℝ) := by
    rw [hB]
    exact Work.FTS.Nonlinear.FstarPkg.c2mInv_radial α hα k z hz
  have hXnn : 0 ≤ s ^ (-(α / 5)) / (α + s) :=
    div_nonneg (Real.rpow_nonneg hs0 _) (by linarith)
  have hW : s ^ 2 * (s ^ (-(α / 5)) / (α + s)) ≤ 1 := by
    have := Work.FTS.Nonlinear.FstarPkg.sinWeight_le_one α s hα hα1 hs0 hs1
    rwa [mul_div_assoc] at this
  have hfact : (k.factorial : ℝ) ≤ 720 := by
    interval_cases k <;> norm_num
  rw [mul_div_assoc]
  rw [show (z + 1) ^ k * (g θ * deriv^[k] B z)
      = g θ * ((z + 1) ^ k * deriv^[k] B z) by ring]
  rw [abs_mul, abs_mul, abs_of_nonneg hXnn]
  have h1 : |g θ| * |(z + 1) ^ k * deriv^[k] B z| * (s ^ (-(α / 5)) / (α + s))
      ≤ (max C0 1 * s ^ 2) * (2 * α * (k.factorial : ℝ))
        * (s ^ (-(α / 5)) / (α + s)) := by
    apply mul_le_mul_of_nonneg_right _ hXnn
    exact mul_le_mul hA hBnd (abs_nonneg _) (by positivity)
  refine le_trans h1 ?_
  have h2 : (max C0 1 * s ^ 2) * (2 * α * (k.factorial : ℝ)) * (s ^ (-(α / 5)) / (α + s))
      = 2 * (max C0 1) * α * (k.factorial : ℝ)
        * (s ^ 2 * (s ^ (-(α / 5)) / (α + s))) := by ring
  rw [h2]
  have h3 : 2 * (max C0 1) * α * (k.factorial : ℝ) * (s ^ 2 * (s ^ (-(α / 5)) / (α + s)))
      ≤ 2 * (max C0 1) * α * (k.factorial : ℝ) * 1 := by
    apply mul_le_mul_of_nonneg_left hW
    have h : (0 : ℝ) < max C0 1 := lt_max_of_lt_right one_pos
    positivity
  have h4 : 2 * (max C0 1) * α * (k.factorial : ℝ) * 1 ≤ 2 * (max C0 1) * α * 720 := by
    have hnn : 0 ≤ 2 * (max C0 1) * α := by
      have h : (0 : ℝ) < max C0 1 := lt_max_of_lt_right one_pos
      positivity
    have := mul_le_mul_of_nonneg_left hfact hnn
    simpa using this
  have h5 : 2 * (max C0 1) * α * 720 = (max C0 1 * 1440) * α := by ring
  linarith [h3, h4, h5]

/-! ## The transfer of the two bounds to `c2m · L₁₂(F_*)` -/

/-- The `z`-part at order six: `|(z+1)^k ∂_z^k (c2m·L₁₂(F_*))| ≤ 4 α k!` on the domain. -/
theorem c2mSix_bound_z (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (k : ℕ) {z θ : ℝ}
    (hz : z ∈ Work.Spaces.Iz) :
    |(z + 1) ^ k * Work.Spaces.pzIter k (Work.FTS.Nonlinear.FstarPkg.c2mL12 α) z θ|
      ≤ 4 * α * (k.factorial : ℝ) := by
  have hunf : Work.FTS.Nonlinear.FstarPkg.c2mL12 α = fun z θ => Work.Construction.c2m θ
      * Work.Construction.L12 (Work.Construction.Fstar α) z := rfl
  rw [hunf]
  have hz0 : (0 : ℝ) ≤ z := hz
  have hz1 : z ∈ Set.Ioi (-1) := Set.mem_Ioi.mpr (by linarith)
  rw [Work.FTS.Nonlinear.FstarPkg.pzIter_c2m_mul_eq
      (F := fun z => Work.Construction.L12 (Work.Construction.Fstar α) z)
      (H := Work.FTS.Nonlinear.FstarPkg.invH α)
      (Work.FTS.Nonlinear.FstarPkg.eqOn_L12_invH α hα hα1) k hz1]
  exact c2mSix_inv_points α z θ hα hz0 k

/-- The mixed part at order six: the `𝒲^{6,∞}`-bound for `c2m·L₁₂(F_*)`, from the same
bound for the explicit function `c2m·2α/(1+z)`. -/
theorem c2mSix_bound_mixed (K : ℝ)
    (hK : ∀ (α z θ : ℝ), 0 < α → α ≤ 1 → 0 ≤ z → θ ∈ Work.Spaces.Iθ →
      ∀ (j k : ℕ), 1 ≤ j → j ≤ 6 → k ≤ 6 →
      |(z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter j
          (fun z θ => Work.Construction.c2m θ * (2 * α / (1 + z)))) z θ
        * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))| ≤ K * α)
    (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (j k : ℕ) (hj1 : 1 ≤ j) (hj6 : j ≤ 6) (hk : k ≤ 6)
    {z θ : ℝ} (hz : z ∈ Work.Spaces.Iz) (hθ : θ ∈ Work.Spaces.Iθ) :
    |(z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter j
        (Work.FTS.Nonlinear.FstarPkg.c2mL12 α)) z θ
      * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))| ≤ K * α := by
  have hunf : Work.FTS.Nonlinear.FstarPkg.c2mL12 α = fun z θ => Work.Construction.c2m θ
      * Work.Construction.L12 (Work.Construction.Fstar α) z := rfl
  rw [hunf]
  have hz0 : (0 : ℝ) ≤ z := hz
  have hz1 : z ∈ Set.Ioi (-1) := Set.mem_Ioi.mpr (by linarith)
  rw [Work.FTS.Nonlinear.FstarPkg.pzIter_DthIter_c2m_mul_eq
      (F := fun z => Work.Construction.L12 (Work.Construction.Fstar α) z)
      (H := Work.FTS.Nonlinear.FstarPkg.invH α)
      (Work.FTS.Nonlinear.FstarPkg.eqOn_L12_invH α hα hα1) j k hz1]
  exact hK α z θ hα hα1 hz0 hθ j k hj1 hj6 hk

/-! ## The universal constant and the sum arithmetic -/

/-- The universal constant of the level-six estimate, given the constant `K` of the mixed
pointwise bound: the `z`-sum `∑_{k<7} 4·k!` plus the 49 mixed summands (each `≤ K α`). -/
noncomputable def c2mSixCW (K : ℝ) : ℝ :=
  (∑ k ∈ Finset.range 7, 4 * (k.factorial : ℝ)) + 49 * K + 1

theorem c2mSixCW_pos (K : ℝ) (hK : 0 < K) : 0 < c2mSixCW K := by
  have h1 : 0 ≤ ∑ k ∈ Finset.range 7, 4 * (k.factorial : ℝ) :=
    Finset.sum_nonneg fun k _ => by positivity
  have h2 : 0 < 49 * K := by linarith
  rw [c2mSixCW]
  linarith

/-- The double sum of a constant over `range 7 × range 7` is `49 c`. -/
theorem c2mSix_sum_const_mul (c : ℝ) :
    (∑ _j ∈ Finset.range 7, ∑ _k ∈ Finset.range 7, c) = 49 * c := by
  simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  ring

/-- The `z`-sum, with the constant `α` pulled out. -/
theorem c2mSix_sum_fact_mul (α : ℝ) :
    (∑ k ∈ Finset.range 7, 4 * α * (k.factorial : ℝ))
      = (∑ k ∈ Finset.range 7, 4 * (k.factorial : ℝ)) * α := by
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => by ring

/-! ## The two halves of the `𝒲^{6,∞}`-bound -/

/-- `c2m·L₁₂(F_*) ∈ 𝒲^{6,∞}`: every one of the finitely many suprema occurring in
`WlInf α 6` is that of a bounded function (the explicit bounds of `c2mSix_bound_z` and
`c2mSix_bound_mixed`). -/
theorem c2mSix_WlInfMem (K : ℝ)
    (hK : ∀ (α z θ : ℝ), 0 < α → α ≤ 1 → 0 ≤ z → θ ∈ Work.Spaces.Iθ →
      ∀ (j k : ℕ), 1 ≤ j → j ≤ 6 → k ≤ 6 →
      |(z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter j
          (fun z θ => Work.Construction.c2m θ * (2 * α / (1 + z)))) z θ
        * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))| ≤ K * α)
    (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    Work.Spaces.WlInfMem α 6 (fun z θ => Work.Construction.c2m θ
      * Work.Construction.L12 (Work.Construction.Fstar α) z) := by
  constructor
  · intro k hk
    exact ⟨4 * α * (k.factorial : ℝ), fun y hy => by
      rcases hy with ⟨z, hz, θ, hθ, rfl⟩
      exact c2mSix_bound_z α hα hα1 k hz⟩
  · intro j hj k hk hj1 hjk
    exact ⟨K * α, fun y hy => by
      rcases hy with ⟨z, hz, θ, hθ, rfl⟩
      exact c2mSix_bound_mixed K hK α hα hα1 j k hj1 hj hk hz hθ⟩

/-- The norm estimate at order six: `|c2m·L₁₂(F_*)|_{𝒲^{6,∞}} ≤ c2mSixCW K · α`. -/
theorem c2mSix_WlInf_le (K : ℝ) (hKpos : 0 < K)
    (hK : ∀ (α z θ : ℝ), 0 < α → α ≤ 1 → 0 ≤ z → θ ∈ Work.Spaces.Iθ →
      ∀ (j k : ℕ), 1 ≤ j → j ≤ 6 → k ≤ 6 →
      |(z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter j
          (fun z θ => Work.Construction.c2m θ * (2 * α / (1 + z)))) z θ
        * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))| ≤ K * α)
    (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    Work.Spaces.WlInf α 6 (fun z θ => Work.Construction.c2m θ
      * Work.Construction.L12 (Work.Construction.Fstar α) z) ≤ c2mSixCW K * α := by
  have hzsum : (∑ k ∈ Finset.range 7, Work.Spaces.supAbs (fun z θ =>
        (z + 1) ^ k * Work.Spaces.pzIter k (Work.FTS.Nonlinear.FstarPkg.c2mL12 α) z θ))
      ≤ ∑ k ∈ Finset.range 7, 4 * α * (k.factorial : ℝ) := by
    apply Finset.sum_le_sum
    intro k hk
    exact Work.Spaces.supAbs_le fun z hz θ _ => c2mSix_bound_z α hα hα1 k hz
  have hmsum : (∑ j ∈ Finset.range 7, ∑ k ∈ Finset.range 7,
        (if 1 ≤ j ∧ k + j ≤ 6 then Work.Spaces.supAbs (fun z θ =>
          (z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter j
            (Work.FTS.Nonlinear.FstarPkg.c2mL12 α)) z θ
            * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) else 0))
      ≤ ∑ j ∈ Finset.range 7, ∑ k ∈ Finset.range 7, K * α := by
    apply Finset.sum_le_sum
    intro j hj
    apply Finset.sum_le_sum
    intro k hk
    by_cases hc : 1 ≤ j ∧ k + j ≤ 6
    · rw [ite_eq_left hc]
      exact Work.Spaces.supAbs_le fun z hz θ hθ =>
        c2mSix_bound_mixed K hK α hα hα1 j k hc.1 (by omega) (by omega) hz hθ
    · rw [ite_eq_right hc]
      exact mul_nonneg hKpos.le hα.le
  calc Work.Spaces.WlInf α 6 (Work.FTS.Nonlinear.FstarPkg.c2mL12 α)
      = (∑ k ∈ Finset.range 7, Work.Spaces.supAbs (fun z θ =>
            (z + 1) ^ k * Work.Spaces.pzIter k (Work.FTS.Nonlinear.FstarPkg.c2mL12 α) z θ))
        + ∑ j ∈ Finset.range 7, ∑ k ∈ Finset.range 7,
            (if 1 ≤ j ∧ k + j ≤ 6 then Work.Spaces.supAbs (fun z θ =>
              (z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter j
                (Work.FTS.Nonlinear.FstarPkg.c2mL12 α)) z θ
                  * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) else 0) := rfl
    _ ≤ (∑ k ∈ Finset.range 7, 4 * α * (k.factorial : ℝ))
        + ∑ j ∈ Finset.range 7, ∑ k ∈ Finset.range 7, K * α := add_le_add hzsum hmsum
    _ = (∑ k ∈ Finset.range 7, 4 * (k.factorial : ℝ)) * α + 49 * (K * α) := by
      rw [c2mSix_sum_fact_mul, c2mSix_sum_const_mul]
    _ ≤ c2mSixCW K * α := by
      rw [c2mSixCW]
      nlinarith [hα.le, hKpos.le]

/-! ## The requested statement -/

theorem c2m_L12Fstar_W6 : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 →
    Work.Spaces.WlInfMem α 6 (fun z θ => Work.Construction.c2m θ
      * Work.Construction.L12 (Work.Construction.Fstar α) z) ∧
    Work.Spaces.WlInf α 6 (fun z θ => Work.Construction.c2m θ
      * Work.Construction.L12 (Work.Construction.Fstar α) z) ≤ C * α := by
  obtain ⟨K, hKpos, hK⟩ := c2mSix_inv_mixed
  exact ⟨c2mSixCW K, c2mSixCW_pos K hKpos, fun α hα hα1 =>
    ⟨c2mSix_WlInfMem K hK α hα hα1, c2mSix_WlInf_le K hKpos hK α hα hα1⟩⟩

end Work.FTS.StrongPersist
