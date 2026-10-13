/-
# The `F_*`-package, `𝒲^{4,∞}`-part: `c2m · L₁₂(F_*)`

The angular coefficient `c2m(θ) = cos 2θ - sin²θ` of the second and sixth terms of `N₀`
(and of the transport term of `𝓛_Γ^T`) multiplies the *radial* function `L₁₂(F_*)` in
those terms, i.e. the function

  `f_α(z,θ) = c2m(θ) · L₁₂(F_*)(z)`.

For the profile `F_*` the operator `L₁₂` collapses to an elementary function
(`Work.Construction.L12_Fstar_eq`): `L₁₂(F_*)(z) = 2α/(1+z)`.  On the domain
`z ∈ [0,∞)` the function `c2m · L₁₂(F_*)` is therefore the fully explicit
`c2m(θ)·2α/(1+z)`, whose `𝒲^{4,∞}`-norm is `O(α)` with a universal constant.

The one subtlety is the point `z = 0`: the `𝒲^{l,∞}`-seminorms involve *two-sided*
derivatives (`Work.Spaces.pzIter`), and `supAbs` is taken over the *closed* half-line
`Iz = [0,∞)`.  At `z = 0` the derivative of `z ↦ L₁₂(F_*)(z)` is the two-sided limit of
the difference quotients, which is controlled by the values of `L₁₂(F_*)` on a *two-sided*
neighbourhood of `0`.  We therefore use the slightly stronger identity
`L₁₂(F_*)(z) = 2α/(1+z)` for `z > -1`
(`Work.FTS.Nonlinear.FstarPkg.L12_Fstar_eq_of_gt_neg_one`), which exhibits the whole
function `L₁₂(F_*)` as `2α/(1+z)` on the open set `(-1,∞) ⊆ ℝ`; all iterated derivatives on
`Iz ⊂ (-1,∞)` then agree with those of the explicit function, and the `𝒲^{4,∞}`-bound for
`c2m · L₁₂(F_*)` follows from the elementary pointwise bounds for the explicit function
(`Work.FTS.Nonlinear.FstarPkg.c2mInv_points`, `…c2mInv_mixed`).

## Layout of the argument

* `eqOn_L12_invH`: the identity `L₁₂(F_*) = 2α/(1+z)` on the open set `(-1,∞)`;
* `deriv_iter_eqOn`, `pzIter_c2m_mul_eq`, `pzIter_DthIter_c2m_mul_eq`: the transfer of the
  equality to the `z`-derivatives (and the `θ`-derivatives) on `Iz`;
* `bound_z`, `bound_mixed`: the two pointwise `𝒲^{4,∞}`-bounds for `c2m · L₁₂(F_*)`,
  obtained from the explicit bounds `c2mInv_points` / `c2mInv_mixed` by that transfer;
* `c2m_L12Fstar_W`: the two `supAbs`-sums are bounded summand by summand
  (`Work.Spaces.supAbs_le`), which gives both `WlInfMem` and the `WlInf`-estimate.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.Nonlinear.Defs
import Submission.Work.Spaces.Gamma_WlInf
import Submission.Work.Construction.L12_Fstar_eq
import Submission.Work.FTS.Nonlinear.FstarPkg.L12_Fstar_eq_of_gt_neg_one
import Submission.Work.FTS.Nonlinear.FstarPkg.c2mInv_points
import Submission.Work.FTS.Nonlinear.FstarPkg.c2mInv_mixed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.FstarPkg

set_option autoImplicit false

/-! ## The two functions, and the transfer of the profile identity -/

/-- The radial factor `2α/(1+z)` of `L₁₂(F_*)`. -/
def invH (α : ℝ) : ℝ → ℝ := fun z => 2 * α / (1 + z)

/-- The function whose `𝒲^{4,∞}`-norm the lemma is about. -/
def c2mL12 (α : ℝ) : ℝ → ℝ → ℝ := fun z θ =>
  Work.Construction.c2m θ * Work.Construction.L12 (Work.Construction.Fstar α) z

@[simp] theorem invH_apply (α z : ℝ) : invH α z = 2 * α / (1 + z) := rfl

@[simp] theorem c2mL12_apply (α z θ : ℝ) : c2mL12 α z θ =
    Work.Construction.c2m θ * Work.Construction.L12 (Work.Construction.Fstar α) z := rfl

/-- The identity `L₁₂(F_*) = 2α/(1+z)` holds on the open set `(-1,∞)`. -/
theorem eqOn_L12_invH (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    Set.EqOn (fun z => Work.Construction.L12 (Work.Construction.Fstar α) z) (invH α)
      (Set.Ioi (-1)) := by
  intro z hz
  exact L12_Fstar_eq_of_gt_neg_one hα hα1 hz

/-- All iterated derivatives of two functions agreeing on the open set `(-1,∞)` agree
on `(-1,∞)`. -/
theorem deriv_iter_eqOn {F H : ℝ → ℝ} (h : Set.EqOn F H (Set.Ioi (-1))) (k : ℕ) :
    Set.EqOn (deriv^[k] F) (deriv^[k] H) (Set.Ioi (-1)) := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
      intro z hz
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact Filter.EventuallyEq.deriv_eq
        (Filter.eventuallyEq_of_mem (isOpen_Ioi.mem_nhds hz) (fun y hy => ih hy))

/-- The iterated `z`-derivatives of `c2m(θ)·F` and `c2m(θ)·H` agree on the domain when
`F = H` on `(-1,∞)`. -/
theorem pzIter_c2m_mul_eq {F H : ℝ → ℝ} (h : Set.EqOn F H (Set.Ioi (-1))) (k : ℕ)
    {z θ : ℝ} (hz : z ∈ Set.Ioi (-1)) :
    Work.Spaces.pzIter k (fun z θ => Work.Construction.c2m θ * F z) z θ
      = Work.Spaces.pzIter k (fun z θ => Work.Construction.c2m θ * H z) z θ := by
  rw [Work.Spaces.pzIter_decomp k (fun θ => Work.Construction.c2m θ) F z θ,
    Work.Spaces.pzIter_decomp k (fun θ => Work.Construction.c2m θ) H z θ,
    deriv_iter_eqOn h k hz]

/-- The iterated `z`-derivatives of `D_θ^j (c2m·F)` and `D_θ^j (c2m·H)` agree on the
domain when `F = H` on `(-1,∞)`. -/
theorem pzIter_DthIter_c2m_mul_eq {F H : ℝ → ℝ} (h : Set.EqOn F H (Set.Ioi (-1)))
    (j k : ℕ) {z θ : ℝ} (hz : z ∈ Set.Ioi (-1)) :
    Work.Spaces.pzIter k (Work.Spaces.DthIter j
        (fun z θ => Work.Construction.c2m θ * F z)) z θ
      = Work.Spaces.pzIter k (Work.Spaces.DthIter j
        (fun z θ => Work.Construction.c2m θ * H z)) z θ := by
  have hF : Work.Spaces.DthIter j (fun z θ => Work.Construction.c2m θ * F z)
      = fun z θ => Work.Spaces.dthU^[j] (Work.Construction.c2m) θ * F z := by
    funext z θ
    exact Work.Spaces.DthIter_decomp j Work.Construction.c2m F z θ
  have hH : Work.Spaces.DthIter j (fun z θ => Work.Construction.c2m θ * H z)
      = fun z θ => Work.Spaces.dthU^[j] (Work.Construction.c2m) θ * H z := by
    funext z θ
    exact Work.Spaces.DthIter_decomp j Work.Construction.c2m H z θ
  rw [hF, hH]
  rw [Work.Spaces.pzIter_decomp k (fun θ => Work.Spaces.dthU^[j] Work.Construction.c2m θ)
        F z θ,
    Work.Spaces.pzIter_decomp k (fun θ => Work.Spaces.dthU^[j] Work.Construction.c2m θ)
        H z θ,
    deriv_iter_eqOn h k hz]

/-! ## The two pointwise bounds for `c2m · L₁₂(F_*)` -/

/-- The `z`-part: `|(z+1)^k ∂_z^k (c2m·L₁₂(F_*))| ≤ 4α·k!` on the domain. -/
theorem bound_z (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (k : ℕ) (hk : k ≤ 4)
    {z θ : ℝ} (hz : z ∈ Work.Spaces.Iz) :
    |(z + 1) ^ k * Work.Spaces.pzIter k (c2mL12 α) z θ| ≤ 4 * α * (k.factorial : ℝ) := by
  have hunf : c2mL12 α = fun z θ => Work.Construction.c2m θ
      * Work.Construction.L12 (Work.Construction.Fstar α) z := rfl
  rw [hunf]
  have hz0 : (0 : ℝ) ≤ z := hz
  have hz1 : z ∈ Set.Ioi (-1) := Set.mem_Ioi.mpr (by linarith)
  have heq := pzIter_c2m_mul_eq (F := fun z => Work.Construction.L12
      (Work.Construction.Fstar α) z) (H := invH α) (eqOn_L12_invH α hα hα1) k
      (z := z) (θ := θ) hz1
  rw [heq]
  exact c2mInv_points α z θ hα hα1 hz0 k hk

/-- The mixed part: `|(z+1)^k ∂_z^k D_θ^j (c2m·L₁₂(F_*)) · sin(2θ)^{-α/5}/(α+sin 2θ)| ≤ K α`
on the domain, for the universal constant `K` of `c2mInv_mixed`. -/
theorem bound_mixed (K : ℝ) (hK : ∀ (α z θ : ℝ), 0 < α → α ≤ 1 → 0 ≤ z →
      θ ∈ Work.Spaces.Iθ → ∀ (j k : ℕ), 1 ≤ j → j ≤ 4 → k ≤ 4 →
      |(z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter j
          (fun z θ => Work.Construction.c2m θ * (2 * α / (1 + z)))) z θ
        * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))| ≤ K * α)
    (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (j k : ℕ) (hj1 : 1 ≤ j) (hj4 : j ≤ 4) (hk : k ≤ 4)
    {z θ : ℝ} (hz : z ∈ Work.Spaces.Iz) (hθ : θ ∈ Work.Spaces.Iθ) :
    |(z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter j (c2mL12 α)) z θ
        * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))| ≤ K * α := by
  have hunf : c2mL12 α = fun z θ => Work.Construction.c2m θ
      * Work.Construction.L12 (Work.Construction.Fstar α) z := rfl
  rw [hunf]
  have hz0 : (0 : ℝ) ≤ z := hz
  have hz1 : z ∈ Set.Ioi (-1) := Set.mem_Ioi.mpr (by linarith)
  have heq := pzIter_DthIter_c2m_mul_eq (F := fun z => Work.Construction.L12
      (Work.Construction.Fstar α) z) (H := invH α) (eqOn_L12_invH α hα hα1) j k
      (z := z) (θ := θ) hz1
  rw [heq]
  exact hK α z θ hα hα1 hz0 hθ j k hj1 hj4 hk

/-! ## The two sums -/

/-- The constant of the final estimate: the `z`-sum `4·(0!+1!+2!+3!+4!)` plus the 25
mixed summands of `c2mInv_mixed` (all bounded by `K α`). -/
def CW (K : ℝ) : ℝ := (∑ k ∈ Finset.range 5, 4 * (k.factorial : ℝ)) + 25 * K + 1

theorem factorial_sum_lt : (∑ k ∈ Finset.range 5, (k.factorial : ℝ)) = 34 := by
  norm_num [Finset.sum_range_succ]

/-- The double sum of a constant over `range 5 × range 5`. -/
theorem sum_range5_const_mul (c : ℝ) :
    (∑ _j ∈ Finset.range 5, ∑ _k ∈ Finset.range 5, c) = 25 * c := by
  simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  ring

/-- The `z`-sum, with the constant `α` pulled out. -/
theorem sum_range5_four_factorial_mul (α : ℝ) :
    (∑ k ∈ Finset.range 5, 4 * α * (k.factorial : ℝ))
      = (∑ k ∈ Finset.range 5, 4 * (k.factorial : ℝ)) * α := by
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem CW_pos (K : ℝ) (hK : 0 < K) : 0 < CW K := by
  have h1 : 0 ≤ ∑ k ∈ Finset.range 5, 4 * (k.factorial : ℝ) :=
    Finset.sum_nonneg fun k _ => by positivity
  have h2 : 0 < 25 * K := by linarith
  rw [CW]
  linarith

/-! ## The main theorem -/

theorem c2m_L12Fstar_W :
    ∃ C : ℝ, 0 < C ∧ ∀ α : ℝ, 0 < α → α ≤ 1 →
      Work.Spaces.WlInfMem α 4 (fun z θ => Work.Construction.c2m θ
        * Work.Construction.L12 (Work.Construction.Fstar α) z) ∧
      Work.Spaces.WlInf α 4 (fun z θ => Work.Construction.c2m θ
        * Work.Construction.L12 (Work.Construction.Fstar α) z) ≤ C * α := by
  obtain ⟨K, hKpos, hK⟩ := c2mInv_mixed
  have hK' : ∀ (α z θ : ℝ), 0 < α → α ≤ 1 → 0 ≤ z → θ ∈ Work.Spaces.Iθ →
      ∀ (j k : ℕ), 1 ≤ j → j ≤ 4 → k ≤ 4 →
      |(z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter j
          (fun z θ => Work.Construction.c2m θ * (2 * α / (1 + z)))) z θ
        * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))| ≤ K * α := hK
  refine ⟨CW K, CW_pos K hKpos, fun α hα hα1 => ⟨?_, ?_⟩⟩
  · -- membership: every summand is bounded
    constructor
    · intro k hk
      exact ⟨4 * α * (k.factorial : ℝ), fun y hy => by
        rcases hy with ⟨z, hz, θ, hθ, rfl⟩
        exact bound_z α hα hα1 k hk hz⟩
    · intro j hj k hk hj1 hjk
      exact ⟨K * α, fun y hy => by
        rcases hy with ⟨z, hz, θ, hθ, rfl⟩
        exact bound_mixed K hK' α hα hα1 j k hj1 hj hk hz hθ⟩
  · -- the norm estimate
    have hzsum : (∑ k ∈ Finset.range 5, Work.Spaces.supAbs (fun z θ =>
          (z + 1) ^ k * Work.Spaces.pzIter k (c2mL12 α) z θ))
        ≤ ∑ k ∈ Finset.range 5, 4 * α * (k.factorial : ℝ) := by
      apply Finset.sum_le_sum
      intro k hk
      have hk4 : k ≤ 4 := by
        have := Finset.mem_range.mp hk
        omega
      exact Work.Spaces.supAbs_le fun z hz θ _ => bound_z α hα hα1 k hk4 hz
    have hmsum : (∑ j ∈ Finset.range 5, ∑ k ∈ Finset.range 5,
          (if 1 ≤ j ∧ k + j ≤ 4 then Work.Spaces.supAbs (fun z θ =>
            (z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter j (c2mL12 α)) z θ
              * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) else 0))
        ≤ ∑ j ∈ Finset.range 5, ∑ k ∈ Finset.range 5, K * α := by
      apply Finset.sum_le_sum
      intro j hj
      apply Finset.sum_le_sum
      intro k hk
      by_cases hc : 1 ≤ j ∧ k + j ≤ 4
      · rw [if_pos hc]
        have hj4 : j ≤ 4 := by
          have := Finset.mem_range.mp hj
          omega
        have hk4 : k ≤ 4 := by
          have := Finset.mem_range.mp hk
          omega
        exact Work.Spaces.supAbs_le fun z hz θ hθ =>
          bound_mixed K hK' α hα hα1 j k hc.1 hj4 hk4 hz hθ
      · rw [if_neg hc]
        exact mul_nonneg hKpos.le hα.le
    calc Work.Spaces.WlInf α 4 (c2mL12 α)
        = (∑ k ∈ Finset.range 5, Work.Spaces.supAbs (fun z θ =>
              (z + 1) ^ k * Work.Spaces.pzIter k (c2mL12 α) z θ))
          + ∑ j ∈ Finset.range 5, ∑ k ∈ Finset.range 5,
              (if 1 ≤ j ∧ k + j ≤ 4 then Work.Spaces.supAbs (fun z θ =>
                (z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter j (c2mL12 α)) z θ
                  * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) else 0) := rfl
      _ ≤ (∑ k ∈ Finset.range 5, 4 * α * (k.factorial : ℝ))
          + ∑ j ∈ Finset.range 5, ∑ k ∈ Finset.range 5, K * α := add_le_add hzsum hmsum
      _ = (∑ k ∈ Finset.range 5, 4 * (k.factorial : ℝ)) * α + 25 * (K * α) := by
        rw [sum_range5_four_factorial_mul, sum_range5_const_mul]
      _ ≤ CW K * α := by
        rw [CW]
        nlinarith [hα.le, hKpos.le]

end Work.FTS.Nonlinear.FstarPkg
