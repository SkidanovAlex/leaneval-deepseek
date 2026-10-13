/-
Copyright: work module for the Elgindi finite-time singularity project.

# Auxiliary definitions and estimates for `dthU_pow_Gam_sharp`

The target lemma `Work.FTS.Nonlinear.Pieces.RNP.dthU_pow_Gam_sharp` states the *sharp*
angular bound

  `|D_θ^m Γ(θ)| ≤ C · α · Γ(θ) · (α + sin 2θ)`,   `2 ≤ m ≤ 5`,

where `Γ(θ) = (sin θ · cos²θ)^{α/3}`, `D_θ = sin(2θ)∂_θ` and `C` is a universal constant.
This module contains the definitions and elementary estimates that the proof needs; the
induction itself lives in the sibling modules.

## The route

`Work.Spaces.dthU_iter_Gam` identifies the angular jet of `Γ` on `(0,π/2)`:

  `D_θ^{j+1} Γ = α · Tfun j α · Γ`,

and `Γ` is non-negative on `Iθ`, so the assertion is equivalent to the *uniform in α* bound

  `|Tfun j α θ| ≤ C · (α + sin 2θ)`,   `θ ∈ Iθ`,

for `j ≤ 4`.  The sequence `Tfun` obeys the recursion
`Tfun (j+1) α = D_θ (Tfun j α) + α · q · Tfun j α` with `q(θ) = cos 2θ - 1/3`, and the
bound is proved by induction on `j`, the induction hypothesis `Hyp j` controlling all
`D_θ`-iterates of `Tfun j α` down to order `4 - j`:

* near `θ = 0` and `θ = π/2` the factor `sin 2θ` in `D_θ` makes every iterate of order
  `≥ 1` vanish, which is exactly what the factor `α + sin 2θ` records;
* `α` is bounded by `1`, so the `α`-weighted Leibniz corrections are controlled by the
  crude bounds `|D_θ^i qfun| ≤ 1000` (`DthQfunBound`, `abs_qfun_le`).

`KB` is the (crude, geometric) sequence of constants making the induction close.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.Spaces.Gamma_WlInf
import Submission.Work.FTS.Nonlinear.FstarPkg.DthFstar_W

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Pieces.RNP

set_option autoImplicit false

/-! ## Elementary angular facts on `Iθ = [0, π/2]` -/

lemma sinTwo_mem_Icc {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    Real.sin (2 * θ) ∈ Set.Icc (0 : ℝ) 1 := by
  have h0 : 0 ≤ θ := hθ.1
  have h1 : θ ≤ Real.pi / 2 := hθ.2
  constructor
  · exact Real.sin_nonneg_of_mem_Icc ⟨by linarith, by linarith [Real.pi_pos]⟩
  · exact Real.sin_le_one _

/-! ## Crude bounds for the `D_θ`-iterates of `qfun`

They are all that is needed for the Leibniz corrections `D_θ^i (α q)`, since the factor `α`
already supplies the smallness in `α`. -/

/-- `D_θ^i qfun` is `O(sin 2θ)`; the `sin 2θ` factor is what makes the induction close near
the two endpoints of `Iθ`. -/
lemma dthU_qfun_le_sin {i : ℕ} (hi : 1 ≤ i) (hi4 : i ≤ 4) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.dthU^[i] Work.Spaces.qfun θ| ≤ 1000 * Real.sin (2 * θ) := by
  have hs := sinTwo_mem_Icc hθ
  have h := Work.FTS.Nonlinear.FstarPkg.DthAux.DthQfunBound hi hi4 θ hθ
  have h1 : (1000 : ℝ) * (Real.sin (2 * θ)) ^ 2 ≤ 1000 * Real.sin (2 * θ) := by
    nlinarith [hs.1, hs.2]
  linarith [h, h1]

/-- The crude bound `|D_θ^m qfun| ≤ 1000` on `Iθ`, for `m ≤ 4`. -/
lemma qfun_iter_abs_le {m : ℕ} (hm : m ≤ 4) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.dthU^[m] Work.Spaces.qfun θ| ≤ 1000 := by
  rcases Nat.eq_zero_or_pos m with h | h
  · subst h
    simp only [Function.iterate_zero_apply]
    exact (Work.FTS.Nonlinear.FstarPkg.DthAux.abs_qfun_le θ).trans (by norm_num)
  · refine (dthU_qfun_le_sin h (by omega) hθ).trans ?_
    have hs := sinTwo_mem_Icc hθ
    linarith [hs.1, hs.2]

/-! ## The constant sequence and the induction hypothesis -/

/-- The geometric sequence of constants of the induction: `KB (j+1) = 20000 * KB j`, with
`KB j ≥ 2·10^7 · 20000^{j-1}` for `j ≥ 1`. -/
noncomputable def KB (j : ℕ) : ℝ := (20000 : ℝ) ^ j * 20000000

lemma KB_pos (j : ℕ) : 0 < KB j := by
  rw [KB]; positivity

lemma KB_succ (j : ℕ) : KB (j + 1) = 20000 * KB j := by
  rw [KB, KB, pow_succ]; ring

lemma KB_mono {j k : ℕ} (hjk : j ≤ k) : KB j ≤ KB k := by
  rw [KB, KB]
  have h1 : (20000 : ℝ) ^ j ≤ (20000 : ℝ) ^ k :=
    pow_le_pow_right₀ (by norm_num) hjk
  exact mul_le_mul_of_nonneg_right h1 (by norm_num)

/-- `KB 1` dominates the constant of the base case of the induction. -/
lemma KB_one_ge : (17001000 : ℝ) ≤ KB 1 := by
  rw [KB]; norm_num

/-- `Hyp j` controls the `D_θ`-iterates of `Tfun j α` up to order `4 - j` by
`KB j · (α + sin 2θ)`, uniformly for `0 < α ≤ 1` and `θ ∈ Iθ`. -/
def Hyp (j : ℕ) : Prop :=
  ∀ (α θ : ℝ), 0 < α → α ≤ 1 → θ ∈ Work.Spaces.Iθ → ∀ k : ℕ, k ≤ 4 - j →
    |Work.Spaces.dthU^[k] (Work.Spaces.Tfun j α) θ| ≤ KB j * (α + Real.sin (2 * θ))

/-! ## The pointwise Leibniz rule and the bound for the corrections -/

/-- Pointwise form of the iterated Leibniz rule for `dthU`. -/
lemma dthU_iter_mul_apply (m : ℕ) (f g : ℝ → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (θ : ℝ) :
    Work.Spaces.dthU^[m] (f * g) θ
      = ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ)
          * (Work.Spaces.dthU^[i] f θ * Work.Spaces.dthU^[m - i] g θ) := by
  have h := congrFun (Work.Spaces.dthU_iter_mul m f g hf hg) θ
  simp only [Finset.sum_apply, Work.Spaces.dthCoef_apply] at h
  exact h

/-- The `D_θ^k (α q · Q)` correction term of the Leibniz expansion is bounded by
`16000 · α · KX` whenever `|D_θ^m Q| ≤ KX` for `m ≤ k ≤ 4`. -/
lemma alpha_qfun_leibniz_abs_le (k : ℕ) (hk : k ≤ 4) {α : ℝ} (hα : 0 < α)
    {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) {Q : ℝ → ℝ} {KX : ℝ}
    (hQ : ∀ m : ℕ, m ≤ k → |Work.Spaces.dthU^[m] Q θ| ≤ KX) :
    |∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ)
        * (Work.Spaces.dthU^[i] (fun θ => α * Work.Spaces.qfun θ) θ
          * Work.Spaces.dthU^[k - i] Q θ)| ≤ 16000 * α * KX := by
  have hα0 : 0 ≤ α := le_of_lt hα
  have hKX : 0 ≤ KX := le_trans (abs_nonneg (Q θ)) (hQ 0 (Nat.zero_le k))
  have hbinom : (∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ)) = (2 : ℝ) ^ k := by
    have h : ((∑ i ∈ Finset.range (k + 1), k.choose i : ℕ) : ℝ) = (2 : ℝ) ^ k := by
      rw [Nat.sum_range_choose]; push_cast; ring
    simpa using h
  have hterm : ∀ i ∈ Finset.range (k + 1),
      |(k.choose i : ℝ) * (Work.Spaces.dthU^[i] (fun θ => α * Work.Spaces.qfun θ) θ
          * Work.Spaces.dthU^[k - i] Q θ)| ≤ (k.choose i : ℝ) * (1000 * α * KX) := by
    intro i hi
    have hik : i ≤ k := by have := Finset.mem_range.mp hi; omega
    have hcast : (0 : ℝ) ≤ (k.choose i : ℝ) := Nat.cast_nonneg _
    have h1 : |Work.Spaces.dthU^[i] (fun θ => α * Work.Spaces.qfun θ) θ| ≤ 1000 * α := by
      have hrew : Work.Spaces.dthU^[i] (fun θ => α * Work.Spaces.qfun θ) θ
          = α * Work.Spaces.dthU^[i] Work.Spaces.qfun θ :=
        congrFun (Work.Spaces.dthU_iter_const_mul i α Work.Spaces.qfun) θ
      rw [hrew, abs_mul, abs_of_pos hα]
      calc α * |Work.Spaces.dthU^[i] Work.Spaces.qfun θ| ≤ α * 1000 :=
            mul_le_mul_of_nonneg_left (qfun_iter_abs_le (by omega) hθ) hα0
        _ = 1000 * α := by ring
    have h2 : |Work.Spaces.dthU^[k - i] Q θ| ≤ KX := hQ (k - i) (Nat.sub_le k i)
    calc |(k.choose i : ℝ) * (Work.Spaces.dthU^[i] (fun θ => α * Work.Spaces.qfun θ) θ
            * Work.Spaces.dthU^[k - i] Q θ)|
        = (k.choose i : ℝ) * (|Work.Spaces.dthU^[i] (fun θ => α * Work.Spaces.qfun θ) θ|
            * |Work.Spaces.dthU^[k - i] Q θ|) := by
          rw [abs_mul, abs_mul, abs_of_nonneg hcast]
      _ ≤ (k.choose i : ℝ) * (1000 * α * KX) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul h1 h2 (abs_nonneg _) (by positivity)) hcast
  calc |∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ)
        * (Work.Spaces.dthU^[i] (fun θ => α * Work.Spaces.qfun θ) θ
          * Work.Spaces.dthU^[k - i] Q θ)|
      ≤ ∑ i ∈ Finset.range (k + 1),
          |(k.choose i : ℝ) * (Work.Spaces.dthU^[i] (fun θ => α * Work.Spaces.qfun θ) θ
            * Work.Spaces.dthU^[k - i] Q θ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * (1000 * α * KX) :=
        Finset.sum_le_sum hterm
    _ = (∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ)) * (1000 * α * KX) := by
        rw [Finset.sum_mul]
    _ = (2 : ℝ) ^ k * (1000 * α * KX) := by rw [hbinom]
    _ ≤ 16 * (1000 * α * KX) := by
        have h2k : (2 : ℝ) ^ k ≤ 16 := by
          calc (2 : ℝ) ^ k ≤ (2 : ℝ) ^ 4 := pow_le_pow_right₀ (by norm_num) hk
            _ = 16 := by norm_num
        exact mul_le_mul_of_nonneg_right h2k (by positivity)
    _ = 16000 * α * KX := by ring

end Work.FTS.Nonlinear.Pieces.RNP
