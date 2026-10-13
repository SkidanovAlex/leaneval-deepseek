import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.H2.Transport3Aux.Z3Defs
import Submission.Work.FTS.H2.Transport3Aux.Z3Aux
import Submission.Work.FTS.H2.WPQ.Interior
import Submission.Work.FTS.H2.Transport3Aux.GoodThetaDefs
import Submission.Work.FTS.H2.Transport3Aux.mx_monomial_bound
import Submission.Work.FTS.H2.T3Q.MultQ

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology

namespace Work.FTS.H2.T3Q

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## The per-term bound, in the interior class

This is the verbatim port of `Work.FTS.H2.Transport3Aux.Z3.TM_abs_le` from the analytic class
`Work.Spaces.SmoothNbhd` (with `θ` in the closed quadrant `Iθ`) to the interior class
`Work.FTS.LocData.SmoothQuad` (with `θ` in the open quadrant `(0,π/2)`): the only change is the
multiplier bound `Work.FTS.H2.Transport3Aux.abs_mixed_le_WlInf` replaced by
`Work.FTS.H2.T3Q.abs_mixed_le_WlInf_Q` (both with the constant `30 |f|_{𝒲^{4,∞}}`).  The
`g`-side AM–GM lemma `Work.FTS.H2.Transport3Aux.abs_mixed_pair_mul_weight_le_HkIntegrand`, the
elementary facts `Work.FTS.H2.Wm_nonneg` / `Work.FTS.H2.Whz_Wm_sq` and the index bookkeeping
`Work.FTS.H2.Transport3Aux.Z3.mx_index_le` are class-free in `f` and are reused verbatim. -/

/-- A surviving mixed-slot Leibniz summand (`1 ≤ i`, `i + j ≤ 4`, `a < i`, `b ≤ j`, not the
order-five case `i + j = 4 ∧ a = 0 ∧ b = 0`) is bounded pointwise on the open quadrant by
`9000 |f|_{𝒲^{4,∞}} · HkIntegrand α 4 g`, for `f` of class `SmoothQuad` with `WlInfMem α 4 f`. -/
theorem TM_abs_le_Q (α : ℝ) (f g : ℝ → ℝ → ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (hsf : Work.FTS.LocData.SmoothQuad f) (hwf : Work.Spaces.WlInfMem α 4 f)
    (i j a b : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ 4) (ha : a < i) (hb : b ≤ j)
    (hfive : ¬ (i + j = 4 ∧ a = 0 ∧ b = 0)) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Set.Ioo 0 (π / 2),
      |Work.FTS.H2.Transport3Aux.Z3.TM α f g i j a b z θ| ≤ 9000 * Work.Spaces.WlInf α 4 f
        * Work.Spaces.HkIntegrand α 4 g z θ := by
  intro z hz θ hθ
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hI : 0 ≤ Work.Spaces.HkIntegrand α 4 g z θ :=
    Work.Spaces.HkIntegrand_nonneg α 4 g z θ
  have hW : 0 ≤ Work.Spaces.WlInf α 4 f := Work.Spaces.WlInf_nonneg α 4 f hwf
  obtain ⟨hr, hrp⟩ := Work.FTS.H2.Transport3Aux.Z3.mx_index_le i j a b hi hij ha hb hfive
  have hab : a + b ≤ 4 := by omega
  have hf1 : |Work.Spaces.mixed b a f z θ| ≤ 30 * Work.Spaces.WlInf α 4 f :=
    abs_mixed_le_WlInf_Q hα hα1 hsf hwf hab hz hθ
  have hgm : |Work.Spaces.mixed (j - b + 1) (i - a) g z θ| * |Work.Spaces.mixed j i g z θ|
      * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      ≤ Work.Spaces.HkIntegrand α 4 g z θ :=
    Work.FTS.H2.Transport3Aux.abs_mixed_pair_mul_weight_le_HkIntegrand α hα g hr hrp hi hij hθI
  have hWmnn : 0 ≤ Wm α z θ := Wm_nonneg α hθI
  have hi4 : i ≤ 4 := by omega
  have hj4 : j ≤ 4 := by omega
  have hcast : (i.choose a : ℝ) * (j.choose b : ℝ) ≤ 256 := by
    have h1 : (i.choose a : ℝ) ≤ 16 := by
      have h := Nat.choose_le_two_pow i a
      have h2 : ((2:ℕ)^i : ℝ) ≤ ((2:ℕ)^4 : ℝ) := by
        exact_mod_cast (Nat.pow_le_pow_right (by norm_num) hi4)
      have h3 : ((2:ℕ)^4 : ℝ) = 16 := by norm_num
      have h4 : (i.choose a : ℝ) ≤ ((2:ℕ)^i : ℝ) := by exact_mod_cast h
      linarith
    have h2 : (j.choose b : ℝ) ≤ 16 := by
      have h := Nat.choose_le_two_pow j b
      have h3 : ((2:ℕ)^j : ℝ) ≤ ((2:ℕ)^4 : ℝ) := by
        exact_mod_cast (Nat.pow_le_pow_right (by norm_num) hj4)
      have h4 : ((2:ℕ)^4 : ℝ) = 16 := by norm_num
      have h5 : (j.choose b : ℝ) ≤ ((2:ℕ)^j : ℝ) := by exact_mod_cast h
      linarith
    nlinarith [h1, h2, Nat.cast_nonneg (α := ℝ) (i.choose a),
      Nat.cast_nonneg (α := ℝ) (j.choose b)]
  have hsq : Wm α z θ * Wm α z θ
      = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
    rw [← sq]
    exact (Work.FTS.H2.Whz_Wm_sq α hα z θ hθI).2
  have hG : |Work.Spaces.mixed (j - b + 1) (i - a) g z θ| * |Work.Spaces.mixed j i g z θ|
      * (Wm α z θ * Wm α z θ) ≤ Work.Spaces.HkIntegrand α 4 g z θ := by
    rw [hsq]
    exact hgm
  have habs : |Work.FTS.H2.Transport3Aux.Z3.TM α f g i j a b z θ|
      = ((i.choose a : ℝ) * (j.choose b : ℝ)) * |Work.Spaces.mixed b a f z θ|
        * (|Work.Spaces.mixed (j - b + 1) (i - a) g z θ| * |Work.Spaces.mixed j i g z θ|
            * (Wm α z θ * Wm α z θ)) := by
    rw [Work.FTS.H2.Transport3Aux.Z3.TM]
    simp only [abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (i.choose a)),
      abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (j.choose b)), abs_of_nonneg hWmnn]
    ring
  rw [habs]
  have hstep : ((i.choose a : ℝ) * (j.choose b : ℝ)) * |Work.Spaces.mixed b a f z θ|
        * (|Work.Spaces.mixed (j - b + 1) (i - a) g z θ| * |Work.Spaces.mixed j i g z θ|
            * (Wm α z θ * Wm α z θ))
      ≤ 256 * (30 * Work.Spaces.WlInf α 4 f) * Work.Spaces.HkIntegrand α 4 g z θ :=
    mul_le_mul (mul_le_mul hcast hf1 (abs_nonneg _) (by positivity)) hG (by positivity)
      (by positivity)
  refine le_trans hstep ?_
  nlinarith [hW, hI]

/-- `Z3.Msurv α f g` (the surviving mixed-slot Leibniz sum of
`H4PairInt α (fun z θ => f z θ * D_z g z θ) g` after the order-five summands and the whole
mismatch family `a = i` have been removed, i.e. the sum over `1 ≤ i`, `i + j ≤ 4`, `a < i`,
`b ≤ j` of `C(i,a)C(j,b)·D_z^bD_θ^af·D_z^{j-b+1}D_θ^{i-a}g·(D_z^jD_θ^ig)·Wm²`) is bounded on
the open quadrant by `4500000 |f|_{𝒲^{4,∞}} · HkIntegrand α 4 g`, for `f` of class `SmoothQuad`
with `WlInfMem α 4 f`.

The proof is a verbatim port of `Work.FTS.H2.Transport3Aux.Z3Aux.Msurv_abs_le` (with its
per-term helper `TM_abs_le`), which proves the same statement in the stronger class
`Work.Spaces.SmoothNbhd f` and on the closed quadrant `θ ∈ Iθ`: replace the multiplier bound
`Work.FTS.H2.Transport3Aux.abs_mixed_le_WlInf` by
`Work.FTS.H2.T3Q.abs_mixed_le_WlInf_Q` (same constant `30|f|_𝒲`, interior class, hypothesis
`θ ∈ Set.Ioo 0 (π/2)`), keep the class-free `g`-lemmas
`Work.FTS.H2.Transport3Aux.abs_mixed_pair_mul_weight_le_HkIntegrand`,
`Work.FTS.H2.Transport3Aux.TM_abs_le`'s arithmetic helpers (`choose_le_two_pow`,
`Whz_Wm_sq`, `Wm_nonneg`), and restrict `θ` to `Set.Ioo 0 (π/2)`.  The index bookkeeping
`Z3.mx_index_le` and the sum bookkeeping `Z3.Msurv` are class-free and are reused verbatim.
`Work.FTS.H2.T3Q.MultQ` provides `abs_mixed_le_WlInf_Q` and the vanishing lemmas at
`sin(2θ) = 0`; do not redefine `abs_mixed_le_WlInf_Q`. -/
theorem Msurv_abs_le_Q (α : ℝ) (f g : ℝ → ℝ → ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (hsf : Work.FTS.LocData.SmoothQuad f) (hwf : Work.Spaces.WlInfMem α 4 f) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Set.Ioo 0 (π / 2),
      |Work.FTS.H2.Transport3Aux.Z3.Msurv α f g z θ| ≤ 4500000 * Work.Spaces.WlInf α 4 f
        * Work.Spaces.HkIntegrand α 4 g z θ := by
  intro z hz θ hθ
  set K : ℝ := Work.Spaces.WlInf α 4 f * Work.Spaces.HkIntegrand α 4 g z θ with hK
  have hK0 : 0 ≤ K := by
    rw [hK]
    exact mul_nonneg (Work.Spaces.WlInf_nonneg α 4 f hwf)
      (Work.Spaces.HkIntegrand_nonneg α 4 g z θ)
  have hslot : ∀ i ∈ Finset.range 5, ∀ j ∈ Finset.range 5,
      |(if 1 ≤ i ∧ i + j ≤ 4 then
          (∑ a ∈ Finset.range i, ∑ b ∈ Finset.range (j + 1),
            (if i + j = 4 ∧ a = 0 ∧ b = 0 then 0
              else Work.FTS.H2.Transport3Aux.Z3.TM α f g i j a b z θ)) else 0)|
        ≤ 180000 * K := by
    intro i hi j hj
    by_cases hc : 1 ≤ i ∧ i + j ≤ 4
    · rw [if_pos hc]
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      calc ∑ a ∈ Finset.range i,
            |∑ b ∈ Finset.range (j + 1),
              (if i + j = 4 ∧ a = 0 ∧ b = 0 then 0
                else Work.FTS.H2.Transport3Aux.Z3.TM α f g i j a b z θ)|
          ≤ ∑ a ∈ Finset.range i, ∑ b ∈ Finset.range (j + 1), (9000 * K) := by
            refine Finset.sum_le_sum fun a ha => ?_
            refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
            refine Finset.sum_le_sum fun b hb => ?_
            by_cases h5 : i + j = 4 ∧ a = 0 ∧ b = 0
            · rw [if_pos h5, abs_zero]
              exact mul_nonneg (by norm_num) hK0
            · rw [if_neg h5]
              have ha' : a < i := Finset.mem_range.mp ha
              have hb' : b ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
              have h := TM_abs_le_Q α f g hα hα1 hsf hwf i j a b hc.1 hc.2 ha' hb' h5 z hz θ hθ
              calc |Work.FTS.H2.Transport3Aux.Z3.TM α f g i j a b z θ|
                  ≤ 9000 * Work.Spaces.WlInf α 4 f * Work.Spaces.HkIntegrand α 4 g z θ := h
                _ = 9000 * K := by rw [hK]; ring
        _ = ((i : ℝ) * ((j : ℝ) + 1)) * (9000 * K) := by
            rw [Finset.sum_const, Finset.sum_const]
            simp only [Finset.card_range, nsmul_eq_mul]
            push_cast
            ring
        _ ≤ 180000 * K := by
            have hi4 : i ≤ 4 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
            have hj4 : j ≤ 4 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
            have h1 : (i : ℝ) ≤ 4 := by exact_mod_cast hi4
            have h2 : ((j : ℝ) + 1) ≤ 5 := by exact_mod_cast (by omega : j + 1 ≤ 5)
            have h3 : (i : ℝ) * ((j : ℝ) + 1) ≤ 20 :=
              by nlinarith [Nat.cast_nonneg (α := ℝ) i]
            nlinarith [hK0, h3]
    · rw [if_neg hc, abs_zero]
      exact mul_nonneg (by norm_num) hK0
  rw [Work.FTS.H2.Transport3Aux.Z3.Msurv]
  calc |∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5, (if 1 ≤ i ∧ i + j ≤ 4 then
          (∑ a ∈ Finset.range i, ∑ b ∈ Finset.range (j + 1),
            (if i + j = 4 ∧ a = 0 ∧ b = 0 then 0
              else Work.FTS.H2.Transport3Aux.Z3.TM α f g i j a b z θ)) else 0)|
      ≤ ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5, (180000 * K) := by
        refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
        refine Finset.sum_le_sum fun i hi => ?_
        refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
        exact Finset.sum_le_sum fun j hj => hslot i hi j hj
    _ = 25 * (180000 * K) := by
        rw [Finset.sum_const, Finset.sum_const]
        simp only [Finset.card_range, nsmul_eq_mul]
        ring
    _ = 4500000 * Work.Spaces.WlInf α 4 f * Work.Spaces.HkIntegrand α 4 g z θ := by
        rw [hK]; ring

end Work.FTS.H2.T3Q
