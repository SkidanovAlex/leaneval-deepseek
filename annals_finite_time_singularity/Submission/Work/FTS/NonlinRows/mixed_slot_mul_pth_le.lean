import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.IntervalCases
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.OpenPkg.ProdOpen.leibniz_open_mixed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.NonlinRows

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-!
# The non-linear mixed slot `D_z^jD_θ^i(f · ∂_θ g)`

Pointwise estimate: the weighted mixed derivative
`D_z^jD_θ^i(f · ∂_θg) · Wt α` of a product of a datum `f` whose mixed derivatives are
`O(sin 2θ)` and the angular derivative of a datum `g` whose angular derivatives satisfy the
`sin 2θ`-divisibility estimate is bounded, in the `ℋ^6`-weight, by `K · C_ψ` times the
`ℋ^6`-integrand of `g`.

The proof is the Leibniz expansion `leibniz_open_mixed` followed by termwise bookkeeping:
each factor `D_z^aD_θ^b f` contributes the factor `sin 2θ` which, together with the
`sin 2θ` of the `C_ψ`-hypothesis, matches the `sin(2θ)^{-γ/2}` of the weight `Wt`.
-/

/-- `sin(2θ) > 0` on the open angular interval `(0,π/2)`. -/
theorem msp_sin_two_pos {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    0 < Real.sin (2 * θ) := by
  have h1 : 0 < 2 * θ := by linarith [hθ.1]
  have h2 : 2 * θ < Real.pi := by have := Real.pi_pos; linarith [hθ.2]
  exact Real.sin_pos_of_pos_of_lt_pi h1 h2

/-- The weight `Wt α z θ = w z · sin(2θ)^{-γ/2}` is nonnegative on `(0,π/2)`. -/
theorem msp_Wt_nonneg (α z θ : ℝ) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    0 ≤ Work.Spaces.Wt α z θ := by
  have hs : 0 ≤ Real.sin (2 * θ) := le_of_lt (msp_sin_two_pos hθ)
  rw [Work.Spaces.Wt, Work.Spaces.w, Work.Spaces.wTheta]
  exact mul_nonneg (div_nonneg (sq_nonneg _) (sq_nonneg _)) (Real.rpow_nonneg hs _)

/-- `(i.choose a : ℝ) ≤ 16` for `i ≤ 4`. -/
theorem msp_choose_le (i a : ℕ) (hi : i ≤ 4) : (i.choose a : ℝ) ≤ 16 := by
  have h : i.choose a ≤ 16 := by
    refine le_trans (Nat.choose_le_two_pow i a) ?_
    interval_cases i <;> norm_num
  exact_mod_cast h

/-- Pulling the absolute value out of a product with two nonnegative factors. -/
theorem msp_abs_factor {c A B W : ℝ} (hW : 0 ≤ W) (hc : 0 ≤ c) :
    |c * (A * B) * W| = c * (|A| * |B| * W) := by
  rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hW, abs_of_nonneg hc]
  ring

/-- **The per-Leibniz-summand bound.**  For `a ≤ i`, `b ≤ j` the summand of the Leibniz
expansion of `D_z^jD_θ^i(f · ∂_θg)` is dominated by
`256·K·C_ψ·∑_{1≤m≤i+1}|D_z^{j-b}D_θ^m g · Wt α|`. -/
theorem msp_term_le {α K Cpsi : ℝ} {f g : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2))
    (hK : ∀ b a : ℕ, a + b ≤ 4 → |Work.Spaces.mixed b a f z θ| ≤ K * Real.sin (2 * θ))
    (hpsi : ∀ c r : ℕ, r ≤ 4 →
      |Real.sin (2 * θ) * Work.Spaces.mixed c r (Work.Spaces.pth g) z θ|
        ≤ Cpsi * ∑ m ∈ Finset.Icc 1 (r + 1), |Work.Spaces.mixed c m g z θ|)
    (hK0 : 0 ≤ K) (hC0 : 0 ≤ Cpsi)
    {i j a b : ℕ} (ha : a ≤ i) (hb : b ≤ j) (hi : i ≤ 4) (hij : i + j ≤ 4) :
    |((i.choose a : ℝ) * (j.choose b : ℝ))
        * (Work.Spaces.mixed b a f z θ
            * Work.Spaces.mixed (j - b) (i - a) (Work.Spaces.pth g) z θ)
        * Work.Spaces.Wt α z θ|
      ≤ 256 * (K * Cpsi) * (∑ m ∈ Finset.Icc 1 (i + 1),
          |Work.Spaces.mixed (j - b) m g z θ * Work.Spaces.Wt α z θ|) := by
  have hs := msp_sin_two_pos hθ
  have hW := msp_Wt_nonneg α z θ hθ
  have hcoef : (0 : ℝ) ≤ (i.choose a : ℝ) * (j.choose b : ℝ) := by positivity
  have hcoef16 : (i.choose a : ℝ) * (j.choose b : ℝ) ≤ 256 := by
    calc (i.choose a : ℝ) * (j.choose b : ℝ) ≤ 16 * 16 :=
          mul_le_mul (msp_choose_le i a hi) (msp_choose_le j b (by omega))
            (by positivity) (by norm_num)
      _ = 256 := by norm_num
  have hab : a + b ≤ 4 := by omega
  have hir : i - a ≤ 4 := by omega
  have hA : |Work.Spaces.mixed b a f z θ| ≤ K * Real.sin (2 * θ) := hK b a hab
  have hB0 := hpsi (j - b) (i - a) hir
  have hBm : Real.sin (2 * θ)
        * |Work.Spaces.mixed (j - b) (i - a) (Work.Spaces.pth g) z θ|
      = |Real.sin (2 * θ)
          * Work.Spaces.mixed (j - b) (i - a) (Work.Spaces.pth g) z θ| := by
    rw [abs_mul, abs_of_pos hs]
  have hsub : Finset.Icc 1 (i - a + 1) ⊆ Finset.Icc 1 (i + 1) := by
    intro m hm
    rw [Finset.mem_Icc] at hm ⊢
    omega
  have hB : Real.sin (2 * θ)
        * |Work.Spaces.mixed (j - b) (i - a) (Work.Spaces.pth g) z θ|
      ≤ Cpsi * ∑ m ∈ Finset.Icc 1 (i + 1), |Work.Spaces.mixed (j - b) m g z θ| := by
    rw [hBm]
    refine le_trans hB0 (mul_le_mul_of_nonneg_left ?_ hC0)
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun m _ _ => abs_nonneg _)
  have hSW : (∑ m ∈ Finset.Icc 1 (i + 1), |Work.Spaces.mixed (j - b) m g z θ|)
        * Work.Spaces.Wt α z θ
      = ∑ m ∈ Finset.Icc 1 (i + 1),
          |Work.Spaces.mixed (j - b) m g z θ * Work.Spaces.Wt α z θ| := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [abs_mul, abs_of_nonneg hW]
  calc |((i.choose a : ℝ) * (j.choose b : ℝ))
        * (Work.Spaces.mixed b a f z θ
            * Work.Spaces.mixed (j - b) (i - a) (Work.Spaces.pth g) z θ)
        * Work.Spaces.Wt α z θ|
      = ((i.choose a : ℝ) * (j.choose b : ℝ))
          * (|Work.Spaces.mixed b a f z θ|
              * |Work.Spaces.mixed (j - b) (i - a) (Work.Spaces.pth g) z θ|
              * Work.Spaces.Wt α z θ) := msp_abs_factor hW hcoef
    _ ≤ ((i.choose a : ℝ) * (j.choose b : ℝ))
          * ((K * Real.sin (2 * θ))
              * |Work.Spaces.mixed (j - b) (i - a) (Work.Spaces.pth g) z θ|
              * Work.Spaces.Wt α z θ) := by
        refine mul_le_mul_of_nonneg_left ?_ hcoef
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hA (abs_nonneg _)) hW
    _ = ((i.choose a : ℝ) * (j.choose b : ℝ))
          * (K * (Real.sin (2 * θ)
              * |Work.Spaces.mixed (j - b) (i - a) (Work.Spaces.pth g) z θ|)
            * Work.Spaces.Wt α z θ) := by ring
    _ ≤ ((i.choose a : ℝ) * (j.choose b : ℝ))
          * (K * (Cpsi * ∑ m ∈ Finset.Icc 1 (i + 1),
              |Work.Spaces.mixed (j - b) m g z θ|) * Work.Spaces.Wt α z θ) := by
        refine mul_le_mul_of_nonneg_left ?_ hcoef
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hB hK0) hW
    _ = ((i.choose a : ℝ) * (j.choose b : ℝ)) * (K * Cpsi)
          * ((∑ m ∈ Finset.Icc 1 (i + 1), |Work.Spaces.mixed (j - b) m g z θ|)
              * Work.Spaces.Wt α z θ) := by ring
    _ = ((i.choose a : ℝ) * (j.choose b : ℝ)) * (K * Cpsi)
          * (∑ m ∈ Finset.Icc 1 (i + 1),
              |Work.Spaces.mixed (j - b) m g z θ * Work.Spaces.Wt α z θ|) := by rw [hSW]
    _ ≤ 256 * (K * Cpsi)
          * (∑ m ∈ Finset.Icc 1 (i + 1),
              |Work.Spaces.mixed (j - b) m g z θ * Work.Spaces.Wt α z θ|) := by
        refine mul_le_mul_of_nonneg_right ?_ (Finset.sum_nonneg fun m _ => abs_nonneg _)
        exact mul_le_mul_of_nonneg_right hcoef16 (mul_nonneg hK0 hC0)

/-- **The main pointwise bound.** -/
theorem msp_main (α : ℝ) (hα : 0 < α) (f g : ℝ → ℝ → ℝ)
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (K : ℝ) (hK : 0 < K)
    (hfK : ∀ (z : ℝ), 0 < z → ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), ∀ b a : ℕ, a + b ≤ 4 →
      |Work.Spaces.mixed b a f z θ| ≤ K * Real.sin (2 * θ))
    (Cpsi : ℝ) (hCpsi : 0 < Cpsi)
    (hpsi : ∀ (c r : ℕ), r ≤ 4 → ∀ (z : ℝ) (θ : ℝ), 0 < z →
      θ ∈ Set.Ioo 0 (Real.pi / 2) →
      |Real.sin (2 * θ) * Work.Spaces.mixed c r (Work.Spaces.pth g) z θ|
        ≤ Cpsi * ∑ m ∈ Finset.Icc 1 (r + 1), |Work.Spaces.mixed c m g z θ|)
    (j i : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ 4) (z θ : ℝ) (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    (Work.Spaces.mixed j i (fun z θ => f z θ * Work.Spaces.pth g z θ) z θ
        * Work.Spaces.Wt α z θ) ^ 2
      ≤ 1000000000000 * (max Cpsi 1) ^ 2 * K ^ 2
        * Work.Spaces.HkIntegrand α 6 g z θ := by
  have hK0 : 0 ≤ K := le_of_lt hK
  have hC0 : 0 ≤ Cpsi := le_of_lt hCpsi
  have hHk : 0 ≤ Work.Spaces.HkIntegrand α 6 g z θ :=
    Work.Spaces.HkIntegrand_nonneg α 6 g z θ
  have hX := Work.FTS.OpenPkg.ProdOpen.leibniz_open_mixed j i f (Work.Spaces.pth g)
    hf hg.pth z θ hz hθ.1 hθ.2
  set Hk : ℝ := Work.Spaces.HkIntegrand α 6 g z θ with hHkdef
  have hHk' : 0 ≤ Hk := by rw [hHkdef]; exact hHk
  set Y : ℕ → ℕ → ℕ → ℝ :=
    fun a b m => |Work.Spaces.mixed (j - b) m g z θ * Work.Spaces.Wt α z θ| with hY
  set Z : ℝ := ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
      ∑ m ∈ Finset.Icc 1 (i + 1), Y a b m with hZ
  -- cardinality bounds
  have hcardΦ : ((Finset.range (i + 1)).card : ℝ) ≤ 5 := by
    rw [Finset.card_range]; exact_mod_cast (show i + 1 ≤ 5 by omega)
  have hcardΨ : ((Finset.range (j + 1)).card : ℝ) ≤ 4 := by
    rw [Finset.card_range]; exact_mod_cast (show j + 1 ≤ 4 by omega)
  have hcardM : ((Finset.Icc 1 (i + 1)).card : ℝ) ≤ 5 := by
    rw [Nat.card_Icc]
    have h : (i + 1) + 1 - 1 = i + 1 := by omega
    rw [h]; exact_mod_cast (show i + 1 ≤ 5 by omega)
  -- each summand of the majorant is a slot of the `ℋ^6`-integrand of `g`
  have hYsq : ∀ a b m : ℕ, b ≤ j → m ∈ Finset.Icc 1 (i + 1) → (Y a b m) ^ 2 ≤ Hk := by
    intro a b m hb hm
    have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
    have hm2 : m ≤ i + 1 := (Finset.mem_Icc.mp hm).2
    have hsub : m + (j - b) ≤ 6 := by omega
    have h := Work.Spaces.sq_le_HkIntegrand_mixed α 6 g z θ m (j - b) hm1 hsub
    have hunf : Y a b m = |Work.Spaces.mixed (j - b) m g z θ * Work.Spaces.Wt α z θ| := by
      simp only [hY]
    rw [hunf, sq_abs]
    exact h
  have hT : ∀ a b : ℕ, b ≤ j →
      (∑ m ∈ Finset.Icc 1 (i + 1), Y a b m) ^ 2 ≤ 25 * Hk := by
    intro a b hb
    have h1 := sq_sum_le_card_mul_sum_sq (s := Finset.Icc 1 (i + 1)) (f := Y a b)
    have h2 : ∑ m ∈ Finset.Icc 1 (i + 1), (Y a b m) ^ 2
        ≤ ((Finset.Icc 1 (i + 1)).card : ℝ) * Hk := by
      have h := Finset.sum_le_card_nsmul (Finset.Icc 1 (i + 1))
        (fun m => (Y a b m) ^ 2) Hk (fun m hm => hYsq a b m hb hm)
      simpa [nsmul_eq_mul] using h
    have h3 : ∑ m ∈ Finset.Icc 1 (i + 1), (Y a b m) ^ 2 ≤ 5 * Hk :=
      le_trans h2 (mul_le_mul_of_nonneg_right hcardM hHk')
    calc (∑ m ∈ Finset.Icc 1 (i + 1), Y a b m) ^ 2
        ≤ ((Finset.Icc 1 (i + 1)).card : ℝ)
            * ∑ m ∈ Finset.Icc 1 (i + 1), (Y a b m) ^ 2 := h1
      _ ≤ 5 * (5 * Hk) :=
          mul_le_mul hcardM h3 (Finset.sum_nonneg fun m _ => sq_nonneg _) (by norm_num)
      _ = 25 * Hk := by ring
  have hS : ∀ a : ℕ,
      (∑ b ∈ Finset.range (j + 1), ∑ m ∈ Finset.Icc 1 (i + 1), Y a b m) ^ 2
        ≤ 400 * Hk := by
    intro a
    have h1 := sq_sum_le_card_mul_sum_sq (s := Finset.range (j + 1))
      (f := fun b => ∑ m ∈ Finset.Icc 1 (i + 1), Y a b m)
    have h2a : ∑ b ∈ Finset.range (j + 1),
          (∑ m ∈ Finset.Icc 1 (i + 1), Y a b m) ^ 2
        ≤ ((Finset.range (j + 1)).card : ℝ) * (25 * Hk) := by
      calc ∑ b ∈ Finset.range (j + 1), (∑ m ∈ Finset.Icc 1 (i + 1), Y a b m) ^ 2
          ≤ ∑ _b ∈ Finset.range (j + 1), 25 * Hk :=
            Finset.sum_le_sum fun b hb =>
              hT a b (by have := Finset.mem_range.mp hb; omega)
        _ = ((Finset.range (j + 1)).card : ℝ) * (25 * Hk) := by
            rw [Finset.sum_const, nsmul_eq_mul]
    have h2 : ∑ b ∈ Finset.range (j + 1),
          (∑ m ∈ Finset.Icc 1 (i + 1), Y a b m) ^ 2 ≤ 4 * (25 * Hk) :=
      le_trans h2a (mul_le_mul_of_nonneg_right hcardΨ (by positivity))
    calc (∑ b ∈ Finset.range (j + 1), ∑ m ∈ Finset.Icc 1 (i + 1), Y a b m) ^ 2
        ≤ ((Finset.range (j + 1)).card : ℝ)
            * ∑ b ∈ Finset.range (j + 1), (∑ m ∈ Finset.Icc 1 (i + 1), Y a b m) ^ 2 := h1
      _ ≤ 4 * (4 * (25 * Hk)) :=
          mul_le_mul hcardΨ h2 (Finset.sum_nonneg fun b _ => sq_nonneg _) (by norm_num)
      _ = 400 * Hk := by ring
  have hZnn : 0 ≤ Z := by
    rw [hZ]
    refine Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ =>
      Finset.sum_nonneg fun m _ => ?_
    simp only [hY]
    exact abs_nonneg _
  have hZ2 : Z ^ 2 ≤ 10000 * Hk := by
    rw [hZ]
    have h1 := sq_sum_le_card_mul_sum_sq (s := Finset.range (i + 1))
      (f := fun a => ∑ b ∈ Finset.range (j + 1), ∑ m ∈ Finset.Icc 1 (i + 1), Y a b m)
    have h2a : ∑ a ∈ Finset.range (i + 1),
          (∑ b ∈ Finset.range (j + 1), ∑ m ∈ Finset.Icc 1 (i + 1), Y a b m) ^ 2
        ≤ ((Finset.range (i + 1)).card : ℝ) * (400 * Hk) := by
      calc ∑ a ∈ Finset.range (i + 1),
            (∑ b ∈ Finset.range (j + 1), ∑ m ∈ Finset.Icc 1 (i + 1), Y a b m) ^ 2
          ≤ ∑ _a ∈ Finset.range (i + 1), 400 * Hk := Finset.sum_le_sum fun a _ => hS a
        _ = ((Finset.range (i + 1)).card : ℝ) * (400 * Hk) := by
            rw [Finset.sum_const, nsmul_eq_mul]
    have h2 : ∑ a ∈ Finset.range (i + 1),
          (∑ b ∈ Finset.range (j + 1), ∑ m ∈ Finset.Icc 1 (i + 1), Y a b m) ^ 2
        ≤ 5 * (400 * Hk) :=
      le_trans h2a (mul_le_mul_of_nonneg_right hcardΦ (by positivity))
    calc (∑ a ∈ Finset.range (i + 1),
          ∑ b ∈ Finset.range (j + 1), ∑ m ∈ Finset.Icc 1 (i + 1), Y a b m) ^ 2
        ≤ ((Finset.range (i + 1)).card : ℝ)
            * ∑ a ∈ Finset.range (i + 1),
                (∑ b ∈ Finset.range (j + 1),
                  ∑ m ∈ Finset.Icc 1 (i + 1), Y a b m) ^ 2 := h1
      _ ≤ 5 * (5 * (400 * Hk)) :=
          mul_le_mul hcardΦ h2 (Finset.sum_nonneg fun a _ => sq_nonneg _) (by norm_num)
      _ = 10000 * Hk := by ring
  -- the Leibniz expansion, bounded termwise
  have hbound1 : |Work.Spaces.mixed j i (fun z θ => f z θ * Work.Spaces.pth g z θ) z θ
        * Work.Spaces.Wt α z θ| ≤ 256 * (K * Cpsi) * Z := by
    rw [hX, hZ]
    simp only [Finset.sum_mul]
    calc |∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
            ((i.choose a : ℝ) * (j.choose b : ℝ))
              * (Work.Spaces.mixed b a f z θ
                  * Work.Spaces.mixed (j - b) (i - a) (Work.Spaces.pth g) z θ)
              * Work.Spaces.Wt α z θ|
        ≤ ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
            |((i.choose a : ℝ) * (j.choose b : ℝ))
              * (Work.Spaces.mixed b a f z θ
                  * Work.Spaces.mixed (j - b) (i - a) (Work.Spaces.pth g) z θ)
              * Work.Spaces.Wt α z θ| := by
          refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
          exact Finset.sum_le_sum fun a _ => Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
            256 * (K * Cpsi) * (∑ m ∈ Finset.Icc 1 (i + 1), Y a b m) := by
          refine Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun b hb => ?_
          have ha' : a ≤ i := by have := Finset.mem_range.mp ha; omega
          have hb' : b ≤ j := by have := Finset.mem_range.mp hb; omega
          simp only [hY]
          exact msp_term_le hθ (hfK z hz θ hθ) (fun c r hr => hpsi c r hr z θ hz hθ)
            hK0 hC0 ha' hb' (by omega) hij
      _ = 256 * (K * Cpsi) * Z := by
          rw [hZ]
          simp only [Finset.mul_sum]
  -- squaring
  have hsq : (Work.Spaces.mixed j i (fun z θ => f z θ * Work.Spaces.pth g z θ) z θ
        * Work.Spaces.Wt α z θ) ^ 2 ≤ (256 * (K * Cpsi) * Z) ^ 2 := by
    have h := pow_le_pow_left₀ (abs_nonneg _) hbound1 2
    rwa [sq_abs] at h
  have hCsq : Cpsi ^ 2 ≤ (max Cpsi 1) ^ 2 := pow_le_pow_left₀ hC0 (le_max_left _ _) 2
  have hMsq : (0 : ℝ) ≤ (max Cpsi 1) ^ 2 := sq_nonneg _
  calc (Work.Spaces.mixed j i (fun z θ => f z θ * Work.Spaces.pth g z θ) z θ
        * Work.Spaces.Wt α z θ) ^ 2
      ≤ (256 * (K * Cpsi) * Z) ^ 2 := hsq
    _ = (256 * (K * Cpsi)) ^ 2 * Z ^ 2 := by ring
    _ ≤ (256 * (K * Cpsi)) ^ 2 * (10000 * Hk) :=
        mul_le_mul_of_nonneg_left hZ2 (sq_nonneg _)
    _ = 65536 * (K ^ 2 * Cpsi ^ 2) * 10000 * Hk := by ring
    _ ≤ 1000000000000 * (K ^ 2 * (max Cpsi 1) ^ 2) * Hk := by
        have h1 : K ^ 2 * Cpsi ^ 2 ≤ K ^ 2 * (max Cpsi 1) ^ 2 :=
          mul_le_mul_of_nonneg_left hCsq (sq_nonneg K)
        calc 65536 * (K ^ 2 * Cpsi ^ 2) * 10000 * Hk
            = (65536 * 10000) * (K ^ 2 * Cpsi ^ 2) * Hk := by ring
          _ ≤ (65536 * 10000) * (K ^ 2 * (max Cpsi 1) ^ 2) * Hk :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 (by norm_num)) hHk'
          _ ≤ 1000000000000 * (K ^ 2 * (max Cpsi 1) ^ 2) * Hk :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right (by norm_num) (mul_nonneg (sq_nonneg K) hMsq))
                hHk'
    _ = 1000000000000 * (max Cpsi 1) ^ 2 * K ^ 2 * Hk := by ring

theorem mixed_slot_mul_pth_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → ∀ (f g : ℝ → ℝ → ℝ),
      Work.FTS.EllipticEst.SmoothOpen f → Work.FTS.EllipticEst.SmoothOpen g →
      ∀ (K : ℝ), 0 < K →
      (∀ (z : ℝ), 0 < z → ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), ∀ b a : ℕ, a + b ≤ 4 →
        |Work.Spaces.mixed b a f z θ| ≤ K * Real.sin (2 * θ)) →
      ∀ (Cpsi : ℝ), 0 < Cpsi →
      (∀ (c r : ℕ), r ≤ 4 → ∀ (z : ℝ) (θ : ℝ), 0 < z → θ ∈ Set.Ioo 0 (Real.pi / 2) →
        |Real.sin (2 * θ) * Work.Spaces.mixed c r (Work.Spaces.pth g) z θ|
          ≤ Cpsi * ∑ m ∈ Finset.Icc 1 (r + 1), |Work.Spaces.mixed c m g z θ|) →
      ∀ (j i : ℕ), 1 ≤ i → i + j ≤ 4 → ∀ (z : ℝ) (θ : ℝ), 0 < z → θ ∈ Set.Ioo 0 (Real.pi / 2) →
        (Work.Spaces.mixed j i (fun z θ => f z θ * Work.Spaces.pth g z θ) z θ
          * Work.Spaces.Wt α z θ) ^ 2
        ≤ C * (max Cpsi 1) ^ 2 * K ^ 2 * Work.Spaces.HkIntegrand α 6 g z θ := by
  refine ⟨1000000000000, by norm_num, ?_⟩
  intro α hα f g hf hg K hK hfK Cpsi hCpsi hpsi j i hi hij z θ hz hθ
  exact msp_main α hα f g hf hg K hK hfK Cpsi hCpsi hpsi j i hi hij z θ hz hθ

end Work.FTS.NonlinRows
