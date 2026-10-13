import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.Interval.Basic
import Submission.Work.FTS.PhiStar.StarDefs
import Submission.Work.FTS.PhiStar.FlatWAux.Linv_lop
import Submission.Work.FTS.PhiStar.LinvFlat.LinvLopAux
import Submission.Work.FTS.PhiStar.LinvFlat.LinvLopOde
import Submission.Work.FTS.PhiStar.LinvFlat.Linv_contDiffOn_hasDerivAt
import Submission.Work.Elliptic.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.DthIter_mul

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Linv_iter_uniform` — uniform control of the `Lop`-iterates of `Linv h`

`Linv h` is the `σ`-normalised zero-moment Dirichlet inverse of `L₀` (node P-G of the
`Φ_*` construction).  It solves the *first-order* linear equation

`Lop (Linv h) = -(h + L₂ · Linv h)`,   `L₂ θ = 5 cos 2θ - 1 = 10 cos²θ - 6`,

equivalently `Lop (Linv h) = (6 - 10 cos²θ)·Linv h - h`, where `Lop u = sin 2θ · u'`.

This file produces a **single** nonnegative sequence `C` — independent of the source `h`
and of the bound `K` — with

`|Lop^[i] (Linv h) θ| ≤ C i · K`,   `i ≤ 5`,   `θ ∈ (0, π/2)`,

from only: `|Linv h θ| ≤ K`, `|Lop^[a] h θ| ≤ K` for `a ≤ 4`, `h ∈ C⁹` on `(0, π/2)` and
`h · sinCos2 ∈ L¹(Iθ)`.  (The zero-moment hypothesis is part of the interface the consumer
uses but is not needed here: the ODE `LI_lop_Linv_eq` is valid without it.)

## Route

The prototype is `LinvFlat.LinvLopIter`, which proves the same statement with the stronger
hypothesis `|Lop^[a] h θ| ≤ K` for `a ≤ 8`.  Here only four source iterates are assumed, so
the induction stops at order `5`: at each step the recursion

`Lop^[n+1] (Linv h) = -(Lop^[n] h) - ∑_{a ≤ n} C(n,a) (Lop^[a] L₂)(Lop^[n-a] (Linv h))`

is obtained from the Leibniz rule for iterates of a product (`LI_lop_iter_Xfun_eqOn`), and
the explicit majorant `C i = 4·(10⁶(M₀+1))^i` closes the induction, where `M₀` is the
uniform bound for the iterates of `L₂` up to order `7` (`LI_L2fun_lop_bound`).  Since `M₀`
does not depend on `h` or `K`, the resulting sequence is uniform.
-/

open scoped Real Topology ContDiff Interval
open MeasureTheory Set Filter

noncomputable section

namespace Work.FTS.PhiStar.AngU

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

theorem Linv_iter_uniform : ∃ C : ℕ → ℝ, (∀ i : ℕ, 0 ≤ C i) ∧
    ∀ (h : ℝ → ℝ) (K : ℝ), 0 ≤ K →
      (∀ a : ℕ, a ≤ 4 → ∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
        |(Work.Spaces.Lop^[a]) h θ| ≤ K) →
      (∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
        |Work.FTS.PhiStar.Linv h θ| ≤ K) →
      ContDiffOn ℝ 9 h (Set.Ioo 0 (Real.pi / 2)) →
      MeasureTheory.IntegrableOn (fun θ => h θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ →
      (∫ θ in Work.Spaces.Iθ, h θ * Work.Elliptic.sinCos2 θ) = 0 →
      ∀ i : ℕ, i ≤ 5 → ∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
        |(Work.Spaces.Lop^[i]) (Work.FTS.PhiStar.Linv h) θ| ≤ C i * K := by
  -- a uniform bound `M₀` for the iterates of the coefficient `L₂` (order `≤ 7`)
  obtain ⟨M0, hM0nn, hM0⟩ := Work.FTS.PhiStar.LinvFlat.LI_L2fun_lop_bound
  refine ⟨fun i => Work.FTS.PhiStar.LinvFlat.LI_Cfun M0 i,
    fun i => Work.FTS.PhiStar.LinvFlat.LI_Cfun_nonneg hM0nn i, ?_⟩
  intro h K hK hiter hlinv hcd hint hmom i hi θ hθ
  have hU : IsOpen (Set.Ioo 0 (Real.pi / 2)) := isOpen_Ioo
  -- `Linv h` is `C^9` on the open interval
  have hg9 : ContDiffOn ℝ 9 (Work.FTS.PhiStar.Linv h) (Set.Ioo 0 (Real.pi / 2)) :=
    (Work.FTS.PhiStar.LinvFlat.Linv_contDiffOn_hasDerivAt (h := h) (n := 9) (by norm_num)
      hcd hint).1
  -- the first-order equation, in the form used by the iterate expansion
  have hode : Set.EqOn (Work.Spaces.Lop (Work.FTS.PhiStar.Linv h))
      (fun θ : ℝ => -(h θ + Work.FTS.PhiStar.LinvFlat.LI_L2fun θ
        * Work.FTS.PhiStar.Linv h θ))
      (Set.Ioo 0 (Real.pi / 2)) :=
    Work.FTS.PhiStar.LinvFlat.LI_lop_Linv_eq hcd hint
  -- the Leibniz recursion for the iterates of `Linv h`
  have hrec : ∀ n : ℕ, n ≤ 4 → ∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
      (Work.Spaces.Lop^[n + 1]) (Work.FTS.PhiStar.Linv h) θ
        = -(Work.Spaces.Lop^[n] h θ)
          - ∑ a ∈ Finset.range (n + 1), (n.choose a : ℝ) *
              ((Work.Spaces.Lop^[a]) Work.FTS.PhiStar.LinvFlat.LI_L2fun θ *
                (Work.Spaces.Lop^[n - a]) (Work.FTS.PhiStar.Linv h) θ) := by
    intro n hn4 θ hθ'
    have h1 : Set.EqOn (Work.Spaces.Lop^[n + 1] (Work.FTS.PhiStar.Linv h))
        (Work.Spaces.Lop^[n]
          (fun θ : ℝ => -(h θ + Work.FTS.PhiStar.LinvFlat.LI_L2fun θ
            * Work.FTS.PhiStar.Linv h θ)))
        (Set.Ioo 0 (Real.pi / 2)) := by
      rw [show (Work.Spaces.Lop^[n + 1]) (Work.FTS.PhiStar.Linv h)
          = (Work.Spaces.Lop^[n]) (Work.Spaces.Lop (Work.FTS.PhiStar.Linv h))
          from Function.iterate_succ_apply (f := Work.Spaces.Lop) n
            (Work.FTS.PhiStar.Linv h)]
      exact Work.FTS.PhiStar.LinvFlat.LI_Lop_iter_congr_eqOn hU n hode
    have h2 := Work.FTS.PhiStar.LinvFlat.LI_lop_iter_Xfun_eqOn hcd hg9 (k := n) (by omega)
    exact h1.trans h2 hθ'
  -- the induction producing the uniform constant
  have key : ∀ n : ℕ, n ≤ 5 → ∀ b : ℕ, b ≤ n → ∀ θ : ℝ,
      θ ∈ Set.Ioo 0 (Real.pi / 2) →
      |(Work.Spaces.Lop^[b]) (Work.FTS.PhiStar.Linv h) θ|
        ≤ Work.FTS.PhiStar.LinvFlat.LI_Cfun M0 b * K := by
    intro n
    induction n with
    | zero =>
        intro _ b hb θ hθ'
        obtain rfl : b = 0 := Nat.le_zero.mp hb
        have hL : (Work.Spaces.Lop^[0]) (Work.FTS.PhiStar.Linv h) θ
            = Work.FTS.PhiStar.Linv h θ := rfl
        have hC0 : Work.FTS.PhiStar.LinvFlat.LI_Cfun M0 0 = 4 := by
          show 4 * (1000000 * (M0 + 1)) ^ 0 = 4
          rw [pow_zero]; ring
        rw [hL, hC0]
        calc |Work.FTS.PhiStar.Linv h θ| ≤ K := hlinv θ hθ'
          _ ≤ 4 * K := by linarith [hK]
    | succ n ih =>
        intro hn b hb θ hθ'
        by_cases hbn : b ≤ n
        · exact ih (by omega) b hbn θ hθ'
        · have hbeq : b = n + 1 := by omega
          subst hbeq
          have hn4 : n ≤ 4 := by omega
          rw [hrec n hn4 θ hθ']
          have hX : |(Work.Spaces.Lop^[n]) h θ| ≤ K := hiter n hn4 θ hθ'
          have hterm : ∀ a ∈ Finset.range (n + 1),
              |(n.choose a : ℝ) * ((Work.Spaces.Lop^[a])
                Work.FTS.PhiStar.LinvFlat.LI_L2fun θ *
                (Work.Spaces.Lop^[n - a]) (Work.FTS.PhiStar.Linv h) θ)|
                ≤ 256 * (M0 * (Work.FTS.PhiStar.LinvFlat.LI_Cfun M0 n * K)) := by
            intro a ha
            have haj : a ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
            have hc0 : (0 : ℝ) ≤ (n.choose a : ℝ) := by positivity
            have hcB : (n.choose a : ℝ) ≤ 256 := by
              have h1 : n.choose a ≤ 2 ^ n := Nat.choose_le_two_pow n a
              have h2 : 2 ^ n ≤ 2 ^ 8 :=
                pow_le_pow_right' (by norm_num : (1 : ℕ) ≤ 2) (by omega)
              have h3 : 2 ^ 8 = (256 : ℕ) := by norm_num
              exact_mod_cast (le_trans h1 (le_trans h2 (le_of_eq h3)))
            rw [abs_mul, abs_of_nonneg hc0, abs_mul]
            have hL2 : |(Work.Spaces.Lop^[a]) Work.FTS.PhiStar.LinvFlat.LI_L2fun θ| ≤ M0 :=
              hM0 a (by omega) θ
            have hgv : |(Work.Spaces.Lop^[n - a]) (Work.FTS.PhiStar.Linv h) θ|
                ≤ Work.FTS.PhiStar.LinvFlat.LI_Cfun M0 (n - a) * K :=
              ih (by omega) (n - a) (by omega) θ hθ'
            have hCf : Work.FTS.PhiStar.LinvFlat.LI_Cfun M0 (n - a)
                ≤ Work.FTS.PhiStar.LinvFlat.LI_Cfun M0 n :=
              Work.FTS.PhiStar.LinvFlat.LI_Cfun_mono hM0nn (Nat.sub_le n a)
            have hBnd : |(Work.Spaces.Lop^[a]) Work.FTS.PhiStar.LinvFlat.LI_L2fun θ| *
                |(Work.Spaces.Lop^[n - a]) (Work.FTS.PhiStar.Linv h) θ|
                ≤ M0 * (Work.FTS.PhiStar.LinvFlat.LI_Cfun M0 n * K) := by
              refine mul_le_mul hL2 ?_ (abs_nonneg _) hM0nn
              exact le_trans hgv (mul_le_mul_of_nonneg_right hCf hK)
            exact mul_le_mul hcB hBnd (mul_nonneg (abs_nonneg _) (abs_nonneg _))
              (by norm_num)
          have hSabs : |∑ a ∈ Finset.range (n + 1), (n.choose a : ℝ) *
                ((Work.Spaces.Lop^[a]) Work.FTS.PhiStar.LinvFlat.LI_L2fun θ *
                  (Work.Spaces.Lop^[n - a]) (Work.FTS.PhiStar.Linv h) θ)|
              ≤ 2048 * (M0 * (Work.FTS.PhiStar.LinvFlat.LI_Cfun M0 n * K)) := by
            refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
            have h2 : ∑ a ∈ Finset.range (n + 1),
                |(n.choose a : ℝ) * ((Work.Spaces.Lop^[a])
                  Work.FTS.PhiStar.LinvFlat.LI_L2fun θ *
                  (Work.Spaces.Lop^[n - a]) (Work.FTS.PhiStar.Linv h) θ)|
                ≤ (Finset.range (n + 1)).card •
                  (256 * (M0 * (Work.FTS.PhiStar.LinvFlat.LI_Cfun M0 n * K))) :=
              Finset.sum_le_card_nsmul _ _ _ (fun a ha => hterm a ha)
            refine le_trans h2 ?_
            rw [Finset.card_range, nsmul_eq_mul]
            have hn8 : (((n + 1 : ℕ)) : ℝ) ≤ 8 := by
              exact_mod_cast (by omega : n + 1 ≤ 8)
            have hY0 : (0 : ℝ)
                ≤ 256 * (M0 * (Work.FTS.PhiStar.LinvFlat.LI_Cfun M0 n * K)) := by
              have hcf : (0 : ℝ) ≤ Work.FTS.PhiStar.LinvFlat.LI_Cfun M0 n :=
                Work.FTS.PhiStar.LinvFlat.LI_Cfun_nonneg hM0nn n
              exact mul_nonneg (by norm_num) (mul_nonneg hM0nn (mul_nonneg hcf hK))
            calc (((n + 1 : ℕ)) : ℝ) *
                  (256 * (M0 * (Work.FTS.PhiStar.LinvFlat.LI_Cfun M0 n * K)))
                ≤ 8 * (256 * (M0 * (Work.FTS.PhiStar.LinvFlat.LI_Cfun M0 n * K))) :=
                  mul_le_mul_of_nonneg_right hn8 hY0
              _ = 2048 * (M0 * (Work.FTS.PhiStar.LinvFlat.LI_Cfun M0 n * K)) := by ring
          have hgoal : K + 2048 * (M0 * (Work.FTS.PhiStar.LinvFlat.LI_Cfun M0 n * K))
              ≤ Work.FTS.PhiStar.LinvFlat.LI_Cfun M0 (n + 1) * K := by
            have hCn1 : (1 : ℝ) ≤ Work.FTS.PhiStar.LinvFlat.LI_Cfun M0 n :=
              Work.FTS.PhiStar.LinvFlat.LI_Cfun_one_le hM0nn n
            have hCn0 : (0 : ℝ) ≤ Work.FTS.PhiStar.LinvFlat.LI_Cfun M0 n :=
              Work.FTS.PhiStar.LinvFlat.LI_Cfun_nonneg hM0nn n
            have hkey2 : 2048 * M0 * (Work.FTS.PhiStar.LinvFlat.LI_Cfun M0 n * K)
                ≤ ((1000000 * (M0 + 1)) - 1) *
                  (Work.FTS.PhiStar.LinvFlat.LI_Cfun M0 n * K) := by
              have h1 : 2048 * M0 ≤ (1000000 * (M0 + 1)) - 1 := by nlinarith [hM0nn]
              exact mul_le_mul_of_nonneg_right h1 (mul_nonneg hCn0 hK)
            have hAK : K ≤ Work.FTS.PhiStar.LinvFlat.LI_Cfun M0 n * K := by
              have := mul_le_mul_of_nonneg_right hCn1 hK
              simpa using this
            have hstepA : K + 2048 * (M0 * (Work.FTS.PhiStar.LinvFlat.LI_Cfun M0 n * K))
                ≤ K + ((1000000 * (M0 + 1)) - 1) *
                  (Work.FTS.PhiStar.LinvFlat.LI_Cfun M0 n * K) := by
              linarith [hkey2]
            have hstepB : K + ((1000000 * (M0 + 1)) - 1) *
                  (Work.FTS.PhiStar.LinvFlat.LI_Cfun M0 n * K)
                ≤ (Work.FTS.PhiStar.LinvFlat.LI_Cfun M0 n * (1000000 * (M0 + 1))) * K := by
              linarith [hAK]
            have hCsucc : Work.FTS.PhiStar.LinvFlat.LI_Cfun M0 (n + 1)
                = Work.FTS.PhiStar.LinvFlat.LI_Cfun M0 n * (1000000 * (M0 + 1)) := by
              show 4 * (1000000 * (M0 + 1)) ^ (n + 1)
                = 4 * (1000000 * (M0 + 1)) ^ n * (1000000 * (M0 + 1))
              rw [pow_succ]; ring
            rw [hCsucc]
            linarith [hstepA, hstepB]
          have htri : |-(Work.Spaces.Lop^[n] h θ)
              - ∑ a ∈ Finset.range (n + 1), (n.choose a : ℝ) *
                ((Work.Spaces.Lop^[a]) Work.FTS.PhiStar.LinvFlat.LI_L2fun θ *
                  (Work.Spaces.Lop^[n - a]) (Work.FTS.PhiStar.Linv h) θ)|
              ≤ K + 2048 * (M0 * (Work.FTS.PhiStar.LinvFlat.LI_Cfun M0 n * K)) := by
            have h1 : |-(Work.Spaces.Lop^[n] h θ)
                - ∑ a ∈ Finset.range (n + 1), (n.choose a : ℝ) *
                  ((Work.Spaces.Lop^[a]) Work.FTS.PhiStar.LinvFlat.LI_L2fun θ *
                    (Work.Spaces.Lop^[n - a]) (Work.FTS.PhiStar.Linv h) θ)|
                ≤ |(Work.Spaces.Lop^[n]) h θ|
                  + |∑ a ∈ Finset.range (n + 1), (n.choose a : ℝ) *
                    ((Work.Spaces.Lop^[a]) Work.FTS.PhiStar.LinvFlat.LI_L2fun θ *
                      (Work.Spaces.Lop^[n - a]) (Work.FTS.PhiStar.Linv h) θ)| := by
              calc |-(Work.Spaces.Lop^[n] h θ)
                    - ∑ a ∈ Finset.range (n + 1), (n.choose a : ℝ) *
                      ((Work.Spaces.Lop^[a]) Work.FTS.PhiStar.LinvFlat.LI_L2fun θ *
                        (Work.Spaces.Lop^[n - a]) (Work.FTS.PhiStar.Linv h) θ)|
                  = |(-(Work.Spaces.Lop^[n] h θ))
                      + (-(∑ a ∈ Finset.range (n + 1), (n.choose a : ℝ) *
                        ((Work.Spaces.Lop^[a]) Work.FTS.PhiStar.LinvFlat.LI_L2fun θ *
                          (Work.Spaces.Lop^[n - a]) (Work.FTS.PhiStar.Linv h) θ)))| := by
                    simp only [sub_eq_add_neg]
                _ ≤ |-(Work.Spaces.Lop^[n] h θ)|
                      + |-(∑ a ∈ Finset.range (n + 1), (n.choose a : ℝ) *
                        ((Work.Spaces.Lop^[a]) Work.FTS.PhiStar.LinvFlat.LI_L2fun θ *
                          (Work.Spaces.Lop^[n - a]) (Work.FTS.PhiStar.Linv h) θ))| :=
                    abs_add_le _ _
                _ = |(Work.Spaces.Lop^[n]) h θ|
                      + |∑ a ∈ Finset.range (n + 1), (n.choose a : ℝ) *
                        ((Work.Spaces.Lop^[a]) Work.FTS.PhiStar.LinvFlat.LI_L2fun θ *
                          (Work.Spaces.Lop^[n - a]) (Work.FTS.PhiStar.Linv h) θ)| := by
                    rw [abs_neg, abs_neg]
            linarith [h1, hX, hSabs]
          linarith [htri, hgoal]
  exact key 5 le_rfl i hi θ hθ

end Work.FTS.PhiStar.AngU
