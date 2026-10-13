import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.Interval.Basic
import Submission.Work.FTS.PhiStar.StarDefs
import Submission.Work.FTS.PhiStar.LinvFlat.Linv_abs_le
import Submission.Work.FTS.PhiStar.LinvFlat.Linv_contDiffOn_hasDerivAt
import Submission.Work.FTS.PhiStar.LinvFlat.LinvLopAux
import Submission.Work.FTS.PhiStar.LinvFlat.LinvLopOde
import Submission.Work.FTS.PhiStar.LinvFlat.LinvBaseBound
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.DthIter_mul
import Submission.Work.Elliptic.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology ContDiff Interval
open MeasureTheory Set Filter

noncomputable section

namespace Work.FTS.PhiStar.LinvFlat

set_option maxHeartbeats 1600000

theorem LinvLopIter : ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧ ∀ (h : ℝ → ℝ) (K : ℝ), 0 ≤ K → ContinuousOn h (Set.Ioo 0 (Real.pi / 2)) → ContDiffOn ℝ 9 h (Set.Ioo 0 (Real.pi / 2)) → (∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) → |h θ| ≤ K) → (∀ i : ℕ, i ≤ 8 → ∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) → |(Work.Spaces.Lop^[i]) h θ| ≤ K) → MeasureTheory.IntegrableOn (fun θ => h θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ → (∫ θ in Work.Spaces.Iθ, h θ * Work.Elliptic.sinCos2 θ) = 0 → ∀ i : ℕ, i ≤ 8 → ∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) → |(Work.Spaces.Lop^[i]) (Work.FTS.PhiStar.Linv h) θ| ≤ C i * K := by
  obtain ⟨M0, hM0nn, hM0⟩ := LI_L2fun_lop_bound
  refine ⟨fun i => LI_Cfun M0 i, fun i => LI_Cfun_nonneg hM0nn i, ?_⟩
  intro h K hK hcont hcd hbd hiter hint hmom i hi θ hθ
  have hU : IsOpen (Set.Ioo 0 (Real.pi / 2)) := isOpen_Ioo
  have hg9 : ContDiffOn ℝ 9 (Work.FTS.PhiStar.Linv h) (Set.Ioo 0 (Real.pi / 2)) :=
    (Linv_contDiffOn_hasDerivAt (h := h) (n := 9) (by norm_num) hcd hint).1
  have hode : Set.EqOn (Work.Spaces.Lop (Work.FTS.PhiStar.Linv h))
      (fun θ : ℝ => -(h θ + LI_L2fun θ * Work.FTS.PhiStar.Linv h θ))
      (Set.Ioo 0 (Real.pi / 2)) := LI_lop_Linv_eq hcd hint
  -- the recursion identity at level `n+1`
  have hrec : ∀ n : ℕ, n ≤ 7 → ∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
      (Work.Spaces.Lop^[n + 1]) (Work.FTS.PhiStar.Linv h) θ
        = -(Work.Spaces.Lop^[n] h θ)
          - ∑ a ∈ Finset.range (n + 1), (n.choose a : ℝ) *
              ((Work.Spaces.Lop^[a]) LI_L2fun θ * (Work.Spaces.Lop^[n - a])
                (Work.FTS.PhiStar.Linv h) θ) := by
    intro n hn7 θ hθ'
    have h1 : Set.EqOn (Work.Spaces.Lop^[n + 1] (Work.FTS.PhiStar.Linv h))
        (Work.Spaces.Lop^[n]
          (fun θ : ℝ => -(h θ + LI_L2fun θ * Work.FTS.PhiStar.Linv h θ)))
        (Set.Ioo 0 (Real.pi / 2)) := by
      rw [show (Work.Spaces.Lop^[n + 1]) (Work.FTS.PhiStar.Linv h)
          = (Work.Spaces.Lop^[n]) (Work.Spaces.Lop (Work.FTS.PhiStar.Linv h))
          from Function.iterate_succ_apply (f := Work.Spaces.Lop) n (Work.FTS.PhiStar.Linv h)]
      exact LI_Lop_iter_congr_eqOn hU n hode
    have h2 := LI_lop_iter_Xfun_eqOn hcd hg9 (k := n) (by omega)
    exact h1.trans h2 hθ'
  -- the bound, by induction on the level
  have key : ∀ n : ℕ, n ≤ 8 → ∀ b : ℕ, b ≤ n → ∀ θ : ℝ,
      θ ∈ Set.Ioo 0 (Real.pi / 2) →
      |(Work.Spaces.Lop^[b]) (Work.FTS.PhiStar.Linv h) θ| ≤ LI_Cfun M0 b * K := by
    intro n
    induction n with
    | zero =>
        intro _ b hb θ hθ'
        obtain rfl : b = 0 := Nat.le_zero.mp hb
        have hbase := LI_lc_abs_le h K hK hbd hint hmom θ hθ'
        have hL : (Work.Spaces.Lop^[0]) (Work.FTS.PhiStar.Linv h) θ
            = Work.FTS.PhiStar.Linv h θ := rfl
        rw [hL]
        have hC0 : LI_Cfun M0 0 = 4 := by
          show 4 * (1000000 * (M0 + 1)) ^ 0 = 4
          rw [pow_zero]; ring
        rw [hC0]
        exact hbase
    | succ n ih =>
        intro hn b hb θ hθ'
        by_cases hbn : b ≤ n
        · exact ih (by omega) b hbn θ hθ'
        · have hbeq : b = n + 1 := by omega
          subst hbeq
          have hn7 : n ≤ 7 := by omega
          have hj7 : n ≤ 7 := hn7
          rw [hrec n hn7 θ hθ']
          have hX : |(Work.Spaces.Lop^[n]) h θ| ≤ K := hiter n (by omega) θ hθ'
          have hterm : ∀ a ∈ Finset.range (n + 1),
              |(n.choose a : ℝ) * ((Work.Spaces.Lop^[a]) LI_L2fun θ *
                (Work.Spaces.Lop^[n - a]) (Work.FTS.PhiStar.Linv h) θ)|
                ≤ 256 * (M0 * (LI_Cfun M0 n * K)) := by
            intro a ha
            have haj : a ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
            have hc0 : (0 : ℝ) ≤ (n.choose a : ℝ) := by positivity
            have hcB : (n.choose a : ℝ) ≤ 256 := by
              have h1 : n.choose a ≤ 2 ^ n := Nat.choose_le_two_pow n a
              have h2 : 2 ^ n ≤ 2 ^ 8 := pow_le_pow_right' (by norm_num : (1 : ℕ) ≤ 2) (by omega)
              have h3 : 2 ^ 8 = (256 : ℕ) := by norm_num
              exact_mod_cast (le_trans h1 (le_trans h2 (le_of_eq h3)))
            rw [abs_mul, abs_of_nonneg hc0, abs_mul]
            have hL2 : |(Work.Spaces.Lop^[a]) LI_L2fun θ| ≤ M0 := hM0 a (by omega) θ
            have hgv : |(Work.Spaces.Lop^[n - a]) (Work.FTS.PhiStar.Linv h) θ|
                ≤ LI_Cfun M0 (n - a) * K := ih (by omega) (n - a) (by omega) θ hθ'
            have hCf : LI_Cfun M0 (n - a) ≤ LI_Cfun M0 n := LI_Cfun_mono hM0nn (Nat.sub_le n a)
            have hBnd : |(Work.Spaces.Lop^[a]) LI_L2fun θ| *
                |(Work.Spaces.Lop^[n - a]) (Work.FTS.PhiStar.Linv h) θ|
                ≤ M0 * (LI_Cfun M0 n * K) := by
              refine mul_le_mul hL2 ?_ (abs_nonneg _) hM0nn
              exact le_trans hgv (mul_le_mul_of_nonneg_right hCf hK)
            exact mul_le_mul hcB hBnd (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (by norm_num)
          have hSabs : |∑ a ∈ Finset.range (n + 1), (n.choose a : ℝ) *
                ((Work.Spaces.Lop^[a]) LI_L2fun θ *
                  (Work.Spaces.Lop^[n - a]) (Work.FTS.PhiStar.Linv h) θ)|
              ≤ 2048 * (M0 * (LI_Cfun M0 n * K)) := by
            refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
            have h2 : ∑ a ∈ Finset.range (n + 1),
                |(n.choose a : ℝ) * ((Work.Spaces.Lop^[a]) LI_L2fun θ *
                  (Work.Spaces.Lop^[n - a]) (Work.FTS.PhiStar.Linv h) θ)|
                ≤ (Finset.range (n + 1)).card • (256 * (M0 * (LI_Cfun M0 n * K))) :=
              Finset.sum_le_card_nsmul _ _ _ (fun a ha => hterm a ha)
            refine le_trans h2 ?_
            rw [Finset.card_range, nsmul_eq_mul]
            have hn8 : (((n + 1 : ℕ)) : ℝ) ≤ 8 := by
              exact_mod_cast (by omega : n + 1 ≤ 8)
            have hY0 : (0 : ℝ) ≤ 256 * (M0 * (LI_Cfun M0 n * K)) := by
              have hcf : (0 : ℝ) ≤ LI_Cfun M0 n := LI_Cfun_nonneg hM0nn n
              exact mul_nonneg (by norm_num) (mul_nonneg hM0nn (mul_nonneg hcf hK))
            calc (((n + 1 : ℕ)) : ℝ) * (256 * (M0 * (LI_Cfun M0 n * K)))
                ≤ 8 * (256 * (M0 * (LI_Cfun M0 n * K))) :=
                  mul_le_mul_of_nonneg_right hn8 hY0
              _ = 2048 * (M0 * (LI_Cfun M0 n * K)) := by ring
          have hgoal : K + 2048 * (M0 * (LI_Cfun M0 n * K)) ≤ LI_Cfun M0 (n + 1) * K := by
            have hCn1 : (1 : ℝ) ≤ LI_Cfun M0 n := LI_Cfun_one_le hM0nn n
            have hCn0 : (0 : ℝ) ≤ LI_Cfun M0 n := LI_Cfun_nonneg hM0nn n
            have hkey2 : 2048 * M0 * (LI_Cfun M0 n * K)
                ≤ ((1000000 * (M0 + 1)) - 1) * (LI_Cfun M0 n * K) := by
              have h1 : 2048 * M0 ≤ (1000000 * (M0 + 1)) - 1 := by nlinarith [hM0nn]
              exact mul_le_mul_of_nonneg_right h1 (mul_nonneg hCn0 hK)
            have hAK : K ≤ LI_Cfun M0 n * K := by
              have := mul_le_mul_of_nonneg_right hCn1 hK
              simpa using this
            have hstepA : K + 2048 * (M0 * (LI_Cfun M0 n * K))
                ≤ K + ((1000000 * (M0 + 1)) - 1) * (LI_Cfun M0 n * K) := by
              linarith [hkey2]
            have hstepB : K + ((1000000 * (M0 + 1)) - 1) * (LI_Cfun M0 n * K)
                ≤ (LI_Cfun M0 n * (1000000 * (M0 + 1))) * K := by
              linarith [hAK]
            have hCsucc : LI_Cfun M0 (n + 1) = LI_Cfun M0 n * (1000000 * (M0 + 1)) := by
              show 4 * (1000000 * (M0 + 1)) ^ (n + 1)
                = 4 * (1000000 * (M0 + 1)) ^ n * (1000000 * (M0 + 1))
              rw [pow_succ]; ring
            rw [hCsucc]
            linarith [hstepA, hstepB]
          have htri : |-(Work.Spaces.Lop^[n] h θ)
              - ∑ a ∈ Finset.range (n + 1), (n.choose a : ℝ) *
                ((Work.Spaces.Lop^[a]) LI_L2fun θ *
                  (Work.Spaces.Lop^[n - a]) (Work.FTS.PhiStar.Linv h) θ)|
              ≤ K + 2048 * (M0 * (LI_Cfun M0 n * K)) := by
            have h1 : |-(Work.Spaces.Lop^[n] h θ)
                - ∑ a ∈ Finset.range (n + 1), (n.choose a : ℝ) *
                  ((Work.Spaces.Lop^[a]) LI_L2fun θ *
                    (Work.Spaces.Lop^[n - a]) (Work.FTS.PhiStar.Linv h) θ)|
                ≤ |(Work.Spaces.Lop^[n]) h θ|
                  + |∑ a ∈ Finset.range (n + 1), (n.choose a : ℝ) *
                    ((Work.Spaces.Lop^[a]) LI_L2fun θ *
                      (Work.Spaces.Lop^[n - a]) (Work.FTS.PhiStar.Linv h) θ)| := by
              calc |-(Work.Spaces.Lop^[n] h θ)
                    - ∑ a ∈ Finset.range (n + 1), (n.choose a : ℝ) *
                      ((Work.Spaces.Lop^[a]) LI_L2fun θ *
                        (Work.Spaces.Lop^[n - a]) (Work.FTS.PhiStar.Linv h) θ)|
                  = |(-(Work.Spaces.Lop^[n] h θ))
                      + (-(∑ a ∈ Finset.range (n + 1), (n.choose a : ℝ) *
                        ((Work.Spaces.Lop^[a]) LI_L2fun θ *
                          (Work.Spaces.Lop^[n - a]) (Work.FTS.PhiStar.Linv h) θ)))| := by
                    simp only [sub_eq_add_neg]
                _ ≤ |-(Work.Spaces.Lop^[n] h θ)|
                      + |-(∑ a ∈ Finset.range (n + 1), (n.choose a : ℝ) *
                        ((Work.Spaces.Lop^[a]) LI_L2fun θ *
                          (Work.Spaces.Lop^[n - a]) (Work.FTS.PhiStar.Linv h) θ))| :=
                    abs_add_le _ _
                _ = |(Work.Spaces.Lop^[n]) h θ|
                      + |∑ a ∈ Finset.range (n + 1), (n.choose a : ℝ) *
                        ((Work.Spaces.Lop^[a]) LI_L2fun θ *
                          (Work.Spaces.Lop^[n - a]) (Work.FTS.PhiStar.Linv h) θ)| := by
                    rw [abs_neg, abs_neg]
            linarith [h1, hX, hSabs]
          linarith [htri, hgoal]
  exact key 8 le_rfl i hi θ hθ


end Work.FTS.PhiStar.LinvFlat
