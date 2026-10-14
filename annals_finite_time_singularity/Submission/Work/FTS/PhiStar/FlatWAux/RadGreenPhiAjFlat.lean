import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.PhiStar.FlatWAux.Expansion
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.RegPkgGal.RVocab
import Submission.Work.FTS.StrongPersist.Star6
import Submission.Work.FTS.StrongPersist.Vocab
import Submission.Work.FTS.VocabO
import Submission.Work.FTS_RegExport.RXR5L.L12fAux.C1Jet_L12f_of_support
import Submission.Work.H2W.FstarDzIterFourPsiAe
import Submission.Work.Spaces.dthU_Gam
-- ===== merged: Submission.Work.FTS.PhiStar.FlatWAux.ChiaLinvLop =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.FlatWAux

noncomputable section

set_option maxHeartbeats 3200000
set_option linter.unusedVariables false

/-- `L₂ θ = 10 cos²θ - 6` on the nose: `L₂ = 5cos2θ - 1` and `cos 2θ = 2cos²θ - 1`. -/
private lemma LI_L2fun_eq_ten_cos_sq (θ : ℝ) :
    Work.FTS.PhiStar.LinvFlat.LI_L2fun θ = 10 * Real.cos θ ^ 2 - 6 := by
  rw [Work.FTS.PhiStar.LinvFlat.LI_L2fun_eq]
  have hs := Real.sin_sq θ
  rw [hs]
  ring

/-- An explicit majorant of the finitely many constants `Kc j 0, …, Kc j 6`, independent of the
function `ψ`: the sum of the absolute values.  (Under the hypotheses of `ChiaLinvLop` all of
them are non-negative anyway, so this really is an upper bound.) -/
def chiaBnd (Kc : ℕ → ℕ → ℝ) (j : ℕ) : ℝ := ∑ n ∈ Finset.range 7, |Kc j n|

private lemma chiaBnd_nonneg (Kc : ℕ → ℕ → ℝ) (j : ℕ) : 0 ≤ chiaBnd Kc j := by
  unfold chiaBnd
  exact Finset.sum_nonneg (fun n _ => abs_nonneg (Kc j n))

private lemma abs_le_chiaBnd (Kc : ℕ → ℕ → ℝ) (j : ℕ) {n : ℕ} (hn : n ≤ 6) :
    |Kc j n| ≤ chiaBnd Kc j := by
  have hmem : n ∈ Finset.range 7 := Finset.mem_range.mpr (Nat.lt_succ_of_le hn)
  unfold chiaBnd
  exact Finset.single_le_sum (fun i _ => abs_nonneg (Kc j i)) hmem

/-- **The `Lop`-iteration bound for `Linv`.**  If `h` is bounded together with its first six
`Lop`-iterates, satisfies the first-order equation `Lop (Linv h) = -(h + L₂ · Linv h)`, is `C^9`,
its inverse `Linv h` is `C^9`, and `h·sinCos2` is integrable with vanishing integral, then
`|Lop^[b] (Linv h) θ| ≤ LI_Cfun M0 b · K` for `b ≤ 6`, where `M0` bounds the `Lop`-iterates of the
coefficient `L₂`.  This is the `i ≤ 6` form of `LinvFlat.LinvLopIter` (there only the iterates up
to order `7` of `h` are actually used). -/
private lemma lop_iter_Linv_le
    (h : ℝ → ℝ) (K M0 : ℝ) (hM0nn : 0 ≤ M0) (hK : 0 ≤ K)
    (hL2 : ∀ a : ℕ, a ≤ 7 → ∀ θ : ℝ,
      |(Work.Spaces.Lop^[a]) Work.FTS.PhiStar.LinvFlat.LI_L2fun θ| ≤ M0)
    (hiter : ∀ n : ℕ, n ≤ 6 → ∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
      |(Work.Spaces.Lop^[n]) h θ| ≤ K)
    (hode : Set.EqOn (Work.Spaces.Lop (Work.FTS.PhiStar.Linv h))
      (fun θ : ℝ => -(h θ + Work.FTS.PhiStar.LinvFlat.LI_L2fun θ
        * Work.FTS.PhiStar.Linv h θ)) (Set.Ioo 0 (Real.pi / 2)))
    (hcd9 : ContDiffOn ℝ 9 h (Set.Ioo 0 (Real.pi / 2)))
    (hg9 : ContDiffOn ℝ 9 (Work.FTS.PhiStar.Linv h) (Set.Ioo 0 (Real.pi / 2)))
    (hint : MeasureTheory.IntegrableOn (fun θ : ℝ => h θ * Work.Elliptic.sinCos2 θ)
      Work.Spaces.Iθ)
    (hmom : (∫ θ in Work.Spaces.Iθ, h θ * Work.Elliptic.sinCos2 θ) = 0) :
    ∀ b : ℕ, b ≤ 6 → ∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
      |(Work.Spaces.Lop^[b]) (Work.FTS.PhiStar.Linv h) θ|
        ≤ Work.FTS.PhiStar.LinvFlat.LI_Cfun M0 b * K := by
  have hU : IsOpen (Set.Ioo 0 (Real.pi / 2)) := isOpen_Ioo
  have hrec : ∀ n : ℕ, n ≤ 5 → ∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
      (Work.Spaces.Lop^[n + 1]) (Work.FTS.PhiStar.Linv h) θ
        = -(Work.Spaces.Lop^[n] h θ)
          - ∑ a ∈ Finset.range (n + 1), (n.choose a : ℝ) *
              ((Work.Spaces.Lop^[a]) Work.FTS.PhiStar.LinvFlat.LI_L2fun θ *
                (Work.Spaces.Lop^[n - a]) (Work.FTS.PhiStar.Linv h) θ) := by
    intro n _ θ hθ'
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
    have h2 := Work.FTS.PhiStar.LinvFlat.LI_lop_iter_Xfun_eqOn hcd9 hg9 (k := n) (by omega)
    exact h1.trans h2 hθ'
  have key : ∀ n : ℕ, n ≤ 6 → ∀ b : ℕ, b ≤ n → ∀ θ : ℝ,
      θ ∈ Set.Ioo 0 (Real.pi / 2) →
      |(Work.Spaces.Lop^[b]) (Work.FTS.PhiStar.Linv h) θ|
        ≤ Work.FTS.PhiStar.LinvFlat.LI_Cfun M0 b * K := by
    intro n
    induction n with
    | zero =>
        intro _ b hb θ hθ'
        obtain rfl : b = 0 := Nat.le_zero.mp hb
        have hbase := Work.FTS.PhiStar.LinvFlat.LI_lc_abs_le h K hK
          (fun θ hθ => hiter 0 (by norm_num) θ hθ) hint hmom θ hθ'
        have hL : (Work.Spaces.Lop^[0]) (Work.FTS.PhiStar.Linv h) θ
            = Work.FTS.PhiStar.Linv h θ := rfl
        rw [hL]
        have hC0 : Work.FTS.PhiStar.LinvFlat.LI_Cfun M0 0 = 4 := by
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
          have hn5 : n ≤ 5 := by omega
          rw [hrec n hn5 θ hθ']
          have hX : |(Work.Spaces.Lop^[n]) h θ| ≤ K := hiter n (by omega) θ hθ'
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
            have hL2a : |(Work.Spaces.Lop^[a])
                Work.FTS.PhiStar.LinvFlat.LI_L2fun θ| ≤ M0 := hL2 a (by omega) θ
            have hgv : |(Work.Spaces.Lop^[n - a]) (Work.FTS.PhiStar.Linv h) θ|
                ≤ Work.FTS.PhiStar.LinvFlat.LI_Cfun M0 (n - a) * K :=
              ih (by omega) (n - a) (by omega) θ hθ'
            have hCf : Work.FTS.PhiStar.LinvFlat.LI_Cfun M0 (n - a)
                ≤ Work.FTS.PhiStar.LinvFlat.LI_Cfun M0 n :=
              Work.FTS.PhiStar.LinvFlat.LI_Cfun_mono hM0nn (Nat.sub_le n a)
            have hBnd : |(Work.Spaces.Lop^[a]) Work.FTS.PhiStar.LinvFlat.LI_L2fun θ| *
                |(Work.Spaces.Lop^[n - a]) (Work.FTS.PhiStar.Linv h) θ|
                ≤ M0 * (Work.FTS.PhiStar.LinvFlat.LI_Cfun M0 n * K) := by
              refine mul_le_mul hL2a ?_ (abs_nonneg _) hM0nn
              exact le_trans hgv (mul_le_mul_of_nonneg_right hCf hK)
            exact mul_le_mul hcB hBnd (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (by norm_num)
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
            have hY0 : (0 : ℝ) ≤
                256 * (M0 * (Work.FTS.PhiStar.LinvFlat.LI_Cfun M0 n * K)) := by
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
                ≤ ((1000000 * (M0 + 1)) - 1)
                    * (Work.FTS.PhiStar.LinvFlat.LI_Cfun M0 n * K) := by
              have h1 : 2048 * M0 ≤ (1000000 * (M0 + 1)) - 1 := by nlinarith [hM0nn]
              exact mul_le_mul_of_nonneg_right h1 (mul_nonneg hCn0 hK)
            have hAK : K ≤ Work.FTS.PhiStar.LinvFlat.LI_Cfun M0 n * K := by
              have := mul_le_mul_of_nonneg_right hCn1 hK
              simpa using this
            have hstepA : K + 2048 * (M0 * (Work.FTS.PhiStar.LinvFlat.LI_Cfun M0 n * K))
                ≤ K + ((1000000 * (M0 + 1)) - 1)
                    * (Work.FTS.PhiStar.LinvFlat.LI_Cfun M0 n * K) := by
              linarith [hkey2]
            have hstepB : K + ((1000000 * (M0 + 1)) - 1)
                    * (Work.FTS.PhiStar.LinvFlat.LI_Cfun M0 n * K)
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
  exact fun b hb θ hθ => key 6 le_rfl b hb θ hθ

theorem ChiaLinvLop (Kc : ℕ → ℕ → ℝ) :
    ∃ K : ℕ → ℕ → ℝ, (∀ j i : ℕ, 0 ≤ K j i) ∧
    ∀ (ψ : ℝ → ℝ),
      (∀ j : ℕ, j ≤ Work.FTS.PhiStar.FlatWAux.J → ∀ i : ℕ, i ≤ 6 →
        ∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
        |(Work.Spaces.Lop^[i]) (Work.FTS.PhiStar.FlatWAux.chia ψ j) θ| ≤ Kc j i) →
      (∀ j : ℕ, j ≤ Work.FTS.PhiStar.FlatWAux.J →
        ContDiffOn ℝ 9 (Work.FTS.PhiStar.FlatWAux.chia ψ j) (Set.Ioo 0 (Real.pi / 2))) →
      (∀ j : ℕ, j ≤ Work.FTS.PhiStar.FlatWAux.J →
        MeasureTheory.IntegrableOn (fun θ : ℝ => Work.FTS.PhiStar.FlatWAux.chia ψ j θ
          * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ) →
      (∀ j : ℕ, j ≤ Work.FTS.PhiStar.FlatWAux.J →
        (∫ θ in Work.Spaces.Iθ, Work.FTS.PhiStar.FlatWAux.chia ψ j θ
          * Work.Elliptic.sinCos2 θ) = 0) →
      (∀ h : ℝ → ℝ, ContinuousOn h (Set.Ioo 0 (Real.pi / 2)) →
        (∃ M : ℝ, ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |h θ| ≤ M) →
        MeasureTheory.IntegrableOn (fun θ => h θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ →
        (∫ θ in Work.Spaces.Iθ, h θ * Work.Elliptic.sinCos2 θ) = 0 →
        ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
          Work.Spaces.Lop (Work.FTS.PhiStar.Linv h) θ
            = (6 - 10 * Real.cos θ ^ 2) * Work.FTS.PhiStar.Linv h θ - h θ) →
      ∀ j : ℕ, j ≤ Work.FTS.PhiStar.FlatWAux.J → ∀ i : ℕ, i ≤ 6 → ∀ θ : ℝ,
        θ ∈ Set.Ioo 0 (Real.pi / 2) →
        |(Work.Spaces.Lop^[i]) (Work.FTS.PhiStar.Linv
          (Work.FTS.PhiStar.FlatWAux.chia ψ j)) θ| ≤ K j i := by
  obtain ⟨M0, hM0nn, hM0⟩ := Work.FTS.PhiStar.LinvFlat.LI_L2fun_lop_bound
  refine ⟨fun j i => Work.FTS.PhiStar.LinvFlat.LI_Cfun M0 i * chiaBnd Kc j,
    fun j i => mul_nonneg (Work.FTS.PhiStar.LinvFlat.LI_Cfun_nonneg hM0nn i)
      (chiaBnd_nonneg Kc j), ?_⟩
  intro ψ hKc hcd9 hint hmom hlinvLop j hj i hi θ hθ
  have hKnneg : ∀ n : ℕ, n ≤ 6 → 0 ≤ Kc j n :=
    fun n hn => le_trans (abs_nonneg _) (hKc j hj n hn θ hθ)
  have hKle : ∀ n : ℕ, n ≤ 6 → Kc j n ≤ chiaBnd Kc j := by
    intro n hn
    have h := abs_le_chiaBnd Kc j hn
    rwa [abs_of_nonneg (hKnneg n hn)] at h
  have hiterall : ∀ n : ℕ, n ≤ 6 → ∀ θ' : ℝ, θ' ∈ Set.Ioo 0 (Real.pi / 2) →
      |(Work.Spaces.Lop^[n]) (Work.FTS.PhiStar.FlatWAux.chia ψ j) θ'| ≤ chiaBnd Kc j :=
    fun n hn θ' hθ' => le_trans (hKc j hj n hn θ' hθ') (hKle n hn)
  have hcont : ContinuousOn (Work.FTS.PhiStar.FlatWAux.chia ψ j)
      (Set.Ioo 0 (Real.pi / 2)) := (hcd9 j hj).continuousOn
  have hbdd : ∃ M : ℝ, ∀ θ' ∈ Set.Ioo 0 (Real.pi / 2),
      |Work.FTS.PhiStar.FlatWAux.chia ψ j θ'| ≤ M :=
    ⟨chiaBnd Kc j, hiterall 0 (by norm_num)⟩
  have hode : Set.EqOn
      (Work.Spaces.Lop (Work.FTS.PhiStar.Linv (Work.FTS.PhiStar.FlatWAux.chia ψ j)))
      (fun θ' : ℝ => -(Work.FTS.PhiStar.FlatWAux.chia ψ j θ'
        + Work.FTS.PhiStar.LinvFlat.LI_L2fun θ'
          * Work.FTS.PhiStar.Linv (Work.FTS.PhiStar.FlatWAux.chia ψ j) θ'))
      (Set.Ioo 0 (Real.pi / 2)) := by
    intro θ' hθ'
    have h1 := hlinvLop (Work.FTS.PhiStar.FlatWAux.chia ψ j) hcont hbdd
      (hint j hj) (hmom j hj) θ' hθ'
    have h2 : (6 - 10 * Real.cos θ' ^ 2)
          * Work.FTS.PhiStar.Linv (Work.FTS.PhiStar.FlatWAux.chia ψ j) θ'
          - Work.FTS.PhiStar.FlatWAux.chia ψ j θ'
        = -(Work.FTS.PhiStar.FlatWAux.chia ψ j θ'
          + Work.FTS.PhiStar.LinvFlat.LI_L2fun θ'
            * Work.FTS.PhiStar.Linv (Work.FTS.PhiStar.FlatWAux.chia ψ j) θ') := by
      rw [LI_L2fun_eq_ten_cos_sq]
      ring
    exact h1.trans h2
  have hg9 : ContDiffOn ℝ 9 (Work.FTS.PhiStar.Linv (Work.FTS.PhiStar.FlatWAux.chia ψ j))
      (Set.Ioo 0 (Real.pi / 2)) :=
    (Work.FTS.PhiStar.LinvFlat.Linv_contDiffOn_hasDerivAt
      (h := Work.FTS.PhiStar.FlatWAux.chia ψ j) (n := 9) (by norm_num)
      (hcd9 j hj) (hint j hj)).1
  exact lop_iter_Linv_le (Work.FTS.PhiStar.FlatWAux.chia ψ j) (chiaBnd Kc j) M0 hM0nn
    (chiaBnd_nonneg Kc j) hM0 hiterall hode (hcd9 j hj) hg9 (hint j hj) (hmom j hj) i hi θ hθ

end

end Work.FTS.PhiStar.FlatWAux
end
-- ===== merged: Submission.Work.FTS.PhiStar.FlatWAux.RadGreenPhiAjFlat =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped ContDiff

namespace Work.FTS.PhiStar.FlatWAux

/-!
# `Work.FTS.PhiStar.FlatWAux.RadGreenPhiAjFlat`

The two α-uniform flat `z`-derivative estimates for the divided radial Green function
`(z+1)/z · radGreen α m c` at the two sources that occur in the `FlatW_psiSeries` route:

* `c = φ = phiA α = phiAj 1 α` (the source of the mode expansion of `RemSource α ψ`);
* `c = 𝒜^J φ = Ajit α J (phiA α) = phiAj (J+1) α` (the remainder term of the `1/λ_m`-expansion).

Both are immediate instances of `RadGreenDivFlatU`, whose only inputs are the smoothness of `c`
on `(0,∞)` and the two-sided flat/decay bounds `|∂^k c| ≤ A/(1+t^{k+1})`,
`|∂^k (c/t)| ≤ A/(1+t^{k+2})` for `k ≤ 14`.  Those are exactly what `PhiAjFlatDecayU` provides
(for the single *α-free* constant `A`, in the range `j ≤ 9`), and `phiAj 1 α = phiA α` while
`phiAj (J+1) α = phiAj 9 α`.  The smoothness input `ContDiffOn ℝ 14` for the `𝒜`-iterates is
proved below by induction on the number of iterations.
-/

/-- **`𝒜^j φ` is `C^∞` at every `z > 0`.**  Here `𝒜 a = αz²a'' + (5+α)za'` is the radial
operator of the `Φ_*` decomposition.  Induction on `j`: the case `j = 0` is the explicit rational
function `φ` (`contDiffAt_phiA_of` for `j = 1`), and the step is a sum of products of the smooth
`z²`, `z` with the first and second iterated derivatives of a `C^∞` function. -/
theorem contDiffAt_Ajit_phiA (α : ℝ) (j : ℕ) {z : ℝ} (hz : 0 < z) :
    ContDiffAt ℝ ∞ (Ajit α j (Work.FTS.VocabO.phiA α)) z := by
  induction j with
  | zero => simpa only [Ajit_zero] using Work.FTS.PhiStar.contDiffAt_phiA α hz
  | succ j ih =>
      rw [Ajit_succ]
      have hd1 : ContDiffAt ℝ ∞ (deriv (Ajit α j (Work.FTS.VocabO.phiA α))) z :=
        Work.FTS.PhiStar.contDiffAt_infty_deriv ih
      have hd2 : ContDiffAt ℝ ∞ (iteratedDeriv 2 (Ajit α j (Work.FTS.VocabO.phiA α))) z :=
        Work.FTS.PhiStar.contDiffAt_infty_iteratedDeriv 2 ih
      exact (((contDiffAt_const (c := α)).mul (contDiffAt_id.pow 2)).mul hd2).add
        (((contDiffAt_const (c := (5 + α))).mul contDiffAt_id).mul hd1)

/-- The `ContDiffOn` form of `contDiffAt_Ajit_phiA`, at any finite order. -/
theorem contDiffOn_Ajit_phiA (α : ℝ) (j : ℕ) (n : ℕ) :
    ContDiffOn ℝ n (Ajit α j (Work.FTS.VocabO.phiA α)) (Set.Ioi 0) :=
  fun z hz => ((contDiffAt_Ajit_phiA α j hz).of_le
    (by simp : ((n : ℕ∞ω)) ≤ ∞)).contDiffWithinAt

theorem RadGreenPhiAjFlat : ∃ C : ℝ, 0 < C ∧
    (∀ (α : ℝ), 0 < α → α ≤ 1 / 5 → ∀ (m : ℕ), 1 ≤ m →
      ∀ k : ℕ, k ≤ 7 → ∀ z : ℝ, 0 < z →
      |(z + 1) ^ k * iteratedDeriv k
        (fun z' => (z' + 1) / z' * Work.FTS.PhiStar.Radial.radGreen α m
          (Work.FTS.VocabO.phiA α) z') z|
        ≤ C / Work.FTS.PhiStar.Gegenbauer.lam m) ∧
    (∀ (α : ℝ), 0 < α → α ≤ 1 / 5 → ∀ (m : ℕ), 1 ≤ m →
      ∀ k : ℕ, k ≤ 7 → ∀ z : ℝ, 0 < z →
      |(z + 1) ^ k * iteratedDeriv k
        (fun z' => (z' + 1) / z' * Work.FTS.PhiStar.Radial.radGreen α m
          (Work.FTS.PhiStar.FlatWAux.Ajit α Work.FTS.PhiStar.FlatWAux.J
            (Work.FTS.VocabO.phiA α)) z') z|
        ≤ C / Work.FTS.PhiStar.Gegenbauer.lam m) := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := RadGreenDivFlatU
  obtain ⟨A, hApos, hA⟩ := PhiAjFlatDecayU
  refine ⟨C₀ * A, mul_pos hC₀pos hApos, ?_, ?_⟩
  · -- the source `φ = phiA α = phiAj 1 α`
    intro α hα hα5 m hm k hk z hz
    have hsmooth : ContDiffOn ℝ 14 (Work.FTS.VocabO.phiA α) (Set.Ioi 0) :=
      fun z hz => (Work.FTS.PhiStar.contDiffAt_phiA_of α 14 hz).contDiffWithinAt
    have hdata := hA α hα hα5 1 (by norm_num)
    exact hC₀ α hα hα5 m hm (Work.FTS.VocabO.phiA α) A (le_of_lt hApos) hsmooth
      hdata.1 hdata.2 k hk z hz
  · -- the remainder source `𝒜^J φ = phiAj (J+1) α = phiAj 9 α`
    intro α hα hα5 m hm k hk z hz
    have hAj : Ajit α J (Work.FTS.VocabO.phiA α) = Work.FTS.PhiStar.phiAj (J + 1) α :=
      Ajit_phiA α J
    have hsmooth : ContDiffOn ℝ 14 (Ajit α J (Work.FTS.VocabO.phiA α)) (Set.Ioi 0) :=
      contDiffOn_Ajit_phiA α J 14
    have hdata := hA α hα hα5 (J + 1) (by norm_num [J])
    have hb1 : ∀ k : ℕ, k ≤ 14 → ∀ t : ℝ, 0 < t →
        |iteratedDeriv k (Ajit α J (Work.FTS.VocabO.phiA α)) t|
          ≤ A / (1 + t ^ (k + 1)) := by
      intro k hk t ht
      rw [hAj]
      exact hdata.1 k hk t ht
    have hb2 : ∀ k : ℕ, k ≤ 14 → ∀ t : ℝ, 0 < t →
        |iteratedDeriv k (fun t' => Ajit α J (Work.FTS.VocabO.phiA α) t' / t') t|
          ≤ A / (1 + t ^ (k + 2)) := by
      intro k hk t ht
      rw [hAj]
      exact hdata.2 k hk t ht
    exact hC₀ α hα hα5 m hm (Ajit α J (Work.FTS.VocabO.phiA α)) A (le_of_lt hApos)
      hsmooth hb1 hb2 k hk z hz

end Work.FTS.PhiStar.FlatWAux
end
