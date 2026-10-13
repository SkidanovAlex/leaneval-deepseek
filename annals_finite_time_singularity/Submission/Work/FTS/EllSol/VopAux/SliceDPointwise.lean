import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.EllSol.VopAux.SliceDDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.VopAux

open Work.FTS.EllipticEst

/-
Pointwise form of the single-slice `∂_θ²`-Poincaré estimate in the open-trace class.

Write `L = D_θ = sin(2θ)∂_θ`, `LopIter i u = L^i u`, `thEta θ = sin(2θ)^{-η}`,
`thGam α θ = sin(2θ)^{-γ}` (`η = eta = 99/100`, `γ = gam α = 1 + α/10`),
`sliceV u = deriv (deriv u)`, and
`sliceD K α u θ = (u θ)²·thEta θ + (u' θ)²·thEta θ + (u'' θ)²·thEta θ
    + ∑_{1 ≤ m ≤ K} (L^m u'' θ)²·thGam α θ`
(`Work.FTS.EllSol.VopAux.sliceD`, defined in
`Submission/Work/FTS/EllSol/VopAux/SliceDDefs.lean`, which is the module to import; it also
contains `sd_LopIter_expand_open`, `sd_LopIter_sin_sq_bound`, `sd_LopIter_cos_bound`,
`sd_two_sub_gam_le_thEta`, `sd_four_sub_gam_le_thEta`, `sd_four_sub_gam_le_thGam`,
`sd_sum_sq_mul_le`, `sd_choose_sq_sum_le` and the `sliceD` summand lemmas
`sd_self_sq_le_sliceD`, `sd_deriv_sq_le_sliceD`, `sd_sliceV_sq_le_sliceD`,
`sd_LopIter_sliceV_sq_le_sliceD`).

Claim.  For `u` of class `C^∞` on the OPEN interval `(0, π/2)` (nothing is assumed outside) and
every `1 ≤ i ≤ K`, the pointwise bound

  `(L^i u θ)²·thGam α θ ≤ C·sliceD K α u θ`

holds at every interior angle `θ ∈ (0, π/2)`, with a constant `C` depending only on `K` (uniform
in `α ∈ (0,1]` and in `u`).

ROUTE (strong induction on `i`, valid because the expansion below reduces `i` to `i-1`).
* `i = 1`: `L u θ = sin(2θ)·u' θ`, so `(L u θ)²thGam α θ = (u' θ)²·sin(2θ)^{2-γ}`; on `Iθ` one has
  `sin(2θ) ≤ 1` and `-η ≤ 2-γ` (as `γ ≤ 11/10`), so by `sin_two_rpow_le_rpow`
  `sin(2θ)^{2-γ} ≤ thEta θ`, and `(u' θ)²thEta θ` is a summand of `sliceD` (`sd_deriv_sq_le_sliceD`).
* `i = n+2 ≥ 2`: expand (`sd_LopIter_expand_open`, whose only hypothesis is the `∀ n` open-interval
  smoothness; note `θ ∈ Ioo 0 (π/2)` is its `θ ∈ sdU`)
  `L^{n+2}u θ = ∑_{a ≤ n} C(n,a)·(L^a sin²(2·) θ)·(L^{n-a}u'' θ)
             + ∑_{a ≤ n} C(n,a)·(L^a (2cos 2·) θ)·(L^{n+1-a}u θ)`.
  Bound `(A+B)²·thGam ≤ 2A²thGam + 2B²thGam` and bound each sum by Cauchy–Schwarz with `thGam ≥ 0`
  (`sd_sum_sq_mul_le` + `sd_choose_sq_sum_le`, giving `∑_a C(n,a)² ≤ (n+1)4^n`).
  In the first sum, `|L^a sin²(2·) θ| ≤ D·sin²(2θ)` for `a ≤ K` (`sd_LopIter_sin_sq_bound`), and
  `sin(2θ)^4·thGam α θ ≤ thEta θ` resp. `≤ thGam α θ` (`sd_four_sub_gam_le_thEta`,
  `sd_four_sub_gam_le_thGam`): the terms with `n-a = 0` are dominated by the `(u'')²thEta` summand
  of `sliceD` (`sd_sliceV_sq_le_sliceD`), those with `1 ≤ n-a ≤ K` by
  `sd_LopIter_sliceV_sq_le_sliceD`.
  In the second sum, `|L^a(2cos 2·) θ| ≤ E` for `a ≤ K` (`sd_LopIter_cos_bound`), and the index
  `1 ≤ n+1-a ≤ n+1 = i-1 < i` lets the strong induction hypothesis apply with `B^{i-1} ≤ B^i`.
  Collecting the constants into `B^i` exactly as in the pre-existing (sorry-free, neigh-
  bourhood-smooth-class) proof `sfb_LopIter_expand_succ` + `key` inside
  `Submission/Work/FTS/EllipticEst/ThetaU/slice_f_bound_open.lean` — the `sfF1`/`sfF2` summands
  there are the two sums above verbatim — yields the claim for `i = n+2 ≤ K`, with
  `B := 2 + π/2 + 34·(K+1)²·D²·4^K` (any sufficiently large `B ≥ 1` works).
-/
theorem SliceDPointwise (K : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (u : ℝ → ℝ), 0 < α → α ≤ 1 →
      (∀ n : ℕ, ContDiffOn ℝ n u (Set.Ioo 0 (Real.pi / 2))) →
      ∀ i ∈ Finset.Icc 1 K, ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        (Work.FTS.EllipticEst.LopIter i u θ) ^ 2 * Work.FTS.EllipticEst.thGam α θ
          ≤ C * Work.FTS.EllSol.VopAux.sliceD K α u θ := by
  -- the two `O(1)` bounds on the iterates of `sin²(2·)` and of `2 cos(2·)`
  obtain ⟨D, hD1, hDss⟩ := sd_LopIter_sin_sq_bound K
  obtain ⟨E, hEpos, hE⟩ := sd_LopIter_cos_bound K
  set F : ℝ := max D E with hFdef
  have hF1 : 1 ≤ F := le_trans hD1 (le_max_left D E)
  have hF0 : 0 ≤ F := le_trans zero_le_one hF1
  have hFD : D ≤ F := le_max_left D E
  have hFE : E ≤ F := le_max_right D E
  -- the two uniform bounds, with the single constant `F`
  have hDssF : ∀ a ≤ K, ∀ θ ∈ Work.Spaces.Iθ,
      |LopIter a (fun θ : ℝ => (Real.sin (2 * θ)) ^ 2) θ|
        ≤ F * (Real.sin (2 * θ)) ^ 2 :=
    fun a ha θ hθ =>
      le_trans (hDss a ha θ hθ) (mul_le_mul_of_nonneg_right hFD (sq_nonneg _))
  have hEF : ∀ a ≤ K, ∀ θ ∈ Work.Spaces.Iθ,
      |LopIter a (fun θ : ℝ => 2 * Real.cos (2 * θ)) θ| ≤ F :=
    fun a ha θ hθ => le_trans (hE a ha θ hθ) hFE
  -- the constant of the induction, an upper bound for the one-step growth
  set B : ℝ := 2 + 34 * ((K : ℝ) + 1) ^ 2 * F ^ 2 * (4 : ℝ) ^ K with hBdef
  have hBextra : 0 ≤ 34 * ((K : ℝ) + 1) ^ 2 * F ^ 2 * (4 : ℝ) ^ K :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (sq_nonneg F))
      (pow_nonneg (by norm_num) K)
  have hB1 : 1 ≤ B := by rw [hBdef]; linarith
  have hB0 : 0 ≤ B := le_trans zero_le_one hB1
  have hBstep : ∀ n ≤ K, 34 * ((n : ℝ) + 1) ^ 2 * F ^ 2 * (4 : ℝ) ^ n ≤ B := by
    intro n hn
    have h1 : ((n : ℝ) + 1) ^ 2 ≤ ((K : ℝ) + 1) ^ 2 := by
      have hn' : (n : ℝ) ≤ (K : ℝ) := by exact_mod_cast hn
      nlinarith [show (0 : ℝ) ≤ (n : ℝ) by positivity]
    have h2 : (4 : ℝ) ^ n ≤ (4 : ℝ) ^ K := pow_le_pow_right₀ (by norm_num) hn
    calc 34 * ((n : ℝ) + 1) ^ 2 * F ^ 2 * (4 : ℝ) ^ n
        ≤ 34 * ((K : ℝ) + 1) ^ 2 * F ^ 2 * (4 : ℝ) ^ K := by gcongr
      _ ≤ B := by rw [hBdef]; linarith
  refine ⟨B ^ K, pow_pos (lt_of_lt_of_le zero_lt_one hB1) K, ?_⟩
  intro α u hα0 hα1 hu i hi θ hθ
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hP0θ : 0 ≤ sliceD K α u θ := sliceD_nonneg K α u hθI
  have hg0 : 0 ≤ thGam α θ := thGam_nonneg hθI
  have hs : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg hθI
  have hs4le : ((Real.sin (2 * θ)) ^ 2) ^ 2 ≤ 1 := by
    have h := sd_sin_sq_le_one hθI
    have h0 : 0 ≤ (Real.sin (2 * θ)) ^ 2 := sq_nonneg _
    calc ((Real.sin (2 * θ)) ^ 2) ^ 2 ≤ 1 ^ 2 := pow_le_pow_left₀ h0 h 2
      _ = 1 := by norm_num
  -- the strong induction on the number of `L`-derivatives
  have key : ∀ m ≤ K, 1 ≤ m →
      (LopIter m u θ) ^ 2 * thGam α θ ≤ B ^ m * sliceD K α u θ := by
    intro m
    refine Nat.strong_induction_on m ?_
    intro m ih hmK hm1
    rcases eq_or_lt_of_le hm1 with hEq | hLt
    · -- `m = 1`: `(L u)² sin(2θ)^{-γ} = (u')² sin(2θ)^{2-γ} ≤ (u')² sin(2θ)^{-η} ≤ sliceD`
      have hm1' : m = 1 := hEq.symm
      subst hm1'
      have hLval : LopIter 1 u θ = Real.sin (2 * θ) * deriv u θ := by
        simp only [LopIter_succ, LopIter_zero, Work.Spaces.Lop]
      rw [hLval]
      have hrpow : (Real.sin (2 * θ)) ^ 2 * thGam α θ
          = (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) :=
        sd_sin_sq_mul_thGam hθI hα0 hα1
      have h2le := sd_two_sub_gam_le_thEta hα1 hθI
      have hdv := sd_deriv_sq_le_sliceD K α u hθI
      have hcomb : (Real.sin (2 * θ) * deriv u θ) ^ 2 * thGam α θ
          = (deriv u θ) ^ 2 * ((Real.sin (2 * θ)) ^ 2 * thGam α θ) := by ring
      rw [hcomb, hrpow]
      calc (deriv u θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
          ≤ (deriv u θ) ^ 2 * thEta θ := mul_le_mul_of_nonneg_left h2le (sq_nonneg _)
        _ ≤ sliceD K α u θ := hdv
        _ ≤ B ^ 1 * sliceD K α u θ := by
            rw [pow_one]
            exact le_mul_of_one_le_left hP0θ hB1
    · -- `m ≥ 2`: the expansion of `L^{n+2}u`
      have hm2 : 2 ≤ m := hLt
      obtain ⟨n, rfl⟩ : ∃ n, m = n + 2 := ⟨m - 2, by omega⟩
      have hnK : n ≤ K := by omega
      have hexp := sd_LopIter_expand_open n u hu hθ
      have hIH : ∀ j, 1 ≤ j → j ≤ n + 1 →
          (LopIter j u θ) ^ 2 * thGam α θ ≤ B ^ (n + 1) * sliceD K α u θ := by
        intro j hj1 hjK
        have hlt : j < n + 2 := by omega
        have hjK' : j ≤ K := by omega
        calc (LopIter j u θ) ^ 2 * thGam α θ ≤ B ^ j * sliceD K α u θ :=
              ih j hlt hjK' hj1
          _ ≤ B ^ (n + 1) * sliceD K α u θ :=
              mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hB1 hjK) hP0θ
      -- the `u''`-terms of the expansion
      have hterm1 : ∀ a ∈ Finset.range (n + 1),
          ((n.choose a : ℝ)
              * LopIter a (fun θ : ℝ => (Real.sin (2 * θ)) ^ 2) θ
              * LopIter (n - a) (sliceV u) θ) ^ 2 * thGam α θ
            ≤ ((n.choose a : ℝ)) ^ 2 * (F ^ 2 * sliceD K α u θ) := by
        intro a ha
        have ha' : a ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
        have haK : a ≤ K := by omega
        have hsq : (LopIter a (fun θ : ℝ => (Real.sin (2 * θ)) ^ 2) θ) ^ 2
            ≤ F ^ 2 * ((Real.sin (2 * θ)) ^ 2) ^ 2 := by
          rw [← sq_abs]
          calc |LopIter a (fun θ : ℝ => (Real.sin (2 * θ)) ^ 2) θ| ^ 2
              ≤ (F * (Real.sin (2 * θ)) ^ 2) ^ 2 :=
                pow_le_pow_left₀ (abs_nonneg _) (hDssF a haK θ hθI) 2
            _ = F ^ 2 * ((Real.sin (2 * θ)) ^ 2) ^ 2 := by ring
        rcases lt_or_eq_of_le ha' with hlt | heq
        · have hm1 : 1 ≤ n - a := by omega
          have hmK : n - a ≤ K := by omega
          have hmv := sd_LopIter_sliceV_sq_le_sliceD K α u
            (Finset.mem_Icc.mpr ⟨hm1, hmK⟩) hθI
          have hX : 0 ≤ (LopIter (n - a) (sliceV u) θ) ^ 2 * thGam α θ :=
            mul_nonneg (sq_nonneg _) hg0
          have hcomb : ((n.choose a : ℝ)
              * LopIter a (fun θ : ℝ => (Real.sin (2 * θ)) ^ 2) θ
              * LopIter (n - a) (sliceV u) θ) ^ 2 * thGam α θ
              = ((n.choose a : ℝ)) ^ 2
                * ((LopIter a (fun θ : ℝ => (Real.sin (2 * θ)) ^ 2) θ) ^ 2
                  * ((LopIter (n - a) (sliceV u) θ) ^ 2 * thGam α θ)) := by ring
          rw [hcomb]
          refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
          calc (LopIter a (fun θ : ℝ => (Real.sin (2 * θ)) ^ 2) θ) ^ 2
                * ((LopIter (n - a) (sliceV u) θ) ^ 2 * thGam α θ)
              ≤ F ^ 2 * ((Real.sin (2 * θ)) ^ 2) ^ 2
                * ((LopIter (n - a) (sliceV u) θ) ^ 2 * thGam α θ) :=
                mul_le_mul_of_nonneg_right hsq hX
            _ = F ^ 2 * (((Real.sin (2 * θ)) ^ 2) ^ 2
                  * ((LopIter (n - a) (sliceV u) θ) ^ 2 * thGam α θ)) := by ring
            _ ≤ F ^ 2 * (1 * ((LopIter (n - a) (sliceV u) θ) ^ 2 * thGam α θ)) :=
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hs4le hX) (sq_nonneg F)
            _ = F ^ 2 * ((LopIter (n - a) (sliceV u) θ) ^ 2 * thGam α θ) := by ring
            _ ≤ F ^ 2 * sliceD K α u θ := mul_le_mul_of_nonneg_left hmv (sq_nonneg F)
        · subst a
          rw [Nat.sub_self, LopIter_zero, Nat.choose_self, Nat.cast_one, one_pow, one_mul]
          have hsqn : (LopIter n (fun θ : ℝ => (Real.sin (2 * θ)) ^ 2) θ) ^ 2
              ≤ F ^ 2 * ((Real.sin (2 * θ)) ^ 2) ^ 2 := by
            rw [← sq_abs]
            calc |LopIter n (fun θ : ℝ => (Real.sin (2 * θ)) ^ 2) θ| ^ 2
                ≤ (F * (Real.sin (2 * θ)) ^ 2) ^ 2 :=
                  pow_le_pow_left₀ (abs_nonneg _) (hDssF n hnK θ hθI) 2
              _ = F ^ 2 * ((Real.sin (2 * θ)) ^ 2) ^ 2 := by ring
          have hrpow : ((Real.sin (2 * θ)) ^ 2) ^ 2 * thGam α θ
              = (Real.sin (2 * θ)) ^ (4 - Work.Spaces.gam α) := by
            have h4a : ((Real.sin (2 * θ)) ^ 2) ^ 2 = (Real.sin (2 * θ)) ^ 4 := by ring
            rw [h4a, show thGam α θ = (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) from rfl]
            exact sd_pow_mul_rpow (sin_two_nonneg hθI) (by norm_num) (sd_gam_ne hα0)
              (by intro hc; exact sd_four_sub_gam_ne hα1 (sub_eq_zero.mpr hc))
          have hcomb : (LopIter n (fun θ : ℝ => (Real.sin (2 * θ)) ^ 2) θ * sliceV u θ) ^ 2
              * thGam α θ
              = (LopIter n (fun θ : ℝ => (Real.sin (2 * θ)) ^ 2) θ) ^ 2
                * ((sliceV u θ) ^ 2 * thGam α θ) := by ring
          have hmain : (LopIter n (fun θ : ℝ => (Real.sin (2 * θ)) ^ 2) θ * sliceV u θ) ^ 2
              * thGam α θ ≤ F ^ 2 * sliceD K α u θ := by
            rw [hcomb]
            have h4le := sd_four_sub_gam_le_thEta hα1 hθI
            have hvle := sd_sliceV_sq_le_sliceD K α u hθI
            calc (LopIter n (fun θ : ℝ => (Real.sin (2 * θ)) ^ 2) θ) ^ 2
                  * ((sliceV u θ) ^ 2 * thGam α θ)
                ≤ F ^ 2 * ((Real.sin (2 * θ)) ^ 2) ^ 2
                  * ((sliceV u θ) ^ 2 * thGam α θ) :=
                  mul_le_mul_of_nonneg_right hsqn (mul_nonneg (sq_nonneg _) hg0)
              _ = F ^ 2 * ((sliceV u θ) ^ 2
                    * (((Real.sin (2 * θ)) ^ 2) ^ 2 * thGam α θ)) := by ring
              _ = F ^ 2 * ((sliceV u θ) ^ 2
                    * (Real.sin (2 * θ)) ^ (4 - Work.Spaces.gam α)) := by rw [hrpow]
              _ ≤ F ^ 2 * ((sliceV u θ) ^ 2 * thEta θ) :=
                  mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h4le (sq_nonneg _))
                    (sq_nonneg F)
              _ ≤ F ^ 2 * sliceD K α u θ := mul_le_mul_of_nonneg_left hvle (sq_nonneg F)
          simpa using hmain
      -- the `u`-terms of the expansion
      have hterm2 : ∀ a ∈ Finset.range (n + 1),
          ((n.choose a : ℝ)
              * LopIter a (fun θ : ℝ => 2 * Real.cos (2 * θ)) θ
              * LopIter (n + 1 - a) u θ) ^ 2 * thGam α θ
            ≤ ((n.choose a : ℝ)) ^ 2 * (F ^ 2 * (B ^ (n + 1) * sliceD K α u θ)) := by
        intro a ha
        have ha' : a ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
        rcases Nat.eq_zero_or_pos a with h0a | hpos
        · subst a
          rw [Nat.choose_zero_right, Nat.cast_one, one_pow, Nat.sub_zero, one_mul]
          have hccval : LopIter 0 (fun θ : ℝ => 2 * Real.cos (2 * θ)) θ
              = 2 * Real.cos (2 * θ) := by simp only [LopIter_zero]
          rw [hccval]
          have hc2 : (2 * Real.cos (2 * θ)) ^ 2 ≤ F ^ 2 := by
            rw [← sq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _) (hEF 0 (Nat.zero_le K) θ hθI) 2
          have hIHn := hIH (n + 1) (by omega) le_rfl
          have hcomb : (2 * Real.cos (2 * θ) * LopIter (n + 1) u θ) ^ 2 * thGam α θ
              = (2 * Real.cos (2 * θ)) ^ 2 * ((LopIter (n + 1) u θ) ^ 2 * thGam α θ) := by
            ring
          rw [hcomb]
          calc (2 * Real.cos (2 * θ)) ^ 2 * ((LopIter (n + 1) u θ) ^ 2 * thGam α θ)
              ≤ F ^ 2 * ((LopIter (n + 1) u θ) ^ 2 * thGam α θ) :=
                mul_le_mul_of_nonneg_right hc2 (mul_nonneg (sq_nonneg _) hg0)
            _ ≤ F ^ 2 * (B ^ (n + 1) * sliceD K α u θ) :=
                mul_le_mul_of_nonneg_left hIHn (sq_nonneg F)
            _ = 1 * (F ^ 2 * (B ^ (n + 1) * sliceD K α u θ)) := by ring
        · obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
          have hbK : b + 1 ≤ K := by omega
          have hcsq : (LopIter (b + 1) (fun θ : ℝ => 2 * Real.cos (2 * θ)) θ) ^ 2
              ≤ F ^ 2 := by
            rw [← sq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _) (hEF (b + 1) hbK θ hθI) 2
          have hj1 : 1 ≤ n + 1 - (b + 1) := by omega
          have hjK : n + 1 - (b + 1) ≤ n + 1 := by omega
          have hIHj := hIH (n + 1 - (b + 1)) hj1 hjK
          have hX : 0 ≤ (LopIter (n + 1 - (b + 1)) u θ) ^ 2 * thGam α θ :=
            mul_nonneg (sq_nonneg _) hg0
          have hcomb : ((n.choose (b + 1) : ℝ)
              * LopIter (b + 1) (fun θ : ℝ => 2 * Real.cos (2 * θ)) θ
              * LopIter (n + 1 - (b + 1)) u θ) ^ 2 * thGam α θ
              = ((n.choose (b + 1) : ℝ)) ^ 2
                * ((LopIter (b + 1) (fun θ : ℝ => 2 * Real.cos (2 * θ)) θ) ^ 2
                  * ((LopIter (n + 1 - (b + 1)) u θ) ^ 2 * thGam α θ)) := by ring
          rw [hcomb]
          refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
          calc (LopIter (b + 1) (fun θ : ℝ => 2 * Real.cos (2 * θ)) θ) ^ 2
                * ((LopIter (n + 1 - (b + 1)) u θ) ^ 2 * thGam α θ)
              ≤ F ^ 2 * ((LopIter (n + 1 - (b + 1)) u θ) ^ 2 * thGam α θ) :=
                mul_le_mul_of_nonneg_right hcsq hX
            _ ≤ F ^ 2 * (B ^ (n + 1) * sliceD K α u θ) :=
                mul_le_mul_of_nonneg_left hIHj (sq_nonneg F)
      -- Cauchy–Schwarz for the first sum
      have hS1sq : (∑ a ∈ Finset.range (n + 1), (n.choose a : ℝ)
            * LopIter a (fun θ : ℝ => (Real.sin (2 * θ)) ^ 2) θ
            * LopIter (n - a) (sliceV u) θ) ^ 2 * thGam α θ
          ≤ ((n : ℝ) + 1) ^ 2 * F ^ 2 * (4 : ℝ) ^ n * sliceD K α u θ := by
        have hcs := sd_sum_sq_mul_le (Finset.range (n + 1))
          (fun a => (n.choose a : ℝ) * LopIter a (fun θ : ℝ => (Real.sin (2 * θ)) ^ 2) θ
            * LopIter (n - a) (sliceV u) θ) hg0
        have hcs' : (∑ a ∈ Finset.range (n + 1), (n.choose a : ℝ)
              * LopIter a (fun θ : ℝ => (Real.sin (2 * θ)) ^ 2) θ
              * LopIter (n - a) (sliceV u) θ) ^ 2 * thGam α θ
            ≤ ((n : ℝ) + 1) * ∑ a ∈ Finset.range (n + 1),
                ((n.choose a : ℝ) * LopIter a (fun θ : ℝ => (Real.sin (2 * θ)) ^ 2) θ
                  * LopIter (n - a) (sliceV u) θ) ^ 2 * thGam α θ := by
          simpa only [Finset.card_range, Nat.cast_add, Nat.cast_one] using hcs
        calc (∑ a ∈ Finset.range (n + 1), (n.choose a : ℝ)
              * LopIter a (fun θ : ℝ => (Real.sin (2 * θ)) ^ 2) θ
              * LopIter (n - a) (sliceV u) θ) ^ 2 * thGam α θ
            ≤ ((n : ℝ) + 1) * ∑ a ∈ Finset.range (n + 1),
                ((n.choose a : ℝ) * LopIter a (fun θ : ℝ => (Real.sin (2 * θ)) ^ 2) θ
                  * LopIter (n - a) (sliceV u) θ) ^ 2 * thGam α θ := hcs'
          _ ≤ ((n : ℝ) + 1) * ∑ a ∈ Finset.range (n + 1),
                (((n.choose a : ℝ)) ^ 2 * (F ^ 2 * sliceD K α u θ)) :=
              mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm1)
                (show (0 : ℝ) ≤ (n : ℝ) + 1 by positivity)
          _ = ((n : ℝ) + 1) * (F ^ 2 * sliceD K α u θ)
                * (∑ a ∈ Finset.range (n + 1), ((n.choose a : ℝ)) ^ 2) := by
              rw [← Finset.sum_mul]
              ring_nf
          _ ≤ ((n : ℝ) + 1) * (F ^ 2 * sliceD K α u θ)
                * (((n : ℝ) + 1) * (4 : ℝ) ^ n) :=
              mul_le_mul_of_nonneg_left (sd_choose_sq_sum_le n)
                (mul_nonneg (by positivity) (mul_nonneg (sq_nonneg F) hP0θ))
          _ = ((n : ℝ) + 1) ^ 2 * F ^ 2 * (4 : ℝ) ^ n * sliceD K α u θ := by ring_nf
      -- Cauchy–Schwarz for the second sum
      have hS2sq : (∑ a ∈ Finset.range (n + 1), (n.choose a : ℝ)
            * LopIter a (fun θ : ℝ => 2 * Real.cos (2 * θ)) θ
            * LopIter (n + 1 - a) u θ) ^ 2 * thGam α θ
          ≤ ((n : ℝ) + 1) ^ 2 * (4 : ℝ) ^ n
              * (F ^ 2 * (B ^ (n + 1) * sliceD K α u θ)) := by
        have hcs := sd_sum_sq_mul_le (Finset.range (n + 1))
          (fun a => (n.choose a : ℝ) * LopIter a (fun θ : ℝ => 2 * Real.cos (2 * θ)) θ
            * LopIter (n + 1 - a) u θ) hg0
        have hcs' : (∑ a ∈ Finset.range (n + 1), (n.choose a : ℝ)
              * LopIter a (fun θ : ℝ => 2 * Real.cos (2 * θ)) θ
              * LopIter (n + 1 - a) u θ) ^ 2 * thGam α θ
            ≤ ((n : ℝ) + 1) * ∑ a ∈ Finset.range (n + 1),
                ((n.choose a : ℝ) * LopIter a (fun θ : ℝ => 2 * Real.cos (2 * θ)) θ
                  * LopIter (n + 1 - a) u θ) ^ 2 * thGam α θ := by
          simpa only [Finset.card_range, Nat.cast_add, Nat.cast_one] using hcs
        calc (∑ a ∈ Finset.range (n + 1), (n.choose a : ℝ)
              * LopIter a (fun θ : ℝ => 2 * Real.cos (2 * θ)) θ
              * LopIter (n + 1 - a) u θ) ^ 2 * thGam α θ
            ≤ ((n : ℝ) + 1) * ∑ a ∈ Finset.range (n + 1),
                ((n.choose a : ℝ) * LopIter a (fun θ : ℝ => 2 * Real.cos (2 * θ)) θ
                  * LopIter (n + 1 - a) u θ) ^ 2 * thGam α θ := hcs'
          _ ≤ ((n : ℝ) + 1) * ∑ a ∈ Finset.range (n + 1),
                (((n.choose a : ℝ)) ^ 2 * (F ^ 2 * (B ^ (n + 1) * sliceD K α u θ))) :=
              mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm2)
                (show (0 : ℝ) ≤ (n : ℝ) + 1 by positivity)
          _ = ((n : ℝ) + 1) * (F ^ 2 * (B ^ (n + 1) * sliceD K α u θ))
                * (∑ a ∈ Finset.range (n + 1), ((n.choose a : ℝ)) ^ 2) := by
              rw [← Finset.sum_mul]
              ring_nf
          _ ≤ ((n : ℝ) + 1) * (F ^ 2 * (B ^ (n + 1) * sliceD K α u θ))
                * (((n : ℝ) + 1) * (4 : ℝ) ^ n) :=
              mul_le_mul_of_nonneg_left (sd_choose_sq_sum_le n)
                (mul_nonneg (by positivity)
                  (mul_nonneg (sq_nonneg F) (mul_nonneg (pow_nonneg hB0 _) hP0θ)))
          _ = ((n : ℝ) + 1) ^ 2 * (4 : ℝ) ^ n
                * (F ^ 2 * (B ^ (n + 1) * sliceD K α u θ)) := by ring_nf
      -- assembly
      rw [hexp]
      have hsq21 : ((∑ a ∈ Finset.range (n + 1), (n.choose a : ℝ)
              * LopIter a (fun θ : ℝ => (Real.sin (2 * θ)) ^ 2) θ
              * LopIter (n - a) (sliceV u) θ)
            + (∑ a ∈ Finset.range (n + 1), (n.choose a : ℝ)
              * LopIter a (fun θ : ℝ => 2 * Real.cos (2 * θ)) θ
              * LopIter (n + 1 - a) u θ)) ^ 2
          ≤ 2 * ((∑ a ∈ Finset.range (n + 1), (n.choose a : ℝ)
              * LopIter a (fun θ : ℝ => (Real.sin (2 * θ)) ^ 2) θ
              * LopIter (n - a) (sliceV u) θ) ^ 2
            + (∑ a ∈ Finset.range (n + 1), (n.choose a : ℝ)
              * LopIter a (fun θ : ℝ => 2 * Real.cos (2 * θ)) θ
              * LopIter (n + 1 - a) u θ) ^ 2) := by
        nlinarith [sq_nonneg ((∑ a ∈ Finset.range (n + 1), (n.choose a : ℝ)
              * LopIter a (fun θ : ℝ => (Real.sin (2 * θ)) ^ 2) θ
              * LopIter (n - a) (sliceV u) θ)
            - (∑ a ∈ Finset.range (n + 1), (n.choose a : ℝ)
              * LopIter a (fun θ : ℝ => 2 * Real.cos (2 * θ)) θ
              * LopIter (n + 1 - a) u θ))]
      have hstep : ((∑ a ∈ Finset.range (n + 1), (n.choose a : ℝ)
              * LopIter a (fun θ : ℝ => (Real.sin (2 * θ)) ^ 2) θ
              * LopIter (n - a) (sliceV u) θ)
            + (∑ a ∈ Finset.range (n + 1), (n.choose a : ℝ)
              * LopIter a (fun θ : ℝ => 2 * Real.cos (2 * θ)) θ
              * LopIter (n + 1 - a) u θ)) ^ 2 * thGam α θ
          ≤ 2 * (((∑ a ∈ Finset.range (n + 1), (n.choose a : ℝ)
              * LopIter a (fun θ : ℝ => (Real.sin (2 * θ)) ^ 2) θ
              * LopIter (n - a) (sliceV u) θ) ^ 2 * thGam α θ)
            + ((∑ a ∈ Finset.range (n + 1), (n.choose a : ℝ)
              * LopIter a (fun θ : ℝ => 2 * Real.cos (2 * θ)) θ
              * LopIter (n + 1 - a) u θ) ^ 2 * thGam α θ)) := by
        have h1 := mul_le_mul_of_nonneg_right hsq21 hg0
        have h2 : 2 * ((∑ a ∈ Finset.range (n + 1), (n.choose a : ℝ)
                * LopIter a (fun θ : ℝ => (Real.sin (2 * θ)) ^ 2) θ
                * LopIter (n - a) (sliceV u) θ) ^ 2
              + (∑ a ∈ Finset.range (n + 1), (n.choose a : ℝ)
                * LopIter a (fun θ : ℝ => 2 * Real.cos (2 * θ)) θ
                * LopIter (n + 1 - a) u θ) ^ 2) * thGam α θ
            = 2 * (((∑ a ∈ Finset.range (n + 1), (n.choose a : ℝ)
                * LopIter a (fun θ : ℝ => (Real.sin (2 * θ)) ^ 2) θ
                * LopIter (n - a) (sliceV u) θ) ^ 2 * thGam α θ)
              + ((∑ a ∈ Finset.range (n + 1), (n.choose a : ℝ)
                * LopIter a (fun θ : ℝ => 2 * Real.cos (2 * θ)) θ
                * LopIter (n + 1 - a) u θ) ^ 2 * thGam α θ)) := by ring
        linarith [h1, le_of_eq h2]
      have hbnd : 2 * (((∑ a ∈ Finset.range (n + 1), (n.choose a : ℝ)
              * LopIter a (fun θ : ℝ => (Real.sin (2 * θ)) ^ 2) θ
              * LopIter (n - a) (sliceV u) θ) ^ 2 * thGam α θ)
            + ((∑ a ∈ Finset.range (n + 1), (n.choose a : ℝ)
              * LopIter a (fun θ : ℝ => 2 * Real.cos (2 * θ)) θ
              * LopIter (n + 1 - a) u θ) ^ 2 * thGam α θ))
          ≤ 2 * (((n : ℝ) + 1) ^ 2 * F ^ 2 * (4 : ℝ) ^ n * sliceD K α u θ
            + ((n : ℝ) + 1) ^ 2 * (4 : ℝ) ^ n
              * (F ^ 2 * (B ^ (n + 1) * sliceD K α u θ))) :=
        mul_le_mul_of_nonneg_left (add_le_add hS1sq hS2sq) (by norm_num)
      have hcore : 2 * (1 + B ^ (n + 1)) ≤ 34 * B ^ (n + 1) := by
        have hBp : 1 ≤ B ^ (n + 1) := one_le_pow₀ hB1
        linarith
      have hfac : 0 ≤ ((n : ℝ) + 1) ^ 2 * F ^ 2 * (4 : ℝ) ^ n * sliceD K α u θ :=
        mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg F))
          (pow_nonneg (by norm_num) n)) hP0θ
      have hfinal1 : 2 * (((n : ℝ) + 1) ^ 2 * F ^ 2 * (4 : ℝ) ^ n * sliceD K α u θ
            + ((n : ℝ) + 1) ^ 2 * (4 : ℝ) ^ n
              * (F ^ 2 * (B ^ (n + 1) * sliceD K α u θ)))
          ≤ 34 * ((n : ℝ) + 1) ^ 2 * F ^ 2 * (4 : ℝ) ^ n * B ^ (n + 1)
              * sliceD K α u θ := by
        calc 2 * (((n : ℝ) + 1) ^ 2 * F ^ 2 * (4 : ℝ) ^ n * sliceD K α u θ
              + ((n : ℝ) + 1) ^ 2 * (4 : ℝ) ^ n
                * (F ^ 2 * (B ^ (n + 1) * sliceD K α u θ)))
            = ((n : ℝ) + 1) ^ 2 * F ^ 2 * (4 : ℝ) ^ n * sliceD K α u θ
              * (2 * (1 + B ^ (n + 1))) := by ring_nf
          _ ≤ ((n : ℝ) + 1) ^ 2 * F ^ 2 * (4 : ℝ) ^ n * sliceD K α u θ
              * (34 * B ^ (n + 1)) := mul_le_mul_of_nonneg_left hcore hfac
          _ = 34 * ((n : ℝ) + 1) ^ 2 * F ^ 2 * (4 : ℝ) ^ n * B ^ (n + 1)
              * sliceD K α u θ := by ring_nf
      have hlast : 34 * ((n : ℝ) + 1) ^ 2 * F ^ 2 * (4 : ℝ) ^ n * B ^ (n + 1)
            * sliceD K α u θ ≤ B ^ (n + 2) * sliceD K α u θ := by
        have hfacs : 0 ≤ B ^ (n + 1) * sliceD K α u θ :=
          mul_nonneg (pow_nonneg hB0 _) hP0θ
        have h := mul_le_mul_of_nonneg_right (hBstep n hnK) hfacs
        calc 34 * ((n : ℝ) + 1) ^ 2 * F ^ 2 * (4 : ℝ) ^ n * B ^ (n + 1)
              * sliceD K α u θ
            = (34 * ((n : ℝ) + 1) ^ 2 * F ^ 2 * (4 : ℝ) ^ n)
              * (B ^ (n + 1) * sliceD K α u θ) := by ring
          _ ≤ B * (B ^ (n + 1) * sliceD K α u θ) := h
          _ = B ^ (n + 2) * sliceD K α u θ := by
              rw [show n + 2 = (n + 1) + 1 by omega, pow_succ]
              ring
      exact le_trans hstep (le_trans hbnd (le_trans hfinal1 hlast))
  have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
  have hiK : i ≤ K := (Finset.mem_Icc.mp hi).2
  calc (LopIter i u θ) ^ 2 * thGam α θ ≤ B ^ i * sliceD K α u θ := key i hiK hi1
    _ ≤ B ^ K * sliceD K α u θ :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hB1 hiK) hP0θ

end Work.FTS.EllSol.VopAux
