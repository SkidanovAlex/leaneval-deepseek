import Mathlib.Analysis.Meromorphic.NormalForm
import Submission.Commons.NumberTheory.DirichletCharacter.zerosInStrip
import Submission.Commons.NumberTheory.Linnik.divisor_eq_closedBall_subset

/-!
# Covering the zeros of the completed Dirichlet L-function by unit windows

`completedL_window_cover`: for a primitive non-trivial Dirichlet character `χ mod N`,
every zero of `Λ(s, χ) = completedLFunction χ s` lies in the critical strip
`0 < Re s < 1` (`zerosInStrip`), so the zeros inside the disk
`B(2 + i t, R)` (with `R ≥ 2`) are all contained in the union of the unit-width
windows `B(2 + i (t - (R + 1) + j), 2.5)` for `0 ≤ j ≤ ceil (2R + 2)`.

Indeed a point `u = x + i y` of the disk with `0 < x < 1` satisfies
`|y - t| ≤ R`, so with `m := y - t + R + 1 ∈ [1, 2R + 1]` and
`j := floor m ≤ ceil (2R + 2)` one has `|y - (t - (R + 1) + j)| = |m - j| < 1`
while `|x - 2| < 2`; hence `u` lies in the window `j`.  Since `Λ` is entire, the
divisor coefficients are non-negative integers (orders of zeros), the divisor on
each ball has finite support, and equality `divisor_B u = divisor_{window j} u`
for `u` in both balls (`divisor_eq_closedBall_subset`) turns the pointwise
covering into the claimed inequality of divisor sums.
-/

open Complex DirichletCharacter Metric
open scoped Real Topology BigOperators

noncomputable section

-- The `∑ j in s` binder for Finset sums was removed from the current mathlib
-- big-operator syntax (only `∑ j ∈ s` remains).  We restore it so that the
-- original statement below parses; it expands to exactly `Finset.sum s`.
syntax (name := bigsum_in) "∑ " ident " in " term ", " term:67 : term
macro_rules (kind := bigsum_in)
  | `(∑ $j:ident in $s, $v) => `(Finset.sum $s (fun $j => $v))

namespace Commons.NumberTheory.DirichletCharacter

private lemma completedLFunction_analyticOnNhd {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (U : Set ℂ) :
    AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ) U := by
  intro z hz
  exact (DirichletCharacter.differentiable_completedLFunction hχ).analyticAt z

private lemma divisor_zero_of_analytic_ne_zero {f : ℂ → ℂ} {U : Set ℂ} {z : ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hz : z ∈ U) (hfz : f z ≠ 0) :
    MeromorphicOn.divisor f U z = 0 := by
  rw [MeromorphicOn.divisor_apply hf.meromorphicOn hz]
  have hAn : AnalyticAt ℂ f z := hf z hz
  have hord : meromorphicOrderAt f z = 0 := by
    rw [hAn.meromorphicOrderAt_eq]
    have h0 : analyticOrderAt f z = 0 := analyticOrderAt_eq_zero.mpr (Or.inr hfz)
    simp [h0]
  simp [hord]

private lemma divisor_real_nonneg_of_analyticOnNhd {f : ℂ → ℂ} {U : Set ℂ} {z : ℂ}
    (hf : AnalyticOnNhd ℂ f U) :
    (0 : ℝ) ≤ ((MeromorphicOn.divisor f U z : ℤ) : ℝ) := by
  by_cases hz : z ∈ U
  · rw [MeromorphicOn.divisor_apply hf.meromorphicOn hz]
    have hAn : AnalyticAt ℂ f z := hf z hz
    have hNF := hAn.meromorphicNFAt
    have hord : (0 : WithTop ℤ) ≤ meromorphicOrderAt f z :=
      (MeromorphicNFAt.meromorphicOrderAt_nonneg_iff_analyticAt hNF).2 hAn
    have hnn : (0 : ℤ) ≤ (meromorphicOrderAt f z).untop₀ :=
      (WithTop.untop₀_nonneg (α := ℤ) (a := meromorphicOrderAt f z)).mpr hord
    exact_mod_cast hnn
  · rw [MeromorphicOn.divisor_def]
    rw [if_neg (by intro h; exact hz h.2)]
    norm_num

private lemma divisor_finSupport {f : ℂ → ℂ} {U : Set ℂ} (hcomp : IsCompact U) :
    (Function.support (fun u : ℂ => (MeromorphicOn.divisor f U u : ℤ))).Finite := by
  simpa using (MeromorphicOn.divisor f U).finiteSupport hcomp

private lemma divisor_real_finSupport_ball {f : ℂ → ℂ} (a : ℂ) (ρ : ℝ) :
    Function.HasFiniteSupport
      (fun u : ℂ => (((MeromorphicOn.divisor f (Metric.closedBall a ρ)) u : ℤ) : ℝ)) := by
  classical
  have hfinZ : (Function.support
      (fun u : ℂ => ((MeromorphicOn.divisor f (Metric.closedBall a ρ)) u : ℤ))).Finite :=
    divisor_finSupport (isCompact_closedBall a ρ)
  exact hfinZ.subset (by
    intro u hu
    rw [Function.mem_support] at hu ⊢
    exact fun hz => hu (by exact_mod_cast hz))

private lemma sum_finSupport_sum (s : Finset ℕ) (b : ℕ → ℂ → ℝ)
    (hfin : ∀ j ∈ s, Function.HasFiniteSupport (b j)) :
    Function.HasFiniteSupport (fun u : ℂ => ∑ j in s, b j u) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [Function.HasFiniteSupport]
  | insert j s' hjs ih =>
      have hfinj : Function.HasFiniteSupport (b j) := hfin j (by simp [hjs])
      have hfins : Function.HasFiniteSupport (fun u : ℂ => ∑ x in s', b x u) := ih (fun x hx => hfin x (by simp [hx]))
      have hsum : (fun u : ℂ => ∑ x in insert j s', b x u) =
          (fun u : ℂ => b j u + ∑ x in s', b x u) := by
        ext u
        rw [Finset.sum_insert hjs]
      rw [hsum]
      exact hfinj.add hfins

private lemma window_cover_exists {u : ℂ} {t R : ℝ} (_hR : 2 ≤ R)
    (huB : u ∈ Metric.closedBall ((2 : ℂ) + Complex.I * (t : ℂ)) R)
    (hre_lo : 0 < u.re) (hre_hi : u.re < 1) :
    ∃ j : ℕ, j ≤ Nat.ceil (2 * R + 2) ∧
      ‖u - ((2 : ℂ) + Complex.I * ((t - (R + 1) + (j : ℝ)) : ℂ))‖ ≤ (5 / 2 : ℝ) := by
  classical
  let c : ℂ := (2 : ℂ) + Complex.I * (t : ℂ)
  have hmem : dist u c ≤ R := by
    simpa [c] using (Metric.mem_closedBall.mp huB)
  have hdist : ‖u - c‖ ≤ R := by simpa [dist_eq_norm] using hmem
  have him0 : |(u - c).im| ≤ ‖u - c‖ := Complex.abs_im_le_norm (u - c)
  have him : |u.im - t| ≤ R := by
    have : |(u - c).im| ≤ R := le_trans him0 hdist
    simpa [c] using this
  let m : ℝ := u.im - t + R + 1
  have hm1 : 1 ≤ m := by
    have hlo := (abs_le.mp him).1
    dsimp [m]
    linarith
  have hm2 : m ≤ 2 * R + 1 := by
    have hhi := (abs_le.mp him).2
    dsimp [m]
    linarith
  let j : ℕ := Nat.floor m
  have hj_ge : (j : ℝ) ≤ m := by
    dsimp [j]
    exact Nat.floor_le (by nlinarith : 0 ≤ m)
  have hj_le : m < (j : ℝ) + 1 := by
    dsimp [j]
    exact Nat.lt_floor_add_one m
  have hfl : (j : ℝ) ≤ (Nat.ceil (2 * R + 2) : ℝ) := by
    calc
      (j : ℝ) ≤ m := hj_ge
      _ ≤ 2 * R + 1 := hm2
      _ ≤ 2 * R + 2 := by nlinarith
      _ ≤ (Nat.ceil (2 * R + 2) : ℝ) := Nat.le_ceil (2 * R + 2)
  have hj : j ≤ Nat.ceil (2 * R + 2) := by
    exact_mod_cast hfl
  refine ⟨j, hj, ?_⟩
  let w : ℂ := (2 : ℂ) + Complex.I * ((t - (R + 1) + (j : ℝ)) : ℂ)
  have hns : ‖u - w‖ ^ 2 = (u.re - 2) ^ 2 + (m - (j : ℝ)) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    rw [Complex.normSq_apply]
    have hre : (u - w).re = u.re - 2 := by simp [w]
    have him2 : (u - w).im = m - (j : ℝ) := by
      dsimp [m]
      simp [w]
      ring
    rw [hre, him2]
    ring
  have hsq1 : (u.re - 2) ^ 2 ≤ 4 := by
    have hs : (u.re - 2) ^ 2 ≤ (2 : ℝ) ^ 2 := by
      exact sq_le_sq' (a := u.re - 2) (b := 2) (by nlinarith [hre_lo]) (by nlinarith [hre_hi])
    norm_num at hs
    exact hs
  have hsq2 : (m - (j : ℝ)) ^ 2 ≤ 1 := by
    refine (sq_le_one_iff_abs_le_one (m - (j : ℝ))).mpr ?_
    rw [abs_of_nonneg (by nlinarith [hj_ge] : (0 : ℝ) ≤ m - (j : ℝ))]
    nlinarith [hj_le]
  have hsq : ‖u - w‖ ^ 2 ≤ (5 / 2) ^ 2 := by
    rw [hns]
    nlinarith
  have habs : |‖u - w‖| ≤ |(5 / 2 : ℝ)| := (sq_le_sq.mp hsq)
  have hmain : ‖u - w‖ ≤ (5 / 2 : ℝ) := by
    simpa [abs_of_nonneg (norm_nonneg (u - w)), abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 5 / 2)] using habs
  simpa [w] using hmain

/-- **Covering lemma for the zero count of the completed L-function.**  For a primitive
non-trivial character `χ mod N`, the divisor sum of `completedLFunction χ` over the disk
`B(2 + i t, R)` (`R ≥ 2`) is bounded by the sum, over the windows indexed by
`j = 0, …, ceil (2R + 2)` centered at `2 + i (t - (R + 1) + j)` with radius `2.5`,
of the divisor sums over those windows.  All zeros of the completed L-function lie in the
critical strip, and the windows cover that part of the disk. -/
theorem completedL_window_cover {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) {R t : ℝ} (hR : 2 ≤ R) :
    (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall ((2 : ℂ) + Complex.I * (t : ℂ)) R)) u : ℤ) : ℝ)) ≤
      ∑ j in Finset.range (Nat.ceil (2 * R + 2) + 1),
        (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
            (Metric.closedBall ((2 : ℂ) + Complex.I * ((t - (R + 1) + (j : ℝ)) : ℂ)) 2.5)) u : ℤ) : ℝ)) := by
  classical
  let Λ : ℂ → ℂ := DirichletCharacter.completedLFunction χ
  let cB : ℂ := (2 : ℂ) + Complex.I * (t : ℂ)
  let cw : ℕ → ℂ := fun j => (2 : ℂ) + Complex.I * ((t - (R + 1) + (j : ℝ)) : ℂ)
  let B : Set ℂ := Metric.closedBall cB R
  let W : ℕ → Set ℂ := fun j => Metric.closedBall (cw j) 2.5
  let a : ℂ → ℝ := fun u => (((MeromorphicOn.divisor Λ B) u : ℤ) : ℝ)
  let b : ℕ → ℂ → ℝ := fun j u => (((MeromorphicOn.divisor Λ (W j)) u : ℤ) : ℝ)
  let s : Finset ℕ := Finset.range (Nat.ceil (2 * R + 2) + 1)
  have hΛan (U : Set ℂ) : AnalyticOnNhd ℂ Λ U := by
    dsimp [Λ]
    exact completedLFunction_analyticOnNhd χ hχ U
  have hfinA : Function.HasFiniteSupport a := by
    dsimp [a, B, cB, Λ]
    exact divisor_real_finSupport_ball (a := ((2 : ℂ) + Complex.I * (t : ℂ))) (ρ := R)
  have hfinB : ∀ j ∈ s, Function.HasFiniteSupport (b j) := by
    intro j hj
    dsimp [b, W, cw, Λ]
    exact divisor_real_finSupport_ball (a := ((2 : ℂ) + Complex.I * ((t - (R + 1) + (j : ℝ)) : ℂ))) (ρ := 2.5)
  have hnonnegB : ∀ (j : ℕ) (u : ℂ), 0 ≤ b j u := by
    intro j u
    dsimp [b, W, cw, Λ]
    exact divisor_real_nonneg_of_analyticOnNhd (completedLFunction_analyticOnNhd χ hχ (Metric.closedBall ((2 : ℂ) + Complex.I * ((t - (R + 1) + (j : ℝ)) : ℂ)) 2.5))
  have hpoint : ∀ u : ℂ, a u ≤ ∑ j in s, b j u := by
    intro u
    by_cases ha0 : a u = 0
    · rw [ha0]
      exact Finset.sum_nonneg (fun j hj => hnonnegB j u)
    · have hdivZ : (MeromorphicOn.divisor Λ B u : ℤ) ≠ 0 := by
        intro hz
        apply ha0
        dsimp [a]
        exact_mod_cast hz
      have huB : u ∈ B := by
        by_contra hnot
        have : MeromorphicOn.divisor Λ B u = 0 :=
          (MeromorphicOn.divisor Λ B).apply_eq_zero_of_notMem hnot
        exact hdivZ this
      have hΛ0 : Λ u = 0 := by
        by_contra hnf
        have hzero : MeromorphicOn.divisor Λ B u = 0 :=
          divisor_zero_of_analytic_ne_zero (hΛan B) huB hnf
        exact hdivZ hzero
      have hst : 0 < u.re ∧ u.re < 1 := by
        exact (Commons.NumberTheory.DirichletCharacter.zerosInStrip χ hχ hχprim u (by simpa [Λ] using hΛ0))
      rcases window_cover_exists (u := u) (t := t) (R := R) hR huB hst.1 hst.2 with ⟨j0, hj0le, hj0dist⟩
      have hj0mem : j0 ∈ s := by
        dsimp [s]
        exact Finset.mem_range.mpr (Nat.lt_succ_of_le hj0le)
      have huW : u ∈ W j0 := by
        dsimp [W, cw]
        rw [Metric.mem_closedBall, dist_eq_norm]
        norm_num
        exact hj0dist
      have heq : a u = b j0 u := by
        dsimp [a, b, B, W]
        have heqZ : MeromorphicOn.divisor Λ (Metric.closedBall cB R) u =
            MeromorphicOn.divisor Λ (Metric.closedBall (cw j0) 2.5) u :=
          Commons.NumberTheory.Linnik.divisor_eq_closedBall_subset (f := Λ) (a := cB) (b := cw j0)
            (ra := R) (rb := 2.5)
            (hf := hΛan (Metric.closedBall cB R ∪ Metric.closedBall (cw j0) 2.5)) huB huW
        exact congrArg (fun n : ℤ => (n : ℝ)) heqZ
      rw [heq]
      exact Finset.single_le_sum (fun j hj => hnonnegB j u) hj0mem
  have hfinBsum : Function.HasFiniteSupport (fun u : ℂ => ∑ j in s, b j u) := by
    exact sum_finSupport_sum (s := s) (b := b) hfinB
  have h1 : (∑ᶠ u : ℂ, a u) ≤ (∑ᶠ u : ℂ, ∑ j in s, b j u) := by
    exact finsum_le_finsum' hfinA hfinBsum hpoint
  have h2 : (∑ᶠ u : ℂ, ∑ j in s, b j u) = ∑ j in s, ∑ᶠ u : ℂ, b j u := by
    exact finsum_sum_comm (s := s) (f := fun (u : ℂ) (j : ℕ) => b j u) (by
      intro j hj
      exact hfinB j hj)
  calc
    (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall ((2 : ℂ) + Complex.I * (t : ℂ)) R)) u : ℤ) : ℝ))
        = ∑ᶠ u : ℂ, a u := by simp [a, Λ, cB, B]
    _ ≤ ∑ᶠ u : ℂ, ∑ j in s, b j u := h1
    _ = ∑ j in s, ∑ᶠ u : ℂ, b j u := h2
    _ = ∑ j in Finset.range (Nat.ceil (2 * R + 2) + 1),
        (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
            (Metric.closedBall ((2 : ℂ) + Complex.I * ((t - (R + 1) + (j : ℝ)) : ℂ)) 2.5)) u : ℤ) : ℝ)) := by
          simp [b, W, cw, s, Λ]

end Commons.NumberTheory.DirichletCharacter