/-
# ZeroFreeTables/P9/zetaCorrector_three_bounds_proof

`zetaCorrector z = -ζ'/ζ(z) - 1/(z-1)` and its first two derivatives are bounded, in real part,
on the compact rectangle `{1 < Re s ≤ 2, |Im s| ≤ 5}`.

The analytic input is the general fact that on a compact set contained in an open set on which a
function `f` is analytic and nowhere zero, `|Re (logDeriv f)^{(k)}|` (`k ≤ 2`) is bounded; applied
to the holomorphic extension `φ = zetaExtPole` of `(s-1)ζ(s)`, and identified with `zetaCorrector`
via the pole splitting `logDeriv φ = 1/(s-1) + ζ'/ζ`.

(The lemmas below are a corrected copy of `P9/zetaExtPoleLemmas`, whose `logDeriv` step currently
does not elaborate; they are kept here so that this development does not depend on it.)
-/
import Mathlib
import Submission.Work.ZeroFreeTables.P9.zetaExtPoleDefs
import Submission.Work.ZeroFreeTables.Rep9.principalRepair

open Complex Set Filter
open scoped Topology

noncomputable section

namespace Work.ZeroFreeTables.P9

/-- On a compact set contained in an open set on which `f` is analytic and nowhere zero, the real
parts of the logarithmic derivative of `f` and of its first two derivatives are bounded by one
positive constant. -/
theorem logDeriv_iteratedDeriv_re_bdd' (f : ℂ → ℂ) (U K : Set ℂ) (hU : IsOpen U)
    (hK : IsCompact K) (hKU : K ⊆ U) (hf : AnalyticOnNhd ℂ f U)
    (hne : ∀ z ∈ U, f z ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ z ∈ K, |(logDeriv f z).re| ≤ C ∧
      |(iteratedDeriv 1 (logDeriv f) z).re| ≤ C ∧
      |(iteratedDeriv 2 (logDeriv f) z).re| ≤ C := by
  have hlog : AnalyticOnNhd ℂ (logDeriv f) U := by
    have h : AnalyticOnNhd ℂ (fun x => deriv f x / f x) U := hf.deriv.div hf hne
    have heq : logDeriv f = fun x => deriv f x / f x := by
      funext x; rw [logDeriv_apply]
    rwa [heq]
  have hiter : ∀ j : ℕ, AnalyticOnNhd ℂ (iteratedDeriv j (logDeriv f)) U := by
    intro j
    induction j with
    | zero => rw [iteratedDeriv_zero]; exact hlog
    | succ j ih => rw [iteratedDeriv_succ]; exact ih.deriv
  have hc : ∀ j : ℕ, ContinuousOn (fun z : ℂ => |(iteratedDeriv j (logDeriv f) z).re|) K := by
    intro j
    exact continuous_abs.comp_continuousOn
      (Complex.continuous_re.comp_continuousOn ((hiter j).continuousOn.mono hKU))
  have hc0 : ContinuousOn (fun z : ℂ => |(logDeriv f z).re|) K :=
    continuous_abs.comp_continuousOn
      (Complex.continuous_re.comp_continuousOn (hlog.continuousOn.mono hKU))
  have hsum : ContinuousOn (fun z : ℂ => |(logDeriv f z).re|
      + |(iteratedDeriv 1 (logDeriv f) z).re| + |(iteratedDeriv 2 (logDeriv f) z).re|) K :=
    (hc0.add (hc 1)).add (hc 2)
  obtain ⟨C₀, hC₀⟩ := hK.bddAbove_image hsum
  have hC : C₀ ≤ |C₀| + 1 := by have h := le_abs_self C₀; linarith
  refine ⟨|C₀| + 1, by positivity, ?_⟩
  intro z hz
  have hle := hC₀ (mem_image_of_mem _ hz)
  have h0 := abs_nonneg (logDeriv f z).re
  have h1 := abs_nonneg (iteratedDeriv 1 (logDeriv f) z).re
  have h2 := abs_nonneg (iteratedDeriv 2 (logDeriv f) z).re
  exact ⟨by linarith, by linarith, by linarith⟩

/-- On the closed rectangle `1 ≤ Re s ≤ 2`, `|Im s| ≤ 5` the extension `z ↦ (z-1)ζ(z)` of `ζ` is
nonzero. -/
theorem zetaExtPole_ne_zero' (s : ℂ) (h1 : 1 ≤ s.re) (h2 : s.re ≤ 2) (h3 : |s.im| ≤ 5) :
    zetaExtPole s ≠ 0 := by
  rcases eq_or_ne s 1 with h | h
  · subst h
    simp [zetaExtPole, psiExtPole, Gammaℝ_one]
  · rw [zetaExtPole_eq s (by rintro rfl; norm_num at h1) h]
    exact mul_ne_zero (sub_ne_zero.mpr h) (riemannZeta_ne_zero_of_one_le_re h1)

/-- The pole splitting of the logarithmic derivative of the extension. -/
theorem logDeriv_zetaExtPole_eq' (s : ℂ) (hs : 1 < s.re) :
    logDeriv zetaExtPole s = 1 / (s - 1) + logDeriv riemannZeta s := by
  have hs0 : s ≠ 0 := by rintro rfl; norm_num at hs
  have hs1 : s ≠ 1 := by rintro rfl; norm_num at hs
  have hev : zetaExtPole =ᶠ[𝓝 s] (fun t : ℂ => (t - 1) * riemannZeta t) := by
    filter_upwards [isOpen_ne.mem_nhds hs0, isOpen_ne.mem_nhds hs1] with t ht0 ht1
    exact zetaExtPole_eq t ht0 ht1
  rw [(logDeriv_congr_nhds hev).self_of_nhds]
  have hkey := logDeriv_mul (f := fun t : ℂ => t - 1) (g := riemannZeta) s
    (sub_ne_zero.mpr hs1) (riemannZeta_ne_zero_of_one_lt_re hs)
    (differentiableAt_id.sub_const 1) (differentiableAt_riemannZeta hs1)
  erw [hkey]
  have hder : deriv (fun t : ℂ => t - 1) s = 1 := by rw [deriv_sub_const, deriv_id'']
  rw [logDeriv_apply, hder]

/-- The open set on which `zetaExtPole` is analytic and nonzero. -/
def zetaExtU' : Set ℂ := {z : ℂ | z ≠ 0 ∧ zetaExtPole z ≠ 0}

lemma isOpen_zetaExtU' : IsOpen zetaExtU' := by
  rw [zetaExtU']
  exact analyticOn_zetaExtPole.continuousOn.isOpen_inter_preimage
    isOpen_compl_singleton isOpen_compl_singleton

lemma zetaRect5_subset_zetaExtU' : zetaRect5 ⊆ zetaExtU' := by
  intro z hz
  simp only [zetaRect5, mem_setOf_eq] at hz
  exact ⟨by rintro rfl; norm_num at hz, zetaExtPole_ne_zero' z hz.1 hz.2.1 hz.2.2⟩

lemma analyticOn_zetaExtPole_of_U' : AnalyticOnNhd ℂ zetaExtPole zetaExtU' :=
  analyticOn_zetaExtPole.mono fun z hz => hz.1

lemma zetaExtPole_ne_zero_on_U' : ∀ z ∈ zetaExtU', zetaExtPole z ≠ 0 := fun z hz => hz.2

theorem zetaCorrector_three_bounds_proof :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, 1 < s.re → s.re ≤ 2 → |s.im| ≤ 5 →
      |(Work.ZeroFreeTables.Rep9.zetaCorrector s).re| ≤ C ∧
      |(iteratedDeriv 1 Work.ZeroFreeTables.Rep9.zetaCorrector s).re| ≤ C ∧
      |(iteratedDeriv 2 Work.ZeroFreeTables.Rep9.zetaCorrector s).re| ≤ C := by
  obtain ⟨C, hCpos, hC⟩ :=
    logDeriv_iteratedDeriv_re_bdd' zetaExtPole zetaExtU' zetaRect5 isOpen_zetaExtU'
      isCompact_zetaRect5 zetaRect5_subset_zetaExtU' analyticOn_zetaExtPole_of_U'
      zetaExtPole_ne_zero_on_U'
  refine ⟨C, hCpos, ?_⟩
  intro s hs1 hs2 hs3
  have hs : s ∈ zetaRect5 := ⟨le_of_lt hs1, hs2, hs3⟩
  obtain ⟨h0, h1, h2⟩ := hC s hs
  have hev : Work.ZeroFreeTables.Rep9.zetaCorrector =ᶠ[𝓝 s]
      (fun t : ℂ => -logDeriv zetaExtPole t) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs1] with t ht
    rw [Work.ZeroFreeTables.Rep9.zetaCorrector, logDeriv_zetaExtPole_eq' t ht]
    ring
  have hgoal : ∀ k : ℕ, (iteratedDeriv k Work.ZeroFreeTables.Rep9.zetaCorrector s).re
      = -((iteratedDeriv k (logDeriv zetaExtPole) s).re) := by
    intro k
    rw [Filter.EventuallyEq.iteratedDeriv_eq k hev, iteratedDeriv_fun_neg, Complex.neg_re]
  refine ⟨?_, ?_, ?_⟩
  · have hg := hgoal 0
    simp only [iteratedDeriv_zero] at hg
    rw [hg]; simpa using h0
  · rw [hgoal 1]; simpa using h1
  · rw [hgoal 2]; simpa using h2

end Work.ZeroFreeTables.P9
