/-
Workaround module: copy of `Submission/Work/ZeroFreeTables/lam0w/zetaCorrBounded.lean`.
The original currently does not compile in this workspace (two goals need a `Pi.add_apply`
simp and an `iteratedDeriv 0` rewriting step), and it is a dependency of the `principalBound4`
chain, so a `sorry`-free, compiling copy is kept here.  The three declarations are renamed
with the `_fm` suffix; the mathematical content is identical.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.lam0w.PrincipalDefs
import Submission.Work.ZeroFreeTables.P9.zetaCorrector_three_bounds_proof

open Complex Filter Set
open scoped Topology

namespace Work.ZeroFreeTables.lam0w

/-- A function analytic on an open set `U` is bounded, together with its first two derivatives, on
every compact `K ⊆ U`. -/
lemma analyticOn_bdd_iteratedDeriv_fm (g : ℂ → ℂ) {U K : Set ℂ} (hU : IsOpen U) (hK : IsCompact K)
    (hKU : K ⊆ U) (hg : AnalyticOnNhd ℂ g U) :
    ∃ C : ℝ, 0 < C ∧ ∀ z ∈ K,
      ‖g z‖ ≤ C ∧ ‖iteratedDeriv 1 g z‖ ≤ C ∧ ‖iteratedDeriv 2 g z‖ ≤ C := by
  have hiter1 : AnalyticOnNhd ℂ (iteratedDeriv 1 g) U := by
    rw [iteratedDeriv_one]; exact hg.deriv
  have hiter2 : AnalyticOnNhd ℂ (iteratedDeriv 2 g) U := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]; exact hg.deriv.deriv
  have hcont0 : ContinuousOn (fun z : ℂ => ‖g z‖) K :=
    continuous_norm.comp_continuousOn (hg.continuousOn.mono hKU)
  have hcont1 : ContinuousOn (fun z : ℂ => ‖iteratedDeriv 1 g z‖) K :=
    continuous_norm.comp_continuousOn (hiter1.continuousOn.mono hKU)
  have hcont2 : ContinuousOn (fun z : ℂ => ‖iteratedDeriv 2 g z‖) K :=
    continuous_norm.comp_continuousOn (hiter2.continuousOn.mono hKU)
  obtain ⟨C₀, hC₀⟩ := hK.bddAbove_image ((hcont0.add hcont1).add hcont2)
  refine ⟨|C₀| + 1, by positivity, fun z hz => ?_⟩
  have hle := hC₀ (mem_image_of_mem _ hz)
  have hC : C₀ ≤ |C₀| + 1 := by have := le_abs_self C₀; linarith
  have hle0 : ‖g z‖ ≤ C₀ := by
    have h := hle
    simp only [Pi.add_apply] at h
    linarith [norm_nonneg (iteratedDeriv 1 g z), norm_nonneg (iteratedDeriv 2 g z)]
  have hle1 : ‖iteratedDeriv 1 g z‖ ≤ C₀ := by
    have h := hle
    simp only [Pi.add_apply] at h
    linarith [norm_nonneg (g z), norm_nonneg (iteratedDeriv 2 g z)]
  have hle2 : ‖iteratedDeriv 2 g z‖ ≤ C₀ := by
    have h := hle
    simp only [Pi.add_apply] at h
    linarith [norm_nonneg (g z), norm_nonneg (iteratedDeriv 1 g z)]
  exact ⟨by linarith, by linarith, by linarith⟩

/-- `ζ`'s logarithmic derivative with the pole term removed is `-logDeriv ((z-1)ζ(z))` for
`Re z > 1`. -/
lemma zetaCorr_eventuallyEq_fm (s : ℂ) (hs : 1 < s.re) :
    Work.ZeroFreeTables.lam0w.zetaCorr =ᶠ[𝓝 s]
      (fun z : ℂ => -logDeriv Work.ZeroFreeTables.P9.zetaExtPole z) := by
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with t ht
  rw [zetaCorr, Work.ZeroFreeTables.P9.logDeriv_zetaExtPole_eq' t ht, one_div]
  ring

/-- `zetaCorr = -ζ'/ζ - 1/(z-1)` is bounded, together with its first two derivatives, on the
rectangle `{1 < Re s ≤ 2, |Im s| ≤ 4}`.

Proof strategy (all ingredients are in Mathlib / already-proved workspace files):
* `ζ` is meromorphic with a single simple pole at `1`; putting `φ z = (z-1) * ζ z` (an entire
  function, here realised as `psi z / Gammaℝ z` with `psi z = (z-1)*completedRiemannZeta₀ z -
  (z-1)/z + 1`, exactly as in `Submission/Work/ZeroFreeTables/P9/zetaLogDeriv_pole_split.lean`)
  one has `zetaCorr = -logDeriv φ` on `Re z > 1`.
* `φ ≠ 0` on the closed rectangle `R = {1 ≤ Re ≤ 2, |Im| ≤ 4}`: at `z = 1` use `φ 1 = 1`, and
  otherwise `φ z = (z-1)*ζ z` with `riemannZeta_ne_zero_of_one_le_re`.
* Hence `u := fun z => -deriv φ z / φ z` is analytic at every point of `R`
  (`AnalyticAt.deriv`, `AnalyticAt.div`, `logDeriv_apply`), so `u`, `deriv u`, `deriv (deriv u)`
  are continuous on the compact `R`; bound them with `IsCompact.exists_bound_of_continuousOn`.
* Finally `zetaCorr =ᶠ[𝓝 s] u` for `s` with `1 < s.re`
  (`Filter.EventuallyEq.iteratedDeriv_eq`, `iteratedDeriv_one`), and
  `{1 < s.re ∧ s.re ≤ 2 ∧ |s.im| ≤ 4} ⊆ R`.
Work with `R` (closed) rather than the region itself: the region is not compact and touches
`Re = 1`. -/
theorem zetaCorrBounded_fm :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, 1 < s.re → s.re ≤ 2 → |s.im| ≤ 4 →
      ‖Work.ZeroFreeTables.lam0w.zetaCorr s‖ ≤ C ∧
      ‖iteratedDeriv 1 Work.ZeroFreeTables.lam0w.zetaCorr s‖ ≤ C ∧
      ‖iteratedDeriv 2 Work.ZeroFreeTables.lam0w.zetaCorr s‖ ≤ C := by
  have hlog : AnalyticOnNhd ℂ (logDeriv Work.ZeroFreeTables.P9.zetaExtPole)
      Work.ZeroFreeTables.P9.zetaExtU' := by
    have heq : logDeriv Work.ZeroFreeTables.P9.zetaExtPole
        = fun x => deriv Work.ZeroFreeTables.P9.zetaExtPole x
            / Work.ZeroFreeTables.P9.zetaExtPole x := by
      funext x; rw [logDeriv_apply]
    rw [heq]
    exact Work.ZeroFreeTables.P9.analyticOn_zetaExtPole_of_U'.deriv.div
      Work.ZeroFreeTables.P9.analyticOn_zetaExtPole_of_U'
      Work.ZeroFreeTables.P9.zetaExtPole_ne_zero_on_U'
  obtain ⟨C, hCpos, hCbd⟩ := analyticOn_bdd_iteratedDeriv_fm
    (fun z : ℂ => -logDeriv Work.ZeroFreeTables.P9.zetaExtPole z)
    (U := Work.ZeroFreeTables.P9.zetaExtU') (K := Work.ZeroFreeTables.P9.zetaRect5)
    Work.ZeroFreeTables.P9.isOpen_zetaExtU' Work.ZeroFreeTables.P9.isCompact_zetaRect5
    Work.ZeroFreeTables.P9.zetaRect5_subset_zetaExtU' hlog.neg
  refine ⟨C, hCpos, fun s hs1 hs2 hs3 => ?_⟩
  have hs : s ∈ Work.ZeroFreeTables.P9.zetaRect5 :=
    ⟨le_of_lt hs1, hs2, le_trans hs3 (by norm_num)⟩
  obtain ⟨b0, b1, b2⟩ := hCbd s hs
  have hev := zetaCorr_eventuallyEq_fm s hs1
  refine ⟨?_, ?_, ?_⟩
  · have h0 : Work.ZeroFreeTables.lam0w.zetaCorr s
        = (fun z : ℂ => -logDeriv Work.ZeroFreeTables.P9.zetaExtPole z) s :=
      Filter.EventuallyEq.eq_of_nhds hev
    rw [h0]
    simpa using b0
  · rw [Filter.EventuallyEq.iteratedDeriv_eq 1 hev]; simpa using b1
  · rw [Filter.EventuallyEq.iteratedDeriv_eq 2 hev]; simpa using b2

end Work.ZeroFreeTables.lam0w
