/-
# `Work.ZeroFreeTables.P9.zetaExtPoleLemmas`

The analytic inputs for `zetaCorrector_three_bounds`:

* `logDeriv_iteratedDeriv_re_bdd` — a general fact: on a compact set `K` contained in an open set `U`
  on which `f` is analytic and nonzero, the real parts of `logDeriv f` and of its first two
  derivatives are bounded by a single positive constant.  (They are analytic on `U` — the two
  higher ones because `AnalyticOnNhd.deriv` preserves analyticity — hence continuous, and a
  continuous real function on a compact set is bounded.)
* `zetaExtPole_ne_zero` — the extension `z ↦ (z-1)ζ(z)` of `ζ` is nonzero on the closed rectangle
  `{1 ≤ Re s ≤ 2, |Im s| ≤ 5}`, because the only possible zeros are those of `ζ` (none for
  `Re s ≥ 1`) and the point `s = 1`, where the extension takes the value `1`.
* `logDeriv_zetaExtPole_eq` — the pole splitting `logDeriv φ = 1/(s-1) + ζ'/ζ` for `Re s > 1`.
* `zetaExtU` — the open set `{z ≠ 0, φ z ≠ 0}` on which `logDeriv φ` is analytic, together with the
  fact that the rectangle sits inside it.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.P9.zetaExtPoleDefs

open Complex Set Filter
open scoped Topology

noncomputable section

namespace Work.ZeroFreeTables.P9

/-- On a compact set contained in an open set on which `f` is analytic and nowhere zero, the real
parts of the logarithmic derivative of `f` and of its first two derivatives are bounded by one
positive constant. -/
theorem logDeriv_iteratedDeriv_re_bdd (f : ℂ → ℂ) (U K : Set ℂ) (hU : IsOpen U) (hK : IsCompact K)
    (hKU : K ⊆ U) (hf : AnalyticOnNhd ℂ f U) (hne : ∀ z ∈ U, f z ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ z ∈ K, |(logDeriv f z).re| ≤ C ∧
      |(iteratedDeriv 1 (logDeriv f) z).re| ≤ C ∧
      |(iteratedDeriv 2 (logDeriv f) z).re| ≤ C := by
  have hlog : AnalyticOnNhd ℂ (logDeriv f) U := by
    have heq : logDeriv f = (fun z : ℂ => deriv f z / f z) := by
      funext z; rw [logDeriv_apply]
    rw [heq]
    exact hf.deriv.div hf hne
  -- the logarithmic derivative and its first two derivatives are analytic on `U`
  have hlog1 : AnalyticOnNhd ℂ (iteratedDeriv 1 (logDeriv f)) U := by
    rw [iteratedDeriv_one]
    exact hlog.deriv
  have hlog2 : AnalyticOnNhd ℂ (iteratedDeriv 2 (logDeriv f)) U := by
    have htwo : iteratedDeriv 2 (logDeriv f) = deriv (iteratedDeriv 1 (logDeriv f)) :=
      iteratedDeriv_succ
    rw [htwo]
    exact hlog1.deriv
  have hc0 : ContinuousOn (fun z : ℂ => |(logDeriv f z).re|) K :=
    _root_.continuous_abs.comp_continuousOn
      (Complex.continuous_re.comp_continuousOn (hlog.continuousOn.mono hKU))
  have hc1 : ContinuousOn (fun z : ℂ => |(iteratedDeriv 1 (logDeriv f) z).re|) K :=
    _root_.continuous_abs.comp_continuousOn
      (Complex.continuous_re.comp_continuousOn (hlog1.continuousOn.mono hKU))
  have hc2 : ContinuousOn (fun z : ℂ => |(iteratedDeriv 2 (logDeriv f) z).re|) K :=
    _root_.continuous_abs.comp_continuousOn
      (Complex.continuous_re.comp_continuousOn (hlog2.continuousOn.mono hKU))
  have hsum : ContinuousOn (fun z : ℂ => |(logDeriv f z).re|
      + |(iteratedDeriv 1 (logDeriv f) z).re| + |(iteratedDeriv 2 (logDeriv f) z).re|) K :=
    (hc0.add hc1).add hc2
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
theorem zetaExtPole_ne_zero (s : ℂ) (h1 : 1 ≤ s.re) (h2 : s.re ≤ 2) (h3 : |s.im| ≤ 5) :
    zetaExtPole s ≠ 0 := by
  rcases eq_or_ne s 1 with h | h
  · subst h
    simp [zetaExtPole, psiExtPole, Gammaℝ_one]
  · rw [zetaExtPole_eq s (by rintro rfl; norm_num at h1) h]
    exact mul_ne_zero (sub_ne_zero.mpr h) (riemannZeta_ne_zero_of_one_le_re h1)

/-- The pole splitting of the logarithmic derivative of the extension: for `Re s > 1` it equals
`1/(s-1) + ζ'/ζ(s)`. -/
theorem logDeriv_zetaExtPole_eq (s : ℂ) (hs : 1 < s.re) :
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
def zetaExtU : Set ℂ := {z : ℂ | z ≠ 0 ∧ zetaExtPole z ≠ 0}

lemma isOpen_zetaExtU : IsOpen zetaExtU := by
  rw [zetaExtU]
  exact analyticOn_zetaExtPole.continuousOn.isOpen_inter_preimage
    isOpen_compl_singleton isOpen_compl_singleton

lemma zetaRect5_subset_zetaExtU : zetaRect5 ⊆ zetaExtU := by
  intro z hz
  have hz' : 1 ≤ z.re ∧ z.re ≤ 2 ∧ |z.im| ≤ 5 := hz
  refine ⟨?_, zetaExtPole_ne_zero z hz'.1 hz'.2.1 hz'.2.2⟩
  intro h0
  have hre : z.re = 0 := by rw [h0]; simp
  linarith [hz'.1]

lemma analyticOn_zetaExtPole_of_U : AnalyticOnNhd ℂ zetaExtPole zetaExtU :=
  analyticOn_zetaExtPole.mono fun _ hz => hz.1

lemma zetaExtPole_ne_zero_on_U : ∀ z ∈ zetaExtU, zetaExtPole z ≠ 0 := fun _ hz => hz.2

end Work.ZeroFreeTables.P9
