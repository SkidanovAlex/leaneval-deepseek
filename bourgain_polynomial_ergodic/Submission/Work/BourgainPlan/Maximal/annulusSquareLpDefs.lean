import Mathlib
import Submission.Work.BourgainPlan.Maximal.annulusSqfunDefs
import Submission.Work.BourgainPlan.Maximal.annulusSymbolSum_mikhlin
import Submission.Work.BourgainPlan.Maximal.czBad_lintegral_compl_czStar_le

/-!
# The `L^p` bound of the annulus square function: the reduction to finite index sets

This module contains the measure-theoretic skeleton of the `L^p` bound of the annulus square
function

  `annulusSqfun b j f x = (∑'_n ‖(K_{j+n} * f)(x)‖²)^{1/2}`,   `K_m = 𝓕⁻ (b m)`,

for `1 < p < ∞`, uniformly in the base scale `j ∈ ℤ`:

* `annulusISup_rpow_eq` — the (order-)continuity of `x ↦ x ^ p` on `ℝ≥0∞` for `p > 0` against arbitrary
  suprema, `(⨆ i, s i) ^ p = ⨆ i, (s i) ^ p`;
* `AnnulusSquareLp p b` — the predicate "the square function is bounded on `L^p` with a constant
  uniform in `j`";
* **`annulusSquareLp_of_finset`** — the reduction of the full bound to its *finite index set*
  form: it suffices to know the bound for `(∑_{n ∈ F} ‖(K_{j+n} * f)(x)‖²)^{p/2}` for every finite
  `F ⊆ ℤ`.  The passage to the full two-sided sum `∑'_n` is a monotone-convergence argument along
  the exhaustion `F_N = [-N, N]`.

The finite-`F` bound itself is proved (in the `1 < p < ∞` range) in `annulusSquareLp` by
Khintchine's inequality plus the Mikhlin multiplier bound for the signed symbol sums
`annulusSymbolSum b j F ε`; this module isolates the part of that argument which is independent of
the symbol family.
-/

open MeasureTheory
open scoped BigOperators ENNReal

namespace Work.BourgainPlan.Maximal

/-- **The `p`-th power commutes with suprema in `ℝ≥0∞`** for a positive exponent:
`(⨆ i, s i) ^ p = ⨆ i, (s i) ^ p`. -/
lemma annulusISup_rpow_eq {ι : Type*} {s : ι → ℝ≥0∞} {p : ℝ} (hp : 0 < p) :
    (⨆ i, s i) ^ p = ⨆ i, (s i) ^ p := by
  have hpp : (1 / p) * p = 1 := by
    rw [one_div, inv_mul_cancel₀ (ne_of_gt hp)]
  refine le_antisymm ?_ ?_
  · have hT : (⨆ i, (s i) ^ p) = ((⨆ i, (s i) ^ p) ^ (1 / p)) ^ p := by
      rw [← ENNReal.rpow_mul, hpp, ENNReal.rpow_one]
    rw [hT, ENNReal.rpow_le_rpow_iff hp]
    refine iSup_le fun i => ?_
    rw [← ENNReal.rpow_le_rpow_iff hp, ← ENNReal.rpow_mul, hpp, ENNReal.rpow_one]
    exact le_iSup (fun i => (s i) ^ p) i
  · refine iSup_le fun i => ENNReal.rpow_le_rpow (le_iSup s i) hp.le

/-- **The `p`-th power of the `eLpNorm` is the `∫⁻ ‖·‖ₑ ^ p`.** -/
lemma annulusELpNorm_rpow_eq_lintegral {p : ℝ} (hp : 0 < p) {g : ℝ → ℂ}
    (hg : AEStronglyMeasurable g (volume : Measure ℝ)) :
    (MeasureTheory.eLpNorm g (ENNReal.ofReal p) (volume : Measure ℝ)) ^ p
      = ∫⁻ x, ‖g x‖ₑ ^ p := by
  rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal
    (ENNReal.ofReal_ne_zero_iff.mpr hp) ENNReal.ofReal_ne_top hg, ENNReal.toReal_ofReal hp.le]
  rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ (ne_of_gt hp), ENNReal.rpow_one]

/-- **The `L^p` bound of the annulus square function**, with a constant uniform in the base scale
`j` and in the (finitely supported, but not assumed so) input `f ∈ L^p`. -/
def AnnulusSquareLp (p : ℝ) (b : ℤ → ℝ → ℂ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (j : ℤ) (f : ℝ → ℂ), MemLp f (ENNReal.ofReal p) volume →
    ∫⁻ x, (annulusSqfun b j f x) ^ p ≤ ENNReal.ofReal C * ∫⁻ x, ‖f x‖ₑ ^ p

/-- A finite set of integers is contained in a symmetric interval `[-N, N]`. -/
lemma exists_Icc_subset_finset (F : Finset ℤ) : ∃ N : ℕ, F ⊆ Finset.Icc (-(N : ℤ)) (N : ℤ) := by
  refine ⟨F.sum fun n => n.natAbs, fun n hn => ?_⟩
  have hle : n.natAbs ≤ F.sum fun m => m.natAbs :=
    Finset.single_le_sum (fun m _ => Nat.zero_le _) hn
  have habs : |n| ≤ ((F.sum fun m => m.natAbs : ℕ) : ℤ) := by
    rw [Int.abs_eq_natAbs]
    exact_mod_cast hle
  rw [Finset.mem_Icc]
  refine ⟨?_, ?_⟩
  · have h1 := neg_abs_le n
    linarith
  · have h1 := le_abs_self n
    linarith

/-- **The reduction to finite index sets.**  If the square-function bound holds for every finite
`F ⊆ ℤ` (with the constant `C`), then it holds for the full two-sided sum, i.e. for
`annulusSqfun`. -/
theorem annulusSquareLp_of_finset {p : ℝ} (hp : 0 < p) {b : ℤ → ℝ → ℂ} {C : ℝ}
    (hfin : ∀ (j : ℤ) (F : Finset ℤ) (f : ℝ → ℂ), MemLp f (ENNReal.ofReal p) volume →
      ∫⁻ x, (∑ n ∈ F, ‖annulusConv b (j + n) f x‖ₑ ^ (2 : ℝ)) ^ (p / 2)
        ≤ ENNReal.ofReal C * ∫⁻ x, ‖f x‖ₑ ^ p)
    (j : ℤ) (f : ℝ → ℂ) (hf : MemLp f (ENNReal.ofReal p) volume) :
    ∫⁻ x, (annulusSqfun b j f x) ^ p ≤ ENNReal.ofReal C * ∫⁻ x, ‖f x‖ₑ ^ p := by
  classical
  set g : ℤ → ℝ → ℝ≥0∞ := fun n x => ‖annulusConv b (j + n) f x‖ₑ ^ (2 : ℝ) with hgdef
  set S : ℕ → ℝ → ℝ≥0∞ := fun N x => ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), g n x with hSdef
  have htsum : ∀ x : ℝ, (∑' n : ℤ, g n x) = ⨆ N : ℕ, S N x := by
    intro x
    rw [ENNReal.tsum_eq_iSup_sum]
    refine le_antisymm ?_ ?_
    · refine iSup_le fun F => ?_
      obtain ⟨N, hN⟩ := exists_Icc_subset_finset F
      refine le_trans ?_ (le_iSup (fun N => S N x) N)
      exact Finset.sum_le_sum_of_subset_of_nonneg hN (fun _ _ _ => bot_le)
    · refine iSup_le fun N => ?_
      exact le_iSup (fun F : Finset ℤ => ∑ n ∈ F, g n x) (Finset.Icc (-(N : ℤ)) (N : ℤ))
  have hpt : ∀ x : ℝ, (annulusSqfun b j f x) ^ p = ⨆ N : ℕ, (S N x) ^ (p / 2) := by
    intro x
    rw [annulusSqfun, ← ENNReal.rpow_mul, show (1 : ℝ) / 2 * p = p / 2 by ring, htsum x,
      annulusISup_rpow_eq (by positivity : (0 : ℝ) < p / 2)]
  have hmeas : ∀ N : ℕ, AEMeasurable (fun x : ℝ => (S N x) ^ (p / 2)) volume := by
    intro N
    have hsum : AEMeasurable (fun x : ℝ => S N x) volume := by
      rw [hSdef]
      refine Finset.aemeasurable_fun_sum _ (fun n hn => ?_)
      rw [hgdef]
      exact ((aemeasurable_annulusConv b (j + n) hf.aestronglyMeasurable.aemeasurable
        (aemeasurable_annulusK b (j + n))).enorm).pow_const (2 : ℝ)
    exact ENNReal.continuous_rpow_const.measurable.comp_aemeasurable hsum
  have hmono : ∀ᵐ x ∂(volume : Measure ℝ), Monotone fun N : ℕ => (S N x) ^ (p / 2) := by
    filter_upwards with x
    intro N M hNM
    refine ENNReal.rpow_le_rpow (Finset.sum_le_sum_of_subset_of_nonneg ?_
      (fun _ _ _ => bot_le)) (by positivity)
    intro n hn
    simp only [Finset.mem_Icc] at hn ⊢
    omega
  calc ∫⁻ x, (annulusSqfun b j f x) ^ p
      = ∫⁻ x, ⨆ N : ℕ, (S N x) ^ (p / 2) := lintegral_congr hpt
    _ = ⨆ N : ℕ, ∫⁻ x, (S N x) ^ (p / 2) := MeasureTheory.lintegral_iSup' hmeas hmono
    _ ≤ ENNReal.ofReal C * ∫⁻ x, ‖f x‖ₑ ^ p :=
        iSup_le fun N => hfin j (Finset.Icc (-(N : ℤ)) (N : ℤ)) f hf

end Work.BourgainPlan.Maximal
