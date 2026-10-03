import Mathlib
import Submission.Work.KMTContract.Defs

/-!
# The cutoff `η = kmtEta`: `C²`-bounds and vanishing of the first two derivatives off `[-1,1]`

`Work.KMTContract.kmtEta` is the paper's cutoff `η`: the smooth bump of `ContDiffBump 0` with
`rIn = 1/2`, `rOut = 1`, viewed as a complex-valued function.  This file collects the analytic
facts about it that the §6/§7 estimates consume:

* `η` is `C²` (indeed `C^∞`), so all three of `η`, `η'`, `η''` are bounded on the compact set
  `[-1,1]` — the constants `M₀, M₁, M₂` of the statement;
* `η` and its first two derivatives vanish for `|y| ≥ 1` (so `η` is supported in `[-1,1]`);
* `η` and `η'` are everywhere differentiable with derivatives `η'` and `η''`.

The vanishing of `η'` and `η''` at the *boundary* points `y = ±1` (where the support of `η` is
merely closed, so neither `deriv_of_notMem_tsupport` nor eventual equality in a full neighbourhood
applies) is handled by the one-sided argument `HasDerivWithinAt.deriv_eq_zero` applied to
`Set.Ici y` (for `y ≥ 1`) and `Set.Iic y` (for `y ≤ -1`): `η` (resp. `η'`) vanishes on the halfline
on the side of `y` where it is nonzero, and a differentiable function vanishing on a halfline
starting at `y` has derivative `0` there.
-/

namespace Work.KMTAreas.A7

open Work.KMTContract

/-- A function `f : ℝ → ℂ` which vanishes on the halfline `[1, ∞)` *and* on `(-∞, -1]` has
`deriv f y = 0` for every `|y| ≥ 1`.  (Choosing the halfline on the appropriate side of `y` and
using `HasDerivWithinAt.deriv_eq_zero` avoids any differentiability hypothesis.) -/
private lemma deriv_eq_zero_of_one_le_abs {f : ℝ → ℂ} (h : ∀ z : ℝ, 1 ≤ |z| → f z = 0) :
    ∀ y : ℝ, 1 ≤ |y| → deriv f y = 0 := by
  intro y hy
  rcases le_or_gt 0 y with hy0 | hy0
  · have hy1 : (1 : ℝ) ≤ y := by rwa [abs_of_nonneg hy0] at hy
    refine HasDerivWithinAt.deriv_eq_zero ?_ (uniqueDiffWithinAt_Ici y)
    refine (hasDerivWithinAt_const y (Set.Ici y) (0 : ℂ)).congr (fun z hz => ?_) (h y hy)
    have hzy : y ≤ z := hz
    exact h z (by rw [abs_of_nonneg (by linarith)]; linarith)
  · have hy1 : y ≤ -1 := by
      have hy' : |y| = -y := abs_of_neg hy0
      linarith
    refine HasDerivWithinAt.deriv_eq_zero ?_ (uniqueDiffWithinAt_Iic y)
    refine (hasDerivWithinAt_const y (Set.Iic y) (0 : ℂ)).congr (fun z hz => ?_) (h y hy)
    have hzy : z ≤ y := hz
    exact h z (by rw [abs_of_nonpos (by linarith)]; linarith)

/-- `η' = 0` off `[-1,1]`. -/
private lemma kmtEta_deriv_eq_zero : ∀ y : ℝ, 1 ≤ |y| → deriv kmtEta y = 0 :=
  deriv_eq_zero_of_one_le_abs (fun _ hz => kmtEta_zero hz)

/-- `η'' = deriv η'`, applied twice. -/
private lemma iteratedDeriv_two_kmtEta : iteratedDeriv 2 kmtEta = deriv (deriv kmtEta) := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]

/-- `η'' = 0` off `[-1,1]`. -/
private lemma kmtEta_iteratedDeriv_two_eq_zero :
    ∀ y : ℝ, 1 ≤ |y| → iteratedDeriv 2 kmtEta y = 0 := by
  intro y hy
  rw [iteratedDeriv_two_kmtEta]
  exact deriv_eq_zero_of_one_le_abs (fun _ hz => kmtEta_deriv_eq_zero _ hz) y hy

/-- **`η = kmtEta` is `C²`, bounded with its first two derivatives on `[-1,1]`, and vanishes
with its first two derivatives off `[-1,1]`.** -/
theorem kmtEta_deriv_bounds : ∃ (M0 M1 M2 : ℝ), 0 ≤ M0 ∧ 0 ≤ M1 ∧ 0 ≤ M2 ∧
      ContDiff ℝ 2 Work.KMTContract.kmtEta ∧
      (∀ y : ℝ, |y| ≤ 1 → ‖Work.KMTContract.kmtEta y‖ ≤ M0) ∧
      (∀ y : ℝ, |y| ≤ 1 → ‖deriv Work.KMTContract.kmtEta y‖ ≤ M1) ∧
      (∀ y : ℝ, |y| ≤ 1 → ‖iteratedDeriv 2 Work.KMTContract.kmtEta y‖ ≤ M2) ∧
      (∀ y : ℝ, 1 ≤ |y| → Work.KMTContract.kmtEta y = 0) ∧
      (∀ y : ℝ, 1 ≤ |y| → deriv Work.KMTContract.kmtEta y = 0) ∧
      (∀ y : ℝ, 1 ≤ |y| → iteratedDeriv 2 Work.KMTContract.kmtEta y = 0) ∧
      (∀ y : ℝ, HasDerivAt Work.KMTContract.kmtEta (deriv Work.KMTContract.kmtEta y) y) ∧
      (∀ y : ℝ, HasDerivAt (deriv Work.KMTContract.kmtEta) (iteratedDeriv 2 Work.KMTContract.kmtEta y) y) := by
  -- `η` is `C^∞` (a smooth bump composed with the inclusion `ℝ ↪ ℂ`), hence `C²`.
  have hcd : ContDiff ℝ 2 kmtEta := by
    have h : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) kmtEta := by
      have h2 := (ContinuousLinearMap.contDiff Complex.ofRealCLM (n := (⊤ : ℕ∞))).comp
        (ContDiffBump.contDiff kmtBump (n := ⊤))
      show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) _
      exact h2
    exact h.of_le (WithTop.coe_le_coe.mpr le_top)
  -- the first two derivatives are continuous, hence bounded on the compact set `[-1,1]`
  have hcont1 : Continuous (deriv kmtEta) := hcd.continuous_deriv (by norm_num)
  have hcont2 : Continuous (iteratedDeriv 2 kmtEta) :=
    hcd.continuous_iteratedDeriv 2 (by norm_num)
  obtain ⟨C1, hC1⟩ :=
    isCompact_Icc.exists_bound_of_continuousOn (s := Set.Icc (-1 : ℝ) 1) hcont1.continuousOn
  obtain ⟨C2, hC2⟩ :=
    isCompact_Icc.exists_bound_of_continuousOn (s := Set.Icc (-1 : ℝ) 1) hcont2.continuousOn
  -- differentiability of `η` and of `η'`
  have hdiff : Differentiable ℝ kmtEta := hcd.differentiable (by norm_num)
  have hdiff_deriv : Differentiable ℝ (deriv kmtEta) := by
    simpa [iteratedDeriv_one] using hcd.differentiable_iteratedDeriv 1 (by norm_num)
  refine ⟨1, max C1 0, max C2 0, zero_le_one, le_max_right _ _, le_max_right _ _, hcd,
    fun y _ => norm_kmtEta_le y, ?_, ?_, fun y hy => kmtEta_zero hy, kmtEta_deriv_eq_zero,
    kmtEta_iteratedDeriv_two_eq_zero,
    fun y => (hdiff.differentiableAt (x := y)).hasDerivAt, fun y => ?_⟩
  · intro y hy
    exact le_trans (hC1 y (Set.mem_Icc.mpr (abs_le.mp hy))) (le_max_left _ _)
  · intro y hy
    exact le_trans (hC2 y (Set.mem_Icc.mpr (abs_le.mp hy))) (le_max_left _ _)
  · rw [iteratedDeriv_two_kmtEta]
    exact (hdiff_deriv.differentiableAt (x := y)).hasDerivAt

end Work.KMTAreas.A7
