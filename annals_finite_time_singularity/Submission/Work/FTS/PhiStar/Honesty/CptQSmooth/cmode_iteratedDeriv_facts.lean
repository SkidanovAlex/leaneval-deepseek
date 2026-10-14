import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.PhiStar.Gegenbauer.FamNormValue
import Submission.Work.FTS.PhiStar.Honesty.CptQSmooth.pzIter_smoothCptQ
import Submission.Work.FTS.PhiStar.Honesty.cmode_decay_of_cptQ
import Submission.Work.FTS.PhiStar.Series.eFam_sup_le
import Submission.Work.FTS.StrongPersist.hasDerivAt_wip_family
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.PhiStar.Honesty.sqrt_weight_mul_eq_of_mem_Ioo
import Submission.Work.Spaces.SmoothCompact_HkMem

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `cmode_iteratedDeriv_facts` — the `z`-regularity and rapid decay of `z ↦ cmode m G z`

For a source `G` which is `C^∞` on `ℝ²` and compactly supported in the *open* quadrant
(`Work.FTS.PhiStar.Honesty.SmoothCptQ G`), the mode coefficients

  `cmode m G z = (∫_θ G z θ · e_m θ · cos θ dθ) / (∫_θ e_m θ² cos θ dθ)`

are `C^∞` functions of `z` whose `j`-th derivative decays faster than any power of `(m+1)`,
*uniformly in* `z`:

  `∀ j N, (∀ m t, 0 < t → HasDerivAt (iteratedDeriv j (cmode m G)) (iteratedDeriv (j+1) …) t)`
  `        ∧ ∃ C ≥ 0, ∀ m t, |iteratedDeriv j (cmode m G) t| ≤ C / (m+1)^N`.

## Route

* **Differentiating under the integral.**  `Work.FTS.PhiStar.Honesty.CptQSmooth.cmode_hasDerivAt_pz`
  gives `HasDerivAt (fun z => cmode m F z) (cmode m (∂_z F) z) z` for every jointly `C^∞` `F`;
  the induction of `cmodeFact_iteratedDeriv_eq` then identifies the `j`-th iterated derivative
  of `z ↦ cmode m G z` with `z ↦ cmode m (∂_z^j G) z`:

    `iteratedDeriv j (fun t => cmode m G t) t = cmode m (pzIter j G) t`.

* **Rapid decay.**  `∂_z^j G` is again a `C^∞` source compactly supported in the same box
  (`pzIter_smoothCptQ`), so `cmode_decay_of_cptQ` applies to it and yields the `(m+1)^{-N}`
  decay for `m ≥ 1`; the case `m = 0` (where the eigenvalue `lam 0 = 0` is unavailable and the
  bound degenerates to a mere constant) is
  `Work.FTS.PhiStar.Honesty.CmodeZero.cmode_zero_abs_le_of_cptQ`.

Note that `j = 0`, `m = 0` is a genuine case: the first conjunct then only asks for the
differentiability of `z ↦ cmode 0 G z`, and the second one for its boundedness.
-/

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty.CptQSmooth

set_option autoImplicit false

/-! ## 1. The iterated `z`-derivatives of a jointly smooth function -/

/-- Every `z`-partial derivative of a jointly `C^∞` function on `ℝ²` is jointly `C^∞`. -/
theorem cmodeFact_pzIter_contDiff {G : ℝ → ℝ → ℝ}
    (hG : ∀ n : ℕ, ContDiff ℝ n (Function.uncurry G)) (j : ℕ) :
    ∀ n : ℕ, ContDiff ℝ n (Function.uncurry (Work.Spaces.pzIter j G)) := by
  intro n
  induction j generalizing n with
  | zero => simpa using hG n
  | succ j ih =>
      have h1 : ContDiffOn ℝ (n + 1) (Function.uncurry (Work.Spaces.pzIter j G)) Set.univ :=
        contDiffOn_univ.mpr (ih (n + 1))
      have h2 := (Work.FTS.PhiStar.Honesty.currySmooth_fin_end isOpen_univ (n := n) h1).1
      rw [show Work.Spaces.pz (Work.Spaces.pzIter j G) = Work.Spaces.pzIter (j + 1) G from
        (Work.Spaces.pzIter_succ j G).symm] at h2
      exact contDiffOn_univ.mp h2

/-! ## 2. The iterated derivatives of `z ↦ cmode m G z` -/

/-- **The `j`-th `z`-derivative of a mode coefficient is the mode coefficient of the `j`-th
`z`-derivative**: `iteratedDeriv j (z ↦ cmode m G z) t = cmode m (pzIter j G) t`. -/
theorem cmodeFact_iteratedDeriv_eq {G : ℝ → ℝ → ℝ}
    (hG : ∀ n : ℕ, ContDiff ℝ n (Function.uncurry G)) (m j : ℕ) (t : ℝ) :
    iteratedDeriv j (fun t' => Work.FTS.PhiStar.Series.cmode m G t') t
      = Work.FTS.PhiStar.Series.cmode m (Work.Spaces.pzIter j G) t := by
  induction j generalizing t with
  | zero => simp
  | succ j ih =>
      rw [iteratedDeriv_succ]
      have hfun : iteratedDeriv j (fun t' => Work.FTS.PhiStar.Series.cmode m G t')
          = fun s => Work.FTS.PhiStar.Series.cmode m (Work.Spaces.pzIter j G) s :=
        funext (fun s => ih s)
      rw [hfun]
      rw [(cmode_hasDerivAt_pz (cmodeFact_pzIter_contDiff hG j) m t).deriv]
      rw [Work.Spaces.pzIter_succ]

/-- The differentiability assertion of the target, stated for a jointly smooth source. -/
theorem cmodeFact_iteratedDeriv_hasDerivAt {G : ℝ → ℝ → ℝ}
    (hG : ∀ n : ℕ, ContDiff ℝ n (Function.uncurry G)) (m j : ℕ) (t : ℝ) :
    HasDerivAt (fun t' =>
        iteratedDeriv j (fun t'' => Work.FTS.PhiStar.Series.cmode m G t'') t')
      (iteratedDeriv (j + 1) (fun t'' => Work.FTS.PhiStar.Series.cmode m G t'') t) t := by
  have hfun : (fun t' : ℝ =>
        iteratedDeriv j (fun t'' => Work.FTS.PhiStar.Series.cmode m G t'') t')
      = fun t' => Work.FTS.PhiStar.Series.cmode m (Work.Spaces.pzIter j G) t' :=
    funext (fun s => cmodeFact_iteratedDeriv_eq hG m j s)
  have hval : iteratedDeriv (j + 1) (fun t'' => Work.FTS.PhiStar.Series.cmode m G t'') t
      = Work.FTS.PhiStar.Series.cmode m (Work.Spaces.pzIter (j + 1) G) t :=
    cmodeFact_iteratedDeriv_eq hG m (j + 1) t
  rw [hfun, hval]
  exact cmode_hasDerivAt_pz (cmodeFact_pzIter_contDiff hG j) m t

/-! ## 3. The target -/

theorem cmode_iteratedDeriv_facts {G : ℝ → ℝ → ℝ} (hG : Work.FTS.PhiStar.Honesty.SmoothCptQ G) (j N : ℕ) :
    (∀ (m : ℕ) (t : ℝ), 0 < t →
      HasDerivAt (fun t' => iteratedDeriv j (fun t'' => Work.FTS.PhiStar.Series.cmode m G t'') t')
        (iteratedDeriv (j + 1) (fun t'' => Work.FTS.PhiStar.Series.cmode m G t'') t) t)
    ∧ (∃ C : ℝ, 0 ≤ C ∧ ∀ (m : ℕ) (t : ℝ),
        |iteratedDeriv j (fun t' => Work.FTS.PhiStar.Series.cmode m G t') t| ≤ C / ((m : ℝ) + 1) ^ N) := by
  constructor
  · intro m t _
    exact cmodeFact_iteratedDeriv_hasDerivAt hG.smooth m j t
  · obtain ⟨C₁, hC₁, hdec⟩ :=
      Work.FTS.PhiStar.Honesty.cmode_decay_of_cptQ (pzIter_smoothCptQ hG j) 0 N
    obtain ⟨C₀, hC₀, hzero⟩ :=
      Work.FTS.PhiStar.Honesty.CmodeZero.cmode_zero_abs_le_of_cptQ (pzIter_smoothCptQ hG j)
    refine ⟨max C₁ C₀, le_max_of_le_left hC₁, ?_⟩
    intro m t
    rw [cmodeFact_iteratedDeriv_eq hG.smooth m j t]
    rcases Nat.eq_zero_or_pos m with hm | hm
    · rw [hm]
      simp only [Nat.cast_zero, zero_add, one_pow, div_one]
      exact le_trans (hzero t) (le_max_right C₁ C₀)
    · have hb : |Work.FTS.PhiStar.Series.cmode m (Work.Spaces.pzIter j G) t|
          ≤ C₁ / ((m : ℝ) + 1) ^ N := by
        simpa using hdec m hm t
      exact le_trans hb (div_le_div_of_nonneg_right (le_max_left C₁ C₀) (by positivity))

end Work.FTS.PhiStar.Honesty.CptQSmooth
