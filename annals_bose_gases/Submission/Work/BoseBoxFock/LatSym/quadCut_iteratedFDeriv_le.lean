import Mathlib.Tactic.Have
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Submission.Work.BoseBoxFock.LatSym.quadCutDefs
import Submission.Work.BoseFixB1S.kineticCrux.chiScale_iteratedFDeriv_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock.LatSym

open scoped ContDiff

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The reference bump `quadBump : E3 → ℝ` has uniformly bounded iterated derivatives:
continuity (`ContDiff.continuous_iteratedFDeriv`) plus compact support
(`ContDiffBump.hasCompactSupport`, `HasCompactSupport.iteratedFDeriv`). -/
lemma exists_quadBump_iteratedFDeriv_bound :
    ∃ M : ℕ → ℝ, (∀ k, 0 ≤ M k) ∧
      ∀ (k : ℕ) (y : E3),
        ‖iteratedFDeriv ℝ k (fun y : E3 => quadBump y) y‖ ≤ M k := by
  have h : ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ y : E3, ‖iteratedFDeriv ℝ k (fun y : E3 => quadBump y) y‖ ≤ C := by
    intro k
    have hcs : HasCompactSupport (iteratedFDeriv ℝ k (fun y : E3 => quadBump y)) :=
      quadBump.hasCompactSupport.iteratedFDeriv k
    have hcont : Continuous (iteratedFDeriv ℝ k (fun y : E3 => quadBump y)) :=
      quadBump.contDiff.continuous_iteratedFDeriv (mod_cast le_top)
    obtain ⟨C, hC⟩ := hcs.exists_bound_of_continuous hcont
    exact ⟨max C 0, le_max_right C 0, fun y => (hC y).trans (le_max_left C 0)⟩
  choose M hM0 hMbd using h
  exact ⟨M, hM0, hMbd⟩

/-- The real-valued truncation `quadCutR n p = quadBump (((n:ℝ)+1)⁻¹ • p)` has `k`-th iterated
derivative bounded by the `k`-th bound for `quadBump`, uniformly in `n` and `p`. -/
lemma quadCutR_iteratedFDeriv_le {M : ℕ → ℝ} (hM0 : ∀ k, 0 ≤ M k)
    (hMbd : ∀ (k : ℕ) (y : E3),
      ‖iteratedFDeriv ℝ k (fun y : E3 => quadBump y) y‖ ≤ M k)
    (k n : ℕ) (p : E3) :
    ‖iteratedFDeriv ℝ k (quadCutR n) p‖ ≤ M k := by
  have hcd : ContDiff ℝ ∞ (fun y : E3 => quadBump y) := quadBump.contDiff
  have hc1 : ‖((n : ℝ) + 1)⁻¹‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
    refine inv_le_one_of_one_le₀ ?_
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hpow : ‖((n : ℝ) + 1)⁻¹‖ ^ k ≤ 1 := pow_le_one₀ (norm_nonneg _) hc1
  change ‖iteratedFDeriv ℝ k (fun z : E3 => (fun y : E3 => quadBump y) (((n : ℝ) + 1)⁻¹ • z)) p‖
    ≤ M k
  calc ‖iteratedFDeriv ℝ k
        (fun z : E3 => (fun y : E3 => quadBump y) (((n : ℝ) + 1)⁻¹ • z)) p‖
      ≤ ‖iteratedFDeriv ℝ k (fun y : E3 => quadBump y) (((n : ℝ) + 1)⁻¹ • p)‖
          * ‖((n : ℝ) + 1)⁻¹‖ ^ k :=
        Work.BoseFixB1S.kineticCrux.norm_iteratedFDeriv_comp_smul_le hcd _ k p
    _ ≤ M k * ‖((n : ℝ) + 1)⁻¹‖ ^ k :=
        mul_le_mul_of_nonneg_right (hMbd k _) (pow_nonneg (norm_nonneg _) k)
    _ ≤ M k * 1 := mul_le_mul_of_nonneg_left hpow (hM0 k)
    _ = M k := mul_one _

/-- The canonical embedding `ℂ.ofReal : ℝ → ℂ` has operator norm `≤ 1`. -/
lemma norm_ofRealCLM_le_one_quadCut : ‖(Complex.ofRealCLM : ℝ →L[ℝ] ℂ)‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun r => ?_)
  rw [one_mul, Complex.ofRealCLM_apply]
  exact le_of_eq (RCLike.norm_ofReal (K := ℂ) r)

/-- Composing a real-valued function with the isometric embedding `ℝ ↪ ℂ` does not increase the
norm of any iterated derivative. -/
lemma norm_iteratedFDeriv_complex_ofReal_le_quadCut {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (j : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ j (fun z : E => (f z : ℂ)) x‖ ≤ ‖iteratedFDeriv ℝ j f x‖ := by
  have hfun : (Complex.ofRealCLM ∘ f) = (fun z : E => (f z : ℂ)) := by
    funext z
    simp only [Function.comp_apply, Complex.ofRealCLM_apply]
  have h := ContinuousLinearMap.norm_iteratedFDeriv_comp_left (𝕜 := ℝ)
    (Complex.ofRealCLM : ℝ →L[ℝ] ℂ) (f := f) (x := x) (N := ∞) (n := j)
    hf.contDiffAt (mod_cast le_top)
  rw [hfun] at h
  calc ‖iteratedFDeriv ℝ j (fun z : E => (f z : ℂ)) x‖
      = ‖iteratedFDeriv ℝ j (Complex.ofRealCLM ∘ f) x‖ := by rw [hfun]
    _ ≤ ‖(Complex.ofRealCLM : ℝ →L[ℝ] ℂ)‖ * ‖iteratedFDeriv ℝ j f x‖ := h
    _ ≤ 1 * ‖iteratedFDeriv ℝ j f x‖ :=
        mul_le_mul_of_nonneg_right norm_ofRealCLM_le_one_quadCut (norm_nonneg _)
    _ = ‖iteratedFDeriv ℝ j f x‖ := one_mul _

/-- **Uniform bounds on the iterated derivatives of the truncating bumps `quadCut n`.**

`Work.BoseBoxFock.LatSym.quadCut n p = quadBump ((n+1)⁻¹ • p)` is `1` on `closedBall 0 (n+1)` and
`0` outside `closedBall 0 (2(n+1))`; in particular it is smooth with compact support.  The claim
below records that there is a *single* sequence of constants `M k`, independent of `n` and of `p`,
bounding the `k`-th iterated derivative of `quadCut n` everywhere.

Route: `‖D^k (quadBump (c • ·)) p‖ ≤ ‖D^k quadBump (c • p)‖ * ‖c‖^k` for `c = ((n:ℝ)+1)⁻¹`
(`Work.BoseFixB1S.kineticCrux.norm_iteratedFDeriv_comp_smul_le`), and `‖c‖ ≤ 1` for `n ≥ 0`; a bound
on `‖D^k quadBump y‖` uniform in `y` is continuity plus compact support
(`HasCompactSupport.exists_bound_of_continuous` with `ContDiffBump.hasCompactSupport` and
`ContDiff.continuous_iteratedFDeriv`).  Finally pass from the real-valued `quadCutR n` to the
`ℂ`-valued `quadCut n = fun p => ((quadCutR n p : ℝ) : ℂ)`: `iteratedFDeriv ℝ k (quadCut n) p` is
`Complex.ofRealCLM ∘ quadCutR n` with `compContinuousLinearMap` inserted
(`ContinuousLinearMap.iteratedFDeriv_comp_left`), and `‖Complex.ofRealCLM‖ ≤ 1` (show it by
`ContinuousLinearMap.opNorm_le_bound` and `‖(r:ℂ)‖ = |r|` for real `r`), so the complex norms are
bounded by the real ones.  `k` is arbitrary (no truncation needed). -/
theorem quadCut_iteratedFDeriv_le :
    ∃ M : ℕ → ℝ, (∀ k, 0 ≤ M k) ∧
      ∀ (k n : ℕ) (p : EuclideanSpace ℝ (Fin 3)),
        ‖iteratedFDeriv ℝ k (Work.BoseBoxFock.LatSym.quadCut n) p‖ ≤ M k := by
  obtain ⟨Mb, hMb0, hMb⟩ := exists_quadBump_iteratedFDeriv_bound
  refine ⟨Mb, hMb0, ?_⟩
  intro k n p
  have hcd : ContDiff ℝ ∞ (quadCutR n) :=
    quadBump.contDiff.comp (contDiff_id.const_smul (((n : ℝ) + 1)⁻¹))
  have h := norm_iteratedFDeriv_complex_ofReal_le_quadCut (f := quadCutR n) hcd k p
  have hfun : (fun z : E3 => (quadCutR n z : ℂ)) = quadCut n := by
    funext z
    rw [quadCut_apply]
  rw [hfun] at h
  exact h.trans (quadCutR_iteratedFDeriv_le hMb0 hMb k n p)

end Work.BoseBoxFock.LatSym
