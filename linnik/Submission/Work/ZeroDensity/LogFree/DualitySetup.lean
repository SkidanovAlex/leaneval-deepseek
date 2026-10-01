import Mathlib
import Submission.Work.ZeroDensity.LogFree.RouteDefs
import Submission.Work.ZeroDensity.LogFree.GramProps

/-!
# `Work.ZeroDensity.LogFree.DualitySetup` — the objects of the Halász duality count (L5)

This file fixes the two functions that the Halász duality frame
`Work.ZeroDensity.Jutila.halaszDualityFrame` is applied to in the proof of the
duality count `Work.ZeroDensity.LogFree.DualityCount p`:

* `halaszU' p q T = U/L² = D^u/L²` (`D = scale q T`, `L = Lscale q T`);
* `halaszA p q T : ℕ → ℂ`, the Halász weight `a_n = (Σψ)(n)·n^{-1/2}·g(n)^{1/2}`;
* `halaszF p q T χ ρ : ℕ → ℂ`, the dual vector
  `f_{χ,ρ}(n) = (Σθ)(n)·χ(n)·n^{1/2-ρ}·g(n)^{1/2}`;
* `halaszN p q T = ⌈X L^{10}⌉`, the truncation point of the frame.

All the analytic input Props of `GramProps.lean` are stated for the *infinite* sums
`Density4.detSum` and `gramEntry`; the truncated sums of the frame are compared with them here
(or in the lemmas of the same directory that are stated in this vocabulary).
-/

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroDensity.LogFree

open Work.LinnikContract

/-- `U' = U/L² = D^u/L²`. -/
def halaszU' (p : Params) (q : ℕ) (T : ℝ) : ℝ := Dpow q T p.u / (Lscale q T) ^ 2

/-- The Halász weight `a_n = (Σψ)(n)·n^{-1/2}·g(n)^{1/2}`. -/
def halaszA (p : Params) (q : ℕ) (T : ℝ) : ℕ → ℂ :=
  fun n => ((psiSum (Dpow q T p.u) (Dpow q T p.v) n : ℝ) : ℂ) * ((n : ℂ) ^ (-(1 / 2 : ℂ)))
    * ((Real.sqrt (gfun (Dpow q T p.x) (halaszU' p q T) n) : ℝ) : ℂ)

/-- The dual vector `f_{χ,ρ}(n) = (Σθ)(n)·χ(n)·n^{1/2-ρ}·g(n)^{1/2}`. -/
def halaszF (p : Params) (q : ℕ) (T : ℝ) (χ : DirichletCharacter ℂ q) (ρ : ℂ) : ℕ → ℂ :=
  fun n => ((thetaS (Dpow q T p.w) n : ℝ) : ℂ) * χ (n : ZMod q) * ((n : ℂ) ^ ((1 / 2 : ℂ) - ρ))
    * ((Real.sqrt (gfun (Dpow q T p.x) (halaszU' p q T) n) : ℝ) : ℂ)

/-- The truncation point `N = ⌈X L^{10}⌉` of the Halász frame. -/
def halaszN (p : Params) (q : ℕ) (T : ℝ) : ℕ :=
  ⌈Dpow q T p.x * (Lscale q T) ^ 10⌉₊

/-! ## Elementary facts -/

lemma halaszU'_apply (p : Params) (q : ℕ) (T : ℝ) :
    halaszU' p q T = Dpow q T p.u / (Lscale q T) ^ 2 := rfl

lemma halaszA_apply (p : Params) (q : ℕ) (T : ℝ) (n : ℕ) :
    halaszA p q T n = ((psiSum (Dpow q T p.u) (Dpow q T p.v) n : ℝ) : ℂ)
      * ((n : ℂ) ^ (-(1 / 2 : ℂ)))
      * ((Real.sqrt (gfun (Dpow q T p.x) (halaszU' p q T) n) : ℝ) : ℂ) := rfl

lemma halaszF_apply (p : Params) (q : ℕ) (T : ℝ) (χ : DirichletCharacter ℂ q) (ρ : ℂ) (n : ℕ) :
    halaszF p q T χ ρ n = ((thetaS (Dpow q T p.w) n : ℝ) : ℂ) * χ (n : ZMod q)
      * ((n : ℂ) ^ ((1 / 2 : ℂ) - ρ))
      * ((Real.sqrt (gfun (Dpow q T p.x) (halaszU' p q T) n) : ℝ) : ℂ) := rfl

/-- The damping factor is non-negative as soon as `U' ≤ X`. -/
lemma gfun_nonneg {X U' : ℝ} (hU' : 0 < U') (hle : U' ≤ X) (n : ℕ) : 0 ≤ gfun X U' n := by
  rw [gfun]
  apply sub_nonneg.mpr
  apply Real.exp_le_exp.mpr
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hX : 0 < X := lt_of_lt_of_le hU' hle
  rw [neg_le_neg_iff]
  exact div_le_div_of_nonneg_left hn hU' hle

end Work.ZeroDensity.LogFree
