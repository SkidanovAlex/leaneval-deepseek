/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EpsCorrTendsto.lean` — the `P₀`-correction vanishes in the limit

The `ε`-scheme is *projected*: `epsRHSP α ρ ε Φs E g τ = Pz (J_ε (epsWP α ρ ε Φs E g τ))` with

  `Pz f = f - (L₁₂ f 0 / pzNorm) • bump`

(`PZero.lean`).  In the `ε → 0` limit the projection must disappear, otherwise the limit satisfies
the dynamics of `rhsFun` *plus* a multiple of `bump`, which is not what `EpsLimPkg.eqT` asserts.
The correction coefficient is `c_ε = L₁₂(J_ε W_ε)(0)/pzNorm` where `W_ε` is the *pre-mollified*
right-hand side `epsWP α ρ ε Φs E g τ`.

This module proves `c_ε → 0` from the two inputs that the design supplies:

* the **zero-mode identity** `L₁₂(W_ε)(0) = 0` for the projected family (the paper's
  `L₁₂(∂_τg)(0) = (1-μ)L₁₂(g)(0)` at a profile with `L₁₂(g)(0) = 0`; delegated as
  `Work.FTS.StrongEps.EpsZeroMode`, whose hypotheses are the class-`C` data of the projected
  slice) — here taken as the hypothesis `h0`, so that this module is independent of it;
* the **mollifier error** `|L₁₂(J_ε f)(0) - L₁₂ f(0)| ≤ C ε |f|_{ℋ⁵}` for `f ∈ C^∞(Q0)` with
  honest `ℋ⁵`-membership (`Work.FTS.StrongEps.L12_Jeps_sub_le`, proved), together with the
  `ε`-uniform `ℋ⁵`-bound `|W_ε|_{ℋ⁵} ≤ B` on the pre-mollified right-hand sides.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Topology.Algebra.Ring.Real
import Submission.Work.FTS.StrongEps.L12_Jeps_sub_le
import Submission.Work.FTS.StrongEps.PZeroAux.pzNorm_pos
import Submission.Work.FTS.StrongEps.PZeroScheme
import Submission.Work.FTS.VocabO2

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-- **The `P₀`-correction vanishes**: along a sequence of pre-mollified right-hand sides `W n` of
the projected scheme, with

* the correct mollifier scales (`0 < ε n ≤ 1`, `ε n → 0`),
* the class-`C`-level regularity of each `W n` (`SmoothOpen`, honest `ℋ⁵`),
* an `ε`-uniform `ℋ⁵`-bound `B` on `W n`, and
* the zero-mode identity `L₁₂(W n)(0) = 0`,

the correction coefficients `c n = L₁₂(J_{ε n}(W n))(0)/pzNorm` tend to `0`. -/
theorem EpsCorr_tendsto_zero {α C₀ Cs B : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn}
    {ε : ℕ → ℝ} {G : ℕ → Fam} {τ : ℝ}
    (hρ : IsSmoothKernel ρ) (hα : α ∈ Set.Ioc 0 1)
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hε : ∀ n : ℕ, 0 < ε n) (hε1 : ∀ n : ℕ, ε n ≤ 1)
    (hεt : Filter.Tendsto ε Filter.atTop (nhds 0))
    (hsm : ∀ n : ℕ, Work.FTS.EllipticEst.SmoothOpen (epsWP α ρ (ε n) Φs E (G n) τ))
    (h5 : ∀ n : ℕ, Work.Spaces.HkMem α 5 (epsWP α ρ (ε n) Φs E (G n) τ))
    (hb : ∀ n : ℕ, Work.Spaces.HkNorm α 5 (epsWP α ρ (ε n) Φs E (G n) τ) ≤ B)
    (h0 : ∀ n : ℕ, Work.Construction.L12 (epsWP α ρ (ε n) Φs E (G n) τ) 0 = 0) :
    Filter.Tendsto
      (fun n : ℕ => Work.Construction.L12
        (Jeps ρ (ε n) (epsWP α ρ (ε n) Φs E (G n) τ)) 0 / pzNorm)
      Filter.atTop (nhds 0) := by
  obtain ⟨C, hCpos, hkey⟩ := L12_Jeps_sub_le ρ hρ
  -- the pointwise bound `|L₁₂(J_ε W)(0)| ≤ C ε |W|_{ℋ⁵} ≤ C ε B`
  have hbd : ∀ n : ℕ,
      |Work.Construction.L12 (Jeps ρ (ε n) (epsWP α ρ (ε n) Φs E (G n) τ)) 0|
        ≤ C * ε n * B := by
    intro n
    have h := hkey α hα (epsWP α ρ (ε n) Φs E (G n) τ) (hsm n) (h5 n) (ε n)
      ⟨hε n, hε1 n⟩
    rw [h0 n, sub_zero] at h
    exact h.trans (mul_le_mul_of_nonneg_left (hb n)
      (mul_nonneg hCpos.le (hε n).le))
  have hzero : Filter.Tendsto
      (fun n : ℕ => C * ε n * B) Filter.atTop (nhds (C * 0 * B)) :=
    ((hεt.const_mul C).mul_const B)
  have hC0 : C * (0 : ℝ) * B = 0 := by ring
  rw [hC0] at hzero
  have habs : Filter.Tendsto
      (fun n : ℕ => |Work.Construction.L12
        (Jeps ρ (ε n) (epsWP α ρ (ε n) Φs E (G n) τ)) 0|) Filter.atTop (nhds 0) :=
    squeeze_zero (fun n => abs_nonneg _) (fun n => hbd n) hzero
  have hmain : Filter.Tendsto
      (fun n : ℕ => Work.Construction.L12
        (Jeps ρ (ε n) (epsWP α ρ (ε n) Φs E (G n) τ)) 0) Filter.atTop (nhds 0) :=
    (tendsto_zero_iff_abs_tendsto_zero _).mpr habs
  have hpz : pzNorm ≠ 0 := ne_of_gt PZeroAux.pzNorm_pos
  simpa only [zero_div] using hmain.div_const pzNorm

end Work.FTS.StrongEps
