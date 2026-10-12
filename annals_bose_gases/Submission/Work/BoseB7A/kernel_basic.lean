import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseB7A.kernel_coef_bounds
import Submission.Work.BoseB7A.lille_threshold
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseB7A.kernel_basic` — the elementary consequences of `Q3Kernel`

The first *derived* facts of the `BoseB7A` chapter (design `BOSE_3Q_LEAD.md` §3,
node N2): the fields of `Q3Kernel K₀ F T E` at a small diluteness `t = μa³`,
together with the parameter values of `FSParamsView`, give, on the quarter region
`P_H^q = {|q| ≥ ¼K_H⁻¹a⁻¹}`,

* `α` is even (`𝒜`, `ℬ` are even, and `α = ℬ/(𝒜+√(𝒜²−ℬ²))`),
* `2|ℬ_q| ≤ 𝒜_q` (FS `eq:BoverA`), hence `1 − α_q² ≥ 1/2`,
* `|α_q| ≤ 64K₀𝓁` (FS `eq:alphaInPH`), the smallness used to discard all the
  squeezed modes of `lem:EstimatesOnQ3-js`,
* `𝒟_q ≥ |q|²/4`, the kinetic reserve on `P_H^q`.

## The arithmetic

On `P_H^q` one has `|q|²/2 ≤ 𝒜_q` (`Q3Kernel.A_ge`) and
`|ℬ_q| ≤ ρ_zK₀a ≤ (3/2)μK₀a`, so

`|ℬ_q|/𝒜_q ≤ 32ρ_zK₀a³K_H² ≤ 48K₀𝓁` and `2|ℬ_q|/𝒜_q ≤ 64ρ_zK₀a³K_H² ≤ 96K₀𝓁`,

with `𝓁 = (μa³)K_H²` (`eq:DefLille`).  Hence the single smallness hypothesis
`96K₀𝓁 ≤ 1` gives every claimed inequality; it holds for `t ≤ t₀(K₀)` because
`𝓁 = X^{97/2} = t^{97/646}` (`Work.BoseB7.FSParamsVals.lille_val`), which is the
content of the delegated `lille_threshold`.

The hypothesis `K₀ < 0` is vacuous: `Q3Kernel.count_PL` together with
`K_ℓK_L ≥ 1` (`FSParamsView`) bounds a non-negative cardinality by `K₀(K_ℓK_L)³`,
so no instance exists and `0 ≤ K₀` is a *consequence* of `Q3Kernel` (this is also
what makes the bound `|α_q| ≤ 64K₀𝓁` meaningful, as its right-hand side must be
non-negative).

## Contents

* `kernel_basic` — the requested statement.
-/

namespace Work.BoseB7A

theorem kernel_basic (K₀ b₀ : ℝ) (hb₀ : 0 < b₀) :
    ∃ t₀ : ℝ, 0 < t₀ ∧
      ∀ {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
        (F : Work.BoseB7.FockData Mode) (T : Work.BoseB7A.TildeData F)
        (E : Work.BoseB7.Q3Env Mode) (hv : Work.BoseB7.FSParamsView E),
        hv.t ≤ t₀ → b₀ ≤ E.b → Work.BoseB7A.Q3Kernel K₀ F T E →
        (∀ k : Mode, E.alpha (-k) = E.alpha k) ∧
        (∀ q : Mode, F.PHq E.KH E.aScat q → 2 * |E.B q| ≤ E.A q) ∧
        (∀ q : Mode, F.PHq E.KH E.aScat q → 1 / 2 ≤ 1 - E.alpha q ^ 2) ∧
        (∀ q : Mode, F.PHq E.KH E.aScat q → |E.alpha q| ≤ 64 * K₀ * E.lille) ∧
        (∀ q : Mode, F.PHq E.KH E.aScat q → ‖F.kmom q‖ ^ 2 / 4 ≤ E.D q) := by
  obtain ⟨t₀, ht₀, hLil⟩ := lille_threshold K₀
  refine ⟨t₀, ht₀, ?_⟩
  intro Mode _ _ _ F _T E hv htle _hb hK
  -- `𝓁 ≥ 0` (so that `96K₀𝓁` is monotone in `K₀`)
  have hlille_nn : 0 ≤ E.lille := by
    have h1 : 0 < E.mu := Work.BoseB7.mu_pos E hv
    have h2 : 0 < E.aScat := hv.a_pos
    simp only [Work.BoseB7.Q3Env.lille, Work.BoseB7.lille]
    exact mul_nonneg (mul_nonneg (le_of_lt h1) (pow_nonneg (le_of_lt h2) 3)) (sq_nonneg _)
  -- the smallness `96K₀𝓁 ≤ 1` of `FSParamsView` at `t ≤ t₀`
  have hsmall96 : 96 * K₀ * E.lille ≤ 1 := by
    have h1 : 96 * max K₀ 0 * E.lille ≤ 1 := hLil E hv htle
    have h2 : K₀ ≤ max K₀ 0 := le_max_left _ _
    have h3 : 96 * K₀ * E.lille ≤ 96 * max K₀ 0 * E.lille := by nlinarith [h2, hlille_nn]
    linarith
  -- `0 ≤ K₀`: forced by the lattice count (`count_PL`) and `K_ℓK_L ≥ 1`
  have hK0 : 0 ≤ K₀ := by
    by_contra hneg
    have hneg' : K₀ < 0 := not_le.mp hneg
    have hcp := hK.count_PL
    have hcard : (0 : ℝ) ≤
        (((Work.BoseB7.excited Mode).filter (fun s => E.fL s ≠ 0)).card : ℝ) := by
      exact_mod_cast Nat.zero_le _
    have hKl : 0 < E.Kl := by linarith [hv.one_le_Kl]
    have hKL : 0 < E.KL := by linarith [hv.one_le_KL]
    have hpos : 0 < (E.Kl * E.KL) ^ 3 := pow_pos (mul_pos hKl hKL) 3
    have hneg2 : K₀ * (E.Kl * E.KL) ^ 3 < 0 := mul_neg_of_neg_of_pos hneg' hpos
    linarith
  -- the per-mode bundle
  have key : ∀ q : Mode, F.PHq E.KH E.aScat q →
      (2 * |E.B q| ≤ E.A q) ∧ (1 / 2 ≤ 1 - E.alpha q ^ 2) ∧
      (|E.alpha q| ≤ 64 * K₀ * E.lille) ∧ (‖F.kmom q‖ ^ 2 / 4 ≤ E.D q) := by
    intro q hq
    have hKH : 0 < E.KH := lt_of_lt_of_le one_pos hv.one_le_KH
    have ha : 0 < E.aScat := hv.a_pos
    have hKa : 0 < E.KH * E.aScat := mul_pos hKH ha
    have hcut : 1 / (4 * E.KH * E.aScat) ≤ ‖F.kmom q‖ := hq
    have h4Ka : 0 < 4 * E.KH * E.aScat := by nlinarith [hKa]
    have hcutpos : 0 < 1 / (4 * E.KH * E.aScat) := by positivity
    have hRpos : 0 < ‖F.kmom q‖ := lt_of_lt_of_le hcutpos hcut
    have hApos : 0 < E.A q := by
      have h1 : 0 < ‖F.kmom q‖ ^ 2 / 2 := by positivity
      linarith [hK.A_ge q hq]
    have hBle : |E.B q| ≤ E.rho * K₀ * E.aScat := by
      have hρ : 0 < E.rho := Work.BoseB7.rho_pos E hv
      rw [hK.B_eq q, abs_mul, abs_of_nonneg (le_of_lt hρ)]
      nlinarith [hK.W1_le q, hρ]
    have hρl : E.rho * E.aScat ^ 3 * E.KH ^ 2 ≤ (3 / 2) * E.lille := by
      have h1 : E.rho ≤ 3 * E.mu / 2 := Work.BoseB7.rho_le E hv
      have h3 : 0 ≤ E.aScat ^ 3 * E.KH ^ 2 :=
        mul_nonneg (pow_nonneg (le_of_lt hv.a_pos) 3) (sq_nonneg _)
      have h4 : E.rho * (E.aScat ^ 3 * E.KH ^ 2) ≤
          (3 * E.mu / 2) * (E.aScat ^ 3 * E.KH ^ 2) :=
        mul_le_mul_of_nonneg_right h1 h3
      simp only [Work.BoseB7.Q3Env.lille, Work.BoseB7.lille]
      nlinarith [h4]
    have hkey := kernel_coef_bounds (A := E.A q) (B := E.B q) (R := ‖F.kmom q‖)
      (ρ := E.rho) (K := K₀) (a := E.aScat) (KH := E.KH) (ell := E.lille)
      hK0 hlille_nn hKa hApos (hK.AB q) hBle (hK.A_ge q hq) hcut hρl hsmall96
    simpa only [Work.BoseB7.Q3Env.alpha, Work.BoseB7.Q3Env.D] using hkey
  exact ⟨fun k => by
      simp only [Work.BoseB7.Q3Env.alpha, Work.BoseB7.alphaCoef,
        hK.A_even k, hK.B_even k],
    fun q hq => (key q hq).1, fun q hq => (key q hq).2.1,
    fun q hq => (key q hq).2.2.1, fun q hq => (key q hq).2.2.2⟩

end Work.BoseB7A
