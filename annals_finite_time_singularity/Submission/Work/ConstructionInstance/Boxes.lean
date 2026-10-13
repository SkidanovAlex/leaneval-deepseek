/-
# `Work.ConstructionInstance.Boxes` — the bootstrap boxes, derived from the self-similar ansatz

This file shows, for the two boxes that the deliverable's item 2 asks for, exactly how the
`St0`–`St3` output turns them into *consequences* rather than assumptions.  The honest content of
the bootstrap is

* the **pointwise self-similar ansatz** in the core,
  `ω(x,t) = λ̄(t)^{-1}·F(ρ(x)^p/λ̄(t), θ(x))·e_θ(x)`, i.e. in the vocabulary of this directory
  `ω (·,t) = (λ̄ t)⁻¹ • omegaS p (fun z θ => g (z / λ̄ t) θ)` (the profile rescaled in the
  self-similar variable — note the extra `λ̄(t)^{-1}` inside the profile argument, which is what
  makes the vorticity blow up while the perturbation stays bounded), and
* the **uniform bound on the perturbation**, `|g(z,θ)| ≤ Cg` for every `z ≥ 0`, `θ ∈ Iθ` (this is
  the design's `(B1)`: `‖g‖_{ℋ⁴} ≤ Cα²`, which by `Work.Spaces.Linf_H2` bounds `g` in `L^∞`).

From those two, `Basic.omegaS_norm_le` gives the **box**

  `λ̄(t)·‖ω(x,t)‖ ≤ 20p + Cg`   for every `t` in the window and every `x`,

i.e. `‖ω(·,t)‖_∞ ≲ 1/λ̄(t)` — which *grows* like `1/(T-t)` and is therefore **incompatible with a
time-independent bound over the window**: this is the content of `Obstruction.lean`, and the reason
the interface's `hBdd`/`hBddDt` must be replaced (see `NOTES.md` §2(0)).  The same computation on a
*fixed strip* `[0,S]`, `S < T`, gives a genuine constant
`M_S := (sup_{t ∈ [-2,S+2]} λ̄(t)^{-1})·(20p + Cg)`.

The lower-bound field `hansatz` is derived in the same way from the profile's lower bound at one
point (`Work.StabilityFar.Profile.exists_Fstar_add_ge`), rescaled by λ̄ as above.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Submission.Work.ConstructionInstance.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

namespace Work.ConstructionInstance

/-- `c * ‖c⁻¹ • v‖ = ‖v‖` for `c > 0`. -/
theorem mul_norm_inv_smul {c : ℝ} (hc : 0 < c) (v : R3) : c * ‖c⁻¹ • v‖ = ‖v‖ := by
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hc, inv_eq_one_div]
  field_simp

/-- **The perturbation bound implies a *uniform* bound of the scaled profile**: if `|g(z,θ)| ≤ Cg`
for all `z ≥ 0`, `θ ∈ Iθ` (the design's `(B1)`, `‖g‖_{ℋ⁴} ≤ Cα²` through
`Work.Spaces.Linf_H2`), then for every self-similar variable `z` the field `omegaSz p g z` is
bounded by `20p + Cg` — because `|F_*(z,θ)| ≤ 20pΓ(θ) ≤ 20p` **uniformly in `z`**
(`Defs.Fstar_abs_le`: the profile `2z/(1+z)²` decays at infinity). -/
theorem omegaSz_norm_le {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) {g : ℝ → ℝ → ℝ} {Cg : ℝ}
    (hCg : 0 ≤ Cg) (hgbdd : ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → |g z θ| ≤ Cg)
    {z : ℝ} (hz : 0 ≤ z) (x : R3) : ‖omegaSz p g z x‖ ≤ 20 * p + Cg := by
  rw [omegaSz_apply, norm_smul, Real.norm_eq_abs]
  have hθ_abs : |Work.Cyl.theta x| ≤ Real.pi / 2 := by
    rw [abs_le]
    exact ⟨le_of_lt (Real.neg_pi_div_two_lt_arctan _),
      le_of_lt (Real.arctan_lt_pi_div_two _)⟩
  have hθmem : |Work.Cyl.theta x| ∈ Work.Spaces.Iθ := ⟨abs_nonneg _, hθ_abs⟩
  have hbdd := profile_abs_le_of_abs (p := p) hp hp1 hgbdd z hz (Work.Cyl.theta x) hθ_abs
  have hnn : 0 ≤ 20 * p * Gamma (p / 3) |Work.Cyl.theta x| + Cg :=
    add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hp.le) (Gamma_nonneg hθmem)) hCg
  calc |profile p g z (Work.Cyl.theta x)| * ‖Work.Cyl.eTheta x‖
      ≤ (20 * p * Gamma (p / 3) |Work.Cyl.theta x| + Cg) * 1 :=
        mul_le_mul hbdd (norm_eTheta_le_one x) (norm_nonneg _) hnn
    _ ≤ 20 * p + Cg := by
        have hG : Gamma (p / 3) |Work.Cyl.theta x| ≤ 1 :=
          Gamma_le_one (by positivity) hθmem
        nlinarith [hp.le, hG, hCg]

/-- **The `L^∞` box of the vorticity from the self-similar ansatz.**  With the pointwise ansatz

  `ω(x,t) = λ̄(t)^{-1}·F(ρ(x)^p/λ̄(t), θ(x))·e_θ(x)`,
  i.e. `ω (·,t) = (λ̄ t)⁻¹ • omegaSz p g (ρ(x)^p / λ̄ t) x`,

and the bootstrap's uniform bound on the perturbation, one gets

  `λ̄(t)·‖ω(x,t)‖ ≤ 20p + Cg`   for every `t` in the window and every `x`,

i.e. `‖ω(·,t)‖_∞ ≤ (20p + Cg)/λ̄(t)`: **the vorticity blows up like `1/λ̄(t)`**, exactly as `St5`
requires, and *incompatible with a time-independent bound over the window* — this is the content of
`Obstruction.lean`, and it shows that the interface's `hBdd` must carry the factor `λ̄(t)` (a
one-line change: `λ̄(t)·‖ω y t‖ ≤ M`), or be replaced by a strip-dependent bound. -/
theorem lam_mul_norm_le_of_ansatz {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) {g : ℝ → ℝ → ℝ} {Cg : ℝ}
    (hCg : 0 ≤ Cg)
    (hgbdd : ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → |g z θ| ≤ Cg)
    {ω : R3 → ℝ → R3} {lam : ℝ → ℝ} {T : ℝ}
    (hlam : ∀ t ∈ Work.SolutionDelivery.extWindow T, 0 < lam t)
    (hans : ∀ t : ℝ, ∀ x : R3,
      ω x t = (lam t)⁻¹ • omegaSz p g (Work.Cyl.rho x ^ p / lam t) x) :
    ∀ t ∈ Work.SolutionDelivery.extWindow T, ∀ x : R3,
      lam t * ‖ω x t‖ ≤ 20 * p + Cg := by
  intro t ht x
  rw [hans t x, mul_norm_inv_smul (hlam t ht)]
  exact omegaSz_norm_le hp hp1 hCg hgbdd
    (div_nonneg (Real.rpow_nonneg (Real.sqrt_nonneg _) p) (hlam t ht).le) x

/-- **The `St5` lower bound from the ansatz and the profile's lower bound at one point**: if the
rescaled profile is `≥ c₀α` somewhere for every `t`, then `λ̄(t)·‖ω(x,t)‖ ≥ c₀α` there — which is
the interface's `hansatz`, now *derived* (and consistent with the box above). -/
theorem exists_lam_mul_norm_ge_of_ansatz {T : ℝ} {ω : R3 → ℝ → R3} {lam : ℝ → ℝ} {p α : ℝ}
    {g : ℝ → ℝ → ℝ} {c₀ : ℝ}
    (hlam : ∀ t ∈ Work.SolutionDelivery.extWindow T, 0 < lam t)
    (hans : ∀ t : ℝ, ∀ x : R3,
      ω x t = (lam t)⁻¹ • omegaSz p g (Work.Cyl.rho x ^ p / lam t) x)
    (hlow : ∀ t : ℝ, ∃ x : R3,
      c₀ * α ≤ ‖omegaSz p g (Work.Cyl.rho x ^ p / lam t) x‖) :
    ∀ t ∈ Work.SolutionDelivery.extWindow T, ∃ x : R3, c₀ * α ≤ lam t * ‖ω x t‖ := by
  intro t ht
  obtain ⟨x, hx⟩ := hlow t
  refine ⟨x, ?_⟩
  rw [hans t x, mul_norm_inv_smul (hlam t ht)]
  exact hx

end Work.ConstructionInstance
