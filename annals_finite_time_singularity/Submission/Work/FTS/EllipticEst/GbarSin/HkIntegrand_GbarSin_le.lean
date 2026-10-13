/-
Copyright: work module for the Elgindi finite-time singularity project.

# The pointwise `H^k`-integrand bound for `Ḡ(α,F) · sin 2θ`

This module proves

  `Work.FTS.EllipticEst.GbarSin.HkIntegrand_GbarSin_le`:
for every `k` there is a constant `K_k ≥ 0`, **independent of both `α ∈ (0,1]` and the source
`F`**, such that on the whole quadrant `[0,∞) × [0,π/2]`

  `HkIntegrand α k (Ḡ(α,F) · sin 2θ) z θ ≤ K_k · w(z)² · Σ_{j ≤ k} (D_z^j Ḡ(α,F)(z))²`,

where `Ḡ(α,F) = Work.Elliptic.Gbar α F` is the singular term of Elgindi's
§'Elliptic Regularity Estimates', `w(z) = (1+z)²/z²` is the radial weight and `D_z = z ∂_z` the
radial derivative.  This is the pointwise (`z`-by-`z`) form of the comparison by which the
`H^k` estimate for `Ḡ · sin 2θ` (the paper's Lemma `HardyInequality4`) is reduced to the
weighted `L²` estimate for the radial iterates `D_z^j Ḡ`.

## The argument

`Ḡ(z) sin 2θ` is a product of a radial factor `g(z) = Ḡ(z)` and an angular factor
`u(θ) = sin 2θ`, so both product rules for the iterated operators apply:

* `D_z^j (g(z) u(θ)) = (rDzIter j g)(z) · u(θ)` (`DzIter_mul_of_radial`),
* `D_θ^i (g(z) u(θ)) = g(z) · (D_θ^i u)(0,θ)` (`DthIter_mul_of_angular`),

and consequently `D_z^j D_θ^i (g u) = (rDzIter j g)(z) · sinIter i θ`.  Substituting these into
the two sums defining `HkIntegrand` (`HkIntegrand_GbarSin_eq`) leaves only angular factors, which
are bounded uniformly in `α`:

* the `D_z`-part of the integrand contains `sin 2θ · (w(z) / sin(2θ)^{η/2})` with
  `η = 99/100`; its square is `w(z)² · sin(2θ)^{2-η}` and `sin(2θ)^{2-η} ≤ 1` because
  `0 ≤ 2 - η ≤ 2` and `0 ≤ sin 2θ ≤ 1` (`Work.FTS.EllipticEst.sum_sq_first_le`);
* the mixed part contains `sinIter i θ · w_θ(θ)` with `w_θ(θ) = sin(2θ)^{-γ/2}`,
  `γ = 1 + α/10`; its square is `sinIter i θ² · sin(2θ)^{-γ}`, bounded by a constant `C_i`
  depending only on `i` — the profile `sinIter i = D_θ^i sin 2θ` vanishes like `sin 2θ` at the
  endpoints of `Iθ` (`sinIter_weight_bound`).  This turns the double sum into
  `w(z)² · (Σ_{i≤k} C_i) · Σ_{j≤k} (rDzIter j Ḡ(z))²`
  (`Work.FTS.EllipticEst.sum_sq_second_le`).

Collecting the two estimates gives the claim with `K_k = 1 + Σ_{i≤k} C_i`, a constant that
involves neither `α` nor any hypothesis on `F`.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.EllipticEst.GbarSetup
import Submission.Work.FTS.EllipticEst.sinIter_weight_bound
import Submission.Work.FTS.EllipticEst.DzIter_mul_of_radial
import Submission.Work.FTS.EllipticEst.DthIter_mul_of_angular
import Submission.Work.FTS.EllipticEst.sum_sq_first_le
import Submission.Work.FTS.EllipticEst.sum_sq_second_le
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology

namespace Work.FTS.EllipticEst.GbarSin

set_option autoImplicit false

/-! ## Rewriting the `H^k`-integrand of a separated product -/

/-- The two product rules turn the `H^k`-integrand of `g(z) · u(θ)` into a double sum whose
summands are products of the radial iterates `rDzIter j g` with the angular iterates of `u`:

`D_z^j (g(z)u(θ)) = (rDzIter j g)(z) · u(θ)` and
`D_θ^i (g(z)u(θ)) = g(z) · (D_θ^i u)(0,θ)`.

Specialised to the target `Ḡ(α,F)(z) · sin 2θ`, where the angular iterate of `sin 2θ` is
`sinIter i θ` (so `g` is the radial profile and the only `z`-dependence of the derivatives is
through `rDzIter j g`). -/
theorem HkIntegrand_GbarSin_eq (α : ℝ) (k : ℕ) (G : ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α k (fun z θ => G z * Real.sin (2 * θ)) z θ
      = (∑ i ∈ Finset.range (k + 1),
          (Work.FTS.EllipticEst.rDzIter i G z * Real.sin (2 * θ)
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        + ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            (if 1 ≤ i ∧ i + j ≤ k then
              (Work.FTS.EllipticEst.rDzIter j G z * Work.FTS.EllipticEst.sinIter i θ
                * Work.Spaces.Wt α z θ) ^ 2 else 0) := by
  have hDth : ∀ i, Work.Spaces.DthIter i (fun z θ => G z * Real.sin (2 * θ))
      = fun z θ => G z * Work.FTS.EllipticEst.sinIter i θ := by
    intro i
    funext z θ
    rw [Work.FTS.EllipticEst.DthIter_mul_of_angular i G (fun θ => Real.sin (2 * θ)) z θ]
    rfl
  have hDz : ∀ j i, Work.Spaces.DzIter j (fun z θ => G z * Work.FTS.EllipticEst.sinIter i θ)
      = fun z θ => Work.FTS.EllipticEst.rDzIter j G z * Work.FTS.EllipticEst.sinIter i θ := by
    intro j i
    exact Work.FTS.EllipticEst.DzIter_radial_mul j G (Work.FTS.EllipticEst.sinIter i)
  have hDz0 : ∀ i, Work.Spaces.DzIter i (fun z θ => G z * Real.sin (2 * θ))
      = fun z θ => Work.FTS.EllipticEst.rDzIter i G z * Real.sin (2 * θ) := by
    intro i
    exact Work.FTS.EllipticEst.DzIter_radial_mul i G (fun θ => Real.sin (2 * θ))
  simp only [Work.Spaces.HkIntegrand, Work.Spaces.mixed, hDth, hDz, hDz0]

/-! ## The target estimate -/

theorem HkIntegrand_GbarSin_le (k : ℕ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ (α : ℝ) (F : ℝ → ℝ → ℝ),
    0 < α → α ≤ 1 → ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
    Work.Spaces.HkIntegrand α k (fun z θ => Work.Elliptic.Gbar α F z * Real.sin (2 * θ)) z θ
      ≤ K * (Work.Spaces.w z) ^ 2 *
          ∑ j ∈ Finset.range (k + 1),
            (Work.FTS.EllipticEst.rDzIter j (Work.Elliptic.Gbar α F) z) ^ 2 := by
  classical
  -- one angular constant `C i` for each `D_θ^i`, independent of `α` and of the source
  let C : ℕ → ℝ := fun i => Classical.choose (Work.FTS.EllipticEst.sinIter_weight_bound i)
  have hCnn : ∀ i, 0 ≤ C i := fun i =>
    (Classical.choose_spec (Work.FTS.EllipticEst.sinIter_weight_bound i)).1
  have hCb : ∀ i (α : ℝ), 0 < α → α ≤ 1 → ∀ θ ∈ Work.Spaces.Iθ,
      (Work.FTS.EllipticEst.sinIter i θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        ≤ C i := fun i =>
    (Classical.choose_spec (Work.FTS.EllipticEst.sinIter_weight_bound i)).2
  refine ⟨1 + ∑ i ∈ Finset.range (k + 1), C i, ?_, ?_⟩
  · have h0 : 0 ≤ ∑ i ∈ Finset.range (k + 1), C i :=
      Finset.sum_nonneg fun i _ => hCnn i
    linarith
  · intro α F hα hα1 z hz θ hθ
    have hsin_nn : 0 ≤ Real.sin (2 * θ) :=
      Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
    have hsin_le : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
    have heta0 : (0 : ℝ) < Work.Spaces.eta := by norm_num [Work.Spaces.eta]
    have heta2 : Work.Spaces.eta ≤ 2 := by norm_num [Work.Spaces.eta]
    -- the two sum estimates, with `s = sin 2θ`, `γ = gam α` and `b j = rDzIter j Ḡ(z)`
    have hA := sum_sq_first_le k (fun i => Work.FTS.EllipticEst.rDzIter i (Work.Elliptic.Gbar α F) z)
      (Work.Spaces.w z) (Real.sin (2 * θ)) Work.Spaces.eta heta0 heta2 hsin_nn hsin_le
    have hB := sum_sq_second_le k (fun j => Work.FTS.EllipticEst.rDzIter j (Work.Elliptic.Gbar α F) z)
      C (fun i => Work.FTS.EllipticEst.sinIter i θ) (Work.Spaces.w z) (Real.sin (2 * θ))
      (Work.Spaces.gam α) hsin_nn hCnn (fun i _ => hCb i α hα hα1 θ hθ)
    rw [HkIntegrand_GbarSin_eq α k (Work.Elliptic.Gbar α F) z θ]
    simp only [Work.Spaces.Wt, Work.Spaces.wTheta]
    refine le_trans (add_le_add hA hB) (le_of_eq ?_)
    ring

end Work.FTS.EllipticEst.GbarSin
