import Mathlib
import Submission.Work.OddVolterra.RowIdentity.WWDefs

/-!
# The substitution `σ = u + θ² (1 - u)` in the swept integral `WW`

The swept integral of the odd row identity is

`WW n h x y u = ∫_σ in u..1, (σ-u)^{n+1/2} · B u σ`,

with `B = Bfun n h x y u` the smooth factor of `Wint` (see `WWDefs`).  This file evaluates it in
the variable `θ` of the substitution

`σ = u + θ² (1 - u)`  (`0 ≤ θ ≤ 1`, `u < 1`),

i.e. it proves

`WW n h x y u = (1-u)^{n+3/2} · ∫_θ in 0..1, 2 θ^{2n+2} · B (u + θ²(1-u))`.

Indeed `dσ = 2θ(1-u) dθ` and

`(σ-u)^{n+1/2} = (θ²(1-u))^{n+1/2} = θ^{2n+1} (1-u)^{n+1/2}`,

so that the integrand becomes `2(1-u)^{n+3/2} θ^{2n+2} B`, and the constant `(1-u)^{n+3/2}` can be
pulled out of the integral.

The change of variables is `intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg`: the
substitution `θ ↦ u + θ²(1-u)` is `C¹` on `[0,1]` with nonnegative derivative `2θ(1-u)`, and -- as
that lemma is unconditional in the integrand -- no regularity of `B` (and hence of `x`, `y`, `h`)
is needed.  All the content is the half-integer power bookkeeping, isolated in
`rpow_sq_mul_half_step` below.
-/

namespace Work.OddVolterra.RowIdentity

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

noncomputable section

/-- The half-integer power bookkeeping behind the substitution `σ = u + θ² δ`:

`(θ² δ)^{n+1/2} · 2 θ δ = δ^{n+3/2} · 2 θ^{2n+2}`  for `θ > 0`, `δ > 0`. -/
lemma rpow_sq_mul_half_step (n : ℕ) {θ δ : ℝ} (hθ : 0 < θ) (hδ : 0 < δ) :
    (θ ^ 2 * δ) ^ ((n : ℝ) + 1 / 2) * (2 * θ * δ)
      = δ ^ ((n : ℝ) + 3 / 2) * (2 * θ ^ (2 * n + 2)) := by
  have hθpow : (θ ^ 2) ^ ((n : ℝ) + 1 / 2) = θ ^ (2 * n + 1) := by
    have hcast : (2 : ℝ) * ((n : ℝ) + 1 / 2) = ((2 * n + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [← Real.rpow_natCast θ (2 * n + 1), ← Real.rpow_two, ← Real.rpow_mul hθ.le, hcast]
  have hθstep : θ ^ (2 * n + 1) * θ = θ ^ (2 * n + 2) := by
    rw [← Real.rpow_natCast θ (2 * n + 2), ← Real.rpow_natCast θ (2 * n + 1),
      ← Real.rpow_add_one hθ.ne']
    congr 1
    push_cast
    ring
  have hδstep : δ ^ ((n : ℝ) + 1 / 2) * δ = δ ^ ((n : ℝ) + 3 / 2) := by
    rw [← Real.rpow_add_one hδ.ne']
    congr 1
    ring
  calc (θ ^ 2 * δ) ^ ((n : ℝ) + 1 / 2) * (2 * θ * δ)
      = ((θ ^ 2) ^ ((n : ℝ) + 1 / 2) * δ ^ ((n : ℝ) + 1 / 2)) * (2 * θ * δ) := by
        rw [Real.mul_rpow (sq_nonneg θ) hδ.le]
    _ = (θ ^ (2 * n + 1) * δ ^ ((n : ℝ) + 1 / 2)) * (2 * θ * δ) := by rw [hθpow]
    _ = (θ ^ (2 * n + 1) * θ) * (δ ^ ((n : ℝ) + 1 / 2) * δ) * 2 := by ring
    _ = θ ^ (2 * n + 2) * δ ^ ((n : ℝ) + 3 / 2) * 2 := by rw [hθstep, hδstep]
    _ = δ ^ ((n : ℝ) + 3 / 2) * (2 * θ ^ (2 * n + 2)) := by ring

/-- The pointwise form of the substitution, with `δ = 1 - u`: the integrand
`Wint u σ · dσ/dθ` at `σ = u + θ²(1-u)` is the substituted integrand times the constant
`(1-u)^{n+3/2}`. -/
lemma Wint_subst_factor_rpow (n : ℕ) (h x y : ℝ → ℝ) {u θ : ℝ} (hθ : 0 < θ) (hu1 : u < 1) :
    Wint n h x y u (u + θ ^ 2 * (1 - u)) * (2 * θ * (1 - u))
      = (1 - u) ^ ((n : ℝ) + 3 / 2)
        * (2 * θ ^ (2 * n + 2) * Bfun n h x y u (u + θ ^ 2 * (1 - u))) := by
  have hδ : 0 < 1 - u := by linarith
  have harg : u + θ ^ 2 * (1 - u) - u = θ ^ 2 * (1 - u) := by ring
  rw [Wint_eq_mul_Bfun, harg]
  calc (θ ^ 2 * (1 - u)) ^ ((n : ℝ) + 1 / 2)
          * Bfun n h x y u (u + θ ^ 2 * (1 - u)) * (2 * θ * (1 - u))
      = ((θ ^ 2 * (1 - u)) ^ ((n : ℝ) + 1 / 2) * (2 * θ * (1 - u)))
          * Bfun n h x y u (u + θ ^ 2 * (1 - u)) := by ring
    _ = ((1 - u) ^ ((n : ℝ) + 3 / 2) * (2 * θ ^ (2 * n + 2)))
          * Bfun n h x y u (u + θ ^ 2 * (1 - u)) := by
          rw [rpow_sq_mul_half_step n hθ hδ]
    _ = (1 - u) ^ ((n : ℝ) + 3 / 2)
          * (2 * θ ^ (2 * n + 2) * Bfun n h x y u (u + θ ^ 2 * (1 - u))) := by ring

/-- **The substitution `σ = u + θ²(1-u)` in the swept integral `WW`.**

`WW n h x y u = (1-u)^{n+3/2} ∫_θ in 0..1, 2 θ^{2n+2} Bfun n h x y u (u + θ²(1-u))`. -/
theorem WW_eq_subst (H : Setup) {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    WW H.n H.h H.x H.y u
      = (1 - u) ^ ((H.n : ℝ) + 3 / 2) *
        ∫ θ in (0 : ℝ)..1,
          2 * θ ^ (2 * H.n + 2) * Bfun H.n H.h H.x H.y u (u + θ ^ 2 * (1 - u)) := by
  have hderiv : ∀ θ ∈ Set.Ioo (min (0 : ℝ) 1) (max (0 : ℝ) 1),
      HasDerivAt (fun θ : ℝ => u + θ ^ 2 * (1 - u)) (2 * θ * (1 - u)) θ := by
    intro θ hθ
    rw [min_eq_left (zero_le_one), max_eq_right (zero_le_one)] at hθ
    have h1 : HasDerivAt (fun θ : ℝ => θ ^ 2 * (1 - u)) (2 * θ * (1 - u)) θ := by
      simpa using ((hasDerivAt_pow 2 θ).mul_const (1 - u))
    simpa [add_comm] using h1.const_add u
  have hnonneg : ∀ θ ∈ Set.Ioo (min (0 : ℝ) 1) (max (0 : ℝ) 1), 0 ≤ 2 * θ * (1 - u) := by
    intro θ hθ
    rw [min_eq_left (zero_le_one), max_eq_right (zero_le_one)] at hθ
    have h2 : 0 < 1 - u := by linarith
    exact mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hθ.1.le) h2.le
  have hsub := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (f := fun θ : ℝ => u + θ ^ 2 * (1 - u)) (f' := fun θ : ℝ => 2 * θ * (1 - u))
    (g := fun σ : ℝ => Wint H.n H.h H.x H.y u σ) (a := 0) (b := 1)
    (by fun_prop) hderiv hnonneg
  have hsub' : (∫ θ in (0 : ℝ)..1,
        Wint H.n H.h H.x H.y u (u + θ ^ 2 * (1 - u)) * (2 * θ * (1 - u)))
      = WW H.n H.h H.x H.y u := by
    rw [WW]
    simpa [Function.comp_def] using hsub
  rw [← hsub']
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall (fun θ hθ => ?_))
  rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hθ
  exact Wint_subst_factor_rpow H.n H.h H.x H.y hθ.1 hu1

end

end Work.OddVolterra.RowIdentity
