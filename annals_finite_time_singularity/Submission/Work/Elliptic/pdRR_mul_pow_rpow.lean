import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Cyl.Coords
import Submission.Work.Cyl.FieldDeriv
import Submission.Work.Elliptic.first_derivs_mul_pow_rpow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The second radial derivative of `r ↦ r² Ψ (r^α, θ)`

This is the second-order companion of `Work.Elliptic.first_derivs_mul_pow_rpow`: whereas that
lemma computes `∂_r` and `∂_{x₃}` (first and second axial) of `(r,z) ↦ r² Ψ(r^α,z)`, here we
compute its *second radial derivative* at a point `(ρ, θ)` with `ρ > 0`:

`∂_rr [r² Ψ(r^α,θ)] = 2 Ψ(ρ^α,θ) + α(α+3) ρ^α ∂_RΨ(ρ^α,θ) + α² ρ^{2α} ∂_RRΨ(ρ^α,θ)`.

The formula is the `∂_rr` analogue of the polar chain rule: with `R = ρ^α`, `r = ρ`, one has
`∂_rr [r²Ψ] = 2Ψ + 2r·(αR/r)∂_RΨ + ...`, and the coefficient of `∂_RΨ` collects to `α(α+3)ρ^α`
while that of `∂_RRΨ` is `α²ρ^{2α}`.

## Strategy

The proof follows exactly the pattern of `Work.Elliptic.pdRR_comp_polar`:

* `pdRR F ρ θ = deriv (fun s ↦ pdR F s θ) ρ` by definition;
* on a neighbourhood of `ρ` the first radial derivative is given by the *first-order*
  formula of `first_derivs_mul_pow_rpow` (which only needs `ContDiffAt ℝ 2` of `uncurry Ψ`
  at the moving point `(s^α, θ)`; this holds eventually because `ContDiffAt` is a local
  property and `s ↦ s^α` is continuous at `ρ > 0`);
* the derivative of the resulting explicit expression is computed with the chain rule for
  `s ↦ Ψ(s^α)θ` and `s ↦ ∂_RΨ(s^α)θ`, which requires `DiffAt2 Ψ` resp. `DiffAt2 (pdR Ψ)`
  at `(ρ^α, θ)` (the latter is the hypothesis `hpdR`);
* the resulting value is matched to the target with the `rpow` identities
  `ρ = ρ^1`, `ρ^{α+1} = ρ^α·ρ`, `ρ^{α-1} = ρ^α/ρ`, `ρ^{2α} = ρ^α·ρ^α`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

open Filter

namespace Work.Elliptic

/-- If `F` is `C²` at `(R t₀, Z t₀)` and `R, Z` are continuous at `t₀`, then `F` is `C²` at
`(R s, Z s)` for all `s` near `t₀`.  (The `ContDiffAt` companion of
`Work.Elliptic.eventually_diffAt2_comp`.) -/
theorem eventually_contDiffAt_comp (F : ℝ × ℝ → ℝ) (R Z : ℝ → ℝ) (t₀ : ℝ)
    (hF : ContDiffAt ℝ 2 F (R t₀, Z t₀)) (hR : ContinuousAt R t₀) (hZ : ContinuousAt Z t₀) :
    ∀ᶠ s in nhds t₀, ContDiffAt ℝ 2 F (R s, Z s) := by
  obtain ⟨u, hu, huF⟩ := hF.contDiffOn le_rfl (by norm_num)
  obtain ⟨v, hvsub, hvopen, hvmem⟩ := mem_nhds_iff.mp hu
  have hcont : ContinuousAt (fun s : ℝ => (R s, Z s)) t₀ := hR.prodMk hZ
  filter_upwards [hcont.preimage_mem_nhds (hvopen.mem_nhds hvmem)] with s hs
  exact (huF.mono hvsub).contDiffAt (hvopen.mem_nhds hs)

theorem pdRR_mul_pow_rpow (Ψ : ℝ → ℝ → ℝ) (α ρ θ : ℝ) (hρ : 0 < ρ)
    (hΨ : ContDiffAt ℝ 2 (Function.uncurry Ψ) (ρ ^ α, θ))
    (hpdR : Work.Cyl.DiffAt2 (Work.Cyl.pdR Ψ) (ρ ^ α) θ) :
    Work.Cyl.pdRR (fun p q => p ^ 2 * Ψ (p ^ α) q) ρ θ
      = 2 * Ψ (ρ ^ α) θ + α * (α + 3) * ρ ^ α * Work.Cyl.pdR Ψ (ρ ^ α) θ
        + α ^ 2 * ρ ^ (2 * α) * Work.Cyl.pdRR Ψ (ρ ^ α) θ := by
  have hρne : ρ ≠ 0 := ne_of_gt hρ
  -- `uncurry Ψ` is `C²` at `(s^α, θ)` for all `s` near `ρ`
  have hΨev : ∀ᶠ s in nhds ρ, ContDiffAt ℝ 2 (Function.uncurry Ψ) (s ^ α, θ) :=
    eventually_contDiffAt_comp (Function.uncurry Ψ) (fun s => s ^ α) (fun _ => θ) ρ hΨ
      (Real.continuousAt_rpow_const ρ α (Or.inl hρne)) continuousAt_const
  -- the first radial derivative is given by `first_derivs_mul_pow_rpow` near `ρ`
  have hev : (fun s => Work.Cyl.pdR (fun p q => p ^ 2 * Ψ (p ^ α) q) s θ)
      =ᶠ[nhds ρ] (fun s => 2 * s * Ψ (s ^ α) θ
        + α * s ^ (α + 1) * Work.Cyl.pdR Ψ (s ^ α) θ) := by
    filter_upwards [hΨev, eventually_gt_nhds hρ] with s hsF hs
    exact (first_derivs_mul_pow_rpow Ψ α s θ hs hsF).1
  rw [Work.Cyl.pdRR, hev.deriv_eq]
  -- first derivatives of the two slices `u ↦ Ψ u θ` and `u ↦ ∂_RΨ u θ` at `ρ^α`
  have hH : HasDerivAt (fun u : ℝ => Ψ u θ) (Work.Cyl.pdR Ψ (ρ ^ α) θ) (ρ ^ α) := by
    have hd : DifferentiableAt ℝ (fun u : ℝ => Ψ u θ) (ρ ^ α) :=
      Work.Cyl.differentiableAt_slice_fst Ψ (ρ ^ α) θ (hΨ.differentiableAt (by decide))
    simpa only [Work.Cyl.pdR] using hd.hasDerivAt
  have hK : HasDerivAt (fun u : ℝ => Work.Cyl.pdR Ψ u θ) (Work.Cyl.pdRR Ψ (ρ ^ α) θ) (ρ ^ α) := by
    have hd : DifferentiableAt ℝ (fun u : ℝ => Work.Cyl.pdR Ψ u θ) (ρ ^ α) :=
      Work.Cyl.differentiableAt_slice_fst (Work.Cyl.pdR Ψ) (ρ ^ α) θ hpdR
    simpa only [Work.Cyl.pdRR] using hd.hasDerivAt
  -- derivatives of the powers `s ↦ s^α`, `s ↦ s^{α+1}` at `ρ`
  have hpow₁ : HasDerivAt (fun s : ℝ => s ^ α) (α * ρ ^ (α - 1)) ρ :=
    Real.hasDerivAt_rpow_const (Or.inl hρne)
  have hpow₂ : HasDerivAt (fun s : ℝ => s ^ (α + 1)) ((α + 1) * ρ ^ α) ρ := by
    have h := Real.hasDerivAt_rpow_const (x := ρ) (p := α + 1) (Or.inl hρne)
    rw [show α + 1 - 1 = α by ring] at h
    exact h
  -- chain rule for the two composed slices
  have hHA : HasDerivAt (fun s : ℝ => Ψ (s ^ α) θ)
      (Work.Cyl.pdR Ψ (ρ ^ α) θ * (α * ρ ^ (α - 1))) ρ := by
    have h := hH.comp ρ hpow₁
    exact h
  have hKA : HasDerivAt (fun s : ℝ => Work.Cyl.pdR Ψ (s ^ α) θ)
      (Work.Cyl.pdRR Ψ (ρ ^ α) θ * (α * ρ ^ (α - 1))) ρ := by
    have h := hK.comp ρ hpow₁
    exact h
  -- the two summands of the explicit expression
  have hA : HasDerivAt (fun s : ℝ => 2 * s * Ψ (s ^ α) θ)
      ((2 * 1) * Ψ (ρ ^ α) θ
        + (2 * ρ) * (Work.Cyl.pdR Ψ (ρ ^ α) θ * (α * ρ ^ (α - 1)))) ρ := by
    have h := ((hasDerivAt_id ρ).const_mul 2).mul hHA
    convert h using 1 <;> (try funext s) <;> simp only [Pi.mul_apply, id] <;> ring
  have hB : HasDerivAt (fun s : ℝ => α * s ^ (α + 1) * Work.Cyl.pdR Ψ (s ^ α) θ)
      ((α * ((α + 1) * ρ ^ α)) * Work.Cyl.pdR Ψ (ρ ^ α) θ
        + (α * ρ ^ (α + 1)) * (Work.Cyl.pdRR Ψ (ρ ^ α) θ * (α * ρ ^ (α - 1)))) ρ := by
    have h := (hpow₂.const_mul α).mul hKA
    convert h using 1 <;> (try funext s) <;> simp only [Pi.mul_apply, id] <;> ring
  -- combine and read off the derivative
  have hg : HasDerivAt (fun s : ℝ => 2 * s * Ψ (s ^ α) θ
        + α * s ^ (α + 1) * Work.Cyl.pdR Ψ (s ^ α) θ) _ ρ := hA.add hB
  rw [hg.deriv]
  -- algebra: rewrite the remaining `rpow`s in terms of `ρ` and `ρ^α`
  have hsub : ρ ^ (α - 1) = ρ ^ α / ρ := by rw [Real.rpow_sub hρ, Real.rpow_one]
  have hadd1 : ρ ^ (α + 1) = ρ ^ α * ρ := by rw [Real.rpow_add hρ, Real.rpow_one]
  have hadd2 : ρ ^ (2 * α) = ρ ^ α * ρ ^ α := by
    rw [show (2 : ℝ) * α = α + α by ring, Real.rpow_add hρ]
  rw [hsub, hadd1, hadd2]
  field_simp
  ring

end Work.Elliptic
