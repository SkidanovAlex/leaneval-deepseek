/-
# `Work.FTS.CoercivityFix.Coer1` — the level-1 coercivity of the clean operator `Lhat`

Definitions and bookkeeping lemmas for the base case of the corrected coercivity of node N2
(`Work.FTS.CoercivityFix`, design `FTS/N45_DESIGN_LEAD.md` §5 T2):

  `2 * |f|²_{ℋ¹} ≤ H1IP α (Lhat f) f`   for `f ∈ RegQ α 2`,

where `Lhat f = 𝓛f − Transport f = f + D_zf − 2f/(1+z) − 3D_θf/(1+z)` is the paper's `𝓛`
with the angular transport term subtracted and *no* nonlocal term.

## The mathematics

`Lhat` has no `L₁₂`-term, so its coercivity needs no `L₁₂`-zero-mode hypothesis at all; the
whole estimate is the two elementary integrations by parts of §6 of the paper:

* the paper's identity `(LW)`, `𝓛(g)w = gw + z∂_z(gw)`, gives for every angular weight
  `σ(θ)` the *sharp* self-adjointness `⟨𝓛u, u⟩_{w²σ} = ½⟨u, u⟩_{w²σ}`;
* the transport pairing `⟨3D_θu/(1+z), u⟩_{w²sin^{-β}}` is `3(β-1)⟨cos(2θ)u²/(1+z)⟩_{w²sin^{-β}}`,
  and the choice `β = η = 99/100` resp. `β = γ = 1 + α/10` makes `|β - 1| = 1/100` resp.
  `α/10` *small*, so that this pairing costs only `(3/100)⟨u,u⟩` resp. `(3α/10)⟨u,u⟩`.

Consequently `⟨Lhat u, u⟩_{w²sin^{-η}} ≥ (47/100)⟨u,u⟩_{w²sin^{-η}}` and
`⟨Lhat u, u⟩_{w²sin^{-γ}} ≥ (17/40)⟨u,u⟩_{w²sin^{-γ}}`.  Fed into the four pairings of `H1IP`
(with coefficients `10, 10¹⁰, 10¹⁷, 10²¹`) this dominates `2|f|²_{ℋ¹}` with a huge margin.

## Contents

* the angular weight `sig β θ = sin(2θ)^{-β}`, the pair weight `Rho β = w²·sin(2θ)^{-β}` and
  the weighted energies `En β u = ∫∫ u² w² sin(2θ)^{-β}`, `EnOne u = ∫∫ u² w²`
  (`wip_Rho_self`, `wip_one_self` identify them with the corresponding `wip`'s);
* the identification of the paper's energies `EDz`, `EfEta`, `EDth`, `Ef` with the
  `En`-functionals (`EDz_eq_En`, `EfEta_eq_En`, `EDth_eq_En`, `Ef_eq_EnOne`);
* the monotonicity `sin(2θ)^{-η} ≤ sin(2θ)^{-γ}` of the angular weight on the *open* interval
  (`sig_eta_le_sig_gam`), and `1 ≤ sin(2θ)^{-η}` (`one_le_sig_eta`).

All the `En`-identifications hold *unconditionally*: they are pointwise algebraic identities
under the integrals.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.CoercivityFix.Basic
import Submission.Work.FTS.LocData.SmoothChain
import Submission.Work.Coercivity.Eztheta1_eq_HkSq_one
import Submission.Work.Coercivity.thetaAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Coer1

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-! ## The angular weight and the weighted energies -/

/-- The angular weight `sin(2θ)^{-β}` of the pairings of `H1IP`. -/
def sig (β θ : ℝ) : ℝ := (Real.sin (2 * θ)) ^ (-β)

/-- The pair weight `ρ_β(z,θ) = w(z)²·sin(2θ)^{-β}`.  With `β = η` and `β = gam α` this is
exactly the weight of the first two resp. the fourth pairing of `Work.Coercivity.H1IP`. -/
def Rho (β : ℝ) : Fn := fun z θ => Work.Spaces.w z ^ 2 * sig β θ

theorem Rho_apply (β : ℝ) (z θ : ℝ) :
    Rho β z θ = Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-β) := rfl

/-- `Rho (gam α)` is the angular weight `Work.Coercivity.thetaW α` of the `γ`-estimates of
§6. -/
theorem Rho_gam (α : ℝ) : Rho (Work.Spaces.gam α) = Work.Coercivity.thetaW α := rfl

/-- The two ways of writing the half-weight agree: `(w/sin(2θ)^{β/2})² = w²·sin(2θ)^{-β}`. -/
theorem wdiv_sq (β z θ : ℝ) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (β / 2)) ^ 2
      = Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-β) := by
  have hs : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have h1 : ((Real.sin (2 * θ)) ^ (β / 2)) ^ 2 = (Real.sin (2 * θ)) ^ β := by
    rw [sq, ← Real.rpow_add hs]
    congr 1
    ring
  rw [div_pow, h1, div_eq_mul_inv, ← Real.rpow_neg (le_of_lt hs)]

/-- The two ways of writing the full angular weight agree:
`(u · Wt α)² = u²·w²·sin(2θ)^{-gam α}` on the open angular interval. -/
theorem Wt_sq (α : ℝ) (u : Fn) {z θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    (u z θ * Work.Spaces.Wt α z θ) ^ 2
      = u z θ ^ 2 * Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
  have hs : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have h1 : ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ 2
      = (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
    rw [sq, ← Real.rpow_add hs]
    congr 1
    ring
  simp only [Work.Spaces.Wt, Work.Spaces.wTheta]
  rw [mul_pow, mul_pow, h1]
  ring

/-- The `β`-weighted energy `E_β(u) = ∫∫ u² w² sin(2θ)^{-β}`. -/
def En (β : ℝ) (u : Fn) : ℝ :=
  ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
    u z θ ^ 2 * Work.Spaces.w z ^ 2 * sig β θ

/-- The unweighted (in `θ`) energy `∫∫ u² w²`. -/
def EnOne (u : Fn) : ℝ :=
  ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, u z θ ^ 2 * Work.Spaces.w z ^ 2

/-- Almost every angle of `Iθ` lies in the *open* interval `(0,π/2)` (the two endpoints form
a null set).  This is the a.e. statement that lets the `SmoothQuad` identities — which hold on
the open quadrant only — be used under the integral. -/
theorem ae_restrict_Iθ_mem_Ioo :
    ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), θ ∈ Set.Ioo 0 (π / 2) := by
  have hset : Set.Ioo (0 : ℝ) (π / 2) =ᵐ[volume] Work.Spaces.Iθ :=
    MeasureTheory.Ioo_ae_eq_Icc
  rw [← MeasureTheory.Measure.restrict_congr_set hset]
  exact MeasureTheory.ae_restrict_mem measurableSet_Ioo

/-- `sin(2θ) ≥ 0` on the closed angular interval. -/
theorem sin_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- If `θ ∈ Iθ` and `sin(2θ) > 0` then `θ` is in the *open* angular interval. -/
theorem mem_Ioo_of_mem_Iθ_of_sin_pos {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ)
    (h : 0 < Real.sin (2 * θ)) : θ ∈ Set.Ioo 0 (π / 2) := by
  refine ⟨lt_of_le_of_ne hθ.1 ?_, lt_of_le_of_ne hθ.2 ?_⟩
  · intro h0
    rw [← h0, mul_zero, Real.sin_zero] at h
    exact absurd h (lt_irrefl 0)
  · intro h0
    rw [h0, show (2 : ℝ) * (π / 2) = π by ring, Real.sin_pi] at h
    exact absurd h (lt_irrefl 0)

/-- The half-weight identity on the *closed* angular interval (at the endpoints both sides
vanish). -/
theorem sig_div_sq_Iθ (β : ℝ) (hβ : β ≠ 0) (z θ : ℝ) (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (β / 2)) ^ 2 = Work.Spaces.w z ^ 2 * sig β θ := by
  have hβ2 : β / 2 ≠ 0 := by intro hc; exact hβ (by linarith)
  rcases eq_or_lt_of_le (sin_nonneg_of_mem_Iθ hθ) with h | h
  · rw [sig]
    rw [← h, Real.zero_rpow hβ2, div_zero, sq, mul_zero,
      Real.zero_rpow (by intro hc; exact hβ (by linarith)), mul_zero]
  · rw [wdiv_sq β z θ (mem_Ioo_of_mem_Iθ_of_sin_pos hθ h)]
    rfl

/-- The full angular-weight identity on the *closed* angular interval. -/
theorem Wt_sq_self_Iθ (α : ℝ) (z θ : ℝ) (hα : 0 < α) (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.Wt α z θ) ^ 2 = Work.Spaces.w z ^ 2 * sig (Work.Spaces.gam α) θ := by
  have hγ : Work.Spaces.gam α ≠ 0 := by rw [Work.Spaces.gam]; intro hc; linarith
  have hγ2 : -(Work.Spaces.gam α / 2) ≠ 0 := by intro hc; exact hγ (by linarith)
  have hγ' : -(Work.Spaces.gam α) ≠ 0 := by intro hc; exact hγ (by linarith)
  have hfun : (Work.Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ 2 := by
    simp only [Work.Spaces.Wt, Work.Spaces.wTheta]
  rw [hfun]
  rcases eq_or_lt_of_le (sin_nonneg_of_mem_Iθ hθ) with h | h
  · rw [sig, ← h, Real.zero_rpow hγ2, Real.zero_rpow hγ']
    ring
  · rw [mul_pow, sig]
    rw [show ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ 2
        = (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) from by
      rw [sq, ← Real.rpow_add h]
      congr 1
      ring]

theorem En_nonneg (β : ℝ) (u : Fn) : 0 ≤ En β u := by
  rw [En]
  refine integral_nonneg_of_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Ici] with z _
  refine integral_nonneg_of_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
  exact mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    (Real.rpow_nonneg (sin_nonneg_of_mem_Iθ hθ) _)

theorem EnOne_nonneg (u : Fn) : 0 ≤ EnOne u := by
  rw [EnOne]
  exact integral_nonneg fun _ => integral_nonneg fun _ =>
    mul_nonneg (sq_nonneg _) (sq_nonneg _)

/-! ## The integration-by-parts hypotheses in the interior class

`Work.Coercivity.IBP` is the package that makes the `z`-integration by parts of §6 valid; its
smoothness field is `Spaces.SmoothNbhd` (**analyticity** on a neighbourhood of the closed
quadrant), which the cut-off data of the route cannot satisfy (design §5 T1).  The package
below is the *interior* replacement: genuine `C^∞` on the open quadrant (`SmoothQuad`),
together with the same boundary limits and the a.e. (in `θ`) honesty of the two one-dimensional
integrals of the fundamental theorem of calculus.  Every instance needed here comes from
`RegQ α 2 f` by `Work.Spaces.HkMem` (see `IntFacts.lean`). -/

/-- The analytic hypotheses of the `z`-integration by parts in the interior class: `u` is
`C^∞` on the open quadrant, the boundary term `z(u w)²` vanishes at `z = 0⁺` and `z = ∞` for
every angle in the *open* interval (`Ioo 0 (π/2)`; this is exactly the first conjunct of
`BdryTraces` in the pairs `(0,0)`, `(1,0)`, `(0,1)` — the endpoints `θ = 0, π/2` are not
constrained by `RegQ`), and for
almost every angle the two one-dimensional integrals of the fundamental theorem of calculus
are honest. -/
structure ZIBP (u : Fn) : Prop where
  smooth : Work.FTS.LocData.SmoothQuad u
  bd0 : ∀ θ ∈ Set.Ioo 0 (π / 2),
    Filter.Tendsto (fun z => z * (u z θ * Work.Spaces.w z) ^ 2) (𝓝[>] 0) (𝓝 0)
  bdTop : ∀ θ ∈ Set.Ioo 0 (π / 2),
    Filter.Tendsto (fun z => z * (u z θ * Work.Spaces.w z) ^ 2) Filter.atTop (𝓝 0)
  intSq : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
    IntegrableOn (fun z => (u z θ * Work.Spaces.w z) ^ 2) (Set.Ioi 0)
  intDeriv : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
    IntegrableOn (fun z => deriv (fun z' => z' * (u z' θ * Work.Spaces.w z') ^ 2) z) (Set.Ioi 0)

/-! ## The integrability bundle

In this development the weighted pairings of `H1IP` are *honest* real numbers: every integrand
that occurs below is `IntegrableOn` the quadrant, and the certificates are collected once and
for all in the structure `IntPkg` (proved for `RegQ α 2 f` in `IntPkg/IntPkg_Q`).  This keeps
the four coercivity estimates of `Estimates.lean` purely algebraic.

The fields fall into five groups:

* `sqDzEta`, `sqMixedEta`, `sqMixedGam`, `sqDzOne`, `sqMixedOne` — the squared blocks with the
  `η`, `γ` and plain radial weights (all dominated by the summands of `HkIntegrand α 2 f`);
* `intL_*` — the `𝓛`-pairings `𝓛u·u·ρ` occurring in the estimates;
* `intLhat_Dz_eta`, `intE2hat_Dz_eta` — the two pieces of the `D_z`-commutator split for `Lhat`;
* `hint_*` — the transport pairings `D_θu·u·ρ/(1+z)`;
* `zibp_*` — the `z`-integration-by-parts hypotheses for the three functions used. -/

structure IntPkg (α : ℝ) (f : Fn) : Prop where
  /-- the squared `D_z`-blocks with the `η`-weight -/
  sqDzEta : ∀ i : ℕ, i ≤ 2 → MeasureTheory.IntegrableOn
    (Function.uncurry (fun z θ => (Work.Spaces.DzIter i f z θ) ^ 2 * Rho Work.Spaces.eta z θ))
    (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
  /-- the squared mixed blocks with the `η`-weight -/
  sqMixedEta : ∀ i j : ℕ, 1 ≤ i → i + j ≤ 2 → MeasureTheory.IntegrableOn
    (Function.uncurry (fun z θ => (Work.Spaces.mixed j i f z θ) ^ 2 * Rho Work.Spaces.eta z θ))
    (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
  /-- the squared mixed blocks with the `γ`-weight -/
  sqMixedGam : ∀ i j : ℕ, 1 ≤ i → i + j ≤ 2 → MeasureTheory.IntegrableOn
    (Function.uncurry (fun z θ =>
      (Work.Spaces.mixed j i f z θ) ^ 2 * Rho (Work.Spaces.gam α) z θ))
    (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
  /-- the squared `D_z`-blocks with the plain radial weight -/
  sqDzOne : ∀ i : ℕ, i ≤ 2 → MeasureTheory.IntegrableOn
    (Function.uncurry (fun z θ => (Work.Spaces.DzIter i f z θ) ^ 2 * Work.Spaces.w z ^ 2))
    (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
  /-- the squared mixed blocks with the plain radial weight -/
  sqMixedOne : ∀ i j : ℕ, 1 ≤ i → i + j ≤ 2 → MeasureTheory.IntegrableOn
    (Function.uncurry (fun z θ => (Work.Spaces.mixed j i f z θ) ^ 2 * Work.Spaces.w z ^ 2))
    (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
  /-- the `𝓛`-pairing of `f` with the `η`-weight -/
  intL_f_eta : MeasureTheory.IntegrableOn
    (Function.uncurry (fun z θ => Work.Coercivity.L f z θ * f z θ * Rho Work.Spaces.eta z θ))
    (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
  /-- the `𝓛`-pairing of `D_z f` with the `η`-weight -/
  intL_Dz_eta : MeasureTheory.IntegrableOn
    (Function.uncurry (fun z θ => Work.Coercivity.L (Work.Spaces.Dz f) z θ
      * Work.Spaces.Dz f z θ * Rho Work.Spaces.eta z θ))
    (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
  /-- the `𝓛`-pairing of `D_θ f` with the `γ`-weight -/
  intL_Dth_gam : MeasureTheory.IntegrableOn
    (Function.uncurry (fun z θ => Work.Coercivity.L (Work.Spaces.Dth f) z θ
      * Work.Spaces.Dth f z θ * Rho (Work.Spaces.gam α) z θ))
    (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
  /-- the `𝓛`-pairing of `f` with the plain radial weight -/
  intL_f_one : MeasureTheory.IntegrableOn
    (Function.uncurry (fun z θ => Work.Coercivity.L f z θ * f z θ * Work.Spaces.w z ^ 2))
    (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
  /-- the `Lhat`-pairing of `D_z f` with the `η`-weight -/
  intLhat_Dz_eta : MeasureTheory.IntegrableOn
    (Function.uncurry (fun z θ => Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dz f) z θ
      * Work.Spaces.Dz f z θ * Rho Work.Spaces.eta z θ))
    (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
  /-- the `D_z`-commutator defect against `D_z f` with the `η`-weight -/
  intE2hat_Dz_eta : MeasureTheory.IntegrableOn
    (Function.uncurry (fun z θ => Work.FTS.CoercivityFix.E2hat f z θ
      * Work.Spaces.Dz f z θ * Rho Work.Spaces.eta z θ))
    (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
  /-- the transport pairing of `f` with the `η`-weight -/
  hint_f_eta : MeasureTheory.IntegrableOn
    (Function.uncurry (fun z θ => Work.Spaces.Dth f z θ * f z θ
      * Rho Work.Spaces.eta z θ / (1 + z)))
    (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
  /-- the transport pairing of `D_z f` with the `η`-weight -/
  hint_Dz_eta : MeasureTheory.IntegrableOn
    (Function.uncurry (fun z θ => Work.Spaces.Dth (Work.Spaces.Dz f) z θ * Work.Spaces.Dz f z θ
      * Rho Work.Spaces.eta z θ / (1 + z)))
    (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
  /-- the transport pairing of `D_θ f` with the `γ`-weight -/
  hint_Dth_gam : MeasureTheory.IntegrableOn
    (Function.uncurry (fun z θ => Work.Spaces.Dth (Work.Spaces.Dth f) z θ
      * Work.Spaces.Dth f z θ * Rho (Work.Spaces.gam α) z θ / (1 + z)))
    (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
  /-- the transport pairing of `f` with the plain radial weight -/
  hint_f_one : MeasureTheory.IntegrableOn
    (Function.uncurry (fun z θ => Work.Spaces.Dth f z θ * f z θ
      * Work.Spaces.w z ^ 2 / (1 + z)))
    (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
  /-- the `z`-integration-by-parts hypotheses for `f` -/
  zibp_f : ZIBP f
  /-- the `z`-integration-by-parts hypotheses for `D_z f` -/
  zibp_Dz : ZIBP (Work.Spaces.Dz f)
  /-- the `z`-integration-by-parts hypotheses for `D_θ f` -/
  zibp_Dth : ZIBP (Work.Spaces.Dth f)

/-! ## The pointwise core of the `z`-integration by parts

The paper's identity `(LW)`, `𝓛(g)·w = g·w + z∂_z(g·w)`, in the interior class `SmoothQuad`.
Both lemmas below are the `SmoothQuad` counterparts of `Work.Coercivity.l_self_w_sq_eq` and
`Work.Coercivity.deriv_zw_sq_eq`; the only change is that the differentiability of the `z`-slice
comes from `SmoothQuad.curry_z` instead of from `Spaces.SmoothNbhd`.  They are stated on the
*open* angular interval (`θ ∈ Ioo 0 (π/2)`), which is what `SmoothQuad` provides, and are used
under the integral only for a.e. `θ`. -/

/-- `𝓛u·u·w² = (u w)² + ½ z ∂_z((u w)²)` on the open quadrant. -/
theorem l_self_w_sq_Q {u : Fn} (hu : Work.FTS.LocData.SmoothQuad u) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Work.Coercivity.L u z θ * u z θ * Work.Spaces.w z ^ 2
      = (u z θ * Work.Spaces.w z) ^ 2
        + (1 / 2) * (z * deriv (fun z' => (u z' θ * Work.Spaces.w z') ^ 2) z) := by
  have hz1 : z ∈ Set.Ioi (-1 : ℝ) := by simp only [Set.mem_Ioi]; linarith
  have hd : DifferentiableAt ℝ (fun z' => u z' θ) z :=
    ((hu.curry_z hθ).differentiableOn Work.FTS.LocData.smoothOrder_ne_zero).differentiableAt
      (isOpen_Ioi.mem_nhds hz1)
  have hf : HasDerivAt (fun z' => u z' θ) (Work.Spaces.pz u z θ) z := hd.hasDerivAt
  have hLw : Work.Coercivity.L u z θ * Work.Spaces.w z
      = u z θ * Work.Spaces.w z
        + z * Work.Spaces.pz (fun z θ => u z θ * Work.Spaces.w z) z θ :=
    Work.Coercivity.L_mul_w_deriv hz hf
  have hgw : DifferentiableAt ℝ (fun z' => u z' θ * Work.Spaces.w z') z :=
    (hf.mul (Work.Coercivity.hasDerivAt_w (ne_of_gt hz))).differentiableAt
  have hgsq : deriv (fun z' => (u z' θ * Work.Spaces.w z') ^ 2) z
      = 2 * (u z θ * Work.Spaces.w z)
          * Work.Spaces.pz (fun z θ => u z θ * Work.Spaces.w z) z θ := by
    have h1 := (hgw.hasDerivAt).pow 2
    have h2 : deriv (fun z' => (u z' θ * Work.Spaces.w z') ^ 2) z
        = 2 * (u z θ * Work.Spaces.w z) ^ (2 - 1)
            * deriv (fun z' => u z' θ * Work.Spaces.w z') z := h1.deriv
    rw [h2]
    simp only [Nat.reduceSub, pow_one]
    rfl
  have hkey : Work.Coercivity.L u z θ * u z θ * Work.Spaces.w z ^ 2
      = (Work.Coercivity.L u z θ * Work.Spaces.w z) * (u z θ * Work.Spaces.w z) := by
    ring
  rw [hkey, hLw, hgsq]
  ring

/-- `∂_z(z (u w)²) = (u w)² + z ∂_z((u w)²)` on the open quadrant. -/
theorem deriv_zw_sq_Q {u : Fn} (hu : Work.FTS.LocData.SmoothQuad u) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    deriv (fun z' => z' * (u z' θ * Work.Spaces.w z') ^ 2) z
      = (u z θ * Work.Spaces.w z) ^ 2
        + z * deriv (fun z' => (u z' θ * Work.Spaces.w z') ^ 2) z := by
  have hz1 : z ∈ Set.Ioi (-1 : ℝ) := by simp only [Set.mem_Ioi]; linarith
  have hd : DifferentiableAt ℝ (fun z' => u z' θ) z :=
    ((hu.curry_z hθ).differentiableOn Work.FTS.LocData.smoothOrder_ne_zero).differentiableAt
      (isOpen_Ioi.mem_nhds hz1)
  have hf : HasDerivAt (fun z' => u z' θ) (Work.Spaces.pz u z θ) z := hd.hasDerivAt
  have hw : DifferentiableAt ℝ (Work.Spaces.w) z :=
    (Work.Coercivity.hasDerivAt_w (ne_of_gt hz)).differentiableAt
  have hg : DifferentiableAt ℝ (fun z' => (u z' θ * Work.Spaces.w z') ^ 2) z :=
    (hd.mul hw).pow 2
  have hmain : deriv (fun z' => z' * (u z' θ * Work.Spaces.w z') ^ 2) z
      = 1 * (u z θ * Work.Spaces.w z) ^ 2
        + z * deriv (fun z' => (u z' θ * Work.Spaces.w z') ^ 2) z :=
    HasDerivAt.deriv ((hasDerivAt_id z).mul hg.hasDerivAt)
  rw [hmain]; ring

/-! ## The `wip`'s of `H1IP` in terms of the `En`-functionals -/

/-- The `β`-weighted `wip` of a function with itself is its `β`-energy. -/
theorem wip_Rho_self (β : ℝ) (u : Fn) :
    Work.Coercivity.wip (Rho β) u u = En β u := by
  rw [Work.Coercivity.wip, En]
  refine setIntegral_congr_fun measurableSet_Ici fun z _ => ?_
  refine setIntegral_congr_fun measurableSet_Icc fun θ _ => ?_
  simp only [Rho, sig]
  ring

/-- The plain `wip` of a function with itself is `EnOne`. -/
theorem wip_one_self (u : Fn) :
    Work.Coercivity.wip (fun z _ => Work.Spaces.w z ^ 2) u u = EnOne u := by
  rw [Work.Coercivity.wip, EnOne]
  refine setIntegral_congr_fun measurableSet_Ici fun z _ => ?_
  refine setIntegral_congr_fun measurableSet_Icc fun θ _ => ?_
  ring

/-! ## Identification with the energies of the coercivity chapter -/

/-- On `Iθ` the two expressions for the half-weight coincide: `(sin(2θ)^{-β/2})² = sin(2θ)^{-β}`. -/
theorem sin_half_sq (β θ : ℝ) (hθ : θ ∈ Work.Spaces.Iθ) :
    ((Real.sin (2 * θ)) ^ (-(β / 2))) ^ 2 = (Real.sin (2 * θ)) ^ (-β) := by
  rcases eq_or_lt_of_le (sin_nonneg_of_mem_Iθ hθ) with h | h
  · rw [← h]
    rcases eq_or_ne β 0 with rfl | hβ
    · norm_num
    · have h1 : -(β / 2) ≠ 0 := by intro hc; exact hβ (by linarith)
      have h2 : -β ≠ 0 := by intro hc; exact hβ (by linarith)
      rw [Real.zero_rpow h1, Real.zero_rpow h2]
      norm_num
  · rw [sq, ← Real.rpow_add h]
    congr 1
    ring

/-- `EfEta u = ∫∫ u² w² sin(2θ)^{-η}`. -/
theorem EfEta_eq_En (u : Fn) : Work.Coercivity.EfEta u = En Work.Spaces.eta u := by
  unfold Work.Coercivity.EfEta Work.Spaces.L2Sq En Work.Coercivity.wtEta
    Work.Coercivity.wtGam sig
  refine setIntegral_congr_fun measurableSet_Ici fun z _ => ?_
  refine setIntegral_congr_fun measurableSet_Icc fun θ hθ => ?_
  rw [mul_pow, mul_pow, sin_half_sq Work.Spaces.eta θ hθ]
  ring

/-- `EDz u = ∫∫ (D_zu)² w² sin(2θ)^{-η}`. -/
theorem EDz_eq_En (u : Fn) : Work.Coercivity.EDz u = En Work.Spaces.eta (Work.Spaces.Dz u) := by
  unfold Work.Coercivity.EDz Work.Spaces.L2Sq En Work.Coercivity.wtEta
    Work.Coercivity.wtGam sig
  refine setIntegral_congr_fun measurableSet_Ici fun z _ => ?_
  refine setIntegral_congr_fun measurableSet_Icc fun θ hθ => ?_
  rw [mul_pow, mul_pow, sin_half_sq Work.Spaces.eta θ hθ]
  ring

/-- `EDth α u = ∫∫ (D_θu)² w² sin(2θ)^{-γ}`. -/
theorem EDth_eq_En (α : ℝ) (u : Fn) :
    Work.Coercivity.EDth α u = En (Work.Spaces.gam α) (Work.Spaces.Dth u) := by
  unfold Work.Coercivity.EDth Work.Spaces.L2Sq En Work.Coercivity.wtGam sig
  refine setIntegral_congr_fun measurableSet_Ici fun z _ => ?_
  refine setIntegral_congr_fun measurableSet_Icc fun θ hθ => ?_
  rw [mul_pow, mul_pow, sin_half_sq (Work.Spaces.gam α) θ hθ]
  ring

/-- `Ef u = ∫∫ u² w²`. -/
theorem Ef_eq_EnOne (u : Fn) : Work.Coercivity.Ef u = EnOne u := by
  unfold Work.Coercivity.Ef Work.Spaces.L2Sq EnOne
  refine setIntegral_congr_fun measurableSet_Ici fun z _ => ?_
  refine setIntegral_congr_fun measurableSet_Icc fun θ _ => ?_
  ring

/-! ## The monotonicity of the angular weight

For `s ∈ (0,1]` and `p ≤ q` we have `s^{-p} ≤ s^{-q}` (`Real.rpow_le_rpow_of_exponent_ge`);
hence on the *open* angular interval, where `0 < sin(2θ) ≤ 1`,

  `sin(2θ)^{-η} ≤ sin(2θ)^{-γ}`  and  `1 = sin(2θ)^{-0} ≤ sin(2θ)^{-η}`.

(The endpoints `θ = 0, π/2`, where `sin(2θ) = 0` and Lean's `rpow` takes the junk value, are
null sets; the comparisons are therefore only used under the integral in their a.e. form.) -/

theorem eta_le_gam (α : ℝ) (hα : 0 < α) : Work.Spaces.eta ≤ Work.Spaces.gam α := by
  rw [Work.Spaces.gam]
  have := Work.Spaces.eta_lt_one
  linarith

theorem sig_eta_le_sig_gam (α : ℝ) (hα : 0 < α) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    sig Work.Spaces.eta θ ≤ sig (Work.Spaces.gam α) θ := by
  have hs : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  rw [sig, sig]
  exact Real.rpow_le_rpow_of_exponent_ge hs hs1 (by linarith [eta_le_gam α hα])

theorem one_le_sig_eta {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    1 ≤ sig Work.Spaces.eta θ := by
  have hs : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have h := Real.rpow_le_rpow_of_exponent_ge hs hs1
    (show -(Work.Spaces.eta) ≤ -(0 : ℝ) by
      have := Work.Spaces.eta_pos; linarith)
  rw [sig]
  simpa using h

theorem sig_eta_le_sig_gam_ae (α : ℝ) (hα : 0 < α) :
    ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      sig Work.Spaces.eta θ ≤ sig (Work.Spaces.gam α) θ :=
  ae_restrict_Iθ_mem_Ioo.mono (fun θ hθ => sig_eta_le_sig_gam α hα hθ)

theorem one_le_sig_eta_ae :
    ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), 1 ≤ sig Work.Spaces.eta θ :=
  ae_restrict_Iθ_mem_Ioo.mono (fun θ hθ => one_le_sig_eta hθ)

end Work.FTS.CoercivityFix.Coer1
