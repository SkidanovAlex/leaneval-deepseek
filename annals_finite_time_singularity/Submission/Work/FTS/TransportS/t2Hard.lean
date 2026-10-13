import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.TransportS.T2S
import Submission.Work.FTS.TransportS.Defs
import Submission.Work.FTS.TransportS.HardDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.TransportS

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 800000

/-!
# `T2Hard`: the five order-five terms of the `D_z`-transport pairing

The statement `Work.FTS.TransportS.T2Hard` bounds the "hard" part of the `D_z`-transport
pairing, `Hhard α f g` (`Submission/Work/FTS/H2/T2Defs.lean`), in the frozen (open-quadrant)
hypothesis class:

* on the `f`-side only `SmoothOpen f`, `HkMem α 4 f`, `CoefThMem 1 f` and the pointwise
  bounds `|f| ≤ Mf`, `|D_z f| ≤ Mf` on the open quadrant are used;
* on the `g`-side `SmoothQuad g`, `HkMem α 4 g`, `HkMem α 5 g`, `DecayAll 4 g` and the
  boundary traces `BdryTraces α 4 g` (from `RegQ α 4 g`) are used.

## Route

`Hhard α f g z θ = ∑_{k : Fin 5} f z θ · z · pz (Thard g k) z θ · Thard g k z θ · w² · sghard α k θ`,
and `z · pz (Thard g k) = Dz (Thard g k) = mixed (5 - k) k g`.  Hence each summand is
`f · X_k · Y_k` with

`X_k = Thard g k · w sin(2θ)^{-η_k/2}`, `Y_k = D_z(Thard g k) · w sin(2θ)^{-η_k/2}`

(`η_0 = η`, `η_k = γ` for `k ≥ 1`, see `Submission/Work/FTS/TransportS/HardDefs.lean`), so
`X_k²` is a slot of `HkIntegrand α 4 g` and `Y_k²` is a slot of `HkIntegrand α 5 g`.  The
elementary AM–GM bound `|Hhard| ≤ 5 Mf · HkIntegrand α 5 g` then makes `Hhard`
product-integrable with respect to `(volume.restrict Iz).prod (volume.restrict Iθ)`, which is
what allows the use of Fubini.

The *sharp* estimate is the radial integration by parts, performed θ-slice by θ-slice
(`Work.FTS.TransportS.slice_identity`): for a.e. `θ ∈ Iθ`,

`∫_z Hhard α f g z θ dz = -∫_z ZE α f g z θ dz`

with `ZE` the correction term of the primitive `ZG = ½ f z w² ZU`
(`Work.FTS.H2.HhardZibp`: `Hhard = ∂_z ZG - ZE`).  Fubini in the product measure turns this
into `∫_z∫_θ Hhard = -∫_z∫_θ ZE`, and the crude bound
`|ZE z θ| ≤ 2 Mf w(z)² ZU α g z θ = 2 Mf ∑_k X_k(z,θ)²` gives
`|∫_z∫_θ Hhard| ≤ 2 Mf ∑_k ∫∫ X_k² ≤ 10 Mf HkSq α 4 g`.
-/

/-- The a.e. version of the per-angle integration by parts identity
(`Work.FTS.TransportS.slice_identity`): for almost every angle `θ` the `z`-integral of `Hhard`
is minus that of `ZE`.  The boundary conditions come from `BdryTraces α 4 g` (i.e. from
`RegQ α 4 g`), and the slice integrabilities from the product-integrability of `gK` and `gK'`
(`Work.FTS.TransportS.integrable_gK`, `integrable_gK'`). -/
theorem ae_slice_identity {α Mf : ℝ} {f g : ℝ → ℝ → ℝ} (hα : 0 < α)
    (hsf : Work.FTS.EllipticEst.SmoothOpen f) (hsg : Work.FTS.LocData.SmoothQuad g)
    (hmg4 : Work.Spaces.HkMem α 4 g) (hmg5 : Work.Spaces.HkMem α 5 g)
    (hbdr : Work.FTS.Nonlin.BdryTraces α 4 g) (hMf : 0 ≤ Mf)
    (hf : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 → |f z θ| ≤ Mf)
    (hDzf : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 → |Work.Spaces.Dz f z θ| ≤ Mf) :
    ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      (∫ z in Work.Spaces.Iz, Work.FTS.H2.Hhard α f g z θ)
        = -(∫ z in Work.Spaces.Iz, Work.FTS.H2.ZE α f g z θ) := by
  have hG : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), ∀ k : Fin 5,
      MeasureTheory.IntegrableOn (fun z => gK α f g k z θ) Work.Spaces.Iz :=
    Filter.eventually_all.mpr fun k => ae_integrableOn_slice (integrable_gK hsf hsg hmg5 hMf hf k)
  have hG' : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), ∀ k : Fin 5,
      MeasureTheory.IntegrableOn (fun z => gK' α f g k z θ) Work.Spaces.Iz :=
    Filter.eventually_all.mpr fun k => ae_integrableOn_slice
      (integrable_gK' (α := α) (Mf := Mf) hα hsf hsg hmg5 hMf hf hDzf k)
  have hbnd_ae : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), ∀ k : Fin 5,
      (Filter.Tendsto (fun z => z * (Work.FTS.H2.Thard g k z θ * Work.Spaces.w z) ^ 2)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
        Filter.Tendsto (fun z => z * (Work.FTS.H2.Thard g k z θ * Work.Spaces.w z) ^ 2)
          atTop (nhds 0)) := by
    filter_upwards [ae_mem_Ioo_Iθ] with θ hθ
    intro k
    have h := (hbdr k.val (4 - k.val) (by have := k.isLt; omega)).1 θ hθ
    have hfun : (fun z => z * (Work.Spaces.mixed (4 - k.val) k.val g z θ
        * Work.Spaces.w z) ^ 2)
        = fun z => z * (Work.FTS.H2.Thard g k z θ * Work.Spaces.w z) ^ 2 := by
      funext z
      rw [Thard_apply g k z θ]
    rw [hfun] at h
    exact h
  filter_upwards [hG, hG', hbnd_ae, ae_mem_Ioo_Iθ] with θ hθG hθG' hθb hθioo
  exact slice_identity hsf hsg hMf hθioo (fun z hz => hf z θ hz hθioo.1 hθioo.2) hθb hθG hθG'

theorem t2Hard : Work.FTS.TransportS.T2Hard := by
  refine ⟨10, by norm_num, ?_⟩
  intro α f g Mf hα hα1 hMf hsf hsg hf hDzf
  obtain ⟨hsmo, -, -⟩ := hsf
  obtain ⟨⟨hsqg, hmg4, hbdr⟩, hmg5, -⟩ := hsg
  -- the a.e. θ-slice identity
  have hae := ae_slice_identity (α := α) (Mf := Mf) hα hsmo hsqg hmg4 hmg5 hbdr hMf hf hDzf
  -- the Fubini swaps and the product-integrabilities
  have hIntH := integrable_Hhard (α := α) (Mf := Mf) hsmo hsqg hmg5 hMf hf
  have hIntZE := integrable_ZE_and_bound (α := α) (Mf := Mf) hsmo hsqg hmg4 hMf hf hDzf
  have hIntZ := hIntZE.1
  have hswapH := MeasureTheory.integral_integral_swap
    (μ := volume.restrict Work.Spaces.Iz) (ν := volume.restrict Work.Spaces.Iθ)
    (f := fun z θ => Work.FTS.H2.Hhard α f g z θ) hIntH
  have hswapZ := MeasureTheory.integral_integral_swap
    (μ := volume.restrict Work.Spaces.Iz) (ν := volume.restrict Work.Spaces.Iθ)
    (f := fun z θ => Work.FTS.H2.ZE α f g z θ) hIntZ
  -- the two iterated integrals are opposite
  have hmain : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, Work.FTS.H2.Hhard α f g z θ)
      = -(∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          Work.FTS.H2.ZE α f g z θ) := by
    rw [hswapH, MeasureTheory.integral_congr_ae hae, MeasureTheory.integral_neg, ← hswapZ]
  -- the estimate on the correction term
  have hbound : |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        Work.FTS.H2.ZE α f g z θ| ≤ 10 * Mf * Work.Spaces.HkSq α 4 g := by
    have hψint : MeasureTheory.Integrable (fun z => ∫ θ in Work.Spaces.Iθ,
        |Work.FTS.H2.ZE α f g z θ|) (volume.restrict Work.Spaces.Iz) := by
      have h := MeasureTheory.Integrable.integral_norm_prod_left hIntZ.abs
      simpa only [Real.norm_eq_abs, abs_abs] using h
    have h2 := Work.Spaces.integral_le_integral_of_ae_le_of_nonneg hψint
      (Filter.Eventually.of_forall fun z => integral_nonneg fun θ => abs_nonneg _)
      (Filter.Eventually.of_forall fun z =>
        MeasureTheory.abs_integral_le_integral_abs
          (f := fun θ => Work.FTS.H2.ZE α f g z θ) (μ := volume.restrict Work.Spaces.Iθ))
    calc |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, Work.FTS.H2.ZE α f g z θ|
        ≤ ∫ z in Work.Spaces.Iz,
            |∫ θ in Work.Spaces.Iθ, Work.FTS.H2.ZE α f g z θ| :=
          MeasureTheory.abs_integral_le_integral_abs
      _ ≤ ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
            |Work.FTS.H2.ZE α f g z θ| := h2
      _ = ∫ p, |Work.FTS.H2.ZE α f g p.1 p.2|
            ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
          MeasureTheory.integral_integral hIntZ.abs
      _ ≤ 10 * Mf * Work.Spaces.HkSq α 4 g := hIntZE.2
  calc |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, Work.FTS.H2.Hhard α f g z θ|
      = |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, Work.FTS.H2.ZE α f g z θ| := by
        rw [hmain, abs_neg]
    _ ≤ 10 * Mf * Work.Spaces.HkSq α 4 g := hbound

end Work.FTS.TransportS
