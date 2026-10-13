import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.H6Aux.R.Slots
import Submission.Work.FTS.StrongPersist.H6Aux.R.DthIbp
import Submission.Work.FTS.StrongPersist.H6Aux.R.WipLSelf
import Submission.Work.FTS.CoercivityFix.Basic
import Submission.Work.FTS.CoercivityFix.Coer1.IntFacts
import Submission.Work.FTS.CoercivityFix.Coer1.Estimates
import Submission.Work.FTS.StrongPersist.H6Aux.R.zw2_deriv_integrable
import Submission.Work.FTS.StrongPersist.H6Aux.R.dth_Phi1_wip_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `⟨𝓛̂u, u⟩_{w²σ} ≥ -(5/2)⟨u, u⟩_{w²σ}` for the angular exponent `q ∈ [0,2]`

This file proves

  `-(5/2)·∫∫ u² w² sin(2θ)^{-q} ≤ wip (Rhoq q) (Lhat u) u`

for `u` smooth on the open quadrant and `0 ≤ q ≤ 2`, from the three joint-integrability
hypotheses `u²ρ_q`, `(D_z u)·u·ρ_q`, `(D_θ u)·u·ρ_q` (`ρ_q = Rhoq q = w²sin(2θ)^{-q}`).

## Route

Write `𝓛̂ = 𝓛 - Transport` (`Lhat_eq`).  Then

* `wip ρ_q (𝓛u) u = ½∫∫ u²ρ_q` — the self-adjointness `WipLSelf` (the `z`-integration by
  parts `wip_Dz_ibp` with `∂_z(z w²) = ((z-3)/(1+z))w²`, valid under the same three
  integrability hypotheses, the third of which is *derived* here from `u²w²σ`
  (`zw2_deriv_integrable`));
* `wip ρ_q (Transport u) u = 3·wip (Φ₁σ) (D_θu) u` with `Φ₁ = w²/(1+z)` (pointwise algebra
  plus scalar homogeneity of `wip`);
* `wip (Φ₁σ) (D_θu) u ≤ ∫∫ u²ρ_q` — the `θ`-integration by parts `wip_Dth_ibp` gives
  `(q-1)∫_z Φ₁∫_θ cos(2θ)σu²`, and `|q-1| ≤ 1`, `|cos 2θ| ≤ 1`, `Φ₁ ≤ w²` give the bound
  (`dth_Phi1_wip_le`).

Adding up: `wip ρ_q (𝓛̂u) u ≥ ½A - 3A = -(5/2)A`.

## Note on the scratch file

`_probe_wl.lean` in this directory is a scratch copy used while `R.Slots` was being
refactored; nothing imports it.
-/
noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Aux.R

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- The angular weight `sin(2θ)^{-q}` (an abbreviation of `Coer1.sig`). -/
private abbrev sigQ (q : ℝ) : ℝ → ℝ := fun θ => (Real.sin (2 * θ)) ^ (-q)

/-- The `z`-only weight `Φ₁ = w²/(1+z)`. -/
private abbrev phiOne : ℝ → ℝ := fun z => (Work.Spaces.w z) ^ 2 / (1 + z)

/-- `wip` depends only on the pointwise product of its three arguments. -/
private theorem wip_int_congr {ρ₁ ρ₂ A₁ A₂ B₁ B₂ : ℝ → ℝ → ℝ}
    (h : ∀ z θ, A₁ z θ * B₁ z θ * ρ₁ z θ = A₂ z θ * B₂ z θ * ρ₂ z θ) :
    Work.Coercivity.wip ρ₁ A₁ B₁ = Work.Coercivity.wip ρ₂ A₂ B₂ := by
  rw [Work.Coercivity.wip, Work.Coercivity.wip]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => h z θ)

/-- `wip ρ u u` is the iterated integral of `u²ρ` (local copy of `SlotsBasic.wip_self_eq`). -/
private theorem wip_self_eq_local (ρ u : ℝ → ℝ → ℝ) :
    Work.Coercivity.wip ρ u u = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
      u z θ ^ 2 * ρ z θ := by
  rw [Work.Coercivity.wip]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
  ring

/-- `sin(2θ)^{-q} ≥ 0` on the closed angular interval. -/
private theorem sigQ_nonneg {q θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ sigQ q θ := by
  have h2 : 0 ≤ 2 * θ := by linarith [hθ.1]
  have h3 : 2 * θ ≤ Real.pi := by linarith [hθ.2, Real.pi_pos]
  exact Real.rpow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi h2 h3) _

/-- **The core estimate** in the normalisation `ρ_q = w²·sin(2θ)^{-q}`: the pairing of
`𝓛̂u` with `u` against `ρ_q` is bounded below by `-(5/2)` times the weighted `L²` mass. -/
private theorem wip_Lhat_ge_aux {u : ℝ → ℝ → ℝ} {q : ℝ}
    (hs : Work.FTS.EllipticEst.SmoothOpen u) (hq0 : 0 ≤ q) (hq2 : q ≤ 2)
    (hZ : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Spaces.Dz u z θ * u z θ
        * ((Work.Spaces.w z) ^ 2 * sigQ q θ)))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    (hT : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Spaces.Dth u z θ * u z θ
        * ((Work.Spaces.w z) ^ 2 * sigQ q θ)))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    (hU : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => u z θ * u z θ
        * ((Work.Spaces.w z) ^ 2 * sigQ q θ)))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    -(5 / 2) * (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        u z θ ^ 2 * ((Work.Spaces.w z) ^ 2 * sigQ q θ))
      ≤ Work.Coercivity.wip (fun z θ => (Work.Spaces.w z) ^ 2 * sigQ q θ)
          (Work.FTS.CoercivityFix.Lhat u) u := by
  -- ## 0. integrability normalisations
  have hσnn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ sigQ q θ := fun θ hθ => sigQ_nonneg hθ
  have hUsq : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => u z θ ^ 2 * (Work.Spaces.w z) ^ 2 * sigQ q θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    refine hU.congr ?_
    filter_upwards with p
    obtain ⟨z, θ⟩ := p
    simp only [Function.uncurry_apply_pair]
    ring
  have hZsq : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Spaces.Dz u z θ * u z θ
        * (Work.Spaces.w z) ^ 2 * sigQ q θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    refine hZ.congr ?_
    filter_upwards with p
    obtain ⟨z, θ⟩ := p
    simp only [Function.uncurry_apply_pair]
    ring
  have hTsq : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Spaces.Dth u z θ * u z θ
        * (Work.Spaces.w z) ^ 2 * sigQ q θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    refine hT.congr ?_
    filter_upwards with p
    obtain ⟨z, θ⟩ := p
    simp only [Function.uncurry_apply_pair]
    ring
  have hUu : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => u z θ * u z θ
        * (Work.Spaces.w z) ^ 2 * sigQ q θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    refine hU.congr ?_
    filter_upwards with p
    obtain ⟨z, θ⟩ := p
    simp only [Function.uncurry_apply_pair]
    ring
  -- ## 1. the derived `z`-weight integrability `u²·∂_z(z w²)·σ`
  have h3 : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => u z θ ^ 2
        * deriv (fun z' => z' * (Work.Spaces.w z') ^ 2) z * sigQ q θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    zw2_deriv_integrable (σ := sigQ q) hσnn hUsq
  -- ## 2. integrability of the `𝓛`- and `Transport`-pairings
  have hdiv : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => u z θ ^ 2 * (Work.Spaces.w z) ^ 2 * sigQ q θ / (1 + z)))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    Work.FTS.CoercivityFix.Coer1.integrableOn_div_one_add_Q hUsq
  have hL : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Coercivity.L u z θ * u z θ
        * ((Work.Spaces.w z) ^ 2 * sigQ q θ)))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    have hsum : MeasureTheory.IntegrableOn
        (Function.uncurry (fun z θ => u z θ ^ 2 * (Work.Spaces.w z) ^ 2 * sigQ q θ
          + (Work.Spaces.Dz u z θ * u z θ * (Work.Spaces.w z) ^ 2 * sigQ q θ)
          - 2 * (u z θ ^ 2 * (Work.Spaces.w z) ^ 2 * sigQ q θ / (1 + z))))
        (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
      (hUsq.add hZsq).sub (hdiv.const_mul 2)
    refine hsum.congr ?_
    filter_upwards with p
    obtain ⟨z, θ⟩ := p
    simp only [Function.uncurry_apply_pair, Work.Coercivity.L, Work.Spaces.Dz]
    ring
  have hTr : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Coercivity.Transport u z θ * u z θ
        * ((Work.Spaces.w z) ^ 2 * sigQ q θ)))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    have hdivT : MeasureTheory.IntegrableOn
        (Function.uncurry (fun z θ => Work.Spaces.Dth u z θ * u z θ
          * (Work.Spaces.w z) ^ 2 * sigQ q θ / (1 + z)))
        (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
      Work.FTS.CoercivityFix.Coer1.integrableOn_div_one_add_Q hTsq
    have h3m : MeasureTheory.IntegrableOn
        (Function.uncurry (fun z θ => 3 * (Work.Spaces.Dth u z θ * u z θ
          * (Work.Spaces.w z) ^ 2 * sigQ q θ / (1 + z))))
        (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := hdivT.const_mul 3
    refine h3m.congr ?_
    filter_upwards with p
    obtain ⟨z, θ⟩ := p
    simp only [Function.uncurry_apply_pair, Work.Coercivity.Transport]
    ring
  -- ## 3. the algebraic split `𝓛̂ = 𝓛 - Transport`
  have hsplit : Work.Coercivity.wip (fun z θ => (Work.Spaces.w z) ^ 2 * sigQ q θ)
        (Work.FTS.CoercivityFix.Lhat u) u
      = Work.Coercivity.wip (fun z θ => (Work.Spaces.w z) ^ 2 * sigQ q θ)
          (Work.Coercivity.L u) u
        - Work.Coercivity.wip (fun z θ => (Work.Spaces.w z) ^ 2 * sigQ q θ)
          (Work.Coercivity.Transport u) u := by
    have h := Work.FTS.CoercivityFix.Coer1.wip_sub_left
      (ρ := fun z θ => (Work.Spaces.w z) ^ 2 * sigQ q θ)
      (A := Work.Coercivity.L u) (B := Work.Coercivity.Transport u) (C := u) hL hTr
    rw [show Work.FTS.CoercivityFix.Lhat u
      = fun z θ => Work.Coercivity.L u z θ - Work.Coercivity.Transport u z θ from rfl]
    exact h
  -- ## 4. the `𝓛`-self pairing (`WipLSelf`)
  have hW : Work.Coercivity.wip (fun z θ => (Work.Spaces.w z) ^ 2 * sigQ q θ)
        (Work.Coercivity.L u) u
      = (1 / 2) * (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          u z θ ^ 2 * ((Work.Spaces.w z) ^ 2 * sigQ q θ)) :=
    WipLSelf (u := u) (σ := sigQ q) hs hUsq hZsq h3
  -- ## 5. the transport term is `3` times the `Φ₁`-weighted `D_θ`-pairing
  have hTr3 : Work.Coercivity.wip (fun z θ => (Work.Spaces.w z) ^ 2 * sigQ q θ)
        (Work.Coercivity.Transport u) u
      = 3 * Work.Coercivity.wip (fun z θ => phiOne z * sigQ q θ)
          (Work.Spaces.Dth u) u := by
    have h1 : Work.Coercivity.wip (fun z θ => (Work.Spaces.w z) ^ 2 * sigQ q θ)
          (Work.Coercivity.Transport u) u
        = Work.Coercivity.wip (fun z θ => (Work.Spaces.w z) ^ 2 * sigQ q θ)
            (fun z θ => 3 * (Work.Spaces.Dth u z θ / (1 + z))) u := by
      refine wip_int_congr (fun z θ => ?_)
      simp only [Work.Coercivity.Transport]
      ring
    have h2 : Work.Coercivity.wip (fun z θ => (Work.Spaces.w z) ^ 2 * sigQ q θ)
          (fun z θ => 3 * (Work.Spaces.Dth u z θ / (1 + z))) u
        = 3 * Work.Coercivity.wip (fun z θ => (Work.Spaces.w z) ^ 2 * sigQ q θ)
            (fun z θ => Work.Spaces.Dth u z θ / (1 + z)) u :=
      Work.Coercivity.wip_smul_left
    have h3' : Work.Coercivity.wip (fun z θ => (Work.Spaces.w z) ^ 2 * sigQ q θ)
          (fun z θ => Work.Spaces.Dth u z θ / (1 + z)) u
        = Work.Coercivity.wip (fun z θ => phiOne z * sigQ q θ)
            (Work.Spaces.Dth u) u := by
      refine wip_int_congr (fun z θ => ?_)
      simp only [phiOne]
      ring
    rw [h1, h2, h3']
  -- ## 6. the `D_θ`-pairing bound
  have hDth : Work.Coercivity.wip (fun z θ => phiOne z * sigQ q θ)
        (Work.Spaces.Dth u) u
      ≤ Work.Coercivity.wip (fun z θ => (Work.Spaces.w z) ^ 2 * sigQ q θ) u u :=
    dth_Phi1_wip_le (q := q) hs hq0 hq2 hTsq hUu
  -- ## 7. assembly
  have hkey : Work.Coercivity.wip (fun z θ => (Work.Spaces.w z) ^ 2 * sigQ q θ)
        (Work.FTS.CoercivityFix.Lhat u) u
      = (1 / 2) * (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          u z θ ^ 2 * ((Work.Spaces.w z) ^ 2 * sigQ q θ))
        - 3 * Work.Coercivity.wip (fun z θ => phiOne z * sigQ q θ)
            (Work.Spaces.Dth u) u := by
    rw [hsplit, hW, hTr3]
  have hself : Work.Coercivity.wip (fun z θ => (Work.Spaces.w z) ^ 2 * sigQ q θ) u u
      = (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          u z θ ^ 2 * ((Work.Spaces.w z) ^ 2 * sigQ q θ)) :=
    wip_self_eq_local _ _
  have hle : Work.Coercivity.wip (fun z θ => phiOne z * sigQ q θ) (Work.Spaces.Dth u) u
      ≤ (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          u z θ ^ 2 * ((Work.Spaces.w z) ^ 2 * sigQ q θ)) := by
    rw [← hself]
    exact hDth
  rw [hkey]
  linarith [hle]

theorem WipLhatGe {u : ℝ → ℝ → ℝ} {q : ℝ} (hs : Work.FTS.EllipticEst.SmoothOpen u)
    (hq0 : 0 ≤ q) (hq2 : q ≤ 2)
    (hZ : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Spaces.Dz u z θ * u z θ
        * Work.FTS.StrongPersist.H6Aux.R.Rhoq q z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    (hT : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Spaces.Dth u z θ * u z θ
        * Work.FTS.StrongPersist.H6Aux.R.Rhoq q z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    (hU : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => u z θ * u z θ
        * Work.FTS.StrongPersist.H6Aux.R.Rhoq q z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    -(5 / 2) * (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        u z θ ^ 2 * Work.FTS.StrongPersist.H6Aux.R.Rhoq q z θ)
      ≤ Work.Coercivity.wip (Work.FTS.StrongPersist.H6Aux.R.Rhoq q)
          (Work.FTS.CoercivityFix.Lhat u) u := by
  have hZw : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Spaces.Dz u z θ * u z θ
        * ((Work.Spaces.w z) ^ 2 * sigQ q θ)))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    refine hZ.congr ?_
    filter_upwards with p
    obtain ⟨z, θ⟩ := p
    simp only [Function.uncurry_apply_pair, Work.FTS.StrongPersist.H6Aux.R.Rhoq,
      Work.FTS.CoercivityFix.Coer1.Rho, Work.FTS.CoercivityFix.Coer1.sig, sigQ]
  have hTw : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Spaces.Dth u z θ * u z θ
        * ((Work.Spaces.w z) ^ 2 * sigQ q θ)))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    refine hT.congr ?_
    filter_upwards with p
    obtain ⟨z, θ⟩ := p
    simp only [Function.uncurry_apply_pair, Work.FTS.StrongPersist.H6Aux.R.Rhoq,
      Work.FTS.CoercivityFix.Coer1.Rho, Work.FTS.CoercivityFix.Coer1.sig, sigQ]
  have hUw : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => u z θ * u z θ
        * ((Work.Spaces.w z) ^ 2 * sigQ q θ)))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    refine hU.congr ?_
    filter_upwards with p
    obtain ⟨z, θ⟩ := p
    simp only [Function.uncurry_apply_pair, Work.FTS.StrongPersist.H6Aux.R.Rhoq,
      Work.FTS.CoercivityFix.Coer1.Rho, Work.FTS.CoercivityFix.Coer1.sig, sigQ]
  have hρeq : (fun z θ : ℝ => (Work.Spaces.w z) ^ 2 * sigQ q θ)
      = Work.FTS.StrongPersist.H6Aux.R.Rhoq q := by
    funext z θ
    simp only [sigQ, Work.FTS.StrongPersist.H6Aux.R.Rhoq,
      Work.FTS.CoercivityFix.Coer1.Rho, Work.FTS.CoercivityFix.Coer1.sig]
  have hAeq : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        u z θ ^ 2 * Work.FTS.StrongPersist.H6Aux.R.Rhoq q z θ)
      = (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        u z θ ^ 2 * ((Work.Spaces.w z) ^ 2 * sigQ q θ)) := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
    simp only [sigQ, Work.FTS.StrongPersist.H6Aux.R.Rhoq,
      Work.FTS.CoercivityFix.Coer1.Rho, Work.FTS.CoercivityFix.Coer1.sig]
  rw [hAeq, ← hρeq]
  exact wip_Lhat_ge_aux hs hq0 hq2 hZw hTw hUw

end Work.FTS.StrongPersist.H6Aux.R
