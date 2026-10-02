/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FlowerGlue2 team
-/
import Submission.Work.FlowerGlue2.SymmDeriv_tricorn
import Submission.Work.FlowerGlue2.SplitPhase_normalForm

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# `Work.FlowerGlue2.L0` — the symmetry package of the parameter normal form, under its final names

`Submission/Work/NOTES_LEAD_mandelbar_implosion.md` §3.1 (L0) asks for six facts about the
normal form on the implosion side.  They are proved in the two files imported here
(`SymmDeriv_tricorn.lean`: the structural facts about `gtc c = (T_c)^[5]`;
`SplitPhase_normalForm.lean`: the split jets, the conjugacy of the two germ values, the `O(λ²)`
bound on `Im τ`, and the two statements about `τ_{c₀}`).  This file exposes them under the names
of the design note, unconditionally, so that a caller never has to instantiate the bundled
hypotheses again.

## Main results

* `Work.FlowerGlue2.gtc_conj_comp`, `Work.FlowerGlue2.deriv_Ft_swap`;
* `Work.FlowerGlue2.hasDerivAt_Ft_split`, `Work.FlowerGlue2.h_split_conj`;
* `Work.FlowerGlue2.im_tau_le`;
* **`Work.FlowerGlue2.tau_c₀`** — `P.h c₀ 0 = 1`, the chart-matching input of
  `Work.FlowerGlue2.exists_refCoord_P`;
* `Work.FlowerGlue2.tendsto_tau_phase` — `(π/λ_c)‖τ_c − 1‖ → 0`.
-/

open scoped Topology
open Filter Set Metric

set_option maxHeartbeats 1000000

namespace Work.FlowerGlue2

open Work.PARIMPL (ParNormal Ft gtc)

noncomputable section

variable {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}

/-- `gtc c = star ∘ Q` with `Q` a holomorphic polynomial: the antiholomorphic nature of the
fifth iterate of the tricorn map. -/
theorem gtc_conj_comp (c : ℂ) :
    ∃ Q : ℂ → ℂ, Differentiable ℂ Q ∧ ∀ z : ℂ, gtc c z = star (Q z) :=
  SymmDeriv_tricorn.1 c

/-- **The multipliers of a `gtc`-swapped pair are conjugate.**  `Ft c = gtc c ∘ gtc c`, and the
informal chain rule for `star ∘ Q` gives `deriv (Ft c) q = star (deriv (Ft c) p)` whenever
`gtc c` swaps `p` and `q`. -/
theorem deriv_Ft_swap {c p q : ℂ} (hpq : gtc c p = q) (hqp : gtc c q = p) :
    deriv (Ft c) q = star (deriv (Ft c) p) :=
  SymmDeriv_tricorn.2 c p q hpq hqp

/-- **L0.2.**  The derivative of the second return map at the two split fixed points of the chart
is `1 + 2(σ a)h(σ a)`, computed from the chart conjugacy and continuity of the germ alone. -/
theorem hasDerivAt_Ft_split (P : ParNormal d) {c : ℂ} (hc : c ∈ P.Nm) (hr : P.lam c < P.r)
    (σ : ℂ) (hσ : σ = 1 ∨ σ = -1) :
    HasDerivAt (Ft c) (1 + 2 * (σ * P.a c) * P.h c (σ * P.a c))
      (P.m c + P.s c * (σ * P.a c)) :=
  splitPhase_hasDerivAt P hc hr σ hσ

/-- **L0.3.**  The germ values at the two split fixed points are conjugate. -/
theorem h_split_conj (P : ParNormal d) {c : ℂ} (hc : c ∈ P.Nm) (hr : P.lam c < P.r) :
    P.h c (P.a c) = star (P.h c (-P.a c)) :=
  splitPhase_h_split_conj P hc hr (fun σ hσ => hasDerivAt_Ft_split P hc hr σ hσ)
    SymmDeriv_tricorn.2

/-- **L0.4.**  `|Im τ_c| ≤ A λ_c²` and `|Im h₁ c| ≤ A λ_c`. -/
theorem im_tau_le (P : ParNormal d) {c : ℂ} (hc : c ∈ P.Nm) (hr : P.lam c < P.r) :
    |(P.h c 0).im| ≤ P.A * P.lam c ^ 2 ∧ |(P.h1 c).im| ≤ P.A * P.lam c :=
  splitPhase_im_bounds P hc hr (h_split_conj P hc hr)

/-- The imaginary part of the germ constant, which is all that L0.4 and L0.5 need. -/
theorem im_tau_le' (P : ParNormal d) {c : ℂ} (hc : c ∈ P.Nm) (hr : P.lam c < P.r) :
    |(P.h c 0).im| ≤ P.A * P.lam c ^ 2 :=
  (im_tau_le P hc hr).1

/-- **L0.5 (a).**  `τ_{c₀} = P.h c₀ 0 = 1`: the rotation has disappeared at the parabolic
parameter.  This is the hypothesis `hτ` of the chart-consistency lemma
`Work.FlowerGlue2.exists_refCoord_P`. -/
theorem tau_c₀ (P : ParNormal d) : P.h c₀ 0 = 1 :=
  splitPhase_tau_c0 P (fun c hc hr => im_tau_le' P hc hr)

/-- At the parabolic parameter the correction constant of the approximate Écalle coordinate is
`κ₀ = 1 - h₁`: this is the identification that turns `approxCoord (P.κ c₀)` into
`approxCoord (1 - a_f)` in the chart matching, and `approxCoordRep (P.κ c₀)` into the model
coordinate of the repelling side. -/
theorem kappa_eq_one_sub_h1 (P : ParNormal d) (hτ : P.h c₀ 0 = 1) :
    P.κ c₀ = 1 - P.h1 c₀ := by
  obtain ⟨-, hκ⟩ := P.κ_eq c₀ (mem_ball_self P.hρ₀)
  rw [hτ] at hκ
  rw [hκ]
  ring

/-- **L0.5 (b).**  `(π/λ_c)‖τ_c − 1‖ → 0` along the implosion side; this is what makes the
`≈ π/λ` transit steps sum to `k + o(1)`. -/
theorem tendsto_tau_phase (P : ParNormal d) :
    Tendsto (fun c => (Real.pi / P.lam c) * ‖P.h c 0 - 1‖) (𝓝[P.Nm] c₀) (𝓝 0) :=
  splitPhase_tendsto_tau_phase P (fun c hc hr => im_tau_le' P hc hr)

end

end Work.FlowerGlue2
