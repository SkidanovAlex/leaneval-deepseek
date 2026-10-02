/-
Copyright: subproject `Submission/Work/FSeed/` of `mandelbar_not_path_connected`.

# FSeed: the classical inputs, and the reduction to `Work.EL.RootParabolic`

The target of the area (`Submission/Work/FSeed/Main.lean`) is

  `∃ c, Nonempty (Work.EL.RootParabolic c)`

where `Work.EL.RootParabolic` is the structure declared in `Submission/Work/ELTop/Defs.lean`
(the input bundle the EL areas and the ELRig chain consume).  Following the contract
(`NOTES_LEAD_mandelbar_EL_F_contracts.md` §9.5 and §7.3, row `FSeed`), the route is

1. `c₁ ∈ closure (paramRay (371/1023)) ∖ paramRay (371/1023)` — a bounded parameter ray
   accumulating on the mandelbar.  This step is **unconditional**:
   `Work.FSeed.exists_paramRay_limit` / `exists_paramRay_limit_α₁_paramRay`
   (`Submission/Work/FSeed/ParamRayLimit.lean`), proved from `Work.Top.NakaneData` alone.
2. Goldberg–Milnor Lemma B.1: a ray landing at a *repelling* point is stable, so
   `R_{c₁}(371/1023)` cannot land at a repelling point; by the landing theorem (Milnor 18.10) it
   lands at a parabolic point.  This is the input `RepellingRayParamStable` below, shared with
   the `hθ` clause of the Top glue.  (Its *dynamical* form — stability of the landing under
   perturbation of the parameter at *every* nearby parameter — is false as stated, because for
   `c ∈ ∂M*` some nearby parameters lie outside `M*`, where `Work.Landing.landsAt` is impossible;
   it was unused and has been deleted.)
3. The classification of that parabolic cycle (odd period `5`, simple, `α₂` co-landing, wake) is
   carried out in `Submission/Work/FSeed/Classify.lean` from the classical local portrait
   `ParabolicLocalPortrait c 5` and the arithmetic of the portrait, using the fact (proved) that
   the multiplier of the second return map at an **odd**-period point is a non-negative real
   (`Work.Landing.Family.deriv_tsq_iterate_odd_real`).

## Provenance of `RootParabolicInput`

* `dyn` — Böttcher's theorem in the dynamical plane (`Work.ParamRays.DynBottcherHomeo`).
* `ray_limit` — the landing of the parameter ray `R(371/1023)` at the root of the non-real
  period-`5` component (MNS arXiv:1404.5031 §4, IM16 arXiv:1406.3428 Lemma 4.1,
  Hubbard–Schleicher arXiv:1209.1753 §3); step 1 above shows that such limit points exist.
* `odd_per` — at that parameter the ray `R_{c₁}(α₁)` lands (Douady–Hubbard) at a point `z₁` of
  **exact odd** period whose second-return multiplier is `1`: `Work.Landing.landsAt_repelling_or_parabolic`
  (Milnor 18.10 for odd periods, in the workspace) gives repelling-or-parabolic, Goldberg–Milnor
  Lemma B.1 excludes the repelling case, and `deriv_tsq_iterate_odd_real` supplies the realness
  that converts "not repelling, not attracting" into `multiplier2 = 1`.
* `portrait` — the ray count at the root point, **modulo `1`**: at most two ray angles land
  there.  Classical at the seed (interior of the root arc): Douady–Hubbard; Milnor 18.10;
  Goldberg–Milnor; MNS 1404.5031 Lemma 4.4(2); Mukherjee 2015.  It is *not* a general principle:
  at the cusps ending the root arc three rays land (HS §5), so the clause must not be read as a
  statement about every parabolic point.
* `simple` — `z₁` is not a cusp: `iteratedDeriv 2 (F c) z₁ ≠ 0`.  A per-parameter classical fact
  about the interior of the root arc (HS Prop. 2.5, Lemma 3.1; MNS Thm 1.2, Lemma 2.9, Thm 3.2;
  IM16 Thm 1.1, Cor. 5.2).
* `crit` — at the root of a hyperbolic component the critical orbit converges to the parabolic
  cycle (McMullen, *Complex Dynamics and Renormalization*, Thm 4.5; MNS §4).
* `wake` — Landing's `L-wake` export, in the form used by the EL areas
  (`Work.EL.wakeSide hN z₁ ((k-1) % 5)`).

Everything the area proves *besides* `RootParabolicInput`,
`RepellingRayParamStable` and `ParabolicLandingAtParamRay` is unconditional.
-/
import Submission.Work.FSeed.Defs
import Submission.Work.ELTop.Defs
import Submission.Work.ParamRays.DynNakane
import Submission.Work.Landing.Land.Landing

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Function
open scoped Topology

noncomputable section

namespace Work.FSeed

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-! ## The two classical inputs shared with the rest of the drive -/

/-- **Goldberg–Milnor Lemma B.1** (parameter form; the `hθ` clause of the Top glue): a parameter
at which the ray at angle `θ` lands at a repelling periodic point is not a limit point of the
parameter ray `R(θ)`. -/
def RepellingRayParamStable : Prop :=
  ∀ (c : ℂ) (k : ℕ) (y : ℂ) (θ : ℝ), Work.Landing.IsRepelling c k y →
    Work.Landing.landsAt c θ y → c ∉ closure (Work.ParamRays.paramRay θ)

/-- **The conclusion of step 2** (Milnor 18.10 together with Goldberg–Milnor Lemma B.1 and the
realness of the multiplier at a point of odd period): at a parameter `c` which is a limit point of
the parameter ray `R(θ)` and at which the *periodic* dynamical ray `R_c(θ)` lands, the landing
point is parabolic. -/
def ParabolicLandingAtParamRay : Prop :=
  ∀ (c : ℂ) (θ : ℝ), Work.Landing.IsPeriodicAngle θ →
    c ∈ closure (Work.ParamRays.paramRay θ) →
    ∀ z : ℂ, Work.Landing.landsAt c θ z → ∃ k : ℕ, Work.Landing.IsParabolic c k z

/-- **Step 2 of the FSeed route**, as a reduction between the two classical inputs: at a parameter
that is a limit point of the parameter ray `R(θ)`, the dynamical ray `R_c(θ)` cannot land at a
*repelling* periodic point. -/
theorem not_isRepelling_of_mem_closure_paramRay (hstable : RepellingRayParamStable) {c : ℂ}
    {θ : ℝ} (hc : c ∈ closure (Work.ParamRays.paramRay θ)) {k : ℕ} {y : ℂ}
    (hrep : Work.Landing.IsRepelling c k y) (hland : Work.Landing.landsAt c θ y) : False :=
  hstable c k y θ hrep hland hc

/-- **The `hθ` clause of the Top glue**, in the form in which it is consumed: if at the parameter
`c` the ray at angle `23/63` (`Work.Landing.paramAngle`) lands at a repelling periodic point, then
`c` is not a limit point of the parameter ray `R(23/63)`.  (The `23/63` ray cannot land at the
parabolic point of period `5`: its angle has period `6`, and `6 ∤ 2·5 = 10`.) -/
theorem not_mem_closure_paramRay_paramAngle (hstable : RepellingRayParamStable) {c y : ℂ}
    (hrep : ∃ k : ℕ, Work.Landing.IsRepelling c k y)
    (hland : Work.Landing.landsAt c Work.Landing.paramAngle y) :
    c ∉ closure (Work.ParamRays.paramRay Work.Landing.paramAngle) := by
  obtain ⟨k, hk⟩ := hrep
  exact hstable c k y Work.Landing.paramAngle hk hland

/-- **Step 2 of the route, in the form that justifies the field `odd_per`.**  If the periodic ray
`R_c(θ)` of **odd** period `k` lands at `z`, and `c` is a limit point of the parameter ray `R(θ)`,
then `z` is a parabolic point of period `k`:

* `Work.Landing.landsAt_repelling_or_parabolic` (Milnor 18.10 for odd periods, in the workspace)
  gives "repelling or parabolic" from the landing, the odd period and `AttractingCyclesInner`;
* Goldberg–Milnor Lemma B.1 (`RepellingRayParamStable`) excludes the repelling case, because `c`
  is a limit point of the parameter ray `R(θ)`.

This is how the field `odd_per` of `RootParabolicInput` is obtained classically at the root of the
non-real period-`5` component. -/
theorem isParabolic_of_landsAt_odd {c : ℂ} {θ : ℝ} {k : ℕ} {z : ℂ}
    (hstab : RepellingRayParamStable) (hgeo : Work.Landing.AttractingCyclesInner c)
    (hodd : Odd k) (hk : 0 < k) (hper : Work.Landing.PeriodicAngle θ k)
    (hland : Work.Landing.landsAt c θ z) (hc : c ∈ closure (Work.ParamRays.paramRay θ)) :
    Work.Landing.IsParabolic c k z := by
  rcases Work.Landing.landsAt_repelling_or_parabolic hland hper hk hodd hgeo with h | h
  · exact (hstab c k z θ h hland hc).elim
  · exact h

/-! ## The input bundle of the area -/

/-- **The classical input bundle of the FSeed area**: the data of the root-parabolic parameter of
the non-real period-`5` component, *before* the classification carried out in `Classify.lean`.

Compared with the structure `Work.EL.RootParabolic` this bundle

* asserts only that `z₁` lies on a cycle of **odd** period `k` whose second-return multiplier is
  `1` (`odd_per`), not that the period is `5`, and not the multiplier at period `5`;
* asserts only that the first root ray lands at `z₁` (`ray₁`), not that both do;
* asserts directly that `z₁` is not a cusp (`simple`), rather than deriving it from a ray count;

and instead carries the classical local portrait `LocalRayPortrait c z₁` of the point — the ray
count **modulo `1`** — from which the co-landing of `α₂` and the exactness of the period are
derived in `Classify.lean`.  The field `simple` is a *per-parameter* classical fact about the seed
(a point in the interior of the root arc), taken here as an input by design: the ray-theoretic
statement that would discharge it at a cusp costs 35–60K
(`NOTES_LEAD_mandelbar_seedsimple.md` §2, §5). -/
structure RootParabolicInput (c : ℂ) where
  /-- Böttcher's theorem in the dynamical plane. -/
  dyn : DynHomeo c
  /-- the characteristic parabolic point of the period-`5` cycle. -/
  z₁ : ℂ
  /-- `c` is a limit point of the parameter ray `R(α₁)`, and is not on it. -/
  ray_limit : c ∈ closure (Work.ParamRays.paramRay α₁) ∧ c ∉ Work.ParamRays.paramRay α₁
  /-- `z₁` lies on a cycle of **exact odd** period `k` whose second-return multiplier is `1`. -/
  odd_per : ∃ k : ℕ, Odd k ∧ (Tantibar c)^[k] z₁ = z₁ ∧
    (∀ j : ℕ, 0 < j → j < k → (Tantibar c)^[j] z₁ ≠ z₁) ∧
    Work.Landing.multiplier2 c k z₁ = 1
  /-- the first root ray lands at `z₁`. -/
  ray₁ : Work.Landing.landsAt c α₁ z₁
  /-- the classical local portrait of the point `z₁`, **modulo `1`**: at most two ray angles
  land at `z₁` (at the seed: exactly the two root rays; classical at the root-arc interior, not a
  general principle — at the cusps ending the root arc three rays land, HS §5). -/
  portrait : LocalRayPortrait c z₁
  /-- **`z₁` is a simple parabolic point** (not a cusp): the second derivative of the holomorphic
  second-return map `F c = (T_c)^[10]` does not vanish at `z₁`.
  Classical: the root arc of the period-5 component is a parabolic arc, i.e. a real-analytic family
  of *simple* parabolic parameters whose only limit points are its two end cusps (HS Prop. 2.5,
  Lemma 3.1; MNS Thm 1.2, Thm 3.2); there are finitely many cusps (MNS Lemma 2.9); the accumulation
  set of the parameter ray `R(α₁)` is contained in the closed root arc and contains a sub-arc of
  positive length (IM 1406.3428 Thm 1.1, Cor. 5.2; MNS Lemma 5.5–5.6).  Hence some limit point of
  `R(α₁)` is a non-cusp parameter of the root arc, which is the parameter this bundle describes. -/
  simple : iteratedDeriv 2 (F c) z₁ ≠ 0
  /-- the critical orbit converges to `z₁`, without hitting it. -/
  crit : Tendsto (fun n : ℕ => (F c)^[n] c) atTop (nhds z₁) ∧ ∀ n : ℕ, (F c)^[n] c ≠ z₁
  /-- the wake condition for the critical orbit (Landing's `L-wake` export), in the vocabulary of
  the EL areas. -/
  wake : ∀ k : ℕ, 1 ≤ k →
    (Tantibar c)^[k] 0 ∈ Work.EL.wakeSide (φ := Work.ParamRays.dynPhiOf c)
      (Work.ParamRays.dynNakane dyn) z₁ ((k - 1) % 5)

/-- **The FSeed hypothesis**: some parameter of the tricorn carries the classical
root-parabolic data of the non-real period-`5` component. -/
def FSeedInput : Prop := ∃ c : ℂ, Nonempty (RootParabolicInput c)

namespace RootParabolicInput

variable {c : ℂ}

/-- The dynamical Böttcher homeomorphism. -/
theorem dynHomeo (h : RootParabolicInput c) : DynHomeo c := h.dyn

/-- `c` is a limit point of the parameter ray `R(α₁)`. -/
theorem mem_closure_paramRay (h : RootParabolicInput c) :
    c ∈ closure (Work.ParamRays.paramRay α₁) := h.ray_limit.1

/-- `c` is not on the parameter ray `R(α₁)`. -/
theorem notMem_paramRay (h : RootParabolicInput c) :
    c ∉ Work.ParamRays.paramRay α₁ := h.ray_limit.2

/-- The odd-period parabolic condition. -/
theorem odd_period (h : RootParabolicInput c) :
    ∃ k : ℕ, Odd k ∧ (Tantibar c)^[k] h.z₁ = h.z₁ ∧
      (∀ j : ℕ, 0 < j → j < k → (Tantibar c)^[j] h.z₁ ≠ h.z₁) ∧
      Work.Landing.multiplier2 c k h.z₁ = 1 := h.odd_per

/-- The first root ray lands at `z₁`. -/
theorem landsAt_α₁ (h : RootParabolicInput c) : Work.Landing.landsAt c α₁ h.z₁ := h.ray₁

/-- The classical local portrait, **modulo `1`**: at most two ray angles land at `z₁`. -/
theorem portrait_two_rays (h : RootParabolicInput c) :
    ∀ θ θ' θ'' : ℝ, Work.Landing.landsAt c θ h.z₁ → Work.Landing.landsAt c θ' h.z₁ →
      Work.Landing.landsAt c θ'' h.z₁ →
      Int.fract θ = Int.fract θ' ∨ Int.fract θ = Int.fract θ'' ∨ Int.fract θ' = Int.fract θ'' :=
  h.portrait.two_rays

/-- **`z₁` is not a cusp**: the second derivative of the holomorphic second-return map
`F c = (T_c)^[10]` does not vanish at `z₁`.  This is the field `RootParabolicInput.simple`, a
classical per-parameter fact about the root-arc interior (`NOTES_LEAD_mandelbar_seedsimple.md`
§4.2). -/
theorem simple_z₁ (h : RootParabolicInput c) : iteratedDeriv 2 (F c) h.z₁ ≠ 0 := h.simple

/-- The critical orbit converges to `z₁`. -/
theorem tendsto_critOrbit (h : RootParabolicInput c) :
    Tendsto (fun n : ℕ => (F c)^[n] c) atTop (nhds h.z₁) := h.crit.1

/-- The critical orbit never hits `z₁`. -/
theorem critOrbit_ne (h : RootParabolicInput c) : ∀ n : ℕ, (F c)^[n] c ≠ h.z₁ := h.crit.2

/-- The wake condition for the `k`-th critical-orbit point. -/
theorem wake_of (h : RootParabolicInput c) (k : ℕ) (hk : 1 ≤ k) :
    (Tantibar c)^[k] 0 ∈ Work.EL.wakeSide (φ := Work.ParamRays.dynPhiOf c)
      (Work.ParamRays.dynNakane h.dyn) h.z₁ ((k - 1) % 5) := h.wake k hk

end RootParabolicInput

end Work.FSeed

end
