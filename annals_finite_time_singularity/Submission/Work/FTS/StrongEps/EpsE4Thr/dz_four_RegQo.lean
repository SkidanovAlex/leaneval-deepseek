/-
# `dz_four_RegQo` — the `D_z`-clause of the level-four coercivity on the **open** class

`Work.FTS.CoercivityFix.Assembly.V_bounds.dz_four` proves, on the frozen class `RegQ α 5`,

  `|IP4 … α (D_z f) f| ≤ Cdz · |f|²_{ℋ⁴}`,

one of the three comparison clauses of the level-four coercivity.  The frozen proof cannot be
run along the route, because `RegQ` contains `SmoothQuad` (which the projected mollified slice
does not satisfy, `not_smoothQuad_Pz_Jeps`).  This file supplies the open-class version
`dz_four_RegQo`: the same statement with `RegQo α 5` in place of `RegQ α 5`.

## The route

The frozen proof is a three-fold recursion on the `D_z`-clause
(`Assembly/V_bounds.dz_step`), starting from the base estimate

  `|H1IP α (D_z v) v| ≤ 10²² · |v|²_{ℋ¹}`   on `RegQ α 2`

(whose proof is the `z`-integration by parts of §6, in its integrated form
`⟨𝓛u, u⟩_{w²σ} = ½⟨u,u⟩_{w²σ}`).  Each level of the recursion raises the required regularity
by one, which is exactly the depth that `RegQ α 5` allows.

The port replaces:

* the two derivative ports `QuadPorts.RegQ_dth`/`RegQ_dz` by their open-class counterparts
  `regQo_dth_dz` (already available);
* the one-sided norm comparison `normSub_Q` by `normSub_SO` (below), whose `D_z`-half is the
  finite-order open-quadrant estimate `Transfer.HkSq_Dz_le_Q0Sm`;
* the a.e. congruence of the partial pairings `Comm2_levels` by the *membership-free*
  congruence `IPGen.Comm2o*` on the open quadrant (`Congr` field), together with the
  pointwise Clairaut identity `D_θ(D_z v) = D_z(D_θ v)` on the open quadrant — available from
  `SmoothOpen` alone (`dzFour_Dth_Dz_comm_Qd`);
* the base estimate `H1IP_Dz_le_one` by its open-class analogue `dzFour_H1IP_Dz_le_one_SO`,
  whose `z`-integration-by-parts package and integrability bundle are the open-class
  structures `Coer1SO.ZIBPO` / `Coer1SO.IP2O`.

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`
(`#print axioms Work.FTS.StrongEps.EpsE4Thr.dz_four_RegQo`).

*Housekeeping.*  `Submission/Work/FTS/StrongEps/EpsE4Thr/_tmp_dzfour_test.lean` is a retired
scratch harness of this development (it replay-adds nothing: it is a renamed copy of the same
assembly, kept because files are never deleted in this workspace).  The three supporting
modules are `Submission/Work/FTS/CoercivityFix/Coer1SO/{Defs,zibpO_of,wip_Dz_self_le_SO,IP2O_of}.lean`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.EpsE4Thr.OpenClass
import Submission.Work.FTS.StrongEps.EpsE4Thr.regQo_dth_dz
import Submission.Work.FTS.CoercivityFix.Assembly.V_bounds
import Submission.Work.FTS.StrongPersist.IP6_lo_coeffs
import Submission.Work.FTS.CoercivityFix.Transfer.HkSq_Dz_le_Q0Sm
import Submission.Work.FTS.CoercivityFix.Coer1SO.Defs
import Submission.Work.FTS.CoercivityFix.Coer1SO.zibpO_of
import Submission.Work.FTS.CoercivityFix.Coer1SO.wip_Dz_self_le_SO
import Submission.Work.FTS.CoercivityFix.Coer1SO.IP2O_of
import Submission.Work.FTS.CoercivityFix.Coer1T.SlotsDzGam
import Submission.Work.FTS.IPGen.IP4Add
import Submission.Work.FTS.CoercivityStep.Norm.HkSq_mono_le
import Submission.Work.FTS.CoercivityStep.Norm.HkSq_Dth_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The one-sided norm comparison of the three slots, in the open class -/

/-- **The open-class `normSub`**: for `f` of class `SmoothOpen` and `HkMem α (n+1)`, the
level-`n` norms of the three slots `f`, `D_θ f`, `D_z f` are dominated by the level-`(n+1)`
norm of `f`.  This is `Assembly.V_bounds.normSub_Q` with the `D_z`-half taken from the
finite-order open-quadrant estimate `Transfer.HkSq_Dz_le_Q0Sm` (the two other halves are
smoothness-free). -/
theorem dzFour_normSub_SO (α : ℝ) (hα : 0 < α) (n : ℕ) :
    ∀ f : Fn, Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α (n + 1) f →
      Work.Spaces.HkSq α n f ≤ Work.Spaces.HkSq α (n + 1) f
        ∧ Work.Spaces.HkSq α n (Work.Spaces.Dth f) ≤ Work.Spaces.HkSq α (n + 1) f
        ∧ Work.Spaces.HkSq α n (Work.Spaces.Dz f) ≤ Work.Spaces.HkSq α (n + 1) f := by
  intro f hsm hmem
  exact ⟨Work.FTS.CoercivityStep.Norm.HkSq_mono_le α (Nat.le_succ n) hmem,
    Work.FTS.CoercivityStep.Norm.HkSq_Dth_le α hα n hmem,
    Work.FTS.CoercivityFix.Transfer.HkSq_Dz_le_Q0Sm α n
      (Work.FTS.StrongPersist.q0Sm_of_smoothOpen hsm (n + 1)) hmem⟩

/-! ## Clairaut on the open quadrant -/

/-- `D_z` and `D_θ` commute at every point of the open quadrant, for a function which is
`C^∞` there: the derivatives are local and the point is interior to `Q0`, so that
`C²`-Schwarz applies.  (Only the *open* quadrant is needed, which is exactly the domain of
`SmoothOpen`; the frozen `Assembly.Dth_Dz_comm_mem` used `SmoothQuad` and had to treat the
boundary points `z = 0`, `sin 2θ = 0` separately.) -/
theorem dzFour_Dth_Dz_comm_Qd {v : Fn} (hs : Work.FTS.EllipticEst.SmoothOpen v) :
    ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Work.Spaces.Dth (Work.Spaces.Dz v) z θ = Work.Spaces.Dz (Work.Spaces.Dth v) z θ := by
  intro z θ hzθ
  have hz : 0 < z := hzθ.1
  have hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2) := hzθ.2
  have hmem : (z, θ) ∈ Work.FTS.EllipticEst.Q0 := ⟨hz, hθ⟩
  have hcd : ContDiffAt ℝ 2 (Function.uncurry v) (z, θ) :=
    (hs.forall 2).contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hmem)
  exact (Work.Spaces.Dz_Dth_comm hcd).symm

/-! ## One step of the `D_z`-clause recursion, on the open class -/

/-- **One step of the `D_z`-clause recursion, on the open class** — the `RegQo` analogue of
`Assembly.dz_step`.  If the *first slot* pairing `⟨IP (D_z v), v⟩` is bounded by
`D·|v|²_{ℋ^{n+1}}` on `RegQo α (n+2)`, then the corresponding pairing of `HkIPStep c₁ c₂ IP` is
bounded by `3·D·max 1 (max c₁ c₂)` times the level-`(n+2)` norm on `RegQo α (n+3)`.

The only structural inputs are the open-class derivative ports (`regQo_dth_dz`), the open-class
one-sided norm comparison (`dzFour_normSub_SO`) and the pointwise commutation
`D_θ(D_z v) = D_z(D_θ v)` on the open quadrant (`dzFour_Dth_Dz_comm_Qd`), used through the
membership-free congruence of `IP` in its first argument. -/
theorem dzFour_dz_step_SO {α : ℝ} (hα : 0 < α) {n : ℕ}
    {IP : Fn → Fn → ℝ} {c₁ c₂ D : ℝ} (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hD : 0 < D)
    (hcongr : ∀ f f' g : Fn,
      (∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd → f z θ = f' z θ) → IP f g = IP f' g)
    (h : ∀ v : Fn, RegQo α (n + 2) v →
      |IP (Work.Spaces.Dz v) v| ≤ D * Work.Spaces.HkSq α (n + 1) v) :
    ∀ v : Fn, RegQo α (n + 3) v →
      |Work.Coercivity.HkIPStep c₁ c₂ IP (Work.Spaces.Dz v) v|
        ≤ (3 * D * max 1 (max c₁ c₂)) * Work.Spaces.HkSq α (n + 2) v := by
  intro v hv
  have hv2 : RegQo α (n + 2) v := regQo_mono (by omega) hv
  have hdth : RegQo α (n + 2) (Work.Spaces.Dth v) := (regQo_dth_dz hα (n := n + 2) hv).1
  have hdz : RegQo α (n + 2) (Work.Spaces.Dz v) := (regQo_dth_dz hα (n := n + 2) hv).2
  have h0 := h v hv2
  have h1 := h (Work.Spaces.Dth v) hdth
  have h2 := h (Work.Spaces.Dz v) hdz
  -- the commutation, transported to the congruence class of `IP`
  have hcomm := dzFour_Dth_Dz_comm_Qd hv2.1
  have hcg := hcongr (Work.Spaces.Dth (Work.Spaces.Dz v))
    (Work.Spaces.Dz (Work.Spaces.Dth v)) (Work.Spaces.Dth v) hcomm
  obtain ⟨hs0, hs1, hs2⟩ := dzFour_normSub_SO α hα (n + 1) v hv2.1 hv2.2.1
  have hB : 0 ≤ Work.Spaces.HkSq α (n + 2) v := Work.Spaces.HkSq_nonneg α (n + 2) v
  have e0 : |IP (Work.Spaces.Dz v) v| ≤ D * Work.Spaces.HkSq α (n + 2) v :=
    le_trans h0 (mul_le_mul_of_nonneg_left hs0 hD.le)
  have e1 : |IP (Work.Spaces.Dz (Work.Spaces.Dth v)) (Work.Spaces.Dth v)|
      ≤ D * Work.Spaces.HkSq α (n + 2) v :=
    le_trans h1 (mul_le_mul_of_nonneg_left hs1 hD.le)
  have e2 : |IP (Work.Spaces.Dz (Work.Spaces.Dz v)) (Work.Spaces.Dz v)|
      ≤ D * Work.Spaces.HkSq α (n + 2) v :=
    le_trans h2 (mul_le_mul_of_nonneg_left hs2 hD.le)
  rw [Work.Coercivity.HkIPStep, hcg]
  have htri : |IP (Work.Spaces.Dz v) v
        + c₁ * IP (Work.Spaces.Dz (Work.Spaces.Dth v)) (Work.Spaces.Dth v)
        + c₂ * IP (Work.Spaces.Dz (Work.Spaces.Dz v)) (Work.Spaces.Dz v)|
      ≤ |IP (Work.Spaces.Dz v) v|
        + c₁ * |IP (Work.Spaces.Dz (Work.Spaces.Dth v)) (Work.Spaces.Dth v)|
        + c₂ * |IP (Work.Spaces.Dz (Work.Spaces.Dz v)) (Work.Spaces.Dz v)| :=
    Work.FTS.CoercivityFix.Assembly.abs_lin3_coef c₁ c₂ hc₁ hc₂ _ _ _
  refine le_trans htri ?_
  have hm1 : (1 : ℝ) ≤ max 1 (max c₁ c₂) := le_max_left _ _
  have hm2 : c₁ ≤ max 1 (max c₁ c₂) := le_trans (le_max_left _ _) (le_max_right _ _)
  have hm3 : c₂ ≤ max 1 (max c₁ c₂) := le_trans (le_max_right _ _) (le_max_right _ _)
  have hcomb : |IP (Work.Spaces.Dz v) v|
        + c₁ * |IP (Work.Spaces.Dz (Work.Spaces.Dth v)) (Work.Spaces.Dth v)|
        + c₂ * |IP (Work.Spaces.Dz (Work.Spaces.Dz v)) (Work.Spaces.Dz v)|
      ≤ (3 * D * max 1 (max c₁ c₂)) * Work.Spaces.HkSq α (n + 2) v := by
    have hc1 : c₁ * |IP (Work.Spaces.Dz (Work.Spaces.Dth v)) (Work.Spaces.Dth v)|
        ≤ c₁ * (D * Work.Spaces.HkSq α (n + 2) v) := mul_le_mul_of_nonneg_left e1 hc₁.le
    have hc2 : c₂ * |IP (Work.Spaces.Dz (Work.Spaces.Dz v)) (Work.Spaces.Dz v)|
        ≤ c₂ * (D * Work.Spaces.HkSq α (n + 2) v) := mul_le_mul_of_nonneg_left e2 hc₂.le
    have hsum : |IP (Work.Spaces.Dz v) v|
        + c₁ * |IP (Work.Spaces.Dz (Work.Spaces.Dth v)) (Work.Spaces.Dth v)|
        + c₂ * |IP (Work.Spaces.Dz (Work.Spaces.Dz v)) (Work.Spaces.Dz v)|
        ≤ D * Work.Spaces.HkSq α (n + 2) v
          + c₁ * (D * Work.Spaces.HkSq α (n + 2) v)
          + c₂ * (D * Work.Spaces.HkSq α (n + 2) v) := by
      linarith [e0, hc1, hc2]
    refine le_trans hsum ?_
    have hcoef : 1 + c₁ + c₂ ≤ 3 * max 1 (max c₁ c₂) := by linarith [hm1, hm2, hm3]
    have hDH : 0 ≤ D * Work.Spaces.HkSq α (n + 2) v := mul_nonneg hD.le hB
    calc D * Work.Spaces.HkSq α (n + 2) v
          + c₁ * (D * Work.Spaces.HkSq α (n + 2) v)
          + c₂ * (D * Work.Spaces.HkSq α (n + 2) v)
        = (1 + c₁ + c₂) * (D * Work.Spaces.HkSq α (n + 2) v) := by ring
      _ ≤ (3 * max 1 (max c₁ c₂)) * (D * Work.Spaces.HkSq α (n + 2) v) :=
          mul_le_mul_of_nonneg_right hcoef hDH
      _ = (3 * D * max 1 (max c₁ c₂)) * Work.Spaces.HkSq α (n + 2) v := by ring
  exact hcomb

/-! ## The base estimate of the `D_z`-clause, on the open class -/

/-- **The base estimate of the `D_z`-clause on the open class.**  On `RegQo α 2` the pairing
of the first slot of `H1IP` with `D_z v` against `v` is dominated by the level-`1` norm of
`v`: the `z`-integration by parts `Coer1SO.wip_Dz_self_le_SO` converts each of the four
pairings into a square of a level-`1` slot.  This is `Assembly.H1IP_Dz_le_one` with the
smoothness weakened from `SmoothQuad` to `SmoothOpen`: the integrability certificates come
from `Coer1SO.IP2O_of` and the `z`-IBP packages from `Coer1SO.zibpO_of`. -/
theorem dzFour_H1IP_Dz_le_one_SO (α : ℝ) (hα : 0 < α) {v : Fn} (hv : RegQo α 2 v) :
    |Work.Coercivity.H1IP α (Work.Spaces.Dz v) v| ≤ (10 : ℝ) ^ 22 * Work.Spaces.HkSq α 1 v := by
  obtain ⟨hs, hm, hb⟩ := hv
  have hp := Work.FTS.CoercivityFix.Coer1SO.IP2O_of α hα hs hm
  have hmem1 : Work.Spaces.HkMem α 1 v :=
    Work.FTS.OpenPkg.HkMem_mono_open hs 1 (by norm_num) hm
  have hηnn : ∀ θ ∈ Work.Spaces.Iθ,
      0 ≤ Work.FTS.CoercivityFix.Coer1.sig Work.Spaces.eta θ :=
    fun θ hθ => Real.rpow_nonneg (Work.FTS.CoercivityFix.Coer1.sin_nonneg_of_mem_Iθ hθ) _
  have hγnn : ∀ θ ∈ Work.Spaces.Iθ,
      0 ≤ Work.FTS.CoercivityFix.Coer1.sig (Work.Spaces.gam α) θ :=
    fun θ hθ => Real.rpow_nonneg (Work.FTS.CoercivityFix.Coer1.sin_nonneg_of_mem_Iθ hθ) _
  have hcomm : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      Work.Spaces.Dth (Work.Spaces.Dz v) z θ = Work.Spaces.Dz (Work.Spaces.Dth v) z θ :=
    hp.dzDthComm.mono (fun _ hz => hz.mono (fun _ hθ => hθ.symm))
  -- the identifications of the boundary traces of the three functions
  have hm0 : Work.Spaces.mixed 0 0 v = v := by
    simp only [Work.Spaces.mixed, Work.Spaces.DzIter_zero, Work.Spaces.DthIter_zero]
  have hmDz : Work.Spaces.mixed 1 0 v = Work.Spaces.Dz v := by
    simp only [Work.Spaces.mixed, Work.Spaces.DthIter_zero, Work.Spaces.DzIter_succ,
      Work.Spaces.DzIter_zero]
  have hmDth : Work.Spaces.mixed 0 1 v = Work.Spaces.Dth v := by
    simp only [Work.Spaces.mixed, Work.Spaces.DzIter_zero, Work.Spaces.DthIter_succ,
      Work.Spaces.DthIter_zero]
  -- the three `z`-integration-by-parts packages
  have hzibp_v : Work.FTS.CoercivityFix.Coer1SO.ZIBPO v :=
    Work.FTS.CoercivityFix.Coer1SO.zibpO_of hs
      (fun θ hθ => by simpa only [hm0] using ((hb 0 0 (by norm_num)).1 θ hθ).1)
      (fun θ hθ => by simpa only [hm0] using ((hb 0 0 (by norm_num)).1 θ hθ).2)
      (hp.sqDzOne_zero.congr (MeasureTheory.ae_restrict_of_forall_mem
        (measurableSet_Ici.prod measurableSet_Icc) (fun p _ => by
          rcases p with ⟨z, θ⟩
          simp only [Function.uncurry_apply_pair]
          ring)))
      hp.intL_f_one
  have hzibp_Dz : Work.FTS.CoercivityFix.Coer1SO.ZIBPO (Work.Spaces.Dz v) :=
    Work.FTS.CoercivityFix.Coer1SO.zibpO_of hs.Dz
      (fun θ hθ => by simpa only [hmDz] using ((hb 0 1 (by norm_num)).1 θ hθ).1)
      (fun θ hθ => by simpa only [hmDz] using ((hb 0 1 (by norm_num)).1 θ hθ).2)
      (hp.sqDzOne_one.congr (MeasureTheory.ae_restrict_of_forall_mem
        (measurableSet_Ici.prod measurableSet_Icc) (fun p _ => by
          rcases p with ⟨z, θ⟩
          simp only [Function.uncurry_apply_pair]
          ring)))
      hp.intL_Dz_one
  have hzibp_Dth : Work.FTS.CoercivityFix.Coer1SO.ZIBPO (Work.Spaces.Dth v) :=
    Work.FTS.CoercivityFix.Coer1SO.zibpO_of hs.Dth
      (fun θ hθ => by simpa only [hmDth] using ((hb 1 0 (by norm_num)).1 θ hθ).1)
      (fun θ hθ => by simpa only [hmDth] using ((hb 1 0 (by norm_num)).1 θ hθ).2)
      (hp.sqDthOne.congr (MeasureTheory.ae_restrict_of_forall_mem
        (measurableSet_Ici.prod measurableSet_Icc) (fun p _ => by
          rcases p with ⟨z, θ⟩
          simp only [Function.uncurry_apply_pair]
          ring)))
      hp.intL_Dth_one
  -- the four pairings, in the `Rho`-normalisation
  have b1 := Work.FTS.CoercivityFix.Coer1SO.wip_Dz_self_le_SO hzibp_Dz hηnn
      (Work.FTS.CoercivityFix.Coer1.to_h1 hp.sqDzEta_one)
      (Work.FTS.CoercivityFix.Coer1.integrableOn_congr_fun_Q hp.intL_Dz_eta
        (fun z θ => by simp only [Work.FTS.CoercivityFix.Coer1.Rho]; ring))
  have b2 := Work.FTS.CoercivityFix.Coer1SO.wip_Dz_self_le_SO hzibp_v hηnn
      (Work.FTS.CoercivityFix.Coer1.to_h1 hp.sqDzEta_zero)
      (Work.FTS.CoercivityFix.Coer1.integrableOn_congr_fun_Q hp.intL_f_eta
        (fun z θ => by simp only [Work.FTS.CoercivityFix.Coer1.Rho]; ring))
  have hb3 := Work.FTS.CoercivityFix.Coer1SO.wip_Dz_self_le_SO hzibp_v
      (σ := fun _ => (1 : ℝ)) (fun θ _ => zero_le_one)
      (Work.FTS.CoercivityFix.Coer1.integrableOn_congr_fun_Q hp.sqDzOne_zero
        (fun z θ => by ring))
      (Work.FTS.CoercivityFix.Coer1.integrableOn_congr_fun_Q hp.intL_f_one
        (fun z θ => by ring))
  have b4 := Work.FTS.CoercivityFix.Coer1SO.wip_Dz_self_le_SO hzibp_Dth hγnn
      (Work.FTS.CoercivityFix.Coer1.to_h1 hp.sqDthGam)
      (Work.FTS.CoercivityFix.Coer1.integrableOn_congr_fun_Q hp.intL_Dth_gam
        (fun z θ => by simp only [Work.FTS.CoercivityFix.Coer1.Rho]; ring))
  have b3 : |Work.Coercivity.wip (fun z _ => Work.Spaces.w z ^ 2)
        (Work.Spaces.Dz v) v|
      ≤ (5 / 2) * Work.Coercivity.wip (fun z _ => Work.Spaces.w z ^ 2) v v := by
    rw [← Work.FTS.CoercivityFix.Assembly.wip_weight_congr
          (ρ := fun z θ => Work.Spaces.w z ^ 2 * (fun _ => (1 : ℝ)) θ)
          (ρ' := fun z _ => Work.Spaces.w z ^ 2)
          (A := Work.Spaces.Dz v) (B := v) (fun z θ => by simp),
      ← Work.FTS.CoercivityFix.Assembly.wip_weight_congr
          (ρ := fun z θ => Work.Spaces.w z ^ 2 * (fun _ => (1 : ℝ)) θ)
          (ρ' := fun z _ => Work.Spaces.w z ^ 2)
          (A := v) (B := v) (fun z θ => by simp)]
    exact hb3
  have hb4 : |Work.Coercivity.wip (fun z θ => Work.Spaces.w z ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
        (Work.Spaces.Dth (Work.Spaces.Dz v)) (Work.Spaces.Dth v)|
      ≤ (5 / 2) * Work.Coercivity.wip (fun z θ => Work.Spaces.w z ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
        (Work.Spaces.Dth v) (Work.Spaces.Dth v) := by
    have hEq : Work.Coercivity.wip (fun z θ => Work.Spaces.w z ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
          (Work.Spaces.Dth (Work.Spaces.Dz v)) (Work.Spaces.Dth v)
        = Work.Coercivity.wip (fun z θ => Work.Spaces.w z ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
          (Work.Spaces.Dz (Work.Spaces.Dth v)) (Work.Spaces.Dth v) :=
      Work.FTS.CoercivityFix.Assembly.wip_congr_ae'
        (ρ := fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
        (g₁ := Work.Spaces.Dth (Work.Spaces.Dz v))
        (g₁' := Work.Spaces.Dz (Work.Spaces.Dth v)) (g₂ := Work.Spaces.Dth v) hcomm
    rw [hEq]
    exact b4
  have h1 : |Work.Coercivity.wip (fun z θ =>
        Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
        (Work.Spaces.Dz (Work.Spaces.Dz v)) (Work.Spaces.Dz v)|
      ≤ (5 / 2) * Work.FTS.CoercivityFix.Coer1.En Work.Spaces.eta (Work.Spaces.Dz v) := by
    rw [Work.FTS.CoercivityFix.Assembly.wip_Rho_eq Work.Spaces.eta
        (Work.Spaces.Dz (Work.Spaces.Dz v)) (Work.Spaces.Dz v),
      ← Work.FTS.CoercivityFix.Coer1.wip_Rho_self Work.Spaces.eta (Work.Spaces.Dz v)]
    exact b1
  have h2 : |Work.Coercivity.wip (fun z θ =>
        Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
        (Work.Spaces.Dz v) v|
      ≤ (5 / 2) * Work.FTS.CoercivityFix.Coer1.En Work.Spaces.eta v := by
    rw [Work.FTS.CoercivityFix.Assembly.wip_Rho_eq Work.Spaces.eta (Work.Spaces.Dz v) v,
      ← Work.FTS.CoercivityFix.Coer1.wip_Rho_self Work.Spaces.eta v]
    exact b2
  have h3 : |Work.Coercivity.wip (fun z _ => Work.Spaces.w z ^ 2) (Work.Spaces.Dz v) v|
      ≤ (5 / 2) * Work.FTS.CoercivityFix.Coer1.EnOne v := by
    rw [← Work.FTS.CoercivityFix.Coer1.wip_one_self v]
    exact b3
  have h4 : |Work.Coercivity.wip (fun z θ => Work.Spaces.w z ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
        (Work.Spaces.Dth (Work.Spaces.Dz v)) (Work.Spaces.Dth v)|
      ≤ (5 / 2) * Work.FTS.CoercivityFix.Coer1.En (Work.Spaces.gam α)
          (Work.Spaces.Dth v) := by
    rw [Work.FTS.CoercivityFix.Assembly.wip_Rho_eq (Work.Spaces.gam α)
        (Work.Spaces.Dth (Work.Spaces.Dz v)) (Work.Spaces.Dth v),
      ← Work.FTS.CoercivityFix.Coer1.wip_Rho_self (Work.Spaces.gam α) (Work.Spaces.Dth v)]
    exact hb4
  -- the `ℋ¹`-norm in terms of the three `En`-energies
  have hshape : Work.Spaces.HkSq α 1 v
      = Work.Coercivity.EfEta v + Work.Coercivity.EDz v + Work.Coercivity.EDth α v :=
    Work.FTS.StrongPersist.HkSq_one_eq_SO α hs hmem1
  have hnorm : Work.Spaces.HkSq α 1 v
      = Work.FTS.CoercivityFix.Coer1.En Work.Spaces.eta v
        + Work.FTS.CoercivityFix.Coer1.En Work.Spaces.eta (Work.Spaces.Dz v)
        + Work.FTS.CoercivityFix.Coer1.En (Work.Spaces.gam α) (Work.Spaces.Dth v) := by
    rw [hshape, Work.FTS.CoercivityFix.Coer1.EDz_eq_En v,
      Work.FTS.CoercivityFix.Coer1.EfEta_eq_En v, Work.FTS.CoercivityFix.Coer1.EDth_eq_En α v]
  have hE3le : Work.FTS.CoercivityFix.Coer1.EnOne v
      ≤ Work.FTS.CoercivityFix.Coer1.En Work.Spaces.eta v :=
    Work.FTS.CoercivityFix.Coer1T.EnOne_le_En_eta (u := v) hp.sqDzOne_zero
      (Work.FTS.CoercivityFix.Coer1.to_h1 (β := Work.Spaces.eta) hp.sqDzEta_zero)
  have hAnn1 : 0 ≤ Work.FTS.CoercivityFix.Coer1.En Work.Spaces.eta (Work.Spaces.Dz v) :=
    Work.FTS.CoercivityFix.Coer1.En_nonneg _ _
  have hAnn2 : 0 ≤ Work.FTS.CoercivityFix.Coer1.En Work.Spaces.eta v :=
    Work.FTS.CoercivityFix.Coer1.En_nonneg _ _
  have hAnn3 : 0 ≤ Work.FTS.CoercivityFix.Coer1.EnOne v :=
    Work.FTS.CoercivityFix.Coer1.EnOne_nonneg _
  have hAnn4 : 0 ≤ Work.FTS.CoercivityFix.Coer1.En (Work.Spaces.gam α)
      (Work.Spaces.Dth v) := Work.FTS.CoercivityFix.Coer1.En_nonneg _ _
  rw [Work.Coercivity.H1IP, hnorm]
  refine le_trans (Work.FTS.CoercivityFix.Assembly.abs_lin4_coef ((10 : ℝ)) ((10 : ℝ) ^ 10)
    ((10 : ℝ) ^ 17) ((10 : ℝ) ^ 21) (by norm_num) (by positivity) (by positivity)
    (by positivity) _ _ _ _) ?_
  nlinarith [h1, h2, h3, h4, hE3le, hAnn1, hAnn2, hAnn3, hAnn4]

/-! ## The `D_z`-clause of the level-four coercivity on the open class -/

theorem dz_four_RegQo {c₁ c₂ c₁' c₂' c₁'' c₂'' : ℝ}
    (h₁ : 0 < c₁) (h₂ : 0 < c₂) (h₁' : 0 < c₁') (h₂' : 0 < c₂')
    (h₁'' : 0 < c₁'') (h₂'' : 0 < c₂'') :
    ∃ Cdz : ℝ, 0 < Cdz ∧ ∀ (α : ℝ), 0 < α → ∀ f : Work.FTS.Galerkin.Fn,
      Work.FTS.StrongEps.EpsE4Thr.RegQo α 5 f →
        |Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α
            (Work.Spaces.Dz f) f| ≤ Cdz * Work.Spaces.HkSq α 4 f := by
  set E₁ : ℝ := 3 * (10 : ℝ) ^ 22 * max 1 (max c₁ c₂) with hE₁
  set E₂ : ℝ := 3 * E₁ * max 1 (max c₁' c₂') with hE₂
  set E₃ : ℝ := 3 * E₂ * max 1 (max c₁'' c₂'') with hE₃
  have hm₁ : (1 : ℝ) ≤ max 1 (max c₁ c₂) := le_max_left _ _
  have hm₂ : (1 : ℝ) ≤ max 1 (max c₁' c₂') := le_max_left _ _
  have hm₃ : (1 : ℝ) ≤ max 1 (max c₁'' c₂'') := le_max_left _ _
  have hE₁pos : 0 < E₁ := by rw [hE₁]; nlinarith [hm₁]
  have hE₂pos : 0 < E₂ := by rw [hE₂]; nlinarith [hE₁pos, hm₂]
  have hE₃pos : 0 < E₃ := by rw [hE₃]; nlinarith [hE₂pos, hm₃]
  refine ⟨E₃, hE₃pos, ?_⟩
  intro α hα f hf
  have hlin : -(1 / 10 : ℝ) ≤ α := by linarith
  have v1 := dzFour_dz_step_SO (IP := Work.Coercivity.H1IP α) (n := 0) hα h₁ h₂
    (by norm_num : (0 : ℝ) < 10 ^ 22) (Work.FTS.IPGen.Comm2o_zero α).congr
    (fun v hv => dzFour_H1IP_Dz_le_one_SO α hα hv)
  have v2 := dzFour_dz_step_SO (IP := Work.FTS.CoercivityFix.Assembly.IP2 c₁ c₂ α) (n := 1)
    hα h₁' h₂' hE₁pos
    (Work.FTS.IPGen.Comm2o_one α hlin).congr
    (by intro v hv; rw [hE₁]; exact v1 v hv)
  have v3 := dzFour_dz_step_SO
    (IP := Work.FTS.CoercivityFix.Assembly.IP3 c₁ c₂ c₁' c₂' α) (n := 2)
    hα h₁'' h₂'' hE₂pos
    (Work.FTS.IPGen.Comm2o_two α hlin).congr
    (by intro v hv; rw [hE₂]; exact v2 v hv)
  have hv3 := v3 f hf
  simp only [Work.FTS.CoercivityFix.Assembly.IP4, Work.FTS.CoercivityFix.Assembly.IP3,
    Work.FTS.CoercivityFix.Assembly.IP2, hE₃] at hv3 ⊢
  simpa using hv3

end Work.FTS.StrongEps.EpsE4Thr
