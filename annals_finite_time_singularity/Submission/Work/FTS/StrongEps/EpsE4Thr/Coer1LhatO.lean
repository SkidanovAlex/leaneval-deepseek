/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EpsE4Thr/Coer1LhatO.lean` — the level-one coercivity of `𝓛̂` on
the **open** class

`CoercivityFix/Coer1/coer1_Lhat.lean` proves `2·|f|²_{ℋ¹} ≤ H1IP α (𝓛̂ f) f` on `RegQ α 2 f` by
assembling the four estimates `est_A`, `est_B`, `est_C`, `est_D` with the arithmetic `assembly`
and the domination `EDthW_le_En_gam`.

This file performs the same assembly on the open class:

* the four estimates are the fleet's open ports `OClass.est_A_O`, `est_B_O`, `est_C_O`, `est_D_O`
  (all stated with `RegQo α 2` + `IntPkgO`);
* `assembly` and `EDthW_le_En_gam` are *class-free* (the former takes the `ℋ¹`-identity and the
  four slot bounds as hypotheses, the latter takes the two integrability facts), so the frozen
  statements apply verbatim;
* the `ℋ¹`-identity comes from `StrongPersist.HkSq_one_eq_SO` (the open analogue of
  `HkSq_one_eq`) and the `En`-identifications of `Coer1.Defs`.

This is the base of the *clean* (`𝓛̂`) induction route that feeds `Transfer/CoerDataT`'s step; it
is the open-class analogue of the theorem whose `CoerAdm`-version `coer1_Lhat` is consumed by
`Assembly.coerData2_one_H1IP`.

Everything here is `sorry`-free.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.EpsE4Thr.OpenClass
import Submission.Work.FTS.StrongEps.EpsE4Thr.IntPkgO
import Submission.Work.FTS.StrongEps.EpsE4Thr.OClass.est_A_O
import Submission.Work.FTS.StrongEps.EpsE4Thr.OClass.est_B_O
import Submission.Work.FTS.StrongEps.EpsE4Thr.OClass.est_C_O
import Submission.Work.FTS.StrongEps.EpsE4Thr.OClass.est_D_O
import Submission.Work.FTS.CoercivityFix.Coer1.Assembly
import Submission.Work.FTS.CoercivityFix.Coer1.Estimates
import Submission.Work.FTS.StrongPersist.IP6_lo_coeffs
import Submission.Work.FTS.StrongEps.EpsE4Thr.CoerDataTO
import Submission.Work.FTS.StrongEps.EpsE4Thr.StepDataO

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

/-- **The level-one coercivity of `𝓛̂` on the open class**: the frozen `Coer1.coer1_Lhat` with
`RegQ α 2` replaced by `RegQo α 2`. -/
theorem coer1_Lhat_O {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1 / 4) {f : Fn}
    (hf : RegQo α 2 f) (hIP : IntPkgO α f) :
    2 * Work.Spaces.HkSq α 1 f
      ≤ Work.Coercivity.H1IP α (Work.FTS.CoercivityFix.Lhat f) f := by
  have hso : Work.FTS.EllipticEst.SmoothOpen f := hf.1
  have hm1 : Work.Spaces.HkMem α 1 f :=
    Work.FTS.OpenPkg.HkMem_mono_open hso 1 (by norm_num) hf.2.1
  -- the `ℋ¹`-energy is the sum of the three weighted energies
  have hHk : Work.Spaces.HkSq α 1 f
      = Work.FTS.CoercivityFix.Coer1.En Work.Spaces.eta (Work.Spaces.Dz f)
        + Work.FTS.CoercivityFix.Coer1.En Work.Spaces.eta f
        + Work.FTS.CoercivityFix.Coer1.En (Work.Spaces.gam α) (Work.Spaces.Dth f) := by
    rw [Work.FTS.StrongPersist.HkSq_one_eq_SO α hso hm1,
      Work.FTS.CoercivityFix.Coer1.EDz_eq_En,
      Work.FTS.CoercivityFix.Coer1.EfEta_eq_En,
      Work.FTS.CoercivityFix.Coer1.EDth_eq_En]
    ring
  -- the two integrability certificates consumed by `EDthW_le_En_gam`
  have hDθW : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      (Work.Spaces.Dth f z θ) ^ 2 * Work.Spaces.w z ^ 2))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    Work.FTS.CoercivityFix.Coer1.integrableOn_congr_fun_Q
      (A := fun z θ => (Work.Spaces.mixed 0 1 f z θ) ^ 2 * Work.Spaces.w z ^ 2)
      (hIP.sqMixedOne 1 0 (by norm_num) (by norm_num)) (fun z θ => by
        simp only [Work.Spaces.mixed, Work.Spaces.DzIter_zero, Work.Spaces.DthIter_zero,
          Work.Spaces.DthIter_succ])
  have hDθG : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      (Work.Spaces.Dth f z θ) ^ 2 * Work.Spaces.w z ^ 2
        * Work.FTS.CoercivityFix.Coer1.sig (Work.Spaces.gam α) θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    Work.FTS.CoercivityFix.Coer1.integrableOn_congr_fun_Q
      (A := fun z θ => (Work.Spaces.mixed 0 1 f z θ) ^ 2
        * Work.Spaces.w z ^ 2 * Work.FTS.CoercivityFix.Coer1.sig (Work.Spaces.gam α) θ)
      (Work.FTS.CoercivityFix.Coer1.to_h1
        (hIP.sqMixedGam 1 0 (by norm_num) (by norm_num))) (fun z θ => by
        simp only [Work.Spaces.mixed, Work.Spaces.DzIter_zero, Work.Spaces.DthIter_zero,
          Work.Spaces.DthIter_succ])
  have hW : Work.Coercivity.EDthW f
      ≤ Work.FTS.CoercivityFix.Coer1.En (Work.Spaces.gam α) (Work.Spaces.Dth f) :=
    Work.FTS.CoercivityFix.Coer1.EDthW_le_En_gam α hα f hDθW hDθG
  have hD : (17 / 40) * Work.FTS.CoercivityFix.Coer1.En (Work.Spaces.gam α) (Work.Spaces.Dth f)
      ≤ Work.Coercivity.wip (Work.FTS.CoercivityFix.Coer1.Rho (Work.Spaces.gam α))
          (Work.Spaces.Dth (Work.FTS.CoercivityFix.Lhat f)) (Work.Spaces.Dth f) := by
    have h := OClass.est_D_O α hα hα1 hf hIP
    rw [Work.FTS.CoercivityFix.Coer1.EDth_eq_En] at h
    have hw : Work.Coercivity.thetaW α = Work.FTS.CoercivityFix.Coer1.Rho (Work.Spaces.gam α) := by
      funext z θ
      rfl
    rw [hw] at h
    exact h
  exact Work.FTS.CoercivityFix.Coer1.assembly α hα hα1 hHk hW
    (OClass.est_A_O α hα hα1 hf hIP) (est_B_O α hα hα1 hf hIP)
    (OClass.est_C_O α hα hα1 hf hIP) hD

/-- **The clean level-1 data of the coercivity induction on the open class** — the open-class
analogue of `Assembly.coerData2_one_H1IP`: the level-`1` `CoerData2O` for `H1IP`, with coercivity
constant `2` (as in `coer1_Lhat`/`ledger`) and the Cauchy–Schwarz constant of `H1IP_cs_Q_O`. -/
theorem coerData2_one_H1IP_O :
    ∃ CC₁ : ℝ, 0 < CC₁ ∧ ∀ α : ℝ, α ∈ Set.Ioc 0 (1 / 4) →
      CoerData2O α 1 (Work.Coercivity.H1IP α) 2 CC₁ := by
  obtain ⟨C, hC, hcs⟩ := H1IP_cs_Q_O
  refine ⟨C, hC, fun α hα => ?_⟩
  have hα4 : α ≤ 1 / 4 := hα.2
  refine
    { hcc := by norm_num
      hCC := hC
      cs := fun f g hf hg =>
        hcs α hα.1 f g (regQo_mono (by norm_num) hf) (regQo_mono (by norm_num) hg)
      coer := fun f hf => ?_ }
  have hreg : RegQo α 2 f := hf
  have h := coer1_Lhat_O hα.1 hα4 hreg (IntPkg_O hα.1 hreg)
  simpa using h


end Work.FTS.StrongEps.EpsE4Thr
