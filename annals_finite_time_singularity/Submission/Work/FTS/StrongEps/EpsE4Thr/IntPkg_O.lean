/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EpsE4Thr/IntPkgO.lean` — the open-class integrability bundle
`IntPkgO`

The four coercivity estimates of the frozen `CoercivityFix/Coer1T` chapter consume the
integrability certificate bundle `Work.FTS.CoercivityFix.Coer1.IntPkg` (defined in
`CoercivityFix/Coer1/Defs.lean`, proved for `RegQ α 2 f` in `CoercivityFix/Coer1/IntFacts.lean`).
That bundle is **not** available on the open class: three of its fields are
`zibp_f : ZIBP f`, `zibp_Dz : ZIBP (Dz f)`, `zibp_Dth : ZIBP (Dth f)`, and `ZIBP`'s first field is
`smooth : LocData.SmoothQuad u` — the flatness-at-`z = 0` condition that `RegQo` does not supply
(and that is *false* for the route's projected slices, `not_smoothQuad_Pz_Jeps`).

`IntPkgO` is the verbatim open-class analogue: the same field list, with the three
`z`-integration-by-parts fields taken in the open class `CoercivityFix.Coer1SO.ZIBPO`.

This file proves the announced consumer `IntPkg_O`
(`RegQo α 2 f → IntPkgO α f`), the open-class re-run of `CoercivityFix.Coer1.IntPkg_Q`, after
which the four slot estimates of `Coer1T` can be ported one by one with `CoerAdm` replaced by
`CoerAdmO`.

`RegQo α 2 f` is `⟨SmoothOpen f, HkMem α 2 f, BdryTraces α 2 f⟩`; `SmoothOpen` supplies
`C^∞` on the *open* quadrant, which is what each a.e./continuity step of the argument consumes.
The proof transcribes `IntPkg_Q` step by step:

* the five squared-block integrability fields come from the summed `ℋ^k`-integrand via
  `Coer1.joint_of_le_HkIntegrand` and the pointwise domination lemmas
  `Spaces.sq_le_HkIntegrand_z` / `Spaces.sq_le_HkIntegrand_mixed`
  (bundle: `IntPkgOAux.IntPkgSq_O`);
* the `𝓛`- and transport pairings are the open-class twins
  `IntPkgOAux.intL_of_O`, `IntPkgOAux.intTr_of_O` of `Coer1.intL_of`, `Coer1.intTr_of`
  (the `AM-GM` `2|ab| ≤ a² + b²` of `Coer1.integrableOn_mul_of_sq_Q`, which only needs
  continuity on the open quadrant);
* the two pieces of the `D_z`-commutator split are `Coer1.intLhat_of`,
  `Coer1.intTransport_of` and `Coer1.intE2hat_of`, the last fed with
  `IntPkgOAux.continuousOn_E2hat_O`;
* the identification of the `(D_θ D_z f)²`-block uses the a.e. Clairaut
  `IntPkgOAux.ae_Dz_Dth_comm_O`;
* the three `ZIBPO` fields are produced by `Coer1SO.zibpO_of` from the boundary traces
  `BdryTraces α 2 f` (pairs `(0,0)`, `(1,0)`, `(0,1)`) and the plain-`w²` pairings.

Everything is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.EpsE4Thr.IntPkgO
import Submission.Work.FTS.StrongEps.EpsE4Thr.OpenClass
import Submission.Work.FTS.CoercivityFix.Coer1.IntFacts
import Submission.Work.FTS.CoercivityFix.Coer1SO.Defs
import Submission.Work.FTS.CoercivityFix.Coer1SO.zibpO_of
import Submission.Work.FTS.StrongEps.EpsE4Thr.IntPkgOAux.IntPkgSq_O
import Submission.Work.FTS.StrongEps.EpsE4Thr.IntPkgOAux.ae_Dz_Dth_comm_O
import Submission.Work.FTS.StrongEps.EpsE4Thr.IntPkgOAux.intL_of_O
import Submission.Work.FTS.StrongEps.EpsE4Thr.IntPkgOAux.intTr_of_O
import Submission.Work.FTS.StrongEps.EpsE4Thr.IntPkgOAux.continuousOn_E2hat_O

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

theorem IntPkg_O {α : ℝ} (hα : 0 < α) {f : Work.FTS.Galerkin.Fn}
    (hf : Work.FTS.StrongEps.EpsE4Thr.RegQo α 2 f) :
    Work.FTS.StrongEps.EpsE4Thr.IntPkgO α f := by
  obtain ⟨hs, hm, hb⟩ := hf
  -- the five squared-block integrability fields
  obtain ⟨hsqE, hsqME, hsqMG, hsqO, hsqMO⟩ :=
    Work.FTS.StrongEps.EpsE4Thr.IntPkgOAux.IntPkgSq_O α hα hs hm
  -- the `𝓛`-pairings
  have hLf_eta := Work.FTS.StrongEps.EpsE4Thr.IntPkgOAux.intL_of_O hs
    (Work.FTS.CoercivityFix.Coer1.continuousOn_Rho _)
    (Work.FTS.CoercivityFix.Coer1.Rho_nonneg _)
    (hsqE 0 (by norm_num)) (hsqE 1 (by norm_num))
  have hLDz_eta := Work.FTS.StrongEps.EpsE4Thr.IntPkgOAux.intL_of_O hs.Dz
    (Work.FTS.CoercivityFix.Coer1.continuousOn_Rho _)
    (Work.FTS.CoercivityFix.Coer1.Rho_nonneg _)
    (hsqE 1 (by norm_num)) (hsqE 2 (by norm_num))
  have hLDth_gam := Work.FTS.StrongEps.EpsE4Thr.IntPkgOAux.intL_of_O hs.Dth
    (Work.FTS.CoercivityFix.Coer1.continuousOn_Rho _)
    (Work.FTS.CoercivityFix.Coer1.Rho_nonneg _)
    (hsqMG 1 0 (by norm_num) (by norm_num)) (hsqMG 1 1 (by norm_num) (by norm_num))
  have hLf_one := Work.FTS.StrongEps.EpsE4Thr.IntPkgOAux.intL_of_O hs
    Work.FTS.CoercivityFix.Coer1.continuousOn_w2
    Work.FTS.CoercivityFix.Coer1.w2_nonneg
    (hsqO 0 (by norm_num)) (hsqO 1 (by norm_num))
  have hLDz_one := Work.FTS.StrongEps.EpsE4Thr.IntPkgOAux.intL_of_O hs.Dz
    Work.FTS.CoercivityFix.Coer1.continuousOn_w2
    Work.FTS.CoercivityFix.Coer1.w2_nonneg
    (hsqO 1 (by norm_num)) (hsqO 2 (by norm_num))
  have hLDth_one := Work.FTS.StrongEps.EpsE4Thr.IntPkgOAux.intL_of_O hs.Dth
    Work.FTS.CoercivityFix.Coer1.continuousOn_w2
    Work.FTS.CoercivityFix.Coer1.w2_nonneg
    (hsqMO 1 0 (by norm_num) (by norm_num)) (hsqMO 1 1 (by norm_num) (by norm_num))
  -- the transport pairings
  have hintf_eta := Work.FTS.StrongEps.EpsE4Thr.IntPkgOAux.intTr_of_O hs
    (Work.FTS.CoercivityFix.Coer1.continuousOn_Rho _)
    (Work.FTS.CoercivityFix.Coer1.Rho_nonneg _)
    (hsqE 0 (by norm_num)) (hsqME 1 0 (by norm_num) (by norm_num))
  have hthDz : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      (Work.Spaces.Dth (Work.Spaces.Dz f) z θ) ^ 2
        * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    have hae : (Function.uncurry (fun z θ =>
          (Work.Spaces.mixed 1 1 f z θ) ^ 2
            * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta z θ))
        =ᵐ[MeasureTheory.volume.restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)]
        (Function.uncurry (fun z θ => (Work.Spaces.Dth (Work.Spaces.Dz f) z θ) ^ 2
          * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta z θ)) := by
      have h := Work.FTS.StrongEps.EpsE4Thr.IntPkgOAux.ae_Dz_Dth_comm_O hs
      rw [Work.FTS.CoercivityFix.Coer1.iz_prod_restrict] at h
      filter_upwards [h] with p hp
      show (Work.Spaces.Dz (Work.Spaces.Dth f) p.1 p.2) ^ 2
          * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta p.1 p.2
        = (Work.Spaces.Dth (Work.Spaces.Dz f) p.1 p.2) ^ 2
          * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta p.1 p.2
      rw [hp]
    exact (hsqME 1 1 (by norm_num) (by norm_num)).congr hae
  have hintDz_eta := Work.FTS.StrongEps.EpsE4Thr.IntPkgOAux.intTr_of_O hs.Dz
    (Work.FTS.CoercivityFix.Coer1.continuousOn_Rho _)
    (Work.FTS.CoercivityFix.Coer1.Rho_nonneg _)
    (hsqE 1 (by norm_num)) hthDz
  have hintDth_gam := Work.FTS.StrongEps.EpsE4Thr.IntPkgOAux.intTr_of_O hs.Dth
    (Work.FTS.CoercivityFix.Coer1.continuousOn_Rho _)
    (Work.FTS.CoercivityFix.Coer1.Rho_nonneg _)
    (hsqMG 1 0 (by norm_num) (by norm_num)) (hsqMG 2 0 (by norm_num) (by norm_num))
  have hintf_one := Work.FTS.StrongEps.EpsE4Thr.IntPkgOAux.intTr_of_O hs
    Work.FTS.CoercivityFix.Coer1.continuousOn_w2
    Work.FTS.CoercivityFix.Coer1.w2_nonneg
    (hsqO 0 (by norm_num)) (hsqMO 1 0 (by norm_num) (by norm_num))
  -- the `Lhat`- and `E2hat`-pairings of the `D_z`-commutator split
  have hLhat := Work.FTS.CoercivityFix.Coer1.intLhat_of hLDz_eta
    (Work.FTS.CoercivityFix.Coer1.intTransport_of hintDz_eta)
  have hE2 : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.FTS.CoercivityFix.E2hat f z θ
        * Work.Spaces.Dz f z θ * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    Work.FTS.CoercivityFix.Coer1.intE2hat_of
      (Work.FTS.StrongEps.EpsE4Thr.IntPkgOAux.continuousOn_E2hat_O hs
        (Work.FTS.CoercivityFix.Coer1.continuousOn_Rho _))
      (Work.FTS.CoercivityFix.Coer1.Rho_nonneg _)
      (hsqE 0 (by norm_num)) (hsqE 1 (by norm_num)) (hsqME 1 0 (by norm_num) (by norm_num))
  -- the boundary traces of the three `z`-integrations by parts
  have hasm0 : ∀ θ ∈ Set.Ioo 0 (π / 2),
      Filter.Tendsto (fun z => z * (f z θ * Work.Spaces.w z) ^ 2) (𝓝[>] 0) (𝓝 0) :=
    fun θ hθ => ((hb 0 0 (by norm_num)).1 θ hθ).1
  have hasmT0 : ∀ θ ∈ Set.Ioo 0 (π / 2),
      Filter.Tendsto (fun z => z * (f z θ * Work.Spaces.w z) ^ 2) Filter.atTop (𝓝 0) :=
    fun θ hθ => ((hb 0 0 (by norm_num)).1 θ hθ).2
  have hasm1 : ∀ θ ∈ Set.Ioo 0 (π / 2),
      Filter.Tendsto (fun z => z * (Work.Spaces.Dz f z θ * Work.Spaces.w z) ^ 2)
        (𝓝[>] 0) (𝓝 0) :=
    fun θ hθ => ((hb 0 1 (by norm_num)).1 θ hθ).1
  have hasmT1 : ∀ θ ∈ Set.Ioo 0 (π / 2),
      Filter.Tendsto (fun z => z * (Work.Spaces.Dz f z θ * Work.Spaces.w z) ^ 2)
        Filter.atTop (𝓝 0) :=
    fun θ hθ => ((hb 0 1 (by norm_num)).1 θ hθ).2
  have hasm2 : ∀ θ ∈ Set.Ioo 0 (π / 2),
      Filter.Tendsto (fun z => z * (Work.Spaces.Dth f z θ * Work.Spaces.w z) ^ 2)
        (𝓝[>] 0) (𝓝 0) :=
    fun θ hθ => ((hb 1 0 (by norm_num)).1 θ hθ).1
  have hasmT2 : ∀ θ ∈ Set.Ioo 0 (π / 2),
      Filter.Tendsto (fun z => z * (Work.Spaces.Dth f z θ * Work.Spaces.w z) ^ 2)
        Filter.atTop (𝓝 0) :=
    fun θ hθ => ((hb 1 0 (by norm_num)).1 θ hθ).2
  refine ⟨hsqE, hsqME, hsqMG, hsqO, hsqMO, hLf_eta, hLDz_eta, hLDth_gam, hLf_one,
    hLhat, hE2, hintf_eta, hintDz_eta, hintDth_gam, hintf_one, ?_, ?_, ?_⟩
  · -- `ZIBPO f`
    refine Work.FTS.CoercivityFix.Coer1SO.zibpO_of hs hasm0 hasmT0 ?_ hLf_one
    refine (hsqO 0 (by norm_num)).congr (MeasureTheory.ae_restrict_of_forall_mem
      (measurableSet_Ici.prod measurableSet_Icc) (fun p hp => ?_))
    rcases p with ⟨z, θ⟩
    simp only [Function.uncurry_apply_pair, Work.Spaces.DzIter_zero]
    ring
  · -- `ZIBPO (D_z f)`
    refine Work.FTS.CoercivityFix.Coer1SO.zibpO_of hs.Dz hasm1 hasmT1 ?_ hLDz_one
    refine (hsqO 1 (by norm_num)).congr (MeasureTheory.ae_restrict_of_forall_mem
      (measurableSet_Ici.prod measurableSet_Icc) (fun p hp => ?_))
    rcases p with ⟨z, θ⟩
    simp only [Function.uncurry_apply_pair, Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero]
    ring
  · -- `ZIBPO (D_θ f)`
    refine Work.FTS.CoercivityFix.Coer1SO.zibpO_of hs.Dth hasm2 hasmT2 ?_ hLDth_one
    refine (hsqMO 1 0 (by norm_num) (by norm_num)).congr
      (MeasureTheory.ae_restrict_of_forall_mem
        (measurableSet_Ici.prod measurableSet_Icc) (fun p hp => ?_))
    rcases p with ⟨z, θ⟩
    simp only [Function.uncurry_apply_pair, Work.Spaces.mixed, Work.Spaces.DzIter_zero,
      Work.Spaces.DthIter_succ, Work.Spaces.DthIter_zero]
    ring

end Work.FTS.StrongEps.EpsE4Thr
