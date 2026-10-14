import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.Nonlinear.Pieces.RNP.GamSharpAux
import Submission.Work.FTS.StrongEps.EpsE4Thr.OpenCoer.SlotWCommon
import Submission.Work.FTS.TransportS.T3SlotAux.Remainder
import Submission.Work.FTS_StreamBdry.SB4.DzEpartEq
import Submission.Work.H2.T1Q.SliceIntQ
import Submission.Work.H2W.FstarDzIterFourPsiAe

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr.OClass

open scoped Real Topology
open MeasureTheory Set Filter

set_option maxHeartbeats 800000

/-! ## The two open-class helpers -/

/-- **The pointwise expansion of `D_θ(𝓛̂ f)` on the open quadrant, in the open class
`SmoothOpen`** (the open-class twin of `Coer1T.intDth_Lhat_gam_expand`, whose hypothesis is
`SmoothQuad`): from `OClass.Dth_Lhat_open`,
`D_θ(𝓛̂f) = D_θf + D_zD_θf − 2D_θf/(1+z) − 3D_θ²f/(1+z)`. -/
theorem intDth_Lhat_gam_expand_open {f : ℝ → ℝ → ℝ} (hs : Work.FTS.EllipticEst.SmoothOpen f)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Work.Spaces.Dth (Work.FTS.CoercivityFix.Lhat f) z θ
      = Work.Spaces.Dth f z θ + Work.Spaces.Dz (Work.Spaces.Dth f) z θ
        - 2 * Work.Spaces.Dth f z θ / (1 + z)
        - 3 * Work.Spaces.Dth (Work.Spaces.Dth f) z θ / (1 + z) := by
  rw [Work.FTS.CoercivityFix.LhatCalc.Dth_Lhat_open hs hz hθ.1 hθ.2]
  simp only [Work.FTS.CoercivityFix.Lhat, Pi.sub_apply, Work.Coercivity.L,
    Work.Coercivity.Transport]

/-- The mixed blocks `D_z^jD_θ^i f` are continuous on the open quadrant, for `f` of class
`SmoothOpen`: the open-class replacement for `Coer1.continuousOn_mixed_Q`, whose hypothesis is
`SmoothQuad`. -/
theorem continuousOn_mixed_open_O {f : ℝ → ℝ → ℝ} (hs : Work.FTS.EllipticEst.SmoothOpen f)
    (j i : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.mixed j i f p.1 p.2)
      Work.FTS.CoercivityFix.Coer1.Qd :=
  (hs.mixed j i).continuousOn

/-- The **open-class** twin of `Work.FTS.CoercivityFix.Coer1T.intDth_Lhat_gam`
(`CoercivityFix/Coer1T/intDth_Lhat_gam.lean`, proved): joint integrability of the `γ`-weighted
pairing `⟨D_θ(𝓛̂ f), D_θ f⟩_{w² sin(2θ)^{-γ}}` on the quadrant, with `RegQ α 2` replaced by
`RegQo α 2` (`SmoothOpen` instead of `SmoothQuad`) and the bundle `IntPkg` by `IntPkgO`.

Frozen proof and its open replacements: the pointwise expansion
`D_θ(𝓛̂ f) = D_θf + D_zD_θf − 2D_θf/(1+z) − 3D_θ²f/(1+z)` (a.e. on the quadrant) comes from
`OClass.Dth_Lhat_open` in place of `LhatCalc.Dth_Lhat`; the blocks `(D_θf)²ρ_γ` and
`(D_zD_θf)²ρ_γ` come from `HkMem α 2 f` (`Coer1.sq_MixedGam`, or an open derivation from
`Spaces.sq_le_HkIntegrand_mixed` + `Coer1.integrableOn_prod` with `SmoothOpen` continuity in place
of `Coer1.continuousOn_mixed_Q`); the `D_θ²f`-term is `IntPkgO.hint_Dth_gam`;
`Coer1.integrableOn_div_one_add_Q`, `Coer1.integrableOn_mul_of_sq_Q`,
`Coer1.ae_prod_fst_pos`, `Coer1.ae_prod_snd_mem_Ioo` are class-free.  Note `thetaW α` and
`Rho (gam α)` are the same expression (`Coer1.Rho_gam` is `rfl`). -/
theorem intDth_Lhat_gam_O (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {f : Work.FTS.Galerkin.Fn}
    (hf : Work.FTS.StrongEps.EpsE4Thr.RegQo α 2 f)
    (hIP : Work.FTS.StrongEps.EpsE4Thr.IntPkgO α f) :
    MeasureTheory.IntegrableOn
        (Function.uncurry (fun z θ => Work.Spaces.Dth (Work.FTS.CoercivityFix.Lhat f) z θ
          * Work.Spaces.Dth f z θ * Work.Coercivity.thetaW α z θ))
        (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
  obtain ⟨hs, -, -⟩ := hf
  -- the weight is nonnegative on the closed angular interval and continuous on the quadrilateral
  have hρnn : ∀ z θ, θ ∈ Work.Spaces.Iθ →
      0 ≤ Work.FTS.CoercivityFix.Coer1.Rho (Work.Spaces.gam α) z θ :=
    Work.FTS.CoercivityFix.Coer1.Rho_nonneg _
  have hρc : ContinuousOn (fun p : ℝ × ℝ =>
      Work.FTS.CoercivityFix.Coer1.Rho (Work.Spaces.gam α) p.1 p.2)
      Work.FTS.CoercivityFix.Coer1.Qd :=
    Work.FTS.CoercivityFix.Coer1.continuousOn_Rho _
  -- ### the two `L²(ρ_γ)`-blocks, from the integrability bundle `IntPkgO`
  have s11 : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => (Work.Spaces.Dz (Work.Spaces.Dth f) z θ) ^ 2
        * Work.FTS.CoercivityFix.Coer1.Rho (Work.Spaces.gam α) z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    refine (hIP.sqMixedGam 1 1 (by norm_num) (by norm_num)).congr ?_
    refine MeasureTheory.ae_restrict_of_forall_mem
      (measurableSet_Ici.prod measurableSet_Icc) (fun p _ => ?_)
    rcases p with ⟨z, θ⟩
    simp only [Function.uncurry_apply_pair, Work.Spaces.mixed, Work.Spaces.DzIter_succ,
      Work.Spaces.DzIter_zero, Work.Spaces.DthIter_succ, Work.Spaces.DthIter_zero]
  have s10 : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => (Work.Spaces.Dth f z θ) ^ 2
        * Work.FTS.CoercivityFix.Coer1.Rho (Work.Spaces.gam α) z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    refine (hIP.sqMixedGam 1 0 (by norm_num) (by norm_num)).congr ?_
    refine MeasureTheory.ae_restrict_of_forall_mem
      (measurableSet_Ici.prod measurableSet_Icc) (fun p _ => ?_)
    rcases p with ⟨z, θ⟩
    simp only [Function.uncurry_apply_pair, Work.Spaces.mixed_zero_left,
      Work.Spaces.DthIter_succ, Work.Spaces.DthIter_zero]
  -- ### `(D_θf)²ρ_γ`
  have hA : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Spaces.Dth f z θ * Work.Spaces.Dth f z θ
        * Work.FTS.CoercivityFix.Coer1.Rho (Work.Spaces.gam α) z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    refine s10.congr ?_
    refine MeasureTheory.ae_restrict_of_forall_mem
      (measurableSet_Ici.prod measurableSet_Icc) (fun p _ => ?_)
    rcases p with ⟨z, θ⟩
    simp only [Function.uncurry_apply_pair, pow_two]
  -- ### `D_zD_θf · D_θf · ρ_γ`
  have hB : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Spaces.Dz (Work.Spaces.Dth f) z θ
        * Work.Spaces.Dth f z θ
        * Work.FTS.CoercivityFix.Coer1.Rho (Work.Spaces.gam α) z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    Work.FTS.CoercivityFix.Coer1.integrableOn_mul_of_sq_Q
      (((continuousOn_mixed_open_O hs 1 1).mul (continuousOn_mixed_open_O hs 0 1)).mul hρc)
      hρnn s11 s10
  -- ### `(D_θf)²ρ_γ/(1+z)`
  have hC : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Spaces.Dth f z θ * Work.Spaces.Dth f z θ
        * Work.FTS.CoercivityFix.Coer1.Rho (Work.Spaces.gam α) z θ / (1 + z)))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    Work.FTS.CoercivityFix.Coer1.integrableOn_div_one_add_Q hA
  -- ### `D_θ²f · D_θf · ρ_γ/(1+z)`, from the bundle `IntPkgO`
  have hD : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Spaces.Dth (Work.Spaces.Dth f) z θ
        * Work.Spaces.Dth f z θ
        * Work.FTS.CoercivityFix.Coer1.Rho (Work.Spaces.gam α) z θ / (1 + z)))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := hIP.hint_Dth_gam
  -- ### the combination, and its a.e. identification with the target integrand
  refine (((hA.add hB).sub (hC.const_mul 2)).sub (hD.const_mul 3)).congr ?_
  have hquad : ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
      0 < p.1 ∧ p.2 ∈ Set.Ioo 0 (π / 2) :=
    Work.FTS.CoercivityFix.Coer1.ae_prod_fst_pos.and
      Work.FTS.CoercivityFix.Coer1.ae_prod_snd_mem_Ioo
  rw [Work.FTS.CoercivityFix.Coer1.iz_prod_restrict] at hquad
  filter_upwards [hquad] with p hp
  obtain ⟨hpz, hpθ⟩ := hp
  obtain ⟨z, θ⟩ := p
  simp only [Function.uncurry_apply_pair, Pi.add_apply, Pi.sub_apply]
  rw [intDth_Lhat_gam_expand_open hs hpz hpθ]
  simp only [Work.FTS.CoercivityFix.Coer1.Rho, Work.FTS.CoercivityFix.Coer1.sig,
    Work.Coercivity.thetaW]
  ring

end Work.FTS.StrongEps.EpsE4Thr.OClass
