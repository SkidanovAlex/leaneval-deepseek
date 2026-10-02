import Mathlib
import Submission.Work.SeedCertRay.RootSeed
import Submission.Work.SeedCertNum.A1Export
import Submission.Work.SeedCertNum.Locate
import Submission.Work.SeedCertNum.EEInstance4
import Submission.Work.SeedDyn.Main
import Submission.Work.FatouParabolic2.mem_Mandelbar_of_parabolic_returnMap_simple
import Submission.Work.FatouParabolic2.Defs
import Submission.Work.FatouParabolic2.fatouParabolicInput_simple

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MandelFinal


noncomputable section

set_option maxRecDepth 10000

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-! ## The bridges between the two certified areas -/

/-- The Fatou chart of the ray area (`Work.SeedCertRay.fatou`) is the one of the seed area
(`Work.SeedCert.fatouW`): both are `-1/(A (z - z₁))`. -/
theorem seedCert_fatou_eq_fatouW (z₁ A z : ℂ) :
    Work.SeedCertRay.fatou z₁ A z = Work.SeedCert.fatouW z₁ A z := by
  simp only [Work.SeedCertRay.fatou, Work.SeedCert.fatouW, neg_div, one_div]

/-- The ray area's repelling petal at depth `4` is the seed area's petal at the certified depth
`RpetalR4 = 4`. -/
theorem seedCert_petal_eq_petalW (z₁ A : ℂ) :
    Work.SeedCertRay.Petal z₁ A 4 = Work.SeedCert.petal z₁ A 4 := by
  ext z
  rw [Work.SeedCertRay.mem_Petal_iff, Work.SeedCert.mem_petal]
  exact ⟨fun h => ⟨h.1, by rw [← seedCert_fatou_eq_fatouW]; exact h.2⟩,
    fun h => ⟨h.1, by rw [seedCert_fatou_eq_fatouW]; exact h.2⟩⟩

/-- `Work.SeedCert.RpetalR4` is `4`. -/
theorem seedCert_RpetalR4 : Work.SeedCert.RpetalR4 = 4 := rfl

/-- `2 ^ -(30 : ℤ)` is positive. -/
theorem seedCert_pow30_pos : (0 : ℝ) < 2 ^ (-(30 : ℤ)) := by norm_num [zpow_neg]

/-- `2 ^ -(20 : ℤ)` is positive. -/
theorem seedCert_pow20_pos : (0 : ℝ) < 2 ^ (-(20 : ℤ)) := by norm_num [zpow_neg]

/-- **`c_b` lies in the ray area's parameter box `Xb`.** -/
theorem seedCert_cb_mem_Xb : Work.SeedCertRay.Xb.mem Work.SeedCert.cb := by
  obtain ⟨hre, hlo, hhi⟩ := Work.SeedCert.cb_in_rayXb
  have e1 : (Work.SeedCertRay.Xb.xl : ℝ) = (-1293728561597 : ℝ) / 2 ^ 40 - 2 ^ (-(30 : ℤ)) := by
    simp only [Work.SeedCertRay.Xb, Work.SeedCertRay.Q, Work.SeedCertRay.MS,
      Work.SeedCertRay.HWM, Work.SeedCertRay.PXM]
    push_cast
    norm_num [zpow_neg]
  have e2 : (Work.SeedCertRay.Xb.xh : ℝ) = (-1293728561597 : ℝ) / 2 ^ 40 + 2 ^ (-(30 : ℤ)) := by
    simp only [Work.SeedCertRay.Xb, Work.SeedCertRay.Q, Work.SeedCertRay.MS,
      Work.SeedCertRay.HWM, Work.SeedCertRay.PXM]
    push_cast
    norm_num [zpow_neg]
  have e3 : (Work.SeedCertRay.Xb.yl : ℝ) = (195856658686 : ℝ) / 2 ^ 40 - 2 ^ (-(30 : ℤ)) := by
    simp only [Work.SeedCertRay.Xb, Work.SeedCertRay.Q, Work.SeedCertRay.MS,
      Work.SeedCertRay.HWM, Work.SeedCertRay.PYM]
    push_cast
    norm_num [zpow_neg]
  have e4 : (Work.SeedCertRay.Xb.yh : ℝ) = (195856658686 : ℝ) / 2 ^ 40 + 2 ^ (-(30 : ℤ)) := by
    simp only [Work.SeedCertRay.Xb, Work.SeedCertRay.Q, Work.SeedCertRay.MS,
      Work.SeedCertRay.HWM, Work.SeedCertRay.PYM]
    push_cast
    norm_num [zpow_neg]
  exact ⟨by rw [e1, hre]; linarith [seedCert_pow30_pos],
    by rw [e2, hre]; linarith [seedCert_pow30_pos],
    by rw [e3]; linarith [seedCert_pow30_pos],
    by rw [e4]; linarith [seedCert_pow30_pos]⟩

/-- **`z₁` lies in the ray area's box `Zb`.** -/
theorem seedCert_z1_mem_Zb : Work.SeedCertRay.Zb.mem Work.SeedCert.z1 := by
  obtain ⟨h1, h2, h3, h4⟩ := Work.SeedCert.z1_in_rayZb
  have e1 : (Work.SeedCertRay.Zb.xl : ℝ) = (-1293130773744 : ℝ) / 2 ^ 40 - 2 ^ (-(20 : ℤ)) := by
    simp only [Work.SeedCertRay.Zb, Work.SeedCertRay.Q, Work.SeedCertRay.MS,
      Work.SeedCertRay.ETA1, Work.SeedCertRay.ZCX]
    push_cast
    norm_num [zpow_neg]
  have e2 : (Work.SeedCertRay.Zb.xh : ℝ) = (-1293130773744 : ℝ) / 2 ^ 40 + 2 ^ (-(20 : ℤ)) := by
    simp only [Work.SeedCertRay.Zb, Work.SeedCertRay.Q, Work.SeedCertRay.MS,
      Work.SeedCertRay.ETA1, Work.SeedCertRay.ZCX]
    push_cast
    norm_num [zpow_neg]
  have e3 : (Work.SeedCertRay.Zb.yl : ℝ) = (195408601406 : ℝ) / 2 ^ 40 - 2 ^ (-(20 : ℤ)) := by
    simp only [Work.SeedCertRay.Zb, Work.SeedCertRay.Q, Work.SeedCertRay.MS,
      Work.SeedCertRay.ETA1, Work.SeedCertRay.ZCY]
    push_cast
    norm_num [zpow_neg]
  have e4 : (Work.SeedCertRay.Zb.yh : ℝ) = (195408601406 : ℝ) / 2 ^ 40 + 2 ^ (-(20 : ℤ)) := by
    simp only [Work.SeedCertRay.Zb, Work.SeedCertRay.Q, Work.SeedCertRay.MS,
      Work.SeedCertRay.ETA1, Work.SeedCertRay.ZCY]
    push_cast
    norm_num [zpow_neg]
  exact ⟨by rw [e1]; linarith [seedCert_pow20_pos],
    by rw [e2]; linarith [seedCert_pow20_pos],
    by rw [e3]; linarith [seedCert_pow20_pos],
    by rw [e4]; linarith [seedCert_pow20_pos]⟩

/-- **`Aquad` lies in the ray area's box `Ab`.** -/
theorem seedCert_Aquad_mem_Ab : Work.SeedCertRay.Ab.mem Work.SeedCert.Aquad := by
  obtain ⟨h1, h2, h3, h4⟩ := Work.SeedCert.Aquad_in_rayAb
  have e1 : (Work.SeedCertRay.Ab.xl : ℝ) = (415268074471237 : ℝ) / 2 ^ 40 - 2 ^ (-(20 : ℤ)) := by
    simp only [Work.SeedCertRay.Ab, Work.SeedCertRay.Q, Work.SeedCertRay.MS,
      Work.SeedCertRay.ETAA, Work.SeedCertRay.ACX]
    push_cast
    norm_num [zpow_neg]
  have e2 : (Work.SeedCertRay.Ab.xh : ℝ) = (415268074471237 : ℝ) / 2 ^ 40 + 2 ^ (-(20 : ℤ)) := by
    simp only [Work.SeedCertRay.Ab, Work.SeedCertRay.Q, Work.SeedCertRay.MS,
      Work.SeedCertRay.ETAA, Work.SeedCertRay.ACX]
    push_cast
    norm_num [zpow_neg]
  have e3 : (Work.SeedCertRay.Ab.yl : ℝ) = (624540193106589 : ℝ) / 2 ^ 40 - 2 ^ (-(20 : ℤ)) := by
    simp only [Work.SeedCertRay.Ab, Work.SeedCertRay.Q, Work.SeedCertRay.MS,
      Work.SeedCertRay.ETAA, Work.SeedCertRay.ACY]
    push_cast
    norm_num [zpow_neg]
  have e4 : (Work.SeedCertRay.Ab.yh : ℝ) = (624540193106589 : ℝ) / 2 ^ 40 + 2 ^ (-(20 : ℤ)) := by
    simp only [Work.SeedCertRay.Ab, Work.SeedCertRay.Q, Work.SeedCertRay.MS,
      Work.SeedCertRay.ETAA, Work.SeedCertRay.ACY]
    push_cast
    norm_num [zpow_neg]
  exact ⟨by rw [e1]; linarith [seedCert_pow20_pos],
    by rw [e2]; linarith [seedCert_pow20_pos],
    by rw [e3]; linarith [seedCert_pow20_pos],
    by rw [e4]; linarith [seedCert_pow20_pos]⟩

/-- **The certified parameter lies in the Mandelbar**, from the *proved* simple case of Fatou's
theorem on parabolic cycles (`Work.FatouParabolic2.fatouParabolicInput_simple`).

`(Tsq c_b)^[5] = (T_cb)^[10]` is the holomorphic return map of the period-`5` cycle; the three
certified facts `g_fix`, `mult_one` and `iteratedDeriv2_ne_zero` make `z₁` a *simple* parabolic
fixed point of it. -/
theorem seedCert_cb_mem_Mandelbar : Work.SeedCert.cb ∈ Mandelbar := by
  have hFatou := Work.FatouParabolic2.fatouParabolicInput_simple
  have hten : ((Work.Landing.Tsq Work.SeedCert.cb)^[5] : ℂ → ℂ) =
      (Tantibar Work.SeedCert.cb)^[10] :=
    Work.SeedCertNum.tsq_iterate_eq_tantibar_iterate Work.SeedCert.cb 5
  have hfix : (Work.Landing.Tsq Work.SeedCert.cb)^[5] Work.SeedCert.z1 = Work.SeedCert.z1 := by
    rw [hten, show (10 : ℕ) = 5 + 5 from rfl,
      Function.iterate_add_apply (f := Tantibar Work.SeedCert.cb) 5 5 Work.SeedCert.z1,
      Work.SeedCert.g_fix, Work.SeedCert.g_fix]
  have hder : deriv ((Work.Landing.Tsq Work.SeedCert.cb)^[5]) Work.SeedCert.z1 = 1 :=
    Work.SeedCert.mult_one
  have h2 : iteratedDeriv 2 ((Work.Landing.Tsq Work.SeedCert.cb)^[5]) Work.SeedCert.z1 ≠ 0 := by
    have h := Work.SeedCert.iteratedDeriv2_ne_zero
    rwa [show Work.FSeed.F Work.SeedCert.cb = (Work.Landing.Tsq Work.SeedCert.cb)^[5]
      from rfl] at h
  exact Work.FatouParabolic2.mem_Mandelbar_of_parabolic_returnMap_simple hFatou hfix hder h2

/-- The dynamical Böttcher homeomorphism of the certified parameter. -/
theorem seedCert_dynBottcherHomeo : Work.ParamRays.DynBottcherHomeo Work.SeedCert.cb :=
  Work.SeedDyn.dynBottcherHomeo seedCert_cb_mem_Mandelbar

end

/-- **The certified root seed.**  The area `SeedCertNum` has certified an explicit parameter
`Work.SeedCert.cb = -1293728561597/2^40 + (195856658686/2^40) i` together with a point
`Work.SeedCert.z1`, a quadratic coefficient `Work.SeedCert.Aquad = F''(z1)/2`, petal constants
`Work.SeedCert.rho1R4`, `Work.SeedCert.deltapR4`, `Work.SeedCert.RpetalR4` and the facts
`g_fix` (`(T_cb)^[5] z1 = z1`), `exact_period` (exact `T_cb`-period `5` of `z1`),
`mult_one` (`multiplier2 cb 5 z1 = 1`), `iteratedDeriv2_ne_zero`
(`iteratedDeriv 2 (F cb) z1 ≠ 0`), `cb_norm_le_two`, plus the box-membership comparisons
`cb_in_rayXb`, `z1_in_rayZb`, `Abox_in_rayAb` and the petal data `ee_petal4_data`
(the two `P1`/`P2` inequalities with `petal`/`fatouW`).

The area `SeedCertRay` proves `landsAt_alphas_data` / `explicitRootSeed_data`: from the ray-chain
certificate plus the `SeedCertNum` data, the two root rays `alpha1 = 371/1023`,
`alpha2 = 404/1023` of `Work.Landing` land at `z1`.

The goal of this task is the single remaining assembly step between the two certified areas and
the seed bundle `Work.SeedExist.ExplicitRootSeed` (the cited-clause-free seed of the project):
combine them, i.e. prove `cb ∈ Mandelbar` from the **proved** simple case of the classical Fatou
result (`Work.FatouParabolic2.fatouParabolicInput_simple` via
`Work.FatouParabolic2.mem_Mandelbar_of_parabolic_returnMap_simple`, using `g_fix`, `mult_one`
and `iteratedDeriv2_ne_zero`), take the Böttcher data
`hN := Work.ParamRays.dynNakane (Work.SeedDyn.dynBottcherHomeo hcb)`,
`hφ := Work.ParamRays.isDynBottcher_dynPhiOf (Work.SeedDyn.dynBottcherHomeo hcb).exists`,
bridge the box memberships `Work.SeedCertRay.Xb.mem cb`, `Zb.mem z1`, `Ab.mem Aquad` with the
plain-real inequalities of `Work.SeedCert.Locate`, bridge `Work.SeedCertRay.Petal`/`fatou` with
`Work.SeedCert.petal`/`fatouW` and `Work.SeedCert.RpetalR4 = 4`, and apply
`Work.SeedCertRay.explicitRootSeed_data`. -/
theorem seedCert : Work.SeedExist.ExplicitRootSeed := by
  obtain ⟨hAne, hρ₁, hδ, hRQ, hP1raw, hP2raw⟩ := Work.SeedCert.ee_petal4_data
  have hr4 : Work.SeedCert.RpetalR4 = 4 := seedCert_RpetalR4
  refine Work.SeedCertRay.explicitRootSeed_data
    (c := Work.SeedCert.cb) (z₁ := Work.SeedCert.z1) (A := Work.SeedCert.Aquad)
    (φ := Work.ParamRays.dynPhiOf Work.SeedCert.cb)
    ?hN ?hφ seedCert_cb_mem_Mandelbar Work.SeedCert.cb_norm_le_two
    seedCert_cb_mem_Xb seedCert_z1_mem_Zb seedCert_Aquad_mem_Ab
    Work.SeedCert.g_fix Work.SeedCert.exact_period Work.SeedCert.mult_one
    Work.SeedCert.iteratedDeriv2_ne_zero Work.SeedCert.deltapR4 Work.SeedCert.rho1R4
    hρ₁ hδ hAne ?hRQ ?hP1 ?hP2
  · exact Work.ParamRays.dynNakane seedCert_dynBottcherHomeo
  · exact Work.ParamRays.isDynBottcher_dynPhiOf seedCert_dynBottcherHomeo.exists
  · exact hRQ
  · intro z hz
    have h := hP1raw (z - Work.SeedCert.z1) (by simpa using hz)
    rw [hr4] at h
    rw [show Work.SeedCert.z1 + (z - Work.SeedCert.z1) = z by ring] at h
    rw [← seedCert_petal_eq_petalW] at h
    exact h
  · intro z hz hm
    have hm' : Work.FSeed.F Work.SeedCert.cb z ∈
        Work.SeedCert.petal Work.SeedCert.z1 Work.SeedCert.Aquad 4 := by
      rw [← seedCert_petal_eq_petalW]
      exact hm
    obtain ⟨h1, h2⟩ := hP2raw z hz (by rwa [hr4])
    refine ⟨?_, ?_⟩
    · rw [seedCert_petal_eq_petalW]
      rwa [hr4] at h1
    · rw [seedCert_fatou_eq_fatouW, seedCert_fatou_eq_fatouW]
      exact h2

end Work.MandelFinal
