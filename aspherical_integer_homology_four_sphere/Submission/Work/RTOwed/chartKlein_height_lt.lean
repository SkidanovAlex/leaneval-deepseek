import Mathlib
import Submission.Work.RTOwed.heightCerts
import Submission.Work.RTOwed.cuspChartBeta
import Submission.Work.RTOwed.cuspCert.lattice_bridge
import Submission.Work.RTOwed.cuspCert.CuspSupport

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Work.RTOwed

noncomputable section

open scoped Matrix BigOperators
open Matrix Set Topology Function

/-! ## The analytic bounds for `tDel` -/

/-- **`tDel` is positive** on `cubeBox a × [11/10,∞)`, from the certificate `tcertD_pos`. -/
theorem tDel_pos {a b : Fin 48} (hne : a ≠ b) (hbit : cubeBit a = cubeBit b)
    {x : CuspE3} (hx : x ∈ cubeBox a) {s : ℝ} (hs : 11/10 ≤ s) : 0 < tDel a b x s := by
  have hc : 0 < (tCp a b : ℝ) := by exact_mod_cast tCp_pos a b hne hbit
  have hcertR : 0 < 121*(tCp a b:ℝ)^2 + 100*(tCp a b:ℝ)*(tEp a b:ℝ)
      - 100*∑ j:Fin 3, (tLp a b j:ℝ)^2 := by
    have h := tcertD_pos a b hne hbit
    have hcast : ((121 * tCp a b ^ 2 + 100 * tCp a b * tEp a b
        - 100 * ∑ j : Fin 3, tLp a b j ^ 2 : ℤ) : ℝ)
        = 121*(tCp a b:ℝ)^2 + 100*(tCp a b:ℝ)*(tEp a b:ℝ)
          - 100*∑ j:Fin 3, (tLp a b j:ℝ)^2 := by
      push_cast; ring
    rw [← hcast]; exact_mod_cast h
  rw [tDel_eq]
  have hb := chartKleinMem.quad_bound_pos (c := (tCp a b:ℝ)) (e := (tEp a b:ℝ))
      (l := fun j : Fin 3 => 2*(tLp a b j:ℝ)) hc x s hs
  have heq : (4*(tCp a b:ℝ)*((tCp a b:ℝ)*(11/10)^2 + (tEp a b:ℝ))
        - ∑ j:Fin 3, (2*(tLp a b j:ℝ))^2)/(4*(tCp a b:ℝ))
      = (121*(tCp a b:ℝ)^2 + 100*(tCp a b:ℝ)*(tEp a b:ℝ)
        - 100*∑ j:Fin 3, (tLp a b j:ℝ)^2)/(100*(tCp a b:ℝ)) := by
    have hsum : ∑ j:Fin 3, (2*(tLp a b j:ℝ))^2 = 4 * ∑ j:Fin 3, (tLp a b j:ℝ)^2 := by
      simp only [Fin.sum_univ_three]; ring
    rw [hsum]
    have hc0 : (tCp a b : ℝ) ≠ 0 := ne_of_gt hc
    field_simp
    ring
  rw [heq] at hb
  exact lt_of_lt_of_le (div_pos hcertR (by positivity)) hb

/-- **`11 tDel - 20 (chartScale a)(chartScale b) s` is positive** on the region, from the
certificate `tcertG_pos`. -/
theorem tG_pos {a b : Fin 48} (hne : a ≠ b) (hbit : cubeBit a = cubeBit b)
    {x : CuspE3} (hx : x ∈ cubeBox a) {s : ℝ} (hs : 11/10 ≤ s) :
    0 < 11 * tDel a b x s - 20 * s * chartScale a * chartScale b := by
  have hc : 0 < (tCp a b : ℝ) := by exact_mod_cast tCp_pos a b hne hbit
  have hscale : 100 * (chartScale a * chartScale b) ≤ 121 * (tCp a b : ℝ) := by
    have h := tCp_ge a b hne hbit
    have hcast : ((100 * chartScaleZ a * chartScaleZ b : ℤ) : ℝ)
        = 100 * (chartScale a * chartScale b) := by
      simp only [chartScale]; push_cast; ring
    have hcast2 : ((121 * tCp a b : ℤ) : ℝ) = 121 * (tCp a b : ℝ) := by push_cast; ring
    rw [← hcast, ← hcast2]; exact_mod_cast h
  have hcertG : 0 < 1331*(tCp a b:ℝ)^2 - 2200*(chartScale a * chartScale b)*(tCp a b:ℝ)
      - 1100*∑ j:Fin 3, (tLp a b j:ℝ)^2 + 1100*(tCp a b:ℝ)*(tEp a b:ℝ) := by
    have h := tcertG_pos a b hne hbit
    have hcast : ((1331 * tCp a b ^ 2 - 2200 * (chartScaleZ a * chartScaleZ b) * tCp a b
        - 1100 * ∑ i : Fin 3, tLp a b i ^ 2 + 1100 * tCp a b * tEp a b : ℤ) : ℝ)
        = 1331*(tCp a b:ℝ)^2 - 2200*(chartScale a * chartScale b)*(tCp a b:ℝ)
          - 1100*∑ j:Fin 3, (tLp a b j:ℝ)^2 + 1100*(tCp a b:ℝ)*(tEp a b:ℝ) := by
      simp only [chartScale]; push_cast; ring
    rw [← hcast]; exact_mod_cast h
  have hspart : 1331*(tCp a b:ℝ)^2 - 2200*(chartScale a * chartScale b)*(tCp a b:ℝ)
      ≤ 1100*(tCp a b:ℝ)^2 * s^2 - 2000*(tCp a b:ℝ)*s*(chartScale a * chartScale b) := by
    have h1 : 0 ≤ s - 11/10 := by linarith
    have h2 : 0 ≤ 1100*(tCp a b:ℝ)^2*(s+11/10) - 2000*(tCp a b:ℝ)*(chartScale a * chartScale b) := by
      nlinarith [hs, hc, hscale]
    have h3 := mul_nonneg h1 h2
    nlinarith [h3]
  have hxpart : -1100 * (∑ j:Fin 3, (tLp a b j:ℝ)^2)
      ≤ 1100*(tCp a b:ℝ)^2 * (∑ j:Fin 3, (x j)^2)
        + 2200*(tCp a b:ℝ) * (∑ j:Fin 3, (tLp a b j:ℝ) * x j) := by
    have h : (0:ℝ) ≤ ∑ j:Fin 3, 1100 * ((tCp a b:ℝ) * x j + (tLp a b j:ℝ))^2 := by
      apply Finset.sum_nonneg; intro j _; positivity
    simp only [Fin.sum_univ_three] at h
    simp only [Fin.sum_univ_three]
    nlinarith [h]
  rw [tDel_eq, chartKleinMem.qsq]
  simp only [Fin.sum_univ_three]
  have hb2 : -1100 * ((tLp a b 0:ℝ)^2 + (tLp a b 1:ℝ)^2 + (tLp a b 2:ℝ)^2)
      ≤ 1100*(tCp a b:ℝ)^2 * ((x 0)^2 + (x 1)^2 + (x 2)^2)
        + 2200*(tCp a b:ℝ) * ((tLp a b 0:ℝ)*(x 0) + (tLp a b 1:ℝ)*(x 1) + (tLp a b 2:ℝ)*(x 2)) := by
    simpa only [Fin.sum_univ_three] using hxpart
  have hg2 : 0 < 1331*(tCp a b:ℝ)^2 - 2200*(chartScale a * chartScale b)*(tCp a b:ℝ)
      - 1100*((tLp a b 0:ℝ)^2 + (tLp a b 1:ℝ)^2 + (tLp a b 2:ℝ)^2)
      + 1100*(tCp a b:ℝ)*(tEp a b:ℝ) := by
    simpa only [Fin.sum_univ_three] using hcertG
  have key : (0:ℝ) < 100*(tCp a b:ℝ) *
      (11*((tCp a b:ℝ)*((x 0)^2+(x 1)^2+(x 2)^2+s^2)
        + (2*(tLp a b 0:ℝ)*(x 0) + 2*(tLp a b 1:ℝ)*(x 1) + 2*(tLp a b 2:ℝ)*(x 2))
        + (tEp a b:ℝ))
       - 20*s*chartScale a*chartScale b) := by
    nlinarith [hspart, hb2, hg2]
  exact (mul_pos_iff_of_pos_left (show (0:ℝ) < 100*(tCp a b:ℝ) by positivity)).mp key

/-! ## The separation theorem -/

/-- **Same-bit cubes are separated by the height `11/10`.** -/
theorem chartKlein_height_lt {a b : Fin 48} (hne : a ≠ b)
    (hbit : Work.RTOwed.cubeBit a = Work.RTOwed.cubeBit b)
    {x : Work.RTOwed.CuspE3} (hx : x ∈ Work.RTOwed.cubeBox a) {s : ℝ} (hs : 11 / 10 ≤ s) :
    ∃ (x' : Work.RTOwed.CuspE3) (s' : ℝ), 0 < s' ∧ s' < 11 / 10 ∧
      Work.RTOwed.chartKlein a (Work.RTOwed.mkE4 x s) =
        Work.RTOwed.chartKlein b (Work.RTOwed.mkE4 x' s') := by
  have hs0 : 0 < s := by linarith
  have hL : Work.HypModel.IsLorentzMat (tM a b) := tM_lorentz a b
  have hUHS : Work.HypModel.hypOfUHS (mkE4 x s) ∈ Work.HypModel.upperSheet :=
    hypOfUHS_mem_upperSheet (by
      show 0 < (mkE4 x s) 3
      rw [chartKleinMem.mkE4_apply_three]; exact hs0)
  set P : Work.HypModel.V5 := tM a b *ᵥ Work.HypModel.hypOfUHS (mkE4 x s) with hP
  have hPmem : P ∈ Work.HypModel.upperSheet := Work.HypModel.mulVec_mem_upperSheet hL hUHS
  set q' : Work.HypModel.E4 := Work.HypModel.uhsOfHyp P with hq'
  have hhyp : Work.HypModel.hypOfUHS q' = P := Work.HypModel.hypOfUHS_uhsOfHyp hPmem
  have hlt43 : P 4 - P 3 = (2*s)⁻¹ * (chartScale a * chartScale b)⁻¹ * tDel a b x s := by
    rw [hP]; exact tM_mulVec_43 a b x s
  have hP43pos : 0 < P 4 - P 3 := Work.HypModel.upperSheet_four_sub_three_pos hPmem
  have htDelpos : 0 < tDel a b x s := tDel_pos hne hbit hx hs
  have hs'pos : 0 < q' 3 := by
    rw [hq', Work.HypModel.uhsOfHyp_apply_three]
    exact inv_pos.mpr hP43pos
  have hq3 : q' 3 = 2*s*chartScale a * chartScale b / tDel a b x s := by
    rw [hq', Work.HypModel.uhsOfHyp_apply_three, hlt43, div_eq_mul_inv]
    rw [_root_.mul_inv_rev, _root_.mul_inv_rev]
    simp only [inv_inv]
    ring
  have hbound : q' 3 < 11/10 := by
    rw [hq3, div_lt_iff₀ htDelpos]
    have := tG_pos hne hbit hx hs
    linarith
  refine ⟨xOf4 q', q' 3, hs'pos, hbound, ?_⟩
  have hmk : mkE4 (xOf4 q') (q' 3) = q' := by
    apply PiLp.ext; intro i; fin_cases i <;> simp [mkE4, xOf4]
  rw [hmk, chartKlein_eq a (mkE4 x s), chartKlein_eq b q', hhyp]
  congr 1
  rw [hP, Matrix.mulVec_mulVec, tM_spec]

end

end Work.RTOwed
