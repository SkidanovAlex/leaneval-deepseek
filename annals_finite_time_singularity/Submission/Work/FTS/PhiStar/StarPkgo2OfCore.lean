import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS.VocabO
import Submission.Work.FTS.PhiStar.wlInf_of_zeroOff
import Submission.Work.FTS.PhiStar.Defs
import Submission.Work.FTS.PhiStar.CoreAux.Defs
import Submission.Work.FTS.PhiStar.CoreAux.FieldsDefs
import Submission.Work.FTS.PhiStar.CoreAux.F0_add
import Submission.Work.FTS.PhiStar.CoreAux.F0_mul
import Submission.Work.FTS.PhiStar.CoreAux.F0_zpz
import Submission.Work.FTS.PhiStar.CoreAux.Fb_zpz
import Submission.Work.FTS.PhiStar.CoreAux.Fb_basic
import Submission.Work.FTS.PhiStar.CoreAux.Fb_add
import Submission.Work.FTS.PhiStar.CoreAux.Fb_of_FlatW
import Submission.Work.FTS.PhiStar.CoreAux.F0_congr
import Submission.Work.FTS.PhiStar.CoreAux.F0_to_WDp
import Submission.Work.FTS.PhiStar.CoreAux.F0_to_CoefTh
import Submission.Work.FTS.PhiStar.CoreAux.smoothOpen_PhiTs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Construction.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.PhiStar.StarPkgo2Aux.CoeffF0
import Submission.Work.FTS.PhiStar.StarPkgo2Aux.FbEH
import Submission.Work.FTS.PhiStar.StarPkgo2Aux.FbEV
import Submission.Work.FTS.PhiStar.StarPkgo2Aux.FbEU
import Submission.Work.FTS.PhiStar.StarPkgo2Aux.F0EPU
import Submission.Work.FTS.PhiStar.StarPkgo2Aux.FieldIdents
import Submission.Work.FTS.PhiStar.StarPkgo2Aux.ZeroOffFields
import Submission.Work.FTS.PhiStar.StarPkgo2Aux.FieldRegularity

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

/-- `Fb n K f` gives the `FlatW n K f` consumed by `wlInf_of_zeroOff`. -/
private theorem Fb_to_FlatW {n : ℕ} {K : ℝ} {f : ℝ → ℝ → ℝ} (h : Fb n K f) :
    Work.FTS.VocabO2.FlatW n f K := by
  intro z θ hz hθ hθ2
  refine ⟨fun k _ => ?_, fun k i hki => ?_⟩
  · simpa using h.f0 k 0 (by omega) z θ hz hθ hθ2
  · exact h.fd k i (by omega) z θ hz hθ hθ2

/-- `Fb` transfers along pointwise equality on the open quadrant. -/
private theorem Fb_congr_p {n : ℕ} {K : ℝ} {f g : ℝ → ℝ → ℝ}
    (h : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → f z θ = g z θ)
    (hg : Fb n K g) : Fb n K f := by
  refine ⟨Work.FTS.PhiStar.CoreAux.F0_congr h hg.f0, Work.FTS.PhiStar.CoreAux.F0_congr ?_ hg.fd⟩
  intro z θ hz hθ hθ'
  have hev : (fun θ' => f z θ') =ᶠ[𝓝 θ] (fun θ' => g z θ') := by
    filter_upwards [isOpen_Ioo.mem_nhds (show θ ∈ Set.Ioo 0 (Real.pi / 2) from ⟨hθ, hθ'⟩)]
      with θ' hθ''
    exact h z θ' hz hθ''.1 hθ''.2
  exact hev.deriv_eq

theorem StarPkgo2OfCore : ∃ C : ℝ, 0 < C ∧ ∀ (α Cs : ℝ) (Φs : Work.FTS.Galerkin.Fn),
    0 < α → α ≤ 1 / 4 → 0 < Cs → Work.FTS.VocabO2.StarCore α Cs Φs → Work.FTS.VocabO2.StarPkgo2 α (C * Cs) Φs := by
  obtain ⟨A0, hA0ge, hth1₀, hth2₀, hth3₀, hth4₀, hz1₀, hz2₀⟩ := StarPkgo2Aux.CoeffF0
  obtain ⟨C1, hC1pos, hFbFlat⟩ := Work.FTS.PhiStar.CoreAux.Fb_of_FlatW
  obtain ⟨Ce, hCepos, hEHb⟩ := StarPkgo2Aux.FbEH
  obtain ⟨Cv, hCvpos, hEVb⟩ := StarPkgo2Aux.FbEV
  obtain ⟨Cu, hCupos, hEUb⟩ := StarPkgo2Aux.FbEU
  obtain ⟨Cp, hCppos, hEPUb⟩ := StarPkgo2Aux.F0EPU
  obtain ⟨Cwd, hCwdpos, hWDp4⟩ := Work.FTS.PhiStar.CoreAux.F0_to_WDp 4
  obtain ⟨Cwd5, hCwd5pos, hWDp5⟩ := Work.FTS.PhiStar.CoreAux.F0_to_WDp 5
  obtain ⟨Cct, hCctpos, hCoeffTh⟩ := Work.FTS.PhiStar.CoreAux.F0_to_CoefTh 3
  obtain ⟨Cwl, hCwlpos, hWlInf⟩ := wlInf_of_zeroOff
  generalize hAdef : A0 + C1 + Ce + Cv + Cu + Cp + Cwd + Cwd5 + Cct + Cwl + 2 = A
  have hA1 : 1 ≤ A := by
    rw [← hAdef]; linarith [hA0ge, le_of_lt hC1pos, le_of_lt hCepos, le_of_lt hCvpos,
      le_of_lt hCupos, le_of_lt hCppos, le_of_lt hCwdpos, le_of_lt hCwd5pos,
      le_of_lt hCctpos, le_of_lt hCwlpos]
  have hA0 : 0 < A := lt_of_lt_of_le one_pos hA1
  have hA0A : A0 ≤ A := by rw [← hAdef]; linarith
  have hAC1 : C1 ≤ A := by rw [← hAdef]; linarith
  have hAe : Ce ≤ A := by rw [← hAdef]; linarith
  have hAv : Cv ≤ A := by rw [← hAdef]; linarith
  have hAu : Cu ≤ A := by rw [← hAdef]; linarith
  have hAp : Cp ≤ A := by rw [← hAdef]; linarith
  have hAwd : Cwd ≤ A := by rw [← hAdef]; linarith
  have hAwd5 : Cwd5 ≤ A := by rw [← hAdef]; linarith
  have hAct : Cct ≤ A := by rw [← hAdef]; linarith
  have hAwl : Cwl ≤ A := by rw [← hAdef]; linarith
  refine ⟨2 * A ^ 6 + 1, by positivity, ?_⟩
  intro α Cs Φs hα hα4 hCs hs
  have hα1 : α ≤ 1 := by linarith
  have hα2 : α + 1 ≤ 2 := by linarith
  have hS0 : 0 ≤ Cs * α := by positivity
  let Ψ : ℝ → ℝ → ℝ := Work.FTS.VocabO2.PhiTs α Φs
  let Y : ℝ → ℝ → ℝ := Work.FTS.VocabO2.Ycheck α Φs
  let fRW : ℝ → ℝ → ℝ :=
    fun z θ => (z + 1) / z * Work.Construction.Rop α (Work.FTS.VocabO2.PhiTs α Φs) z θ
  let fV : ℝ → ℝ → ℝ := Work.Construction.Vop (Work.FTS.VocabO2.PhiTs α Φs)
  let fVz : ℝ → ℝ → ℝ :=
    fun z θ => (z + 1) / z * Work.Construction.Vop (Work.FTS.VocabO2.PhiTs α Φs) z θ
  let fUs : ℝ → ℝ → ℝ :=
    fun z θ => Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs) z θ / Work.Construction.s2 θ
  let fUsz : ℝ → ℝ → ℝ :=
    fun z θ => (z + 1) / z * (Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs) z θ
      / Work.Construction.s2 θ)
  let fDU : ℝ → ℝ → ℝ := Work.Spaces.pth (Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs))
  have hsmΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    (Work.FTS.PhiStar.CoreAux.smoothOpen_PhiTs hα hα1 hs.smooth).1
  have hsmY : Work.FTS.EllipticEst.SmoothOpen Y :=
    (Work.FTS.PhiStar.CoreAux.smoothOpen_PhiTs hα hα1 hs.smooth).2.2
  have hFbY : Fb 6 (A * (Cs * α)) Y := by
    refine Fb.mono le_rfl ?_ (hFbFlat (Cs * α) Y (by positivity) hsmY hs.core)
    nlinarith [hAC1, hS0]
  have hsq : F0 6 A (fun _ θ => Real.sin θ ^ 2) := F0.mono le_rfl hA0A hth1₀
  have hccs : F0 6 A (fun _ θ => Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2) :=
    F0.mono le_rfl hA0A hth2₀
  have hc2 : F0 6 A (fun _ θ => Real.cos (2 * θ)) := F0.mono le_rfl hA0A hth3₀
  have hsi : F0 6 A (fun _ θ => Real.sin (2 * θ)) := F0.mono le_rfl hA0A hth4₀
  have hcz : F0 6 A (fun z _ => z / (1 + z)) := F0.mono le_rfl hA0A hz1₀
  have hci : F0 6 A (fun z _ => (1 + z)⁻¹) := F0.mono le_rfl hA0A hz2₀
  have hident := StarPkgo2Aux.FieldIdents α Ψ Y hsmΨ (fun z θ _ => rfl)
  have hreg := StarPkgo2Aux.FieldRegularity α Ψ hsmΨ
  have hzer := StarPkgo2Aux.ZeroOffFields α Ψ hs.zeroOff
  -- ## the flat bounds of the clean expressions
  have hFbEH := hEHb α (Cs * α) A Y (le_of_lt hα) hS0 hA1 hsmY hsq hccs hc2 hsi hcz hci hFbY
  have hFbEV := hEVb α (Cs * α) A Y (le_of_lt hα) hS0 hA1 hsmY hsq hccs hc2 hsi hcz hci hFbY
  have hFbEU := hEUb α (Cs * α) A Y (le_of_lt hα) hS0 hA1 hsmY hsq hccs hc2 hsi hcz hci hFbY
  have hF0EPU := hEPUb α (Cs * α) A Y (le_of_lt hα) hS0 hA1 hsmY hsq hccs hc2 hsi hcz hci hFbY
  -- ## transfer to the actual fields
  have hFbRW : Fb 4 (Ce * A ^ 4 * (Cs * α) * (α + 1)) fRW :=
    Fb_congr_p (fun z θ hz hθ hθ2 => ((hident z θ (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ, hθ2⟩)).1).symm) hFbEH
  have hFbV : Fb 4 (Cv * A ^ 4 * (Cs * α) * (α + 1)) fV :=
    Fb_congr_p (fun z θ hz hθ hθ2 => ((hident z θ (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ, hθ2⟩)).2.1).symm) hFbEV.2
  have hFbVz : Fb 4 (Cv * A ^ 4 * (Cs * α) * (α + 1)) fVz :=
    Fb_congr_p (fun z θ hz hθ hθ2 => ((hident z θ (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ, hθ2⟩)).2.2.1).symm) hFbEV.1
  have hFbUs : Fb 4 (Cu * A ^ 4 * (Cs * α) * (α + 1)) fUs :=
    Fb_congr_p (fun z θ hz hθ hθ2 => ((hident z θ (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ, hθ2⟩)).2.2.2.1).symm) hFbEU.2
  have hFbUsz : Fb 4 (Cu * A ^ 4 * (Cs * α) * (α + 1)) fUsz :=
    Fb_congr_p (fun z θ hz hθ hθ2 => ((hident z θ (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ, hθ2⟩)).2.2.2.2.1).symm) hFbEU.1
  have hF0DU : F0 5 (Cp * A ^ 4 * (Cs * α) * (α + 1)) fDU :=
    Work.FTS.PhiStar.CoreAux.F0_congr
      (fun z θ hz hθ hθ2 => ((hident z θ (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ, hθ2⟩)).2.2.2.2.2).symm) hF0EPU
  -- ## the `𝒲`-bounds
  have hWlRW := hWlInf α fRW (Ce * A ^ 4 * (Cs * α) * (α + 1)) hα hα1
    hzer.1 hreg.1 (Fb_to_FlatW hFbRW)
  have hWlV := hWlInf α fV (Cv * A ^ 4 * (Cs * α) * (α + 1)) hα hα1
    hzer.2.1 hreg.2.1 (Fb_to_FlatW hFbV)
  have hWlVz := hWlInf α fVz (Cv * A ^ 4 * (Cs * α) * (α + 1)) hα hα1
    hzer.2.2.1 hreg.2.2.1 (Fb_to_FlatW hFbVz)
  have hWlUs := hWlInf α fUs (Cu * A ^ 4 * (Cs * α) * (α + 1)) hα hα1
    hzer.2.2.2.1 hreg.2.2.2.1 (Fb_to_FlatW hFbUs)
  have hWlUsz := hWlInf α fUsz (Cu * A ^ 4 * (Cs * α) * (α + 1)) hα hα1
    hzer.2.2.2.2 hreg.2.2.2.2.1 (Fb_to_FlatW hFbUsz)
  -- ## the old fields
  have hWDRW := hWDp4 (Ce * A ^ 4 * (Cs * α) * (α + 1)) fRW (by positivity) hreg.1 hFbRW.1
  have hWDV := hWDp4 (Cv * A ^ 4 * (Cs * α) * (α + 1)) fV (by positivity) hreg.2.1 hFbV.1
  have hWDDU := hWDp5 (Cp * A ^ 4 * (Cs * α) * (α + 1)) fDU (by positivity)
    hreg.2.2.2.2.2 hF0DU
  have hCfV := hCoeffTh (Cv * A ^ 4 * (Cs * α) * (α + 1)) fV (by positivity) hreg.2.1
    (F0.mono (by norm_num : 3 ≤ 4) le_rfl hFbV.2)
  -- ## the constant comparisons
  have hbig : ∀ x y : ℝ, 0 ≤ x → x ≤ A → 0 ≤ y → y ≤ A →
      x * (y * A ^ 4 * (Cs * α) * (α + 1)) ≤ ((2 * A ^ 6 + 1) * Cs) * α := by
    intro x y hx0 hxA hy0 hyA
    have hxy : x * y ≤ A * A := mul_le_mul hxA hyA hy0 (by linarith)
    have hA4 : 0 ≤ A ^ 4 := by positivity
    have h1 : A ^ 4 * (Cs * α) * (α + 1) ≤ A ^ 4 * (Cs * α) * 2 :=
      mul_le_mul_of_nonneg_left hα2 (by positivity)
    have h2 : x * (y * A ^ 4 * (Cs * α) * (α + 1)) ≤ (A * A) * (A ^ 4 * (Cs * α) * 2) := by
      rw [show x * (y * A ^ 4 * (Cs * α) * (α + 1))
        = (x * y) * (A ^ 4 * (Cs * α) * (α + 1)) from by ring]
      exact mul_le_mul hxy h1 (by positivity) (by positivity)
    have h3 : (A * A) * (A ^ 4 * (Cs * α) * 2) = 2 * A ^ 6 * (Cs * α) := by ring
    rw [h3] at h2
    have h4 : 2 * A ^ 6 * (Cs * α) ≤ ((2 * A ^ 6 + 1) * Cs) * α := by
      have h5 : 2 * A ^ 6 * (Cs * α) = (2 * A ^ 6) * (Cs * α) := by ring
      rw [h5]
      have h6 : 2 * A ^ 6 ≤ 2 * A ^ 6 + 1 := by linarith
      calc (2 * A ^ 6) * (Cs * α) ≤ (2 * A ^ 6 + 1) * (Cs * α) :=
            mul_le_mul_of_nonneg_right h6 hS0
        _ = ((2 * A ^ 6 + 1) * Cs) * α := by ring
    linarith
  -- ## `vanishU`
  have hvanish : Work.Spaces.VanishTheta (Work.Construction.Uop α Ψ) := by
    have hz0 : ∀ z : ℝ, (z, (0 : ℝ)) ∉ Work.FTS.EllipticEst.Q0 := by
      intro z hmem
      exact absurd (Work.FTS.EllipticEst.mem_Q0.mp hmem).2.1 (lt_irrefl 0)
    have hzπ : ∀ z : ℝ, (z, Real.pi / 2) ∉ Work.FTS.EllipticEst.Q0 := by
      intro z hmem
      exact absurd (Work.FTS.EllipticEst.mem_Q0.mp hmem).2.2 (lt_irrefl _)
    refine ⟨fun z => ?_, fun z => ?_⟩
    · show Work.Construction.Uop α Ψ z 0 = 0
      have h1 : Ψ z 0 = 0 := hs.zeroOff z 0 (hz0 z)
      have hsl : (fun z' : ℝ => Ψ z' 0) = fun _ => (0 : ℝ) :=
        funext (fun z' => hs.zeroOff z' 0 (hz0 z'))
      have h2 : Work.Spaces.pz Ψ z 0 = 0 := by
        simp only [Work.Spaces.pz]
        rw [hsl]
        simp
      simp only [Work.Construction.Uop, h1, h2]
      ring
    · show Work.Construction.Uop α Ψ z (Real.pi / 2) = 0
      have h1 : Ψ z (Real.pi / 2) = 0 := hs.zeroOff z (Real.pi / 2) (hzπ z)
      have hsl : (fun z' : ℝ => Ψ z' (Real.pi / 2)) = fun _ => (0 : ℝ) :=
        funext (fun z' => hs.zeroOff z' (Real.pi / 2) (hzπ z'))
      have h2 : Work.Spaces.pz Ψ z (Real.pi / 2) = 0 := by
        simp only [Work.Spaces.pz]
        rw [hsl]
        simp
      simp only [Work.Construction.Uop, h1, h2]
      ring
  exact
    { toStarPkgo :=
        { sol := hs.sol
          smooth := hs.smooth
          R := ⟨hWDRW.1, le_trans hWDRW.2 (hbig Cwd Ce (by positivity) hAwd (by positivity) hAe)⟩
          dU := ⟨hWDDU.1, le_trans hWDDU.2 (hbig Cwd5 Cp (by positivity) hAwd5 (by positivity) hAp)⟩
          V := ⟨hWDV.1, le_trans hWDV.2 (hbig Cwd Cv (by positivity) hAwd (by positivity) hAv)⟩
          vanishU := hvanish
          Vth := ⟨hCfV.1, le_trans hCfV.2 (hbig Cct Cv (by positivity) hAct (by positivity) hAv)⟩ }
      RW := ⟨hWlRW.1, le_trans hWlRW.2 (hbig Cwl Ce (by positivity) hAwl (by positivity) hAe)⟩
      VW := ⟨hWlV.1, le_trans hWlV.2 (hbig Cwl Cv (by positivity) hAwl (by positivity) hAv)⟩
      VzW := ⟨hWlVz.1, le_trans hWlVz.2 (hbig Cwl Cv (by positivity) hAwl (by positivity) hAv)⟩
      UsW := ⟨hWlUs.1, le_trans hWlUs.2 (hbig Cwl Cu (by positivity) hAwl (by positivity) hAu)⟩
      UszW := ⟨hWlUsz.1, le_trans hWlUsz.2 (hbig Cwl Cu (by positivity) hAwl (by positivity) hAu)⟩ }

end Work.FTS.PhiStar
