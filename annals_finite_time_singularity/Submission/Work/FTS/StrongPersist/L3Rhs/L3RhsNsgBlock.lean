import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.LocData.zero_slice_locG
import Submission.Work.FTS.Nonlinear.Pieces.rl1Pieces.PsgEngine
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.StarSlotPcs.DzdIterBound
import Submission.Work.FTS.StrongPersist.L3Rhs.Defs
import Submission.Work.FTS.StrongPersist.L3Rhs.L3MulDth
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_MuLamOK.Conversion
import Submission.Work.FTS_RegExport.RXT.jc3_aux
import Submission.Work.FTS_RegExport.RXT.velVanish2Star
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.L3Rhs

open Work.FTS.Galerkin (Fn)
open Work.Spaces (HkMem HkSq HkNorm)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## The three summands on the open quadrant -/


/-- `N₂^{sg} = -2𝒰(Φ̃_*)·∂_θf = -2·(𝒰(Φ̃_*)/sin 2θ)·D_θf` on the open quadrant. -/
private theorem nsg_alg2 (α : ℝ) (Φs f : Fn) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.FTS.Nonlin.N2sg α Φs f z θ
        = -2 * (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ
            / Work.Construction.s2 θ) * Work.Spaces.Dth f z θ := by
  intro z θ hz hθ hθ2
  have hs : Real.sin (2 * θ) ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos]))
  simp only [Work.FTS.Nonlin.N2sg, Work.Spaces.Dth, Work.Construction.s2]
  field_simp [hs]

/-- `N₃^{sg} = -2α𝒱(Φ̃_*)·D_zf` (definitionally). -/
private theorem nsg_alg3 (α : ℝ) (Φs f : Fn) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.FTS.Nonlin.N3sg α Φs f z θ
        = (-2 * α) * Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) z θ
            * Work.Spaces.Dz f z θ := by
  intro z θ hz hθ hθ2
  simp only [Work.FTS.Nonlin.N3sg]

/-! ## Smoothness of the block on the open quadrant -/

private theorem nsg_smooth (α Cs : ℝ) (Φs f : Fn) (hα : 0 < α) (hα1 : α ≤ 1)
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.FTS.EllipticEst.SmoothOpen (NSgSum α Φs f) := by
  have hΨ : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.PhiTs α Φs) :=
    Work.FTS.NonlinRows.NRow10aux.smoothOpen_PhiTs hα hα1 hstar.toStarPkgo
  have hR : Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs)) :=
    Work.FTS.NonlinRows.smoothOpen_Rop hΨ
  have hU : Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs)) :=
    Work.FTS.NonlinRows.Rl1.smoothOpen_Uop_open hΨ
  have hV : Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs)) :=
    Work.FTS.NonlinRows.Rl1.smoothOpen_Vop_open hΨ
  have h1 : Work.FTS.EllipticEst.SmoothOpen (fun z θ =>
      2 * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ * f z θ) := by
    show ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => 2 * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) p.1 p.2
        * f p.1 p.2) Work.FTS.EllipticEst.Q0
    exact (contDiffOn_const.mul hR).mul hf
  have h2 : Work.FTS.EllipticEst.SmoothOpen (fun z θ =>
      -2 * Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ
        * Work.Spaces.pth f z θ) := by
    show ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => -2 * Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) p.1 p.2
        * Work.Spaces.pth f p.1 p.2) Work.FTS.EllipticEst.Q0
    exact ((contDiffOn_const.mul hU).mul (Work.FTS.EllipticEst.SmoothOpen.pth hf))
  have h3 : Work.FTS.EllipticEst.SmoothOpen (fun z θ =>
      -2 * α * Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) z θ
        * Work.Spaces.Dz f z θ) := by
    show ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => -2 * α * Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) p.1 p.2
        * Work.Spaces.Dz f p.1 p.2) Work.FTS.EllipticEst.Q0
    exact (((contDiffOn_const.mul contDiffOn_const).mul hV).mul
      (Work.FTS.EllipticEst.SmoothOpen.Dz hf))
  have h1' : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N1sg α Φs f) := by
    unfold Work.FTS.Nonlin.N1sg
    exact h1
  have h2' : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N2sg α Φs f) := by
    unfold Work.FTS.Nonlin.N2sg
    exact h2
  have h3' : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N3sg α Φs f) := by
    unfold Work.FTS.Nonlin.N3sg
    exact h3
  show Work.FTS.EllipticEst.SmoothOpen (fun z θ =>
    Work.FTS.Nonlin.N1sg α Φs f z θ + Work.FTS.Nonlin.N2sg α Φs f z θ
      + Work.FTS.Nonlin.N3sg α Φs f z θ)
  exact Work.FTS.EllipticEst.smoothOpen_add
    (Work.FTS.EllipticEst.smoothOpen_add h1' h2') h3'


/-! ## Elementary algebra of the pricing factors -/

private theorem sqrt_four {a b c d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    Real.sqrt (a * b * c * d)
      = Real.sqrt a * Real.sqrt b * Real.sqrt c * Real.sqrt d := by
  rw [show a * b * c * d = a * (b * (c * d)) by ring, Real.sqrt_mul ha, Real.sqrt_mul hb,
    Real.sqrt_mul hc]
  ring

private theorem shape_one {α Cs M : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hM : 0 ≤ M) :
    (1 + |Cs|) * α ^ (-(1 : ℝ)) * (1 + M)
      ≤ (1 + |Cs|) ^ 4 * α ^ (-(4 : ℝ)) * (1 + M) ^ 4 := by
  have hA : (1 + |Cs|) ≤ (1 + |Cs|) ^ 4 := by
    have h := pow_le_pow_right₀ (show (1 : ℝ) ≤ 1 + |Cs| by linarith [abs_nonneg Cs])
      (show (1 : ℕ) ≤ 4 by norm_num)
    simpa using h
  have hB : α ^ (-(1 : ℝ)) ≤ α ^ (-(4 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_ge hα hα1 (by norm_num)
  have hD : (1 + M) ≤ (1 + M) ^ 4 := by
    have h := pow_le_pow_right₀ (show (1 : ℝ) ≤ 1 + M by linarith)
      (show (1 : ℕ) ≤ 4 by norm_num)
    simpa using h
  exact mul_le_mul (mul_le_mul hA hB (by positivity) (by positivity)) hD (by positivity)
    (by positivity)

private theorem shape_two {α Cs M : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hM : 0 ≤ M) :
    (1 + |Cs|) * α ^ (-(1 : ℝ)) * M
      ≤ (1 + |Cs|) ^ 4 * α ^ (-(4 : ℝ)) * (1 + M) ^ 4 := by
  have hA : (1 + |Cs|) ≤ (1 + |Cs|) ^ 4 := by
    have h := pow_le_pow_right₀ (show (1 : ℝ) ≤ 1 + |Cs| by linarith [abs_nonneg Cs])
      (show (1 : ℕ) ≤ 4 by norm_num)
    simpa using h
  have hB : α ^ (-(1 : ℝ)) ≤ α ^ (-(4 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_ge hα hα1 (by norm_num)
  have hD : M ≤ (1 + M) ^ 4 := by
    have h1 : M ≤ 1 + M := by linarith
    have h2 : (1 : ℝ) ≤ 1 + M := by linarith
    have h := pow_le_pow_right₀ h2 (show (1 : ℕ) ≤ 4 by norm_num)
    linarith [h]
  exact mul_le_mul (mul_le_mul hA hB (by positivity) (by positivity)) hD hM (by positivity)

/-! ## The block estimate, from the three pieces -/

private theorem nsg_main (C1 C2 C3 : ℝ) (hC1 : 0 < C1) (hC2 : 0 < C2) (hC3 : 0 < C3)
    (hDth : ∀ (α : ℝ) (h f : Fn), 0 < α → α ≤ 1 →
      Work.FTS.EllipticEst.SmoothOpen h → Work.Spaces.WlInfMem α 4 h →
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
      Work.Spaces.HkMem α 3 (fun z θ => h z θ * Work.Spaces.Dth f z θ) ∧
      Work.Spaces.HkSq α 3 (fun z θ => h z θ * Work.Spaces.Dth f z θ)
        ≤ C2 / (Work.Spaces.gam α - 1) * (Work.Spaces.WlInf α 4 h) ^ 2
            * Work.Spaces.HkSq α 4 f)
    (hDz : ∀ (α : ℝ) (h f : Fn), 0 < α → α ≤ 1 →
      Work.FTS.EllipticEst.SmoothOpen h → Work.Spaces.WlInfMem α 4 h →
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
      Work.Spaces.HkMem α 3 (fun z θ => h z θ * Work.Spaces.Dz f z θ) ∧
      Work.Spaces.HkSq α 3 (fun z θ => h z θ * Work.Spaces.Dz f z θ)
        ≤ C3 / (Work.Spaces.gam α - 1) * (Work.Spaces.WlInf α 4 h) ^ 2
            * Work.Spaces.HkSq α 4 f)
    (hNsg1 : ∀ (α Cs M : ℝ) (Φs f : Fn), 0 < α → α ≤ 1 →
      Work.FTS.VocabO2.StarPkgo2 α Cs Φs → Work.FTS.StrongPersist.H6Adm α f →
      Work.FTS.Nonlin.Xn α f ≤ M →
      Work.Spaces.HkMem α 3 (Work.FTS.Nonlin.N1sg α Φs f) ∧
      Work.Spaces.HkNorm α 3 (Work.FTS.Nonlin.N1sg α Φs f)
        ≤ C1 * (1 + |Cs|) * α ^ (-(1 : ℝ)) * (1 + M)) :
    ∃ C Cpow α₂ : ℝ, 0 < C ∧ 0 ≤ Cpow ∧ 0 < α₂ ∧
      ∀ α ∈ Set.Ioc 0 α₂, ∀ (Cs : ℝ) (Φs f : Fn) (M : ℝ),
        Work.FTS.VocabO2.StarPkgo2 α Cs Φs → Work.FTS.StrongPersist.H6Adm α f →
        Work.FTS.Nonlin.Xn α f ≤ M →
        ContDiffOn ℝ 3 (Function.uncurry (NSgSum α Φs f)) Work.FTS.EllipticEst.Q0 ∧
        HkMem α 3 (NSgSum α Φs f) ∧
        HkNorm α 3 (NSgSum α Φs f) ≤ C * (1 + |Cs|) ^ 4 * α ^ (-Cpow) * (1 + M) ^ 4 := by
  refine ⟨200 * (C1 + (40 * C2 + 1) + (40 * C3 + 1) + 1), 4, 1 / 2, by positivity,
    by norm_num, by norm_num, ?_⟩
  intro α hαIoc Cs Φs f M hstar hadm hM
  have hα : 0 < α := hαIoc.1
  have hα1 : α ≤ 1 := by linarith [hαIoc.2]
  have hf : Work.FTS.EllipticEst.SmoothOpen f := hadm.reg.1
  have hf6 : HkMem α 6 f := hadm.reg.2
  have hf4 : HkMem α 4 f :=
    Work.FTS.StrongPersist.HkMem_of_le_of_smoothOpen α (by norm_num) hf hf6
  have hMnn : 0 ≤ M := le_trans (Real.sqrt_nonneg _) hM
  have hSq4 : HkSq α 4 f ≤ M ^ 2 := by
    have h1 : HkSq α 4 f = (Work.FTS.Nonlin.Xn α f) ^ 2 := by
      rw [Work.FTS.Nonlin.Xn, Work.Spaces.HkNorm,
        Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 4 f)]
    rw [h1]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hM 2
  have hψ : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.PhiTs α Φs) :=
    Work.FTS.NonlinRows.NRow10aux.smoothOpen_PhiTs hα hα1 hstar.toStarPkgo
  have hWlnn2 : 0 ≤ Work.Spaces.WlInf α 4
      (fun z θ => Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ
        / Work.Construction.s2 θ) := Work.FTS.H2.WPQ.WlInf_nonneg' hstar.UsW.1
  have hWlnn3 : 0 ≤ Work.Spaces.WlInf α 4
      (Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs)) :=
    Work.FTS.H2.WPQ.WlInf_nonneg' hstar.VW.1
  -- ### piece 1: `N₁^{sg}`
  obtain ⟨hmem1, hbnd1⟩ := hNsg1 α Cs M Φs f hα hα1 hstar hadm hM
  -- ### piece 2: `N₂^{sg} = -2·(𝒰(Φ̃_*)/sin 2θ)·D_θf`
  have hsm2 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ
        / Work.Construction.s2 θ) :=
    (Work.FTS.PhiStar.StarPkgo2Aux.FieldRegularity α (Work.FTS.Nonlin.PhiTs α Φs) hψ).2.2.2.1
  obtain ⟨hmemP2, hsqP2⟩ := hDth α
    (fun z θ => Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ
      / Work.Construction.s2 θ) f hα hα1 hsm2 hstar.UsW.1 hf hf4
  have h2mem : HkMem α 3 (Work.FTS.Nonlin.N2sg α Φs f) :=
    Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 3
      (Work.FTS.LocData.HkMem_const_mul α 3 (-2) hmemP2)
      (fun z hz θ hθ => by
        rw [nsg_alg2 α Φs f z θ hz hθ.1 hθ.2]
        ring)
  have heq2 : HkSq α 3 (Work.FTS.Nonlin.N2sg α Φs f)
      = 4 * HkSq α 3 (fun z θ =>
          (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ
            / Work.Construction.s2 θ) * Work.Spaces.Dth f z θ) := by
    rw [Work.FTS.EllipticEst.HkSq_congr_open α 3
      (g := fun z θ => -2 * ((Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ
            / Work.Construction.s2 θ) * Work.Spaces.Dth f z θ))
      (fun z θ hz hθ hθ2 => by rw [nsg_alg2 α Φs f z θ hz hθ hθ2]; ring)]
    rw [Work.FTS.LocData.HkSq_const_mul α 3 (-2) hmemP2]
    norm_num
  have h2sq : HkSq α 3 (Work.FTS.Nonlin.N2sg α Φs f) ≤ 40 * C2 * Cs ^ 2 * α * M ^ 2 := by
    have hkey : C2 / (Work.Spaces.gam α - 1)
        * (Work.Spaces.WlInf α 4 (fun z θ =>
            Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ
              / Work.Construction.s2 θ)) ^ 2
        * HkSq α 4 f ≤ 10 * C2 * Cs ^ 2 * α * M ^ 2 := by
      have hW2 : (Work.Spaces.WlInf α 4 (fun z θ =>
            Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ
              / Work.Construction.s2 θ)) ^ 2 ≤ (Cs * α) ^ 2 :=
        pow_le_pow_left₀ hWlnn2 hstar.UsW.2 2
      have hdiv : C2 / (Work.Spaces.gam α - 1) = C2 * (10 / α) := by
        rw [Work.Spaces.gam_sub_one]; field_simp
      calc C2 / (Work.Spaces.gam α - 1)
            * (Work.Spaces.WlInf α 4 (fun z θ =>
                Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ
                  / Work.Construction.s2 θ)) ^ 2
            * HkSq α 4 f
          = (C2 * (10 / α)) * (Work.Spaces.WlInf α 4 (fun z θ =>
                Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ
                  / Work.Construction.s2 θ)) ^ 2 * HkSq α 4 f := by rw [hdiv]
        _ ≤ (C2 * (10 / α)) * (Cs * α) ^ 2 * M ^ 2 := by
            refine mul_le_mul (mul_le_mul_of_nonneg_left hW2 (by positivity)) hSq4
              (Work.Spaces.HkSq_nonneg α 4 f) (by positivity)
        _ = 10 * C2 * Cs ^ 2 * α * M ^ 2 := by field_simp
    linarith [heq2, hsqP2, hkey]
  have h2norm : HkNorm α 3 (Work.FTS.Nonlin.N2sg α Φs f)
      ≤ (40 * C2 + 1) * (1 + |Cs|) * α ^ (-(1 : ℝ)) * M := by
    have h1 : HkNorm α 3 (Work.FTS.Nonlin.N2sg α Φs f)
        ≤ Real.sqrt (40 * C2 * Cs ^ 2 * α * M ^ 2) := Real.sqrt_le_sqrt h2sq
    have h2 : Real.sqrt (40 * C2 * Cs ^ 2 * α * M ^ 2)
        = Real.sqrt (40 * C2) * |Cs| * Real.sqrt α * M := by
      rw [sqrt_four (by positivity) (sq_nonneg Cs) hα.le (sq_nonneg M),
        Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs, abs_of_nonneg hMnn]
    rw [h2] at h1
    have hCsle : |Cs| ≤ 1 + |Cs| := by linarith [abs_nonneg Cs]
    have hsqa : Real.sqrt α ≤ α ^ (-(1 : ℝ)) := by
      rw [Real.rpow_neg_one]
      exact le_trans (Real.sqrt_le_one.mpr hα1) ((one_le_inv₀ hα).mpr hα1)
    have hsq40 : Real.sqrt (40 * C2) ≤ 40 * C2 + 1 := by
      refine (Real.sqrt_le_left (by positivity : (0 : ℝ) ≤ 40 * C2 + 1)).mpr ?_
      nlinarith [hC2, sq_nonneg (40 * C2)]
    refine le_trans h1 ?_
    refine mul_le_mul_of_nonneg_right ?_ hMnn
    exact mul_le_mul (mul_le_mul hsq40 hCsle (abs_nonneg Cs) (by positivity)) hsqa
      (Real.sqrt_nonneg α) (by positivity)
  -- ### piece 3: `N₃^{sg} = -2α𝒱(Φ̃_*)·D_zf`
  have hsm3 : Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs)) :=
    Work.FTS.NonlinRows.Rl1.smoothOpen_Vop_open hψ
  obtain ⟨hmemP3, hsqP3⟩ := hDz α (Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs)) f
    hα hα1 hsm3 hstar.VW.1 hf hf4
  have h3mem : HkMem α 3 (Work.FTS.Nonlin.N3sg α Φs f) :=
    Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 3
      (Work.FTS.LocData.HkMem_const_mul α 3 (-2 * α) hmemP3)
      (fun z hz θ hθ => by
        rw [nsg_alg3 α Φs f z θ hz hθ.1 hθ.2]
        ring)
  have heq3 : HkSq α 3 (Work.FTS.Nonlin.N3sg α Φs f)
      = 4 * α ^ 2 * HkSq α 3 (fun z θ =>
          Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) z θ * Work.Spaces.Dz f z θ) := by
    rw [Work.FTS.EllipticEst.HkSq_congr_open α 3
      (g := fun z θ => (-2 * α) * (Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) z θ
          * Work.Spaces.Dz f z θ))
      (fun z θ hz hθ hθ2 => by rw [nsg_alg3 α Φs f z θ hz hθ hθ2]; ring)]
    rw [Work.FTS.LocData.HkSq_const_mul α 3 (-2 * α) hmemP3]
    ring
  have h3sq : HkSq α 3 (Work.FTS.Nonlin.N3sg α Φs f) ≤ 40 * C3 * Cs ^ 2 * α ^ 3 * M ^ 2 := by
    have hkey : C3 / (Work.Spaces.gam α - 1)
        * (Work.Spaces.WlInf α 4
            (Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs))) ^ 2
        * HkSq α 4 f ≤ 10 * C3 * Cs ^ 2 * α * M ^ 2 := by
      have hW2 : (Work.Spaces.WlInf α 4
            (Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs))) ^ 2 ≤ (Cs * α) ^ 2 :=
        pow_le_pow_left₀ hWlnn3 hstar.VW.2 2
      have hdiv : C3 / (Work.Spaces.gam α - 1) = C3 * (10 / α) := by
        rw [Work.Spaces.gam_sub_one]; field_simp
      calc C3 / (Work.Spaces.gam α - 1)
            * (Work.Spaces.WlInf α 4
                (Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs))) ^ 2 * HkSq α 4 f
          = (C3 * (10 / α)) * (Work.Spaces.WlInf α 4
                (Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs))) ^ 2 * HkSq α 4 f := by
            rw [hdiv]
        _ ≤ (C3 * (10 / α)) * (Cs * α) ^ 2 * M ^ 2 := by
            refine mul_le_mul (mul_le_mul_of_nonneg_left hW2 (by positivity)) hSq4
              (Work.Spaces.HkSq_nonneg α 4 f) (by positivity)
        _ = 10 * C3 * Cs ^ 2 * α * M ^ 2 := by field_simp
    have hstep : 4 * α ^ 2 * HkSq α 3 (fun z θ =>
        Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) z θ * Work.Spaces.Dz f z θ)
        ≤ 40 * C3 * Cs ^ 2 * α ^ 3 * M ^ 2 := by
      calc 4 * α ^ 2 * HkSq α 3 (fun z θ =>
            Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) z θ * Work.Spaces.Dz f z θ)
          ≤ 4 * α ^ 2 * (C3 / (Work.Spaces.gam α - 1)
              * (Work.Spaces.WlInf α 4
                  (Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs))) ^ 2 * HkSq α 4 f) :=
            mul_le_mul_of_nonneg_left hsqP3 (by positivity)
        _ ≤ 4 * α ^ 2 * (10 * C3 * Cs ^ 2 * α * M ^ 2) :=
            mul_le_mul_of_nonneg_left hkey (by positivity)
        _ = 40 * C3 * Cs ^ 2 * α ^ 3 * M ^ 2 := by ring
    linarith [heq3, hstep]
  have h3norm : HkNorm α 3 (Work.FTS.Nonlin.N3sg α Φs f)
      ≤ (40 * C3 + 1) * (1 + |Cs|) * α ^ (-(1 : ℝ)) * M := by
    have h1 : HkNorm α 3 (Work.FTS.Nonlin.N3sg α Φs f)
        ≤ Real.sqrt (40 * C3 * Cs ^ 2 * α ^ 3 * M ^ 2) := Real.sqrt_le_sqrt h3sq
    have h2 : Real.sqrt (40 * C3 * Cs ^ 2 * α ^ 3 * M ^ 2)
        = Real.sqrt (40 * C3) * |Cs| * Real.sqrt (α ^ 3) * M := by
      rw [sqrt_four (by positivity) (sq_nonneg Cs) (by positivity) (sq_nonneg M),
        Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs, abs_of_nonneg hMnn]
    rw [h2] at h1
    have hCsle : |Cs| ≤ 1 + |Cs| := by linarith [abs_nonneg Cs]
    have hsqa : Real.sqrt (α ^ 3) ≤ α ^ (-(1 : ℝ)) := by
      rw [Real.rpow_neg_one]
      refine le_trans (Real.sqrt_le_one.mpr (by nlinarith [hα.le, hα1])) ?_
      exact (one_le_inv₀ hα).mpr hα1
    have hsq40 : Real.sqrt (40 * C3) ≤ 40 * C3 + 1 := by
      refine (Real.sqrt_le_left (by positivity : (0 : ℝ) ≤ 40 * C3 + 1)).mpr ?_
      nlinarith [hC3, sq_nonneg (40 * C3)]
    refine le_trans h1 ?_
    refine mul_le_mul_of_nonneg_right ?_ hMnn
    exact mul_le_mul (mul_le_mul hsq40 hCsle (abs_nonneg Cs) (by positivity)) hsqa
      (Real.sqrt_nonneg (α ^ 3)) (by positivity)
  -- ### the smoothness and the sum
  have hsmSum : Work.FTS.EllipticEst.SmoothOpen (NSgSum α Φs f) := nsg_smooth α Cs Φs f hα hα1 hstar hf
  have hcont1 : ContDiffOn ℝ 3 (Function.uncurry (Work.FTS.Nonlin.N1sg α Φs f))
      Work.FTS.EllipticEst.Q0 := by
    have h1 : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N1sg α Φs f) := by
      unfold Work.FTS.Nonlin.N1sg
      show ContDiffOn ℝ Work.Stability.smoothOrder
        (fun p : ℝ × ℝ => 2 * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) p.1 p.2
          * f p.1 p.2) Work.FTS.EllipticEst.Q0
      exact (contDiffOn_const.mul (Work.FTS.NonlinRows.smoothOpen_Rop hψ)).mul hf
    exact (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp h1 3
  have hcont2 : ContDiffOn ℝ 3 (Function.uncurry (Work.FTS.Nonlin.N2sg α Φs f))
      Work.FTS.EllipticEst.Q0 := by
    have h1 : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N2sg α Φs f) := by
      unfold Work.FTS.Nonlin.N2sg
      show ContDiffOn ℝ Work.Stability.smoothOrder
        (fun p : ℝ × ℝ => -2 * Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) p.1 p.2
          * Work.Spaces.pth f p.1 p.2) Work.FTS.EllipticEst.Q0
      exact ((contDiffOn_const.mul (Work.FTS.NonlinRows.Rl1.smoothOpen_Uop_open hψ)).mul
        (Work.FTS.EllipticEst.SmoothOpen.pth hf))
    exact (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp h1 3
  have hcont3 : ContDiffOn ℝ 3 (Function.uncurry (Work.FTS.Nonlin.N3sg α Φs f))
      Work.FTS.EllipticEst.Q0 := by
    have h1 : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N3sg α Φs f) := by
      unfold Work.FTS.Nonlin.N3sg
      show ContDiffOn ℝ Work.Stability.smoothOrder
        (fun p : ℝ × ℝ => -2 * α * Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) p.1 p.2
          * Work.Spaces.Dz f p.1 p.2) Work.FTS.EllipticEst.Q0
      exact (((contDiffOn_const.mul contDiffOn_const).mul (Work.FTS.NonlinRows.Rl1.smoothOpen_Vop_open hψ)).mul
        (Work.FTS.EllipticEst.SmoothOpen.Dz hf))
    exact (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp h1 3
  have hcont12 : ContDiffOn ℝ 3 (Function.uncurry (fun z θ =>
      Work.FTS.Nonlin.N1sg α Φs f z θ + Work.FTS.Nonlin.N2sg α Φs f z θ))
      Work.FTS.EllipticEst.Q0 := hcont1.add hcont2
  have hsum12 : HkMem α 3 (fun z θ => Work.FTS.Nonlin.N1sg α Φs f z θ
      + Work.FTS.Nonlin.N2sg α Φs f z θ) ∧
      HkNorm α 3 (fun z θ => Work.FTS.Nonlin.N1sg α Φs f z θ
        + Work.FTS.Nonlin.N2sg α Φs f z θ)
        ≤ Real.sqrt 2 * (HkNorm α 3 (Work.FTS.Nonlin.N1sg α Φs f)
          + HkNorm α 3 (Work.FTS.Nonlin.N2sg α Φs f)) :=
    Work.FTS.StrongPersist.HkAddFin hcont1 hcont2 hmem1 h2mem
  have hsum : HkMem α 3 (NSgSum α Φs f) ∧
      HkNorm α 3 (NSgSum α Φs f)
        ≤ Real.sqrt 2 * (HkNorm α 3 (fun z θ => Work.FTS.Nonlin.N1sg α Φs f z θ
            + Work.FTS.Nonlin.N2sg α Φs f z θ)
          + HkNorm α 3 (Work.FTS.Nonlin.N3sg α Φs f)) :=
    Work.FTS.StrongPersist.HkAddFin hcont12 hcont3 hsum12.1 h3mem
  -- ### the final arithmetic
  set x : ℝ := (1 + |Cs|) * α ^ (-(1 : ℝ)) with hx
  set y : ℝ := (1 + |Cs|) ^ 4 * α ^ (-(4 : ℝ)) * (1 + M) ^ 4 with hy
  have hynn : 0 ≤ y := by rw [hy]; positivity
  have hb1 : HkNorm α 3 (Work.FTS.Nonlin.N1sg α Φs f) ≤ C1 * (x * (1 + M)) := by
    rw [hx]
    calc HkNorm α 3 (Work.FTS.Nonlin.N1sg α Φs f)
        ≤ C1 * (1 + |Cs|) * α ^ (-(1 : ℝ)) * (1 + M) := hbnd1
      _ = C1 * ((1 + |Cs|) * α ^ (-(1 : ℝ)) * (1 + M)) := by ring
  have hb2 : HkNorm α 3 (Work.FTS.Nonlin.N2sg α Φs f) ≤ (40 * C2 + 1) * (x * M) := by
    rw [hx]
    calc HkNorm α 3 (Work.FTS.Nonlin.N2sg α Φs f)
        ≤ (40 * C2 + 1) * (1 + |Cs|) * α ^ (-(1 : ℝ)) * M := h2norm
      _ = (40 * C2 + 1) * ((1 + |Cs|) * α ^ (-(1 : ℝ)) * M) := by ring
  have hb3 : HkNorm α 3 (Work.FTS.Nonlin.N3sg α Φs f) ≤ (40 * C3 + 1) * (x * M) := by
    rw [hx]
    calc HkNorm α 3 (Work.FTS.Nonlin.N3sg α Φs f)
        ≤ (40 * C3 + 1) * (1 + |Cs|) * α ^ (-(1 : ℝ)) * M := h3norm
      _ = (40 * C3 + 1) * ((1 + |Cs|) * α ^ (-(1 : ℝ)) * M) := by ring
  have hsh1 : x * (1 + M) ≤ y := by
    rw [hx, hy]; exact shape_one hα hα1 hMnn
  have hsh2 : x * M ≤ y := by
    rw [hx, hy]; exact shape_two hα hα1 hMnn
  have hsqrt2 : Real.sqrt 2 ≤ 2 := by
    have h : (2 : ℝ) = Real.sqrt 2 ^ 2 := (Real.sq_sqrt (by norm_num)).symm
    nlinarith [Real.sqrt_nonneg 2]
  have hb1' : HkNorm α 3 (Work.FTS.Nonlin.N1sg α Φs f) ≤ C1 * y :=
    le_trans hb1 (mul_le_mul_of_nonneg_left hsh1 hC1.le)
  have hb2' : HkNorm α 3 (Work.FTS.Nonlin.N2sg α Φs f) ≤ (40 * C2 + 1) * y :=
    le_trans hb2 (mul_le_mul_of_nonneg_left hsh2 (by positivity))
  have hb3' : HkNorm α 3 (Work.FTS.Nonlin.N3sg α Φs f) ≤ (40 * C3 + 1) * y :=
    le_trans hb3 (mul_le_mul_of_nonneg_left hsh2 (by positivity))
  have hN1nn : 0 ≤ HkNorm α 3 (Work.FTS.Nonlin.N1sg α Φs f) :=
    Real.sqrt_nonneg _
  have hN2nn : 0 ≤ HkNorm α 3 (Work.FTS.Nonlin.N2sg α Φs f) :=
    Real.sqrt_nonneg _
  have hN3nn : 0 ≤ HkNorm α 3 (Work.FTS.Nonlin.N3sg α Φs f) :=
    Real.sqrt_nonneg _
  have hnorm : HkNorm α 3 (NSgSum α Φs f)
      ≤ 200 * (C1 + (40 * C2 + 1) + (40 * C3 + 1) + 1) * y := by
    have hA : HkNorm α 3 (fun z θ => Work.FTS.Nonlin.N1sg α Φs f z θ
        + Work.FTS.Nonlin.N2sg α Φs f z θ) ≤ 2 * (C1 + (40 * C2 + 1)) * y := by
      have hsum' : HkNorm α 3 (Work.FTS.Nonlin.N1sg α Φs f)
          + HkNorm α 3 (Work.FTS.Nonlin.N2sg α Φs f) ≤ (C1 + (40 * C2 + 1)) * y := by
        linarith [hb1', hb2']
      refine le_trans hsum12.2 ?_
      calc Real.sqrt 2 * (HkNorm α 3 (Work.FTS.Nonlin.N1sg α Φs f)
            + HkNorm α 3 (Work.FTS.Nonlin.N2sg α Φs f))
          ≤ 2 * (HkNorm α 3 (Work.FTS.Nonlin.N1sg α Φs f)
            + HkNorm α 3 (Work.FTS.Nonlin.N2sg α Φs f)) :=
            mul_le_mul_of_nonneg_right hsqrt2 (by linarith)
        _ ≤ 2 * ((C1 + (40 * C2 + 1)) * y) := mul_le_mul_of_nonneg_left hsum' (by norm_num)
        _ = 2 * (C1 + (40 * C2 + 1)) * y := by ring
    refine le_trans hsum.2 ?_
    have hsum2' : HkNorm α 3 (fun z θ => Work.FTS.Nonlin.N1sg α Φs f z θ
          + Work.FTS.Nonlin.N2sg α Φs f z θ) + HkNorm α 3 (Work.FTS.Nonlin.N3sg α Φs f)
        ≤ (2 * (C1 + (40 * C2 + 1)) + (40 * C3 + 1)) * y := by
      linarith [hA, hb3']
    calc Real.sqrt 2 * (HkNorm α 3 (fun z θ => Work.FTS.Nonlin.N1sg α Φs f z θ
            + Work.FTS.Nonlin.N2sg α Φs f z θ) + HkNorm α 3 (Work.FTS.Nonlin.N3sg α Φs f))
        ≤ 2 * (HkNorm α 3 (fun z θ => Work.FTS.Nonlin.N1sg α Φs f z θ
            + Work.FTS.Nonlin.N2sg α Φs f z θ) + HkNorm α 3 (Work.FTS.Nonlin.N3sg α Φs f)) :=
          mul_le_mul_of_nonneg_right hsqrt2
            (add_nonneg (Real.sqrt_nonneg (Work.Spaces.HkSq α 3 (fun z θ => Work.FTS.Nonlin.N1sg α Φs f z θ
              + Work.FTS.Nonlin.N2sg α Φs f z θ))) (Real.sqrt_nonneg (Work.Spaces.HkSq α 3 (Work.FTS.Nonlin.N3sg α Φs f))))
      _ ≤ 2 * ((2 * (C1 + (40 * C2 + 1)) + (40 * C3 + 1)) * y) :=
          mul_le_mul_of_nonneg_left hsum2' (by norm_num)
      _ ≤ 200 * (C1 + (40 * C2 + 1) + (40 * C3 + 1) + 1) * y := by
          have hkey0 : 2 * (2 * (C1 + (40 * C2 + 1)) + (40 * C3 + 1))
              ≤ 200 * (C1 + (40 * C2 + 1) + (40 * C3 + 1) + 1) := by
            nlinarith [hC1, hC2, hC3]
          calc 2 * ((2 * (C1 + (40 * C2 + 1)) + (40 * C3 + 1)) * y)
              = (2 * (2 * (C1 + (40 * C2 + 1)) + (40 * C3 + 1))) * y := by ring
            _ ≤ 200 * (C1 + (40 * C2 + 1) + (40 * C3 + 1) + 1) * y :=
                mul_le_mul_of_nonneg_right hkey0 hynn
  refine ⟨?_, hsum.1, ?_⟩
  · exact (Work.FTS.EllipticEst.smoothOpen_iff_forall (NSgSum α Φs f)).mp hsmSum 3
  · have hy' : HkNorm α 3 (NSgSum α Φs f)
        ≤ 200 * (C1 + (40 * C2 + 1) + (40 * C3 + 1) + 1)
            * ((1 + |Cs|) ^ 4 * α ^ (-(4 : ℝ)) * (1 + M) ^ 4) := by
      rw [← hy]; exact hnorm
    calc HkNorm α 3 (NSgSum α Φs f)
        ≤ 200 * (C1 + (40 * C2 + 1) + (40 * C3 + 1) + 1)
            * ((1 + |Cs|) ^ 4 * α ^ (-(4 : ℝ)) * (1 + M) ^ 4) := hy'
      _ = 200 * (C1 + (40 * C2 + 1) + (40 * C3 + 1) + 1)
            * (1 + |Cs|) ^ 4 * α ^ (-(4 : ℝ)) * (1 + M) ^ 4 := by ring


/-! ## The block estimate -/

/-- **The `ℋ³`-estimate for the `N^{sg}`-block of the level-three right-hand side.** -/
theorem L3RhsNsgBlock : ∃ C Cpow α₂ : ℝ, 0 < C ∧ 0 ≤ Cpow ∧ 0 < α₂ ∧
    ∀ α ∈ Set.Ioc 0 α₂, ∀ (Cs : ℝ) (Φs f : Work.FTS.Galerkin.Fn) (M : ℝ),
      Work.FTS.VocabO2.StarPkgo2 α Cs Φs → Work.FTS.StrongPersist.H6Adm α f → Work.FTS.Nonlin.Xn α f ≤ M →
      ContDiffOn ℝ 3 (Function.uncurry (Work.FTS.StrongPersist.L3Rhs.NSgSum α Φs f)) Work.FTS.EllipticEst.Q0 ∧
      Work.Spaces.HkMem α 3 (Work.FTS.StrongPersist.L3Rhs.NSgSum α Φs f) ∧
      Work.Spaces.HkNorm α 3 (Work.FTS.StrongPersist.L3Rhs.NSgSum α Φs f)
        ≤ C * (1 + |Cs|) ^ 4 * α ^ (-Cpow) * (1 + M) ^ 4 := by
  obtain ⟨C1, hC1, hNsg1⟩ := L3Nsg1
  obtain ⟨C2, hC2, hDth⟩ := L3MulDth
  obtain ⟨C3, hC3, hDz⟩ := L3MulDz
  exact nsg_main C1 C2 C3 hC1 hC2 hC3 hDth hDz hNsg1

end Work.FTS.StrongPersist.L3Rhs
