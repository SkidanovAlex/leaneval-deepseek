/-
# `Submission/Work/FTS/StrongPersist/L3Rhs/NfkAux/NfkAsm.lean`

The **assembly** of the `NFkSum` block estimate
(`Work.FTS.StrongPersist.L3Rhs.L3RhsNfkBlock`) from its five pieces.  See
`NfkAux/NfkSmooth.lean` for the `C³`-regularity of the six summands.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongPersist.L3Rhs.NfkAux.NfkSmooth

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.L3Rhs.NfkAux

open Work.FTS.Galerkin (Fn)
open Work.Spaces (HkMem HkSq HkNorm)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## The assembly of the block estimate -/

open Work.FTS.StrongPersist.L3Rhs (NFkSum)

/-- **Assembly of the `NFkSum` block estimate.**  From the five piece estimates and the
`ℋ⁴`-honesty of the angular moment `z ↦ FK f z` (`fkH_field`), the block `NFkSum α f` is `C³`
on the open quadrant, honest in `ℋ³`, and bounded by
`C·α^{-Cpow}·(1+M)⁴·(1+Xn6 α f)²`. -/
theorem nfk_assembly
    (hT1 : ∃ C Cpow : ℝ, 0 < C ∧ 0 ≤ Cpow ∧
      ∀ (α : ℝ), α ∈ Set.Ioc 0 1 → ∀ (f : Fn), Work.FTS.StrongPersist.H6Adm α f →
        HkMem α 3 (Work.FTS.Nonlin.N4gg α f) ∧
        HkSq α 3 (Work.FTS.Nonlin.N4gg α f)
          ≤ C * α ^ (-Cpow)
              * (1 + HkSq α 4 (fun z (_ : ℝ) => Work.Construction.FK f z)) * HkSq α 4 f)
    (hT2 : ∃ C Cpow : ℝ, 0 < C ∧ 0 ≤ Cpow ∧
      ∀ (α : ℝ), α ∈ Set.Ioc 0 1 → ∀ (f : Fn), Work.FTS.StrongPersist.H6Adm α f →
        HkMem α 3 (Work.FTS.Nonlin.N5gg f) ∧
        HkSq α 3 (Work.FTS.Nonlin.N5gg f)
          ≤ C * α ^ (-Cpow)
              * (1 + HkSq α 4 (fun z (_ : ℝ) => Work.Construction.FK f z)) * HkSq α 4 f)
    (hT3 : ∃ C Cpow : ℝ, 0 < C ∧ 0 ≤ Cpow ∧
      ∀ (α : ℝ) (f : Fn) (MK : ℝ), 0 < α → α ≤ 1 → Work.FTS.StrongPersist.H6Adm α f →
        HkMem α 4 (fun z (_ : ℝ) => Work.Construction.FK f z) →
        Work.FTS.Nonlin.Xn α (fun z (_ : ℝ) => Work.Construction.FK f z) ≤ MK →
        HkMem α 3 (fun z θ => Work.FTS.Nonlin.N4gs α f z θ + Work.FTS.Nonlin.N5gs α f z θ) ∧
        HkSq α 3 (fun z θ => Work.FTS.Nonlin.N4gs α f z θ + Work.FTS.Nonlin.N5gs α f z θ)
          ≤ C * α ^ (-Cpow) * (1 + MK) ^ 2)
    (hT5 : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), α ∈ Set.Ioc 0 1 → ∀ (f : Fn),
      Work.FTS.EllipticEst.SmoothOpen f → HkMem α 4 f →
      HkMem α 3 (Work.FTS.Nonlin.N4sg α f) ∧
      HkSq α 3 (Work.FTS.Nonlin.N4sg α f) ≤ C * HkSq α 4 f)
    (hT6 : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), α ∈ Set.Ioc 0 1 → ∀ (f : Fn),
      Work.FTS.EllipticEst.SmoothOpen f → HkMem α 4 f →
      HkMem α 3 (Work.FTS.Nonlin.N5sg α f) ∧
      HkSq α 3 (Work.FTS.Nonlin.N5sg α f) ≤ C * HkSq α 4 f)
    (hFK : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (g : Fn),
      Work.FTS.VocabO.HQo α 4 g → Work.Construction.L12 g 0 = 0 →
      HkMem α 4 (fun z (_ : ℝ) => Work.Construction.FK g z) ∧
      Work.FTS.Nonlin.Xn α (fun z (_ : ℝ) => Work.Construction.FK g z)
        ≤ C * Work.FTS.Nonlin.Xn α g) :
    ∃ C Cpow α₂ : ℝ, 0 < C ∧ 0 ≤ Cpow ∧ 0 < α₂ ∧
      ∀ α ∈ Set.Ioc 0 α₂, ∀ (f : Fn) (M : ℝ),
        Work.FTS.StrongPersist.H6Adm α f → Work.FTS.Nonlin.Xn α f ≤ M →
        ContDiffOn ℝ 3 (Function.uncurry (NFkSum α f)) Work.FTS.EllipticEst.Q0 ∧
        HkMem α 3 (NFkSum α f) ∧
        HkNorm α 3 (NFkSum α f)
          ≤ C * α ^ (-Cpow) * (1 + M) ^ 4 * (1 + Work.FTS.StrongPersist.Xn6 α f) ^ 2 := by
  obtain ⟨CT1, Cp1, hCT1pos, hCp1nn, hb1⟩ := hT1
  obtain ⟨CT2, Cp2, hCT2pos, hCp2nn, hb2⟩ := hT2
  obtain ⟨CT3, Cp3, hCT3pos, hCp3nn, hb3⟩ := hT3
  obtain ⟨CT5, hCT5pos, hb5⟩ := hT5
  obtain ⟨CT6, hCT6pos, hb6⟩ := hT6
  obtain ⟨Cfk, hCfkpos, hbFK⟩ := hFK
  have hCT5nn : (0 : ℝ) ≤ CT5 := hCT5pos.le
  have hCT6nn : (0 : ℝ) ≤ CT6 := hCT6pos.le
  set K0 : ℝ := max 1 Cfk with hK0def
  have hK01 : (1 : ℝ) ≤ K0 := le_max_left _ _
  have hK0f : Cfk ≤ K0 := le_max_right _ _
  have hK0pos : (0 : ℝ) < K0 := lt_of_lt_of_le one_pos hK01
  have hK0nn : (0 : ℝ) ≤ K0 := hK0pos.le
  have hK0sq : (1 : ℝ) ≤ K0 ^ 2 := by
    have h := pow_le_pow_left₀ (show (0 : ℝ) ≤ 1 by norm_num) hK01 2
    simpa using h
  set Cpow : ℝ := max (max Cp1 Cp2) (max Cp3 0) with hCpowdef
  have hCpow_nn : (0 : ℝ) ≤ Cpow :=
    le_trans (le_max_right Cp3 0) (le_max_right (max Cp1 Cp2) (max Cp3 0))
  have hCp1le : Cp1 ≤ Cpow := le_trans (le_max_left _ _) (le_max_left _ _)
  have hCp2le : Cp2 ≤ Cpow := le_trans (le_max_right _ _) (le_max_left _ _)
  have hCp3le : Cp3 ≤ Cpow := le_trans (le_max_left _ _) (le_max_right _ _)
  set K1 : ℝ := 16 * K0 ^ 2 * ((CT1 + CT2) + CT3 + (CT5 + CT6)) with hK1def
  have hK1pos : (0 : ℝ) < K1 := by
    rw [hK1def]
    have h0 : (0 : ℝ) < K0 ^ 2 := pow_pos hK0pos 2
    have h1 : (0 : ℝ) < (CT1 + CT2) + CT3 + (CT5 + CT6) := by linarith
    exact mul_pos (mul_pos (by norm_num) h0) h1
  refine ⟨Real.sqrt K1 + 1, Cpow, 1, by positivity, hCpow_nn, by norm_num, ?_⟩
  intro α hαIoc f M hf hM
  obtain ⟨hα, hα1⟩ := Set.mem_Ioc.mp hαIoc
  have hsm : Work.FTS.EllipticEst.SmoothOpen f := hf.reg.1
  have hmem6 : HkMem α 6 f := hf.reg.2
  have hmem4 : HkMem α 4 f := Work.FTS.OpenPkg.HkMem_mono_open (k := 6) hsm 4 (by norm_num) hmem6
  have hMnn : 0 ≤ M := le_trans (Real.sqrt_nonneg (HkSq α 4 f)) hM
  have hM4 : (0 : ℝ) ≤ (1 + M) ^ 4 := by positivity
  have hF4le : HkSq α 4 f ≤ (1 + M) ^ 2 := by
    have h1 : HkSq α 4 f = (HkNorm α 4 f) ^ 2 := (Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 4 f)).symm
    rw [h1]
    have h2 : (HkNorm α 4 f) ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hM 2
    nlinarith [h2, hMnn]
  obtain ⟨hmemFK, hFKnorm⟩ := hbFK α hα hα1 f ⟨hsm, hmem4⟩ hf.l12
  have hQle : HkSq α 4 (fun z (_ : ℝ) => Work.Construction.FK f z) ≤ (Cfk * M) ^ 2 := by
    have h1 : HkNorm α 4 (fun z (_ : ℝ) => Work.Construction.FK f z) ≤ Cfk * M :=
      le_trans hFKnorm (mul_le_mul_of_nonneg_left hM hCfkpos.le)
    have h2 : HkSq α 4 (fun z (_ : ℝ) => Work.Construction.FK f z)
        = (HkNorm α 4 (fun z (_ : ℝ) => Work.Construction.FK f z)) ^ 2 :=
      (Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 4 _)).symm
    rw [h2]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
  have hQb : 1 + HkSq α 4 (fun z (_ : ℝ) => Work.Construction.FK f z)
      ≤ K0 ^ 2 * (1 + M) ^ 2 := by
    have hQ2 : HkSq α 4 (fun z (_ : ℝ) => Work.Construction.FK f z) ≤ Cfk ^ 2 * M ^ 2 := by
      nlinarith [hQle]
    have hCfksq : Cfk ^ 2 ≤ K0 ^ 2 := pow_le_pow_left₀ hCfkpos.le hK0f 2
    nlinarith [hQ2, hK0sq, hCfksq, hMnn]
  set Ap : ℝ := α ^ (-Cpow) with hApdef
  have hAp1 : (1 : ℝ) ≤ Ap := by
    rw [hApdef]
    have h := Real.rpow_le_rpow_of_exponent_ge hα hα1 (show (-Cpow) ≤ (0 : ℝ) by linarith)
    simpa using h
  have hApnn : (0 : ℝ) ≤ Ap := le_trans zero_le_one hAp1
  have hXall : (0 : ℝ) ≤ Ap * K0 ^ 2 * (1 + M) ^ 4 :=
    mul_nonneg (mul_nonneg hApnn (sq_nonneg K0)) hM4
  have hAp1' : α ^ (-Cp1) ≤ Ap := by
    rw [hApdef]
    exact Real.rpow_le_rpow_of_exponent_ge hα hα1 (by linarith)
  have hAp2' : α ^ (-Cp2) ≤ Ap := by
    rw [hApdef]
    exact Real.rpow_le_rpow_of_exponent_ge hα hα1 (by linarith)
  have hAp3' : α ^ (-Cp3) ≤ Ap := by
    rw [hApdef]
    exact Real.rpow_le_rpow_of_exponent_ge hα hα1 (by linarith)
  obtain ⟨hm1, hb1'⟩ := hb1 α hαIoc f hf
  obtain ⟨hm2, hb2'⟩ := hb2 α hαIoc f hf
  have hXnMK : Work.FTS.Nonlin.Xn α (fun z (_ : ℝ) => Work.Construction.FK f z) ≤ Cfk * M :=
    le_trans hFKnorm (mul_le_mul_of_nonneg_left hM hCfkpos.le)
  obtain ⟨hm34, hb34'⟩ := hb3 α f (Cfk * M) hα hα1 hf hmemFK hXnMK
  obtain ⟨hm5, hb5'⟩ := hb5 α hαIoc f hsm hmem4
  obtain ⟨hm6, hb6'⟩ := hb6 α hαIoc f hsm hmem4
  have hQnn : (0 : ℝ) ≤ 1 + HkSq α 4 (fun z (_ : ℝ) => Work.Construction.FK f z) := by
    have := Work.Spaces.HkSq_nonneg α 4 (fun z (_ : ℝ) => Work.Construction.FK f z); linarith
  have hK0sqnn : (0 : ℝ) ≤ K0 ^ 2 * (1 + M) ^ 2 := mul_nonneg (sq_nonneg K0) (sq_nonneg (1 + M))
  have hT1b : HkSq α 3 (Work.FTS.Nonlin.N4gg α f) ≤ CT1 * Ap * K0 ^ 2 * (1 + M) ^ 4 := by
    refine hb1'.trans ?_
    have h1 : CT1 * α ^ (-Cp1) ≤ CT1 * Ap := mul_le_mul_of_nonneg_left hAp1' hCT1pos.le
    calc CT1 * α ^ (-Cp1) * (1 + HkSq α 4 (fun z (_ : ℝ) => Work.Construction.FK f z))
          * HkSq α 4 f
        ≤ (CT1 * Ap) * (K0 ^ 2 * (1 + M) ^ 2) * (1 + M) ^ 2 :=
          mul_le_mul (mul_le_mul h1 hQb hQnn (mul_nonneg hCT1pos.le hApnn)) hF4le
            (Work.Spaces.HkSq_nonneg α 4 f) (mul_nonneg (mul_nonneg hCT1pos.le hApnn) hK0sqnn)
      _ = CT1 * Ap * K0 ^ 2 * (1 + M) ^ 4 := by ring
  have hT2b : HkSq α 3 (Work.FTS.Nonlin.N5gg f) ≤ CT2 * Ap * K0 ^ 2 * (1 + M) ^ 4 := by
    refine hb2'.trans ?_
    have h1 : CT2 * α ^ (-Cp2) ≤ CT2 * Ap := mul_le_mul_of_nonneg_left hAp2' hCT2pos.le
    calc CT2 * α ^ (-Cp2) * (1 + HkSq α 4 (fun z (_ : ℝ) => Work.Construction.FK f z))
          * HkSq α 4 f
        ≤ (CT2 * Ap) * (K0 ^ 2 * (1 + M) ^ 2) * (1 + M) ^ 2 :=
          mul_le_mul (mul_le_mul h1 hQb hQnn (mul_nonneg hCT2pos.le hApnn)) hF4le
            (Work.Spaces.HkSq_nonneg α 4 f) (mul_nonneg (mul_nonneg hCT2pos.le hApnn) hK0sqnn)
      _ = CT2 * Ap * K0 ^ 2 * (1 + M) ^ 4 := by ring
  have hT34b : HkSq α 3 (fun z θ => Work.FTS.Nonlin.N4gs α f z θ + Work.FTS.Nonlin.N5gs α f z θ)
      ≤ CT3 * Ap * K0 ^ 2 * (1 + M) ^ 4 := by
    refine hb34'.trans ?_
    have hMKb : (1 + Cfk * M) ^ 2 ≤ K0 ^ 2 * (1 + M) ^ 2 := by
      have h1 : 1 + Cfk * M ≤ K0 * (1 + M) := by nlinarith [hK01, hK0f, hMnn]
      have h2 : (0 : ℝ) ≤ 1 + Cfk * M := by nlinarith [hCfkpos, hMnn]
      calc (1 + Cfk * M) ^ 2 ≤ (K0 * (1 + M)) ^ 2 := pow_le_pow_left₀ h2 h1 2
        _ = K0 ^ 2 * (1 + M) ^ 2 := by ring
    have h4 : (1 + M) ^ 2 ≤ (1 + M) ^ 4 := by
      have h : (1 : ℝ) ≤ (1 + M) ^ 2 := by nlinarith [hMnn]
      calc (1 + M) ^ 2 = (1 + M) ^ 2 * 1 := by ring
        _ ≤ (1 + M) ^ 2 * (1 + M) ^ 2 := mul_le_mul_of_nonneg_left h (by positivity)
        _ = (1 + M) ^ 4 := by ring
    calc CT3 * α ^ (-Cp3) * (1 + Cfk * M) ^ 2
        ≤ CT3 * Ap * (K0 ^ 2 * (1 + M) ^ 2) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hAp3' hCT3pos.le) hMKb
            (by positivity) (mul_nonneg hCT3pos.le hApnn)
      _ ≤ CT3 * Ap * (K0 ^ 2 * (1 + M) ^ 4) := by
          refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hCT3pos.le hApnn)
          exact mul_le_mul_of_nonneg_left h4 (sq_nonneg K0)
      _ = CT3 * Ap * K0 ^ 2 * (1 + M) ^ 4 := by ring
  have hfacM : (1 : ℝ) ≤ Ap * K0 ^ 2 * (1 + M) ^ 2 := by
    have h4 : (1 : ℝ) ≤ (1 + M) ^ 2 := by nlinarith [hMnn]
    calc (1 : ℝ) = (1 * 1) * 1 := by ring
      _ ≤ (Ap * K0 ^ 2) * (1 + M) ^ 2 :=
          mul_le_mul (mul_le_mul hAp1 hK0sq (by norm_num) hApnn) h4 (by norm_num)
            (mul_nonneg hApnn (sq_nonneg K0))
  have hT5b : HkSq α 3 (Work.FTS.Nonlin.N4sg α f) ≤ CT5 * Ap * K0 ^ 2 * (1 + M) ^ 4 := by
    refine (hb5'.trans (mul_le_mul_of_nonneg_left hF4le hCT5nn)).trans ?_
    calc CT5 * (1 + M) ^ 2 ≤ CT5 * (1 + M) ^ 2 * (Ap * K0 ^ 2 * (1 + M) ^ 2) :=
          le_mul_of_one_le_right (by positivity) hfacM
      _ = CT5 * Ap * K0 ^ 2 * (1 + M) ^ 4 := by ring
  have hT6b : HkSq α 3 (Work.FTS.Nonlin.N5sg α f) ≤ CT6 * Ap * K0 ^ 2 * (1 + M) ^ 4 := by
    refine (hb6'.trans (mul_le_mul_of_nonneg_left hF4le hCT6nn)).trans ?_
    calc CT6 * (1 + M) ^ 2 ≤ CT6 * (1 + M) ^ 2 * (Ap * K0 ^ 2 * (1 + M) ^ 2) :=
          le_mul_of_one_le_right (by positivity) hfacM
      _ = CT6 * Ap * K0 ^ 2 * (1 + M) ^ 4 := by ring
  have hc1 := contDiffOn_N4gg hα hα1 hsm hmem6
  have hc2 := contDiffOn_N5gg hα hα1 hsm hmem6
  have hc3 := contDiffOn_N4gs α hα hα1 hsm hmem6
  have hc4 := contDiffOn_N5gs α hα hα1 hsm hmem6
  have hc5 := contDiffOn_N4sg α hα hα1 hsm hmem6
  have hc6 := contDiffOn_N5sg α hα hα1 hsm hmem6
  have hc12 : ContDiffOn ℝ 3 (Function.uncurry (fun z θ =>
      Work.FTS.Nonlin.N4gg α f z θ + Work.FTS.Nonlin.N5gg f z θ))
      Work.FTS.EllipticEst.Q0 := (hc1.add hc2).congr (fun p _ => rfl)
  have hc34 : ContDiffOn ℝ 3 (Function.uncurry (fun z θ =>
      Work.FTS.Nonlin.N4gs α f z θ + Work.FTS.Nonlin.N5gs α f z θ))
      Work.FTS.EllipticEst.Q0 := (hc3.add hc4).congr (fun p _ => rfl)
  have hc56 : ContDiffOn ℝ 3 (Function.uncurry (fun z θ =>
      Work.FTS.Nonlin.N4sg α f z θ + Work.FTS.Nonlin.N5sg α f z θ))
      Work.FTS.EllipticEst.Q0 := (hc5.add hc6).congr (fun p _ => rfl)
  have hc1234 : ContDiffOn ℝ 3 (Function.uncurry (fun z θ =>
      (Work.FTS.Nonlin.N4gg α f z θ + Work.FTS.Nonlin.N5gg f z θ)
        + (Work.FTS.Nonlin.N4gs α f z θ + Work.FTS.Nonlin.N5gs α f z θ)))
      Work.FTS.EllipticEst.Q0 := (hc12.add hc34).congr (fun p _ => rfl)
  have hcAll : ContDiffOn ℝ 3 (Function.uncurry (fun z θ =>
      (Work.FTS.Nonlin.N4gg α f z θ + Work.FTS.Nonlin.N5gg f z θ)
        + (Work.FTS.Nonlin.N4gs α f z θ + Work.FTS.Nonlin.N5gs α f z θ)
        + (Work.FTS.Nonlin.N4sg α f z θ + Work.FTS.Nonlin.N5sg α f z θ)))
      Work.FTS.EllipticEst.Q0 := (hc1234.add hc56).congr (fun p _ => rfl)
  have hNF : NFkSum α f = fun z θ =>
      (Work.FTS.Nonlin.N4gg α f z θ + Work.FTS.Nonlin.N5gg f z θ)
        + (Work.FTS.Nonlin.N4gs α f z θ + Work.FTS.Nonlin.N5gs α f z θ)
        + (Work.FTS.Nonlin.N4sg α f z θ + Work.FTS.Nonlin.N5sg α f z θ) := by
    funext z θ
    simp only [NFkSum]
    ring
  have hcNF : ContDiffOn ℝ 3 (Function.uncurry (NFkSum α f)) Work.FTS.EllipticEst.Q0 := by
    rw [hNF]
    exact hcAll
  have hAB := HkMem_HkSq_add2 (α := α) (k := 3) hc1 hc2 hm1 hm2
  have hEF := HkMem_HkSq_add2 (α := α) (k := 3) hc5 hc6 hm5 hm6
  have hABCD := HkMem_HkSq_add2 (α := α) (k := 3) hc12 hc34 hAB.1 hm34
  have hALL := HkMem_HkSq_add2 (α := α) (k := 3) hc1234 hc56 hABCD.1 hEF.1
  have hmemNF : HkMem α 3 (NFkSum α f) := by
    rw [hNF]
    exact hALL.1
  have hALL2 : HkSq α 3 (fun z θ =>
      (Work.FTS.Nonlin.N4gg α f z θ + Work.FTS.Nonlin.N5gg f z θ)
        + (Work.FTS.Nonlin.N4gs α f z θ + Work.FTS.Nonlin.N5gs α f z θ)
        + (Work.FTS.Nonlin.N4sg α f z θ + Work.FTS.Nonlin.N5sg α f z θ))
      ≤ 2 * HkSq α 3 (fun z θ =>
            (Work.FTS.Nonlin.N4gg α f z θ + Work.FTS.Nonlin.N5gg f z θ)
              + (Work.FTS.Nonlin.N4gs α f z θ + Work.FTS.Nonlin.N5gs α f z θ))
        + 2 * HkSq α 3 (fun z θ =>
            Work.FTS.Nonlin.N4sg α f z θ + Work.FTS.Nonlin.N5sg α f z θ) := hALL.2
  have hABCD2 : HkSq α 3 (fun z θ =>
      (Work.FTS.Nonlin.N4gg α f z θ + Work.FTS.Nonlin.N5gg f z θ)
        + (Work.FTS.Nonlin.N4gs α f z θ + Work.FTS.Nonlin.N5gs α f z θ))
      ≤ 2 * HkSq α 3 (fun z θ => Work.FTS.Nonlin.N4gg α f z θ + Work.FTS.Nonlin.N5gg f z θ)
        + 2 * HkSq α 3 (fun z θ => Work.FTS.Nonlin.N4gs α f z θ + Work.FTS.Nonlin.N5gs α f z θ) :=
    hABCD.2
  have hAB2 : HkSq α 3 (fun z θ => Work.FTS.Nonlin.N4gg α f z θ + Work.FTS.Nonlin.N5gg f z θ)
      ≤ 2 * HkSq α 3 (Work.FTS.Nonlin.N4gg α f) + 2 * HkSq α 3 (Work.FTS.Nonlin.N5gg f) := hAB.2
  have hEF2 : HkSq α 3 (fun z θ => Work.FTS.Nonlin.N4sg α f z θ + Work.FTS.Nonlin.N5sg α f z θ)
      ≤ 2 * HkSq α 3 (Work.FTS.Nonlin.N4sg α f) + 2 * HkSq α 3 (Work.FTS.Nonlin.N5sg α f) := hEF.2
  have hbig : HkSq α 3 (NFkSum α f)
      ≤ (8 * CT1 + 8 * CT2 + 4 * CT3 + 4 * CT5 + 4 * CT6) * (Ap * K0 ^ 2 * (1 + M) ^ 4) := by
    rw [hNF]
    nlinarith [hALL2, hABCD2, hAB2, hEF2, hT1b, hT2b, hT34b, hT5b, hT6b,
      Work.Spaces.HkSq_nonneg α 3 (Work.FTS.Nonlin.N4gg α f),
      Work.Spaces.HkSq_nonneg α 3 (Work.FTS.Nonlin.N5gg f),
      Work.Spaces.HkSq_nonneg α 3 (Work.FTS.Nonlin.N4sg α f),
      Work.Spaces.HkSq_nonneg α 3 (Work.FTS.Nonlin.N5sg α f),
      Work.Spaces.HkSq_nonneg α 3 (fun z θ => Work.FTS.Nonlin.N4gg α f z θ + Work.FTS.Nonlin.N5gg f z θ),
      Work.Spaces.HkSq_nonneg α 3 (fun z θ => Work.FTS.Nonlin.N4gs α f z θ + Work.FTS.Nonlin.N5gs α f z θ),
      Work.Spaces.HkSq_nonneg α 3 (fun z θ => Work.FTS.Nonlin.N4sg α f z θ + Work.FTS.Nonlin.N5sg α f z θ),
      Work.Spaces.HkSq_nonneg α 3 (fun z θ =>
        (Work.FTS.Nonlin.N4gg α f z θ + Work.FTS.Nonlin.N5gg f z θ)
          + (Work.FTS.Nonlin.N4gs α f z θ + Work.FTS.Nonlin.N5gs α f z θ))]
  have hTot : HkSq α 3 (NFkSum α f) ≤ K1 * Ap * (1 + M) ^ 4 := by
    refine hbig.trans ?_
    have hcoef : 8 * CT1 + 8 * CT2 + 4 * CT3 + 4 * CT5 + 4 * CT6
        ≤ 16 * ((CT1 + CT2) + CT3 + (CT5 + CT6)) := by linarith
    calc (8 * CT1 + 8 * CT2 + 4 * CT3 + 4 * CT5 + 4 * CT6) * (Ap * K0 ^ 2 * (1 + M) ^ 4)
        ≤ (16 * ((CT1 + CT2) + CT3 + (CT5 + CT6))) * (Ap * K0 ^ 2 * (1 + M) ^ 4) :=
          mul_le_mul_of_nonneg_right hcoef hXall
      _ = K1 * Ap * (1 + M) ^ 4 := by rw [hK1def]; ring
  refine ⟨hcNF, hmemNF, ?_⟩
  have hXn6nn : (0 : ℝ) ≤ Work.FTS.StrongPersist.Xn6 α f := Real.sqrt_nonneg (HkSq α 6 f)
  have h1M : (0 : ℝ) ≤ 1 + M := by linarith
  have h1X : (0 : ℝ) ≤ 1 + Work.FTS.StrongPersist.Xn6 α f := by linarith
  have h4M1 : (1 : ℝ) ≤ (1 + M) ^ 4 := by
    have h := pow_le_pow_left₀ (show (0 : ℝ) ≤ 1 by norm_num) (by linarith : (1 : ℝ) ≤ 1 + M) 4
    simpa using h
  have h4X1 : (1 : ℝ) ≤ (1 + Work.FTS.StrongPersist.Xn6 α f) ^ 4 := by
    have h := pow_le_pow_left₀ (show (0 : ℝ) ≤ 1 by norm_num)
      (by linarith : (1 : ℝ) ≤ 1 + Work.FTS.StrongPersist.Xn6 α f) 4
    simpa using h
  have hfac : (1 : ℝ) ≤ Ap * ((1 + M) ^ 4 * (1 + Work.FTS.StrongPersist.Xn6 α f) ^ 4) := by
    calc (1 : ℝ) = 1 * (1 * 1) := by ring
      _ ≤ Ap * ((1 + M) ^ 4 * (1 + Work.FTS.StrongPersist.Xn6 α f) ^ 4) :=
          mul_le_mul hAp1 (mul_le_mul h4M1 h4X1 (by norm_num) (by linarith)) (by norm_num) hApnn
  have hb : HkSq α 3 (NFkSum α f)
      ≤ (Real.sqrt K1 * Ap * (1 + M) ^ 4
          * (1 + Work.FTS.StrongPersist.Xn6 α f) ^ 2) ^ 2 := by
    refine hTot.trans ?_
    have hsqr : (Real.sqrt K1 * Ap * (1 + M) ^ 4
          * (1 + Work.FTS.StrongPersist.Xn6 α f) ^ 2) ^ 2
        = K1 * Ap ^ 2 * (1 + M) ^ 8 * (1 + Work.FTS.StrongPersist.Xn6 α f) ^ 4 := by
      rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hK1pos.le]
      ring
    rw [hsqr]
    calc K1 * Ap * (1 + M) ^ 4
        ≤ K1 * Ap * (1 + M) ^ 4
            * (Ap * ((1 + M) ^ 4 * (1 + Work.FTS.StrongPersist.Xn6 α f) ^ 4)) :=
          le_mul_of_one_le_right (mul_nonneg (mul_nonneg (le_of_lt hK1pos) hApnn) hM4) hfac
      _ = K1 * Ap ^ 2 * (1 + M) ^ 8 * (1 + Work.FTS.StrongPersist.Xn6 α f) ^ 4 := by ring
  have hnorm : HkNorm α 3 (NFkSum α f)
      ≤ Real.sqrt K1 * Ap * (1 + M) ^ 4 * (1 + Work.FTS.StrongPersist.Xn6 α f) ^ 2 := by
    calc HkNorm α 3 (NFkSum α f) = Real.sqrt (HkSq α 3 (NFkSum α f)) := rfl
      _ ≤ Real.sqrt ((Real.sqrt K1 * Ap * (1 + M) ^ 4
            * (1 + Work.FTS.StrongPersist.Xn6 α f) ^ 2) ^ 2) := Real.sqrt_le_sqrt hb
      _ = Real.sqrt K1 * Ap * (1 + M) ^ 4 * (1 + Work.FTS.StrongPersist.Xn6 α f) ^ 2 :=
          Real.sqrt_sq (mul_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hApnn)
              (pow_nonneg h1M 4)) (pow_nonneg h1X 2))
  calc HkNorm α 3 (NFkSum α f)
      ≤ Real.sqrt K1 * Ap * (1 + M) ^ 4 * (1 + Work.FTS.StrongPersist.Xn6 α f) ^ 2 := hnorm
    _ ≤ (Real.sqrt K1 + 1) * Ap * (1 + M) ^ 4 * (1 + Work.FTS.StrongPersist.Xn6 α f) ^ 2 := by
        have h2 : (0 : ℝ) ≤ Ap * (1 + M) ^ 4 * (1 + Work.FTS.StrongPersist.Xn6 α f) ^ 2 :=
          mul_nonneg (mul_nonneg hApnn hM4) (pow_nonneg h1X 2)
        have h3 : Real.sqrt K1 ≤ Real.sqrt K1 + 1 := by linarith
        calc Real.sqrt K1 * Ap * (1 + M) ^ 4 * (1 + Work.FTS.StrongPersist.Xn6 α f) ^ 2
            = Real.sqrt K1 * (Ap * (1 + M) ^ 4 * (1 + Work.FTS.StrongPersist.Xn6 α f) ^ 2) := by ring
          _ ≤ (Real.sqrt K1 + 1) * (Ap * (1 + M) ^ 4 * (1 + Work.FTS.StrongPersist.Xn6 α f) ^ 2) :=
              mul_le_mul_of_nonneg_right h3 h2
          _ = (Real.sqrt K1 + 1) * Ap * (1 + M) ^ 4
                * (1 + Work.FTS.StrongPersist.Xn6 α f) ^ 2 := by ring
    _ = (Real.sqrt K1 + 1) * (α ^ (-Cpow)) * (1 + M) ^ 4
          * (1 + Work.FTS.StrongPersist.Xn6 α f) ^ 2 := by rw [hApdef]

end Work.FTS.StrongPersist.L3Rhs.NfkAux
