import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.GalBasis.hk_sq_api
import Submission.Work.FTS.Nonlinear.Open.Main
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.StrongEps.ClassCRHS.HkMemXnN0
import Submission.Work.FTS.StrongEps.E4R3.N4C.T4HonestGen
import Submission.Work.FTS.StrongEps.E4R3.Nblock6.N_b6_five
import Submission.Work.FTS.StrongEps.EComparison.E_slots_diff_le
import Submission.Work.FTS.StrongEps.EpsE4Thr.CoerDataTO
import Submission.Work.FTS.StrongEps.EpsE4Thr.HnegCore
import Submission.Work.FTS.StrongEps.EpsE4Thr.OpenBarrier
import Submission.Work.FTS.StrongEps.EpsE4Thr.TransO.CoerTransferO
import Submission.Work.FTS.StrongEps.EpsRLX.ProfRHSAux.Components2
import Submission.Work.FTS.StrongEps.EpsWPBounds
import Submission.Work.FTS.StrongEps.EpsZero.slice_facts_of_classC
import Submission.Work.FTS.StrongEps.JfamP_norm
import Submission.Work.FTS.StrongEps.smoothOpen_epsWP
import Submission.Work.FTS.StrongPersist.H6Aux.R.SlotHigh
import Submission.Work.FTS.StrongPersist.H6Row6.row6PertData
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.starSlotShift
import Submission.Work.FTS.TransportS.T3SlotAux.Remainder
import Submission.Work.FTS.TransportS.t3SlotGuarded
import Submission.Work.FTS_EllLimOK.IsBslSolPos_add
import Submission.Work.FTS_LocDatum3a.L12_Jeps_locG6
import Submission.Work.FTS_RegExport.RXT.Sys.pth_vop_slot_bd
import Submission.Work.FTS_RegExport.RXT.landau_1d
import Submission.Work.FTS_RegExport.THL.cs7_rop_split
import Submission.Work.FTS_RegExport.THL.cs7_theta_holder
import Submission.Work.FTS_RegExport.THL.vopPert_theta_holder
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_theta
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.jfamP_core_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv

open Work.FTS.Galerkin (Fn Fam slice dynLin dynRHS)

set_option autoImplicit false
set_option maxHeartbeats 800000

/-- The level-four pairing of the a-priori chapter, abbreviated. -/
abbrev IP4 (c₁ c₂ c₁' c₂' c₁'' c₂'' α : ℝ) : Fn → Fn → ℝ :=
  Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α

/-- **The closing arithmetic of the smallness hypothesis.**  For `α > 0` and `C₀ α^{1/4} ≤ 1` one
has `C₀ α² ≤ α^{7/4}`, so the a-priori ball `Xn α x ≤ C₀ α²` sits inside the N4 smallness ball
`Xn α x ≤ α^{7/4}`. -/
theorem C0_alpha2_le_rpow {C₀ α : ℝ} (hα : 0 < α) (hsmall : C₀ * α ^ (1 / 4 : ℝ) ≤ 1) :
    C₀ * α ^ 2 ≤ α ^ (7 / 4 : ℝ) := by
  have h1 : α ^ (1 / 4 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hα _).ne'
  have h2 : C₀ ≤ α ^ (-(1 / 4) : ℝ) := by
    have h3 : C₀ * α ^ (1 / 4 : ℝ) / α ^ (1 / 4 : ℝ) ≤ 1 / α ^ (1 / 4 : ℝ) :=
      div_le_div_of_nonneg_right hsmall (le_of_lt (Real.rpow_pos_of_pos hα _))
    rw [mul_div_cancel_right₀ _ h1] at h3
    rwa [one_div, ← Real.rpow_neg hα.le] at h3
  calc C₀ * α ^ 2 = C₀ * α ^ (2 : ℝ) := by rw [Real.rpow_ofNat]
    _ ≤ α ^ (-(1 / 4) : ℝ) * α ^ (2 : ℝ) := mul_le_mul_of_nonneg_right h2 (by positivity)
    _ = α ^ (-(1 / 4) + 2 : ℝ) := (Real.rpow_add hα _ _).symm
    _ = α ^ (7 / 4 : ℝ) := by norm_num

/-- The `ℋ⁴`-honesty of `dynLin α (fun z θ _ => f z θ) 0 = -𝓛_Γ^T f`, from that of `𝓛_Γ^T f`
(pointwise negation preserves the integrand). -/
theorem hkMem_dynLin {α : ℝ} {f : Fn}
    (h : Work.Spaces.HkMem α 4 (Work.Coercivity.LGammaT α f)) :
    Work.Spaces.HkMem α 4 (dynLin α (fun z θ _ => f z θ) 0) := by
  have h2 : dynLin α (fun z θ _ => f z θ) 0
      = fun z θ => - (Work.Coercivity.LGammaT α f) z θ := by
    funext z θ
    rfl
  rw [h2]
  exact Work.FTS.StrongEps.hkMem_neg_epsWP h

/-- **The core inequality of the level-four barrier, at a positive mollification scale.**

This is the statement of `jfamP_core_le` with the extra hypothesis `0 < ε₀`; the passage to
*negative* `ε₀` is by reflection of the kernel (`JepsNegComp`) and the case `ε₀ = 0` is degenerate
(`JepsZero`), both handled in the main theorem below.

The proof is the four-step argument of the chapter:

1. **dissipation.** `IP_dynLin_le_of_eq` (open-class coercivity plus `UnifIPO.up`) turns the
   barrier hypothesis `IP4 α x x = clo·(C₀α²)²` into `IP4 α (dynLin α g τ) x ≤ -cc·(clo·(C₀α²)²/Cup)`;
2. **`ℋ⁶`-regularity of the projected family.** `HkNorm_JfamP_le_pos` bounds the `ℋ⁶`-size of
   `slice (JfamP ρ ε₀ g) s` by `A e^{A ε₀} Xn6 (slice g s) ≤ A e^{A ε₀} M`; this is the input
   that `HQo_dynRHS` needs for the `ℋ⁴`-membership of the nonlinear part;
3. **additivity.** `IPGen.Comm2o_three` (the three-step `Comm2o` package, which asks for the open
   class `SmoothOpen` + `HkMem α 4` on its three arguments) splits the pairing of
   `dynLin + dynRHS`;
4. **the nonlinear half.** `hN4` bounds `|rhsPair IP4 α x (Φs + E x)|` by `CcN·Pbd α (Xn α x)`,
   and `Pbd_mono` upgrades `Xn α x ≤ C₀α²` to `Pbd α (C₀α²)`; the sign `0 ≤ CcN` is recovered from
   `UnifIPO.up` (which forces `HkSq α 4 x > 0`, hence `Pbd α (Xn α x) > 0`). -/
theorem core_le_pos {ρ : ℝ × ℝ → ℝ} (c₁ c₂ c₁' c₂' c₁'' c₂'' : ℝ)
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    {α₂ cc clo Cup Ccs CcN : ℝ}
    (hU : Work.FTS.StrongEps.EpsE4Thr.UnifIPO (IP4 c₁ c₂ c₁' c₂' c₁'' c₂'') α₂ cc clo Cup Ccs)
    {Ce Cs : ℝ}
    (hN4 : ∀ α ∈ Set.Ioc 0 α₂, ∀ {g Φs Φg : Fn},
      Work.FTS.ClassC.ClassC α g → Work.FTS.StrongEps.EpsE4Thr.CoerAdmO α g →
      Work.FTS.VocabO2.StarPkgo2 α Cs Φs → Work.FTS.VocabO.EllPkgGo α Ce g Φg →
      Work.FTS.Nonlin.Xn α g ≤ α ^ (7 / 4 : ℝ) →
      |Work.FTS.Apriori.rhsPair (IP4 c₁ c₂ c₁' c₂' c₁'' c₂'')
        α g (fun z θ => Φs z θ + Φg z θ)|
        ≤ CcN * Work.FTS.Nonlin.Pbd α (Work.FTS.Nonlin.Xn α g))
    {α C₀ M : ℝ} (hα : α ∈ Set.Ioc 0 α₂) (hα1 : α ≤ 1) (hC₀ : 0 < C₀) (hM : 0 ≤ M)
    (hsmall : C₀ * α ^ (1 / 4 : ℝ) ≤ 1)
    {T τ ε₀ : ℝ} {Φs : Fn} {E : Fn → Fn} {g : Fam}
    (hε₀ : 0 < ε₀) (hτ : τ ∈ Set.Ioo 0 T)
    (hreg : Work.FTS.StrongEps.EpsRegP α ρ ε₀ T g)
    (hXn6 : ∀ s ∈ Set.Icc 0 T, Work.FTS.StrongGlobal.Xn6 α (slice g s) ≤ M)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hml : Work.FTS.StrongEps.MuLamOK α C₀ Φs E)
    (hb4 : ∀ t ∈ Set.Icc 0 τ, Work.FTS.Nonlin.Xn α (slice (Work.FTS.StrongEps.JfamP ρ ε₀ g) t)
      ≤ C₀ * α ^ 2)
    (hY : IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α
        (slice (Work.FTS.StrongEps.JfamP ρ ε₀ g) τ)
        (slice (Work.FTS.StrongEps.JfamP ρ ε₀ g) τ) = clo * (C₀ * α ^ 2) ^ 2) :
    IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α
        (dynLin α (Work.FTS.StrongEps.JfamP ρ ε₀ g) τ
          + dynRHS α (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.StrongEps.JfamP ρ ε₀ g))
              (Work.FTS.StrongEps.JfamP ρ ε₀ g) τ)
        (slice (Work.FTS.StrongEps.JfamP ρ ε₀ g) τ)
      ≤ -(cc * ((clo * (C₀ * α ^ 2) ^ 2) / Cup) - CcN * Work.FTS.Nonlin.Pbd α (C₀ * α ^ 2)) := by
  have hαIoc : α ∈ Set.Ioc 0 1 := ⟨hα.1, hα1⟩
  have hτT : τ ∈ Set.Icc 0 T := ⟨le_of_lt hτ.1, le_of_lt hτ.2⟩
  set x : Fn := slice (Work.FTS.StrongEps.JfamP ρ ε₀ g) τ with hx
  have hclassC : Work.FTS.ClassC.ClassC α x := (hreg.2 τ hτT).2.2
  have hcoer : Work.FTS.StrongEps.EpsE4Thr.CoerAdmO α x :=
    Work.FTS.StrongEps.EpsE4Thr.coerAdmO_slice_JfamP hreg τ hτT
  have hregL : Work.FTS.StrongEps.EpsE4Thr.RegQo α 4 (Work.Coercivity.LGammaT α x) :=
    Work.FTS.StrongEps.EpsE4Thr.regQo_LGammaT hαIoc hclassC
  -- ### positivity of the barrier level and of the norms
  have hCup : 0 < Cup := hU.pos.2.2.2.1
  have hclo : 0 < clo := hU.pos.2.2.1
  have hα2 : 0 < C₀ * α ^ 2 := mul_pos hC₀ (pow_pos hα.1 2)
  have hYpos : 0 < clo * (C₀ * α ^ 2) ^ 2 := mul_pos hclo (pow_pos hα2 2)
  -- ### step 1: the dissipative half
  have hdLin : IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α (dynLin α (Work.FTS.StrongEps.JfamP ρ ε₀ g) τ) x
      ≤ - cc * ((clo * (C₀ * α ^ 2) ^ 2) / Cup) :=
    Work.FTS.StrongEps.EpsE4Thr.IP_dynLin_le_of_eq (IP := IP4 c₁ c₂ c₁' c₂' c₁'' c₂'')
      (g := Work.FTS.StrongEps.JfamP ρ ε₀ g) (τ := τ) hU hα hcoer hregL hY
  -- ### step 2: the `ℋ⁶`-bound on the projected family, and the `HQo`-regularity of `dynRHS`
  obtain ⟨A, hA0, hAle⟩ := HkNorm_JfamP_le_pos hρ
  have hB0 : 0 ≤ A * Real.exp (A * ε₀) := mul_nonneg hA0 (Real.exp_pos _).le
  have hb6 : ∀ s ∈ Set.Icc 0 τ, Work.FTS.StrongGlobal.Xn6 α
      (slice (Work.FTS.StrongEps.JfamP ρ ε₀ g) s) ≤ A * Real.exp (A * ε₀) * M := by
    intro s hs
    have hsT : s ∈ Set.Icc 0 T := ⟨hs.1, le_trans hs.2 hτT.2⟩
    have hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry (slice g s)) Work.FTS.StrongEps.Quad :=
      fun n => Work.FTS.EllipticEst.SmoothOpen.forall (hreg.2 s hsT).1 n
    have hmem : Work.Spaces.HkMem α 6 (slice g s) := (hreg.2 s hsT).2.1
    obtain ⟨-, hbd⟩ := hAle hαIoc hε₀ hsm hmem
    exact le_trans hbd (mul_le_mul_of_nonneg_left (hXn6 s hsT) hB0)
  have hCτ : ∀ s ∈ Set.Icc 0 τ, Work.FTS.ClassC.ClassC α
      (slice (Work.FTS.StrongEps.JfamP ρ ε₀ g) s) :=
    fun s hs => (hreg.2 s ⟨hs.1, le_trans hs.2 hτT.2⟩).2.2
  have hdynD : Work.FTS.VocabO.HQo α 4
      (dynRHS α (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.StrongEps.JfamP ρ ε₀ g))
        (Work.FTS.StrongEps.JfamP ρ ε₀ g) τ) :=
    HQo_dynRHS hτ.1 hαIoc hEll hstar hml hCτ hb4 hb6
  -- ### the `HQo` memberships of the two other arguments of the pairing
  have hlin_sm : Work.FTS.EllipticEst.SmoothOpen
      (dynLin α (Work.FTS.StrongEps.JfamP ρ ε₀ g) τ) :=
    (Work.FTS.StrongEps.ClassCRHS.SmoothOpenRHS hα.1 hα1 hclassC (hEll x hclassC).1 hstar).2.2.1.neg
  have hlin_mem : Work.Spaces.HkMem α 4 (dynLin α (Work.FTS.StrongEps.JfamP ρ ε₀ g) τ) :=
    hkMem_dynLin hregL.2.1
  have hx_mem : Work.Spaces.HkMem α 4 x :=
    Work.FTS.OpenPkg.HkMem_mono_open hclassC.reg 4 (by norm_num) hclassC.mem
  -- ### step 3: additivity of `IP4` on the open class
  have hadd : IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α
        (dynLin α (Work.FTS.StrongEps.JfamP ρ ε₀ g) τ
          + dynRHS α (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.StrongEps.JfamP ρ ε₀ g))
              (Work.FTS.StrongEps.JfamP ρ ε₀ g) τ) x
      = IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α (dynLin α (Work.FTS.StrongEps.JfamP ρ ε₀ g) τ) x
        + IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α
            (dynRHS α (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.StrongEps.JfamP ρ ε₀ g))
              (Work.FTS.StrongEps.JfamP ρ ε₀ g) τ) x :=
    (Work.FTS.IPGen.Comm2o_three α (by linarith [hα.1])).add
      (dynLin α (Work.FTS.StrongEps.JfamP ρ ε₀ g) τ)
      (dynRHS α (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.StrongEps.JfamP ρ ε₀ g))
        (Work.FTS.StrongEps.JfamP ρ ε₀ g) τ) x
      hlin_sm hdynD.1 hclassC.reg hlin_mem hdynD.2 hx_mem
  -- ### step 4: the nonlinear half, via the N4 pairing estimate
  have hXn_le : Work.FTS.Nonlin.Xn α x ≤ α ^ (7 / 4 : ℝ) := by
    have h1 : Work.FTS.Nonlin.Xn α x ≤ C₀ * α ^ 2 := hb4 τ ⟨le_of_lt hτ.1, le_rfl⟩
    have h2 : C₀ * α ^ 2 ≤ α ^ (7 / 4 : ℝ) := C0_alpha2_le_rpow hα.1 hsmall
    linarith
  have hN4app := hN4 α hα (g := x) (Φs := Φs) (Φg := E x) hclassC hcoer hstar
    (hEll x hclassC).1 hXn_le
  have hident : IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α
        (dynRHS α (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.StrongEps.JfamP ρ ε₀ g))
          (Work.FTS.StrongEps.JfamP ρ ε₀ g) τ) x
      = Work.FTS.Apriori.rhsPair (IP4 c₁ c₂ c₁' c₂' c₁'' c₂'') α x
          (fun z θ => Φs z θ + E x z θ) := by
    rw [hx]
    rfl
  have hCcN : 0 ≤ CcN := by
    have hup := hU.up α hα x hcoer
    have h1 : 0 < Cup * Work.Spaces.HkSq α 4 x := by
      rw [hY] at hup
      exact lt_of_lt_of_le hYpos hup
    have hsq : 0 < Work.Spaces.HkSq α 4 x := pos_of_mul_pos_right h1 hCup.le
    have hXpos : 0 < Work.FTS.Nonlin.Xn α x := Real.sqrt_pos.mpr hsq
    have hPbdpos : 0 < Work.FTS.Nonlin.Pbd α (Work.FTS.Nonlin.Xn α x) := by
      have h0 : 0 < α ^ 2 * Work.FTS.Nonlin.Xn α x := mul_pos (pow_pos hα.1 2) hXpos
      have h3 : 0 ≤ α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α x ^ 3 :=
        mul_nonneg (Real.rpow_nonneg hα.1.le _) (pow_nonneg hXpos.le 3)
      have h4 : 0 ≤ α ^ (-(5 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α x ^ 4 :=
        mul_nonneg (Real.rpow_nonneg hα.1.le _) (pow_nonneg hXpos.le 4)
      have h5 : 0 ≤ Real.sqrt α * Work.FTS.Nonlin.Xn α x ^ 2 :=
        mul_nonneg (Real.sqrt_nonneg _) (sq_nonneg _)
      simp only [Work.FTS.Nonlin.Pbd]
      linarith
    have h2 : 0 ≤ CcN * Work.FTS.Nonlin.Pbd α (Work.FTS.Nonlin.Xn α x) :=
      le_trans (abs_nonneg _) hN4app
    exact (mul_nonneg_iff_of_pos_right hPbdpos).mp h2
  have hdynD_le : IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α
        (dynRHS α (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.StrongEps.JfamP ρ ε₀ g))
          (Work.FTS.StrongEps.JfamP ρ ε₀ g) τ) x
      ≤ CcN * Work.FTS.Nonlin.Pbd α (C₀ * α ^ 2) := by
    have hmono : Work.FTS.Nonlin.Pbd α (Work.FTS.Nonlin.Xn α x)
        ≤ Work.FTS.Nonlin.Pbd α (C₀ * α ^ 2) :=
      Work.FTS.Apriori.Pbd_mono hα.1 (Work.Spaces.HkNorm_nonneg α 4 x)
        (hb4 τ ⟨le_of_lt hτ.1, le_rfl⟩)
    calc IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α
          (dynRHS α (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.StrongEps.JfamP ρ ε₀ g))
            (Work.FTS.StrongEps.JfamP ρ ε₀ g) τ) x
        = Work.FTS.Apriori.rhsPair (IP4 c₁ c₂ c₁' c₂' c₁'' c₂'') α x
            (fun z θ => Φs z θ + E x z θ) := hident
      _ ≤ |Work.FTS.Apriori.rhsPair (IP4 c₁ c₂ c₁' c₂' c₁'' c₂'') α x
            (fun z θ => Φs z θ + E x z θ)| := le_abs_self _
      _ ≤ CcN * Work.FTS.Nonlin.Pbd α (Work.FTS.Nonlin.Xn α x) := hN4app
      _ ≤ CcN * Work.FTS.Nonlin.Pbd α (C₀ * α ^ 2) :=
          mul_le_mul_of_nonneg_left hmono hCcN
  -- ### assembly of the two halves
  rw [hadd]
  linarith [hdLin, hdynD_le]

theorem jfamP_core_le {ρ : ℝ × ℝ → ℝ} (c₁ c₂ c₁' c₂' c₁'' c₂'' : ℝ)
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    {α₂ cc clo Cup Ccs CcN : ℝ}
    (hU : Work.FTS.StrongEps.EpsE4Thr.UnifIPO
      (Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'') α₂ cc clo Cup Ccs)
    {Ce Cs : ℝ}
    (hN4 : ∀ α ∈ Set.Ioc 0 α₂, ∀ {g Φs Φg : Work.FTS.Galerkin.Fn},
      Work.FTS.ClassC.ClassC α g → Work.FTS.StrongEps.EpsE4Thr.CoerAdmO α g →
      Work.FTS.VocabO2.StarPkgo2 α Cs Φs → Work.FTS.VocabO.EllPkgGo α Ce g Φg →
      Work.FTS.Nonlin.Xn α g ≤ α ^ (7 / 4 : ℝ) →
      |Work.FTS.Apriori.rhsPair (Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'')
        α g (fun z θ => Φs z θ + Φg z θ)|
        ≤ CcN * Work.FTS.Nonlin.Pbd α (Work.FTS.Nonlin.Xn α g))
    {α C₀ M : ℝ} (hα : α ∈ Set.Ioc 0 α₂) (hα1 : α ≤ 1) (hC₀ : 0 < C₀) (hM : 0 ≤ M)
    (hsmall : C₀ * α ^ (1 / 4 : ℝ) ≤ 1) :
    ∀ {T τ ε₀ : ℝ} {Φs : Work.FTS.Galerkin.Fn}
      {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {g₀ : Work.FTS.Galerkin.Fn}
      {g : Work.FTS.Galerkin.Fam},
      τ ∈ Set.Ioo 0 T →
      Work.FTS.StrongEps.EpsRegP α ρ ε₀ T g →
      (∀ s ∈ Set.Icc 0 T, Work.FTS.StrongGlobal.Xn6 α (Work.FTS.Galerkin.slice g s) ≤ M) →
      (∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α u →
        Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u)) →
      Work.FTS.VocabO2.StarPkgo2 α Cs Φs → Work.FTS.StrongEps.MuLamOK α C₀ Φs E →
      (∀ t ∈ Set.Icc 0 τ, Work.FTS.Nonlin.Xn α
        (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε₀ g) t) ≤ C₀ * α ^ 2) →
      Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α
          (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε₀ g) τ)
          (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε₀ g) τ) = clo * (C₀ * α ^ 2) ^ 2 →
      Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α
          (Work.FTS.Galerkin.dynLin α (Work.FTS.StrongEps.JfamP ρ ε₀ g) τ
            + Work.FTS.Galerkin.dynRHS α
                (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.StrongEps.JfamP ρ ε₀ g))
                (Work.FTS.StrongEps.JfamP ρ ε₀ g) τ)
          (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε₀ g) τ)
        ≤ -(cc * ((clo * (C₀ * α ^ 2) ^ 2) / Cup) - CcN * Work.FTS.Nonlin.Pbd α (C₀ * α ^ 2)) := by
  intro T τ ε₀ Φs E g₀ g hτ hreg hXn6 hEll hstar hml hb4 hY
  have hCup : 0 < Cup := hU.pos.2.2.2.1
  have hclo : 0 < clo := hU.pos.2.2.1
  have hα2 : 0 < C₀ * α ^ 2 := mul_pos hC₀ (pow_pos hα.1 2)
  have hYpos : 0 < clo * (C₀ * α ^ 2) ^ 2 := mul_pos hclo (pow_pos hα2 2)
  rcases lt_trichotomy ε₀ 0 with hneg | hzero | hpos
  · -- ### `ε₀ < 0`: reflect the kernel at `-ε₀ > 0`
    set ρ' : ℝ × ℝ → ℝ := fun p => ρ (-p) with hρ'def
    have hε₀' : 0 < -ε₀ := neg_pos.mpr hneg
    obtain ⟨hρ', hJeps⟩ := JepsNegComp hρ hneg
    have hfam : Work.FTS.StrongEps.JfamP ρ' (-ε₀) g = Work.FTS.StrongEps.JfamP ρ ε₀ g := by
      funext z θ s
      show Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ' (-ε₀) (slice g s)) z θ
        = Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε₀ (slice g s)) z θ
      rw [← hJeps (slice g s)]
    have hreg' : Work.FTS.StrongEps.EpsRegP α ρ' (-ε₀) T g :=
      ⟨hreg.1, fun τ hτ' => ⟨(hreg.2 τ hτ').1, (hreg.2 τ hτ').2.1, by
        rw [← hJeps (slice g τ)]
        exact (hreg.2 τ hτ').2.2⟩⟩
    have hb4' : ∀ t ∈ Set.Icc 0 τ, Work.FTS.Nonlin.Xn α
        (slice (Work.FTS.StrongEps.JfamP ρ' (-ε₀) g) t) ≤ C₀ * α ^ 2 := by
      intro t ht
      rw [hfam]
      exact hb4 t ht
    have hY' : Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α
        (slice (Work.FTS.StrongEps.JfamP ρ' (-ε₀) g) τ)
        (slice (Work.FTS.StrongEps.JfamP ρ' (-ε₀) g) τ) = clo * (C₀ * α ^ 2) ^ 2 := by
      rw [hfam]
      exact hY
    rw [← hfam]
    exact core_le_pos (ρ := ρ') c₁ c₂ c₁' c₂' c₁'' c₂'' hρ' hU hN4 hα hα1 hC₀ hM hsmall
      hε₀' hτ hreg' hXn6 hEll hstar hml hb4' hY'
  · -- ### `ε₀ = 0`: the projected family vanishes, against the barrier hypothesis
    subst hzero
    obtain ⟨hJeps0, hPz0, hKn0, -⟩ := JepsZero ρ (slice g τ)
    have hx0 : slice (Work.FTS.StrongEps.JfamP ρ 0 g) τ = 0 := by
      show Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ 0 (slice g τ)) = 0
      rw [hJeps0, hPz0]
    have hsq0 : Work.Spaces.HkSq α 4 (0 : Fn) = 0 := by
      calc Work.Spaces.HkSq α 4 (0 : Fn) = (Work.Spaces.HkNorm α 4 (0 : Fn)) ^ 2 := by
            rw [Work.Spaces.HkNorm, Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 4 _)]
        _ = 0 := by rw [hKn0]; ring
    have hcoer : Work.FTS.StrongEps.EpsE4Thr.CoerAdmO α
        (slice (Work.FTS.StrongEps.JfamP ρ 0 g) τ) :=
      Work.FTS.StrongEps.EpsE4Thr.coerAdmO_slice_JfamP hreg τ
        ⟨le_of_lt hτ.1, le_of_lt hτ.2⟩
    have hup := hU.up α hα _ hcoer
    exfalso
    rw [hx0] at hup hY
    rw [hsq0, mul_zero] at hup
    linarith
  · -- ### `ε₀ > 0`: the main case
    exact core_le_pos (ρ := ρ) c₁ c₂ c₁' c₂' c₁'' c₂'' hρ hU hN4 hα hα1 hC₀ hM hsmall
      hpos hτ hreg hXn6 hEll hstar hml hb4 hY

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.n4Pair_classC =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3

set_option autoImplicit false

/-- **`UnifIPO` is monotone in the range `α₂`**: the clauses are quantified over
`α ∈ (0, α₂]`, so a witness on the larger range restricts to the smaller one. -/
theorem UnifIPO_mono {IP : ℝ → Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn → ℝ}
    {α₂ α₂' cc clo Cup Ccs : ℝ} (hα₂' : α₂' ≤ α₂) (hα₂'pos : 0 < α₂')
    (h : Work.FTS.StrongEps.EpsE4Thr.UnifIPO IP α₂ cc clo Cup Ccs) :
    Work.FTS.StrongEps.EpsE4Thr.UnifIPO IP α₂' cc clo Cup Ccs :=
  ⟨⟨hα₂'pos, h.pos.2.1, h.pos.2.2.1, h.pos.2.2.2.1, h.pos.2.2.2.2⟩,
   fun α f g => h.symm α f g,
   fun α hα f₁ f₂ g h₁ h₂ h₃ => h.add_fst α ⟨hα.1, le_trans hα.2 hα₂'⟩ f₁ f₂ g h₁ h₂ h₃,
   fun α hα c f g h₁ h₂ => h.smul_fst α ⟨hα.1, le_trans hα.2 hα₂'⟩ c f g h₁ h₂,
   fun α hα f f' g h₁ h₂ hh => h.congr_qd α ⟨hα.1, le_trans hα.2 hα₂'⟩ f f' g h₁ h₂ hh,
   fun α hα f hf => h.nonneg α ⟨hα.1, le_trans hα.2 hα₂'⟩ f hf,
   fun α hα f g h₁ h₂ => h.cs α ⟨hα.1, le_trans hα.2 hα₂'⟩ f g h₁ h₂,
   fun α hα f hf => h.lo α ⟨hα.1, le_trans hα.2 hα₂'⟩ f hf,
   fun α hα f hf => h.up α ⟨hα.1, le_trans hα.2 hα₂'⟩ f hf,
   fun α hα f hf => h.coer α ⟨hα.1, le_trans hα.2 hα₂'⟩ f hf,
   fun α hα f hf => h.Dz_self α ⟨hα.1, le_trans hα.2 hα₂'⟩ f hf⟩

theorem n4Pair_classC {Ce Cs : ℝ} (hCe : 0 < Ce) (hCs : 0 < Cs) :
    ∃ (c₁ c₂ c₁' c₂' c₁'' c₂'' α₂ cc clo Cup Ccs CcN : ℝ),
      0 < c₁ ∧ 0 < c₂ ∧ 0 < c₁' ∧ 0 < c₂' ∧ 0 < c₁'' ∧ 0 < c₂'' ∧
      0 < α₂ ∧ 0 < cc ∧ 0 < clo ∧ 0 < Cup ∧ 0 < Ccs ∧ 0 < CcN ∧
      Work.FTS.StrongEps.EpsE4Thr.UnifIPO
          (Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'') α₂ cc clo Cup Ccs ∧
      ∀ α ∈ Set.Ioc 0 α₂, ∀ {g Φs Φg : Work.FTS.Galerkin.Fn},
        Work.FTS.ClassC.ClassC α g → Work.FTS.StrongEps.EpsE4Thr.CoerAdmO α g →
        Work.FTS.VocabO2.StarPkgo2 α Cs Φs → Work.FTS.VocabO.EllPkgGo α Ce g Φg →
        Work.FTS.Nonlin.Xn α g ≤ α ^ (7 / 4 : ℝ) →
        |Work.FTS.Apriori.rhsPair
            (Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'')
            α g (fun z θ => Φs z θ + Φg z θ)|
          ≤ CcN * Work.FTS.Nonlin.Pbd α (Work.FTS.Nonlin.Xn α g) := by
  -- ## the coercivity witness for the concrete `IP4`
  obtain ⟨c₁, c₂, c₁', c₂', c₁'', c₂'', h₁, h₂, h₁', h₂', h₁'', h₂'', α₂U, cc, clo, Cup, Ccs,
    hα₂U, hcc, hclo, hCup, hCcs, hU⟩ :=
    Work.FTS.StrongEps.EpsE4Thr.TransO.unifIPO_IP4_of_transfer
  -- ## the honest clause bundle for those coefficients
  obtain ⟨Ct, α₂E, hCtpos, hα₂Epos, hE⟩ :=
    Work.FTS.StrongEps.E4R3.N4C.n4ExtraH_IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' h₁ h₂ h₁' h₂' h₁'' h₂''
  -- ## a common range
  set α₂ : ℝ := min α₂E (min α₂U 1) with hα₂def
  have hα₂pos : 0 < α₂ := by
    rw [hα₂def]; exact lt_min hα₂Epos (lt_min hα₂U one_pos)
  have hα₂one : α₂ ≤ 1 := by
    rw [hα₂def]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hα₂E' : α₂ ≤ α₂E := by rw [hα₂def]; exact min_le_left _ _
  have hα₂U' : α₂ ≤ α₂U := by
    rw [hα₂def]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hE' : Work.FTS.StrongEps.E4R3.N4C.N4ExtraH
      (Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'') α₂ Ct :=
    hE.mono hα₂E' hα₂pos
  -- ## the norm interface and the honest row table
  obtain ⟨Ci, _hCi, hN⟩ :=
    Work.FTS.OpenPkg.N4Norm'_exists_of_all_fields (α₂ := α₂) hα₂pos hα₂one
  obtain ⟨K₁, hK₁, hrowN0⟩ := Work.FTS.StrongEps.E4R3.N4C.rowsN0T
    (IP := Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'') hN hE'
  obtain ⟨K₂, hK₂, hrowN⟩ := Work.FTS.StrongEps.E4R3.N4C.rowsNT
    (IP := Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'')
    (Ce := Ce) (Cs := Cs) hN hE'
  obtain ⟨K₃, hK₃, hrowAux⟩ := Work.FTS.StrongEps.E4R3.N4C.rowsAuxT
    (IP := Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'')
    (Ce := Ce) (Cs := Cs) hN hE'
  have hhk : ∀ {α : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn},
      Work.FTS.StrongEps.E4R3.N4C.CtxT Cs Ce α₂ α g Φs Φg →
      Work.FTS.OpenPkg.PiecesHk α g Φs Φg :=
    Work.FTS.StrongEps.E4R3.N4C.rowsHkT
      (IP := Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'')
      (Ce := Ce) (Cs := Cs) hN hE'
  have hsp : ∀ {α : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn},
      Work.FTS.StrongEps.E4R3.N4C.CtxT Cs Ce α₂ α g Φs Φg →
      Work.FTS.NonlinRows.SplitsData α g Φs Φg :=
    Work.FTS.StrongEps.E4R3.N4C.rowsSplitsT (Cs := Cs) (Ce := Ce) (α₂ := α₂)
  have hR : Work.FTS.StrongEps.E4R3.N4C.RowsT
      (Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'') α₂ Ce Cs :=
    ⟨K₁, K₂, K₃, hK₁, hK₂, hK₃, fun hc => hrowN0 hc, fun hc => hrowN hc,
      fun hc => hrowAux hc, fun hc => hhk hc, fun hc => hsp hc⟩
  -- ## the pairing estimate
  obtain ⟨CcN, α₄, hCcN, hα₄pos, _hα₄α₂, hbound⟩ :=
    Work.FTS.StrongEps.E4R3.N4C.pairingBoundT
      (IP := Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'') hCs hCe hE' hR
  -- ## the final constants
  have hfinpos : 0 < min α₄ α₂ := lt_min hα₄pos hα₂pos
  refine ⟨c₁, c₂, c₁', c₂', c₁'', c₂'', min α₄ α₂, cc, clo, Cup, Ccs, CcN, h₁, h₂, h₁', h₂',
    h₁'', h₂'', hfinpos, hcc, hclo, hCup, hCcs, hCcN, ?_, ?_⟩
  · exact UnifIPO_mono (le_trans (min_le_right _ _) hα₂U') hfinpos hU
  · intro α hα g Φs Φg hclassC hco hstar hell hX
    have hα₄ : α ≤ α₄ := le_trans hα.2 (min_le_left _ _)
    have hα₂' : α ≤ α₂ := le_trans hα.2 (min_le_right _ _)
    have hα1 : α ≤ 1 := le_trans hα₂' hα₂one
    exact hbound α ⟨hα.1, hα₄⟩ (g := g) (Φs := Φs) (Φg := Φg)
      ⟨hα.1, hα1, hα₂', hclassC, hco, hstar, hell⟩ hX

end Work.FTS.StrongEps.E4R3
end
