import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.IPGen.IP4Lin
import Submission.Work.FTS.LocData.zero_slice_locG
import Submission.Work.FTS.OpenPkg.WtohWin.Assembly
import Submission.Work.FTS.StrongEps.E4R3.N4C.T2HonestGen
import Submission.Work.FTS.StrongEps.E4R3.N4C.T4HonestGen
import Submission.Work.FTS.StrongPersist.H6Row6.Lift
import Submission.Work.FTS.StrongPersist.N6Trans.Hon.SlotHon
import Submission.Work.FTS.StrongPersist.N6Trans.T1Hon.LeafSum
import Submission.Work.FTS.StrongPersist.SP6.EUz6
import Submission.Work.FTS.TransportS.Defs
import Submission.Work.FTS.TransportS.t3SlotGuarded
import Submission.Work.FTS_MuLamOK.Rows.Rl1Defs
import Submission.Work.FTS_RegExport.RXT.velVanish2Star
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_theta
import Submission.Work.PhiStar.Honesty.sqrt_weight_mul_eq_of_mem_Ioo
import Submission.Work.Spaces.sup_mixed_le_H4
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.N4C.ExtraH =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.N4C

open Work.FTS.Galerkin (Fn)
open Work.FTS.Nonlin (Xn)
open Work.FTS.VocabO (HQo CoefTh CoefThMem WDp WDMem)
open Work.Spaces (HkMem HkSq HkNorm Dz Dth)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The honest clause bundle `N4ExtraH` for the concrete `IP4` with positive step
coefficients.** -/
theorem n4ExtraH_IP4 (c₁ c₂ c₁' c₂' c₁'' c₂'' : ℝ) (h₁ : 0 < c₁) (h₂ : 0 < c₂)
    (h₁' : 0 < c₁') (h₂' : 0 < c₂') (h₁'' : 0 < c₁'') (h₂'' : 0 < c₂'') :
    ∃ Ct α₂ : ℝ, 0 < Ct ∧ 0 < α₂ ∧ N4ExtraH (IP4 c₁ c₂ c₁' c₂' c₁'' c₂'') α₂ Ct := by
  obtain ⟨Ccs, α₂cs, hCcs, hα₂cs, hcs⟩ :=
    Work.FTS.IPGen.ip4_cs_HQo h₁.le h₂.le h₁'.le h₂'.le h₁''.le h₂''.le
  obtain ⟨α₂add, hα₂add, hadd⟩ :=
    Work.FTS.IPGen.ip4_add_HQo (c₁ := c₁) (c₂ := c₂) (c₁' := c₁') (c₂' := c₂')
      (c₁'' := c₁'') (c₂'' := c₂'')
  obtain ⟨Ct1, α₂1, hCt1, hα₂1, ht1⟩ := T1HonestGen c₁ c₂ c₁' c₂' c₁'' c₂'' h₁ h₂ h₁' h₂' h₁'' h₂''
  obtain ⟨Ct2, α₂2, hCt2, hα₂2, ht2⟩ := T2HonestGen c₁ c₂ c₁' c₂' c₁'' c₂'' h₁ h₂ h₁' h₂' h₁'' h₂''
  obtain ⟨Ct3, α₂3, hCt3, hα₂3, ht3⟩ := T3HonestGen c₁ c₂ c₁' c₂' c₁'' c₂'' h₁ h₂ h₁' h₂' h₁'' h₂''
  obtain ⟨Ct4, α₂4, hCt4, hα₂4, ht4⟩ := T4HonestGen c₁ c₂ c₁' c₂' c₁'' c₂'' h₁ h₂ h₁' h₂' h₁'' h₂''
  obtain ⟨Cdz, hCdz, hdz⟩ :=
    Work.FTS.StrongEps.EpsE4Thr.dz_four_RegQo (c₁ := c₁) (c₂ := c₂) (c₁' := c₁') (c₂' := c₂')
      (c₁'' := c₁'') (c₂'' := c₂'') h₁ h₂ h₁' h₂' h₁'' h₂''
  set Ct : ℝ := max Ccs (max Ct1 (max Ct2 (max Ct3 (max Ct4 (max Cdz 1))))) with hCtdef
  set α₂ : ℝ := min α₂cs (min α₂add (min α₂1 (min α₂2 (min α₂3 (min α₂4 1))))) with hα₂def
  have hCtpos : 0 < Ct := by
    rw [hCtdef]
    have e1 : (1 : ℝ) ≤ max Cdz 1 := le_max_right _ _
    have e2 : max Cdz 1 ≤ max Ct4 (max Cdz 1) := le_max_right _ _
    have e3 : max Ct4 (max Cdz 1) ≤ max Ct3 (max Ct4 (max Cdz 1)) := le_max_right _ _
    have e4 : max Ct3 (max Ct4 (max Cdz 1))
        ≤ max Ct2 (max Ct3 (max Ct4 (max Cdz 1))) := le_max_right _ _
    have e5 : max Ct2 (max Ct3 (max Ct4 (max Cdz 1)))
        ≤ max Ct1 (max Ct2 (max Ct3 (max Ct4 (max Cdz 1)))) := le_max_right _ _
    have e6 : max Ct1 (max Ct2 (max Ct3 (max Ct4 (max Cdz 1))))
        ≤ max Ccs (max Ct1 (max Ct2 (max Ct3 (max Ct4 (max Cdz 1))))) := le_max_right _ _
    linarith
  have hα₂pos : 0 < α₂ := by
    rw [hα₂def]
    exact lt_min hα₂cs (lt_min hα₂add (lt_min hα₂1 (lt_min hα₂2 (lt_min hα₂3
      (lt_min hα₂4 one_pos)))))
  -- the monotonicity of the constant and of the range
  have hCcs_le : Ccs ≤ Ct := by rw [hCtdef]; exact le_max_left _ _
  have hCt1_le : Ct1 ≤ Ct := by
    rw [hCtdef]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hCt2_le : Ct2 ≤ Ct := by
    rw [hCtdef]
    exact le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  have hCt3_le : Ct3 ≤ Ct := by
    rw [hCtdef]
    exact le_trans (le_max_left _ _)
      (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))
  have hCt4_le : Ct4 ≤ Ct := by
    rw [hCtdef]
    exact le_trans (le_max_left _ _) (le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))))
  have hCdz_le : Cdz ≤ Ct := by
    rw [hCtdef]
    exact le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))))
  have hα₂cs' : α₂ ≤ α₂cs := by rw [hα₂def]; exact min_le_left _ _
  have hα₂add' : α₂ ≤ α₂add := by
    rw [hα₂def]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hα₂1' : α₂ ≤ α₂1 := by
    rw [hα₂def]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hα₂2' : α₂ ≤ α₂2 := by
    rw [hα₂def]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hα₂3' : α₂ ≤ α₂3 := by
    rw [hα₂def]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))))
  have hα₂4' : α₂ ≤ α₂4 := by
    rw [hα₂def]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (min_le_left _ _)))))
  refine ⟨Ct, α₂, hCtpos, hα₂pos, ?_⟩
  refine ⟨⟨hCtpos, hα₂pos⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro α hα f g hf hg
    have hα' : α ∈ Set.Ioc 0 α₂cs := ⟨hα.1, le_trans hα.2 hα₂cs'⟩
    have hXf : 0 ≤ Xn α f := Work.Spaces.HkNorm_nonneg α 4 f
    have hXg : 0 ≤ Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
    calc |IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α f g|
        ≤ Ccs * Xn α f * Xn α g := hcs α hα' f g hf hg
      _ = (Ccs * Xn α f) * Xn α g := by ring
      _ ≤ (Ct * Xn α f) * Xn α g :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCcs_le hXf) hXg
      _ = Ct * Xn α f * Xn α g := by ring
  ·
    intro α hα f₁ f₂ g h₁ h₂ h₃
    have hα' : α ∈ Set.Ioc 0 α₂add := ⟨hα.1, le_trans hα.2 hα₂add'⟩
    exact hadd α hα' f₁ f₂ g h₁ h₂ h₃
  ·
    intro α _ c f g _ _
    exact Work.FTS.IPGen.ip4_smul c₁ c₂ c₁' c₂' c₁'' c₂'' c α f g
  ·
    intro α _ f g _ _
    exact Work.FTS.IPGen.ip4_neg c₁ c₂ c₁' c₂' c₁'' c₂'' α f g
  ·
    intro α hα f f' g _ _ _ h
    exact Work.FTS.IPGen.ip4_congr_Qd hα.1 h
  ·
    intro α hα g hg
    have hαpos : 0 < α := hα.1
    have hbd := hdz α hαpos g hg
    have hmod : HkSq α 4 g = (Xn α g) ^ 2 := by
      show HkSq α 4 g = (Real.sqrt (HkSq α 4 g)) ^ 2
      exact (Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 4 g)).symm
    calc |IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α (Dz g) g|
        ≤ Cdz * HkSq α 4 g := hbd
      _ = Cdz * (Xn α g) ^ 2 := by rw [hmod]
      _ ≤ Ct * Xn α g ^ 2 :=
          mul_le_mul_of_nonneg_right hCdz_le (sq_nonneg _)
  ·
    intro α hα f g hf hg sm dec
    have hα' : α ∈ Set.Ioc 0 α₂1 := ⟨hα.1, le_trans hα.2 hα₂1'⟩
    calc |IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α (fun z θ => f z θ * Dth g z θ) g|
        ≤ Ct1 * α ^ (-(1 / 2 : ℝ)) * Xn α f * Xn α g ^ 2 :=
          ht1 α hα' f g hf.1 hf.2 hg sm dec
      _ ≤ Ct * α ^ (-(1 / 2 : ℝ)) * Xn α f * Xn α g ^ 2 :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCt1_le
              (Real.rpow_nonneg hα.1.le _)) (Work.Spaces.HkNorm_nonneg α 4 f))
            (sq_nonneg _)
  ·
    intro α hα f g hf hmf hcf hg hm4 hm5 dec
    have hα' : α ∈ Set.Ioc 0 α₂2 := ⟨hα.1, le_trans hα.2 hα₂2'⟩
    have h0 : 0 ≤ Xn α f + CoefTh 1 f :=
      add_nonneg (Work.Spaces.HkNorm_nonneg α 4 f) (Work.FTS.TransportS.coefTh_nonneg 1 f)
    calc |IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α (fun z θ => f z θ * Dz g z θ) g|
        ≤ Ct2 * α ^ (-(1 / 2 : ℝ)) * (Xn α f + CoefTh 1 f) * Xn α g ^ 2 :=
          ht2 α hα' f g hf hmf hcf hg hm4 hm5 dec
      _ ≤ Ct * α ^ (-(1 / 2 : ℝ)) * (Xn α f + CoefTh 1 f) * Xn α g ^ 2 :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCt2_le
              (Real.rpow_nonneg hα.1.le _)) h0) (sq_nonneg _)
  ·
    intro α hα f g hf hwf hcf hg hm4 hm5 dec
    have hα' : α ∈ Set.Ioc 0 α₂3 := ⟨hα.1, le_trans hα.2 hα₂3'⟩
    have h0 : 0 ≤ Work.Spaces.WlInf α 4 f + CoefTh 3 f :=
      add_nonneg (Work.FTS.H2.WlInf_nonneg hwf) (Work.FTS.TransportS.coefTh_nonneg 3 f)
    calc |IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α (fun z θ => f z θ * Dz g z θ) g|
        ≤ Ct3 * α ^ (-(1 / 2 : ℝ)) * (Work.Spaces.WlInf α 4 f + CoefTh 3 f) * Xn α g ^ 2 :=
          ht3 α hα' f g hf hwf hcf hg hm4 hm5 dec
      _ ≤ Ct * α ^ (-(1 / 2 : ℝ)) * (Work.Spaces.WlInf α 4 f + CoefTh 3 f) * Xn α g ^ 2 :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCt3_le
              (Real.rpow_nonneg hα.1.le _)) h0) (sq_nonneg _)
  ·
    intro α hα f g hf hwf hg hm4 hm5 dec
    have hα' : α ∈ Set.Ioc 0 α₂4 := ⟨hα.1, le_trans hα.2 hα₂4'⟩
    have h0 : 0 ≤ WDp 4 f := Work.FTS.OpenPkg.WDp_nonneg 4 f
    calc |IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α (fun z θ => f z θ * Dth g z θ) g|
        ≤ Ct4 * α ^ (-(1 / 2 : ℝ)) * WDp 4 f * Xn α g ^ 2 := ht4 α hα' f g hf hwf hg hm4 hm5 dec
      _ ≤ Ct * α ^ (-(1 / 2 : ℝ)) * WDp 4 f * Xn α g ^ 2 :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCt4_le
              (Real.rpow_nonneg hα.1.le _)) h0) (sq_nonneg _)

end Work.FTS.StrongEps.E4R3.N4C
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.UnifIPOOfCoerFinal =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr

open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.Nonlin (Xn)

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "IP4" => Work.FTS.CoercivityFix.Assembly.IP4

/-- **`UnifIPO` for `IP4` from the coercivity clause alone.**  `lo`, `up` and `Dz_self` are
supplied by `lo_four_open`, `up_four_open` and `dz_four_RegQo`; `coer` is the hypothesis. -/
theorem unifIPO_IP4_of_coer_only {c₁ c₂ c₁' c₂' c₁'' c₂'' : ℝ}
    (h₁ : 0 < c₁) (h₂ : 0 < c₂) (h₁' : 0 < c₁') (h₂' : 0 < c₂')
    (h₁'' : 0 < c₁'') (h₂'' : 0 < c₂'')
    {α₂ cc : ℝ} (hα₂ : 0 < α₂) (hcc : 0 < cc)
    (hcoer : ∀ α ∈ Set.Ioc 0 α₂, ∀ f : Fn, CoerAdmO α f →
      cc * Work.Spaces.HkSq α 4 f
        ≤ IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α (Work.Coercivity.LGammaT α f) f) :
    ∃ clo Cup Ccs : ℝ, 0 < clo ∧ 0 < Cup ∧ 0 < Ccs ∧
      UnifIPO (IP4 c₁ c₂ c₁' c₂' c₁'' c₂'') (min α₂ 1) cc clo Cup Ccs := by
  obtain ⟨Cdz, hCdz, hdzb⟩ :=
    dz_four_RegQo (c₁ := c₁) (c₂ := c₂) (c₁' := c₁') (c₂' := c₂')
      (c₁'' := c₁'') (c₂'' := c₂'') h₁ h₂ h₁' h₂' h₁'' h₂''
  refine unifIPO_IP4_of_coer h₁ h₂ h₁' h₂' h₁'' h₂'' hα₂ hcc hcoer ⟨Cdz, hCdz, ?_⟩
  intro α hα f hf
  have h := hdzb α hα.1 f hf.1
  have hsq : (Xn α f) ^ 2 = Work.Spaces.HkSq α 4 f := by
    rw [Work.FTS.Nonlin.Xn, Work.Spaces.HkNorm, Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 4 f)]
  rwa [hsq]

end Work.FTS.StrongEps.EpsE4Thr
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Row6.row6PertData =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Row6

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

open Work.FTS.StrongPersist.H6Pair6Aux.T6Coef (CoefData)

/-! ## Scaling the `CoefTh`/`supAbsO` vocabulary, and the `CoefData` structure

The three perturbed residual fields entering `row6PertData` are the scalar multiples
`2·Rop(Φ̃)`, `-2·(Uop(Φ̃)/sin 2θ)` and `-2α·Vop(Φ̃)` of the fields priced by the level-four
elliptic package `EllPkgGo`.  The lemmas below transport the `CoefData`/`CoefTh` data through
a scalar factor, and are the only place where the scalar bookkeeping happens. -/

/-- `∂_θ` commutes with multiplication by a constant (the unconditional form of `deriv`). -/
theorem r6_pth_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.pth (fun z θ => c * f z θ) = fun z θ => c * Work.Spaces.pth f z θ := by
  funext z θ
  simp only [Work.Spaces.pth]
  exact deriv_const_mul_field c

/-- `SmoothOpen` is stable under multiplication by a constant. -/
theorem r6_smoothOpen_const_mul (c : ℝ) {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => c * f z θ) := by
  refine (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mpr (fun n => ?_)
  exact contDiffOn_const.mul ((Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hf n)

/-- `supAbsO` of a scalar multiple: bound the function pointwise first, then pull the scalar
out. -/
theorem r6_supAbsO_const_mul_le {c : ℝ} {g : ℝ → ℝ → ℝ} {K : ℝ}
    (hK : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → |g z θ| ≤ K) :
    Work.FTS.H2.supAbsO (fun z θ => c * g z θ) ≤ |c| * Work.FTS.H2.supAbsO g := by
  refine Work.FTS.H2.supAbsO_le fun z θ hz hθ hθ' => ?_
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left
    (Work.FTS.H2.le_supAbsO hz hθ hθ' hK) (abs_nonneg c)

/-- `CoefTh` is subadditive for scalar multiples. -/
theorem r6_coefTh_const_mul_le {l : ℕ} {c : ℝ} {g : ℝ → ℝ → ℝ}
    (hmem : Work.FTS.VocabO.CoefThMem l g) :
    Work.FTS.VocabO.CoefTh l (fun z θ => c * g z θ)
      ≤ |c| * Work.FTS.VocabO.CoefTh l g := by
  unfold Work.FTS.VocabO.CoefTh
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun b _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  by_cases hbi : b + i ≤ l
  · rw [if_pos hbi, if_pos hbi]
    obtain ⟨K, hK⟩ := hmem b i hbi
    rw [r6_pth_const_mul c g,
      Work.FTS.LocData.mixed_const_mul c b i (Work.Spaces.pth g)]
    show Work.FTS.H2.supAbsO (fun z θ => c * Work.Spaces.mixed b i (Work.Spaces.pth g) z θ)
      ≤ |c| * Work.FTS.H2.supAbsO (Work.Spaces.mixed b i (Work.Spaces.pth g))
    exact r6_supAbsO_const_mul_le hK
  · rw [if_neg hbi, if_neg hbi, mul_zero]

/-- `CoefThMem` is preserved by multiplication with a constant. -/
theorem r6_coefThMem_const_mul {l : ℕ} {c : ℝ} {g : ℝ → ℝ → ℝ}
    (hmem : Work.FTS.VocabO.CoefThMem l g) :
    Work.FTS.VocabO.CoefThMem l (fun z θ => c * g z θ) := by
  intro b i hbi
  obtain ⟨K, hK⟩ := hmem b i hbi
  refine ⟨|c| * K, fun z θ hz hθ hθ' => ?_⟩
  rw [r6_pth_const_mul c g, Work.FTS.LocData.mixed_const_mul c b i (Work.Spaces.pth g),
    abs_mul]
  exact mul_le_mul_of_nonneg_left (hK z θ hz hθ hθ') (abs_nonneg c)

/-- **`CoefData` of a scalar multiple**: all six fields scale with the factor `|c|`. -/
theorem r6_coefData_const_mul {α c : ℝ} {A : Work.FTS.Galerkin.Fn} {K0 K4 K6 : ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen A)
    (h4 : Work.Spaces.HkMem α 4 A) (h6 : Work.Spaces.HkMem α 6 A)
    (hval : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → |A z θ| ≤ K0)
    (hn4 : Work.Spaces.HkNorm α 4 A ≤ K4) (hn6 : Work.Spaces.HkNorm α 6 A ≤ K6)
    (hK0 : 0 ≤ K0) (hK4 : 0 ≤ K4) (hK6 : 0 ≤ K6) :
    CoefData α (fun z θ => c * A z θ) (|c| * K0) (|c| * K4) (|c| * K6) := by
  have hc0 : 0 ≤ |c| := abs_nonneg c
  have hco : ∀ n : ℕ, ContDiffOn ℝ (↑n) (Function.uncurry A)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall A).mp hsm
  refine ⟨r6_smoothOpen_const_mul c hsm,
    Work.FTS.LocData.HkMem_const_mul α 4 c h4,
    Work.FTS.LocData.HkMem_const_mul α 6 c h6,
    fun z θ hz hθ hθ' => ?_, ?_, ?_⟩
  · rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hval z θ hz hθ hθ') hc0
  · show Work.Spaces.HkNorm α 4 (fun z θ => c * A z θ) ≤ |c| * K4
    rw [Work.FTS.EllipticEst.HkNorm_const_mul α 4 c hco]
    exact mul_le_mul_of_nonneg_left hn4 hc0
  · show Work.Spaces.HkNorm α 6 (fun z θ => c * A z θ) ≤ |c| * K6
    rw [Work.FTS.EllipticEst.HkNorm_const_mul α 6 c hco]
    exact mul_le_mul_of_nonneg_left hn6 hc0

/-- `CoefData` is monotone in the three constants. -/
theorem r6_coefData_mono {α : ℝ} {A : Work.FTS.Galerkin.Fn} {K0 K4 K6 K0' K4' K6' : ℝ}
    (h : CoefData α A K0 K4 K6) (h0 : K0 ≤ K0') (h4 : K4 ≤ K4') (h6 : K6 ≤ K6') :
    CoefData α A K0' K4' K6' :=
  ⟨h.sm, h.h4, h.h6, fun z θ hz hθ hθ' => le_trans (h.val z θ hz hθ hθ') h0,
    le_trans h.n4 h4, le_trans h.n6 h6⟩

/-! ## The constant arithmetic -/





/-! ## The lemma -/


end

end Work.FTS.StrongPersist.H6Row6
end
