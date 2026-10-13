/-
# `E4R3/N4C/ExtraH` — the honest clause bundle for the concrete `IP4`

This module instantiates the honest clause bundle `N4C.N4ExtraH` at the concrete coercive
pairing `Work.FTS.CoercivityFix.Assembly.IP4 c₁ … c₂''` with *arbitrary positive* step
coefficients.  The clauses are taken from

* `cs` — `IPGen.ip4_cs_HQo` (Cauchy–Schwarz on the open class `HQo α 4 × HQo α 4`);
* `add` — `IPGen.ip4_add_HQo` (additivity on `HQo α 4`);
* `smul`, `neg` — `IPGen.ip4_smul`, `IPGen.ip4_neg` (unconditional homogeneity and negation);
* `congr` — `IPGen.ip4_congr_Qd` (membership-free congruence on the open quadrant);
* `dz` — `EpsE4Thr.dz_four_RegQo` (the lossless `D_z`-self-pairing on the open coercivity
  class `RegQo α 5`, one of the three comparison clauses of the level-four coercivity);
* `t1`/`t2`/`t3`/`t4` — the honest transport clauses `N4C.T1HonestGen` … `N4C.T4HonestGen`.

The single constant `Ct` and the single range `α₂` are the maxima resp. minima of the constants
and ranges of the six families; the monotonicity of each clause in the constant and in the range
is elementary.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongEps.E4R3.N4C.Defs
import Submission.Work.FTS.StrongEps.E4R3.N4C.T1HonestGen
import Submission.Work.FTS.StrongEps.E4R3.N4C.T2HonestGen
import Submission.Work.FTS.StrongEps.E4R3.N4C.T3HonestGen
import Submission.Work.FTS.StrongEps.E4R3.N4C.T4HonestGen
import Submission.Work.FTS.IPGen.IP4Lin
import Submission.Work.FTS.IPGen.IP4Add
import Submission.Work.FTS.IPGen.IP4Smul
import Submission.Work.FTS.StrongEps.EpsE4Thr.dz_four_RegQo
import Submission.Work.FTS.OpenPkg.Basic
import Submission.Work.FTS.H2.STBounds

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
