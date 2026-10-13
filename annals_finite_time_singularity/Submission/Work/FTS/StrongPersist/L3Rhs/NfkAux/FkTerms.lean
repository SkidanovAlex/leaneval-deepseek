/-
# `Submission/Work/FTS/StrongPersist/L3Rhs/NfkAux/FkTerms.lean`

The two terms of the `NFkSum` block in which the angular moment `FK f` multiplies a function of
`f`:

* `N₄^{gg} = -(1/2)·FK f·D_θ f`  (`N4gg_mem`),
* `N₅^{gg} = -sin²θ·FK f·f`      (`N5gg_mem`),

both honest in `ℋ³` with a bound of the shape `C α^{-Cpow} (1 + |FK f|²_{ℋ⁴}) |f|²_{ℋ⁴}`.

## Route

The `z`-jets of `FK f` are bounded pointwise by its own `ℋ⁴`-norm (`NfkAux.FK_jets`, via the
radial Agmon inequality `NfkAux.RadSupZ` and the slot bound `NfkAux.FK_slot_le`); the product with
the general factor `D_θ f` resp. `sin²θ·f` is the radial-multiplier estimate `NfkAux.ProdRadSupO`
at `k = 3`.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongPersist.L3Rhs.Defs
import Submission.Work.FTS.StrongPersist.L3Rhs.Assembly
import Submission.Work.FTS.StrongPersist.L3Rhs.NfkAux.Basic
import Submission.Work.FTS.StrongPersist.L3Rhs.NfkAux.FkSlots
import Submission.Work.FTS.StrongPersist.L3Rhs.NfkAux.FkJets
import Submission.Work.FTS.StrongPersist.L3Rhs.NfkAux.ProdRadSup
import Submission.Work.FTS.StrongPersist.L3Rhs.NfkAux.ProdRadSupO
import Submission.Work.FTS.StrongPersist.L3Rhs.NfkAux.RadSupZ
import Submission.Work.FTS.FinalClock.HkIntegrandMulDthSmooth
import Submission.Work.FTS.CoercivityFix.Transfer.E2_blocks
import Submission.Work.FTS.LocData.hLoc_hk
import Submission.Work.H2.T1Q.PwBdQ
import Submission.Work.Spaces.HkSq_terms

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.L3Rhs.NfkAux

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-- The `θ`-independent function `z ↦ FK f z` is `C³` on the open quadrant. -/
theorem FK_contDiffOn_Q0 {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 6 f) :
    ContDiffOn ℝ 3 (Function.uncurry (fun z (_ : ℝ) => Work.Construction.FK f z))
      Work.FTS.EllipticEst.Q0 := by
  have h := contDiffOn_FK hα hα1 hsm hmem 3 (by norm_num)
  have hfst : ContDiffOn ℝ 3 (fun p : ℝ × ℝ => p.1) Work.FTS.EllipticEst.Q0 := contDiffOn_fst
  have hcomp := h.comp hfst (fun p hp => (Work.FTS.EllipticEst.mem_Q0.mp hp).1)
  have hfun : (fun p : ℝ × ℝ => Work.Construction.FK f p.1)
      = Function.uncurry (fun z (_ : ℝ) => Work.Construction.FK f z) := rfl
  rw [← hfun]
  exact hcomp

/-! ## `N₄^{gg} = -(1/2)·FK f·D_θ f` -/

/-- **The `N₄^{gg}`-term is honest in `ℋ³` with the announced bound.** -/
theorem N4gg_mem : ∃ C Cpow : ℝ, 0 < C ∧ 0 ≤ Cpow ∧
    ∀ (α : ℝ), α ∈ Set.Ioc 0 1 → ∀ (f : ℝ → ℝ → ℝ),
      Work.FTS.StrongPersist.H6Adm α f →
      Work.Spaces.HkMem α 3 (Work.FTS.Nonlin.N4gg α f) ∧
      Work.Spaces.HkSq α 3 (Work.FTS.Nonlin.N4gg α f)
        ≤ C * α ^ (-Cpow)
          * (1 + Work.Spaces.HkSq α 4 (fun z (_ : ℝ) => Work.Construction.FK f z))
          * Work.Spaces.HkSq α 4 f := by
  obtain ⟨Cprod, Cpow, hCprodpos, hCpownn, hprod⟩ := ProdRadSupO 3
  obtain ⟨Cj, hCjpos, hj⟩ := FK_jets
  refine ⟨Cprod * (1 + Cj), Cpow, mul_pos hCprodpos (by linarith), hCpownn, ?_⟩
  intro α hαIoc f hf
  obtain ⟨hα, hα1⟩ := Set.mem_Ioc.mp hαIoc
  have hsm : Work.FTS.EllipticEst.SmoothOpen f := hf.reg.1
  have hmem6 : Work.Spaces.HkMem α 6 f := hf.reg.2
  have hmem4 : Work.Spaces.HkMem α 4 f :=
    Work.FTS.OpenPkg.HkMem_mono_open (k := 6) hsm 4 (by norm_num) hmem6
  -- the angular moment is honest in `ℋ⁴`
  obtain ⟨Cfk, hCfkpos, hfk⟩ := Work.FTS.OpenPkg.fkH_field
  obtain ⟨hFKmem, -⟩ := hfk α hα hα1 f ⟨hsm, hmem4⟩ hf.l12
  -- the jet bound for the multiplier `z ↦ -(1/2)·FK f z`
  have hjets : ∀ (a : ℕ), a ≤ 3 → ∀ z ∈ Set.Ioi (0 : ℝ),
      (Work.Elliptic.DzdIter a (fun z => (-(1 / 2)) * Work.Construction.FK f z) z) ^ 2
        ≤ (Cj / 4) * Work.Spaces.HkSq α 4 (fun z (_ : ℝ) => Work.Construction.FK f z) := by
    intro a ha z hz
    rw [DzdIter_const_mul_apply a (-(1 / 2)) (fun z => Work.Construction.FK f z) z]
    have h := hj α hαIoc f hsm hmem6 hFKmem a ha z hz
    have hnn : (0 : ℝ) ≤ Work.Spaces.HkSq α 4
        (fun z (_ : ℝ) => Work.Construction.FK f z) := Work.Spaces.HkSq_nonneg α 4 _
    nlinarith [h, hnn, hCjpos, sq_nonneg (Work.Elliptic.DzdIter a
      (fun z => Work.Construction.FK f z) z)]
  have hr_smooth : ∀ (a : ℕ), a ≤ 3 →
      ContDiffOn ℝ a (fun z => (-(1 / 2)) * Work.Construction.FK f z) (Set.Ioi (0 : ℝ)) := by
    intro a ha
    have h : ContDiffOn ℝ a (fun z => Work.Construction.FK f z) (Set.Ioi (0 : ℝ)) :=
      contDiffOn_FK hα hα1 hsm hmem6 a (by omega)
    have h2 := h.const_smul (-(1 / 2) : ℝ)
    simpa only [Pi.smul_apply, smul_eq_mul] using h2
  have hslice : ∀ (i : ℕ), i ≤ 3 → ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      ContDiffOn ℝ i (fun z => Work.Spaces.Dth f z θ) (Set.Ioi (0 : ℝ)) := by
    intro i hi θ hθ
    exact Work.FTS.FinalClock.contDiffOn_zslice (hsm.Dth.forall i) hθ
  have hslice' : ∀ (j i : ℕ), 1 ≤ i → i + j ≤ 3 → ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      ContDiffOn ℝ j (fun z => Work.Spaces.DthIter i (Work.Spaces.Dth f) z θ)
        (Set.Ioi (0 : ℝ)) := by
    intro j i hi hij θ hθ
    rw [DthIter_Dth i f]
    exact Work.FTS.FinalClock.contDiffOn_zslice ((hsm.DthIter (i + 1)).forall j) hθ
  have hmemD : Work.Spaces.HkMem α 3 (Work.Spaces.Dth f) := hkMem_dth_three hα hsm hmem4
  obtain ⟨hmemProd, hbndProd⟩ := hprod α (fun z => (-(1 / 2)) * Work.Construction.FK f z)
    (Work.Spaces.Dth f) ((Cj / 4) * Work.Spaces.HkSq α 4
      (fun z (_ : ℝ) => Work.Construction.FK f z))
    hα (mul_nonneg (div_nonneg hCjpos.le (by norm_num)) (Work.Spaces.HkSq_nonneg α 4 _))
      (by norm_num) hjets hr_smooth hslice hslice' (hsm.Dth.forall 3) hmemD
  have heq : Work.FTS.Nonlin.N4gg α f
      = fun z θ => (fun z => (-(1 / 2)) * Work.Construction.FK f z) z
          * Work.Spaces.Dth f z θ := by
    funext z θ
    simp only [Work.FTS.Nonlin.N4gg] <;> ring
  rw [heq]
  refine ⟨hmemProd, ?_⟩
  have hMKnn : (0 : ℝ) ≤ Work.Spaces.HkSq α 4
      (fun z (_ : ℝ) => Work.Construction.FK f z) := Work.Spaces.HkSq_nonneg α 4 _
  have hDth : Work.Spaces.HkSq α 3 (Work.Spaces.Dth f) ≤ Work.Spaces.HkSq α 4 f :=
    Work.FTS.CoercivityStep.Norm.HkSq_Dth_le α hα 3 hmem4
  have h1 : (1 + (Cj / 4) * Work.Spaces.HkSq α 4 (fun z (_ : ℝ) => Work.Construction.FK f z))
      ≤ (1 + Cj)
        * (1 + Work.Spaces.HkSq α 4 (fun z (_ : ℝ) => Work.Construction.FK f z)) := by
    nlinarith [hMKnn, hCjpos]
  calc Work.Spaces.HkSq α 3
        (fun z θ => (fun z => (-(1 / 2)) * Work.Construction.FK f z) z
          * Work.Spaces.Dth f z θ)
      ≤ Cprod * α ^ (-Cpow)
          * (1 + (Cj / 4) * Work.Spaces.HkSq α 4 (fun z (_ : ℝ) => Work.Construction.FK f z))
          * Work.Spaces.HkSq α 3 (Work.Spaces.Dth f) := hbndProd
    _ ≤ Cprod * α ^ (-Cpow) * ((1 + Cj)
          * (1 + Work.Spaces.HkSq α 4 (fun z (_ : ℝ) => Work.Construction.FK f z)))
          * Work.Spaces.HkSq α 4 f := by
        have hCpow : (0 : ℝ) ≤ α ^ (-Cpow) := Real.rpow_nonneg hα.le _
        have hCL : (0 : ℝ) ≤ Cprod * α ^ (-Cpow) := mul_nonneg hCprodpos.le hCpow
        have hCD : (0 : ℝ) ≤ Cprod * α ^ (-Cpow) * ((1 + Cj)
            * (1 + Work.Spaces.HkSq α 4 (fun z (_ : ℝ) => Work.Construction.FK f z))) :=
          mul_nonneg hCL (mul_nonneg (by linarith) (by linarith [hMKnn]))
        exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hCL)
            (Work.Spaces.HkSq_nonneg α 3 _)).trans
          (mul_le_mul_of_nonneg_left hDth hCD)
    _ = Cprod * (1 + Cj) * α ^ (-Cpow)
          * (1 + Work.Spaces.HkSq α 4 (fun z (_ : ℝ) => Work.Construction.FK f z))
          * Work.Spaces.HkSq α 4 f := by ring

/-! ## `N₅^{gg} = -sin²θ·FK f·f` -/

/-- **The `N₅^{gg}`-term is honest in `ℋ³` with the announced bound.** -/
theorem N5gg_mem : ∃ C Cpow : ℝ, 0 < C ∧ 0 ≤ Cpow ∧
    ∀ (α : ℝ), α ∈ Set.Ioc 0 1 → ∀ (f : ℝ → ℝ → ℝ),
      Work.FTS.StrongPersist.H6Adm α f →
      Work.Spaces.HkMem α 3 (Work.FTS.Nonlin.N5gg f) ∧
      Work.Spaces.HkSq α 3 (Work.FTS.Nonlin.N5gg f)
        ≤ C * α ^ (-Cpow)
          * (1 + Work.Spaces.HkSq α 4 (fun z (_ : ℝ) => Work.Construction.FK f z))
          * Work.Spaces.HkSq α 4 f := by
  obtain ⟨Cprod, Cpow, hCprodpos, hCpownn, hprod⟩ := ProdRadSupO 3
  obtain ⟨Cj, hCjpos, hj⟩ := FK_jets
  obtain ⟨Cang, hCangpos, hCang⟩ := Work.Blocks.HkMul_ang_le 3
  refine ⟨Cprod * (1 + Cj) * Cang, Cpow, mul_pos (mul_pos hCprodpos (by linarith)) hCangpos, hCpownn, ?_⟩
  intro α hαIoc f hf
  obtain ⟨hα, hα1⟩ := Set.mem_Ioc.mp hαIoc
  have hsm : Work.FTS.EllipticEst.SmoothOpen f := hf.reg.1
  have hmem6 : Work.Spaces.HkMem α 6 f := hf.reg.2
  have hmem4 : Work.Spaces.HkMem α 4 f :=
    Work.FTS.OpenPkg.HkMem_mono_open (k := 6) hsm 4 (by norm_num) hmem6
  have hmem3 : Work.Spaces.HkMem α 3 f :=
    Work.FTS.OpenPkg.HkMem_mono_open (k := 6) hsm 3 (by norm_num) hmem6
  obtain ⟨Cfk, hCfkpos, hfk⟩ := Work.FTS.OpenPkg.fkH_field
  obtain ⟨hFKmem, -⟩ := hfk α hα hα1 f ⟨hsm, hmem4⟩ hf.l12
  have hjets : ∀ (a : ℕ), a ≤ 3 → ∀ z ∈ Set.Ioi (0 : ℝ),
      (Work.Elliptic.DzdIter a (fun z => (-1) * Work.Construction.FK f z) z) ^ 2
        ≤ (Cj / 1) * Work.Spaces.HkSq α 4 (fun z (_ : ℝ) => Work.Construction.FK f z) := by
    intro a ha z hz
    rw [DzdIter_const_mul_apply a (-1) (fun z => Work.Construction.FK f z) z]
    have h := hj α hαIoc f hsm hmem6 hFKmem a ha z hz
    have hnn : (0 : ℝ) ≤ Work.Spaces.HkSq α 4
        (fun z (_ : ℝ) => Work.Construction.FK f z) := Work.Spaces.HkSq_nonneg α 4 _
    nlinarith [h, hnn, hCjpos, sq_nonneg (Work.Elliptic.DzdIter a
      (fun z => Work.Construction.FK f z) z)]
  have hr_smooth : ∀ (a : ℕ), a ≤ 3 →
      ContDiffOn ℝ a (fun z => (-1) * Work.Construction.FK f z) (Set.Ioi (0 : ℝ)) := by
    intro a ha
    have h : ContDiffOn ℝ a (fun z => Work.Construction.FK f z) (Set.Ioi (0 : ℝ)) :=
      contDiffOn_FK hα hα1 hsm hmem6 a (by omega)
    have h2 := h.const_smul (-1 : ℝ)
    simpa only [Pi.smul_apply, smul_eq_mul] using h2
  have hg_sm : Work.FTS.EllipticEst.SmoothOpen (fun z θ => Real.sin θ ^ 2 * f z θ) :=
    smoothOpen_sin_sq_mul hsm
  have hslice : ∀ (i : ℕ), i ≤ 3 → ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      ContDiffOn ℝ i (fun z => Real.sin θ ^ 2 * f z θ) (Set.Ioi (0 : ℝ)) := by
    intro i hi θ hθ
    exact Work.FTS.FinalClock.contDiffOn_zslice (hg_sm.forall i) hθ
  have hslice' : ∀ (j i : ℕ), 1 ≤ i → i + j ≤ 3 → ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      ContDiffOn ℝ j (fun z => Work.Spaces.DthIter i (fun z θ => Real.sin θ ^ 2 * f z θ) z θ)
        (Set.Ioi (0 : ℝ)) := by
    intro j i hi hij θ hθ
    exact Work.FTS.FinalClock.contDiffOn_zslice ((hg_sm.DthIter i).forall j) hθ
  have htri := hCang α f hα hα1 hsm
  have hmem_g : Work.Spaces.HkMem α 3 (fun z θ => Real.sin θ ^ 2 * f z θ) :=
    (htri.2.2 hmem3).2.2.1
  obtain ⟨hmemProd, hbndProd⟩ := hprod α (fun z => (-1) * Work.Construction.FK f z)
    (fun z θ => Real.sin θ ^ 2 * f z θ) (Cj / 1 * Work.Spaces.HkSq α 4
      (fun z (_ : ℝ) => Work.Construction.FK f z))
    hα (mul_nonneg (by linarith : (0:ℝ) ≤ Cj / 1) (Work.Spaces.HkSq_nonneg α 4 _))
      (by norm_num) hjets hr_smooth hslice hslice' (hg_sm.forall 3) hmem_g
  have heq : Work.FTS.Nonlin.N5gg f
      = fun z θ => (fun z => (-1) * Work.Construction.FK f z) z
          * (Real.sin θ ^ 2 * f z θ) := by
    funext z θ
    simp only [Work.FTS.Nonlin.N5gg] <;> ring
  rw [heq]
  refine ⟨hmemProd, ?_⟩
  have hMKnn : (0 : ℝ) ≤ Work.Spaces.HkSq α 4
      (fun z (_ : ℝ) => Work.Construction.FK f z) := Work.Spaces.HkSq_nonneg α 4 _
  have hsq_g : Work.Spaces.HkSq α 3 (fun z θ => Real.sin θ ^ 2 * f z θ)
      ≤ Cang * Work.Spaces.HkSq α 3 f := (htri.2.2 hmem3).2.2.2
  have hmono : Work.Spaces.HkSq α 3 f ≤ Work.Spaces.HkSq α 4 f :=
    Work.FTS.CoercivityStep.Norm.HkSq_mono_le α (by norm_num) hmem4
  have h1 : (1 + (Cj / 1) * Work.Spaces.HkSq α 4 (fun z (_ : ℝ) => Work.Construction.FK f z))
      ≤ (1 + Cj)
        * (1 + Work.Spaces.HkSq α 4 (fun z (_ : ℝ) => Work.Construction.FK f z)) := by
    nlinarith [hMKnn, hCjpos]
  have hCpow : (0 : ℝ) ≤ α ^ (-Cpow) := Real.rpow_nonneg hα.le _
  refine hbndProd.trans ?_
  calc Cprod * α ^ (-Cpow)
        * (1 + (Cj / 1) * Work.Spaces.HkSq α 4 (fun z (_ : ℝ) => Work.Construction.FK f z))
        * Work.Spaces.HkSq α 3 (fun z θ => Real.sin θ ^ 2 * f z θ)
      ≤ Cprod * α ^ (-Cpow) * ((1 + Cj)
          * (1 + Work.Spaces.HkSq α 4 (fun z (_ : ℝ) => Work.Construction.FK f z)))
          * (Cang * Work.Spaces.HkSq α 4 f) := by
        have hCD2 : (0 : ℝ) ≤ Cprod * α ^ (-Cpow) * ((1 + Cj)
            * (1 + Work.Spaces.HkSq α 4 (fun z (_ : ℝ) => Work.Construction.FK f z))) :=
          mul_nonneg (mul_nonneg hCprodpos.le hCpow)
            (mul_nonneg (by linarith) (by linarith [hMKnn]))
        refine mul_le_mul ?_ ?_ (Work.Spaces.HkSq_nonneg α 3 _) ?_
        · exact mul_le_mul_of_nonneg_left h1 (mul_nonneg hCprodpos.le hCpow)
        · exact hsq_g.trans (mul_le_mul_of_nonneg_left hmono hCangpos.le)
        · exact hCD2
    _ = Cprod * (1 + Cj) * Cang * α ^ (-Cpow)
          * (1 + Work.Spaces.HkSq α 4 (fun z (_ : ℝ) => Work.Construction.FK f z))
          * Work.Spaces.HkSq α 4 f := by ring

end Work.FTS.StrongPersist.L3Rhs.NfkAux
