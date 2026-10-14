import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Filter.Defs
import Submission.Work.FTS.StrongEps.EpsE4Thr.step2_data_ge_O
import Submission.Work.FTS.StrongEps.L12Sub4.L12ZeroLog
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkDzdIterSqLe
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.hkMem_fk_mul
import Submission.Work.FTS_EllLimOK.Assembly
import Submission.Work.FTS_EllLimOK.Defs3
import Submission.Work.FTS_EllLimOK.Glue
import Submission.Work.FTS_EllLimOK.LimTower_identify3
import Submission.Work.FTS_EllLimOK.PkgRepair
import Submission.Work.FTS_EllLimOK.ZDecay_of_decay_bounds
import Submission.Work.FTS_EllLimOK.tower_jet_identities
import Submission.Work.FTS_EllLimOK.wt_bddAbove_of_compact
import Submission.Work.FTS_MuLamOK.Rows.Rl1Defs
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_theta
import Submission.Work.H2.WPQ.m_term_le_smoothQuad
import Submission.Work.H2W.asliceMomentEq
import Submission.Work.H6Pair6Aux.T6Fix.mixed_sinGain_of_pthFlat
import Submission.Work.R1G.DecayInZ_gA
import Submission.Work.Spaces.one_le_mul_w
import Submission.Work.Stability.mul_rpow_le
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.TransO.StepPairO =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.TransO

open Work.FTS.Galerkin (Fn)
open Work.FTS.StrongEps.EpsE4Thr (CoerAdmO CoerData2O CoerDataTO RegQo StepReg2O Comm2O
  hnormD_all_O)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

/-- **The joint induction, one step, on the open class.**  From the level-`n` clean data and the
level-`n` transfer data of the same `IP` with the *same* Cauchy–Schwarz constant `CC`, one obtains
the level-`(n+1)` versions, provided the smallness conditions of `step2_data_ge_O` and of
`stepT_O` hold. -/
theorem stepPair_O (α : ℝ) (n : ℕ) (hα : 0 < α) (hn : n ≤ 3) (hn1 : 1 ≤ n)
    {IP : Fn → Fn → ℝ} {cc CC ccT : ℝ}
    (hcl : CoerData2O α n IP cc CC)
    (ht : CoerDataTO α n IP ccT CC)
    (hc : Comm2O α n IP)
    (hcw : Work.FTS.CoercivityFix.Transfer.CommSm α n IP)
    (hcs1 : ∀ f : Fn, CoerAdmO α f →
      |IP (Work.FTS.CoercivityFix.Transfer.E1 α f) (Work.Spaces.Dth f)|
        ≤ CC * Work.Spaces.HkNorm α n (Work.FTS.CoercivityFix.Transfer.E1 α f)
            * Work.Spaces.HkNorm α n (Work.Spaces.Dth f))
    (hcs2 : ∀ f : Fn, CoerAdmO α f →
      |IP (Work.FTS.CoercivityFix.Transfer.E2 α f) (Work.Spaces.Dz f)|
        ≤ CC * Work.Spaces.HkNorm α n (Work.FTS.CoercivityFix.Transfer.E2 α f)
            * Work.Spaces.HkNorm α n (Work.Spaces.Dz f))
    (hreg : StepReg2O α n)
    {κE κ₁ κ₂ J : ℝ} (hκE : 0 ≤ κE) (hκ₁ : 0 ≤ κ₁) (hκ₂ : 0 ≤ κ₂)
    (hJ : 0 < J)
    (hÊ : ∀ f : Fn, RegQo α (n + 1) f →
      Work.Spaces.HkNorm α n (Work.FTS.CoercivityFix.E2hat f)
        ≤ κE * (Work.Spaces.HkNorm α n f + Work.Spaces.HkNorm α n (Work.Spaces.Dth f)))
    (hid1 : ∀ f : Fn, CoerAdmO α f → ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Work.Spaces.Dth (Work.Coercivity.LGammaT α f) z θ
        = Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dth f) z θ
          + Work.FTS.CoercivityFix.Transfer.E1 α f z θ)
    (hid2 : ∀ f : Fn, CoerAdmO α f → ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Work.Spaces.Dz (Work.Coercivity.LGammaT α f) z θ
        = Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dz f) z θ
          + Work.FTS.CoercivityFix.Transfer.E2 α f z θ)
    (hbk1 : ∀ f : Fn, CoerAdmO α f →
      Work.FTS.CoercivityFix.Transfer.AddOKSm α n
        (Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dth f))
        (Work.FTS.CoercivityFix.Transfer.E1 α f) (Work.Spaces.Dth f))
    (hbk2 : ∀ f : Fn, CoerAdmO α f →
      Work.FTS.CoercivityFix.Transfer.AddOKSm α n
        (Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dz f))
        (Work.FTS.CoercivityFix.Transfer.E2 α f) (Work.Spaces.Dz f))
    (hnA : ∀ f : Fn, CoerAdmO α f →
      Work.Spaces.HkNorm α n (Work.FTS.CoercivityFix.Transfer.E1 α f)
        ≤ α * κ₁ * (Work.Spaces.HkNorm α n f + Work.Spaces.HkNorm α n (Work.Spaces.Dth f)))
    (hnB : ∀ f : Fn, CoerAdmO α f →
      Work.Spaces.HkNorm α n (Work.FTS.CoercivityFix.Transfer.E2 α f)
        ≤ κ₂ * (Work.Spaces.HkNorm α n f + Work.Spaces.HkNorm α n (Work.Spaces.Dth f)))
    (hsmall : Work.FTS.CoercivityFix.StepSmall cc CC κE 1 J)
    (hs3 : J * (16 * (CC * κ₂) ^ 2) ≤ ccT * cc)
    (hs4 : J * (16 * (CC * κ₂) ^ 2) ≤ 1 * cc ^ 2)
    (hs1 : 1 * (16 * (CC * α * κ₁) ^ 2) ≤ ccT * cc)
    (hs2 : CC * α * κ₁ ≤ cc / 8) :
    0 < cc * min 1 (min 1 J) / (2 * 1) ∧
      0 < min (3 * ccT / 4) (min (5 * 1 * cc / 8) (3 * J * cc / 4)) / 1 ∧
      CoerData2O α (n + 1)
        (Work.Coercivity.HkIPStep 1 J IP) (cc * min 1 (min 1 J) / (2 * 1))
        (3 * max 1 (max 1 J) * CC) ∧
      CoerDataTO α (n + 1) (Work.Coercivity.HkIPStep 1 J IP)
        (min (3 * ccT / 4) (min (5 * 1 * cc / 8) (3 * J * cc / 4)) / 1)
        (3 * max 1 (max 1 J) * CC) := by
  have hD : (0 : ℝ) < 1 := one_pos
  have hnormD : ∀ f : Fn, RegQo α (n + 1) f →
      Work.Spaces.HkSq α (n + 1) f
        ≤ 1 * (Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f)
            + Work.Spaces.HkSq α n (Work.Spaces.Dz f)) :=
    hnormD_all_O α hα hn1
  have hnormDT : ∀ f : Fn, CoerAdmO α f →
      Work.Spaces.HkSq α (n + 1) f
        ≤ 1 * (Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f)
            + Work.Spaces.HkSq α n (Work.Spaces.Dz f)) :=
    fun f hf => hnormD f (regQo_mono (k := n + 1) (l := 5) (by omega) hf.1)
  have hclean := Work.FTS.StrongEps.EpsE4Thr.step2_data_ge_O α n hα hcl hκE one_pos hJ hD
    hsmall hreg hc hÊ hnormD
  have htrans := stepT_O α n hα hn (ht := ht) (hcl := hcl) (hc := hcw) (hreg := hreg)
    (hid1 := hid1) (hid2 := hid2) (hbk1 := hbk1) (hbk2 := hbk2)
    (hcs1 := hcs1) (hcs2 := hcs2)
    (hn1 := hnA) (hn2 := hnB)
    (hκ₁ := hκ₁) (hκ₂ := hκ₂) (hc₁ := one_pos) (hc₂ := hJ) (hD := hD)
    (hs1 := hs1) (hs2 := hs2) (hs3 := hs3) (hs4 := hs4) (hnormD := hnormDT)
  refine ⟨hclean.hcc, htrans.hcc, ?_, ?_⟩
  · simpa only [one_mul] using hclean
  · simpa only [one_mul] using htrans

end Work.FTS.StrongEps.EpsE4Thr.TransO
end
end
-- ===== merged: Submission.Work.FTS_EllLimOK.ClosedCompact3_of_bounds_fatou =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-! ## The `ℋ⁰`-Fatou step, in the shape used below -/


/-! ## The main theorem -/


end Work.FTS_EllLimOK
end
end
-- ===== merged: Submission.Work.FTS_EllLimOK.exists_ellLimOK3_of_closed =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open Filter Set

namespace Work.FTS_EllLimOK

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-! ## `JConv3` is closed under the vector space operations -/

/-- `JConv3` is additive (the two limits are `C³` on the open quadrant, so the Leibniz-free
additivity of the mixed blocks is available). -/
theorem jconv3_add {Ψn Φn : ℕ → Fn} {Ψ Φ : Fn}
    (hΨ : JConv3 Ψn Ψ) (hΦ : JConv3 Φn Φ)
    (hΨn : ∀ n, ContDiffOn ℝ 3 (Function.uncurry (Ψn n)) Work.Construction.Qd)
    (hΦn : ∀ n, ContDiffOn ℝ 3 (Function.uncurry (Φn n)) Work.Construction.Qd)
    (hΨc : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd)
    (hΦc : ContDiffOn ℝ 3 (Function.uncurry Φ) Work.Construction.Qd) :
    JConv3 (fun n => Ψn n + Φn n) (Ψ + Φ) := by
  intro j i hji z θ hz
  have hseq : (fun n => Work.Spaces.mixed j i (Ψn n + Φn n) z θ)
      = fun n => Work.Spaces.mixed j i (Ψn n) z θ + Work.Spaces.mixed j i (Φn n) z θ := by
    funext n
    exact mixed_add_Qd (hΨn n) (hΦn n) hji hz
  rw [hseq, mixed_add_Qd hΨc hΦc hji hz]
  exact (hΨ j i hji z θ hz).add (hΦ j i hji z θ hz)

/-- `JConv3` is homogeneous. -/
theorem jconv3_smul (c : ℝ) {Ψn : ℕ → Fn} {Ψ : Fn} (hΨ : JConv3 Ψn Ψ) :
    JConv3 (fun n => c • Ψn n) (c • Ψ) := by
  intro j i hji z θ hz
  show Tendsto (fun n => Work.Spaces.mixed j i (c • Ψn n) z θ) atTop
    (𝓝 (Work.Spaces.mixed j i (c • Ψ) z θ))
  simp only [Work.FTS.EllipticEst.mixed_smul, Pi.smul_apply, smul_eq_mul]
  exact (hΨ j i hji z θ hz).const_mul c


/-! ## The order-`3` jet limit does not depend on the sequence -/


/-! ## The order-`3` graph submodule -/

/-- **The order-`3` graph**: pairs `(f, Ψ)` where `Ψ` is a `C³` solution for `f` and the
`C³`-jets of `E (fn n)` converge to those of `Ψ` along some (hence every) `LimSeq4` to `f`.
This is `Glue.graphG` with `2` replaced by `3`. -/
def graphG3 (α : ℝ) (E : Fn →ₗ[ℝ] Fn)
    (hsm : ∀ g, Work.FTS.ClassC.ClassC α g →
      ContDiffOn ℝ 3 (Function.uncurry (E g)) Work.Construction.Qd) :
    Submodule ℝ (Fn × Fn) where
  carrier := {p | (∃ fn : ℕ → Fn, LimSeq4 α fn p.1 ∧ JConv3 (fun n => E (fn n)) p.2) ∧
    Work.FTS.StrongGlobal.IsBslSolPos α p.1 p.2 ∧
    ContDiffOn ℝ 3 (Function.uncurry p.2) Work.Construction.Qd}
  zero_mem' := by
    refine ⟨⟨fun _ => 0, limSeq4_const (Work.FTS.ClassC.classC_zero α), ?_⟩,
      isBslSolPos_zero α, contDiffOn_const⟩
    intro j i _ z θ _
    simp only [map_zero]
    exact tendsto_const_nhds
  add_mem' := by
    rintro ⟨f, Ψ⟩ ⟨h, Φ⟩ ⟨⟨fn, hfn, hJf⟩, hlf, hsf⟩ ⟨⟨hn, hhn, hJh⟩, hlh, hsh⟩
    refine ⟨⟨fun n => fn n + hn n, limSeq4_add hfn hhn, ?_⟩,
      IsBslSolPos_add hlf hlh (hsf.of_le (by norm_num)) (hsh.of_le (by norm_num)), hsf.add hsh⟩
    have hmap : (fun n => E (fn n + hn n)) = fun n => E (fn n) + E (hn n) := by
      funext n
      rw [map_add]
    rw [hmap]
    exact jconv3_add hJf hJh (fun n => hsm _ (hfn.classC n)) (fun n => hsm _ (hhn.classC n))
      hsf hsh
  smul_mem' := by
    rintro c ⟨f, Ψ⟩ ⟨⟨fn, hfn, hJf⟩, hlf, hsf⟩
    refine ⟨⟨fun n => c • fn n, limSeq4_smul c hfn, ?_⟩, isBslSolPos_smul' hlf,
      hsf.const_smul c⟩
    have hmap : (fun n => E (c • fn n)) = fun n => c • E (fn n) := by
      funext n
      rw [map_smul]
    rw [hmap]
    exact jconv3_smul c hJf

/-! ## The main theorem -/


end Work.FTS_EllLimOK
end
end
