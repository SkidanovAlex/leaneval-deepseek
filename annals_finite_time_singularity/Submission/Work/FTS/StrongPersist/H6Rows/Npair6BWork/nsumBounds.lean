import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.IntervalCases
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.NsumAux.gPertDz
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.NsumAux.gPertMul
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.NsumAux.gPertSup
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.NsumG.nsumG1
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.NsumG.nsumG2
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.NsumG.nsumG5H
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.NsumG.nsumGK
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.nsumData
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.rowCoefSup
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS_EllLimOK.ThetaJets.Theta_jets_le
import Submission.Work.FTS_MuLamOK.Rows.Rl1Defs
import Submission.Work.PhiStar.Honesty.sqrt_weight_mul_eq_of_mem_Ioo

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

/-- **The per-slot bound for the level-six `N`-row sum.**

This is the composition of the twenty per-piece bounds (`NsumG.nsumG1`, `nsumG2`,
`nsumGK`, `nsumG5E`, `nsumG5H` and the six `NsumAux.gPert*` piece bounds, i.e. the pieces `nsP0 … nsP19` of `Npair6SupAux/NDefs.lean` grouped by the
row they instantiate): the pairing of the twenty-term sum is split into the sum of the pairings
(`NsumAux.abs_slotPairing_sum_le`, whose input is the `C⁶`/`ℋ⁶`-data of the twenty pieces read
off `H6Row6.NS6.pieces`), the triangle inequality is applied, and the constants are absorbed
into the powers of `α`, `(1+|Ce|+|Cs|)`, `(1+M)`.

The `α`-budget closes because the rows are stated with the *sharp* perturbation prices
(`coefData_pertSharp`: `K0 = K α^{-1/2}|Ce|M`) and the rows' products `(1+K0+K4+K6)(1+HkNorm)`
never produce a `(1+HkSq)²`; the worst power is `α^{-4}·α^{-1/2} = α^{-4.5} ≤ α^{-10}`. -/
theorem nsumBounds (Ce : ℝ) : ∃ C : ℝ, 0 < C ∧
    ∀ α ∈ Set.Ioc 0 1, ∀ (g Φ : Work.FTS.Galerkin.Fam) (τ M Cs : ℝ)
      (E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn) (Φs : Work.FTS.Galerkin.Fn)
      (a b : ℕ) (ρ : ℝ → ℝ → ℝ),
      0 ≤ τ →
      Work.FTS.StrongPersist.L6Ctx (Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1)
        α M Ce Cs E Φs g Φ τ →
      a + b ≤ 6 → Work.FTS.TransportS.IsLeafW α a ρ →
      |Work.FTS.TransportS.slotPairing ρ a b
          (Work.FTS.StrongPersist.H6Rows.Npair6SupAux.nsum α
            (Work.FTS.Galerkin.slice g τ) (E (Work.FTS.Galerkin.slice g τ)) Φs)
          (Work.FTS.Galerkin.slice g τ)|
        ≤ C * α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4 * (1 + M) ^ 4
            * (1 + Work.Spaces.HkSq α 6 (Work.FTS.Galerkin.slice g τ)) := by
  -- ## the five groups of per-piece bounds
  obtain ⟨C1, hC1pos, hG1⟩ := NsumG.nsumG1 Ce
  obtain ⟨C2, hC2pos, hG2⟩ := NsumG.nsumG2 Ce
  obtain ⟨C4, hC4pos, hGK⟩ := NsumG.nsumGK Ce
  obtain ⟨C5, hC5pos, hG5E⟩ := NsumG.nsumG5E Ce
  obtain ⟨C6, hC6pos, hG5H⟩ := NsumG.nsumG5H Ce
  -- the six perturbed-residual pieces (guard-compliant replacement of `NsumG.nsumG3`)
  obtain ⟨C7, hC7pos, hnsP2⟩ := NsumAux.nsP2Bound Ce
  obtain ⟨C8, hC8pos, hnsP3⟩ := NsumAux.nsP3Bound Ce
  obtain ⟨C9, hC9pos, hnsP6⟩ := NsumAux.nsP6Bound Ce
  obtain ⟨C10, hC10pos, hnsP7⟩ := NsumAux.nsP7Bound Ce
  obtain ⟨C11, hC11pos, hnsP10⟩ := NsumAux.nsP10Bound Ce
  obtain ⟨C12, hC12pos, hnsP11⟩ := NsumAux.nsP11Bound Ce
  have hC1 : (0 : ℝ) ≤ C1 := hC1pos.le
  have hC2 : (0 : ℝ) ≤ C2 := hC2pos.le
  have hC4 : (0 : ℝ) ≤ C4 := hC4pos.le
  have hC5 : (0 : ℝ) ≤ C5 := hC5pos.le
  have hC6 : (0 : ℝ) ≤ C6 := hC6pos.le
  set CC : ℝ := C1 + C2 + C4 + C5 + C6 + C7 + C8 + C9 + C10 + C11 + C12 with hCC
  have hCC0 : (0 : ℝ) ≤ CC := by rw [hCC]; linarith
  have hle1 : C1 ≤ CC := by rw [hCC]; linarith
  have hle2 : C2 ≤ CC := by rw [hCC]; linarith
  have hle4 : C4 ≤ CC := by rw [hCC]; linarith
  have hle5 : C5 ≤ CC := by rw [hCC]; linarith
  have hle6 : C6 ≤ CC := by rw [hCC]; linarith
  have hle7 : C7 ≤ CC := by rw [hCC]; linarith
  have hle8 : C8 ≤ CC := by rw [hCC]; linarith
  have hle9 : C9 ≤ CC := by rw [hCC]; linarith
  have hle10 : C10 ≤ CC := by rw [hCC]; linarith
  have hle11 : C11 ≤ CC := by rw [hCC]; linarith
  have hle12 : C12 ≤ CC := by rw [hCC]; linarith
  refine ⟨20 * CC + 1, by positivity, ?_⟩
  intro α hαIoc g Φ τ M Cs E Φs a b ρ hτ hctx hab hleaf
  have hα0 : 0 < α := hαIoc.1
  have hα1 : α ≤ 1 := hαIoc.2
  set f : Fn := slice g τ with hf
  set Ef : Fn := E (slice g τ) with hEfdef
  -- ## the shape factor
  set S : ℝ := α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4 * (1 + M) ^ 4
      * (1 + Work.Spaces.HkSq α 6 f) with hSdef
  have hS0 : (0 : ℝ) ≤ S := by
    rw [hSdef]
    exact mul_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg hα0.le _) (by positivity))
      (by positivity)) (by linarith [Work.Spaces.HkSq_nonneg α 6 f])
  -- ## the group bounds for this datum
  have hbG1 := hG1 α hαIoc g Φ τ M Cs E Φs hτ hctx a b ρ hab hleaf
  obtain ⟨hG1a, hG1b, hG1c⟩ := hbG1
  have hbG2 := hG2 α hαIoc g Φ τ M Cs E Φs hτ hctx a b ρ hab hleaf
  obtain ⟨hG2a, hG2b, hG2c⟩ := hbG2
  have hnsP2b := hnsP2 α hαIoc g Φ τ M Cs E Φs a b ρ hτ hctx hab hleaf
  have hnsP3b := hnsP3 α hαIoc g Φ τ M Cs E Φs a b ρ hτ hctx hab hleaf
  have hnsP6b := hnsP6 α hαIoc g Φ τ M Cs E Φs a b ρ hτ hctx hab hleaf
  have hnsP7b := hnsP7 α hαIoc g Φ τ M Cs E Φs a b ρ hτ hctx hab hleaf
  have hnsP10b := hnsP10 α hαIoc g Φ τ M Cs E Φs a b ρ hτ hctx hab hleaf
  have hnsP11b := hnsP11 α hαIoc g Φ τ M Cs E Φs a b ρ hτ hctx hab hleaf
  have hbGK := hGK α hαIoc g Φ τ M Cs E Φs hτ hctx a b ρ hab hleaf
  obtain ⟨hGKa, hGKb, hGKc, hGKd⟩ := hbGK
  have hbG5 := hG5E α hαIoc g Φ τ M Cs E Φs hτ hctx a b ρ hab hleaf
  obtain ⟨hG5a, hG5b⟩ := hbG5
  have hbG5H := hG5H α hαIoc g Φ τ M Cs E Φs hτ hctx a b ρ hab hleaf
  obtain ⟨hG5Hc, hG5Hd⟩ := hbG5H
  -- ## the `C⁶`/`ℋ⁶` data of the twenty pieces
  have hreg : Work.FTS.StrongPersist.H6Adm α f := hctx.hreg
  have hell : Work.FTS.StrongPersist.Ell6Ctx α Ce Cs E Φs f (slice Φ τ) := hctx.hell
  have hstar6 : Work.FTS.StrongPersist.StarPkg6 α Cs Φs := hctx.hstar6
  have hkfm : Work.Spaces.HkMem α 6 (fun z (_ : ℝ) => Work.Construction.FK f z) :=
    fk_hkMem α hαIoc f hreg.reg.1 hreg.reg.2
  have hmulSm : ∀ (u v : Fn), Work.FTS.EllipticEst.SmoothOpen u → Work.Spaces.HkMem α 6 u →
      Work.FTS.EllipticEst.SmoothOpen v → Work.Spaces.HkMem α 6 v →
      Work.Spaces.HkMem α 6 (fun z θ => u z θ * v z θ) :=
    fun u v hus hum hvs hvm => hkMem_mul_of6 hα0 hα1 ⟨hus, hum⟩ ⟨hvs, hvm⟩
  have D : Work.FTS.StrongPersist.H6Row6.NS6.Data α Ce Cs f Ef Φs :=
    { hα := hα0
      hα1 := hα1
      fsm := hreg.reg.1
      fm := hreg.reg.2
      f7 := hctx.h7
      Efsm := hell.hell.smooth
      Φssm := hell.hstar.smooth
      l12 := hreg.l12
      star := hstar6
      ell := hell.hell
      kfm := hkfm
      hadm := hreg
      mulSm := hmulSm }
  have hpcs := Work.FTS.StrongPersist.H6Row6.NS6.pieces D
  -- ## the twenty per-piece bounds, all with the constant `CC` and the shape `S`
  have hmul : ∀ {Ci : ℝ}, Ci ≤ CC →
      ∀ {P : ℝ}, |P| ≤ Ci * α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4 * (1 + M) ^ 4
          * (1 + Work.Spaces.HkSq α 6 (slice g τ)) → |P| ≤ CC * S := by
    intro Ci hCi P hP
    have hshape : Ci * α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4 * (1 + M) ^ 4
        * (1 + Work.Spaces.HkSq α 6 (slice g τ)) = Ci * S := by
      rw [hSdef]
      ring
    calc |P| ≤ Ci * α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4 * (1 + M) ^ 4
          * (1 + Work.Spaces.HkSq α 6 (slice g τ)) := hP
      _ = Ci * S := hshape
      _ ≤ CC * S := mul_le_mul_of_nonneg_right hCi hS0
  have hpiece : ∀ k ≤ 19,
      |Work.FTS.TransportS.slotPairing ρ a b
        (Work.FTS.StrongPersist.H6Row6.pcs α f Ef Φs k) f| ≤ CC * S := by
    intro k hk
    interval_cases k
    · exact hmul hle1 hG1a
    · exact hmul hle2 hG2a
    · exact hmul hle7 hnsP2b
    · exact hmul hle8 hnsP3b
    · exact hmul hle1 hG1b
    · exact hmul hle2 hG2b
    · exact hmul hle9 hnsP6b
    · exact hmul hle10 hnsP7b
    · exact hmul hle1 hG1c
    · exact hmul hle2 hG2c
    · exact hmul hle11 hnsP10b
    · exact hmul hle12 hnsP11b
    · exact hmul hle4 hGKa
    · exact hmul hle4 hGKb
    · exact hmul hle5 hG5a
    · exact hmul hle6 hG5Hc
    · exact hmul hle4 hGKc
    · exact hmul hle4 hGKd
    · exact hmul hle5 hG5b
    · exact hmul hle6 hG5Hd
  -- ## the assembly
  have hcd : ∀ k ≤ 19, NsumAux.Smooth6 (Work.FTS.StrongPersist.H6Row6.pcs α f Ef Φs k) :=
    fun k hk => (hpcs k (by omega)).1
  have hm : ∀ k ≤ 19, Work.Spaces.HkMem α 6
      (Work.FTS.StrongPersist.H6Row6.pcs α f Ef Φs k) :=
    fun k hk => (hpcs k (by omega)).2
  have hmain := NsumAux.abs_slotPairing_sum_le (α := α) hα0 hab hleaf
    (hf6 := hreg.reg.1.forall 6) (hfm := hreg.reg.2) hcd hm hCC0 hS0 hpiece
  have hsum : Work.FTS.StrongPersist.H6Rows.Npair6SupAux.nsum α f Ef Φs
      = ∑ k ∈ Finset.range 20, Work.FTS.StrongPersist.H6Row6.pcs α f Ef Φs k :=
    Work.FTS.StrongPersist.H6Row6.pcs_sum α f Ef Φs
  rw [hsum]
  refine hmain.trans ?_
  exact le_of_eq (by rw [hSdef]; ring)

end Work.FTS.StrongPersist.H6Rows.Npair6BWork
