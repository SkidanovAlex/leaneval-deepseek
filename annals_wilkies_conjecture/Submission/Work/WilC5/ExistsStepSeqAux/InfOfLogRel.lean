import Mathlib
import Submission.Work.WilC5.Values
import Submission.Work.WilC5.ValuesLemmas
import Submission.Work.WilC5.ValArith
import Submission.Work.WilC5.Bridge
import Submission.Work.WilC5.ExpLog
import Submission.Work.WilC5.S4ExpF.Bridge
import Submission.Work.WilC5.logFun_expE
import Submission.Work.WilC5.expE_add_of_model
import Submission.Work.WilC5.expE_strictMono
import Submission.Work.WilC5.RealConst
import Submission.Work.WilC5.stdPart
import Submission.Work.WilC5.ReductEmb
import Submission.Work.WilC5.StepSeqUnbounded

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

namespace Work.WilC5.ExistsStepSeqAux

theorem InfOfLogRel
    {K : Type} [WilkiesDesign.CG.LEc.Structure K] [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] [FirstOrder.Ring.CompatibleRing K]
    [WilkiesDesign.CG.rexpL.Structure K] [(FirstOrder.Language.constantsOn ℝ).Structure K]
    [FirstOrder.Language.Theory.Model K WilkiesDesign.CG.TE]
    (hrexp : ∀ x : K, @FirstOrder.Language.Structure.funMap WilkiesDesign.CG.rexpL K _ 1
        WilkiesDesign.CG.rexpFunc.rexp ![x] = Work.WilC5.rexpFromExp x)
    (hadd : ∀ x y : K, Work.WilC5.addE x y = x + y)
    (hmul : ∀ x y : K, Work.WilC5.mulE x y = x * y)
    (hone : (Work.WilC5.oneE : K) = 1)
    (hleneg : ∀ x y : K, Work.WilC5.leE x y ↔ x ≤ y)
    (B : WilkiesDesign.CG.LRc.Substructure K)
    (hBexp : ∀ b ∈ (B : Set K), Work.WilC5.expE b ∈ (B : Set K))
    {y : K} (hypos : 0 < y)
    (hynew : ∀ b : ↥B, ¬ Work.WilC5.SameArch (b : K) y)
    {a : ↥B} {t : K} (ht0 : t ≠ 0)
    (hrel : Work.WilC5.logFun y = Work.WilC5.addE (a : K) t ∨
            Work.WilC5.logFun y = Work.WilC5.subE (a : K) t) :
    ¬ Work.WilC5.IsFiniteVal t := by
  -- `logFun y` is a genuine logarithm, and `y > 0`
  have hyposE : Work.WilC5.leE Work.WilC5.zeroE y ∧ ¬ Work.WilC5.leE y Work.WilC5.zeroE :=
    (Work.WilC5.S4ExpF.leE_zero_iff (K := K) (inferInstance) hadd hleneg y).mpr hypos
  have hexplog : Work.WilC5.expE (Work.WilC5.logFun y) = y :=
    Work.WilC5.expE_logFun_of_pos (M := K) (inferInstance) hyposE
  -- Normalise the relation to the form `logFun y = addE a s` with `s = ±t`
  have hrel' : Work.WilC5.logFun y = Work.WilC5.addE (a : K) t ∨
      Work.WilC5.logFun y = Work.WilC5.addE (a : K) (-t) := by
    rcases hrel with h | h
    · exact Or.inl h
    · refine Or.inr ?_
      rw [h, Work.WilC5.S4ExpF.subE_eq_sub (K := K) (inferInstance) hadd (a : K) t, hadd]
      ring
  -- The main contradiction: `logFun y = a + s` with `s` finite is impossible
  have hmain : ∀ s : K, Work.WilC5.IsFiniteVal s →
      Work.WilC5.logFun y = Work.WilC5.addE (a : K) s → False := by
    intro s hs hrels
    obtain ⟨N, hN⟩ := hs
    -- `s ≤ N+1` and `-s ≤ N+1`
    have hs_le : s ≤ ((N : K) + 1) := le_trans (le_abs_self s) hN
    have hs_neg_le : -s ≤ ((N : K) + 1) := le_trans (neg_le_abs s) hN
    -- `exp` of a standard natural is bounded by a standard natural
    obtain ⟨Mu, hMu⟩ :=
      Work.WilC5.expNat_le (K := K) (inferInstance) hadd hmul hone hleneg (N + 1)
    have hN1 : ((N : K) + 1) = (((N + 1 : ℕ)) : K) := (Nat.cast_succ N).symm
    have hexp_le : Work.WilC5.expE s ≤ (Mu : K) := by
      have h := (hleneg _ _).mp (Work.WilC5.expE_le_of_le (M := K) (inferInstance)
        ((hleneg s _).mpr hs_le))
      calc Work.WilC5.expE s ≤ Work.WilC5.expE ((N : K) + 1) := h
        _ = Work.WilC5.expE ((((N + 1 : ℕ)) : K)) := by rw [hN1]
        _ ≤ (Mu : K) := hMu
    have hexp_neg_le : Work.WilC5.expE (-s) ≤ (Mu : K) := by
      have h := (hleneg _ _).mp (Work.WilC5.expE_le_of_le (M := K) (inferInstance)
        ((hleneg (-s) _).mpr hs_neg_le))
      calc Work.WilC5.expE (-s) ≤ Work.WilC5.expE ((N : K) + 1) := h
        _ = Work.WilC5.expE ((((N + 1 : ℕ)) : K)) := by rw [hN1]
        _ ≤ (Mu : K) := hMu
    -- `exp s > 0` and `exp s * exp (-s) = 1`
    have hpos : 0 < Work.WilC5.expE s :=
      (Work.WilC5.S4ExpF.leE_zero_iff (K := K) (inferInstance) hadd hleneg _).mp
        (Work.WilC5.expE_pos_of_model (M := K) (inferInstance) s)
    have hsplit : Work.WilC5.expE s * Work.WilC5.expE (-s) = 1 := by
      rw [← hmul, ← Work.WilC5.expE_add_of_model (M := K) (inferInstance) s (-s), hadd,
        add_neg_cancel, ← Work.WilC5.S4ExpF.zeroE_eq_zero (K := K) (inferInstance) hadd,
        Work.WilC5.S4ExpF.expE_zeroE_of_model (K := K) (inferInstance), hone]
    have hone_le : (1 : K) ≤ Work.WilC5.expE s * ((Mu : K) + 1) := by
      calc (1 : K) = Work.WilC5.expE s * Work.WilC5.expE (-s) := hsplit.symm
        _ ≤ Work.WilC5.expE s * ((Mu : K) + 1) :=
              mul_le_mul_of_nonneg_left
                (le_trans hexp_neg_le (le_add_of_nonneg_right zero_le_one)) (le_of_lt hpos)
    have hinv_le : ((Mu : K) + 1)⁻¹ ≤ Work.WilC5.expE s :=
      (inv_le_iff_one_le_mul₀ (by positivity : (0 : K) < (Mu : K) + 1)).mpr hone_le
    -- `exp s` is a unit of the standard real valuation
    have hunit : WilkiesDesign.CG.IsUnitVal (Work.WilC5.expE s) := by
      refine ⟨Mu, ?_, ?_⟩
      · rw [abs_of_pos hpos]; exact hinv_le
      · rw [abs_of_pos hpos]; exact le_trans hexp_le (le_add_of_nonneg_right zero_le_one)
    have hsame1 : Work.WilC5.SameArch (Work.WilC5.expE s) 1 :=
      (Work.WilC5.IsUnitVal_iff_SameArch (Work.WilC5.expE s)).mp hunit
    -- hence `y = exp a * exp s` has the same value as `exp a ∈ B`
    have hy_eq : y = Work.WilC5.expE (a : K) * Work.WilC5.expE s := by
      rw [← hexplog, hrels, Work.WilC5.expE_add_of_model (M := K) (inferInstance), hmul]
    have hSA : Work.WilC5.SameArch y (Work.WilC5.expE (a : K)) := by
      rw [hy_eq]
      have h := Work.WilC5.SameArch_mul
        (Work.WilC5.SameArch_equiv.refl (Work.WilC5.expE (a : K))) hsame1
      rwa [mul_one] at h
    exact hynew ⟨Work.WilC5.expE (a : K), hBexp (a : K) a.2⟩
      (Work.WilC5.SameArch_equiv.symm hSA)
  intro hfin
  have hfin_neg : Work.WilC5.IsFiniteVal (-t) := by
    obtain ⟨N, hN⟩ := hfin
    exact ⟨N, by rwa [abs_neg]⟩
  rcases hrel' with h | h
  · exact hmain t hfin h
  · exact hmain (-t) hfin_neg h

end Work.WilC5.ExistsStepSeqAux
