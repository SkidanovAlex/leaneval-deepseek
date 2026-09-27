import Mathlib
import Submission.Work.EKLC6Core.Basic
import Submission.Work.EKLC6Core.Hcond_mono
import Submission.Work.EKLC6Core.HcondFam_partSigmaFam
import Submission.Work.EKLGen.tendsto_Hcond_iSup_univ
import Submission.Work.EKLGen.Hcond_iInf_of_tendsto
import Submission.Work.EKLGen.exists_partSigma_tendsto
import Submission.Work.EKLComp.Hcond_joinTwo
import Submission.Work.EKLComp.hPart_eq_ent_of_generating
import Submission.Work.EKLC6Core.BiGenAux
import Submission.Work.EKLC6Core.BiGenChain.Basic
import Submission.Work.EKLC6Core.Hcond_nonneg
import Submission.Work.EKLC6Core.Hcond_le_Hcond_add

/-!
# `HcondSig_iInf` — continuity from above of the σ-algebra conditional entropy

`HcondSig μ M B = ⨆_{P : partSigma P ≤ M} ofReal (Hcond μ P B)` is the conditional entropy of the
countably generated σ-algebra `M` given `B`.  It is antitone in `B`, and this file proves that it
is *continuous from above* along an increasing sequence: for `C : ℕ → MeasurableSpace X` monotone
with `C l ≤ mX`, and `M` countably generated with `HcondSig μ M (C 0) ≠ ⊤`,

`(⨅ l, HcondSig μ M (C l)) = HcondSig μ M (⨆ l, C l)`.

The (easy) inequality `HcondSig μ M (⨆ l, C l) ≤ ⨅ l, HcondSig μ M (C l)` is antitonicity.  For
the reverse inequality one chooses a refining chain `F : ℕ → FinPart X` of finite partitions with
`partSigma (F n) ↑ M` (which exists because `M` is countably generated) and uses

* the chain rule bound `Hcond μ P B ≤ Hcond μ (F n) B + Hcond μ P (partSigma (F n) ⊔ B)`
  (`Work.EKLC6Core.Hcond_le_Hcond_add`), which turns the supremum over `P` into the *chain*
  sup `⨆ n, ofReal (Hcond μ (F n) B)` (`HcondSig_eq_iSup_chain`);
* the Lévy continuity for *finite* partitions (`Work.EKLGen.Hcond_iInf_of_tendsto`), which gives
  `Hcond μ (F n) (⨆ l, C l) = ⨅ l, Hcond μ (F n) (C l)`, hence that the chain-sup at `B` is
  continuous from above;
* the finiteness hypothesis `HcondSig μ M (C 0) ≠ ⊤`, which makes the difference
  `HcondSig μ M (partSigma (F n) ⊔ C 0) = HcondSig μ M (C 0) - ofReal (Hcond μ (F n) (C 0))`
  tend to `0` (`HcondSig_iInf_chain_sup_eq_zero`).

The `@Work.EKLContract.Hcond X mX μ …` annotations are needed because the local hypotheses
`M B : MeasurableSpace X` are themselves typeclass candidates for the ambient instance.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

noncomputable section

namespace Work.EKLC6Core

/-! ## Monotonicity of `HcondSig` -/

/-- `HcondSig μ · C` is monotone in the first σ-algebra. -/
theorem HcondSig_mono_left {X : Type*} [mX : MeasurableSpace X] (μ : MeasureTheory.Measure X)
    [MeasureTheory.IsProbabilityMeasure μ] {A B C : MeasurableSpace X} (h : A ≤ B) :
    @HcondSig X mX μ A C ≤ @HcondSig X mX μ B C := by
  refine iSup_le fun P => ?_
  exact le_iSup (fun Q : {Q : @Work.EKLContract.FinPart X mX //
      (@Work.EKLContract.partSigma X mX Q) ≤ B} =>
    ENNReal.ofReal (@Work.EKLContract.Hcond X mX μ Q.1 C)) ⟨P.1, le_trans P.2 h⟩

/-- `HcondSig μ M ·` is antitone in the conditioning σ-algebra. -/
theorem HcondSig_antitone_cond {X : Type*} [mX : MeasurableSpace X] (μ : MeasureTheory.Measure X)
    [MeasureTheory.IsProbabilityMeasure μ] {M C C' : MeasurableSpace X} (h : C ≤ C') :
    @HcondSig X mX μ M C' ≤ @HcondSig X mX μ M C := by
  refine iSup_le fun P => ?_
  refine le_trans (ENNReal.ofReal_le_ofReal (Hcond_mono (mX := mX) μ P.1 C C' h)) ?_
  exact le_iSup (fun Q : {Q : @Work.EKLContract.FinPart X mX //
      (@Work.EKLContract.partSigma X mX Q) ≤ M} =>
    ENNReal.ofReal (@Work.EKLContract.Hcond X mX μ Q.1 C)) P

/-! ## Two elementary helpers -/

/-- A sequence tending to `A` admits, for every `ε > 0`, a term within `ε` of `A` from below. -/
theorem exists_le_add_of_tendsto {a : ℕ → ℝ} {A : ℝ}
    (h : Tendsto a atTop (nhds A)) : ∀ ε : ℝ, 0 < ε → ∃ l, a l ≤ A + ε := by
  intro ε hε
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp h) ε hε
  refine ⟨N, ?_⟩
  have h1 := hN N le_rfl
  rw [Real.dist_eq] at h1
  linarith [(abs_lt.mp h1).2]

/-- If a nonnegative sequence `a` is approached from above in the sense that every `ε > 0` bounds
some term by `A + ε`, then `⨅ l, ofReal (a l) ≤ ofReal A`. -/
theorem iInf_ofReal_le {a : ℕ → ℝ} {A : ℝ} (hA : 0 ≤ A)
    (h : ∀ ε : ℝ, 0 < ε → ∃ l, a l ≤ A + ε) :
    (⨅ l, ENNReal.ofReal (a l)) ≤ ENNReal.ofReal A := by
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  obtain ⟨l, hl⟩ := h (ε : ℝ) (by exact_mod_cast hε)
  calc (⨅ l, ENNReal.ofReal (a l)) ≤ ENNReal.ofReal (a l) := iInf_le _ l
    _ ≤ ENNReal.ofReal (A + (ε : ℝ)) := ENNReal.ofReal_le_ofReal hl
    _ = ENNReal.ofReal A + (ε : ℝ≥0∞) := by
        rw [ENNReal.ofReal_add hA (by positivity), ENNReal.ofReal_coe_nnreal]

/-! ## The supremum over partitions is attained along a generating chain -/

/-- **The countable-partition identity.**  For a refining chain `F` of finite partitions with
`partSigma (F n) ↑ M`, the supremum defining `HcondSig μ M B` is attained along the chain. -/
theorem HcondSig_eq_iSup_chain {X : Type*} [mX : MeasurableSpace X] (μ : MeasureTheory.Measure X)
    [MeasureTheory.IsProbabilityMeasure μ] {M : MeasurableSpace X}
    (F : ℕ → @Work.EKLContract.FinPart X mX)
    (hFle : ∀ n, (@Work.EKLContract.partSigma X mX (F n)) ≤ M)
    (hFmono : Monotone (fun n => (@Work.EKLContract.partSigma X mX (F n))))
    (hFsup : (⨆ n, (@Work.EKLContract.partSigma X mX (F n))) = M)
    {B : MeasurableSpace X} (hB : B ≤ mX) :
    @HcondSig X mX μ M B = ⨆ n, ENNReal.ofReal (@Work.EKLContract.Hcond X mX μ (F n) B) := by
  refine le_antisymm ?_ ?_
  · refine iSup_le fun P => ?_
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    have hbdd : BddBelow (Set.range (fun n => @Work.EKLContract.Hcond X mX μ P.1
        ((@Work.EKLContract.partSigma X mX (F n)) ⊔ B))) :=
      ⟨0, by rintro _ ⟨n, rfl⟩; exact Hcond_nonneg (mX := mX) μ P.1 _⟩
    -- every `partSigma (F n)` sits below the ambient σ-algebra
    have hpartX : ∀ n, (@Work.EKLContract.partSigma X mX (F n)) ≤ mX :=
      fun n => Work.EKLC6Core.BiGenChain.partSigma_le_mX (mX := mX) (F n)
    have hMle : M ≤ mX := by rw [← hFsup]; exact iSup_le hpartX
    have hzero : (⨅ n, @Work.EKLContract.Hcond X mX μ P.1
        ((@Work.EKLContract.partSigma X mX (F n)) ⊔ B)) = 0 := by
      have hmono : Monotone (fun n => (@Work.EKLContract.partSigma X mX (F n)) ⊔ B) :=
        fun i j hij => sup_le_sup (hFmono hij) le_rfl
      have hsup : (⨆ n, (@Work.EKLContract.partSigma X mX (F n)) ⊔ B) = M ⊔ B := by
        rw [iSup_sup_eq, hFsup, iSup_const]
      have hle : ∀ n, (@Work.EKLContract.partSigma X mX (F n)) ⊔ B ≤ mX :=
        fun n => sup_le (hpartX n) hB
      have hc := Work.EKLGen.Hcond_iInf_of_tendsto (mX := mX) μ P.1
        (fun n => (@Work.EKLContract.partSigma X mX (F n)) ⊔ B) (M ⊔ B) hmono hle
        (sup_le hMle hB) hsup
      rw [← hc]
      have h1 : @Work.EKLContract.Hcond X mX μ P.1 (M ⊔ B)
          ≤ @Work.EKLContract.Hcond X mX μ P.1 (@Work.EKLContract.partSigma X mX P.1) :=
        Hcond_mono (mX := mX) μ P.1 _ _ (le_trans P.2 le_sup_left)
      rw [BiGenAux.Hcond_partSigma_eq_zero (mX := mX) μ P.1] at h1
      exact le_antisymm h1 (Hcond_nonneg (mX := mX) μ P.1 _)
    obtain ⟨N, hN⟩ := (ciInf_lt_iff hbdd).mp (by rw [hzero]; exact_mod_cast hε)
    have hD := Hcond_le_Hcond_add (mX := mX) μ P.1 (F N) B
    calc ENNReal.ofReal (@Work.EKLContract.Hcond X mX μ P.1 B)
        ≤ ENNReal.ofReal (@Work.EKLContract.Hcond X mX μ (F N) B
            + @Work.EKLContract.Hcond X mX μ P.1
              ((@Work.EKLContract.partSigma X mX (F N)) ⊔ B)) :=
          ENNReal.ofReal_le_ofReal hD
      _ = ENNReal.ofReal (@Work.EKLContract.Hcond X mX μ (F N) B)
            + ENNReal.ofReal (@Work.EKLContract.Hcond X mX μ P.1
              ((@Work.EKLContract.partSigma X mX (F N)) ⊔ B)) :=
          ENNReal.ofReal_add (Hcond_nonneg (mX := mX) μ (F N) B)
            (Hcond_nonneg (mX := mX) μ P.1 _)
      _ ≤ ENNReal.ofReal (@Work.EKLContract.Hcond X mX μ (F N) B) + (ε : ℝ≥0∞) := by
          refine add_le_add (le_refl _) ?_
          rw [← ENNReal.ofReal_coe_nnreal]
          exact ENNReal.ofReal_le_ofReal (le_of_lt hN)
      _ ≤ (⨆ n, ENNReal.ofReal (@Work.EKLContract.Hcond X mX μ (F n) B)) + (ε : ℝ≥0∞) :=
          add_le_add (le_iSup (fun n =>
            ENNReal.ofReal (@Work.EKLContract.Hcond X mX μ (F n) B)) N) (le_refl _)
  · refine iSup_le fun n => ?_
    exact le_iSup (fun Q : {Q : @Work.EKLContract.FinPart X mX //
        (@Work.EKLContract.partSigma X mX Q) ≤ M} =>
      ENNReal.ofReal (@Work.EKLContract.Hcond X mX μ Q.1 B)) ⟨F n, hFle n⟩

/-! ## The chain rule at the level of `HcondSig` -/

/-- **Chain rule for `HcondSig`.**  For a finite partition `F` with `partSigma F ≤ M`,
`HcondSig μ M B = ofReal (Hcond μ F B) + HcondSig μ M (partSigma F ⊔ B)`. -/
theorem HcondSig_eq_add {X : Type*} [mX : MeasurableSpace X] (μ : MeasureTheory.Measure X)
    [MeasureTheory.IsProbabilityMeasure μ] {M : MeasurableSpace X}
    (F : @Work.EKLContract.FinPart X mX) (hF : (@Work.EKLContract.partSigma X mX F) ≤ M)
    (B : MeasurableSpace X) :
    @HcondSig X mX μ M B
      = ENNReal.ofReal (@Work.EKLContract.Hcond X mX μ F B)
        + @HcondSig X mX μ M ((@Work.EKLContract.partSigma X mX F) ⊔ B) := by
  haveI : Nonempty {P : @Work.EKLContract.FinPart X mX //
      (@Work.EKLContract.partSigma X mX P) ≤ M} := ⟨⟨F, hF⟩⟩
  refine le_antisymm ?_ ?_
  · -- ≤ : use the chain-rule bound for a general partition `P`
    refine iSup_le fun P => ?_
    have hD := Hcond_le_Hcond_add (mX := mX) μ P.1 F B
    calc ENNReal.ofReal (@Work.EKLContract.Hcond X mX μ P.1 B)
        ≤ ENNReal.ofReal (@Work.EKLContract.Hcond X mX μ F B
            + @Work.EKLContract.Hcond X mX μ P.1
              ((@Work.EKLContract.partSigma X mX F) ⊔ B)) :=
          ENNReal.ofReal_le_ofReal hD
      _ = ENNReal.ofReal (@Work.EKLContract.Hcond X mX μ F B)
            + ENNReal.ofReal (@Work.EKLContract.Hcond X mX μ P.1
              ((@Work.EKLContract.partSigma X mX F) ⊔ B)) :=
          ENNReal.ofReal_add (Hcond_nonneg (mX := mX) μ F B)
            (Hcond_nonneg (mX := mX) μ P.1 _)
      _ ≤ ENNReal.ofReal (@Work.EKLContract.Hcond X mX μ F B)
            + @HcondSig X mX μ M ((@Work.EKLContract.partSigma X mX F) ⊔ B) :=
          add_le_add (le_refl _) (le_iSup (fun Q : {Q : @Work.EKLContract.FinPart X mX //
            (@Work.EKLContract.partSigma X mX Q) ≤ M} =>
            ENNReal.ofReal (@Work.EKLContract.Hcond X mX μ Q.1
              ((@Work.EKLContract.partSigma X mX F) ⊔ B))) P)
  · -- ≥ : bound the supremum by the entropy of the binary join
    have key : ∀ P : {P : @Work.EKLContract.FinPart X mX //
        (@Work.EKLContract.partSigma X mX P) ≤ M},
        ENNReal.ofReal (@Work.EKLContract.Hcond X mX μ F B)
          + ENNReal.ofReal (@Work.EKLContract.Hcond X mX μ P.1
              ((@Work.EKLContract.partSigma X mX F) ⊔ B))
        ≤ @HcondSig X mX μ M B := by
      intro P
      have hj := Work.EKLComp.Hcond_joinTwo (mX := mX) μ F P.1 B
      have hpart : (@Work.EKLContract.partSigma X mX
          (@Work.EKLComp.joinTwo X mX F P.1)) ≤ M := by
        rw [@Work.EKLComp.partSigma_joinTwo X mX]
        exact sup_le hF P.2
      have h1 : ENNReal.ofReal (@Work.EKLContract.Hcond X mX μ
          (@Work.EKLComp.joinTwo X mX F P.1) B) ≤ @HcondSig X mX μ M B :=
        le_iSup (fun Q : {Q : @Work.EKLContract.FinPart X mX //
          (@Work.EKLContract.partSigma X mX Q) ≤ M} =>
          ENNReal.ofReal (@Work.EKLContract.Hcond X mX μ Q.1 B)) ⟨_, hpart⟩
      refine le_trans (le_of_eq ?_) h1
      rw [hj, ENNReal.ofReal_add (Hcond_nonneg (mX := mX) μ F B)
          (Hcond_nonneg (mX := mX) μ P.1 _),
        show B ⊔ (@Work.EKLContract.partSigma X mX F) = (@Work.EKLContract.partSigma X mX F) ⊔ B
          from sup_comm B _]
    calc ENNReal.ofReal (@Work.EKLContract.Hcond X mX μ F B)
          + @HcondSig X mX μ M ((@Work.EKLContract.partSigma X mX F) ⊔ B)
        = ENNReal.ofReal (@Work.EKLContract.Hcond X mX μ F B)
          + ⨆ P : {P : @Work.EKLContract.FinPart X mX //
              (@Work.EKLContract.partSigma X mX P) ≤ M},
              ENNReal.ofReal (@Work.EKLContract.Hcond X mX μ P.1
                ((@Work.EKLContract.partSigma X mX F) ⊔ B)) := rfl
      _ = ⨆ P : {P : @Work.EKLContract.FinPart X mX //
              (@Work.EKLContract.partSigma X mX P) ≤ M},
              (ENNReal.ofReal (@Work.EKLContract.Hcond X mX μ F B)
                + ENNReal.ofReal (@Work.EKLContract.Hcond X mX μ P.1
                  ((@Work.EKLContract.partSigma X mX F) ⊔ B))) := ENNReal.add_iSup _
      _ ≤ @HcondSig X mX μ M B := iSup_le key

/-! ## The chain-sup vanishes in the limit -/

/-- **Lévy from above for `HcondSig`.**  If `HcondSig μ M B < ∞`, the conditional entropies of `B`
given `partSigma (F n) ⊔ B` tend to `0`. -/
theorem HcondSig_iInf_chain_sup_eq_zero {X : Type*} [mX : MeasurableSpace X]
    (μ : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure μ]
    {M : MeasurableSpace X} (F : ℕ → @Work.EKLContract.FinPart X mX)
    (hFle : ∀ n, (@Work.EKLContract.partSigma X mX (F n)) ≤ M)
    (hFmono : Monotone (fun n => (@Work.EKLContract.partSigma X mX (F n))))
    (hFsup : (⨆ n, (@Work.EKLContract.partSigma X mX (F n))) = M)
    {B : MeasurableSpace X} (hB : B ≤ mX) (hfin : @HcondSig X mX μ M B ≠ ⊤) :
    (⨅ n, @HcondSig X mX μ M ((@Work.EKLContract.partSigma X mX (F n)) ⊔ B)) = 0 := by
  have hchain : @HcondSig X mX μ M B
      = ⨆ n, ENNReal.ofReal (@Work.EKLContract.Hcond X mX μ (F n) B) :=
    HcondSig_eq_iSup_chain (mX := mX) μ F hFle hFmono hFsup hB
  have h_eq : (⨅ n, @HcondSig X mX μ M ((@Work.EKLContract.partSigma X mX (F n)) ⊔ B))
      = ⨅ n, (@HcondSig X mX μ M B
          - ENNReal.ofReal (@Work.EKLContract.Hcond X mX μ (F n) B)) := by
    refine iInf_congr fun n => ?_
    have h := HcondSig_eq_add (mX := mX) μ (F n) (hFle n) B
    rw [add_comm] at h
    exact (ENNReal.sub_eq_of_eq_add (ne_of_lt ENNReal.ofReal_lt_top) h).symm
  have h2 : (⨅ n, (@HcondSig X mX μ M B
        - ENNReal.ofReal (@Work.EKLContract.Hcond X mX μ (F n) B)))
      = @HcondSig X mX μ M B - ⨆ n, ENNReal.ofReal (@Work.EKLContract.Hcond X mX μ (F n) B) :=
    (ENNReal.sub_iSup hfin).symm
  rw [h_eq, h2, ← hchain]
  exact tsub_self _

/-! ## The main theorem -/

theorem HcondSig_iInf {X : Type*} [mX : MeasurableSpace X]
    (μ : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure μ]
    (M : MeasurableSpace X)
    (hMgen : ∃ b : Set (Set X), b.Countable ∧ M = MeasurableSpace.generateFrom b)
    (hMle : M ≤ mX) (C : ℕ → MeasurableSpace X) (hCmono : Monotone C)
    (hCle : ∀ l, C l ≤ mX) (hfin : @Work.EKLC6Core.HcondSig X mX μ M (C 0) ≠ ⊤) :
    (⨅ l, @Work.EKLC6Core.HcondSig X mX μ M (C l))
      = @Work.EKLC6Core.HcondSig X mX μ M (⨆ l, C l) := by
  obtain ⟨b, hbc, hbgen⟩ := hMgen
  have hseq : ∃ f : ℕ → Set X, (∀ n, @MeasurableSet X M (f n)) ∧
      MeasurableSpace.generateFrom (Set.range f) = M := by
    letI : MeasurableSpace X := M
    haveI : MeasurableSpace.CountablyGenerated X := ⟨b, hbc, hbgen⟩
    exact ⟨MeasurableSpace.natGeneratingSequence X,
      fun n => MeasurableSpace.measurableSet_natGeneratingSequence n,
      MeasurableSpace.generateFrom_natGeneratingSequence X⟩
  obtain ⟨f, hfM, hfgen⟩ := hseq
  have hfX : ∀ n, @MeasurableSet X mX (f n) := fun n => hMle (f n) (hfM n)
  obtain ⟨F, hF1, hF2, hF3⟩ :=
    Work.EKLGen.exists_finPart_chain_of_generating (mX := mX) f hfX
  have hFle : ∀ n, (@Work.EKLContract.partSigma X mX (F n)) ≤ M :=
    fun n => by rw [← hfgen]; exact hF1 n
  have hFsup : (⨆ n, (@Work.EKLContract.partSigma X mX (F n))) = M := by rw [hF3, hfgen]
  have hFmono : Monotone (fun n => (@Work.EKLContract.partSigma X mX (F n))) :=
    monotone_nat_of_le_succ hF2
  refine le_antisymm ?_ ?_
  · -- hard direction: `⨅ l, HcondSig μ M (C l) ≤ HcondSig μ M (⨆ l, C l)`
    have hchainS : @HcondSig X mX μ M (⨆ l, C l)
        = ⨆ n, ENNReal.ofReal (@Work.EKLContract.Hcond X mX μ (F n) (⨆ l, C l)) :=
      HcondSig_eq_iSup_chain (mX := mX) μ F hFle hFmono hFsup (iSup_le hCle)
    have hstep5 : (⨅ n, @HcondSig X mX μ M
        ((@Work.EKLContract.partSigma X mX (F n)) ⊔ (C 0))) = 0 :=
      HcondSig_iInf_chain_sup_eq_zero (mX := mX) μ F hFle hFmono hFsup (hCle 0) hfin
    have step_a : ∀ n, (⨅ l, @HcondSig X mX μ M (C l))
        ≤ ENNReal.ofReal (@Work.EKLContract.Hcond X mX μ (F n) (⨆ l, C l))
          + @HcondSig X mX μ M ((@Work.EKLContract.partSigma X mX (F n)) ⊔ (C 0)) := by
      intro n
      have hpoint : ∀ l, @HcondSig X mX μ M (C l)
          ≤ ENNReal.ofReal (@Work.EKLContract.Hcond X mX μ (F n) (C l))
            + @HcondSig X mX μ M ((@Work.EKLContract.partSigma X mX (F n)) ⊔ (C 0)) := by
        intro l
        rw [HcondSig_eq_add (mX := mX) μ (F n) (hFle n) (C l)]
        exact add_le_add (le_refl _)
          (HcondSig_antitone_cond (mX := mX) μ
            (sup_le_sup (le_refl _) (hCmono (Nat.zero_le l))))
      calc (⨅ l, @HcondSig X mX μ M (C l))
          ≤ ⨅ l, (ENNReal.ofReal (@Work.EKLContract.Hcond X mX μ (F n) (C l))
              + @HcondSig X mX μ M ((@Work.EKLContract.partSigma X mX (F n)) ⊔ (C 0))) :=
            iInf_mono hpoint
        _ = (⨅ l, ENNReal.ofReal (@Work.EKLContract.Hcond X mX μ (F n) (C l)))
              + @HcondSig X mX μ M ((@Work.EKLContract.partSigma X mX (F n)) ⊔ (C 0)) :=
            ENNReal.iInf_add.symm
        _ ≤ ENNReal.ofReal (@Work.EKLContract.Hcond X mX μ (F n) (⨆ l, C l))
              + @HcondSig X mX μ M ((@Work.EKLContract.partSigma X mX (F n)) ⊔ (C 0)) := by
            refine add_le_add ?_ (le_refl _)
            refine iInf_ofReal_le (Hcond_nonneg (mX := mX) μ (F n) (⨆ l, C l))
              fun ε hε => ?_
            exact exists_le_add_of_tendsto
              (Work.EKLGen.tendsto_Hcond_iSup_univ (mX := mX) μ (F n) C hCmono hCle) ε hε
    calc (⨅ l, @HcondSig X mX μ M (C l))
        ≤ ⨅ n, (ENNReal.ofReal (@Work.EKLContract.Hcond X mX μ (F n) (⨆ l, C l))
            + @HcondSig X mX μ M ((@Work.EKLContract.partSigma X mX (F n)) ⊔ (C 0))) :=
          le_iInf step_a
      _ ≤ (⨆ n, ENNReal.ofReal (@Work.EKLContract.Hcond X mX μ (F n) (⨆ l, C l)))
            + (⨅ n, @HcondSig X mX μ M
              ((@Work.EKLContract.partSigma X mX (F n)) ⊔ (C 0))) := by
          calc (⨅ n, (ENNReal.ofReal (@Work.EKLContract.Hcond X mX μ (F n) (⨆ l, C l))
                + @HcondSig X mX μ M ((@Work.EKLContract.partSigma X mX (F n)) ⊔ (C 0))))
              ≤ ⨅ n, ((⨆ m,
                    ENNReal.ofReal (@Work.EKLContract.Hcond X mX μ (F m) (⨆ l, C l)))
                  + @HcondSig X mX μ M
                    ((@Work.EKLContract.partSigma X mX (F n)) ⊔ (C 0))) :=
                iInf_mono fun n => add_le_add (le_iSup (fun m =>
                  ENNReal.ofReal (@Work.EKLContract.Hcond X mX μ (F m) (⨆ l, C l))) n)
                  (le_refl _)
            _ = (⨆ m, ENNReal.ofReal (@Work.EKLContract.Hcond X mX μ (F m) (⨆ l, C l)))
                  + (⨅ n, @HcondSig X mX μ M
                    ((@Work.EKLContract.partSigma X mX (F n)) ⊔ (C 0))) :=
                ENNReal.add_iInf.symm
      _ = @HcondSig X mX μ M (⨆ l, C l) := by rw [← hchainS, hstep5, add_zero]
  · -- easy direction
    refine le_iInf fun l => HcondSig_antitone_cond (mX := mX) μ (le_iSup C l)

end Work.EKLC6Core

end
