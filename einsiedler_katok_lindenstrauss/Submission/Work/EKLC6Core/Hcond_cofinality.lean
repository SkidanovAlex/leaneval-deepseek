import Mathlib
import Submission.Work.EKLC6Core.Hcond_mono
import Submission.Work.EKLC6Core.Hcond_le_Hcond_add
import Submission.Work.EKLC6Core.exists_Hcond_le_of_iSup_le_zero
import Submission.Work.EKLComp.hPart_eq_ent_of_generating

/-!
# `Work.EKLC6Core.ofReal_Hcond_le_iSup_of_partSigma_iSup` — cofinality of a refining chain

The bridge that turns a **countable** generating partition into a supremum of **finite** ones:

    ofReal (Hcond μ R C) ≤ ⨆ m, ofReal (Hcond μ (S m) C)

whenever the σ-algebras `σ (S m)` of a sequence of finite partitions increase and their supremum
contains `σ R`.  No finiteness hypothesis is needed.

This is step (1) of the plan recorded in `EKLC6Core/ENTROPY_GEN_NOTE.md` §3 for the open
Pisa 7.6(ii) statement `ent_le_HcondSig_of_countable_gen`: instantiating `S m := truncPart P m`
(the truncations of a countable partition `P`) expresses the conditional entropy of any finite
sub-partition of `σ (range P)` through those of the truncations, hence (taking the supremum and
using the definition of `HcondSig` as a supremum over finite sub-partitions)

    HcondSig μ (σ (range P)) C = ⨆ m, ofReal (Hcond μ (truncPart P m) C).

Ingredients (all already in the tree):

* the chain-rule inequality `Work.EKLC6Core.Hcond_le_Hcond_add`
  (`H_μ(P|m) ≤ H_μ(Q|m) + H_μ(P|m ∨ σ Q)`, for arbitrary `P`, `Q`);
* `Hcond μ R B = 0` as soon as `σ R ≤ B` (from the proved `Hcond_partSigma_eq_zero` and
  monotonicity of `Hcond` in the conditioning σ-algebra);
* Lévy's theorem for `Hcond μ R ·` along an increasing sequence of σ-algebras
  (`Work.EKLC6Core.exists_Hcond_le_of_iSup_le_zero`).
-/

open MeasureTheory
open scoped BigOperators

noncomputable section

namespace Work.EKLC6Core

/-- `Hcond` vanishes as soon as the conditioning σ-algebra contains the partition's σ-algebra. -/
lemma Hcond_eq_zero_of_partSigma_le {X : Type*} [mX : MeasurableSpace X]
    (μ : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure μ]
    (R : @Work.EKLContract.FinPart X mX) {B : MeasurableSpace X}
    (h : (@Work.EKLContract.partSigma X mX R) ≤ B) :
    @Work.EKLContract.Hcond X mX μ R B = 0 :=
  le_antisymm
    (le_trans (Hcond_mono (mX := mX) (μ := μ) R (@Work.EKLContract.partSigma X mX R) B h)
      (le_of_eq (Work.EKLComp.Hcond_partSigma_eq_zero (mX := mX) (μ := μ) R)))
    (Hcond_nonneg_aux (mX := mX) (μ := μ) R B)

/-- **Cofinality of a refining chain.**  If `σ (S m)` is monotone and its supremum contains `σ R`,
then `ofReal (H_μ(R|C))` is at most the supremum of the `ofReal (H_μ(S m | C))`. -/
theorem ofReal_Hcond_le_iSup_of_partSigma_iSup {X : Type*} [mX : MeasurableSpace X]
    (μ : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure μ]
    (R : @Work.EKLContract.FinPart X mX) (S : ℕ → @Work.EKLContract.FinPart X mX)
    {C : MeasurableSpace X}
    (hmono : Monotone fun m => @Work.EKLContract.partSigma X mX (S m))
    (hC : C ≤ mX) (hSm : ∀ m, @Work.EKLContract.partSigma X mX (S m) ≤ mX)
    (hR : @Work.EKLContract.partSigma X mX R ≤ ⨆ m, @Work.EKLContract.partSigma X mX (S m)) :
    ENNReal.ofReal (@Work.EKLContract.Hcond X mX μ R C)
      ≤ ⨆ m, ENNReal.ofReal (@Work.EKLContract.Hcond X mX μ (S m) C) := by
  classical
  set Aseq : ℕ → MeasurableSpace X :=
    fun m => @Work.EKLContract.partSigma X mX (S m) ⊔ C with hAseq
  have hAmono : Monotone Aseq := fun a b hab => sup_le_sup_right (hmono hab) C
  have hAle : ∀ m, Aseq m ≤ mX := fun m => sup_le (hSm m) hC
  have hsup : (⨆ m, Aseq m) = (⨆ m, @Work.EKLContract.partSigma X mX (S m)) ⊔ C := by
    rw [hAseq]
    rw [iSup_sup_eq, iSup_const]
  have hzero : @Work.EKLContract.Hcond X mX μ R (⨆ m, Aseq m) = 0 := by
    refine Hcond_eq_zero_of_partSigma_le (mX := mX) (μ := μ) R ?_
    rw [hsup]
    exact le_sup_of_le_left hR
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  obtain ⟨m, hm⟩ := exists_Hcond_le_of_iSup_le_zero (mX := mX) (μ := μ) R Aseq hAmono hAle
    (le_of_eq hzero) (show (0 : ℝ) < ((ε : NNReal) : ℝ) from by exact_mod_cast hε)
  have h1 := Hcond_le_Hcond_add (mX := mX) (μ := μ) R (S m) C
  have h1' : @Work.EKLContract.Hcond X mX μ R C
      ≤ @Work.EKLContract.Hcond X mX μ (S m) C
        + @Work.EKLContract.Hcond X mX μ R (Aseq m) := h1
  calc ENNReal.ofReal (@Work.EKLContract.Hcond X mX μ R C)
      ≤ ENNReal.ofReal (@Work.EKLContract.Hcond X mX μ (S m) C
          + @Work.EKLContract.Hcond X mX μ R (Aseq m)) := ENNReal.ofReal_le_ofReal h1'
    _ = ENNReal.ofReal (@Work.EKLContract.Hcond X mX μ (S m) C)
        + ENNReal.ofReal (@Work.EKLContract.Hcond X mX μ R (Aseq m)) :=
        ENNReal.ofReal_add (Hcond_nonneg_aux (mX := mX) (μ := μ) (S m) C)
          (Hcond_nonneg_aux (mX := mX) (μ := μ) R (Aseq m))
    _ ≤ (⨆ m, ENNReal.ofReal (@Work.EKLContract.Hcond X mX μ (S m) C))
        + ENNReal.ofReal ((ε : NNReal) : ℝ) :=
        add_le_add (le_iSup (fun m => ENNReal.ofReal
          (@Work.EKLContract.Hcond X mX μ (S m) C)) m) (ENNReal.ofReal_le_ofReal hm)
    _ = (⨆ m, ENNReal.ofReal (@Work.EKLContract.Hcond X mX μ (S m) C))
        + (ε : ENNReal) := by rw [ENNReal.ofReal_coe_nnreal]

end Work.EKLC6Core

end
