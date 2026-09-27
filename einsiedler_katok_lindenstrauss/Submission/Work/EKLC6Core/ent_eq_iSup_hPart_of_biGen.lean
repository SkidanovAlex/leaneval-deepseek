import Mathlib
import Submission.Work.EKLC6Core.BiGenAux
import Submission.Work.EKLC6Core.BiGenSup.iSup_comap_winPart_eq
import Submission.Work.EKLC6Core.BiGenChain.hPart_le_hPart_add_Hcond

/-!
# The bilateral generating theorem for Kolmogorov–Sinai entropy

If `𝒮` is a σ-algebra whose full `T`-orbit generates the ambient σ-algebra (`hbil`), and
`G l` is a refining sequence of finite partitions with `⨆ l, partSigma (G l) = 𝒮`, then

`ent μ T = ⨆ l, ENNReal.ofReal (hPart μ T (G l))`.

The proof replaces `G l` by the two-sided window `winPart Tinv hTinv (G l) l` whose entropy rate
equals that of `G l` (`BiGenAux.hPart_winPart_le`), applies the chain-rule bound
(`BiGenChain.hPart_le_hPart_add_Hcond`), and lets `l → ∞`, where the past σ-algebra of the window
exhausts the ambient σ-algebra (`BiGenSup.iSup_comap_winPart_eq`) while the conditional entropy
tends to `0` (`BiGenAux.HcondFam_tendsto`).
-/

set_option linter.unusedSectionVars false

open MeasureTheory Filter Topology
open scoped ENNReal BigOperators

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract

/-- `partSigma P ≤ mX` for a finite partition `P`. -/
theorem partSigma_le_mX' {X : Type*} [mX : MeasurableSpace X] (P : @FinPart X mX) :
    @partSigma X mX P ≤ mX := by
  rw [partSigma]
  refine MeasurableSpace.generateFrom_le ?_
  rintro s ⟨i, rfl⟩
  exact P.measurable i

/-- Monotonicity of the window σ-algebra along a refining sequence. -/
theorem partSigma_winPart_mono {X : Type*} [mX : MeasurableSpace X]
    (Tinv : X → X) (hTinv : Measurable Tinv) (G : ℕ → @FinPart X mX)
    (hGmono : ∀ l, @partSigma X mX (G l) ≤ @partSigma X mX (G (l + 1))) (l : ℕ) :
    @partSigma X mX (@BiGenAux.winPart X mX Tinv hTinv (G l) l)
      ≤ @partSigma X mX (@BiGenAux.winPart X mX Tinv hTinv (G (l + 1)) (l + 1)) := by
  rw [BiGenAux.partSigma_winPart, BiGenAux.partSigma_winPart]
  refine iSup_le fun i => ?_
  refine le_trans (MeasurableSpace.comap_mono (hGmono l)) ?_
  exact le_iSup (fun i' : Fin (l + 1) =>
      MeasurableSpace.comap (Tinv^[(i' : ℕ) + 1]) (@partSigma X mX (G (l + 1))))
    ⟨(i : ℕ), by have := i.isLt; omega⟩

theorem ent_eq_iSup_hPart_of_biGen {X : Type*} [mX : MeasurableSpace X]
    (μ : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure μ] (T Tinv : X → X)
    (hinv : Function.LeftInverse Tinv T)
    (hmp : MeasureTheory.MeasurePreserving T μ μ)
    (hTinv : Measurable Tinv)
    (𝒮 : MeasurableSpace X)
    (hbil : (⨆ n : ℕ, MeasurableSpace.comap (T^[n]) 𝒮 ⊔
        MeasurableSpace.comap (Tinv^[n]) 𝒮) = mX)
    (G : ℕ → @Work.EKLContract.FinPart X mX)
    (hGmono : ∀ l, @Work.EKLContract.partSigma X mX (G l) ≤
      @Work.EKLContract.partSigma X mX (G (l + 1)))
    (hGgen : (⨆ l, @Work.EKLContract.partSigma X mX (G l)) = 𝒮) :
    @Work.EKLContract.ent X mX μ T
      = ⨆ l, ENNReal.ofReal (@Work.EKLContract.hPart X mX μ T (G l)) := by
  letI : MeasurableSpace X := mX
  have hT : Measurable T := hmp.measurable
  refine le_antisymm ?_ ?_
  · show (⨆ Q : @FinPart X mX, ENNReal.ofReal (@hPart X mX μ T Q)) ≤
      (⨆ l, ENNReal.ofReal (@hPart X mX μ T (G l)))
    refine iSup_le fun Q => ?_
    -- the two-sided window attached to `G l`
    set W : ℕ → @FinPart X mX := fun l => @BiGenAux.winPart X mX Tinv hTinv (G l) l with hW
    set A : ℕ → MeasurableSpace X := fun l =>
      ⨆ n : ℕ, MeasurableSpace.comap (T^[n]) (@partSigma X mX (W l)) with hA
    have hWstep : ∀ l, @partSigma X mX (W l) ≤ @partSigma X mX (W (l + 1)) := by
      intro l
      rw [hW]
      exact partSigma_winPart_mono Tinv hTinv G hGmono l
    have hWmono : ∀ l l', l ≤ l' → @partSigma X mX (W l) ≤ @partSigma X mX (W l') := by
      intro l l' hll'
      exact Nat.le_induction le_rfl (fun n _ ih => le_trans ih (hWstep n)) l' hll'
    have hAmono : Monotone A := by
      intro l l' hll'
      refine iSup_le fun n => ?_
      exact le_trans (MeasurableSpace.comap_mono (hWmono l l' hll'))
        (le_iSup (fun n' : ℕ => MeasurableSpace.comap (T^[n']) (@partSigma X mX (W l'))) n)
    have hAle : ∀ l, A l ≤ mX := by
      intro l
      refine iSup_le fun n => ?_
      exact le_trans (MeasurableSpace.comap_mono (partSigma_le_mX' (W l)))
        ((hT.iterate n).comap_le)
    have hAsup : (⨆ l : ℕ, A l) = mX := by
      rw [hA, hW]
      exact BiGenSup.iSup_comap_winPart_eq T Tinv hinv hTinv 𝒮 G hGmono hGgen hbil
    -- the conditional entropy of `Q` against `A l` tends to `0`
    have hconv : ∀ ε : ℝ, 0 < ε → ∃ l : ℕ, @Hcond X mX μ Q (A l) ≤ ε := by
      intro ε hε
      have htend := BiGenAux.HcondFam_tendsto μ Q.parts A hAmono hAle
      have htop : @Hcond X mX μ Q mX ≤ 0 := BiGenAux.Hcond_top_le_zero μ Q
      have htop' : Work.EKLComp.Core.HcondFam X μ Q.parts (⨆ l : ℕ, A l) ≤ 0 := by
        rw [hAsup, Work.EKLComp.Core.HcondFam_eq_Hcond]
        exact htop
      obtain ⟨l, hl⟩ := Filter.eventually_atTop.1
        (htend.eventually (isOpen_Iio.mem_nhds (lt_of_le_of_lt htop' hε)))
      refine ⟨l, ?_⟩
      have hb := hl l le_rfl
      have heq : Work.EKLComp.Core.HcondFam X μ Q.parts (A l) = @Hcond X mX μ Q (A l) :=
        Work.EKLComp.Core.HcondFam_eq_Hcond μ Q (A l)
      rw [heq] at hb
      exact le_of_lt hb
    -- the chain-rule bound
    have hmain : ∀ l : ℕ,
        @hPart X mX μ T Q ≤ @hPart X mX μ T (G l) + @Hcond X mX μ Q (A l) := by
      intro l
      have h1 := BiGenChain.hPart_le_hPart_add_Hcond μ hmp (W l) Q
      have hAl : A l = ⨆ n : ℕ, MeasurableSpace.comap (T^[n]) (@partSigma X mX (W l)) := by
        rw [hA]
      rw [hAl]
      have h2 := BiGenAux.hPart_winPart_le μ hinv hmp hTinv (G l) l
      linarith [h1, h2]
    -- conclude
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    obtain ⟨l, hl⟩ := hconv (ε : ℝ) (by exact_mod_cast hε)
    have hGl0 : (0 : ℝ) ≤ @hPart X mX μ T (G l) := Work.EKLComp.Core.hPart_nonneg μ T (G l)
    have hε0 : (0 : ℝ) ≤ (ε : ℝ) := by positivity
    calc ENNReal.ofReal (@hPart X mX μ T Q)
        ≤ ENNReal.ofReal (@hPart X mX μ T (G l) + ((ε : ℝ))) := by
          refine ENNReal.ofReal_le_ofReal ?_
          linarith [hmain l, hl]
      _ = ENNReal.ofReal (@hPart X mX μ T (G l)) + ENNReal.ofReal ((ε : ℝ)) :=
          ENNReal.ofReal_add hGl0 hε0
      _ = ENNReal.ofReal (@hPart X mX μ T (G l)) + (ε : ℝ≥0∞) := by
          rw [ENNReal.ofReal_coe_nnreal]
      _ ≤ (⨆ l, ENNReal.ofReal (@hPart X mX μ T (G l))) + (ε : ℝ≥0∞) :=
          add_le_add (le_iSup (fun l => ENNReal.ofReal (@hPart X mX μ T (G l))) l) le_rfl
  · show (⨆ l, ENNReal.ofReal (@hPart X mX μ T (G l))) ≤
      (⨆ Q : @FinPart X mX, ENNReal.ofReal (@hPart X mX μ T Q))
    exact iSup_le fun l =>
      le_iSup (fun Q : @FinPart X mX => ENNReal.ofReal (@hPart X mX μ T Q)) (G l)

end Work.EKLC6Core
