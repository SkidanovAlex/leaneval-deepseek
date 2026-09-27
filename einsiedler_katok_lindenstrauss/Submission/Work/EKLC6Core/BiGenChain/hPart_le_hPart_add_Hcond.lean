import Mathlib
import Submission.Work.EKLComp.Core
import Submission.Work.EKLComp.Entropy
import Submission.Work.EKLComp.Hcond
import Submission.Work.EKLC6Core.Hcond_mono
import Submission.Work.EKLC6Core.HcondFam_partSigmaFam
import Submission.Work.EKLC6Core.BiGenChain.Basic
import Submission.Work.EKLC6Core.BiGenChain.HcondFam_join_chain
import Submission.Work.EKLComp.hPart_eq_Hcond_past

open MeasureTheory Filter Topology
open scoped ENNReal BigOperators

noncomputable section

namespace Work.EKLC6Core.BiGenChain

open Work.EKLContract
open Work.EKLComp.Core

variable {X : Type*} [mX : MeasurableSpace X]

/-- **Step bound.**  For `M ≥ 1`, the conditional entropy of the `M`-fold join of `Q` against the
`M`-fold window of `P` is at most the sum, over `l < M`, of the conditional entropies of `Q`
against the `(l+1)`-fold windows of `P`.

The proof is the entropy chain rule (`HcondFam_join_chain`) applied to the splitting of the join at
its first letter (`HcondFam_joinSets_append`), together with the invariance of the conditional
entropy under the measure-preserving pullback (`HcondFam_comap_preimage_gen`). -/
theorem HcondFam_joinSets_le_sum (μ : Measure X) [IsProbabilityMeasure μ] {T : X → X}
    (hmp : MeasurePreserving T μ μ) (P Q : FinPart X) (M : ℕ) (hM : 1 ≤ M) :
    HcondFam X μ (joinSets T Q M) (partSigmaFam (joinSets T P M))
      ≤ ∑ l ∈ Finset.range M,
          HcondFam X μ Q.parts (partSigmaFam (joinSets T P (l + 1))) := by
  have hT : Measurable T := hmp.measurable
  revert hM
  induction M with
  | zero => intro hM; omega
  | succ N ih =>
    intro hN1
    rcases Nat.eq_zero_or_pos N with hN | hN
    · -- `M = 1`: reindex the one-letter join
      subst hN
      rw [Finset.sum_range_one]
      have hJ1 : (joinSets T Q 1) = fun v : Fin 1 → Fin Q.n => Q.parts (fin1Equiv Q.n v) := by
        funext v
        rw [joinSets_one]
        rfl
      rw [hJ1, HcondFam_equiv_gen (partSigmaFam (joinSets T P 1)) μ (fin1Equiv Q.n) Q.parts]
    · -- `M = N + 1` with `N ≥ 1`: split off the first letter
      have ihN := ih hN
      have hsplit := HcondFam_joinSets_append (mX := mX) μ T Q
        (B := joinSets T P (N + 1)) 1 N
      have hstep1 : HcondFam X μ (joinSets T Q 1) (partSigmaFam (joinSets T P (N + 1)))
          = HcondFam X μ Q.parts (partSigmaFam (joinSets T P (N + 1))) := by
        have hJ1 : (joinSets T Q 1) = fun v : Fin 1 → Fin Q.n => Q.parts (fin1Equiv Q.n v) := by
          funext v
          rw [joinSets_one]
          rfl
        rw [hJ1, HcondFam_equiv_gen (partSigmaFam (joinSets T P (N + 1))) μ (fin1Equiv Q.n)
          Q.parts]
      have hstep2 : HcondFam X μ
            (fun v : Fin N → Fin Q.n => T ⁻¹' joinSets T Q N v)
            (partSigmaFam (joinSets T P (N + 1)))
          ≤ HcondFam X μ (joinSets T Q N) (partSigmaFam (joinSets T P N)) := by
        have h1 : HcondFam X μ (fun v : Fin N → Fin Q.n => T ⁻¹' joinSets T Q N v)
              (partSigmaFam (joinSets T P (N + 1)))
            ≤ HcondFam X μ (fun v : Fin N → Fin Q.n => T ⁻¹' joinSets T Q N v)
              (MeasurableSpace.comap T (partSigmaFam (joinSets T P N))) :=
          HcondFam_mono_gen (m₁ := MeasurableSpace.comap T (partSigmaFam (joinSets T P N)))
            (m₂ := partSigmaFam (joinSets T P (N + 1))) μ
            (fun v : Fin N → Fin Q.n => T ⁻¹' joinSets T Q N v)
            (fun v => (joinSets_measurable hT Q N v).preimage hT)
            (comap_partSigmaFam_joinSets_le T P N)
            (partSigmaFam_le_mX _ (joinSets_measurable hT P (N + 1)))
        have h2 : HcondFam X μ (fun v : Fin N → Fin Q.n => T ⁻¹' joinSets T Q N v)
              (MeasurableSpace.comap T (partSigmaFam (joinSets T P N)))
            = HcondFam X μ (joinSets T Q N) (partSigmaFam (joinSets T P N)) := by
          rw [comap_partSigmaFam T (joinSets T P N)]
          exact HcondFam_comap_preimage_gen μ hmp (joinSets_isMPart hT Q N)
            (joinSets_isMPart hT P N)
        exact h1.trans (le_of_eq h2)
      have hchain := HcondFam_join_chain (mX := mX) μ
        (A := joinSets T Q 1) (C := fun v : Fin N → Fin Q.n => T ⁻¹' joinSets T Q N v)
        (B := joinSets T P (N + 1)) (joinSets_isMPart hT Q 1)
        (isMPart_preimage (joinSets_isMPart hT Q N) hT) (joinSets_isMPart hT P (N + 1))
      rw [Finset.sum_range_succ]
      calc HcondFam X μ (joinSets T Q (N + 1)) (partSigmaFam (joinSets T P (N + 1)))
          = HcondFam X μ (joinSets T Q (1 + N)) (partSigmaFam (joinSets T P (N + 1))) := by
            rw [Nat.add_comm]
        _ = HcondFam X μ (fun q : (Fin 1 → Fin Q.n) × (Fin N → Fin Q.n) =>
              joinSets T Q 1 q.1 ∩ T^[1] ⁻¹' joinSets T Q N q.2)
              (partSigmaFam (joinSets T P (N + 1))) := hsplit
        _ = HcondFam X μ (joinSets T Q 1) (partSigmaFam (joinSets T P (N + 1)))
            + HcondFam X μ (fun v : Fin N → Fin Q.n => T ⁻¹' joinSets T Q N v)
              (partSigmaFam (joinSets T P (N + 1))
                ⊔ partSigmaFam (joinSets T Q 1)) := hchain
        _ ≤ HcondFam X μ (joinSets T Q 1) (partSigmaFam (joinSets T P (N + 1)))
            + HcondFam X μ (fun v : Fin N → Fin Q.n => T ⁻¹' joinSets T Q N v)
              (partSigmaFam (joinSets T P (N + 1))) := by
            refine add_le_add le_rfl ?_
            refine HcondFam_mono_gen (mX := mX) (m₁ := partSigmaFam (joinSets T P (N + 1)))
              (m₂ := partSigmaFam (joinSets T P (N + 1)) ⊔ partSigmaFam (joinSets T Q 1)) μ
              (fun v : Fin N → Fin Q.n => T ⁻¹' joinSets T Q N v)
              (fun v => (joinSets_measurable hT Q N v).preimage hT) le_sup_left ?_
            exact sup_le (partSigmaFam_le_mX _ (joinSets_measurable hT P (N + 1)))
              (partSigmaFam_le_mX _ (joinSets_measurable hT Q 1))
        _ ≤ HcondFam X μ Q.parts (partSigmaFam (joinSets T P (N + 1)))
            + HcondFam X μ (joinSets T Q N) (partSigmaFam (joinSets T P N)) :=
            add_le_add (le_of_eq hstep1) hstep2
        _ ≤ HcondFam X μ Q.parts (partSigmaFam (joinSets T P (N + 1)))
            + ∑ l ∈ Finset.range N,
              HcondFam X μ Q.parts (partSigmaFam (joinSets T P (l + 1))) :=
            add_le_add le_rfl ihN
        _ = ∑ l ∈ Finset.range N,
              HcondFam X μ Q.parts (partSigmaFam (joinSets T P (l + 1)))
            + HcondFam X μ Q.parts (partSigmaFam (joinSets T P (N + 1))) := add_comm _ _

theorem hPart_le_hPart_add_Hcond {X : Type*} [mX : MeasurableSpace X]
    (μ : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure μ]
    {T : X → X} (hmp : MeasureTheory.MeasurePreserving T μ μ)
    (P Q : @Work.EKLContract.FinPart X mX) :
    @Work.EKLContract.hPart X mX μ T Q
      ≤ @Work.EKLContract.hPart X mX μ T P
        + @Work.EKLContract.Hcond X mX μ Q
            (⨆ n : ℕ, MeasurableSpace.comap (T^[n]) (@Work.EKLContract.partSigma X mX P)) := by
  have hT : Measurable T := hmp.measurable
  -- the orbit σ-algebra
  set 𝓐 : MeasurableSpace X := ⨆ n : ℕ, MeasurableSpace.comap (T^[n]) (partSigma P) with h𝓐
  -- the local `𝓐` is an instance candidate for `MeasurableSpace X`; re-declare the ambient
  -- instance so that it stays preferred by typeclass search
  letI : MeasurableSpace X := mX
  have h𝓐le : 𝓐 ≤ mX := by
    rw [h𝓐]
    exact iSup_le fun n =>
      (MeasurableSpace.comap_mono (partSigma_le_mX P)).trans ((hT.iterate n).comap_le)
  -- the windows `⋁_{k<l} T^{-k}(partSigma P)`
  have hwinle : ∀ l : ℕ, partSigmaFam (joinSets T P l) ≤ mX :=
    fun l => partSigmaFam_le_mX _ (joinSets_measurable hT P l)
  have hwinmono : Monotone (fun l : ℕ => partSigmaFam (joinSets T P l)) := by
    intro l l' hll'
    change MeasurableSpace.generateFrom (Set.range (joinSets T P l))
      ≤ MeasurableSpace.generateFrom (Set.range (joinSets T P l'))
    rw [Work.EKLComp.HPartSigma.partSigma_joinSets T P l,
      Work.EKLComp.HPartSigma.partSigma_joinSets T P l']
    exact iSup_le fun k => le_iSup_of_le (Fin.castLE hll' k) le_rfl
  have hwinsup : (⨆ l : ℕ, partSigmaFam (joinSets T P l)) = 𝓐 := by
    refine le_antisymm ?_ ?_
    · refine iSup_le fun l => partSigmaFam_joinSets_le_iSup T P l
    · rw [h𝓐]
      refine iSup_le fun n => ?_
      exact (Work.EKLComp.HPartSigma.le_partSigma_joinSets T P n).trans
        (iSup_le fun N => le_iSup (fun l : ℕ => partSigmaFam (joinSets T P l)) N)
  -- the conditional entropies against the windows
  have hcc_tendsto : Tendsto (fun l : ℕ =>
        HcondFam X μ Q.parts (partSigmaFam (joinSets T P (l + 1)))) atTop
      (nhds (HcondFam X μ Q.parts 𝓐)) := by
    have h := Work.EKLGen.tendsto_Hcond_iSup_univ (mX := mX) μ Q
      (fun l : ℕ => partSigmaFam (joinSets T P (l + 1)))
      (fun l l' hll' => hwinmono (Nat.succ_le_succ hll'))
      (fun l => hwinle (l + 1))
    have hsup : (⨆ l : ℕ, partSigmaFam (joinSets T P (l + 1)))
        = (⨆ l : ℕ, partSigmaFam (joinSets T P l)) := by
      refine le_antisymm
        (iSup_le fun l => le_iSup (fun l : ℕ => partSigmaFam (joinSets T P l)) (l + 1))
        (iSup_le fun l => ?_)
      rcases Nat.eq_zero_or_pos l with hl | hl
      · subst hl
        exact (hwinmono (Nat.zero_le 1)).trans
          (le_iSup (fun l : ℕ => partSigmaFam (joinSets T P (l + 1))) 0)
      · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hl)
        exact le_iSup (fun l : ℕ => partSigmaFam (joinSets T P (l + 1))) k
    rw [hsup, hwinsup] at h
    exact h
  -- Fekete's lemma for the entropy of the joins of `P`
  have hlimP : Tendsto (fun M : ℕ => Hfam μ (joinSets T P M) / (M : ℝ)) atTop
      (nhds (hPart μ T P)) := by
    have hsub : Subadditive (fun N : ℕ => Hfam μ (joinSets T P N)) :=
      fun m n => Hfam_joinSets_add_le μ hmp P m n
    have hbdd : BddBelow (Set.range fun n : ℕ => Hfam μ (joinSets T P n) / (n : ℝ)) :=
      ⟨0, by rintro _ ⟨n, rfl⟩; exact div_nonneg (Hfam_nonneg μ _) (Nat.cast_nonneg n)⟩
    have hlim := hsub.tendsto_lim hbdd
    rw [Work.EKLComp.Core.hPart_eq_lim μ hmp P hsub]
    exact hlim
  -- Cesàro averages of the conditional entropies
  have hlimC : Tendsto (fun M : ℕ => (∑ l ∈ Finset.range M,
        HcondFam X μ Q.parts (partSigmaFam (joinSets T P (l + 1)))) / (M : ℝ)) atTop
      (nhds (HcondFam X μ Q.parts 𝓐)) := by
    have h := hcc_tendsto.cesaro
    simpa only [div_eq_mul_inv, mul_comm] using h
  -- the per-`M` inequality
  have hkey : ∀ M : ℕ, 1 ≤ M → @hPart X mX μ T Q
      ≤ Hfam μ (joinSets T P M) / (M : ℝ)
        + (∑ l ∈ Finset.range M,
            HcondFam X μ Q.parts (partSigmaFam (joinSets T P (l + 1)))) / (M : ℝ) := by
    intro M hM
    have hMpos : (0 : ℝ) < (M : ℝ) := by positivity
    have h1 : @hPart X mX μ T Q ≤ Hfam μ (joinSets T Q M) / (M : ℝ) := by
      have h := hPart_le_avg μ T Q (M - 1)
      have hcast : ((M - 1 : ℕ) : ℝ) + 1 = (M : ℝ) := by
        rw [Nat.cast_sub hM, Nat.cast_one]; ring
      rwa [Nat.sub_add_cancel hM, hcast] at h
    have h2 : Hfam μ (joinSets T Q M) ≤ Hfam μ (joinSets T P M)
        + ∑ l ∈ Finset.range M,
            HcondFam X μ Q.parts (partSigmaFam (joinSets T P (l + 1))) := by
      have ha := Hfam_le_Hfam_add_HcondFam μ hT Q (joinSets_isMPart hT P M) M
      have hb := HcondFam_joinSets_le_sum μ hmp P Q M hM
      linarith
    calc @hPart X mX μ T Q ≤ Hfam μ (joinSets T Q M) / (M : ℝ) := h1
      _ ≤ (Hfam μ (joinSets T P M)
            + ∑ l ∈ Finset.range M,
                HcondFam X μ Q.parts (partSigmaFam (joinSets T P (l + 1)))) / (M : ℝ) :=
          div_le_div_of_nonneg_right h2 (le_of_lt hMpos)
      _ = Hfam μ (joinSets T P M) / (M : ℝ)
            + (∑ l ∈ Finset.range M,
                HcondFam X μ Q.parts (partSigmaFam (joinSets T P (l + 1)))) / (M : ℝ) := by
          rw [add_div]
  have hlim := hlimP.add hlimC
  have hfin := le_of_tendsto_of_tendsto tendsto_const_nhds hlim
    (eventually_atTop.mpr ⟨1, hkey⟩)
  exact hfin

end Work.EKLC6Core.BiGenChain
