import Mathlib
import Submission.Work.EKLComp.EntJacobsAux
import Submission.Work.EKLComp.Entropy
import Submission.Work.EKLComp.Hpart.Hfam_join_chain
import Submission.Work.EKLComp.Hpart.tendsto_Hcond_iSup
import Submission.Work.EKLC6Core.Hcond_mono
import Submission.Work.EKLComp.tendsto_hPart
import Submission.Work.EKLEntJacobs.condJoin_subadditive
import Submission.Work.EKLEntJacobs.condEnt_finPart_approx

/-!
# `hPart μ T Q ≤ hPartCond μ T Q (invariants T)`

The entropy of a finite partition with respect to a measure-preserving transformation is at most
its conditional entropy with respect to the `T`-invariant σ-algebra.

The proof is the standard "conditioning on a finite partition" argument.  For a finite measurable
partition `B` whose parts are `T`-invariant:

* (chain rule, `Hfam_le_Hfam_add_HcondFam`) the entropy of the `N`-fold join of `Q` along `T` is at
  most `Hfam μ B + HcondFam μ (⋁_{k<N}T^{-k}Q) σ(B)`;
* the conditional entropies `N ↦ HcondFam μ (⋁_{k<N}T^{-k}Q) σ(B)` are subadditive, so that a block
  argument gives `hPart μ T Q ≤ HcondFam μ (⋁_{k<M}T^{-k}Q) σ(B) / M` for every `M ≥ 1`
  (`hPart_le_condEnt_div`);
* finitely generated sub-σ-algebras of an arbitrary σ-algebra `I` approximate the conditional
  entropy given `I` (`condEnt_finPart_approx`), so the infimum over `B` of the right hand side is
  at most `hPartCond μ T Q I`.
-/

open MeasureTheory Filter
open scoped BigOperators

noncomputable section

namespace Work.EKLEntJacobs

variable {X : Type} [mX : MeasurableSpace X]


/-! ### 1. Intersections of finite measurable partitions -/

theorem isMPart_prod {ι κ : Type} [Fintype ι] [Fintype κ] {A : ι → Set X} {B : κ → Set X}
    (hA : Work.EKLComp.Core.IsMPart A) (hB : Work.EKLComp.Core.IsMPart B) :
    Work.EKLComp.Core.IsMPart (fun p : ι × κ => A p.1 ∩ B p.2) := by
  refine ⟨fun p => (hA.measurable p.1).inter (hB.measurable p.2), ?_, ?_⟩
  · rintro ⟨i, k⟩ ⟨i', k'⟩ hne
    rcases eq_or_ne i i' with rfl | hi
    · rcases eq_or_ne k k' with rfl | hk
      · exact absurd rfl hne
      · exact (hB.disjoint hk).mono Set.inter_subset_right Set.inter_subset_right
    · exact (hA.disjoint hi).mono Set.inter_subset_left Set.inter_subset_left
  · rw [Set.eq_univ_iff_forall]
    intro x
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (by rw [hA.cover]; trivial : x ∈ ⋃ i, A i)
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp (by rw [hB.cover]; trivial : x ∈ ⋃ k, B k)
    exact Set.mem_iUnion.mpr ⟨(i, k), ⟨hi, hk⟩⟩

/-! ### 2. The entropy chain rule in the form used below -/

theorem Hfam_prod_eq (μ : Measure X) [IsProbabilityMeasure μ]
    {ι κ : Type} [Fintype ι] [Fintype κ] {A : ι → Set X} {B : κ → Set X}
    (hA : Work.EKLComp.Core.IsMPart A) (hB : Work.EKLComp.Core.IsMPart B) :
    Work.EKLContract.Hfam μ (fun p : ι × κ => A p.1 ∩ B p.2)
      = Work.EKLContract.Hfam μ B
        + Work.EKLComp.Core.HcondFam X μ A (Work.EKLComp.Core.partSigmaFam B) := by
  have h := Work.EKLComp.Hpart.Hfam_join_chain_general μ hA hB
  have hsum : (∑ p : ι × κ, Real.negMulLog ((μ (A p.1 ∩ B p.2)).toReal))
      = ∑ q : κ × ι, Real.negMulLog ((μ (A q.2 ∩ B q.1)).toReal) :=
    Equiv.sum_comp (Equiv.prodComm ι κ)
      (fun q : κ × ι => Real.negMulLog ((μ (A q.2 ∩ B q.1)).toReal))
  have hcomm : Work.EKLContract.Hfam μ (fun p : ι × κ => A p.1 ∩ B p.2)
      = Work.EKLContract.Hfam μ (fun p : κ × ι => B p.1 ∩ A p.2) := by
    simp only [Work.EKLContract.Hfam]
    rw [hsum]
    exact Finset.sum_congr rfl fun q _ => by rw [Set.inter_comm]
  exact hcomm.trans h

theorem Hfam_le_Hfam_add_HcondFam (μ : Measure X) [IsProbabilityMeasure μ]
    {T : X → X} (hT : Measurable T) (Q : Work.EKLContract.FinPart X)
    {κ : Type} [Fintype κ] {B : κ → Set X} (hB : Work.EKLComp.Core.IsMPart B) (N : ℕ) :
    Work.EKLContract.Hfam μ (Work.EKLContract.joinSets T Q N)
      ≤ Work.EKLContract.Hfam μ B
        + Work.EKLComp.Core.HcondFam X μ (Work.EKLContract.joinSets T Q N)
            (Work.EKLComp.Core.partSigmaFam B) := by
  have hA : Work.EKLComp.Core.IsMPart (Work.EKLContract.joinSets T Q N) :=
    Work.EKLComp.Core.joinSets_isMPart hT Q N
  have h1 := Work.EKLComp.Core.Hfam_mono μ hA (isMPart_prod hA hB)
    (fun p : (Fin N → Fin Q.n) × κ => p.1) (fun p => Set.inter_subset_left)
  rw [Hfam_prod_eq μ hA hB] at h1
  exact h1

/-! ### 3. Block subadditivity -/

theorem subadditive_mul_le {c : ℕ → ℝ} (h : Subadditive c) (M : ℕ) :
    ∀ k : ℕ, 1 ≤ k → c (k * M) ≤ (k : ℝ) * c M := by
  intro k
  induction k with
  | zero => intro hk; omega
  | succ k ih =>
      intro hk
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · subst hk0
        simp
      · have ih' := ih hkpos
        have hle := h (k * M) M
        rw [Nat.succ_mul]
        push_cast
        linarith

/-! ### 4. From subadditivity of the conditional entropies to `hPart` -/

theorem hPart_le_condEnt_div (μ : Measure X) [IsProbabilityMeasure μ]
    {T : X → X} (hT : Measurable T) (Q : Work.EKLContract.FinPart X)
    {κ : Type} [Fintype κ] {B : κ → Set X} (hB : Work.EKLComp.Core.IsMPart B)
    (hsub : Subadditive (fun N : ℕ => Work.EKLComp.Core.HcondFam X μ
      (Work.EKLContract.joinSets T Q N) (Work.EKLComp.Core.partSigmaFam B)))
    {M : ℕ} (hM : 1 ≤ M) :
    Work.EKLContract.hPart μ T Q
      ≤ Work.EKLComp.Core.HcondFam X μ (Work.EKLContract.joinSets T Q M)
          (Work.EKLComp.Core.partSigmaFam B) / (M : ℝ) := by
  set c : ℕ → ℝ := fun N => Work.EKLComp.Core.HcondFam X μ
      (Work.EKLContract.joinSets T Q N) (Work.EKLComp.Core.partSigmaFam B) with hc
  have hsub' : Subadditive c := hsub
  have hMR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hpt : ∀ k : ℕ, 1 ≤ k → Work.EKLContract.hPart μ T Q
      ≤ (Work.EKLContract.Hfam μ B) / (k : ℝ) + c M / (M : ℝ) := by
    intro k hk
    have hkM : 1 ≤ k * M := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
    have hkMR : ((k * M : ℕ) : ℝ) = (k : ℝ) * (M : ℝ) := by push_cast; ring
    have h1 : Work.EKLContract.hPart μ T Q
        ≤ Work.EKLContract.Hfam μ (Work.EKLContract.joinSets T Q (k * M))
            / ((k : ℝ) * (M : ℝ)) := by
      have h := Work.EKLComp.Core.hPart_le_avg μ T Q (k * M - 1)
      have hidx : (k * M - 1) + 1 = k * M := Nat.sub_add_cancel hkM
      have hcast : ((k * M - 1 : ℕ) : ℝ) + 1 = (k : ℝ) * (M : ℝ) := by
        rw [Nat.cast_sub hkM, Nat.cast_one, hkMR]
        ring
      rw [hidx, hcast] at h
      exact h
    have h2 : Work.EKLContract.Hfam μ (Work.EKLContract.joinSets T Q (k * M))
        ≤ Work.EKLContract.Hfam μ B + c (k * M) :=
      Hfam_le_Hfam_add_HcondFam μ hT Q hB (k * M)
    have h3 : c (k * M) ≤ (k : ℝ) * c M := subadditive_mul_le hsub' M k hk
    have hA0 : 0 ≤ Work.EKLContract.Hfam μ B := Work.EKLComp.Core.Hfam_nonneg μ B
    have hnum : Work.EKLContract.Hfam μ (Work.EKLContract.joinSets T Q (k * M))
        ≤ Work.EKLContract.Hfam μ B + (k : ℝ) * c M := by linarith
    have hden : (0 : ℝ) < (k : ℝ) * (M : ℝ) := mul_pos hkR hMR
    have h6 : (Work.EKLContract.Hfam μ B + (k : ℝ) * c M) / ((k : ℝ) * (M : ℝ))
        = (Work.EKLContract.Hfam μ B) / ((k : ℝ) * (M : ℝ)) + c M / (M : ℝ) := by
      have hkne : (k : ℝ) ≠ 0 := ne_of_gt hkR
      rw [add_div, mul_div_mul_left _ _ hkne]
    have h7 : (Work.EKLContract.Hfam μ B) / ((k : ℝ) * (M : ℝ))
        ≤ (Work.EKLContract.Hfam μ B) / (k : ℝ) :=
      div_le_div_of_nonneg_left hA0 hkR (by
        have h1M : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
        calc (k : ℝ) = (k : ℝ) * 1 := by ring
          _ ≤ (k : ℝ) * (M : ℝ) := mul_le_mul_of_nonneg_left h1M (le_of_lt hkR))
    calc Work.EKLContract.hPart μ T Q
        ≤ Work.EKLContract.Hfam μ (Work.EKLContract.joinSets T Q (k * M))
            / ((k : ℝ) * (M : ℝ)) := h1
      _ ≤ (Work.EKLContract.Hfam μ B + (k : ℝ) * c M) / ((k : ℝ) * (M : ℝ)) :=
          div_le_div_of_nonneg_right hnum (le_of_lt hden)
      _ = (Work.EKLContract.Hfam μ B) / ((k : ℝ) * (M : ℝ)) + c M / (M : ℝ) := h6
      _ ≤ (Work.EKLContract.Hfam μ B) / (k : ℝ) + c M / (M : ℝ) := add_le_add h7 le_rfl
  have hlim : Tendsto (fun k : ℕ =>
      (Work.EKLContract.Hfam μ B) / (k : ℝ) + c M / (M : ℝ)) atTop (nhds (c M / (M : ℝ))) := by
    have h0 : Tendsto (fun k : ℕ => (Work.EKLContract.Hfam μ B) / (k : ℝ)) atTop (nhds 0) :=
      tendsto_const_div_atTop_nhds_zero_nat _
    simpa using h0.add tendsto_const_nhds
  exact ge_of_tendsto hlim (eventually_atTop.mpr ⟨1, fun k hk => hpt k hk⟩)

/-! ### 5. Assembly -/

theorem hPart_le_hPartCond_of (μ : Measure X) [IsProbabilityMeasure μ]
    (T : X → X) (hT : Measurable T) (Q : Work.EKLContract.FinPart X)
    (hsub_lemma : ∀ {κ : Type} [Fintype κ] {B : κ → Set X},
      Work.EKLComp.Core.IsMPart B → (∀ j, T ⁻¹' B j = B j) →
      Subadditive (fun N : ℕ => Work.EKLComp.Core.HcondFam X μ
        (Work.EKLContract.joinSets T Q N) (Work.EKLComp.Core.partSigmaFam B)))
    (happrox : ∀ {ι : Type} [Fintype ι] {A : ι → Set X}, Work.EKLComp.Core.IsMPart A →
      ∀ ε : ℝ, 0 < ε → ∃ (κ : Type) (_ : Fintype κ) (B : κ → Set X),
        (∀ j, @MeasurableSet X (MeasurableSpace.invariants T) (B j)) ∧
        Work.EKLComp.Core.IsMPart B ∧
        Work.EKLComp.Core.HcondFam X μ A (Work.EKLComp.Core.partSigmaFam B)
          ≤ Work.EKLComp.Core.HcondFam X μ A (MeasurableSpace.invariants T) + ε) :
    Work.EKLContract.hPart μ T Q
      ≤ Work.EKLComp.hPartCond μ T Q (MeasurableSpace.invariants T) := by
  rw [Work.EKLComp.hPartCond]
  refine le_ciInf fun N => ?_
  set M : ℕ := N + 1 with hMdef
  have hM : 1 ≤ M := by omega
  have hMR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hcast : ((N : ℝ) + 1) = (M : ℝ) := by rw [hMdef]; push_cast; ring
  rw [hcast]
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  have hA : Work.EKLComp.Core.IsMPart (Work.EKLContract.joinSets T Q M) :=
    Work.EKLComp.Core.joinSets_isMPart hT Q M
  obtain ⟨κ, hκ, B, hBI, hB, hle⟩ := happrox hA (δ * (M : ℝ)) (by positivity)
  have hinv : ∀ j, T ⁻¹' B j = B j := fun j =>
    (MeasurableSpace.measurableSet_invariants.mp (hBI j)).2
  have hsub := hsub_lemma hB hinv
  have hmain := hPart_le_condEnt_div μ hT Q hB hsub hM
  have h6 : (Work.EKLComp.Core.HcondFam X μ (Work.EKLContract.joinSets T Q M)
        (MeasurableSpace.invariants T) + δ * (M : ℝ)) / (M : ℝ)
      = Work.EKLComp.Core.HcondFam X μ (Work.EKLContract.joinSets T Q M)
          (MeasurableSpace.invariants T) / (M : ℝ) + δ := by
    have hMne : (M : ℝ) ≠ 0 := ne_of_gt hMR
    rw [add_div, mul_div_cancel_right₀ δ hMne]
  calc Work.EKLContract.hPart μ T Q
      ≤ Work.EKLComp.Core.HcondFam X μ (Work.EKLContract.joinSets T Q M)
          (Work.EKLComp.Core.partSigmaFam B) / (M : ℝ) := hmain
    _ ≤ (Work.EKLComp.Core.HcondFam X μ (Work.EKLContract.joinSets T Q M)
          (MeasurableSpace.invariants T) + δ * (M : ℝ)) / (M : ℝ) :=
        div_le_div_of_nonneg_right hle (le_of_lt hMR)
    _ = Work.EKLComp.Core.HcondFam X μ (Work.EKLContract.joinSets T Q M)
          (MeasurableSpace.invariants T) / (M : ℝ) + δ := h6


/-! ## The requested theorem -/

theorem hPart_le_hPartCond {X : Type} [mX : MeasurableSpace X] [StandardBorelSpace X]
    (μ : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure μ]
    (T : X → X) (hT : Measurable T) (hmp : MeasureTheory.MeasurePreserving T μ μ)
    (Q : Work.EKLContract.FinPart X) :
    Work.EKLContract.hPart μ T Q
      ≤ Work.EKLComp.hPartCond μ T Q (MeasurableSpace.invariants T) := by
  refine hPart_le_hPartCond_of μ T hT Q ?_ ?_
  · intro κ hκ B hB hinv
    exact condJoin_subadditive μ T hmp Q hB hinv
  · intro ι hι A hA ε hε
    exact condEnt_finPart_approx (I := MeasurableSpace.invariants T) μ
      (MeasurableSpace.invariants_le T) hA ε hε

end Work.EKLEntJacobs
