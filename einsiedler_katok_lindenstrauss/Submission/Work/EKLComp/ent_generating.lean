import Mathlib
import Submission.Work.EKLComp.Entropy
import Submission.Work.EKLComp.EntGenDefs
import Submission.Work.EKLComp.EntGenSmall

/-!
# C3 (E4) — the generating-sequence theorem for Kolmogorov–Sinai entropy

`ent μ T = ⨆ m, ENNReal.ofReal (hPart μ T (P m))` for an increasing sequence of finite
measurable partitions whose generated σ-algebras generate `mX`.

## Structure of the proof

Write `CH μ A B := Hfam μ (A ⊗ B) - Hfam μ A` for the *conditional entropy* of a (partition)
family `B` given a (partition) family `A`, where `A ⊗ B` is the product-indexed family of
intersections.

* `CH_prod_le` / `CH_le_of_join`: subadditivity in the second argument and monotonicity under
  refinement of the conditioning family; both are instances of Shannon's inequality
  (`Work.EKLComp.shannon`, proved in parallel).
* `CH_joinSets_le`: `CH(⋁_{k<N} T^{-k}P, ⋁_{k<N}T^{-k}Q) ≤ N·CH(P,Q)` (induction on `N`).
* Dividing by `N` and taking the infimum over `N` gives, for every finite partition `Q`,
  `hPart μ T Q ≤ hPart μ T P + CH μ P Q`.
* `CH_small`: if the atoms of `Q` are approximated by unions of atoms of `P` up to measure `ε`,
  then `CH μ P Q ≤ 2·Q.n·ε + 3·Q.n·√ε` (the per-atom scalar estimate
  `Work.EKLComp.negMulLog_sum_le_delta`, plus the fact that an element of `partSigma P` is a union
  of atoms, `Work.EKLComp.partSigma_eq_unions_atoms`).
* `Work.EKLComp.exists_measurable_approx`: measurable sets are approximated by members of the
  increasing σ-algebras `partSigma (P m)` (the union `⋃ m, partSigma (P m)` is a Boolean algebra
  generating `mX`).
* Assembly: for every finite partition `Q`, `hPart μ T Q ≤ ⨆ m, hPart μ T (P m)`, and the result
  follows by monotonicity of `ENNReal.ofReal`.

The lemmas `shannon`, `entropy_prod_le`, `partSigma_eq_unions_atoms`, `partSigma_mono_iterate`,
`exists_measurable_approx` and `negMulLog_sum_le_delta` are proved by colleagues in parallel, in
the files of the same names; the copies below are placeholders that are deleted once those land.
-/

open MeasureTheory
open scoped ENNReal BigOperators symmDiff
open Work.EKLContract

noncomputable section

set_option linter.unusedSectionVars false

namespace Work.EKLComp

/-! ## 2. Subadditivity and monotonicity of `CH` (instances of Shannon's inequality) -/

variable {X : Type} [mX : MeasurableSpace X]

/-- `CH` is subadditive in its second argument. -/
theorem CH_prod_le {ι κ ρ : Type*} [Fintype ι] [Fintype κ] [Fintype ρ] (μ : Measure X)
    [IsProbabilityMeasure μ] {A : ι → Set X} {B : κ → Set X} {C : ρ → Set X}
    (hA : Core.IsMPart A) (hB : Core.IsMPart B) (hC : Core.IsMPart C) :
    CH μ A (joinFam B C) ≤ CH μ A B + CH μ A C := by
  have hS := shannon μ hA hB hC
  have h1 : Hfam μ (fun q : ι × (κ × ρ) => A q.1 ∩ joinFam B C q.2)
      = Hfam μ (fun q : (ι × κ) × ρ => A q.1.1 ∩ B q.1.2 ∩ C q.2) := by
    rw [show (fun q : ι × (κ × ρ) => A q.1 ∩ joinFam B C q.2) = joinFam A (joinFam B C)
      from rfl]
    rw [← Core.Hfam_equiv μ (Equiv.prodAssoc ι κ ρ) (joinFam A (joinFam B C))]
    refine Hfam_congr μ (funext fun q => ?_)
    simp only [Equiv.prodAssoc_apply, joinFam_apply]
    rw [Set.inter_assoc]
  simp only [CH_eq]
  rw [h1]
  linarith

/-- Refining the conditioning family decreases the conditional entropy. -/
theorem CH_le_of_join {ι κ ρ : Type*} [Fintype ι] [Fintype κ] [Fintype ρ] (μ : Measure X)
    [IsProbabilityMeasure μ] {A : ι → Set X} {B : κ → Set X} {C : ρ → Set X}
    (hA : Core.IsMPart A) (hB : Core.IsMPart B) (hC : Core.IsMPart C) :
    CH μ (joinFam A C) B ≤ CH μ A B := by
  have hS := shannon μ hA hC hB
  have h1 : Hfam μ (fun q : (ι × ρ) × κ => joinFam A C q.1 ∩ B q.2)
      = Hfam μ (fun q : (ι × ρ) × κ => A q.1.1 ∩ C q.1.2 ∩ B q.2) := by
    refine Hfam_congr μ (funext fun q => ?_)
    rw [joinFam_apply]
  have h2 : Hfam μ (joinFam A C) = Hfam μ (fun q : ι × ρ => A q.1 ∩ C q.2) := by
    refine Hfam_congr μ (funext fun q => ?_)
    rw [joinFam_apply]
  simp only [CH_eq]
  rw [h1, h2]
  linarith

/-- The two orders of the product join give the same conditional entropy. -/
theorem CH_prodComm {ι κ ρ : Type*} [Fintype ι] [Fintype κ] [Fintype ρ] (μ : Measure X)
    {A : ι → Set X} {B : κ → Set X} {C : ρ → Set X} :
    CH μ (joinFam A C) B = CH μ (joinFam C A) B := by
  have h1 : Hfam μ (fun q : (ι × ρ) × κ => joinFam A C q.1 ∩ B q.2)
      = Hfam μ (fun q : (ρ × ι) × κ => joinFam C A q.1 ∩ B q.2) := by
    rw [← Core.Hfam_equiv μ (swap₂ ι ρ κ) (fun q : (ι × ρ) × κ => joinFam A C q.1 ∩ B q.2)]
    refine Hfam_congr μ (funext fun q => ?_)
    simp only [swap₂_apply, joinFam_apply]
    ext x
    simp only [Set.mem_inter_iff]
    tauto
  have h2 : Hfam μ (joinFam A C) = Hfam μ (joinFam C A) := by
    rw [← Core.Hfam_equiv μ (swapEquiv ρ ι) (joinFam C A)]
    refine Hfam_congr μ (funext fun q => ?_)
    simp only [swapEquiv_apply, joinFam_apply]
    exact Set.inter_comm _ _
  simp only [CH_eq]
  rw [h1, h2]

/-- Refining the conditioning family decreases the conditional entropy (join written first). -/
theorem CH_le_of_join' {ι κ ρ : Type*} [Fintype ι] [Fintype κ] [Fintype ρ] (μ : Measure X)
    [IsProbabilityMeasure μ] {A : ι → Set X} {B : κ → Set X} {C : ρ → Set X}
    (hA : Core.IsMPart A) (hB : Core.IsMPart B) (hC : Core.IsMPart C) :
    CH μ (joinFam C A) B ≤ CH μ A B := by
  rw [← CH_prodComm (μ := μ) (A := A) (B := B) (C := C)]
  exact CH_le_of_join μ hA hB hC

/-! ## 3. The pullback of a finite partition -/

/-- The conditional entropy of two pulled-back partitions is unchanged. -/
theorem CH_vpart (μ : Measure X) [IsProbabilityMeasure μ] {T : X → X}
    (hmp : MeasurePreserving T μ μ) (N : ℕ) (P Q : FinPart X) :
    CH μ (vpart T N P) (vpart T N Q) = CHp μ P Q := by
  have hpre : ∀ s : Set X, MeasurableSet s → μ ((T^[N]) ⁻¹' s) = μ s := fun s hs =>
    (hmp.iterate N).measure_preimage hs.nullMeasurableSet
  have h1 : Hfam μ (fun q : Fin P.n × Fin Q.n => vpart T N P q.1 ∩ vpart T N Q q.2)
      = Hfam μ (joinFam P.parts Q.parts) := by
    simp only [Hfam, joinFam_apply]
    refine Finset.sum_congr rfl fun q _ => ?_
    simp only [vpart_apply]
    rw [← Set.preimage_inter, hpre _ ((P.measurable q.1).inter (Q.measurable q.2))]
  have h2 : Hfam μ (vpart T N P) = Hfam μ P.parts := by
    simp only [Hfam, vpart_apply]
    exact Finset.sum_congr rfl fun i _ => by rw [hpre _ (P.measurable i)]
  simp only [CH_eq, CHp_eq]
  rw [h1, h2]

/-! ## 4. The recursion for the `N`-fold join -/

/-- One step of the join recursion. -/
theorem Hfam_joinSets_succ (μ : Measure X) (T : X → X) (P : FinPart X) (N : ℕ) :
    Hfam μ (joinFam (joinSets T P N) (vpart T N P)) = Hfam μ (joinSets T P (N + 1)) := by
  rw [← Core.Hfam_equiv μ (joinEquiv N P) (joinSets T P (N + 1))]
  refine Hfam_congr μ (funext fun q => ?_)
  simp only [joinFam_apply, vpart_apply, joinEquiv_apply]
  rw [Core.joinSets_append T P N 1 q.1 (fun _ => q.2), Core.joinSets_one]

/-- One step of the join recursion, for a pair of partitions. -/
theorem Hfam_joinFam_joinSets_succ (μ : Measure X) (T : X → X) (P Q : FinPart X) (N : ℕ) :
    Hfam μ (joinFam (joinSets T P (N + 1)) (joinSets T Q (N + 1)))
      = Hfam μ (joinFam (joinFam (joinSets T P N) (vpart T N P))
          (joinFam (joinSets T Q N) (vpart T N Q))) := by
  rw [← Core.Hfam_equiv μ (joinEquiv₂ N P Q)
    (joinFam (joinSets T P (N + 1)) (joinSets T Q (N + 1)))]
  refine Hfam_congr μ (funext fun q => ?_)
  simp only [joinEquiv₂_apply, joinFam_apply, vpart_apply, joinEquiv_apply]
  rw [Core.joinSets_append T P N 1 q.1.1 (fun _ => q.1.2),
      Core.joinSets_append T Q N 1 q.2.1 (fun _ => q.2.2), Core.joinSets_one, Core.joinSets_one]

/-- `CH` of the `N+1`-fold joins is `CH` of the `N`-fold joins joined with the last factor. -/
theorem CH_joinSets_succ (μ : Measure X) (T : X → X) (P Q : FinPart X) (N : ℕ) :
    CH μ (joinSets T P (N + 1)) (joinSets T Q (N + 1))
      = CH μ (joinFam (joinSets T P N) (vpart T N P))
          (joinFam (joinSets T Q N) (vpart T N Q)) := by
  show Hfam μ (joinFam (joinSets T P (N + 1)) (joinSets T Q (N + 1)))
      - Hfam μ (joinSets T P (N + 1))
    = Hfam μ (joinFam (joinFam (joinSets T P N) (vpart T N P))
        (joinFam (joinSets T Q N) (vpart T N Q)))
      - Hfam μ (joinFam (joinSets T P N) (vpart T N P))
  rw [Hfam_joinFam_joinSets_succ μ T P Q N, ← Hfam_joinSets_succ μ T P N]

/-! ## 5. The chain inequality `CH(⋁T^{-k}P, ⋁T^{-k}Q) ≤ N · CH(P,Q)` -/

theorem CH_joinSets_le (μ : Measure X) [IsProbabilityMeasure μ] {T : X → X}
    (hmp : MeasurePreserving T μ μ) (P Q : FinPart X) (N : ℕ) :
    CH μ (joinSets T P N) (joinSets T Q N) ≤ (N : ℝ) * CHp μ P Q := by
  have hT : Measurable T := hmp.measurable
  induction N with
  | zero =>
    have h1 : Hfam μ (joinSets T P 0) = 0 := by
      simp [Hfam, Core.joinSets_zero, measure_univ]
    have h2 : Hfam μ (fun q : (Fin 0 → Fin P.n) × (Fin 0 → Fin Q.n) =>
        joinSets T P 0 q.1 ∩ joinSets T Q 0 q.2) = 0 := by
      simp [Hfam, Core.joinSets_zero, measure_univ]
    rw [CH_eq, h1, h2]
    simp
  | succ N ih =>
    have hprod := CH_prod_le μ
      (isMPart_joinFam (Core.joinSets_isMPart hT P N) (isMPart_vpart hT N P))
      (Core.joinSets_isMPart hT Q N)
      (isMPart_vpart hT N Q)
    have hmono1 := CH_le_of_join μ (Core.joinSets_isMPart hT P N)
      (Core.joinSets_isMPart hT Q N) (isMPart_vpart hT N P)
    have hmono2 := CH_le_of_join' μ (isMPart_vpart hT N P) (isMPart_vpart hT N Q)
      (Core.joinSets_isMPart hT P N)
    have hstat := CH_vpart μ hmp N P Q
    rw [CH_joinSets_succ μ T P Q N]
    calc CH μ (joinFam (joinSets T P N) (vpart T N P))
            (joinFam (joinSets T Q N) (vpart T N Q))
        ≤ CH μ (joinFam (joinSets T P N) (vpart T N P)) (joinSets T Q N)
            + CH μ (joinFam (joinSets T P N) (vpart T N P)) (vpart T N Q) := hprod
      _ ≤ CH μ (joinSets T P N) (joinSets T Q N) + CH μ (vpart T N P) (vpart T N Q) :=
          add_le_add hmono1 hmono2
      _ ≤ (N : ℝ) * CHp μ P Q + CHp μ P Q := by linarith [ih, hstat]
      _ = ((N + 1 : ℕ) : ℝ) * CHp μ P Q := by push_cast; ring

/-! ## 6. From the chain to `hPart μ T Q ≤ hPart μ T P + CH(P,Q)` -/

theorem hPart_le_hPart_add_CHp (μ : Measure X) [IsProbabilityMeasure μ] {T : X → X}
    (hmp : MeasurePreserving T μ μ) (P Q : FinPart X) :
    hPart μ T Q ≤ hPart μ T P + CHp μ P Q := by
  have hT : Measurable T := hmp.measurable
  have hkey : ∀ N : ℕ, Hfam μ (joinSets T Q (N + 1))
      ≤ Hfam μ (joinSets T P (N + 1)) + ((N : ℝ) + 1) * CHp μ P Q := by
    intro N
    have h1 : Hfam μ (joinSets T Q (N + 1))
        ≤ Hfam μ (joinSets T P (N + 1)) + CH μ (joinSets T P (N + 1)) (joinSets T Q (N + 1)) :=
      Hfam_le_Hfam_add_CH μ (Core.joinSets_isMPart hT P (N + 1))
        (Core.joinSets_isMPart hT Q (N + 1))
    have h2 := CH_joinSets_le μ hmp P Q (N + 1)
    have h3 : ((N + 1 : ℕ) : ℝ) * CHp μ P Q = ((N : ℝ) + 1) * CHp μ P Q := by
      push_cast; ring
    linarith [h1, h2, h3]
  have hdiv : ∀ N : ℕ, Hfam μ (joinSets T Q (N + 1)) / ((N : ℝ) + 1)
      ≤ Hfam μ (joinSets T P (N + 1)) / ((N : ℝ) + 1) + CHp μ P Q := by
    intro N
    have hc : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    have h2 : (Hfam μ (joinSets T P (N + 1)) + ((N : ℝ) + 1) * CHp μ P Q) / ((N : ℝ) + 1)
        = Hfam μ (joinSets T P (N + 1)) / ((N : ℝ) + 1) + CHp μ P Q := by
      field_simp
    calc Hfam μ (joinSets T Q (N + 1)) / ((N : ℝ) + 1)
        ≤ (Hfam μ (joinSets T P (N + 1)) + ((N : ℝ) + 1) * CHp μ P Q) / ((N : ℝ) + 1) :=
          div_le_div_of_nonneg_right (hkey N) (le_of_lt hc)
      _ = _ := h2
  have hinf : hPart μ T Q - CHp μ P Q ≤ hPart μ T P := by
    show hPart μ T Q - CHp μ P Q
      ≤ ⨅ N : ℕ, Hfam μ (joinSets T P (N + 1)) / ((N : ℝ) + 1)
    refine le_ciInf fun N => ?_
    linarith [Core.hPart_le_avg μ T Q N, hdiv N]
  linarith


/-! ## 7. The generating theorem -/

/-- For every finite partition `Q`, `ENNReal.ofReal (hPart μ T Q)` is at most the (extended) sup of
the `ENNReal.ofReal (hPart μ T (P m))`. -/
theorem ofReal_hPart_le_iSup (μ : Measure X) [IsProbabilityMeasure μ] {T : X → X}
    (hmp : MeasurePreserving T μ μ) (P : ℕ → FinPart X)
    (hmono : ∀ m, Refines (P (m + 1)) (P m)) (hgen : (⨆ m, partSigma (P m)) = mX)
    (Q : FinPart X) :
    ENNReal.ofReal (hPart μ T Q) ≤ ⨆ m, ENNReal.ofReal (hPart μ T (P m)) := by
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hεr : (0 : ℝ) < (ε : ℝ) / 2 := by positivity
  obtain ⟨m, hm⟩ := CHp_small μ P hmono hgen Q ((ε : ℝ) / 2) hεr
  have hCH0 : 0 ≤ CHp μ (P m) Q := CH_nonneg μ (isMPart_parts (P m)) (isMPart_parts Q)
  have hP0 : 0 ≤ hPart μ T (P m) := Core.hPart_nonneg μ T (P m)
  have h2 : ENNReal.ofReal (CHp μ (P m) Q) ≤ (ε : ℝ≥0∞) := by
    refine le_trans (ENNReal.ofReal_le_ofReal hm) ?_
    rw [← ENNReal.ofReal_coe_nnreal]
    refine ENNReal.ofReal_le_ofReal ?_
    have : (0 : ℝ) < (ε : ℝ) := by positivity
    linarith
  calc ENNReal.ofReal (hPart μ T Q)
      ≤ ENNReal.ofReal (hPart μ T (P m) + CHp μ (P m) Q) :=
        ENNReal.ofReal_le_ofReal (hPart_le_hPart_add_CHp μ hmp (P m) Q)
    _ = ENNReal.ofReal (hPart μ T (P m)) + ENNReal.ofReal (CHp μ (P m) Q) :=
        ENNReal.ofReal_add hP0 hCH0
    _ ≤ (⨆ m, ENNReal.ofReal (hPart μ T (P m))) + (ε : ℝ≥0∞) :=
        add_le_add (le_iSup (fun m => ENNReal.ofReal (hPart μ T (P m))) m) h2

/-- **Kolmogorov–Sinai: a generating sequence computes the entropy.** -/
theorem ent_generating {X : Type} [mX : MeasurableSpace X] (μ : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure μ]
    (T : X → X) (hT : Measurable T) (hmp : MeasureTheory.MeasurePreserving T μ μ)
    (P : ℕ → Work.EKLContract.FinPart X)
    (hmono : ∀ m, Work.EKLContract.Refines (P (m+1)) (P m))
    (hgen : (⨆ m, Work.EKLContract.partSigma (P m)) = mX) :
    Work.EKLContract.ent μ T = ⨆ m, ENNReal.ofReal (Work.EKLContract.hPart μ T (P m)) := by
  refine le_antisymm ?_ ?_
  · show (⨆ Q : Work.EKLContract.FinPart X, ENNReal.ofReal (Work.EKLContract.hPart μ T Q)) ≤ _
    exact iSup_le fun Q => ofReal_hPart_le_iSup μ hmp P hmono hgen Q
  · show _ ≤ (⨆ Q : Work.EKLContract.FinPart X, ENNReal.ofReal (Work.EKLContract.hPart μ T Q))
    exact iSup_le fun m =>
      le_iSup (fun Q : Work.EKLContract.FinPart X => ENNReal.ofReal (Work.EKLContract.hPart μ T Q))
        (P m)

end Work.EKLComp
