import ChallengeDeps
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1B.tBdiagFormInd_slice_split_box
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1B.sbKin_slice_slotSplit` — the sliding kinetic word splits over the blocks

The FS grouping step (Step E of `thm:smallbox`) needs the sliding small-box kinetic word
`Work.BoseFixB1.sbKin μ M u` (= FS `eq:appTB`, the corpus's `Work.UBBInputs8.tBwordBInd`) to be a
**sum of one-slot forms over the particles** in the exact structural sense of
`Work.KinPSuperadd.SlotSplit`: for every block decomposition `N = N₁ + N₂` of the particle number,
a smooth state `Φ` on `X (N₁+N₂)` satisfies

    sbKin (N₁+N₂) Φ
      = ∫_{w ∈ abox N₂ ℓ} sbKin N₁ (fun u ↦ Φ (merge(u,w)))
        + ∫_{u ∈ abox N₁ ℓ} sbKin N₂ (fun w ↦ Φ (merge(u,w))) ,      ℓ = sideAt μ (a v),

together with the slice-integrability of both summands (which is what makes the two integrals
honest and the infimum step of the grouping argument legal).

## Route

`sbKin μ M u Φ = tbGapCoeff (ℓ·d) ε_T · cnPlusBoxInd ℓ B V Φ
                 + tBdiagFormInd ℓ B V χ_B (fsKinCoeff c) Φ` **by definition**
(`sbKin = tBwordBInd = tBwordInd`, with the spectral half `tBwordKinInd = tBdiagFormInd`), where
`ℓ = sideAt μ (a v)`, `d = (paramsAt μ (a v)).d`, `ε_T = (paramsAt μ (a v)).eT`,
`c = sbCut μ (a v)`, `B = dlBox ℓ d u`, `V = boxMass ℓ d u`, `χ_B = chiB ℓ d u`.  Both summands
are one-slot forms and therefore `SlotSplit`:

* **the count** (`cnPlusBoxInd = Σᵢ ∫ (Q_{B,i}Φ)²`): the block identity is
  `Work.BoseFixB1B.cns_split_gen`, and the slice integrability is obtained from the *big-box*
  integrability `cns_split_integrableOn_boxQInd_sq_gen` transported along the measure-preserving
  block split `aboxSplit_measurePreserving_restrict` and then integrated out
  (`Integrable.integral_prod_{left,right}`);
* **the spectral half** (`tBdiagFormInd`): the block identity is the PROVED
  `Work.BoseFixB1B.tBdiagFormInd_slice_split_box`, and the slice integrability is read off the
  joint `(p,w)`-integrability `Work.BoseFixB1B.tBdiagFormInd_blockIntegrand_integrable` in exactly
  the same way (the `p`-integral of the joint integrand is the slot functional of the slice).

The two halves are summed with `SlotSplit.const_mul` / `SlotSplit.add`, and the resulting word is
identified with `sbKin` pointwise by unfolding the definitions (`slotSplit_congr_word`).

The FS regime facts used are `0 < ℓ` and `0 < d` (`Work.BoseFixB1.adm_ell_pos`, `adm_d_pos`), the
measurability/boundedness of the sliding box `dlBox ℓ d u`
(`Work.SmallBoxSliding.measurableSet_dlBox`, `Work.BoseFixB1B.cns_split_dlBox_subset`), the
smoothness/compact support of the window (`Work.SmallBoxTBWord.contDiff_chiB`,
`hasCompactSupport_chiB`, `Submission.BoseGases.chiB_support_mem`) and the quadratic growth of the
symbol `fsKinCoeff c` (`abs_fsKinCoeff_le`).
-/

noncomputable section

open MeasureTheory
open scoped Real BigOperators ENNReal

namespace Work.BoseFixB1B

open _root_.BoseGases Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 0. Elementary facts about the symbol `[r−c]₊²` -/

/-- The FS spectral coefficient `[r−c]₊²` is continuous. -/
lemma measurable_fsKinCoeff (c : ℝ) : Measurable (Submission.BoseGases.fsKinCoeff c) := by
  have h : Submission.BoseGases.fsKinCoeff c = fun r : ℝ => (max (r - c) 0) ^ 2 := rfl
  rw [h]
  exact (((continuous_id.sub continuous_const).max continuous_const).pow 2).measurable

/-- The FS spectral coefficient obeys the quadratic growth bound `[r−c]₊² ≤ (1+r)²` on `r ≥ 0`
(which is the `K = 1`, `d = 2 < 3` hypothesis of the joint-integrability lemma).  The `c ≥ 0`
hypothesis is needed: for `c < −1` the coefficient is *not* dominated by `(1+r)²` at small `r`. -/
lemma abs_fsKinCoeff_le {c : ℝ} (hc : 0 ≤ c) :
    ∀ r : ℝ, 0 ≤ r → |Submission.BoseGases.fsKinCoeff c r| ≤ 1 * (1 + r) ^ 2 := by
  intro r hr
  have h1 : Submission.BoseGases.fsKinCoeff c r = (max (r - c) 0) ^ 2 := rfl
  have h2 : max (r - c) 0 ≤ r := max_le (by linarith) hr
  have h3 : 0 ≤ max (r - c) 0 := le_max_right _ _
  rw [h1, abs_of_nonneg (sq_nonneg _), one_mul]
  calc (max (r - c) 0) ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ h3 h2 2
    _ ≤ (1 + r) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2

/-! ## 1. `SlotSplit` transports along pointwise equal words -/

/-- `SlotSplit` is a pointwise property of the word: two words that agree on every state are
`SlotSplit` together. -/
lemma slotSplit_congr_word {s : ℝ} {K L : ∀ N : ℕ, (X N → ℝ) → ℝ}
    (h : Work.KinPSuperadd.SlotSplit s K) (hKL : ∀ (N : ℕ) (Φ : X N → ℝ), K N Φ = L N Φ) :
    Work.KinPSuperadd.SlotSplit s L := by
  refine ⟨?_, ?_, ?_⟩
  · intro N1 N2 Φ hΦ
    rw [← hKL (N1 + N2) Φ, h.split Φ hΦ]
    congr 1
    · apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun w => hKL N1 _)
    · apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun u => hKL N2 _)
  · intro N1 N2 Φ hΦ
    exact (h.int₁ Φ hΦ).congr (Filter.Eventually.of_forall (fun w => hKL N1 _))
  · intro N1 N2 Φ hΦ
    exact (h.int₂ Φ hΦ).congr (Filter.Eventually.of_forall (fun u => hKL N2 _))

/-! ## 2. The excited-count half: `cnPlusBoxInd` -/

/-- **First-block slice integrability of the box count.**  The `w`-slice integral of the excited
count of the first block is integrable over the box of the frozen block.  This is `SlotSplit.int₁`
for `cnPlusBoxInd`, and it is *not* a formal consequence of the block identity: it is obtained by
transporting the big-box integrability of each squared slot field along the measure-preserving
block split and then integrating out the `u`-variable. -/
lemma integrableOn_cnPlusBoxInd_slice_fst {N1 N2 : ℕ} {s V C : ℝ} (hs : 0 < s) {A : Set E3}
    (hA : MeasurableSet A) (hAc : A ⊆ Submission.BoseGases.acube s)
    {Φ : X (N1 + N2) → ℝ} (hΦm : Measurable Φ) (hC0 : 0 ≤ C)
    (hCb : ∀ x ∈ Submission.BoseGases.abox (N1 + N2) s, |Φ x| ≤ C) :
    IntegrableOn (fun w : X N2 => Work.UBBInputs8.cnPlusBoxInd s A V
      (fun u => Φ (Submission.BoseGases.mergeBlock N1 N2 (u, w))))
      (Submission.BoseGases.abox N2 s) := by
  have hterm : ∀ j : Fin N1, Integrable (fun w : X N2 =>
      ∫ u in Submission.BoseGases.abox N1 s,
        (Work.UBBInputs8.boxQInd V A j
          (fun u' => Φ (Submission.BoseGases.mergeBlock N1 N2 (u', w))) u) ^ 2)
      ((volume : Measure (X N2)).restrict (Submission.BoseGases.abox N2 s)) := by
    intro j
    have hGint : IntegrableOn (fun x : X (N1 + N2) =>
        (Work.UBBInputs8.boxQInd V A (Fin.castAdd N2 j) Φ x) ^ 2)
        (Submission.BoseGases.abox (N1 + N2) s) volume :=
      cns_split_integrableOn_boxQInd_sq_gen hs hA hAc hΦm hC0 hCb (Fin.castAdd N2 j)
    have hGe : Integrable (fun p : X N1 × X N2 =>
        (Work.UBBInputs8.boxQInd V A (Fin.castAdd N2 j) Φ
          (Submission.BoseGases.mergeBlock N1 N2 p)) ^ 2)
        ((volume.restrict (Submission.BoseGases.abox N1 s)).prod
          (volume.restrict (Submission.BoseGases.abox N2 s))) := by
      apply (Submission.BoseGases.aboxSplit_measurePreserving_restrict N1 N2 s
        |>.integrable_comp_emb (Submission.BoseGases.blockSplitEquiv N1 N2).measurableEmbedding).mp
      refine hGint.congr ?_
      filter_upwards with x
      simp [Function.comp_apply, Submission.BoseGases.blockSplitEquiv_apply,
        Submission.BoseGases.mergeBlock_eq]
    exact (hGe.integral_prod_right).congr
      (Filter.Eventually.of_forall (fun w => by
        apply integral_congr_ae
        filter_upwards with u
        rw [cns_split_boxQInd_merge_castAdd]))
  have hsum := integrable_finsetSum Finset.univ (fun j _ => hterm j)
  have hgoal : Integrable (fun w : X N2 => Work.UBBInputs8.cnPlusBoxInd s A V
      (fun u => Φ (Submission.BoseGases.mergeBlock N1 N2 (u, w))))
      ((volume : Measure (X N2)).restrict (Submission.BoseGases.abox N2 s)) := by
    simpa only [Work.UBBInputs8.cnPlusBoxInd] using hsum
  exact hgoal

/-- **Second-block slice integrability of the box count** (`SlotSplit.int₂` for `cnPlusBoxInd`). -/
lemma integrableOn_cnPlusBoxInd_slice_snd {N1 N2 : ℕ} {s V C : ℝ} (hs : 0 < s) {A : Set E3}
    (hA : MeasurableSet A) (hAc : A ⊆ Submission.BoseGases.acube s)
    {Φ : X (N1 + N2) → ℝ} (hΦm : Measurable Φ) (hC0 : 0 ≤ C)
    (hCb : ∀ x ∈ Submission.BoseGases.abox (N1 + N2) s, |Φ x| ≤ C) :
    IntegrableOn (fun u : X N1 => Work.UBBInputs8.cnPlusBoxInd s A V
      (fun w => Φ (Submission.BoseGases.mergeBlock N1 N2 (u, w))))
      (Submission.BoseGases.abox N1 s) := by
  have hterm : ∀ j : Fin N2, Integrable (fun u : X N1 =>
      ∫ w in Submission.BoseGases.abox N2 s,
        (Work.UBBInputs8.boxQInd V A j
          (fun w' => Φ (Submission.BoseGases.mergeBlock N1 N2 (u, w'))) w) ^ 2)
      ((volume : Measure (X N1)).restrict (Submission.BoseGases.abox N1 s)) := by
    intro j
    have hGint : IntegrableOn (fun x : X (N1 + N2) =>
        (Work.UBBInputs8.boxQInd V A (Fin.natAdd N1 j) Φ x) ^ 2)
        (Submission.BoseGases.abox (N1 + N2) s) volume :=
      cns_split_integrableOn_boxQInd_sq_gen hs hA hAc hΦm hC0 hCb (Fin.natAdd N1 j)
    have hGe : Integrable (fun p : X N1 × X N2 =>
        (Work.UBBInputs8.boxQInd V A (Fin.natAdd N1 j) Φ
          (Submission.BoseGases.mergeBlock N1 N2 p)) ^ 2)
        ((volume.restrict (Submission.BoseGases.abox N1 s)).prod
          (volume.restrict (Submission.BoseGases.abox N2 s))) := by
      apply (Submission.BoseGases.aboxSplit_measurePreserving_restrict N1 N2 s
        |>.integrable_comp_emb (Submission.BoseGases.blockSplitEquiv N1 N2).measurableEmbedding).mp
      refine hGint.congr ?_
      filter_upwards with x
      simp [Function.comp_apply, Submission.BoseGases.blockSplitEquiv_apply,
        Submission.BoseGases.mergeBlock_eq]
    exact (hGe.integral_prod_left).congr
      (Filter.Eventually.of_forall (fun u => by
        apply integral_congr_ae
        filter_upwards with w
        rw [cns_split_boxQInd_merge_natAdd]))
  have hsum := integrable_finsetSum Finset.univ (fun j _ => hterm j)
  have hgoal : Integrable (fun u : X N1 => Work.UBBInputs8.cnPlusBoxInd s A V
      (fun w => Φ (Submission.BoseGases.mergeBlock N1 N2 (u, w))))
      ((volume : Measure (X N1)).restrict (Submission.BoseGases.abox N1 s)) := by
    simpa only [Work.UBBInputs8.cnPlusBoxInd] using hsum
  exact hgoal

/-- **The box excited count is `SlotSplit`**: the block identity (`cns_split_gen`) plus the two
slice-integrabilities. -/
theorem slotSplit_cnPlusBoxInd {s V : ℝ} (hs : 0 < s) {A : Set E3} (hA : MeasurableSet A)
    (hAc : A ⊆ Submission.BoseGases.acube s) :
    Work.KinPSuperadd.SlotSplit s
      (fun (N : ℕ) (Φ : X N → ℝ) => Work.UBBInputs8.cnPlusBoxInd s A V Φ) := by
  have hbound : ∀ ⦃M : ℕ⦄ (Ψ : X M → ℝ), ContDiff ℝ (⊤ : ℕ∞) Ψ →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Submission.BoseGases.abox M s, |Ψ x| ≤ C := by
    intro M Ψ hΨ
    obtain ⟨C, hC⟩ := (Submission.BoseGases.abox_compact M hs).exists_bound_of_continuousOn
      (s := Submission.BoseGases.abox M s) (f := Ψ) hΨ.continuous.continuousOn
    exact ⟨C, le_trans (norm_nonneg (Ψ 0)) (hC 0 (Submission.BoseGases.zero_mem_abox hs.le)),
      fun x hx => by simpa [Real.norm_eq_abs] using hC x hx⟩
  refine ⟨?_, ?_, ?_⟩
  · intro N1 N2 Φ hΦ
    exact cns_split_gen hs hA hAc hΦ.continuous
  · intro N1 N2 Φ hΦ
    obtain ⟨C, hC0, hCb⟩ := hbound Φ hΦ
    exact integrableOn_cnPlusBoxInd_slice_fst hs hA hAc hΦ.continuous.measurable hC0 hCb
  · intro N1 N2 Φ hΦ
    obtain ⟨C, hC0, hCb⟩ := hbound Φ hΦ
    exact integrableOn_cnPlusBoxInd_slice_snd hs hA hAc hΦ.continuous.measurable hC0 hCb

/-! ## 3. The spectral half: `tBdiagFormInd` -/

/-- **First-block slice integrability of the spectral half** (`SlotSplit.int₁` for
`tBdiagFormInd`).  The joint `(p,w)`-integrability of the amplitude integrand
(`tBdiagFormInd_blockIntegrand_integrable`) makes the `p`-integral — i.e. the slot functional of
the slice — integrable in the frozen block. -/
lemma integrableOn_tBdiagFormInd_slice_fst {N1 N2 : ℕ} {s V : ℝ} (hs : 0 < s) {A : Set E3}
    (hA : MeasurableSet A) (hAc : A ⊆ Submission.BoseGases.acube s)
    {χ : E3 → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχs : HasCompactSupport χ)
    (hχA : ∀ z : E3, z ∉ A → χ z = 0)
    {Φ : X (N1 + N2) → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    {F : ℝ → ℝ} (hFm : Measurable F) {K d : ℝ} (hK : 0 ≤ K) (hd : d < 3)
    (hFd : ∀ r : ℝ, 0 ≤ r → |F r| ≤ K * (1 + r) ^ d) :
    IntegrableOn (fun w : X N2 => Work.UBBInputs8.tBdiagFormInd s A V χ F
      (fun u => Φ (Submission.BoseGases.mergeBlock N1 N2 (u, w))))
      (Submission.BoseGases.abox N2 s) := by
  have hJ := (tBdiagFormInd_blockIntegrand_integrable (N1 := N1) (N2 := N2) (V := V)
    hs hA hAc hχ hχs hχA hΦ hFm hK hd hFd).1
  have hterm : ∀ j : Fin N1, Integrable (fun w : X N2 =>
      ((2 * π) ^ 3)⁻¹ * ∫ p : E3, F ‖p‖ * ((s ^ 3)⁻¹ *
        ∫ u in Submission.BoseGases.abox N1 s,
          ‖Work.SmallBoxTBWord.tBamp χ p
            (Work.UBBInputs8.boxQInd V A j
              (fun u' => Φ (Submission.BoseGases.mergeBlock N1 N2 (u', w)))) j u‖ ^ 2))
      ((volume : Measure (X N2)).restrict (Submission.BoseGases.abox N2 s)) :=
    fun j => ((hJ j).integral_prod_right).const_mul _
  have hsum := integrable_finsetSum Finset.univ (fun j _ => hterm j)
  have hgoal : Integrable (fun w : X N2 => Work.UBBInputs8.tBdiagFormInd s A V χ F
      (fun u => Φ (Submission.BoseGases.mergeBlock N1 N2 (u, w))))
      ((volume : Measure (X N2)).restrict (Submission.BoseGases.abox N2 s)) := by
    simpa only [Work.UBBInputs8.tBdiagFormInd] using hsum
  exact hgoal

/-- **Second-block slice integrability of the spectral half** (`SlotSplit.int₂` for
`tBdiagFormInd`). -/
lemma integrableOn_tBdiagFormInd_slice_snd {N1 N2 : ℕ} {s V : ℝ} (hs : 0 < s) {A : Set E3}
    (hA : MeasurableSet A) (hAc : A ⊆ Submission.BoseGases.acube s)
    {χ : E3 → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχs : HasCompactSupport χ)
    (hχA : ∀ z : E3, z ∉ A → χ z = 0)
    {Φ : X (N1 + N2) → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    {F : ℝ → ℝ} (hFm : Measurable F) {K d : ℝ} (hK : 0 ≤ K) (hd : d < 3)
    (hFd : ∀ r : ℝ, 0 ≤ r → |F r| ≤ K * (1 + r) ^ d) :
    IntegrableOn (fun u : X N1 => Work.UBBInputs8.tBdiagFormInd s A V χ F
      (fun w => Φ (Submission.BoseGases.mergeBlock N1 N2 (u, w))))
      (Submission.BoseGases.abox N1 s) := by
  have hJ := (tBdiagFormInd_blockIntegrand_integrable (N1 := N1) (N2 := N2) (V := V)
    hs hA hAc hχ hχs hχA hΦ hFm hK hd hFd).2
  have hterm : ∀ j : Fin N2, Integrable (fun u : X N1 =>
      ((2 * π) ^ 3)⁻¹ * ∫ p : E3, F ‖p‖ * ((s ^ 3)⁻¹ *
        ∫ w in Submission.BoseGases.abox N2 s,
          ‖Work.SmallBoxTBWord.tBamp χ p
            (Work.UBBInputs8.boxQInd V A j
              (fun w' => Φ (Submission.BoseGases.mergeBlock N1 N2 (u, w')))) j w‖ ^ 2))
      ((volume : Measure (X N1)).restrict (Submission.BoseGases.abox N1 s)) :=
    fun j => ((hJ j).integral_prod_right).const_mul _
  have hsum := integrable_finsetSum Finset.univ (fun j _ => hterm j)
  have hgoal : Integrable (fun u : X N1 => Work.UBBInputs8.tBdiagFormInd s A V χ F
      (fun w => Φ (Submission.BoseGases.mergeBlock N1 N2 (u, w))))
      ((volume : Measure (X N1)).restrict (Submission.BoseGases.abox N1 s)) := by
    simpa only [Work.UBBInputs8.tBdiagFormInd] using hsum
  exact hgoal

/-- **The spectral half of `sbKin` is `SlotSplit`**: the block identity
(`tBdiagFormInd_slice_split_box`) plus the two slice-integrabilities. -/
theorem slotSplit_tBdiagFormInd {s V : ℝ} (hs : 0 < s) {A : Set E3} (hA : MeasurableSet A)
    (hAc : A ⊆ Submission.BoseGases.acube s) {χ : E3 → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχs : HasCompactSupport χ) (hχA : ∀ z : E3, z ∉ A → χ z = 0)
    {F : ℝ → ℝ} (hFm : Measurable F) {K d : ℝ} (hK : 0 ≤ K) (hd : d < 3)
    (hFd : ∀ r : ℝ, 0 ≤ r → |F r| ≤ K * (1 + r) ^ d) :
    Work.KinPSuperadd.SlotSplit s
      (fun (N : ℕ) (Φ : X N → ℝ) => Work.UBBInputs8.tBdiagFormInd s A V χ F Φ) :=
  ⟨fun N1 N2 Φ hΦ => tBdiagFormInd_slice_split_box hs hA hAc hχ hχs hχA hFm hK hd hFd hΦ,
   fun N1 N2 Φ hΦ => integrableOn_tBdiagFormInd_slice_fst hs hA hAc hχ hχs hχA hΦ hFm hK hd hFd,
   fun N1 N2 Φ hΦ => integrableOn_tBdiagFormInd_slice_snd hs hA hAc hχ hχs hχA hΦ hFm hK hd hFd⟩

/-! ## 4. The assembly: `sbKin` is `SlotSplit` -/

theorem sbKin_slice_slotSplit {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) {ε₀ μ : ℝ} (hAdm : Work.BoseBoxFix.Adm v ε₀ μ)
    (u : EuclideanSpace ℝ (Fin 3)) :
    Work.KinPSuperadd.SlotSplit (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (fun (N : ℕ) (Φ : Submission.BoseGases.X N → ℝ) =>
        Work.BoseFixB1.sbKin (v := v) μ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M u Φ) := by
  set ℓ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v) with hℓdef
  set d := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d with hddef
  set eT := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT with heTdef
  set c := Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v) with hcdef
  have hℓ : 0 < ℓ := by rw [hℓdef]; exact Work.BoseFixB1.adm_ell_pos hAdm
  have hd : 0 < d := by rw [hddef]; exact Work.BoseFixB1.adm_d_pos hAdm
  have hs : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s :=
    Work.BoseFixB1.adm_s_pos hAdm
  have hc : 0 < c := by
    rw [hcdef, Work.BoseFixB1.sbCut]
    exact inv_pos.mpr (mul_pos (mul_pos (by rw [← hddef]; exact hd) hs) hℓ)
  set A := Submission.BoseGases.dlBox ℓ d u with hAdef
  set V := Work.SmallBoxSliding.boxMass ℓ d u with hVdef
  set χ := Submission.BoseGases.chiB ℓ d u with hχdef
  have hA : MeasurableSet A := by rw [hAdef]; exact Work.SmallBoxSliding.measurableSet_dlBox ℓ d u
  have hAc : A ⊆ Submission.BoseGases.acube ℓ := by
    rw [hAdef]; exact cns_split_dlBox_subset ℓ d u
  have hχ : ContDiff ℝ (⊤ : ℕ∞) χ := by
    rw [hχdef]; exact Work.SmallBoxTBWord.contDiff_chiB hℓ hd u
  have hχs : HasCompactSupport χ := by
    rw [hχdef]; exact Work.SmallBoxTBWord.hasCompactSupport_chiB hℓ hd u
  have hχA : ∀ z : E3, z ∉ A → χ z = 0 := by
    intro z hz
    by_contra hne
    exact hz (by rw [hAdef]; exact Submission.BoseGases.chiB_support_mem hℓ hd u z hne)
  have hCn : Work.KinPSuperadd.SlotSplit ℓ
      (fun (N : ℕ) (Φ : X N → ℝ) => Work.UBBInputs8.cnPlusBoxInd ℓ A V Φ) :=
    slotSplit_cnPlusBoxInd hℓ hA hAc
  have hFd : ∀ r : ℝ, 0 ≤ r →
      |Submission.BoseGases.fsKinCoeff c r| ≤ 1 * (1 + r) ^ (2 : ℝ) := by
    intro r hr
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    exact abs_fsKinCoeff_le hc.le r hr
  have hDiag : Work.KinPSuperadd.SlotSplit ℓ
      (fun (N : ℕ) (Φ : X N → ℝ) =>
        Work.UBBInputs8.tBdiagFormInd ℓ A V χ (Submission.BoseGases.fsKinCoeff c) Φ) :=
    slotSplit_tBdiagFormInd hℓ hA hAc hχ hχs hχA (measurable_fsKinCoeff c)
      (K := 1) (d := 2) zero_le_one (by norm_num) hFd
  have hSum : Work.KinPSuperadd.SlotSplit ℓ
      (fun (N : ℕ) (Φ : X N → ℝ) =>
        Work.SmallBoxTBWord.tbGapCoeff (ℓ * d) eT * Work.UBBInputs8.cnPlusBoxInd ℓ A V Φ
          + Work.UBBInputs8.tBdiagFormInd ℓ A V χ (Submission.BoseGases.fsKinCoeff c) Φ) :=
    (hCn.const_mul (Work.SmallBoxTBWord.tbGapCoeff (ℓ * d) eT)).add hDiag
  refine slotSplit_congr_word hSum (fun N Φ => ?_)
  simp only [Work.BoseFixB1.sbKin, Work.UBBInputs8.tBwordBInd, Work.UBBInputs8.tBwordInd,
    Work.UBBInputs8.tBwordKinInd]
  rw [← hℓdef, ← hddef, ← heTdef, ← hAdef, ← hVdef, ← hχdef, ← hcdef]

end Work.BoseFixB1B
