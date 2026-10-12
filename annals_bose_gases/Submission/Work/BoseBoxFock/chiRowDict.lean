import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.boxSlotOf_evec_zero_eq_aPC
import Submission.Work.BoseBoxFock.chiRowDefs2
import Submission.Work.BoseBoxFock.chiRow_aPC_dict
import Submission.Work.BoseBoxFock.chiRow_aP_abox_facts
import Submission.Work.BoseBoxFock.chiRow_slotSum_expand_weak
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.chiRowDict` — the box → position dictionary of the FS `Q₁` χ-row

The FS `Q₁` row is realised on the box by the slot operators `boxSlotSum e T` at
`T = rankOne (evec0 m)`, `rankOnePair C (evec0 m)`, `rankOnePair (evec0 m) C` (χ-row) and the
same with `C` replaced by the `χ²`-row vector `C'`.  This module identifies those slot words,
on the box, with the corpus's position-space slot means `aPC`/`aP` at the *pinned* weights
`chiMode = χ_Λ² − θ_Λ − chiTail` (resp. `thMode`).

Everything here is `sorry`-free.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

set_option autoImplicit false
set_option maxHeartbeats 800000

local notation "Sp" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

/-! ## 1. The pinned modes vanish off the cube -/

lemma chiLam_eq_zero_of_notMem_acube {ℓ : ℝ} (hℓ : 0 < ℓ) {z : Sp} (hz : z ∉ acube ℓ) :
    Work.BoseK15.corpusBox.chiLam ℓ z = 0 := by
  by_contra hne
  exact hz (by
    rw [← corpusBox_boxL_eq_acube hℓ]
    exact Work.BoseB4.BoxData.chiLam_supp (B := Work.BoseK15.corpusBox) hℓ hne)

lemma thetaFun_eq_one_of_mem_acube {ℓ : ℝ} (hℓ : 0 < ℓ) {z : Sp} (hz : z ∈ acube ℓ) :
    Work.BoseK15.corpusBox.thetaFun ℓ z = 1 := by
  rw [Work.BoseB4.BoxData.thetaFun_apply, if_pos (by rwa [corpusBox_boxL_eq_acube hℓ])]

lemma modeVec_eq_zero_of_notMem_acube {ℓ : ℝ} (hℓ : 0 < ℓ) (k z : Sp) (hz : z ∉ acube ℓ) :
    Work.BoseK15.corpusBox.modeVec ℓ k z = 0 := by
  rw [Work.BoseB4.BoxData.modeVec_apply, chiLam_eq_zero_of_notMem_acube hℓ hz,
    Complex.ofReal_zero, mul_zero]

lemma thetaExp_eq_zero_of_notMem_acube {ℓ : ℝ} (hℓ : 0 < ℓ) (s z : Sp) (hz : z ∉ acube ℓ) :
    Work.BoseK15.corpusBox.thetaExp ℓ s z = 0 := by
  rw [Work.BoseB4.BoxData.thetaExp_apply, Work.BoseB4.BoxData.thetaFun_apply,
    if_neg (by rwa [corpusBox_boxL_eq_acube hℓ]), mul_zero]

lemma qVec_eq_zero_of_notMem_acube {ℓ : ℝ} (hℓ : 0 < ℓ) (k z : Sp) (hz : z ∉ acube ℓ) :
    Work.BoseK15.corpusBox.qVec ℓ k z = 0 := by
  rw [Work.BoseB4.BoxData.qVec_apply, modeVec_eq_zero_of_notMem_acube hℓ k z hz,
    Work.BoseB4.BoxData.thetaFun_apply, if_neg (by rwa [corpusBox_boxL_eq_acube hℓ])]
  ring

lemma chiTail_eq_zero_of_notMem_acube {ℓ : ℝ} (hℓ : 0 < ℓ) (N : ℕ) {z : Sp}
    (hz : z ∉ acube ℓ) : chiTail ℓ N z = 0 := by
  unfold chiTail
  rw [chiLam_eq_zero_of_notMem_acube hℓ hz, Work.BoseB4.BoxData.thetaFun_apply,
    if_neg (by rwa [corpusBox_boxL_eq_acube hℓ]),
    Finset.sum_eq_zero (fun k _ => by rw [qVec_eq_zero_of_notMem_acube hℓ _ _ hz, mul_zero])]
  simp

lemma thetaTail_eq_zero_of_notMem_acube {ℓ : ℝ} (hℓ : 0 < ℓ) (N : ℕ) {z : Sp}
    (hz : z ∉ acube ℓ) : thetaTail ℓ N z = 0 := by
  unfold thetaTail
  rw [chiLam_eq_zero_of_notMem_acube hℓ hz, Work.BoseB4.BoxData.thetaFun_apply,
    if_neg (by rwa [corpusBox_boxL_eq_acube hℓ]),
    Finset.sum_eq_zero (fun s _ => by rw [thetaExp_eq_zero_of_notMem_acube hℓ _ _ hz, mul_zero])]
  simp

lemma chiMode_eq_zero_of_notMem_acube {ℓ : ℝ} (hℓ : 0 < ℓ) (N : ℕ) {z : Sp}
    (hz : z ∉ acube ℓ) : chiMode ℓ N z = 0 := by
  unfold chiMode
  rw [chiLam_eq_zero_of_notMem_acube hℓ hz, Work.BoseB4.BoxData.thetaFun_apply,
    if_neg (by rwa [corpusBox_boxL_eq_acube hℓ]), chiTail_eq_zero_of_notMem_acube hℓ N hz]
  simp

lemma thMode_eq_zero_of_notMem_acube {ℓ : ℝ} (hℓ : 0 < ℓ) (N : ℕ) {z : Sp}
    (hz : z ∉ acube ℓ) : thMode ℓ N z = 0 := by
  unfold thMode
  rw [chiLam_eq_zero_of_notMem_acube hℓ hz, Work.BoseB4.BoxData.thetaFun_apply,
    if_neg (by rwa [corpusBox_boxL_eq_acube hℓ]), thetaTail_eq_zero_of_notMem_acube hℓ N hz]
  simp

/-! ## 2. The pinned superposed modes -/

/-- `ηOf` is additive in its vector argument (finite linearity, pointwise). -/
lemma etaOf_finset_sum {m : ℕ} [NeZero m] {κ : Type*} (s : Finset κ) (c : κ → ℝ)
    (w : κ → Fin m → ℝ) (e : Fin m → Sp → ℂ) (z : Sp) :
    Work.BoseDict.etaOf e (∑ k ∈ s, c k • w k) z
      = ∑ k ∈ s, c k * Work.BoseDict.etaOf e (w k) z := by
  simp only [Work.BoseDict.etaOf, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))
  ring

/-- **The pinning of the summed `χ`-mode at the superposed vector `C`.**  If the physical modes
`qVec(ℓ,·)` are pinned to `√ℓ³·η_{f k}` and `C = ∑_k ĉ_k • f k`, then
`√ℓ³·η_C = χ_Λ² − θ_Λ − chiTail = chiMode`. -/
theorem pin_chiMode_of_sum {m : ℕ} [NeZero m] {ℓ : ℝ} (hℓ : 0 < ℓ) {N : ℕ}
    {e : Fin m → Sp → ℂ} {f : Lab N → Fin m → ℝ} {C : Fin m → ℝ}
    (hC : C = ∑ k : Lab N,
      (Work.BoseK15.corpusBox.hatChi (ℓ • kmomLab ℓ N k)) • f k)
    (hq : ∀ k : Lab N, Work.BoseK15.corpusBox.qVec ℓ (kmomLab ℓ N k)
      =ᵐ[MeasureTheory.volume] fun x =>
        ((Real.sqrt (ℓ ^ 3) : ℝ) : ℂ) * Work.BoseDict.etaOf e (f k) x) :
    (fun z => ((Real.sqrt (ℓ ^ 3) : ℝ) : ℂ) * Work.BoseDict.etaOf e C z)
      =ᵐ[MeasureTheory.volume] chiMode ℓ N := by
  have h1 : (fun z => ((Real.sqrt (ℓ ^ 3) : ℝ) : ℂ) * Work.BoseDict.etaOf e C z)
      =ᵐ[MeasureTheory.volume] fun z => ∑ k : Lab N,
          ((Work.BoseK15.corpusBox.hatChi (ℓ • kmomLab ℓ N k) : ℝ) : ℂ)
            * Work.BoseK15.corpusBox.qVec ℓ (kmomLab ℓ N k) z := by
    filter_upwards [(Finset.eventually_all Finset.univ).mpr (fun k _ => hq k)] with z hz
    rw [hC]
    rw [etaOf_finset_sum Finset.univ
      (fun k => Work.BoseK15.corpusBox.hatChi (ℓ • kmomLab ℓ N k)) f e z]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    rw [hz k hk]
    ring
  refine h1.trans ?_
  filter_upwards with z
  unfold chiMode chiTail
  ring

/-- **The pinning of the summed `χ²`-row mode at the superposed vector `C'`.** -/
theorem pin_thMode_of_sum {m : ℕ} [NeZero m] {ℓ : ℝ} (hℓ : 0 < ℓ) {N : ℕ}
    {e : Fin m → Sp → ℂ} {g : Lab N → Fin m → ℝ} {C' : Fin m → ℝ}
    (hC : C' = ∑ s ∈ (Finset.univ.filter (fun s : Lab N => s ≠ 0)),
      (Work.BoseK15.corpusBox.hatChiSq (ℓ • kmomLab ℓ N s)) • g s)
    (hq : ∀ s : Lab N, s ≠ 0 → Work.BoseK15.corpusBox.thetaExp ℓ (kmomLab ℓ N s)
      =ᵐ[MeasureTheory.volume] fun x =>
        ((Real.sqrt (ℓ ^ 3) : ℝ) : ℂ) * Work.BoseDict.etaOf e (g s) x) :
    (fun z => ((Real.sqrt (ℓ ^ 3) : ℝ) : ℂ) * Work.BoseDict.etaOf e C' z)
      =ᵐ[MeasureTheory.volume] thMode ℓ N := by
  have h1 : (fun z => ((Real.sqrt (ℓ ^ 3) : ℝ) : ℂ) * Work.BoseDict.etaOf e C' z)
      =ᵐ[MeasureTheory.volume] fun z =>
          ∑ s ∈ (Finset.univ.filter (fun s : Lab N => s ≠ 0)),
            ((Work.BoseK15.corpusBox.hatChiSq (ℓ • kmomLab ℓ N s) : ℝ) : ℂ)
              * Work.BoseK15.corpusBox.thetaExp ℓ (kmomLab ℓ N s) z := by
    filter_upwards [(Finset.eventually_all _).mpr (fun s hs => hq s (Finset.mem_filter.mp hs).2)]
      with z hz
    rw [hC]
    rw [etaOf_finset_sum _ (fun s => Work.BoseK15.corpusBox.hatChiSq (ℓ • kmomLab ℓ N s)) g e z]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun s hs => ?_)
    rw [hz s hs]
    ring
  refine h1.trans ?_
  filter_upwards with z
  unfold thMode thetaTail
  ring

/-! ## 3. The slot sums at the pinned modes -/

/-- The pinning constant `(√ℓ³)⁻¹` has the required normalisation. -/
lemma conj_inv_sqrt_mul_self {ℓ : ℝ} (hℓ : 0 < ℓ) :
    (starRingEnd ℂ) (((Real.sqrt (ℓ ^ 3))⁻¹ : ℂ)) * (((Real.sqrt (ℓ ^ 3))⁻¹ : ℂ))
      = (ℓ ^ 3)⁻¹ := by
  rw [map_inv₀, Complex.conj_ofReal, ← mul_inv, ← Complex.ofReal_mul,
    Real.mul_self_sqrt (by positivity), Complex.ofReal_inv]

/-- **The `χ`-row slot sum at the superposed pinned mode.**  On the box, the slot sum of the
rank-one operator `|C⟩⟨evec0|` is the sum of the pinned mode at the slot weights times the slot
means. -/
theorem chiRow_chiMode_dict {m d : ℕ} [NeZero m] {ℓ : ℝ} (hℓ : 0 < ℓ) {N : ℕ}
    {e : Fin m → Sp → ℂ}
    (hpin : e 0 =ᵐ[MeasureTheory.volume] fun z =>
      ((Real.sqrt (ℓ ^ 3))⁻¹ : ℂ) * Work.BoseK15.corpusBox.thetaFun ℓ z)
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    {C : Fin m → ℝ}
    (hC : (fun z => ((Real.sqrt (ℓ ^ 3) : ℝ) : ℂ) * Work.BoseDict.etaOf e C z)
      =ᵐ[MeasureTheory.volume] chiMode ℓ N)
    (Θ : Work.BoseDict.Xn d → ℂ) (hΘm : Measurable Θ)
    (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C) :
    (fun x => Work.BoseDict.boxSlotSum e
        (Work.BoseBoxFock.rankOnePair C (Work.BoseBoxFock.evec0 m)) Θ x)
      =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox d ℓ)]
      fun x => ∑ j : Fin d, chiMode ℓ N (x j) * Work.BoseBoxFock.aPC ℓ j Θ x := by
  have hexp := chiRow_slotSum_expand_weak hmeas hbdd hsupp C
    (Work.BoseBoxFock.evec0 m) Θ hΘm hΘb
  have hcoord := fun j : Fin d => (chiRow_aPC_dict hℓ).2.2 j hC
  have hslot : ∀ j : Fin d, (fun x => Work.BoseDict.boxSlotOf e C
        (Work.BoseBoxFock.evec0 m) j Θ x)
      =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox d ℓ)]
      fun x => chiMode ℓ N (x j) * Work.BoseBoxFock.aPC ℓ j Θ x := by
    intro j
    have h1 := boxSlotOf_chiMode_eq (m := m) (n := d) (ℓ := ℓ) hℓ hpin C Θ j
    have h2 := hcoord j
    filter_upwards [h1, h2] with x hx1 hx2
    simp only [Work.BoseBoxFock.evec0] at hx1 ⊢
    rw [hx1, mul_comm (Work.BoseDict.etaOf e C (x j)) (((Real.sqrt (ℓ ^ 3) : ℝ)) : ℂ), hx2]
  have hsu := (Finset.eventually_all Finset.univ).mpr (fun j _ => hslot j)
  filter_upwards [hsu] with x hx
  rw [hexp, Finset.sum_apply]
  exact Finset.sum_congr rfl (fun j _ => hx j (Finset.mem_univ j))

/-- **The `χ²`-row (`ω`-row) slot sum at the superposed pinned mode.** -/
theorem thRow_thMode_dict {m d : ℕ} [NeZero m] {ℓ : ℝ} (hℓ : 0 < ℓ) {N : ℕ}
    {e : Fin m → Sp → ℂ}
    (hpin : e 0 =ᵐ[MeasureTheory.volume] fun z =>
      ((Real.sqrt (ℓ ^ 3))⁻¹ : ℂ) * Work.BoseK15.corpusBox.thetaFun ℓ z)
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    {C' : Fin m → ℝ}
    (hC : (fun z => ((Real.sqrt (ℓ ^ 3) : ℝ) : ℂ) * Work.BoseDict.etaOf e C' z)
      =ᵐ[MeasureTheory.volume] thMode ℓ N)
    (Θ : Work.BoseDict.Xn d → ℂ) (hΘm : Measurable Θ)
    (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C) :
    (fun x => Work.BoseDict.boxSlotSum e
        (Work.BoseBoxFock.rankOnePair C' (Work.BoseBoxFock.evec0 m)) Θ x)
      =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox d ℓ)]
      fun x => ∑ j : Fin d, thMode ℓ N (x j) * Work.BoseBoxFock.aPC ℓ j Θ x := by
  have hexp := chiRow_slotSum_expand_weak hmeas hbdd hsupp C'
    (Work.BoseBoxFock.evec0 m) Θ hΘm hΘb
  have hcoord := fun j : Fin d => (chiRow_aPC_dict hℓ).2.2 j hC
  have hslot : ∀ j : Fin d, (fun x => Work.BoseDict.boxSlotOf e C'
        (Work.BoseBoxFock.evec0 m) j Θ x)
      =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox d ℓ)]
      fun x => thMode ℓ N (x j) * Work.BoseBoxFock.aPC ℓ j Θ x := by
    intro j
    have h1 := boxSlotOf_chiMode_eq (m := m) (n := d) (ℓ := ℓ) hℓ hpin C' Θ j
    have h2 := hcoord j
    filter_upwards [h1, h2] with x hx1 hx2
    simp only [Work.BoseBoxFock.evec0] at hx1 ⊢
    rw [hx1, mul_comm (Work.BoseDict.etaOf e C' (x j)) (((Real.sqrt (ℓ ^ 3) : ℝ)) : ℂ), hx2]
  have hsu := (Finset.eventually_all Finset.univ).mpr (fun j _ => hslot j)
  filter_upwards [hsu] with x hx
  rw [hexp, Finset.sum_apply]
  exact Finset.sum_congr rfl (fun j _ => hx j (Finset.mem_univ j))

/-- **The condensate slot sum** (`n₀ = Σ_j aPC j`) at a state supported in the box. -/
theorem chiRow_n0_dict {m d : ℕ} [NeZero m] {ℓ : ℝ} (hℓ : 0 < ℓ)
    {e : Fin m → Sp → ℂ} (hmeas : ∀ l, Measurable (e l))
    (hemem : ∀ l, MeasureTheory.MemLp (e l) ⊤)
    (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (hpin : e 0 =ᵐ[MeasureTheory.volume] fun z =>
      ((Real.sqrt (ℓ ^ 3))⁻¹ : ℂ) * Work.BoseK15.corpusBox.thetaFun ℓ z)
    (Θ : Work.BoseDict.Xn d → ℂ) (hΘm : Measurable Θ)
    (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C)
    (hΘs : Function.support Θ ⊆ Submission.BoseGases.abox d ℓ) :
    (fun x => Work.BoseDict.boxSlotSum e
        (Work.BoseBoxFock.rankOne (Work.BoseBoxFock.evec0 m)) Θ x)
      =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox d ℓ)]
      fun x => ∑ j : Fin d, Work.BoseBoxFock.aPC ℓ j Θ x := by
  have hexp := chiRow_slotSum_expand_weak hmeas hbdd hsupp
    (Work.BoseBoxFock.evec0 m) (Work.BoseBoxFock.evec0 m) Θ hΘm hΘb
  have hslot := boxSlotOf_evec_zero_eq_aPC (m := m) (d := d) hℓ hemem hsupp
    ⟨((Real.sqrt (ℓ ^ 3))⁻¹ : ℂ), conj_inv_sqrt_mul_self hℓ, hpin⟩ Θ hΘs
  have hsu := (Finset.eventually_all Finset.univ).mpr (fun j _ => hslot j)
  filter_upwards [hsu] with x hx
  rw [Work.BoseBoxFock.rankOne_eq_rankOnePair, hexp, Finset.sum_apply]
  exact Finset.sum_congr rfl (fun j _ => hx j (Finset.mem_univ j))


/-! ## 4. The transpose (second orientation) slot sum -/

/-- **The transpose slot sum at the pinned mode.**  On the box, the slot sum of `|evec0⟩⟨C|` is
the sum of the slot means of `conj(chiMode(·_j))·Θ`. -/
theorem chiRow_chiModeT_dict {m d : ℕ} [NeZero m] {ℓ : ℝ} (hℓ : 0 < ℓ) {N : ℕ}
    {e : Fin m → Sp → ℂ}
    (hpin : e 0 =ᵐ[MeasureTheory.volume] fun z =>
      ((Real.sqrt (ℓ ^ 3))⁻¹ : ℂ) * Work.BoseK15.corpusBox.thetaFun ℓ z)
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    {C : Fin m → ℝ}
    (hC : (fun z => ((Real.sqrt (ℓ ^ 3) : ℝ) : ℂ) * Work.BoseDict.etaOf e C z)
      =ᵐ[MeasureTheory.volume] chiMode ℓ N)
    (Θ : Work.BoseDict.Xn d → ℂ) (hΘm : Measurable Θ)
    (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C) :
    (fun x => Work.BoseDict.boxSlotSum e
        (Work.BoseBoxFock.rankOnePair (Work.BoseBoxFock.evec0 m) C) Θ x)
      =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox d ℓ)]
      fun x => ∑ j : Fin d, Work.BoseBoxFock.aPC ℓ j
        (fun y => (starRingEnd ℂ) (chiMode ℓ N (y j)) * Θ y) x := by
  have hs : ((Real.sqrt (ℓ ^ 3) : ℝ) : ℂ) ≠ 0 := by
    rw [Ne, Complex.ofReal_eq_zero]
    exact ne_of_gt (Real.sqrt_pos_of_pos (pow_pos hℓ 3))
  have hsq : (((Real.sqrt (ℓ ^ 3) : ℝ) : ℂ))⁻¹ * (((Real.sqrt (ℓ ^ 3) : ℝ) : ℂ))⁻¹
      = (((ℓ ^ 3 : ℝ))⁻¹ : ℂ) := by
    have h1 : (((Real.sqrt (ℓ ^ 3) : ℝ) : ℂ))⁻¹ * (((Real.sqrt (ℓ ^ 3) : ℝ) : ℂ))⁻¹
        = (((Real.sqrt (ℓ ^ 3) * Real.sqrt (ℓ ^ 3) : ℝ)) : ℂ)⁻¹ := by
      rw [← mul_inv, ← Complex.ofReal_mul]
    rw [h1, Real.mul_self_sqrt (by positivity), ← Complex.ofReal_inv]
  have hconjC : (fun z => (starRingEnd ℂ) (Work.BoseDict.etaOf e C z))
      =ᵐ[MeasureTheory.volume] fun z =>
        (((Real.sqrt (ℓ ^ 3) : ℝ) : ℂ))⁻¹ * (starRingEnd ℂ) (chiMode ℓ N z) := by
    filter_upwards [hC] with z hz
    have h2 : ((Real.sqrt (ℓ ^ 3) : ℝ) : ℂ) * (starRingEnd ℂ) (Work.BoseDict.etaOf e C z)
        = (starRingEnd ℂ) (chiMode ℓ N z) := by
      rw [← Complex.conj_ofReal, ← map_mul, hz]
    rw [← h2, inv_mul_cancel_left₀ hs]
  -- the pin of `e 0` read at the `j`-th coordinate, a.e. on the box
  have hpinc : ∀ j : Fin d, ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox d ℓ)),
      e 0 (x j) = ((Real.sqrt (ℓ ^ 3))⁻¹ : ℂ) * Work.BoseK15.corpusBox.thetaFun ℓ (x j) := by
    intro j
    have hcube : ∀ᵐ y ∂((MeasureTheory.volume : MeasureTheory.Measure Sp).restrict
        (Submission.BoseGases.acube ℓ)),
        e 0 y = ((Real.sqrt (ℓ ^ 3))⁻¹ : ℂ) * Work.BoseK15.corpusBox.thetaFun ℓ y :=
      MeasureTheory.ae_mono MeasureTheory.Measure.restrict_le_self hpin
    have hpi := (MeasureTheory.Measure.tendsto_eval_ae_ae
      (μ := fun _ : Fin d => (MeasureTheory.volume : MeasureTheory.Measure Sp).restrict
        (Submission.BoseGases.acube ℓ)) (i := j)).eventually hcube
    rw [Submission.BoseGases.restrict_abox_eq_pi d ℓ]
    exact hpi
  have hslot : ∀ j : Fin d, (fun x => Work.BoseDict.boxSlotOf e
        (Work.BoseBoxFock.evec0 m) C j Θ x)
      =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox d ℓ)]
      fun x => Work.BoseBoxFock.aPC ℓ j
        (fun y => (starRingEnd ℂ) (chiMode ℓ N (y j)) * Θ y) x := by
    intro j
    have hint : ∀ x : Work.BoseDict.Xn d,
        (∫ z : Sp, (starRingEnd ℂ) (Work.BoseDict.etaOf e C z) * Θ (Function.update x j z))
          = (((Real.sqrt (ℓ ^ 3) : ℝ) : ℂ))⁻¹
            * ∫ z : Sp, (starRingEnd ℂ) (chiMode ℓ N z) * Θ (Function.update x j z) := by
      intro x
      rw [← MeasureTheory.integral_const_mul]
      apply MeasureTheory.integral_congr_ae
      filter_upwards [hconjC] with z hz
      rw [hz]
      ring
    filter_upwards [hpinc j, MeasureTheory.self_mem_ae_restrict
      (Submission.BoseGases.abox_measurable d ℓ)] with x hx hxmem
    have hxj : x j ∈ Submission.BoseGases.acube ℓ :=
      (Submission.BoseGases.mem_abox_iff d ℓ x).mp hxmem j
    have hbox : Work.BoseDict.boxSlotOf e (Work.BoseBoxFock.evec0 m) C j Θ x
        = Work.BoseDict.etaOf e (Work.BoseBoxFock.evec0 m) (x j) *
          ∫ z : Sp, (starRingEnd ℂ) (Work.BoseDict.etaOf e C z) * Θ (Function.update x j z) :=
      rfl
    have he0 : Work.BoseDict.etaOf e (Work.BoseBoxFock.evec0 m) (x j) = e 0 (x j) :=
      Work.BoseDict.etaOf_pi_single e 0 (x j)
    have hcube : (∫ z : Sp, (starRingEnd ℂ) (chiMode ℓ N z) * Θ (Function.update x j z))
        = ∫ z in Submission.BoseGases.acube ℓ,
            (starRingEnd ℂ) (chiMode ℓ N z) * Θ (Function.update x j z) :=
      (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
        (s := Submission.BoseGases.acube ℓ)
        (fun z hz => by rw [chiMode_eq_zero_of_notMem_acube hℓ N hz, map_zero, zero_mul])).symm
    have haPC : Work.BoseBoxFock.aPC ℓ j
          (fun y => (starRingEnd ℂ) (chiMode ℓ N (y j)) * Θ y) x
        = ((1 / ℓ ^ 3 : ℝ) : ℂ) * ∫ z in Submission.BoseGases.acube ℓ,
            (starRingEnd ℂ) (chiMode ℓ N z) * Θ (Function.update x j z) := by
      unfold Work.BoseBoxFock.aPC
      congr 1
      apply integral_congr_ae
      filter_upwards with y
      rw [Function.update_apply, if_pos rfl]
    rw [hbox, he0, hx, hint x, hcube, haPC,
      Work.BoseBoxFock.thetaFun_eq_one_of_mem_acube hℓ hxj]
    rw [show ((1 / ℓ ^ 3 : ℝ) : ℂ) = ((ℓ ^ 3 : ℝ) : ℂ)⁻¹ from by
      rw [one_div, Complex.ofReal_inv]]
    rw [← hsq]
    ring
  have hexp := chiRow_slotSum_expand_weak hmeas hbdd hsupp
    (Work.BoseBoxFock.evec0 m) C Θ hΘm hΘb
  have hsu := (Finset.eventually_all Finset.univ).mpr (fun j _ => hslot j)
  filter_upwards [hsu] with x hx
  rw [hexp, Finset.sum_apply]
  exact Finset.sum_congr rfl (fun j _ => hx j (Finset.mem_univ j))


/-- **The transpose slot sum at the pinned `χ²`-row mode.**  On the box, the slot sum of `|evec0⟩⟨C|` is
the sum of the slot means of `conj(thMode(·_j))·Θ`. -/
theorem thRow_thModeT_dict {m d : ℕ} [NeZero m] {ℓ : ℝ} (hℓ : 0 < ℓ) {N : ℕ}
    {e : Fin m → Sp → ℂ}
    (hpin : e 0 =ᵐ[MeasureTheory.volume] fun z =>
      ((Real.sqrt (ℓ ^ 3))⁻¹ : ℂ) * Work.BoseK15.corpusBox.thetaFun ℓ z)
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    {C : Fin m → ℝ}
    (hC : (fun z => ((Real.sqrt (ℓ ^ 3) : ℝ) : ℂ) * Work.BoseDict.etaOf e C z)
      =ᵐ[MeasureTheory.volume] thMode ℓ N)
    (Θ : Work.BoseDict.Xn d → ℂ) (hΘm : Measurable Θ)
    (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C) :
    (fun x => Work.BoseDict.boxSlotSum e
        (Work.BoseBoxFock.rankOnePair (Work.BoseBoxFock.evec0 m) C) Θ x)
      =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox d ℓ)]
      fun x => ∑ j : Fin d, Work.BoseBoxFock.aPC ℓ j
        (fun y => (starRingEnd ℂ) (thMode ℓ N (y j)) * Θ y) x := by
  have hs : ((Real.sqrt (ℓ ^ 3) : ℝ) : ℂ) ≠ 0 := by
    rw [Ne, Complex.ofReal_eq_zero]
    exact ne_of_gt (Real.sqrt_pos_of_pos (pow_pos hℓ 3))
  have hsq : (((Real.sqrt (ℓ ^ 3) : ℝ) : ℂ))⁻¹ * (((Real.sqrt (ℓ ^ 3) : ℝ) : ℂ))⁻¹
      = (((ℓ ^ 3 : ℝ))⁻¹ : ℂ) := by
    have h1 : (((Real.sqrt (ℓ ^ 3) : ℝ) : ℂ))⁻¹ * (((Real.sqrt (ℓ ^ 3) : ℝ) : ℂ))⁻¹
        = (((Real.sqrt (ℓ ^ 3) * Real.sqrt (ℓ ^ 3) : ℝ)) : ℂ)⁻¹ := by
      rw [← mul_inv, ← Complex.ofReal_mul]
    rw [h1, Real.mul_self_sqrt (by positivity), ← Complex.ofReal_inv]
  have hconjC : (fun z => (starRingEnd ℂ) (Work.BoseDict.etaOf e C z))
      =ᵐ[MeasureTheory.volume] fun z =>
        (((Real.sqrt (ℓ ^ 3) : ℝ) : ℂ))⁻¹ * (starRingEnd ℂ) (thMode ℓ N z) := by
    filter_upwards [hC] with z hz
    have h2 : ((Real.sqrt (ℓ ^ 3) : ℝ) : ℂ) * (starRingEnd ℂ) (Work.BoseDict.etaOf e C z)
        = (starRingEnd ℂ) (thMode ℓ N z) := by
      rw [← Complex.conj_ofReal, ← map_mul, hz]
    rw [← h2, inv_mul_cancel_left₀ hs]
  -- the pin of `e 0` read at the `j`-th coordinate, a.e. on the box
  have hpinc : ∀ j : Fin d, ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox d ℓ)),
      e 0 (x j) = ((Real.sqrt (ℓ ^ 3))⁻¹ : ℂ) * Work.BoseK15.corpusBox.thetaFun ℓ (x j) := by
    intro j
    have hcube : ∀ᵐ y ∂((MeasureTheory.volume : MeasureTheory.Measure Sp).restrict
        (Submission.BoseGases.acube ℓ)),
        e 0 y = ((Real.sqrt (ℓ ^ 3))⁻¹ : ℂ) * Work.BoseK15.corpusBox.thetaFun ℓ y :=
      MeasureTheory.ae_mono MeasureTheory.Measure.restrict_le_self hpin
    have hpi := (MeasureTheory.Measure.tendsto_eval_ae_ae
      (μ := fun _ : Fin d => (MeasureTheory.volume : MeasureTheory.Measure Sp).restrict
        (Submission.BoseGases.acube ℓ)) (i := j)).eventually hcube
    rw [Submission.BoseGases.restrict_abox_eq_pi d ℓ]
    exact hpi
  have hslot : ∀ j : Fin d, (fun x => Work.BoseDict.boxSlotOf e
        (Work.BoseBoxFock.evec0 m) C j Θ x)
      =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox d ℓ)]
      fun x => Work.BoseBoxFock.aPC ℓ j
        (fun y => (starRingEnd ℂ) (thMode ℓ N (y j)) * Θ y) x := by
    intro j
    have hint : ∀ x : Work.BoseDict.Xn d,
        (∫ z : Sp, (starRingEnd ℂ) (Work.BoseDict.etaOf e C z) * Θ (Function.update x j z))
          = (((Real.sqrt (ℓ ^ 3) : ℝ) : ℂ))⁻¹
            * ∫ z : Sp, (starRingEnd ℂ) (thMode ℓ N z) * Θ (Function.update x j z) := by
      intro x
      rw [← MeasureTheory.integral_const_mul]
      apply MeasureTheory.integral_congr_ae
      filter_upwards [hconjC] with z hz
      rw [hz]
      ring
    filter_upwards [hpinc j, MeasureTheory.self_mem_ae_restrict
      (Submission.BoseGases.abox_measurable d ℓ)] with x hx hxmem
    have hxj : x j ∈ Submission.BoseGases.acube ℓ :=
      (Submission.BoseGases.mem_abox_iff d ℓ x).mp hxmem j
    have hbox : Work.BoseDict.boxSlotOf e (Work.BoseBoxFock.evec0 m) C j Θ x
        = Work.BoseDict.etaOf e (Work.BoseBoxFock.evec0 m) (x j) *
          ∫ z : Sp, (starRingEnd ℂ) (Work.BoseDict.etaOf e C z) * Θ (Function.update x j z) :=
      rfl
    have he0 : Work.BoseDict.etaOf e (Work.BoseBoxFock.evec0 m) (x j) = e 0 (x j) :=
      Work.BoseDict.etaOf_pi_single e 0 (x j)
    have hcube : (∫ z : Sp, (starRingEnd ℂ) (thMode ℓ N z) * Θ (Function.update x j z))
        = ∫ z in Submission.BoseGases.acube ℓ,
            (starRingEnd ℂ) (thMode ℓ N z) * Θ (Function.update x j z) :=
      (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
        (s := Submission.BoseGases.acube ℓ)
        (fun z hz => by rw [thMode_eq_zero_of_notMem_acube hℓ N hz, map_zero, zero_mul])).symm
    have haPC : Work.BoseBoxFock.aPC ℓ j
          (fun y => (starRingEnd ℂ) (thMode ℓ N (y j)) * Θ y) x
        = ((1 / ℓ ^ 3 : ℝ) : ℂ) * ∫ z in Submission.BoseGases.acube ℓ,
            (starRingEnd ℂ) (thMode ℓ N z) * Θ (Function.update x j z) := by
      unfold Work.BoseBoxFock.aPC
      congr 1
      apply integral_congr_ae
      filter_upwards with y
      rw [Function.update_apply, if_pos rfl]
    rw [hbox, he0, hx, hint x, hcube, haPC,
      Work.BoseBoxFock.thetaFun_eq_one_of_mem_acube hℓ hxj]
    rw [show ((1 / ℓ ^ 3 : ℝ) : ℂ) = ((ℓ ^ 3 : ℝ) : ℂ)⁻¹ from by
      rw [one_div, Complex.ofReal_inv]]
    rw [← hsq]
    ring
  have hexp := chiRow_slotSum_expand_weak hmeas hbdd hsupp
    (Work.BoseBoxFock.evec0 m) C Θ hΘm hΘb
  have hsu := (Finset.eventually_all Finset.univ).mpr (fun j _ => hslot j)
  filter_upwards [hsu] with x hx
  rw [hexp, Finset.sum_apply]
  exact Finset.sum_congr rfl (fun j _ => hx j (Finset.mem_univ j))


end Work.BoseBoxFock