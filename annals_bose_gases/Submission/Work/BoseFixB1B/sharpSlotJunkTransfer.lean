import Mathlib
import Submission.Work.BoseFixB1B.qLHSden_aeStronglyMeasurable
import Submission.Work.BoseKinLoc.Sector.lintegral_slotBox_slotIso
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END
set_option synthInstance.maxSize 1024
set_option synthInstance.maxHeartbeats 400000

/-!
# `Submission.Work.BoseFixB1B.sharpSlotJunkTransfer`

**The junk transfer for the per-slot-set assembly** (`Work.BoseFixB1B.sharpSlotBound`).

If the potential density of the slot piece is *not* integrable on the analysis box, then the
potential word of the **sharp box state** `1_{B(u)^{|S|}}` (which is the word the fibre of the
piece would have) is itself the junk value `0`: the non-integrability of

    D x = (slotPiece B S Φ x)^2 · qLHSden N L μ w w1 x

transfers to the sharp density `1_{B^{|S|}} · qLHSden |S| L μ w w1`, because `Φ` is bounded on the
box and `qLHSden` is the same density on both sides of the slot splitting
(`Work.SlotWord.qLHSden_slotComb`).  The transfer is the inequality

    ⊤ = ∫⁻ ‖D‖ₑ ≤ ofReal (‖Φ‖²_∞) · vol(slotOutside) · ∫⁻ ‖1_{B^{|S|}} qLHSden‖ₑ ,

via `slotSplit_lintegral_slotSet` (the measurability-free slot splitting of a `slotSet`-supported
`∫⁻`-integrand) and `setLIntegral_prod_le_const` (a Tonelli bound for a function of the first
variable only, again measurability-free).

The only measurability input is `Work.BoseFixB1B.qLHSden_aeStronglyMeasurable`, which converts
`¬ IntegrableOn D` into `∫⁻ ‖D‖ₑ = ⊤`.
-/

namespace Work.BoseFixB1B

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **The `∫⁻`-splitting of a `slotSet`-supported integrand, without measurability.** -/
theorem slotSplit_lintegral_slotSet {N : ℕ} (L : ℝ) {B : Set E3}
    (hBL : B ⊆ Submission.BoseGases.acube L) (S : Finset (Fin N))
    (G : Submission.BoseGases.X N → ℝ≥0∞)
    (hG : ∀ x : Submission.BoseGases.X N, G x ≠ 0 → x ∈ Work.PerSector.slotSet B S) :
    ∫⁻ x in Submission.BoseGases.abox N L, G x
      = ∫⁻ p in Work.PerSector.slotBox (ι := Work.PerSector.SlotIn N S) B ×ˢ
          Work.PerSector.slotOutside L B S,
          G (Work.PerSector.slotComb S p.1 p.2) := by
  classical
  have hinst : (Finset.Subtype.fintype S : Fintype (Work.PerSector.SlotIn N S)) =
      Subtype.fintype (fun i : Fin N => i ∈ S) := Subsingleton.elim _ _
  have hmp : MeasurePreserving (⇑(Work.PerSector.Work.PerSector.slotME S))
      (volume : Measure (Submission.BoseGases.X N))
      (volume : Measure ((Work.PerSector.SlotIn N S → E3) × (Work.PerSector.SlotOut N S → E3))) := by
    rw [Work.PerSector.Work.PerSector.slotME, hinst]
    exact volume_preserving_piEquivPiSubtypeProd (fun _ : Fin N => E3) (fun i : Fin N => i ∈ S)
  have h1 : ∫⁻ x in Submission.BoseGases.abox N L, G x
      = ∫⁻ p in Work.PerSector.slotBox (ι := Work.PerSector.SlotIn N S)
            (Submission.BoseGases.acube L) ×ˢ
          Work.PerSector.slotBox (ι := Work.PerSector.SlotOut N S)
            (Submission.BoseGases.acube L),
          G (Work.PerSector.slotComb S p.1 p.2) := by
    have hcv := hmp.setLIntegral_comp_emb
      (Work.PerSector.Work.PerSector.slotME S).measurableEmbedding
      (fun p : (Work.PerSector.SlotIn N S → E3) × (Work.PerSector.SlotOut N S → E3) =>
        G (Work.PerSector.slotComb S p.1 p.2)) (Submission.BoseGases.abox N L)
    rw [Work.PerSector.Work.PerSector.slotME_image_abox (N := N) S L] at hcv
    have hcong : (∫⁻ a in Submission.BoseGases.abox N L,
          G (Work.PerSector.slotComb S
            ((Work.PerSector.Work.PerSector.slotME S) a).1
            ((Work.PerSector.Work.PerSector.slotME S) a).2))
        = ∫⁻ a in Submission.BoseGases.abox N L, G a :=
      lintegral_congr (fun a => by rw [Work.PerSector.Work.PerSector.slotComb_slotME S a])
    rw [hcong] at hcv
    exact hcv
  rw [h1]
  have hts : Work.PerSector.slotBox (ι := Work.PerSector.SlotIn N S) B ×ˢ
        Work.PerSector.slotOutside L B S
      ⊆ Work.PerSector.slotBox (ι := Work.PerSector.SlotIn N S) (Submission.BoseGases.acube L) ×ˢ
        Work.PerSector.slotBox (ι := Work.PerSector.SlotOut N S) (Submission.BoseGases.acube L) :=
    Set.prod_mono (Work.PerSector.Work.PerSector.slotBox_mono hBL)
      (Work.PerSector.Work.PerSector.slotBox_mono Set.inter_subset_left)
  refine Work.SlotWord.setLIntegral_eq_setLIntegral_of_eq_zero_off volume hts ?_
  rintro ⟨z, y⟩ hp hpt
  rw [Set.mem_prod, Work.PerSector.mem_slotBox_iff, Work.PerSector.mem_slotBox_iff] at hp
  obtain ⟨_, hyac⟩ := hp
  by_contra hne
  apply hpt
  rw [Set.mem_prod, Work.PerSector.mem_slotBox_iff, Work.PerSector.mem_slotOutside_iff]
  have hmem := (Work.PerSector.slotComb_mem_slotSet_iff B S z y).mp (hG _ hne)
  exact ⟨fun i => hmem.1 i, hyac, fun j => hmem.2 j⟩

/-- **Tonelli bound for a function of the first variable only.** -/
theorem setLIntegral_prod_le_const {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite ν] {s : Set α} {t : Set β} (hs : MeasurableSet s)
    (ht : MeasurableSet t) (g : α → ℝ≥0∞) (htfin : ν t < ⊤) :
    ∫⁻ p in s ×ˢ t, g p.1 ∂(μ.prod ν) ≤ ν t * ∫⁻ z in s, g z ∂μ := by
  have h1 : ∫⁻ p in s ×ˢ t, g p.1 ∂(μ.prod ν)
      = ∫⁻ p, (s ×ˢ t).indicator (fun q : α × β => g q.1) p ∂(μ.prod ν) :=
    (MeasureTheory.lintegral_indicator (hs.prod ht) (fun q : α × β => g q.1)).symm
  rw [h1]
  refine le_trans (MeasureTheory.lintegral_prod_le _) ?_
  have hone : ∀ z : α, s.indicator (fun _ => (1 : ℝ≥0∞)) z ≠ ⊤ := by
    intro z
    by_cases hz : z ∈ s
    · rw [Set.indicator_of_mem hz]; exact ENNReal.one_ne_top
    · rw [Set.indicator_of_notMem hz]; exact ENNReal.zero_ne_top
  have hpt : ∀ (z : α) (y : β), (s ×ˢ t).indicator (fun q : α × β => g q.1) (z, y)
      = s.indicator (fun _ => (1 : ℝ≥0∞)) z * (t.indicator (fun _ => (1 : ℝ≥0∞)) y * g z) := by
    intro z y
    by_cases h : (z, y) ∈ s ×ˢ t
    · rw [Set.indicator_of_mem h (fun q : α × β => g q.1)]
      rw [Set.mem_prod] at h
      rw [Set.indicator_of_mem h.1, Set.indicator_of_mem h.2, one_mul, one_mul]
    · rw [Set.indicator_of_notMem h (fun q : α × β => g q.1)]
      have h' : ¬ (z ∈ s ∧ y ∈ t) := by simpa [Set.mem_prod] using h
      by_cases hz : z ∈ s
      · rw [Set.indicator_of_mem hz]
        have hy : y ∉ t := fun hy => h' ⟨hz, hy⟩
        rw [Set.indicator_of_notMem hy, zero_mul, mul_zero]
      · rw [Set.indicator_of_notMem hz, zero_mul]
  have hinner : ∀ z : α,
      (∫⁻ y, t.indicator (fun _ => (1 : ℝ≥0∞)) y * g z ∂ν) = ν t * g z := by
    intro z
    rw [MeasureTheory.lintegral_mul_const (g z)
        (measurable_const.indicator ht : Measurable (t.indicator (fun _ => (1 : ℝ≥0∞)))),
      MeasureTheory.lintegral_indicator ht, MeasureTheory.setLIntegral_const, one_mul]
  rw [show (∫⁻ z, ∫⁻ y, (s ×ˢ t).indicator (fun q : α × β => g q.1) (z, y) ∂ν ∂μ)
      = ∫⁻ z, s.indicator (fun _ => (1 : ℝ≥0∞)) z * (ν t * g z) ∂μ from by
    refine lintegral_congr (fun z => ?_)
    rw [show (∫⁻ y, (s ×ˢ t).indicator (fun q : α × β => g q.1) (z, y) ∂ν)
        = ∫⁻ y, s.indicator (fun _ => (1 : ℝ≥0∞)) z *
            (t.indicator (fun _ => (1 : ℝ≥0∞)) y * g z) ∂ν from
      lintegral_congr (fun y => hpt z y)]
    rw [MeasureTheory.lintegral_const_mul' _ _ (hone z), hinner z]]
  rw [show (∫⁻ z, s.indicator (fun _ => (1 : ℝ≥0∞)) z * (ν t * g z) ∂μ)
      = ν t * ∫⁻ z, s.indicator (fun _ => (1 : ℝ≥0∞)) z * g z ∂μ from by
    rw [show (fun z => s.indicator (fun _ => (1 : ℝ≥0∞)) z * (ν t * g z))
        = fun z => ν t * (s.indicator (fun _ => (1 : ℝ≥0∞)) z * g z) from by
      funext z
      rw [← mul_assoc, mul_comm (s.indicator (fun _ => (1 : ℝ≥0∞)) z) (ν t), mul_assoc]]
    exact MeasureTheory.lintegral_const_mul' _ _ htfin.ne]
  rw [show (∫⁻ z, s.indicator (fun _ => (1 : ℝ≥0∞)) z * g z ∂μ) = ∫⁻ z in s, g z ∂μ from by
    rw [show (∫⁻ z, s.indicator (fun _ => (1 : ℝ≥0∞)) z * g z ∂μ)
        = ∫⁻ z, s.indicator g z ∂μ from by
      refine lintegral_congr (fun z => ?_)
      by_cases hz : z ∈ s
      · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz, one_mul]
      · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz, zero_mul]]
    rw [← MeasureTheory.lintegral_indicator hs (fun z => g z)]]

/-- **A set integral over `s` of the `t`-indicator times `g` is the set integral over `t`.** -/
theorem setLIntegral_indicator_one_mul {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {s t : Set α} (hs : MeasurableSet s) (ht : MeasurableSet t) (hta : t ⊆ s)
    (g : α → ℝ≥0∞) :
    ∫⁻ z in s, t.indicator (fun _ => (1 : ℝ≥0∞)) z * g z ∂μ = ∫⁻ z in t, g z ∂μ := by
  rw [← MeasureTheory.lintegral_indicator hs
      (fun z => t.indicator (fun _ => (1 : ℝ≥0∞)) z * g z),
    ← MeasureTheory.lintegral_indicator ht g]
  refine lintegral_congr (fun z => ?_)
  by_cases hz : z ∈ t
  · rw [Set.indicator_of_mem (hta hz) (fun z => t.indicator (fun _ => (1 : ℝ≥0∞)) z * g z),
      Set.indicator_of_mem hz g, Set.indicator_of_mem hz (fun _ => (1 : ℝ≥0∞)), one_mul]
  · rw [Set.indicator_of_notMem hz g]
    have hfz : t.indicator (fun _ => (1 : ℝ≥0∞)) z * g z = 0 := by
      rw [Set.indicator_of_notMem hz (fun _ => (1 : ℝ≥0∞)), zero_mul]
    by_cases hzs : z ∈ s
    · rw [Set.indicator_of_mem hzs, hfz]
    · rw [Set.indicator_of_notMem hzs]

theorem qLHSsharp_junk {v : E3 → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R)
    (hav : 0 < _root_.BoseGases.a v)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) {μ : ℝ} (hμ : Work.BoseBoxFix.Adm v ε₀ μ)
    {u : E3} (hu : u ∈ Work.SmallBoxSliding.goodSet (PBℓ v μ) (PBd v μ) μ)
    {n : ℕ} (Φ : Work.BoseKinLoc.BoxState n (PBℓ v μ))
    (S : Finset (Fin n)) (hS : 0 < S.card)
    (hni : ¬ MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X n =>
        (Work.PerSector.slotPiece (Submission.BoseGases.dlBox (PBℓ v μ) (PBd v μ) u) S
            (Φ : Submission.BoseGases.X n → ℝ) x) ^ 2
          * Submission.BoseGases.qLHSden n (PBℓ v μ) μ
              (Submission.BoseGases.wSmallPair (PBM v μ) (PBℓ v μ) (PBd v μ) u v)
              (Submission.BoseGases.wSmall1Pair h (PBM v μ) (PBℓ v μ) (PBd v μ) u) x)
      (Submission.BoseGases.abox n (PBℓ v μ))) :
    Submission.BoseGases.qLHSword (N := S.card) (PBℓ v μ) μ
        (Submission.BoseGases.wSmallPair (PBM v μ) (PBℓ v μ) (PBd v μ) u v)
        (Submission.BoseGases.wSmall1Pair h (PBM v μ) (PBℓ v μ) (PBd v μ) u)
        (sharpBoxState (Submission.BoseGases.dlBox (PBℓ v μ) (PBd v μ) u)
          (fun _ : Submission.BoseGases.X S.card => (1 : ℝ))) = 0 := by
  classical
  have hL : 0 < PBℓ v μ := Work.BoseFixB1.adm_ell_pos hμ
  have hd : 0 < PBd v μ := Work.BoseFixB1.adm_d_pos hμ
  have hM1 : 1 ≤ PBM v μ := by
    show 1 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
    rw [Work.BoseFixB1.M_eq_mValue]; norm_num [Work.BoseBox.mValue]
  have hBmeas : MeasurableSet (Submission.BoseGases.dlBox (PBℓ v μ) (PBd v μ) u) :=
    Work.SmallBoxSliding.measurableSet_dlBox _ _ _
  have hBsub : Submission.BoseGases.dlBox (PBℓ v μ) (PBd v μ) u ⊆
      Submission.BoseGases.acube (PBℓ v μ) := Work.SmallBoxSliding.dlBox_subset_acube _ _ _
  set w : E3 → E3 → ℝ := Submission.BoseGases.wSmallPair (PBM v μ) (PBℓ v μ) (PBd v μ) u v with hw
  set w1 : E3 → E3 → ℝ :=
    Submission.BoseGases.wSmall1Pair h (PBM v μ) (PBℓ v μ) (PBd v μ) u with hw1
  have hsupp1 : ∀ x : E3, x ∉ Submission.BoseGases.dlBox (PBℓ v μ) (PBd v μ) u →
      ∀ y : E3, w1 x y = 0 :=
    fun x hx y => Work.SlotWord.wSmall1Pair_support_left hM1 hL hd u hx y
  have hsupp2 : ∀ x y : E3, (x ∉ Submission.BoseGases.dlBox (PBℓ v μ) (PBd v μ) u ∨
      y ∉ Submission.BoseGases.dlBox (PBℓ v μ) (PBd v μ) u) → w x y = 0 := by
    intro x y hxy
    rcases hxy with hx | hy
    · exact Work.SlotWord.wSmallPair_support_left hM1 hL hd u v hx y
    · have h0 : Submission.BoseGases.chiSmallB (PBM v μ) (PBℓ v μ) (PBd v μ) u y = 0 := by
        by_contra hne
        exact hy (Work.SlotWord.chiSmallB_support_mem_dlBox hM1 hL hd hne)
      rw [hw, Submission.BoseGases.wSmallPair, h0, mul_zero]
  -- the bound on `Φ`
  obtain ⟨C₀, hC₀⟩ := (Submission.BoseGases.abox_compact n hL).exists_bound_of_continuousOn
    (s := Submission.BoseGases.abox n (PBℓ v μ)) (f := (Φ : Submission.BoseGases.X n → ℝ))
    Φ.contDiff.continuous.continuousOn
  set C : ℝ := max C₀ 0 with hCdef
  have hC : ∀ x ∈ Submission.BoseGases.abox n (PBℓ v μ),
      ‖(Φ : Submission.BoseGases.X n → ℝ) x‖ ≤ C :=
    fun x hx => le_trans (hC₀ x hx) (le_max_left _ _)
  have hCnn : 0 ≤ C := le_max_right _ _
  -- `qLHSden` is a.e. strongly measurable
  have hqmeas : MeasureTheory.AEStronglyMeasurable
      (fun x : Submission.BoseGases.X n => Submission.BoseGases.qLHSden n (PBℓ v μ) μ w w1 x)
      ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)).restrict
        (Submission.BoseGases.abox n (PBℓ v μ))) :=
    qLHSden_aeStronglyMeasurable (c := 0) (C := 0) h hv hv1 hvrad hR hv_supp hav hε₀ hμ hu (n := n)
  set Df : Submission.BoseGases.X n → ℝ := fun x =>
    (Work.PerSector.slotPiece (Submission.BoseGases.dlBox (PBℓ v μ) (PBd v μ) u) S
        (Φ : Submission.BoseGases.X n → ℝ) x) ^ 2 *
      Submission.BoseGases.qLHSden n (PBℓ v μ) μ w w1 x with hDfdef
  have hni' : ¬ MeasureTheory.IntegrableOn Df (Submission.BoseGases.abox n (PBℓ v μ)) := hni
  have hDmeas : MeasureTheory.AEStronglyMeasurable Df
      ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)).restrict
        (Submission.BoseGases.abox n (PBℓ v μ))) := by
    rw [hDfdef]
    have hm : Measurable (fun x : Submission.BoseGases.X n =>
        (Work.PerSector.slotPiece (Submission.BoseGases.dlBox (PBℓ v μ) (PBd v μ) u) S
            (Φ : Submission.BoseGases.X n → ℝ) x) ^ 2) :=
      (Work.PerSector.slotPiece_measurable _ hBmeas S
        Φ.contDiff.continuous.measurable).pow_const (2 : ℕ)
    exact (hm.aestronglyMeasurable).mul hqmeas
  have hDtop : (∫⁻ x, ‖Df x‖ₑ ∂((MeasureTheory.volume : MeasureTheory.Measure
      (Submission.BoseGases.X n)).restrict (Submission.BoseGases.abox n (PBℓ v μ)))) = ⊤ := by
    have hnf : ¬ MeasureTheory.HasFiniteIntegral Df
        ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)).restrict
          (Submission.BoseGases.abox n (PBℓ v μ))) := fun hf => hni' ⟨hDmeas, hf⟩
    exact top_le_iff.mp (le_of_not_gt hnf)
  -- the pointwise bound
  have hpt : ∀ x ∈ Submission.BoseGases.abox n (PBℓ v μ),
      ‖Df x‖ₑ ≤ ENNReal.ofReal (C ^ 2) *
        ((Work.PerSector.slotSet (Submission.BoseGases.dlBox (PBℓ v μ) (PBd v μ) u) S).indicator
          (fun _ => (1 : ℝ≥0∞)) x *
          ‖Submission.BoseGases.qLHSden n (PBℓ v μ) μ w w1 x‖ₑ) := by
    intro x hx
    have hbx : ‖(Φ : Submission.BoseGases.X n → ℝ) x‖ ≤ C := hC x hx
    have hΦle : ((Φ : Submission.BoseGases.X n → ℝ) x) ^ 2 ≤ C ^ 2 := by
      rw [sq_le_sq, abs_of_nonneg hCnn]
      rwa [Real.norm_eq_abs] at hbx
    show ‖(Work.PerSector.slotPiece (Submission.BoseGases.dlBox (PBℓ v μ) (PBd v μ) u) S
        (Φ : Submission.BoseGases.X n → ℝ) x) ^ 2 *
        Submission.BoseGases.qLHSden n (PBℓ v μ) μ w w1 x‖ₑ ≤
      ENNReal.ofReal (C ^ 2) *
        ((Work.PerSector.slotSet (Submission.BoseGases.dlBox (PBℓ v μ) (PBd v μ) u) S).indicator
          (fun _ => (1 : ℝ≥0∞)) x * ‖Submission.BoseGases.qLHSden n (PBℓ v μ) μ w w1 x‖ₑ)
    have hsharp : (Work.PerSector.slotPiece (Submission.BoseGases.dlBox (PBℓ v μ) (PBd v μ) u) S
        (Φ : Submission.BoseGases.X n → ℝ) x) ^ 2
        = (Work.PerSector.slotSet (Submission.BoseGases.dlBox (PBℓ v μ) (PBd v μ) u) S).indicator
            (fun y => ((Φ : Submission.BoseGases.X n → ℝ) y) ^ 2) x := by
      by_cases hxs : x ∈ Work.PerSector.slotSet
          (Submission.BoseGases.dlBox (PBℓ v μ) (PBd v μ) u) S
      · rw [show Work.PerSector.slotPiece (Submission.BoseGases.dlBox (PBℓ v μ) (PBd v μ) u) S
            (Φ : Submission.BoseGases.X n → ℝ) x = (Φ : Submission.BoseGases.X n → ℝ) x
            from Set.indicator_of_mem hxs _,
          Set.indicator_of_mem hxs]
      · rw [show Work.PerSector.slotPiece (Submission.BoseGases.dlBox (PBℓ v μ) (PBd v μ) u) S
            (Φ : Submission.BoseGases.X n → ℝ) x = 0
            from Set.indicator_of_notMem hxs _,
          Set.indicator_of_notMem hxs]
        ring
    rw [enorm_mul, Real.enorm_eq_ofReal_abs, abs_of_nonneg (sq_nonneg _), hsharp]
    by_cases hxs : x ∈ Work.PerSector.slotSet (Submission.BoseGases.dlBox (PBℓ v μ) (PBd v μ) u) S
    · rw [Set.indicator_of_mem hxs, Set.indicator_of_mem hxs, one_mul]
      exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hΦle) zero_le
    · rw [Set.indicator_of_notMem hxs, Set.indicator_of_notMem hxs]
      simp
  set F : Submission.BoseGases.X n → ℝ≥0∞ := fun x =>
    (Work.PerSector.slotSet (Submission.BoseGases.dlBox (PBℓ v μ) (PBd v μ) u) S).indicator
      (fun _ => (1 : ℝ≥0∞)) x *
      ‖Submission.BoseGases.qLHSden n (PBℓ v μ) μ w w1 x‖ₑ with hFdef
  have hFtop : (∫⁻ x, F x ∂((MeasureTheory.volume : MeasureTheory.Measure
      (Submission.BoseGases.X n)).restrict (Submission.BoseGases.abox n (PBℓ v μ)))) = ⊤ := by
    have h1 : (∫⁻ x, ‖Df x‖ₑ ∂((MeasureTheory.volume : MeasureTheory.Measure
        (Submission.BoseGases.X n)).restrict (Submission.BoseGases.abox n (PBℓ v μ))))
        ≤ ENNReal.ofReal (C ^ 2) * (∫⁻ x, F x ∂((MeasureTheory.volume : MeasureTheory.Measure
            (Submission.BoseGases.X n)).restrict (Submission.BoseGases.abox n (PBℓ v μ)))) := by
      calc (∫⁻ x, ‖Df x‖ₑ ∂((MeasureTheory.volume : MeasureTheory.Measure
              (Submission.BoseGases.X n)).restrict (Submission.BoseGases.abox n (PBℓ v μ))))
          ≤ ∫⁻ x, ENNReal.ofReal (C ^ 2) * F x ∂((MeasureTheory.volume :
              MeasureTheory.Measure (Submission.BoseGases.X n)).restrict
                (Submission.BoseGases.abox n (PBℓ v μ))) := by
            refine MeasureTheory.lintegral_mono_ae ?_
            filter_upwards [MeasureTheory.ae_restrict_mem
              (Submission.BoseGases.abox_measurable n (PBℓ v μ))] with x hx
            exact hpt x hx
        _ = ENNReal.ofReal (C ^ 2) * (∫⁻ x, F x ∂((MeasureTheory.volume :
              MeasureTheory.Measure (Submission.BoseGases.X n)).restrict
                (Submission.BoseGases.abox n (PBℓ v μ)))) :=
            MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    have h2 : ⊤ ≤ ENNReal.ofReal (C ^ 2) * (∫⁻ x, F x ∂((MeasureTheory.volume :
        MeasureTheory.Measure (Submission.BoseGases.X n)).restrict
          (Submission.BoseGases.abox n (PBℓ v μ)))) := by
      rw [← hDtop]; exact h1
    by_contra hne
    exact not_le.mpr (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (lt_top_iff_ne_top.mpr hne)) h2
  -- splitting
  have hFsupp : ∀ x : Submission.BoseGases.X n, F x ≠ 0 →
      x ∈ Work.PerSector.slotSet (Submission.BoseGases.dlBox (PBℓ v μ) (PBd v μ) u) S := by
    intro x hx
    by_contra h0
    apply hx
    show (Work.PerSector.slotSet (Submission.BoseGases.dlBox (PBℓ v μ) (PBd v μ) u) S).indicator
        (fun _ => (1 : ℝ≥0∞)) x *
        ‖Submission.BoseGases.qLHSden n (PBℓ v μ) μ w w1 x‖ₑ = 0
    rw [Set.indicator_of_notMem h0, zero_mul]
  have hsplit := slotSplit_lintegral_slotSet (N := n) (PBℓ v μ) hBsub S F hFsupp
  -- pointwise identification on the slot product
  have h3 : (∫⁻ p in Work.PerSector.slotBox (ι := Work.PerSector.SlotIn n S)
          (Submission.BoseGases.dlBox (PBℓ v μ) (PBd v μ) u) ×ˢ
        Work.PerSector.slotOutside (PBℓ v μ)
          (Submission.BoseGases.dlBox (PBℓ v μ) (PBd v μ) u) S,
        F (Work.PerSector.slotComb S p.1 p.2))
      = ∫⁻ p in Work.PerSector.slotBox (ι := Work.PerSector.SlotIn n S)
          (Submission.BoseGases.dlBox (PBℓ v μ) (PBd v μ) u) ×ˢ
        Work.PerSector.slotOutside (PBℓ v μ)
          (Submission.BoseGases.dlBox (PBℓ v μ) (PBd v μ) u) S,
        ‖Submission.BoseGases.qLHSden S.card (PBℓ v μ) μ w w1
          (fun m : Fin S.card => p.1 ((Work.BoseKinLoc.Sector.slotIso S).symm m))‖ₑ := by
    refine MeasureTheory.setLIntegral_congr_fun ?_ ?_
    · exact (Work.PerSector.Work.PerSector.slotBox_measurable hBmeas).prod
        (Work.SlotWord.measurableSet_slotOutside (PBℓ v μ) hBmeas S)
    · rintro ⟨z, y⟩ hp
      rw [Set.mem_prod, Work.PerSector.mem_slotBox_iff] at hp
      obtain ⟨hz, hy⟩ := hp
      have hyout : ∀ j : Work.PerSector.SlotOut n S,
          y j ∉ Submission.BoseGases.dlBox (PBℓ v μ) (PBd v μ) u :=
        (Work.PerSector.mem_slotOutside_iff.mp hy).2
      have hmem : Work.PerSector.slotComb S z y ∈ Work.PerSector.slotSet
          (Submission.BoseGases.dlBox (PBℓ v μ) (PBd v μ) u) S :=
        (Work.PerSector.slotComb_mem_slotSet_iff _ S z y).mpr ⟨hz, hyout⟩
      have hden := Work.SlotWord.qLHSden_slotComb (PBℓ v μ) (PBd v μ) μ u S
        (Work.BoseKinLoc.Sector.slotIso S) w w1 hsupp1 hsupp2
        (fun m : Fin S.card => z ((Work.BoseKinLoc.Sector.slotIso S).symm m)) y hyout
      have hcomp : (fun i : Work.PerSector.SlotIn n S =>
          (fun m : Fin S.card => z ((Work.BoseKinLoc.Sector.slotIso S).symm m))
            ((Work.BoseKinLoc.Sector.slotIso S) i)) = z := by
        funext i; simp
      rw [hcomp] at hden
      show F (Work.PerSector.slotComb S z y)
          = ‖Submission.BoseGases.qLHSden S.card (PBℓ v μ) μ w w1
              (fun m : Fin S.card => z ((Work.BoseKinLoc.Sector.slotIso S).symm m))‖ₑ
      rw [hFdef]
      simp only [Pi.mul_apply]
      rw [Set.indicator_of_mem hmem, one_mul, hden]
  -- the outside volume is finite
  have hvol_lt : (MeasureTheory.volume : MeasureTheory.Measure
      (Work.PerSector.SlotOut n S → E3))
      (Work.PerSector.slotOutside (PBℓ v μ)
        (Submission.BoseGases.dlBox (PBℓ v μ) (PBd v μ) u) S) < ⊤ := by
    have hsub : Work.PerSector.slotOutside (PBℓ v μ)
          (Submission.BoseGases.dlBox (PBℓ v μ) (PBd v μ) u) S
        ⊆ Work.PerSector.slotBox (ι := Work.PerSector.SlotOut n S) (Submission.BoseGases.acube (PBℓ v μ)) := by
      intro y hy
      rw [Work.PerSector.mem_slotBox_iff]
      exact (Work.PerSector.mem_slotOutside_iff.mp hy).1
    refine lt_of_le_of_lt (measure_mono hsub) ?_
    rw [show Work.PerSector.slotBox (ι := Work.PerSector.SlotOut n S)
          (Submission.BoseGases.acube (PBℓ v μ))
        = Set.univ.pi (fun _ : Work.PerSector.SlotOut n S =>
            Submission.BoseGases.acube (PBℓ v μ)) from by
      ext z; simp [Work.PerSector.slotBox]]
    rw [MeasureTheory.volume_pi, MeasureTheory.Measure.pi_pi]
    exact ENNReal.prod_lt_top (fun _ _ => by
      rw [Submission.BoseGases.acube_volume (PBℓ v μ) hL.le]
      exact ENNReal.ofReal_lt_top)
  -- Tonelli bound
  have h4 := setLIntegral_prod_le_const (volume : Measure (Work.PerSector.SlotIn n S → E3))
    (volume : Measure (Work.PerSector.SlotOut n S → E3))
    (s := Work.PerSector.slotBox (ι := Work.PerSector.SlotIn n S)
      (Submission.BoseGases.dlBox (PBℓ v μ) (PBd v μ) u))
    (t := Work.PerSector.slotOutside (PBℓ v μ)
      (Submission.BoseGases.dlBox (PBℓ v μ) (PBd v μ) u) S)
    (Work.PerSector.Work.PerSector.slotBox_measurable hBmeas)
    (Work.SlotWord.measurableSet_slotOutside (PBℓ v μ) hBmeas S)
    (fun z : Work.PerSector.SlotIn n S → E3 =>
      ‖Submission.BoseGases.qLHSden S.card (PBℓ v μ) μ w w1
        (fun m : Fin S.card => z ((Work.BoseKinLoc.Sector.slotIso S).symm m))‖ₑ) hvol_lt
  -- reindexing
  have h5 : (∫⁻ z in Work.PerSector.slotBox (ι := Work.PerSector.SlotIn n S)
        (Submission.BoseGases.dlBox (PBℓ v μ) (PBd v μ) u),
        ‖Submission.BoseGases.qLHSden S.card (PBℓ v μ) μ w w1
          (fun m : Fin S.card => z ((Work.BoseKinLoc.Sector.slotIso S).symm m))‖ₑ)
      = ∫⁻ x in Work.PerSector.slotBox (ι := Fin S.card)
          (Submission.BoseGases.dlBox (PBℓ v μ) (PBd v μ) u),
        ‖Submission.BoseGases.qLHSden S.card (PBℓ v μ) μ w w1 x‖ₑ := by
    have hg2 : (fun x : Fin S.card → E3 =>
        ‖Submission.BoseGases.qLHSden S.card (PBℓ v μ) μ w w1
          (fun m : Fin S.card => (fun i : Work.PerSector.SlotIn n S =>
            x ((Work.BoseKinLoc.Sector.slotIso S) i)) ((Work.BoseKinLoc.Sector.slotIso S).symm m))‖ₑ)
        = fun x => ‖Submission.BoseGases.qLHSden S.card (PBℓ v μ) μ w w1 x‖ₑ := by
      funext x
      simp only [Equiv.apply_symm_apply]
    rw [← hg2]
    exact (Work.BoseKinLoc.Sector.lintegral_slotBox_slotIso (N := n) S hBmeas
      (fun z : Work.PerSector.SlotIn n S → E3 =>
        ‖Submission.BoseGases.qLHSden S.card (PBℓ v μ) μ w w1
          (fun m : Fin S.card => z ((Work.BoseKinLoc.Sector.slotIso S).symm m))‖ₑ)).symm
  -- the sharp density, in indicator form
  have hbox_abox : Work.PerSector.slotBox (ι := Fin S.card)
        (Submission.BoseGases.dlBox (PBℓ v μ) (PBd v μ) u)
      ⊆ Submission.BoseGases.abox S.card (PBℓ v μ) := by
    intro z hz i
    exact hBsub (by simpa [Work.PerSector.slotBox] using hz i)
  have hsharp_swap : (∫⁻ z, ‖(sharpBoxState (Submission.BoseGases.dlBox (PBℓ v μ) (PBd v μ) u)
        (fun _ : Submission.BoseGases.X S.card => (1 : ℝ)) z) ^ 2 *
        Submission.BoseGases.qLHSden S.card (PBℓ v μ) μ w w1 z‖ₑ ∂
      ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X S.card)).restrict
        (Submission.BoseGases.abox S.card (PBℓ v μ))))
      = ∫⁻ z in Submission.BoseGases.abox S.card (PBℓ v μ),
          (Work.PerSector.slotBox (ι := Fin S.card)
              (Submission.BoseGases.dlBox (PBℓ v μ) (PBd v μ) u)).indicator
            (fun _ => (1 : ℝ≥0∞)) z *
            ‖Submission.BoseGases.qLHSden S.card (PBℓ v μ) μ w w1 z‖ₑ := by
    rw [show (∫⁻ z, ‖(sharpBoxState (Submission.BoseGases.dlBox (PBℓ v μ) (PBd v μ) u)
          (fun _ : Submission.BoseGases.X S.card => (1 : ℝ)) z) ^ 2 *
          Submission.BoseGases.qLHSden S.card (PBℓ v μ) μ w w1 z‖ₑ ∂
        ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X S.card)).restrict
          (Submission.BoseGases.abox S.card (PBℓ v μ))))
        = ∫⁻ z in Submission.BoseGases.abox S.card (PBℓ v μ),
          ‖(sharpBoxState (Submission.BoseGases.dlBox (PBℓ v μ) (PBd v μ) u)
            (fun _ : Submission.BoseGases.X S.card => (1 : ℝ)) z) ^ 2 *
            Submission.BoseGases.qLHSden S.card (PBℓ v μ) μ w w1 z‖ₑ from rfl]
    refine MeasureTheory.setLIntegral_congr_fun
      (Submission.BoseGases.abox_measurable S.card (PBℓ v μ)) (fun z _ => ?_)
    show ‖(sharpBoxState (Submission.BoseGases.dlBox (PBℓ v μ) (PBd v μ) u)
        (fun _ : Submission.BoseGases.X S.card => (1 : ℝ)) z) ^ 2 *
        Submission.BoseGases.qLHSden S.card (PBℓ v μ) μ w w1 z‖ₑ
      = (Work.PerSector.slotBox (ι := Fin S.card)
            (Submission.BoseGases.dlBox (PBℓ v μ) (PBd v μ) u)).indicator
          (fun _ => (1 : ℝ≥0∞)) z *
          ‖Submission.BoseGases.qLHSden S.card (PBℓ v μ) μ w w1 z‖ₑ
    rw [enorm_mul, Real.enorm_eq_ofReal_abs, abs_of_nonneg (sq_nonneg _)]
    by_cases hz : z ∈ Work.PerSector.slotBox (ι := Fin S.card)
        (Submission.BoseGases.dlBox (PBℓ v μ) (PBd v μ) u)
    · have h1 : (sharpBoxState (Submission.BoseGases.dlBox (PBℓ v μ) (PBd v μ) u)
          (fun _ : Submission.BoseGases.X S.card => (1 : ℝ)) z) ^ 2 = 1 := by
        rw [sharpState_apply, if_pos (by simpa [Work.PerSector.slotBox] using hz)]
        norm_num
      rw [h1, Set.indicator_of_mem hz, ENNReal.ofReal_one, one_mul]
    · have h1 : (sharpBoxState (Submission.BoseGases.dlBox (PBℓ v μ) (PBd v μ) u)
          (fun _ : Submission.BoseGases.X S.card => (1 : ℝ)) z) ^ 2 = 0 := by
        rw [sharpState_apply, if_neg (by simpa [Work.PerSector.slotBox] using hz)]
        norm_num
      rw [h1, Set.indicator_of_notMem hz, ENNReal.ofReal_zero, zero_mul]
  have h6 : (∫⁻ z in Work.PerSector.slotBox (ι := Fin S.card)
        (Submission.BoseGases.dlBox (PBℓ v μ) (PBd v μ) u),
        ‖Submission.BoseGases.qLHSden S.card (PBℓ v μ) μ w w1 z‖ₑ)
      = ∫⁻ z in Submission.BoseGases.abox S.card (PBℓ v μ),
          (Work.PerSector.slotBox (ι := Fin S.card)
              (Submission.BoseGases.dlBox (PBℓ v μ) (PBd v μ) u)).indicator
            (fun _ => (1 : ℝ≥0∞)) z *
            ‖Submission.BoseGases.qLHSden S.card (PBℓ v μ) μ w w1 z‖ₑ :=
    (setLIntegral_indicator_one_mul (Submission.BoseGases.abox_measurable S.card (PBℓ v μ))
      (Work.PerSector.Work.PerSector.slotBox_measurable hBmeas) hbox_abox
      (fun z => ‖Submission.BoseGases.qLHSden S.card (PBℓ v μ) μ w w1 z‖ₑ)).symm
  -- conclude
  have hI : (∫⁻ z in Submission.BoseGases.abox S.card (PBℓ v μ),
        (Work.PerSector.slotBox (ι := Fin S.card)
            (Submission.BoseGases.dlBox (PBℓ v μ) (PBd v μ) u)).indicator
          (fun _ => (1 : ℝ≥0∞)) z *
          ‖Submission.BoseGases.qLHSden S.card (PBℓ v μ) μ w w1 z‖ₑ) = ⊤ := by
    have hbound : (∫⁻ x in Work.PerSector.slotBox (ι := Fin S.card)
        (Submission.BoseGases.dlBox (PBℓ v μ) (PBd v μ) u),
        ‖Submission.BoseGases.qLHSden S.card (PBℓ v μ) μ w w1 x‖ₑ) = ⊤ := by
      have hchain : ⊤ ≤ (MeasureTheory.volume : MeasureTheory.Measure
          (Work.PerSector.SlotOut n S → E3))
          (Work.PerSector.slotOutside (PBℓ v μ)
            (Submission.BoseGases.dlBox (PBℓ v μ) (PBd v μ) u) S)
          * (∫⁻ x in Work.PerSector.slotBox (ι := Fin S.card)
              (Submission.BoseGases.dlBox (PBℓ v μ) (PBd v μ) u),
              ‖Submission.BoseGases.qLHSden S.card (PBℓ v μ) μ w w1 x‖ₑ) := by
        rw [← hFtop, hsplit, h3, ← h5]
        exact h4
      by_contra hne
      exact not_le.mpr (ENNReal.mul_lt_top hvol_lt (lt_top_iff_ne_top.mpr hne)) hchain
    rw [← h6]; exact hbound
  rw [Submission.BoseGases.qLHSword]
  refine MeasureTheory.integral_undef ?_
  refine fun hint => ?_
  have hf : (∫⁻ z, ‖(fun x => (sharpBoxState (Submission.BoseGases.dlBox (PBℓ v μ) (PBd v μ) u)
        (fun _ : Submission.BoseGases.X S.card => (1 : ℝ)) x) ^ 2 *
        Submission.BoseGases.qLHSden S.card (PBℓ v μ) μ w w1 x) z‖ₑ ∂
      ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X S.card)).restrict
        (Submission.BoseGases.abox S.card (PBℓ v μ)))) < ⊤ := hint.hasFiniteIntegral
  simp only [] at hf
  rw [hsharp_swap] at hf
  rw [hI] at hf
  exact absurd hf (lt_irrefl _)

end Work.BoseFixB1B
