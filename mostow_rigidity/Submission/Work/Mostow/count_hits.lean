import Mathlib
import Submission.Work.Mostow.tiDefs
import Submission.Work.Mostow.stab_eq_blk
import Submission.Work.Mostow.volH_fermi_prod
import Submission.Work.Mostow.volH_le_card_mul_of_ae_count
import Submission.Work.Mostow.nearIdAt_conj
import Submission.Work.Mostow.fermi_image_measurable
import Submission.Work.Mostow.fund_domain_hull_null
import Submission.Work.Mostow.centralizer_acts_fermi

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory
open scoped ENNReal Pointwise

noncomputable section

set_option maxHeartbeats 0

/-! ## Small facts about the Fermi chart -/

/-- `NearIdAt` conjugation, restated. -/
private lemma ch_nearIdAt_conj {n : ℕ} (hA : POActionProp n) (hI : HypIsometryProp n)
    (g a : PO n 1) (z : E n) (η : ℝ) :
    NearIdAt (g⁻¹ * a * g) z η ↔ NearIdAt a (g • z) η :=
  Work.Mostow.nearIdAt_conj n hA hI g a z η

private lemma ch_nrmC_fermi (k m : ℕ) (v : E k) (w : E m) :
    nrmC k m (fermi k m v w) = sinhc ‖w‖ • w := by
  ext i; simp [nrmC, fermi]

private lemma ch_norm_nrmC_fermi (k m : ℕ) (v : E k) (w : E m) :
    ‖nrmC k m (fermi k m v w)‖ = Real.sinh ‖w‖ := by
  rw [ch_nrmC_fermi, norm_smul, Real.norm_eq_abs, abs_of_pos (fermi_sinhc_pos ‖w‖)]
  exact fermi_sinhc_mul_self ‖w‖

private lemma ch_fermi_inj (k m : ℕ) :
    Function.Injective (fun p : E k × E m => fermi k m p.1 p.2) := by
  intro p q h
  have h2 := congrArg (fermiInv k m) h
  rw [(fermi_inv k m).1 p.1 p.2, (fermi_inv k m).1 q.1 q.2] at h2
  exact h2

/-- The image part of the tube slice lies in the Fermi tube. -/
private lemma ch_image_subset_tube (j m : ℕ) (DY : Set (E j)) (ρ : ℝ) :
    (fun p : E j × E m => fermi j m p.1 p.2) ''
        (toMeasurable (volH j) DY ×ˢ Metric.closedBall 0 ρ) ⊆ tube j m ρ := by
  rintro u ⟨⟨v, w⟩, ⟨-, hw⟩, rfl⟩
  simp only [tube, Set.mem_setOf_eq]
  rw [ch_norm_nrmC_fermi]
  exact Real.sinh_le_sinh.mpr (by simpa [Metric.mem_closedBall, dist_eq_norm] using hw)

private lemma ch_smul_measurable {n : ℕ} (hI : HypIsometryProp n) (g : PO n 1) :
    Measurable (fun u : E n => g • u) :=
  ((HypIsoData.ofProp hI).contDiff_smul g).continuous.measurable

private lemma ch_smul_image_eq_preimage {n : ℕ} (hA : POActionProp n) (g : PO n 1) (s : Set (E n)) :
    (fun u : E n => g⁻¹ • u) '' s = (fun u : E n => g • u) ⁻¹' s := by
  have hA' := POBasic.ofProp hA
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change g • (g⁻¹ • y) ∈ s
    rw [← hA'.mul_smul, mul_inv_cancel, hA'.one_smul]
    exact hy
  · intro hx
    refine ⟨g • x, hx, ?_⟩
    change g⁻¹ • (g • x) = x
    rw [← hA'.mul_smul, inv_mul_cancel, hA'.one_smul]

/-! ## The main counting lemma -/

theorem count_hits (j m : ℕ) (hAj : Submission.Mostow.POActionProp j) (hIj : Submission.Mostow.HypIsometryProp j)
    (hA : Submission.Mostow.POActionProp (j + m)) (hI : Submission.Mostow.HypIsometryProp (j + m)) (hm : 1 ≤ m)
    (Λ : Subgroup (LeanEval.Geometry.MostowRigidity.PO (j + m) 1)) (hdisc : IsDiscrete (SetLike.coe Λ))
    (R : Submission.Mostow.E m ≃ₗᵢ[ℝ] Submission.Mostow.E m)
    (hb : Submission.Mostow.blk j m 1 R ∈ Λ) (hR : ∀ w : Submission.Mostow.E m, R w = w → w = 0)
    (DY : Set (Submission.Mostow.E j))
    (hDY : MeasureTheory.IsFundamentalDomain
        (Subgroup.closure (Submission.Mostow.resStd j m '' ((Subgroup.centralizer {Submission.Mostow.blk j m 1 R} ⊓ Λ : Subgroup (LeanEval.Geometry.MostowRigidity.PO (j + m) 1)) : Set (LeanEval.Geometry.MostowRigidity.PO (j + m) 1))))
        DY (Submission.Mostow.volH j))
    (D : Set (Submission.Mostow.E (j + m))) (hD : MeasureTheory.IsFundamentalDomain Λ D (Submission.Mostow.volH (j + m)))
    (ρ η₁ : ℝ) (hρ : 0 ≤ ρ)
    (htube : ∀ u : Submission.Mostow.E (j + m), u ∈ Submission.Mostow.tube j m ρ → Submission.Mostow.NearIdAt (Submission.Mostow.blk j m 1 R) u η₁)
    (Cj : ℕ)
    (hCj : ∀ w : Submission.Mostow.E (j + m), Submission.Mostow.NearIdAt (Submission.Mostow.blk j m 1 R) w η₁ →
        ({c : LeanEval.Geometry.MostowRigidity.PO (j + m) 1 | Submission.Mostow.NearIdAt c w η₁ ∧ ∃ γ ∈ Λ, c = γ⁻¹ * Submission.Mostow.blk j m 1 R * γ}.Finite ∧
         {c : LeanEval.Geometry.MostowRigidity.PO (j + m) 1 | Submission.Mostow.NearIdAt c w η₁ ∧ ∃ γ ∈ Λ, c = γ⁻¹ * Submission.Mostow.blk j m 1 R * γ}.ncard ≤ Cj))
    (hKfin : Finite {c : LeanEval.Geometry.MostowRigidity.PO (j + m) 1 // c ∈ Λ ∧ c ∈ Subgroup.centralizer {Submission.Mostow.blk j m 1 R} ∧ Submission.Mostow.resStd j m c = 1}) :
    ∀ᵐ z ∂((Submission.Mostow.volH (j + m)).restrict D),
      ∃ s : Finset Λ,
        s.card ≤ Cj * Nat.card {c : LeanEval.Geometry.MostowRigidity.PO (j + m) 1 // c ∈ Λ ∧ c ∈ Subgroup.centralizer {Submission.Mostow.blk j m 1 R} ∧ Submission.Mostow.resStd j m c = 1} ∧
        ∀ γ : Λ, (γ : LeanEval.Geometry.MostowRigidity.PO (j + m) 1) • z ∈ Work.Mostow.tiTubeSlice j m DY ρ → γ ∈ s := by
  classical
  have hAjP := POBasic.ofProp hAj
  have hAP := POBasic.ofProp hA
  have hAI := HypIsoData.ofProp hI
  have hMP : ∀ g : PO (j + m) 1, MeasurePreserving (fun u : E (j + m) => g • u)
      (volH (j + m)) (volH (j + m)) := hAI.measurePreserving_smul
  haveI : SMulInvariantMeasure (PO (j + m) 1) (E (j + m)) (volH (j + m)) :=
    ⟨fun c s hs => (hMP c).measure_preimage hs.nullMeasurableSet⟩
  haveI : Countable Λ := countable_of_isDiscrete (PO (j + m) 1) hdisc
  -- abbreviations
  set b : PO (j + m) 1 := blk j m 1 R with hbdef
  set Zb : Subgroup (PO (j + m) 1) := Subgroup.centralizer ({b} : Set (PO (j + m) 1)) with hZbdef
  set DY' : Set (E j) := toMeasurable (volH j) DY with hDY'def
  set ΓY : Subgroup (PO j 1) :=
    Subgroup.closure (resStd j m '' ((Zb ⊓ Λ : Subgroup (PO (j + m) 1)) : Set (PO (j + m) 1))) with hΓYdef
  have hDYΓ : IsFundamentalDomain ΓY DY (volH j) := hDY
  have hDY'meas : MeasurableSet DY' := measurableSet_toMeasurable _ _
  have hDY'ae : DY' =ᵐ[volH j] DY := hDY.nullMeasurableSet.toMeasurable_ae_eq
  have hDY'diff : volH j (DY' \ DY) = 0 := (ae_eq_set.mp hDY'ae).1
  have hDYdiff : volH j (DY \ DY') = 0 := (ae_eq_set.mp hDY'ae).2
  set I : Set (E (j + m)) :=
    (fun p : E j × E m => fermi j m p.1 p.2) '' (DY' ×ˢ Metric.closedBall 0 ρ) with hIdef
  have hImeas : MeasurableSet I := by
    rw [hIdef]
    exact fermi_image_measurable j m DY' (Metric.closedBall 0 ρ) hDY'meas measurableSet_closedBall
  have hSdef : tiTubeSlice j m DY ρ = toMeasurable (volH (j + m)) I := by
    rw [tiTubeSlice, hIdef, hDY'def]
  have hSmeas : MeasurableSet (tiTubeSlice j m DY ρ) := by
    rw [hSdef]; exact measurableSet_toMeasurable _ _
  have hSdiff : volH (j + m) (tiTubeSlice j m DY ρ \ I) = 0 := by
    have h : toMeasurable (volH (j + m)) I =ᵐ[volH (j + m)] I :=
      NullMeasurableSet.toMeasurable_ae_eq (hImeas.nullMeasurableSet (μ := volH (j + m)))
    have h2 := (ae_eq_set.mp h).1
    rwa [hSdef]
  have hI_tube : I ⊆ tube j m ρ := by
    rw [hIdef, hDY'def]
    exact ch_image_subset_tube j m DY ρ
  -- the bad set
  set K0 : Set (PO (j + m) 1) := {k | k ∈ Λ ∧ k ∈ Zb ∧ resStd j m k ≠ 1} with hK0def
  set BadB : Set (E (j + m)) := {u | u ∈ I ∧ ∃ k ∈ K0, k • u ∈ tiTubeSlice j m DY ρ} with hBadBdef
  set Bad : Set (E (j + m)) := (tiTubeSlice j m DY ρ \ I) ∪ BadB with hBaddef
  have hGood : ∀ u : E (j + m), u ∈ tiTubeSlice j m DY ρ → u ∉ Bad →
      ∀ k : PO (j + m) 1, k ∈ Λ → k ∈ Zb → resStd j m k ≠ 1 →
        k • u ∉ tiTubeSlice j m DY ρ := by
    intro u huS huBad k hkΛ hkZ hkres hku
    refine huBad (Or.inr ⟨?_, k, ⟨hkΛ, hkZ, hkres⟩, hku⟩)
    by_contra h
    exact huBad (Or.inl ⟨huS, h⟩)
  have hK0count : Countable {k : PO (j + m) 1 // k ∈ K0} :=
    (Function.Injective.countable (f := fun k : {k : PO (j + m) 1 // k ∈ K0} =>
      (⟨(k : PO (j + m) 1), k.2.1⟩ : Λ))
      (fun a b hab => Subtype.ext (congrArg (fun x : Λ => (x : PO (j + m) 1)) hab)))
  have hBadmeas : MeasurableSet Bad := by
    have hBadBmeas : MeasurableSet BadB := by
      have hset : {u : E (j + m) | u ∈ I ∧ ∃ k ∈ K0, k • u ∈ tiTubeSlice j m DY ρ}
          = I ∩ ⋃ (k : {k : PO (j + m) 1 // k ∈ K0}),
              (fun u : E (j + m) => (k : PO (j + m) 1) • u) ⁻¹' (tiTubeSlice j m DY ρ) := by
        ext u
        simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iUnion, Set.mem_preimage]
        constructor
        · rintro ⟨huI, k, hk, hku⟩; exact ⟨huI, ⟨k, hk⟩, hku⟩
        · rintro ⟨huI, ⟨k, hk⟩, hku⟩; exact ⟨huI, k, hk, hku⟩
      rw [hBadBdef, hset]
      refine hImeas.inter ?_
      exact MeasurableSet.iUnion fun k => hSmeas.preimage (ch_smul_measurable hI (k : PO (j + m) 1))
    rw [hBaddef]
    exact (hSmeas.diff hImeas).union hBadBmeas
  -- BadB is null
  have hBadB_null : volH (j + m) BadB = 0 := by
    haveI := hK0count
    have hcover : BadB ⊆ ⋃ (k : {k : PO (j + m) 1 // k ∈ K0}),
        ({u : E (j + m) | u ∈ I ∧ (k : PO (j + m) 1) • u ∈ I} ∪
         {u : E (j + m) | (k : PO (j + m) 1) • u ∈ (tiTubeSlice j m DY ρ \ I)}) := by
      rintro u ⟨huI, k, hkK0, hkS⟩
      rcases em ((k : PO (j + m) 1) • u ∈ I) with h | h
      · exact Set.mem_iUnion.mpr ⟨⟨k, hkK0⟩, Or.inl ⟨huI, h⟩⟩
      · exact Set.mem_iUnion.mpr ⟨⟨k, hkK0⟩, Or.inr ⟨hkS, h⟩⟩
    refine measure_mono_null hcover ?_
    refine measure_iUnion_null fun k => ?_
    refine measure_union_null ?_ ?_
    · -- {u | u ∈ I ∧ k • u ∈ I} is null
      have hkK0 : (k : PO (j + m) 1) ∈ K0 := k.2
      have hkΛ : (k : PO (j + m) 1) ∈ Λ := hkK0.1
      have hkZ : (k : PO (j + m) 1) ∈ Zb := hkK0.2.1
      have hkres : resStd j m (k : PO (j + m) 1) ≠ 1 := hkK0.2.2
      have hkZ' : (k : PO (j + m) 1) ∈
          Subgroup.centralizer ({blk j m 1 R} : Set (PO (j + m) 1)) := by
        rw [hZbdef] at hkZ
        rwa [hbdef] at hkZ
      have hmemΓ : resStd j m (k : PO (j + m) 1) ∈ ΓY := by
        rw [hΓYdef]
        exact Subgroup.subset_closure ⟨(k : PO (j + m) 1), ⟨hkZ, hkΛ⟩, rfl⟩
      let γ0 : ΓY := ⟨(resStd j m (k : PO (j + m) 1))⁻¹, ΓY.inv_mem hmemΓ⟩
      have hγ0ne : γ0 ≠ 1 := by
        intro h
        have h2 : (resStd j m (k : PO (j + m) 1))⁻¹ = 1 :=
          congrArg (fun x : ΓY => (x : PO j 1)) h
        rw [inv_eq_one] at h2
        exact hkres h2
      have hfund := fund_domain_hull_null j hIj ΓY DY hDYΓ γ0 hγ0ne
      have hfund' : volH j (((fun v : E j => (resStd j m (k : PO (j + m) 1))⁻¹ • v) '' DY') ∩ DY') = 0 := by
        have h := hfund
        rw [← hDY'def] at h
        rw [Set.inter_comm]
        exact h
      have hmeasA : MeasurableSet ((fun v : E j => (resStd j m (k : PO (j + m) 1))⁻¹ • v) '' DY') := by
        rw [hDY'def, ch_smul_image_eq_preimage hAj (resStd j m (k : PO (j + m) 1))
          (toMeasurable (volH j) DY)]
        exact (measurableSet_toMeasurable _ _).preimage
          (ch_smul_measurable hIj (resStd j m (k : PO (j + m) 1)))
      have hsub : {u : E (j + m) | u ∈ I ∧ (k : PO (j + m) 1) • u ∈ I} ⊆
          (fun p : E j × E m => fermi j m p.1 p.2) ''
            (((fun v : E j => (resStd j m (k : PO (j + m) 1))⁻¹ • v) '' DY' ∩ DY')
              ×ˢ Metric.closedBall 0 ρ) := by
        rintro u ⟨huI, hkuI⟩
        rw [hIdef] at huI hkuI
        obtain ⟨⟨v, w⟩, ⟨hv, hw⟩, rfl⟩ := huI
        obtain ⟨⟨v', w'⟩, ⟨hv', hw'⟩, heq⟩ := hkuI
        have hact : (k : PO (j + m) 1) • fermi j m v w =
            fermi j m ((resStd j m (k : PO (j + m) 1)) • v)
              (nrmStd j m (k : PO (j + m) 1) w) :=
          centralizer_acts_fermi j m hAj hIj hA hI R hR (k : PO (j + m) 1) hkZ' v w
        have hv'mem : (resStd j m (k : PO (j + m) 1)) • v ∈ DY' := by
          have h1 : (resStd j m (k : PO (j + m) 1)) • v
              = (fermiInv j m ((k : PO (j + m) 1) • fermi j m v w)).1 := by
            rw [hact, (fermi_inv j m).1]
          rw [h1, ← heq, (fermi_inv j m).1]
          exact hv'
        have hv_inv : (resStd j m (k : PO (j + m) 1))⁻¹
            • ((resStd j m (k : PO (j + m) 1)) • v) = v := by
          rw [← hAjP.mul_smul, inv_mul_cancel, hAjP.one_smul]
        exact ⟨(v, w), ⟨⟨⟨(resStd j m (k : PO (j + m) 1)) • v, ⟨hv'mem, hv_inv⟩⟩, hv⟩, hw⟩, rfl⟩
      refine measure_mono_null hsub ?_
      rw [volH_fermi_prod j m ((fun v : E j => (resStd j m (k : PO (j + m) 1))⁻¹ • v) '' DY' ∩ DY')
        (Metric.closedBall 0 ρ) (hmeasA.inter hDY'meas) measurableSet_closedBall]
      rw [hfund']
      simp
    · -- {u | k • u ∈ S \ I} is null
      have hmeasT : MeasurableSet (tiTubeSlice j m DY ρ \ I) := hSmeas.diff hImeas
      have hpre : {u : E (j + m) | (k : PO (j + m) 1) • u ∈ (tiTubeSlice j m DY ρ \ I)}
          = (fun u : E (j + m) => (k : PO (j + m) 1) • u) ⁻¹' (tiTubeSlice j m DY ρ \ I) := rfl
      rw [hpre, SMulInvariantMeasure.measure_preimage_smul (k : PO (j + m) 1) hmeasT]
      exact hSdiff
  have hBad_null : volH (j + m) Bad = 0 := by
    rw [hBaddef]
    exact measure_union_null hSdiff hBadB_null
  -- the a.e. statement
  have hBadAll_null : volH (j + m)
      (⋃ γ : Λ, (fun x : E (j + m) => (γ : PO (j + m) 1) • x) ⁻¹' Bad) = 0 := by
    refine measure_iUnion_null fun γ => ?_
    rw [SMulInvariantMeasure.measure_preimage_smul (γ : PO (j + m) 1) hBadmeas]
    exact hBad_null
  have hgood_ae : ∀ᵐ z ∂((volH (j + m)).restrict D),
      ∀ γ : Λ, (γ : PO (j + m) 1) • z ∉ Bad := by
    rw [ae_restrict_iff'₀ hD.nullMeasurableSet]
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hBadAll_null] with z hz hzD
    intro γ hγ
    exact hz (Set.mem_iUnion.mpr ⟨γ, hγ⟩)
  -- the counting
  filter_upwards [hgood_ae] with z hgoodz
  by_cases hΔ : ∃ γ : Λ, (γ : PO (j + m) 1) • z ∈ tiTubeSlice j m DY ρ
  · obtain ⟨γ₁, hγ₁⟩ := hΔ
    set u : E (j + m) := (γ₁ : PO (j + m) 1) • z with hu
    have huS : u ∈ tiTubeSlice j m DY ρ := hγ₁
    have huBad : u ∉ Bad := hgoodz γ₁
    have huTube : u ∈ tube j m ρ := by
      have huI : u ∈ I := by
        by_contra h
        exact huBad (Or.inl ⟨huS, h⟩)
      exact hI_tube huI
    set Sig : Set (PO (j + m) 1) := {c | NearIdAt c u η₁ ∧ ∃ γ ∈ Λ, c = γ⁻¹ * b * γ} with hSigdef
    have hSigfin : Sig.Finite := (hCj u (htube u huTube)).1
    have hSigcard : Sig.ncard ≤ Cj := (hCj u (htube u huTube)).2
    set Δs : Set Λ := {γ : Λ | (γ : PO (j + m) 1) • z ∈ tiTubeSlice j m DY ρ} with hΔsdef
    let Φ : Λ → PO (j + m) 1 := fun γ =>
      (((γ * γ₁⁻¹ : Λ)) : PO (j + m) 1)⁻¹ * b * (((γ * γ₁⁻¹ : Λ)) : PO (j + m) 1)
    have hΦmem : ∀ γ : Λ, γ ∈ Δs → Φ γ ∈ Sig := by
      intro γ hγ
      have hΦeq : Φ γ = (((γ * γ₁⁻¹ : Λ)) : PO (j + m) 1)⁻¹ * b * (((γ * γ₁⁻¹ : Λ)) : PO (j + m) 1) := rfl
      rw [hΦeq]
      have hzu : (((γ * γ₁⁻¹ : Λ)) : PO (j + m) 1) • u = (γ : PO (j + m) 1) • z := by
        rw [hu]
        calc (((γ * γ₁⁻¹ : Λ)) : PO (j + m) 1) • ((γ₁ : PO (j + m) 1) • z)
            = ((((γ * γ₁⁻¹ : Λ)) : PO (j + m) 1) * (γ₁ : PO (j + m) 1)) • z :=
                (hAP.mul_smul _ _ _).symm
          _ = (((γ : PO (j + m) 1) * (γ₁ : PO (j + m) 1)⁻¹) * (γ₁ : PO (j + m) 1)) • z := by
                rw [Subgroup.coe_mul, Subgroup.coe_inv]
          _ = (γ : PO (j + m) 1) • z := by rw [mul_assoc, inv_mul_cancel, mul_one]
      refine ⟨?_, ?_⟩
      · rw [ch_nearIdAt_conj hA hI (((γ * γ₁⁻¹ : Λ)) : PO (j + m) 1) b u η₁, hzu]
        have hγTube : (γ : PO (j + m) 1) • z ∈ tube j m ρ := by
          have hγI : (γ : PO (j + m) 1) • z ∈ I := by
            by_contra h
            exact hgoodz γ (Or.inl ⟨hγ, h⟩)
          exact hI_tube hγI
        exact htube _ hγTube
      · exact ⟨(((γ * γ₁⁻¹ : Λ)) : PO (j + m) 1), (γ * γ₁⁻¹ : Λ).2, rfl⟩
    -- the kernel
    set Pker : Set Λ := {k : Λ | (k : PO (j + m) 1) ∈ Zb ∧ resStd j m (k : PO (j + m) 1) = 1}
      with hPkerdef
    have hPker_fin : Pker.Finite := by
      haveI : Finite {c : PO (j + m) 1 // c ∈ Λ ∧ c ∈ Zb ∧ resStd j m c = 1} := hKfin
      refine Finite.of_injective
        (fun k : Pker => (⟨(k.1 : PO (j + m) 1), k.1.2, k.2.1, k.2.2⟩ :
          {c : PO (j + m) 1 // c ∈ Λ ∧ c ∈ Zb ∧ resStd j m c = 1})) ?_
      intro a b hab
      have h2 := congrArg (fun x : {c : PO (j + m) 1 // c ∈ Λ ∧ c ∈ Zb ∧ resStd j m c = 1} =>
        (x : PO (j + m) 1)) hab
      exact Subtype.ext (Subtype.ext h2)
    have hPker_card : Pker.ncard ≤
        Nat.card {c : PO (j + m) 1 // c ∈ Λ ∧ c ∈ Zb ∧ resStd j m c = 1} := by
      haveI : Finite {c : PO (j + m) 1 // c ∈ Λ ∧ c ∈ Zb ∧ resStd j m c = 1} := hKfin
      rw [← Nat.card_coe_set_eq]
      refine Nat.card_le_card_of_injective
        (fun k : Pker => (⟨(k.1 : PO (j + m) 1), k.1.2, k.2.1, k.2.2⟩ :
          {c : PO (j + m) 1 // c ∈ Λ ∧ c ∈ Zb ∧ resStd j m c = 1})) ?_
      intro a b hab
      have h2 := congrArg (fun x : {c : PO (j + m) 1 // c ∈ Λ ∧ c ∈ Zb ∧ resStd j m c = 1} =>
        (x : PO (j + m) 1)) hab
      exact Subtype.ext (Subtype.ext h2)
    -- the covering
    set T : Finset (PO (j + m) 1) := hSigfin.toFinset with hTdef
    have hTmem : ∀ c : PO (j + m) 1, c ∈ T ↔ c ∈ Sig := by
      intro c
      rw [hTdef]
      exact Set.Finite.mem_toFinset hSigfin
    have hTcard : T.card ≤ Cj := by
      rw [hTdef, ← Set.ncard_eq_toFinset_card Sig hSigfin]
      exact hSigcard
    let rep : PO (j + m) 1 → Λ := fun c =>
      if h : ∃ γ : Λ, γ ∈ Δs ∧ Φ γ = c then h.choose else 1
    have hrep : ∀ c : PO (j + m) 1, (∃ γ : Λ, γ ∈ Δs ∧ Φ γ = c) →
        rep c ∈ Δs ∧ Φ (rep c) = c := by
      intro c h
      have h1 : rep c = h.choose := dif_pos h
      rw [h1]
      exact h.choose_spec
    set Sf : Finset Λ := T.biUnion (fun c => hPker_fin.toFinset.image (fun k => k * rep c))
      with hSfdef
    have hcover : Δs ⊆ ↑Sf := by
      intro γ hγ
      have hΦSig : Φ γ ∈ Sig := hΦmem γ hγ
      have hΦT : Φ γ ∈ T := (hTmem _).mpr hΦSig
      obtain ⟨hrepΔ, hrepΦ⟩ := hrep (Φ γ) ⟨γ, hγ, rfl⟩
      set π : Λ := rep (Φ γ) with hπdef
      set kk : Λ := γ * π⁻¹ with hkkdef
      have hΦform : ∀ x : Λ, Φ x = (γ₁ : PO (j + m) 1) *
          ((x : PO (j + m) 1)⁻¹ * b * (x : PO (j + m) 1)) * (γ₁ : PO (j + m) 1)⁻¹ := by
        intro x
        show (((x * γ₁⁻¹ : Λ)) : PO (j + m) 1)⁻¹ * b * (((x * γ₁⁻¹ : Λ)) : PO (j + m) 1)
            = (γ₁ : PO (j + m) 1) * ((x : PO (j + m) 1)⁻¹ * b * (x : PO (j + m) 1))
              * (γ₁ : PO (j + m) 1)⁻¹
        rw [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      have hAeq : ((γ : PO (j + m) 1)⁻¹ * b * (γ : PO (j + m) 1))
          = ((π : PO (j + m) 1)⁻¹ * b * (π : PO (j + m) 1)) := by
        have h1 : Φ γ = Φ π := hrepΦ.symm
        rw [hΦform γ, hΦform π] at h1
        calc (γ : PO (j + m) 1)⁻¹ * b * (γ : PO (j + m) 1)
            = (γ₁ : PO (j + m) 1)⁻¹ * ((γ₁ : PO (j + m) 1)
                * ((γ : PO (j + m) 1)⁻¹ * b * (γ : PO (j + m) 1))
                * (γ₁ : PO (j + m) 1)⁻¹) * (γ₁ : PO (j + m) 1) := by group
          _ = (γ₁ : PO (j + m) 1)⁻¹ * ((γ₁ : PO (j + m) 1)
                * ((π : PO (j + m) 1)⁻¹ * b * (π : PO (j + m) 1))
                * (γ₁ : PO (j + m) 1)⁻¹) * (γ₁ : PO (j + m) 1) := by rw [h1]
          _ = (π : PO (j + m) 1)⁻¹ * b * (π : PO (j + m) 1) := by group
      have hkkZ : (kk : PO (j + m) 1) ∈ Zb := by
        have hkkc : (kk : PO (j + m) 1) = (γ : PO (j + m) 1) * (π : PO (j + m) 1)⁻¹ := by
          rw [hkkdef, Subgroup.coe_mul, Subgroup.coe_inv]
        have hbkk : (kk : PO (j + m) 1)⁻¹ * b * (kk : PO (j + m) 1) = b := by
          rw [hkkc]
          calc ((γ : PO (j + m) 1) * (π : PO (j + m) 1)⁻¹)⁻¹ * b
                * ((γ : PO (j + m) 1) * (π : PO (j + m) 1)⁻¹)
              = (π : PO (j + m) 1) * ((γ : PO (j + m) 1)⁻¹ * b * (γ : PO (j + m) 1))
                * (π : PO (j + m) 1)⁻¹ := by group
            _ = (π : PO (j + m) 1) * ((π : PO (j + m) 1)⁻¹ * b * (π : PO (j + m) 1))
                * (π : PO (j + m) 1)⁻¹ := by rw [hAeq]
            _ = b := by group
        have hkbk : b * (kk : PO (j + m) 1) = (kk : PO (j + m) 1) * b := by
          calc b * (kk : PO (j + m) 1)
              = ((kk : PO (j + m) 1) * (kk : PO (j + m) 1)⁻¹) * b * (kk : PO (j + m) 1) := by group
            _ = (kk : PO (j + m) 1) * ((kk : PO (j + m) 1)⁻¹ * b * (kk : PO (j + m) 1)) := by group
            _ = (kk : PO (j + m) 1) * b := by rw [hbkk]
        rw [hZbdef, Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        subst hy
        exact hkbk
      have hkkres : resStd j m (kk : PO (j + m) 1) = 1 := by
        by_contra hne
        have hπS : (π : PO (j + m) 1) • z ∈ tiTubeSlice j m DY ρ := hrepΔ
        have hπBad : (π : PO (j + m) 1) • z ∉ Bad := hgoodz π
        refine hGood ((π : PO (j + m) 1) • z) hπS hπBad (kk : PO (j + m) 1) kk.2 hkkZ hne ?_
        have hcoee : (kk : PO (j + m) 1) * (π : PO (j + m) 1) = (γ : PO (j + m) 1) := by
          rw [hkkdef, Subgroup.coe_mul, Subgroup.coe_inv]
          group
        show (kk : PO (j + m) 1) • ((π : PO (j + m) 1) • z) ∈ tiTubeSlice j m DY ρ
        rw [← hAP.mul_smul, hcoee]
        exact hγ
      have hkkP : kk ∈ Pker := ⟨hkkZ, hkkres⟩
      have hγeq : γ = kk * rep (Φ γ) := by
        rw [hkkdef]
        show γ = (γ * π⁻¹) * rep (Φ γ)
        rw [← hπdef]
        group
      rw [hSfdef]
      refine Finset.mem_biUnion.mpr ⟨Φ γ, hΦT, ?_⟩
      refine Finset.mem_image.mpr ⟨kk, ?_, ?_⟩
      · rw [Set.Finite.mem_toFinset]
        exact hkkP
      · exact hγeq.symm
    refine ⟨Sf, ?_, ?_⟩
    · have hSfcard : Sf.card ≤ T.card * Pker.ncard := by
        rw [hSfdef]
        refine Finset.card_biUnion_le_card_mul T _ Pker.ncard ?_
        intro c hc
        calc (hPker_fin.toFinset.image (fun k => k * rep c)).card
            ≤ hPker_fin.toFinset.card := Finset.card_image_le
          _ = Pker.ncard := (Set.ncard_eq_toFinset_card Pker hPker_fin).symm
      calc Sf.card ≤ T.card * Pker.ncard := hSfcard
        _ ≤ Cj * Nat.card {c : PO (j + m) 1 // c ∈ Λ ∧ c ∈ Zb ∧ resStd j m c = 1} :=
            Nat.mul_le_mul hTcard hPker_card
    · intro γ hγ
      exact hcover hγ
  · exact ⟨∅, by simp, fun γ hγ => absurd ⟨γ, hγ⟩ hΔ⟩

end

end Work.Mostow
