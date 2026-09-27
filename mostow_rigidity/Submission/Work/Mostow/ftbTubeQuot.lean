import Mathlib
import Submission.Work.Mostow.gapAEvenDefs
import Submission.Work.Mostow.fermi_measurePreserving
import Submission.Work.Mostow.volH_fermi_prod
import Submission.Work.Mostow.fermi_image_measurable
import Submission.Work.Mostow.resStdDiscreteStrata
import Submission.Work.Mostow.volH_le_card_mul_of_ae_count
import Submission.Work.Mostow.fund_domain_hull_null
import Submission.Work.Mostow.finite_nearStab
import Submission.Work.Mostow.ftbCountInter
import Submission.Work.Mostow.ftbResStdMul

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory
open scoped ENNReal Pointwise

noncomputable section

/-! ## Elementary chart facts used by the tube computation -/

instance ftbqMulActionPO (n : ℕ) : MulAction (PO n 1) (E n) where
  one_smul := poOneSMul
  mul_smul := poMulSMul

lemma ftbq_sinhc_mul_self (s : ℝ) : sinhc s * s = Real.sinh s := by
  rw [sinhc]
  by_cases h : s = 0
  · simp [h]
  · simp only [h, ↓reduceIte]
    field_simp

lemma ftbq_nrmC_fermi (j m : ℕ) (v : E j) (w : E m) :
    nrmC j m (fermi j m v w) = sinhc ‖w‖ • w := by
  ext i; simp [nrmC, fermi]

lemma ftbq_norm_nrmC_fermi (j m : ℕ) (v : E j) (w : E m) :
    ‖nrmC j m (fermi j m v w)‖ = Real.sinh ‖w‖ := by
  rw [ftbq_nrmC_fermi, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (le_of_lt (fermi_sinhc_pos ‖w‖)), ftbq_sinhc_mul_self]

lemma ftbq_fermi_mem_tube (j m : ℕ) (ρ : ℝ) (v : E j) (w : E m) :
    fermi j m v w ∈ tube j m ρ ↔ ‖w‖ ≤ ρ := by
  rw [tube, Set.mem_ofPred_eq, ftbq_norm_nrmC_fermi]
  exact Real.sinh_le_sinh

lemma ftbq_fermi_zero (j m : ℕ) : fermi j m (0 : E j) (0 : E m) = 0 := by
  apply WithLp.ofLp_injective
  funext i
  refine Fin.addCases (motive := fun i =>
    WithLp.ofLp (fermi j m (0 : E j) (0 : E m)) i = WithLp.ofLp (0 : E (j + m)) i)
    (fun i => ?_) (fun i => ?_) i <;> simp [fermi]

lemma ftbq_measurableSet_smul (j : ℕ) (hIj : HypIsometryProp j) (g : PO j 1) {S : Set (E j)}
    (hS : MeasurableSet S) : MeasurableSet (g • S) := by
  haveI : MeasurableConstSMul (PO j 1) (E j) :=
    ⟨fun c => (HypIsoData.ofProp hIj).contDiff_smul c |>.continuous.measurable⟩
  have h : (g • S : Set (E j)) = (fun x : E j => g⁻¹ • x) ⁻¹' S := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      show g⁻¹ • (g • x) ∈ S
      rw [inv_smul_smul]
      exact hx
    · intro hy
      exact ⟨g⁻¹ • y, hy, by
        show g • (g⁻¹ • y) = y
        rw [smul_inv_smul]⟩
  rw [h]
  exact (measurable_const_smul g⁻¹) hS

lemma ftbq_po_eq_of_smul_eq (j : ℕ) (hAj : POActionProp j) {g h : PO j 1}
    (hh : ∀ v : E j, g • v = h • v) : g = h := by
  have hb := POBasic.ofProp hAj
  have h1 : g⁻¹ * h = 1 := hb.faithful (g⁻¹ * h) fun v => by
    rw [hb.mul_smul g⁻¹ h v, ← hh v, ← hb.mul_smul g⁻¹ g v, inv_mul_cancel, hb.one_smul]
  exact inv_mul_eq_one.mp h1

lemma ftbq_continuous_nrmC (j m : ℕ) : Continuous (nrmC j m) := by
  rw [show nrmC j m = fun u : E (j + m) => WithLp.toLp 2 (fun i : Fin m => u (Fin.natAdd j i))
    from rfl]
  fun_prop

theorem ftbTubeQuot (j m : ℕ) (hAj : Submission.Mostow.POActionProp j)
    (hIj : Submission.Mostow.HypIsometryProp j)
    (hA : Submission.Mostow.POActionProp (j + m)) (hI : Submission.Mostow.HypIsometryProp (j + m))
    (Λ : Subgroup (PO (j + m) 1)) (R : E m ≃ₗᵢ[ℝ] E m) (Dc : Set (E (j + m))) (DY : Set (E j))
    (ρ : ℝ) (hρ : 0 ≤ ρ) (hdis : IsDiscrete (SetLike.coe Λ)) (hb : blk j m 1 R ∈ Λ)
    (hnfv : ∀ w, R w = w → w = 0)
    (hblk : ∀ c ∈ (Subgroup.centralizer {blk j m 1 R} ⊓ Λ : Subgroup (PO (j + m) 1)),
      ∀ (v : E j) (w : E m),
        (c : PO (j + m) 1) • fermi j m v w = fermi j m (resStd j m (c : PO (j + m) 1) • v)
          (nrmStd j m (c : PO (j + m) 1) w))
    (hDc : IsFundamentalDomain (↥(Subgroup.centralizer {blk j m 1 R} ⊓ Λ : Subgroup (PO (j + m) 1)))
      Dc (volH (j + m)))
    (hDY : IsFundamentalDomain
      (Subgroup.closure (resStd j m '' ((Subgroup.centralizer {blk j m 1 R} ⊓ Λ : Subgroup (PO (j + m) 1)) :
        Set (PO (j + m) 1)))) DY (volH j)) :
    volH j DY * tubeMeasure j m (Metric.closedBall 0 ρ) ≤
      (Nat.card {c : PO (j + m) 1 // c ∈ Λ ∧ c ∈ Subgroup.centralizer {blk j m 1 R} ∧
        resStd j m c = 1} : ENNReal) * volH (j + m) (tube j m ρ ∩ Dc) := by
  classical
  have hIdj : HypIsoData j := HypIsoData.ofProp hIj
  have hIdn : HypIsoData (j + m) := HypIsoData.ofProp hI
  -- the centraliser of the block element inside `Λ`
  let C : Subgroup (PO (j + m) 1) :=
    Subgroup.centralizer ({blk j m 1 R} : Set (PO (j + m) 1)) ⊓ Λ
  have hCsub : (C : Set (PO (j + m) 1)) ⊆ (Λ : Set (PO (j + m) 1)) := fun c hc => hc.2
  haveI : Countable C := (countable_of_isDiscrete (PO (j + m) 1) hdis).mono hCsub
  haveI : MeasurableConstSMul (PO (j + m) 1) (E (j + m)) :=
    ⟨fun c => (hIdn.contDiff_smul c).continuous.measurable⟩
  haveI : MeasurableConstSMul (PO j 1) (E j) :=
    ⟨fun c => (hIdj.contDiff_smul c).continuous.measurable⟩
  haveI : SMulInvariantMeasure (PO j 1) (E j) (volH j) :=
    ⟨fun c s hs => (hIdj.measurePreserving_smul c).measure_preimage hs.nullMeasurableSet⟩
  haveI : MeasurableConstSMul C (E (j + m)) :=
    ⟨fun c => (hIdn.contDiff_smul (c : PO (j + m) 1)).continuous.measurable⟩
  haveI : SMulInvariantMeasure C (E (j + m)) (volH (j + m)) :=
    ⟨fun c s hs =>
      (hIdn.measurePreserving_smul (c : PO (j + m) 1)).measure_preimage hs.nullMeasurableSet⟩
  -- the Fermi slice and its volume
  let DY' : Set (E j) := toMeasurable (volH j) DY
  let F : Set (E (j + m)) :=
    (fun p : E j × E m => fermi j m p.1 p.2) '' (DY' ×ˢ Metric.closedBall (0 : E m) ρ)
  have hDY'meas : MeasurableSet DY' := measurableSet_toMeasurable (volH j) DY
  have hball : MeasurableSet (Metric.closedBall (0 : E m) ρ) :=
    Metric.isClosed_closedBall.measurableSet
  have hFmeas : MeasurableSet F := fermi_image_measurable j m DY' _ hDY'meas hball
  have hFvol : volH (j + m) F = volH j DY * tubeMeasure j m (Metric.closedBall (0 : E m) ρ) := by
    show (volH (j + m))
        ((fun p : E j × E m => fermi j m p.1 p.2) '' (DY' ×ˢ Metric.closedBall (0 : E m) ρ)) = _
    rw [volH_fermi_prod j m DY' (Metric.closedBall (0 : E m) ρ) hDY'meas hball]
    congr 1
    exact measure_toMeasurable DY
  have hFsub : F ⊆ tube j m ρ := by
    rintro z ⟨p, hp, rfl⟩
    rw [ftbq_fermi_mem_tube]
    have h2 : dist p.2 (0 : E m) ≤ ρ := Metric.mem_closedBall.mp hp.2
    rwa [dist_eq_norm, sub_zero] at h2
  -- the tube is invariant under the centraliser
  have hTinv : ∀ c : C, ∀ u : E (j + m), c • u ∈ tube j m ρ ↔ u ∈ tube j m ρ := by
    intro c u
    show (c : PO (j + m) 1) • u ∈ tube j m ρ ↔ u ∈ tube j m ρ
    rw [tube, Set.mem_ofPred_eq, Set.mem_ofPred_eq]
    have hnrm : nrmC j m ((c : PO (j + m) 1) • u)
        = nrmStd j m (c : PO (j + m) 1) (nrmC j m u) := by
      have h1 : (c : PO (j + m) 1) • u
          = fermi j m (resStd j m (c : PO (j + m) 1) • (fermiInv j m u).1)
              (nrmStd j m (c : PO (j + m) 1) (fermiInv j m u).2) := by
        conv_lhs => rw [← (fermi_inv j m).2.1 u]
        rw [hblk (c : PO (j + m) 1) c.2 (fermiInv j m u).1 (fermiInv j m u).2]
      rw [h1, ftbq_nrmC_fermi]
      conv_rhs => rw [← (fermi_inv j m).2.1 u, ftbq_nrmC_fermi]
      simp only [map_smul, LinearIsometryEquiv.norm_map]
    rw [hnrm, LinearIsometryEquiv.norm_map]
  have hTubeMeas : MeasurableSet (tube j m ρ) := by
    have h : tube j m ρ = nrmC j m ⁻¹' Metric.closedBall (0 : E m) (Real.sinh ρ) := by
      ext u; simp [tube, Metric.mem_closedBall, dist_eq_norm]
    rw [h]
    exact Metric.isClosed_closedBall.measurableSet.preimage (ftbq_continuous_nrmC j m).measurable
  -- the kernel is finite
  have hKfin : ({c : PO (j + m) 1 | c ∈ Λ ∧ c ∈ Subgroup.centralizer {blk j m 1 R} ∧
      resStd j m c = 1} : Set (PO (j + m) 1)).Finite := by
    have hfin : ({γ : Λ | hdist (0 : E (j + m)) ((γ : PO (j + m) 1) • (0 : E (j + m))) ≤ 0}).Finite :=
      finite_nearStab (POBasic.ofProp hA) hIdn hdis (0 : ℝ)
    refine (hfin.image (fun γ : Λ => (γ : PO (j + m) 1))).subset ?_
    rintro c ⟨hcΛ, hccent, hrc⟩
    refine ⟨⟨c, hcΛ⟩, ?_, rfl⟩
    have hcC : c ∈ C := ⟨hccent, hcΛ⟩
    have h0 : c • (0 : E (j + m)) = 0 := by
      rw [← ftbq_fermi_zero j m,
        hblk c hcC (0 : E j) (0 : E m), hrc, (POBasic.ofProp hAj).one_smul (0 : E j),
        map_zero, ftbq_fermi_zero]
    show hdist (0 : E (j + m)) ((⟨c, hcΛ⟩ : Λ) • (0 : E (j + m))) ≤ 0
    rw [show ((⟨c, hcΛ⟩ : Λ) • (0 : E (j + m))) = 0 from h0]
    exact le_of_eq ((hIdn.eq_zero 0 0).mpr rfl)
  haveI : Fintype {c : PO (j + m) 1 // c ∈ Λ ∧ c ∈ Subgroup.centralizer {blk j m 1 R} ∧
      resStd j m c = 1} := hKfin.fintype
  -- the `C`-orbits of the slice
  let Pairs : Type := {p : C × C //
    resStd j m (p.1 : PO (j + m) 1) ≠ resStd j m (p.2 : PO (j + m) 1)}
  let Bad : Set (E (j + m)) := ⋃ p : Pairs,
    ((p.1.1 : PO (j + m) 1)⁻¹ • F ∩ (p.1.2 : PO (j + m) 1)⁻¹ • F)
  let BadY : Set (E j) := ⋃ p : Pairs,
    ((resStd j m (p.1.1 : PO (j + m) 1))⁻¹ • DY' ∩
      (resStd j m (p.1.2 : PO (j + m) 1))⁻¹ • DY')
  have hBadmeas : MeasurableSet Bad :=
    MeasurableSet.iUnion fun p : Pairs =>
      (ftbq_measurableSet_smul (j + m) hI _ hFmeas).inter
        (ftbq_measurableSet_smul (j + m) hI _ hFmeas)
  have hBadPo : ∀ z : E (j + m), z ∈ Bad ↔ ∃ c₁ c₂ : C,
      resStd j m (c₁ : PO (j + m) 1) ≠ resStd j m (c₂ : PO (j + m) 1) ∧
        (c₁ : PO (j + m) 1) • z ∈ F ∧ (c₂ : PO (j + m) 1) • z ∈ F := by
    intro z
    constructor
    · intro hz
      obtain ⟨p, hp⟩ := Set.mem_iUnion.mp hz
      have h1 : (p.1.1 : PO (j + m) 1) • z ∈ F := by
        have h := hp.1
        rwa [Set.mem_inv_smul_set_iff] at h
      have h2 : (p.1.2 : PO (j + m) 1) • z ∈ F := by
        have h := hp.2
        rwa [Set.mem_inv_smul_set_iff] at h
      exact ⟨p.1.1, p.1.2, p.2, h1, h2⟩
    · rintro ⟨c₁, c₂, hne, h1, h2⟩
      refine Set.mem_iUnion.mpr ⟨⟨(c₁, c₂), hne⟩, ?_, ?_⟩
      · rwa [Set.mem_inv_smul_set_iff]
      · rwa [Set.mem_inv_smul_set_iff]
  have hTinvPO : ∀ c : PO (j + m) 1, c ∈ C → ∀ u : E (j + m),
      c • u ∈ tube j m ρ ↔ u ∈ tube j m ρ := fun c hc u => hTinv ⟨c, hc⟩ u
  have hBadTube : Bad ⊆ tube j m ρ := by
    intro z hz
    obtain ⟨c₁, c₂, hne, h1, h2⟩ := (hBadPo z).mp hz
    exact (hTinvPO (c₁ : PO (j + m) 1) c₁.2 z).mp (hFsub h1)
  have hBadYmeas : MeasurableSet BadY :=
    MeasurableSet.iUnion fun p : Pairs =>
      (ftbq_measurableSet_smul j hIj _ hDY'meas).inter
        (ftbq_measurableSet_smul j hIj _ hDY'meas)
  have hBadYnull : volH j BadY = 0 := by
    refine measure_iUnion_null fun p : Pairs => ?_
    have hkG : resStd j m (p.1.1 : PO (j + m) 1)
        * (resStd j m (p.1.2 : PO (j + m) 1))⁻¹ ∈
        Subgroup.closure (resStd j m '' (C : Set (PO (j + m) 1))) :=
      Subgroup.mul_mem _ (Subgroup.subset_closure ⟨p.1.1, p.1.1.2, rfl⟩)
        (Subgroup.inv_mem _ (Subgroup.subset_closure ⟨p.1.2, p.1.2.2, rfl⟩))
    have hkne : (⟨resStd j m (p.1.1 : PO (j + m) 1)
        * (resStd j m (p.1.2 : PO (j + m) 1))⁻¹, hkG⟩ :
        Subgroup.closure (resStd j m '' (C : Set (PO (j + m) 1)))) ≠ 1 := by
      intro hc
      exact p.2 (by
        have h : resStd j m (p.1.1 : PO (j + m) 1)
            * (resStd j m (p.1.2 : PO (j + m) 1))⁻¹ = 1 := by
          have h2 := congrArg (fun t : Subgroup.closure (resStd j m '' (C : Set (PO (j + m) 1))) =>
            (t : PO j 1)) hc
          simpa using h2
        exact mul_inv_eq_one.mp h)
    have hmain := fund_domain_hull_null j hIj
      (Subgroup.closure (resStd j m '' (C : Set (PO (j + m) 1)))) DY hDY
      ⟨_, hkG⟩ hkne
    have hset : (resStd j m (p.1.1 : PO (j + m) 1)) •
        ((resStd j m (p.1.1 : PO (j + m) 1))⁻¹ • DY' ∩
          (resStd j m (p.1.2 : PO (j + m) 1))⁻¹ • DY')
        = DY' ∩ (resStd j m (p.1.1 : PO (j + m) 1)
            * (resStd j m (p.1.2 : PO (j + m) 1))⁻¹) • DY' := by
      rw [Set.smul_set_inter, smul_inv_smul, smul_smul]
    have hsm : volH j ((resStd j m (p.1.1 : PO (j + m) 1))⁻¹ • DY' ∩
        (resStd j m (p.1.2 : PO (j + m) 1))⁻¹ • DY')
        = volH j ((resStd j m (p.1.1 : PO (j + m) 1)) •
            ((resStd j m (p.1.1 : PO (j + m) 1))⁻¹ • DY' ∩
              (resStd j m (p.1.2 : PO (j + m) 1))⁻¹ • DY')) :=
      (MeasureTheory.measure_smul (μ := volH j) (resStd j m (p.1.1 : PO (j + m) 1)) _).symm
    rw [hsm, hset]
    simpa only [Set.image_smul] using hmain
  have hBadZero : volH (j + m) Bad = 0 := by
    have hsub : Bad ⊆ (fun p : E j × E m => fermi j m p.1 p.2) ''
        (BadY ×ˢ Metric.closedBall (0 : E m) ρ) := by
      intro z hz
      obtain ⟨c₁, c₂, hne, hz₁, hz₂⟩ := (hBadPo z).mp hz
      have hztube : z ∈ tube j m ρ := hBadTube hz
      have hzW : fermi j m (fermiInv j m z).1 (fermiInv j m z).2 = z := (fermi_inv j m).2.1 z
      have hWle : ‖(fermiInv j m z).2‖ ≤ ρ :=
        (ftbq_fermi_mem_tube j m ρ (fermiInv j m z).1 (fermiInv j m z).2).mp
          (by rw [hzW]; exact hztube)
      have key : ∀ (c : C), (c : C) • z ∈ F →
          (fermiInv j m z).1 ∈ (resStd j m (c : PO (j + m) 1))⁻¹ • DY' := by
        intro c hcz
        rw [Set.mem_inv_smul_set_iff]
        obtain ⟨q, hq, hqz⟩ := hcz
        have hqz' : fermi j m q.1 q.2 = (c : PO (j + m) 1) • z := hqz
        have h1 : fermi j m q.1 q.2
            = fermi j m (resStd j m (c : PO (j + m) 1) • (fermiInv j m z).1)
                (nrmStd j m (c : PO (j + m) 1) (fermiInv j m z).2) := by
          rw [hqz']
          rw [show (c : PO (j + m) 1) • z
              = fermi j m (resStd j m (c : PO (j + m) 1) • (fermiInv j m z).1)
                  (nrmStd j m (c : PO (j + m) 1) (fermiInv j m z).2) from by
            conv_lhs => rw [← hzW]
            rw [hblk (c : PO (j + m) 1) c.2 (fermiInv j m z).1 (fermiInv j m z).2]]
        have h2 := congrArg (fermiInv j m) h1
        rw [(fermi_inv j m).1, (fermi_inv j m).1] at h2
        have h2' : q.1 = resStd j m (c : PO (j + m) 1) • (fermiInv j m z).1 := by
          simpa using congrArg Prod.fst h2
        rw [← h2']
        exact hq.1
      have hy₁ := key c₁ hz₁
      have hy₂ := key c₂ hz₂
      have hyBad : (fermiInv j m z).1 ∈ BadY :=
        Set.mem_iUnion.mpr ⟨⟨(c₁, c₂), hne⟩, hy₁, hy₂⟩
      refine ⟨((fermiInv j m z).1, (fermiInv j m z).2), ⟨hyBad, ?_⟩,
        show (fun p : E j × E m => fermi j m p.1 p.2) ((fermiInv j m z).1, (fermiInv j m z).2) = z
          from hzW⟩
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
      exact hWle
    have hB : volH (j + m) ((fun p : E j × E m => fermi j m p.1 p.2) ''
        (BadY ×ˢ Metric.closedBall (0 : E m) ρ)) = 0 := by
      rw [volH_fermi_prod j m BadY (Metric.closedBall (0 : E m) ρ) hBadYmeas hball,
        hBadYnull, zero_mul]
    exact measure_mono_null hsub hB
  -- `Bad` is `C`-invariant
  have hresmul : ∀ x y : C, resStd j m ((x : PO (j + m) 1) * (y : PO (j + m) 1))
      = resStd j m (x : PO (j + m) 1) * resStd j m (y : PO (j + m) 1) :=
    fun x y => ftbResStdMul j m hAj hA Λ R hblk (x : PO (j + m) 1) (y : PO (j + m) 1) x.2 y.2
  have hBadInvPo : ∀ c : PO (j + m) 1, c ∈ C → c • Bad = Bad := by
    intro c hc
    let cC : C := ⟨c, hc⟩
    ext z
    rw [Set.mem_smul_set_iff_inv_smul_mem, hBadPo, hBadPo]
    constructor
    · rintro ⟨d₁, d₂, hne, h1, h2⟩
      refine ⟨d₁ * cC⁻¹, d₂ * cC⁻¹, ?_, ?_, ?_⟩
      · intro heq
        have heq' : resStd j m ((d₁ : PO (j + m) 1) * ((cC⁻¹ : C) : PO (j + m) 1))
            = resStd j m ((d₂ : PO (j + m) 1) * ((cC⁻¹ : C) : PO (j + m) 1)) := by
          simpa only [Subgroup.coe_mul] using heq
        rw [hresmul d₁ cC⁻¹, hresmul d₂ cC⁻¹] at heq'
        exact hne (mul_right_cancel heq')
      · show (d₁ * cC⁻¹) • z ∈ F
        rw [← smul_smul]
        exact h1
      · show (d₂ * cC⁻¹) • z ∈ F
        rw [← smul_smul]
        exact h2
    · rintro ⟨e₁, e₂, hne, h1, h2⟩
      refine ⟨e₁ * cC, e₂ * cC, ?_, ?_, ?_⟩
      · intro heq
        have heq' : resStd j m ((e₁ : PO (j + m) 1) * ((cC : C) : PO (j + m) 1))
            = resStd j m ((e₂ : PO (j + m) 1) * ((cC : C) : PO (j + m) 1)) := by
          simpa only [Subgroup.coe_mul] using heq
        rw [hresmul e₁ cC, hresmul e₂ cC] at heq'
        exact hne (mul_right_cancel heq')
      · show (e₁ * cC) • (cC⁻¹ • z) ∈ F
        rw [smul_smul, mul_assoc, mul_inv_cancel, mul_one]
        exact h1
      · show (e₂ * cC) • (cC⁻¹ • z) ∈ F
        rw [smul_smul, mul_assoc, mul_inv_cancel, mul_one]
        exact h2
  have hBadInv : ∀ c : C, c • Bad = Bad := fun c => hBadInvPo c c.2
  -- the bad points of the fundamental domain are null
  have hBadDcNull : volH (j + m) (Bad ∩ Dc) = 0 := by
    have htsum := hDc.measure_eq_tsum' Bad
    have hterm : ∀ c : C, volH (j + m) (Bad ∩ c • Dc) = volH (j + m) (Bad ∩ Dc) := by
      intro c
      have hinv : (c⁻¹ : C) • (Bad ∩ c • Dc) = Bad ∩ Dc := by
        rw [Set.smul_set_inter, show (c⁻¹ : C) • Bad = Bad from hBadInv c⁻¹,
          smul_smul, inv_mul_cancel, one_smul]
      have hsm : volH (j + m) (Bad ∩ c • Dc)
          = volH (j + m) ((c⁻¹ : C) • (Bad ∩ c • Dc)) :=
        (MeasureTheory.measure_smul (μ := volH (j + m)) (c⁻¹ : C) _).symm
      rw [hsm, hinv]
    have h2 : (∑' c : C, volH (j + m) (Bad ∩ Dc)) = 0 := by
      rw [show (∑' c : C, volH (j + m) (Bad ∩ Dc))
          = ∑' c : C, volH (j + m) (Bad ∩ c • Dc) from tsum_congr fun c => (hterm c).symm,
        ← htsum]
      exact hBadZero
    exact (ENNReal.tsum_eq_zero.mp h2) 1
  -- the counting hypothesis
  have hae : ∀ᵐ z ∂((volH (j + m)).restrict Dc), z ∉ Bad := by
    rw [ae_iff]
    have hset : {z : E (j + m) | ¬ z ∉ Bad} = Bad := by ext z; simp
    rw [hset, Measure.restrict_apply hBadmeas]
    exact hBadDcNull
  let Kc : Finset C := Finset.univ.image
    (fun k : {c : PO (j + m) 1 // c ∈ Λ ∧ c ∈ Subgroup.centralizer {blk j m 1 R} ∧
        resStd j m c = 1} => (⟨(k : PO (j + m) 1), k.2.2.1, k.2.1⟩ : C))
  have hresStd_one : resStd j m (1 : PO (j + m) 1) = 1 := by
    refine ftbq_po_eq_of_smul_eq j hAj fun v => ?_
    show resStd j m (1 : PO (j + m) 1) • v = (1 : PO j 1) • v
    rw [poOneSMul]
    have h := hblk 1 C.one_mem v 0
    rw [poOneSMul] at h
    have h2 := congrArg (fermiInv j m) h
    rw [(fermi_inv j m).1, (fermi_inv j m).1] at h2
    have h5 : v = resStd j m (1 : PO (j + m) 1) • v := by
      simpa using congrArg Prod.fst h2
    exact h5.symm
  have hcount : ∀ᵐ z ∂((volH (j + m)).restrict Dc),
      ∃ s : Finset C, s.card ≤ Nat.card {c : PO (j + m) 1 // c ∈ Λ ∧
          c ∈ Subgroup.centralizer {blk j m 1 R} ∧ resStd j m c = 1} ∧
        ∀ c : C, c • z ∈ F → c ∈ s := by
    filter_upwards [hae] with z hz
    by_cases hne : ∃ c : C, c • z ∈ F
    · obtain ⟨c₀, hc₀⟩ := hne
      refine ⟨Kc.image (fun k : C => c₀ * k), ?_, ?_⟩
      · calc (Kc.image (fun k : C => c₀ * k)).card ≤ Kc.card := Finset.card_image_le
          _ ≤ (Finset.univ : Finset {c : PO (j + m) 1 // c ∈ Λ ∧
                c ∈ Subgroup.centralizer {blk j m 1 R} ∧ resStd j m c = 1}).card :=
              Finset.card_image_le
          _ = Nat.card {c : PO (j + m) 1 // c ∈ Λ ∧ c ∈ Subgroup.centralizer {blk j m 1 R} ∧
                resStd j m c = 1} := by
              rw [Finset.card_univ, Nat.card_eq_fintype_card]
      · intro c hc
        have hres : resStd j m (c : PO (j + m) 1) = resStd j m (c₀ : PO (j + m) 1) := by
          by_contra hne'
          exact hz ((hBadPo z).mpr ⟨c, c₀, hne', hc, hc₀⟩)
        have hinv0 : resStd j m ((c₀ : PO (j + m) 1)⁻¹)
            = (resStd j m (c₀ : PO (j + m) 1))⁻¹ := by
          have h1 : resStd j m ((c₀ : PO (j + m) 1) * (c₀ : PO (j + m) 1)⁻¹) = 1 := by
            rw [mul_inv_cancel, hresStd_one]
          rw [ftbResStdMul j m hAj hA Λ R hblk ((c₀ : PO (j + m) 1))
            ((c₀ : PO (j + m) 1)⁻¹) c₀.2 (C.inv_mem c₀.2)] at h1
          exact eq_inv_of_mul_eq_one_right h1
        have hkres : resStd j m (((c₀⁻¹ * c : C)) : PO (j + m) 1) = 1 := by
          have hcoe : (((c₀⁻¹ * c : C)) : PO (j + m) 1)
              = (c₀ : PO (j + m) 1)⁻¹ * (c : PO (j + m) 1) := rfl
          rw [hcoe, ftbResStdMul j m hAj hA Λ R hblk ((c₀ : PO (j + m) 1)⁻¹)
            ((c : PO (j + m) 1)) (C.inv_mem c₀.2) c.2, hinv0, hres, inv_mul_cancel]
        have hkcent : (((c₀⁻¹ * c : C)) : PO (j + m) 1)
            ∈ Subgroup.centralizer ({blk j m 1 R} : Set (PO (j + m) 1)) := (c₀⁻¹ * c).2.1
        have hkΛ : (((c₀⁻¹ * c : C)) : PO (j + m) 1) ∈ Λ := (c₀⁻¹ * c).2.2
        have hmemKc : (⟨(((c₀⁻¹ * c : C)) : PO (j + m) 1), hkcent, hkΛ⟩ : C) ∈ Kc := by
          refine Finset.mem_image.mpr ⟨⟨_, hkΛ, hkcent, hkres⟩, Finset.mem_univ _, ?_⟩
          exact Subtype.ext rfl
        have hceq : c = c₀ * (⟨(((c₀⁻¹ * c : C)) : PO (j + m) 1), hkcent, hkΛ⟩ : C) := by
          refine Subtype.ext ?_
          show (c : PO (j + m) 1) = (c₀ : PO (j + m) 1) *
            (((c₀⁻¹ * c : C)) : PO (j + m) 1)
          rw [show (((c₀⁻¹ * c : C)) : PO (j + m) 1)
              = (c₀ : PO (j + m) 1)⁻¹ * (c : PO (j + m) 1) from rfl]
          group
        rw [hceq]
        exact Finset.mem_image.mpr ⟨_, hmemKc, rfl⟩
    · exact ⟨∅, by simp, fun c hc => absurd ⟨c, hc⟩ hne⟩
  -- assemble
  have hmain := ftbCountInter (volH (j + m)) hDc hFmeas hTubeMeas hTinv hFsub
    (Nat.card {c : PO (j + m) 1 // c ∈ Λ ∧ c ∈ Subgroup.centralizer {blk j m 1 R} ∧
      resStd j m c = 1}) hcount
  calc volH j DY * tubeMeasure j m (Metric.closedBall 0 ρ)
      = volH (j + m) F := hFvol.symm
    _ ≤ (Nat.card {c : PO (j + m) 1 // c ∈ Λ ∧ c ∈ Subgroup.centralizer {blk j m 1 R} ∧
          resStd j m c = 1} : ENNReal) * volH (j + m) (Dc ∩ tube j m ρ) := hmain
    _ = (Nat.card {c : PO (j + m) 1 // c ∈ Λ ∧ c ∈ Subgroup.centralizer {blk j m 1 R} ∧
          resStd j m c = 1} : ENNReal) * volH (j + m) (tube j m ρ ∩ Dc) := by
        rw [Set.inter_comm]

end

end Work.Mostow
