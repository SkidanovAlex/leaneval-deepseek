import Mathlib
import Submission.Work.EKLContract.All
import Submission.Work.EKLRelCross.Instances
import Submission.Work.EKLRelCross.horoZone
import Submission.Work.EKLRelCross.invariant_notes

namespace Work.EKLRelCross

open MeasureTheory Filter
open scoped Topology Pointwise

set_option linter.style.haveILetI false
set_option autoImplicit false

private theorem haar_right_haar {G : Type*} [Group G] [TopologicalSpace G] [T2Space G]
    [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G]
    [SecondCountableTopology G]
    (u : G) (φ : ℕ → G ≃ₜ* G) (hφ : Tendsto (fun n => φ n u) atTop (𝓝 1)) :
    (Measure.haar : Measure G).map (fun x => x * u) = Measure.haar := by
  set h0 : Measure G := Measure.haar with hh0
  haveI : Measure.IsHaarMeasure h0 := inferInstance
  haveI : h0.Regular := inferInstance
  obtain ⟨f, hf_comp, hf_nonneg, hf_one⟩ := exists_continuous_nonneg_pos (1 : G)
  have hf_cont : Continuous ⇑f := f.continuous
  have hf_int_pos : 0 < ∫ x, f x ∂h0 :=
    hf_cont.integral_pos_of_hasCompactSupport_nonneg_nonzero hf_comp hf_nonneg hf_one
  have hf_int_ne : ∫ x, f x ∂h0 ≠ 0 := ne_of_gt hf_int_pos
  obtain ⟨Cf, hCf⟩ : ∃ C, ∀ x, ‖f x‖ ≤ C := by
    have hc : IsCompact (⇑f '' tsupport (⇑f)) := hf_comp.isCompact.image hf_cont
    obtain ⟨C, hC⟩ := hc.isBounded.exists_norm_le
    refine ⟨max C 0, fun x => ?_⟩
    by_cases hx : x ∈ tsupport (⇑f)
    · exact le_trans (hC (f x) (Set.mem_image_of_mem _ hx)) (le_max_left _ _)
    · rw [image_eq_zero_of_notMem_tsupport hx, norm_zero]; exact le_max_right _ _
  set g : G → ℝ := fun v => (∫ x, f (x * v) ∂h0) / (∫ x, f x ∂h0) with hg_def
  have hg_nonneg : ∀ v, 0 ≤ g v := fun v =>
    div_nonneg (integral_nonneg (fun x => hf_nonneg (x * v))) (le_of_lt hf_int_pos)
  have hg_eq_hsf : ∀ v : G, (g v).toNNReal = (h0.map (fun x => x * v)).haarScalarFactor h0 := by
    intro v
    haveI h1 : IsFiniteMeasureOnCompacts (h0.map (fun x => x * v)) :=
      Measure.IsFiniteMeasureOnCompacts.map h0 (Homeomorph.mulRight v)
    haveI h2 : (h0.map (fun x => x * v)).IsMulLeftInvariant :=
      isMulLeftInvariant_map_mul_right (μ := h0) v
    have key : ((h0.map (fun x => x * v)).haarScalarFactor h0 : ℝ) = g v := by
      rw [Measure.haarScalarFactor_eq_integral_div (h0.map (fun x => x * v)) h0 hf_cont hf_comp hf_int_ne,
        hg_def]
      rw [show ∫ x, f x ∂(h0.map (fun x => x * v)) = ∫ x, f (x * v) ∂h0 from by
        simpa using MeasureTheory.integral_map_equiv ((Homeomorph.mulRight v).toMeasurableEquiv) (⇑f)]
    rw [← key, Real.toNNReal_coe]
  have hmap_eq : ∀ v : G, h0.map (fun x => x * v) = (g v).toNNReal • h0 := by
    intro v
    haveI h1 : IsFiniteMeasureOnCompacts (h0.map (fun x => x * v)) :=
      Measure.IsFiniteMeasureOnCompacts.map h0 (Homeomorph.mulRight v)
    haveI h2 : (h0.map (fun x => x * v)).IsMulLeftInvariant :=
      isMulLeftInvariant_map_mul_right (μ := h0) v
    rw [hg_eq_hsf v]
    exact Measure.isMulLeftInvariant_eq_smul (h0.map (fun x => x * v)) h0
  have hauto : ∀ ψ : G ≃ₜ* G, h0.map (fun x => x * (ψ u)) = h0.map (fun x => x * u) := by
    intro ψ
    haveI hmψ : Measurable ⇑ψ := ψ.continuous.measurable
    haveI hmψi : Measurable ⇑(ψ.symm) := ψ.symm.continuous.measurable
    have hpos : mulEquivHaarChar ψ ≠ 0 := (mulEquivHaarChar_pos ψ).ne'
    have hc_map : h0.map (⇑ψ) = (mulEquivHaarChar ψ)⁻¹ • h0 := by
      have key := mulEquivHaarChar_smul_map h0 ψ
      have := congrArg (fun (ν : Measure G) => (mulEquivHaarChar ψ)⁻¹ • ν) key
      rw [smul_smul, inv_mul_cancel₀ hpos, one_smul] at this
      exact this
    have hc_map' : h0.map (⇑ψ.symm) = mulEquivHaarChar ψ • h0 := by
      have key := mulEquivHaarChar_smul_map h0 ψ.symm
      have h3 := congrArg (fun (ν : Measure G) => (mulEquivHaarChar ψ.symm)⁻¹ • ν) key
      rw [smul_smul, inv_mul_cancel₀ (mulEquivHaarChar_pos ψ.symm).ne', one_smul] at h3
      rw [h3, mulEquivHaarChar_symm, inv_inv]
    calc h0.map (fun x => x * (ψ u))
        = ((h0.map (⇑ψ.symm)).map (fun x => x * u)).map (⇑ψ) := by
            rw [Measure.map_map hmψ (measurable_mul_const u),
                Measure.map_map (hmψ.comp (measurable_mul_const u)) hmψi]
            congr 1
            funext x
            simp [Function.comp_apply]
      _ = mulEquivHaarChar ψ • ((h0.map (fun x => x * u)).map (⇑ψ)) := by
            rw [hc_map', Measure.map_smul, Measure.map_smul] <;> try fun_prop
      _ = mulEquivHaarChar ψ • (((g u).toNNReal • h0).map (⇑ψ)) := by rw [hmap_eq u]
      _ = mulEquivHaarChar ψ • ((g u).toNNReal • (h0.map (⇑ψ))) := by rw [Measure.map_smul] <;> try fun_prop
      _ = mulEquivHaarChar ψ • ((g u).toNNReal • ((mulEquivHaarChar ψ)⁻¹ • h0)) := by rw [hc_map]
      _ = (mulEquivHaarChar ψ * (g u).toNNReal * (mulEquivHaarChar ψ)⁻¹) • h0 := by
            rw [smul_smul, smul_smul]
      _ = (g u).toNNReal • h0 := by
            congr 1
            rw [mul_comm (mulEquivHaarChar ψ) _, mul_assoc, mul_inv_cancel₀ hpos, mul_one]
      _ = h0.map (fun x => x * u) := (hmap_eq u).symm
  have hF : Tendsto (fun n => ∫ x, f (x * (φ n u)) ∂h0) atTop (𝓝 (∫ x, f x ∂h0)) := by
    obtain ⟨N, hNc, hNnhds⟩ := exists_compact_mem_nhds (1 : G)
    have hNinv_nhds : N⁻¹ ∈ 𝓝 (1:G) :=
      (continuous_inv.continuousAt (x := (1:G))).preimage_mem_nhds (by simpa using hNnhds)
    set Ns : Set G := N ∩ N⁻¹ with hNsdef
    have hNs_c : IsCompact Ns := hNc.inter hNc.inv
    have hNs_nhds : Ns ∈ 𝓝 (1:G) := Filter.inter_mem hNnhds hNinv_nhds
    have hNs_inv : ∀ w ∈ Ns, w⁻¹ ∈ Ns := by
      intro w hw
      rw [hNsdef] at hw ⊢
      simp only [Set.mem_inter_iff, Set.mem_inv] at hw ⊢
      exact ⟨hw.2, by simpa using hw.1⟩
    have hLc : IsCompact (tsupport (⇑f)) := hf_comp.isCompact
    have hLNc : IsCompact (tsupport (⇑f) * Ns) := hLc.mul hNs_c
    have hLNmeas : MeasurableSet (tsupport (⇑f) * Ns) := hLNc.isClosed.measurableSet
    have hbound_int :
        Integrable (fun x => Cf * (tsupport (⇑f) * Ns).indicator (fun _ => (1:ℝ)) x) h0 := by
      have h1 : Integrable ((tsupport (⇑f) * Ns).indicator (fun _ => (1:ℝ))) h0 := by
        rw [integrable_indicator_iff hLNmeas]
        exact integrableOn_const hLNc.measure_lt_top.ne (by simp)
      exact h1.const_mul Cf
    refine tendsto_integral_filter_of_dominated_convergence
      (F := fun n x => f (x * (φ n u))) (f := ⇑f)
      (fun x => Cf * (tsupport (⇑f) * Ns).indicator (fun _ => (1:ℝ)) x) ?_ ?_ hbound_int ?_
    · filter_upwards [] with n
      exact (hf_cont.comp (continuous_id.mul continuous_const)).aestronglyMeasurable
    · filter_upwards [hφ hNs_nhds] with n hn
      filter_upwards [] with x
      by_cases hx : x ∈ tsupport (⇑f) * Ns
      · rw [Set.indicator_of_mem hx, mul_one]
        exact hCf (x * (φ n u))
      · rw [Set.indicator_of_notMem hx, mul_zero]
        have hzero : f (x * (φ n u)) = 0 := by
          apply image_eq_zero_of_notMem_tsupport
          intro hmem
          apply hx
          have hw : (φ n u)⁻¹ ∈ Ns := hNs_inv _ hn
          have := Set.mul_mem_mul hmem hw
          simpa [mul_assoc] using this
        rw [hzero, norm_zero]
    · filter_upwards [] with x
      have ht : Tendsto (fun n => x * (φ n u)) atTop (𝓝 (x * (1:G))) := tendsto_const_nhds.mul hφ
      have := hf_cont.continuousAt.tendsto.comp ht
      simpa [Function.comp_def] using this
  have hconst : ∀ n, ∫ x, f (x * (φ n u)) ∂h0 = ∫ x, f (x * u) ∂h0 := by
    intro n
    calc ∫ x, f (x * (φ n u)) ∂h0
        = ∫ y, f y ∂(h0.map (fun x => x * (φ n u))) := by
            simpa using (MeasureTheory.integral_map_equiv ((Homeomorph.mulRight (φ n u)).toMeasurableEquiv) (⇑f)).symm
      _ = ∫ y, f y ∂(h0.map (fun x => x * u)) := by rw [hauto (φ n)]
      _ = ∫ x, f (x * u) ∂h0 := by
            simpa using MeasureTheory.integral_map_equiv ((Homeomorph.mulRight u).toMeasurableEquiv) (⇑f)
  have hFu : Tendsto (fun n => ∫ x, f (x * (φ n u)) ∂h0) atTop (𝓝 (∫ x, f (x * u) ∂h0)) :=
    Filter.Tendsto.congr' (Eventually.of_forall fun n => (hconst n).symm) tendsto_const_nhds
  have hInt_eq : ∫ x, f (x * u) ∂h0 = ∫ x, f x ∂h0 := tendsto_nhds_unique hFu hF
  have hu : g u = 1 := by
    change (∫ x, f (x * u) ∂h0) / (∫ x, f x ∂h0) = 1
    rw [hInt_eq, div_self hf_int_ne]
  rw [hh0] at hmap_eq ⊢
  rw [hmap_eq u, hu, Real.toNNReal_one, one_smul]

theorem haar_map_mul_right_eq_self_of_tendsto_aut {G : Type*} [Group G] [TopologicalSpace G] [T2Space G]
    [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G]
    [SecondCountableTopology G] (h : Measure G) [Measure.IsHaarMeasure h]
    (u : G) (φ : ℕ → G ≃ₜ* G) (hφ : Tendsto (fun n => φ n u) atTop (𝓝 1)) :
    h.map (fun x => x * u) = h := by
  have h0 := haar_right_haar (G := G) u φ hφ
  have hc : h = h.haarScalarFactor Measure.haar • Measure.haar :=
    Measure.isMulLeftInvariant_eq_smul h Measure.haar
  rw [hc, Measure.map_smul, h0] <;> try fun_prop


private lemma gconj_left {G : Type*} [Group G] (a x : G) : a⁻¹ * (a * x * a⁻¹) * a = x := by
  group

private lemma gconj_right {G : Type*} [Group G] (a x : G) : a * (a⁻¹ * x * a) * a⁻¹ = x := by
  group

private lemma gconj_mul {G : Type*} [Group G] (a x y : G) :
    a * (x * y) * a⁻¹ = (a * x * a⁻¹) * (a * y * a⁻¹) := by
  group

private def conjCE (U : Subgroup Work.EKLContract.SL3) (a : Work.EKLContract.SL3)
    (ha : ∀ u ∈ U, a * u * a⁻¹ ∈ U) (ha' : ∀ u ∈ U, a⁻¹ * u * a ∈ U) : ↥U ≃ₜ* ↥U :=
  ContinuousMulEquiv.mk
    { toFun := fun x => ⟨a * (x : Work.EKLContract.SL3) * a⁻¹, ha x.1 x.2⟩
      invFun := fun x => ⟨a⁻¹ * (x : Work.EKLContract.SL3) * a, ha' x.1 x.2⟩
      left_inv := fun x => Subtype.ext (by
        simpa only [Subtype.coe_mk] using gconj_left a (x : Work.EKLContract.SL3))
      right_inv := fun x => Subtype.ext (by
        simpa only [Subtype.coe_mk] using gconj_right a (x : Work.EKLContract.SL3))
      map_mul' := fun x y => Subtype.ext (by
        simp only [Subgroup.coe_mul]
        exact gconj_mul a (x : Work.EKLContract.SL3) (y : Work.EKLContract.SL3)) }
    (Continuous.subtype_mk (f := fun x : ↥U => a * (x : Work.EKLContract.SL3) * a⁻¹)
      ((continuous_const.mul continuous_subtype_val).mul continuous_const) (fun x => ha x.1 x.2))
    (Continuous.subtype_mk (f := fun x : ↥U => a⁻¹ * (x : Work.EKLContract.SL3) * a)
      ((continuous_const.mul continuous_subtype_val).mul continuous_const) (fun x => ha' x.1 x.2))

set_option maxHeartbeats 1000000 in
theorem horoUnimodular {U : Subgroup Work.EKLContract.SL3}
    (hU : Work.EKLContract.IsHoro U)
    (ν : MeasureTheory.Measure Work.EKLContract.SL3)
    (hradon : MeasureTheory.IsFiniteMeasureOnCompacts ν)
    (hcar : ν (U : Set Work.EKLContract.SL3)ᶜ = 0) (hne : ν ≠ 0)
    (hri : ∀ u ∈ U, ν.map (fun g => g * u) = ν) :
    (∀ u ∈ U, ν.map (fun g => u * g) = ν) ∧
      (∀ u ∈ U, ν.map (fun g => u * g * u⁻¹) = ν) := by
  have hUc : IsClosed (U : Set Work.EKLContract.SL3) := hU.1
  have hAnorm : ∀ t : Fin 3 → ℝ, ∀ u ∈ U, Work.EKLContract.aDiag t * u * (Work.EKLContract.aDiag t)⁻¹ ∈ U :=
    hU.2.1
  obtain ⟨t0, hcontr⟩ := hU.2.2
  haveI : LocallyCompactSpace ↥U := hUc.locallyCompactSpace
  haveI : SecondCountableTopology ↥U :=
    TopologicalSpace.Subtype.secondCountableTopology (U : Set Work.EKLContract.SL3)
  have hUmeas : MeasurableSet (U : Set Work.EKLContract.SL3) := hUc.measurableSet
  have hmval : Measurable (Subtype.val : ↥U → Work.EKLContract.SL3) := continuous_subtype_val.measurable
  set νU : MeasureTheory.Measure ↥U :=
    MeasureTheory.Measure.comap (Subtype.val : ↥U → Work.EKLContract.SL3) ν with hνU
  have hνU_map : νU.map (Subtype.val : ↥U → Work.EKLContract.SL3) = ν := by
    have h := (MeasurableEmbedding.subtype_coe hUmeas).map_comap ν
    rw [Subtype.range_coe] at h
    have h2 : ν.restrict (U : Set Work.EKLContract.SL3) = ν := by
      apply Measure.restrict_eq_self_of_ae_mem
      rw [ae_iff]
      convert hcar using 2
      all_goals (ext x; simp)
    rw [hνU]
    exact h.trans h2
  haveI hfinU : IsFiniteMeasureOnCompacts νU := by
    rw [hνU]
    exact IsFiniteMeasureOnCompacts.comap' ν continuous_subtype_val (MeasurableEmbedding.subtype_coe hUmeas)
  have hνU_ne : νU ≠ 0 := by
    intro h0
    apply hne
    rw [← hνU_map, h0, Measure.map_zero]
  have hνU_ri : ∀ u : ↥U, νU.map (fun x => x * u) = νU := by
    intro u
    refine (MeasurableEmbedding.map_injective (MeasurableEmbedding.subtype_coe hUmeas)) ?_
    have hstep : Measure.map (Subtype.val) (Measure.map (fun x : ↥U => x * u) νU)
        = Measure.map (fun g : Work.EKLContract.SL3 => g * u.1)
            (Measure.map (Subtype.val) νU) := by
      rw [Measure.map_map hmval (measurable_mul_const u)]
      rw [show (Subtype.val ∘ fun x : ↥U => x * u)
            = (fun g : Work.EKLContract.SL3 => g * u.1) ∘
              (Subtype.val : ↥U → Work.EKLContract.SL3) from rfl]
      rw [← Measure.map_map (measurable_mul_const u.1) hmval]
    exact hstep.trans ((congrArg (Measure.map (fun g : Work.EKLContract.SL3 => g * u.1))
      hνU_map).trans ((hri u.1 u.2).trans hνU_map.symm))
  have hmem : ∀ n, ∀ u ∈ U,
      Work.EKLContract.aDiag t0 ^ n * u * (Work.EKLContract.aDiag t0 ^ n)⁻¹ ∈ U := by
    intro n u hu
    rw [Work.EKLContract.Lemmas.horoUij_aDiag_pow]
    exact hAnorm (fun k => (n : ℝ) * t0 k) u hu
  have hmem' : ∀ n, ∀ u ∈ U,
      (Work.EKLContract.aDiag t0 ^ n)⁻¹ * u * Work.EKLContract.aDiag t0 ^ n ∈ U := by
    intro n u hu
    have h1 : (Work.EKLContract.aDiag t0 ^ n)⁻¹
        = Work.EKLContract.aDiag (fun k => -((n : ℝ) * t0 k)) := by
      rw [Work.EKLContract.Lemmas.horoUij_aDiag_pow]
      exact inv_eq_of_mul_eq_one_left (Work.EKLContract.aDiag_neg_mul (fun k => (n : ℝ) * t0 k))
    have h3 : (Work.EKLContract.aDiag (-(fun k => (n : ℝ) * t0 k)))⁻¹
        = Work.EKLContract.aDiag (fun k => (n : ℝ) * t0 k) :=
      inv_eq_of_mul_eq_one_left (Work.EKLContract.aDiag_mul_neg (fun k => (n : ℝ) * t0 k))
    rw [h1, Work.EKLContract.Lemmas.horoUij_aDiag_pow, ← h3]
    exact hAnorm (-(fun k => (n : ℝ) * t0 k)) u hu
  let φ : ℕ → ↥U ≃ₜ* ↥U :=
    fun n => conjCE U (Work.EKLContract.aDiag t0 ^ n) (hmem n) (hmem' n)
  have hcoeφ : ∀ (n : ℕ) (v : ↥U),
      ((φ n v : ↥U) : Work.EKLContract.SL3)
        = Work.EKLContract.aDiag t0 ^ n * (v : Work.EKLContract.SL3) * (Work.EKLContract.aDiag t0 ^ n)⁻¹ := by
    intro n v
    change ((conjCE U (Work.EKLContract.aDiag t0 ^ n) (hmem n) (hmem' n)) v : Work.EKLContract.SL3)
        = Work.EKLContract.aDiag t0 ^ n * (v : Work.EKLContract.SL3) * (Work.EKLContract.aDiag t0 ^ n)⁻¹
    rfl
  have hφtend : ∀ v : ↥U, Tendsto (fun n => φ n v) atTop (𝓝 1) := by
    intro v
    rw [tendsto_subtype_rng]
    have hfun : (fun n => ((φ n v : ↥U) : Work.EKLContract.SL3))
        = fun n => Work.EKLContract.aDiag t0 ^ n * (v : Work.EKLContract.SL3) * (Work.EKLContract.aDiag t0 ^ n)⁻¹ :=
      funext (fun n => hcoeφ n v)
    rw [hfun]
    simpa using hcontr v.1 v.2
  have haar_r : ∀ v : ↥U, Measure.haar.map (fun x => x * v) = Measure.haar :=
    fun v => haar_map_mul_right_eq_self_of_tendsto_aut Measure.haar v φ (hφtend v)
  have haar_inv_l : ∀ w : ↥U,
      ((Measure.haar : Measure ↥U).inv).map (fun x => w * x) = (Measure.haar : Measure ↥U).inv := by
    intro w
    rw [Measure.inv_def, Measure.map_map (measurable_const_mul w) measurable_inv]
    rw [show (fun x : ↥U => w * x) ∘ Inv.inv = Inv.inv ∘ (fun x : ↥U => x * w⁻¹) from by
          funext x
          simp only [Function.comp_apply, mul_inv_rev, inv_inv]]
    rw [← Measure.map_map measurable_inv (measurable_mul_const w⁻¹), haar_r w⁻¹, ← Measure.inv_def]
  haveI hriI : νU.IsMulRightInvariant := ⟨hνU_ri⟩
  haveI hfinI : IsFiniteMeasureOnCompacts νU.inv :=
    Measure.IsFiniteMeasureOnCompacts.map νU (Homeomorph.inv ↥U)
  have hc : νU.inv = νU.inv.haarScalarFactor Measure.haar • Measure.haar :=
    Measure.isMulLeftInvariant_eq_smul νU.inv Measure.haar
  have hνU_eq : νU = νU.inv.haarScalarFactor Measure.haar • (Measure.haar : Measure ↥U).inv := by
    have h := congrArg (fun (m : Measure ↥U) => m.inv) hc
    rw [Measure.inv_inv, Measure.inv_def, Measure.map_smul, ← Measure.inv_def] at h <;> try fun_prop
    exact h
  have hleft : ∀ u : ↥U, νU.map (fun x => u * x) = νU := by
    intro u
    calc νU.map (fun x => u * x)
        = (νU.inv.haarScalarFactor Measure.haar • (Measure.haar : Measure ↥U).inv).map
            (fun x => u * x) := congrArg (Measure.map (fun x => u * x)) hνU_eq
      _ = νU.inv.haarScalarFactor Measure.haar •
            (((Measure.haar : Measure ↥U).inv).map (fun x => u * x)) := by rw [Measure.map_smul] <;> try fun_prop
      _ = νU.inv.haarScalarFactor Measure.haar • (Measure.haar : Measure ↥U).inv := by rw [haar_inv_l u]
      _ = νU := hνU_eq.symm
  have key : ∀ u' : ↥U, ν.map (fun g => (u' : Work.EKLContract.SL3) * g)
      = (νU.map (fun x => u' * x)).map (Subtype.val : ↥U → Work.EKLContract.SL3) := by
    intro u'
    have hfun : ((fun g : Work.EKLContract.SL3 => (u' : Work.EKLContract.SL3) * g) ∘
          (Subtype.val : ↥U → Work.EKLContract.SL3))
        = (Subtype.val : ↥U → Work.EKLContract.SL3) ∘ (fun x : ↥U => u' * x) := by
      funext x
      simp only [Function.comp_apply, Subgroup.coe_mul]
    rw [← hνU_map, Measure.map_map (measurable_const_mul (u' : Work.EKLContract.SL3)) hmval, hfun,
        ← Measure.map_map hmval (measurable_const_mul u')]
  have hfirst : ∀ u ∈ U, ν.map (fun g => u * g) = ν := by
    intro u hu
    have hk := key ⟨u, hu⟩
    rw [hleft ⟨u, hu⟩, hνU_map] at hk
    simpa using hk
  refine ⟨hfirst, ?_⟩
  intro u hu
  calc ν.map (fun g => u * g * u⁻¹)
      = (ν.map (fun g => g * u⁻¹)).map (fun g => u * g) := by
          rw [Measure.map_map (measurable_const_mul u) (measurable_mul_const u⁻¹)]
          congr 1
          funext g
          simp only [Function.comp_apply, mul_assoc]
    _ = ν.map (fun g => u * g) := by rw [hri u⁻¹ (U.inv_mem hu)]
    _ = ν := hfirst u hu


end Work.EKLRelCross
