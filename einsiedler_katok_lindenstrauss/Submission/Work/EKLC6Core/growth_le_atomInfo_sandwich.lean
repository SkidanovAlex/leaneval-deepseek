import Mathlib
import Submission.Work.EKLC6Core.growth_le_HcondSig
import Submission.Work.EKLC6Core.growth_le_atomInfo
import Submission.Work.EKLC6Core.radius_independence
import Submission.Work.EKLContract.All

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

/-- The flow map `y ↦ aDiag t • y`. -/
def aShift (t : Fin 3 → ℝ) : X3 → X3 := fun y => aDiag t • y

@[simp] theorem aShift_apply (t : Fin 3 → ℝ) (y : X3) : aShift t y = aDiag t • y := rfl

theorem aShift_pow_apply (t : Fin 3 → ℝ) (n : ℕ) (x : X3) :
    (aShift t)^[n] x = aDiag t ^ n • x :=
  congrFun (smul_iterate (aDiag t) n) x

/-- **Telescoping of Pisa 7.34 along the orbit.** -/
theorem orbit_telescope_gl {μ : Measure X3} [IsProbabilityMeasure μ] {U : Subgroup SL3}
    {ν : X3 → Measure SL3} {X' X'' : Set X3} (t : Fin 3 → ℝ)
    (hL : IsLeafwise μ U ν X') (hU : IsHoro U) (hcov : ACovariant ν X'')
    (hX'' : μ X''ᶜ = 0) (hAinv : IsAInvariant μ)
    {A : MeasurableSpace X3} {Z : Set X3} (hplaq : IsPlaqueAlgebra U Z A) (hZ : μ Zᶜ = 0) :
    ∀ᵐ x ∂μ, ∀ n : ℕ,
      (∑ j ∈ Finset.range n, atomInfo A U ν t ((aShift t)^[j] x))
        = Real.log ((ν ((aShift t)^[n] x) (shape A U ((aShift t)^[n] x))).toReal)
          - Real.log ((ν x (shape A U x)).toReal)
          + ∑ j ∈ Finset.range n, growthFun U ν t ((aShift t)^[j+1] x) := by
  letI : MeasurableSpace X3 := instMeasurableSpaceX3
  have hmp : MeasurePreserving (aShift t) μ μ := hAinv t
  have hbase := atomInfo_ae_eq_aux (t := t) hL hU hcov hX'' hAinv hplaq hZ
  have hAt : ∀ᵐ x ∂μ, ∀ k : ℕ,
      atomInfo A U ν t ((aShift t)^[k] x)
        = Real.log ((ν ((aShift t)^[k+1] x) (shape A U ((aShift t)^[k+1] x))).toReal)
          - Real.log ((ν ((aShift t)^[k] x) (shape A U ((aShift t)^[k] x))).toReal)
          + growthFun U ν t ((aShift t)^[k+1] x) := by
    rw [MeasureTheory.ae_all_iff]
    intro k
    have hk := (hmp.iterate k).quasiMeasurePreserving.ae hbase
    filter_upwards [hk] with x hx
    simp only [Function.iterate_succ_apply', aShift_apply]
    exact hx
  filter_upwards [hAt] with x hx
  intro n
  rw [Finset.sum_congr rfl (fun j _ => hx j), Finset.sum_add_distrib]
  have htel := Finset.sum_range_sub (fun i : ℕ => Real.log ((ν ((aShift t)^[i] x)
      (shape A U ((aShift t)^[i] x))).toReal)) n
  rw [htel]
  simp only [Function.iterate_zero_apply]

/-- For a leaf-wise system carried by `U`, `V r` may be replaced by `V r ∩ U`, and this
common mass is positive and finite at every point of the domain. -/
theorem V_mass_facts_gl {μ : Measure X3} [IsProbabilityMeasure μ] {U : Subgroup SL3}
    {ν : X3 → Measure SL3} {X' : Set X3} (hL : IsLeafwise μ U ν X')
    {y : X3} (hy : y ∈ X') {r : ℝ} (hr : 0 < r) :
    ν y (V r ∩ (U : Set SL3)) = ν y (V r) ∧
      0 < ν y (V r ∩ (U : Set SL3)) ∧ ν y (V r ∩ (U : Set SL3)) < ⊤ := by
  letI : MeasurableSpace X3 := instMeasurableSpaceX3
  have hcar : ν y (V r ∩ (U : Set SL3)) = ν y (V r) := by
    refine le_antisymm (measure_mono Set.inter_subset_left) ?_
    calc ν y (V r) = ν y ((V r ∩ (U : Set SL3)) ∪ (V r ∩ (U : Set SL3)ᶜ)) := by
          rw [Set.inter_union_compl]
      _ ≤ ν y (V r ∩ (U : Set SL3)) + ν y (V r ∩ (U : Set SL3)ᶜ) := measure_union_le _ _
      _ = ν y (V r ∩ (U : Set SL3)) := by
          rw [measure_mono_null Set.inter_subset_right (hL.carried y hy), add_zero]
  refine ⟨hcar, ?_, ?_⟩
  · rw [hcar]; exact hL.pos y hy r hr
  · have hsub : V r ∩ (U : Set SL3) ⊆ {g : SL3 | ∀ i j, -(1 + r) ≤ g i j ∧ g i j ≤ 1 + r} := by
      intro g hg i j
      exact abs_le.mp (Work.EKLProd.mem_V_entries_le hg.1 i j)
    exact lt_of_le_of_lt (measure_mono hsub)
      ((hL.radon y hy).lt_top_of_isCompact
        (Work.EKLProd.sl3EntryBox_compact (fun _ _ => -(1 + r)) (fun _ _ => 1 + r)))

/-- `atomInfo` is nonnegative pointwise as soon as the plaque algebra is `aDiag t`-descending:
the pulled-back σ-algebra is coarser, hence its atom is larger, hence the shape is larger and
the conditional mass of the `A`-atom is at most `1`. -/
theorem atomInfo_nonneg_gl {U : Subgroup SL3} {ν : X3 → Measure SL3} {t : Fin 3 → ℝ}
    {A : MeasurableSpace X3}
    (hdec : MeasurableSpace.comap (fun y : X3 => aDiag t • y) A ≤ A) (x : X3) :
    0 ≤ atomInfo A U ν t x := by
  have hatom : atom A x ⊆ atom (MeasurableSpace.comap (fun y : X3 => aDiag t • y) A) x :=
    Set.sInter_mono (fun s hs => ⟨hdec s hs.1, hs.2⟩)
  have hsub : shape A U x ⊆ shape (MeasurableSpace.comap (fun y : X3 => aDiag t • y) A) U x :=
    fun u hu => ⟨hu.1, hatom hu.2⟩
  rw [show atomInfo A U ν t x = -Real.log ((ν x (shape A U x)).toReal /
      (ν x (shape (MeasurableSpace.comap (fun y : X3 => aDiag t • y) A) U x)).toReal)
      from rfl, neg_nonneg]
  by_cases htop : ν x (shape (MeasurableSpace.comap (fun y : X3 => aDiag t • y) A) U x) = ⊤
  · rw [htop, ENNReal.toReal_top]
    simp
  · have hle : (ν x (shape A U x)).toReal
        ≤ (ν x (shape (MeasurableSpace.comap (fun y : X3 => aDiag t • y) A) U x)).toReal :=
      ENNReal.toReal_mono htop (measure_mono hsub)
    have hden0 : (0 : ℝ) ≤ (ν x (shape (MeasurableSpace.comap
        (fun y : X3 => aDiag t • y) A) U x)).toReal := ENNReal.toReal_nonneg
    rcases eq_or_lt_of_le hden0 with h0 | hpos
    · rw [h0.symm, div_zero, Real.log_zero]
    · exact Real.log_nonpos (div_nonneg ENNReal.toReal_nonneg hden0)
        ((div_le_one hpos).mpr hle)

theorem growth_le_atomInfo_sandwich {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ] {U : Subgroup Work.EKLContract.SL3}
    {ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    {X' X'' : Set Work.EKLContract.X3} (t : Fin 3 → ℝ)
    (hL : Work.EKLContract.IsLeafwise μ U ν X') (hU : Work.EKLContract.IsHoro U)
    (hcov : Work.EKLC6Core.ACovariant ν X'') (hX'' : μ X''ᶜ = 0)
    (hAinv : Work.EKLContract.IsAInvariant μ)
    (hint : MeasureTheory.Integrable (Work.EKLC6Core.growthFun U ν t) μ)
    (hcontr : ∀ u ∈ U, Filter.Tendsto
      (fun n : ℕ => Work.EKLContract.aDiag t ^ n * u * (Work.EKLContract.aDiag t ^ n)⁻¹)
      Filter.atTop (nhds 1))
    {A : MeasurableSpace Work.EKLContract.X3} {Z : Set Work.EKLContract.X3}
    (hplaq : Work.EKLContract.IsPlaqueAlgebra U Z A)
    (hdec : MeasurableSpace.comap (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) A ≤ A)
    (hZ : μ Zᶜ = 0)
    (hmeas_atom : AEMeasurable (Work.EKLC6Core.atomInfo A U ν t) μ)
    {Y : ℕ → Set Work.EKLContract.X3} {δ R : ℕ → ℝ}
    (hYmeas : ∀ k : ℕ, @MeasurableSet Work.EKLContract.X3
      Work.EKLContract.instMeasurableSpaceX3 (Y k))
    (hδ : ∀ k, 0 < δ k) (hR : ∀ k, 0 < R k)
    (hY : ∀ (k : ℕ) (y : Work.EKLContract.X3), y ∈ Y k →
      (Work.EKLContract.V (δ k) ∩ (U : Set Work.EKLContract.SL3)) ⊆
          Work.EKLContract.shape A U y ∧
        Work.EKLContract.shape A U y ⊆ Work.EKLContract.V (R k))
    (hvisit : ∀ᵐ x ∂μ, ∃ k : ℕ, ∃ᶠ n in Filter.atTop,
      (Work.EKLContract.aDiag t ^ n) • x ∈ Y k) :
    ENNReal.ofReal (MeasureTheory.integral μ (fun x => Work.EKLC6Core.growthFun U ν t x)) ≤
      MeasureTheory.lintegral μ (fun x => ENNReal.ofReal (Work.EKLC6Core.atomInfo A U ν t x)) := by
  classical
  letI : MeasurableSpace X3 := instMeasurableSpaceX3
  rcases eq_or_ne (∫⁻ x, ENNReal.ofReal (atomInfo A U ν t x) ∂μ) ⊤ with htop | hne
  · rw [htop]; exact le_top
  have hAi_nn : 0 ≤ᵐ[μ] (fun x : X3 => atomInfo A U ν t x) :=
    Filter.Eventually.of_forall (fun x => atomInfo_nonneg_gl hdec x)
  have hAi_aesm : AEStronglyMeasurable (fun x : X3 => atomInfo A U ν t x) μ :=
    hmeas_atom.aestronglyMeasurable
  have hAi_int : Integrable (fun x : X3 => atomInfo A U ν t x) μ :=
    (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hAi_aesm hAi_nn).mp hne
  have hmp : MeasurePreserving (aShift t) μ μ := hAinv t
  have hbg : Integrable (fun x : X3 => growthFun U ν t x) μ := hint
  have hbAi := Work.EKLComp.birkhoff_all μ (aShift t) hmp
    (fun x : X3 => atomInfo A U ν t x) hAi_int
  have hbg' := Work.EKLComp.birkhoff_all μ (aShift t) hmp
    (fun x : X3 => growthFun U ν t x) hbg
  have hTpow := aShift_pow_apply (t := t)
  have hRI : ∀ᵐ x ∂μ, ∀ k : ℕ,
      (Filter.Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log
          ((ν ((aShift t)^[n] x) (V (δ k) ∩ (U : Set SL3))).toReal))
          Filter.atTop (nhds 0)) ∧
      (Filter.Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log
          ((ν ((aShift t)^[n] x) (V (R k) ∩ (U : Set SL3))).toReal))
          Filter.atTop (nhds 0)) := by
    rw [MeasureTheory.ae_all_iff]
    intro k
    have h1 := radius_independence (μ := μ) t hL hU hcov hX'' hAinv hint hcontr (hδ k)
    have h2 := radius_independence (μ := μ) t hL hU hcov hX'' hAinv hint hcontr (hR k)
    filter_upwards [h1, h2] with x hx1 hx2
    exact ⟨hx1.congr (fun n => by rw [hTpow n x]), hx2.congr (fun n => by rw [hTpow n x])⟩
  have hkey : condExp (MeasurableSpace.invariants (aShift t)) μ
        (fun x : X3 => atomInfo A U ν t x) =ᵐ[μ]
      condExp (MeasurableSpace.invariants (aShift t)) μ (fun x : X3 => growthFun U ν t x) := by
    have hAll : ∀ᵐ x ∂μ, ∀ j : ℕ, (aShift t)^[j] x ∈ X' ∩ X'' ∩ Z := by
      rw [MeasureTheory.ae_all_iff]
      intro j
      have hj : MeasurePreserving ((aShift t)^[j]) μ μ := hmp.iterate j
      have h1 : ∀ᵐ x ∂μ, (aShift t)^[j] x ∈ X' :=
        hj.quasiMeasurePreserving.ae (by rw [MeasureTheory.ae_iff]; exact hL.conull)
      have h2 : ∀ᵐ x ∂μ, (aShift t)^[j] x ∈ X'' :=
        hj.quasiMeasurePreserving.ae (by rw [MeasureTheory.ae_iff]; exact hX'')
      have h3 : ∀ᵐ x ∂μ, (aShift t)^[j] x ∈ Z :=
        hj.quasiMeasurePreserving.ae (by rw [MeasureTheory.ae_iff]; exact hZ)
      filter_upwards [h1, h2, h3] with x hx1 hx2 hx3
      exact ⟨⟨hx1, hx2⟩, hx3⟩
    have hTel := orbit_telescope_gl (μ := μ) t hL hU hcov hX'' hAinv hplaq hZ
    filter_upwards [hbAi, hbg', hTel, hRI, hvisit, hAll] with x hbAi_x hbg_x hTel_x hRI_x hvis hxg
    obtain ⟨k, hfreq⟩ := hvis
    have hfreq' : ∀ N : ℕ, ∃ n : ℕ, N + 1 ≤ n ∧ (aDiag t ^ n) • x ∈ Y k :=
      fun N => (Filter.frequently_atTop).mp hfreq (N + 1)
    choose φ hφ using hfreq'
    have hφmemA : ∀ n : ℕ, (aDiag t ^ φ n) • x ∈ Y k := fun n => (hφ n).2
    have hφmem : ∀ n : ℕ, (aShift t)^[φ n] x ∈ Y k := fun n => by
      rw [hTpow]; exact hφmemA n
    have hφtop : Filter.Tendsto φ Filter.atTop Filter.atTop := by
      rw [Filter.tendsto_atTop_atTop]
      intro b
      exact ⟨b, fun a ha => le_trans ha (le_trans (Nat.le_succ a) (hφ a).1)⟩
    have hLim1 : Filter.Tendsto (fun n : ℕ => Work.EKLComp.Birkhoff.birkA (aShift t)
        (fun x : X3 => atomInfo A U ν t x) (φ n) x) Filter.atTop
        (nhds (condExp (MeasurableSpace.invariants (aShift t)) μ
          (fun x : X3 => atomInfo A U ν t x) x)) := hbAi_x.comp hφtop
    have hsumg : ∀ n : ℕ, (∑ j ∈ Finset.range (φ n), growthFun U ν t ((aShift t)^[j+1] x))
        = ((φ n : ℝ) + 1) * Work.EKLComp.Birkhoff.birkA (aShift t)
            (fun x : X3 => growthFun U ν t x) (φ n + 1) x - growthFun U ν t x := by
      intro n
      have hcast : ((φ n + 1 : ℕ) : ℝ) = (φ n : ℝ) + 1 := by push_cast; ring
      rw [Work.EKLComp.Birkhoff.birkA_def, hcast, Finset.sum_range_succ']
      simp only [Function.iterate_zero_apply]
      have hne : ((φ n : ℝ) + 1) ≠ 0 := by positivity
      field_simp
      ring
    have hest : ∀ n : ℕ, Work.EKLComp.Birkhoff.birkA (aShift t)
          (fun x : X3 => atomInfo A U ν t x) (φ n) x
        = ((φ n : ℝ)⁻¹ * ((φ n : ℝ) + 1)) * Work.EKLComp.Birkhoff.birkA (aShift t)
            (fun x : X3 => growthFun U ν t x) (φ n + 1) x
          + (φ n : ℝ)⁻¹ * (Real.log ((ν ((aShift t)^[φ n] x)
                (shape A U ((aShift t)^[φ n] x))).toReal)
              - Real.log ((ν x (shape A U x)).toReal) - growthFun U ν t x) := by
      intro n
      have htel := hTel_x (φ n)
      rw [Work.EKLComp.Birkhoff.birkA_def]
      rw [show (∑ k ∈ Finset.range (φ n),
            (fun x : X3 => atomInfo A U ν t x) ((aShift t)^[k] x))
          = ∑ k ∈ Finset.range (φ n), atomInfo A U ν t ((aShift t)^[k] x) from rfl, htel]
      rw [hsumg n]
      ring
    have hφinv_nn : ∀ n : ℕ, (0 : ℝ) ≤ (φ n : ℝ)⁻¹ :=
      fun n => inv_nonneg.mpr (Nat.cast_nonneg _)
    have hψlim : Filter.Tendsto (fun n : ℕ => (φ n : ℝ)⁻¹ * Real.log
        ((ν ((aShift t)^[φ n] x) (shape A U ((aShift t)^[φ n] x))).toReal))
        Filter.atTop (nhds 0) := by
      have hlow : Filter.Tendsto (fun n : ℕ => (φ n : ℝ)⁻¹ * Real.log
          ((ν ((aShift t)^[φ n] x) (V (δ k) ∩ (U : Set SL3))).toReal))
          Filter.atTop (nhds 0) := (hRI_x k).1.comp hφtop
      have hup : Filter.Tendsto (fun n : ℕ => (φ n : ℝ)⁻¹ * Real.log
          ((ν ((aShift t)^[φ n] x) (V (R k) ∩ (U : Set SL3))).toReal))
          Filter.atTop (nhds 0) := (hRI_x k).2.comp hφtop
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlow hup ?_ ?_
      · intro n
        have hy : (aShift t)^[φ n] x ∈ Y k := hφmem n
        have hgood : (aShift t)^[φ n] x ∈ X' ∩ X'' ∩ Z := hxg (φ n)
        have hbox := V_mass_facts_gl hL hgood.1.1 (hδ k)
        have hspos := shape_mass_pos hL hplaq hgood.1.1 hgood.2
        have hle : (ν ((aShift t)^[φ n] x) (V (δ k) ∩ (U : Set SL3))).toReal
            ≤ (ν ((aShift t)^[φ n] x) (shape A U ((aShift t)^[φ n] x))).toReal :=
          ENNReal.toReal_mono (ne_of_lt hspos.2) (measure_mono (hY k _ hy).1)
        exact mul_le_mul_of_nonneg_left
          (Real.log_le_log (ENNReal.toReal_pos (ne_of_gt hbox.2.1) (ne_of_lt hbox.2.2)) hle)
          (hφinv_nn n)
      · intro n
        have hy : (aShift t)^[φ n] x ∈ Y k := hφmem n
        have hgood : (aShift t)^[φ n] x ∈ X' ∩ X'' ∩ Z := hxg (φ n)
        have hbox := V_mass_facts_gl hL hgood.1.1 (hR k)
        have hspos := shape_mass_pos hL hplaq hgood.1.1 hgood.2
        have hle : ν ((aShift t)^[φ n] x) (shape A U ((aShift t)^[φ n] x))
            ≤ ν ((aShift t)^[φ n] x) (V (R k) ∩ (U : Set SL3)) := by
          rw [hbox.1]
          exact measure_mono (hY k _ hy).2
        have hle' : (ν ((aShift t)^[φ n] x) (shape A U ((aShift t)^[φ n] x))).toReal
            ≤ (ν ((aShift t)^[φ n] x) (V (R k) ∩ (U : Set SL3))).toReal :=
          ENNReal.toReal_mono (ne_of_lt hbox.2.2) hle
        exact mul_le_mul_of_nonneg_left
          (Real.log_le_log (ENNReal.toReal_pos (ne_of_gt hspos.1) (ne_of_lt hspos.2)) hle')
          (hφinv_nn n)
    have hcastφ : Filter.Tendsto (fun n : ℕ => (φ n : ℝ)) Filter.atTop Filter.atTop :=
      tendsto_natCast_atTop_atTop.comp hφtop
    have h_inv : Filter.Tendsto (fun n : ℕ => (φ n : ℝ)⁻¹) Filter.atTop (nhds 0) :=
      (hcastφ.const_div_atTop 1).congr (fun n => one_div (φ n : ℝ))
    have hβ : Filter.Tendsto (fun n : ℕ => (φ n : ℝ)⁻¹ * ((φ n : ℝ) + 1)) Filter.atTop
        (nhds 1) := by
      have hone : Filter.Tendsto (fun n : ℕ => (1 : ℝ) + (φ n : ℝ)⁻¹) Filter.atTop
          (nhds 1) := by simpa using tendsto_const_nhds.add h_inv
      refine hone.congr' (Filter.Eventually.of_forall (fun n => ?_))
      have hne : (φ n : ℝ) ≠ 0 := by
        have h : 0 < φ n := by have h1 := (hφ n).1; omega
        exact_mod_cast h.ne'
      field_simp
    have hΦtop : Filter.Tendsto (fun n : ℕ => φ n + 1) Filter.atTop Filter.atTop := by
      rw [Filter.tendsto_atTop_atTop]
      intro b
      exact ⟨b, fun a ha => by have h := (hφ a).1; omega⟩
    have hB : Filter.Tendsto (fun n : ℕ => Work.EKLComp.Birkhoff.birkA (aShift t)
        (fun x : X3 => growthFun U ν t x) (φ n + 1) x) Filter.atTop
        (nhds (condExp (MeasurableSpace.invariants (aShift t)) μ
          (fun x : X3 => growthFun U ν t x) x)) := hbg_x.comp hΦtop
    have htail : Filter.Tendsto (fun n : ℕ => (φ n : ℝ)⁻¹ * (Real.log
          ((ν ((aShift t)^[φ n] x) (shape A U ((aShift t)^[φ n] x))).toReal)
        - Real.log ((ν x (shape A U x)).toReal) - growthFun U ν t x)) Filter.atTop (nhds 0) := by
      have h2 : Filter.Tendsto (fun n : ℕ => (φ n : ℝ)⁻¹ *
          (Real.log ((ν x (shape A U x)).toReal) + growthFun U ν t x)) Filter.atTop (nhds 0) := by
        have h := h_inv.mul_const (Real.log ((ν x (shape A U x)).toReal) + growthFun U ν t x)
        simpa using h
      have hcomb : Filter.Tendsto (fun n : ℕ => (φ n : ℝ)⁻¹ * Real.log
            ((ν ((aShift t)^[φ n] x) (shape A U ((aShift t)^[φ n] x))).toReal)
          - (φ n : ℝ)⁻¹ * (Real.log ((ν x (shape A U x)).toReal) + growthFun U ν t x))
          Filter.atTop (nhds 0) := by simpa using hψlim.sub h2
      refine hcomb.congr' (Filter.Eventually.of_forall (fun n => ?_))
      ring
    have hlim_rhs : Filter.Tendsto (fun n : ℕ =>
          ((φ n : ℝ)⁻¹ * ((φ n : ℝ) + 1)) * Work.EKLComp.Birkhoff.birkA (aShift t)
            (fun x : X3 => growthFun U ν t x) (φ n + 1) x
          + (φ n : ℝ)⁻¹ * (Real.log ((ν ((aShift t)^[φ n] x)
                (shape A U ((aShift t)^[φ n] x))).toReal)
              - Real.log ((ν x (shape A U x)).toReal) - growthFun U ν t x)) Filter.atTop
        (nhds (condExp (MeasurableSpace.invariants (aShift t)) μ
          (fun x : X3 => growthFun U ν t x) x)) := by
      have h := (hβ.mul hB).add htail
      simpa using h
    have hLim2 : Filter.Tendsto (fun n : ℕ => Work.EKLComp.Birkhoff.birkA (aShift t)
        (fun x : X3 => atomInfo A U ν t x) (φ n) x) Filter.atTop
        (nhds (condExp (MeasurableSpace.invariants (aShift t)) μ
          (fun x : X3 => growthFun U ν t x) x)) :=
      hlim_rhs.congr' (Filter.Eventually.of_forall (fun n => (hest n).symm))
    exact tendsto_nhds_unique hLim1 hLim2
  have hcs : (fun x : X3 => condExp (MeasurableSpace.invariants (aShift t)) μ
        (fun x : X3 => atomInfo A U ν t x) x)
      =ᵐ[μ] (fun x : X3 => condExp (MeasurableSpace.invariants (aShift t)) μ
        (fun x : X3 => growthFun U ν t x) x) := hkey
  have hIntEq : ∫ x, growthFun U ν t x ∂μ = ∫ x, atomInfo A U ν t x ∂μ := by
    have h1 : ∫ x, condExp (MeasurableSpace.invariants (aShift t)) μ
          (fun x : X3 => atomInfo A U ν t x) x ∂μ = ∫ x, atomInfo A U ν t x ∂μ :=
      MeasureTheory.integral_condExp (μ := μ) (f := fun x : X3 => atomInfo A U ν t x)
        (m := MeasurableSpace.invariants (aShift t)) (m₀ := inferInstance)
        (MeasurableSpace.invariants_le (aShift t))
    have h2 : ∫ x, condExp (MeasurableSpace.invariants (aShift t)) μ
          (fun x : X3 => growthFun U ν t x) x ∂μ = ∫ x, growthFun U ν t x ∂μ :=
      MeasureTheory.integral_condExp (μ := μ) (f := fun x : X3 => growthFun U ν t x)
        (m := MeasurableSpace.invariants (aShift t)) (m₀ := inferInstance)
        (MeasurableSpace.invariants_le (aShift t))
    rw [← h2, ← h1]
    exact MeasureTheory.integral_congr_ae hcs.symm
  calc ENNReal.ofReal (MeasureTheory.integral μ (fun x => growthFun U ν t x))
      = ENNReal.ofReal (∫ x, atomInfo A U ν t x ∂μ) := by rw [hIntEq]
    _ ≤ ∫⁻ x, ENNReal.ofReal (atomInfo A U ν t x) ∂μ :=
        ofReal_integral_le_lintegral_ofReal hAi_int
    _ = MeasureTheory.lintegral μ (fun x => ENNReal.ofReal (atomInfo A U ν t x)) := rfl

end Work.EKLC6Core

end
