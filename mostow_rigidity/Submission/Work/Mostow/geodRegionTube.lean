import Mathlib
import Submission.Work.Mostow.geodSetup
import Submission.Work.Mostow.margRegionInvariant
import Submission.Work.Mostow.tubeIneq
import Submission.Work.Mostow.fermiW_chart
import Submission.Work.Mostow.volH_le_card_mul_of_ae_count
import Submission.Work.Mostow.margRegionNrmCSat
import Submission.Work.Mostow.margRegionMeasurable
import Submission.Work.Mostow.geodPtCardFinite
import Submission.Work.Mostow.nearIdAtBlkChar
import Submission.Work.Mostow.resStd_hom_discrete
import Submission.Work.Mostow.fund_domain_hull_null
import Submission.Work.Mostow.blk_hom
import Submission.Work.Mostow.blk_smul_fermi
import Submission.Work.Mostow.fermiW_mem_margRegion
import Submission.Work.Mostow.foot_fermiW
import Submission.Work.Mostow.geodPtFinset
import Submission.Work.Mostow.volH_fermiW_prod
import Submission.Work.Mostow.fermiW_image_measurable

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory
open scoped ENNReal Pointwise

set_option linter.style.haveILetI false

noncomputable section

/-! ## The normal image of the Margulis region -/

def grtU (m : ℕ) (Λ : Subgroup (PO (1 + m) 1)) (η₁ : ℝ) : Set (E m) :=
  {W : E m | Submission.Mostow.fermiW 1 m (0 : E 1) W ∈ Work.Mostow.margRegion m Λ η₁}

def grtTube (m : ℕ) (Λ : Subgroup (PO (1 + m) 1)) (η₁ : ℝ) (DY : Set (E 1)) : Set (E (1 + m)) :=
  (fun p : E 1 × E m => Submission.Mostow.fermiW 1 m p.1 p.2) ''
    (toMeasurable (Submission.Mostow.volH 1) DY ×ˢ grtU m Λ η₁)

lemma grtU_eq (m : ℕ) (hA : Submission.Mostow.POActionProp (1 + m))
    (hI : Submission.Mostow.HypIsometryProp (1 + m)) (hA1 : Submission.Mostow.POActionProp 1)
    (hI1 : Submission.Mostow.HypIsometryProp 1) (Λ : Subgroup (PO (1 + m) 1)) (η₁ : ℝ) :
    grtU m Λ η₁ = Submission.Mostow.nrmC 1 m '' Work.Mostow.margRegion m Λ η₁ := by
  ext W
  constructor
  · intro hW
    exact ⟨Submission.Mostow.fermiW 1 m (0 : E 1) W, hW, Work.Mostow.nib_nrmC_fermiW m 0 W⟩
  · rintro ⟨u, hu, rfl⟩
    show Submission.Mostow.fermiW 1 m (0 : E 1) (Submission.Mostow.nrmC 1 m u) ∈
      Work.Mostow.margRegion m Λ η₁
    exact margRegionNrmCSat m hA hI hA1 hI1 Λ η₁ u _
      (by rw [Work.Mostow.nib_nrmC_fermiW]) hu

lemma grtU_measurable (m : ℕ) (hA : Submission.Mostow.POActionProp (1 + m))
    (hI : Submission.Mostow.HypIsometryProp (1 + m))
    (Λ : Subgroup (PO (1 + m) 1))
    (hdisc : _root_.IsDiscrete (SetLike.coe Λ)) (η₁ : ℝ) :
    MeasurableSet (grtU m Λ η₁) := by
  have h1 : (fun W : E m => Submission.Mostow.fermiW 1 m (0 : E 1) W)
      = fun W => Work.Mostow.prodeMap 1 m ((0 : E 1), W) := by
    funext W
    rw [Work.Mostow.fermiW_eq_prodeMap, smul_zero]
  have hmeas : Measurable (fun W : E m => Submission.Mostow.fermiW 1 m (0 : E 1) W) := by
    rw [h1]
    exact (Work.Mostow.measurable_prodeMap_one m).comp
      (Measurable.prodMk measurable_const measurable_id)
  exact (margRegionMeasurable m hA hI Λ hdisc η₁).preimage hmeas

/-- every point of the slice over `grtU`, at any foot, lies in the Margulis region -/
lemma grt_image_subset_marg (m : ℕ) (hA : Submission.Mostow.POActionProp (1 + m))
    (hI : Submission.Mostow.HypIsometryProp (1 + m)) (hA1 : Submission.Mostow.POActionProp 1)
    (hI1 : Submission.Mostow.HypIsometryProp 1) (Λ : Subgroup (PO (1 + m) 1)) (η₁ : ℝ)
    (A : Set (E 1)) :
    (fun p : E 1 × E m => Submission.Mostow.fermiW 1 m p.1 p.2) '' (A ×ˢ grtU m Λ η₁)
      ⊆ Work.Mostow.margRegion m Λ η₁ := by
  rintro u ⟨⟨v, W⟩, ⟨-, hW⟩, rfl⟩
  exact margRegionNrmCSat m hA hI hA1 hI1 Λ η₁
    (Submission.Mostow.fermiW 1 m (0 : E 1) W) _
    (by rw [Work.Mostow.nib_nrmC_fermiW, Work.Mostow.nib_nrmC_fermiW]) hW

lemma grtTube_subset_marg (m : ℕ) (hA : Submission.Mostow.POActionProp (1 + m))
    (hI : Submission.Mostow.HypIsometryProp (1 + m)) (hA1 : Submission.Mostow.POActionProp 1)
    (hI1 : Submission.Mostow.HypIsometryProp 1) (Λ : Subgroup (PO (1 + m) 1)) (η₁ : ℝ)
    (DY : Set (E 1)) : grtTube m Λ η₁ DY ⊆ Work.Mostow.margRegion m Λ η₁ :=
  grt_image_subset_marg m hA hI hA1 hI1 Λ η₁ _

lemma grtTube_measurable (m : ℕ) (hA : Submission.Mostow.POActionProp (1 + m))
    (hI : Submission.Mostow.HypIsometryProp (1 + m))
    (Λ : Subgroup (PO (1 + m) 1)) (hdisc : _root_.IsDiscrete (SetLike.coe Λ)) (η₁ : ℝ)
    (DY : Set (E 1)) : MeasurableSet (grtTube m Λ η₁ DY) := by
  rw [grtTube]
  exact fermiW_image_measurable m _
    (grtU m Λ η₁) (measurableSet_toMeasurable _ _)
    (grtU_measurable m hA hI Λ hdisc η₁)

lemma grtTube_measure (m : ℕ) (hA : Submission.Mostow.POActionProp (1 + m))
    (hI : Submission.Mostow.HypIsometryProp (1 + m)) (hA1 : Submission.Mostow.POActionProp 1)
    (hI1 : Submission.Mostow.HypIsometryProp 1)
    (Λ : Subgroup (PO (1 + m) 1)) (hdisc : _root_.IsDiscrete (SetLike.coe Λ)) (η₁ : ℝ)
    (DY : Set (E 1)) :
    Submission.Mostow.volH (1 + m) (grtTube m Λ η₁ DY)
      = Submission.Mostow.volH 1 DY *
        (MeasureTheory.volume : MeasureTheory.Measure (E m))
          (Submission.Mostow.nrmC 1 m '' Work.Mostow.margRegion m Λ η₁) := by
  rw [grtTube]
  rw [volH_fermiW_prod m _ _ (measurableSet_toMeasurable _ _)
        (grtU_measurable m hA hI Λ hdisc η₁)]
  rw [MeasureTheory.measure_toMeasurable, grtU_eq m hA hI hA1 hI1 Λ η₁]

/-- the foot of a point of the slice lies in (the hull of) `DY` -/
lemma grt_foot_mem (m : ℕ) (Λ : Subgroup (PO (1 + m) 1)) (η₁ : ℝ) {DY : Set (E 1)}
    {p : E (1 + m)} (hp : p ∈ grtTube m Λ η₁ DY) :
    (Submission.Mostow.fermiInv 1 m p).1 ∈ toMeasurable (Submission.Mostow.volH 1) DY := by
  rw [grtTube] at hp
  obtain ⟨⟨v, W⟩, ⟨hv, -⟩, rfl⟩ := hp
  rw [foot_fermiW]
  exact hv

/-- a measure-preserving isometry maps null sets to null sets -/
lemma volH_smul_null {n : ℕ} (hA : Submission.Mostow.POActionProp n)
    (hI : Submission.Mostow.HypIsometryProp n) (g : PO n 1) {Z : Set (E n)}
    (hZ : Submission.Mostow.volH n Z = 0) : Submission.Mostow.volH n (g • Z) = 0 := by
  letI : MulAction (PO n 1) (E n) :=
    { toSMul := Submission.Mostow.instSMulPO, one_smul := hA.2.2.2.1, mul_smul := hA.2.2.2.2.1 }
  have hpre : (fun u : E n => g⁻¹ • u) ⁻¹' Z = g • Z := by
    ext x
    simp [Set.mem_smul_set_iff_inv_smul_mem]
  rw [← hpre]
  exact ((hI.2.2.2.2.2.2.2.2.2.2.2.1 g⁻¹).quasiMeasurePreserving).preimage_null hZ


/-- the group law for the action, in the `(g * h⁻¹) • (h • u) = g • u` shape -/
lemma grt_smul_mul_inv {n : ℕ} (hA : Submission.Mostow.POActionProp n) (g h : PO n 1) (u : E n) :
    (g * h⁻¹) • (h • u) = g • u := by
  calc (g * h⁻¹) • (h • u) = g • (h⁻¹ • (h • u)) := hA.2.2.2.2.1 g h⁻¹ (h • u)
    _ = g • ((h⁻¹ * h) • u) := by rw [hA.2.2.2.2.1]
    _ = g • ((1 : PO n 1) • u) := by rw [inv_mul_cancel]
    _ = g • u := by rw [hA.2.2.2.1]

lemma grt_inv_smul_smul {n : ℕ} (hA : Submission.Mostow.POActionProp n) (g : PO n 1) (u : E n) :
    g⁻¹ • (g • u) = u := by
  calc g⁻¹ • (g • u) = (g⁻¹ * g) • u := (hA.2.2.2.2.1 g⁻¹ g u).symm
    _ = (1 : PO n 1) • u := by rw [inv_mul_cancel]
    _ = u := hA.2.2.2.1 u

/-! ## The a.e. multiplicity bound -/

theorem grtCountAux (m : ℕ) (hA : Submission.Mostow.POActionProp (1 + m))
    (hI : Submission.Mostow.HypIsometryProp (1 + m))
    (hA1 : Submission.Mostow.POActionProp 1) (hI1 : Submission.Mostow.HypIsometryProp 1)
    (Λ : Subgroup (PO (1 + m) 1)) (hdisc : _root_.IsDiscrete (SetLike.coe Λ))
    (D : Set (E (1 + m)))
    (hD : MeasureTheory.IsFundamentalDomain Λ D (Submission.Mostow.volH (1 + m)))
    (η₁ : ℝ) (DY : Set (E 1))
    (hDY : MeasureTheory.IsFundamentalDomain
      (Subgroup.closure (Submission.Mostow.resStd 1 m ''
        (Work.Mostow.geodStab m hA Λ : Set (PO (1 + m) 1)))) DY (Submission.Mostow.volH 1))
    (h6 : ∀ (u v : E (1 + m)), u ∈ Work.Mostow.margRegion m Λ η₁ →
      v ∈ Work.Mostow.margRegion m Λ η₁ →
      ∀ γ : PO (1 + m) 1, γ ∈ Λ → γ • u = v → γ ∈ Work.Mostow.geodStab m hA Λ) :
    ∀ᵐ z ∂((Submission.Mostow.volH (1 + m)).restrict D),
      ∃ s : Finset Λ, s.card ≤ Work.Mostow.geodPtCard m Λ ∧
        ∀ γ : Λ, (γ : PO (1 + m) 1) • z ∈ grtTube m Λ η₁ DY → γ ∈ s := by
  classical
  set G : Subgroup (PO 1 1) := Subgroup.closure (Submission.Mostow.resStd 1 m ''
    (Work.Mostow.geodStab m hA Λ : Set (PO (1 + m) 1))) with hGdef
  set DY' : Set (E 1) := toMeasurable (Submission.Mostow.volH 1) DY with hDY'def
  set U : Set (E m) := grtU m Λ η₁ with hUdef
  set F : Set (E (1 + m)) := grtTube m Λ η₁ DY with hFdef
  obtain ⟨hPfin, -⟩ := Work.Mostow.geodPtCardFinite m hA hI hA1 hI1 Λ hdisc
  have hstabDisc : IsDiscrete (SetLike.coe (Work.Mostow.geodStab m hA Λ)) :=
    hdisc.mono (fun g hg => hg.1)
  have hGdisc : IsDiscrete (SetLike.coe G) := by
    have h := (Work.Mostow.resStd_hom_discrete 1 m hA1 hI1 hA hI).2
      (Work.Mostow.geodStab m hA Λ) hstabDisc (fun c hc => hc.2)
    rw [hGdef]
    exact h.1
  haveI : Countable G := (Work.Mostow.countable_of_isDiscrete (PO 1 1) hGdisc).to_subtype
  haveI : Countable Λ := (Work.Mostow.countable_of_isDiscrete (PO (1 + m) 1) hdisc).to_subtype
  -- the exceptional null set
  set EXC : Set (E 1) := ⋃ (g : {g : G // g ≠ 1}),
    (fun x : E 1 => ((g : G) : PO 1 1) • x) '' DY' ∩ DY' with hEXCdef
  have hEXCnull : Submission.Mostow.volH 1 EXC = 0 := by
    rw [hEXCdef]
    refine measure_iUnion_null fun g => ?_
    have h := Work.Mostow.fund_domain_hull_null 1 hI1 G DY hDY (g : G) g.2
    rw [hDY'def, Set.inter_comm]
    exact h
  -- the bad points
  set T : Set (E (1 + m)) :=
    F ∩ {p : E (1 + m) | (Submission.Mostow.fermiInv 1 m p).1 ∈ EXC} with hTdef
  have hTnull : Submission.Mostow.volH (1 + m) T = 0 := by
    have hsub : T ⊆ (fun p : E 1 × E m => Submission.Mostow.fermiW 1 m p.1 p.2) ''
        (toMeasurable (Submission.Mostow.volH 1) EXC ×ˢ U) := by
      rintro p ⟨hpF, hpexc⟩
      rw [hFdef] at hpF
      simp only [grtTube] at hpF
      obtain ⟨⟨v, W⟩, ⟨hv, hW⟩, rfl⟩ := hpF
      refine ⟨(v, W), ⟨?_, hW⟩, rfl⟩
      have h1 : (Submission.Mostow.fermiInv 1 m (Submission.Mostow.fermiW 1 m v W)).1 ∈ EXC := hpexc
      rw [foot_fermiW] at h1
      exact subset_toMeasurable _ _ h1
    refine le_antisymm ?_ zero_le
    calc Submission.Mostow.volH (1 + m) T
        ≤ Submission.Mostow.volH (1 + m) ((fun p : E 1 × E m =>
            Submission.Mostow.fermiW 1 m p.1 p.2) ''
            (toMeasurable (Submission.Mostow.volH 1) EXC ×ˢ U)) := measure_mono hsub
      _ = Submission.Mostow.volH 1 (toMeasurable (Submission.Mostow.volH 1) EXC) *
            (MeasureTheory.volume : MeasureTheory.Measure (E m)) U :=
          volH_fermiW_prod m _ U (measurableSet_toMeasurable _ _)
            (grtU_measurable m hA hI Λ hdisc η₁)
      _ = 0 * (MeasureTheory.volume : MeasureTheory.Measure (E m)) U := by
          rw [measure_toMeasurable, hEXCnull]
      _ = 0 := zero_mul _
  -- bad points are transported back
  set Bad : Set (E (1 + m)) :=
    ⋃ γ : Λ, (fun u : E (1 + m) => ((γ : Λ) : PO (1 + m) 1)⁻¹ • u) '' T with hBaddef
  have hBadnull : Submission.Mostow.volH (1 + m) Bad = 0 := by
    rw [hBaddef]
    exact measure_iUnion_null fun γ => volH_smul_null hA hI ((γ : Λ) : PO (1 + m) 1)⁻¹ hTnull
  have hae : ∀ᵐ z ∂((Submission.Mostow.volH (1 + m)).restrict D), z ∉ Bad := by
    rw [ae_iff]
    have h0 : ((Submission.Mostow.volH (1 + m)).restrict D) Bad = 0 :=
      le_antisymm (le_trans (Measure.restrict_apply_le _ _) (le_of_eq hBadnull)) zero_le
    simpa using h0
  filter_upwards [hae] with z hz
  by_cases hne : ∃ γ : Λ, ((γ : Λ) : PO (1 + m) 1) • z ∈ F
  · obtain ⟨γ₂, hγ₂⟩ := hne
    have hγ₂raw : ((γ₂ : Λ) : PO (1 + m) 1) • z ∈ grtTube m Λ η₁ DY := by
      rw [← hFdef]; exact hγ₂
    have hkey : ∀ γ : Λ, ((γ : Λ) : PO (1 + m) 1) • z ∈ F →
        (((γ : Λ) : PO (1 + m) 1) * ((γ₂ : Λ) : PO (1 + m) 1)⁻¹) ∈ Work.Mostow.geodStab m hA Λ ∧
        Submission.Mostow.resStd 1 m (((γ : Λ) : PO (1 + m) 1) *
          ((γ₂ : Λ) : PO (1 + m) 1)⁻¹) = 1 := by
      intro γ hγ
      have hγraw : ((γ : Λ) : PO (1 + m) 1) • z ∈ grtTube m Λ η₁ DY := by
        rw [← hFdef]; exact hγ
      have hmem : (((γ : Λ) : PO (1 + m) 1) * ((γ₂ : Λ) : PO (1 + m) 1)⁻¹) ∈
          Work.Mostow.geodStab m hA Λ := by
        refine h6 (((γ₂ : Λ) : PO (1 + m) 1) • z) (((γ : Λ) : PO (1 + m) 1) • z) ?_ ?_
          (((γ : Λ) : PO (1 + m) 1) * ((γ₂ : Λ) : PO (1 + m) 1)⁻¹) ?_ ?_
        · exact grtTube_subset_marg m hA hI hA1 hI1 Λ η₁ DY hγ₂raw
        · exact grtTube_subset_marg m hA hI hA1 hI1 Λ η₁ DY hγraw
        · exact Λ.mul_mem γ.2 (Λ.inv_mem γ₂.2)
        · exact grt_smul_mul_inv hA _ _ _
      refine ⟨hmem, ?_⟩
      by_contra hresne
      have hdstab : (((γ : Λ) : PO (1 + m) 1) * ((γ₂ : Λ) : PO (1 + m) 1)⁻¹) ∈
          Submission.Mostow.SetStabStd 1 m := hmem.2
      have hgmem : Submission.Mostow.resStd 1 m
          (((γ : Λ) : PO (1 + m) 1) * ((γ₂ : Λ) : PO (1 + m) 1)⁻¹) ∈ G :=
        Subgroup.subset_closure ⟨_, hmem, rfl⟩
      set g₀ : {g : G // g ≠ 1} :=
        ⟨⟨Submission.Mostow.resStd 1 m
            (((γ : Λ) : PO (1 + m) 1) * ((γ₂ : Λ) : PO (1 + m) 1)⁻¹), hgmem⟩, by
          intro hh
          apply hresne
          have h1 : (⟨Submission.Mostow.resStd 1 m
              (((γ : Λ) : PO (1 + m) 1) * ((γ₂ : Λ) : PO (1 + m) 1)⁻¹), hgmem⟩ : G) = 1 := hh
          have h2 := congrArg (fun x : G => (x : PO 1 1)) h1
          simpa using h2⟩ with hg₀def
      have hfoot : (Submission.Mostow.fermiInv 1 m (((γ : Λ) : PO (1 + m) 1) • z)).1 =
          ((g₀ : G) : PO 1 1) •
            (Submission.Mostow.fermiInv 1 m (((γ₂ : Λ) : PO (1 + m) 1) • z)).1 := by
        have hfa := Work.Mostow.ti_foot_action 1 m hA1 hI1 hA hI
          (((γ : Λ) : PO (1 + m) 1) * ((γ₂ : Λ) : PO (1 + m) 1)⁻¹) hdstab
          (((γ₂ : Λ) : PO (1 + m) 1) • z)
        have hact : (((γ : Λ) : PO (1 + m) 1) * ((γ₂ : Λ) : PO (1 + m) 1)⁻¹) •
            (((γ₂ : Λ) : PO (1 + m) 1) • z) = ((γ : Λ) : PO (1 + m) 1) • z :=
          grt_smul_mul_inv hA _ _ _
        rw [hact] at hfa
        simpa [hg₀def] using hfa
      have hf₁ := grt_foot_mem m Λ η₁ hγraw
      have hf₂ := grt_foot_mem m Λ η₁ hγ₂raw
      have hexc : (Submission.Mostow.fermiInv 1 m (((γ : Λ) : PO (1 + m) 1) • z)).1 ∈ EXC := by
        rw [hEXCdef]
        refine Set.mem_iUnion.mpr ⟨g₀, ?_⟩
        rw [hfoot]
        refine Set.mem_inter ?_ ?_
        · exact ⟨_, hf₂, rfl⟩
        · exact hfoot ▸ hf₁
      have hzmem : z ∈ (fun u : E (1 + m) => ((γ : Λ) : PO (1 + m) 1)⁻¹ • u) '' T := by
        exact ⟨((γ : Λ) : PO (1 + m) 1) • z, ⟨hγ, hexc⟩, grt_inv_smul_smul hA _ _⟩
      rw [hBaddef] at hz
      exact hz (Set.mem_iUnion.mpr ⟨γ, hzmem⟩)
    exact geodPtFinset m hA Λ z F γ₂ hPfin hkey
  · refine ⟨∅, by simp, fun γ hγ => absurd ⟨γ, hγ⟩ hne⟩

/-! ## The tube-volume inequality -/

theorem geodRegionTube (m : ℕ) (hm : 4 ≤ m) (hev : Even m)
    (hA : Submission.Mostow.POActionProp (1 + m)) (hI : Submission.Mostow.HypIsometryProp (1 + m))
    (hA1 : Submission.Mostow.POActionProp 1) (hI1 : Submission.Mostow.HypIsometryProp 1) :
    ∃ Cn : ℝ, 0 < Cn ∧ ∃ η₁max : ℝ, 0 < η₁max ∧ ∀ η₁ : ℝ, 0 < η₁ → η₁ ≤ η₁max →
      ∀ (Λ : Subgroup (LeanEval.Geometry.MostowRigidity.PO (1 + m) 1))
        (D : Set (Submission.Mostow.E (1 + m)))
        (R : Submission.Mostow.E m ≃ₗᵢ[ℝ] Submission.Mostow.E m),
        _root_.IsDiscrete (SetLike.coe Λ) →
        MeasureTheory.IsFundamentalDomain Λ D (Submission.Mostow.volH (1 + m)) →
        Submission.Mostow.blk 1 m 1 R ∈ Λ → (∀ w : Submission.Mostow.E m, R w = w → w = 0) →
        (∀ (a : LeanEval.Geometry.MostowRigidity.PO (1 + m) 1) (u : Submission.Mostow.E (1 + m)),
          a ∈ Λ → a ∈ Submission.Mostow.SetStabStd 1 m →
          Submission.Mostow.resStd 1 m a = 1 → a ≠ 1 → Submission.Mostow.NearIdAt a u η₁ →
          Submission.Mostow.fixSet a = Submission.Mostow.stdTG 1 m) →
        (∀ u v : Submission.Mostow.E (1 + m), u ∈ Work.Mostow.margRegion m Λ η₁ →
          v ∈ Work.Mostow.margRegion m Λ η₁ →
          ∀ γ : LeanEval.Geometry.MostowRigidity.PO (1 + m) 1, γ ∈ Λ → γ • u = v →
          γ ∈ Work.Mostow.geodStab m hA Λ) →
        ∀ (DY : Set (Submission.Mostow.E 1)),
          MeasureTheory.IsFundamentalDomain
            (Subgroup.closure (Submission.Mostow.resStd 1 m ''
              (Work.Mostow.geodStab m hA Λ : Set (LeanEval.Geometry.MostowRigidity.PO (1 + m) 1))))
            DY (Submission.Mostow.volH 1) →
          Submission.Mostow.volH 1 DY *
              (MeasureTheory.volume : MeasureTheory.Measure (Submission.Mostow.E m))
                (Submission.Mostow.nrmC 1 m '' Work.Mostow.margRegion m Λ η₁) ≤
            ENNReal.ofReal Cn * (Work.Mostow.geodPtCard m Λ : ENNReal) *
              Submission.Mostow.volH (1 + m) D := by
  refine ⟨1, one_pos, 1, one_pos, ?_⟩
  intro η₁ hη₁ hle Λ D R hdisc hD hblk hR hgap h6 DY hDY
  have hcount := grtCountAux m hA hI hA1 hI1 Λ hdisc D hD η₁ DY hDY h6
  have hFmeas : MeasurableSet (grtTube m Λ η₁ DY) := grtTube_measurable m hA hI Λ hdisc η₁ DY
  have hmain := Work.Mostow.volH_le_card_mul_of_ae_count (1 + m) hA hI Λ hdisc hD hFmeas
    (Work.Mostow.geodPtCard m Λ) hcount
  rw [grtTube_measure m hA hI hA1 hI1 Λ hdisc η₁ DY] at hmain
  rw [← grtU_eq m hA hI hA1 hI1 Λ η₁] at hmain
  calc Submission.Mostow.volH 1 DY * (MeasureTheory.volume : MeasureTheory.Measure (Submission.Mostow.E m))
        (Submission.Mostow.nrmC 1 m '' Work.Mostow.margRegion m Λ η₁)
      = Submission.Mostow.volH 1 DY * (MeasureTheory.volume : MeasureTheory.Measure (Submission.Mostow.E m))
        (grtU m Λ η₁) := by rw [← grtU_eq m hA hI hA1 hI1 Λ η₁]
    _ ≤ (Work.Mostow.geodPtCard m Λ : ENNReal) * Submission.Mostow.volH (1 + m) D := hmain
    _ = ENNReal.ofReal 1 * (Work.Mostow.geodPtCard m Λ : ENNReal) *
        Submission.Mostow.volH (1 + m) D := by rw [ENNReal.ofReal_one, one_mul]

end
end Work.Mostow
