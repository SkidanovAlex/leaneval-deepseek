import Mathlib
import Submission.Work.EKLProd.prodFlowerFam_exists

/-!
# `prodFlowerFam_exists` with a prescribed lower bound on the radius

The construction of `Work.EKLProd.prodFlowerFam_exists` produces a product-box flower family
`F` whose radius `F.R` is the one selected by `exists_prodBox_radius` (at the entry bound
`C₀ + 2`, where `C₀` bounds the inverses of `V 2`).  Nothing in the construction is specific
to that choice: any `R ≥ 1` with `V (C₀ + 2) ∩ H ⊆ prodBox T U R` works, and `prodBox` is
monotone in the radius.  Hence we may *prescribe* the radius: for every `R₀ ≥ 1` there is a
family with `F.R ≥ R₀`.  This is the form the C5b tower identity needs (the box must be large
enough for the alignment step `alignT`/`alignU`).

The proof below repeats the assembly of `Work.EKLProd.prodFlowerFam_exists` verbatim, except
that the radius returned by `exists_prodBox_radius` is enlarged to `R = max R₁ R₀`.
-/

open MeasureTheory Topology Filter
open scoped Pointwise ENNReal

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

noncomputable section

namespace Work.EKLRelProduct

open Work.EKLContract
open Work.EKLProd

/-- The product box is monotone in the radius. -/
theorem prodBox_mono {T U : Subgroup SL3} {ε ε' : ℝ} (h : ε ≤ ε') :
    Work.EKLProd.prodBox T U ε ⊆ Work.EKLProd.prodBox T U ε' := by
  rintro g ⟨a, ha, b, hb, rfl⟩
  exact ⟨a, ⟨fun i j => lt_of_lt_of_le (ha.1 i j) h, ha.2⟩,
    b, ⟨fun i j => lt_of_lt_of_le (hb.1 i j) h, hb.2⟩, rfl⟩

theorem prodFlowerFam_exists_rad (hX3 : Work.EKLContract.P_X3) {H T U : Subgroup Work.EKLContract.SL3} (hH : Work.EKLContract.IsHoro H) (hT : Work.EKLContract.IsHoro T) (hU : Work.EKLContract.IsHoro U) (hTH : T ≤ H) (hUH : U ≤ H) (hnorm : ∀ g ∈ T, ∀ u ∈ U, g * u * g⁻¹ ∈ U) (hcop : ∀ h ∈ H, ∃ g ∈ T, ∃ u ∈ U, h = g * u) (hdisj : ∀ g ∈ T, g ∈ U → g = 1) {μ : MeasureTheory.Measure Work.EKLContract.X3} [MeasureTheory.IsProbabilityMeasure μ] (hA : Work.EKLContract.IsAInvariant μ) (R₀ : ℝ) (hR₀ : 1 ≤ R₀) : ∃ F : Work.EKLProd.ProdFlowerFam H T U μ, R₀ ≤ F.R := by
  classical
  haveI : PolishSpace X3 := hX3.2.1
  have hHc : IsClosed (H : Set SL3) := hH.1
  have hTc : IsClosed (T : Set SL3) := hT.1
  have hUc : IsClosed (U : Set SL3) := hU.1
  -- (1) the radius and the cross-section scale
  obtain ⟨C₀, hC₀⟩ := Work.EKLProd.inv_entries_bound 2 (by norm_num)
  obtain ⟨R₁, hR₁1, hR₁subV⟩ := exists_prodBox_radius hTH hUH hnorm hcop hdisj hHc hTc hUc (C₀ + 2)
  set R : ℝ := max R₁ R₀ with hRdef
  have hR₀R : R₀ ≤ R := by rw [hRdef]; exact le_max_right _ _
  have hR1 : 1 ≤ R := le_trans hR₀ hR₀R
  have hRsubV : ∀ h : SL3, h ∈ (H : Set SL3) → h ∈ V (C₀ + 2) →
      h ∈ Work.EKLProd.prodBox T U R :=
    fun h hh hhV => prodBox_mono (by rw [hRdef]; exact le_max_left R₁ R₀) (hR₁subV h hh hhV)
  obtain ⟨C₁, hC₁⟩ := prodBox_inv_mul_entries_bound (T := T) (U := U) (ε := R) (by linarith)
  set ρ : ℝ := max (C₁ + 1) 3 with hρdef
  have hρ : 2 < ρ := by rw [hρdef]; exact lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hC₁ρ : C₁ + 1 ≤ ρ := by rw [hρdef]; exact le_max_left _ _
  have hblock : ∀ g ∈ prodBox T U R, ∀ g' ∈ prodBox T U R, g'⁻¹ * g ∈ Work.EKLComp.Ucl H ρ := by
    intro g hg g' hg'
    refine mem_Ucl_of_entries_le (C := C₁) (ρ := ρ)
      (H.mul_mem (H.inv_mem (prodBox_subset_H hTH hUH hg')) (prodBox_subset_H hTH hUH hg)) ?_ ?_
    · intro i j
      exact hC₁ g hg g' hg' i j
    · exact hC₁ρ
  have hsub : ∀ t ∈ Work.EKLComp.Ucl H 1, t⁻¹ ∈ prodBox T U R := by
    intro t ht
    refine hRsubV t⁻¹ (H.inv_mem ht.1) ?_
    refine mem_V_of_entries_le (C := C₀) (b := C₀ + 2) ?_ ?_
    · intro i j
      exact hC₀ t (Ucl_one_subset_V_two ht) i j
    · linarith
  -- (2) almost every point has a free `H`-orbit and only positive-measure neighbourhoods
  have hfree_ae : ∀ᵐ x ∂μ, x ∈ FreeOrbit H := by
    filter_upwards [Work.EKLC7.ae_free_orbit_of_horo μ hA H hH] with x hx
    intro h₁ h₁H h₂ h₂H heq
    have hfix : (h₂⁻¹ * h₁) • x = x := by rw [mul_smul, heq, inv_smul_smul]
    have hone : h₂⁻¹ * h₁ = 1 := hx _ (H.mul_mem (H.inv_mem h₂H) h₁H) hfix
    calc h₁ = h₂ * (h₂⁻¹ * h₁) := (mul_inv_cancel_left h₂ h₁).symm
      _ = h₂ := by rw [hone, mul_one]
  have hpos_ae : ∀ᵐ x ∂μ, ∀ s : Set X3, IsOpen s → x ∈ s → 0 < μ s :=
    Work.EKLC7.ae_isOpen_pos (μ := μ)
  set Gd : Set X3 := FreeOrbit H ∩ {x | ∀ s : Set X3, IsOpen s → x ∈ s → 0 < μ s} with hGddef
  have hGdcompl : μ Gdᶜ = 0 := by
    have h1 : ∀ᵐ x ∂μ, x ∈ Gd := by
      filter_upwards [hfree_ae, hpos_ae] with x hx1 hx2
      exact ⟨hx1, hx2⟩
    rw [MeasureTheory.ae_iff] at h1
    convert h1 using 2
    all_goals (ext a; simp)
  have hGdne : Gd.Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro hempty
    have h := hGdcompl
    rw [hempty, Set.compl_empty] at h
    rw [measure_univ] at h
    exact one_ne_zero h
  have hFmeas : MeasurableSet (FreeOrbit H) := by
    have h : FreeOrbit H = {x : X3 | ∀ u ∈ H, u • x = x → u = 1} := by
      ext x
      exact freeOrbit_iff_stab
    rw [h]
    exact Work.EKLRelCross.freeSet_borel hHc
  -- (3) the local flowers
  obtain ⟨basis, hbasis⟩ := TopologicalSpace.exists_seq_basis (α := X3)
  have hloc : ∀ x : {x : X3 // x ∈ Gd}, ∃ (Fl : BoxFlowerFam1 H T U μ R) (O : Set X3),
      IsOpen O ∧ (x : X3) ∈ O ∧ O ∩ FreeOrbit H ⊆ Fl.G :=
    fun x => boxFlower_local_exists hX3 hTH hUH hnorm hcop hdisj hHc hTc hUc hR1 hρ hblock hsub μ
      x.1 x.2.1 (fun s hs hxs => x.2.2 s hs hxs) hfree_ae
  choose Fl Ol hOlopen hxOl hGOl using hloc
  let xg : X3 := Classical.choose hGdne
  have hxg : xg ∈ Gd := Classical.choose_spec hGdne
  let ι : Set ℕ := {n | 0 < μ (basis n) ∧ ∃ x : {x : X3 // x ∈ Gd}, basis n ⊆ Ol x}
  have hchoice : ∀ n, n ∈ ι → ∃ x : {x : X3 // x ∈ Gd}, basis n ⊆ Ol x := fun n hn => hn.2
  let FF : ℕ → BoxFlowerFam1 H T U μ R := fun j =>
    if h : (Nat.unpair j).1 ∈ ι then Fl (Classical.choose (hchoice _ h)) else Fl ⟨xg, hxg⟩
  let GG : ℕ → Set X3 := fun j =>
    if h : (Nat.unpair j).1 ∈ ι then basis (Nat.unpair j).1 ∩ FreeOrbit H else ∅
  have hGG_pos : ∀ j, GG j = (if h : (Nat.unpair j).1 ∈ ι then
      basis (Nat.unpair j).1 ∩ FreeOrbit H else ∅) := fun j => rfl
  have hFF_pos : ∀ j, FF j = (if h : (Nat.unpair j).1 ∈ ι then
      Fl (Classical.choose (hchoice _ h)) else Fl ⟨xg, hxg⟩) := fun j => rfl
  -- the fields of the family
  have hmeasG : ∀ n, MeasurableSet (GG n) := by
    intro n
    rw [hGG_pos n]
    by_cases h : (Nat.unpair n).1 ∈ ι
    · rw [dif_pos h]
      exact (hbasis.isOpen (Set.mem_range_self _)).measurableSet.inter hFmeas
    · rw [dif_neg h]
      exact MeasurableSet.empty
  have hGZ : ∀ n, GG n ⊆ (FF n).Z := by
    intro n
    rw [hGG_pos n, hFF_pos n]
    by_cases h : (Nat.unpair n).1 ∈ ι
    · rw [dif_pos h, dif_pos h]
      exact Set.Subset.trans (Set.Subset.trans
        (Set.inter_subset_inter (Classical.choose_spec (hchoice _ h)) (subset_refl _))
        (hGOl (Classical.choose (hchoice _ h)))) (Fl (Classical.choose (hchoice _ h))).GZ
    · rw [dif_neg h, dif_neg h]
      exact Set.empty_subset _
  have hZpos : ∀ n, μ ((FF n).Z) ≠ 0 := by
    intro n
    rw [hFF_pos n]
    by_cases h : (Nat.unpair n).1 ∈ ι
    · rw [dif_pos h]
      exact (Fl (Classical.choose (hchoice _ h))).Zpos
    · rw [dif_neg h]
      exact (Fl ⟨xg, hxg⟩).Zpos
  have hcover : μ (⋃ n, GG n)ᶜ = 0 := by
    have hmem : ∀ᵐ y ∂μ, y ∈ ⋃ n, GG n := by
      filter_upwards [hfree_ae, hpos_ae] with y hyfree hypos
      have hyG : y ∈ Gd := ⟨hyfree, hypos⟩
      have hyO : y ∈ Ol ⟨y, hyG⟩ := hxOl ⟨y, hyG⟩
      obtain ⟨v, hv, hyv, hvsub⟩ :=
        hbasis.exists_subset_of_mem_open hyO (hOlopen ⟨y, hyG⟩)
      obtain ⟨n, rfl⟩ := hv
      have hposn : 0 < μ (basis n) := hypos _ (hbasis.isOpen (Set.mem_range_self n)) hyv
      have hn : n ∈ ι := ⟨hposn, ⟨⟨y, hyG⟩, hvsub⟩⟩
      refine Set.mem_iUnion.mpr ⟨Nat.pair n 0, ?_⟩
      rw [hGG_pos (Nat.pair n 0), Nat.unpair_pair, dif_pos hn]
      exact ⟨hyv, hyfree⟩
    rw [MeasureTheory.ae_iff] at hmem
    convert hmem using 2
    all_goals (ext a; simp)
  refine ⟨ProdFlowerFam.mk R hR1 (fun n => (FF n).Z) GG (fun n => (FF n).mH)
      (fun n => (FF n).mT) (fun n => (FF n).mU) (fun n => (FF n).co)
      hmeasG hGZ hZpos hcover
      (fun n => (FF n).plaqH) (fun n => (FF n).plaqT) (fun n => (FF n).plaqU)
      (fun n => (FF n).alignT) (fun n => (FF n).alignU)
      (fun n => (FF n).meas_co) (fun n => (FF n).co_mem)
      (fun n => (FF n).freeZ) (fun n => (FF n).co_smul)
      (fun n => (FF n).shapeH) (fun n => (FF n).shapeT) (fun n => (FF n).shapeU)
      (fun n => (FF n).meas_tp) (fun n => (FF n).meas_up), ?_⟩
  · exact hR₀R
end Work.EKLRelProduct
