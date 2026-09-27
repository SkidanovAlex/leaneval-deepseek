import Mathlib
import Submission.Work.EKLProd.ProdFlowerDefs
import Submission.Work.EKLProd.BoxFlowerDefs
import Submission.Work.EKLProd.BoxFlowerLocal
import Submission.Work.EKLProd.exists_prodBox_radius
import Submission.Work.EKLProd.prodBox_inv_mul_entries_bound
import Submission.Work.EKLRelCross.pisa_crosssection
import Submission.Work.EKLC7.AeFreeStab
import Submission.Work.EKLC7.FlowerFamExists
import Submission.Work.EKLComp.flower_piece_borel
import Submission.Work.EKLComp.flower_small_cover
import Submission.Work.EKLComp.flower_basis_sep

/-!
# Existence of a family of product-box flowers (the geometric input of `P_Product`)

`Work.EKLProd.ProdFlowerFam H T U μ` is the datum consumed by the tower identity of C5b.  This
module constructs it from the local flowers of `Submission/Work/EKLProd/BoxFlowerLocal.lean` by
the countable-basis argument of Pisa Cor. 6.15:

* choose a radius `R ≥ 1` with `V C₀ ∩ H ⊆ prodBox T U R` (`exists_prodBox_radius`), where `C₀`
  is an entry bound for inverses of elements of `V 2`, so that `(Ucl H 1)⁻¹ ⊆ prodBox T U R`;
* choose the cross-section scale `ρ > 2` with `prodBox T U R · (prodBox T U R)⁻¹ ⊆ Ucl H ρ`
  (`prodBox_inv_mul_entries_bound`), which is what the cross-section property of
  `pisa_crosssection` requires;
* at every point of a conull set (free `H`-orbit and all open neighbourhoods of positive measure)
  build a local flower `BoxFlowerFam1 H T U μ R` with an open neighbourhood `O` whose free points
  lie in the base (`boxFlower_local_exists`);
* register, for every basis element `basis n` lying inside one of these neighbourhoods, the
  corresponding flower (padded with one fixed flower on the remaining indices, so that every
  member of the family has a domain of positive measure).

The bases of the registered flowers, intersected with the (conull) free locus, cover `μ`-almost
everything: for a.e. `y` the basis element `basis n ∋ y` of the countable basis is contained in
the neighbourhood of the local flower at `y`.
-/

open MeasureTheory Topology Filter
open scoped Pointwise ENNReal

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

noncomputable section

namespace Work.EKLProd

open Work.EKLContract

theorem prodFlowerFam_exists (hX3 : Work.EKLContract.P_X3) {H T U : Subgroup Work.EKLContract.SL3} (hH : Work.EKLContract.IsHoro H) (hT : Work.EKLContract.IsHoro T) (hU : Work.EKLContract.IsHoro U) (hTH : T ≤ H) (hUH : U ≤ H) (hnorm : ∀ g ∈ T, ∀ u ∈ U, g * u * g⁻¹ ∈ U) (hcop : ∀ h ∈ H, ∃ g ∈ T, ∃ u ∈ U, h = g * u) (hdisj : ∀ g ∈ T, g ∈ U → g = 1) {μ : MeasureTheory.Measure Work.EKLContract.X3} [MeasureTheory.IsProbabilityMeasure μ] (hA : Work.EKLContract.IsAInvariant μ) : Nonempty (Work.EKLProd.ProdFlowerFam H T U μ) := by
  classical
  haveI : PolishSpace X3 := hX3.2.1
  have hHc : IsClosed (H : Set SL3) := hH.1
  have hTc : IsClosed (T : Set SL3) := hT.1
  have hUc : IsClosed (U : Set SL3) := hU.1
  -- (1) the radius and the cross-section scale
  obtain ⟨C₀, hC₀⟩ := Work.EKLProd.inv_entries_bound 2 (by norm_num)
  obtain ⟨R, hR1, hRsubV⟩ := exists_prodBox_radius hTH hUH hnorm hcop hdisj hHc hTc hUc (C₀ + 2)
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
  have FFam : ProdFlowerFam H T U μ :=
    { R := R, one_le_R := hR1, Z := fun n => (FF n).Z, G := GG,
      mH := fun n => (FF n).mH, mT := fun n => (FF n).mT, mU := fun n => (FF n).mU,
      co := fun n => (FF n).co,
      measG := hmeasG, GZ := hGZ, Zpos := hZpos, cover := hcover,
      plaqH := fun n => (FF n).plaqH, plaqT := fun n => (FF n).plaqT,
      plaqU := fun n => (FF n).plaqU,
      alignT := fun n => (FF n).alignT, alignU := fun n => (FF n).alignU,
      meas_co := fun n => (FF n).meas_co, co_mem := fun n => (FF n).co_mem,
      freeZ := fun n => (FF n).freeZ, co_smul := fun n => (FF n).co_smul,
      shapeH := fun n => (FF n).shapeH, shapeT := fun n => (FF n).shapeT,
      shapeU := fun n => (FF n).shapeU, meas_tp := fun n => (FF n).meas_tp,
      meas_up := fun n => (FF n).meas_up }
  exact ⟨FFam⟩

end Work.EKLProd
