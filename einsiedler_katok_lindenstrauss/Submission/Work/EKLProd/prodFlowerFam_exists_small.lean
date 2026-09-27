import Mathlib
import Submission.Work.EKLProd.ProdFlowerDefs
import Submission.Work.EKLProd.BoxFlowerDefs
import Submission.Work.EKLProd.BoxFlowerLocal
import Submission.Work.EKLProd.boxFlower_local_exists_small
import Submission.Work.EKLProd.prodFlowerFam_exists
import Submission.Work.EKLRelProduct.prodFlowerFam_exists_rad
import Submission.Work.EKLRelCross.pisa_crosssection
import Submission.Work.EKLContract.Defs


open MeasureTheory Topology Filter
open scoped Pointwise ENNReal

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

noncomputable section

namespace Work.EKLProd

open Work.EKLContract

/-- **Existence of a product-box flower family of prescribed radius whose plaque coordinates on the base lie in the closed unit ball.**

This is `Work.EKLRelProduct.prodFlowerFam_exists_rad` strengthened by the conjunct
`∀ n x ∈ F.G n, ∃ t ∈ Ucl H 1, F.co n x = t⁻¹`.  It is what makes the shapes of the flowers grow
with the radius: for `x ∈ G n` the shape is `prodBox T U R · (co n x)⁻¹`, so `co n x = t⁻¹` with
`t` in the *unit* ball gives `prodBox T U (R/C) ⊆ shape (mH n) H x` for a universal `C`
(see `Work.EKLProd.prodBox_div_subset_shape`).

PLAN.  Both `Work.EKLProd.boxFlower_local_exists` and the assembly of
`Work.EKLRelProduct.prodFlowerFam_exists_rad` must be *re-run* with the extra conjunct, since
neither statement exposes the cross-section `C` of `Work.EKLRelCross.pisa_crosssection` nor its
witness.  Copy the body of `Submission/Work/EKLProd/BoxFlowerLocal.lean` (the data `Z`, `mH`,
`mT`, `mU`, `co` from `pisa_crosssection` + `box_measSection` + `boxSigma` + `box_atom` +
`box_shape_eq` + `exists_open_inter_prodBox` + `boxCollar_borel` and the three
`IsPlaqueAlgebra` proofs), and add before the final `refine`: for `y ∈ G = interior E ∩
FreeOrbit H`, `hret` gives the unique `t ∈ Ucl H 1` with `t • y ∈ C`; then `y = t⁻¹ • (t • y)`
with `t • y ∈ C` and `t⁻¹ ∈ prodBox T U R` (hypothesis `hsub`), so `Work.EKLProd.boxCollar_point_unique`
applied to the two representations `co y • (ψ y).2.2 = y` and `t⁻¹ • (t • y) = y` (both group
elements in `prodBox T U R`, both base points in `C`) gives `co y = t⁻¹`.  Then copy the assembly
of `Submission/Work/EKLRelProduct/prodFlowerFam_exists_rad.lean` carrying the extra conjunct
through (the assembled base is `basis n ∩ FreeOrbit H`, contained in `interior E` of the local
flower registered at that index, so the strengthened local statement applies). -/
theorem prodFlowerFam_exists_small (hX3 : Work.EKLContract.P_X3) {H T U : Subgroup Work.EKLContract.SL3} (hH : Work.EKLContract.IsHoro H) (hT : Work.EKLContract.IsHoro T) (hU : Work.EKLContract.IsHoro U) (hTH : T ≤ H) (hUH : U ≤ H) (hnorm : ∀ g ∈ T, ∀ u ∈ U, g * u * g⁻¹ ∈ U) (hcop : ∀ h ∈ H, ∃ g ∈ T, ∃ u ∈ U, h = g * u) (hdisj : ∀ g ∈ T, g ∈ U → g = 1) {μ : MeasureTheory.Measure Work.EKLContract.X3} [MeasureTheory.IsProbabilityMeasure μ] (hA : Work.EKLContract.IsAInvariant μ) (R₀ : ℝ) (hR₀ : 1 ≤ R₀) : ∃ F : Work.EKLProd.ProdFlowerFam H T U μ, R₀ ≤ F.R ∧ ∀ n : ℕ, ∀ x ∈ F.G n, ∃ t ∈ Work.EKLComp.Ucl H 1, F.co n x = t⁻¹ := by
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
    fun h hh hhV => Work.EKLRelProduct.prodBox_mono (by rw [hRdef]; exact le_max_left R₁ R₀)
      (hR₁subV h hh hhV)
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
  -- (3) the local flowers (strengthened: coordinates on the base lie in the inverse unit ball)
  obtain ⟨basis, hbasis⟩ := TopologicalSpace.exists_seq_basis (α := X3)
  have hloc : ∀ x : {x : X3 // x ∈ Gd}, ∃ (Fl : BoxFlowerFam1 H T U μ R) (O : Set X3),
      IsOpen O ∧ (x : X3) ∈ O ∧ O ∩ FreeOrbit H ⊆ Fl.G ∧
      ∀ y ∈ Fl.G, ∃ t ∈ Work.EKLComp.Ucl H 1, Fl.co y = t⁻¹ :=
    fun x => boxFlower_local_exists_small hX3 hTH hUH hnorm hcop hdisj hHc hTc hUc hR1 hρ hblock hsub μ
      x.1 x.2.1 (fun s hs hxs => x.2.2 s hs hxs) hfree_ae
  choose Fl Ol hOl using hloc
  have hOlopen : ∀ x, IsOpen (Ol x) := fun x => (hOl x).1
  have hxOl : ∀ x, (x : X3) ∈ Ol x := fun x => (hOl x).2.1
  have hGOl : ∀ x, Ol x ∩ FreeOrbit H ⊆ (Fl x).G := fun x => (hOl x).2.2.1
  have hFlco : ∀ x, ∀ y ∈ (Fl x).G, ∃ t ∈ Work.EKLComp.Ucl H 1, (Fl x).co y = t⁻¹ :=
    fun x => (hOl x).2.2.2
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
  have hGGG : ∀ n, GG n ⊆ (FF n).G := by
    intro n
    rw [hGG_pos n, hFF_pos n]
    by_cases h : (Nat.unpair n).1 ∈ ι
    · rw [dif_pos h, dif_pos h]
      exact Set.Subset.trans
        (Set.inter_subset_inter (Classical.choose_spec (hchoice _ h)) (subset_refl _))
        (hGOl (Classical.choose (hchoice _ h)))
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
      (fun n => (FF n).meas_tp) (fun n => (FF n).meas_up), hR₀R, ?_⟩
  intro n x hxG
  have hxG' : x ∈ GG n := hxG
  show ∃ t ∈ Work.EKLComp.Ucl H 1, (FF n).co x = t⁻¹
  rw [hFF_pos n]
  by_cases h : (Nat.unpair n).1 ∈ ι
  · rw [dif_pos h]
    refine hFlco (Classical.choose (hchoice _ h)) x ?_
    have h2 : x ∈ (FF n).G := hGGG n hxG'
    rw [hFF_pos n, dif_pos h] at h2
    exact h2
  · rw [dif_neg h]
    refine hFlco ⟨xg, hxg⟩ x ?_
    have h2 : x ∈ (FF n).G := hGGG n hxG'
    rw [hFF_pos n, dif_neg h] at h2
    exact h2

end Work.EKLProd
