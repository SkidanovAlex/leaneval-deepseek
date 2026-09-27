import Mathlib
import Submission.Work.EKLProd.BoxFlowerLocal

/-!
# The product-box flower at a free point, with unit plaque coordinates on the base

This is `Work.EKLProd.boxFlower_local_exists` strengthened by the conjunct

`∀ x ∈ F.G, ∃ t ∈ Ucl H 1, F.co x = t⁻¹`,

i.e. the plaque coordinate of every point of the base of the local flower is the inverse of a
*unit* displacement of `H`.  The proof re-runs the construction of
`Submission/Work/EKLProd/BoxFlowerLocal.lean` verbatim (all the supporting lemmas are imported
from that module) and adds, at the end, the argument of `ProdFlowerPLAN.md` / the plan of
`prodFlowerFam_exists_small`: for `y ∈ G` the cross-section property gives the unique
`t ∈ Ucl H 1` with `t • y ∈ C`; since `hsub` puts `t⁻¹` in `prodBox T U R` and the coordinates of
the flower give `co y • (ψ y).2.2 = y = t⁻¹ • (t • y)`, the uniqueness part of the cross-section
property (`hcross` applied to `c = (ψ y).2.2 ∈ C` and the displacement `t * co y ∈ Ucl H ρ`)
forces `t * co y = 1`, hence `co y = t⁻¹`.

This is the local input of the strengthened countable assembly
`Work.EKLProd.prodFlowerFam_exists_small`; the conjunct `co x = t⁻¹` with `t` in the *unit* ball is
what makes the shapes of the assembled flowers grow with the radius, see
`Work.EKLProd.prodBox_div_subset_shape`.
-/

open MeasureTheory Topology Filter
open scoped Pointwise ENNReal

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

noncomputable section

namespace Work.EKLProd

open Work.EKLContract

theorem boxFlower_local_exists_small (hX3 : Work.EKLContract.P_X3) {H T U : Subgroup Work.EKLContract.SL3}
    (hTH : T ≤ H) (hUH : U ≤ H)
    (hnorm : ∀ g ∈ T, ∀ u ∈ U, g * u * g⁻¹ ∈ U)
    (hcop : ∀ h ∈ H, ∃ g ∈ T, ∃ u ∈ U, h = g * u)
    (hdisj : ∀ g ∈ T, g ∈ U → g = 1)
    (hHc : IsClosed (H : Set Work.EKLContract.SL3)) (hTc : IsClosed (T : Set Work.EKLContract.SL3))
    (hUc : IsClosed (U : Set Work.EKLContract.SL3))
    {R ρ : ℝ} (hR : 1 ≤ R) (hρ : 2 < ρ)
    (hblock : ∀ g ∈ Work.EKLProd.prodBox T U R, ∀ g' ∈ Work.EKLProd.prodBox T U R,
      g'⁻¹ * g ∈ Work.EKLComp.Ucl H ρ)
    (hsub : ∀ t ∈ Work.EKLComp.Ucl H 1, t⁻¹ ∈ Work.EKLProd.prodBox T U R)
    (μ : MeasureTheory.Measure Work.EKLContract.X3) [MeasureTheory.IsProbabilityMeasure μ]
    (x₀ : Work.EKLContract.X3) (hfree : x₀ ∈ Work.EKLProd.FreeOrbit H)
    (hposx : ∀ s : Set Work.EKLContract.X3, IsOpen s → x₀ ∈ s → 0 < μ s)
    (hfree_ae : ∀ᵐ x ∂μ, x ∈ Work.EKLProd.FreeOrbit H) :
    ∃ (F : Work.EKLProd.BoxFlowerFam1 H T U μ R) (O : Set Work.EKLContract.X3), IsOpen O ∧ x₀ ∈ O ∧
      O ∩ Work.EKLProd.FreeOrbit H ⊆ F.G ∧
      ∀ x ∈ F.G, ∃ t ∈ Work.EKLComp.Ucl H 1, F.co x = t⁻¹ := by
  classical
  haveI : PolishSpace X3 := hX3.2.1
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  -- ## The cross-section of the `H`-flow at `x₀`, cut down to the free points
  obtain ⟨E, C₀, hEcl, hxE, hCE, hC₀meas, hret, hcross₀⟩ :=
    Work.EKLRelCross.pisa_crosssection hHc x₀ hρ hfree
  have hFmeas : MeasurableSet (FreeOrbit H) := by
    have h : FreeOrbit H = {x : X3 | ∀ u ∈ H, u • x = x → u = 1} := by
      ext x
      exact freeOrbit_iff_stab
    rw [h]
    exact Work.EKLRelCross.freeSet_borel hHc
  set C : Set X3 := C₀ ∩ FreeOrbit H with hCdef
  have hCmeas : MeasurableSet C := hC₀meas.inter hFmeas
  have hfreeC : ∀ c ∈ C, c ∈ FreeOrbit H := fun c hc => hc.2
  have hcross : ∀ c ∈ C, ∀ v ∈ Work.EKLComp.Ucl H ρ, v • c ∈ C → v = 1 :=
    fun c hc v hv hvc => hcross₀ c hc.1 v hv hvc.1
  -- ## A countable family of open sets separating the points of `X₃`
  obtain ⟨W, hWopen, hW0, hWsep⟩ := Work.EKLComp.flower_basis_sep
  have hWmeas : ∀ i, MeasurableSet (W i) := fun i => (hWopen i).measurableSet
  have hsepW : ∀ x ∈ C, ∀ y ∈ C, (∀ i, x ∈ W i ↔ y ∈ W i) → x = y :=
    fun x _ y _ h => hWsep x y h
  -- ## The transversal is nonempty; the measurable section of the parametrisation
  have hCne : C.Nonempty := by
    obtain ⟨t, ⟨ht, htx⟩, -⟩ := hret x₀ (interior_subset hxE)
    exact ⟨t • x₀, htx, freeOrbit_smul (H := H) hfree ht.1⟩
  have hne : (boxParam T U R C).Nonempty := by
    obtain ⟨c, hc⟩ := hCne
    exact ⟨(1, (1, c)), ⟨⟨(Work.EKLContract.Lemmas.V_open_one R hRpos).2, T.one_mem⟩,
      ⟨(Work.EKLContract.Lemmas.V_open_one R hRpos).2, U.one_mem⟩, hc⟩⟩
  obtain ⟨ψ, hψmeas, hψ⟩ := box_measSection hdisj hTc hUc hCmeas hblock hfreeC hcross hne
  -- ## The product box is the trace on `H` of an open set of `SL₃(ℝ)`
  obtain ⟨N, hNopen, hNH⟩ := exists_open_inter_prodBox hTH hUH hnorm hcop hdisj hHc hTc hUc (R := R)
  -- ## The flower data
  set Z : Set X3 := boxCollar T U R C with hZdef
  set mH : MeasurableSpace X3 := boxSigma T U R C W with hmHdef
  set co : X3 → SL3 := fun x => if x ∈ Z then (ψ x).1 * (ψ x).2.1 else 1 with hcodef
  -- the flower σ-algebra is Borel and countably generated, and `Z` is a generator
  have hZ_mH : MeasurableSet[mH] Z := by
    have hgen : boxCollar T U R C = boxCollar T U R (C ∩ W 0) := by rw [hW0, Set.inter_univ]
    rw [hZdef, hgen]
    exact MeasurableSpace.measurableSet_generateFrom (Set.mem_range_self 0)
  have hmH_borel : mH ≤ borel X3 := by
    rw [hmHdef]
    refine MeasurableSpace.generateFrom_le ?_
    rintro s ⟨i, rfl⟩
    exact boxCollar_borel hdisj hTc hUc hblock hfreeC hcross Set.inter_subset_left
      (hCmeas.inter (hWmeas i))
  have hZbore : @MeasurableSet X3 instMeasurableSpaceX3 Z := hmH_borel Z hZ_mH
  -- ## The parametrisation of a point of `Z`
  have hψZ : ∀ x ∈ Z, ψ x ∈ boxParam T U R C ∧ boxParamMap (ψ x) = x := by
    intro x hx
    have hx' : x ∈ boxCollar T U R C := hx
    rw [boxCollar] at hx'
    obtain ⟨p, hp, hpx⟩ := hx'
    have h1 : ψ (boxParamMap p) = p := hψ p hp
    have h2 : ψ x = p := by rw [← hpx]; exact h1
    exact ⟨h2.symm ▸ hp, by rw [h2]; exact hpx⟩
  have hunpack : ∀ x ∈ Z, (ψ x).1 ∈ V R ∩ (T : Set SL3) ∧
      (ψ x).2.1 ∈ V R ∩ (U : Set SL3) ∧ (ψ x).2.2 ∈ C := by
    intro x hx
    obtain ⟨h1, -⟩ := hψZ x hx
    exact ⟨h1.1, h1.2.1, h1.2.2⟩
  have hco_Z : ∀ x ∈ Z, co x = (ψ x).1 * (ψ x).2.1 := by
    intro x hx
    simp only [hcodef, if_pos hx]
  -- ## The atoms of the flower are the box plaques of the transversal points
  have key : ∀ x ∈ Z, ∃ c ∈ C, c ∈ FreeOrbit H ∧ atom mH x = boxCollar T U R {c} ∧
      co x ∈ prodBox T U R ∧ co x • c = x := by
    intro x hx
    have hxZ := hx
    obtain ⟨c, hcC, hxc, hatom⟩ := box_atom hblock hcross hW0 hsepW x hx
    obtain ⟨hp1, hp2, hpc⟩ := hunpack x hx
    have hmap : ((ψ x).1 * (ψ x).2.1) • (ψ x).2.2 = x := (hψZ x hx).2
    have hψbox : (ψ x).1 * (ψ x).2.1 ∈ prodBox T U R :=
      ⟨(ψ x).1, ⟨hp1.1, hp1.2⟩, (ψ x).2.1, ⟨hp2.1, hp2.2⟩, rfl⟩
    rw [boxCollar_eq, Set.mem_ofPred_eq] at hxc
    obtain ⟨g, hg, c', hc', hgc⟩ := hxc
    rw [Set.mem_singleton_iff] at hc'
    have hbc : (ψ x).2.2 = c :=
      boxCollar_point_unique (hbound := hblock) (hcross := hcross)
        (g := g) (g' := (ψ x).1 * (ψ x).2.1) (c := c) (c' := (ψ x).2.2)
        hg hψbox hcC hpc (by rw [hmap, ← hgc, hc'])
    refine ⟨c, hcC, hfreeC c hcC, ?_, ?_, ?_⟩
    · exact hatom
    · rw [hco_Z x hxZ]
      exact hψbox
    · rw [hco_Z x hxZ, ← hbc]
      exact hmap
  have hco_mem : ∀ x ∈ Z, co x ∈ prodBox T U R := by
    intro x hx
    obtain ⟨c, -, -, -, hmem, -⟩ := key x hx
    exact hmem
  have hcoH : ∀ x : X3, co x ∈ (H : Set SL3) := by
    intro x
    by_cases hx : x ∈ Z
    · exact prodBox_subset_H hTH hUH (hco_mem x hx)
    · simp only [hcodef, if_neg hx]
      exact H.one_mem
  -- ## The coordinate of a box translate of a transversal point
  have hco_of : ∀ (y : X3) (g : SL3) (c : X3), g ∈ prodBox T U R → c ∈ C → g • c = y →
      co y = g := by
    intro y g c hg hc hgc
    have hyZ : y ∈ Z := by
      rw [hZdef, boxCollar_eq, Set.mem_ofPred_eq]
      exact ⟨g, hg, c, hc, hgc⟩
    obtain ⟨hψp, hψmap⟩ := hψZ y hyZ
    have hψmap' : ((ψ y).1 * (ψ y).2.1) • (ψ y).2.2 = y := hψmap
    obtain ⟨hp1, hp2, hpc⟩ := hunpack y hyZ
    have htype : (ψ y).1 * (ψ y).2.1 ∈ prodBox T U R :=
      ⟨(ψ y).1, ⟨hp1.1, hp1.2⟩, (ψ y).2.1, ⟨hp2.1, hp2.2⟩, rfl⟩
    have hcc : (ψ y).2.2 = c :=
      boxCollar_point_unique (hbound := hblock) (hcross := hcross)
        (g := g) (g' := (ψ y).1 * (ψ y).2.1) (c := c) (c' := (ψ y).2.2)
        hg htype hc hpc (by rw [hψmap']; exact hgc.symm)
    have hgg : (ψ y).1 * (ψ y).2.1 = g := by
      have h1 : ((ψ y).1 * (ψ y).2.1) • (ψ y).2.2 = g • (ψ y).2.2 := by
        rw [hψmap', hcc]
        exact hgc.symm
      exact hfreeC (ψ y).2.2 hpc _ (prodBox_subset_H hTH hUH htype) g
        (prodBox_subset_H hTH hUH hg) h1
    rw [hco_Z y hyZ, hgg]
  -- ## The coordinate is multiplicative along the `H`-action
  have hco_smul : ∀ x ∈ Z, ∀ h ∈ H, h • x ∈ atom mH x → co (h • x) = h * co x := by
    intro x hx h hh hhat
    obtain ⟨c, hcC, hcfree, hatom, hmem, hmul⟩ := key x hx
    have hhat' : h • x ∈ boxCollar T U R {c} := by rw [← hatom]; exact hhat
    rw [boxCollar_eq, Set.mem_ofPred_eq] at hhat'
    obtain ⟨g', hg', c', hc', hgc'⟩ := hhat'
    rw [Set.mem_singleton_iff] at hc'
    have hthis : h • x = g' • c := by rw [hc'] at hgc'; exact hgc'.symm
    have h1 : (h * co x) • c = g' • c := by rw [mul_smul, hmul]; exact hthis
    have h2 : h * co x = g' :=
      hfreeC c hcC (h * co x) (H.mul_mem hh (hcoH x)) g' (prodBox_subset_H hTH hUH hg') h1
    exact hco_of (h • x) (h * co x) c (by rw [h2]; exact hg') hcC (by rw [mul_smul, hmul])
  -- ## Measurability of the coordinate and of its two parts
  have hco_meas : @Measurable X3 SL3 instMeasurableSpaceX3 instMeasurableSpaceSL3 co := by
    rw [hcodef]
    exact Measurable.ite hZbore (hψmeas.fst.mul hψmeas.snd.fst) measurable_const
  have hmeas_parts : @Measurable X3 SL3 instMeasurableSpaceX3 instMeasurableSpaceSL3
        (fun x : X3 => hT T U (co x)) ∧
      @Measurable X3 SL3 instMeasurableSpaceX3 instMeasurableSpaceSL3
        (fun x : X3 => hU T U (co x)) :=
    measurable_hT_hU_comp hTH hUH hnorm hcop hdisj hHc hTc hUc hco_meas hcoH
  -- ## The strip algebras
  set mT : MeasurableSpace X3 :=
    mH ⊔ MeasurableSpace.comap (fun x : X3 => hU T U (co x)) (borel SL3) with hmTdef
  set mU : MeasurableSpace X3 :=
    mH ⊔ MeasurableSpace.comap (fun x : X3 => hT T U (co x)) (borel SL3) with hmUdef
  have hmH_le_mT : mH ≤ mT := le_sup_left
  have hmH_le_mU : mH ≤ mU := le_sup_left
  have hmT_borel : mT ≤ borel X3 := by
    rw [hmTdef]
    exact sup_le hmH_borel (Measurable.comap_le hmeas_parts.2)
  have hmU_borel : mU ≤ borel X3 := by
    rw [hmUdef]
    exact sup_le hmH_borel (Measurable.comap_le hmeas_parts.1)
  have hmT_cnt : ∃ b : Set (Set X3), b.Countable ∧ mT = MeasurableSpace.generateFrom b := by
    obtain ⟨basis, hbasis⟩ := exists_basis_sl3
    refine ⟨Set.range (fun i => boxCollar T U R (C ∩ W i)) ∪
      Set.range (fun n => (fun x : X3 => hU T U (co x)) ⁻¹' basis n),
      Set.Countable.union (Set.countable_range _) (Set.countable_range _), ?_⟩
    rw [hmTdef, hmHdef,
      show boxSigma T U R C W
        = MeasurableSpace.generateFrom (Set.range (fun i => boxCollar T U R (C ∩ W i))) from rfl,
      comap_borel_eq_gen hbasis (fun x : X3 => hU T U (co x)), generateFrom_union_sup]
  have hmU_cnt : ∃ b : Set (Set X3), b.Countable ∧ mU = MeasurableSpace.generateFrom b := by
    obtain ⟨basis, hbasis⟩ := exists_basis_sl3
    refine ⟨Set.range (fun i => boxCollar T U R (C ∩ W i)) ∪
      Set.range (fun n => (fun x : X3 => hT T U (co x)) ⁻¹' basis n),
      Set.Countable.union (Set.countable_range _) (Set.countable_range _), ?_⟩
    rw [hmUdef, hmHdef,
      show boxSigma T U R C W
        = MeasurableSpace.generateFrom (Set.range (fun i => boxCollar T U R (C ∩ W i))) from rfl,
      comap_borel_eq_gen hbasis (fun x : X3 => hT T U (co x)), generateFrom_union_sup]
  -- ## The atoms of the strip algebras
  have hatom_T : ∀ x ∈ Z, atom mT x =
      atom mH x ∩ {y : X3 | hU T U (co y) = hU T U (co x)} := by
    intro x hx
    rw [hmTdef, hmHdef,
      show boxSigma T U R C W
        = MeasurableSpace.generateFrom (Set.range (fun i => boxCollar T U R (C ∩ W i))) from rfl,
      atom_sup_comap]
  have hatom_U : ∀ x ∈ Z, atom mU x =
      atom mH x ∩ {y : X3 | hT T U (co y) = hT T U (co x)} := by
    intro x hx
    rw [hmUdef, hmHdef,
      show boxSigma T U R C W
        = MeasurableSpace.generateFrom (Set.range (fun i => boxCollar T U R (C ∩ W i))) from rfl,
      atom_sup_comap]
  -- ## The shapes
  have hshapeH : ∀ x ∈ Z, shape mH H x = {g : SL3 | g ∈ H ∧ g * co x ∈ prodBox T U R} := by
    intro x hx
    obtain ⟨c, hcC, -, hatom, hmem, hmul⟩ := key x hx
    rw [hmHdef]
    exact box_shape_eq hTH hUH hfreeC hcC hmem hmul hatom
  have hshapeT : ∀ x ∈ Z, shape mT T x = {g : SL3 | g ∈ T ∧ g * co x ∈ prodBox T U R} := by
    intro x hx
    obtain ⟨c, hcC, -, hatom, hmem, hmul⟩ := key x hx
    ext g
    constructor
    · rintro ⟨hgT, hgat⟩
      rw [hatom_T x hx, hatom] at hgat
      obtain ⟨hgat1, hgat2⟩ := hgat
      rw [boxCollar_eq, Set.mem_ofPred_eq] at hgat1
      obtain ⟨g', hg', c', hc', hgc'⟩ := hgat1
      rw [Set.mem_singleton_iff] at hc'
      have hgoal : g * co x = g' := by
        have h1 : (g * co x) • c = g' • c := by rw [mul_smul, hmul, ← hgc', hc']
        exact hfreeC c hcC _ (H.mul_mem (hTH hgT) (hcoH x)) g' (prodBox_subset_H hTH hUH hg') h1
      exact ⟨hgT, by rw [hgoal]; exact hg'⟩
    · rintro ⟨hgT, hgbox⟩
      refine ⟨hgT, ?_⟩
      rw [hatom_T x hx, hatom]
      have hmem1 : g • x ∈ boxCollar T U R {c} := by
        rw [boxCollar_eq, Set.mem_ofPred_eq]
        exact ⟨g * co x, hgbox, c, rfl, by rw [mul_smul, hmul]⟩
      have hcoe : co (g • x) = g * co x :=
        hco_of (g • x) (g * co x) c hgbox hcC (by rw [mul_smul, hmul])
      refine ⟨hmem1, ?_⟩
      show hU T U (co (g • x)) = hU T U (co x)
      rw [hcoe, hU_mul_T_left hTH hcop hdisj hgT (hcoH x)]
  have hshapeU : ∀ x ∈ Z, shape mU U x = {g : SL3 | g ∈ U ∧ g * co x ∈ prodBox T U R} := by
    intro x hx
    obtain ⟨c, hcC, -, hatom, hmem, hmul⟩ := key x hx
    ext g
    constructor
    · rintro ⟨hgU, hgat⟩
      rw [hatom_U x hx, hatom] at hgat
      obtain ⟨hgat1, hgat2⟩ := hgat
      rw [boxCollar_eq, Set.mem_ofPred_eq] at hgat1
      obtain ⟨g', hg', c', hc', hgc'⟩ := hgat1
      rw [Set.mem_singleton_iff] at hc'
      have hgoal : g * co x = g' := by
        have h1 : (g * co x) • c = g' • c := by rw [mul_smul, hmul, ← hgc', hc']
        exact hfreeC c hcC _ (H.mul_mem (hUH hgU) (hcoH x)) g' (prodBox_subset_H hTH hUH hg') h1
      exact ⟨hgU, by rw [hgoal]; exact hg'⟩
    · rintro ⟨hgU, hgbox⟩
      refine ⟨hgU, ?_⟩
      rw [hatom_U x hx, hatom]
      have hmem1 : g • x ∈ boxCollar T U R {c} := by
        rw [boxCollar_eq, Set.mem_ofPred_eq]
        exact ⟨g * co x, hgbox, c, rfl, by rw [mul_smul, hmul]⟩
      have hcoe : co (g • x) = g * co x :=
        hco_of (g • x) (g * co x) c hgbox hcC (by rw [mul_smul, hmul])
      refine ⟨hmem1, ?_⟩
      show hT T U (co (g • x)) = hT T U (co x)
      rw [hcoe, hT_mul_right_U hnorm hcop hdisj hUH hgU (hcoH x)]
  -- ## The shapes are traces of open sets and entrywise bounded
  have hshapeH_open : ∀ x ∈ Z, ∃ O : Set SL3, IsOpen O ∧ shape mH H x = O ∩ (H : Set SL3) := by
    intro x hx
    refine ⟨{g : SL3 | g * co x ∈ N}, ?_, ?_⟩
    · exact hNopen.preimage (continuous_id.mul continuous_const)
    · rw [hshapeH x hx]
      ext g
      constructor
      · rintro ⟨hgH, hgbox⟩
        refine ⟨?_, hgH⟩
        have hmemP : g * co x ∈ prodBox T U R := hgbox
        rw [← hNH] at hmemP
        exact hmemP.1
      · rintro ⟨hgN, hgH⟩
        refine ⟨hgH, ?_⟩
        have hmemN : g * co x ∈ N ∩ (H : Set SL3) := ⟨hgN, H.mul_mem hgH (hcoH x)⟩
        rwa [hNH] at hmemN
  have hshapeT_open : ∀ x ∈ Z, ∃ O : Set SL3, IsOpen O ∧ shape mT T x = O ∩ (T : Set SL3) := by
    intro x hx
    refine ⟨{g : SL3 | g * co x ∈ N}, ?_, ?_⟩
    · exact hNopen.preimage (continuous_id.mul continuous_const)
    · rw [hshapeT x hx]
      ext g
      constructor
      · rintro ⟨hgT, hgbox⟩
        refine ⟨?_, hgT⟩
        have hmemP : g * co x ∈ prodBox T U R := hgbox
        rw [← hNH] at hmemP
        exact hmemP.1
      · rintro ⟨hgN, hgT⟩
        refine ⟨hgT, ?_⟩
        have hmemN : g * co x ∈ N ∩ (H : Set SL3) := ⟨hgN, H.mul_mem (hTH hgT) (hcoH x)⟩
        rwa [hNH] at hmemN
  have hshapeU_open : ∀ x ∈ Z, ∃ O : Set SL3, IsOpen O ∧ shape mU U x = O ∩ (U : Set SL3) := by
    intro x hx
    refine ⟨{g : SL3 | g * co x ∈ N}, ?_, ?_⟩
    · exact hNopen.preimage (continuous_id.mul continuous_const)
    · rw [hshapeU x hx]
      ext g
      constructor
      · rintro ⟨hgU, hgbox⟩
        refine ⟨?_, hgU⟩
        have hmemP : g * co x ∈ prodBox T U R := hgbox
        rw [← hNH] at hmemP
        exact hmemP.1
      · rintro ⟨hgN, hgU⟩
        refine ⟨hgU, ?_⟩
        have hmemN : g * co x ∈ N ∩ (H : Set SL3) := ⟨hgN, H.mul_mem (hUH hgU) (hcoH x)⟩
        rwa [hNH] at hmemN
  have hshapeH_bdd : ∀ x ∈ Z, ∃ C : ℝ, ∀ g ∈ shape mH H x, ∀ i j : Fin 3, |g i j| ≤ C := by
    intro x hx
    refine ⟨3 * ((3 * (1 + R) ^ 2) * (3 * (2 * (1 + R) ^ 2) ^ 2)), ?_⟩
    intro g hg i j
    rw [hshapeH x hx] at hg
    obtain ⟨-, hgbox⟩ := hg
    have h1 : ∀ i j : Fin 3, |(g * co x) i j| ≤ 3 * (1 + R) ^ 2 := prodBox_entry_le hRpos hgbox
    have h2 : ∀ i j : Fin 3, |((co x)⁻¹) i j| ≤ 3 * (2 * (1 + R) ^ 2) ^ 2 :=
      prodBox_inv_entry_le hRpos (hco_mem x hx)
    have heq : g = (g * co x) * (co x)⁻¹ := by group
    rw [heq]
    exact abs_mul_entries_le (A := g * co x) (B := (co x)⁻¹)
      (b := 3 * (1 + R) ^ 2) (d := 3 * (2 * (1 + R) ^ 2) ^ 2)
      (by positivity) (by positivity) h1 h2 i j
  have hshapeT_bdd : ∀ x ∈ Z, ∃ C : ℝ, ∀ g ∈ shape mT T x, ∀ i j : Fin 3, |g i j| ≤ C := by
    intro x hx
    refine ⟨3 * ((3 * (1 + R) ^ 2) * (3 * (2 * (1 + R) ^ 2) ^ 2)), ?_⟩
    intro g hg i j
    rw [hshapeT x hx] at hg
    obtain ⟨-, hgbox⟩ := hg
    have h1 : ∀ i j : Fin 3, |(g * co x) i j| ≤ 3 * (1 + R) ^ 2 := prodBox_entry_le hRpos hgbox
    have h2 : ∀ i j : Fin 3, |((co x)⁻¹) i j| ≤ 3 * (2 * (1 + R) ^ 2) ^ 2 :=
      prodBox_inv_entry_le hRpos (hco_mem x hx)
    have heq : g = (g * co x) * (co x)⁻¹ := by group
    rw [heq]
    exact abs_mul_entries_le (A := g * co x) (B := (co x)⁻¹)
      (b := 3 * (1 + R) ^ 2) (d := 3 * (2 * (1 + R) ^ 2) ^ 2)
      (by positivity) (by positivity) h1 h2 i j
  have hshapeU_bdd : ∀ x ∈ Z, ∃ C : ℝ, ∀ g ∈ shape mU U x, ∀ i j : Fin 3, |g i j| ≤ C := by
    intro x hx
    refine ⟨3 * ((3 * (1 + R) ^ 2) * (3 * (2 * (1 + R) ^ 2) ^ 2)), ?_⟩
    intro g hg i j
    rw [hshapeU x hx] at hg
    obtain ⟨-, hgbox⟩ := hg
    have h1 : ∀ i j : Fin 3, |(g * co x) i j| ≤ 3 * (1 + R) ^ 2 := prodBox_entry_le hRpos hgbox
    have h2 : ∀ i j : Fin 3, |((co x)⁻¹) i j| ≤ 3 * (2 * (1 + R) ^ 2) ^ 2 :=
      prodBox_inv_entry_le hRpos (hco_mem x hx)
    have heq : g = (g * co x) * (co x)⁻¹ := by group
    rw [heq]
    exact abs_mul_entries_le (A := g * co x) (B := (co x)⁻¹)
      (b := 3 * (1 + R) ^ 2) (d := 3 * (2 * (1 + R) ^ 2) ^ 2)
      (by positivity) (by positivity) h1 h2 i j
  -- ## The three plaque algebras
  have hplaqH : IsPlaqueAlgebra H Z mH := by
    refine ⟨hmH_borel, ⟨Set.range (fun i => boxCollar T U R (C ∩ W i)), Set.countable_range _, rfl⟩,
      hZ_mH, ?_⟩
    intro x hx
    obtain ⟨c, hcC, hcfree, hatom, hmem, hmul⟩ := key x hx
    refine ⟨?_, ?_, hshapeH_open x hx, hshapeH_bdd x hx⟩
    · intro y hy
      rw [hatom] at hy
      rw [boxCollar_eq, Set.mem_ofPred_eq] at hy
      obtain ⟨g, hg, c', hc', hgc⟩ := hy
      rw [Set.mem_singleton_iff] at hc'
      rw [hc'] at hgc
      rw [hZdef, boxCollar_eq, Set.mem_ofPred_eq]
      exact ⟨g, hg, c, hcC, hgc⟩
    · intro y hy
      rw [hatom, boxCollar_eq, Set.mem_ofPred_eq] at hy
      obtain ⟨g, hg, c', hc', hgc⟩ := hy
      rw [Set.mem_singleton_iff] at hc'
      rw [hc'] at hgc
      refine ⟨g * (co x)⁻¹, H.mul_mem (prodBox_subset_H hTH hUH hg) (H.inv_mem (hcoH x)), ?_⟩
      calc (g * (co x)⁻¹) • x
          = (g * (co x)⁻¹) • (co x • c) := by rw [hmul]
        _ = (g * (co x)⁻¹ * co x) • c := by rw [← mul_smul]
        _ = g • c := by rw [show g * (co x)⁻¹ * co x = g from by group]
        _ = y := hgc
  have hplaqT : IsPlaqueAlgebra T Z mT := by
    refine ⟨hmT_borel, hmT_cnt, (MeasurableSpace.le_def.mp hmH_le_mT) Z hZ_mH, ?_⟩
    intro x hx
    obtain ⟨c, hcC, hcfree, hatom, hmem, hmul⟩ := key x hx
    obtain ⟨t₀, ht₀, u₀, hu₀, ht₀u₀⟩ := hmem
    have htu : hT T U (co x) = t₀ ∧ hU T U (co x) = u₀ :=
      mul_eq_mul_of_mem hdisj (hT_mem ⟨t₀, ht₀.2, u₀, hu₀.2, ht₀u₀.symm⟩) ht₀.2
        (hU_mem ⟨t₀, ht₀.2, u₀, hu₀.2, ht₀u₀.symm⟩) hu₀.2
        (by rw [hT_mul_hU ⟨t₀, ht₀.2, u₀, hu₀.2, ht₀u₀.symm⟩, ← ht₀u₀])
    have ht₀T : hT T U (co x) ∈ T := hT_mem ⟨t₀, ht₀.2, u₀, hu₀.2, ht₀u₀.symm⟩
    refine ⟨?_, ?_, hshapeT_open x hx, hshapeT_bdd x hx⟩
    · intro y hy
      have hy' : y ∈ atom mH x := atom_subset_of_le hmH_le_mT x hy
      rw [hatom] at hy'
      rw [boxCollar_eq, Set.mem_ofPred_eq] at hy'
      obtain ⟨g, hg, c', hc', hgc⟩ := hy'
      rw [Set.mem_singleton_iff] at hc'
      rw [hc'] at hgc
      rw [hZdef, boxCollar_eq, Set.mem_ofPred_eq]
      exact ⟨g, hg, c, hcC, hgc⟩
    · intro y hy
      rw [hatom_T x hx, hatom] at hy
      obtain ⟨hy1, hy2⟩ := hy
      rw [boxCollar_eq, Set.mem_ofPred_eq] at hy1
      obtain ⟨g, hg, c', hc', hgc⟩ := hy1
      rw [Set.mem_singleton_iff] at hc'
      rw [hc'] at hgc
      have hcoy : co y = g := hco_of y g c hg hcC hgc
      obtain ⟨t₁, ht₁, u₁, hu₁, ht₁u₁⟩ := hg
      have hgdec : hT T U g * hU T U g = g := hT_mul_hU ⟨t₁, ht₁.2, u₁, hu₁.2, ht₁u₁.symm⟩
      have hUg : hU T U g = hU T U (co x) := by rw [← hcoy, hy2]
      refine ⟨hT T U g * (hT T U (co x))⁻¹,
        T.mul_mem (hT_mem ⟨t₁, ht₁.2, u₁, hu₁.2, ht₁u₁.symm⟩) (T.inv_mem ht₀T), ?_⟩
      calc (hT T U g * (hT T U (co x))⁻¹) • x
          = (hT T U g * (hT T U (co x))⁻¹) • (co x • c) := by rw [hmul]
        _ = (hT T U g * (hT T U (co x))⁻¹ * (t₀ * u₀)) • c := by rw [← mul_smul, ← ht₀u₀]
        _ = (hT T U g * hU T U (co x)) • c := by
              rw [show hT T U g * (hT T U (co x))⁻¹ * (t₀ * u₀)
                    = hT T U g * hU T U (co x) from by rw [← htu.1, ← htu.2]; group]
        _ = (hT T U g * hU T U g) • c := by rw [hUg]
        _ = g • c := by rw [hgdec]
        _ = y := hgc
  have hplaqU : IsPlaqueAlgebra U Z mU := by
    refine ⟨hmU_borel, hmU_cnt, (MeasurableSpace.le_def.mp hmH_le_mU) Z hZ_mH, ?_⟩
    intro x hx
    obtain ⟨c, hcC, hcfree, hatom, hmem, hmul⟩ := key x hx
    obtain ⟨t₀, ht₀, u₀, hu₀, ht₀u₀⟩ := hmem
    have htu : hT T U (co x) = t₀ ∧ hU T U (co x) = u₀ :=
      mul_eq_mul_of_mem hdisj (hT_mem ⟨t₀, ht₀.2, u₀, hu₀.2, ht₀u₀.symm⟩) ht₀.2
        (hU_mem ⟨t₀, ht₀.2, u₀, hu₀.2, ht₀u₀.symm⟩) hu₀.2
        (by rw [hT_mul_hU ⟨t₀, ht₀.2, u₀, hu₀.2, ht₀u₀.symm⟩, ← ht₀u₀])
    have ht₀T : hT T U (co x) ∈ T := hT_mem ⟨t₀, ht₀.2, u₀, hu₀.2, ht₀u₀.symm⟩
    have hu₀U : hU T U (co x) ∈ U := hU_mem ⟨t₀, ht₀.2, u₀, hu₀.2, ht₀u₀.symm⟩
    refine ⟨?_, ?_, hshapeU_open x hx, hshapeU_bdd x hx⟩
    · intro y hy
      have hy' : y ∈ atom mH x := atom_subset_of_le hmH_le_mU x hy
      rw [hatom] at hy'
      rw [boxCollar_eq, Set.mem_ofPred_eq] at hy'
      obtain ⟨g, hg, c', hc', hgc⟩ := hy'
      rw [Set.mem_singleton_iff] at hc'
      rw [hc'] at hgc
      rw [hZdef, boxCollar_eq, Set.mem_ofPred_eq]
      exact ⟨g, hg, c, hcC, hgc⟩
    · intro y hy
      rw [hatom_U x hx, hatom] at hy
      obtain ⟨hy1, hy2⟩ := hy
      rw [boxCollar_eq, Set.mem_ofPred_eq] at hy1
      obtain ⟨g, hg, c', hc', hgc⟩ := hy1
      rw [Set.mem_singleton_iff] at hc'
      rw [hc'] at hgc
      have hcoy : co y = g := hco_of y g c hg hcC hgc
      obtain ⟨t₁, ht₁, u₁, hu₁, ht₁u₁⟩ := hg
      have hgdec : hT T U g * hU T U g = g := hT_mul_hU ⟨t₁, ht₁.2, u₁, hu₁.2, ht₁u₁.symm⟩
      have hu₁U : hU T U g ∈ U := hU_mem ⟨t₁, ht₁.2, u₁, hu₁.2, ht₁u₁.symm⟩
      have hTg : hT T U g = hT T U (co x) := by rw [← hcoy, hy2]
      refine ⟨hT T U (co x) * (hU T U g * (hU T U (co x))⁻¹) * (hT T U (co x))⁻¹,
        hnorm (hT T U (co x)) ht₀T (hU T U g * (hU T U (co x))⁻¹)
          (U.mul_mem hu₁U (U.inv_mem hu₀U)), ?_⟩
      calc (hT T U (co x) * (hU T U g * (hU T U (co x))⁻¹) * (hT T U (co x))⁻¹) • x
          = (hT T U (co x) * (hU T U g * (hU T U (co x))⁻¹) * (hT T U (co x))⁻¹)
              • (co x • c) := by rw [hmul]
        _ = (hT T U (co x) * (hU T U g * (hU T U (co x))⁻¹) * (hT T U (co x))⁻¹ * (t₀ * u₀))
              • c := by rw [← mul_smul, ← ht₀u₀]
        _ = (hT T U (co x) * hU T U g) • c := by
              rw [show hT T U (co x) * (hU T U g * (hU T U (co x))⁻¹) * (hT T U (co x))⁻¹
                    * (t₀ * u₀) = hT T U (co x) * hU T U g from by
                rw [← htu.1, ← htu.2]; group]
        _ = (hT T U g * hU T U g) • c := by rw [← hTg]
        _ = g • c := by rw [hgdec]
        _ = y := hgc
  -- ## Assemble
  have hGmeas : @MeasurableSet X3 instMeasurableSpaceX3 (interior E ∩ FreeOrbit H) :=
    measurableSet_inter_freeOrbit isOpen_interior hHc
  have hGZ : interior E ∩ FreeOrbit H ⊆ Z := by
    rintro x ⟨hxO, hxfree⟩
    obtain ⟨t, ⟨ht, htx⟩, -⟩ := hret x (interior_subset hxO)
    have hcC : t • x ∈ C := ⟨htx, freeOrbit_smul (H := H) hxfree ht.1⟩
    rw [hZdef, boxCollar_eq, Set.mem_ofPred_eq]
    exact ⟨t⁻¹, hsub t ht, t • x, hcC, inv_smul_smul t x⟩
  have hZpos : μ Z ≠ 0 := by
    have hcompl : μ (FreeOrbit H)ᶜ = 0 := by
      rw [MeasureTheory.ae_iff] at hfree_ae
      exact hfree_ae
    have hle : μ (interior E) ≤ μ (interior E ∩ FreeOrbit H) := by
      have h1 : interior E = (interior E ∩ FreeOrbit H) ∪ (interior E ∩ (FreeOrbit H)ᶜ) := by
        ext y
        constructor
        · intro hy
          by_cases h : y ∈ FreeOrbit H
          · exact Or.inl ⟨hy, h⟩
          · exact Or.inr ⟨hy, h⟩
        · rintro (⟨hy, -⟩ | ⟨hy, -⟩) <;> exact hy
      calc μ (interior E) = μ ((interior E ∩ FreeOrbit H) ∪ (interior E ∩ (FreeOrbit H)ᶜ)) := by
            conv_lhs => rw [h1]
        _ ≤ μ (interior E ∩ FreeOrbit H) + μ (interior E ∩ (FreeOrbit H)ᶜ) :=
            measure_union_le _ _
        _ = μ (interior E ∩ FreeOrbit H) := by
            rw [measure_mono_null Set.inter_subset_right hcompl, add_zero]
    exact ne_of_gt (lt_of_lt_of_le (lt_of_lt_of_le (hposx (interior E) isOpen_interior hxE)
      hle) (measure_mono hGZ))
  have hfreeZ : ∀ x ∈ Z, x ∈ FreeOrbit H := by
    intro x hx
    rw [hZdef, boxCollar_eq, Set.mem_ofPred_eq] at hx
    obtain ⟨g, hg, c, hc, hgc⟩ := hx
    rw [← hgc]
    exact freeOrbit_smul (H := H) (hfreeC c hc) (prodBox_subset_H hTH hUH hg)
  -- ## The plaque coordinate on the base is the inverse of a unit displacement
  have hExtra : ∀ x ∈ interior E ∩ FreeOrbit H, ∃ t ∈ Work.EKLComp.Ucl H 1, co x = t⁻¹ := by
    intro x hx
    obtain ⟨hxO, hxfree⟩ := hx
    have hxZ : x ∈ Z := hGZ ⟨hxO, hxfree⟩
    obtain ⟨t, ⟨htUcl, htxC⟩, -⟩ := hret x (interior_subset hxO)
    have hcoP : co x ∈ prodBox T U R := hco_mem x hxZ
    have htinvP : t⁻¹ ∈ prodBox T U R := hsub t htUcl
    have hψC : (ψ x).2.2 ∈ C := (hunpack x hxZ).2.2
    have hmap : co x • (ψ x).2.2 = x := by
      rw [hco_Z x hxZ]
      exact (hψZ x hxZ).2
    have hv : t * co x ∈ Work.EKLComp.Ucl H ρ := by
      simpa using hblock (co x) hcoP t⁻¹ htinvP
    have htxC' : t • x ∈ C := ⟨htxC, freeOrbit_smul (H := H) hxfree htUcl.1⟩
    have hone : t * co x = 1 :=
      hcross (ψ x).2.2 hψC (t * co x) hv (by rw [mul_smul, hmap]; exact htxC')
    exact ⟨t, htUcl, by
      calc co x = t⁻¹ * (t * co x) := by group
        _ = t⁻¹ := by rw [hone, mul_one]⟩
  refine ⟨?_, interior E, isOpen_interior, hxE, ?_, ?_⟩
  · exact { Z := Z
            G := interior E ∩ FreeOrbit H
            mH := mH
            mT := mT
            mU := mU
            co := co
            measG := hGmeas
            GZ := hGZ
            Zpos := hZpos
            plaqH := hplaqH
            plaqT := hplaqT
            plaqU := hplaqU
            alignT := hmH_le_mT
            alignU := hmH_le_mU
            meas_co := hco_meas
            co_mem := hco_mem
            freeZ := hfreeZ
            co_smul := hco_smul
            shapeH := hshapeH
            shapeT := hshapeT
            shapeU := hshapeU
            meas_tp := hmeas_parts.1
            meas_up := hmeas_parts.2 }
  · exact subset_refl _
  · exact hExtra

end Work.EKLProd
