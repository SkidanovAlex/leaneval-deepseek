import Mathlib
import Submission.Work.BW.kcb_lat_defs
import Submission.Work.BW.sieg2KernelDefs
import Submission.Work.BW.sieg2_PhiE_surjective
import Submission.Work.BW.sieg2_intLatE_basis
import Submission.Work.BW.TV.covolume_intLatE
import Submission.Work.BW.TV.mem_kerLatE_iff
import Submission.Work.BW.TV.kerLattice_zbasis
import Submission.Work.BW.sieg2_kerLatE_aux
import Submission.Work.BW.exists_zbasis_kerLattice
import Submission.Work.BW.sieg2_Phi_img_discrete
import Submission.Work.BW.sic_kcbEquiv_PhiE
import Submission.Work.BW.sic_kcbEquiv_intLatE
import Submission.Work.BW.TV.mem_intLatE_iff_latL

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 1000000

namespace Work.BW

open NumberField
open scoped Classical

noncomputable section

variable {F : Type*} [Field F] [NumberField F]

/-! ## The integral lattice `intLatE F N` -/

/-- `intLatE F N` is discrete (it is the `ℤ`-span of an `ℝ`-basis). -/
theorem kcb_intLatE_discrete (N : ℕ) : DiscreteTopology ↥(intLatE F N) :=
  Work.BW.TV.discreteTopology_intLatE (F := F) N

/-- `intLatE F N` spans the coordinate model over `ℝ`. -/
theorem kcb_intLatE_span_top (N : ℕ) :
    Submodule.span ℝ (intLatE F N : Set (kcbE F N)) = ⊤ := by
  obtain ⟨b, hb⟩ := sieg2_intLatE_basis (F := F) N
  rw [← hb]
  exact ZSpan.span_top b

/-! ## Dimensions -/

/-- `Module.finrank ℝ (kcbE F N) = N · [F : ℚ]`. -/
theorem kcbE_finrank (N : ℕ) : Module.finrank ℝ (kcbE F N) = N * Module.finrank ℚ F := by
  rw [LinearEquiv.finrank_eq (kcbEquiv F N), Module.finrank_pi_fintype]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    NumberField.mixedEmbedding.euclidean.finrank]
  simp

/-- `Module.finrank ℝ (ker (PhiE a)) = (N - M) · [F : ℚ]` for `F`-linearly independent rows. -/
theorem ker_PhiE_finrank {M N : ℕ} (a : Fin M → Fin N → F) (hli : LinearIndependent F a) :
    Module.finrank ℝ ↥(LinearMap.ker (PhiE a)) = Module.finrank ℚ F * (N - M) := by
  have hsurj := sieg2_PhiE_surjective (F := F) a hli
  have h := LinearMap.finrank_range_add_finrank_ker (PhiE a)
  rw [LinearMap.range_eq_top.mpr hsurj] at h
  rw [LinearEquiv.finrank_eq (Submodule.topEquiv (R := ℝ) (M := kcbE F M)), kcbE_finrank,
    kcbE_finrank] at h
  have hd : Module.finrank ℝ ↥(LinearMap.ker (PhiE a))
      = N * Module.finrank ℚ F - M * Module.finrank ℚ F := by
    rw [← h]
    omega
  rw [hd, ← Nat.sub_mul, mul_comm]

/-! ## The kernel lattice in the mixed coordinates -/

/-- The mixed coordinates of `toEMap F N z` are `z`. -/
theorem kcb_ofLp_toEMap {N : ℕ} (z : CoordSpace F N) :
    (fun j q => (Work.BW.TV.toEMap F N z).ofLp (j, q)) = z :=
  Work.BW.TV.ofLpMap_toEMap (F := F) N z

/-- `toEMap` carries the kernel lattice onto the kernel lattice of the coordinate model. -/
theorem map_toEMap_kerLattice {M N : ℕ} (a : Fin M → Fin N → F) :
    Submodule.map (Work.BW.TV.toEMap F N) (kerLattice (F := F) a) = kerLatE a := by
  refine Submodule.ext (fun y => ?_)
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine (Work.BW.TV.mem_kerLatE_iff (F := F) a (Work.BW.TV.toEMap F N z)).mpr ?_
    rwa [kcb_ofLp_toEMap]
  · intro hy
    refine ⟨Work.BW.TV.ofLpMap F N y, ?_, Work.BW.TV.toEMap_ofLpMap F N y⟩
    exact (Work.BW.TV.mem_kerLatE_iff (F := F) a y).mp hy

/-- The kernel lattice `kerLatE a` has a `ℤ`-basis of cardinality `(N - M) · [F : ℚ]`. -/
theorem exists_zbasis_kerLatE {M N : ℕ} (hMN : M < N) (a : Fin M → Fin N → F)
    (hind : LinearIndependent F a) :
    ∃ w : Fin (Module.finrank ℚ F * (N - M)) → kcbE F N,
      LinearIndependent ℤ w ∧ Submodule.span ℤ (Set.range w) = kerLatE a := by
  obtain ⟨v, hvli, hvspan⟩ := exists_zbasis_kerLattice (F := F) hMN a hind
  have hinj : Function.Injective (Work.BW.TV.toEMap F N : CoordSpace F N → kcbE F N) := by
    intro x y h
    have h' := congrArg (Work.BW.TV.ofLpMap F N) h
    rwa [Work.BW.TV.ofLpMap_toEMap, Work.BW.TV.ofLpMap_toEMap] at h'
  refine ⟨fun i => Work.BW.TV.toEMap F N (v i), ?_, ?_⟩
  · exact hvli.map' (Work.BW.TV.toEMap F N) (LinearMap.ker_eq_bot.mpr hinj)
  · have hrange : Set.range (fun i => Work.BW.TV.toEMap F N (v i))
        = (Work.BW.TV.toEMap F N) '' Set.range v := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨v i, ⟨i, rfl⟩, rfl⟩
      · rintro ⟨w, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, rfl⟩
    rw [hrange, ← Submodule.map_span, hvspan, map_toEMap_kerLattice]

/-! ## Discreteness of the kernel lattices -/

/-- The kernel lattice `kerLatE a` is discrete (it is contained in `intLatE F N`). -/
theorem kcb_kerLatE_discrete {M N : ℕ} (a : Fin M → Fin N → F) :
    DiscreteTopology ↥(kerLatE (F := F) a) := by
  haveI := kcb_intLatE_discrete (F := F) N
  have hsub : ∀ x ∈ kerLatE (F := F) a, x ∈ intLatE F N := fun x hx =>
    (Submodule.mem_inf.mp hx).1
  let g : ↥(kerLatE (F := F) a) → kcbE F N := fun x => x.1
  have hgm : ∀ x, g x ∈ intLatE F N := fun x => hsub _ x.2
  have hgc : Continuous g := continuous_subtype_val
  refine DiscreteTopology.of_continuous_injective
    (show Continuous (fun x : ↥(kerLatE (F := F) a) =>
      (⟨g x, hgm x⟩ : ↥(intLatE F N))) from Continuous.subtype_mk hgc hgm) ?_
  intro x y h
  have h1 : (x : kcbE F N) = (y : kcbE F N) :=
    congrArg (fun z : ↥(intLatE F N) => (z : kcbE F N)) h
  exact Subtype.ext h1

/-- Membership in the kernel lattice, viewed inside the kernel of `PhiE a`. -/
theorem kcb_mem_kerLatK_iff {M N : ℕ} (a : Fin M → Fin N → F)
    (x : ↥(LinearMap.ker (PhiE a))) :
    x ∈ kerLatK (F := F) a ↔ ((x : ↥(LinearMap.ker (PhiE a))) : kcbE F N) ∈ kerLatE a := by
  rw [kerLatK, Submodule.mem_comap]
  rfl

/-- The kernel lattice, viewed inside the kernel of `PhiE a`, is discrete. -/
theorem kcb_kerLatK_discrete {M N : ℕ} (a : Fin M → Fin N → F) :
    DiscreteTopology ↥(kerLatK (F := F) a) := by
  haveI := kcb_kerLatE_discrete (F := F) a
  let g : ↥(kerLatK (F := F) a) → kcbE F N := fun x => x.1.1
  have hgm : ∀ x, g x ∈ kerLatE (F := F) a := fun x =>
    (kcb_mem_kerLatK_iff (F := F) a x.1).mp x.2
  have hgc : Continuous g := continuous_subtype_val.comp continuous_subtype_val
  refine DiscreteTopology.of_continuous_injective
    (show Continuous (fun x : ↥(kerLatK (F := F) a) =>
      (⟨g x, hgm x⟩ : ↥(kerLatE (F := F) a))) from Continuous.subtype_mk hgc hgm) ?_
  intro x y h
  have h1 : g x = g y := congrArg (fun z : ↥(kerLatE (F := F) a) => (z : kcbE F N)) h
  have h2 : (x.1 : ↥(LinearMap.ker (PhiE a))) = y.1 := Subtype.ext h1
  exact Subtype.ext h2

/-! ## The kernel lattice spans the kernel -/

/-- A point of `kerLatE a` lies in the kernel of `PhiE a`. -/
theorem kcb_kerLatE_le_ker {M N : ℕ} (a : Fin M → Fin N → F) :
    ∀ y ∈ kerLatE (F := F) a, y ∈ LinearMap.ker (PhiE a) := fun y hy =>
  (Submodule.restrictScalars_mem ℤ (LinearMap.ker (PhiE a)) y).mp
    (Submodule.mem_inf.mp hy).2

/-- The kernel lattice `kerLatE a` spans `ker (PhiE a)` over `ℝ`. -/
theorem span_kerLatE_eq_ker {M N : ℕ} (hMN : M < N) (a : Fin M → Fin N → F)
    (hind : LinearIndependent F a) :
    Submodule.span ℝ (kerLatE a : Set (kcbE F N)) = LinearMap.ker (PhiE a) := by
  obtain ⟨w, hwli, hspanw⟩ := exists_zbasis_kerLatE (F := F) hMN a hind
  have hdisc : DiscreteTopology ↥(Submodule.span ℤ (Set.range w)) := by
    rw [hspanw]; exact kcb_kerLatE_discrete (F := F) a
  have hZ : Set.finrank ℤ (Set.range w) = Module.finrank ℚ F * (N - M) := by
    rw [show Set.finrank ℤ (Set.range w) = Module.finrank ℤ ↥(Submodule.span ℤ (Set.range w))
        from rfl, finrank_span_eq_card hwli, Fintype.card_fin]
  have hR : Set.finrank ℝ (Set.range w) = Module.finrank ℚ F * (N - M) :=
    (Real.finrank_eq_int_finrank_of_discrete (s := Set.range w) hdisc).trans hZ
  have hwmem : ∀ i, w i ∈ kerLatE (F := F) a := fun i => by
    rw [← hspanw]; exact Submodule.subset_span ⟨i, rfl⟩
  have hle : Submodule.span ℝ (Set.range w) ≤ LinearMap.ker (PhiE a) := by
    rw [Submodule.span_le]
    rintro y ⟨i, rfl⟩
    exact kcb_kerLatE_le_ker (F := F) a _ (hwmem i)
  have heq : Submodule.span ℝ (Set.range w) = LinearMap.ker (PhiE a) := by
    refine Submodule.eq_of_le_of_finrank_eq hle ?_
    rw [show Module.finrank ℝ ↥(Submodule.span ℝ (Set.range w)) = Set.finrank ℝ (Set.range w)
        from rfl, hR, ker_PhiE_finrank (F := F) a hind]
  refine le_antisymm ?_ ?_
  · rw [Submodule.span_le]
    intro y hy
    exact kcb_kerLatE_le_ker (F := F) a y hy
  · rw [← heq]
    exact Submodule.span_mono (by rintro y ⟨i, rfl⟩; exact hwmem i)

/-- The kernel lattice, viewed inside the kernel of `PhiE a`, spans it over `ℝ`. -/
theorem kcb_span_kerLatK_top {M N : ℕ} (hMN : M < N) (a : Fin M → Fin N → F)
    (hind : LinearIndependent F a) :
    Submodule.span ℝ (kerLatK (F := F) a :
      Set ↥(LinearMap.ker (PhiE a))) = ⊤ := by
  have himg : (Submodule.subtype (LinearMap.ker (PhiE a))) ''
      (kerLatK (F := F) a : Set ↥(LinearMap.ker (PhiE a))) =
      (kerLatE a : Set (kcbE F N)) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (kcb_mem_kerLatK_iff (F := F) a x).mp hx
    · intro hy
      refine ⟨⟨y, kcb_kerLatE_le_ker (F := F) a y hy⟩, ?_, rfl⟩
      exact (kcb_mem_kerLatK_iff (F := F) a
        ⟨y, kcb_kerLatE_le_ker (F := F) a y hy⟩).mpr hy
  have h := span_kerLatE_eq_ker (F := F) hMN a hind
  rw [← himg, ← Submodule.map_span] at h
  have h' : Submodule.map (Submodule.subtype (LinearMap.ker (PhiE a)))
      (Submodule.span ℝ (kerLatK (F := F) a : Set ↥(LinearMap.ker (PhiE a)))) =
      Submodule.map (Submodule.subtype (LinearMap.ker (PhiE a))) ⊤ := by
    rw [h, Submodule.map_subtype_top]
  exact Submodule.map_injective_of_injective
    (f := Submodule.subtype (LinearMap.ker (PhiE a))) (fun x y hxy => Subtype.ext hxy) h'

/-! ## The image lattice `imgLatE a` -/

/-- The coordinate equivalence `kcbEquiv F M` carries `imgLatE a` onto the image of the product
integral lattice `PLat F N` under the mixed model `Phi a`. -/
theorem kcb_imgLat_map_eq {M N : ℕ} (a : Fin M → Fin N → F) :
    Submodule.map ((kcbEquiv F M).toLinearMap.restrictScalars ℤ) (imgLatE (F := F) a) =
      Submodule.map ((Phi a).restrictScalars ℤ) (PLat F N) := by
  refine Submodule.ext (fun y => ?_)
  rw [Submodule.mem_map, Submodule.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [imgLatE] at hx
    obtain ⟨x', hx', hxy'⟩ := Submodule.mem_map.mp hx
    have hxy'' : (PhiE (F := F) a) x' = x := hxy'
    refine ⟨(kcbEquiv F N) x', ?_, ?_⟩
    · have hmem : (kcbEquiv F N) x' ∈ ⇑(kcbEquiv F N) '' (intLatE F N : Set (kcbE F N)) :=
        ⟨x', hx', rfl⟩
      rw [sic_kcbEquiv_intLatE] at hmem
      exact hmem
    · have h1 : (Phi a) ((kcbEquiv F N) x') = (kcbEquiv F M) x := by
        rw [← sic_kcbEquiv_PhiE (F := F) a x', hxy'']
      change (Phi a) ((kcbEquiv F N) x') = (kcbEquiv F M) x
      exact h1
  · rintro ⟨z, hz, rfl⟩
    have hz' : z ∈ ⇑(kcbEquiv F N) '' (intLatE F N : Set (kcbE F N)) := by
      rw [sic_kcbEquiv_intLatE]; exact hz
    obtain ⟨x', hx', rfl⟩ := hz'
    refine ⟨(PhiE a) x', ?_, ?_⟩
    · rw [imgLatE]; exact Submodule.mem_map.mpr ⟨x', hx', rfl⟩
    · change (kcbEquiv F M) ((PhiE a) x') = (Phi a) ((kcbEquiv F N) x')
      exact sic_kcbEquiv_PhiE (F := F) a x'

/-- The image lattice `imgLatE a` is discrete. -/
theorem kcb_imgLatE_discrete {M N : ℕ} (a : Fin M → Fin N → F) :
    DiscreteTopology ↥(imgLatE (F := F) a) := by
  set fM := (kcbEquiv F M).toLinearMap.restrictScalars ℤ with hfMdef
  haveI : DiscreteTopology ↥(Submodule.map fM (imgLatE (F := F) a)) := by
    rw [kcb_imgLat_map_eq (F := F) a]; exact sieg2_Phi_img_discrete (F := F) a
  have hcomap : ZLattice.comap ℝ (Submodule.map fM (imgLatE (F := F) a))
      (kcbEquiv F M).toLinearMap = imgLatE (F := F) a := by
    refine Submodule.ext (fun y => ?_)
    change y ∈ (Submodule.map fM (imgLatE (F := F) a)).comap
      ((kcbEquiv F M).toLinearMap.restrictScalars ℤ) ↔ y ∈ imgLatE (F := F) a
    rw [Submodule.mem_comap]
    constructor
    · intro hy
      obtain ⟨x, hx, hxy⟩ := Submodule.mem_map.mp hy
      rw [hfMdef, LinearMap.restrictScalars_apply] at hxy
      exact (kcbEquiv F M).injective hxy ▸ hx
    · intro hy
      exact Submodule.mem_map.mpr ⟨y, hy, rfl⟩
  have hd := ZLattice.comap_discreteTopology ℝ (Submodule.map fM (imgLatE (F := F) a))
    (e := (kcbEquiv F M).toLinearMap)
    (kcbEquiv F M).toLinearMap.continuous_of_finiteDimensional
    (fun x y h => (kcbEquiv F M).injective h)
  rwa [hcomap] at hd

/-- The image lattice `imgLatE a` spans the coordinate model `kcbE F M` over `ℝ`. -/
theorem kcb_span_imgLatE_top {M N : ℕ} (a : Fin M → Fin N → F)
    (hli : LinearIndependent F a) :
    Submodule.span ℝ (imgLatE (F := F) a : Set (kcbE F M)) = ⊤ := by
  have hsurj := sieg2_PhiE_surjective (F := F) a hli
  have himg : (imgLatE (F := F) a : Set (kcbE F M)) =
      (PhiE a) '' (intLatE F N : Set (kcbE F N)) := by
    rw [imgLatE, Submodule.map_coe]
    rfl
  rw [himg, ← Submodule.map_span, kcb_intLatE_span_top (F := F) N, Submodule.map_top,
    LinearMap.range_eq_top.mpr hsurj]

/-! ## The statement -/

theorem kcb_lattice_instances {F : Type*} [Field F] [NumberField F] {M N : ℕ} (hMN : M < N)
    (a : Fin M → Fin N → F) (hli : LinearIndependent F a) :
    DiscreteTopology ↥(Work.BW.intLatE F N) ∧
    Submodule.span ℝ (Work.BW.intLatE F N :
      Set (EuclideanSpace ℝ (Fin N × NumberField.mixedEmbedding.index F))) = ⊤ ∧
    DiscreteTopology ↥(Work.BW.kerLatK (F := F) a) ∧
    Submodule.span ℝ (Work.BW.kerLatK (F := F) a :
      Set ↥(LinearMap.ker (Work.BW.PhiE (F := F) a))) = ⊤ ∧
    DiscreteTopology ↥(Work.BW.imgLatE (F := F) a) ∧
    Submodule.span ℝ (Work.BW.imgLatE (F := F) a :
      Set (EuclideanSpace ℝ (Fin M × NumberField.mixedEmbedding.index F))) = ⊤ := by
  exact ⟨kcb_intLatE_discrete (F := F) N, kcb_intLatE_span_top (F := F) N,
    kcb_kerLatK_discrete (F := F) a, kcb_span_kerLatK_top (F := F) hMN a hli,
    kcb_imgLatE_discrete (F := F) a, kcb_span_imgLatE_top (F := F) a hli⟩

end

end Work.BW
