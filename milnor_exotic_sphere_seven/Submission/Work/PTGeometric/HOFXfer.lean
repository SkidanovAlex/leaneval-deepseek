import Mathlib
import Submission.Work.PTGeometric.HOFDefs
import Submission.Work.PTGeometric.HOFExc

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Topology

namespace Work.PTGeometric.HOF

noncomputable section

/-!
# Chart transfers of local homology classes

For a partial homeomorphism `e : W ⇀ ℝ^N` (a chart), a point `w ∈ e.source` and a class at `e w`,
we build the transferred class at `w`, and prove the facts needed for the target
`Work.PTGeometric.exists_halfOrientationFamily_of_det_pos`:

* the transfer `chartTr` is surjective, hence carries a generator to a generator;
* for two charts at a common point, the transfers of the standard Euclidean generators agree
  whenever the transition has positive determinant (`chartTr_change`, in `HOFChart.lean`) — the
  analytic input there is the germ lemma `Work.PTGeometric.HOF.eucFam_germ_ball`.
-/

variable {W : TopCat} {N : ℕ}

/-- The excluded set `{x}` of a point of the ambient space, seen inside an open subset `U ∋ x`. -/
abbrev punctSet (X : TopCat) (U : Set X) (x : X) : Set ↥U := trace U ({x} : Set X)

/-! ## Excision, in the `RelHmapOf` normal form -/

/-- **The localisation `H_N(U, U∖K) → H_N(X, X∖K)` out of an open subset**, in the `RelHmapOf`
normal form (the same linear map as `excMap`). -/
def excM (X : TopCat) (N : ℕ) (U : Set X) (K : Set X) :
    Work.Orient.RelH (TopCat.of ↥U) N (trace U K) →ₗ[ℤ] Work.Orient.RelH X N K :=
  RelHmapOf N (Work.Cohomology.subtypeIncl X U) (trace U K) K (fun z hz => hz)

/-- `excM` is `excMap`. -/
theorem excM_eq_excMap (X : TopCat) (N : ℕ) (U : Set X) (K : Set X) :
    excM X N U K = excMap X N U K := (excMap_eq_relHmapOf X N U K).symm

/-- The localisation out of an open subset is injective (excision). -/
theorem excM_injective (X : TopCat) (N : ℕ) (U : Set X) (hU : IsOpen U) (K : Set X)
    (hKU : K ⊆ U) (hKc : IsClosed K) : Function.Injective (excM X N U K) := by
  rw [excM_eq_excMap]
  haveI := isIso_excMap X N U hU K hKU hKc
  exact (ConcreteCategory.bijective_of_isIso
    (HomologicalComplex.homologyMap (Work.Cohomology.relChainsMap X U (Kᶜ)) N)).1

/-- **Excision as a linear equivalence**, in the `excM` normal form. -/
noncomputable def excE (X : TopCat) (N : ℕ) (U : Set X) (hU : IsOpen U) (K : Set X)
    (hKU : K ⊆ U) (hKc : IsClosed K) :
    Work.Orient.RelH (TopCat.of ↥U) N (trace U K) ≃ₗ[ℤ] Work.Orient.RelH X N K :=
  LinearEquiv.ofBijective (excM X N U K) (by
    rw [excM_eq_excMap]
    haveI := isIso_excMap X N U hU K hKU hKc
    exact ConcreteCategory.bijective_of_isIso
      (HomologicalComplex.homologyMap (Work.Cohomology.relChainsMap X U (Kᶜ)) N))

/-- The defining property of `excE`. -/
theorem excE_apply (X : TopCat) (N : ℕ) (U : Set X) (hU : IsOpen U) (K : Set X)
    (hKU : K ⊆ U) (hKc : IsClosed K) (v : Work.Orient.RelH (TopCat.of ↥U) N (trace U K)) :
    excE X N U hU K hKU hKc v = excM X N U K v := rfl

/-- The composite of `excE` with its inverse. -/
theorem excM_excE_symm (X : TopCat) (N : ℕ) (U : Set X) (hU : IsOpen U) (K : Set X)
    (hKU : K ⊆ U) (hKc : IsClosed K) (v : Work.Orient.RelH X N K) :
    excM X N U K ((excE X N U hU K hKU hKc).symm v) = v := by
  have h := LinearEquiv.apply_symm_apply (excE X N U hU K hKU hKc) v
  rwa [excE_apply] at h

/-- The inverse of `excE` is a section of the localisation. -/
theorem excE_symm_excM (X : TopCat) (N : ℕ) (U : Set X) (hU : IsOpen U) (K : Set X)
    (hKU : K ⊆ U) (hKc : IsClosed K) (v : Work.Orient.RelH (TopCat.of ↥U) N (trace U K)) :
    (excE X N U hU K hKU hKc).symm (excM X N U K v) = v :=
  LinearEquiv.symm_apply_apply _ v

/-- **Excision, in the "one point excluded" form.** -/
noncomputable def punctIso (X : TopCat) (N : ℕ) (U : Set X) (hU : IsOpen U) (x : X) (hx : x ∈ U)
    (hxc : IsClosed ({x} : Set X)) :
    Work.Orient.RelH (TopCat.of ↥U) N (punctSet X U x) ≃ₗ[ℤ]
      Work.Orient.RelH X N ({x} : Set X) :=
  excE X N U hU ({x} : Set X) (Set.singleton_subset_iff.mpr hx) hxc

/-- The defining property of `punctIso`. -/
theorem punctIso_apply (X : TopCat) (N : ℕ) (U : Set X) (hU : IsOpen U) (x : X) (hx : x ∈ U)
    (hxc : IsClosed ({x} : Set X)) (v : Work.Orient.RelH (TopCat.of ↥U) N (punctSet X U x)) :
    punctIso X N U hU x hx hxc v = excM X N U ({x} : Set X) v := rfl

/-- The inverse of `punctIso` is a section of the localisation. -/
theorem punctIso_symm_apply (X : TopCat) (N : ℕ) (U : Set X) (hU : IsOpen U) (x : X)
    (hx : x ∈ U) (hxc : IsClosed ({x} : Set X))
    (v : Work.Orient.RelH (TopCat.of ↥U) N (punctSet X U x)) :
    (punctIso X N U hU x hx hxc).symm (excM X N U ({x} : Set X) v) = v :=
  LinearEquiv.symm_apply_apply _ v

/-- The composite of `punctIso` with the localisation. -/
theorem punctIso_excM_symm (X : TopCat) (N : ℕ) (U : Set X) (hU : IsOpen U) (x : X)
    (hx : x ∈ U) (hxc : IsClosed ({x} : Set X)) (v : Work.Orient.RelH X N ({x} : Set X)) :
    excM X N U ({x} : Set X) ((punctIso X N U hU x hx hxc).symm v) = v := by
  have h : punctIso X N U hU x hx hxc ((punctIso X N U hU x hx hxc).symm v) = v :=
    LinearEquiv.apply_symm_apply _ v
  rwa [punctIso_apply] at h

/-! ## The inclusion of one subset in another -/

/-- The inclusion of a subset in a larger one, as a continuous map of the subtypes. -/
def inclSub {X : Type} [TopologicalSpace X] (B U : Set X) (h : B ⊆ U) :
    TopCat.of ↥B ⟶ TopCat.of ↥U :=
  TopCat.ofHom ⟨fun z => ⟨(z : X), h z.2⟩, by
    exact Continuous.subtype_mk continuous_subtype_val (fun z => h z.2)⟩

/-- The inclusion, followed by the inclusion of the bigger set, is the inclusion of the smaller. -/
theorem inclSub_comp_subtypeIncl {X : TopCat} {B U : Set X} (h : B ⊆ U) :
    inclSub B U h ≫ Work.Cohomology.subtypeIncl X U
      = Work.Cohomology.subtypeIncl X B := by
  apply TopCat.ext
  intro z
  rfl

/-- **The localisation is natural with respect to the inclusion of open subsets.** -/
theorem excM_comp_inclSub {X : TopCat} {B U : Set X} {K : Set X} (hBU : B ⊆ U) :
    (excM X N U K).comp (RelHmapOf N (inclSub B U hBU) (trace B K) (trace U K)
        (fun z hz => hz))
      = excM X N B K := by
  have hf : ∀ z ∉ trace B K, (inclSub B U hBU) z ∉ trace U K := fun z hz => hz
  have hg : ∀ z ∉ trace U K, (Work.Cohomology.subtypeIncl X U) z ∉ K := fun z hz => hz
  have hgf : ∀ z ∉ trace B K, (inclSub B U hBU ≫ Work.Cohomology.subtypeIncl X U) z ∉ K :=
    fun z hz => hz
  have hf' : ∀ z ∉ trace B K, (Work.Cohomology.subtypeIncl X B) z ∉ K := fun z hz => hz
  simp only [excM]
  rw [RelHmapOf_comp (f := inclSub B U hBU) (g := Work.Cohomology.subtypeIncl X U)
    (K := trace B K) (K' := trace U K) (K'' := K) hf hg hgf]
  exact RelHmapOf_congr (f := inclSub B U hBU ≫ Work.Cohomology.subtypeIncl X U)
    (f' := Work.Cohomology.subtypeIncl X B) (inclSub_comp_subtypeIncl hBU) hgf hf'

/-- **The inverse of excision commutes with the inclusion of open subsets.** -/
theorem excE_symm_incl {X : TopCat} {B U : Set X} (hBU : B ⊆ U) (hB : IsOpen B)
    (hU : IsOpen U) {K : Set X} (hKB : K ⊆ B) (hKU : K ⊆ U) (hKc : IsClosed K)
    (v : Work.Orient.RelH X N K) :
    RelHmapOf N (inclSub B U hBU) (trace B K) (trace U K) (fun z hz => hz)
        ((excE X N B hB K hKB hKc).symm v)
      = (excE X N U hU K hKU hKc).symm v := by
  have h1 : excM X N U K (RelHmapOf N (inclSub B U hBU) (trace B K) (trace U K)
      (fun z hz => hz) ((excE X N B hB K hKB hKc).symm v)) = v := by
    rw [← LinearMap.comp_apply, excM_comp_inclSub hBU, excM_excE_symm]
  have h2 : excM X N U K ((excE X N U hU K hKU hKc).symm v) = v := excM_excE_symm X N U hU K hKU hKc v
  exact (excM_injective X N U hU K hKU hKc) (h1.trans h2.symm)

/-- **The localisation is natural with respect to the restriction of the excluded set.** -/
theorem excM_comp_resRelH (X : TopCat) (N : ℕ) (U : Set X)
    {K₁ K₂ : Set X} (h : K₁ ⊆ K₂) :
    (excM X N U K₁).comp
        (Work.Orient.resRelH (TopCat.of ↥U) N (A := trace U K₁) (B := trace U K₂)
          (fun z hz => h hz))
      = (Work.Orient.resRelH X N h).comp (excM X N U K₂) := by
  simp only [excM]
  exact RelHmapOf_resRelH (X := TopCat.of ↥U) (Y := X) (n := N)
    (Work.Cohomology.subtypeIncl X U) (K₁ := trace U K₁) (K₂ := trace U K₂)
    (K'₁ := K₁) (K'₂ := K₂) (fun z hz => h hz) (fun z hz => h hz)
    (fun z hz => hz) (fun z hz => hz)

/-- **The restriction of the excluded set commutes with the inverse of excision.** -/
theorem resRelH_excE_symm (X : TopCat) (N : ℕ) (U : Set X) (hU : IsOpen U)
    {K₁ K₂ : Set X} (h : K₁ ⊆ K₂) (h₂U : K₂ ⊆ U) (h₁U : K₁ ⊆ U)
    (h₁c : IsClosed K₁) (h₂c : IsClosed K₂) (v : Work.Orient.RelH X N K₂) :
    Work.Orient.resRelH (TopCat.of ↥U) N (A := trace U K₁) (B := trace U K₂)
        (fun z hz => h hz)
        ((excE X N U hU K₂ h₂U h₂c).symm v)
      = (excE X N U hU K₁ h₁U h₁c).symm (Work.Orient.resRelH X N h v) := by
  have h1 : excM X N U K₁
      ((Work.Orient.resRelH (TopCat.of ↥U) N (A := trace U K₁) (B := trace U K₂)
        (fun z hz => h hz)) ((excE X N U hU K₂ h₂U h₂c).symm v))
      = (Work.Orient.resRelH X N h) v := by
    rw [← LinearMap.comp_apply, excM_comp_resRelH X N U h, LinearMap.comp_apply,
      excM_excE_symm]
  have h2 : excM X N U K₁
      ((excE X N U hU K₁ h₁U h₁c).symm ((Work.Orient.resRelH X N h) v))
      = (Work.Orient.resRelH X N h) v := excM_excE_symm X N U hU K₁ h₁U h₁c _
  exact (excM_injective X N U hU K₁ h₁U h₁c) (h1.trans h2.symm)

/-! ## The corestricted chart maps -/

variable [T1Space W]

/-- The chart map, corestricted to the target. -/
def eCore (e : OpenPartialHomeomorph W (Euc N)) :
    TopCat.of ↥e.source ⟶ TopCat.of ↥e.target :=
  TopCat.ofHom ⟨fun z => ⟨e (z : W), e.map_source z.2⟩, by
    exact Continuous.subtype_mk e.continuousOn.domRestrict (fun z => e.map_source z.2)⟩

/-- The inverse chart map, corestricted to the source. -/
def eSymmCore (e : OpenPartialHomeomorph W (Euc N)) :
    TopCat.of ↥e.target ⟶ TopCat.of ↥e.source :=
  TopCat.ofHom ⟨fun z => ⟨e.symm (z : Euc N), e.map_target z.2⟩, by
    exact Continuous.subtype_mk e.continuousOn_symm.domRestrict (fun z => e.map_target z.2)⟩

/-- The inverse chart map, as a map into the ambient space. -/
def eSymmA (e : OpenPartialHomeomorph W (Euc N)) : TopCat.of ↥e.target ⟶ W :=
  TopCat.ofHom ⟨fun z => e.symm (z : Euc N), by
    exact e.continuousOn_symm.domRestrict⟩

@[simp] theorem eCore_apply_coe (e : OpenPartialHomeomorph W (Euc N)) (z : ↥e.source) :
    (((eCore e) z : ↥e.target) : Euc N) = e (z : W) := rfl

@[simp] theorem eSymmCore_apply_coe (e : OpenPartialHomeomorph W (Euc N)) (z : ↥e.target) :
    (((eSymmCore e) z : ↥e.source) : W) = e.symm (z : Euc N) := rfl

@[simp] theorem eSymmA_apply (e : OpenPartialHomeomorph W (Euc N)) (z : ↥e.target) :
    (eSymmA e) z = e.symm (z : Euc N) := rfl

/-- `eSymmA` is the corestricted inverse followed by the inclusion. -/
theorem eSymmA_eq (e : OpenPartialHomeomorph W (Euc N)) :
    eSymmA e = eSymmCore e ≫ Work.Cohomology.subtypeIncl W e.source := by
  apply TopCat.ext
  intro z
  rfl

/-- The pair condition for `eSymmCore`. -/
theorem eSymmCore_pair (e : OpenPartialHomeomorph W (Euc N)) (w : W) (hw : w ∈ e.source)
    {z : ↥e.target} (hz : z ∉ punctSet (TopCat.of (Euc N)) e.target (e w)) :
    (eSymmCore e) z ∉ punctSet W e.source w := by
  intro h
  refine hz ?_
  show (z : Euc N) = e w
  have h' : e.symm (z : Euc N) = w := h
  have h2 : e (e.symm (z : Euc N)) = e w := congrArg e h'
  have h3 : e (e.symm (z : Euc N)) = (z : Euc N) := e.right_inv z.2
  rw [h3] at h2
  exact h2

/-- The pair condition for `eSymmA`. -/
theorem eSymmA_pair (e : OpenPartialHomeomorph W (Euc N)) (w : W) (hw : w ∈ e.source)
    {z : ↥e.target} (hz : z ∉ punctSet (TopCat.of (Euc N)) e.target (e w)) :
    (eSymmA e) z ∉ ({w} : Set W) := by
  intro h
  refine hz ?_
  show (z : Euc N) = e w
  have h2 : e (e.symm (z : Euc N)) = e w := congrArg e h
  have h3 : e (e.symm (z : Euc N)) = (z : Euc N) := e.right_inv z.2
  rw [h3] at h2
  exact h2

/-- The pair condition for `eCore`. -/
theorem eCore_pair (e : OpenPartialHomeomorph W (Euc N)) (w : W) (hw : w ∈ e.source)
    {z : ↥e.source} (hz : z ∉ punctSet W e.source w) :
    (eCore e) z ∉ punctSet (TopCat.of (Euc N)) e.target (e w) := by
  intro h
  refine hz ?_
  show (z : W) = w
  have h2 : e.symm (e (z : W)) = e.symm (e w) := congrArg e.symm h
  rw [e.left_inv z.2, e.left_inv hw] at h2
  exact h2

/-- The corestricted chart map followed by its inverse is the identity. -/
theorem eSymmCore_eCore (e : OpenPartialHomeomorph W (Euc N)) :
    eSymmCore e ≫ eCore e = 𝟙 (TopCat.of ↥e.target) := by
  apply TopCat.ext
  intro z
  exact Subtype.ext (e.right_inv z.2)

/-- The inverse chart map followed by the chart map is the identity. -/
theorem eCore_eSymmCore (e : OpenPartialHomeomorph W (Euc N)) :
    eCore e ≫ eSymmCore e = 𝟙 (TopCat.of ↥e.source) := by
  apply TopCat.ext
  intro z
  exact Subtype.ext (e.left_inv z.2)

/-! ## The chart transfer -/

/-- **The transfer of a local class along a chart**: from a class at `e w` to a class at `w`. -/
def chartTr (e : OpenPartialHomeomorph W (Euc N)) (w : W) (hw : w ∈ e.source) :
    Work.Orient.RelH (TopCat.of (Euc N)) N ({e w} : Set (Euc N)) →ₗ[ℤ]
      Work.Orient.RelH W N ({w} : Set W) :=
  (RelHmapOf N (eSymmA e) (punctSet (TopCat.of (Euc N)) e.target (e w)) ({w} : Set W)
      (fun z hz => eSymmA_pair e w hw hz)).comp
    ((punctIso (TopCat.of (Euc N)) N e.target e.open_target (e w) (e.map_source hw)
      isClosed_singleton).symm.toLinearMap)

/-- **The inverse chart transfer**: from a class at `w` to a class at `e w`. -/
def chartInvCore (e : OpenPartialHomeomorph W (Euc N)) (w : W) (hw : w ∈ e.source) :
    Work.Orient.RelH W N ({w} : Set W) →ₗ[ℤ]
      Work.Orient.RelH (TopCat.of (Euc N)) N ({e w} : Set (Euc N)) :=
  (punctIso (TopCat.of (Euc N)) N e.target e.open_target (e w) (e.map_source hw)
      isClosed_singleton).toLinearMap.comp
    ((RelHmapOf N (eCore e) (punctSet W e.source w)
        (punctSet (TopCat.of (Euc N)) e.target (e w)) (fun z hz => eCore_pair e w hw hz)).comp
      ((punctIso W N e.source e.open_source w hw isClosed_singleton).symm.toLinearMap))

/-- The defining property of `chartTr`. -/
theorem chartTr_apply (e : OpenPartialHomeomorph W (Euc N)) (w : W) (hw : w ∈ e.source)
    (v : Work.Orient.RelH (TopCat.of (Euc N)) N ({e w} : Set (Euc N))) :
    chartTr e w hw v
      = RelHmapOf N (eSymmA e) (punctSet (TopCat.of (Euc N)) e.target (e w)) ({w} : Set W)
          (fun z hz => eSymmA_pair e w hw hz)
          (((punctIso (TopCat.of (Euc N)) N e.target e.open_target (e w) (e.map_source hw)
            isClosed_singleton).symm.toLinearMap) v) := rfl

/-- The defining property of `chartInvCore`. -/
theorem chartInvCore_apply (e : OpenPartialHomeomorph W (Euc N)) (w : W) (hw : w ∈ e.source)
    (v : Work.Orient.RelH W N ({w} : Set W)) :
    chartInvCore e w hw v
      = (punctIso (TopCat.of (Euc N)) N e.target e.open_target (e w) (e.map_source hw)
          isClosed_singleton).toLinearMap
          (RelHmapOf N (eCore e) (punctSet W e.source w)
            (punctSet (TopCat.of (Euc N)) e.target (e w)) (fun z hz => eCore_pair e w hw hz)
            (((punctIso W N e.source e.open_source w hw isClosed_singleton).symm.toLinearMap) v)) := rfl

/-- The ambient form of the transfer is the corestricted form followed by the localisation. -/
theorem relHmapOf_eSymmA (e : OpenPartialHomeomorph W (Euc N)) (w : W) (hw : w ∈ e.source) :
    RelHmapOf N (eSymmA e) (punctSet (TopCat.of (Euc N)) e.target (e w)) ({w} : Set W)
        (fun z hz => eSymmA_pair e w hw hz)
      = (excM W N e.source ({w} : Set W)).comp
          (RelHmapOf N (eSymmCore e) (punctSet (TopCat.of (Euc N)) e.target (e w))
            (punctSet W e.source w) (fun z hz => eSymmCore_pair e w hw hz)) := by
  simp only [excM]
  rw [RelHmapOf_comp (f := eSymmCore e) (g := Work.Cohomology.subtypeIncl W e.source)
    (K := punctSet (TopCat.of (Euc N)) e.target (e w)) (K' := punctSet W e.source w)
    (K'' := ({w} : Set W)) (fun z hz => eSymmCore_pair e w hw hz) (fun z hz => hz)
    (fun z hz => by rw [← eSymmA_eq]; exact eSymmA_pair e w hw hz)]
  exact RelHmapOf_congr (f := eSymmA e)
    (f' := eSymmCore e ≫ Work.Cohomology.subtypeIncl W e.source) (eSymmA_eq e)
    (fun z hz => eSymmA_pair e w hw hz)
    (fun z hz => by rw [← eSymmA_eq]; exact eSymmA_pair e w hw hz)

/-- The inverse of `punctIso` inverts the ambient form of the transfer. -/
theorem punctIso_symm_relHmapOf (e : OpenPartialHomeomorph W (Euc N)) (w : W) (hw : w ∈ e.source)
    (z : Work.Orient.RelH (TopCat.of ↥e.target) N
      (punctSet (TopCat.of (Euc N)) e.target (e w))) :
    ((punctIso W N e.source e.open_source w hw isClosed_singleton).symm.toLinearMap)
        (RelHmapOf N (eSymmA e) (punctSet (TopCat.of (Euc N)) e.target (e w)) ({w} : Set W)
          (fun z hz => eSymmA_pair e w hw hz) z)
      = RelHmapOf N (eSymmCore e) (punctSet (TopCat.of (Euc N)) e.target (e w))
          (punctSet W e.source w) (fun z hz => eSymmCore_pair e w hw hz) z := by
  rw [relHmapOf_eSymmA e w hw, LinearMap.comp_apply]
  exact punctIso_symm_apply W N e.source e.open_source w hw isClosed_singleton _

/-- The corestricted chart map followed by the inverse chart map is the identity. -/
theorem relHmapOf_eCore_comp_eSymmCore (e : OpenPartialHomeomorph W (Euc N)) (w : W)
    (hw : w ∈ e.source) :
    (RelHmapOf N (eCore e) (punctSet W e.source w)
        (punctSet (TopCat.of (Euc N)) e.target (e w)) (fun z hz => eCore_pair e w hw hz)).comp
      (RelHmapOf N (eSymmCore e) (punctSet (TopCat.of (Euc N)) e.target (e w))
        (punctSet W e.source w) (fun z hz => eSymmCore_pair e w hw hz))
      = LinearMap.id := by
  rw [RelHmapOf_comp (f := eSymmCore e) (g := eCore e)
    (K := punctSet (TopCat.of (Euc N)) e.target (e w)) (K' := punctSet W e.source w)
    (K'' := punctSet (TopCat.of (Euc N)) e.target (e w))
    (fun z hz => eSymmCore_pair e w hw hz) (fun z hz => eCore_pair e w hw hz)
    (fun z hz => by rw [eSymmCore_eCore]; exact hz)]
  rw [RelHmapOf_congr (f := eSymmCore e ≫ eCore e) (f' := 𝟙 (TopCat.of ↥e.target))
    (eSymmCore_eCore e) _ _]
  exact RelHmapOf_id _

/-- The inverse chart map followed by the chart map is the identity. -/
theorem relHmapOf_eSymmCore_comp_eCore (e : OpenPartialHomeomorph W (Euc N)) (w : W)
    (hw : w ∈ e.source) :
    (RelHmapOf N (eSymmCore e) (punctSet (TopCat.of (Euc N)) e.target (e w))
        (punctSet W e.source w) (fun z hz => eSymmCore_pair e w hw hz)).comp
      (RelHmapOf N (eCore e) (punctSet W e.source w)
        (punctSet (TopCat.of (Euc N)) e.target (e w)) (fun z hz => eCore_pair e w hw hz))
      = LinearMap.id := by
  rw [RelHmapOf_comp (f := eCore e) (g := eSymmCore e)
    (K := punctSet W e.source w) (K' := punctSet (TopCat.of (Euc N)) e.target (e w))
    (K'' := punctSet W e.source w)
    (fun z hz => eCore_pair e w hw hz) (fun z hz => eSymmCore_pair e w hw hz)
    (fun z hz => by rw [eCore_eSymmCore]; exact hz)]
  rw [RelHmapOf_congr (f := eCore e ≫ eSymmCore e) (f' := 𝟙 (TopCat.of ↥e.source))
    (eCore_eSymmCore e) _ _]
  exact RelHmapOf_id _

/-- The corestricted chart map after the inverse chart map is the identity on its domain. -/
theorem relHmapOf_eCore_apply_eSymmCore (e : OpenPartialHomeomorph W (Euc N)) (w : W)
    (hw : w ∈ e.source) (z : Work.Orient.RelH (TopCat.of ↥e.target) N
      (punctSet (TopCat.of (Euc N)) e.target (e w))) :
    RelHmapOf N (eCore e) (punctSet W e.source w)
        (punctSet (TopCat.of (Euc N)) e.target (e w)) (fun z hz => eCore_pair e w hw hz)
        (RelHmapOf N (eSymmCore e) (punctSet (TopCat.of (Euc N)) e.target (e w))
          (punctSet W e.source w) (fun z hz => eSymmCore_pair e w hw hz) z) = z := by
  rw [← LinearMap.comp_apply, relHmapOf_eCore_comp_eSymmCore e w hw, LinearMap.id_apply]

/-- The inverse chart map after the chart map is the identity on its domain. -/
theorem relHmapOf_eSymmCore_apply_eCore (e : OpenPartialHomeomorph W (Euc N)) (w : W)
    (hw : w ∈ e.source) (z : Work.Orient.RelH (TopCat.of ↥e.source) N
      (punctSet W e.source w)) :
    RelHmapOf N (eSymmCore e) (punctSet (TopCat.of (Euc N)) e.target (e w))
        (punctSet W e.source w) (fun z hz => eSymmCore_pair e w hw hz)
        (RelHmapOf N (eCore e) (punctSet W e.source w)
          (punctSet (TopCat.of (Euc N)) e.target (e w)) (fun z hz => eCore_pair e w hw hz) z)
      = z := by
  rw [← LinearMap.comp_apply, relHmapOf_eSymmCore_comp_eCore e w hw, LinearMap.id_apply]

/-- The ambient transfer followed by the corestricted chart map is the localisation. -/
theorem relHmapOf_eSymmA_apply_eCore (e : OpenPartialHomeomorph W (Euc N)) (w : W)
    (hw : w ∈ e.source) (z : Work.Orient.RelH (TopCat.of ↥e.source) N
      (punctSet W e.source w)) :
    RelHmapOf N (eSymmA e) (punctSet (TopCat.of (Euc N)) e.target (e w)) ({w} : Set W)
        (fun z hz => eSymmA_pair e w hw hz)
        (RelHmapOf N (eCore e) (punctSet W e.source w)
          (punctSet (TopCat.of (Euc N)) e.target (e w)) (fun z hz => eCore_pair e w hw hz) z)
      = excM W N e.source ({w} : Set W) z := by
  rw [relHmapOf_eSymmA e w hw, LinearMap.comp_apply, relHmapOf_eSymmCore_apply_eCore e w hw]

/-- **The transfer is a section of its inverse.** -/
theorem chartInvCore_chartTr (e : OpenPartialHomeomorph W (Euc N)) (w : W) (hw : w ∈ e.source)
    (v : Work.Orient.RelH (TopCat.of (Euc N)) N ({e w} : Set (Euc N))) :
    chartInvCore e w hw (chartTr e w hw v) = v := by
  rw [chartTr_apply, chartInvCore_apply]
  rw [punctIso_symm_relHmapOf e w hw, relHmapOf_eCore_apply_eSymmCore e w hw]
  exact LinearEquiv.apply_symm_apply _ v

/-- **The transfer is a retraction of its inverse.** -/
theorem punctIso_symm_toLinearMap_apply (X : TopCat) (N : ℕ) (U : Set X) (hU : IsOpen U)
    (x : X) (hx : x ∈ U) (hxc : IsClosed ({x} : Set X))
    (v : Work.Orient.RelH (TopCat.of ↥U) N (punctSet X U x)) :
    ((punctIso X N U hU x hx hxc).symm.toLinearMap)
      ((punctIso X N U hU x hx hxc).toLinearMap v) = v :=
  LinearEquiv.symm_apply_apply _ v

/-- The composite `punctIso.symm ∘ excM` is the identity, in the spelling used in the definitions. -/
theorem punctIso_symm_toLinearMap_excM (X : TopCat) (N : ℕ) (U : Set X) (hU : IsOpen U)
    (x : X) (hx : x ∈ U) (hxc : IsClosed ({x} : Set X))
    (v : Work.Orient.RelH (TopCat.of ↥U) N (punctSet X U x)) :
    ((punctIso X N U hU x hx hxc).symm.toLinearMap) (excM X N U ({x} : Set X) v) = v :=
  LinearEquiv.symm_apply_apply _ v

/-- `punctIso_excM_symm` with the `.toLinearMap` spelling used in the definitions. -/
theorem punctIso_excM_symm' (X : TopCat) (N : ℕ) (U : Set X) (hU : IsOpen U) (x : X)
    (hx : x ∈ U) (hxc : IsClosed ({x} : Set X)) (v : Work.Orient.RelH X N ({x} : Set X)) :
    excM X N U ({x} : Set X) (((punctIso X N U hU x hx hxc).symm.toLinearMap) v) = v :=
  punctIso_excM_symm X N U hU x hx hxc v

theorem chartTr_chartInvCore (e : OpenPartialHomeomorph W (Euc N)) (w : W) (hw : w ∈ e.source)
    (v : Work.Orient.RelH W N ({w} : Set W)) :
    chartTr e w hw (chartInvCore e w hw v) = v := by
  rw [chartInvCore_apply, chartTr_apply]
  rw [punctIso_symm_toLinearMap_apply]
  rw [relHmapOf_eSymmA_apply_eCore e w hw, punctIso_excM_symm']

/-- **The chart transfer is surjective.** -/
theorem chartTr_surjective (e : OpenPartialHomeomorph W (Euc N)) (w : W) (hw : w ∈ e.source) :
    Function.Surjective (chartTr e w hw) :=
  fun v => ⟨chartInvCore e w hw v, chartTr_chartInvCore e w hw v⟩

end

end Work.PTGeometric.HOF
