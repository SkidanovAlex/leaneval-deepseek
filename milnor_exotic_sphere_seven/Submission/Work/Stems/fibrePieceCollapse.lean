import Mathlib
import Submission.Work.Serre.isZero_homology_relChainsR_cylCMid_of_pairComparison
import Submission.Work.Serre.CsrSharp.Tools
import Submission.Work.Serre.CylCMidVan.relChainsR_excisionInterior
import Submission.Work.Serre.cylCollarShrink
import Submission.Work.Serre.CMidPairDefs
import Submission.Work.Serre.C1CylExplicit
import Submission.Work.Serre.DiscPair.relPairHomotopic
import Submission.Work.Serre.relCohPreimageDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The collapse of the mapping cylinder onto the cone attachment is a homology isomorphism

`Work.Stems.collapseMap_isIso`: for a continuous map `q : C(X,B)` and `b : B`, the map of relative
rational chain complexes

  `C_*(X, q⁻¹{b};ℚ) ⟶ C_*(CMid q b, (cylRetract q)⁻¹{b};ℚ)`

induced by the inclusion of the bottom copy of the mapping cylinder `cyl q` is an isomorphism on
homology.  It is the "cone attachment" half of the identification of the pair `(cyl q, CMid q b)`
with the cofibre of the pair map `(X, q⁻¹{b}) → (B,{b})`.

The proof factors the inclusion as

`(X, q⁻¹b) ≅ (cylBot q, cylBot q ∩ P) ⟶ (collar part of CMid, ∩ P) ⟶ (CMid q b, P)`,

the first map being the bottom-copy homeomorphism (`pcHomeo`), the second a homotopy equivalence of
pairs given by the collar shrink (`Work.Serre.cylShrinkHomotopy`, whose values stay in `CMid` and
preserve the fibre cone), and the third an excision isomorphism
(`Work.Serre.CylCMidVan.relChainsR_excisionInterior` for the cover of `CMid q b` by the collar and
the interior of the cone).
-/

set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits
open scoped Topology unitInterval

namespace Work.Stems

noncomputable section

variable {B : Type} [TopologicalSpace B] {X : Type} [TopologicalSpace X]

/-- The fibre cone `P = (cylRetract q)⁻¹{b}` inside `CMid q b`. -/
abbrev pcPc (q : C(X, B)) (b : B) : Set ↥(Work.Serre.CMid q b) :=
  {x | (x : Work.Serre.cyl q) ∈ Work.Serre.fibreSet q b}

/-- The collar part of `CMid q b`. -/
abbrev pcUc (q : C(X, B)) (b : B) : Set ↥(Work.Serre.CMid q b) :=
  {x | (x : Work.Serre.cyl q) ∈ Work.Serre.cylCollar q}

/-- The fibre cone inside the bottom copy. -/
abbrev pcAc (q : C(X, B)) (b : B) : Set ↥(Work.Serre.cylBot q) :=
  {a | (a : Work.Serre.cyl q) ∈ Work.Serre.fibreSet q b}

/-- The fibre cone inside the collar part of `CMid q b`. -/
abbrev pcBc (q : C(X, B)) (b : B) : Set ↥(pcUc q b) :=
  {x | ((x.1 : ↥(Work.Serre.CMid q b)) : Work.Serre.cyl q) ∈ Work.Serre.fibreSet q b}

/-- The shrink at time `1` as a map `↥(pcUc q b) → ↥(cylBot q)`. -/
def pcShr (q : C(X, B)) (b : B) : C(↥(pcUc q b), ↥(Work.Serre.cylBot q)) :=
  (Work.Serre.cylShrinkToBot q).comp
    ⟨fun z => ⟨z.1.1, z.2⟩, by fun_prop⟩

@[simp] lemma pcShr_apply (q : C(X, B)) (b : B) (z : ↥(pcUc q b)) :
    ((pcShr q b z : ↥(Work.Serre.cylBot q)) : Work.Serre.cyl q)
      = ((Work.Serre.cylShrink q 1 ⟨z.1.1, z.2⟩ : ↥(Work.Serre.cylCollar q))
          : Work.Serre.cyl q) := rfl

/-- The inclusion `↥(cylBot q) → ↥(pcUc q b)`. -/
def pcIncl (q : C(X, B)) (b : B) : C(↥(Work.Serre.cylBot q), ↥(pcUc q b)) where
  toFun a := ⟨⟨a.1, Work.Serre.CMid_subset q b a.2⟩, Work.Serre.cylBot_subset_cylCollar q a.2⟩
  continuous_toFun := by fun_prop

@[simp] lemma pcIncl_apply (q : C(X, B)) (b : B) (a : ↥(Work.Serre.cylBot q)) :
    ((pcIncl q b a : ↥(pcUc q b)).1 : Work.Serre.cyl q) = (a : Work.Serre.cyl q) := rfl

lemma pc_cylShrink_mem_CMid (q : C(X, B)) (b : B) (s : unitInterval)
    (z : ↥(Work.Serre.cylCollar q))
    (hz : (z : Work.Serre.cyl q) ∈ Work.Serre.CMid q b) :
    ((Work.Serre.cylShrink q s z : ↥(Work.Serre.cylCollar q)) : Work.Serre.cyl q)
      ∈ Work.Serre.CMid q b := by
  rcases hz with hA | hP
  · rw [Work.Serre.cylShrink_fixes_bot q s hA]
    exact Or.inl hA
  · right
    show Work.Serre.cylRetract q
      ((Work.Serre.cylShrink q s z : ↥(Work.Serre.cylCollar q)) : Work.Serre.cyl q) = b
    rw [Work.Serre.cylRetract_cylShrink]
    exact hP

/-- The underlying function of the reduced shrink homotopy. -/
def pcHomFun (q : C(X, B)) (b : B) : unitInterval × ↥(pcUc q b) → ↥(pcUc q b) := fun p =>
  ⟨⟨(Work.Serre.cylShrink q p.1 ⟨p.2.1.1, p.2.2⟩ : ↥(Work.Serre.cylCollar q)),
      pc_cylShrink_mem_CMid q b p.1 _ p.2.1.2⟩,
    (Work.Serre.cylShrink q p.1 ⟨p.2.1.1, p.2.2⟩ : ↥(Work.Serre.cylCollar q)).2⟩

@[simp] lemma pcHomFun_apply (q : C(X, B)) (b : B) (s : unitInterval) (z : ↥(pcUc q b)) :
    (((pcHomFun q b (s, z) : ↥(pcUc q b)).1 : ↥(Work.Serre.CMid q b)) : Work.Serre.cyl q)
      = ((Work.Serre.cylShrink q s ⟨z.1.1, z.2⟩ : ↥(Work.Serre.cylCollar q))
          : Work.Serre.cyl q) := rfl

lemma continuous_pcHomFun (q : C(X, B)) (b : B) : Continuous (pcHomFun q b) := by
  have hφ : Continuous (fun p : unitInterval × ↥(pcUc q b) =>
      (⟨p.2.1.1, p.2.2⟩ : ↥(Work.Serre.cylCollar q))) :=
    Continuous.subtype_mk (f := fun p : unitInterval × ↥(pcUc q b) => (p.2.1.1 : Work.Serre.cyl q))
      (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd)) (fun p => p.2.2)
  have h1 : Continuous (fun p : unitInterval × ↥(pcUc q b) =>
      ((Work.Serre.cylShrink q p.1 ⟨p.2.1.1, p.2.2⟩ : ↥(Work.Serre.cylCollar q))
        : Work.Serre.cyl q)) := by
    have h0 : Continuous (fun p : unitInterval × ↥(pcUc q b) =>
        (((Work.Serre.cylShrinkHomotopy q).toContinuousMap
          (p.1, (⟨p.2.1.1, p.2.2⟩ : ↥(Work.Serre.cylCollar q))) : ↥(Work.Serre.cylCollar q))
            : Work.Serre.cyl q)) :=
      continuous_subtype_val.comp
        ((Work.Serre.cylShrinkHomotopy q).toContinuousMap.continuous.comp
          (Continuous.prodMk continuous_fst hφ))
    refine Continuous.congr h0 ?_
    intro p
    exact congrArg Subtype.val (Work.Serre.cylShrinkHomotopy_apply q p.1
      (⟨p.2.1.1, p.2.2⟩ : ↥(Work.Serre.cylCollar q)))
  exact Continuous.subtype_mk
    (Continuous.subtype_mk h1 (fun p => pc_cylShrink_mem_CMid q b p.1 _ p.2.1.2))
    (fun p => (Work.Serre.cylShrink q p.1 ⟨p.2.1.1, p.2.2⟩ : ↥(Work.Serre.cylCollar q)).2)

/-- The reduced shrink homotopy on the collar part of `CMid q b`. -/
def pcHomotopy (q : C(X, B)) (b : B) :
    ContinuousMap.Homotopy (ContinuousMap.id ↥(pcUc q b)) ((pcIncl q b).comp (pcShr q b)) where
  toContinuousMap := ⟨pcHomFun q b, continuous_pcHomFun q b⟩
  map_zero_left := fun y => by
    refine Subtype.ext (Subtype.ext ?_)
    rw [pcHomFun_apply]
    show ((Work.Serre.cylShrink q 0 ⟨y.1.1, y.2⟩ : ↥(Work.Serre.cylCollar q))
        : Work.Serre.cyl q) = (y.1.1 : Work.Serre.cyl q)
    have h := Work.Serre.cylShrinkHomotopy_apply q 0 (⟨y.1.1, y.2⟩ : ↥(Work.Serre.cylCollar q))
    rw [← h]
    exact congrArg Subtype.val ((Work.Serre.cylShrinkHomotopy q).map_zero_left _)
  map_one_left := fun y => by
    refine Subtype.ext (Subtype.ext ?_)
    rw [pcHomFun_apply, ContinuousMap.comp_apply, pcIncl_apply, pcShr_apply]

lemma pc_homotopy_memBc (q : C(X, B)) (b : B) (s : unitInterval) (z : ↥(pcUc q b))
    (hz : z ∈ pcBc q b) : ((pcHomotopy q b) (s, z)) ∈ pcBc q b := by
  show Work.Serre.cylRetract q
    ((((pcHomotopy q b) (s, z) : ↥(pcUc q b)).1 : ↥(Work.Serre.CMid q b)) : Work.Serre.cyl q) = b
  rw [show (((pcHomotopy q b) (s, z) : ↥(pcUc q b)).1 : ↥(Work.Serre.CMid q b))
      = (pcHomFun q b (s, z)).1 from rfl]
  rw [pcHomFun_apply]
  rw [Work.Serre.cylRetract_cylShrink]
  exact hz

/-- The shrink fixes the bottom copy (as maps `↥(cylBot q) → ↥(cylBot q)`). -/
lemma pcShr_comp_pcIncl (q : C(X, B)) (b : B) :
    (pcShr q b).comp (pcIncl q b) = ContinuousMap.id ↥(Work.Serre.cylBot q) := by
  ext a
  rw [ContinuousMap.comp_apply, ContinuousMap.id_apply]
  rw [pcShr_apply]
  rw [Work.Serre.cylShrink_fixes_bot q 1 a.2]
  rfl

/-- A rewriting form of `cylRetract_cylIncl`. -/
lemma pc_cylRetract_cylIncl (q : C(X, B)) (x : X) :
    Work.Serre.cylRetract q (Work.Serre.cylIncl q x) = q x :=
  DFunLike.congr_fun (Work.Serre.cylRetract_cylIncl q) x

/-- The bottom copy is the zero locus of the collar coordinate. -/
lemma pc_cylBot_eq (q : C(X, B)) : Work.Serre.cylBot q = {y | Work.Serre.cylLam q y = 0} :=
  Work.Serre.cylBot_eq_cylLam_zero q

/-- The collar part of `CMid q b` is open. -/
lemma pc_isOpen_Uc (q : C(X, B)) (b : B) : IsOpen (pcUc q b) :=
  (Work.Serre.isOpen_cylCollar q).preimage continuous_subtype_val

/-- The open set `{λ > 0}` inside `CMid q b` is contained in the fibre cone. -/
lemma pc_pos_subset (q : C(X, B)) (b : B) :
    {y : ↥(Work.Serre.CMid q b) |
        0 < ((Work.Serre.cylLam q (y : Work.Serre.cyl q) : unitInterval) : ℝ)}
      ⊆ pcPc q b := by
  intro y hy
  show (y : Work.Serre.cyl q) ∈ Work.Serre.fibreSet q b
  show Work.Serre.cylRetract q (y : Work.Serre.cyl q) = b
  rcases y.2 with hA | hP
  · exfalso
    have h0 : Work.Serre.cylLam q (y : Work.Serre.cyl q) = 0 :=
      (Set.ext_iff.mp (pc_cylBot_eq q) (y : Work.Serre.cyl q)).mp hA
    have h0' : ((Work.Serre.cylLam q (y : Work.Serre.cyl q) : unitInterval) : ℝ) = 0 := by
      rw [h0]; rfl
    exact absurd (show ((Work.Serre.cylLam q (y : Work.Serre.cyl q) : unitInterval) : ℝ)
      = 0 from h0') (ne_of_gt hy)
  · exact hP

/-- **Excision**: the pair `(collar part, fibre cone)` computes the pair `(CMid q b, fibre cone)`. -/
theorem pc_excision (q : C(X, B)) (b : B) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      (Work.Serre.relChainsRInclPairMap (TopCat.of ↥(Work.Serre.CMid q b))
        (pcUc q b) (pcPc q b)) n) := by
  refine Work.Serre.CylCMidVan.relChainsR_excisionInterior (pcUc q b) (pcPc q b) ?_ n
  refine Set.eq_univ_of_forall (fun x => ?_)
  by_cases hx : ((Work.Serre.cylLam q (x : Work.Serre.cyl q) : unitInterval) : ℝ) < 1
  · exact Or.inr ((pc_isOpen_Uc q b).interior_eq.symm ▸ hx)
  · refine Or.inl (interior_maximal (pc_pos_subset q b) ?_ ?_)
    · exact (isOpen_lt continuous_const
        (continuous_subtype_val.comp ((Work.Serre.cylLam q).continuous.comp
          continuous_subtype_val)))
    · have hle : ((Work.Serre.cylLam q (x : Work.Serre.cyl q) : unitInterval) : ℝ) ≤ 1 :=
        (Work.Serre.cylLam q (x : Work.Serre.cyl q)).2.2
      have h1 : ((Work.Serre.cylLam q (x : Work.Serre.cyl q) : unitInterval) : ℝ) = 1 :=
        le_antisymm hle (not_lt.mp hx)
      show 0 < ((Work.Serre.cylLam q (x : Work.Serre.cyl q) : unitInterval) : ℝ)
      rw [h1]; norm_num

/-- The inclusion of the bottom copy into the collar part, as a map of pairs. -/
lemma pc_incl_maps (q : C(X, B)) (b : B) :
    Set.MapsTo (pcIncl q b) (pcAc q b) (pcBc q b) := by
  intro a ha
  show ((pcIncl q b a : ↥(pcUc q b)).1 : Work.Serre.cyl q) ∈ Work.Serre.fibreSet q b
  rw [pcIncl_apply]
  exact ha

/-- **The shrink**: the inclusion of the bottom copy into the collar part is an isomorphism on
relative rational homology. -/
theorem pc_shrink (q : C(X, B)) (b : B) (n : ℕ)
    (hg : Set.MapsTo (pcIncl q b) (pcAc q b) (pcBc q b)) :
    IsIso (HomologicalComplex.homologyMap
      (Work.Serre.relChainsRPairMap (pcAc q b) (pcBc q b) (pcIncl q b) hg) n) := by
  have hs : Set.MapsTo (pcShr q b) (pcBc q b) (pcAc q b) := by
    intro z hz
    show (pcShr q b z : ↥(Work.Serre.cylBot q)) ∈ pcAc q b
    show Work.Serre.cylRetract q ((pcShr q b z : ↥(Work.Serre.cylBot q)) : Work.Serre.cyl q) = b
    rw [pcShr_apply, Work.Serre.cylRetract_cylShrink]
    exact hz
  have hchain1 : Work.Serre.relChainsRPairMap (pcAc q b) (pcBc q b) (pcIncl q b) hg
      ≫ Work.Serre.relChainsRPairMap (pcBc q b) (pcAc q b) (pcShr q b) hs
      = 𝟙 _ := by
    have key := Work.Serre.CsrSharp.Tools.relChainsRPairMap_comp (pcIncl q b) (pcShr q b) hg hs
      (hg'' := fun a ha => hs (hg ha))
    rw [key]
    have key2 := Work.Serre.CsrSharp.Tools.relChainsRPairMap_congr
      (A := pcAc q b) (B := pcAc q b)
      (g := (pcShr q b).comp (pcIncl q b)) (g' := ContinuousMap.id ↥(Work.Serre.cylBot q))
      (pcShr_comp_pcIncl q b) (fun a ha => hs (hg ha)) (fun a ha => ha)
    rw [key2]
    exact Work.Serre.CsrSharp.Tools.relChainsRPairMap_id' (pcAc q b) (fun a ha => ha)
  have hhom1 : HomologicalComplex.homologyMap
        (Work.Serre.relChainsRPairMap (pcAc q b) (pcBc q b) (pcIncl q b) hg) n
      ≫ HomologicalComplex.homologyMap
        (Work.Serre.relChainsRPairMap (pcBc q b) (pcAc q b) (pcShr q b) hs) n = 𝟙 _ := by
    rw [← HomologicalComplex.homologyMap_comp, hchain1]
    exact HomologicalComplex.homologyMap_id ..
  have hhom2 : HomologicalComplex.homologyMap
        (Work.Serre.relChainsRPairMap (pcBc q b) (pcAc q b) (pcShr q b) hs) n
      ≫ HomologicalComplex.homologyMap
        (Work.Serre.relChainsRPairMap (pcAc q b) (pcBc q b) (pcIncl q b) hg) n = 𝟙 _ := by
    have hhom := Work.Serre.DiscPair.relPairHomotopic (A := pcBc q b) (B := pcBc q b)
      (f := ContinuousMap.id ↥(pcUc q b)) (g := (pcIncl q b).comp (pcShr q b))
      (fun z hz => hz) (fun z hz => hg (hs hz)) (pcHomotopy q b)
      (fun s z hz => pc_homotopy_memBc q b s z hz) n
    have key := Work.Serre.CsrSharp.Tools.relChainsRPairMap_comp (pcShr q b) (pcIncl q b) hs hg
      (hg'' := fun z hz => hg (hs hz))
    rw [← HomologicalComplex.homologyMap_comp, key, ← hhom]
    rw [Work.Serre.CsrSharp.Tools.relChainsRPairMap_id' (pcBc q b) (fun z hz => hz)]
    exact HomologicalComplex.homologyMap_id ..
  exact IsIso.mk ⟨HomologicalComplex.homologyMap
    (Work.Serre.relChainsRPairMap (pcBc q b) (pcAc q b) (pcShr q b) hs) n,
    hhom1, hhom2⟩

/-- The bottom copy of the mapping cylinder is homeomorphic to `X`; this is
`Work.Serre.cylHomeoExplicit` in the `Work.Serre.cylBot` spelling. -/
def pcHomeo (q : C(X, B)) : X ≃ₜ ↥(Work.Serre.cylBot q) where
  toFun := fun x => ⟨Work.Serre.cylIncl q x, ⟨x, rfl⟩⟩
  invFun := fun a => (Work.Serre.cylHomeoExplicit q).choose.symm
    ⟨(a : Work.Serre.cyl q), a.2⟩
  left_inv := fun x => by
    show (Work.Serre.cylHomeoExplicit q).choose.symm
        ⟨(Work.Serre.cylIncl q x : Work.Serre.cyl q),
          (⟨x, rfl⟩ : Work.Serre.cylIncl q x ∈ Set.range (Work.Serre.cylIncl q))⟩ = x
    have h : (⟨(Work.Serre.cylIncl q x : Work.Serre.cyl q),
        (⟨x, rfl⟩ : Work.Serre.cylIncl q x ∈ Set.range (Work.Serre.cylIncl q))⟩ :
          ↥(Set.range (Work.Serre.cylIncl q))) =
        (Work.Serre.cylHomeoExplicit q).choose x := by
      apply Subtype.ext
      exact ((Work.Serre.cylHomeoExplicit q).choose_spec x).symm
    rw [h, Homeomorph.symm_apply_apply]
  right_inv := fun a => by
    show (⟨Work.Serre.cylIncl q ((Work.Serre.cylHomeoExplicit q).choose.symm
        ⟨(a : Work.Serre.cyl q), a.2⟩), ⟨_, rfl⟩⟩ : ↥(Work.Serre.cylBot q)) = a
    apply Subtype.ext
    show (Work.Serre.cylIncl q ((Work.Serre.cylHomeoExplicit q).choose.symm
        ⟨(a : Work.Serre.cyl q), a.2⟩) : Work.Serre.cyl q) = (a : Work.Serre.cyl q)
    rw [← (Work.Serre.cylHomeoExplicit q).choose_spec
      ((Work.Serre.cylHomeoExplicit q).choose.symm ⟨(a : Work.Serre.cyl q), a.2⟩)]
    rw [Homeomorph.apply_symm_apply]
  continuous_toFun := by fun_prop
  continuous_invFun := by
    apply Continuous.comp ((Work.Serre.cylHomeoExplicit q).choose.symm.continuous)
    exact Continuous.subtype_mk continuous_subtype_val _

/-- `pcHomeo` as a continuous map. -/
abbrev pcHomeoC (q : C(X, B)) : C(X, ↥(Work.Serre.cylBot q)) :=
  ⟨(pcHomeo q).toFun, (pcHomeo q).continuous_toFun⟩

/-- The inverse of `pcHomeo`, as a continuous map. -/
abbrev pcHomeoInv (q : C(X, B)) : C(↥(Work.Serre.cylBot q), X) :=
  ⟨(pcHomeo q).symm, (pcHomeo q).symm.continuous⟩

@[simp] lemma pcHomeoC_apply (q : C(X, B)) (x : X) :
    ((pcHomeoC q x : ↥(Work.Serre.cylBot q)) : Work.Serre.cyl q) = Work.Serre.cylIncl q x := rfl

/-- `pcHomeo` sends `q⁻¹{b}` into the fibre cone. -/
lemma pc_homeo_maps (q : C(X, B)) (b : B) :
    Set.MapsTo (pcHomeoC q) (q ⁻¹' ({b} : Set B)) (pcAc q b) := by
  intro x hx
  show ((pcHomeoC q x : ↥(Work.Serre.cylBot q)) : Work.Serre.cyl q)
    ∈ Work.Serre.fibreSet q b
  show Work.Serre.cylRetract q ((pcHomeoC q x : ↥(Work.Serre.cylBot q))
    : Work.Serre.cyl q) = b
  rw [pcHomeoC_apply, pc_cylRetract_cylIncl q x]
  exact hx

/-- The inverse of `pcHomeo` maps the fibre cone back into `q⁻¹{b}`. -/
lemma pcHomeoInv_maps (q : C(X, B)) (b : B) :
    Set.MapsTo (pcHomeoInv q) (pcAc q b) (q ⁻¹' ({b} : Set B)) := by
  intro a ha
  have h3 : (pcHomeo q) ((pcHomeo q).symm a) = a := Homeomorph.apply_symm_apply (pcHomeo q) a
  have h2 : Work.Serre.cylIncl q (pcHomeoInv q a) = (a : Work.Serre.cyl q) := by
    have h4 : ((pcHomeo q) ((pcHomeo q).symm a) : Work.Serre.cyl q)
        = (a : Work.Serre.cyl q) := congrArg Subtype.val h3
    rw [← h4]
    rfl
  show q (pcHomeoInv q a) = b
  rw [← pc_cylRetract_cylIncl q (pcHomeoInv q a)]
  rw [h2]
  exact ha

/-- **The homeomorphism step**: the bottom copy of the mapping cylinder computes `(X, q⁻¹b)`. -/
theorem pc_homeo (q : C(X, B)) (b : B) (n : ℕ)
    (hAB : Set.MapsTo (pcHomeoC q) (q ⁻¹' ({b} : Set B)) (pcAc q b)) :
    IsIso (HomologicalComplex.homologyMap
      (Work.Serre.relChainsRPairMap (q ⁻¹' ({b} : Set B)) (pcAc q b)
        (pcHomeoC q) hAB) n) := by
  have hs : Set.MapsTo (pcHomeoInv q) (pcAc q b) (q ⁻¹' ({b} : Set B)) :=
    pcHomeoInv_maps q b
  have hleft : (pcHomeoInv q).comp (pcHomeoC q) = ContinuousMap.id X := by
    ext x
    exact Homeomorph.symm_apply_apply (pcHomeo q) x
  have hright : (pcHomeoC q).comp (pcHomeoInv q) = ContinuousMap.id ↥(Work.Serre.cylBot q) := by
    ext a
    exact congrArg Subtype.val (Homeomorph.apply_symm_apply (pcHomeo q) a)
  have hchain1 : Work.Serre.relChainsRPairMap (q ⁻¹' ({b} : Set B)) (pcAc q b)
        (pcHomeoC q) hAB
      ≫ Work.Serre.relChainsRPairMap (pcAc q b) (q ⁻¹' ({b} : Set B)) (pcHomeoInv q) hs
      = 𝟙 _ := by
    rw [Work.Serre.CsrSharp.Tools.relChainsRPairMap_comp (pcHomeoC q) (pcHomeoInv q) hAB hs
      (hg'' := fun x hx => hs (hAB hx))]
    refine (Work.Serre.CsrSharp.Tools.relChainsRPairMap_congr hleft
      (fun x hx => hs (hAB hx)) (fun x hx => hx)).trans ?_
    exact Work.Serre.CsrSharp.Tools.relChainsRPairMap_id' (q ⁻¹' ({b} : Set B))
      (fun x hx => hx)
  have hchain2 : Work.Serre.relChainsRPairMap (pcAc q b) (q ⁻¹' ({b} : Set B)) (pcHomeoInv q) hs
      ≫ Work.Serre.relChainsRPairMap (q ⁻¹' ({b} : Set B)) (pcAc q b) (pcHomeoC q) hAB
      = 𝟙 _ := by
    rw [Work.Serre.CsrSharp.Tools.relChainsRPairMap_comp (pcHomeoInv q) (pcHomeoC q) hs hAB
      (hg'' := fun a ha => hAB (hs ha))]
    refine (Work.Serre.CsrSharp.Tools.relChainsRPairMap_congr hright
      (fun a ha => hAB (hs ha)) (fun a ha => ha)).trans ?_
    exact Work.Serre.CsrSharp.Tools.relChainsRPairMap_id' (pcAc q b) (fun a ha => ha)
  have hhom1 : HomologicalComplex.homologyMap
        (Work.Serre.relChainsRPairMap (q ⁻¹' ({b} : Set B)) (pcAc q b) (pcHomeoC q) hAB) n
      ≫ HomologicalComplex.homologyMap
        (Work.Serre.relChainsRPairMap (pcAc q b) (q ⁻¹' ({b} : Set B)) (pcHomeoInv q) hs) n
      = 𝟙 _ := by
    rw [← HomologicalComplex.homologyMap_comp, hchain1]
    exact HomologicalComplex.homologyMap_id ..
  have hhom2 : HomologicalComplex.homologyMap
        (Work.Serre.relChainsRPairMap (pcAc q b) (q ⁻¹' ({b} : Set B)) (pcHomeoInv q) hs) n
      ≫ HomologicalComplex.homologyMap
        (Work.Serre.relChainsRPairMap (q ⁻¹' ({b} : Set B)) (pcAc q b) (pcHomeoC q) hAB) n
      = 𝟙 _ := by
    rw [← HomologicalComplex.homologyMap_comp, hchain2]
    exact HomologicalComplex.homologyMap_id ..
  exact IsIso.mk ⟨HomologicalComplex.homologyMap
    (Work.Serre.relChainsRPairMap (pcAc q b) (q ⁻¹' ({b} : Set B)) (pcHomeoInv q) hs) n,
    hhom1, hhom2⟩

/-- The inclusion of the collar part into `CMid q b`, as a continuous map. -/
abbrev pcUC (q : C(X, B)) (b : B) : C(↥(pcUc q b), ↥(Work.Serre.CMid q b)) :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-- **The collapse is a homology isomorphism.** -/
theorem collapseMap_isIso (q : C(X, B)) (b : B) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap (Work.Serre.collapseMap q b) n) := by
  classical
  have hAB : Set.MapsTo (pcHomeoC q) (q ⁻¹' ({b} : Set B)) (pcAc q b) := pc_homeo_maps q b
  have hg1 : Set.MapsTo (pcIncl q b) (pcAc q b) (pcBc q b) := pc_incl_maps q b
  let A : Work.StemsB.relChainsR ℚ (TopCat.of X) (q ⁻¹' ({b} : Set B)) ⟶
      Work.StemsB.relChainsR ℚ (TopCat.of ↥(Work.Serre.cylBot q)) (pcAc q b) :=
    Work.Serre.relChainsRPairMap (q ⁻¹' ({b} : Set B)) (pcAc q b) (pcHomeoC q) hAB
  let Bm : Work.StemsB.relChainsR ℚ (TopCat.of ↥(Work.Serre.cylBot q)) (pcAc q b) ⟶
      Work.StemsB.relChainsR ℚ (TopCat.of ↥(pcUc q b)) (pcBc q b) :=
    Work.Serre.relChainsRPairMap (pcAc q b) (pcBc q b) (pcIncl q b) hg1
  let C : Work.StemsB.relChainsR ℚ (TopCat.of ↥(pcUc q b)) (pcBc q b) ⟶
      Work.StemsB.relChainsR ℚ (TopCat.of ↥(Work.Serre.CMid q b)) (pcPc q b) :=
    Work.Serre.relChainsRInclPairMap (TopCat.of ↥(Work.Serre.CMid q b)) (pcUc q b) (pcPc q b)
  have h3 : IsIso (HomologicalComplex.homologyMap A n) := pc_homeo q b n hAB
  have h2 : IsIso (HomologicalComplex.homologyMap Bm n) := pc_shrink q b n hg1
  have h1 : IsIso (HomologicalComplex.homologyMap C n) := pc_excision q b n
  have hg2 : Set.MapsTo (pcUC q b) (pcBc q b) (pcPc q b) := by
    intro y hy
    show ((y : ↥(pcUc q b)).1 : Work.Serre.cyl q) ∈ Work.Serre.fibreSet q b
    exact hy
  have hg3 : Set.MapsTo ((pcUC q b).comp (pcIncl q b)) (pcAc q b) (pcPc q b) := by
    intro y hy
    show ((pcUC q b) ((pcIncl q b) y) : ↥(Work.Serre.CMid q b)) ∈ pcPc q b
    exact hg2 (hg1 hy)
  have hg4 : Set.MapsTo ((pcUC q b).comp ((pcIncl q b).comp (pcHomeoC q)))
      (q ⁻¹' ({b} : Set B)) (pcPc q b) := fun x hx => hg3 (hAB hx)
  have hToCMid : Set.MapsTo (Work.Serre.toCMid q b) (q ⁻¹' ({b} : Set B)) (pcPc q b) := by
    intro x hx
    show (Work.Serre.toCMid q b x : ↥(Work.Serre.CMid q b)) ∈ pcPc q b
    show Work.Serre.cylRetract q (Work.Serre.cylIncl q x) = b
    rw [pc_cylRetract_cylIncl q x]
    exact hx
  have hmap : (pcUC q b).comp ((pcIncl q b).comp (pcHomeoC q)) = Work.Serre.toCMid q b := by
    ext x
    show ((pcIncl q b (pcHomeoC q x)).1 : Work.Serre.cyl q) = Work.Serre.cylIncl q x
    rw [pcIncl_apply]
    exact pcHomeoC_apply q x
  have hcomp : Work.Serre.collapseMap q b = A ≫ Bm ≫ C := by
    simp only [A, Bm, C, Work.Serre.collapseMap]
    rw [show Work.Serre.relChainsRInclPairMap (TopCat.of ↥(Work.Serre.CMid q b))
          (pcUc q b) (pcPc q b)
        = Work.Serre.relChainsRPairMap (pcBc q b) (pcPc q b) (pcUC q b)
            (fun y hy => hg2 hy) from rfl]
    rw [Work.Serre.CsrSharp.Tools.relChainsRPairMap_comp (pcIncl q b) (pcUC q b) hg1 hg2
      (hg'' := hg3)]
    rw [Work.Serre.CsrSharp.Tools.relChainsRPairMap_comp (pcHomeoC q)
      ((pcUC q b).comp (pcIncl q b)) hAB hg3 (hg'' := hg4)]
    exact (Work.Serre.CsrSharp.Tools.relChainsRPairMap_congr hmap hg4 hToCMid).symm
  have hcompHom : HomologicalComplex.homologyMap (Work.Serre.collapseMap q b) n
      = HomologicalComplex.homologyMap A n ≫ HomologicalComplex.homologyMap Bm n
        ≫ HomologicalComplex.homologyMap C n := by
    rw [hcomp, HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp]
  haveI := h3
  haveI := h2
  haveI := h1
  rw [hcompHom]
  infer_instance


end

end Work.Stems
