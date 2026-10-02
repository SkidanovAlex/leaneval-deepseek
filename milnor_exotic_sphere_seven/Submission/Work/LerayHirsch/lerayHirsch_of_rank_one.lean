import Mathlib
import Submission.Work.LerayHirsch.LH
import Submission.Work.LerayHirsch.lhEven_of_pullback_bijective
import Submission.Work.LerayHirsch.lhOdd_of_pullback_bijective

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# Leray–Hirsch for the projectivisation of a **line** bundle

`Work.LerayHirsch.LerayHirschFull Z` is the Leray–Hirsch statement
`H^*(P(E);ℤ) ≅ ⊕_{i<m} H^{*-2i}(B;ℤ)` for the projectivisation `π : P(E) → B` of a complex
gluing-data bundle `Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι` of rank `m`.

For `m = 1` — the case required by the rank-one stage of the splitting principle — the statement is
*elementary*: the fibres of `π` are `(ℂ ∖ 0)/ℂˣ`, a single point, so `π : P(E) → B` is a
homeomorphism; hence `π^*` is an isomorphism of cohomology in every degree.  In rank one the
Leray–Hirsch index type `{i : Fin 1 // (i:ℕ) ≤ k}` has a single element `0` and the Leray–Hirsch
map is `π^*` with the degree bookkeeping of `Work.Thom.cohTransport`; so both the even statement
`LerayHirsch Z` and its odd companion `LerayHirschOdd Z` reduce to the bijectivity of `π^*`, which
this file proves.

The route to the bijectivity of `π^*` is:

* **the section `projSec`** `b ↦ [b, e₁]` of `π`, i.e. the projectivisation of the constant model
  vector `e₁ ∈ ℂ¹` (this is `Work.LerayHirsch.fibreOf` of `Punctum.lean`); `π ∘ projSec = id`;
* **rank one: the fibre is a point.**  Two nonzero vectors in the one-dimensional fibre over `b`
  differ by a unit scalar, so any two points of `P(E)` with the same projection are equal
  (`mkProj_eq_of_proj_eq_rank_one`); hence `projSec ∘ π = id`;
* **continuity of `projSec`.**  The naive composite (`mkProj` of the constant model section) is *not*
  continuous for a non-trivial bundle, because `Z.indexAt` may jump; the proof goes through the
  local trivialisation instead: on `Z.baseSet i` the map `projSec` agrees with `mkProj` of the
  continuous local section `b ↦ Z.localTriv i ⁻¹ (b, e₁)` of the *trivialised* bundle, and the
  model-vector section is identified with it by the rank-one proportionality.  Since the open sets
  `Z.baseSet i` cover `B`, this gives global continuity;
* **`CohMap` functoriality** (`Work.Thom.CohMap_comp`, `CohMap_id`): the two identities
  `π ∘ s = id`, `s ∘ π = id` give `CohMap π ≫ CohMap s = 𝟙` and `CohMap s ≫ CohMap π = 𝟙`, so
  `(CohMap (projMap Z) ℤ n).hom` is bijective for every `n`.

The reduction of `LerayHirsch`/`LerayHirschOdd` to the bijectivity of `π^*` is
`Submission/Work/LerayHirsch/lhEven_of_pullback_bijective.lean` and
`Submission/Work/LerayHirsch/lhOdd_of_pullback_bijective.lean`.
-/

namespace Work.LerayHirsch

open Work.TangentClasses Work.Thom CategoryTheory

noncomputable section

variable {B : Type} [TopologicalSpace B] {ι : Type} [Fintype ι]

/-! ## 1. Rank one: the fibre of the projectivisation is a point -/

/-- **Two nonzero vectors of `ℂ¹` differ by a unit scalar.**  This is the only place where the
rank-one hypothesis `m = 1` enters: it makes every nonzero vector a basis of its fibre. -/
theorem exists_units_smul_of_ne_zero (v w : EuclideanSpace ℂ (Fin 1)) (hv : v ≠ 0) (hw : w ≠ 0) :
    ∃ c : ℂˣ, v = (c : ℂ) • w := by
  have hv0 : v 0 ≠ 0 := fun h => hv (by ext i; fin_cases i; simpa using h)
  have hw0 : w 0 ≠ 0 := fun h => hw (by ext i; fin_cases i; simpa using h)
  refine ⟨Units.mk0 (v 0 / w 0) (div_ne_zero hv0 hw0), ?_⟩
  ext i
  fin_cases i
  simp [div_mul_cancel₀ _ hw0]

/-- **The fibre of the projectivisation of a line bundle is a point.**  Two points of `E ∖ 0` over
the same base point differ by a nonzero scalar, hence define the same point of `P(E)`. -/
theorem mkProj_eq_of_proj_eq_rank_one (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι)
    {p q : ↥(zeroComplement (realification Z))} (h : p.1.proj = q.1.proj) :
    mkProj Z p = mkProj Z q := by
  rw [mkProj_eq_iff]
  have hp : (show EuclideanSpace ℂ (Fin 1) from p.1.2) ≠ 0 := p.2
  have hq : (show EuclideanSpace ℂ (Fin 1) from q.1.2) ≠ 0 := q.2
  obtain ⟨c, hc⟩ := exists_units_smul_of_ne_zero _ _ hp hq
  refine ⟨c, ?_⟩
  refine Subtype.ext (Bundle.TotalSpace.ext ?_ ?_)
  · simpa using h.symm
  · show HEq (show EuclideanSpace ℂ (Fin 1) from (smulPunct Z c q).1.2)
      (show EuclideanSpace ℂ (Fin 1) from p.1.2)
    rw [smulPunct_snd]
    exact heq_of_eq hc.symm

/-- **The coordinate changes of a gluing-data bundle are injective**: `Z.coordChange i j b` kills
only `0`, on `Z.baseSet i ∩ Z.baseSet j` (where it is invertible with inverse
`Z.coordChange j i b`).  (Used to see that the local trivialisation of the punctured bundle stays
inside the complement of the zero section.) -/
theorem coordChange_apply_ne_zero {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {B' : Type*} [TopologicalSpace B'] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {ι' : Type*} (Z : VectorBundleCore 𝕜 B' F ι') (i j : ι') {b : B'}
    (hib : b ∈ Z.baseSet i) (hjb : b ∈ Z.baseSet j) {w : F} (hw : w ≠ 0) :
    Z.coordChange i j b w ≠ 0 := by
  intro h
  have h2 : Z.coordChange j i b (Z.coordChange i j b w) = w := by
    have h1 := Z.coordChange_comp (i := i) (j := j) (k := i) b ⟨⟨hib, hjb⟩, hib⟩ w
    rw [Z.coordChange_self i b hib] at h1
    exact h1
  rw [h, map_zero] at h2
  exact hw h2.symm

/-! ## 2. The section `b ↦ [b, e₁]` of `π : P(E) → B` -/

/-- The first basis vector of the model fibre `ℂ¹`. -/
def rankOneE1 : EuclideanSpace ℂ (Fin 1) := EuclideanSpace.single 0 1

theorem rankOneE1_ne_zero : rankOneE1 ≠ 0 := by
  intro h
  have h0 := congrArg (fun v : EuclideanSpace ℂ (Fin 1) => v 0) h
  simp [rankOneE1] at h0

/-- **The tautological section of the projectivisation of a line bundle**: the class of the model
vector `e₁` in the fibre `E_b`.  (`Work.LerayHirsch.fibreOf` `Punctum.lean`.) -/
def projSec (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι) (b : B) : ProjSpace Z :=
  (fibreOf Z b ⟨rankOneE1, rankOneE1_ne_zero⟩).1

/-- `projSec` is a section of the projection: `π ∘ projSec = id`. -/
@[simp] theorem projMap_projSec (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι) (b : B) :
    projMap Z (projSec Z b) = b := rfl

/-- **`projSec` is the inverse of `π`**: it picks the unique point of the (one-point) fibre. -/
theorem projSec_projMap (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι)
    (x : ProjSpace Z) : projSec Z (projMap Z x) = x := by
  obtain ⟨p, rfl⟩ := surjective_mkProj Z x
  show (fibreOf Z (projMap Z (mkProj Z p)) ⟨rankOneE1, rankOneE1_ne_zero⟩).1 = mkProj Z p
  rw [show (fibreOf Z (projMap Z (mkProj Z p)) ⟨rankOneE1, rankOneE1_ne_zero⟩).1
      = mkProj Z (⟨(⟨p.1.proj, rankOneE1⟩ : (realification Z).TotalSpace),
          by rw [mem_zeroComplement]; exact rankOneE1_ne_zero⟩ :
        ↥(zeroComplement (realification Z))) from rfl]
  exact (mkProj_eq_of_proj_eq_rank_one Z (p := p)
    (q := ⟨(⟨p.1.proj, rankOneE1⟩ : (realification Z).TotalSpace),
      by rw [mem_zeroComplement]; exact rankOneE1_ne_zero⟩) rfl).symm

/-! ## 3. Continuity of `projSec`

On the trivialising open set `Z.baseSet i` the section `projSec` agrees with `mkProj` of the
*local* section `b ↦ Z.localTriv i ⁻¹ (b, e₁)`, which is continuous because a trivialisation is a
homeomorphism onto its target; this is enough because the `Z.baseSet i` cover `B`. -/

/-- The local section `b ↦ Z.localTriv i ⁻¹ (b, e₁)` of the punctured total space of `Z`
(a point of `E ∖ 0`). -/
theorem locPt_mem (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι) (i : ι)
    (b : ↥(Z.baseSet i)) :
    (⟨b.1, ((realification Z).localTriv i).symm b.1 rankOneE1⟩ : (realification Z).TotalSpace)
      ∈ zeroComplement (realification Z) := by
  rw [mem_zeroComplement,
    VectorBundleCore.localTriv_symm_apply (realification Z) i (by
      show b.1 ∈ (realification Z).baseSet i
      rw [realification_baseSet]; exact b.2) rankOneE1]
  exact coordChange_apply_ne_zero (realification Z) i ((realification Z).indexAt b.1)
    (by show b.1 ∈ (realification Z).baseSet i; rw [realification_baseSet]; exact b.2)
    ((realification Z).mem_baseSet_at b.1) rankOneE1_ne_zero

/-- The local section of the punctured total space is continuous on `Z.baseSet i`. -/
theorem continuous_locPt_mem (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι) (i : ι) :
    Continuous (fun b : ↥(Z.baseSet i) =>
      (⟨⟨b.1, ((realification Z).localTriv i).symm b.1 rankOneE1⟩,
        locPt_mem Z i b⟩ : ↥(zeroComplement (realification Z)))) := by
  have hg : Continuous (fun b : ↥(Z.baseSet i) =>
      ((b.1, rankOneE1) : B × EuclideanSpace ℂ (Fin 1))) :=
    continuous_subtype_val.prodMk continuous_const
  have hmem : ∀ b : ↥(Z.baseSet i), ((b.1, rankOneE1) : B × EuclideanSpace ℂ (Fin 1))
      ∈ ((realification Z).localTriv i).target := by
    intro b
    rw [Bundle.Trivialization.mem_target]
    show b.1 ∈ (realification Z).baseSet i
    rw [realification_baseSet]; exact b.2
  have h1 : Continuous (fun b : ↥(Z.baseSet i) =>
      (⟨b.1, ((realification Z).localTriv i).symm b.1 rankOneE1⟩ : (realification Z).TotalSpace)) :=
    ((realification Z).localTriv i).continuousOn_symm.comp_continuous hg hmem
  exact h1.subtype_mk (fun b => locPt_mem Z i b)

/-- **`projSec` is continuous on each `Z.baseSet i`.** -/
theorem continuousOn_projSecOn (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι) (i : ι) :
    ContinuousOn (fun b : B => projSec Z b) (Z.baseSet i) := by
  have key : ∀ b : ↥(Z.baseSet i),
      mkProj Z (⟨⟨b.1, ((realification Z).localTriv i).symm b.1 rankOneE1⟩,
        locPt_mem Z i b⟩ : ↥(zeroComplement (realification Z))) = projSec Z b.1 := by
    intro b
    exact mkProj_eq_of_proj_eq_rank_one Z
      (q := ⟨(⟨b.1, rankOneE1⟩ : (realification Z).TotalSpace), by
        rw [mem_zeroComplement]; exact rankOneE1_ne_zero⟩) rfl
  have h : Continuous (fun b : ↥(Z.baseSet i) => projSec Z b.1) :=
    ((continuous_mkProj Z).comp (continuous_locPt_mem Z i)).congr (fun b => key b)
  exact continuousOn_iff_continuous_domRestrict.mpr h

/-- **`projSec` is continuous.**  Every `b` lies in the open set `Z.baseSet (Z.indexAt b)`, on
which the previous lemma gives continuity. -/
theorem continuous_projSec (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι) :
    Continuous (projSec Z) := by
  rw [continuous_iff_continuousAt]
  intro b
  exact (continuousOn_projSecOn Z (Z.indexAt b)).continuousAt
    ((Z.isOpen_baseSet (Z.indexAt b)).mem_nhds (Z.mem_baseSet_at b))

/-! ## 4. `π^*` is bijective in every degree -/

/-- **The projection of a line bundle induces a bijection on cohomology in every degree.**  The
section `projSec` is a continuous two-sided inverse of `π`, so `CohMap π` and `CohMap projSec` are
mutually inverse on cohomology (`Work.Thom.CohMap_comp`). -/
theorem bijective_CohMap_projMap_rank_one (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι)
    (n : ℕ) : Function.Bijective (CohMap (projMap Z) ℤ n).hom := by
  let s : C(B, ProjSpace Z) := ⟨projSec Z, continuous_projSec Z⟩
  have hπs : (projMap Z).comp s = ContinuousMap.id B :=
    ContinuousMap.ext (fun b => by change projMap Z (projSec Z b) = b; simp)
  have hsπ : s.comp (projMap Z) = ContinuousMap.id (ProjSpace Z) :=
    ContinuousMap.ext (fun x => projSec_projMap Z x)
  have key1 : (CohMap (projMap Z) ℤ n) ≫ (CohMap s ℤ n) = 𝟙 (Coh ℤ n B) := by
    rw [← CohMap_comp s (projMap Z) ℤ n, hπs, CohMap_id]
  have key2 : (CohMap s ℤ n) ≫ (CohMap (projMap Z) ℤ n) = 𝟙 (Coh ℤ n (ProjSpace Z)) := by
    rw [← CohMap_comp (projMap Z) s ℤ n, hsπ, CohMap_id]
  have e1 : ∀ x : Coh ℤ n B, (CohMap s ℤ n).hom ((CohMap (projMap Z) ℤ n).hom x) = x := by
    intro x
    have h := congrArg (fun φ : Coh ℤ n B ⟶ Coh ℤ n B => φ.hom) key1
    simp only [ModuleCat.hom_comp, ModuleCat.hom_id, LinearMap.comp_apply, LinearMap.id_apply] at h
    exact LinearMap.congr_fun h x
  have e2 : ∀ y : Coh ℤ n (ProjSpace Z),
      (CohMap (projMap Z) ℤ n).hom ((CohMap s ℤ n).hom y) = y := by
    intro y
    have h := congrArg (fun φ : Coh ℤ n (ProjSpace Z) ⟶
      Coh ℤ n (ProjSpace Z) => φ.hom) key2
    simp only [ModuleCat.hom_comp, ModuleCat.hom_id, LinearMap.comp_apply, LinearMap.id_apply] at h
    exact LinearMap.congr_fun h y
  refine ⟨fun x y hxy => ?_, fun y => ⟨(CohMap s ℤ n).hom y, e2 y⟩⟩
  have hx := e1 x
  have hy := e1 y
  rw [hxy] at hx
  exact hx.symm.trans hy

/-! ## 5. Leray–Hirsch in rank one -/

theorem lerayHirsch_of_rank_one {B : Type} [TopologicalSpace B] {ι : Type} [Fintype ι]
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι) :
    Work.LerayHirsch.LerayHirschFull Z :=
  ⟨lhEven_of_pullback_bijective Z (bijective_CohMap_projMap_rank_one Z),
   lhOdd_of_pullback_bijective Z (bijective_CohMap_projMap_rank_one Z)⟩

end

end Work.LerayHirsch
