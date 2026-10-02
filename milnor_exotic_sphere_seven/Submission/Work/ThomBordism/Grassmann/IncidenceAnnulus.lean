import Mathlib
import Submission.Work.ThomBordism.Grassmann.IncidenceTriv

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-!
# Radial homotopy equivalence between the open annulus and the punctured space

For `r ≥ 1` the open annulus `A^r = {x : ℝ^r | 1 < ‖x‖ < 3}` is homotopy equivalent to the
punctured space `ℝ^r ∖ 0`, by the radial retraction `x ↦ (2/‖x‖) • x` and the radial homotopy
`x ↦ ((1-t)·(2/‖x‖) + t) • x`, which runs from the retraction (`t = 0`) to the identity (`t = 1`).

Consequently `π^* : Hʲ(Y) → Hʲ(Y × A^r)` is bijective whenever `j + 2 ≤ r`
(`annulusPuncturedCohomology`): the projection of `Y × A^r` factors through the projection of
`Y × (ℝ^r∖0)`, whose pullback is bijective by `trivPuncturedCohomology`, and the inclusion
`Y × A^r ↪ Y × (ℝ^r∖0)` is a homotopy equivalence.
-/

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial Topology
open unitInterval

namespace Work.ThomBordism.Grassmann

noncomputable section

open Work.Cohomology

/-- The open annulus `{x : ℝ^r | 1 < ‖x‖ ∧ ‖x‖ < 3}`. -/
def annSet (r : ℕ) : Set (EuclideanSpace ℝ (Fin r)) := {x | 1 < ‖x‖ ∧ ‖x‖ < 3}

/-- The punctured space `ℝ^r ∖ 0`. -/
def puncSet (r : ℕ) : Set (EuclideanSpace ℝ (Fin r)) := {x | x ≠ 0}

/-- The open annulus. -/
abbrev Ann (r : ℕ) : Type := ↥(annSet r)

/-- The punctured space. -/
abbrev Punc (r : ℕ) : Type := ↥(puncSet r)

/-- The radial retraction of the punctured space onto the sphere of radius `2`. -/
def radRetr (r : ℕ) (x : Punc r) : EuclideanSpace ℝ (Fin r) := (2 / ‖x.1‖) • x.1

/-- The inclusion of the annulus in the punctured space. -/
def annIncl (r : ℕ) (x : Ann r) : EuclideanSpace ℝ (Fin r) := x.1

/-- The coefficient of the radial homotopy. -/
def radCoef (r : ℕ) (t : ℝ) (x : EuclideanSpace ℝ (Fin r)) : ℝ :=
  (1 - t) * (2 / ‖x‖) + t

/-- The radial path. -/
def radPath (r : ℕ) (t : ℝ) (x : EuclideanSpace ℝ (Fin r)) : EuclideanSpace ℝ (Fin r) :=
  radCoef r t x • x

theorem radCoef_nonneg (r : ℕ) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (x : EuclideanSpace ℝ (Fin r)) (hx0 : (0 : ℝ) < ‖x‖) : 0 ≤ radCoef r t x := by
  have h2 : (0 : ℝ) ≤ 2 / ‖x‖ := by positivity
  rw [radCoef]
  exact add_nonneg (mul_nonneg (by linarith) h2) ht0

theorem norm_radPath (r : ℕ) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (x : EuclideanSpace ℝ (Fin r)) (hx0 : (0 : ℝ) < ‖x‖) :
    ‖radPath r t x‖ = 2 * (1 - t) + t * ‖x‖ := by
  rw [radPath, norm_smul, Real.norm_eq_abs, abs_of_nonneg (radCoef_nonneg r t ht0 ht1 x hx0),
    radCoef, add_mul, mul_assoc, div_mul_cancel₀ _ (ne_of_gt hx0)]
  ring

theorem punc_norm_pos (r : ℕ) (x : Punc r) : (0 : ℝ) < ‖x.1‖ := norm_pos_iff.mpr x.2

theorem ann_norm_pos (r : ℕ) (x : Ann r) : (0 : ℝ) < ‖x.1‖ := by
  have h := x.2.1
  linarith

theorem radRetr_mem (r : ℕ) (x : Punc r) : radRetr r x ∈ annSet r := by
  have hx : (0 : ℝ) < ‖x.1‖ := punc_norm_pos r x
  have hnorm : ‖radRetr r x‖ = 2 := by
    rw [radRetr, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity),
      div_mul_cancel₀ _ (ne_of_gt hx)]
  rw [annSet, Set.mem_setOf_eq, hnorm]
  norm_num

theorem annIncl_mem (r : ℕ) (x : Ann r) : annIncl r x ∈ puncSet r := by
  intro h0
  have h : 1 < ‖annIncl r x‖ := x.2.1
  rw [h0, norm_zero] at h
  linarith

theorem radPath_mem_ann (r : ℕ) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (x : Ann r) :
    radPath r t x.1 ∈ annSet r := by
  have h1 := x.2.1
  have h3 := x.2.2
  have hn := norm_radPath r t ht0 ht1 x.1 (ann_norm_pos r x)
  have hp : (0 : ℝ) < (1 - t) + t * (‖x.1‖ - 1) := by
    rcases eq_or_lt_of_le ht1 with h | h
    · rw [h]; linarith
    · have : (0 : ℝ) ≤ t * (‖x.1‖ - 1) := mul_nonneg ht0 (by linarith)
      linarith
  have hp3 : (0 : ℝ) < (1 - t) + t * (3 - ‖x.1‖) := by
    rcases eq_or_lt_of_le ht1 with h | h
    · rw [h]; linarith
    · have : (0 : ℝ) ≤ t * (3 - ‖x.1‖) := mul_nonneg ht0 (by linarith)
      linarith
  constructor
  · rw [hn, show 2 * (1 - t) + t * ‖x.1‖ = 1 + ((1 - t) + t * (‖x.1‖ - 1)) from by ring]
    linarith
  · rw [hn, show 2 * (1 - t) + t * ‖x.1‖
        = 3 - ((1 - t) + t * (3 - ‖x.1‖)) from by ring]
    linarith

theorem radPath_mem_punc (r : ℕ) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (x : Punc r) :
    radPath r t x.1 ∈ puncSet r := by
  have hx0 : (0 : ℝ) < ‖x.1‖ := punc_norm_pos r x
  intro h0
  have hn := norm_radPath r t ht0 ht1 x.1 hx0
  have h1 : ‖radPath r t x.1‖ = 0 := by rw [h0, norm_zero]
  rw [hn] at h1
  have hpos : (0 : ℝ) < 2 * (1 - t) + t * ‖x.1‖ := by
    rcases eq_or_lt_of_le ht1 with h | h
    · rw [h]; linarith
    · have : (0 : ℝ) ≤ t * ‖x.1‖ := mul_nonneg ht0 (le_of_lt hx0)
      linarith
  linarith

/-! ## Continuity -/

theorem continuous_radCoef_punc (r : ℕ) :
    Continuous fun q : I × Punc r => radCoef r (q.1 : ℝ) q.2.1 := by
  have h2 : Continuous fun q : I × Punc r => (2 : ℝ) / ‖q.2.1‖ :=
    continuous_const.div ((continuous_subtype_val.comp continuous_snd).norm)
      (fun q => ne_of_gt (punc_norm_pos r q.2))
  have ht : Continuous fun q : I × Punc r => (q.1 : ℝ) :=
    continuous_subtype_val.comp continuous_fst
  exact (continuous_const.sub ht).mul h2 |>.add ht

theorem continuous_radCoef_ann (r : ℕ) :
    Continuous fun q : I × Ann r => radCoef r (q.1 : ℝ) q.2.1 := by
  have h2 : Continuous fun q : I × Ann r => (2 : ℝ) / ‖q.2.1‖ :=
    continuous_const.div ((continuous_subtype_val.comp continuous_snd).norm)
      (fun q => ne_of_gt (ann_norm_pos r q.2))
  have ht : Continuous fun q : I × Ann r => (q.1 : ℝ) :=
    continuous_subtype_val.comp continuous_fst
  exact (continuous_const.sub ht).mul h2 |>.add ht

theorem continuous_radRetr (r : ℕ) :
    Continuous fun x : Punc r => (⟨radRetr r x, radRetr_mem r x⟩ : Ann r) := by
  refine Continuous.subtype_mk ?_ _
  have hx : Continuous fun x : Punc r => ‖x.1‖ := continuous_subtype_val.norm
  have h2 : Continuous fun x : Punc r => (2 : ℝ) / ‖x.1‖ :=
    continuous_const.div hx (fun x => ne_of_gt (punc_norm_pos r x))
  exact h2.smul continuous_subtype_val

theorem continuous_annIncl (r : ℕ) :
    Continuous fun x : Ann r => (⟨annIncl r x, annIncl_mem r x⟩ : Punc r) :=
  Continuous.subtype_mk continuous_subtype_val _

theorem continuous_radPath_ann (r : ℕ) :
    Continuous fun q : I × Ann r => (⟨radPath r (q.1 : ℝ) q.2.1, radPath_mem_ann r (q.1 : ℝ)
      q.1.2.1 q.1.2.2 q.2⟩ : Ann r) :=
  Continuous.subtype_mk ((continuous_radCoef_ann r).smul
    (continuous_subtype_val.comp continuous_snd)) _

theorem continuous_radPath_punc (r : ℕ) :
    Continuous fun q : I × Punc r => (⟨radPath r (q.1 : ℝ) q.2.1, radPath_mem_punc r (q.1 : ℝ)
      q.1.2.1 q.1.2.2 q.2⟩ : Punc r) :=
  Continuous.subtype_mk ((continuous_radCoef_punc r).smul
    (continuous_subtype_val.comp continuous_snd)) _

/-! ## The homotopy equivalences -/

/-- The inclusion of the annulus in the punctured space, as a continuous map. -/
noncomputable def annInclC (r : ℕ) : C(Ann r, Punc r) :=
  ⟨fun x => ⟨annIncl r x, annIncl_mem r x⟩, continuous_annIncl r⟩

/-- The radial retraction, as a continuous map. -/
noncomputable def radRetrC (r : ℕ) : C(Punc r, Ann r) :=
  ⟨fun x => ⟨radRetr r x, radRetr_mem r x⟩, continuous_radRetr r⟩

/-- The radial homotopy from `radRetr ∘ annIncl` to the identity of the annulus. -/
noncomputable def homotopyAnn (r : ℕ) :
    ContinuousMap.Homotopy (X := Ann r) (Y := Ann r)
      ((radRetrC r).comp (annInclC r)) (ContinuousMap.id (Ann r)) where
  toFun q := ⟨radPath r (q.1 : ℝ) q.2.1, radPath_mem_ann r (q.1 : ℝ) q.1.2.1 q.1.2.2 q.2⟩
  continuous_toFun := continuous_radPath_ann r
  map_zero_left x := Subtype.ext (by
    show radPath r ((0 : I) : ℝ) x.1 = radRetr r ⟨annIncl r x, annIncl_mem r x⟩
    simp [radPath, radCoef, radRetr, annIncl])
  map_one_left x := Subtype.ext (by
    show radPath r ((1 : I) : ℝ) x.1 = x.1
    simp [radPath, radCoef])

/-- The radial homotopy from `annIncl ∘ radRetr` to the identity of the punctured space. -/
noncomputable def homotopyPunc (r : ℕ) :
    ContinuousMap.Homotopy (X := Punc r) (Y := Punc r)
      ((annInclC r).comp (radRetrC r)) (ContinuousMap.id (Punc r)) where
  toFun q := ⟨radPath r (q.1 : ℝ) q.2.1, radPath_mem_punc r (q.1 : ℝ) q.1.2.1 q.1.2.2 q.2⟩
  continuous_toFun := continuous_radPath_punc r
  map_zero_left x := Subtype.ext (by
    show radPath r ((0 : I) : ℝ) x.1 = radRetr r x
    rw [radPath, radCoef, radRetr]
    norm_num)
  map_one_left x := Subtype.ext (by
    show radPath r ((1 : I) : ℝ) x.1 = x.1
    simp [radPath, radCoef])

/-- **The open annulus is homotopy equivalent to the punctured space.** -/
theorem nonempty_homotopyEquiv_annulus_punctured (r : ℕ) :
    Nonempty (ContinuousMap.HomotopyEquiv (Ann r) (Punc r)) :=
  ⟨ContinuousMap.HomotopyEquiv.mk (annInclC r) (radRetrC r)
    ⟨homotopyAnn r⟩ ⟨homotopyPunc r⟩⟩

/-! ## The product with an arbitrary space -/

/-- The inclusion `Y × A^r → Y × (ℝ^r∖0)`. -/
noncomputable def prodIncl (r : ℕ) (Y : Type) [TopologicalSpace Y] :
    C(Y × Ann r, Y × Punc r) :=
  ⟨fun p => (p.1, ⟨annIncl r p.2, annIncl_mem r p.2⟩),
    continuous_fst.prodMk ((continuous_annIncl r).comp continuous_snd)⟩

/-- The radial retraction `Y × (ℝ^r∖0) → Y × A^r`. -/
noncomputable def prodRetr (r : ℕ) (Y : Type) [TopologicalSpace Y] :
    C(Y × Punc r, Y × Ann r) :=
  ⟨fun p => (p.1, ⟨radRetr r p.2, radRetr_mem r p.2⟩),
    continuous_fst.prodMk ((continuous_radRetr r).comp continuous_snd)⟩

/-- The underlying function of the product homotopy towards the annulus. -/
noncomputable def prodHomFnAnn (r : ℕ) (Y : Type) [TopologicalSpace Y]
    (q : I × (Y × Ann r)) : Y × Ann r :=
  (q.2.1, ⟨radPath r (q.1 : ℝ) q.2.2.1,
    radPath_mem_ann r (q.1 : ℝ) q.1.2.1 q.1.2.2 q.2.2⟩)

/-- The underlying function of the product homotopy towards the punctured space. -/
noncomputable def prodHomFnPunc (r : ℕ) (Y : Type) [TopologicalSpace Y]
    (q : I × (Y × Punc r)) : Y × Punc r :=
  (q.2.1, ⟨radPath r (q.1 : ℝ) q.2.2.1,
    radPath_mem_punc r (q.1 : ℝ) q.1.2.1 q.1.2.2 q.2.2⟩)

theorem continuous_prodHomAnn (r : ℕ) (Y : Type) [TopologicalSpace Y] :
    Continuous (prodHomFnAnn r Y) := by
  have h1 : Continuous fun q : I × (Y × Ann r) => q.2.1 :=
    continuous_fst.comp continuous_snd
  have h2 : Continuous fun q : I × (Y × Ann r) =>
      (⟨radPath r (q.1 : ℝ) q.2.2.1, radPath_mem_ann r (q.1 : ℝ) q.1.2.1 q.1.2.2
        q.2.2⟩ : Ann r) :=
    (continuous_radPath_ann r).comp
      (continuous_fst.prodMk (continuous_snd.comp continuous_snd))
  exact h1.prodMk h2

theorem continuous_prodHomPunc (r : ℕ) (Y : Type) [TopologicalSpace Y] :
    Continuous (prodHomFnPunc r Y) := by
  have h1 : Continuous fun q : I × (Y × Punc r) => q.2.1 :=
    continuous_fst.comp continuous_snd
  have h2 : Continuous fun q : I × (Y × Punc r) =>
      (⟨radPath r (q.1 : ℝ) q.2.2.1, radPath_mem_punc r (q.1 : ℝ) q.1.2.1 q.1.2.2
        q.2.2⟩ : Punc r) :=
    (continuous_radPath_punc r).comp
      (continuous_fst.prodMk (continuous_snd.comp continuous_snd))
  exact h1.prodMk h2

/-- The radial homotopy on the product, towards the annulus. -/
noncomputable def homotopyProdAnn (r : ℕ) (Y : Type) [TopologicalSpace Y] :
    ContinuousMap.Homotopy (X := Y × Ann r) (Y := Y × Ann r)
      (((prodRetr r Y).comp (prodIncl r Y) : C(Y × Ann r, Y × Ann r)))
      (ContinuousMap.id (Y × Ann r)) where
  toFun := prodHomFnAnn r Y
  continuous_toFun := continuous_prodHomAnn r Y
  map_zero_left x := Prod.ext rfl (Subtype.ext (by
    show radPath r ((0 : I) : ℝ) x.2.1 = radRetr r ⟨annIncl r x.2, annIncl_mem r x.2⟩
    simp [radPath, radCoef, radRetr, annIncl, prodIncl, prodRetr]))
  map_one_left x := Prod.ext rfl (Subtype.ext (by
    show radPath r ((1 : I) : ℝ) x.2.1 = x.2.1
    simp [radPath, radCoef, prodIncl, prodRetr]))

/-- The radial homotopy on the product, towards the punctured space. -/
noncomputable def homotopyProdPunc (r : ℕ) (Y : Type) [TopologicalSpace Y] :
    ContinuousMap.Homotopy (X := Y × Punc r) (Y := Y × Punc r)
      (((prodIncl r Y).comp (prodRetr r Y) : C(Y × Punc r, Y × Punc r)))
      (ContinuousMap.id (Y × Punc r)) where
  toFun := prodHomFnPunc r Y
  continuous_toFun := continuous_prodHomPunc r Y
  map_zero_left x := Prod.ext rfl (Subtype.ext (by
    show radPath r ((0 : I) : ℝ) x.2.1 = radRetr r x.2
    simp [radPath, radCoef, radRetr, prodIncl, prodRetr]))
  map_one_left x := Prod.ext rfl (Subtype.ext (by
    show radPath r ((1 : I) : ℝ) x.2.1 = x.2.1
    simp [radPath, radCoef, prodIncl, prodRetr]))

/-- **The product `Y × A^r` is homotopy equivalent to `Y × (ℝ^r∖0)`.** -/
noncomputable def prodHomotopyEquiv (r : ℕ) (Y : Type) [TopologicalSpace Y] :
    ContinuousMap.HomotopyEquiv (Y × Ann r) (Y × Punc r) :=
  ContinuousMap.HomotopyEquiv.mk (prodIncl r Y) (prodRetr r Y)
    ⟨homotopyProdAnn r Y⟩ ⟨homotopyProdPunc r Y⟩

theorem nonempty_homotopyEquiv_prod (r : ℕ) (Y : Type) [TopologicalSpace Y] :
    Nonempty (ContinuousMap.HomotopyEquiv (Y × Ann r) (Y × Punc r)) :=
  ⟨prodHomotopyEquiv r Y⟩

/-- **The projection of `Y × A^r` is a cohomology isomorphism** in degrees `j + 2 ≤ r`. -/
theorem annulusPuncturedCohomology (r j : ℕ) (hj : j + 2 ≤ r) (Y : Type) [TopologicalSpace Y] :
    Function.Bijective ((Work.Cohomology.singularCohomologyMap ℤ
      (TopCat.of (Y × Ann r)) (TopCat.of Y)
      (TopCat.ofHom ⟨fun p => p.1, continuous_fst⟩) j).hom) := by
  let e := prodHomotopyEquiv r Y
  let fC : C(Y × Ann r, Y × Punc r) := e.toFun
  let pfC : C(Y × Punc r, Y) := ⟨fun p => p.1, continuous_fst⟩
  let paC : C(Y × Ann r, Y) := ⟨fun p => p.1, continuous_fst⟩
  let f : TopCat.of (Y × Ann r) ⟶ TopCat.of (Y × Punc r) := TopCat.ofHom fC
  let g : TopCat.of (Y × Punc r) ⟶ TopCat.of (Y × Ann r) := TopCat.ofHom e.invFun
  have h1 : TopCat.Homotopy (f ≫ g) (𝟙 (TopCat.of (Y × Ann r))) := e.left_inv.some
  have h2 : TopCat.Homotopy (g ≫ f) (𝟙 (TopCat.of (Y × Punc r))) := e.right_inv.some
  have hiso : IsIso (Work.Cohomology.singularCohomologyMap ℤ
      (TopCat.of (Y × Ann r)) (TopCat.of (Y × Punc r)) f j) :=
    Work.Cohomology.homotopyEquiv ℤ _ _ f g h1 h2 j
  have hf : Function.Bijective ((Work.Cohomology.singularCohomologyMap ℤ
      (TopCat.of (Y × Ann r)) (TopCat.of (Y × Punc r)) f j).hom) :=
    bijective_of_isIso_moduleCat _
  have hp : Function.Bijective ((Work.Cohomology.singularCohomologyMap ℤ
      (TopCat.of (Y × Punc r)) (TopCat.of Y) (TopCat.ofHom pfC) j).hom) := by
    show Function.Bijective ((Work.Cohomology.singularCohomologyMap ℤ
      (TopCat.of (Y × Punc r)) (TopCat.of Y)
      (TopCat.ofHom ⟨fun p : Y × Punc r => p.1, continuous_fst⟩) j).hom)
    exact trivPuncturedCohomology r j hj Y
  have hcm : paC = pfC.comp fC := by
    apply ContinuousMap.ext
    intro p
    rfl
  have hcomp : (Work.Cohomology.singularCohomologyMap ℤ (TopCat.of (Y × Ann r)) (TopCat.of Y)
        (TopCat.ofHom paC) j)
      = (Work.Cohomology.singularCohomologyMap ℤ (TopCat.of (Y × Punc r)) (TopCat.of Y)
          (TopCat.ofHom pfC) j) ≫
        (Work.Cohomology.singularCohomologyMap ℤ (TopCat.of (Y × Ann r))
          (TopCat.of (Y × Punc r)) f j) := by
    rw [hcm, show TopCat.ofHom (pfC.comp fC) = f ≫ TopCat.ofHom pfC from rfl]
    exact Work.Cohomology.singularCohomologyMap_comp (R := ℤ) f (TopCat.ofHom pfC) j
  show Function.Bijective ((Work.Cohomology.singularCohomologyMap ℤ (TopCat.of (Y × Ann r))
    (TopCat.of Y) (TopCat.ofHom paC) j).hom)
  rw [hcomp, ModuleCat.hom_comp]
  exact ⟨fun x y hxy => hp.1 (hf.1 hxy), fun z => by
    obtain ⟨w, hw⟩ := hf.2 z
    obtain ⟨v, hv⟩ := hp.2 w
    exact ⟨v, by rw [LinearMap.comp_apply, hv, hw]⟩⟩

end

end Work.ThomBordism.Grassmann
