/-
# The layer-direction chart of the collar is an open embedding

`layerPtSq z = z.2 • bndOfU z.1` is the layer-direction chart of the collar: it sends the pair
(perimeter parameter `u`, layer parameter `t`) of the rectangle `(0,1) × (1/2,1]` to the point of the
filling square `Sq` on the boundary circle of radius `t` at perimeter parameter `u`.

The proof goes through the *up-collar* domain `(0,1) × (1/2,∞)`, on which the same formula is an
open embedding **into the plane**:

  `layerPtUp : (0,1) × (1/2,∞) → ℝ²`,  `layerPtUp (u,t) = t • bndOfU u`.

Indeed `layerPtUp = scal ∘ (BarS ∘ mod) × id` where

* `BarS : ℝ/ℤ → ∂Sq` is the homeomorphism `θ ↦ bndOfU θ` (a continuous bijection from the compact
  circle onto the closed boundary circle of the square);
* `mod : (0,1) → ℝ/ℤ` is the restriction of the quotient map, an open embedding (`(0,1) ≅ ℝ/ℤ∖{0}`);
* `scal : (1/2,∞) × ∂Sq → ℝ²∖{0}`, `scal(b,q) = b • q`, is a homeomorphism onto the open set
  `{p | 1/2 < ‖p‖∞}`.

Then `layerPtSq` is the corestriction of the restriction of `layerPtUp` to
`collarLayerDom = (0,1) × (1/2,1]`; the range is `{1/2 < ‖·‖∞} ∖ {(t,t) | 1/2 < t ≤ 1}`, which is
open in the square because its complement is closed.
-/
import Mathlib
import Submission.Work.Cusp.CuspChartAux
import Submission.Work.Cusp.bndOfU_add_int
import Submission.Work.Cusp.nrm_bnd
import Submission.Work.Cusp.nrm_smul
import Submission.Work.Cusp.nrm_continuous
import Submission.Work.Cusp.smul_bnd

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open Set Topology Function
open scoped Real InnerProductSpace

namespace Work.Cusp

/-! ### Continuity of `bndOfU`

`bndOfU u = F (Int.fract u)` for the four-branched piecewise affine function `F` whose branches
agree at the corners of `Sq`; `ContinuousOn.comp_fract''` glues them. -/

private def bF1 (s : ℝ) : E2 := !₂[(1 : ℝ), 1 - 8 * s]
private def bF2 (s : ℝ) : E2 := !₂[3 - 8 * s, (-1 : ℝ)]
private def bF3 (s : ℝ) : E2 := !₂[(-1 : ℝ), 8 * s - 5]
private def bF4 (s : ℝ) : E2 := !₂[8 * s - 7, (1 : ℝ)]
private def bG3 (s : ℝ) : E2 := if s < 3 / 4 then bF3 s else bF4 s
private def bG2 (s : ℝ) : E2 := if s < 1 / 2 then bF2 s else bG3 s
private def bG1 (s : ℝ) : E2 := if s < 1 / 4 then bF1 s else bG2 s

private lemma bG1_zero_eq_one : bG1 0 = bG1 1 := by
  simp only [bG1, bG2, bG3, bF1, bF4]
  norm_num

private lemma bG1_cont : Continuous bG1 := by
  have h3 : Continuous bG3 := by
    unfold bG3
    refine Continuous.if ?_ ?_ ?_
    · intro s hs
      have hs' : s ∈ frontier (Set.Iio (3 / 4 : ℝ)) := hs
      rw [frontier_Iio] at hs'
      simp only [Set.mem_singleton_iff] at hs'
      subst hs'
      simp only [bF3, bF4]
      norm_num
    · unfold bF3; fun_prop
    · unfold bF4; fun_prop
  have h2 : Continuous bG2 := by
    unfold bG2
    refine Continuous.if ?_ ?_ h3
    · intro s hs
      have hs' : s ∈ frontier (Set.Iio (1 / 2 : ℝ)) := hs
      rw [frontier_Iio] at hs'
      simp only [Set.mem_singleton_iff] at hs'
      subst hs'
      simp only [bF2]
      rw [show bG3 (1 / 2) = bF3 (1 / 2) from by
        simp only [bG3]
        rw [ite_eq_left (by norm_num : (1 : ℝ) / 2 < 3 / 4)]]
      simp only [bF3]
      norm_num
    · unfold bF2; fun_prop
  unfold bG1
  refine Continuous.if ?_ ?_ h2
  · intro s hs
    have hs' : s ∈ frontier (Set.Iio (1 / 4 : ℝ)) := hs
    rw [frontier_Iio] at hs'
    simp only [Set.mem_singleton_iff] at hs'
    subst hs'
    simp only [bF1]
    rw [show bG2 (1 / 4) = bF2 (1 / 4) from by
      simp only [bG2]
      rw [ite_eq_left (by norm_num : (1 : ℝ) / 4 < 1 / 2)]]
    simp only [bF2]
    norm_num
  · unfold bF1; fun_prop

private lemma bndOfU_eq : bndOfU = bG1 ∘ Int.fract := rfl

/-- **`bndOfU` is continuous**: it is the `1`-periodic function obtained by gluing the four
piecewise affine parametrisations of the edges of the square. -/
theorem continuous_bndOfU : Continuous (bndOfU : ℝ → E2) := by
  have h : Continuous (bG1 ∘ Int.fract) :=
    ContinuousOn.comp_fract'' (f := bG1) bG1_cont.continuousOn bG1_zero_eq_one
  rwa [bndOfU_eq]

/-! ### The up-collar domain and the plane-level chart -/

/-- The perimeter interval `(0,1) = (0, 0+1)`, written so as to agree definitionally with the
source of the quotient homeomorphism `AddCircle.openPartialHomeomorphCoe 1 0`. -/
def collarI : Set ℝ := Set.Ioo (0:ℝ) (0+1)

/-- The layer interval `(1/2,∞)`. -/
def collarJ : Set ℝ := Set.Ioi (1/2 : ℝ)

/-- `(0,1) × (1/2,∞)`: the domain on which the layer chart is an open embedding into the plane. -/
def collarUpDom : Set (ℝ × ℝ) := collarI ×ˢ collarJ

theorem collarLayerDom_subset_collarUpDom : collarLayerDom ⊆ collarUpDom := by
  rintro z ⟨h1, h2, h3, -⟩
  exact ⟨⟨h1, by linarith⟩, h3⟩

/-- **The plane-level layer chart**: `(u,t) ↦ t • bndOfU u` on the up-collar domain. -/
def layerPtUp (z : {z : ℝ × ℝ // z ∈ collarUpDom}) : E2 := z.1.2 • bndOfU z.1.1

/-! ### The boundary circle `∂Sq = {q | nrm q = 1}` as a quotient of `ℝ/ℤ` -/

/-- The boundary `∂Sq = {q | nrm q = 1}` of the square. -/
def Sph : Set E2 := {q | nrm q = 1}

/-- The continuous lift `ℝ/ℤ → E2` of `bndOfU`. -/
def Bar : AddCircle (1:ℝ) → E2 := AddCircle.liftIco (1:ℝ) (0:ℝ) bndOfU

theorem Bar_coe' (x : ℝ) (hx : x ∈ Set.Ico (0:ℝ) (0+1)) : Bar (x : AddCircle (1:ℝ)) = bndOfU x :=
  AddCircle.liftIco_coe_apply hx

/-- The representative in `[0,1)` of a point of the circle. -/
def uRep (θ : AddCircle (1:ℝ)) : ℝ :=
  (((AddCircle.equivIco (1:ℝ) (0:ℝ) θ : Set.Ico (0:ℝ) (0+1))) : ℝ)

theorem uRep_mem (θ : AddCircle (1:ℝ)) : uRep θ ∈ Set.Ico (0:ℝ) (0+1) :=
  (AddCircle.equivIco (1:ℝ) (0:ℝ) θ).2

theorem uRep_coe (θ : AddCircle (1:ℝ)) : ((uRep θ : ℝ) : AddCircle (1:ℝ)) = θ :=
  AddCircle.coe_equivIco

theorem Bar_uRep (θ : AddCircle (1:ℝ)) : Bar θ = bndOfU (uRep θ) :=
  (congrArg Bar (uRep_coe θ).symm).trans (Bar_coe' _ (uRep_mem θ))

theorem Bar_mem (θ : AddCircle (1:ℝ)) : nrm (Bar θ) = 1 := by
  rw [Bar_uRep]; exact nrm_bndOfU _

/-- The homeomorphism `ℝ/ℤ → ∂Sq`, `θ ↦ bndOfU θ`. -/
def BarS (θ : AddCircle (1:ℝ)) : Sph := ⟨Bar θ, Bar_mem θ⟩

theorem BarS_inj : Injective BarS := by
  intro θ θ' h
  have h2 : Bar θ = Bar θ' := congrArg Subtype.val h
  have hb : bndOfU (uRep θ) = bndOfU (uRep θ') := by rwa [Bar_uRep, Bar_uRep] at h2
  have hfr : Int.fract (uRep θ) = Int.fract (uRep θ') := by
    rw [← uPerim_bndOfU, ← uPerim_bndOfU, hb]
  have e1 : uRep θ = Int.fract (uRep θ) :=
    (Int.fract_eq_self.mpr ⟨(uRep_mem θ).1, by linarith [(uRep_mem θ).2]⟩).symm
  have e2 : uRep θ' = Int.fract (uRep θ') :=
    (Int.fract_eq_self.mpr ⟨(uRep_mem θ').1, by linarith [(uRep_mem θ').2]⟩).symm
  calc θ = ((uRep θ : ℝ) : AddCircle (1:ℝ)) := (uRep_coe θ).symm
    _ = ((uRep θ' : ℝ) : AddCircle (1:ℝ)) := by rw [e1, e2, hfr]
    _ = θ' := uRep_coe θ'

theorem BarS_surj : Surjective BarS := by
  intro q
  refine ⟨(uPerim q.1 : ℝ), ?_⟩
  apply Subtype.ext
  show Bar (↑(uPerim q.1)) = q.1
  rw [Bar_coe' _ (show uPerim q.1 ∈ Set.Ico (0:ℝ) (0+1) from
    ⟨(uPerim_mem q.2).1, by linarith [(uPerim_mem q.2).2]⟩)]
  exact nrmu_bndOfU_uPerim q.2

/-- **The homeomorphism `ℝ/ℤ → ∂Sq`**: `bndOfU` is continuous and bijective, the circle is compact
and the boundary circle of the square is Hausdorff. -/
theorem isOpenEmbedding_barS : IsOpenEmbedding BarS := by
  have hzero : bndOfU 0 = bndOfU (1:ℝ) := by
    simpa using (bndOfU_add_int (0:ℝ) 1).symm
  have hBarc : Continuous Bar := AddCircle.liftIco_zero_continuous hzero continuous_bndOfU.continuousOn
  have hBarSc : Continuous BarS := Continuous.subtype_mk hBarc Bar_mem
  have hb : Bijective BarS := ⟨BarS_inj, BarS_surj⟩
  have hh : IsHomeomorph BarS := isHomeomorph_iff_continuous_bijective.mpr ⟨hBarSc, hb⟩
  exact IsEmbedding.isOpenEmbedding_of_surjective ⟨hh.isInducing, hh.injective⟩ hh.surjective

/-! ### The open embedding `(0,1) → ℝ/ℤ` -/

/-- The restriction of the quotient map `ℝ → ℝ/ℤ` to `(0,1)` is an open embedding onto
`ℝ/ℤ ∖ {0}`. -/
theorem isOpenEmbedding_modCircle :
    IsOpenEmbedding (fun a : ↥collarI => (a.1 : AddCircle (1:ℝ))) := by
  have h := (AddCircle.openPartialHomeomorphCoe (1:ℝ) (0:ℝ)).isOpenEmbedding_restrict
  have hfun : ((AddCircle.openPartialHomeomorphCoe (1:ℝ) (0:ℝ)).source.domRestrict
        ↑(AddCircle.openPartialHomeomorphCoe (1:ℝ) (0:ℝ)))
      = fun a : ↥collarI => (a.1 : AddCircle (1:ℝ)) := by
    funext a
    rw [Set.domRestrict_apply]
    rfl
  rwa [hfun] at h

/-! ### The scaling map `(1/2,∞) × ∂Sq → ℝ²`, `(b,q) ↦ b • q` -/

/-- **Scaling the boundary circle of the square is an open embedding into the plane**, with range
`{p | 1/2 < ‖p‖∞}`. -/
theorem isOpenEmbedding_smulSph :
    IsOpenEmbedding (fun z : {b : ℝ // 1/2 < b} × {q : E2 // nrm q = 1} => z.1.1 • z.2.1) := by
  set T : Set E2 := {p | 1/2 < nrm p} with hT
  have hTopen : IsOpen T := isOpen_lt continuous_const nrm_continuous
  have hmem : ∀ z : {b : ℝ // 1/2 < b} × {q : E2 // nrm q = 1}, z.1.1 • z.2.1 ∈ T := by
    rintro ⟨b, q⟩
    rw [hT, Set.mem_ofPred_eq, nrm_smul, q.2, mul_one, abs_of_pos (lt_trans (by norm_num) b.2)]
    exact b.2
  have hne : ∀ p : T, p.1 ≠ 0 := by
    intro p h
    have h2 : (1:ℝ)/2 < nrm p.1 := p.2
    rw [h, show nrm (0 : E2) = 0 from by simp [nrm]] at h2
    norm_num at h2
  let e : {b : ℝ // 1/2 < b} × {q : E2 // nrm q = 1} ≃ T :=
    { toFun := fun z => ⟨z.1.1 • z.2.1, hmem z⟩
      invFun := fun p => (⟨nrm p.1, p.2⟩, ⟨bnd p.1, nrm_bnd (hne p)⟩)
      left_inv := by
        rintro ⟨b, q⟩
        apply Prod.ext
        · apply Subtype.ext
          show nrm (b.1 • q.1) = b.1
          rw [nrm_smul, q.2, mul_one, abs_of_pos (lt_trans (by norm_num) b.2)]
        · apply Subtype.ext
          show bnd (b.1 • q.1) = q.1
          rw [bnd, nrm_smul, q.2, mul_one, abs_of_pos (lt_trans (by norm_num) b.2),
            inv_smul_smul₀ (ne_of_gt (lt_trans (by norm_num) b.2))]
      right_inv := by
        intro p
        apply Subtype.ext
        show nrm (p:E2) • bnd (p:E2) = (p:E2)
        rw [smul_bnd] }
  have hc1 : Continuous e := by
    refine Continuous.subtype_mk
      (f := fun z : {b : ℝ // 1/2 < b} × {q : E2 // nrm q = 1} => z.1.1 • z.2.1) ?_ hmem
    fun_prop
  have hc2 : Continuous e.symm := by
    show Continuous (fun p : T => ((⟨nrm (p:E2), p.2⟩ : {b : ℝ // 1/2 < b}),
        (⟨bnd (p:E2), nrm_bnd (hne p)⟩ : {q : E2 // nrm q = 1})))
    refine (Continuous.subtype_mk (nrm_continuous.comp continuous_subtype_val)
      (fun p : T => p.2)).prodMk ?_
    refine Continuous.subtype_mk ?_ (fun p : T => nrm_bnd (p := p.1) (hne p))
    have hpos : ∀ p : T, (0:ℝ) < nrm (p:E2) := fun p => lt_trans (by norm_num) p.2
    have h1 : Continuous (fun p : T => (nrm (p:E2))⁻¹) :=
      (nrm_continuous.comp continuous_subtype_val).inv₀ (fun p => ne_of_gt (hpos p))
    have h3 : Continuous (fun p : T => (nrm (p:E2))⁻¹ • ((p:E2))) :=
      h1.smul continuous_subtype_val
    simpa only [bnd] using h3
  let H : {b : ℝ // 1/2 < b} × {q : E2 // nrm q = 1} ≃ₜ T := Homeomorph.mk e hc1 hc2
  have hE : IsOpenEmbedding (fun z : {b : ℝ // 1/2 < b} × {q : E2 // nrm q = 1} => (H z : E2)) :=
    (IsOpen.isOpenEmbedding_subtypeVal hTopen).comp H.isOpenEmbedding
  have hfun : (fun z : {b : ℝ // 1/2 < b} × {q : E2 // nrm q = 1} => (H z : E2))
      = fun z : {b : ℝ // 1/2 < b} × {q : E2 // nrm q = 1} => z.1.1 • z.2.1 := by
    funext z; rfl
  rwa [hfun] at hE

/-! ### The direction chart `(0,1) → ∂Sq` -/

/-- **The perimeter parametrisation `(0,1) → ∂Sq` is an open embedding.** -/
theorem isOpenEmbedding_bndOfU_I :
    IsOpenEmbedding
      (fun a : ↥collarI => (⟨bndOfU a.1, nrm_bndOfU a.1⟩ : {q : E2 // nrm q = 1})) := by
  have heq : (fun a : ↥collarI => (⟨bndOfU a.1, nrm_bndOfU a.1⟩ : {q : E2 // nrm q = 1}))
      = fun a : ↥collarI => BarS ((a.1 : ℝ) : AddCircle (1:ℝ)) := by
    funext a
    exact Subtype.ext (Bar_coe' a.1 ⟨le_of_lt a.2.1, a.2.2⟩).symm
  rw [heq]
  exact isOpenEmbedding_barS.comp isOpenEmbedding_modCircle

/-! ### The plane-level chart is an open embedding -/

/-- **`(u,t) ↦ t • bndOfU u` is an open embedding of `(0,1) × (1/2,∞)` into the plane.** -/
theorem isOpenEmbedding_layerPtUp : IsOpenEmbedding layerPtUp := by
  set A : ↥collarI → {q : E2 // nrm q = 1} := fun a => ⟨bndOfU a.1, nrm_bndOfU a.1⟩ with hAdef
  have hA : IsOpenEmbedding A := isOpenEmbedding_bndOfU_I
  have hP : IsOpenEmbedding (Prod.map A (id : ↥collarJ → ↥collarJ)) :=
    hA.prodMap IsOpenEmbedding.id
  have hS : IsOpenEmbedding (⇑(Homeomorph.prodComm {q : E2 // nrm q = 1} ↥collarJ)) :=
    (Homeomorph.prodComm {q : E2 // nrm q = 1} ↥collarJ).isOpenEmbedding
  have hSc : IsOpenEmbedding (fun w : ↥collarJ × {q : E2 // nrm q = 1} => w.1.1 • w.2.1) :=
    isOpenEmbedding_smulSph
  have he : IsOpenEmbedding (⇑(Homeomorph.Set.prod collarI collarJ)) :=
    (Homeomorph.Set.prod collarI collarJ).isOpenEmbedding
  have hcomp := hSc.comp (hS.comp (hP.comp he))
  have heq : (fun w : ↥collarJ × {q : E2 // nrm q = 1} => w.1.1 • w.2.1)
        ∘ (⇑(Homeomorph.prodComm {q : E2 // nrm q = 1} ↥collarJ))
        ∘ (Prod.map A (id : ↥collarJ → ↥collarJ))
        ∘ (⇑(Homeomorph.Set.prod collarI collarJ)) = layerPtUp := by
    funext z
    rfl
  rwa [heq] at hcomp

/-! ### The layer chart of the collar -/

/-- **The layer-direction chart of the collar is an open embedding.** -/
theorem isOpenEmbedding_layerPtSq :
    Topology.IsOpenEmbedding
      (fun z : {z : ℝ × ℝ // z ∈ Work.Cusp.collarLayerDom} => Work.Cusp.layerPtSq z) := by
  have hsub : collarLayerDom ⊆ collarUpDom := collarLayerDom_subset_collarUpDom
  have hincl : IsEmbedding (Set.inclusion hsub) := IsEmbedding.inclusion hsub
  have hUp := isOpenEmbedding_layerPtUp
  have hcomp : IsEmbedding
      (fun z : {z : ℝ × ℝ // z ∈ collarLayerDom} => z.1.2 • bndOfU z.1.1) := by
    have h := hUp.isEmbedding.comp hincl
    simpa only [Function.comp_def, Set.inclusion, layerPtUp] using h
  have hEmb : IsEmbedding (fun z : {z : ℝ × ℝ // z ∈ collarLayerDom} => layerPtSq z) := by
    refine (IsEmbedding.of_comp_iff
      (f := fun z : {z : ℝ × ℝ // z ∈ collarLayerDom} => layerPtSq z)
      (g := (Subtype.val : Work.Space.SquarePt → E2)) (IsEmbedding.subtypeVal)).mp ?_
    show IsEmbedding (fun z : {z : ℝ × ℝ // z ∈ collarLayerDom} =>
      ((layerPtSq z : Work.Space.SquarePt) : E2))
    simpa only [layerPtSq, layerPt] using hcomp
  refine ⟨hEmb, ?_⟩
  have hrange : range (fun z : {z : ℝ × ℝ // z ∈ collarLayerDom} => layerPtSq z)
      = (Subtype.val : Work.Space.SquarePt → E2) ⁻¹' (range layerPtUp) := by
    ext p
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨⟨z.1, hsub z.2⟩, rfl⟩
    · rintro ⟨w, hw⟩
      have hw2 : layerPtUp w = (p : Work.Space.E2) := hw
      have hb : w.1.2 ≤ 1 := by
        have h1 : nrm (p : E2) ≤ 1 := Work.Space.sqNorm_le_one p
        have h2 : nrm (layerPtUp w) = w.1.2 := by
          rw [layerPtUp, nrm_smul, nrm_bndOfU, mul_one,
            abs_of_pos (lt_trans (by norm_num) w.2.2)]
        rw [hw2] at h2
        exact h2 ▸ h1
      refine ⟨⟨w.1, ⟨w.2.1.1, by linarith [w.2.1.2], w.2.2, hb⟩⟩, ?_⟩
      apply Subtype.ext
      show layerPtUp w = (p : Work.Space.E2)
      exact hw2
  rw [hrange]
  exact hUp.isOpen_range.preimage continuous_subtype_val

end Work.Cusp
