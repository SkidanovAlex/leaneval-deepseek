import Mathlib
import Submission.Work.TangentClasses.Bundle
import Submission.Work.Thom.localThom_full
import Submission.Work.Thom.Glue
import Submission.Work.Thom.naturalModelClass_punct
import Submission.Work.Thom.relCohMap_homotopic
import Submission.Work.Thom.ATools
import Submission.Work.Thom.ChartOrientation
import Submission.Work.Thom.mixedCupC_oneH_zero
import Submission.Work.Thom.exists_path_GL_pos_linear
import Submission.Work.Cohomology.h0Evaluation

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# `det > 0` over the overlap orients the two chart-trivialisations

The main theorem of this file is `Work.Thom.isOrientedOver_of_det_pos`: if the coordinate change
`Z.coordChange i j` of a real bundle `Z → B` of rank `n` has positive determinant at every point of
`U ∩ V` (with `U ⊆ Z.baseSet i`, `V ⊆ Z.baseSet j`), then the two chart-trivialisations of the
natural model Thom class agree over `U ∩ V`, i.e. `Work.Thom.IsOrientedOver Z n U V` holds.

The chart classes are the pullbacks of the punctured model class `Work.Thom.Mpun n W` along the chart
homeomorphisms, and the two charts differ by the gauge automorphism `gaugeMap` of
`Submission/Work/Thom/ChartOrientation.lean`.  The mathematical content of this file is that an
*orientation preserving* gauge fixes the model class `Mpun n W`:

* `Mpun_gaugeEnd_homotopy` — a gauge homotopic to the identity *through gauges* fixes `Mpun`
  (homotopy invariance of relative cohomology);
* `Mpun_gaugeEnd_subsingleton` — over a single point every orientation preserving gauge is homotopic
  to the identity through gauges (`Work.Thom.exists_path_GL_pos_linear`);
* `Mpun_gaugeEnd_invariant` — a general orientation preserving gauge fixes `Mpun`.  Here the general
  case is reduced to the point case: the two classes differ by `π^*(a)` for a unit `a ∈ H⁰(Y)`
  (bijectivity of the cup map with `Mpun`), and a unit of `H⁰` is detected by its restrictions to
  the points of `Y` (`h0_eq_oneH_of_point_incl`).
-/

open Work.TangentClasses

namespace Work.Thom

open CategoryTheory

noncomputable section

variable {Y : Type} [TopologicalSpace Y]

/-! ## The gauge automorphism of a product with `ℝⁿ` -/

/-- The endomorphisms of `ℝⁿ` acting as gauge transformations of the bundle `Y × ℝⁿ → Y`. -/
abbrev Gauge (n : ℕ) : Type := EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)

/-- The gauge automorphism `(y, v) ↦ (y, D y v)` of `Y × ℝⁿ`. -/
def gaugeEnd {n : ℕ} (D : Y → Gauge n) (hD : Continuous D) :
    C(Y × EuclideanSpace ℝ (Fin n), Y × EuclideanSpace ℝ (Fin n)) :=
  ⟨fun p => (p.1, D p.1 p.2),
    continuous_fst.prodMk ((hD.comp continuous_fst).clm_apply continuous_snd)⟩

@[simp] theorem gaugeEnd_apply {n : ℕ} (D : Y → Gauge n) (hD : Continuous D)
    (p : Y × EuclideanSpace ℝ (Fin n)) : gaugeEnd D hD p = (p.1, D p.1 p.2) := rfl

/-- The application formula of the base inclusion `↥W × ℝⁿ → B × ℝⁿ`. -/
@[simp] theorem baseIncl_apply (B : Type) [TopologicalSpace B] (W : Set B) (n : ℕ)
    (p : ↥W × EuclideanSpace ℝ (Fin n)) :
    baseIncl B W n p = (((p.1 : ↥W) : B), p.2) := rfl

/-- The gauge automorphism preserves the complement of the zero section when the gauges are
injective. -/
theorem gaugeEnd_mem {n : ℕ} (D : Y → Gauge n) (hD : Continuous D)
    (hB : ∀ y, Function.Bijective (D y)) :
    ∀ p ∈ Punct Y n, gaugeEnd D hD p ∈ Punct Y n := by
  intro p hp
  simp only [Punct, Set.mem_ofPred_eq] at hp ⊢
  intro h
  have h' : D p.1 p.2 = 0 := h
  exact hp ((hB p.1).1 (by rw [h']; simp))

/-- An endomorphism of `ℝⁿ` with non-zero determinant is bijective. -/
theorem gaugeEnd_bijective_of_det_ne_zero {n : ℕ} (A : Gauge n)
    (h : LinearMap.det A.toLinearMap ≠ 0) : Function.Bijective A := by
  have hker : LinearMap.ker A.toLinearMap = ⊥ := by
    by_contra hne
    exact h (LinearMap.det_eq_zero_iff_ker_ne_bot.2 hne)
  constructor
  · exact LinearMap.ker_eq_bot.1 hker
  · have hinj : Function.Injective A.toLinearMap := LinearMap.ker_eq_bot.1 hker
    intro w
    obtain ⟨v, hv⟩ := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).1 hinj w
    exact ⟨v, hv⟩

/-! ## The gauge homotopy -/

/-- **A gauge homotopic to the identity through gauges fixes the model class.** -/
theorem Mpun_gaugeEnd_homotopy (n : ℕ) (hn : 1 ≤ n) {Y : Type} [TopologicalSpace Y]
    (D : Y → Gauge n) (hD : Continuous D) (hB : ∀ y, Function.Bijective (D y))
    (H : C(unitInterval × Y, Gauge n)) (H0 : ∀ y, H (0, y) = D y) (H1 : ∀ y, H (1, y) = 1)
    (Hinv : ∀ t y, Function.Bijective (H (t, y))) :
    (relCohMap (gaugeEnd D hD) (Punct Y n) (Punct Y n) (gaugeEnd_mem D hD hB) ℤ n).hom
      (Mpun n Y) = Mpun n Y := by
  have hcont : Continuous (fun q : unitInterval × (Y × EuclideanSpace ℝ (Fin n)) =>
      ((q.2.1 : Y), H (q.1, q.2.1) q.2.2)) :=
    (continuous_fst.comp continuous_snd).prodMk
      ((H.continuous.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))) |>.clm_apply
        (continuous_snd.comp continuous_snd))
  let Ψ : C(unitInterval × (Y × EuclideanSpace ℝ (Fin n)), Y × EuclideanSpace ℝ (Fin n)) :=
    ⟨_, hcont⟩
  have hmem : ∀ t p, p ∈ Punct Y n → Ψ (t, p) ∈ Punct Y n := by
    intro t p hp
    simp only [Punct, Set.mem_ofPred_eq] at hp ⊢
    intro h
    have h' : H (t, p.1) p.2 = 0 := h
    exact hp ((Hinv t p.1).1 (by rw [h']; simp))
  let hom : ContinuousMap.Homotopy (gaugeEnd D hD)
      (ContinuousMap.id (Y × EuclideanSpace ℝ (Fin n))) :=
    { toContinuousMap := Ψ
      map_zero_left := by
        intro p
        refine Prod.ext rfl ?_
        show H (0, p.1) p.2 = D p.1 p.2
        rw [H0 p.1]
      map_one_left := by
        intro p
        refine Prod.ext rfl ?_
        show H (1, p.1) p.2 = p.2
        rw [H1 p.1]
        rfl }
  have hEq := relCohMap_homotopic (Punct Y n) (Punct Y n) (gaugeEnd_mem D hD hB)
    (fun _ hp => hp) hom hmem ℤ n
  rw [hEq, relCohMap_idA, ModuleCat.hom_id]
  rfl

/-! ## Naturality of the degree-zero evaluation -/

/-- The `0`-simplex of the singular simplicial set of `X` associated with a point is natural. -/
theorem toSSetObj₀Equiv_map {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y))
    (s : (TopCat.toSSet.obj (TopCat.of X)).obj (Opposite.op (SimplexCategory.mk 0))) :
    TopCat.toSSetObj₀Equiv ((TopCat.toSSet.map (TopCat.ofHom f)).app
        (Opposite.op (SimplexCategory.mk 0)) s) = f (TopCat.toSSetObj₀Equiv s) := by
  simp only [TopCat.toSSetObj₀Equiv_apply]
  rfl

/-- **Naturality of the evaluation `h0Ev` under a pullback.** -/
theorem h0Ev_pullback {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y))
    (s : (TopCat.toSSet.obj (TopCat.of X)).obj (Opposite.op (SimplexCategory.mk 0)))
    (y : Coh ℤ 0 Y) :
    Work.Cohomology.h0Ev (TopCat.toSSet.obj (TopCat.of X)) s ((CohMap f ℤ 0).hom y)
      = Work.Cohomology.h0Ev (TopCat.toSSet.obj (TopCat.of Y))
          ((TopCat.toSSet.map (TopCat.ofHom f)).app (Opposite.op (SimplexCategory.mk 0)) s) y := by
  obtain ⟨α, hα, hx⟩ := Work.Cohomology.exists_cohomologyClassOf ℤ
    (TopCat.toSSet.obj (TopCat.of Y)) 0 y
  subst hx
  show Work.Cohomology.h0Ev (TopCat.toSSet.obj (TopCat.of X)) s
      ((HomologicalComplex.homologyMap
        (Work.Cohomology.dualChainMap ℤ (TopCat.of X) (TopCat.of Y) (TopCat.ofHom f)) 0).hom
        (Work.Cohomology.cohomologyClassOf ℤ (TopCat.toSSet.obj (TopCat.of Y)) α hα))
    = Work.Cohomology.h0Ev (TopCat.toSSet.obj (TopCat.of Y))
        ((TopCat.toSSet.map (TopCat.ofHom f)).app (Opposite.op (SimplexCategory.mk 0)) s)
        (Work.Cohomology.cohomologyClassOf ℤ (TopCat.toSSet.obj (TopCat.of Y)) α hα)
  rw [Work.Cohomology.singularCohomologyMap_classOf ℤ (TopCat.ofHom f) α hα]
  rw [Work.Cohomology.h0Ev_classOf, Work.Cohomology.h0Ev_classOf]
  show (((SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom f)) (ModuleCat.of ℤ ℤ)).f 0).hom.dualMap α)
      (Work.Cohomology.h0Gen (TopCat.toSSet.obj (TopCat.of X)) s)
    = α (Work.Cohomology.h0Gen (TopCat.toSSet.obj (TopCat.of Y))
        ((TopCat.toSSet.map (TopCat.ofHom f)).app (Opposite.op (SimplexCategory.mk 0)) s))
  rw [LinearMap.dualMap_apply]
  congr 1
  have h := congrArg (fun (g : ModuleCat.of ℤ ℤ ⟶
      ((TopCat.toSSet.obj (TopCat.of Y)).chainComplex (ModuleCat.of ℤ ℤ)).X 0) => g.hom 1)
    (SSet.ι_chainComplexMap_f (TopCat.toSSet.obj (TopCat.of X)) (TopCat.toSSet.obj (TopCat.of Y))
      (TopCat.toSSet.map (TopCat.ofHom f)) (ModuleCat.of ℤ ℤ) s)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  simpa only [Work.Cohomology.h0Gen] using h

/-- The unit class of `H⁰` evaluates to `1` at every `0`-simplex. -/
theorem h0Ev_oneH {X : Type} [TopologicalSpace X]
    (s : (TopCat.toSSet.obj (TopCat.of X)).obj (Opposite.op (SimplexCategory.mk 0))) :
    Work.Cohomology.h0Ev (TopCat.toSSet.obj (TopCat.of X)) s
      (Work.Cohomology.oneH ℤ (TopCat.toSSet.obj (TopCat.of X))) = 1 := by
  rw [Work.Cohomology.oneH, Work.Cohomology.h0Ev_classOf]
  exact Work.Cohomology.genEval_unitCochain ℤ (TopCat.toSSet.obj (TopCat.of X)) s

/-- A class of `H⁰` whose restriction to every point of the space is the unit class is the unit
class. -/
theorem h0_eq_oneH_of_point_incl {Y : Type} [TopologicalSpace Y] (a : Coh ℤ 0 Y)
    (h : ∀ x : Y, (CohMap (⟨fun y : ↥({x} : Set Y) => (y : Y), continuous_subtype_val⟩ :
        C(↥({x} : Set Y), Y)) ℤ 0).hom a
        = Work.Cohomology.oneH ℤ (TopCat.toSSet.obj (TopCat.of ↥({x} : Set Y)))) :
    a = Work.Cohomology.oneH ℤ (TopCat.toSSet.obj (TopCat.of Y)) := by
  obtain ⟨α, hα, hx⟩ := Work.Cohomology.exists_cohomologyClassOf ℤ
    (TopCat.toSSet.obj (TopCat.of Y)) 0 a
  have hval : ∀ s : (TopCat.toSSet.obj (TopCat.of Y)).obj (Opposite.op (SimplexCategory.mk 0)),
      Work.Cohomology.genEval ℤ (TopCat.toSSet.obj (TopCat.of Y)) α s = 1 := by
    intro s
    set x : Y := TopCat.toSSetObj₀Equiv s with hxdef
    set s₀ : (TopCat.toSSet.obj (TopCat.of ↥({x} : Set Y))).obj
        (Opposite.op (SimplexCategory.mk 0)) :=
      TopCat.toSSetObj₀Equiv.symm (⟨x, rfl⟩ : ↥({x} : Set Y)) with hs₀
    have hnat := h0Ev_pullback (⟨fun y : ↥({x} : Set Y) => (y : Y), continuous_subtype_val⟩ :
      C(↥({x} : Set Y), Y)) s₀ a
    rw [h x, h0Ev_oneH] at hnat
    have hs : (TopCat.toSSet.map (TopCat.ofHom (⟨fun y : ↥({x} : Set Y) => (y : Y),
        continuous_subtype_val⟩ : C(↥({x} : Set Y), Y)))).app
        (Opposite.op (SimplexCategory.mk 0)) s₀ = s := by
      apply TopCat.toSSetObj₀Equiv.injective
      rw [toSSetObj₀Equiv_map, Equiv.apply_symm_apply, hxdef]
      rfl
    rw [hs] at hnat
    rw [← hx, Work.Cohomology.h0Ev_classOf] at hnat
    exact hnat.symm
  have hαeq : α = Work.Cohomology.unitCochain ℤ (TopCat.toSSet.obj (TopCat.of Y)) := by
    apply Work.Cohomology.genEval_ext
    intro s
    rw [hval s, Work.Cohomology.genEval_unitCochain]
  have hmain : Work.Cohomology.cohomologyClassOf ℤ (TopCat.toSSet.obj (TopCat.of Y)) α hα
      = Work.Cohomology.oneH ℤ (TopCat.toSSet.obj (TopCat.of Y)) := by
    show Work.Cohomology.cohomologyClassOf ℤ (TopCat.toSSet.obj (TopCat.of Y)) α hα
      = Work.Cohomology.cohomologyClassOf ℤ (TopCat.toSSet.obj (TopCat.of Y))
          (Work.Cohomology.unitCochain ℤ (TopCat.toSSet.obj (TopCat.of Y)))
          (Work.Cohomology.cochainDiff_unitCochain ℤ (TopCat.toSSet.obj (TopCat.of Y)))
    exact Work.Cohomology.cohomologyClassOf_congr ℤ (TopCat.toSSet.obj (TopCat.of Y)) hαeq hα
      (Work.Cohomology.cochainDiff_unitCochain ℤ (TopCat.toSSet.obj (TopCat.of Y)))
  rw [← hx]
  exact hmain

/-! ## Two bookkeeping lemmas for the degree zero/cup degree discrepancy -/

/-- Transporting a relative class along an equality of degrees commutes with the pullback. -/
theorem relCohMap_cast {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y))
    (A : Set X) (B : Set Y) (hf : ∀ x ∈ A, f x ∈ B) {k k' : ℕ} (h : k' = k)
    (x : RelCoh ℤ k' Y B) :
    (relCohMap f A B hf ℤ k).hom (h ▸ x) = h ▸ ((relCohMap f A B hf ℤ k').hom x) := by
  subst h
  rfl

/-- Transporting along an equality of degrees is injective. -/
theorem eq_of_cast_eq {α : ℕ → Type} {k k' : ℕ} (h : k = k') {x y : α k}
    (hxy : h ▸ x = h ▸ y) : x = y := by
  subst h
  exact hxy

/-- Equal continuous maps induce the same pullback on cohomology. -/
theorem CohMap_congr {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] {f g : C(X, Y)}
    (h : f = g) (R : Type) [CommRing R] (n : ℕ) : CohMap f R n = CohMap g R n := by
  subst h
  rfl

/-! ## The point case -/

/-- **Over a single point, every orientation preserving gauge fixes the model class.** -/
theorem Mpun_gaugeEnd_subsingleton (n : ℕ) (hn : 1 ≤ n) {Y : Type} [TopologicalSpace Y]
    [Subsingleton Y] [Nonempty Y] (D : Y → Gauge n) (hD : Continuous D)
    (hdet : ∀ y, 0 < LinearMap.det (D y).toLinearMap) :
    (relCohMap (gaugeEnd D hD) (Punct Y n) (Punct Y n)
      (gaugeEnd_mem D hD (fun y => gaugeEnd_bijective_of_det_ne_zero (D y) (ne_of_gt (hdet y))))
      ℤ n).hom (Mpun n Y) = Mpun n Y := by
  classical
  have hB : ∀ y, Function.Bijective (D y) :=
    fun y => gaugeEnd_bijective_of_det_ne_zero (D y) (ne_of_gt (hdet y))
  obtain ⟨y₀⟩ : Nonempty Y := inferInstance
  obtain ⟨γ, hγ0, hγ1, hγbij⟩ := exists_path_GL_pos_linear n (D y₀) (hdet y₀)
  refine Mpun_gaugeEnd_homotopy n hn D hD hB
    (⟨fun q => γ q.1, γ.continuous.comp continuous_fst⟩) ?_ ?_ ?_
  · intro y
    change γ (0 : unitInterval) = D y
    rw [hγ0]
    exact (congrArg D (Subsingleton.elim y y₀)).symm
  · intro y
    exact hγ1
  · intro t y
    exact hγbij t

/-- **The pullback of the gauge-transformed model class to the fibre over a point.** -/
theorem baseIncl_gaugeEnd (n : ℕ) (hn : 1 ≤ n) {Y : Type} [TopologicalSpace Y] (x : Y)
    (D : Y → Gauge n) (hD : Continuous D) (hB : ∀ y, Function.Bijective (D y))
    (hdetx : 0 < LinearMap.det (D x).toLinearMap) :
    (relCohMap (baseIncl Y {x} n) (Punct ↥({x} : Set Y) n) (Punct Y n)
      (fun _ hp => hp) ℤ n).hom
      ((relCohMap (gaugeEnd D hD) (Punct Y n) (Punct Y n) (gaugeEnd_mem D hD hB) ℤ n).hom
        (Mpun n Y)) = Mpun n ↥({x} : Set Y) := by
  -- the gauge over the one-point base `↥{x}`, and its two membership proofs
  have hBc : ∀ _ : ↥({x} : Set Y), Function.Bijective (D x) := fun _ => hB x
  have hgf : ∀ p ∈ Punct ↥({x} : Set Y) n,
      (gaugeEnd D hD) (baseIncl Y {x} n p) ∈ Punct Y n :=
    fun p hp => gaugeEnd_mem D hD hB (baseIncl Y {x} n p) hp
  have hgf' : ∀ p ∈ Punct ↥({x} : Set Y) n,
      (baseIncl Y {x} n) (gaugeEnd (fun _ : ↥({x} : Set Y) => D x) continuous_const p)
        ∈ Punct Y n :=
    fun p hp => gaugeEnd_mem (fun _ : ↥({x} : Set Y) => D x) continuous_const hBc p hp
  rw [relCohMap_compA_apply (Punct ↥({x} : Set Y) n) (Punct Y n) (Punct Y n)
    (baseIncl Y {x} n) (gaugeEnd D hD) (fun _ hp => hp) (gaugeEnd_mem D hD hB) hgf ℤ n
    (Mpun n Y)]
  have hmap : (gaugeEnd D hD).comp (baseIncl Y {x} n)
      = (baseIncl Y {x} n).comp (gaugeEnd (fun _ : ↥({x} : Set Y) => D x) continuous_const) := by
    apply ContinuousMap.ext
    intro p
    simp only [ContinuousMap.comp_apply, gaugeEnd_apply, baseIncl_apply]
    rw [Set.mem_singleton_iff.mp p.1.2]
  rw [relCohMap_congrA (Punct ↥({x} : Set Y) n) (Punct Y n) hmap hgf hgf' ℤ n]
  rw [← relCohMap_compA_apply (Punct ↥({x} : Set Y) n) (Punct ↥({x} : Set Y) n) (Punct Y n)
    (gaugeEnd (fun _ : ↥({x} : Set Y) => D x) continuous_const) (baseIncl Y {x} n)
    (gaugeEnd_mem (fun _ : ↥({x} : Set Y) => D x) continuous_const hBc) (fun _ hp => hp)
    hgf' ℤ n (Mpun n Y)]
  rw [Mpun_natural n Y {x}]
  exact Mpun_gaugeEnd_subsingleton n hn (fun _ : ↥({x} : Set Y) => D x) continuous_const
    (fun _ => hdetx)

/-! ## The general case -/

/-- **An orientation preserving gauge fixes the model class.** -/
theorem Mpun_gaugeEnd_invariant (n : ℕ) (hn : 1 ≤ n) {Y : Type} [TopologicalSpace Y]
    (D : Y → Gauge n) (hD : Continuous D)
    (hdet : ∀ y, 0 < LinearMap.det (D y).toLinearMap) :
    (relCohMap (gaugeEnd D hD) (Punct Y n) (Punct Y n)
      (gaugeEnd_mem D hD (fun y => gaugeEnd_bijective_of_det_ne_zero (D y) (ne_of_gt (hdet y))))
      ℤ n).hom (Mpun n Y) = Mpun n Y := by
  classical
  have hB : ∀ y, Function.Bijective (D y) :=
    fun y => gaugeEnd_bijective_of_det_ne_zero (D y) (ne_of_gt (hdet y))
  obtain ⟨a, ha⟩ := (Mpun_isModel n Y 0).2
    ((Nat.zero_add n).symm ▸ ((relCohMap (gaugeEnd D hD) (Punct Y n) (Punct Y n)
      (gaugeEnd_mem D hD hB) ℤ n).hom (Mpun n Y)))
  -- the pointwise analysis
  have hpt : ∀ x : Y, (CohMap (⟨fun y : ↥({x} : Set Y) => (y : Y), continuous_subtype_val⟩ :
      C(↥({x} : Set Y), Y)) ℤ 0).hom a
      = Work.Cohomology.oneH ℤ (TopCat.toSSet.obj (TopCat.of ↥({x} : Set Y))) := by
    intro x
    set incl : C(↥({x} : Set Y), Y) := ⟨fun y => (y : Y), continuous_subtype_val⟩ with hincl
    have hι : ∀ p ∈ Punct ↥({x} : Set Y) n, baseIncl Y {x} n p ∈ Punct Y n := fun _ hp => hp
    have key := congrArg (fun z => (relCohMap (baseIncl Y {x} n) (Punct ↥({x} : Set Y) n)
      (Punct Y n) hι ℤ (0 + n)).hom z) ha
    -- the left hand side, computed by naturality
    have hL : (relCohMap (baseIncl Y {x} n) (Punct ↥({x} : Set Y) n) (Punct Y n)
        hι ℤ (0 + n)).hom
        ((mixedCupC ℤ (Punct Y n) 0 n) ((CohMap (projFstA Y n) ℤ 0).hom a) (Mpun n Y))
        = (mixedCupC ℤ (Punct ↥({x} : Set Y) n) 0 n)
            ((CohMap (projFstA ↥({x} : Set Y) n) ℤ 0).hom ((CohMap incl ℤ 0).hom a))
            (Mpun n ↥({x} : Set Y)) := by
      rw [mixedCupC_pairNatural (baseIncl Y {x} n) (Punct ↥({x} : Set Y) n) (Punct Y n)
        hι 0 n ((CohMap (projFstA Y n) ℤ 0).hom a) (Mpun n Y)]
      have hX : (CohMap (baseIncl Y {x} n) ℤ 0).hom ((CohMap (projFstA Y n) ℤ 0).hom a)
          = (CohMap (projFstA ↥({x} : Set Y) n) ℤ 0).hom ((CohMap incl ℤ 0).hom a) := by
        rw [CohMap_comp_apply (baseIncl Y {x} n) (projFstA Y n) ℤ 0 a,
          CohMap_comp_apply (projFstA ↥({x} : Set Y) n) incl ℤ 0 a]
        have hmap : (projFstA Y n).comp (baseIncl Y {x} n)
            = incl.comp (projFstA ↥({x} : Set Y) n) := by
          apply ContinuousMap.ext
          intro p
          rfl
        rw [CohMap_congr hmap ℤ 0]
      have hZ : (relCohMap (baseIncl Y {x} n) (Punct ↥({x} : Set Y) n) (Punct Y n)
          hι ℤ n).hom (Mpun n Y) = Mpun n ↥({x} : Set Y) := by
        rw [show (relCohMap (baseIncl Y {x} n) (Punct ↥({x} : Set Y) n) (Punct Y n) hι ℤ n)
            = (relCohMap (baseIncl Y {x} n) (Punct ↥({x} : Set Y) n) (Punct Y n)
              (fun _ hp => hp) ℤ n) from relCohMap_hcongrA _ _ _ _ _ ℤ n]
        exact Mpun_natural n Y {x}
      rw [hX, hZ]
    -- the right hand side
    have hR : (relCohMap (baseIncl Y {x} n) (Punct ↥({x} : Set Y) n) (Punct Y n)
        hι ℤ (0 + n)).hom
        ((Nat.zero_add n).symm ▸ ((relCohMap (gaugeEnd D hD) (Punct Y n) (Punct Y n)
          (gaugeEnd_mem D hD hB) ℤ n).hom (Mpun n Y)))
        = (Nat.zero_add n).symm ▸ (Mpun n ↥({x} : Set Y)) := by
      rw [relCohMap_cast (baseIncl Y {x} n) (Punct ↥({x} : Set Y) n) (Punct Y n) hι
        (h := (Nat.zero_add n).symm)
        ((relCohMap (gaugeEnd D hD) (Punct Y n) (Punct Y n) (gaugeEnd_mem D hD hB) ℤ n).hom
          (Mpun n Y))]
      congr 1
      rw [show (relCohMap (baseIncl Y {x} n) (Punct ↥({x} : Set Y) n) (Punct Y n) hι ℤ n)
          = (relCohMap (baseIncl Y {x} n) (Punct ↥({x} : Set Y) n) (Punct Y n)
            (fun _ hp => hp) ℤ n) from relCohMap_hcongrA _ _ _ _ _ ℤ n]
      exact baseIncl_gaugeEnd n hn x D hD hB (hdet x)
    -- conclude the pointwise statement
    have hcast : (mixedCupC ℤ (Punct ↥({x} : Set Y) n) 0 n)
        ((CohMap (projFstA ↥({x} : Set Y) n) ℤ 0).hom
          (Work.Cohomology.oneH ℤ (TopCat.toSSet.obj (TopCat.of ↥({x} : Set Y)))))
        (Mpun n ↥({x} : Set Y)) = (Nat.zero_add n).symm ▸ (Mpun n ↥({x} : Set Y)) := by
      rw [CohMap_oneH, mixedCupC_oneH_zero]
    refine (Mpun_isModel n ↥({x} : Set Y) 0).1 ?_
    simp only []
    rw [← hL, key, hR, hcast]
  -- conclude
  have hmain : a = Work.Cohomology.oneH ℤ (TopCat.toSSet.obj (TopCat.of Y)) :=
    h0_eq_oneH_of_point_incl a hpt
  have ha' : (mixedCupC ℤ (Punct Y n) 0 n) ((CohMap (projFstA Y n) ℤ 0).hom a) (Mpun n Y)
      = (Nat.zero_add n).symm ▸ ((relCohMap (gaugeEnd D hD) (Punct Y n) (Punct Y n)
          (gaugeEnd_mem D hD hB) ℤ n).hom (Mpun n Y)) := by
    simpa only [] using ha
  have step2 : (mixedCupC ℤ (Punct Y n) 0 n) ((CohMap (projFstA Y n) ℤ 0).hom a) (Mpun n Y)
      = (Nat.zero_add n).symm ▸ (Mpun n Y) := by
    rw [hmain, CohMap_oneH, mixedCupC_oneH_zero]
  exact eq_of_cast_eq (α := fun k => RelCoh ℤ k (Y × EuclideanSpace ℝ (Fin n)) (Punct Y n))
    (h := (Nat.zero_add n).symm) (ha'.symm.trans step2)

/-! ## The gauge change of a chart -/

/-- **The gauge change of a chart fixes the model class when `det (coordChange i j) > 0`.**
This is the `det > 0` version of `Work.Thom.gaugeMap_Mpun`. -/
theorem gaugeMap_Mpun_of_det_pos {B : Type} [TopologicalSpace B] {F : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] {ι : Type}
    (Z : RealBundle B F ι) (n : ℕ) (hn : 1 ≤ n)
    (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin n)) (i j : ι) (W : Set B)
    (hW : W ⊆ Z.baseSet i ∩ Z.baseSet j)
    (hdet : ∀ x : ↥W, 0 < LinearMap.det ((Z.coordChange i j (x : B)).toLinearMap)) :
    (relCohMap (gaugeMap Z n e i j W hW) (Punct ↥W n) (Punct ↥W n)
      (gaugeMap_mem_punct Z n e i j W hW) ℤ n).hom (Mpun n ↥W) = Mpun n ↥W := by
  classical
  let D : ↥W → Gauge n := fun x =>
    (e : F →L[ℝ] EuclideanSpace ℝ (Fin n)).comp
      (((Z.coordChange i j (x : B)) : F →L[ℝ] F).comp
        (e.symm : EuclideanSpace ℝ (Fin n) →L[ℝ] F))
  have hcoord : Continuous (fun x : ↥W => Z.coordChange i j (x : B)) :=
    (Z.continuousOn_coordChange i j).comp_continuous continuous_subtype_val (fun x => hW x.2)
  have hD : Continuous D := by
    set Ψ : (F →L[ℝ] F) →ₗ[ℝ] (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :=
      { toFun := fun A => (e : F →L[ℝ] EuclideanSpace ℝ (Fin n)).comp
          (A.comp (e.symm : EuclideanSpace ℝ (Fin n) →L[ℝ] F))
        map_add' := by intro A B; ext v; simp
        map_smul' := by intro c A; ext v; simp }
    exact (LinearMap.continuous_of_finiteDimensional Ψ).comp hcoord
  have hdet' : ∀ x : ↥W, 0 < LinearMap.det ((D x).toLinearMap) := by
    intro x
    have hDx : (D x).toLinearMap
        = (e.toLinearEquiv : F →ₗ[ℝ] EuclideanSpace ℝ (Fin n)) ∘ₗ
          ((Z.coordChange i j (x : B)).toLinearMap) ∘ₗ
          ((e.toLinearEquiv).symm : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] F) := rfl
    rw [hDx, LinearMap.det_conj _ e.toLinearEquiv]
    exact hdet x
  have hmap : gaugeEnd D hD = gaugeMap Z n e i j W hW := by
    apply ContinuousMap.ext
    intro q
    simp only [gaugeEnd_apply, gaugeMap_apply]
    rfl
  have hmem : ∀ p ∈ Punct ↥W n, gaugeEnd D hD p ∈ Punct ↥W n :=
    gaugeEnd_mem D hD (fun x => gaugeEnd_bijective_of_det_ne_zero (D x) (ne_of_gt (hdet' x)))
  exact (congrArg (fun φ => φ.hom (Mpun n ↥W))
      (relCohMap_congrA (Punct ↥W n) (Punct ↥W n) hmap
        (gaugeMap_mem_punct Z n e i j W hW) hmem ℤ n)).symm.trans
    (Mpun_gaugeEnd_invariant n hn D hD hdet')

/-- **The chart classes over `W` for the two charts `i`, `j` agree when the determinant of the
transition function is positive.**  This is the `det > 0` version of
`Work.Thom.localThomOfChart_eq_of_gauge`. -/
theorem localThomOfChart_eq_of_det_pos {B : Type} [TopologicalSpace B] {F : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] {ι : Type}
    (Z : RealBundle B F ι) (n : ℕ) (hn : 1 ≤ n)
    (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin n)) (i j : ι) (W : Set B)
    (hWi : W ⊆ Z.baseSet i) (hWj : W ⊆ Z.baseSet j) (hW : W ⊆ Z.baseSet i ∩ Z.baseSet j)
    (hdet : ∀ x : ↥W, 0 < LinearMap.det ((Z.coordChange i j (x : B)).toLinearMap)) :
    (localThomOfChart Z n e j W hWj).τ = (localThomOfChart Z n e i W hWi).τ := by
  have hcomp : (chartHomeo Z n e j W hWj :
        C(↥(Z.proj ⁻¹' W), ↥W × EuclideanSpace ℝ (Fin n)))
      = (gaugeMap Z n e i j W hW).comp (chartHomeo Z n e i W hWi :
          C(↥(Z.proj ⁻¹' W), ↥W × EuclideanSpace ℝ (Fin n))) :=
    chartHomeo_eq_gaugeMap Z n e i j W hWi hWj hW
  have hcj : ∀ p ∈ pieceZero Z W,
      (chartHomeo Z n e j W hWj : C(↥(Z.proj ⁻¹' W), ↥W × EuclideanSpace ℝ (Fin n))) p
        ∈ Punct ↥W n := chartHomeo_mem Z n e j W hWj
  have hc2 : ∀ p ∈ pieceZero Z W,
      ((gaugeMap Z n e i j W hW).comp (chartHomeo Z n e i W hWi :
        C(↥(Z.proj ⁻¹' W), ↥W × EuclideanSpace ℝ (Fin n)))) p ∈ Punct ↥W n :=
    fun p hp => gaugeMap_mem_punct Z n e i j W hW (chartHomeo Z n e i W hWi p)
      (chartHomeo_mem Z n e i W hWi p hp)
  have h1 : relCohMap (chartHomeo Z n e j W hWj :
        C(↥(Z.proj ⁻¹' W), ↥W × EuclideanSpace ℝ (Fin n)))
        (pieceZero Z W) (Punct ↥W n) hcj ℤ n
      = relCohMap ((gaugeMap Z n e i j W hW).comp (chartHomeo Z n e i W hWi :
            C(↥(Z.proj ⁻¹' W), ↥W × EuclideanSpace ℝ (Fin n))))
          (pieceZero Z W) (Punct ↥W n) hc2 ℤ n :=
    relCohMap_congrA (pieceZero Z W) (Punct ↥W n) hcomp hcj hc2 ℤ n
  have h2 := relCohMap_compA_apply (pieceZero Z W) (Punct ↥W n) (Punct ↥W n)
    (chartHomeo Z n e i W hWi : C(↥(Z.proj ⁻¹' W), ↥W × EuclideanSpace ℝ (Fin n)))
    (gaugeMap Z n e i j W hW) (chartHomeo_mem Z n e i W hWi)
    (gaugeMap_mem_punct Z n e i j W hW) hc2 ℤ n (Mpun n ↥W)
  have h3 : (relCohMap (chartHomeo Z n e i W hWi :
          C(↥(Z.proj ⁻¹' W), ↥W × EuclideanSpace ℝ (Fin n)))
          (pieceZero Z W) (Punct ↥W n) (chartHomeo_mem Z n e i W hWi) ℤ n).hom
          ((relCohMap (gaugeMap Z n e i j W hW) (Punct ↥W n) (Punct ↥W n)
            (gaugeMap_mem_punct Z n e i j W hW) ℤ n).hom (Mpun n ↥W))
      = (relCohMap (chartHomeo Z n e i W hWi :
            C(↥(Z.proj ⁻¹' W), ↥W × EuclideanSpace ℝ (Fin n)))
            (pieceZero Z W) (Punct ↥W n) (chartHomeo_mem Z n e i W hWi) ℤ n).hom
            (Mpun n ↥W) := by
    rw [gaugeMap_Mpun_of_det_pos Z n hn e i j W hW hdet]
  have hstart : (localThomOfChart Z n e j W hWj).τ
      = (relCohMap (chartHomeo Z n e j W hWj :
            C(↥(Z.proj ⁻¹' W), ↥W × EuclideanSpace ℝ (Fin n)))
            (pieceZero Z W) (Punct ↥W n) hcj ℤ n).hom (Mpun n ↥W) := rfl
  have hend : (relCohMap (chartHomeo Z n e i W hWi :
          C(↥(Z.proj ⁻¹' W), ↥W × EuclideanSpace ℝ (Fin n)))
          (pieceZero Z W) (Punct ↥W n) (chartHomeo_mem Z n e i W hWi) ℤ n).hom
          (Mpun n ↥W) = (localThomOfChart Z n e i W hWi).τ := rfl
  rw [hstart, congrArg (fun φ => φ.hom (Mpun n ↥W)) h1, ← h2, h3, hend]
/-- **`det > 0` over the overlap orients the two chart-trivialisations.** -/
theorem isOrientedOver_of_det_pos (n : ℕ) (hn : 1 ≤ n)
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (hF : Module.finrank ℝ F = n) {B : Type} [TopologicalSpace B] {ι : Type}
    (Z : Work.TangentClasses.RealBundle B F ι)
    {U V : Set B} {i j : ι} (hUi : U ⊆ Z.baseSet i) (hVj : V ⊆ Z.baseSet j)
    (hdet : ∀ x : ↥(U ∩ V), 0 < LinearMap.det ((Z.coordChange i j (x : B)).toLinearMap)) :
    Work.Thom.IsOrientedOver Z n U V := by
  have hfr : Module.finrank ℝ F = Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) := by
    rw [finrank_euclideanSpace_fin]; exact hF
  let e : F ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
    ContinuousLinearEquiv.ofFinrankEq (𝕜 := ℝ) (E := F)
      (F := EuclideanSpace ℝ (Fin n)) hfr
  have hWi : U ∩ V ⊆ Z.baseSet i := fun x hx => hUi hx.1
  have hWj : U ∩ V ⊆ Z.baseSet j := fun x hx => hVj hx.2
  refine ⟨localThomOfChart Z n e i U hUi, localThomOfChart Z n e j V hVj,
    localThomOfChart Z n e i (U ∩ V) hWi, ?_, ?_⟩
  · exact localThomOfChart_restrict Z n e i (U ∩ V) U hWi hUi (fun x hx => hx.1)
  · exact (localThomOfChart_restrict Z n e j (U ∩ V) V hWj hVj (fun x hx => hx.2)).trans
      (localThomOfChart_eq_of_det_pos Z n hn e i j (U ∩ V) hWi hWj
        (fun x hx => ⟨hUi hx.1, hVj hx.2⟩) hdet)

end

end Work.Thom
