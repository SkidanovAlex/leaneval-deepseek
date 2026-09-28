import Mathlib
import Submission.Work.Stems.Hurewicz

/-!
# The wedge, the pinch, and the cube concatenation

This file collects the point-set topology used in the proof of additivity of the Hurewicz chain map
(`Submission/Work/Stems/hurewiczChain_transAt.lean`):

* the wedge `Sⁿ ∨ Sⁿ` (as the "cross" in `Sⁿ × Sⁿ`), its inclusions and folds, and the gluing
  `wedgeMap` of two based maps `Sⁿ → X`;
* the pinch `pinchMap : Sⁿ → Sⁿ ∨ Sⁿ` along a coordinate, described on the cube by the two
  reparametrisations `sigmaA`, `sigmaB` occurring in `GenLoop.transAt`;
* the identification `cubeLift (transAt i q p) = wedgeMap … ∘ pinchMap`;
* the induced map `hm` on homology, and its functoriality.
-/

open CategoryTheory AlgebraicTopology
open scoped Topology Topology.Homotopy unitInterval

namespace Work.Stems

noncomputable section

variable {n : ℕ}

/-- The base point of `Sⁿ` used throughout: the image of the base point of the cube under the
collapse `Iⁿ → Sⁿ`. -/
def sphBase (n : ℕ) (hn : 1 ≤ n) : sphere n := collapseMap n hn 0

theorem collapseMap_mem_boundary (n : ℕ) (hn : 1 ≤ n) {q : CubeI n}
    (hq : q ∈ Cube.boundary (Fin n)) : collapseMap n hn q = sphBase n hn :=
  collapseMap_boundary n hn hq

/-- The wedge `Sⁿ ∨ Sⁿ`, realised as the "cross" `(Sⁿ × {b}) ∪ ({b} × Sⁿ) ⊆ Sⁿ × Sⁿ`. -/
def wedgeSet (b : sphere n) : Set (sphere n × sphere n) := {z | z.1 = b ∨ z.2 = b}

/-- The first inclusion `Sⁿ → Sⁿ ∨ Sⁿ`. -/
def wedgeInl (b : sphere n) : C(sphere n, wedgeSet b) :=
  ⟨fun x => ⟨(x, b), Or.inr rfl⟩,
    Continuous.subtype_mk (continuous_id.prodMk continuous_const) (fun x => Or.inr rfl)⟩

/-- The second inclusion `Sⁿ → Sⁿ ∨ Sⁿ`. -/
def wedgeInr (b : sphere n) : C(sphere n, wedgeSet b) :=
  ⟨fun y => ⟨(b, y), Or.inl rfl⟩,
    Continuous.subtype_mk (continuous_const.prodMk continuous_id) (fun y => Or.inl rfl)⟩

/-- The first projection (fold) `Sⁿ ∨ Sⁿ → Sⁿ`. -/
def wedgeFst (b : sphere n) : C(wedgeSet b, sphere n) :=
  ⟨fun z => z.1.1, continuous_fst.comp continuous_subtype_val⟩

/-- The second projection (fold) `Sⁿ ∨ Sⁿ → Sⁿ`. -/
def wedgeSnd (b : sphere n) : C(wedgeSet b, sphere n) :=
  ⟨fun z => z.1.2, continuous_snd.comp continuous_subtype_val⟩

@[simp] theorem wedgeInl_apply (b : sphere n) (x : sphere n) :
    ((wedgeInl b) x : sphere n × sphere n) = (x, b) := rfl

@[simp] theorem wedgeInr_apply (b : sphere n) (y : sphere n) :
    ((wedgeInr b) y : sphere n × sphere n) = (b, y) := rfl

@[simp] theorem wedgeFst_apply (b : sphere n) (z : wedgeSet b) : (wedgeFst b) z = z.1.1 := rfl

@[simp] theorem wedgeSnd_apply (b : sphere n) (z : wedgeSet b) : (wedgeSnd b) z = z.1.2 := rfl

@[simp] theorem wedgeFst_inl (b : sphere n) : (wedgeFst b).comp (wedgeInl b) = ContinuousMap.id _ := by
  ext x; rfl

@[simp] theorem wedgeFst_inr (b : sphere n) :
    (wedgeFst b).comp (wedgeInr b) = ContinuousMap.const _ b := by
  ext y; rfl

@[simp] theorem wedgeSnd_inl (b : sphere n) :
    (wedgeSnd b).comp (wedgeInl b) = ContinuousMap.const _ b := by
  ext x; rfl

@[simp] theorem wedgeSnd_inr (b : sphere n) :
    (wedgeSnd b).comp (wedgeInr b) = ContinuousMap.id _ := by
  ext y; rfl

/-- The "gluing" of two based maps `Sⁿ → X` into a map `Sⁿ ∨ Sⁿ → X`: `fq` on the first summand
and `fp` on the second, both based at the same point `b`. -/
def wedgeMap {X : Type} [TopologicalSpace X] (b : sphere n) (fq fp : C(sphere n, X))
    (h : fq b = fp b) : C(wedgeSet b, X) :=
  ⟨fun z => if z.1.2 = b then fq z.1.1 else fp z.1.2, by
    rw [← continuousOn_univ]
    have hAB : (Set.univ : Set (wedgeSet b)) =
        {z : wedgeSet b | z.1.2 = b} ∪ {z : wedgeSet b | z.1.1 = b} := by
      ext z
      simp only [Set.mem_univ, Set.mem_union, Set.mem_ofPred_eq, true_iff]
      rcases z.2 with h1 | h1
      · exact Or.inr h1
      · exact Or.inl h1
    rw [hAB, continuousOn_union_iff_of_isClosed]
    · constructor
      · apply ((fq.comp (wedgeFst b)).continuous.continuousOn).congr
        intro z hz
        show (if ((z : sphere n × sphere n)).2 = b then fq ((z : sphere n × sphere n)).1
          else fp ((z : sphere n × sphere n)).2) = fq ((z : sphere n × sphere n)).1
        rw [if_pos (show ((z : sphere n × sphere n)).2 = b from hz)]
      · apply ((fp.comp (wedgeSnd b)).continuous.continuousOn).congr
        intro z hz
        show (if ((z : sphere n × sphere n)).2 = b then fq ((z : sphere n × sphere n)).1
          else fp ((z : sphere n × sphere n)).2) = fp ((z : sphere n × sphere n)).2
        by_cases h2 : ((z : sphere n × sphere n)).2 = b
        · rw [if_pos h2]; rw [show ((z : sphere n × sphere n)).1 = b from hz]; rw [h]; rw [h2]
        · rw [if_neg h2]
    · exact isClosed_eq continuous_subtype_val.snd continuous_const
    · exact isClosed_eq continuous_subtype_val.fst continuous_const⟩

@[simp] theorem wedgeMap_inl {X : Type} [TopologicalSpace X] (b : sphere n) (fq fp : C(sphere n, X))
    (h : fq b = fp b) (x : sphere n) : wedgeMap b fq fp h (wedgeInl b x) = fq x := by
  show (if (((wedgeInl b x : wedgeSet b)) : sphere n × sphere n).2 = b then
    fq (((wedgeInl b x : wedgeSet b)) : sphere n × sphere n).1 else
    fp (((wedgeInl b x : wedgeSet b)) : sphere n × sphere n).2) = fq x
  rw [if_pos (show ((((wedgeInl b x : wedgeSet b))) : sphere n × sphere n).2 = b from rfl)]
  rfl

@[simp] theorem wedgeMap_inr {X : Type} [TopologicalSpace X] (b : sphere n) (fq fp : C(sphere n, X))
    (h : fq b = fp b) (y : sphere n) : wedgeMap b fq fp h (wedgeInr b y) = fp y := by
  show (if (((wedgeInr b y : wedgeSet b)) : sphere n × sphere n).2 = b then
    fq (((wedgeInr b y : wedgeSet b)) : sphere n × sphere n).1 else
    fp (((wedgeInr b y : wedgeSet b)) : sphere n × sphere n).2) = fp y
  split_ifs with hc
  · have hy : y = b := hc
    rw [show (((wedgeInr b y : wedgeSet b)) : sphere n × sphere n).1 = b from rfl, h, ← hy]
  · rfl


/-! ## The pinch `Sⁿ → Sⁿ ∨ Sⁿ` along a coordinate -/

/-- The base point of the wedge. -/
def wedgeBase (b : sphere n) : wedgeSet b := ⟨(b, b), Or.inl rfl⟩

@[simp] theorem wedgeInl_self (b : sphere n) : wedgeInl b b = wedgeBase b := Subtype.ext rfl
@[simp] theorem wedgeInr_self (b : sphere n) : wedgeInr b b = wedgeBase b := Subtype.ext rfl

/-- The reparametrisation of the `i`-th coordinate used on the *first* half of the cube in
`GenLoop.transAt`. -/
def sigmaA (i : Fin n) (t : CubeI n) : CubeI n :=
  Function.update t i (Set.projIcc (0 : ℝ) 1 zero_le_one (2 * (t i : ℝ)))

/-- The reparametrisation of the `i`-th coordinate used on the *second* half of the cube in
`GenLoop.transAt`. -/
def sigmaB (i : Fin n) (t : CubeI n) : CubeI n :=
  Function.update t i (Set.projIcc (0 : ℝ) 1 zero_le_one (2 * (t i : ℝ) - 1))

theorem continuous_sigmaA (i : Fin n) : Continuous (sigmaA (n := n) i) :=
  continuous_id.update i (continuous_projIcc.comp (continuous_const.mul
    (continuous_subtype_val.comp (continuous_apply i))))

theorem continuous_sigmaB (i : Fin n) : Continuous (sigmaB (n := n) i) :=
  continuous_id.update i (continuous_projIcc.comp ((continuous_const.mul
    (continuous_subtype_val.comp (continuous_apply i))).sub continuous_const))

@[simp] theorem sigmaA_apply_self (i : Fin n) (t : CubeI n) :
    sigmaA i t i = Set.projIcc (0 : ℝ) 1 zero_le_one (2 * (t i : ℝ)) := by
  rw [sigmaA, Function.update_apply, if_pos rfl]

@[simp] theorem sigmaB_apply_self (i : Fin n) (t : CubeI n) :
    sigmaB i t i = Set.projIcc (0 : ℝ) 1 zero_le_one (2 * (t i : ℝ) - 1) := by
  rw [sigmaB, Function.update_apply, if_pos rfl]

theorem sigmaA_apply_of_ne (i : Fin n) (t : CubeI n) {j : Fin n} (hj : j ≠ i) :
    sigmaA i t j = t j := by
  rw [sigmaA, Function.update_apply, if_neg hj]

theorem sigmaB_apply_of_ne (i : Fin n) (t : CubeI n) {j : Fin n} (hj : j ≠ i) :
    sigmaB i t j = t j := by
  rw [sigmaB, Function.update_apply, if_neg hj]

theorem projIcc_zero_eq : Set.projIcc (0 : ℝ) 1 zero_le_one 0 = (0 : Set.Icc (0 : ℝ) 1) := by
  rw [Set.projIcc_of_mem zero_le_one (by constructor <;> norm_num)]; exact Subtype.ext rfl

theorem projIcc_left_of_le_zero {x : ℝ} (hx : x ≤ 0) :
    Set.projIcc (0 : ℝ) 1 zero_le_one x = (0 : Set.Icc (0 : ℝ) 1) := by
  rw [Set.projIcc_of_le_left zero_le_one hx]; exact Subtype.ext rfl

theorem projIcc_right_of_one_le {x : ℝ} (hx : 1 ≤ x) :
    Set.projIcc (0 : ℝ) 1 zero_le_one x = (1 : Set.Icc (0 : ℝ) 1) := by
  rw [Set.projIcc_of_right_le zero_le_one hx]; exact Subtype.ext rfl

theorem sigmaA_mem_boundary (i : Fin n) {t : CubeI n} (ht : t ∈ Cube.boundary (Fin n)) :
    sigmaA i t ∈ Cube.boundary (Fin n) := by
  obtain ⟨j, hj⟩ := ht
  refine ⟨j, ?_⟩
  rw [sigmaA, Function.update_apply]
  by_cases hji : j = i
  · rw [if_pos hji]
    rcases hj with h0 | h1
    · left
      rw [hji] at h0
      rw [show (2 : ℝ) * (t i : ℝ) = 0 by rw [h0]; norm_num]
      exact projIcc_zero_eq
    · right
      rw [hji] at h1
      exact projIcc_right_of_one_le (by rw [h1]; norm_num)
  · rw [if_neg hji]; exact hj

theorem sigmaB_mem_boundary (i : Fin n) {t : CubeI n} (ht : t ∈ Cube.boundary (Fin n)) :
    sigmaB i t ∈ Cube.boundary (Fin n) := by
  obtain ⟨j, hj⟩ := ht
  refine ⟨j, ?_⟩
  rw [sigmaB, Function.update_apply]
  by_cases hji : j = i
  · rw [if_pos hji]
    rcases hj with h0 | h1
    · left
      rw [hji] at h0
      exact projIcc_left_of_le_zero (by rw [h0]; norm_num)
    · right
      rw [hji] at h1
      rw [show (2 : ℝ) * (t i : ℝ) - 1 = 1 by rw [h1]; norm_num]
      exact projIcc_right_of_one_le le_rfl
  · rw [if_neg hji]; exact hj

/-- On the boundary of the cube, the `A`-reparametrisation has `i`-th coordinate `1`
(as soon as `t` has `i`-th coordinate `1/2`). -/
theorem sigmaA_apply_self_of_eq_half (i : Fin n) {t : CubeI n} (ht : (t i : ℝ) = 1 / 2) :
    sigmaA i t i = 1 := by
  rw [sigmaA_apply_self, show (2 : ℝ) * (t i : ℝ) = 1 by rw [ht]; norm_num]
  exact projIcc_right_of_one_le le_rfl

theorem sigmaB_apply_self_of_eq_half (i : Fin n) {t : CubeI n} (ht : (t i : ℝ) = 1 / 2) :
    sigmaB i t i = 0 := by
  rw [sigmaB_apply_self, show (2 : ℝ) * (t i : ℝ) - 1 = 0 by rw [ht]; norm_num]
  exact projIcc_zero_eq

/-- The cube-level description of the pinch: the first half of the cube is mapped to the first
summand of the wedge by the reparametrisation `sigmaA` followed by the collapse, the second half
to the second summand. -/
def pinchRep (n : ℕ) (hn : 1 ≤ n) (i : Fin n) (t : CubeI n) : wedgeSet (sphBase n hn) :=
  if (t i : ℝ) ≤ 1 / 2 then
    wedgeInl (sphBase n hn) (collapseMap n hn (sigmaA i t))
  else
    wedgeInr (sphBase n hn) (collapseMap n hn (sigmaB i t))

theorem continuous_pinchRep (n : ℕ) (hn : 1 ≤ n) (i : Fin n) :
    Continuous (pinchRep n hn i) := by
  refine Continuous.if_le
    (f' := fun t : CubeI n => wedgeInl (sphBase n hn) (collapseMap n hn (sigmaA i t)))
    (g' := fun t : CubeI n => wedgeInr (sphBase n hn) (collapseMap n hn (sigmaB i t)))
    (f := fun t : CubeI n => (t i : ℝ)) (g := fun _ : CubeI n => (1 / 2 : ℝ))
    ((wedgeInl _).continuous.comp ((collapseMap n hn).continuous.comp (continuous_sigmaA i)))
    ((wedgeInr _).continuous.comp ((collapseMap n hn).continuous.comp (continuous_sigmaB i)))
    (continuous_subtype_val.comp (continuous_apply i)) continuous_const ?_
  intro t ht
  have hA : collapseMap n hn (sigmaA i t) = sphBase n hn :=
    collapseMap_mem_boundary n hn ⟨i, Or.inr (sigmaA_apply_self_of_eq_half i ht)⟩
  have hB : collapseMap n hn (sigmaB i t) = sphBase n hn :=
    collapseMap_mem_boundary n hn ⟨i, Or.inl (sigmaB_apply_self_of_eq_half i ht)⟩
  rw [hA, hB, wedgeInl_self, wedgeInr_self]

theorem pinchRep_eq_base (n : ℕ) (hn : 1 ≤ n) (i : Fin n) {t : CubeI n}
    (ht : t ∈ Cube.boundary (Fin n)) : pinchRep n hn i t = wedgeBase (sphBase n hn) := by
  rw [pinchRep]
  by_cases hc : (t i : ℝ) ≤ 1 / 2
  · rw [if_pos hc,
      collapseMap_mem_boundary n hn (sigmaA_mem_boundary i ht), wedgeInl_self]
  · rw [if_neg hc,
      collapseMap_mem_boundary n hn (sigmaB_mem_boundary i ht), wedgeInr_self]

theorem pinchRep_factors (n : ℕ) (hn : 1 ≤ n) (i : Fin n) :
    Function.FactorsThrough (pinchRep n hn i) (collapseMap n hn) := by
  intro t t' htt'
  rcases collapseMap_fiber n hn htt' with h | ⟨ht, ht'⟩
  · rw [h]
  · rw [pinchRep_eq_base n hn i ht, pinchRep_eq_base n hn i ht']

/-- **The pinch** `Sⁿ → Sⁿ ∨ Sⁿ` along the `i`-th coordinate: it collapses the equatorial
"middle" hyperplane of the cube (the subspace over which the two halves are glued) to the wedge
point, and maps the two halves of the cube to the two summands. -/
def pinchMap (n : ℕ) (hn : 1 ≤ n) (i : Fin n) : C(sphere n, wedgeSet (sphBase n hn)) :=
  (collapseMap_isQuotientMap n hn).lift ⟨pinchRep n hn i, continuous_pinchRep n hn i⟩
    (pinchRep_factors n hn i)

theorem pinchMap_comp (n : ℕ) (hn : 1 ≤ n) (i : Fin n) :
    (pinchMap n hn i).comp (collapseMap n hn) = ⟨pinchRep n hn i, continuous_pinchRep n hn i⟩ :=
  (collapseMap_isQuotientMap n hn).lift_comp _ _

@[simp] theorem pinchMap_apply_collapse (n : ℕ) (hn : 1 ≤ n) (i : Fin n) (t : CubeI n) :
    pinchMap n hn i (collapseMap n hn t) = pinchRep n hn i t :=
  congrFun (congrArg DFunLike.coe (pinchMap_comp n hn i)) t


/-! ## The cube concatenation is the pinch composite -/

/-- Evaluation of a lifted cube at the collapse of a cube point. -/
theorem cubeLift_apply_collapse (n : ℕ) (hn : 1 ≤ n) {X : Type} [TopologicalSpace X] {x₀ : X}
    (f : Ω^ (Fin n) X x₀) (t : CubeI n) :
    cubeLift n hn f (collapseMap n hn t) = f t :=
  congrFun (congrArg DFunLike.coe (cubeLift_comp n hn f)) t

/-- A lifted cube maps the base point of `Sⁿ` to `x₀`. -/
theorem cubeLift_sphBase (n : ℕ) (hn : 1 ≤ n) {X : Type} [TopologicalSpace X] {x₀ : X}
    (f : Ω^ (Fin n) X x₀) : cubeLift n hn f (sphBase n hn) = x₀ := by
  have h2 : cubeLift n hn f (collapseMap n hn 0) = f.1 0 :=
    cubeLift_apply_collapse n hn f 0
  rw [sphBase, h2]
  exact GenLoop.boundary f 0 (zero_mem_cubeBoundary n hn)

/-- The explicit form of `GenLoop.transAt` on a cube point. -/
theorem GenLoop.transAt_apply (n : ℕ) {X : Type} [TopologicalSpace X] {x₀ : X}
    (i : Fin n) (f g : Ω^ (Fin n) X x₀) (t : CubeI n) :
    (GenLoop.transAt i f g) t = if (t i : ℝ) ≤ 1 / 2 then f (sigmaA i t) else g (sigmaB i t) := by
  rw [GenLoop.transAt, GenLoop.coe_copy]
  rfl

/-- The wedge gluing of the two lifted halves of the pinch. -/
theorem wedgeMap_pinchRep (n : ℕ) (hn : 1 ≤ n) (i : Fin n) {X : Type} [TopologicalSpace X]
    (fq fp : C(sphere n, X)) (h : fq (sphBase n hn) = fp (sphBase n hn)) (t : CubeI n) :
    wedgeMap (sphBase n hn) fq fp h (pinchRep n hn i t) =
      (if (t i : ℝ) ≤ 1 / 2 then fq (collapseMap n hn (sigmaA i t))
        else fp (collapseMap n hn (sigmaB i t))) := by
  rw [pinchRep]
  split_ifs with hc
  · rw [wedgeMap_inl]
  · rw [wedgeMap_inr]

/-- **The cube concatenation is the pinch composite.**  The lift to `Sⁿ` of the concatenated loop
`transAt i q p` is the composition of the pinch `Sⁿ → Sⁿ ∨ Sⁿ` with the gluing of the two lifted
halves. -/
theorem cubeLift_transAt_eq (n : ℕ) (hn : 1 ≤ n) (i : Fin n) {X : Type} [TopologicalSpace X]
    {x₀ : X} (p q : Ω^ (Fin n) X x₀)
    (h : cubeLift n hn q (sphBase n hn) = cubeLift n hn p (sphBase n hn)) :
    cubeLift n hn (GenLoop.transAt i q p) =
      (wedgeMap (sphBase n hn) (cubeLift n hn q) (cubeLift n hn p) h).comp (pinchMap n hn i) := by
  apply ContinuousMap.ext
  intro y
  obtain ⟨t, ht⟩ := (collapseMap_isQuotientMap n hn).surjective y
  rw [← ht]
  rw [ContinuousMap.comp_apply]
  rw [pinchMap_apply_collapse]
  rw [wedgeMap_pinchRep (n := n) (hn := hn) (i := i)
    (fq := cubeLift n hn q) (fp := cubeLift n hn p) (h := h) (t := t)]
  simp only [cubeLift_apply_collapse]
  rw [GenLoop.transAt_apply n i q p t]

/-- The composition of the wedge gluing with the first inclusion is the first map. -/
theorem wedgeMap_comp_inl (n : ℕ) (hn : 1 ≤ n) {X : Type} [TopologicalSpace X]
    (fq fp : C(sphere n, X)) (h : fq (sphBase n hn) = fp (sphBase n hn)) :
    (wedgeMap (sphBase n hn) fq fp h).comp (wedgeInl (sphBase n hn)) = fq := by
  ext x
  rw [ContinuousMap.comp_apply, wedgeMap_inl]

theorem wedgeMap_comp_inr (n : ℕ) (hn : 1 ≤ n) {X : Type} [TopologicalSpace X]
    (fq fp : C(sphere n, X)) (h : fq (sphBase n hn) = fp (sphBase n hn)) :
    (wedgeMap (sphBase n hn) fq fp h).comp (wedgeInr (sphBase n hn)) = fp := by
  ext x
  rw [ContinuousMap.comp_apply, wedgeMap_inr]


/-! ## The induced map on homology as a linear map -/

/-- The map induced by a continuous map on the `n`-th singular homology, as a `ℤ`-linear map. -/
abbrev hm {A B : Type} [TopologicalSpace A] [TopologicalSpace B] (f : C(A, B)) (n : ℕ) :
    ((chains (TopCat.of A)).homology n) →ₗ[ℤ] ((chains (TopCat.of B)).homology n) :=
  (HomologicalComplex.homologyMap
    (Work.Cohomology.chainMap ℤ (TopCat.of A) (TopCat.of B) (TopCat.ofHom f)) n).hom

/-- The Hurewicz class is `hm` applied to the sphere generator. -/
theorem hurewiczClass_eq_hm (n : ℕ) (hn : 1 ≤ n) {X : Type} [TopologicalSpace X]
    (f : C(sphere n, X)) : hurewiczClass n hn f = hm f n (sphereGenerator n hn) := rfl

/-- Functoriality of `hm`. -/
theorem hm_comp (n : ℕ) {A B D : Type} [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalSpace D] (f : C(B, D)) (g : C(A, B)) :
    hm (f.comp g) n = (hm f n).comp (hm g n) := by
  have h1 : Work.Cohomology.chainMap ℤ (TopCat.of A) (TopCat.of D) (TopCat.ofHom (f.comp g))
      = Work.Cohomology.chainMap ℤ (TopCat.of A) (TopCat.of B) (TopCat.ofHom g)
        ≫ Work.Cohomology.chainMap ℤ (TopCat.of B) (TopCat.of D) (TopCat.ofHom f) := by
    simp only [Work.Cohomology.chainMap]
    rw [TopCat.ofHom_comp g f, CategoryTheory.Functor.map_comp]
  simp only [hm, h1, HomologicalComplex.homologyMap_comp, ModuleCat.hom_comp]

/-- The identity induces the identity on homology. -/
theorem hm_id (n : ℕ) {A : Type} [TopologicalSpace A] :
    hm (ContinuousMap.id A) n = LinearMap.id := by
  have h1 : Work.Cohomology.chainMap ℤ (TopCat.of A) (TopCat.of A) (TopCat.ofHom (ContinuousMap.id A))
      = 𝟙 _ := by
    rw [TopCat.ofHom_id, Work.Cohomology.chainMap, CategoryTheory.Functor.map_id]
  simp only [hm, h1, HomologicalComplex.homologyMap_id, ModuleCat.hom_id]

/-- A constant map induces the zero map on positive-degree homology. -/
theorem hm_const (n : ℕ) {A : Type} [TopologicalSpace A] (a : A) (hn : 1 ≤ n) :
    hm (ContinuousMap.const A a) n = 0 := by
  have h1 : ContinuousMap.const A a
      = (ContinuousMap.const PUnit a).comp (ContinuousMap.const A PUnit.unit) := by
    ext x; rfl
  rw [h1, hm_comp]
  have hz0 : CategoryTheory.Limits.IsZero ((chains (TopCat.of PUnit)).homology n) :=
    Work.Cohomology.homologyContractible n hn
  have hz : HomologicalComplex.homologyMap
      (Work.Cohomology.chainMap ℤ (TopCat.of A) (TopCat.of PUnit)
        (TopCat.ofHom (ContinuousMap.const A PUnit.unit))) n = 0 :=
    hz0.eq_zero_of_tgt _
  simp only [hm, hz, ModuleCat.hom_zero, LinearMap.comp_zero]

end
end Work.Stems
