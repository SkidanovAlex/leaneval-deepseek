import Mathlib
import Submission.Work.Orient.Defs
import Submission.Work.Cohomology.localHomology
import Submission.Work.ThomBordism.localGenDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false

namespace Work.Orient.Boundary

open scoped Manifold

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

noncomputable section

/-! ## Generic translation lemmas for relative homology -/

/-- **Excision**, as an isomorphism statement: for open `U, A ⊆ X` with `U ∪ A = X` the inclusion
of pairs `(U, U ∩ A) → (X, A)` induces an isomorphism on relative homology. -/
theorem excision_iso (X : TopCat) (U A : Set X) (hU : IsOpen U) (hA : IsOpen A)
    (hcov : U ∪ A = Set.univ) (k : ℕ) :
    Nonempty ((Work.Cohomology.relChains (TopCat.of U) {y : U | (y : X) ∈ A}).homology k ≅
      (Work.Cohomology.relChains X A).homology k) := by
  haveI := Work.Cohomology.excision_relChainsMap_isIso X U A hU hA hcov k
  exact ⟨asIso (HomologicalComplex.homologyMap (Work.Cohomology.relChainsMap X U A) k)⟩

/-- The restriction of a homeomorphism to a pair of corresponding subsets. -/
def homeomorphRestrict {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (φ : X ≃ₜ Y) (A : Set X) (B : Set Y) (hA : ∀ x, x ∈ A ↔ φ x ∈ B) : ↥A ≃ₜ ↥B where
  toFun x := ⟨φ x.1, (hA x.1).mp x.2⟩
  invFun y := ⟨φ.symm y.1, (hA (φ.symm y.1)).mpr (by rw [φ.apply_symm_apply]; exact y.2)⟩
  left_inv x := Subtype.ext (φ.symm_apply_apply x.1)
  right_inv y := Subtype.ext (φ.apply_symm_apply y.1)
  continuous_toFun := Continuous.subtype_mk (φ.continuous.comp continuous_subtype_val)
    (fun x => (hA x.1).mp x.2)
  continuous_invFun := Continuous.subtype_mk (φ.symm.continuous.comp continuous_subtype_val)
    (fun y => (hA (φ.symm y.1)).mpr (by rw [φ.apply_symm_apply]; exact y.2))

/-- **A homeomorphism of pairs induces an isomorphism on relative homology.** -/
theorem homeoRelChainsIso {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (φ : X ≃ₜ Y) (A : Set X) (B : Set Y)
    (hA : ∀ x, x ∈ A ↔ φ x ∈ B) (k : ℕ) :
    Nonempty ((Work.Cohomology.relChains (TopCat.of X) A).homology k ≅
      (Work.Cohomology.relChains (TopCat.of Y) B).homology k) := by
  let ψ := homeomorphRestrict φ A B hA
  let f : TopCat.of X ⟶ TopCat.of Y := TopCat.ofHom φ.toHomotopyEquiv.toFun
  let g : TopCat.of A ⟶ TopCat.of B := TopCat.ofHom ψ.toHomotopyEquiv.toFun
  have hw : Work.Cohomology.subtypeIncl (TopCat.of X) A ≫ f
      = g ≫ Work.Cohomology.subtypeIncl (TopCat.of Y) B := by
    ext z; rfl
  have hfq : ∀ k, IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.chainMap ℤ (TopCat.of X) (TopCat.of Y) f) k) :=
    fun k => Work.Cohomology.isIso_homologyMap_chainMap_of_homotopyEquiv
      (X := TopCat.of X) (Y := TopCat.of Y) φ.toHomotopyEquiv k
  have hgq : ∀ k, IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.chainMap ℤ (TopCat.of A) (TopCat.of B) g) k) :=
    fun k => Work.Cohomology.isIso_homologyMap_chainMap_of_homotopyEquiv
      (X := TopCat.of A) (Y := TopCat.of B) ψ.toHomotopyEquiv k
  haveI := Work.Cohomology.relChainsMapOf_homologyMap_isIso (X := TopCat.of X)
    (Y := TopCat.of Y) A B f g hw k hfq hgq
  exact ⟨asIso (HomologicalComplex.homologyMap
    (Work.Cohomology.relChainsMapOf (X := TopCat.of X) (Y := TopCat.of Y) A B f g hw) k)⟩

/-- **The half-space model is a T1 space.** -/
theorem t1Space_halfSpace (n : ℕ) : T1Space (EuclideanHalfSpace (n + 1)) :=
  t1Space_of_injective_of_continuous
    (f := (Subtype.val : EuclideanHalfSpace (n + 1) → EuclideanSpace ℝ (Fin (n + 1))))
    Subtype.val_injective continuous_subtype_val

/-- **A chart identifies the local homology of `X` at `x` with the relative homology of its target
at the image point.**  `e : OpenPartialHomeomorph X Y` with `x ∈ e.source`. -/
theorem relChains_chart_iso {X : TopCat} [T1Space X] {Y : Type} [TopologicalSpace Y]
    (e : OpenPartialHomeomorph X Y) (x : X) (hx : x ∈ e.source) (k : ℕ) :
    Nonempty ((Work.Cohomology.relChains X {y : X | y ≠ x}).homology k ≅
      (Work.Cohomology.relChains (TopCat.of e.target)
        {z : e.target | (z : Y) ≠ e x}).homology k) := by
  have hA : IsOpen {y : X | y ≠ x} := isClosed_singleton.isOpen_compl
  have hcov : e.source ∪ {y : X | y ≠ x} = Set.univ := by
    apply Set.eq_univ_of_forall
    intro y
    by_cases h : y = x
    · exact Or.inl (h ▸ hx)
    · exact Or.inr h
  obtain ⟨e1⟩ := excision_iso X e.source {y : X | y ≠ x} e.open_source hA hcov k
  have hAB : ∀ y : e.source, y ∈ {y : e.source | (y : X) ≠ x} ↔
      e.toHomeomorphSourceTarget y ∈ {z : e.target | (z : Y) ≠ e x} := by
    intro y
    constructor
    · intro hy heq
      apply hy
      have h1 : e.symm (e y.1) = y.1 := e.left_inv y.2
      have h2 : e.symm (e x) = x := e.left_inv hx
      have h3 : e y.1 = e x := heq
      rw [← h1, h3, h2]
    · intro hy hyx
      exact hy (congrArg e hyx)
  obtain ⟨e2⟩ := homeoRelChainsIso (X := e.source) (Y := e.target)
    e.toHomeomorphSourceTarget {y : e.source | (y : X) ≠ x}
    {z : e.target | (z : Y) ≠ e x} hAB k
  exact ⟨e1.symm ≪≫ e2⟩

/-- **Reduction to the half-space model.**  For a space charted in the half-space, the local
homology at `x` is the relative homology of the half-space itself at the image of `x`. -/
theorem locH_iso_halfspace (n k : ℕ) (W : TopCat) [T2Space W]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W] (x : W) :
    Nonempty (LocH W k x ≅ (Work.Cohomology.relChains
      (TopCat.of (EuclideanHalfSpace (n + 1)))
      {y : EuclideanHalfSpace (n + 1) | y ≠ chartAt (EuclideanHalfSpace (n + 1)) x x}).homology k) := by
  haveI : T1Space (EuclideanHalfSpace (n + 1)) := t1Space_halfSpace n
  haveI : T1Space W := ChartedSpace.t1Space (EuclideanHalfSpace (n + 1)) W
  set c : EuclideanHalfSpace (n + 1) := chartAt (EuclideanHalfSpace (n + 1)) x x with hc
  have hxT : x ∈ (chartAt (EuclideanHalfSpace (n + 1)) x).source :=
    mem_chart_source (EuclideanHalfSpace (n + 1)) x
  obtain ⟨e1⟩ := relChains_chart_iso (chartAt (EuclideanHalfSpace (n + 1)) x) x hxT k
  have hArg : IsOpen {y : EuclideanHalfSpace (n + 1) | y ≠ c} := isClosed_singleton.isOpen_compl
  have hcov : (chartAt (EuclideanHalfSpace (n + 1)) x).target ∪
      {y : EuclideanHalfSpace (n + 1) | y ≠ c} = Set.univ := by
    apply Set.eq_univ_of_forall
    intro y
    by_cases h : y = c
    · exact Or.inl (h ▸ (chartAt (EuclideanHalfSpace (n + 1)) x).map_source hxT)
    · exact Or.inr h
  obtain ⟨e2⟩ := excision_iso (TopCat.of (EuclideanHalfSpace (n + 1)))
    (chartAt (EuclideanHalfSpace (n + 1)) x).target {y : EuclideanHalfSpace (n + 1) | y ≠ c}
    (chartAt (EuclideanHalfSpace (n + 1)) x).open_target hArg hcov k
  exact ⟨e1 ≪≫ e2⟩

/-! ## The flat models -/

/-- **If the inclusion `A ↪ X` is a homotopy equivalence then `H_*(X,A) = 0`.** -/
theorem isZero_relChains_of_homotopyEquiv_incl {X : TopCat} {A : Set X}
    (g : X ⟶ TopCat.of A)
    (h1 : TopCat.Homotopy (Work.Cohomology.subtypeIncl X A ≫ g) (𝟙 (TopCat.of A)))
    (h2 : TopCat.Homotopy (g ≫ Work.Cohomology.subtypeIncl X A) (𝟙 X)) (k : ℕ) :
    IsZero ((Work.Cohomology.relChains X A).homology k) := by
  have hq : QuasiIso (Work.Cohomology.inclChains X A) := by
    rw [quasiIso_iff]
    intro i
    rw [quasiIsoAt_iff_isIso_homologyMap]
    exact Work.Cohomology.homologyEquiv ℤ (TopCat.of A) X
      (Work.Cohomology.subtypeIncl X A) g h1 h2 i
  exact (HomologicalComplex.exactAt_iff_isZero_homology (Work.Cohomology.relChains X A) k).mp
    ((Work.Cohomology.hPairShort_shortExact X A).acyclic_X₃ hq k)

/-- **The local homology of the half-space at a boundary point vanishes.** -/
theorem halfspace_boundary_isZero (n k : ℕ) (c : EuclideanHalfSpace (n + 1)) (hc : c.1 0 = 0) :
    IsZero ((Work.Cohomology.relChains (TopCat.of (EuclideanHalfSpace (n + 1)))
      {y : EuclideanHalfSpace (n + 1) | y ≠ c}).homology k) := by
  let X : TopCat := TopCat.of {y : EuclideanSpace ℝ (Fin (n + 1)) | 0 ≤ y 0}
  let A : Set X := {y | y ≠ c}
  let v : EuclideanSpace ℝ (Fin (n + 1)) := EuclideanSpace.single 0 1
  have hv0 : v 0 = 1 := by simp [v]
  have hy0 : ∀ y : ↥X, (0 : ℝ) ≤ (y : EuclideanSpace ℝ (Fin (n + 1))) 0 := fun y => y.2
  have hcoord : ∀ (y : ↥X) (t : ℝ),
      ((y : EuclideanSpace ℝ (Fin (n + 1))) + t • v) 0 =
        (y : EuclideanSpace ℝ (Fin (n + 1))) 0 + t := by
    intro y t
    simp [PiLp.add_apply, PiLp.smul_apply, hv0]
  have hmem : ∀ (y : ↥X) (t : ℝ), 0 ≤ t →
      0 ≤ ((y : EuclideanSpace ℝ (Fin (n + 1))) + t • v) 0 := by
    intro y t ht
    rw [hcoord y t]
    have := hy0 y
    linarith
  have hc' : c.1 0 = 0 := hc
  have hne1 : ∀ y : ↥X,
      (⟨(y : EuclideanSpace ℝ (Fin (n + 1))) + (1 : ℝ) • v, hmem y 1 zero_le_one⟩ : ↥X) ≠ c := by
    intro y h
    have h4 := Subtype.ext_iff.mp h
    have h3 : (y : EuclideanSpace ℝ (Fin (n + 1))) 0 + 1 = 0 := by
      have h5 : ((y : EuclideanSpace ℝ (Fin (n + 1))) + (1 : ℝ) • v) 0 = c.1 0 :=
        congrArg (fun w : EuclideanSpace ℝ (Fin (n + 1)) => w 0) h4
      rw [hcoord y 1, hc'] at h5
      exact h5
    have := hy0 y
    linarith
  have hneA : ∀ (y : ↥A) (t : ℝ) (ht : 0 ≤ t),
      (⟨(((y : ↥A) : ↥X) : EuclideanSpace ℝ (Fin (n + 1))) + t • v,
        hmem ((y : ↥A) : ↥X) t ht⟩ : ↥X) ≠ c := by
    intro y t ht h
    have h4 := Subtype.ext_iff.mp h
    have h2 : (((y : ↥A) : ↥X) : EuclideanSpace ℝ (Fin (n + 1))) 0 + t = 0 := by
      have h5 : ((((y : ↥A) : ↥X) : EuclideanSpace ℝ (Fin (n + 1))) + t • v) 0 = c.1 0 :=
        congrArg (fun w : EuclideanSpace ℝ (Fin (n + 1)) => w 0) h4
      rw [hcoord ((y : ↥A) : ↥X) t, hc'] at h5
      exact h5
    have ht0 : t = 0 := by have := hy0 ((y : ↥A) : ↥X); linarith
    have heq : ((((y : ↥A) : ↥X) : EuclideanSpace ℝ (Fin (n + 1))) + t • v) = c.1 := h4
    rw [ht0, zero_smul, add_zero] at heq
    exact (y.2 : ((y : ↥A) : ↥X) ≠ c) (Subtype.ext heq)
  have hcont0 : Continuous fun y : ↥X => (y : EuclideanSpace ℝ (Fin (n + 1))) :=
    continuous_subtype_val
  have hcontX : Continuous fun q : ↑unitInterval × ↥X =>
      (⟨(q.2 : EuclideanSpace ℝ (Fin (n + 1))) + (q.1 : ℝ) • v,
        hmem q.2 (q.1 : ℝ) q.1.2.1⟩ : ↥X) := by
    refine (((hcont0.comp continuous_snd).add ?_)).subtype_mk _
    exact Continuous.smul (continuous_subtype_val.comp continuous_fst) continuous_const
  have hcontA1 : Continuous fun q : ↑unitInterval × ↥A => ((q.2 : ↥A) : ↥X) :=
    continuous_subtype_val.comp continuous_snd
  have hcontA2 : Continuous fun q : ↑unitInterval × ↥A =>
      (((q.2 : ↥A) : ↥X) : EuclideanSpace ℝ (Fin (n + 1))) :=
    continuous_subtype_val.comp hcontA1
  have hcontA : Continuous fun q : ↑unitInterval × ↥A =>
      (⟨(((q.2 : ↥A) : ↥X) : EuclideanSpace ℝ (Fin (n + 1))) + (q.1 : ℝ) • v,
        hmem ((q.2 : ↥A) : ↥X) (q.1 : ℝ) q.1.2.1⟩ : ↥X) := by
    refine ((hcontA2.add ?_)).subtype_mk _
    exact Continuous.smul (continuous_subtype_val.comp continuous_fst) continuous_const
  let gfun : C(↥X, ↥A) :=
    ⟨fun y => ⟨⟨(y : EuclideanSpace ℝ (Fin (n + 1))) + (1 : ℝ) • v,
        hmem y 1 zero_le_one⟩, hne1 y⟩,
      (((hcont0.add (Continuous.const_smul continuous_const (1 : ℝ))).subtype_mk
        (fun y => hmem y 1 zero_le_one))).subtype_mk (fun y => hne1 y)⟩
  let g : X ⟶ TopCat.of A := TopCat.ofHom gfun
  let HF : C(↑unitInterval × ↥X, ↥X) :=
    ⟨fun q => ⟨(q.2 : EuclideanSpace ℝ (Fin (n + 1))) + (q.1 : ℝ) • v,
      hmem q.2 (q.1 : ℝ) q.1.2.1⟩, hcontX⟩
  let HAF : C(↑unitInterval × ↥A, ↥A) :=
    ⟨fun q => ⟨⟨(((q.2 : ↥A) : ↥X) : EuclideanSpace ℝ (Fin (n + 1))) + (q.1 : ℝ) • v,
      hmem ((q.2 : ↥A) : ↥X) (q.1 : ℝ) q.1.2.1⟩, hneA q.2 (q.1 : ℝ) q.1.2.1⟩,
      hcontA.subtype_mk (fun q => hneA q.2 (q.1 : ℝ) q.1.2.1)⟩
  have H0X : TopCat.Homotopy (𝟙 X) (g ≫ Work.Cohomology.subtypeIncl X A) :=
    ContinuousMap.Homotopy.mk HF
      (fun x => by
        change HF (0, x) = x
        apply Subtype.ext
        show (x : EuclideanSpace ℝ (Fin (n + 1))) + (((0 : ↑unitInterval) : ℝ)) • v =
          (x : EuclideanSpace ℝ (Fin (n + 1)))
        simp)
      (fun x => by
        change HF (1, x) = (g ≫ Work.Cohomology.subtypeIncl X A).hom x
        have hgf : (g ≫ Work.Cohomology.subtypeIncl X A).hom x =
            (⟨(x : EuclideanSpace ℝ (Fin (n + 1))) + (1 : ℝ) • v,
              hmem x 1 zero_le_one⟩ : ↥X) := rfl
        rw [hgf]
        apply Subtype.ext
        show (x : EuclideanSpace ℝ (Fin (n + 1))) + (((1 : ↑unitInterval) : ℝ)) • v =
          (x : EuclideanSpace ℝ (Fin (n + 1))) + (1 : ℝ) • v
        simp)
  have H0A : TopCat.Homotopy (𝟙 (TopCat.of A)) (Work.Cohomology.subtypeIncl X A ≫ g) :=
    ContinuousMap.Homotopy.mk HAF
      (fun a => by
        change HAF (0, a) = a
        apply Subtype.ext
        apply Subtype.ext
        show (((a : ↥A) : ↥X) : EuclideanSpace ℝ (Fin (n + 1))) +
          (((0 : ↑unitInterval) : ℝ)) • v = (((a : ↥A) : ↥X) : EuclideanSpace ℝ (Fin (n + 1)))
        simp)
      (fun a => by
        change HAF (1, a) = (Work.Cohomology.subtypeIncl X A ≫ g).hom a
        have hgf : (Work.Cohomology.subtypeIncl X A ≫ g).hom a =
            (⟨⟨(((a : ↥A) : ↥X) : EuclideanSpace ℝ (Fin (n + 1))) + (1 : ℝ) • v,
              hmem ((a : ↥A) : ↥X) 1 zero_le_one⟩, hne1 ((a : ↥A) : ↥X)⟩ : ↥A) := rfl
        rw [hgf]
        apply Subtype.ext
        apply Subtype.ext
        show (((a : ↥A) : ↥X) : EuclideanSpace ℝ (Fin (n + 1))) +
          (((1 : ↑unitInterval) : ℝ)) • v =
          (((a : ↥A) : ↥X) : EuclideanSpace ℝ (Fin (n + 1))) + (1 : ℝ) • v
        simp)
  exact isZero_relChains_of_homotopyEquiv_incl g H0A.symm H0X.symm k

/-- The inclusion of a ball lying in the half-space, as a homeomorphism onto the ball. -/
def halfspaceBallHomeo (n : ℕ) (B : Set (EuclideanSpace ℝ (Fin (n + 1))))
    (hB : ∀ z ∈ B, 0 ≤ z 0) :
    ↥{y : EuclideanHalfSpace (n + 1) | y.1 ∈ B} ≃ₜ ↥B where
  toFun y := ⟨y.1.1, y.2⟩
  invFun z := ⟨⟨z.1, hB z.1 z.2⟩, z.2⟩
  left_inv y := Subtype.ext (Subtype.ext rfl)
  right_inv z := Subtype.ext rfl
  continuous_toFun := Continuous.subtype_mk
    (continuous_subtype_val.comp continuous_subtype_val) _
  continuous_invFun := Continuous.subtype_mk
    (Continuous.subtype_mk continuous_subtype_val _) _

/-- **The local homology of the half-space at an interior point is `ℤ`.** -/
theorem halfspace_interior_top_iso (n : ℕ) (c : EuclideanHalfSpace (n + 1)) (hc : 0 < c.1 0) :
    Nonempty ((Work.Cohomology.relChains (TopCat.of (EuclideanHalfSpace (n + 1)))
      {y : EuclideanHalfSpace (n + 1) | y ≠ c}).homology (n + 1) ≅ ModuleCat.of ℤ ℤ) := by
  haveI : T1Space (EuclideanHalfSpace (n + 1)) := t1Space_halfSpace n
  have hopen : IsOpen {z : EuclideanSpace ℝ (Fin (n + 1)) | 0 < z 0} :=
    isOpen_lt continuous_const (PiLp.continuous_apply 2 (fun _ : Fin (n + 1) => ℝ) 0)
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hopen c.1 hc
  let B : Set (EuclideanSpace ℝ (Fin (n + 1))) := Metric.ball c.1 r
  let BH : Set (EuclideanHalfSpace (n + 1)) := {y | y.1 ∈ B}
  have hBle : ∀ z ∈ B, 0 ≤ z 0 := fun z hz => le_of_lt (hball hz)
  have hBH : IsOpen BH := Metric.isOpen_ball.preimage continuous_subtype_val
  have hA : IsOpen {y : EuclideanHalfSpace (n + 1) | y ≠ c} := isClosed_singleton.isOpen_compl
  have hcB : c.1 ∈ B := Metric.mem_ball_self hr
  have hcov : BH ∪ {y : EuclideanHalfSpace (n + 1) | y ≠ c} = Set.univ := by
    apply Set.eq_univ_of_forall
    intro y
    by_cases h : y = c
    · exact Or.inl (h ▸ hcB)
    · exact Or.inr h
  obtain ⟨e1⟩ := excision_iso (TopCat.of (EuclideanHalfSpace (n + 1))) BH
    {y : EuclideanHalfSpace (n + 1) | y ≠ c} hBH hA hcov (n + 1)
  have hA1 : ∀ y : ↥BH, y ∈ {y : ↥BH | (y : EuclideanHalfSpace (n + 1)) ≠ c} ↔
      halfspaceBallHomeo n B hBle y ∈ {z : ↥B | z.1 ≠ c.1} := by
    intro y
    constructor
    · intro hy heq
      exact hy (Subtype.ext heq)
    · intro hy hyx
      exact hy (congrArg Subtype.val hyx)
  obtain ⟨e2⟩ := homeoRelChainsIso (X := ↥BH) (Y := ↥B) (halfspaceBallHomeo n B hBle)
    {y : ↥BH | (y : EuclideanHalfSpace (n + 1)) ≠ c} {z : ↥B | z.1 ≠ c.1} hA1 (n + 1)
  obtain ⟨e3⟩ := Work.Cohomology.ballPairHomologyTop_aux (n + 1) (Nat.succ_le_succ (Nat.zero_le n))
    c.1 r hr
  exact ⟨e1.symm ≪≫ e2 ≪≫ e3⟩

end

/-!
# The local homology of a manifold with boundary

For a topological space `W` charted in the half-space model `EuclideanHalfSpace (n+1)` (so that `W`
is a manifold with boundary `(𝓡∂ (n+1)).boundary W`), the local homology `H_{n+1}(W, W ∖ {x})` is
`ℤ` at every **interior** point and `0` at every **boundary** point.

This is the local input of the relative fundamental class `[W, ∂W] ∈ H_{n+1}(W, ∂W; ℤ)` of a compact
oriented manifold with boundary (ORIENT, item 2 of the deliverable; the field `w_fund` of
`Work.ThomBordism.NullBordismFamily` is only required at interior points precisely because of the
second half of this statement).

**Route** (a chart reduces both cases to the flat model).
* Excision plus the chart homeomorphism identify `H_{n+1}(W, W∖{x})` with `H_{n+1}(H, H∖{e x})` for
  a half-space chart `e` at `x` and a small (in the half-space) open neighbourhood `H` of `e x`.
* If `e x` is an interior point, `H` can be taken to be a Euclidean ball and the existing flat
  computation applies (`Work.Cohomology.localHomology`, `Work.Cohomology.ballPairHomologyTop`).
  (A global `ChartedSpace (EuclideanSpace ℝ (Fin (n+1))) W` cannot exist when the boundary is
  nonempty, so the interior case needs the local/excision version of that computation; see
  `Work.Surgery.exists_interiorChart` for the interior charts.)
* If `e x` lies on the hyperplane, `H` can be taken to be a half-ball, and `H_{n+1}(H, H∖{0}) = 0`
  for the half-space `H = EuclideanHalfSpace (n+1)` by the long exact sequence of the pair together
  with the contractibility of `H` and of `H ∖ {0}` (the latter deformation retracts onto the closed
  hemisphere `{y | ‖y‖ = 1 ∧ 0 ≤ y 0}`, which is homeomorphic to a closed ball).
-/
theorem localHomology_corner (n : ℕ) (W : TopCat) [T2Space W]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W] (x : W) :
    (x ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W →
        Nonempty (Work.Orient.LocH W (n + 1) x ≅ ModuleCat.of ℤ ℤ)) ∧
      (x ∈ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W →
        CategoryTheory.Limits.IsZero (Work.Orient.LocH W (n + 1) x)) := by
  have hce : (extChartAt (modelWithCornersEuclideanHalfSpace (n + 1)) x x :
      EuclideanSpace ℝ (Fin (n + 1))) =
      (chartAt (EuclideanHalfSpace (n + 1)) x x).1 := by
    simp [extChartAt_coe]
  constructor
  · intro hxnot
    have hInt : (modelWithCornersEuclideanHalfSpace (n + 1)).IsInteriorPoint x :=
      ((modelWithCornersEuclideanHalfSpace (n + 1)).isInteriorPoint_iff_not_isBoundaryPoint x).mpr
        hxnot
    have hpos : 0 < (chartAt (EuclideanHalfSpace (n + 1)) x x).1 0 := by
      have h1 : (extChartAt (modelWithCornersEuclideanHalfSpace (n + 1)) x x :
          EuclideanSpace ℝ (Fin (n + 1))) ∈
          interior (Set.range (modelWithCornersEuclideanHalfSpace (n + 1))) := hInt
      have h2 : (chartAt (EuclideanHalfSpace (n + 1)) x x).1 ∈
          interior (Set.range (modelWithCornersEuclideanHalfSpace (n + 1))) := by
        rw [← hce]; exact h1
      rw [show Set.range (modelWithCornersEuclideanHalfSpace (n + 1)) =
          {z : EuclideanSpace ℝ (Fin (n + 1)) | 0 ≤ z 0} from
          range_euclideanHalfSpace (n + 1), interior_halfSpace 2 0 0] at h2
      exact h2
    obtain ⟨e1⟩ := locH_iso_halfspace n (n + 1) W x
    obtain ⟨e2⟩ := halfspace_interior_top_iso n (chartAt (EuclideanHalfSpace (n + 1)) x x) hpos
    exact ⟨e1 ≪≫ e2⟩
  · intro hxbnd
    have hb : (modelWithCornersEuclideanHalfSpace (n + 1)).IsBoundaryPoint x := hxbnd
    have h0 : (chartAt (EuclideanHalfSpace (n + 1)) x x).1 0 = 0 := by
      have h1 : (extChartAt (modelWithCornersEuclideanHalfSpace (n + 1)) x x :
          EuclideanSpace ℝ (Fin (n + 1))) ∈
          frontier (Set.range (modelWithCornersEuclideanHalfSpace (n + 1))) := hb
      have h2 : (chartAt (EuclideanHalfSpace (n + 1)) x x).1 ∈
          frontier (Set.range (modelWithCornersEuclideanHalfSpace (n + 1))) := by
        rw [← hce]; exact h1
      rw [frontier_range_modelWithCornersEuclideanHalfSpace (n + 1)] at h2
      exact h2.symm
    obtain ⟨e1⟩ := locH_iso_halfspace n (n + 1) W x
    exact IsZero.of_iso (halfspace_boundary_isZero n (n + 1)
      (chartAt (EuclideanHalfSpace (n + 1)) x x) h0) e1

end Work.Orient.Boundary
