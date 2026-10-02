import Mathlib
import Submission.Work.Thom.ThomClass
import Submission.Work.Thom.ChartOrientation
import Submission.Work.Thom.Orientation.Mpun_gaugeEnd_neg
import Submission.Work.Thom.Continuous
import Submission.Work.Thom.Coh_zero_cover_injective_gen
import Submission.Work.ThomBordism.Grassmann.localThomMapChartInjective

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# The Euler class of an odd-rank oriented real bundle is 2-torsion

An integral Thom class of a real bundle of odd rank `n` restricts to a *generator* of
`H^n(fibre, fibre∖0) ≅ ℤ` on every fibre, and the fibrewise negation `v ↦ -v` acts on that
generator by the degree `(-1)^n = -1` of the antipodal map of `S^{n-1}`.  Hence the negation — a
homeomorphism of the Thom pair `(E,E∖0)` over the identity — sends the Thom class to its negative,
`a^*τ = -τ`, and therefore the Euler class `e = z^*τ` satisfies `e = z^*(a^*τ) = -e`, i.e. `2e = 0`.

This file builds the ingredients:

* `negMap Z` — the fibrewise negation `p ↦ ⟨p.1, -p.2⟩` of a real bundle, with its continuity;
* `negPiece` — its restriction to a piece of the total space over `W ⊆ B`;
* `trivNeg_eq_neg` — **the model computation**: for odd `n` the fibrewise negation of the *trivial*
  bundle acts as `-1` on `H^n(↥W × ℝⁿ, ↥W × (ℝⁿ∖0))`.  It is here that `(-1)^n = -1`, i.e. the
  oddness of the rank, enters;
* `chartHomeo_comp_negPiece` — the chart homeomorphism intertwines the fibrewise negation of the
  bundle with that of the model;
* `negPiece_pullback` — consequently the restriction of *any* class to a chart piece is negated by
  the fibrewise negation.

-/

namespace Work.ThomBordism.Grassmann

open Work.Thom Work.TangentClasses CategoryTheory

noncomputable section

variable {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {ι : Type}

/-! ## The fibrewise negation of a real bundle -/

/-- **The fibrewise negation** of a real bundle: `p ↦ ⟨p.1, -p.2⟩`.  It is continuous because it is
the fibrewise rescaling by the constant function `-1` (`Work.Thom.continuous_smul_section`). -/
def negMap (Z : RealBundle B F ι) : C(Z.TotalSpace, Z.TotalSpace) :=
  ⟨fun p => ⟨p.1, -p.2⟩, by
    have h := Work.Thom.continuous_smul_section Z (ContinuousMap.id Z.TotalSpace)
      ⟨fun _ => (-1 : ℝ), continuous_const⟩
    have h2 : (fun x : Z.TotalSpace => (⟨x.proj, (-1:ℝ) • x.snd⟩ : Z.TotalSpace))
        = (fun p : Z.TotalSpace => (⟨p.1, -p.2⟩ : Z.TotalSpace)) := by
      funext p
      show (⟨p.1, (-1:ℝ) • p.2⟩ : Z.TotalSpace) = ⟨p.1, -p.2⟩
      rw [neg_one_smul]
    have h' : Continuous (fun x : Z.TotalSpace =>
        (⟨x.proj, (-1:ℝ) • x.snd⟩ : Z.TotalSpace)) := h
    rw [h2] at h'
    exact h'⟩

@[simp] theorem negMap_apply (Z : RealBundle B F ι) (p : Z.TotalSpace) :
    negMap Z p = ⟨p.1, -p.2⟩ := rfl

/-- The fibrewise negation preserves the complement of the zero section. -/
theorem negMap_mem (Z : RealBundle B F ι) : ∀ p ∈ Work.Thom.zeroComplement Z,
    negMap Z p ∈ Work.Thom.zeroComplement Z := by
  intro p hp
  rw [Work.Thom.mem_zeroComplement] at hp ⊢
  exact neg_ne_zero.mpr hp

/-- The fibrewise negation fixes the zero section. -/
theorem negMap_comp_zeroSection (Z : RealBundle B F ι) :
    (negMap Z).comp (Work.Thom.zeroSection Z) = Work.Thom.zeroSection Z := by
  apply ContinuousMap.ext
  intro b
  show (⟨b, -(0:F)⟩ : Z.TotalSpace) = (⟨b, (0:F)⟩ : Z.TotalSpace)
  simp

/-- The fibrewise negation is an involution. -/
theorem negMap_comp_negMap (Z : RealBundle B F ι) :
    (negMap Z).comp (negMap Z) = ContinuousMap.id Z.TotalSpace := by
  apply ContinuousMap.ext
  intro p
  show (⟨p.1, -(-p.2)⟩ : Z.TotalSpace) = p
  simp

/-- The fibrewise negation restricted to the piece of the total space over `W ⊆ B`. -/
def negPiece (Z : RealBundle B F ι) (W : Set B) :
    C(↥(Z.proj ⁻¹' W), ↥(Z.proj ⁻¹' W)) :=
  ⟨fun p => ⟨negMap Z p.1, p.2⟩, by
    refine Continuous.subtype_mk ?_ (fun p => p.2)
    exact (negMap Z).continuous.comp continuous_subtype_val⟩

@[simp] theorem negPiece_apply (Z : RealBundle B F ι) (W : Set B)
    (p : ↥(Z.proj ⁻¹' W)) : (negPiece Z W p : Z.TotalSpace) = negMap Z p.1 := rfl

/-- The fibrewise negation of a piece preserves the zero complement of the piece. -/
theorem negPiece_mem (Z : RealBundle B F ι) (W : Set B) :
    ∀ p ∈ Work.Thom.pieceZero Z W, negPiece Z W p ∈ Work.Thom.pieceZero Z W :=
  fun p hp => negMap_mem Z p.1 hp

/-- The fibrewise negation commutes with the inclusion of a piece in the total space. -/
theorem negMap_comp_subtypeMap (Z : RealBundle B F ι) (W : Set B) :
    (negMap Z).comp (Work.Thom.subtypeMap (Z.proj ⁻¹' W))
      = (Work.Thom.subtypeMap (Z.proj ⁻¹' W)).comp (negPiece Z W) := by
  apply ContinuousMap.ext
  intro p
  rfl

/-! ## The model computation: the negation of the trivial bundle acts by `-1` -/

/-- **The fibrewise negation of the trivial bundle of rank `n` over `Y`**: the gauge end of the
constant gauge `-1`. -/
def trivNeg (n : ℕ) (Y : Type) [TopologicalSpace Y] :
    C(Y × EuclideanSpace ℝ (Fin n), Y × EuclideanSpace ℝ (Fin n)) :=
  Work.Thom.gaugeEnd (fun _ : Y => -(ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))))
    continuous_const

theorem trivNeg_apply (n : ℕ) (Y : Type) [TopologicalSpace Y]
    (p : Y × EuclideanSpace ℝ (Fin n)) : trivNeg n Y p = (p.1, -p.2) := by
  rw [trivNeg, Work.Thom.gaugeEnd_apply]
  rfl

/-- The determinant of the gauge `-1` on `ℝⁿ` is `(-1)^n`, hence negative for odd `n`. -/
theorem det_neg_one_gauge_neg {n : ℕ} (hn : Odd n) :
    LinearMap.det ((-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))).toLinearMap) < 0 := by
  have h1 : ((-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))).toLinearMap)
      = -(1 : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)) := by
    ext v
    simp
  rw [h1]
  have h : (-(1 : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)))
      = (-1:ℝ) • (1 : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)) := by simp
  rw [h, LinearMap.det_smul]
  simp [Odd.neg_one_pow hn]

/-- The negation of the trivial bundle covers the identity: the first projection is unchanged. -/
theorem projFstA_comp_trivNeg (n : ℕ) (Y : Type) [TopologicalSpace Y] :
    (Work.Thom.projFstA Y n).comp (trivNeg n Y) = Work.Thom.projFstA Y n := by
  apply ContinuousMap.ext
  intro p
  rw [ContinuousMap.comp_apply, trivNeg_apply]
  rfl

/-- The negation preserves the punctured part. -/
theorem trivNeg_mem (n : ℕ) (Y : Type) [TopologicalSpace Y] :
    ∀ p ∈ Work.Thom.Punct Y n, trivNeg n Y p ∈ Work.Thom.Punct Y n := by
  intro p hp
  rw [trivNeg_apply]
  show -p.2 ≠ 0
  exact neg_ne_zero.mpr hp

/-! ## Transporting along a degree equality -/

/-- Negation commutes with the transport along an equality of degrees. -/
theorem eqRec_neg {α : Sort*} {β : α → Type*} [∀ a, AddCommGroup (β a)] {a b : α} (h : a = b)
    (x : β a) : h ▸ (-x) = -(h ▸ x) := by cases h; rfl

/-- The transport of zero along an equality of degrees is zero. -/
theorem eqRec_zero {α : Sort*} {β : α → Type*} [∀ a, AddGroup (β a)] {a b : α} (h : a = b) :
    h ▸ (0 : β a) = 0 := by cases h; rfl

/-- The restriction of a relative class to a piece commutes with a change of degree. -/
theorem pieceRes_cast (Z : RealBundle B F ι) (W : Set B) {a b : ℕ} (h : a = b)
    (x : Work.Thom.OpenThom Z a) :
    (Work.Thom.PieceRes Z W b).hom (h ▸ x)
      = h ▸ ((Work.Thom.PieceRes Z W a).hom x) := by
  cases h
  rfl

/-- The transport along an equality of degrees is injective. -/
theorem eqRec_injective {α : Sort*} {β : α → Type*} {a b : α} (h : a = b) (x y : β a)
    (hxy : h ▸ x = h ▸ y) : x = y := by cases h; exact hxy

/-- Transporting a homology class along an equality of degrees commutes with `homologyMap`. -/
theorem homologyMap_cast' {R : Type} [CommRing R] {K L : CochainComplex (ModuleCat R) ℕ}
    (φ : K ⟶ L) {a b : ℕ} (h : a = b) (x : K.homology a) :
    (HomologicalComplex.homologyMap φ b).hom (h ▸ x)
      = h ▸ ((HomologicalComplex.homologyMap φ a).hom x) := by cases h; rfl

/-! ## The model computation: the negation of the trivial bundle acts by `-1` -/

/-- **THE MODEL COMPUTATION.**  For odd `n` the fibrewise negation of the trivial bundle of rank `n`
over `Y` acts as `-1` on the *whole* relative cohomology `H^n(Y × ℝⁿ, Y × (ℝⁿ∖0))`: every class
there is `π^*(x) ⌣ Mpun` (`Work.Thom.Mpun_isModel`), the negation fixes `π^*(x)` (it covers the
identity) and negates `Mpun` (`Work.Thom.Orientation.Mpun_gaugeEnd_neg`, the determinant of `-1`
being `(-1)^n = -1`). -/
theorem trivNeg_eq_neg (n : ℕ) (hn : Odd n) (Y : Type) [TopologicalSpace Y]
    (α : RelCoh ℤ n (Y × EuclideanSpace ℝ (Fin n)) (Work.Thom.Punct Y n)) :
    (Work.Thom.relCohMap (trivNeg n Y) (Work.Thom.Punct Y n) (Work.Thom.Punct Y n)
      (trivNeg_mem n Y) ℤ n).hom α = -α := by
  have key : ∀ β : RelCoh ℤ (0 + n) (Y × EuclideanSpace ℝ (Fin n)) (Work.Thom.Punct Y n),
      (Work.Thom.relCohMap (trivNeg n Y) (Work.Thom.Punct Y n) (Work.Thom.Punct Y n)
        (trivNeg_mem n Y) ℤ (0 + n)).hom β = -β := by
    intro β
    obtain ⟨x, hx⟩ := (Work.Thom.Mpun_isModel n Y 0).2 β
    rw [← hx]
    rw [Work.Thom.mixedCupC_pairNatural (trivNeg n Y) (Work.Thom.Punct Y n) (Work.Thom.Punct Y n)
      (trivNeg_mem n Y) 0 n ((Work.Thom.CohMap (Work.Thom.projFstA Y n) ℤ 0).hom x)
      (Work.Thom.Mpun n Y)]
    have hcoh : (Work.Thom.CohMap (trivNeg n Y) ℤ 0).hom
        ((Work.Thom.CohMap (Work.Thom.projFstA Y n) ℤ 0).hom x)
        = (Work.Thom.CohMap (Work.Thom.projFstA Y n) ℤ 0).hom x := by
      rw [Work.Thom.CohMap_comp_apply (trivNeg n Y) (Work.Thom.projFstA Y n) ℤ 0 x,
        projFstA_comp_trivNeg]
    rw [hcoh]
    have hmem : ∀ p ∈ Work.Thom.Punct Y n, Work.Thom.gaugeEnd
        (fun _ : Y => -(ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)))) continuous_const p
        ∈ Work.Thom.Punct Y n := by
      intro p hp
      rw [Work.Thom.gaugeEnd_apply]
      show (-p.2) ≠ 0
      exact neg_ne_zero.mpr hp
    have hmp : (Work.Thom.relCohMap (trivNeg n Y) (Work.Thom.Punct Y n) (Work.Thom.Punct Y n)
        (trivNeg_mem n Y) ℤ n).hom (Work.Thom.Mpun n Y) = -(Work.Thom.Mpun n Y) := by
      rw [Work.Thom.relCohMap_hcongrA (trivNeg n Y) (Work.Thom.Punct Y n) (Work.Thom.Punct Y n)
        (trivNeg_mem n Y) hmem ℤ n]
      exact Work.Thom.Orientation.Mpun_gaugeEnd_neg n (by rcases hn with ⟨k, hk⟩; omega) (Y := Y)
        (fun _ : Y => -(ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)))) continuous_const
        (fun y => det_neg_one_gauge_neg hn)
    rw [hmp]
    exact (map_neg (mixedCupC ℤ (Work.Thom.Punct Y n) 0 n
      ((Work.Thom.CohMap (Work.Thom.projFstA Y n) ℤ 0).hom x)) (Work.Thom.Mpun n Y))
  have hcast : (Work.Thom.relCohMap (trivNeg n Y) (Work.Thom.Punct Y n) (Work.Thom.Punct Y n)
        (trivNeg_mem n Y) ℤ (0 + n)).hom ((Nat.zero_add n).symm ▸ α)
      = (Nat.zero_add n).symm ▸ ((Work.Thom.relCohMap (trivNeg n Y) (Work.Thom.Punct Y n)
          (Work.Thom.Punct Y n) (trivNeg_mem n Y) ℤ n).hom α) :=
    homologyMap_cast'
      (Work.Cohomology.relComplexMap (X₁ := TopCat.of (Y × EuclideanSpace ℝ (Fin n)))
        (X₂ := TopCat.of (Y × EuclideanSpace ℝ (Fin n))) ℤ (Work.Thom.Punct Y n)
        (Work.Thom.Punct Y n) (TopCat.ofHom (trivNeg n Y)) (trivNeg_mem n Y))
      (Nat.zero_add n).symm α
  refine eqRec_injective
    (β := fun m => ↥(RelCoh ℤ m (Y × EuclideanSpace ℝ (Fin n)) (Work.Thom.Punct Y n)))
    (Nat.zero_add n).symm
    ((Work.Thom.relCohMap (trivNeg n Y) (Work.Thom.Punct Y n)
      (Work.Thom.Punct Y n) (trivNeg_mem n Y) ℤ n).hom α) (-α) ?_
  calc (Nat.zero_add n).symm ▸ ((Work.Thom.relCohMap (trivNeg n Y) (Work.Thom.Punct Y n)
          (Work.Thom.Punct Y n) (trivNeg_mem n Y) ℤ n).hom α)
      = (Work.Thom.relCohMap (trivNeg n Y) (Work.Thom.Punct Y n) (Work.Thom.Punct Y n)
          (trivNeg_mem n Y) ℤ (0 + n)).hom ((Nat.zero_add n).symm ▸ α) := hcast.symm
    _ = -((Nat.zero_add n).symm ▸ α) := key ((Nat.zero_add n).symm ▸ α)
    _ = (Nat.zero_add n).symm ▸ (-α) :=
        (eqRec_neg (β := fun m => ↥(RelCoh ℤ m (Y × EuclideanSpace ℝ (Fin n))
            (Work.Thom.Punct Y n))) (Nat.zero_add n).symm α).symm

/-! ## The chart homeomorphism intertwines the two negations -/

/-- The chart homeomorphism carries the fibrewise negation of the bundle to the fibrewise negation
of the trivial bundle over `W`. -/
theorem chartHomeo_comp_negPiece (Z : RealBundle B F ι) (n : ℕ)
    (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin n)) (i : ι) (W : Set B) (hW : W ⊆ Z.baseSet i) :
    ((Work.Thom.chartHomeo Z n e i W hW :
        ↥(Z.proj ⁻¹' W) ≃ₜ (↥W × EuclideanSpace ℝ (Fin n))) :
        C(↥(Z.proj ⁻¹' W), ↥W × EuclideanSpace ℝ (Fin n))).comp (negPiece Z W)
      = (trivNeg n ↥W).comp ((Work.Thom.chartHomeo Z n e i W hW :
          ↥(Z.proj ⁻¹' W) ≃ₜ (↥W × EuclideanSpace ℝ (Fin n))) :
          C(↥(Z.proj ⁻¹' W), ↥W × EuclideanSpace ℝ (Fin n))) := by
  apply ContinuousMap.ext
  intro p
  have h1 : (Work.Thom.chartHomeo Z n e i W hW) (negPiece Z W p)
      = (⟨⟨Z.proj p.1, p.2⟩, e ((Z.coordChange (Z.indexAt (p.1).1) i (p.1).1) (-(p.1).2))⟩
        : ↥W × EuclideanSpace ℝ (Fin n)) := by
    rw [Work.Thom.chartHomeo_apply]
    rfl
  have h2 : (Work.Thom.chartHomeo Z n e i W hW) p
      = (⟨⟨Z.proj p.1, p.2⟩, e ((Z.coordChange (Z.indexAt (p.1).1) i (p.1).1) (p.1).2)⟩
        : ↥W × EuclideanSpace ℝ (Fin n)) := by
    rw [Work.Thom.chartHomeo_apply]
  simp only [ContinuousMap.comp_apply, trivNeg_apply]
  rw [show (↑(Work.Thom.chartHomeo Z n e i W hW) :
        C(↥(Z.proj ⁻¹' W), ↥W × EuclideanSpace ℝ (Fin n))) (negPiece Z W p)
      = (Work.Thom.chartHomeo Z n e i W hW) (negPiece Z W p) from rfl,
    show (↑(Work.Thom.chartHomeo Z n e i W hW) :
        C(↥(Z.proj ⁻¹' W), ↥W × EuclideanSpace ℝ (Fin n))) p
      = (Work.Thom.chartHomeo Z n e i W hW) p from rfl,
    h1, h2]
  simp only [Prod.fst, Prod.snd]
  rw [map_neg, map_neg]

/-! ## The local computation -/

/-- The inverse chart homeomorphism intertwines the model negation with the negation of the piece
(the `symm` form of `chartHomeo_comp_negPiece`). -/
theorem negPiece_comp_chartHomeoSymm (Z : RealBundle B F ι) (n : ℕ)
    (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin n)) (i : ι) (W : Set B) (hW : W ⊆ Z.baseSet i) :
    (negPiece Z W).comp (((Work.Thom.chartHomeo Z n e i W hW).symm :
        ↥W × EuclideanSpace ℝ (Fin n) ≃ₜ ↥(Z.proj ⁻¹' W)) :
        C(↥W × EuclideanSpace ℝ (Fin n), ↥(Z.proj ⁻¹' W)))
      = (((Work.Thom.chartHomeo Z n e i W hW).symm :
        ↥W × EuclideanSpace ℝ (Fin n) ≃ₜ ↥(Z.proj ⁻¹' W)) :
        C(↥W × EuclideanSpace ℝ (Fin n), ↥(Z.proj ⁻¹' W))).comp (trivNeg n ↥W) := by
  apply ContinuousMap.ext
  intro q
  have h := congrArg (fun (f : C(↥(Z.proj ⁻¹' W), ↥W × EuclideanSpace ℝ (Fin n))) =>
      f ((Work.Thom.chartHomeo Z n e i W hW).symm q)) (chartHomeo_comp_negPiece Z n e i W hW)
  simp only [ContinuousMap.comp_apply] at h
  change (Work.Thom.chartHomeo Z n e i W hW)
      ((negPiece Z W) ((Work.Thom.chartHomeo Z n e i W hW).symm q))
    = (trivNeg n ↥W)
      ((Work.Thom.chartHomeo Z n e i W hW) ((Work.Thom.chartHomeo Z n e i W hW).symm q)) at h
  rw [Homeomorph.apply_symm_apply] at h
  have h4 := congrArg (fun x => (Work.Thom.chartHomeo Z n e i W hW).symm x) h
  rw [Homeomorph.symm_apply_apply] at h4
  exact h4

/-- **The local computation.**  On every chart piece of the bundle the fibrewise negation acts on
the relative cohomology by `-1`; consequently it negates the restriction of any class, in
particular of a Thom class. -/
theorem negPiece_restrict (Z : RealBundle B F ι) (n : ℕ) (hn : Odd n)
    (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin n)) (i : ι) (W : Set B) (hW : W ⊆ Z.baseSet i)
    (σ : Work.Thom.OpenThom Z n) :
    (Work.Thom.PieceRes Z W n).hom
        ((Work.Thom.relCohMap (negMap Z) (Work.Thom.zeroComplement Z) (Work.Thom.zeroComplement Z)
          (negMap_mem Z) ℤ n).hom σ)
      = -(Work.Thom.PieceRes Z W n).hom σ := by
  have hpr : (Work.Thom.PieceRes Z W n)
      = Work.Thom.relCohMap (Work.Thom.subtypeMap (Z.proj ⁻¹' W)) (Work.Thom.pieceZero Z W)
          (Work.Thom.zeroComplement Z) (fun _ hy => hy) ℤ n := rfl
  -- (1) pull the outer pullback past the negation
  have h1 := Work.Thom.relCohMap_compA_apply (Work.Thom.pieceZero Z W) (Work.Thom.zeroComplement Z)
    (Work.Thom.zeroComplement Z) (Work.Thom.subtypeMap (Z.proj ⁻¹' W)) (negMap Z)
    (fun _ hy => hy) (negMap_mem Z) (fun _ hy => negMap_mem Z _ hy) ℤ n σ
  -- (2) replace the composite of the two maps
  have h2 : (ModuleCat.Hom.hom
        (Work.Thom.relCohMap ((negMap Z).comp (Work.Thom.subtypeMap (Z.proj ⁻¹' W)))
          (Work.Thom.pieceZero Z W) (Work.Thom.zeroComplement Z) (fun _ hy => negMap_mem Z _ hy)
          ℤ n)) σ
      = (ModuleCat.Hom.hom
        (Work.Thom.relCohMap ((Work.Thom.subtypeMap (Z.proj ⁻¹' W)).comp (negPiece Z W))
          (Work.Thom.pieceZero Z W) (Work.Thom.zeroComplement Z) (fun _ hy => negMap_mem Z _ hy)
          ℤ n)) σ := by
    rw [Work.Thom.relCohMap_congrA (Work.Thom.pieceZero Z W) (Work.Thom.zeroComplement Z)
      (negMap_comp_subtypeMap Z W) (fun _ hy => negMap_mem Z _ hy)
      (fun _ hy => negMap_mem Z _ hy) ℤ n]
  -- (3) split off the negated piece
  have h3 : (ModuleCat.Hom.hom
        (Work.Thom.relCohMap ((Work.Thom.subtypeMap (Z.proj ⁻¹' W)).comp (negPiece Z W))
          (Work.Thom.pieceZero Z W) (Work.Thom.zeroComplement Z) (fun _ hy => negMap_mem Z _ hy)
          ℤ n)) σ
      = (Work.Thom.relCohMap (negPiece Z W) (Work.Thom.pieceZero Z W) (Work.Thom.pieceZero Z W)
          (negPiece_mem Z W) ℤ n).hom
          ((Work.Thom.relCohMap (Work.Thom.subtypeMap (Z.proj ⁻¹' W)) (Work.Thom.pieceZero Z W)
            (Work.Thom.zeroComplement Z) (fun _ hy => hy) ℤ n).hom σ) :=
    (Work.Thom.relCohMap_compA_apply (Work.Thom.pieceZero Z W) (Work.Thom.pieceZero Z W)
      (Work.Thom.zeroComplement Z) (negPiece Z W) (Work.Thom.subtypeMap (Z.proj ⁻¹' W))
      (negPiece_mem Z W) (fun _ hy => hy) (fun _ hy => negMap_mem Z _ hy) ℤ n σ).symm
  -- (4) the model computation, transported along the chart homeomorphism
  have h4 : (Work.Thom.relCohMap (negPiece Z W) (Work.Thom.pieceZero Z W)
        (Work.Thom.pieceZero Z W) (negPiece_mem Z W) ℤ n).hom
        ((Work.Thom.relCohMap (Work.Thom.subtypeMap (Z.proj ⁻¹' W)) (Work.Thom.pieceZero Z W)
          (Work.Thom.zeroComplement Z) (fun _ hy => hy) ℤ n).hom σ)
      = -((Work.Thom.relCohMap (Work.Thom.subtypeMap (Z.proj ⁻¹' W)) (Work.Thom.pieceZero Z W)
          (Work.Thom.zeroComplement Z) (fun _ hy => hy) ℤ n).hom σ) := by
    set X : ↥(Work.Thom.PieceCoh Z W n) :=
      (Work.Thom.relCohMap (Work.Thom.subtypeMap (Z.proj ⁻¹' W)) (Work.Thom.pieceZero Z W)
        (Work.Thom.zeroComplement Z) (fun _ hy => hy) ℤ n).hom σ with hX
    have key : ∀ q : ↥W × EuclideanSpace ℝ (Fin n),
        (Work.Thom.chartHomeo Z n e i W hW)
          (((Work.Thom.chartHomeo Z n e i W hW).symm :
            C(↥W × EuclideanSpace ℝ (Fin n), ↥(Z.proj ⁻¹' W))) q) = q := by
      intro q
      change (Work.Thom.chartHomeo Z n e i W hW)
        ((Work.Thom.chartHomeo Z n e i W hW).symm q) = q
      exact Homeomorph.apply_symm_apply _ _
    have hmem_iff : ∀ q : ↥W × EuclideanSpace ℝ (Fin n),
        q ∈ Work.Thom.Punct ↥W n ↔
          ((Work.Thom.chartHomeo Z n e i W hW).symm :
            C(↥W × EuclideanSpace ℝ (Fin n), ↥(Z.proj ⁻¹' W))) q
            ∈ Work.Thom.pieceZero Z W := by
      intro q
      rw [Work.Thom.chartHomeo_mem_punct Z n e i W hW, key]
    have hmem' : ∀ q ∈ Work.Thom.Punct ↥W n,
        ((Work.Thom.chartHomeo Z n e i W hW).symm :
          C(↥W × EuclideanSpace ℝ (Fin n), ↥(Z.proj ⁻¹' W))) q
          ∈ Work.Thom.pieceZero Z W := fun q hq => (hmem_iff q).1 hq
    suffices h : (Work.Thom.relCohMap
          (((Work.Thom.chartHomeo Z n e i W hW).symm :
            ↥W × EuclideanSpace ℝ (Fin n) ≃ₜ ↥(Z.proj ⁻¹' W)) :
            C(↥W × EuclideanSpace ℝ (Fin n), ↥(Z.proj ⁻¹' W)))
          (Work.Thom.Punct ↥W n) (Work.Thom.pieceZero Z W) hmem' ℤ n).hom
          ((Work.Thom.relCohMap (negPiece Z W) (Work.Thom.pieceZero Z W)
            (Work.Thom.pieceZero Z W) (negPiece_mem Z W) ℤ n).hom X)
        = (Work.Thom.relCohMap
          (((Work.Thom.chartHomeo Z n e i W hW).symm :
            ↥W × EuclideanSpace ℝ (Fin n) ≃ₜ ↥(Z.proj ⁻¹' W)) :
            C(↥W × EuclideanSpace ℝ (Fin n), ↥(Z.proj ⁻¹' W)))
          (Work.Thom.Punct ↥W n) (Work.Thom.pieceZero Z W) hmem' ℤ n).hom (-X) by
      exact (Work.Thom.bijective_relCohMap_of_homeomorphA (Work.Thom.Punct ↥W n)
        (Work.Thom.pieceZero Z W) ((Work.Thom.chartHomeo Z n e i W hW).symm) hmem_iff ℤ n).1 h
    erw [Work.Thom.relCohMap_compA_apply (Work.Thom.Punct ↥W n) (Work.Thom.pieceZero Z W)
      (Work.Thom.pieceZero Z W)
      (((Work.Thom.chartHomeo Z n e i W hW).symm :
        ↥W × EuclideanSpace ℝ (Fin n) ≃ₜ ↥(Z.proj ⁻¹' W)) :
        C(↥W × EuclideanSpace ℝ (Fin n), ↥(Z.proj ⁻¹' W)))
      (negPiece Z W) hmem' (negPiece_mem Z W)
      (fun q hq => negPiece_mem Z W _ (hmem' q hq)) ℤ n X]
    rw [Work.Thom.relCohMap_congrA (Work.Thom.Punct ↥W n) (Work.Thom.pieceZero Z W)
      (negPiece_comp_chartHomeoSymm Z n e i W hW)
      (fun q hq => negPiece_mem Z W _ (hmem' q hq))
      (fun q hq => hmem' ((trivNeg n ↥W) q) (trivNeg_mem n ↥W q hq)) ℤ n]
    erw [← Work.Thom.relCohMap_compA_apply (Work.Thom.Punct ↥W n) (Work.Thom.Punct ↥W n)
      (Work.Thom.pieceZero Z W) (trivNeg n ↥W)
      (((Work.Thom.chartHomeo Z n e i W hW).symm :
        ↥W × EuclideanSpace ℝ (Fin n) ≃ₜ ↥(Z.proj ⁻¹' W)) :
        C(↥W × EuclideanSpace ℝ (Fin n), ↥(Z.proj ⁻¹' W)))
      (trivNeg_mem n ↥W) hmem' (fun q hq => hmem' ((trivNeg n ↥W) q) (trivNeg_mem n ↥W q hq))
      ℤ n X]
    rw [trivNeg_eq_neg n hn ↥W _]
    rw [map_neg]
  rw [hpr]
  exact h1.trans (h2.trans (h3.trans h4))


/-! ## The assembly -/

/-- **The fibrewise negation negates any Thom class of a bundle of odd rank**, whence the Euler
class is `2`-torsion. -/
theorem eulerClassOddRank {B : Type} [TopologicalSpace B] {F : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type} [FiniteDimensional ℝ F]
    (Z : Work.TangentClasses.RealBundle B F ι) {n : ℕ} (hrank : Z.rank = n) (T : Work.Thom.ThomClass Z n)
    (hn : Odd n) : (2 : ℤ) • T.eulerClass = 0 := by
  classical
  -- `z = a^*τ + τ`
  set z : Work.Thom.OpenThom Z n :=
    (Work.Thom.relCohMap (negMap Z) (Work.Thom.zeroComplement Z) (Work.Thom.zeroComplement Z)
      (negMap_mem Z) ℤ n).hom T.τ + T.τ with hz
  -- `w` is `z` read in degree `0 + n`, where the degree-zero Thom isomorphism lives
  set w : Work.Thom.OpenThom Z (0 + n) := (Nat.zero_add n).symm ▸ z with hw
  obtain ⟨c, hc⟩ := (T.isThom 0).2 w
  -- the coordinate of the restriction of `τ` to a chart piece kills `c` there
  have hchart : ∀ (i : ι) (W : Set B) (hW : W ⊆ Z.baseSet i),
      Work.Thom.localThomMap Z n W ((Work.Thom.PieceRes Z W n).hom T.τ) 0
        ((Work.Thom.CohMap (Work.Thom.subtypeMap W) ℤ 0).hom c) = 0 := by
    intro i W hW
    have hF : Module.finrank ℝ F = Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) := by
      rw [finrank_euclideanSpace_fin]; exact hrank
    obtain ⟨e⟩ : Nonempty (F ≃L[ℝ] EuclideanSpace ℝ (Fin n)) :=
      ⟨ContinuousLinearEquiv.ofFinrankEq hF⟩
    -- the restriction of `z` to the piece vanishes
    have hz0 : (Work.Thom.PieceRes Z W n).hom z = 0 := by
      rw [hz, map_add, negPiece_restrict Z n hn e i W hW T.τ, neg_add_cancel]
    -- transport to degree `0 + n`
    have hw0 : (Work.Thom.PieceRes Z W (0 + n)).hom w = 0 := by
      rw [hw, pieceRes_cast Z W (Nat.zero_add n).symm z, hz0]
      exact eqRec_zero (β := fun m => ↥(Work.Thom.PieceCoh Z W m)) (Nat.zero_add n).symm
    -- the local Thom map of the restriction
    have h2 := Work.Thom.thomMap_restrict Z n 0 W T.τ c
    rw [hc] at h2
    rw [hw, hw0] at h2
    exact h2.symm
  -- hence `c = 0` by the degree-zero cover separation
  have hchild := fun (i : ι) (W : Set B) (hW : W ⊆ Z.baseSet i) =>
    localThomMapChartInjective Z hrank T i W hW
  have hc0 : c = 0 :=
    Work.Thom.Coh_zero_cover_injective_gen (fun i : ι => Z.baseSet i)
      (fun i => Z.isOpen_baseSet i) (fun x => ⟨Z.indexAt x, Z.mem_baseSet_at x⟩) c
      (fun i => hchild i (Z.baseSet i) subset_rfl
        (by rw [hchart i (Z.baseSet i) subset_rfl, map_zero]))
  -- hence `w = 0` and `z = 0`
  have hw0 : w = 0 := by
    rw [← hc, hc0, map_zero]
  have hz0 : z = 0 := by
    have h1 : (Nat.zero_add n).symm ▸ z = 0 := hw ▸ hw0
    refine eqRec_injective (β := fun m => ↥(Work.Thom.OpenThom Z m)) (Nat.zero_add n).symm z 0 ?_
    rw [h1]
    exact (eqRec_zero (β := fun m => ↥(Work.Thom.OpenThom Z m)) (Nat.zero_add n).symm).symm
  -- hence `a^*τ = -τ`
  have hneg : (Work.Thom.relCohMap (negMap Z) (Work.Thom.zeroComplement Z)
      (Work.Thom.zeroComplement Z) (negMap_mem Z) ℤ n).hom T.τ = -T.τ := by
    have h : (Work.Thom.relCohMap (negMap Z) (Work.Thom.zeroComplement Z)
        (Work.Thom.zeroComplement Z) (negMap_mem Z) ℤ n).hom T.τ + T.τ = 0 := by
      rw [← hz]
      exact hz0
    exact eq_neg_of_add_eq_zero_left h
  -- and therefore the Euler class satisfies `e = -e`
  have he : T.eulerClass = -T.eulerClass := by
    show (Work.Thom.CohMap (Work.Thom.zeroSection Z) ℤ n).hom
        ((Work.Thom.openToAbs Z n).hom T.τ)
      = -(Work.Thom.CohMap (Work.Thom.zeroSection Z) ℤ n).hom
        ((Work.Thom.openToAbs Z n).hom T.τ)
    rw [← map_neg, ← map_neg, ← hneg]
    rw [Work.Thom.relCohMap_relToAbs_apply (negMap Z) (Work.Thom.zeroComplement Z)
      (Work.Thom.zeroComplement Z) (negMap_mem Z) ℤ n T.τ]
    rw [Work.Thom.CohMap_comp_apply (Work.Thom.zeroSection Z) (negMap Z) ℤ n
      ((Work.Thom.relToAbs ℤ (Work.Thom.zeroComplement Z) n).hom T.τ)]
    rw [negMap_comp_zeroSection]
  calc (2 : ℤ) • T.eulerClass = T.eulerClass + T.eulerClass := by
        rw [show (2 : ℤ) = 1 + 1 by norm_num, add_zsmul, one_zsmul]
    _ = T.eulerClass + (-T.eulerClass) := congrArg (fun x => T.eulerClass + x) he
    _ = 0 := add_neg_cancel _

end

end Work.ThomBordism.Grassmann
