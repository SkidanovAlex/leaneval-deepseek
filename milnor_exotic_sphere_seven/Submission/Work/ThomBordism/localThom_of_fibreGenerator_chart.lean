import Mathlib
import Submission.Work.ThomBordism.thomClassFibreDefs
import Submission.Work.Thom.localThom_full
import Submission.Work.Thom.ChartOrientation
import Submission.Work.Thom.localThom_union
import Submission.Work.Tubular.localThomOfChart_fibre_span_top
import Submission.Work.Thom.chartCoeffAux

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false

/-!
# A fibre generator over a chart piece is a local Thom class

`Work.ThomBordism.localThom_of_fibreGenerator_chart`: for a real bundle `Z → B` of rank `n` and a
class `σ ∈ H^n(E, E∖0;ℤ)` restricting to a generator on every fibre pair `(Z_b, Z_b∖0)`, the
restriction of `σ` to any piece `W ⊆ Z.baseSet i` of a chart is a local Thom class, i.e. the local
Thom map `x ↦ π_W^*(x) ⌣ σ|_W` is bijective in every degree.

The mathematical content: over a chart the bundle is trivial, so `σ|_W = π^*(c) ⌣ τ₀` with `τ₀` the
explicit chart class `Work.Thom.localThomOfChart` and `c ∈ H⁰(W;ℤ)` (the Thom isomorphism in degree
`0`); the fibrewise condition says that `c` takes the value `±1` at every point, so `c` is a unit;
hence `σ|_W` is a unit multiple of a local Thom class.
-/

namespace Work.ThomBordism

open Work.TangentClasses CategoryTheory

noncomputable section

variable {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {ι : Type}

/-! ## Degree casts in the mixed cup product -/

/-- The mixed cup product commutes with a cast of the *inner* degree. -/
lemma mixedCupC_cast_right_gen {X : Type} [TopologicalSpace X] (A : Set X) (m : ℕ) {k k' : ℕ}
    (h : k = k') (a : Work.Thom.Coh ℤ m X) (z : Work.Thom.RelCoh ℤ k X A) :
    Work.Thom.mixedCupC ℤ A m k' a (h ▸ z)
      = (congrArg (fun t => m + t) h) ▸ (Work.Thom.mixedCupC ℤ A m k a z) := by
  cases h; rfl

/-- A cast of the degree commutes with the scalar action (reverse orientation of
`Work.Tubular.relCoh_cast_smul'`). -/
lemma relCoh_cast_smul_gen {X : Type} [TopologicalSpace X] (A : Set X) {a b : ℕ} (h : a = b)
    (m : ℤ) (x : Work.Thom.RelCoh ℤ a X A) :
    m • (h ▸ x) = h ▸ (m • x) := by
  cases h; rfl

/-- A cast of the degree composed with its inverse cancels against the scalar action. -/
lemma relCoh_cast_smul_cancel {X : Type} [TopologicalSpace X] (A : Set X) {a b : ℕ} (h : a = b)
    (m : ℤ) (x : Work.Thom.RelCoh ℤ b X A) :
    h ▸ (m • (h.symm ▸ x)) = m • x := by
  cases h; rfl

/-- Transport of a relative cohomology class along an equality of degrees, with the pair fixed (so
that the `Eq.rec` motive is the fixed family `fun t => RelCoh ℤ t X A`). -/
def relCohCastGen {X : Type} [TopologicalSpace X] (A : Set X) {a b : ℕ} (h : a = b)
    (x : Work.Thom.RelCoh ℤ a X A) : Work.Thom.RelCoh ℤ b X A := h ▸ x

lemma relCohCastGen_eq {X : Type} [TopologicalSpace X] (A : Set X) {a b : ℕ} (h : a = b)
    (x : Work.Thom.RelCoh ℤ a X A) : relCohCastGen A h x = h ▸ x := rfl

/-- `relCohCastGen` commutes with the scalar action. -/
lemma relCohCastGen_smul {X : Type} [TopologicalSpace X] (A : Set X) {a b : ℕ} (h : a = b)
    (m : ℤ) (x : Work.Thom.RelCoh ℤ a X A) :
    m • relCohCastGen A h x = relCohCastGen A h (m • x) := by
  rw [relCohCastGen_eq]
  cases h; rfl

/-- `relCohCastGen` composed with its inverse cancels. -/
lemma relCohCastGen_symm_cancel {X : Type} [TopologicalSpace X] (A : Set X) {a b : ℕ} (h : a = b)
    (x : Work.Thom.RelCoh ℤ b X A) :
    relCohCastGen A h (relCohCastGen A h.symm x) = x := by
  rw [relCohCastGen_eq, relCohCastGen_eq]
  cases h; rfl

/-- `relCohCastGen` is compatible with an equality of the transported class. -/
lemma relCohCastGen_congr {X : Type} [TopologicalSpace X] (A : Set X) {a b : ℕ} (h : a = b)
    {x y : Work.Thom.RelCoh ℤ a X A} (hxy : x = y) :
    relCohCastGen A h x = relCohCastGen A h y := by
  rw [hxy]


/-- `relCohCastGen` followed by the scalar action and its inverse is just the scalar action. -/
lemma relCohCastGen_smul_cancel {X : Type} [TopologicalSpace X] (A : Set X) {a b : ℕ} (h : a = b)
    (m : ℤ) (x : Work.Thom.RelCoh ℤ b X A) :
    relCohCastGen A h (m • (relCohCastGen A h.symm x)) = m • x :=
  (relCohCastGen_smul A h m (relCohCastGen A h.symm x)).symm.trans
    (congrArg (fun z => m • z) (relCohCastGen_symm_cancel A h x))

/-- Two casts compose. -/
lemma eqRec_trans_cast {P : ℕ → Type} {a b c : ℕ} (h₁ : a = b) (h₂ : b = c) (x : P a) :
    h₂ ▸ (h₁ ▸ x) = ((h₁.trans h₂) ▸ x) := by
  cases h₁; cases h₂; rfl

/-- **Associativity of the mixed cup product with a degree-zero factor**, over `ℤ` (the
`ℤ`-case of `Work.StemsB.mixedCupC_assoc_zero`). -/
theorem mixedCupC_assoc_zero_Z {X : Type} [TopologicalSpace X] (A : Set X) (m k : ℕ)
    (a : Work.Thom.Coh ℤ m X) (c : Work.Thom.Coh ℤ 0 X) (z : Work.Thom.RelCoh ℤ k X A) :
    (Work.Thom.mixedCupC ℤ A m (0 + k)) a ((Work.Thom.mixedCupC ℤ A 0 k) c z)
      = (Nat.add_assoc m 0 k) ▸
          ((Work.Thom.mixedCupC ℤ A m k)
            ((Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj (TopCat.of X)) m 0) a c) z) := by
  obtain ⟨α, hα, rfl⟩ := Work.Cohomology.exists_cohomologyClassOf ℤ
    (TopCat.toSSet.obj (TopCat.of X)) m a
  obtain ⟨β, hβ, rfl⟩ := Work.Cohomology.exists_cohomologyClassOf ℤ
    (TopCat.toSSet.obj (TopCat.of X)) 0 c
  obtain ⟨ζ, hζ, rfl⟩ := Work.Cohomology.exists_relClassOf ℤ (TopCat.of X) A k z
  simp only [Work.Thom.mixedCupC_eq_mixedCup]
  obtain ⟨hmem1, hcoc1, h1⟩ :=
    Work.Cohomology.mixedCup_apply (TopCat.of X) A 0 k β ζ hβ hζ
  rw [h1]
  obtain ⟨hmem2, hcoc2, h2⟩ :=
    Work.Cohomology.mixedCup_apply (TopCat.of X) A m (0 + k) α
      ⟨Work.Cohomology.cup ℤ (TopCat.toSSet.obj (TopCat.of X)) β ζ.1, hmem1⟩ hα hcoc1
  rw [h2]
  rw [Work.Cohomology.cupH'_apply' ℤ (TopCat.toSSet.obj (TopCat.of X)) α β hα hβ]
  obtain ⟨hmem3, hcoc3, h3⟩ :=
    Work.Cohomology.mixedCup_apply (TopCat.of X) A m k
      (Work.Cohomology.cup ℤ (TopCat.toSSet.obj (TopCat.of X)) α β) ζ
      (Work.Cohomology.cochainDiff_cup_of_cocycles ℤ (TopCat.toSSet.obj (TopCat.of X)) α β hα hβ)
      hζ
  rw [h3]
  let u3 : Work.Cohomology.relKern ℤ (TopCat.of X) A (m + k) :=
    ⟨Work.Cohomology.cup ℤ (TopCat.toSSet.obj (TopCat.of X))
        (Work.Cohomology.cup ℤ (TopCat.toSSet.obj (TopCat.of X)) α β) ζ.1, hmem3⟩
  have hu3 : Work.Cohomology.relDiffLM ℤ (TopCat.of X) A (m + k) u3 = 0 := hcoc3
  have hu3' : Work.Cohomology.relDiffLM ℤ (TopCat.of X) A (m + (0 + k))
      (((Work.Cohomology.relComplex ℤ (TopCat.of X) A).XIsoOfEq (Nat.add_assoc m 0 k)).hom u3) = 0 := by
    rw [← Work.Cohomology.relComplex_d_apply]
    exact Work.Thom.cocycle_transport_K (K := Work.Cohomology.relComplex ℤ (TopCat.of X) A)
      (Nat.add_assoc m 0 k) u3 (by rw [Work.Cohomology.relComplex_d_apply]; exact hu3)
  rw [Work.Thom.relClassOf_cast (Y := TopCat.of X) (A := A) (Nat.add_assoc m 0 k) u3 hu3 hu3']
  refine Work.Cohomology.relClassOf_congr ℤ (TopCat.of X) A hcoc2 _ (Subtype.ext ?_)
  rw [Work.Thom.relComplex_XIsoOfEq_coe (Y := TopCat.of X) (B := A) (Nat.add_assoc m 0 k)]
  simpa only [Subtype.coe_mk, Subtype.coe_eta] using
    (Work.Cohomology.cupAssoc ℤ (TopCat.toSSet.obj (TopCat.of X)) α β ζ.1).symm

/-! ## `H^k`-linearity of the local Thom map -/

/-- **`H^k`-linearity of the local Thom map over `H⁰`.** -/
theorem localThomMap_cup_general_aux (Z : Work.TangentClasses.RealBundle B F ι) (n : ℕ) (W : Set B)
    (τ : Work.Thom.PieceCoh Z W n) (c : Work.Thom.Coh ℤ 0 ↥W) (k : ℕ)
    (x : Work.Thom.Coh ℤ k ↥W) :
    Work.Thom.localThomMap Z n W
        ((Nat.zero_add n) ▸ (Work.Thom.localThomMap Z n W τ 0 c)) k x
      = Work.Thom.localThomMap Z n W τ k
          (Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj (TopCat.of ↥W)) k 0 x c) := by
  set A : Set ↥(Z.proj ⁻¹' W) := Work.Thom.pieceZero Z W with hA
  have h1 : Work.Thom.localThomMap Z n W
        ((Nat.zero_add n) ▸ (Work.Thom.localThomMap Z n W τ 0 c)) k x
      = (Work.Thom.mixedCupC ℤ A k n)
          ((Work.Thom.CohMap (Work.Thom.pieceProj Z W) ℤ k).hom x)
          ((Nat.zero_add n) ▸ ((Work.Thom.mixedCupC ℤ A 0 n)
            ((Work.Thom.CohMap (Work.Thom.pieceProj Z W) ℤ 0).hom c) τ)) := rfl
  have hnat := Work.Cohomology.cupNaturalH ℤ (TopCat.ofHom (Work.Thom.pieceProj Z W)) k 0 x c
  have h2 : (Work.Thom.mixedCupC ℤ A k n)
          ((Work.Thom.CohMap (Work.Thom.pieceProj Z W) ℤ k).hom
            (Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj (TopCat.of ↥W)) k 0 x c)) τ
      = Work.Thom.localThomMap Z n W τ k
          (Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj (TopCat.of ↥W)) k 0 x c) := rfl
  rw [h1, ← h2]
  rw [show (Work.Thom.CohMap (Work.Thom.pieceProj Z W) ℤ k).hom
        (Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj (TopCat.of ↥W)) k 0 x c)
      = (Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj (TopCat.of ↥(Z.proj ⁻¹' W))) k 0)
          ((Work.Thom.CohMap (Work.Thom.pieceProj Z W) ℤ k).hom x)
          ((Work.Thom.CohMap (Work.Thom.pieceProj Z W) ℤ 0).hom c) from hnat]
  rw [mixedCupC_cast_right_gen A k (Nat.zero_add n)
    ((Work.Thom.CohMap (Work.Thom.pieceProj Z W) ℤ k).hom x)
    ((Work.Thom.mixedCupC ℤ A 0 n) ((Work.Thom.CohMap (Work.Thom.pieceProj Z W) ℤ 0).hom c) τ)]
  rw [mixedCupC_assoc_zero_Z A k n
    ((Work.Thom.CohMap (Work.Thom.pieceProj Z W) ℤ k).hom x)
    ((Work.Thom.CohMap (Work.Thom.pieceProj Z W) ℤ 0).hom c) τ]
  exact (eqRec_trans_cast (P := fun t => Work.Thom.RelCoh ℤ t ↥(Z.proj ⁻¹' W) A)
    (Nat.add_assoc k 0 n) (congrArg (fun t => k + t) (Nat.zero_add n))
    ((Work.Thom.mixedCupC ℤ A k n)
      ((Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj (TopCat.of ↥(Z.proj ⁻¹' W))) k 0)
        ((Work.Thom.CohMap (Work.Thom.pieceProj Z W) ℤ k).hom x)
        ((Work.Thom.CohMap (Work.Thom.pieceProj Z W) ℤ 0).hom c)) τ)).trans (by rfl)

/-! ## The fibre generator condition at a point, in the piece language -/

/-- The comparison map from the relative cohomology of the fibre over `b` to that of the piece over
`{b}` (the two pairs differ only in the presentation of the excluded set). -/
def fibreToPiece (Z : Work.TangentClasses.RealBundle B F ι) (b : B) (n : ℕ) :
    Work.Thom.RelCoh ℤ n ↥(Work.ThomBordism.fibre Z b) (fibrePunctSub Z b) →ₗ[ℤ]
      Work.Thom.PieceCoh Z ({b} : Set B) n :=
  (Work.Thom.relCohMap (ContinuousMap.id ↥(Z.proj ⁻¹' ({b} : Set B)))
    (Work.Thom.pieceZero Z ({b} : Set B)) (fibrePunctSub Z b)
    (fun y hy => ⟨y.2, hy⟩) ℤ n).hom

/-- The comparison map sends the fibre restriction of a class to its restriction to the piece. -/
theorem fibreToPiece_fibreRes (Z : Work.TangentClasses.RealBundle B F ι) (b : B) (n : ℕ)
    (σ : Work.Thom.OpenThom Z n) :
    fibreToPiece Z b n (fibreRes Z b n σ) = (Work.Thom.PieceRes Z ({b} : Set B) n).hom σ := by
  have hmem : ∀ y ∈ Work.Thom.pieceZero Z ({b} : Set B), y ∈ fibrePunctSub Z b :=
    fun y hy => ⟨y.2, hy⟩
  have hfp : ∀ y ∈ fibrePunctSub Z b,
      (Work.Thom.subtypeMap (Z.proj ⁻¹' ({b} : Set B))) y ∈ Work.Thom.zeroComplement Z :=
    fun y hy => hy.2
  have haz : ∀ y ∈ Work.Thom.pieceZero Z ({b} : Set B),
      (Work.Thom.subtypeMap (Z.proj ⁻¹' ({b} : Set B))) y ∈ Work.Thom.zeroComplement Z :=
    fun y hy => hy
  have hkey : (Work.Thom.relCohMap (ContinuousMap.id ↥(Z.proj ⁻¹' ({b} : Set B)))
        (Work.Thom.pieceZero Z ({b} : Set B)) (fibrePunctSub Z b) hmem ℤ n).hom
        ((Work.Thom.relCohMap (Work.Thom.subtypeMap (Z.proj ⁻¹' ({b} : Set B)))
          (fibrePunctSub Z b) (Work.Thom.zeroComplement Z) hfp ℤ n).hom σ)
      = (Work.Thom.relCohMap (Work.Thom.subtypeMap (Z.proj ⁻¹' ({b} : Set B)))
          (Work.Thom.pieceZero Z ({b} : Set B)) (Work.Thom.zeroComplement Z)
          (fun y hy => hy) ℤ n).hom σ :=
    (Work.Thom.relCohMap_compA_apply (Work.Thom.pieceZero Z ({b} : Set B))
      (fibrePunctSub Z b) (Work.Thom.zeroComplement Z)
      (ContinuousMap.id ↥(Z.proj ⁻¹' ({b} : Set B)))
      (Work.Thom.subtypeMap (Z.proj ⁻¹' ({b} : Set B))) hmem hfp haz ℤ n σ).trans
      (congrArg (fun (g : Work.Thom.RelCoh ℤ n Z.TotalSpace (Work.Thom.zeroComplement Z) →ₗ[ℤ]
          Work.Thom.RelCoh ℤ n ↥(Z.proj ⁻¹' ({b} : Set B))
            (Work.Thom.pieceZero Z ({b} : Set B))) => g σ)
        (congrArg ModuleCat.Hom.hom (Work.Thom.relCohMap_congrA _ _
          (ContinuousMap.comp_id (Work.Thom.subtypeMap (Z.proj ⁻¹' ({b} : Set B))))
          haz (fun y hy => hy) ℤ n)))
  show (Work.Thom.relCohMap (ContinuousMap.id ↥(Z.proj ⁻¹' ({b} : Set B)))
        (Work.Thom.pieceZero Z ({b} : Set B)) (fibrePunctSub Z b) hmem ℤ n).hom
        (fibreRes Z b n σ) = (Work.Thom.PieceRes Z ({b} : Set B) n).hom σ
  exact hkey

theorem fibreToPiece_range (Z : Work.TangentClasses.RealBundle B F ι) (b : B) (n : ℕ) :
    (fibreToPiece Z b n).range = ⊤ := by
  have hmem : ∀ y ∈ Work.Thom.pieceZero Z ({b} : Set B), y ∈ fibrePunctSub Z b :=
    fun y hy => ⟨y.2, hy⟩
  have hmem' : ∀ y ∈ fibrePunctSub Z b, y ∈ Work.Thom.pieceZero Z ({b} : Set B) :=
    fun y hy => hy.2
  have hcomp := Work.Thom.relCohMap_compA (Work.Thom.pieceZero Z ({b} : Set B))
    (fibrePunctSub Z b) (Work.Thom.pieceZero Z ({b} : Set B))
    (ContinuousMap.id ↥(Z.proj ⁻¹' ({b} : Set B)))
    (ContinuousMap.id ↥(Z.proj ⁻¹' ({b} : Set B))) hmem hmem' (fun y hy => hy) ℤ n
  have hcomp' : CategoryTheory.CategoryStruct.comp
      (Work.Thom.relCohMap (ContinuousMap.id ↥(Z.proj ⁻¹' ({b} : Set B)))
        (fibrePunctSub Z b) (Work.Thom.pieceZero Z ({b} : Set B)) hmem' ℤ n)
      (Work.Thom.relCohMap (ContinuousMap.id ↥(Z.proj ⁻¹' ({b} : Set B)))
        (Work.Thom.pieceZero Z ({b} : Set B)) (fibrePunctSub Z b) hmem ℤ n)
      = 𝟙 (Work.Thom.RelCoh ℤ n ↥(Z.proj ⁻¹' ({b} : Set B))
          (Work.Thom.pieceZero Z ({b} : Set B))) :=
    hcomp.trans ((Work.Thom.relCohMap_congrA _ _
      (ContinuousMap.id_comp (ContinuousMap.id ↥(Z.proj ⁻¹' ({b} : Set B)))) _ _ ℤ n).trans
      (Work.Thom.relCohMap_idA (Work.Thom.pieceZero Z ({b} : Set B)) ℤ n))
  have hlin : (fibreToPiece Z b n).comp
      ((Work.Thom.relCohMap (ContinuousMap.id ↥(Z.proj ⁻¹' ({b} : Set B)))
        (fibrePunctSub Z b) (Work.Thom.pieceZero Z ({b} : Set B)) hmem' ℤ n).hom)
      = LinearMap.id := by
    have h2 := congrArg ModuleCat.Hom.hom hcomp'
    rw [ModuleCat.hom_comp, ModuleCat.hom_id] at h2
    exact h2
  rw [LinearMap.range_eq_top]
  intro y
  exact ⟨_, LinearMap.congr_fun hlin y⟩

/-- **A fibre generator restricts to a generator on every point-piece.** -/
theorem span_pieceRes_singleton (Z : Work.TangentClasses.RealBundle B F ι) (n : ℕ)
    (σ : Work.Thom.OpenThom Z n) (h : IsFibreGenerator Z n σ) (b : B) :
    Submodule.span ℤ {(Work.Thom.PieceRes Z ({b} : Set B) n).hom σ} = ⊤ := by
  have hgen : Submodule.span ℤ {fibreRes Z b n σ} = ⊤ := h b
  have hkey : fibreToPiece Z b n (fibreRes Z b n σ)
      = (Work.Thom.PieceRes Z ({b} : Set B) n).hom σ := fibreToPiece_fibreRes Z b n σ
  have hmap : Submodule.map (fibreToPiece Z b n) (Submodule.span ℤ {fibreRes Z b n σ})
      = Submodule.span ℤ {fibreToPiece Z b n (fibreRes Z b n σ)} := by
    rw [Submodule.map_span, Set.image_singleton]
  have htop : Submodule.map (fibreToPiece Z b n) (⊤ : Submodule ℤ
      (Work.Thom.RelCoh ℤ n ↥(Work.ThomBordism.fibre Z b) (fibrePunctSub Z b))) = ⊤ := by
    rw [Submodule.map_top]
    exact fibreToPiece_range Z b n
  rw [← hkey, ← hmap, hgen, htop]

/-! ## The pointwise coefficient of a fibre generator is `±1` -/

/-- The coefficient equation restricted to a point (in the degree-cast form). -/
theorem pieceRes_singleton_cast (Z : Work.TangentClasses.RealBundle B F ι) (n : ℕ)
    (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin n)) (i : ι) {W : Set B} (hW : W ⊆ Z.baseSet i)
    (σ : Work.Thom.OpenThom Z n) (c : Work.Thom.Coh ℤ 0 ↥W)
    (hc : (Work.Thom.PieceRes Z W n).hom σ
      = (Nat.zero_add n) ▸ (Work.Thom.localThomMap Z n W
          (Work.Thom.chartCoh Z n e i W hW) 0 c))
    (b : B) (hb : b ∈ W) (hbsub : ({b} : Set B) ⊆ Z.baseSet i) :
    (Work.Thom.PieceRes Z ({b} : Set B) n).hom σ
      = (Nat.zero_add n) ▸ (Work.Thom.localThomMap Z n ({b} : Set B)
          (Work.Thom.chartCoh Z n e i ({b} : Set B) hbsub) 0
          ((Work.Thom.CohMap (Work.Thom.ptIncl W b hb) ℤ 0).hom c)) := by
  have h2 : (Work.Thom.PieceRes Z ({b} : Set B) n).hom σ
      = (Work.Cohomology.pdCohMap (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
          (Z.proj ⁻¹' W) (Z.proj ⁻¹' ({b} : Set B))
          (Set.preimage_mono (Work.Thom.singleton_subset_of_mem hb)) n).hom
          ((Work.Thom.PieceRes Z W n).hom σ) := by
    rw [show (Work.Thom.PieceRes Z ({b} : Set B) n)
        = (Work.Thom.PieceRes Z W n) ≫ (Work.Cohomology.pdCohMap (TopCat.of Z.TotalSpace)
            (Work.Thom.zeroComplement Z) (Z.proj ⁻¹' W) (Z.proj ⁻¹' ({b} : Set B))
            (Set.preimage_mono (Work.Thom.singleton_subset_of_mem hb)) n) from
      Work.Cohomology.pdCohRes_comp (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
        (Z.proj ⁻¹' W) (Z.proj ⁻¹' ({b} : Set B))
        (Set.preimage_mono (Work.Thom.singleton_subset_of_mem hb)) n,
      ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [h2, hc, Work.Thom.cast_pdCohMap Z (Work.Thom.singleton_subset_of_mem hb) (Nat.zero_add n)
    (Work.Thom.localThomMap Z n W (Work.Thom.chartCoh Z n e i W hW) 0 c)]
  exact congrArg (fun y => (Nat.zero_add n) ▸ y)
    (Work.Thom.localThomMap_piece_pt Z n e i hW b hb hbsub c)

/-- The cast/smul bookkeeping for the chart class over a point. -/
private theorem relCohCastGen_smul_cancel_chart (Z : Work.TangentClasses.RealBundle B F ι) (b : B)
    (n : ℕ) (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin n)) (i : ι)
    (hbsub : ({b} : Set B) ⊆ Z.baseSet i) (m : ℤ) :
    (Nat.zero_add n) ▸ (m • ((Nat.zero_add n).symm ▸
        (Work.Thom.chartCoh Z n e i ({b} : Set B) hbsub)))
      = m • (Work.Thom.chartCoh Z n e i ({b} : Set B) hbsub) :=
  relCohCastGen_smul_cancel _ (Nat.zero_add n) m
    (Work.Thom.chartCoh Z n e i ({b} : Set B) hbsub)

/-- The coefficient equation restricted to a point, in the `ℤ`-action form. -/
theorem pieceRes_singleton_smul (Z : Work.TangentClasses.RealBundle B F ι) (n : ℕ)
    (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin n)) (i : ι) {W : Set B} (hW : W ⊆ Z.baseSet i)
    (σ : Work.Thom.OpenThom Z n) (c : Work.Thom.Coh ℤ 0 ↥W)
    (hc : (Work.Thom.PieceRes Z W n).hom σ
      = (Nat.zero_add n) ▸ (Work.Thom.localThomMap Z n W
          (Work.Thom.chartCoh Z n e i W hW) 0 c))
    (b : B) (hb : b ∈ W) (hbsub : ({b} : Set B) ⊆ Z.baseSet i) :
    (Work.Thom.PieceRes Z ({b} : Set B) n).hom σ
      = (Work.Thom.ptEv ⟨b, hb⟩ c) • (Work.Thom.chartCoh Z n e i ({b} : Set B) hbsub) := by
  have h1 := pieceRes_singleton_cast Z n e i hW σ c hc b hb hbsub
  have honePt : (Work.Thom.localThomMap Z n ({b} : Set B)
        (Work.Thom.chartCoh Z n e i ({b} : Set B) hbsub) 0) (Work.Thom.onePt b)
      = (Nat.zero_add n).symm ▸ (Work.Thom.chartCoh Z n e i ({b} : Set B) hbsub) :=
    Work.Thom.localThomMap_oneH Z n ({b} : Set B) (Work.Thom.chartCoh Z n e i ({b} : Set B) hbsub)
  have hmap : (Work.Thom.localThomMap Z n ({b} : Set B)
        (Work.Thom.chartCoh Z n e i ({b} : Set B) hbsub) 0)
        ((Work.Thom.ptEv ⟨b, hb⟩ c) • Work.Thom.onePt b)
      = (Work.Thom.ptEv ⟨b, hb⟩ c) • ((Work.Thom.localThomMap Z n ({b} : Set B)
          (Work.Thom.chartCoh Z n e i ({b} : Set B) hbsub) 0) (Work.Thom.onePt b)) :=
    map_zsmul _ _ _
  have hcast := relCohCastGen_smul_cancel_chart Z b n e i hbsub (Work.Thom.ptEv ⟨b, hb⟩ c)
  calc (Work.Thom.PieceRes Z ({b} : Set B) n).hom σ
      = (Nat.zero_add n) ▸ (Work.Thom.localThomMap Z n ({b} : Set B)
          (Work.Thom.chartCoh Z n e i ({b} : Set B) hbsub) 0
          ((Work.Thom.CohMap (Work.Thom.ptIncl W b hb) ℤ 0).hom c)) := h1
    _ = (Nat.zero_add n) ▸ (Work.Thom.localThomMap Z n ({b} : Set B)
          (Work.Thom.chartCoh Z n e i ({b} : Set B) hbsub) 0
          ((Work.Thom.ptEv ⟨b, hb⟩ c) • Work.Thom.onePt b)) :=
        congrArg (fun y => (Nat.zero_add n) ▸ (Work.Thom.localThomMap Z n ({b} : Set B)
          (Work.Thom.chartCoh Z n e i ({b} : Set B) hbsub) 0 y))
          (Work.Thom.CohMap_ptIncl_smul W b hb c)
    _ = (Nat.zero_add n) ▸ ((Work.Thom.ptEv ⟨b, hb⟩ c) •
          ((Work.Thom.localThomMap Z n ({b} : Set B)
            (Work.Thom.chartCoh Z n e i ({b} : Set B) hbsub) 0) (Work.Thom.onePt b))) :=
        congrArg (fun y => (Nat.zero_add n) ▸ y) hmap
    _ = (Nat.zero_add n) ▸ ((Work.Thom.ptEv ⟨b, hb⟩ c) •
          ((Nat.zero_add n).symm ▸ (Work.Thom.chartCoh Z n e i ({b} : Set B) hbsub))) :=
        congrArg (fun y => (Nat.zero_add n) ▸ y)
          (congrArg (fun z => (Work.Thom.ptEv ⟨b, hb⟩ c) • z) honePt)
    _ = (Work.Thom.ptEv ⟨b, hb⟩ c) • (Work.Thom.chartCoh Z n e i ({b} : Set B) hbsub) := hcast

/-- **The crux**: at every point of the chart piece the coefficient of a fibre generator is `±1`. -/
theorem ptEv_coeff_eq_one_or_neg_one (Z : Work.TangentClasses.RealBundle B F ι) (n : ℕ)
    (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin n)) (i : ι) {W : Set B} (hW : W ⊆ Z.baseSet i)
    (σ : Work.Thom.OpenThom Z n) (c : Work.Thom.Coh ℤ 0 ↥W)
    (hc : (Work.Thom.PieceRes Z W n).hom σ
      = (Nat.zero_add n) ▸ (Work.Thom.localThomMap Z n W
          (Work.Thom.chartCoh Z n e i W hW) 0 c))
    (hgen : ∀ (b : B) (hb : b ∈ W),
      Submodule.span ℤ {(Work.Thom.PieceRes Z ({b} : Set B) n).hom σ} = ⊤)
    (b : B) (hb : b ∈ W) :
    Work.Thom.ptEv ⟨b, hb⟩ c = 1 ∨ Work.Thom.ptEv ⟨b, hb⟩ c = -1 := by
  set hbsub : ({b} : Set B) ⊆ Z.baseSet i :=
    fun y hy => hW (Work.Thom.singleton_subset_of_mem hb hy) with hhbsub
  set g : Work.Thom.PieceCoh Z ({b} : Set B) n :=
    Work.Thom.chartCoh Z n e i ({b} : Set B) hbsub with hg
  have hσb : (Work.Thom.PieceRes Z ({b} : Set B) n).hom σ
      = (Work.Thom.ptEv ⟨b, hb⟩ c) • g := pieceRes_singleton_smul Z n e i hW σ c hc b hb hbsub
  -- `g` lies in the span of `σ|_{{b}}`, which is everything
  have hgenb := hgen b hb
  rw [hσb] at hgenb
  have hmem : g ∈ Submodule.span ℤ {(Work.Thom.ptEv ⟨b, hb⟩ c) • g} := by
    rw [hgenb]; exact Submodule.mem_top
  obtain ⟨k, hk⟩ := Submodule.mem_span_singleton.mp hmem
  -- push along the chart homeomorphism to the model over the one-point base
  set φ : Work.Thom.RelCoh ℤ n (↥({b} : Set B) × EuclideanSpace ℝ (Fin n))
        (Work.Thom.Punct ↥({b} : Set B) n) →ₗ[ℤ] Work.Thom.PieceCoh Z ({b} : Set B) n :=
    (Work.Thom.relCohMap (Work.Thom.chartHomeo Z n e i ({b} : Set B) hbsub :
        C(↥(Z.proj ⁻¹' ({b} : Set B)), ↥({b} : Set B) × EuclideanSpace ℝ (Fin n)))
      (Work.Thom.pieceZero Z ({b} : Set B)) (Work.Thom.Punct ↥({b} : Set B) n)
      (Work.Thom.chartHomeo_mem Z n e i ({b} : Set B) hbsub) ℤ n).hom with hφ
  have hφM : φ (Work.Thom.Mpun n ↥({b} : Set B)) = g := rfl
  have hφinj : Function.Injective φ :=
    (Work.Thom.bijective_relCohMap_of_homeomorphA (Work.Thom.pieceZero Z ({b} : Set B))
      (Work.Thom.Punct ↥({b} : Set B) n) (Work.Thom.chartHomeo Z n e i ({b} : Set B) hbsub)
      (Work.Thom.chartHomeo_mem_punct Z n e i ({b} : Set B) hbsub) ℤ n).1
  have hkφ : (k * Work.Thom.ptEv ⟨b, hb⟩ c) • Work.Thom.Mpun n ↥({b} : Set B)
      = Work.Thom.Mpun n ↥({b} : Set B) := by
    apply hφinj
    rw [map_zsmul, hφM, ← smul_smul]
    rw [← int_smul_eq_zsmul (inferInstance : Module ℤ (Work.Thom.PieceCoh Z ({b} : Set B) n))
      k (Work.Thom.ptEv ⟨b, hb⟩ c • g)]
    exact hk
  -- the model class is a generator over `H⁰`
  have hmod := Work.Thom.Mpun_isModel n ↥({b} : Set B) 0
  have hone : (Work.Thom.mixedCupC ℤ (Work.Thom.Punct ↥({b} : Set B) n) 0 n)
      ((Work.Thom.CohMap (Work.Thom.projFstA ↥({b} : Set B) n) ℤ 0).hom
        (Work.Cohomology.oneH ℤ (TopCat.toSSet.obj (TopCat.of ↥({b} : Set B)))))
      (Work.Thom.Mpun n ↥({b} : Set B))
      = relCohCastGen (Work.Thom.Punct ↥({b} : Set B) n) (Nat.zero_add n).symm
          (Work.Thom.Mpun n ↥({b} : Set B)) := by
    rw [Work.Thom.CohMap_oneH, Work.Thom.mixedCupC_oneH_zero]
    exact (relCohCastGen_eq _ _ _).symm
  have hlin1 : (Work.Thom.CohMap (Work.Thom.projFstA ↥({b} : Set B) n) ℤ 0).hom
        ((k * Work.Thom.ptEv ⟨b, hb⟩ c) •
          Work.Cohomology.oneH ℤ (TopCat.toSSet.obj (TopCat.of ↥({b} : Set B))))
      = (k * Work.Thom.ptEv ⟨b, hb⟩ c) •
        ((Work.Thom.CohMap (Work.Thom.projFstA ↥({b} : Set B) n) ℤ 0).hom
          (Work.Cohomology.oneH ℤ (TopCat.toSSet.obj (TopCat.of ↥({b} : Set B))))) :=
    map_zsmul _ _ _
  have hlin2 : (Work.Thom.mixedCupC ℤ (Work.Thom.Punct ↥({b} : Set B) n) 0 n)
        ((k * Work.Thom.ptEv ⟨b, hb⟩ c) •
          ((Work.Thom.CohMap (Work.Thom.projFstA ↥({b} : Set B) n) ℤ 0).hom
            (Work.Cohomology.oneH ℤ (TopCat.toSSet.obj (TopCat.of ↥({b} : Set B))))))
        (Work.Thom.Mpun n ↥({b} : Set B))
      = (k * Work.Thom.ptEv ⟨b, hb⟩ c) •
        ((Work.Thom.mixedCupC ℤ (Work.Thom.Punct ↥({b} : Set B) n) 0 n)
          ((Work.Thom.CohMap (Work.Thom.projFstA ↥({b} : Set B) n) ℤ 0).hom
            (Work.Cohomology.oneH ℤ (TopCat.toSSet.obj (TopCat.of ↥({b} : Set B)))))
          (Work.Thom.Mpun n ↥({b} : Set B))) :=
    congrArg (fun (f : Work.Thom.RelCoh ℤ n (↥({b} : Set B) × EuclideanSpace ℝ (Fin n))
        (Work.Thom.Punct ↥({b} : Set B) n) →ₗ[ℤ]
        Work.Thom.RelCoh ℤ (0 + n) (↥({b} : Set B) × EuclideanSpace ℝ (Fin n))
          (Work.Thom.Punct ↥({b} : Set B) n)) => f (Work.Thom.Mpun n ↥({b} : Set B)))
      (map_zsmul (Work.Thom.mixedCupC ℤ (Work.Thom.Punct ↥({b} : Set B) n) 0 n)
        (k * Work.Thom.ptEv ⟨b, hb⟩ c)
        ((Work.Thom.CohMap (Work.Thom.projFstA ↥({b} : Set B) n) ℤ 0).hom
          (Work.Cohomology.oneH ℤ (TopCat.toSSet.obj (TopCat.of ↥({b} : Set B))))))
  have hfin : (k * Work.Thom.ptEv ⟨b, hb⟩ c) •
        (relCohCastGen (Work.Thom.Punct ↥({b} : Set B) n) (Nat.zero_add n).symm
          (Work.Thom.Mpun n ↥({b} : Set B)))
      = relCohCastGen (Work.Thom.Punct ↥({b} : Set B) n) (Nat.zero_add n).symm
          (Work.Thom.Mpun n ↥({b} : Set B)) :=
    (relCohCastGen_smul _ (Nat.zero_add n).symm (k * Work.Thom.ptEv ⟨b, hb⟩ c)
      (Work.Thom.Mpun n ↥({b} : Set B))).trans
      (relCohCastGen_congr _ (Nat.zero_add n).symm hkφ)
  have hkey : (Work.Thom.mixedCupC ℤ (Work.Thom.Punct ↥({b} : Set B) n) 0 n)
      ((Work.Thom.CohMap (Work.Thom.projFstA ↥({b} : Set B) n) ℤ 0).hom
        ((k * Work.Thom.ptEv ⟨b, hb⟩ c) •
          Work.Cohomology.oneH ℤ (TopCat.toSSet.obj (TopCat.of ↥({b} : Set B)))))
      (Work.Thom.Mpun n ↥({b} : Set B))
      = (Work.Thom.mixedCupC ℤ (Work.Thom.Punct ↥({b} : Set B) n) 0 n)
        ((Work.Thom.CohMap (Work.Thom.projFstA ↥({b} : Set B) n) ℤ 0).hom
          (Work.Cohomology.oneH ℤ (TopCat.toSSet.obj (TopCat.of ↥({b} : Set B)))))
        (Work.Thom.Mpun n ↥({b} : Set B)) := by
    rw [hlin1, hlin2, hone]
    exact hfin
  have h1 : (k * Work.Thom.ptEv ⟨b, hb⟩ c) •
      (Work.Cohomology.oneH ℤ (TopCat.toSSet.obj (TopCat.of ↥({b} : Set B))))
      = Work.Cohomology.oneH ℤ (TopCat.toSSet.obj (TopCat.of ↥({b} : Set B))) :=
    hmod.1 hkey
  have h4 : k * Work.Thom.ptEv ⟨b, hb⟩ c = 1 := by
    have hh := congrArg (Work.Thom.ptEv (⟨b, rfl⟩ : ↥({b} : Set B))) h1
    rw [Work.Thom.ptEv_smul, Work.Thom.ptEv_one, mul_one] at hh
    exact hh
  exact Int.eq_one_or_neg_one_of_mul_eq_one
    (show Work.Thom.ptEv ⟨b, hb⟩ c * k = 1 by rw [mul_comm]; exact h4)

/-! ## A degree-zero class whose evaluations are `±1` is an involution -/

/-- If `ptEv` of a degree-zero class is `±1` at every point then the class is an involution, hence
a unit, hence cupping with it is bijective in every degree. -/
theorem cup_self_eq_oneH_of_ptEv (W : Set B) (c : Work.Thom.Coh ℤ 0 ↥W)
    (h : ∀ (b : B) (hb : b ∈ W), Work.Thom.ptEv ⟨b, hb⟩ c = 1 ∨ Work.Thom.ptEv ⟨b, hb⟩ c = -1) :
    Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj (TopCat.of ↥W)) 0 0 c c
      = Work.Cohomology.oneH ℤ (TopCat.toSSet.obj (TopCat.of ↥W)) := by
  refine Work.Thom.ptEv_ext (fun p : ↥W => ?_)
  obtain ⟨b, hb⟩ := p
  rcases h b hb with h1 | h1
  · rw [Work.Thom.ptEv_cup, h1, mul_one, Work.Thom.ptEv_one]
  · rw [Work.Thom.ptEv_cup, h1, Work.Thom.ptEv_one]
    norm_num

/-- **Cupping with an involution of `H⁰` is bijective in every degree.** -/
theorem bijective_cup_of_involution (W : Set B) (c : Work.Thom.Coh ℤ 0 ↥W)
    (hc : Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj (TopCat.of ↥W)) 0 0 c c
      = Work.Cohomology.oneH ℤ (TopCat.toSSet.obj (TopCat.of ↥W))) (k : ℕ) :
    Function.Bijective (fun x : Work.Thom.Coh ℤ k ↥W =>
      Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj (TopCat.of ↥W)) k 0 x c) := by
  have hinv : ∀ y : Work.Thom.Coh ℤ k ↥W,
      Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj (TopCat.of ↥W)) k 0
        (Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj (TopCat.of ↥W)) k 0 y c) c = y := by
    intro y
    have h1 := Work.Cohomology.cupH'_assoc ℤ (TopCat.toSSet.obj (TopCat.of ↥W)) k 0 0 y c c
    rw [hc] at h1
    rw [Work.Cohomology.cupH'_one_right] at h1
    exact h1
  refine ⟨fun x y hxy => ?_, fun y => ⟨Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj (TopCat.of ↥W))
    k 0 y c, hinv y⟩⟩
  have h2 := congrArg (fun w => Work.Cohomology.cupH' ℤ
    (TopCat.toSSet.obj (TopCat.of ↥W)) k 0 w c) hxy
  rwa [hinv x, hinv y] at h2

/-! ## The main theorem -/

theorem localThom_of_fibreGenerator_chart {B : Type} [TopologicalSpace B] {F : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] {ι : Type} {n : ℕ}
    (Z : Work.TangentClasses.RealBundle B F ι) (σ : Work.Thom.OpenThom Z n)
    (hn : n = Module.finrank ℝ F) (h : Work.ThomBordism.IsFibreGenerator Z n σ) :
    ∀ (i : ι) (W : Set B), W ⊆ Z.baseSet i → ∀ k : ℕ,
      Function.Bijective (Work.Thom.localThomMap Z n W
        ((Work.Thom.PieceRes Z W n).hom σ) k) := by
  have hfr : Module.finrank ℝ F = Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) := by
    rw [finrank_euclideanSpace_fin]
    exact hn.symm
  intro i W hW k
  let e : F ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
    ContinuousLinearEquiv.ofFinrankEq (𝕜 := ℝ) (E := F) (F := EuclideanSpace ℝ (Fin n)) hfr
  -- the coefficient of `σ|_W` with respect to the explicit chart class
  obtain ⟨c, hc⟩ := ((Work.Thom.localThomOfChart Z n e i W hW).isThom 0).2
    ((Nat.zero_add n).symm ▸ ((Work.Thom.PieceRes Z W n).hom σ))
  have hc' : (Work.Thom.PieceRes Z W n).hom σ
      = (Nat.zero_add n) ▸ (Work.Thom.localThomMap Z n W
          (Work.Thom.chartCoh Z n e i W hW) 0 c) := by
    have h2 := congrArg (fun y => (Nat.zero_add n) ▸ y) hc
    rw [Work.Tubular.relCoh_cast_symm_cast] at h2
    exact h2.symm
  -- the fibrewise condition, in the piece language
  have hgen : ∀ (b : B) (hb : b ∈ W),
      Submodule.span ℤ {(Work.Thom.PieceRes Z ({b} : Set B) n).hom σ} = ⊤ :=
    fun b _ => span_pieceRes_singleton Z n σ h b
  -- the coefficient is `±1` at every point, hence an involution
  have hpt := fun b hb => ptEv_coeff_eq_one_or_neg_one Z n e i hW σ c hc' hgen b hb
  have hcup := cup_self_eq_oneH_of_ptEv W c hpt
  -- the local Thom map of `σ|_W` factors as the chart one composed with the cup with `c`
  have hfun : ⇑(Work.Thom.localThomMap Z n W ((Work.Thom.PieceRes Z W n).hom σ) k)
      = ⇑(Work.Thom.localThomMap Z n W (Work.Thom.chartCoh Z n e i W hW) k) ∘
          (fun x : Work.Thom.Coh ℤ k ↥W =>
            Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj (TopCat.of ↥W)) k 0 x c) := by
    funext x
    rw [hc']
    exact localThomMap_cup_general_aux Z n W (Work.Thom.chartCoh Z n e i W hW) c k x
  rw [hfun]
  exact ((Work.Thom.localThomOfChart Z n e i W hW).isThom k).comp
    (bijective_cup_of_involution W c hcup k)

end

end Work.ThomBordism
