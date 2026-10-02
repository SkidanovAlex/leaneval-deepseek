import Mathlib
import Submission.Work.Whitney.RankTwo.Basic
import Submission.Work.Whitney.RankTwo.Eval
import Submission.Work.Whitney.RankTwo.Chain
import Submission.Work.Whitney.RankTwo.Cochains
import Submission.Work.Thom.naturalModelClass_punct
import Submission.Work.Thom.stepDefs
import Submission.Work.Whitney.Mn_one_eq_pairDelta
import Submission.Work.Cohomology.MVcapSquares
import Submission.Work.Thom.Orientation.pairDelta_flip_one
import Submission.Work.Cohomology.KroneckerH
import Submission.Work.Whitney.RankTwo.CupRep

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

namespace Work.Whitney.RankTwo

open Work.Thom Work.Cohomology
open Work.Thom.Orientation
open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Simplicial

noncomputable section

variable (Y : Type) [TopologicalSpace Y]

/-! ## The ambient spaces -/

/-- The total space of the trivial real line bundle over `Y`. -/
abbrev R1 : Type := Y × EuclideanSpace ℝ (Fin 1)

/-- The total space of the trivial real plane bundle over `Y`. -/
abbrev R2 : Type := Y × EuclideanSpace ℝ (Fin 2)

/-- The ball bundle of rank one over `Y`. -/
abbrev BBall : Type := Y × MBall 1

/-! ## Sign cochains -/

/-- The sign of a point of `Y × ℝ¹`: the sign of its fibre coordinate. -/
def signFibR2 (p : R1 Y) : ℤ := posOf (p.2.ofLp 0)

/-- The sign of a point of `Y × D¹`. -/
def signBall (p : BBall Y) : ℤ := posOf (p.2.1.ofLp 0)

/-- The singular simplicial set of `Y × ℝ¹`. -/
abbrev ssR1 : SSet := TopCat.toSSet.obj (TopCat.of (R1 Y))

/-- The simplex equivalence for `Y × ℝ¹`. -/
abbrev eR1 (n : ℕ) :
    (ssR1 Y) _⦋n⦌ ≃ C(stdSimplex ℝ (Fin (n + 1)), TopCat.of (R1 Y)) :=
  TopCat.toSSetObjEquivOld (TopCat.of (R1 Y)) (Opposite.op (SimplexCategory.mk n))

/-- The singular simplicial set of the rank-one sphere bundle `Sph Y 1`. -/
abbrev ssSph1 : SSet := TopCat.toSSet.obj (TopCat.of ↥(Sph Y 1))

/-- The simplex equivalence for the rank-one sphere bundle. -/
abbrev eSph1 (n : ℕ) :
    (ssSph1 Y) _⦋n⦌ ≃ C(stdSimplex ℝ (Fin (n + 1)), TopCat.of ↥(Sph Y 1)) :=
  TopCat.toSSetObjEquivOld (TopCat.of ↥(Sph Y 1)) (Opposite.op (SimplexCategory.mk n))

/-- The singular simplicial set of the ball bundle `Y × D¹`. -/
abbrev ssBall : SSet := TopCat.toSSet.obj (TopCat.of (BBall Y))

/-- The simplex equivalence for the ball bundle. -/
abbrev eBall (n : ℕ) :
    (ssBall Y) _⦋n⦌ ≃ C(stdSimplex ℝ (Fin (n + 1)), TopCat.of (BBall Y)) :=
  TopCat.toSSetObjEquivOld (TopCat.of (BBall Y)) (Opposite.op (SimplexCategory.mk n))

/-- The sign cochain of the rank-one total space. -/
noncomputable def sg0 : Cochain ℤ (ssR1 Y) 0 :=
  cochainOf (ssR1 Y) 0 (fun σ => signFibR2 Y ((eR1 Y 0) σ default))

@[simp] theorem genEval_sg0 (σ : (ssR1 Y) _⦋0⦌) :
    genEval ℤ (ssR1 Y) (sg0 Y) σ = signFibR2 Y ((eR1 Y 0) σ default) :=
  genEval_cochainOf (ssR1 Y) 0 _ σ

/-- The sign cochain of the rank-one sphere bundle. -/
noncomputable def sg0Sph : Cochain ℤ (ssSph1 Y) 0 :=
  cochainOf (ssSph1 Y) 0 (fun σ => signFibR2 Y ((↑((eSph1 Y 0) σ default) : R1 Y)))

@[simp] theorem genEval_sg0Sph (σ : (ssSph1 Y) _⦋0⦌) :
    genEval ℤ (ssSph1 Y) (sg0Sph Y) σ
      = signFibR2 Y ((↑((eSph1 Y 0) σ default) : R1 Y)) :=
  genEval_cochainOf (ssSph1 Y) 0 _ σ

/-- The sign cochain of the ball bundle. -/
noncomputable def sgBall : Cochain ℤ (ssBall Y) 0 :=
  cochainOf (ssBall Y) 0 (fun σ => signBall Y ((eBall Y 0) σ default))

@[simp] theorem genEval_sgBall (σ : (ssBall Y) _⦋0⦌) :
    genEval ℤ (ssBall Y) (sgBall Y) σ = signBall Y ((eBall Y 0) σ default) :=
  genEval_cochainOf (ssBall Y) 0 _ σ

/-- Its differential: the explicit `1`-cocycle of the disc bundle. -/
noncomputable def eta : Cochain ℤ (ssBall Y) 1 := cochainDiff ℤ (ssBall Y) (sgBall Y)

/-! ## The `0`-simplex at a point -/

/-- The `0`-simplex of the ball bundle at a point. -/
noncomputable def ptBall (x : BBall Y) : (ssBall Y) _⦋0⦌ :=
  (eBall Y 0).symm (ContinuousMap.const (stdSimplex ℝ (Fin 1)) x)

@[simp] theorem eBall_ptBall (x : BBall Y) :
    eBall Y 0 (ptBall Y x) = ContinuousMap.const (stdSimplex ℝ (Fin 1)) x :=
  (eBall Y 0).apply_symm_apply _

/-- The `0`-simplex of the rank-one sphere bundle at a point. -/
noncomputable def ptSph1 (x : ↥(Sph Y 1)) : (ssSph1 Y) _⦋0⦌ :=
  (eSph1 Y 0).symm (ContinuousMap.const (stdSimplex ℝ (Fin 1)) x)

@[simp] theorem eSph1_ptSph1 (x : ↥(Sph Y 1)) :
    eSph1 Y 0 (ptSph1 Y x) = ContinuousMap.const (stdSimplex ℝ (Fin 1)) x :=
  (eSph1 Y 0).apply_symm_apply _

theorem genEval_sgBall_ptBall (x : BBall Y) :
    genEval ℤ (ssBall Y) (sgBall Y) (ptBall Y x) = signBall Y x := by
  rw [genEval_sgBall, eBall_ptBall]
  rfl

theorem genEval_sg0Sph_ptSph1 (x : ↥(Sph Y 1)) :
    genEval ℤ (ssSph1 Y) (sg0Sph Y) (ptSph1 Y x)
      = signFibR2 Y ((↑x : R1 Y)) := by
  rw [genEval_sg0Sph, eSph1_ptSph1]
  rfl

/-! ## The straight simplices of the ball whose cap images are the arcs -/

/-- The angle function of the `k`-th arc, as a bundled continuous map. -/
noncomputable def arcAngC (k : ℕ) : C(stdSimplex ℝ (Fin 2), ℝ) :=
  (ContinuousMap.const _ (ang k)) * (coord 2 0)
    + (ContinuousMap.const _ (ang (k + 1))) * (coord 2 1)

@[simp] theorem arcAngC_apply (k : ℕ) (q : stdSimplex ℝ (Fin 2)) :
    arcAngC k q = ang k * q 0 + ang (k + 1) * q 1 := rfl

/-- The cosine of the angle of the `k`-th arc. -/
noncomputable def segCosC (k : ℕ) : C(stdSimplex ℝ (Fin 2), ℝ) :=
  (⟨Real.cos, Real.continuous_cos⟩ : C(ℝ, ℝ)).comp (arcAngC k)

theorem norm_one1 : ‖(one1 : EuclideanSpace ℝ (Fin 1))‖ = 1 :=
  Work.Cohomology.s0N.2

/-- The straight segment of the ball whose cap image is the `k`-th arc, as a vector. -/
noncomputable def segVecC (k : ℕ) : C(stdSimplex ℝ (Fin 2), EuclideanSpace ℝ (Fin 1)) :=
  ⟨fun q => (segCosC k q) • one1, (segCosC k).continuous.smul continuous_const⟩

@[simp] theorem segVecC_apply (k : ℕ) (q : stdSimplex ℝ (Fin 2)) :
    segVecC k q = (segCosC k q) • (one1 : EuclideanSpace ℝ (Fin 1)) := rfl

theorem segVecC_mem (k : ℕ) (q : stdSimplex ℝ (Fin 2)) : segVecC k q ∈ mBall 1 := by
  show ‖segVecC k q‖ ≤ 1
  rw [segVecC_apply, norm_smul, norm_one1, mul_one, Real.norm_eq_abs]
  exact abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩

/-- The `k`-th straight segment of the ball, as a continuous map into `Y × D¹`. -/
noncomputable def segC (y : Y) (k : ℕ) : C(stdSimplex ℝ (Fin 2), TopCat.of (BBall Y)) :=
  ⟨fun q => (y, ⟨segVecC k q, segVecC_mem k q⟩),
    Continuous.prodMk continuous_const
      (Continuous.subtype_mk (segVecC k).continuous (fun q => segVecC_mem k q))⟩

theorem segC_apply (y : Y) (k : ℕ) (q : stdSimplex ℝ (Fin 2)) :
    (segC Y y k q : BBall Y) = (y, ⟨segVecC k q, segVecC_mem k q⟩) := rfl

theorem segC_vec (y : Y) (k : ℕ) (q : stdSimplex ℝ (Fin 2)) :
    (segC Y y k q : BBall Y).2.1 = segVecC k q := rfl

theorem segC_fst (y : Y) (k : ℕ) (q : stdSimplex ℝ (Fin 2)) :
    (segC Y y k q : BBall Y).1 = y := rfl

/-- The corresponding singular simplex. -/
noncomputable def segSimp (y : Y) (k : ℕ) : (ssBall Y) _⦋1⦌ :=
  (eBall Y 1).symm (segC Y y k)

@[simp] theorem eBall_segSimp (y : Y) (k : ℕ) : eBall Y 1 (segSimp Y y k) = segC Y y k :=
  (eBall Y 1).apply_symm_apply _

/-- The chain `Σ_{k<3} seg k` of the three straight simplices. -/
noncomputable def segChain (y : Y) : ((ssBall Y).chainComplex zR).X 1 :=
  ∑ k ∈ Finset.range 3, ((ssBall Y).ιChainComplex (R := zR) (segSimp Y y k)).hom 1

/-! ## The arcs of the hexagon in the three ambient spaces -/

/-- The singular simplicial set of `Y × ℝ²`. -/
abbrev ssR2 : SSet := TopCat.toSSet.obj (TopCat.of (R2 Y))

/-- The simplex equivalence for `Y × ℝ²`. -/
abbrev eR2 (n : ℕ) :
    (ssR2 Y) _⦋n⦌ ≃ C(stdSimplex ℝ (Fin (n + 1)), TopCat.of (R2 Y)) :=
  TopCat.toSSetObjEquivOld (TopCat.of (R2 Y)) (Opposite.op (SimplexCategory.mk n))

/-- The singular simplicial set of `Y × S¹` (the rank-two sphere bundle before the identification
with the subspace of `Y × ℝ²`). -/
abbrev ssMSph2 : SSet := TopCat.toSSet.obj (TopCat.of (Y × MSph 2))

/-- The simplex equivalence for `Y × S¹`. -/
abbrev eMSph2 (n : ℕ) :
    (ssMSph2 Y) _⦋n⦌ ≃ C(stdSimplex ℝ (Fin (n + 1)), TopCat.of (Y × MSph 2)) :=
  TopCat.toSSetObjEquivOld (TopCat.of (Y × MSph 2)) (Opposite.op (SimplexCategory.mk n))

/-- The singular simplicial set of `Thom.Sph Y 2 ⊆ Y × ℝ²`. -/
abbrev ssSph2 : SSet := TopCat.toSSet.obj (TopCat.of ↥(Sph Y 2))

/-- The simplex equivalence for the rank-two sphere bundle. -/
abbrev eSph2 (n : ℕ) :
    (ssSph2 Y) _⦋n⦌ ≃ C(stdSimplex ℝ (Fin (n + 1)), TopCat.of ↥(Sph Y 2)) :=
  TopCat.toSSetObjEquivOld (TopCat.of ↥(Sph Y 2)) (Opposite.op (SimplexCategory.mk n))

/-- The unit vector of the `k`-th arc, as a continuous map into `ℝ²`. -/
noncomputable def arcVecC (k : ℕ) : C(stdSimplex ℝ (Fin 2), EuclideanSpace ℝ (Fin 2)) :=
  ⟨fun q => u2 (arcAngC k q), continuous_u2.comp (arcAngC k).continuous⟩

@[simp] theorem arcVecC_apply (k : ℕ) (q : stdSimplex ℝ (Fin 2)) :
    arcVecC k q = u2 (arcAngC k q) := rfl

/-- The `k`-th arc, as a continuous map into `Y × ℝ²`. -/
noncomputable def arcUC (y : Y) (k : ℕ) :
    C(stdSimplex ℝ (Fin 2), TopCat.of (R2 Y)) :=
  ⟨fun q => (y, arcVecC k q), continuous_const.prodMk (arcVecC k).continuous⟩

@[simp] theorem arcUC_apply (y : Y) (k : ℕ) (q : stdSimplex ℝ (Fin 2)) :
    arcUC Y y k q = (y, arcVecC k q) := rfl

/-- The `k`-th arc, as a singular simplex of `Y × ℝ²`. -/
noncomputable def arcUSimp (y : Y) (k : ℕ) : (ssR2 Y) _⦋1⦌ :=
  (eR2 Y 1).symm (arcUC Y y k)

@[simp] theorem eR2_arcUSimp (y : Y) (k : ℕ) : eR2 Y 1 (arcUSimp Y y k) = arcUC Y y k :=
  (eR2 Y 1).apply_symm_apply _

/-- The `k`-th arc, as a continuous map into `Y × S¹`. -/
noncomputable def arcSphC (y : Y) (k : ℕ) :
    C(stdSimplex ℝ (Fin 2), TopCat.of (Y × MSph 2)) :=
  ⟨fun q => (y, ⟨arcVecC k q, norm_u2 _⟩),
    continuous_const.prodMk
      (Continuous.subtype_mk (arcVecC k).continuous (fun q => norm_u2 _))⟩

@[simp] theorem arcSphC_apply (y : Y) (k : ℕ) (q : stdSimplex ℝ (Fin 2)) :
    arcSphC Y y k q = (y, ⟨arcVecC k q, norm_u2 _⟩) := rfl

/-- The `k`-th arc, as a singular simplex of `Y × S¹`. -/
noncomputable def arcSphSimp (y : Y) (k : ℕ) : (ssMSph2 Y) _⦋1⦌ :=
  (eMSph2 Y 1).symm (arcSphC Y y k)

@[simp] theorem eMSph2_arcSphSimp (y : Y) (k : ℕ) :
    eMSph2 Y 1 (arcSphSimp Y y k) = arcSphC Y y k :=
  (eMSph2 Y 1).apply_symm_apply _

/-- The `k`-th arc, as a continuous map into the rank-two sphere bundle `Sph Y 2`. -/
noncomputable def arcSC (y : Y) (k : ℕ) :
    C(stdSimplex ℝ (Fin 2), TopCat.of ↥(Sph Y 2)) :=
  ⟨fun q => ⟨(y, arcVecC k q), norm_u2 _⟩,
    Continuous.subtype_mk
      (continuous_const.prodMk (arcVecC k).continuous) (fun q => norm_u2 _)⟩

@[simp] theorem arcSC_apply (y : Y) (k : ℕ) (q : stdSimplex ℝ (Fin 2)) :
    arcSC Y y k q = ⟨(y, arcVecC k q), norm_u2 _⟩ := rfl

/-- The `k`-th arc, as a singular simplex of `Sph Y 2`. -/
noncomputable def arcSSimp (y : Y) (k : ℕ) : (ssSph2 Y) _⦋1⦌ :=
  (eSph2 Y 1).symm (arcSC Y y k)

@[simp] theorem eSph2_arcSSimp (y : Y) (k : ℕ) : eSph2 Y 1 (arcSSimp Y y k) = arcSC Y y k :=
  (eSph2 Y 1).apply_symm_apply _


/-! ## The base, the sections and the boundary of the disc bundle -/

/-- The singular simplicial set of the base. -/
abbrev ssY : SSet := TopCat.toSSet.obj (TopCat.of Y)

/-- The underlying map of a pushed-forward simplex. -/
theorem toSSetObjEquiv_app_eq (P P' : TopCat) (g : P ⟶ P') (n : ℕ)
    (x : (TopCat.toSSet.obj P).obj (Opposite.op (SimplexCategory.mk n)))
    (t : stdSimplex ℝ (Fin (n + 1))) :
    (TopCat.toSSetObjEquivOld P' (Opposite.op (SimplexCategory.mk n)))
        ((ConcreteCategory.hom ((TopCat.toSSet.map g).app (Opposite.op (SimplexCategory.mk n)))) x) t
      = g ((TopCat.toSSetObjEquivOld P (Opposite.op (SimplexCategory.mk n))) x t) := rfl

/-- The pullback of a cochain along a continuous map, evaluated on a simplex. -/
theorem genEval_pullback {X Z : TopCat} (f : X ⟶ Z) {n : ℕ}
    (α : Cochain ℤ (TopCat.toSSet.obj Z) n) (σ : (TopCat.toSSet.obj X) _⦋n⦌) :
    genEval ℤ (TopCat.toSSet.obj X) (((dualChainMap ℤ X Z f).f n).hom α) σ
      = genEval ℤ (TopCat.toSSet.obj Z) α ((TopCat.toSSet.map f).app (Opposite.op ⦋n⦌) σ) := by
  rw [dualChainMap_f_hom]
  exact genEval_dualMap ℤ (TopCat.toSSet.map f) α σ

/-- The pullback of a cochain along a continuous map, as a cochain. -/
noncomputable abbrev pullCM {X Z : Type} [TopologicalSpace X] [TopologicalSpace Z]
    (f : C(X, Z)) {n : ℕ} (α : Cochain ℤ (TopCat.toSSet.obj (TopCat.of Z)) n) :
    Cochain ℤ (TopCat.toSSet.obj (TopCat.of X)) n :=
  ((dualChainMap ℤ (TopCat.of X) (TopCat.of Z) (TopCat.ofHom f)).f n).hom α

/-- The defining evaluation rule of `pullCM`. -/
theorem genEval_pullCM {X Z : Type} [TopologicalSpace X] [TopologicalSpace Z]
    (f : C(X, Z)) {n : ℕ} (α : Cochain ℤ (TopCat.toSSet.obj (TopCat.of Z)) n)
    (σ : (TopCat.toSSet.obj (TopCat.of X)) _⦋n⦌) :
    genEval ℤ (TopCat.toSSet.obj (TopCat.of X)) (pullCM f α) σ
      = genEval ℤ (TopCat.toSSet.obj (TopCat.of Z)) α
          ((TopCat.toSSet.map (TopCat.ofHom f)).app (Opposite.op ⦋n⦌) σ) :=
  genEval_pullback (TopCat.ofHom f) α σ

/-- The fibre coordinate of a point of the rank-one sphere bundle never vanishes. -/
theorem sph1_coord_ne_zero (p : ↥(Sph Y 1)) : ((p : R1 Y).2.ofLp 0) ≠ 0 := by
  intro h
  have h0 : (p : R1 Y).2 = 0 := (ofLp_zero_iff (p : R1 Y).2).mp h
  have h1 : ‖(p : R1 Y).2‖ = 1 := p.2
  rw [h0, norm_zero] at h1
  norm_num at h1

theorem signFibR2_sphPlus (y : Y) : signFibR2 Y (y, (sphPlus : EuclideanSpace ℝ (Fin 1))) = 1 := by
  change posOf ((sphPlus : EuclideanSpace ℝ (Fin 1)).ofLp 0) = 1
  rw [show (sphPlus : EuclideanSpace ℝ (Fin 1)).ofLp 0 = (1 : ℝ) from rfl, posOf_pos one_pos]

theorem signFibR2_sphMinus (y : Y) : signFibR2 Y (y, (sphMinus : EuclideanSpace ℝ (Fin 1))) = 0 := by
  change posOf ((sphMinus : EuclideanSpace ℝ (Fin 1)).ofLp 0) = 0
  rw [show (sphMinus : EuclideanSpace ℝ (Fin 1)).ofLp 0 = (-1 : ℝ) from rfl,
    posOf_nonpos (by norm_num)]

theorem sphPlus_mem_ball : (sphPlus : EuclideanSpace ℝ (Fin 1)) ∈ mBall 1 := by
  show ‖(sphPlus : EuclideanSpace ℝ (Fin 1))‖ ≤ 1
  rw [show (sphPlus : EuclideanSpace ℝ (Fin 1)) = (one1 : EuclideanSpace ℝ (Fin 1)) from rfl,
    norm_one1]

theorem sphMinus_mem_ball : (sphMinus : EuclideanSpace ℝ (Fin 1)) ∈ mBall 1 := by
  show ‖(sphMinus : EuclideanSpace ℝ (Fin 1))‖ ≤ 1
  rw [show (sphMinus : EuclideanSpace ℝ (Fin 1)) = -(one1 : EuclideanSpace ℝ (Fin 1)) from rfl,
    norm_neg, norm_one1]

theorem signBall_plus (y : Y) : signBall Y (y, ⟨sphPlus, sphPlus_mem_ball⟩) = 1 := by
  change posOf ((sphPlus : EuclideanSpace ℝ (Fin 1)).ofLp 0) = 1
  rw [show (sphPlus : EuclideanSpace ℝ (Fin 1)).ofLp 0 = (1 : ℝ) from rfl, posOf_pos one_pos]

theorem signBall_minus (y : Y) : signBall Y (y, ⟨sphMinus, sphMinus_mem_ball⟩) = 0 := by
  change posOf ((sphMinus : EuclideanSpace ℝ (Fin 1)).ofLp 0) = 0
  rw [show (sphMinus : EuclideanSpace ℝ (Fin 1)).ofLp 0 = (-1 : ℝ) from rfl,
    posOf_nonpos (by norm_num)]

/-- The point `(y, +1)` of the disc bundle, as a `0`-simplex. -/
noncomputable def ballPlus (y : Y) : (ssBall Y) _⦋0⦌ :=
  ptBall Y (y, ⟨sphPlus, sphPlus_mem_ball⟩)

/-- The point `(y, -1)` of the disc bundle, as a `0`-simplex. -/
noncomputable def ballMinus (y : Y) : (ssBall Y) _⦋0⦌ :=
  ptBall Y (y, ⟨sphMinus, sphMinus_mem_ball⟩)

theorem genEval_sgBall_ballPlus (y : Y) :
    genEval ℤ (ssBall Y) (sgBall Y) (ballPlus Y y) = 1 := by
  rw [ballPlus, genEval_sgBall_ptBall, signBall_plus]

theorem genEval_sgBall_ballMinus (y : Y) :
    genEval ℤ (ssBall Y) (sgBall Y) (ballMinus Y y) = 0 := by
  rw [ballMinus, genEval_sgBall_ptBall, signBall_minus]

/-! ## The boundary of the disc bundle and the restricted disc-full map -/

/-- The singular simplicial set of the boundary `DiscB Y 1` of the disc bundle. -/
abbrev ssDiscB : SSet := TopCat.toSSet.obj (TopCat.of ↥(DiscB Y 1))

/-- The simplex equivalence for the boundary of the disc bundle. -/
abbrev eDiscB (n : ℕ) :
    (ssDiscB Y) _⦋n⦌ ≃ C(stdSimplex ℝ (Fin (n + 1)), TopCat.of ↥(DiscB Y 1)) :=
  TopCat.toSSetObjEquivOld (TopCat.of ↥(DiscB Y 1)) (Opposite.op (SimplexCategory.mk n))

/-- The disc-full map, restricted to the boundary of the disc bundle. -/
noncomputable def resDisc : C(↥(DiscB Y 1), ↥(Sph Y 1)) :=
  ⟨fun q => ⟨CleanA.discFullMap Y 1 q.1, CleanA.discFullMap_mem Y 1 q.1 q.2⟩,
    Continuous.subtype_mk ((CleanA.discFullMap Y 1).continuous.comp continuous_subtype_val)
      (fun q => CleanA.discFullMap_mem Y 1 q.1 q.2)⟩

theorem resDisc_val (q : ↥(DiscB Y 1)) :
    ((resDisc Y q : ↥(Sph Y 1)) : R1 Y) = CleanA.discFullMap Y 1 q.1 := rfl

/-- The boundary cochain of the disc bundle: the restriction of the sign cochain. -/
noncomputable abbrev gamma : Cochain ℤ (ssDiscB Y) 0 :=
  ((dualChainMap ℤ (TopCat.of ↥(DiscB Y 1)) (TopCat.of ↥(Sph Y 1))
      (TopCat.ofHom (resDisc Y))).f 0) (sg0Sph Y)


/-! ## Pullbacks of cochains along simplicial maps and continuous maps -/

/-- The pullback of a cochain along a simplicial map. -/
noncomputable abbrev pullC {X Y : SSet} (f : X ⟶ Y) {n : ℕ} (α : Cochain ℤ Y n) : Cochain ℤ X n :=
  ((SSet.chainComplexMap f (ModuleCat.of ℤ ℤ)).f n).hom.dualMap α

/-- The defining evaluation rule of `pullC`. -/
theorem genEval_pullC {X Y : SSet} (f : X ⟶ Y) {n : ℕ} (α : Cochain ℤ Y n) (σ : X _⦋n⦌) :
    genEval ℤ X (pullC f α) σ
      = genEval ℤ Y α ((ConcreteCategory.hom (f.app (Opposite.op ⦋n⦌))) σ) :=
  genEval_dualMap ℤ f α σ

/-- The pullback of a cochain commutes with the differential. -/
theorem cochainDiff_pullC {X Y : SSet} (f : X ⟶ Y) {n : ℕ} (α : Cochain ℤ Y n) :
    cochainDiff ℤ X (pullC f α) = pullC f (cochainDiff ℤ Y α) := by
  apply genEval_ext
  intro σ
  rw [genEval_cochainDiff, genEval_pullC, genEval_cochainDiff]
  exact Finset.sum_congr rfl fun i _ => by rw [genEval_pullC, SSet.δ_naturality_apply]

/-- The pullback of a cochain along a continuous map commutes with the differential. -/
theorem cochainDiff_pullCM {X Z : Type} [TopologicalSpace X] [TopologicalSpace Z]
    (f : C(X, Z)) {n : ℕ} (α : Cochain ℤ (TopCat.toSSet.obj (TopCat.of Z)) n) :
    cochainDiff ℤ (TopCat.toSSet.obj (TopCat.of X)) (pullCM f α)
      = pullCM f (cochainDiff ℤ (TopCat.toSSet.obj (TopCat.of Z)) α) :=
  cochainDiff_pullC (TopCat.toSSet.map (TopCat.ofHom f)) α

/-! ## The sign cochain of the rank-one sphere bundle is a cocycle -/

/-- The base, as a simplicial set with its simplices as continuous maps. -/
abbrev eY (n : ℕ) : (ssY Y) _⦋n⦌ ≃ C(stdSimplex ℝ (Fin (n + 1)), TopCat.of Y) :=
  TopCat.toSSetObjEquivOld (TopCat.of Y) (Opposite.op (SimplexCategory.mk n))

theorem eSph1_δ_apply {n : ℕ} (x : (ssSph1 Y) _⦋n + 1⦌) (i : Fin (n + 2))
    (z : stdSimplex ℝ (Fin (n + 1))) :
    eSph1 Y n ((ssSph1 Y).δ i x) z = eSph1 Y (n + 1) x (stdSimplex.map i.succAbove z) :=
  TopCat.toSSetObjEquivOld_δ_apply x i z

theorem ssSph1_δ_zero_eq_ptSph1 (σ : (ssSph1 Y) _⦋1⦌) :
    (ssSph1 Y).δ 0 σ = ptSph1 Y ((eSph1 Y 1) σ (stdSimplex.vertex (1 : Fin 2))) := by
  apply (eSph1 Y 0).injective
  apply ContinuousMap.ext
  intro z
  rw [eSph1_δ_apply, eSph1_ptSph1, ContinuousMap.const_apply, map_succAbove0_eq_vertex]

theorem ssSph1_δ_one_eq_ptSph1 (σ : (ssSph1 Y) _⦋1⦌) :
    (ssSph1 Y).δ 1 σ = ptSph1 Y ((eSph1 Y 1) σ (stdSimplex.vertex (0 : Fin 2))) := by
  apply (eSph1 Y 0).injective
  apply ContinuousMap.ext
  intro z
  rw [eSph1_δ_apply, eSph1_ptSph1, ContinuousMap.const_apply, map_succAbove1_eq_vertex]

theorem genEval_cochainDiff_sg0Sph (σ : (ssSph1 Y) _⦋1⦌) :
    genEval ℤ (ssSph1 Y) (cochainDiff ℤ (ssSph1 Y) (sg0Sph Y)) σ
      = signFibR2 Y (↑((eSph1 Y 1) σ (stdSimplex.vertex (1 : Fin 2))) : R1 Y)
        - signFibR2 Y (↑((eSph1 Y 1) σ (stdSimplex.vertex (0 : Fin 2))) : R1 Y) := by
  rw [genEval_cochainDiff, Fin.sum_univ_two, ssSph1_δ_zero_eq_ptSph1, ssSph1_δ_one_eq_ptSph1,
    genEval_sg0Sph_ptSph1, genEval_sg0Sph_ptSph1]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_mul, neg_one_mul]
  ring

theorem sg0Sph_coc : cochainDiff ℤ (ssSph1 Y) (sg0Sph Y) = 0 := by
  apply genEval_ext
  intro σ
  rw [genEval_cochainDiff_sg0Sph]
  show signFibR2 Y (↑((eSph1 Y 1) σ (stdSimplex.vertex (1 : Fin 2))) : R1 Y)
      - signFibR2 Y (↑((eSph1 Y 1) σ (stdSimplex.vertex (0 : Fin 2))) : R1 Y)
      = genEval ℤ (ssSph1 Y) (0 : Cochain ℤ (ssSph1 Y) 1) σ
  rw [show genEval ℤ (ssSph1 Y) (0 : Cochain ℤ (ssSph1 Y) 1) σ = 0 from rfl]
  have hcont : Continuous fun q : stdSimplex ℝ (Fin 2) =>
      (((eSph1 Y 1) σ q : ↥(Sph Y 1)) : R1 Y).2.ofLp 0 := by fun_prop
  have hne : ∀ q : stdSimplex ℝ (Fin 2),
      (((eSph1 Y 1) σ q : ↥(Sph Y 1)) : R1 Y).2.ofLp 0 ≠ 0 :=
    fun q => sph1_coord_ne_zero Y ((eSph1 Y 1) σ q)
  have hconst := posOf_const_of_continuous_ne_zero (f := ⟨_, hcont⟩) hne
  by_cases h1 : 0 < (((eSph1 Y 1) σ (stdSimplex.vertex (1 : Fin 2)) : ↥(Sph Y 1)) : R1 Y).2.ofLp 0
  · have h0 : 0 < (((eSph1 Y 1) σ (stdSimplex.vertex (0 : Fin 2)) : ↥(Sph Y 1)) : R1 Y).2.ofLp 0 :=
      hconst.mpr h1
    rw [signFibR2, signFibR2, posOf_pos h1, posOf_pos h0, sub_self]
  · have h0 : ¬ 0 < (((eSph1 Y 1) σ (stdSimplex.vertex (0 : Fin 2)) : ↥(Sph Y 1)) : R1 Y).2.ofLp 0 :=
      fun h0 => h1 (hconst.mp h0)
    rw [signFibR2, signFibR2, posOf_nonpos h1, posOf_nonpos h0, sub_self]

/-! ## The sections and the boundary cochain -/


/-- The "lower band" of the rank-two sphere bundle: the points whose unit fibre vector lies in
`mLower 1`.  It contains the lower half of the hexagon. -/
abbrev lowerBand : Set (R2 Y) := {p | p.2 ∈ mLower 1}


/-- The cap map followed by the identification of `Y × S¹` with the rank-two sphere bundle. -/
noncomputable abbrev capHomeo : C(BBall Y, ↥(Sph Y 2)) :=
  (((prodSubsetHomeoA Y (EuclideanSpace ℝ (Fin 2)) (mSph 2) : C(Y × MSph 2, ↥(Sph Y 2))))).comp
    (capMapPairSph Y 1)

end

end Work.Whitney.RankTwo
