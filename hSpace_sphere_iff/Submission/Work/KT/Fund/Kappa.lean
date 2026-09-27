import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.Fund.Basic
import Submission.Work.KT.Fund.Geom
import Submission.Work.KT.Fund.Pullback
import Submission.Work.KT.Fund.Clutch
import Submission.Work.KT.Fund.clutch_agree
import Submission.Work.KT.Fund.OrthProjAlg
import Submission.Work.KT.Fund.isUnit_one_add_conjTranspose_mul
import Submission.Work.KT.Fund.graphB_recipB_conjTranspose_mul_self
import Submission.Work.KT.Bott.patch_idem_dim
import Submission.Work.KT.ExtGen.disc_square
import Submission.Work.KT.Fund.Laurent

/-!
# `Work.KT.Fund.Kappa` — the clutched class `κ(u)` of a unit over `C(X × S¹, ℂ)`

For an invertible matrix `u` over `C(X × S¹, ℂ)` the *clutching construction* glues two trivial
bundles over the two hemispheres of `S²` along `u`; the result is a well defined class
`kappa u ∈ K0 C(X × S², ℂ)`.  Concretely, with `F`, `G` lifts of `u` and `u⁻¹` to the disc,

  `kappa u = k0Glue.symm (cls (pairMat (orthProj [[1],[F]]) (orthProj [[G],[1]])))`,

an idempotent over `pullAlg2 X` of size `2n`.  This is the element of `K̃(X × S²)` of Hatcher's
elementary proof of Bott periodicity.
-/

namespace Work.KT.Fund

open Matrix

noncomputable section

variable (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]

/-! ## The two projections out of the fibre product -/

/-- The first projection `↥(pullAlg2 X) →+* C(X × D, ℂ)`. -/
def prF : ↥(pullAlg2 X) →+* C(X × Ball ℂ, ℂ) :=
  (RingHom.fst (C(X × Ball ℂ, ℂ)) (C(X × Ball ℂ, ℂ))).comp (pullAlg2 X).val.toRingHom

/-- The second projection `↥(pullAlg2 X) →+* C(X × D, ℂ)`. -/
def prS : ↥(pullAlg2 X) →+* C(X × Ball ℂ, ℂ) :=
  (RingHom.snd (C(X × Ball ℂ, ℂ)) (C(X × Ball ℂ, ℂ))).comp (pullAlg2 X).val.toRingHom

@[simp] lemma prF_apply (z : ↥(pullAlg2 X)) : prF X z = z.1.1 := rfl
@[simp] lemma prS_apply (z : ↥(pullAlg2 X)) : prS X z = z.1.2 := rfl

/-- Two matrices over `pullAlg2 X` which agree after both projections are equal. -/
lemma mat_ext {ι : Type} {A B : Matrix ι ι ↥(pullAlg2 X)}
    (h₁ : A.map (prF X) = B.map (prF X)) (h₂ : A.map (prS X) = B.map (prS X)) : A = B := by
  refine Matrix.ext fun i j => ?_
  refine Subtype.ext ?_
  refine Prod.ext ?_ ?_
  · have h := congrFun (congrFun h₁ i) j
    rw [Matrix.map_apply, Matrix.map_apply, prF_apply, prF_apply] at h
    exact h
  · have h := congrFun (congrFun h₂ i) j
    rw [Matrix.map_apply, Matrix.map_apply, prS_apply, prS_apply] at h
    exact h

/-- The element of `pullAlg2 X` from a compatible pair of disc functions. -/
def mkPair (a₀ a₁ : C(X × Ball ℂ, ℂ)) (h : bdryRestrict X a₀ = bdryRestrict X a₁) :
    ↥(pullAlg2 X) := ⟨(a₀, a₁), h⟩

@[simp] lemma prF_mkPair (a₀ a₁ : C(X × Ball ℂ, ℂ)) (h) :
    prF X (mkPair X a₀ a₁ h) = a₀ := rfl

@[simp] lemma prS_mkPair (a₀ a₁ : C(X × Ball ℂ, ℂ)) (h) :
    prS X (mkPair X a₀ a₁ h) = a₁ := rfl

/-- Matrices over `pullAlg2 X` from a compatible pair of matrices over the disc. -/
def pairMat {ι : Type} (M₀ M₁ : Matrix ι ι C(X × Ball ℂ, ℂ))
    (h : M₀.map (fun f => bdryRestrict X f) = M₁.map (fun f => bdryRestrict X f)) :
    Matrix ι ι ↥(pullAlg2 X) :=
  fun i j => mkPair X (M₀ i j) (M₁ i j) (by
    have h' := congrFun (congrFun h i) j
    simpa only [Matrix.map_apply] using h')

@[simp] lemma pairMat_map_prF {ι : Type} (M₀ M₁ : Matrix ι ι C(X × Ball ℂ, ℂ))
    (h : M₀.map (fun f => bdryRestrict X f) = M₁.map (fun f => bdryRestrict X f)) :
    (pairMat X M₀ M₁ h).map (prF X) = M₀ := rfl

@[simp] lemma pairMat_map_prS {ι : Type} (M₀ M₁ : Matrix ι ι C(X × Ball ℂ, ℂ))
    (h : M₀.map (fun f => bdryRestrict X f) = M₁.map (fun f => bdryRestrict X f)) :
    (pairMat X M₀ M₁ h).map (prS X) = M₁ := rfl

/-! ## The clutched idempotent -/

/-- The clutched idempotent over `pullAlg2 X` attached to a unit `u` over the circle and lifts
`F`, `G` of `u`, `u⁻¹` to the disc: the orthogonal projection onto the graph of `F` over the
first disc, glued to the projection onto the reciprocal graph of `G` over the second. -/
def clutchIdem (n : ℕ) (u : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ)
    (F G : Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ))
    (hF : F.map (fun f => bdryRestrict X f) = ↑u)
    (hG : G.map (fun f => bdryRestrict X f) = ↑(u⁻¹)) : Mat ↥(pullAlg2 X) :=
  ⟨n + n, Matrix.reindex finSumFinEquiv finSumFinEquiv
    (pairMat X (graphProj C(X × Ball ℂ, ℂ) F) (recipProj C(X × Ball ℂ, ℂ) G)
      (clutch_agree X n u F G hF hG))⟩

lemma reindex_mul_self {a b : ℕ} (M : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) ↥(pullAlg2 X)) :
    (Matrix.reindex finSumFinEquiv finSumFinEquiv M) *
        (Matrix.reindex finSumFinEquiv finSumFinEquiv M)
      = Matrix.reindex finSumFinEquiv finSumFinEquiv (M * M) := by
  simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv]

lemma graphProj_isIdem {n : ℕ} (F : Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ)) :
    graphProj C(X × Ball ℂ, ℂ) F * graphProj C(X × Ball ℂ, ℂ) F
      = graphProj C(X × Ball ℂ, ℂ) F := by
  unfold graphProj
  exact orthProj_mul_self _ _ (by
    rw [(graphB_recipB_conjTranspose_mul_self C(X × Ball ℂ, ℂ) F F).1]
    exact isUnit_one_add_conjTranspose_mul F)

lemma recipProj_isIdem {n : ℕ} (G : Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ)) :
    recipProj C(X × Ball ℂ, ℂ) G * recipProj C(X × Ball ℂ, ℂ) G
      = recipProj C(X × Ball ℂ, ℂ) G := by
  unfold recipProj
  exact orthProj_mul_self _ _ (by
    rw [(graphB_recipB_conjTranspose_mul_self C(X × Ball ℂ, ℂ) G G).2]
    exact isUnit_one_add_conjTranspose_mul G)

lemma clutchIdem_isIdem (n : ℕ) (u : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ)
    (F G : Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ))
    (hF : F.map (fun f => bdryRestrict X f) = ↑u)
    (hG : G.map (fun f => bdryRestrict X f) = ↑(u⁻¹)) :
    (clutchIdem X n u F G hF hG).IsIdem := by
  show (Matrix.reindex finSumFinEquiv finSumFinEquiv
        (pairMat X (graphProj C(X × Ball ℂ, ℂ) F) (recipProj C(X × Ball ℂ, ℂ) G)
          (clutch_agree X n u F G hF hG))) *
      (Matrix.reindex finSumFinEquiv finSumFinEquiv
        (pairMat X (graphProj C(X × Ball ℂ, ℂ) F) (recipProj C(X × Ball ℂ, ℂ) G)
          (clutch_agree X n u F G hF hG))) = _
  rw [reindex_mul_self]
  congr 1
  apply mat_ext X
  · rw [Matrix.map_mul, pairMat_map_prF, graphProj_isIdem]
  · rw [Matrix.map_mul, pairMat_map_prS, recipProj_isIdem]

/-! ## Continuity and closedness of the fibre product -/

/-- The inclusion `X × S¹ → X × D` as a continuous map. -/
def sphInclCm : C(X × Sph ℂ, X × Ball ℂ) where
  toFun p := (p.1, sphIncl p.2)
  continuous_toFun := by
    exact continuous_fst.prodMk (sphIncl.continuous.comp continuous_snd)

lemma bdryRestrict_eq_comp :
    (⇑(bdryRestrict X) : C(X × Ball ℂ, ℂ) → C(X × Sph ℂ, ℂ))
      = fun g => g.comp (sphInclCm X) := by
  funext g
  exact ContinuousMap.compStarAlgHom'_apply ℂ ℂ (sphInclCm X) g

lemma continuous_bdryRestrict : Continuous (bdryRestrict X) := by
  rw [bdryRestrict_eq_comp]
  exact ContinuousMap.continuous_precomp (sphInclCm X)

lemma isClosed_pullAlg2 :
    IsClosed (pullAlg2 X).carrier := by
  have hc : Continuous (fun z : C(X × Ball ℂ, ℂ) × C(X × Ball ℂ, ℂ) =>
      (bdryRestrict X z.1, bdryRestrict X z.2)) :=
    ((continuous_bdryRestrict X).comp continuous_fst).prodMk
      ((continuous_bdryRestrict X).comp continuous_snd)
  have hset : (pullAlg2 X).carrier
      = (fun z : C(X × Ball ℂ, ℂ) × C(X × Ball ℂ, ℂ) =>
          (bdryRestrict X z.1, bdryRestrict X z.2)) ⁻¹'
        {w : C(X × Sph ℂ, ℂ) × C(X × Sph ℂ, ℂ) | w.1 = w.2} := by
    ext z; rfl
  rw [hset]
  exact (isClosed_eq continuous_fst continuous_snd).preimage hc

/-! ## The clutched class `κ(u)` -/

/-- A lift of a matrix over `C(X × S¹, ℂ)` to the disc (Tietze). -/
def liftOf {m : ℕ} (M : Matrix (Fin m) (Fin m) C(X × Sph ℂ, ℂ)) :
    Matrix (Fin m) (Fin m) C(X × Ball ℂ, ℂ) :=
  (Bott.mat_lift_surj (bdryRestrict X) (ExtGen.bdryRestrict_surjective X) M).choose

lemma liftOf_spec {m : ℕ} (M : Matrix (Fin m) (Fin m) C(X × Sph ℂ, ℂ)) :
    (liftOf X M).map (fun f => bdryRestrict X f) = M :=
  (Bott.mat_lift_surj (bdryRestrict X) (ExtGen.bdryRestrict_surjective X) M).choose_spec

/-- The clutched class `κ(u) ∈ K0 C(X × S², ℂ)` of a unit `u` over the circle. -/
def kappa (n : ℕ) (u : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ) : K0 C(X × S2, ℂ) :=
  let uM : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ) := u
  let vM : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ) :=
    (u⁻¹ : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ)
  (k0Glue X).symm (cls (clutchIdem X n u (liftOf X uM) (liftOf X vM)
    (liftOf_spec X uM) (liftOf_spec X vM)))

lemma kappa_val (n : ℕ) (u : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ) :
    kappa X n u = (k0Glue X).symm (cls (clutchIdem X n u
      (liftOf X (u : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)))
      (liftOf X ((u⁻¹ : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ) :
        Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)))
      (liftOf_spec X (u : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)))
      (liftOf_spec X ((u⁻¹ : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ) :
        Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))))) := rfl

/-! ## Auxiliary maps: slices of a homotopy, and the Bott unit -/

/-- `(x, z) ↦ ((x, 0), z)`. -/
def incl0 : C(X × Sph ℂ, (X × unitInterval) × Sph ℂ) where
  toFun p := ((p.1, 0), p.2)
  continuous_toFun := by fun_prop

/-- `(x, z) ↦ ((x, 1), z)`. -/
def incl1 : C(X × Sph ℂ, (X × unitInterval) × Sph ℂ) where
  toFun p := ((p.1, 1), p.2)
  continuous_toFun := by fun_prop

/-- Pull-back of a matrix over `C(X, ℂ)` to `X × S¹`. -/
def pullMat {n : ℕ} (M : Matrix (Fin n) (Fin n) C(X, ℂ)) :
    Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ) :=
  M.map (fun f => f.comp (ContinuousMap.fst : C(X × Sph ℂ, X)))

@[simp] lemma pullMat_apply {n : ℕ} (M : Matrix (Fin n) (Fin n) C(X, ℂ)) (i j : Fin n)
    (p : X × Sph ℂ) : pullMat X M i j p = M i j p.1 := rfl

/-- The coordinate unit `z` of `S¹ = Sph ℂ`, as a `1 × 1` invertible matrix over
`C(X × S¹, ℂ)`. -/
def zUnitMat : (Matrix (Fin 1) (Fin 1) C(X × Sph ℂ, ℂ))ˣ :=
  Units.map (Matrix.scalar (Fin 1) : C(X × Sph ℂ, ℂ) →+*
    Matrix (Fin 1) (Fin 1) C(X × Sph ℂ, ℂ)) (zUnit X)

lemma zUnitMat_apply :
    (zUnitMat X : Matrix (Fin 1) (Fin 1) C(X × Sph ℂ, ℂ)) 0 0
      = (zUnit X : C(X × Sph ℂ, ℂ)) := by
  show (Matrix.diagonal (fun _ : Fin 1 => (↑(zUnit X) : C(X × Sph ℂ, ℂ)))) 0 0
    = (↑(zUnit X) : C(X × Sph ℂ, ℂ))
  rw [Matrix.diagonal_apply_eq]

end

end Work.KT.Fund
