import Mathlib
import Submission.Work.KT.Fund.Kappa
import Submission.Work.KT.homotopy_inv

namespace Work.KT.Fund

open Matrix

noncomputable section

variable (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]

/-! # `Work.KT.Fund.kappa_homotopic` — homotopy invariance of the clutched class

Building blocks:

* `kh_matrix_mul`, `kh_matrix_conjTranspose`, `kh_matrix_reindex`: continuity of the elementary
  matrix operations along a continuous path (rectangular products have no `Mul` instance, so these
  are proved entrywise).
* `continuous_graphProj_path`, `continuous_recipProj_path`: the graph projections of a continuous
  path of disc lifts form a continuous path of matrices.
* `pairIdem` and `pairMat_path`: a continuous path of lifts gives, via `Work.KT.homotopy_inv`, a
  constant `K₀`-class of the associated clutched idempotent.
* the main theorem: `kappa` is invariant under a homotopy of the clutching function. -/

/-! ## Continuity of the elementary matrix operations -/

lemma kh_matrix_mul {ι κ p : Type} [Fintype κ] {R : Type} [Semiring R] [TopologicalSpace R]
    [ContinuousAdd R] [ContinuousMul R] {A : unitInterval → Matrix ι κ R}
    {B : unitInterval → Matrix κ p R} (hA : Continuous A) (hB : Continuous B) :
    Continuous (fun t => A t * B t) := by
  apply continuous_matrix
  intro i j
  simp only [Matrix.mul_apply]
  exact continuous_finsetSum _ fun k _ => (hA.matrix_elem i k).mul (hB.matrix_elem k j)

lemma kh_matrix_conjTranspose {ι κ : Type} {R : Type} [Star R] [TopologicalSpace R]
    [ContinuousStar R] {A : unitInterval → Matrix ι κ R} (hA : Continuous A) :
    Continuous (fun t => (A t).conjTranspose) := by
  apply continuous_matrix
  intro i j
  exact continuous_star.comp (hA.matrix_elem j i)

lemma kh_matrix_reindex {ι ι' κ κ' : Type} (e : ι ≃ ι') (e' : κ ≃ κ')
    {R : Type} [TopologicalSpace R] {M : unitInterval → Matrix ι κ R} (hM : Continuous M) :
    Continuous (fun t => Matrix.reindex e e' (M t)) := by
  apply continuous_matrix
  intro i j
  show Continuous (fun t => M t (e.symm i) (e'.symm j))
  exact hM.matrix_elem (e.symm i) (e'.symm j)

/-! ## Continuity of the graph projections along a path -/

lemma continuous_graphB_path {n : ℕ} {Y : Type} [TopologicalSpace Y]
    (P : unitInterval → Matrix (Fin n) (Fin n) C(Y, ℂ)) (hP : Continuous P) :
    Continuous (fun t => graphB C(Y, ℂ) (P t)) := by
  apply continuous_matrix
  intro i j
  rcases i with a | a
  · by_cases h : a = j
    · simp only [graphB, h, if_true]; exact continuous_const
    · simp only [graphB, h, if_false]; exact continuous_const
  · simp only [graphB]
    exact (continuous_apply j).comp ((continuous_apply a).comp hP)

lemma continuous_recipB_path {n : ℕ} {Y : Type} [TopologicalSpace Y]
    (Q : unitInterval → Matrix (Fin n) (Fin n) C(Y, ℂ)) (hQ : Continuous Q) :
    Continuous (fun t => recipB C(Y, ℂ) (Q t)) := by
  apply continuous_matrix
  intro i j
  rcases i with a | a
  · simp only [recipB]
    exact (continuous_apply j).comp ((continuous_apply a).comp hQ)
  · by_cases h : a = j
    · simp only [recipB, h, if_true]; exact continuous_const
    · simp only [recipB, h, if_false]; exact continuous_const

lemma continuous_orthProj_path {n : ℕ}
    (B : unitInterval → Matrix (Fin n ⊕ Fin n) (Fin n) C(X × Ball ℂ, ℂ)) (hB : Continuous B)
    (hU : ∀ t, IsUnit ((B t).conjTranspose * B t)) :
    Continuous (fun t => orthProj C(X × Ball ℂ, ℂ) (B t)) := by
  have hBc := kh_matrix_conjTranspose hB
  have hgram := kh_matrix_mul hBc hB
  have hinv : Continuous (fun t => Ring.inverse ((B t).conjTranspose * B t)) := by
    rw [continuous_iff_continuousAt]
    intro t
    have hd : IsUnit (((B t).conjTranspose * B t).det) :=
      (Matrix.isUnit_iff_isUnit_det _).mp (hU t)
    have hdet : ContinuousAt Ring.inverse (((B t).conjTranspose * B t).det) := by
      have h := NormedRing.inverse_continuousAt (hd.unit)
      rwa [IsUnit.unit_spec] at h
    have hci : ContinuousAt Inv.inv ((B t).conjTranspose * B t) :=
      continuousAt_matrix_inv _ hdet
    have hcomp : ContinuousAt (fun s => Inv.inv ((B s).conjTranspose * B s)) t :=
      hci.comp (f := fun s => (B s).conjTranspose * B s) (g := Inv.inv) hgram.continuousAt
    convert hcomp using 1
    funext s
    exact (Matrix.nonsing_inv_eq_ringInverse _).symm
  have h0 := kh_matrix_mul hB hinv
  have h1 := kh_matrix_mul h0 hBc
  unfold orthProj
  exact h1

lemma continuous_graphProj_path {n : ℕ}
    (P : unitInterval → Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ)) (hP : Continuous P) :
    Continuous (fun t => graphProj C(X × Ball ℂ, ℂ) (P t)) := by
  refine continuous_orthProj_path X (fun t => graphB C(X × Ball ℂ, ℂ) (P t))
    (continuous_graphB_path P hP) ?_
  intro t
  rw [(graphB_recipB_conjTranspose_mul_self C(X × Ball ℂ, ℂ) (P t) (P t)).1]
  exact isUnit_one_add_conjTranspose_mul (P t)

lemma continuous_recipProj_path {n : ℕ}
    (Q : unitInterval → Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ)) (hQ : Continuous Q) :
    Continuous (fun t => recipProj C(X × Ball ℂ, ℂ) (Q t)) := by
  refine continuous_orthProj_path X (fun t => recipB C(X × Ball ℂ, ℂ) (Q t))
    (continuous_recipB_path Q hQ) ?_
  intro t
  rw [(graphB_recipB_conjTranspose_mul_self C(X × Ball ℂ, ℂ) (Q t) (Q t)).2]
  exact isUnit_one_add_conjTranspose_mul (Q t)

/-! ## The clutched idempotent as a function of the pair of projections -/

/-- The clutched idempotent, taken as a function of the two disc projections alone.  This is
`clutchIdem` with the unit argument dropped: `clutchIdem` only uses the unit through the *proof* of
the gluing identity, so the matrix is a function of the two projections. -/
def pairIdem {n : ℕ} (M₀ M₁ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) C(X × Ball ℂ, ℂ))
    (h : M₀.map (fun f => bdryRestrict X f) = M₁.map (fun f => bdryRestrict X f)) :
    Work.KT.Mat ↥(pullAlg2 X) :=
  ⟨n + n, Matrix.reindex finSumFinEquiv finSumFinEquiv (pairMat X M₀ M₁ h)⟩

lemma pairIdem_irrel {n : ℕ} {M₀ M₁ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) C(X × Ball ℂ, ℂ)}
    (h h' : M₀.map (fun f => bdryRestrict X f) = M₁.map (fun f => bdryRestrict X f)) :
    pairIdem X M₀ M₁ h = pairIdem X M₀ M₁ h' := by
  unfold pairIdem
  congr 1

lemma pairIdem_congr {n : ℕ} {M₀ M₀' M₁ M₁' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) C(X × Ball ℂ, ℂ)}
    (h₀ : M₀ = M₀') (h₁ : M₁ = M₁')
    (h : M₀.map (fun f => bdryRestrict X f) = M₁.map (fun f => bdryRestrict X f))
    (h' : M₀'.map (fun f => bdryRestrict X f) = M₁'.map (fun f => bdryRestrict X f)) :
    pairIdem X M₀ M₁ h = pairIdem X M₀' M₁' h' := by
  subst h₀
  subst h₁
  exact pairIdem_irrel X h h'

/-- `clutchIdem` depends on the unit only through the (irrelevant) gluing proof. -/
lemma clutchIdem_eq_pairIdem {n : ℕ} (u : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ)
    (F G : Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ))
    (hF : F.map (fun f => bdryRestrict X f) = ↑u)
    (hG : G.map (fun f => bdryRestrict X f) = ↑(u⁻¹))
    (h : (graphProj C(X × Ball ℂ, ℂ) F).map (fun f => bdryRestrict X f)
        = (recipProj C(X × Ball ℂ, ℂ) G).map (fun f => bdryRestrict X f)) :
    clutchIdem X n u F G hF hG = pairIdem X (graphProj C(X × Ball ℂ, ℂ) F)
      (recipProj C(X × Ball ℂ, ℂ) G) h := by
  unfold clutchIdem pairIdem
  congr 1

/-- The pair idempotent of the graph and reciprocal-graph projections of two lifts is idempotent,
for *any* gluing proof. -/
lemma pairIdem_isIdem {n : ℕ} (F G : Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ))
    (h : (graphProj C(X × Ball ℂ, ℂ) F).map (fun f => bdryRestrict X f)
        = (recipProj C(X × Ball ℂ, ℂ) G).map (fun f => bdryRestrict X f)) :
    (pairIdem X (graphProj C(X × Ball ℂ, ℂ) F) (recipProj C(X × Ball ℂ, ℂ) G) h).IsIdem := by
  show (Matrix.reindex finSumFinEquiv finSumFinEquiv
      (pairMat X (graphProj C(X × Ball ℂ, ℂ) F) (recipProj C(X × Ball ℂ, ℂ) G) h)) *
      (Matrix.reindex finSumFinEquiv finSumFinEquiv
      (pairMat X (graphProj C(X × Ball ℂ, ℂ) F) (recipProj C(X × Ball ℂ, ℂ) G) h)) = _
  rw [reindex_mul_self]
  congr 1
  apply mat_ext X
  · rw [Matrix.map_mul, pairMat_map_prF, graphProj_isIdem]
  · rw [Matrix.map_mul, pairMat_map_prS, recipProj_isIdem]

/-- Continuity of the pair-idempotent path. -/
lemma continuous_pairIdem_path {n : ℕ}
    (P Q : unitInterval → Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ))
    (hP : Continuous P) (hQ : Continuous Q)
    (hagr : ∀ t, (graphProj C(X × Ball ℂ, ℂ) (P t)).map (fun f => bdryRestrict X f)
        = (recipProj C(X × Ball ℂ, ℂ) (Q t)).map (fun f => bdryRestrict X f)) :
    Continuous (fun t => pairMat X (graphProj C(X × Ball ℂ, ℂ) (P t))
      (recipProj C(X × Ball ℂ, ℂ) (Q t)) (hagr t)) := by
  apply continuous_matrix
  intro i j
  apply Continuous.subtype_mk
  exact Continuous.prodMk ((continuous_graphProj_path X P hP).matrix_elem i j)
      ((continuous_recipProj_path X Q hQ).matrix_elem i j)

/-- **A continuous path of disc lifts has constant clutched class.**  If `P`, `Q` are continuous
paths of matrices over the disc whose graph/reciprocal-graph projections glue along the circle
(which holds when `P t` lifts a unit and `Q t` a lift of its inverse), then the associated clutched
idempotents have the same class in `K₀` at the two ends. -/
lemma pairIdem_path {n : ℕ}
    (P Q : unitInterval → Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ))
    (hP : Continuous P) (hQ : Continuous Q)
    (hagr : ∀ t, (graphProj C(X × Ball ℂ, ℂ) (P t)).map (fun f => bdryRestrict X f)
        = (recipProj C(X × Ball ℂ, ℂ) (Q t)).map (fun f => bdryRestrict X f)) :
    cls (pairIdem X (graphProj C(X × Ball ℂ, ℂ) (P 0)) (recipProj C(X × Ball ℂ, ℂ) (Q 0))
        (hagr 0))
      = cls (pairIdem X (graphProj C(X × Ball ℂ, ℂ) (P 1)) (recipProj C(X × Ball ℂ, ℂ) (Q 1))
        (hagr 1)) := by
  let γ : unitInterval → Matrix (Fin (n + n)) (Fin (n + n)) ↥(pullAlg2 X) :=
    fun t => Matrix.reindex finSumFinEquiv finSumFinEquiv
      (pairMat X (graphProj C(X × Ball ℂ, ℂ) (P t)) (recipProj C(X × Ball ℂ, ℂ) (Q t))
        (hagr t))
  have hγ : Continuous γ := kh_matrix_reindex _ _ (continuous_pairIdem_path X P Q hP hQ hagr)
  have hidem : ∀ t, γ t * γ t = γ t := fun t => pairIdem_isIdem X (P t) (Q t) (hagr t)
  have key := homotopy_inv (C(X × Ball ℂ, ℂ) × C(X × Ball ℂ, ℂ)) (pullAlg2 X)
    (isClosed_pullAlg2 X) (n + n) γ hγ hidem
  exact key

/-! ## The straight-line path of lifts

For two lifts `F₀`, `F₁` of the same unit over the circle, the convex combination
`t ↦ F₀ + t • (F₁ - F₀)` is a continuous path of lifts; this is the elementary step that makes the
clutched class independent of the choice of lifts. -/

lemma map_bdryRestrict_line {n : ℕ}
    (F₀ F₁ : Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ)) (t : unitInterval) :
    (F₀ + ((t : ℝ) : ℂ) • (F₁ - F₀)).map (fun f => bdryRestrict X f)
      = F₀.map (fun f => bdryRestrict X f)
        + ((t : ℝ) : ℂ) • (F₁.map (fun f => bdryRestrict X f)
          - F₀.map (fun f => bdryRestrict X f)) := by
  ext i j
  have hsm : bdryRestrict X (((t : ℝ) : ℂ) • (F₁ i j - F₀ i j))
      = ((t : ℝ) : ℂ) • bdryRestrict X (F₁ i j - F₀ i j) := by
    ext p; simp only [bdryRestrict_apply, ContinuousMap.smul_apply]
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply]
  rw [map_add, hsm, map_sub]

lemma map_bdryRestrict_line_eq {n : ℕ} {u : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ}
    {F₀ F₁ : Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ)}
    (h₀ : F₀.map (fun f => bdryRestrict X f) = ↑u)
    (h₁ : F₁.map (fun f => bdryRestrict X f) = ↑u) (t : unitInterval) :
    (F₀ + ((t : ℝ) : ℂ) • (F₁ - F₀)).map (fun f => bdryRestrict X f) = ↑u := by
  rw [map_bdryRestrict_line X F₀ F₁ t, h₀, h₁]
  simp

lemma continuous_line {n : ℕ} (F₀ F₁ : Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ)) :
    Continuous (fun t : unitInterval => F₀ + ((t : ℝ) : ℂ) • (F₁ - F₀)) := by
  apply continuous_matrix
  intro i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, ContinuousMap.add_apply,
    ContinuousMap.sub_apply, ContinuousMap.smul_apply]
  fun_prop

/-! ## The slice families -/

/-- The slice-at-time `t` family on the disc, uncurried into a single continuous map. -/
def sliceBallBig (X : Type) [TopologicalSpace X] :
    C(unitInterval × (X × Ball ℂ), (X × unitInterval) × Ball ℂ) where
  toFun q := ((q.2.1, q.1), q.2.2)
  continuous_toFun := by fun_prop

@[simp] lemma sliceBallBig_apply (X : Type) [TopologicalSpace X]
    (q : unitInterval × (X × Ball ℂ)) :
    sliceBallBig X q = ((q.2.1, q.1), q.2.2) := rfl

/-- The slice-at-time `t` family on the boundary circle, uncurried. -/
def sliceSphBig (X : Type) [TopologicalSpace X] :
    C(unitInterval × (X × Sph ℂ), (X × unitInterval) × Sph ℂ) where
  toFun q := ((q.2.1, q.1), q.2.2)
  continuous_toFun := by fun_prop

@[simp] lemma sliceSphBig_apply (X : Type) [TopologicalSpace X]
    (q : unitInterval × (X × Sph ℂ)) :
    sliceSphBig X q = ((q.2.1, q.1), q.2.2) := rfl

end

section Helpers

variable (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]

lemma pullAlg_apply' {Y Z : Type} [TopologicalSpace Y] [TopologicalSpace Z] (g : C(Y, Z))
    (f : C(Z, ℂ)) : pullAlg g f = f.comp g :=
  ContinuousMap.compStarAlgHom'_apply ℂ ℂ g f

lemma coe_units_mapMatrix {m : ℕ} {A B : Type} [Ring A] [Ring B]
    (φ : A →+* B) (u : (Matrix (Fin m) (Fin m) A)ˣ) :
    (↑(Units.map (RingHom.mapMatrix φ).toMonoidHom u) : Matrix (Fin m) (Fin m) B)
      = (u : Matrix (Fin m) (Fin m) A).map ⇑φ := by
  simp only [Units.coe_map]
  exact RingHom.mapMatrix_apply φ (u : Matrix (Fin m) (Fin m) A)

lemma coe_units_mapMatrix_inv {m : ℕ} {A B : Type} [Ring A] [Ring B]
    (φ : A →+* B) (u : (Matrix (Fin m) (Fin m) A)ˣ) :
    (↑((Units.map (RingHom.mapMatrix φ).toMonoidHom u)⁻¹) : Matrix (Fin m) (Fin m) B)
      = (↑(u⁻¹) : Matrix (Fin m) (Fin m) A).map ⇑φ := by
  simp only [Units.coe_map_inv]
  exact RingHom.mapMatrix_apply φ (↑(u⁻¹) : Matrix (Fin m) (Fin m) A)

/-- The boundary restriction commutes with taking the `t`-slice: restricting `g ∘ slice_t` to
the circle is the same as slicing `g`'s boundary value. -/
lemma bdryRestrict_slice (t : unitInterval) (g : C((X × unitInterval) × Ball ℂ, ℂ)) :
    bdryRestrict X (g.comp ((sliceBallBig X).curry t))
      = (bdryRestrict (X × unitInterval) g).comp ((sliceSphBig X).curry t) := by
  ext p
  simp only [bdryRestrict_apply, ContinuousMap.comp_apply, ContinuousMap.curry_apply,
    sliceBallBig_apply, sliceSphBig_apply]

@[simp] lemma sliceSphBig_curry_zero : (sliceSphBig X).curry 0 = incl0 X := by
  refine ContinuousMap.ext fun p => ?_
  rw [ContinuousMap.curry_apply, sliceSphBig_apply]
  rfl

@[simp] lemma sliceSphBig_curry_one : (sliceSphBig X).curry 1 = incl1 X := by
  refine ContinuousMap.ext fun p => ?_
  rw [ContinuousMap.curry_apply, sliceSphBig_apply]
  rfl

end Helpers

section Main

set_option maxHeartbeats 1000000 in
theorem kappa_homotopic (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (n : ℕ) (u v : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ)
    (H : (Matrix (Fin n) (Fin n) C((X × unitInterval) × Sph ℂ, ℂ))ˣ)
    (h₀ : ((H : Matrix (Fin n) (Fin n) C((X × unitInterval) × Sph ℂ, ℂ)).map
        (fun f => f.comp (Work.KT.Fund.incl0 X)))
      = (u : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)))
    (h₁ : ((H : Matrix (Fin n) (Fin n) C((X × unitInterval) × Sph ℂ, ℂ)).map
        (fun f => f.comp (Work.KT.Fund.incl1 X)))
      = (v : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))) :
    Work.KT.Fund.kappa X n u = Work.KT.Fund.kappa X n v := by
  rw [kappa_val X n u, kappa_val X n v]
  refine congrArg (⇑(k0Glue X).symm) ?_
  -- the two lifts used in the definition of `kappa`
  let L₀ : Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ) :=
    liftOf X (u : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))
  let M₀ : Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ) :=
    liftOf X ((u⁻¹ : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ) :
      Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))
  let L₁ : Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ) :=
    liftOf X (v : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))
  let M₁ : Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ) :=
    liftOf X ((v⁻¹ : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ) :
      Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))
  have hL₀ : L₀.map (fun f => bdryRestrict X f) = ↑u :=
    liftOf_spec X (u : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))
  have hM₀ : M₀.map (fun f => bdryRestrict X f) = ↑(u⁻¹) :=
    liftOf_spec X ((u⁻¹ : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ) :
      Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))
  have hL₁ : L₁.map (fun f => bdryRestrict X f) = ↑v :=
    liftOf_spec X (v : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))
  have hM₁ : M₁.map (fun f => bdryRestrict X f) = ↑(v⁻¹) :=
    liftOf_spec X ((v⁻¹ : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ) :
      Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))
  -- the lifts of the homotopy
  let Hm : Matrix (Fin n) (Fin n) C((X × unitInterval) × Sph ℂ, ℂ) :=
    (H : Matrix (Fin n) (Fin n) C((X × unitInterval) × Sph ℂ, ℂ))
  let Hi : Matrix (Fin n) (Fin n) C((X × unitInterval) × Sph ℂ, ℂ) :=
    ((H⁻¹ : (Matrix (Fin n) (Fin n) C((X × unitInterval) × Sph ℂ, ℂ))ˣ) :
      Matrix (Fin n) (Fin n) C((X × unitInterval) × Sph ℂ, ℂ))
  let FH : Matrix (Fin n) (Fin n) C((X × unitInterval) × Ball ℂ, ℂ) :=
    liftOf (X × unitInterval) Hm
  let GH : Matrix (Fin n) (Fin n) C((X × unitInterval) × Ball ℂ, ℂ) :=
    liftOf (X × unitInterval) Hi
  have hFH : FH.map (fun f => bdryRestrict (X × unitInterval) f) = Hm :=
    liftOf_spec (X × unitInterval) Hm
  have hGH : GH.map (fun f => bdryRestrict (X × unitInterval) f) = Hi :=
    liftOf_spec (X × unitInterval) Hi
  -- the paths of lifts obtained by slicing the homotopy
  let Ph : unitInterval → Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ) :=
    fun t => FH.map (fun g => g.comp ((sliceBallBig X).curry t))
  let Qh : unitInterval → Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ) :=
    fun t => GH.map (fun g => g.comp ((sliceBallBig X).curry t))
  let W : unitInterval → (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ :=
    fun t => Units.map
      (RingHom.mapMatrix ((pullAlg ((sliceSphBig X).curry t)).toRingHom)).toMonoidHom H
  have hPh : Continuous Ph := by
    apply continuous_matrix
    intro i j
    have heq : (fun t : unitInterval => (FH i j).comp ((sliceBallBig X).curry t))
        = ((FH i j).comp (sliceBallBig X)).curry := by
      funext t; ext p
      simp only [ContinuousMap.comp_apply, ContinuousMap.curry_apply]
    show Continuous (fun t : unitInterval => (FH i j).comp ((sliceBallBig X).curry t))
    rw [heq]
    exact (((FH i j).comp (sliceBallBig X)).curry).continuous
  have hQh : Continuous Qh := by
    apply continuous_matrix
    intro i j
    have heq : (fun t : unitInterval => (GH i j).comp ((sliceBallBig X).curry t))
        = ((GH i j).comp (sliceBallBig X)).curry := by
      funext t; ext p
      simp only [ContinuousMap.comp_apply, ContinuousMap.curry_apply]
    show Continuous (fun t : unitInterval => (GH i j).comp ((sliceBallBig X).curry t))
    rw [heq]
    exact (((GH i j).comp (sliceBallBig X)).curry).continuous
  -- the coefficient of the pulled-back unit
  have hφt : ∀ t, ⇑((pullAlg ((sliceSphBig X).curry t)).toRingHom)
      = fun f => f.comp ((sliceSphBig X).curry t) := by
    intro t; funext f; exact pullAlg_apply' ((sliceSphBig X).curry t) f
  have hWcoe : ∀ t, (↑(W t) : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))
      = Hm.map (fun f => f.comp ((sliceSphBig X).curry t)) := by
    intro t
    rw [coe_units_mapMatrix ((pullAlg ((sliceSphBig X).curry t)).toRingHom) H, hφt t]
  have hWinvcoe : ∀ t, (↑((W t)⁻¹) : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))
      = Hi.map (fun f => f.comp ((sliceSphBig X).curry t)) := by
    intro t
    rw [coe_units_mapMatrix_inv ((pullAlg ((sliceSphBig X).curry t)).toRingHom) H, hφt t]
  have hW0 : W 0 = u := by
    refine Units.ext ?_
    rw [hWcoe 0, sliceSphBig_curry_zero]
    exact h₀
  have hW1 : W 1 = v := by
    refine Units.ext ?_
    rw [hWcoe 1, sliceSphBig_curry_one]
    exact h₁
  -- the boundary values of the paths
  have hPhW : ∀ t, (Ph t).map (fun f => bdryRestrict X f) = ↑(W t) := by
    intro t
    rw [hWcoe t]
    apply Matrix.ext
    intro i j
    simp only [Matrix.map_apply]
    show bdryRestrict X ((FH i j).comp ((sliceBallBig X).curry t))
      = (Hm i j).comp ((sliceSphBig X).curry t)
    rw [bdryRestrict_slice X t (FH i j)]
    congr 1
    exact congrFun (congrFun hFH i) j
  have hQhW : ∀ t, (Qh t).map (fun f => bdryRestrict X f) = ↑((W t)⁻¹) := by
    intro t
    rw [hWinvcoe t]
    apply Matrix.ext
    intro i j
    simp only [Matrix.map_apply]
    show bdryRestrict X ((GH i j).comp ((sliceBallBig X).curry t))
      = (Hi i j).comp ((sliceSphBig X).curry t)
    rw [bdryRestrict_slice X t (GH i j)]
    congr 1
    exact congrFun (congrFun hGH i) j
  have hPh0 : (Ph 0).map (fun f => bdryRestrict X f) = ↑u := by rw [hPhW 0, hW0]
  have hQh0 : (Qh 0).map (fun f => bdryRestrict X f) = ↑(u⁻¹) := by rw [hQhW 0, hW0]
  have hPh1 : (Ph 1).map (fun f => bdryRestrict X f) = ↑v := by rw [hPhW 1, hW1]
  have hQh1 : (Qh 1).map (fun f => bdryRestrict X f) = ↑(v⁻¹) := by rw [hQhW 1, hW1]
  -- segment A: independence of the lifts of `u`
  let Pa : unitInterval → Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ) :=
    fun t => L₀ + ((t : ℝ) : ℂ) • (Ph 0 - L₀)
  let Qa : unitInterval → Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ) :=
    fun t => M₀ + ((t : ℝ) : ℂ) • (Qh 0 - M₀)
  have hPa : Continuous Pa := continuous_line X L₀ (Ph 0)
  have hQa : Continuous Qa := continuous_line X M₀ (Qh 0)
  have hPa0 : Pa 0 = L₀ := by simp [Pa]
  have hPa1 : Pa 1 = Ph 0 := by simp [Pa]
  have hQa0 : Qa 0 = M₀ := by simp [Qa]
  have hQa1 : Qa 1 = Qh 0 := by simp [Qa]
  have hagrA : ∀ t, (graphProj C(X × Ball ℂ, ℂ) (Pa t)).map (fun f => bdryRestrict X f)
      = (recipProj C(X × Ball ℂ, ℂ) (Qa t)).map (fun f => bdryRestrict X f) :=
    fun t => clutch_agree X n u (Pa t) (Qa t)
      (map_bdryRestrict_line_eq X hL₀ hPh0 t) (map_bdryRestrict_line_eq X hM₀ hQh0 t)
  have hA := pairIdem_path X Pa Qa hPa hQa hagrA
  have cA0 : pairIdem X (graphProj C(X × Ball ℂ, ℂ) L₀) (recipProj C(X × Ball ℂ, ℂ) M₀)
        (clutch_agree X n u L₀ M₀ hL₀ hM₀)
      = pairIdem X (graphProj C(X × Ball ℂ, ℂ) (Pa 0)) (recipProj C(X × Ball ℂ, ℂ) (Qa 0))
        (hagrA 0) :=
    pairIdem_congr X (by rw [hPa0]) (by rw [hQa0]) _ _
  have cA1 : pairIdem X (graphProj C(X × Ball ℂ, ℂ) (Pa 1)) (recipProj C(X × Ball ℂ, ℂ) (Qa 1))
        (hagrA 1)
      = pairIdem X (graphProj C(X × Ball ℂ, ℂ) (Ph 0)) (recipProj C(X × Ball ℂ, ℂ) (Qh 0))
        (clutch_agree X n u (Ph 0) (Qh 0) hPh0 hQh0) :=
    pairIdem_congr X (by rw [hPa1]) (by rw [hQa1]) _ _
  have e1 : cls (clutchIdem X n u L₀ M₀ hL₀ hM₀)
      = cls (clutchIdem X n u (Ph 0) (Qh 0) hPh0 hQh0) := by
    rw [clutchIdem_eq_pairIdem X u L₀ M₀ hL₀ hM₀ (clutch_agree X n u L₀ M₀ hL₀ hM₀),
      clutchIdem_eq_pairIdem X u (Ph 0) (Qh 0) hPh0 hQh0
        (clutch_agree X n u (Ph 0) (Qh 0) hPh0 hQh0)]
    exact (congrArg cls cA0).trans (hA.trans (congrArg cls cA1))
  -- segment B: the homotopy in the unit
  have hagrB : ∀ t, (graphProj C(X × Ball ℂ, ℂ) (Ph t)).map (fun f => bdryRestrict X f)
      = (recipProj C(X × Ball ℂ, ℂ) (Qh t)).map (fun f => bdryRestrict X f) :=
    fun t => clutch_agree X n (W t) (Ph t) (Qh t) (hPhW t) (hQhW t)
  have hB := pairIdem_path X Ph Qh hPh hQh hagrB
  have cB0 : pairIdem X (graphProj C(X × Ball ℂ, ℂ) (Ph 0)) (recipProj C(X × Ball ℂ, ℂ) (Qh 0))
        (hagrB 0)
      = pairIdem X (graphProj C(X × Ball ℂ, ℂ) (Ph 0)) (recipProj C(X × Ball ℂ, ℂ) (Qh 0))
        (clutch_agree X n u (Ph 0) (Qh 0) hPh0 hQh0) :=
    pairIdem_irrel X _ _
  have cB1 : pairIdem X (graphProj C(X × Ball ℂ, ℂ) (Ph 1)) (recipProj C(X × Ball ℂ, ℂ) (Qh 1))
        (hagrB 1)
      = pairIdem X (graphProj C(X × Ball ℂ, ℂ) (Ph 1)) (recipProj C(X × Ball ℂ, ℂ) (Qh 1))
        (clutch_agree X n v (Ph 1) (Qh 1) hPh1 hQh1) :=
    pairIdem_irrel X _ _
  have e2 : cls (clutchIdem X n u (Ph 0) (Qh 0) hPh0 hQh0)
      = cls (clutchIdem X n v (Ph 1) (Qh 1) hPh1 hQh1) := by
    rw [clutchIdem_eq_pairIdem X u (Ph 0) (Qh 0) hPh0 hQh0
          (clutch_agree X n u (Ph 0) (Qh 0) hPh0 hQh0),
      clutchIdem_eq_pairIdem X v (Ph 1) (Qh 1) hPh1 hQh1
        (clutch_agree X n v (Ph 1) (Qh 1) hPh1 hQh1)]
    exact (congrArg cls cB0).trans (hB.trans (congrArg cls cB1))
  -- segment C: independence of the lifts of `v`
  let Pc : unitInterval → Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ) :=
    fun t => Ph 1 + ((t : ℝ) : ℂ) • (L₁ - Ph 1)
  let Qc : unitInterval → Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ) :=
    fun t => Qh 1 + ((t : ℝ) : ℂ) • (M₁ - Qh 1)
  have hPc : Continuous Pc := continuous_line X (Ph 1) L₁
  have hQc : Continuous Qc := continuous_line X (Qh 1) M₁
  have hPc0 : Pc 0 = Ph 1 := by simp [Pc]
  have hPc1 : Pc 1 = L₁ := by simp [Pc]
  have hQc0 : Qc 0 = Qh 1 := by simp [Qc]
  have hQc1 : Qc 1 = M₁ := by simp [Qc]
  have hagrC : ∀ t, (graphProj C(X × Ball ℂ, ℂ) (Pc t)).map (fun f => bdryRestrict X f)
      = (recipProj C(X × Ball ℂ, ℂ) (Qc t)).map (fun f => bdryRestrict X f) :=
    fun t => clutch_agree X n v (Pc t) (Qc t)
      (map_bdryRestrict_line_eq X hPh1 hL₁ t) (map_bdryRestrict_line_eq X hQh1 hM₁ t)
  have hC := pairIdem_path X Pc Qc hPc hQc hagrC
  have cC0 : pairIdem X (graphProj C(X × Ball ℂ, ℂ) (Ph 1)) (recipProj C(X × Ball ℂ, ℂ) (Qh 1))
        (clutch_agree X n v (Ph 1) (Qh 1) hPh1 hQh1)
      = pairIdem X (graphProj C(X × Ball ℂ, ℂ) (Pc 0)) (recipProj C(X × Ball ℂ, ℂ) (Qc 0))
        (hagrC 0) :=
    pairIdem_congr X (by rw [hPc0]) (by rw [hQc0]) _ _
  have cC1 : pairIdem X (graphProj C(X × Ball ℂ, ℂ) (Pc 1)) (recipProj C(X × Ball ℂ, ℂ) (Qc 1))
        (hagrC 1)
      = pairIdem X (graphProj C(X × Ball ℂ, ℂ) L₁) (recipProj C(X × Ball ℂ, ℂ) M₁)
        (clutch_agree X n v L₁ M₁ hL₁ hM₁) :=
    pairIdem_congr X (by rw [hPc1]) (by rw [hQc1]) _ _
  have e3 : cls (clutchIdem X n v (Ph 1) (Qh 1) hPh1 hQh1)
      = cls (clutchIdem X n v L₁ M₁ hL₁ hM₁) := by
    rw [clutchIdem_eq_pairIdem X v (Ph 1) (Qh 1) hPh1 hQh1
          (clutch_agree X n v (Ph 1) (Qh 1) hPh1 hQh1),
      clutchIdem_eq_pairIdem X v L₁ M₁ hL₁ hM₁ (clutch_agree X n v L₁ M₁ hL₁ hM₁)]
    exact (congrArg cls cC0).trans (hC.trans (congrArg cls cC1))
  exact e1.trans (e2.trans e3)



end Main

end Work.KT.Fund
