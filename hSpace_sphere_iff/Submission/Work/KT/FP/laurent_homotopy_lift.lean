import Mathlib
import Submission.Work.KT.FP.PencilDefs
import Submission.Work.KT.Bott.laurent_approx
import Submission.Work.KT.Bott.seg_unit
import Submission.Work.KT.Bott.LauDefs

/-!
# `Work.KT.FP.laurent_homotopy_lift`

Given a homotopy of invertible matrices over `X × S¹` whose two ends are the images under
`Work.KT.laurentMap` of Laurent polynomial matrices `P₀`, `P₁` over `C(X, ℂ)`, this file produces a
Laurent polynomial matrix `Q` over `C(X × [0,1], ℂ)` whose image under `laurentMap (X × [0,1])` is
invertible and whose two ends are again `P₀` and `P₁`.

The proof is "Laurent approximation plus endpoint correction": approximate the homotopy `H` on
`X × [0,1]` by `Qt = P.map (laurentMap (X × [0,1]))`, then subtract the two endpoint errors,
weighted by `1 - t` and `t`.  The corrected matrix is again a Laurent polynomial matrix, its two
ends are exactly `P₀`, `P₁`, and it is invertible because it is a small perturbation of `H`.

The supporting notion is `laurentCoeff`, the coefficient-wise extension of a ring homomorphism of
coefficient rings to Laurent polynomials, together with its compatibility with `Work.KT.laurentMap`
(`laurentMap_natural`).
-/

namespace Work.KT.FP

open Matrix

noncomputable section

/-! ## The coefficient-wise map of Laurent polynomials -/

/-- The coefficient-wise extension of a ring homomorphism `φ : R →+* S` of coefficient rings to a
ring homomorphism `R[T;T⁻¹] →+* S[T;T⁻¹]`, `∑_k a_k T^k ↦ ∑_k φ(a_k) T^k`. -/
def laurentCoeff {R S : Type*} [Semiring R] [Semiring S] (φ : R →+* S) :
    LaurentPolynomial R →+* LaurentPolynomial S :=
  AddMonoidAlgebra.mapRingHom ℤ φ

@[simp] lemma laurentCoeff_apply_coeff {R S : Type*} [Semiring R] [Semiring S]
    (φ : R →+* S) (p : LaurentPolynomial R) (k : ℤ) :
    (laurentCoeff φ p).coeff k = φ (p.coeff k) :=
  AddMonoidAlgebra.coeff_mapRingHom φ p k

lemma laurentCoeff_C {R S : Type*} [Semiring R] [Semiring S] (φ : R →+* S) (r : R) :
    laurentCoeff φ (LaurentPolynomial.C r) = LaurentPolynomial.C (φ r) := by
  show (AddMonoidAlgebra.mapRingHom ℤ φ) (AddMonoidAlgebra.single 0 r) = _
  rw [AddMonoidAlgebra.mapRingHom_single]
  simp

lemma laurentCoeff_T {R S : Type*} [Semiring R] [Semiring S] (φ : R →+* S) (k : ℤ) :
    laurentCoeff φ (LaurentPolynomial.T k) = LaurentPolynomial.T k := by
  show (AddMonoidAlgebra.mapRingHom ℤ φ) (AddMonoidAlgebra.single k 1) = _
  rw [AddMonoidAlgebra.mapRingHom_single]
  simp

@[simp] lemma laurentCoeff_id {R : Type*} [Semiring R] :
    laurentCoeff (RingHom.id R) = RingHom.id (LaurentPolynomial R) :=
  AddMonoidAlgebra.mapRingHom_id

@[simp] lemma laurentCoeff_comp {R S T : Type*} [Semiring R] [Semiring S] [Semiring T]
    (φ : S →+* T) (ψ : R →+* S) :
    laurentCoeff (φ.comp ψ) = (laurentCoeff φ).comp (laurentCoeff ψ) :=
  AddMonoidAlgebra.mapRingHom_comp φ ψ

/-! ## Naturality of `laurentMap` -/

/-- The product map `X' × S¹ → X × S¹` induced by `g : X' → X`. -/
def mapSphProd {X X' : Type} [TopologicalSpace X] [TopologicalSpace X'] (g : C(X', X)) :
    C(X' × Sph ℂ, X × Sph ℂ) :=
  ⟨fun p => (g p.1, p.2), by fun_prop⟩

@[simp] lemma mapSphProd_apply {X X' : Type} [TopologicalSpace X] [TopologicalSpace X']
    (g : C(X', X)) (p : X' × Sph ℂ) : mapSphProd g p = (g p.1, p.2) := rfl

/-- Pulling back along `pullAlg` is contravariantly functorial. -/
lemma pullAlg_comp_apply {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] (h : C(Y, X)) (k : C(Z, Y)) (a : C(X, ℂ)) :
    (pullAlg k) ((pullAlg h) a) = (pullAlg (h.comp k)) a := by
  ext z; rfl

/-- **Naturality of `laurentMap`**: pulling back a Laurent polynomial function along the map
`X' × S¹ → X × S¹` induced by `g : X' → X` is the same as mapping the coefficients along the
pullback of functions. -/
theorem laurentMap_natural {X X' : Type} [TopologicalSpace X] [TopologicalSpace X']
    (g : C(X', X)) (p : LaurentPolynomial C(X, ℂ)) :
    (laurentMap X p).comp (mapSphProd g)
      = laurentMap X' (laurentCoeff (pullAlg g).toRingHom p) := by
  suffices h : (pullAlg (mapSphProd g)).toRingHom.comp (laurentMap X)
      = (laurentMap X').comp (laurentCoeff (pullAlg g).toRingHom) by
    have hp := RingHom.congr_fun h p
    rw [RingHom.comp_apply, RingHom.comp_apply] at hp
    simpa [pullAlg, ContinuousMap.compStarAlgHom'_apply] using hp
  refine AddMonoidAlgebra.ringHom_ext (M := ℤ) ?_ ?_
  · intro r
    simp only [RingHom.comp_apply]
    change (pullAlg (mapSphProd g)) ((laurentMap X) (LaurentPolynomial.C r))
      = (laurentMap X') ((laurentCoeff (pullAlg g).toRingHom) (LaurentPolynomial.C r))
    rw [laurentCoeff_C, laurentMap_C, laurentMap_C]
    change (pullAlg (mapSphProd g)) ((pullAlg (ContinuousMap.fst)) r)
      = (pullAlg (ContinuousMap.fst)) ((pullAlg g) r)
    rw [pullAlg_comp_apply (ContinuousMap.fst) (mapSphProd g) r,
        pullAlg_comp_apply g (ContinuousMap.fst) r]
    rw [show (ContinuousMap.fst.comp (mapSphProd g)) = (g.comp ContinuousMap.fst) from by
      ext x; rfl]
  · intro k
    simp only [RingHom.comp_apply]
    change (pullAlg (mapSphProd g)) ((laurentMap X) (LaurentPolynomial.T k))
      = (laurentMap X') ((laurentCoeff (pullAlg g).toRingHom) (LaurentPolynomial.T k))
    rw [laurentCoeff_T, laurentMap_T, laurentMap_T]
    have hz : Units.map ((pullAlg (mapSphProd g)).toRingHom.toMonoidHom) (zUnit X) = zUnit X' := by
      ext p; rfl
    calc (pullAlg (mapSphProd g)) ((zUnit X ^ k).val)
        = ((Units.map ((pullAlg (mapSphProd g)).toRingHom.toMonoidHom) (zUnit X ^ k))).val :=
          (Units.coe_map _ _).symm
      _ = (((Units.map ((pullAlg (mapSphProd g)).toRingHom.toMonoidHom) (zUnit X)) ^ k)).val := by
          rw [map_zpow]
      _ = ((zUnit X' ^ k)).val := by rw [hz]

@[simp] lemma laurentMap_natural_apply {X X' : Type} [TopologicalSpace X] [TopologicalSpace X']
    (g : C(X', X)) (p : LaurentPolynomial C(X, ℂ)) (x' : X') (z : Sph ℂ) :
    laurentMap X' (laurentCoeff (pullAlg g).toRingHom p) (x', z) = laurentMap X p (g x', z) := by
  rw [← laurentMap_natural g p]
  rfl

/-! ## The slice maps and their compatibility with `laurentMap` -/

/-- The first projection `X × [0,1] → X`. -/
def fstProd (X : Type) [TopologicalSpace X] : C(X × unitInterval, X) := ContinuousMap.fst

/-- The inclusion of the `t = 0` slice. -/
def slice0 (X : Type) [TopologicalSpace X] : C(X, X × unitInterval) :=
  ⟨fun x => (x, 0), by fun_prop⟩

/-- The inclusion of the `t = 1` slice. -/
def slice1 (X : Type) [TopologicalSpace X] : C(X, X × unitInterval) :=
  ⟨fun x => (x, 1), by fun_prop⟩

@[simp] lemma slice0_apply (X : Type) [TopologicalSpace X] (x : X) : slice0 X x = (x, 0) := rfl
@[simp] lemma slice1_apply (X : Type) [TopologicalSpace X] (x : X) : slice1 X x = (x, 1) := rfl
@[simp] lemma fstProd_apply (X : Type) [TopologicalSpace X] (p : X × unitInterval) :
    fstProd X p = p.1 := rfl

/-- Evaluating the coefficient map along `fstProd` on the slice `t = 0`. -/
@[simp] lemma laurentMap_fstProd_apply {X : Type} [TopologicalSpace X]
    (p : LaurentPolynomial C(X, ℂ)) (x : X) (t : unitInterval) (z : Sph ℂ) :
    laurentMap (X × unitInterval)
        (laurentCoeff (pullAlg (fstProd X)).toRingHom p) ((x, t), z)
      = laurentMap X p (x, z) := by
  rw [laurentMap_natural_apply (fstProd X) p (x, t) z]
  rfl

/-- Evaluating the coefficient map along the `t = 0` slice. -/
@[simp] lemma laurentMap_slice0_apply {X : Type} [TopologicalSpace X]
    (q : LaurentPolynomial C(X × unitInterval, ℂ)) (x : X) (z : Sph ℂ) :
    laurentMap X (laurentCoeff (pullAlg (slice0 X)).toRingHom q) (x, z)
      = laurentMap (X × unitInterval) q ((x, 0), z) := by
  rw [laurentMap_natural_apply (slice0 X) q x z]
  rfl

/-- Evaluating the coefficient map along the `t = 1` slice. -/
@[simp] lemma laurentMap_slice1_apply {X : Type} [TopologicalSpace X]
    (q : LaurentPolynomial C(X × unitInterval, ℂ)) (x : X) (z : Sph ℂ) :
    laurentMap X (laurentCoeff (pullAlg (slice1 X)).toRingHom q) (x, z)
      = laurentMap (X × unitInterval) q ((x, 1), z) := by
  rw [laurentMap_natural_apply (slice1 X) q x z]
  rfl

/-! ## Norm bookkeeping for `Work.KT.Bott.LauDefs.mNorm` -/

lemma mNorm_add_le {R : Type*} [NormedRing R] (n : ℕ) (A B : Matrix (Fin n) (Fin n) R) :
    Work.KT.Bott.LauDefs.mNorm n (A + B) ≤ Work.KT.Bott.LauDefs.mNorm n A + Work.KT.Bott.LauDefs.mNorm n B := by
  letI : NormedRing (Matrix (Fin n) (Fin n) R) := Matrix.linftyOpNormedRing
  have hA : ‖A‖₊ = Work.KT.Bott.LauDefs.mNorm n A := Matrix.linfty_opNNNorm_def A
  have hB : ‖B‖₊ = Work.KT.Bott.LauDefs.mNorm n B := Matrix.linfty_opNNNorm_def B
  have hAB : ‖A + B‖₊ = Work.KT.Bott.LauDefs.mNorm n (A + B) := Matrix.linfty_opNNNorm_def (A + B)
  rw [← hAB, ← hA, ← hB]
  exact nnnorm_add_le A B

lemma mNorm_le_of_entry_le {R : Type*} [NormedRing R] (n : ℕ)
    {X Y Z : Matrix (Fin n) (Fin n) R}
    (h : ∀ i j, ‖X i j‖ ≤ ‖Y i j‖ + ‖Z i j‖) :
    Work.KT.Bott.LauDefs.mNorm n X ≤ Work.KT.Bott.LauDefs.mNorm n Y + Work.KT.Bott.LauDefs.mNorm n Z := by
  unfold Work.KT.Bott.LauDefs.mNorm
  refine Finset.sup_le fun i _ => ?_
  calc ∑ j, ‖X i j‖₊ ≤ ∑ j, (‖Y i j‖₊ + ‖Z i j‖₊) :=
        Finset.sum_le_sum fun j _ => by
          rw [← NNReal.coe_le_coe]; push_cast; exact h i j
    _ = ∑ j, ‖Y i j‖₊ + ∑ j, ‖Z i j‖₊ := Finset.sum_add_distrib
    _ ≤ Finset.univ.sup (fun i => ∑ j, ‖Y i j‖₊) + Finset.univ.sup (fun i => ∑ j, ‖Z i j‖₊) :=
        add_le_add (Finset.le_sup (f := fun i => ∑ j, ‖Y i j‖₊) (Finset.mem_univ i))
          (Finset.le_sup (f := fun i => ∑ j, ‖Z i j‖₊) (Finset.mem_univ i))

lemma mNorm_pullback_le {Y Y' : Type} [TopologicalSpace Y] [TopologicalSpace Y']
    [CompactSpace Y] [CompactSpace Y']
    (h : C(Y', Y)) (n : ℕ) (A : Matrix (Fin n) (Fin n) C(Y, ℂ)) :
    Work.KT.Bott.LauDefs.mNorm n (A.map (pullAlg h).toRingHom) ≤ Work.KT.Bott.LauDefs.mNorm n A := by
  refine Work.KT.Bott.LauDefs.mNorm_map_le n (pullAlg h).toRingHom ?_ A
  intro a
  refine (ContinuousMap.norm_le ((pullAlg h) a) (norm_nonneg a)).mpr fun y' => ?_
  simpa [pullAlg, ContinuousMap.compStarAlgHom'_apply] using ContinuousMap.norm_coe_le_norm a (h y')

/-- Evaluating a pullback at a point. -/
lemma pullAlg_apply_apply {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (g : C(X, Y)) (a : C(Y, ℂ)) (x : X) : (pullAlg g) a x = a (g x) := rfl

/-- Evaluating the `toRingHom` of a pullback at a point. -/
lemma pullAlg_toRingHom_apply {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (g : C(X, Y)) (a : C(Y, ℂ)) (x : X) : (pullAlg g).toRingHom a x = a (g x) := rfl

lemma norm_laurentMap_tC_le_one {X : Type} [TopologicalSpace X] [CompactSpace X] :
    ‖laurentMap (X × unitInterval) (LaurentPolynomial.C (Work.KT.Bott.LauDefs.tC X))‖ ≤ 1 := by
  refine (ContinuousMap.norm_le (laurentMap (X × unitInterval)
    (LaurentPolynomial.C (Work.KT.Bott.LauDefs.tC X))) zero_le_one).mpr fun p => ?_
  rw [laurentMap_C, pullAlg_apply_apply, Work.KT.Bott.LauDefs.tC_apply]
  have h : ‖(((ContinuousMap.fst p).2 : ℝ) : ℂ)‖ = |((ContinuousMap.fst p).2 : ℝ)| :=
    RCLike.norm_ofReal _
  rw [h, abs_of_nonneg (ContinuousMap.fst p).2.2.1]
  exact (ContinuousMap.fst p).2.2.2

lemma norm_laurentMap_one_sub_tC_le_one {X : Type} [TopologicalSpace X] [CompactSpace X] :
    ‖laurentMap (X × unitInterval) (LaurentPolynomial.C (1 - Work.KT.Bott.LauDefs.tC X))‖ ≤ 1 := by
  refine (ContinuousMap.norm_le (laurentMap (X × unitInterval)
    (LaurentPolynomial.C (1 - Work.KT.Bott.LauDefs.tC X))) zero_le_one).mpr fun p => ?_
  rw [laurentMap_C, pullAlg_apply_apply]
  simp only [ContinuousMap.sub_apply, ContinuousMap.one_apply, Work.KT.Bott.LauDefs.tC_apply]
  have hcast : (1 : ℂ) - (((ContinuousMap.fst p).2 : ℝ) : ℂ)
      = (((1 - ((ContinuousMap.fst p).2 : ℝ)) : ℝ) : ℂ) := by
    rw [Complex.ofReal_sub, Complex.ofReal_one]
  rw [hcast]
  have h : ‖(((1 - ((ContinuousMap.fst p).2 : ℝ)) : ℝ) : ℂ)‖
      = |(1 - ((ContinuousMap.fst p).2 : ℝ))| := RCLike.norm_ofReal _
  rw [h, abs_of_nonneg (by linarith [(ContinuousMap.fst p).2.2.2])]
  linarith [(ContinuousMap.fst p).2.2.1]

@[simp] lemma laurentMap_C_tC_apply_zero {X : Type} [TopologicalSpace X] (x : X) (z : Sph ℂ) :
    laurentMap (X × unitInterval) (LaurentPolynomial.C (Work.KT.Bott.LauDefs.tC X)) ((x, 0), z)
      = 0 := by
  rw [laurentMap_C, pullAlg_apply_apply, Work.KT.Bott.LauDefs.tC_apply]
  norm_num

@[simp] lemma laurentMap_C_tC_apply_one {X : Type} [TopologicalSpace X] (x : X) (z : Sph ℂ) :
    laurentMap (X × unitInterval) (LaurentPolynomial.C (Work.KT.Bott.LauDefs.tC X)) ((x, 1), z)
      = 1 := by
  rw [laurentMap_C, pullAlg_apply_apply, Work.KT.Bott.LauDefs.tC_apply]
  norm_num

@[simp] lemma laurentMap_C_one_sub_tC_apply_zero {X : Type} [TopologicalSpace X] (x : X)
    (z : Sph ℂ) :
    laurentMap (X × unitInterval) (LaurentPolynomial.C (1 - Work.KT.Bott.LauDefs.tC X))
      ((x, 0), z) = 1 := by
  rw [laurentMap_C, pullAlg_apply_apply]
  simp only [ContinuousMap.sub_apply, ContinuousMap.one_apply, Work.KT.Bott.LauDefs.tC_apply]
  norm_num

@[simp] lemma laurentMap_C_one_sub_tC_apply_one {X : Type} [TopologicalSpace X] (x : X)
    (z : Sph ℂ) :
    laurentMap (X × unitInterval) (LaurentPolynomial.C (1 - Work.KT.Bott.LauDefs.tC X))
      ((x, 1), z) = 0 := by
  rw [laurentMap_C, pullAlg_apply_apply]
  simp only [ContinuousMap.sub_apply, ContinuousMap.one_apply, Work.KT.Bott.LauDefs.tC_apply]
  norm_num


/-- **Laurent polynomial lift of a homotopy of clutching functions.** -/
theorem laurent_homotopy_lift (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (n : ℕ)
    (H : (Matrix (Fin n) (Fin n) C((X × unitInterval) × Sph ℂ, ℂ))ˣ)
    (P₀ P₁ : Matrix (Fin n) (Fin n) (LaurentPolynomial C(X, ℂ)))
    (h₀ : ∀ (i j : Fin n) (x : X) (z : Sph ℂ),
      (H : Matrix (Fin n) (Fin n) C((X × unitInterval) × Sph ℂ, ℂ)) i j ((x, 0), z)
        = (P₀.map (Work.KT.laurentMap X)) i j (x, z))
    (h₁ : ∀ (i j : Fin n) (x : X) (z : Sph ℂ),
      (H : Matrix (Fin n) (Fin n) C((X × unitInterval) × Sph ℂ, ℂ)) i j ((x, 1), z)
        = (P₁.map (Work.KT.laurentMap X)) i j (x, z)) :
    ∃ Q : Matrix (Fin n) (Fin n) (LaurentPolynomial C(X × unitInterval, ℂ)),
      IsUnit (Q.map (Work.KT.laurentMap (X × unitInterval))) ∧
      (∀ (i j : Fin n) (x : X) (z : Sph ℂ),
        (Q.map (Work.KT.laurentMap (X × unitInterval))) i j ((x, 0), z)
          = (P₀.map (Work.KT.laurentMap X)) i j (x, z)) ∧
      (∀ (i j : Fin n) (x : X) (z : Sph ℂ),
        (Q.map (Work.KT.laurentMap (X × unitInterval))) i j ((x, 1), z)
          = (P₁.map (Work.KT.laurentMap X)) i j (x, z)) := by
  obtain ⟨A, hA1, hA2⟩ : ∃ A : Matrix (Fin n) (Fin n) C((X × unitInterval) × Sph ℂ, ℂ),
      (H : Matrix (Fin n) (Fin n) C((X × unitInterval) × Sph ℂ, ℂ)) * A = 1 ∧
      A * (H : Matrix (Fin n) (Fin n) C((X × unitInterval) × Sph ℂ, ℂ)) = 1 :=
    ⟨↑(H⁻¹), H.mul_inv, H.inv_mul⟩
  let δ : NNReal := (3 * (Work.KT.Bott.LauDefs.mNorm n A + 1))⁻¹
  have hδ : δ = (3 * (Work.KT.Bott.LauDefs.mNorm n A + 1))⁻¹ := rfl
  have hδpos : 0 < δ := by rw [hδ]; exact inv_pos.mpr (by positivity)
  obtain ⟨Qt, hQt⟩ := Work.KT.Bott.mat_approx (X × unitInterval) n
    (H : Matrix (Fin n) (Fin n) C((X × unitInterval) × Sph ℂ, ℂ)) δ hδpos
  let A0 : Matrix (Fin n) (Fin n) (LaurentPolynomial C(X, ℂ)) :=
    Qt.map (laurentCoeff (pullAlg (slice0 X)).toRingHom) - P₀
  let A1 : Matrix (Fin n) (Fin n) (LaurentPolynomial C(X, ℂ)) :=
    Qt.map (laurentCoeff (pullAlg (slice1 X)).toRingHom) - P₁
  let B0 : Matrix (Fin n) (Fin n) (LaurentPolynomial C(X × unitInterval, ℂ)) :=
    A0.map (laurentCoeff (pullAlg (fstProd X)).toRingHom)
  let B1 : Matrix (Fin n) (Fin n) (LaurentPolynomial C(X × unitInterval, ℂ)) :=
    A1.map (laurentCoeff (pullAlg (fstProd X)).toRingHom)
  let Q : Matrix (Fin n) (Fin n) (LaurentPolynomial C(X × unitInterval, ℂ)) :=
    fun i j => Qt i j - LaurentPolynomial.C (1 - Work.KT.Bott.LauDefs.tC X) * B0 i j
      - LaurentPolynomial.C (Work.KT.Bott.LauDefs.tC X) * B1 i j
  refine ⟨Q, ?_, ?_, ?_⟩
  · -- invertibility
    refine Work.KT.Bott.isUnit_of_mNorm_sub_mul_lt_one
      (V := Q.map (laurentMap (X × unitInterval))) hA1 hA2 ?_
    have hδ3 : 3 * δ * Work.KT.Bott.LauDefs.mNorm n A < 1 := by
      have h3 : (3 : NNReal) * 3⁻¹ = 1 := mul_inv_cancel₀ (by norm_num)
      rw [hδ, mul_inv]
      rw [show (3 : NNReal) * (3⁻¹ * (Work.KT.Bott.LauDefs.mNorm n A + 1)⁻¹)
            * Work.KT.Bott.LauDefs.mNorm n A
          = (3 * 3⁻¹) * ((Work.KT.Bott.LauDefs.mNorm n A + 1)⁻¹ * Work.KT.Bott.LauDefs.mNorm n A)
            from by ring,
          h3, one_mul]
      exact Work.KT.Bott.inv_add_one_mul_lt_one _
    have hA0map : A0.map (laurentMap X)
        = ((Qt.map (laurentMap (X × unitInterval)))
            - (H : Matrix (Fin n) (Fin n) C((X × unitInterval) × Sph ℂ, ℂ))).map
            (pullAlg (mapSphProd (slice0 X))).toRingHom := by
      refine Matrix.ext fun i j => ?_
      refine ContinuousMap.ext fun p => ?_
      obtain ⟨x, z⟩ := p
      simp only [Matrix.map_apply, Matrix.sub_apply, A0, map_sub, laurentMap_slice0_apply,
        ContinuousMap.comp_apply, ContinuousMap.sub_apply, pullAlg_apply_apply,
        pullAlg_toRingHom_apply, mapSphProd_apply, slice0_apply]
      rw [h₀ i j x z, Matrix.map_apply]
    have hA1map : A1.map (laurentMap X)
        = ((Qt.map (laurentMap (X × unitInterval)))
            - (H : Matrix (Fin n) (Fin n) C((X × unitInterval) × Sph ℂ, ℂ))).map
            (pullAlg (mapSphProd (slice1 X))).toRingHom := by
      refine Matrix.ext fun i j => ?_
      refine ContinuousMap.ext fun p => ?_
      obtain ⟨x, z⟩ := p
      simp only [Matrix.map_apply, Matrix.sub_apply, A1, map_sub, laurentMap_slice1_apply,
        ContinuousMap.comp_apply, ContinuousMap.sub_apply, pullAlg_apply_apply,
        pullAlg_toRingHom_apply, mapSphProd_apply, slice1_apply]
      rw [h₁ i j x z, Matrix.map_apply]
    have hB0map : B0.map (laurentMap (X × unitInterval))
        = (A0.map (laurentMap X)).map (pullAlg (mapSphProd (fstProd X))).toRingHom := by
      refine Matrix.ext fun i j => ?_
      show laurentMap (X × unitInterval) (laurentCoeff (pullAlg (fstProd X)).toRingHom (A0 i j))
        = (pullAlg (mapSphProd (fstProd X))) (laurentMap X (A0 i j))
      exact (laurentMap_natural (fstProd X) (A0 i j)).symm
    have hB1map : B1.map (laurentMap (X × unitInterval))
        = (A1.map (laurentMap X)).map (pullAlg (mapSphProd (fstProd X))).toRingHom := by
      refine Matrix.ext fun i j => ?_
      show laurentMap (X × unitInterval) (laurentCoeff (pullAlg (fstProd X)).toRingHom (A1 i j))
        = (pullAlg (mapSphProd (fstProd X))) (laurentMap X (A1 i j))
      exact (laurentMap_natural (fstProd X) (A1 i j)).symm
    have hentry : ∀ i j, ‖(Qt.map (laurentMap (X × unitInterval))
          - Q.map (laurentMap (X × unitInterval))) i j‖
        ≤ ‖(B0.map (laurentMap (X × unitInterval))) i j‖
          + ‖(B1.map (laurentMap (X × unitInterval))) i j‖ := by
      intro i j
      have hrewrite : (Qt.map (laurentMap (X × unitInterval))
            - Q.map (laurentMap (X × unitInterval))) i j
          = laurentMap (X × unitInterval) (LaurentPolynomial.C (1 - Work.KT.Bott.LauDefs.tC X))
              * (B0.map (laurentMap (X × unitInterval))) i j
            + laurentMap (X × unitInterval) (LaurentPolynomial.C (Work.KT.Bott.LauDefs.tC X))
              * (B1.map (laurentMap (X × unitInterval))) i j := by
        simp only [Matrix.sub_apply, Matrix.map_apply]
        rw [show Q i j = Qt i j - LaurentPolynomial.C (1 - Work.KT.Bott.LauDefs.tC X) * B0 i j
              - LaurentPolynomial.C (Work.KT.Bott.LauDefs.tC X) * B1 i j from rfl,
          map_sub, map_sub, map_mul, map_mul]
        ring
      rw [hrewrite]
      calc ‖laurentMap (X × unitInterval) (LaurentPolynomial.C (1 - Work.KT.Bott.LauDefs.tC X))
              * (B0.map (laurentMap (X × unitInterval))) i j
            + laurentMap (X × unitInterval) (LaurentPolynomial.C (Work.KT.Bott.LauDefs.tC X))
              * (B1.map (laurentMap (X × unitInterval))) i j‖
          ≤ ‖laurentMap (X × unitInterval) (LaurentPolynomial.C (1 - Work.KT.Bott.LauDefs.tC X))
              * (B0.map (laurentMap (X × unitInterval))) i j‖
            + ‖laurentMap (X × unitInterval) (LaurentPolynomial.C (Work.KT.Bott.LauDefs.tC X))
              * (B1.map (laurentMap (X × unitInterval))) i j‖ := norm_add_le _ _
        _ ≤ ‖laurentMap (X × unitInterval) (LaurentPolynomial.C (1 - Work.KT.Bott.LauDefs.tC X))‖
              * ‖(B0.map (laurentMap (X × unitInterval))) i j‖
            + ‖laurentMap (X × unitInterval) (LaurentPolynomial.C (Work.KT.Bott.LauDefs.tC X))‖
              * ‖(B1.map (laurentMap (X × unitInterval))) i j‖ :=
            add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
        _ ≤ 1 * ‖(B0.map (laurentMap (X × unitInterval))) i j‖
            + 1 * ‖(B1.map (laurentMap (X × unitInterval))) i j‖ := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_right norm_laurentMap_one_sub_tC_le_one (norm_nonneg _)
          · exact mul_le_mul_of_nonneg_right norm_laurentMap_tC_le_one (norm_nonneg _)
        _ = ‖(B0.map (laurentMap (X × unitInterval))) i j‖
            + ‖(B1.map (laurentMap (X × unitInterval))) i j‖ := by rw [one_mul, one_mul]
    have htri : Work.KT.Bott.LauDefs.mNorm n
          ((H : Matrix (Fin n) (Fin n) C((X × unitInterval) × Sph ℂ, ℂ))
            - Q.map (laurentMap (X × unitInterval)))
        ≤ Work.KT.Bott.LauDefs.mNorm n
            ((H : Matrix (Fin n) (Fin n) C((X × unitInterval) × Sph ℂ, ℂ))
              - Qt.map (laurentMap (X × unitInterval)))
          + Work.KT.Bott.LauDefs.mNorm n
            (Qt.map (laurentMap (X × unitInterval)) - Q.map (laurentMap (X × unitInterval))) := by
      have h := mNorm_add_le n
        ((H : Matrix (Fin n) (Fin n) C((X × unitInterval) × Sph ℂ, ℂ))
          - Qt.map (laurentMap (X × unitInterval)))
        (Qt.map (laurentMap (X × unitInterval)) - Q.map (laurentMap (X × unitInterval)))
      rwa [show ((H : Matrix (Fin n) (Fin n) C((X × unitInterval) × Sph ℂ, ℂ))
              - Qt.map (laurentMap (X × unitInterval)))
            + (Qt.map (laurentMap (X × unitInterval)) - Q.map (laurentMap (X × unitInterval)))
          = (H : Matrix (Fin n) (Fin n) C((X × unitInterval) × Sph ℂ, ℂ))
              - Q.map (laurentMap (X × unitInterval)) from by abel] at h
    have hB0b : Work.KT.Bott.LauDefs.mNorm n (B0.map (laurentMap (X × unitInterval)))
        ≤ Work.KT.Bott.LauDefs.mNorm n
            ((H : Matrix (Fin n) (Fin n) C((X × unitInterval) × Sph ℂ, ℂ))
              - Qt.map (laurentMap (X × unitInterval))) := by
      rw [hB0map]
      calc Work.KT.Bott.LauDefs.mNorm n
            ((A0.map (laurentMap X)).map (pullAlg (mapSphProd (fstProd X))).toRingHom)
          ≤ Work.KT.Bott.LauDefs.mNorm n (A0.map (laurentMap X)) :=
            mNorm_pullback_le (mapSphProd (fstProd X)) n _
        _ = Work.KT.Bott.LauDefs.mNorm n
              (((Qt.map (laurentMap (X × unitInterval)))
                - (H : Matrix (Fin n) (Fin n) C((X × unitInterval) × Sph ℂ, ℂ))).map
                (pullAlg (mapSphProd (slice0 X))).toRingHom) := by rw [hA0map]
        _ ≤ Work.KT.Bott.LauDefs.mNorm n
              ((Qt.map (laurentMap (X × unitInterval)))
                - (H : Matrix (Fin n) (Fin n) C((X × unitInterval) × Sph ℂ, ℂ))) :=
            mNorm_pullback_le (mapSphProd (slice0 X)) n _
        _ = Work.KT.Bott.LauDefs.mNorm n
              ((H : Matrix (Fin n) (Fin n) C((X × unitInterval) × Sph ℂ, ℂ))
                - Qt.map (laurentMap (X × unitInterval))) :=
            Work.KT.Bott.LauDefs.mNorm_sub_comm n _ _
    have hB1b : Work.KT.Bott.LauDefs.mNorm n (B1.map (laurentMap (X × unitInterval)))
        ≤ Work.KT.Bott.LauDefs.mNorm n
            ((H : Matrix (Fin n) (Fin n) C((X × unitInterval) × Sph ℂ, ℂ))
              - Qt.map (laurentMap (X × unitInterval))) := by
      rw [hB1map]
      calc Work.KT.Bott.LauDefs.mNorm n
            ((A1.map (laurentMap X)).map (pullAlg (mapSphProd (fstProd X))).toRingHom)
          ≤ Work.KT.Bott.LauDefs.mNorm n (A1.map (laurentMap X)) :=
            mNorm_pullback_le (mapSphProd (fstProd X)) n _
        _ = Work.KT.Bott.LauDefs.mNorm n
              (((Qt.map (laurentMap (X × unitInterval)))
                - (H : Matrix (Fin n) (Fin n) C((X × unitInterval) × Sph ℂ, ℂ))).map
                (pullAlg (mapSphProd (slice1 X))).toRingHom) := by rw [hA1map]
        _ ≤ Work.KT.Bott.LauDefs.mNorm n
              ((Qt.map (laurentMap (X × unitInterval)))
                - (H : Matrix (Fin n) (Fin n) C((X × unitInterval) × Sph ℂ, ℂ))) :=
            mNorm_pullback_le (mapSphProd (slice1 X)) n _
        _ = Work.KT.Bott.LauDefs.mNorm n
              ((H : Matrix (Fin n) (Fin n) C((X × unitInterval) × Sph ℂ, ℂ))
                - Qt.map (laurentMap (X × unitInterval))) :=
            Work.KT.Bott.LauDefs.mNorm_sub_comm n _ _
    have hcorr : Work.KT.Bott.LauDefs.mNorm n
          (Qt.map (laurentMap (X × unitInterval)) - Q.map (laurentMap (X × unitInterval)))
        ≤ Work.KT.Bott.LauDefs.mNorm n (B0.map (laurentMap (X × unitInterval)))
          + Work.KT.Bott.LauDefs.mNorm n (B1.map (laurentMap (X × unitInterval))) :=
      mNorm_le_of_entry_le n hentry
    have hbound : Work.KT.Bott.LauDefs.mNorm n
          ((H : Matrix (Fin n) (Fin n) C((X × unitInterval) × Sph ℂ, ℂ))
            - Q.map (laurentMap (X × unitInterval))) ≤ 3 * δ := by
      have hstep : Work.KT.Bott.LauDefs.mNorm n
            ((H : Matrix (Fin n) (Fin n) C((X × unitInterval) × Sph ℂ, ℂ))
              - Q.map (laurentMap (X × unitInterval)))
          ≤ 3 * Work.KT.Bott.LauDefs.mNorm n
              ((H : Matrix (Fin n) (Fin n) C((X × unitInterval) × Sph ℂ, ℂ))
                - Qt.map (laurentMap (X × unitInterval))) := by
        calc Work.KT.Bott.LauDefs.mNorm n
              ((H : Matrix (Fin n) (Fin n) C((X × unitInterval) × Sph ℂ, ℂ))
                - Q.map (laurentMap (X × unitInterval)))
            ≤ Work.KT.Bott.LauDefs.mNorm n
                ((H : Matrix (Fin n) (Fin n) C((X × unitInterval) × Sph ℂ, ℂ))
                  - Qt.map (laurentMap (X × unitInterval)))
              + Work.KT.Bott.LauDefs.mNorm n
                (Qt.map (laurentMap (X × unitInterval)) - Q.map (laurentMap (X × unitInterval))) := htri
          _ ≤ Work.KT.Bott.LauDefs.mNorm n
                ((H : Matrix (Fin n) (Fin n) C((X × unitInterval) × Sph ℂ, ℂ))
                  - Qt.map (laurentMap (X × unitInterval)))
              + (Work.KT.Bott.LauDefs.mNorm n (B0.map (laurentMap (X × unitInterval)))
                + Work.KT.Bott.LauDefs.mNorm n (B1.map (laurentMap (X × unitInterval)))) :=
              add_le_add le_rfl hcorr
          _ ≤ Work.KT.Bott.LauDefs.mNorm n
                ((H : Matrix (Fin n) (Fin n) C((X × unitInterval) × Sph ℂ, ℂ))
                  - Qt.map (laurentMap (X × unitInterval)))
              + (Work.KT.Bott.LauDefs.mNorm n
                    ((H : Matrix (Fin n) (Fin n) C((X × unitInterval) × Sph ℂ, ℂ))
                      - Qt.map (laurentMap (X × unitInterval)))
                + Work.KT.Bott.LauDefs.mNorm n
                    ((H : Matrix (Fin n) (Fin n) C((X × unitInterval) × Sph ℂ, ℂ))
                      - Qt.map (laurentMap (X × unitInterval)))) :=
              add_le_add le_rfl (add_le_add hB0b hB1b)
          _ = 3 * Work.KT.Bott.LauDefs.mNorm n
                ((H : Matrix (Fin n) (Fin n) C((X × unitInterval) × Sph ℂ, ℂ))
                  - Qt.map (laurentMap (X × unitInterval))) := by ring
      calc Work.KT.Bott.LauDefs.mNorm n
            ((H : Matrix (Fin n) (Fin n) C((X × unitInterval) × Sph ℂ, ℂ))
              - Q.map (laurentMap (X × unitInterval)))
          ≤ 3 * Work.KT.Bott.LauDefs.mNorm n
              ((H : Matrix (Fin n) (Fin n) C((X × unitInterval) × Sph ℂ, ℂ))
                - Qt.map (laurentMap (X × unitInterval))) := hstep
        _ ≤ 3 * δ := le_of_lt (mul_lt_mul_of_pos_left hQt (by norm_num))
    calc Work.KT.Bott.LauDefs.mNorm n
          ((H : Matrix (Fin n) (Fin n) C((X × unitInterval) × Sph ℂ, ℂ))
            - Q.map (laurentMap (X × unitInterval))) * Work.KT.Bott.LauDefs.mNorm n A
        ≤ (3 * δ) * Work.KT.Bott.LauDefs.mNorm n A :=
          mul_le_mul_of_nonneg_right hbound zero_le
      _ < 1 := hδ3
  · -- t = 0
    intro i j x z
    show laurentMap (X × unitInterval) (Q i j) ((x, 0), z) = laurentMap X (P₀ i j) (x, z)
    have hQij : laurentMap (X × unitInterval) (Q i j)
        = laurentMap (X × unitInterval) (Qt i j)
          - laurentMap (X × unitInterval) (LaurentPolynomial.C (1 - Work.KT.Bott.LauDefs.tC X))
            * laurentMap (X × unitInterval) (B0 i j)
          - laurentMap (X × unitInterval) (LaurentPolynomial.C (Work.KT.Bott.LauDefs.tC X))
            * laurentMap (X × unitInterval) (B1 i j) := by
      simp only [Q, map_sub, map_mul]
    have hB0 : laurentMap (X × unitInterval) (B0 i j) ((x, 0), z) = laurentMap X (A0 i j) (x, z) := by
      simp only [B0, Matrix.map_apply, laurentMap_fstProd_apply]
    have hA0 : laurentMap X (A0 i j) (x, z)
        = laurentMap (X × unitInterval) (Qt i j) ((x, 0), z) - laurentMap X (P₀ i j) (x, z) := by
      simp only [A0, Matrix.sub_apply, Matrix.map_apply, map_sub, ContinuousMap.sub_apply,
        laurentMap_slice0_apply]
    rw [hQij]
    simp only [ContinuousMap.sub_apply, ContinuousMap.mul_apply,
      laurentMap_C_one_sub_tC_apply_zero, laurentMap_C_tC_apply_zero, hB0, hA0]
    ring
  · -- t = 1
    intro i j x z
    show laurentMap (X × unitInterval) (Q i j) ((x, 1), z) = laurentMap X (P₁ i j) (x, z)
    have hQij : laurentMap (X × unitInterval) (Q i j)
        = laurentMap (X × unitInterval) (Qt i j)
          - laurentMap (X × unitInterval) (LaurentPolynomial.C (1 - Work.KT.Bott.LauDefs.tC X))
            * laurentMap (X × unitInterval) (B0 i j)
          - laurentMap (X × unitInterval) (LaurentPolynomial.C (Work.KT.Bott.LauDefs.tC X))
            * laurentMap (X × unitInterval) (B1 i j) := by
      simp only [Q, map_sub, map_mul]
    have hB1 : laurentMap (X × unitInterval) (B1 i j) ((x, 1), z) = laurentMap X (A1 i j) (x, z) := by
      simp only [B1, Matrix.map_apply, laurentMap_fstProd_apply]
    have hA1 : laurentMap X (A1 i j) (x, z)
        = laurentMap (X × unitInterval) (Qt i j) ((x, 1), z) - laurentMap X (P₁ i j) (x, z) := by
      simp only [A1, Matrix.sub_apply, Matrix.map_apply, map_sub, ContinuousMap.sub_apply,
        laurentMap_slice1_apply]
    rw [hQij]
    simp only [ContinuousMap.sub_apply, ContinuousMap.mul_apply,
      laurentMap_C_one_sub_tC_apply_one, laurentMap_C_tC_apply_one, hB1, hA1]
    ring

end

end Work.KT.FP
