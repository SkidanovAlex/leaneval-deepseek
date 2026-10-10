import Mathlib.RingTheory.TotallySplit
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Rep.Basic
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Submission.NK.GlobalCFTdeep.Herbrand.Descent.exists_det_ne_zero_of_map_solution
import Submission.NK.GlobalCFTdeep.Herbrand.RepIso
import Submission.NK.GlobalCFTdeep.Herbrand.herbrandEq_iff_of_full_lattices
import Submission.NK.GlobalCFTdeep.LogLattice.realBasis_of_full_lattice

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

open CategoryTheory

namespace NK.GlobalCFTdeep.LogLattice

noncomputable section

/-! ## Auxiliary constructions

This section collects the elementary constructions used in the comparison of two full lattices in
the same real representation: the action of `g` on a stable subgroup as a `ℤ`-linear map, the
matrix of that action in a `ℤ`-basis, and the "rational coordinates" map of a `ℤ`-lattice. -/

/-- The action of `G` on a `G`-stable additive subgroup, as a monoid homomorphism into the
`ℤ`-linear endomorphisms. -/
def actRepLin {G : Type*} [Group G] {M : Type*} [AddCommGroup M] [Module ℤ M]
    [DistribMulAction G M] [SMulCommClass G ℤ M] (H : AddSubgroup M)
    (hH : ∀ (g : G) {x : M}, x ∈ H → g • x ∈ H) : G →* (↥H →ₗ[ℤ] ↥H) :=
  letI := NK.GlobalCFTdeep.stableDistribMulActionSubgroup H hH
  Representation.ofDistribMulAction ℤ G ↥H

/-- The action of `g` on a `G`-stable additive subgroup, as a `ℤ`-linear map. -/
def actLin {G : Type*} [Group G] {M : Type*} [AddCommGroup M] [Module ℤ M]
    [DistribMulAction G M] [SMulCommClass G ℤ M] (H : AddSubgroup M)
    (hH : ∀ (g : G) {x : M}, x ∈ H → g • x ∈ H) (g : G) : ↥H →ₗ[ℤ] ↥H :=
  actRepLin H hH g

theorem actLin_coe_apply {G : Type*} [Group G] {M : Type*} [AddCommGroup M] [Module ℤ M]
    [DistribMulAction G M] [SMulCommClass G ℤ M] (H : AddSubgroup M)
    (hH : ∀ (g : G) {x : M}, x ∈ H → g • x ∈ H) (g : G) (x : ↥H) :
    (((actLin H hH g) x : ↥H) : M) = g • (x : M) := by
  rw [actLin, actRepLin]
  exact NK.GlobalCFTdeep.stableDistribMulActionSubgroup_smul_apply H hH g x

theorem repOfStableAddSubgroup_ρ_eq {G : Type*} [Group G] {M : Type*} [AddCommGroup M]
    [Module ℤ M] [DistribMulAction G M] [SMulCommClass G ℤ M] (H : AddSubgroup M)
    (hH : ∀ (g : G) {x : M}, x ∈ H → g • x ∈ H) (g : G) :
    (NK.GlobalCFTdeep.repOfStableAddSubgroup H hH).ρ g = actLin H hH g := rfl

/-- The matrix of the action of `g` on a stable subgroup, in a `ℤ`-basis. -/
def actMat {G : Type*} [Group G] {M : Type*} [AddCommGroup M] [Module ℤ M]
    [DistribMulAction G M] [SMulCommClass G ℤ M] {n : ℕ} (H : AddSubgroup M)
    (hH : ∀ (g : G) {x : M}, x ∈ H → g • x ∈ H) (b : Module.Basis (Fin n) ℤ ↥H) (g : G) :
    Matrix (Fin n) (Fin n) ℤ :=
  LinearMap.toMatrix b b (actLin H hH g)

theorem actMat_one {G : Type*} [Group G] {M : Type*} [AddCommGroup M] [Module ℤ M]
    [DistribMulAction G M] [SMulCommClass G ℤ M] {n : ℕ} (H : AddSubgroup M)
    (hH : ∀ (g : G) {x : M}, x ∈ H → g • x ∈ H) (b : Module.Basis (Fin n) ℤ ↥H) :
    actMat H hH b 1 = 1 := by
  simp only [actMat, actLin, actRepLin, map_one, LinearMap.toMatrix_one]

theorem actMat_mul {G : Type*} [Group G] {M : Type*} [AddCommGroup M] [Module ℤ M]
    [DistribMulAction G M] [SMulCommClass G ℤ M] {n : ℕ} (H : AddSubgroup M)
    (hH : ∀ (g : G) {x : M}, x ∈ H → g • x ∈ H) (b : Module.Basis (Fin n) ℤ ↥H) (g g' : G) :
    actMat H hH b (g * g') = actMat H hH b g * actMat H hH b g' := by
  simp only [actMat, actLin, actRepLin, map_mul, LinearMap.toMatrix_mul]

/-- Componentwise `ℤ → ℚ` on coordinate functions. -/
def intCastPi (n : ℕ) : (Fin n → ℤ) →ₗ[ℤ] (Fin n → ℚ) where
  toFun x := fun i => (x i : ℚ)
  map_add' x y := by ext i; simp
  map_smul' m x := by ext i; simp [Int.cast_mul]

@[simp] theorem intCastPi_apply {n : ℕ} (x : Fin n → ℤ) (i : Fin n) :
    intCastPi n x i = (x i : ℚ) := rfl

/-- The rational coordinates of an element of a `ℤ`-lattice in a `ℤ`-basis. -/
def coordMap {n : ℕ} {W : Type*} [AddCommGroup W] [Module ℤ W]
    (b : Module.Basis (Fin n) ℤ W) : W →ₗ[ℤ] (Fin n → ℚ) :=
  (intCastPi n).comp b.equivFun.toLinearMap

theorem coordMap_apply {n : ℕ} {W : Type*} [AddCommGroup W] [Module ℤ W]
    (b : Module.Basis (Fin n) ℤ W) (x : W) (i : Fin n) :
    coordMap b x i = ((b.repr x) i : ℚ) := by
  simp [coordMap, intCastPi, Module.Basis.equivFun_apply]

/-- Casting a product of an integral matrix with an integral vector to `ℚ`. -/
theorem cast_mulVec {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (v : Fin n → ℤ) :
    intCastPi n (A.mulVec v) = (A.map (Int.castRingHom ℚ)).mulVec (intCastPi n v) := by
  ext i
  simp only [intCastPi_apply, Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.mul_apply,
    Pi.zero_apply, Pi.add_apply]
  push_cast
  exact Finset.sum_congr rfl fun j _ => by
    show (A i j : ℚ) * (v j : ℚ) = (A i j : ℚ) * (v j : ℚ)
    ring

/-- **Equivariance of the coordinate map.**  The rational coordinates of `g • x` are the matrix of
the action applied to the coordinates of `x`. -/
theorem coordMap_actLin {G : Type*} [Group G] {M : Type*} [AddCommGroup M] [Module ℤ M]
    [DistribMulAction G M] [SMulCommClass G ℤ M] {n : ℕ} (H : AddSubgroup M)
    (hH : ∀ (g : G) {x : M}, x ∈ H → g • x ∈ H) (b : Module.Basis (Fin n) ℤ ↥H) (g : G)
    (x : ↥H) :
    coordMap b (actLin H hH g x) =
      Matrix.mulVec ((actMat H hH b g).map (Int.castRingHom ℚ)) (coordMap b x) := by
  have h1 : b.equivFun (actLin H hH g x) = (actMat H hH b g).mulVec (b.equivFun x) := by
    rw [Module.Basis.equivFun_apply b (actLin H hH g x),
      ← LinearMap.toMatrix_mulVec_repr b b (actLin H hH g) x,
      Module.Basis.equivFun_apply b x]
    rfl
  show intCastPi n (b.equivFun (actLin H hH g x)) = _
  rw [h1, cast_mulVec]
  congr 1

theorem coordMap_injective {n : ℕ} {W : Type*} [AddCommGroup W] [Module ℤ W]
    (b : Module.Basis (Fin n) ℤ W) : Function.Injective (coordMap b) := by
  intro x y hxy
  have h : b.equivFun x = b.equivFun y := by
    funext i
    have hi := congrFun hxy i
    simp only [coordMap_apply, Module.Basis.equivFun_apply] at hi
    exact Int.cast_injective hi
  exact b.equivFun.injective h

theorem coordMap_self {n : ℕ} {W : Type*} [AddCommGroup W] [Module ℤ W]
    (b : Module.Basis (Fin n) ℤ W) (i : Fin n) :
    coordMap b (b i) = (Pi.single i (1 : ℚ) : Fin n → ℚ) := by
  ext j
  rw [coordMap_apply, Module.Basis.repr_self]
  by_cases h : i = j
  · rw [h, Finsupp.single_eq_same, Pi.single_eq_same, Int.cast_one]
  · rw [Finsupp.single_eq_of_ne (Ne.symm h), Pi.single_eq_of_ne (Ne.symm h), Int.cast_zero]

/-- The matrix of `x ↦ M *ᵥ x` in the standard basis is `M`. -/
theorem toMatrix_mulVecLin_pi {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) :
    LinearMap.toMatrix (Pi.basisFun ℝ (Fin d)) (Pi.basisFun ℝ (Fin d))
      (Matrix.mulVecLin M) = M := by
  ext i j
  simp only [LinearMap.toMatrix_apply, Matrix.mulVecLin_apply, Pi.basisFun_apply,
    Pi.basisFun_repr, Matrix.mulVec_single_one, Matrix.col_apply]


/-- The two castings `A.map (Int.castRingHom ℚ)).map (algebraMap ℚ ℝ)` and `A.map (Int.castRingHom ℝ)`
agree. -/
theorem map_map_castRingHom {d : ℕ} (A : Matrix (Fin d) (Fin d) ℤ) :
    (A.map (Int.castRingHom ℚ)).map (algebraMap ℚ ℝ) = A.map (Int.castRingHom ℝ) := by
  rw [Matrix.map_map]
  congr 1


/-- `e (e.symm x) = x` for a linear equivalence, phrased for the underlying linear maps. -/
theorem toLinearMap_symm_toLinearMap {R M M₂ : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    [AddCommMonoid M₂] [Module R M₂] (e : M ≃ₗ[R] M₂) (x : M₂) :
    e.toLinearMap (e.symm.toLinearMap x) = x := LinearEquiv.apply_symm_apply e x

/-- `e.symm (e x) = x` for a linear equivalence, phrased for the underlying linear maps. -/
theorem symm_toLinearMap_toLinearMap {R M M₂ : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    [AddCommMonoid M₂] [Module R M₂] (e : M ≃ₗ[R] M₂) (x : M) :
    e.symm.toLinearMap (e.toLinearMap x) = x := LinearEquiv.symm_apply_apply e x

/-- The action of a cast matrix on `Pi.single j 1` is the `j`-th column. -/
theorem map_mulVec_single {d : ℕ} (A : Matrix (Fin d) (Fin d) ℤ) (j : Fin d) :
    (A.map (Int.castRingHom ℝ)).mulVec (Pi.single j 1) = fun i => ((A i j : ℤ) : ℝ) := by
  funext i
  rw [Matrix.mulVec_single_one, Matrix.col_apply, Matrix.map_apply, Int.coe_castRingHom]

/-- **The matrices of the two actions are conjugate over `ℚ`.**  Let `M, N` be `G`-stable full
lattices in the same real representation `V` (finitely generated over `ℤ`, spanning `V` over `ℝ`,
of `ℤ`-rank equal to `dim_ℝ V`).  Then there are `ℤ`-bases `bM`, `bN` of `M`, `N` and an invertible
rational matrix `Y` conjugating the matrix of the action of `g` on `M` in the basis `bM` to that of
the action of `g` on `N` in the basis `bN`, simultaneously for all `g : G`.

This is the "descent from `ℝ` to `ℚ`" (Milne, *CFT*, Lemma 3.2) applied to the change-of-basis
matrix between the two lattices: both images of the bases in `V` are `ℝ`-bases of `V`
(`realBasis_of_full_lattice`), so the change of basis matrix `X` is invertible over `ℝ` and
intertwines the two actions; `NK.GlobalCFTdeep.Herbrand.Descent.exists_det_ne_zero_of_map_solution`
then produces the rational `Y`. -/
theorem exists_ratMatrix_conjugating {G : Type*} [Group G] [Fintype G]
    {V : Type*} [AddCommGroup V] [Module ℝ V] [DistribMulAction G V] [SMulCommClass G ℝ V]
    (M N : AddSubgroup V) (hMG : ∀ (g : G) {x : V}, x ∈ M → g • x ∈ M)
    (hNG : ∀ (g : G) {x : V}, x ∈ N → g • x ∈ N)
    [Module.Finite ℤ ↥M] [Module.Free ℤ ↥M] [Module.Finite ℤ ↥N] [Module.Free ℤ ↥N]
    (hMspan : Submodule.span ℝ (M : Set V) = ⊤) (hNspan : Submodule.span ℝ (N : Set V) = ⊤)
    (hrankM : Module.finrank ℤ ↥M = Module.finrank ℝ V)
    (hrankN : Module.finrank ℤ ↥N = Module.finrank ℝ V) :
    ∃ (bM : Module.Basis (Fin (Module.finrank ℝ V)) ℤ ↥M)
      (bN : Module.Basis (Fin (Module.finrank ℝ V)) ℤ ↥N)
      (Y : Matrix (Fin (Module.finrank ℝ V)) (Fin (Module.finrank ℝ V)) ℚ),
      Y.det ≠ 0 ∧ ∀ g : G,
        (actMat N hNG bN g).map (Int.castRingHom ℚ) * Y
          = Y * (actMat M hMG bM g).map (Int.castRingHom ℚ) := by
  classical
  have hcardM : Fintype.card (Fin (Module.finrank ℤ ↥M)) = Module.finrank ℝ V := by
    rw [Fintype.card_fin]; exact hrankM
  have hcardN : Fintype.card (Fin (Module.finrank ℤ ↥N)) = Module.finrank ℝ V := by
    rw [Fintype.card_fin]; exact hrankN
  let bM : Module.Basis (Fin (Module.finrank ℝ V)) ℤ ↥M :=
    (Module.finBasis ℤ ↥M).reindex (Fintype.equivFinOfCardEq hcardM)
  let bN : Module.Basis (Fin (Module.finrank ℝ V)) ℤ ↥N :=
    (Module.finBasis ℤ ↥N).reindex (Fintype.equivFinOfCardEq hcardN)
  obtain ⟨bMR, hbMR⟩ := realBasis_of_full_lattice M hMspan bM
  obtain ⟨bNR, hbNR⟩ := realBasis_of_full_lattice N hNspan bN
  let ΦM : (Fin (Module.finrank ℝ V) → ℝ) ≃ₗ[ℝ] V := bMR.equivFun.symm
  let ΦN : (Fin (Module.finrank ℝ V) → ℝ) ≃ₗ[ℝ] V := bNR.equivFun.symm
  set bR : Module.Basis (Fin (Module.finrank ℝ V)) ℝ (Fin (Module.finrank ℝ V) → ℝ) :=
    Pi.basisFun ℝ (Fin (Module.finrank ℝ V)) with hbR
  let X : Matrix (Fin (Module.finrank ℝ V)) (Fin (Module.finrank ℝ V)) ℝ :=
    LinearMap.toMatrix bR bR (ΦN.symm.toLinearMap ∘ₗ ΦM.toLinearMap)
  -- ## the change of basis matrix is invertible
  have hXdet : X.det ≠ 0 := by
    have hinv : X * (LinearMap.toMatrix bR bR (ΦM.symm.toLinearMap ∘ₗ ΦN.toLinearMap)) = 1 := by
      rw [← LinearMap.toMatrix_comp bR bR bR, ← LinearMap.toMatrix_id bR]
      congr 1
      ext x
      simp
    intro h
    have h1 := congrArg Matrix.det hinv
    rw [Matrix.det_mul, h, zero_mul, Matrix.det_one] at h1
    exact one_ne_zero h1.symm
  -- ## the identification `ΦM x = ∑ i, x i • bM i`
  have hPhiM_apply : ∀ x : Fin (Module.finrank ℝ V) → ℝ,
      ΦM.toLinearMap x = ∑ i, x i • ((bM i : ↥M) : V) := by
    intro x
    calc ΦM.toLinearMap x = bMR.equivFun.symm x := rfl
      _ = ∑ i, x i • bMR i := Module.Basis.equivFun_symm_apply bMR x
      _ = ∑ i, x i • ((bM i : ↥M) : V) := Finset.sum_congr rfl fun i _ => by rw [hbMR]
  have hPhiN_apply : ∀ x : Fin (Module.finrank ℝ V) → ℝ,
      ΦN.toLinearMap x = ∑ i, x i • ((bN i : ↥N) : V) := by
    intro x
    calc ΦN.toLinearMap x = bNR.equivFun.symm x := rfl
      _ = ∑ i, x i • bNR i := Module.Basis.equivFun_symm_apply bNR x
      _ = ∑ i, x i • ((bN i : ↥N) : V) := Finset.sum_congr rfl fun i _ => by rw [hbNR]
  -- ## it intertwines the two actions
  have hPhiM : ∀ g : G, ΦM.toLinearMap ∘ₗ Matrix.mulVecLin ((actMat M hMG bM g).map (Int.castRingHom ℝ))
      = (DistribSMul.toLinearMap ℝ V g) ∘ₗ ΦM.toLinearMap := by
    intro g
    refine Module.Basis.ext bR fun j => ?_
    have hsingle : (∑ i, (Pi.single j (1 : ℝ) : Fin (Module.finrank ℝ V) → ℝ) i
        • ((bM i : ↥M) : V)) = ((bM j : ↥M) : V) := by
      rw [Finset.sum_eq_single j]
      · rw [Pi.single_eq_same, one_smul]
      · intro i _ hi
        rw [Pi.single_eq_of_ne hi, zero_smul]
      · intro hj
        exact absurd (Finset.mem_univ j) hj
    have hsum : (∑ i, ((actMat M hMG bM g) i j : ℝ) • ((bM i : ↥M) : V))
        = ((actLin M hMG g (bM j) : ↥M) : V) := by
      have h2 : (∑ i, ((actMat M hMG bM g) i j : ℝ) • ((bM i : ↥M) : V))
          = ((∑ i, (actMat M hMG bM g) i j • bM i : ↥M) : V) := by
        rw [show ((∑ i, (actMat M hMG bM g) i j • bM i : ↥M) : V)
            = ∑ i, (((actMat M hMG bM g) i j • bM i : ↥M) : V) from
              map_sum (AddSubgroup.subtype M)
                (fun i => (actMat M hMG bM g) i j • bM i) Finset.univ]
        exact Finset.sum_congr rfl fun i _ => by
          rw [AddSubgroup.coe_zsmul, Int.cast_smul_eq_zsmul]
      rw [h2]
      congr 1
      have hto : ∀ i, (actMat M hMG bM g) i j
          = (bM.repr (actLin M hMG g (bM j))) i := fun i => by
        rw [actMat, LinearMap.toMatrix_apply]
      exact (Finset.sum_congr rfl fun i _ => by rw [hto i]).trans
        (Module.Basis.sum_repr bM (actLin M hMG g (bM j)))
    simp only [LinearMap.comp_apply, Matrix.mulVecLin_apply, DistribSMul.toLinearMap_apply]
    rw [show bR j = Pi.single j (1 : ℝ) from by rw [hbR]; exact Pi.basisFun_apply ℝ _ j,
      map_mulVec_single]
    rw [hPhiM_apply, hPhiM_apply, hsum, hsingle]
    exact actLin_coe_apply M hMG g (bM j)
  have hPhiN : ∀ g : G, ΦN.toLinearMap ∘ₗ Matrix.mulVecLin ((actMat N hNG bN g).map (Int.castRingHom ℝ))
      = (DistribSMul.toLinearMap ℝ V g) ∘ₗ ΦN.toLinearMap := by
    intro g
    refine Module.Basis.ext bR fun j => ?_
    have hsingle : (∑ i, (Pi.single j (1 : ℝ) : Fin (Module.finrank ℝ V) → ℝ) i
        • ((bN i : ↥N) : V)) = ((bN j : ↥N) : V) := by
      rw [Finset.sum_eq_single j]
      · rw [Pi.single_eq_same, one_smul]
      · intro i _ hi
        rw [Pi.single_eq_of_ne hi, zero_smul]
      · intro hj
        exact absurd (Finset.mem_univ j) hj
    have hsum : (∑ i, ((actMat N hNG bN g) i j : ℝ) • ((bN i : ↥N) : V))
        = ((actLin N hNG g (bN j) : ↥N) : V) := by
      have h2 : (∑ i, ((actMat N hNG bN g) i j : ℝ) • ((bN i : ↥N) : V))
          = ((∑ i, (actMat N hNG bN g) i j • bN i : ↥N) : V) := by
        rw [show ((∑ i, (actMat N hNG bN g) i j • bN i : ↥N) : V)
            = ∑ i, (((actMat N hNG bN g) i j • bN i : ↥N) : V) from
              map_sum (AddSubgroup.subtype N)
                (fun i => (actMat N hNG bN g) i j • bN i) Finset.univ]
        exact Finset.sum_congr rfl fun i _ => by
          rw [AddSubgroup.coe_zsmul, Int.cast_smul_eq_zsmul]
      rw [h2]
      congr 1
      have hto : ∀ i, (actMat N hNG bN g) i j
          = (bN.repr (actLin N hNG g (bN j))) i := fun i => by
        rw [actMat, LinearMap.toMatrix_apply]
      exact (Finset.sum_congr rfl fun i _ => by rw [hto i]).trans
        (Module.Basis.sum_repr bN (actLin N hNG g (bN j)))
    simp only [LinearMap.comp_apply, Matrix.mulVecLin_apply, DistribSMul.toLinearMap_apply]
    rw [show bR j = Pi.single j (1 : ℝ) from by rw [hbR]; exact Pi.basisFun_apply ℝ _ j,
      map_mulVec_single]
    rw [hPhiN_apply, hPhiN_apply, hsum, hsingle]
    exact actLin_coe_apply N hNG g (bN j)
  have hXintw : ∀ g : G,
      (actMat N hNG bN g).map (Int.castRingHom ℝ) * X
        = X * (actMat M hMG bM g).map (Int.castRingHom ℝ) := by
    intro g
    have hcomp : Matrix.mulVecLin ((actMat N hNG bN g).map (Int.castRingHom ℝ))
          ∘ₗ (ΦN.symm.toLinearMap ∘ₗ ΦM.toLinearMap)
        = (ΦN.symm.toLinearMap ∘ₗ ΦM.toLinearMap)
          ∘ₗ Matrix.mulVecLin ((actMat M hMG bM g).map (Int.castRingHom ℝ)) := by
      refine LinearMap.ext fun x => ?_
      simp only [LinearMap.comp_apply]
      have h1 : ΦN.toLinearMap (Matrix.mulVecLin ((actMat N hNG bN g).map (Int.castRingHom ℝ))
            (ΦN.symm.toLinearMap (ΦM.toLinearMap x)))
          = g • (ΦM.toLinearMap x) := by
        have h := LinearMap.congr_fun (hPhiN g) (ΦN.symm.toLinearMap (ΦM.toLinearMap x))
        simp only [LinearMap.comp_apply, DistribSMul.toLinearMap_apply] at h
        rw [show ΦN.toLinearMap (ΦN.symm.toLinearMap (ΦM.toLinearMap x)) = ΦM.toLinearMap x from
          toLinearMap_symm_toLinearMap ΦN (ΦM.toLinearMap x)] at h
        exact h
      have h2 : ΦM.toLinearMap (Matrix.mulVecLin ((actMat M hMG bM g).map (Int.castRingHom ℝ)) x)
          = g • (ΦM.toLinearMap x) := by
        have h := LinearMap.congr_fun (hPhiM g) x
        simpa only [LinearMap.comp_apply, DistribSMul.toLinearMap_apply] using h
      have h1' : Matrix.mulVecLin ((actMat N hNG bN g).map (Int.castRingHom ℝ))
            (ΦN.symm.toLinearMap (ΦM.toLinearMap x))
          = ΦN.symm.toLinearMap (g • (ΦM.toLinearMap x)) := by
        rw [← h1, symm_toLinearMap_toLinearMap]
      rw [h2]
      exact h1'
    have := congrArg (LinearMap.toMatrix bR bR) hcomp
    rwa [LinearMap.toMatrix_comp bR bR bR, LinearMap.toMatrix_comp bR bR bR,
      toMatrix_mulVecLin_pi, toMatrix_mulVecLin_pi] at this
  -- ## descent to `ℚ`
  refine ⟨bM, bN, ?_⟩
  set e := Fintype.equivFin G with he
  have hXmat : ∀ i : Fin (Fintype.card G),
      (((actMat N hNG bN (e.symm i)).map (Int.castRingHom ℚ)).map (algebraMap ℚ ℝ)) * X
        = X * (((actMat M hMG bM (e.symm i)).map (Int.castRingHom ℚ)).map (algebraMap ℚ ℝ)) := by
    intro i
    rw [map_map_castRingHom, map_map_castRingHom]
    exact hXintw (e.symm i)
  obtain ⟨Y, hYeq, hYdet⟩ := Herbrand.Descent.exists_det_ne_zero_of_map_solution
    (fun i => (actMat M hMG bM (e.symm i)).map (Int.castRingHom ℚ))
    (fun i => (actMat N hNG bN (e.symm i)).map (Int.castRingHom ℚ)) X hXmat hXdet
  exact ⟨Y, hYdet, fun g => by
    have := hYeq (e g)
    simpa [he] using this⟩

/-- **Milne, *CFT*, 3.2–3.5: two full `G`-stable lattices in the same real representation have the
same Herbrand quotient.**  This is the comparison step of Milne's proof of Proposition 3.1: the log
lattice `M = M' + ℤ·e` and the divisor lattice `Hom(T, ℤ)` are both *full* lattices in
`∏_{w ∈ T} ℝ`, hence have the same Herbrand quotient, even though they are in general *not*
commensurable (their `ℚ`-forms differ).

**Both lattices must have the same `ℤ`-rank as the `ℝ`-dimension of `V`** (this is the hypothesis
`hrankM`/`hrankN`): merely spanning `V` over `ℝ` does not force the `ℚ`-forms to agree — the
counterexample is `V = ℝ`, `M = ℤ`, `N = ℤ + ℤ√2` (both span `ℝ`, but `M` has rank `1` and `N`
rank `2`), where the invariants differ.  With `finrank ℤ M = finrank ℝ V` (and the same for `N`)
the canonical maps `ℝ ⊗[ℤ] M → V` and `ℝ ⊗[ℤ] N → V` are isomorphisms, so both `ℝ ⊗ M` and
`ℝ ⊗ N` are `ℝ[G]`-isomorphic to `V`.

## Proof sketch

1. The inclusions extend to `ℝ`-linear `G`-equivariant maps `ℝ ⊗[ℤ] M → V`, `ℝ ⊗[ℤ] N → V`
   (`LinearMap.baseChange`); surjectivity is `hMspan`/`hNspan`, and injectivity follows from the
   rank hypotheses (source and target have the same `ℝ`-dimension, via `Module.finrank_baseChange`).
   Composing the inverse of one with the other gives an `ℝ[G]`-isomorphism
   `e : ℝ ⊗[ℤ] M ≃ₗ[ℝ] ℝ ⊗[ℤ] N`.
2. Pick `ℤ`-bases (`Module.finBasis`), let `P g`, `Q g` be the matrices of the actions and
   `X := LinearMap.toMatrix (bM.baseChange ℝ) (bN.baseChange ℝ) e`; then `X.det ≠ 0` and
   `(Q g).map (algebraMap ℚ ℝ) * X = X * (P g).map (algebraMap ℚ ℝ)`
   (`LinearMap.toMatrix_comp`, `Module.Basis.baseChange_apply`).  By
   `NK.GlobalCFTdeep.Herbrand.Descent.exists_det_ne_zero_of_map_solution` there is an invertible
   rational `Y` with `Q g * Y = Y * P g`.
3. `Y` gives a `ℚ[G]`-isomorphism `γ : ℚ ⊗[ℤ] M ≃ₗ[ℚ] ℚ ⊗[ℤ] N` (`Matrix.toLin` on the
   base-changed bases).  Then `γ ⁻¹(N) ⊆ ℚ ⊗[ℤ] M` is a `ℤ[G]`-lattice with the same `ℚ`-form as
   `M`, so `M` and `γ ⁻¹(N)` are commensurable and Herbrand's result for a finite-index subgroup
   (`herbrandEq_iff_of_finite_quotient`, applied to a common finite-index sublattice) gives
   `HerbrandEq M m ↔ HerbrandEq (γ ⁻¹(N)) m`; and `herbrandEq_of_repIso` along `γ` gives
   `HerbrandEq (γ ⁻¹(N)) m ↔ HerbrandEq N m`.

The finiteness hypotheses required by the finite-index comparison are supplied by
`NK.GlobalCFTdeep.Herbrand.finite_tateCohomology_of_moduleFinite` (all the modules occurring are
finitely generated over `ℤ`). -/
theorem herbrandEq_iff_of_span_eq_top {G : Type} [Group G] [Fintype G] [IsCyclic G]
    {V : Type} [AddCommGroup V] [Module ℝ V] [DistribMulAction G V] [SMulCommClass G ℝ V]
    (M N : AddSubgroup V) (hMG : ∀ (g : G) {x : V}, x ∈ M → g • x ∈ M)
    (hNG : ∀ (g : G) {x : V}, x ∈ N → g • x ∈ N)
    [Module.Finite ℤ M] [Module.Free ℤ M] [Module.Finite ℤ N] [Module.Free ℤ N]
    (hMspan : Submodule.span ℝ (M : Set V) = ⊤) (hNspan : Submodule.span ℝ (N : Set V) = ⊤)
    (hrankM : Module.finrank ℤ M = Module.finrank ℝ V)
    (hrankN : Module.finrank ℤ N = Module.finrank ℝ V)
    (m : ℕ) :
    NK.GlobalCFTdeep.HerbrandEq (NK.GlobalCFTdeep.repOfStableAddSubgroup M hMG) m ↔
      NK.GlobalCFTdeep.HerbrandEq (NK.GlobalCFTdeep.repOfStableAddSubgroup N hNG) m := by
  classical
  letI : CommGroup G := IsCyclic.commGroup
  obtain ⟨bM, bN, Y, hYdet, hYeq⟩ :=
    exists_ratMatrix_conjugating M N hMG hNG hMspan hNspan hrankM hrankN
  -- ## the two integral representations, mapped to `ℚ`
  let Pq : G → Matrix (Fin (Module.finrank ℝ V)) (Fin (Module.finrank ℝ V)) ℚ :=
    fun g => (actMat M hMG bM g).map (Int.castRingHom ℚ)
  let Qq : G → Matrix (Fin (Module.finrank ℝ V)) (Fin (Module.finrank ℝ V)) ℚ :=
    fun g => (actMat N hNG bN g).map (Int.castRingHom ℚ)
  have hPq_one : Pq 1 = 1 := by
    ext i j
    simp only [Pq, actMat_one, Matrix.map_apply, Matrix.one_apply]
    split_ifs <;> simp
  have hPq_mul : ∀ g h : G, Pq (g * h) = Pq g * Pq h := by
    intro g h
    simp only [Pq]
    rw [actMat_mul, Matrix.map_mul]
  have hQq_one : Qq 1 = 1 := by
    ext i j
    simp only [Qq, actMat_one, Matrix.map_apply, Matrix.one_apply]
    split_ifs <;> simp
  have hQq_mul : ∀ g h : G, Qq (g * h) = Qq g * Qq h := by
    intro g h
    simp only [Qq]
    rw [actMat_mul, Matrix.map_mul]
  -- ## the `ℚ[G]`-action on `ℚ^d` given by the matrices `Pq`
  letI : DistribMulAction G (Fin (Module.finrank ℝ V) → ℚ) :=
    { smul := fun g x => (Pq g).mulVec x
      one_smul := fun x => by
        show (Pq 1).mulVec x = x
        rw [hPq_one, Matrix.one_mulVec]
      mul_smul := fun g h x => by
        show (Pq (g * h)).mulVec x = (Pq g).mulVec ((Pq h).mulVec x)
        rw [hPq_mul, ← Matrix.mulVec_mulVec x (Pq g) (Pq h)]
      smul_zero := fun g => by
        show (Pq g).mulVec 0 = 0
        rw [Matrix.mulVec_zero]
      smul_add := fun g x y => by
        show (Pq g).mulVec (x + y) = (Pq g).mulVec x + (Pq g).mulVec y
        rw [Matrix.mulVec_add] }
  haveI : SMulCommClass G ℚ (Fin (Module.finrank ℝ V) → ℚ) :=
    ⟨fun g q x => Matrix.mulVec_smul (Pq g) q x⟩
  -- ## the coordinate maps of the two lattices
  let fM : ↥M →ₗ[ℤ] (Fin (Module.finrank ℝ V) → ℚ) := coordMap bM
  let fN : ↥N →ₗ[ℤ] (Fin (Module.finrank ℝ V) → ℚ) := coordMap bN
  have hfM_inj : Function.Injective fM := coordMap_injective bM
  have hfN_inj : Function.Injective fN := coordMap_injective bN
  have hfM : ∀ (g : G) (x : ↥M), fM (actLin M hMG g x) = (Pq g).mulVec (fM x) :=
    fun g x => coordMap_actLin M hMG bM g x
  have hfN : ∀ (g : G) (y : ↥N), fN (actLin N hNG g y) = (Qq g).mulVec (fN y) :=
    fun g y => coordMap_actLin N hNG bN g y
  -- ## the rational change of basis and the lattice it defines
  set YM : (Fin (Module.finrank ℝ V) → ℚ) →ₗ[ℚ] (Fin (Module.finrank ℝ V) → ℚ) :=
    Matrix.mulVecLin Y with hYM
  set YZ : (Fin (Module.finrank ℝ V) → ℚ) →ₗ[ℤ] (Fin (Module.finrank ℝ V) → ℚ) :=
    YM.restrictScalars ℤ with hYZ
  have hYkey : ∀ (g : G) (x : Fin (Module.finrank ℝ V) → ℚ),
      YM (g • x) = (Qq g).mulVec (YM x) := by
    intro g x
    rw [show g • x = (Pq g).mulVec x from rfl, Matrix.mulVecLin_apply,
      Matrix.mulVecLin_apply, Matrix.mulVec_mulVec x Y (Pq g),
      Matrix.mulVec_mulVec x (Qq g) Y, hYeq g]
  -- ## the two full lattices in `ℚ^d`
  let L₁ : AddSubgroup (Fin (Module.finrank ℝ V) → ℚ) := fM.range.toAddSubgroup
  let L₂ : AddSubgroup (Fin (Module.finrank ℝ V) → ℚ) :=
    AddSubgroup.comap YZ.toAddMonoidHom fN.range.toAddSubgroup
  have hL₁ : ∀ (g : G) {x : Fin (Module.finrank ℝ V) → ℚ}, x ∈ L₁ → g • x ∈ L₁ := by
    intro g x hx
    obtain ⟨a, rfl⟩ := LinearMap.mem_range.mp (show x ∈ fM.range from hx)
    refine LinearMap.mem_range.mpr ⟨actLin M hMG g a, ?_⟩
    show fM (actLin M hMG g a) = (Pq g).mulVec (fM a)
    exact hfM g a
  have hL₂ : ∀ (g : G) {x : Fin (Module.finrank ℝ V) → ℚ}, x ∈ L₂ → g • x ∈ L₂ := by
    intro g x hx
    have hx' : YZ x ∈ fN.range := AddSubgroup.mem_comap.mp hx
    obtain ⟨y, hy⟩ := LinearMap.mem_range.mp hx'
    refine AddSubgroup.mem_comap.mpr (LinearMap.mem_range.mpr ⟨actLin N hNG g y, ?_⟩)
    show fN (actLin N hNG g y) = YZ (g • x)
    rw [hfN g y, hy]
    exact (hYkey g x).symm
  -- ## finiteness of the two lattices over `ℤ`
  haveI hfinNrange : Module.Finite ℤ ↥(fN.range) :=
    Module.Finite.equiv (LinearEquiv.ofInjective fN hfN_inj)
  haveI hfin₁ : Module.Finite ℤ ↥L₁ :=
    Module.Finite.equiv (LinearEquiv.ofInjective fM hfM_inj)
  have hYinj : Function.Injective YM := by
    intro x y hxy
    have h0 : YM (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    rw [hYM, Matrix.mulVecLin_apply] at h0
    have h1 : Y.det • (x - y) = 0 := by
      have h2 : (Y.adjugate * Y).mulVec (x - y) = 0 := by
        rw [← Matrix.mulVec_mulVec (x - y) Y.adjugate Y, h0, Matrix.mulVec_zero]
      simpa only [Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec] using h2
    rcases smul_eq_zero.mp h1 with h | h
    · exact absurd h hYdet
    · exact sub_eq_zero.mp h
  have hYsurj : Function.Surjective YM :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := YM) (by simp)).mp hYinj
  let Yc : ↥L₂ →ₗ[ℤ] ↥(fN.range) :=
    { toFun := fun x => (⟨YZ (x : Fin (Module.finrank ℝ V) → ℚ),
          AddSubgroup.mem_comap.mp x.2⟩ : ↥(fN.range))
      map_add' := fun x y => by
        refine Subtype.ext ?_
        show YZ ((x + y : ↥L₂) : Fin (Module.finrank ℝ V) → ℚ)
          = YZ (x : Fin (Module.finrank ℝ V) → ℚ) + YZ (y : Fin (Module.finrank ℝ V) → ℚ)
        rw [show ((x + y : ↥L₂) : Fin (Module.finrank ℝ V) → ℚ)
          = (x : Fin (Module.finrank ℝ V) → ℚ) + (y : Fin (Module.finrank ℝ V) → ℚ) from rfl,
          map_add]
      map_smul' := fun n x => by
        refine Subtype.ext ?_
        show YZ ((n • x : ↥L₂) : Fin (Module.finrank ℝ V) → ℚ)
          = n • YZ (x : Fin (Module.finrank ℝ V) → ℚ)
        rw [AddSubgroup.coe_zsmul, map_smul] }
  have hYc_val : ∀ x : ↥L₂, ((Yc x : ↥(fN.range)) : Fin (Module.finrank ℝ V) → ℚ) = YM (x : _) := by
    intro x
    show YZ (x : Fin (Module.finrank ℝ V) → ℚ) = YM (x : Fin (Module.finrank ℝ V) → ℚ)
    rw [hYZ]
    rfl
  have hYc_bij : Function.Bijective Yc := by
    constructor
    · intro x y hxy
      refine Subtype.ext (hYinj ?_)
      have := congrArg (fun z : ↥(fN.range) => (z : Fin (Module.finrank ℝ V) → ℚ)) hxy
      rwa [hYc_val x, hYc_val y] at this
    · rintro ⟨z, hz⟩
      obtain ⟨x, hx⟩ := hYsurj z
      refine ⟨⟨x, ?_⟩, ?_⟩
      · show YM x ∈ fN.range
        rw [hx]; exact hz
      · refine Subtype.ext ?_
        rw [hYc_val]
        exact hx
  haveI hfin₂ : Module.Finite ℤ ↥L₂ :=
    Module.Finite.equiv (LinearEquiv.ofBijective Yc hYc_bij).symm
  -- ## the two lattices span `ℚ^d`
  have hspanM : Submodule.span ℚ (fM.range : Set (Fin (Module.finrank ℝ V) → ℚ)) = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro x
    have hx : x = ∑ i, x i • (Pi.single i (1 : ℚ) : Fin (Module.finrank ℝ V) → ℚ) := by
      ext j
      rw [Finset.sum_apply, Finset.sum_eq_single j]
      · rw [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
      · intro i _ hi
        rw [Pi.smul_apply, Pi.single_eq_of_ne (Ne.symm hi), smul_zero]
      · intro hj
        exact absurd (Finset.mem_univ j) hj
    rw [hx]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    exact ⟨bM i, coordMap_self bM i⟩
  have hspanN : Submodule.span ℚ (fN.range : Set (Fin (Module.finrank ℝ V) → ℚ)) = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro x
    have hx : x = ∑ i, x i • (Pi.single i (1 : ℚ) : Fin (Module.finrank ℝ V) → ℚ) := by
      ext j
      rw [Finset.sum_apply, Finset.sum_eq_single j]
      · rw [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
      · intro i _ hi
        rw [Pi.smul_apply, Pi.single_eq_of_ne (Ne.symm hi), smul_zero]
      · intro hj
        exact absurd (Finset.mem_univ j) hj
    rw [hx]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    exact ⟨bN i, coordMap_self bN i⟩
  have hspan₁ : Submodule.span ℚ (L₁ : Set (Fin (Module.finrank ℝ V) → ℚ)) = ⊤ :=
    hspanM
  have hspan₂ : Submodule.span ℚ (L₂ : Set (Fin (Module.finrank ℝ V) → ℚ)) = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro x
    have hmap : Submodule.map YM
        (Submodule.span ℚ (L₂ : Set (Fin (Module.finrank ℝ V) → ℚ))) = ⊤ := by
      rw [Submodule.map_span]
      have himg : (YM '' (L₂ : Set (Fin (Module.finrank ℝ V) → ℚ)))
          = (fN.range : Set (Fin (Module.finrank ℝ V) → ℚ)) := by
        ext z
        constructor
        · rintro ⟨y, hy, rfl⟩
          exact AddSubgroup.mem_comap.mp hy
        · intro hz
          obtain ⟨y, hyz⟩ := hYsurj z
          refine ⟨y, ?_, hyz⟩
          show YM y ∈ fN.range
          rw [hyz]; exact hz
      rw [himg, hspanN]
    have hx : YM x ∈ Submodule.map YM
        (Submodule.span ℚ (L₂ : Set (Fin (Module.finrank ℝ V) → ℚ))) := by
      rw [hmap]; trivial
    obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.mp hx
    rw [← hYinj hyx]; exact hy
  -- ## the representations of `M` and of `L₁` are isomorphic
  let e₁ : ↥M ≃ₗ[ℤ] ↥L₁ := LinearEquiv.ofInjective fM hfM_inj
  have he₁_pt : ∀ (g : G) (x : ↥M), e₁ (actLin M hMG g x) = actLin L₁ hL₁ g (e₁ x) := by
    intro g x
    refine Subtype.ext ?_
    rw [LinearEquiv.ofInjective_apply, actLin_coe_apply, LinearEquiv.ofInjective_apply]
    exact hfM g x
  have he₁ : ∀ g : G, (e₁ : ↥M →ₗ[ℤ] ↥L₁) ∘ₗ (repOfStableAddSubgroup M hMG).ρ g
      = (repOfStableAddSubgroup L₁ hL₁).ρ g ∘ₗ (e₁ : ↥M →ₗ[ℤ] ↥L₁) := by
    intro g
    rw [repOfStableAddSubgroup_ρ_eq M hMG g, repOfStableAddSubgroup_ρ_eq L₁ hL₁ g]
    refine LinearMap.ext fun x => ?_
    exact he₁_pt g x
  -- ## the representations of `L₂` and of `N` are isomorphic
  let ψ : ↥L₂ →ₗ[ℤ] ↥N := (LinearEquiv.ofInjective fN hfN_inj).symm.toLinearMap ∘ₗ Yc
  have hψ : ∀ x : ↥L₂, fN (ψ x) = YM (x : Fin (Module.finrank ℝ V) → ℚ) := by
    intro x
    have h1 : fN (ψ x) = ((Yc x : ↥(fN.range)) : Fin (Module.finrank ℝ V) → ℚ) := by
      show fN ((LinearEquiv.ofInjective fN hfN_inj).symm (Yc x)) = _
      rw [← LinearEquiv.ofInjective_apply fN (h := hfN_inj)
        ((LinearEquiv.ofInjective fN hfN_inj).symm (Yc x)), LinearEquiv.apply_symm_apply]
    rw [h1, hYc_val]
  have hψ_bij : Function.Bijective ψ := by
    constructor
    · intro x y hxy
      have h : YM (x : Fin (Module.finrank ℝ V) → ℚ) = YM (y : _) := by
        rw [← hψ x, ← hψ y, hxy]
      exact Subtype.ext (hYinj h)
    · intro y
      obtain ⟨x, hx⟩ := hYsurj (fN y)
      refine ⟨⟨x, ?_⟩, ?_⟩
      · show YM x ∈ fN.range
        rw [hx]; exact LinearMap.mem_range.mpr ⟨y, rfl⟩
      · refine hfN_inj ?_
        rw [hψ]
        exact hx
  have hψ_pt : ∀ (g : G) (x : ↥L₂), ψ (actLin L₂ hL₂ g x) = actLin N hNG g (ψ x) := by
    intro g x
    refine hfN_inj ?_
    rw [hψ, actLin_coe_apply, hfN g (ψ x), hψ]
    exact hYkey g (x : Fin (Module.finrank ℝ V) → ℚ)
  have hψ_intw : ∀ g : G, ψ ∘ₗ (repOfStableAddSubgroup L₂ hL₂).ρ g
      = (repOfStableAddSubgroup N hNG).ρ g ∘ₗ ψ := by
    intro g
    rw [repOfStableAddSubgroup_ρ_eq L₂ hL₂ g, repOfStableAddSubgroup_ρ_eq N hNG g]
    refine LinearMap.ext fun x => ?_
    exact hψ_pt g x
  -- ## assembly
  have iso₁ : repOfStableAddSubgroup M hMG ≅ repOfStableAddSubgroup L₁ hL₁ :=
    Rep.mkIso (Representation.Equiv.mk e₁ he₁)
  have iso₂ : repOfStableAddSubgroup L₂ hL₂ ≅ repOfStableAddSubgroup N hNG :=
    Rep.mkIso (Representation.Equiv.mk (LinearEquiv.ofBijective ψ hψ_bij) hψ_intw)
  exact (herbrandEq_of_repIso iso₁ m).trans
    (((Herbrand.herbrandEq_iff_of_full_lattices L₁ L₂ hL₁ hL₂ hspan₁ hspan₂) m).trans
      (herbrandEq_of_repIso iso₂ m))

end

end NK.GlobalCFTdeep.LogLattice
