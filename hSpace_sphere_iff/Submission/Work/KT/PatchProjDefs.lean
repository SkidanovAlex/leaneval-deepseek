import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.FPatch
import Submission.Work.KT.ClutchGeom
import Submission.Work.KT.FiberUtil
import Submission.Work.KT.mvLin

/-!
# The clutching projection over the double disk (`Work.KT.PatchProjDefs`)

Let `V` be a real normed space, `ρ : C(Ball V, ℂ) →+* C(Sph V, ℂ)` the restriction to the
boundary sphere and `TwoDisk V = FiberProd ρ ρ` the algebra of the double disk (`C(S^{dim V})`).

Given a unit `γ ∈ GL_n(C(Sph V, ℂ))` and a unit `G` over the ball whose boundary restriction is the
hyperbolic block matrix `diag(γ, γ⁻¹)` (which exists by `Work.KT.lift_diag_unit`), the *clutching
projection* is

  `clipP γ G = (G⁻¹ · diag(1_n,0_n) · G , diag(1_n,0_n)) ∈ M_{2n}(TwoDisk V)`,

a matrix over the double disk: the two components agree on the boundary because `diag(γ,γ⁻¹)`
commutes with `diag(1_n,0_n)`.  It is an idempotent whose image is the patched module of `γ`
(`clipP_range`), and whose `K₀`-class is the class of the trivial bundle of rank `n`
(`cls_clipP`, from the vanishing of the reduced `K`-theory of an odd-dimensional sphere).
-/

namespace Work.KT

open Matrix

noncomputable section

set_option maxHeartbeats 800000

variable (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The `2n × 2n` matrices over the ball. -/
abbrev BallMat (n : ℕ) := Matrix (Fin (n + n)) (Fin (n + n)) C(Ball V, ℂ)

/-! ## Commutativity of the function algebras

The project's convention is to carry `Ring` instances on subalgebras and to pass commutativity
explicitly. -/

theorem comm_sphereC : ∀ x y : C(Sph V, ℂ), x * y = y * x := fun x y => by
  ext z; exact mul_comm _ _

theorem comm_ballC : ∀ x y : C(Ball V, ℂ), x * y = y * x := fun x y => by
  ext z; exact mul_comm _ _

theorem comm_twoDisk : ∀ x y : TwoDisk V, x * y = y * x := by
  intro x y
  refine Subtype.ext (Prod.ext ?_ ?_) <;> ext z <;> exact mul_comm _ _

/-! ## Block vectors -/

/-- The vector with first block `f` and second block `g`. -/
def padVec {S : Type} {m : ℕ} (f g : Fin m → S) : Fin (m + m) → S := Fin.addCases f g

@[simp] lemma padVec_castAdd {S : Type} {m : ℕ} (f g : Fin m → S) (i : Fin m) :
    padVec f g (Fin.castAdd m i) = f i := by
  show Fin.addCases f g (Fin.castAdd m i) = f i
  exact Fin.addCases_left i

@[simp] lemma padVec_natAdd {S : Type} {m : ℕ} (f g : Fin m → S) (i : Fin m) :
    padVec f g (Fin.natAdd m i) = g i := by
  show Fin.addCases f g (Fin.natAdd m i) = g i
  exact Fin.addCases_right i

@[simp] lemma padVec_addNat {S : Type} {m : ℕ} (f g : Fin m → S) (i : Fin m) :
    padVec f g (Fin.addNat i m) = g i := by
  rw [show (Fin.addNat i m : Fin (m + m)) = Fin.natAdd m i from
    Fin.ext (Nat.add_comm _ _)]
  exact padVec_natAdd f g i

@[simp] lemma padVec_inl {S : Type} {m : ℕ} (f g : Fin m → S) (i : Fin m) :
    padVec f g (finSumFinEquiv (Sum.inl i)) = f i := padVec_castAdd f g i

@[simp] lemma padVec_inr {S : Type} {m : ℕ} (f g : Fin m → S) (i : Fin m) :
    padVec f g (finSumFinEquiv (Sum.inr i)) = g i := padVec_natAdd f g i

/-- The first block of a vector. -/
def fstBlk {S : Type} {m : ℕ} (v : Fin (m + m) → S) : Fin m → S :=
  fun i => v (finSumFinEquiv (Sum.inl i))

/-- The second block of a vector. -/
def sndBlk {S : Type} {m : ℕ} (v : Fin (m + m) → S) : Fin m → S :=
  fun i => v (finSumFinEquiv (Sum.inr i))

@[simp] lemma fstBlk_padVec {S : Type} {m : ℕ} (f g : Fin m → S) : fstBlk (padVec f g) = f := by
  funext i
  rw [fstBlk, padVec_inl]

@[simp] lemma sndBlk_padVec {S : Type} {m : ℕ} (f g : Fin m → S) : sndBlk (padVec f g) = g := by
  funext i
  rw [sndBlk, padVec_inr]

lemma padVec_fstBlk {S : Type} {m : ℕ} (v : Fin (m + m) → S) :
    padVec (fstBlk v) (sndBlk v) = v := by
  funext j
  obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective j
  rcases s with i | i
  · rw [padVec_inl]; rfl
  · rw [padVec_inr]; rfl

/-- A vector whose second block is `g` is the padding of its first block and `g`. -/
lemma eq_padVec_of_sndBlk_eq {S : Type} {m : ℕ} {v : Fin (m + m) → S} {g : Fin m → S}
    (h : sndBlk v = g) : v = padVec (fstBlk v) g := by
  calc v = padVec (fstBlk v) (sndBlk v) := (padVec_fstBlk v).symm
    _ = padVec (fstBlk v) g := by rw [h]

/-- Two paddings are equal only if their blocks are. -/
lemma padVec_inj {S : Type} {m : ℕ} {f g f' g' : Fin m → S}
    (h : padVec f g = padVec f' g') : f = f' ∧ g = g' := by
  constructor
  · funext i
    have ht := congrFun h (finSumFinEquiv (Sum.inl i))
    simpa using ht
  · funext i
    have ht := congrFun h (finSumFinEquiv (Sum.inr i))
    simpa using ht

theorem map_padVec_ringHom {A B : Type} [Ring A] [Ring B] (φ : A →+* B) {m : ℕ}
    (f g : Fin m → A) :
    (fun j => φ (padVec f g j)) = padVec (fun i => φ (f i)) (fun i => φ (g i)) := by
  funext j
  obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective j
  rcases s with i | i <;> simp

/-- Block matrix–vector multiplication on block vectors. -/
theorem blockMulVec_padVec {S : Type} [Ring S] {m : ℕ}
    (A D : Matrix (Fin m) (Fin m) S) (f g : Fin m → S) :
    (Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks A 0 0 D)) *ᵥ padVec f g =
      padVec (A *ᵥ f) (D *ᵥ g) := by
  funext j
  obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective j
  rcases s with i | i
  · rw [blockMulVec_inl]
    have h : (fun j => padVec f g (finSumFinEquiv (Sum.inl j))) = f := by
      funext j; simp
    rw [h]
    simp
  · rw [blockMulVec_inr]
    have h : (fun j => padVec f g (finSumFinEquiv (Sum.inr j))) = g := by
      funext j; simp
    rw [h]
    simp

/-! ## Matrix bookkeeping for the block form -/

theorem mapMatrix_mapMatrix {A B C : Type} [Ring A] [Ring B] [Ring C] (φ : A →+* B)
    (ψ : B →+* C) {N : ℕ} (M : Matrix (Fin N) (Fin N) A) :
    RingHom.mapMatrix ψ (RingHom.mapMatrix φ M) = RingHom.mapMatrix (ψ.comp φ) M := by
  apply Matrix.ext
  intro i j
  rfl

theorem map_reindex_mapMatrix {A B : Type} [Ring A] [Ring B] (φ : A →+* B) {m : ℕ}
    (M : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) A) :
    RingHom.mapMatrix φ (Matrix.reindex finSumFinEquiv finSumFinEquiv M) =
      Matrix.reindex finSumFinEquiv finSumFinEquiv (RingHom.mapMatrix φ M) := by
  apply Matrix.ext
  intro i j
  rfl

theorem map_fromBlocks_zero {A B : Type} [Ring A] [Ring B] (φ : A →+* B) {m : ℕ} :
    RingHom.mapMatrix φ
        (Matrix.fromBlocks (1 : Matrix (Fin m) (Fin m) A) 0 0
          (0 : Matrix (Fin m) (Fin m) A)) =
      Matrix.fromBlocks (1 : Matrix (Fin m) (Fin m) B) 0 0 0 := by
  apply Matrix.ext
  intro i j
  rcases i with a | a <;> rcases j with b | b <;>
    · simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.fromBlocks_apply₁₁,
        Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
        Matrix.zero_apply, Matrix.one_apply]
      by_cases h : a = b <;> simp [h, map_one, map_zero]

/-- A ring homomorphism carries the standard projection to the standard projection. -/
theorem mapMatrix_stdProj {A B : Type} [Ring A] [Ring B] (φ : A →+* B) (m : ℕ) :
    RingHom.mapMatrix φ (stdProj A m) = stdProj B m := by
  rw [stdProj, stdProj, map_reindex_mapMatrix, map_fromBlocks_zero]


/-! ## The hyperbolic gluing and the standard projection -/

/-- The hyperbolic block matrix `diag(γ, γ⁻¹)`. -/
def diagGlue (n : ℕ) (γ : (Matrix (Fin n) (Fin n) C(Sph V, ℂ))ˣ) :
    Matrix (Fin (n + n)) (Fin (n + n)) C(Sph V, ℂ) :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv
    (Matrix.fromBlocks (↑γ : Matrix (Fin n) (Fin n) C(Sph V, ℂ)) 0 0
      (↑(γ⁻¹) : Matrix (Fin n) (Fin n) C(Sph V, ℂ)))

/-- The standard projection `diag(1_n, 0_n)` as a matrix over the boundary sphere. -/
def clipZ₀ (n : ℕ) : Matrix (Fin (n + n)) (Fin (n + n)) C(Sph V, ℂ) :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv
    (Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) C(Sph V, ℂ)) 0 0 0)

/-- The standard projection `diag(1_n, 0_n)` as a matrix over the double disk. -/
def clipZ (n : ℕ) : Matrix (Fin (n + n)) (Fin (n + n)) (TwoDisk V) := stdProj (TwoDisk V) n

/-- The image of the standard projection under either component of the double disk is the standard
projection over the sphere. -/
theorem mapMatrix_clipZ (n : ℕ) {ψ : TwoDisk V →+* C(Ball V, ℂ)}
    (hψ : ψ = (FiberProd.fstHom : TwoDisk V →+* C(Ball V, ℂ)) ∨
      ψ = (FiberProd.sndHom : TwoDisk V →+* C(Ball V, ℂ))) :
    RingHom.mapMatrix ((restRho V).comp ψ) (clipZ V n) = clipZ₀ V n := by
  rcases hψ with h | h <;> subst h
  · rw [clipZ, clipZ₀, stdProj, map_reindex_mapMatrix, map_fromBlocks_zero]
  · rw [clipZ, clipZ₀, stdProj, map_reindex_mapMatrix, map_fromBlocks_zero]

theorem mapMatrix_fstHom_clipZ (n : ℕ) :
    RingHom.mapMatrix (FiberProd.fstHom : TwoDisk V →+* C(Ball V, ℂ)) (clipZ V n) =
      stdProj (C(Ball V, ℂ)) n := by
  rw [clipZ, mapMatrix_stdProj]

theorem mapMatrix_sndHom_clipZ (n : ℕ) :
    RingHom.mapMatrix (FiberProd.sndHom : TwoDisk V →+* C(Ball V, ℂ)) (clipZ V n) =
      stdProj (C(Ball V, ℂ)) n := by
  rw [clipZ, mapMatrix_stdProj]

theorem rho_fstHom_eq_sndHom :
    (restRho V).comp (FiberProd.fstHom : TwoDisk V →+* C(Ball V, ℂ)) =
      (restRho V).comp (FiberProd.sndHom : TwoDisk V →+* C(Ball V, ℂ)) :=
  RingHom.ext fun z => z.2

theorem clipZ₀_mul_diagGlue (n : ℕ) (γ : (Matrix (Fin n) (Fin n) C(Sph V, ℂ))ˣ) :
    clipZ₀ V n * diagGlue V n γ =
      Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks (↑γ : Matrix (Fin n) (Fin n) C(Sph V, ℂ)) 0 0 0) := by
  unfold clipZ₀ diagGlue
  simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply,
    Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.one_mul]

theorem diagGlue_mul_clipZ₀ (n : ℕ) (γ : (Matrix (Fin n) (Fin n) C(Sph V, ℂ))ˣ) :
    diagGlue V n γ * clipZ₀ V n =
      Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks (↑γ : Matrix (Fin n) (Fin n) C(Sph V, ℂ)) 0 0 0) := by
  unfold clipZ₀ diagGlue
  simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply,
    Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one]

theorem clipZ₀_comm_diagGlue (n : ℕ) (γ : (Matrix (Fin n) (Fin n) C(Sph V, ℂ))ˣ) :
    clipZ₀ V n * diagGlue V n γ = diagGlue V n γ * clipZ₀ V n := by
  rw [clipZ₀_mul_diagGlue, diagGlue_mul_clipZ₀]

theorem mapMatrix_Ginv_mul_diagGlue (n : ℕ) (γ : (Matrix (Fin n) (Fin n) C(Sph V, ℂ))ˣ)
    {G : (BallMat V n)ˣ}
    (hG : RingHom.mapMatrix (restRho V) (↑G : BallMat V n) = diagGlue V n γ) :
    RingHom.mapMatrix (restRho V) (↑(G⁻¹) : BallMat V n) * diagGlue V n γ = 1 := by
  rw [← hG, ← map_mul, Units.inv_mul, map_one]

theorem diagGlue_mul_mapMatrix_Ginv (n : ℕ) (γ : (Matrix (Fin n) (Fin n) C(Sph V, ℂ))ˣ)
    {G : (BallMat V n)ˣ}
    (hG : RingHom.mapMatrix (restRho V) (↑G : BallMat V n) = diagGlue V n γ) :
    diagGlue V n γ * RingHom.mapMatrix (restRho V) (↑(G⁻¹) : BallMat V n) = 1 := by
  rw [← hG, ← map_mul, Units.mul_inv, map_one]

/-! ## The clutching projection -/

/-- The clutching projection determined by a lift `G` of `diag(γ, γ⁻¹)`. -/
def clipP (n : ℕ) (γ : (Matrix (Fin n) (Fin n) C(Sph V, ℂ))ˣ) (G : (BallMat V n)ˣ)
    (hG : RingHom.mapMatrix (restRho V) (↑G : BallMat V n) = diagGlue V n γ) :
    Matrix (Fin (n + n)) (Fin (n + n)) (TwoDisk V) :=
  fiberMatrix (ρ₁ := restRho V) (ρ₂ := restRho V)
    ((↑(G⁻¹) : BallMat V n) *
      RingHom.mapMatrix (FiberProd.fstHom : TwoDisk V →+* C(Ball V, ℂ)) (clipZ V n) *
        (↑G : BallMat V n))
    (RingHom.mapMatrix (FiberProd.sndHom : TwoDisk V →+* C(Ball V, ℂ)) (clipZ V n))
    (by
      rw [RingHom.map_mul, RingHom.map_mul, mapMatrix_mapMatrix, mapMatrix_mapMatrix, hG,
        mapMatrix_clipZ V n (Or.inr rfl), mapMatrix_clipZ V n (Or.inl rfl)]
      rw [mul_assoc, clipZ₀_comm_diagGlue, ← mul_assoc,
        mapMatrix_Ginv_mul_diagGlue V n γ hG, one_mul])

/-- The first component of the clutching projection. -/
theorem mapMatrix_clipP_fst (n : ℕ) (γ : (Matrix (Fin n) (Fin n) C(Sph V, ℂ))ˣ)
    (G : (BallMat V n)ˣ)
    (hG : RingHom.mapMatrix (restRho V) (↑G : BallMat V n) = diagGlue V n γ) :
    RingHom.mapMatrix (FiberProd.fstHom : TwoDisk V →+* C(Ball V, ℂ)) (clipP V n γ G hG) =
      (↑(G⁻¹) : BallMat V n) *
        RingHom.mapMatrix (FiberProd.fstHom : TwoDisk V →+* C(Ball V, ℂ)) (clipZ V n) *
          (↑G : BallMat V n) := by
  apply Matrix.ext
  intro i j
  rfl

/-- The second component of the clutching projection. -/
theorem mapMatrix_clipP_snd (n : ℕ) (γ : (Matrix (Fin n) (Fin n) C(Sph V, ℂ))ˣ)
    (G : (BallMat V n)ˣ)
    (hG : RingHom.mapMatrix (restRho V) (↑G : BallMat V n) = diagGlue V n γ) :
    RingHom.mapMatrix (FiberProd.sndHom : TwoDisk V →+* C(Ball V, ℂ)) (clipP V n γ G hG) =
      RingHom.mapMatrix (FiberProd.sndHom : TwoDisk V →+* C(Ball V, ℂ)) (clipZ V n) := by
  apply Matrix.ext
  intro i j
  rfl

end

end Work.KT
