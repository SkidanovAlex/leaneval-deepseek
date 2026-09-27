import Mathlib

/-!
# Work.KT.Defs — shared definitions for the K-theoretic odd case of `hSpace_sphere_iff`

Model: complex K-theory of a compact space `X` is the algebraic `K₀` of the commutative
`ℂ`-algebra `C(X, ℂ)` (Swan).  Relative groups, quotient spaces and mapping cones are never built
as spaces: they are replaced by subalgebras of function algebras.

* `K0 R` — Grothendieck group of idempotent square matrices over a ring `R` up to
  Murray–von Neumann equivalence: the free abelian group on all square matrices modulo
  `[p ⊕ q] = [p] + [q]`, `[p] = [q]` for equivalent idempotents, and `[p] = 0` for non-idempotents.
* `K0.map φ` — functoriality along a ring homomorphism.
* `IsK0Mul μ`, `IsPsi2 ψ`, `IsPsi3 ψ` — characterisations (by values on generators) of the ring
  product and of the Adams operations `ψ²`, `ψ³`.  `ψ²(p) = [Sym² p] − [Λ² p]` (eigenspaces of the
  swap on `p ⊗ p`); `ψ³(p) = [V₀] − [V_ω]` (eigenspaces of the cyclic permutation on `p ⊗ p ⊗ p`).
  No splitting principle is needed for these.
* `constOn X A` — functions constant on `A` (= `C(X/A)`); `Kpair V` — the pair (unit ball, unit
  sphere) of a normed space `V`, i.e. `C(D_V / S_V) = C(S^{dim V})`.
* `coneAlg f` — `C(C_f)` for `f : S_V → T`, as the pullback `C(T) ×_{C(S_V)} C(D_V)`.
* `prodAlg V W` — `C((D_V/S_V) × (D_W/S_W))`, the algebra in which external products are detected.
* `HopfOddK m f` — `f : S^{4m-1} → S^{2m}` has odd Hopf invariant, in `K`-theory.
-/

namespace Work.KT

open Matrix

noncomputable section

/-! ## Algebraic `K₀` -/

/-- A square matrix of some size. -/
abbrev Mat (R : Type) [Ring R] : Type := Σ n : ℕ, Matrix (Fin n) (Fin n) R

variable {R S : Type} [Ring R] [Ring S]

/-- `p` is idempotent. -/
def Mat.IsIdem (p : Mat R) : Prop := p.2 * p.2 = p.2

/-- Block sum `p ⊕ q`. -/
def Mat.sum (p q : Mat R) : Mat R :=
  ⟨p.1 + q.1, Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks p.2 0 0 q.2)⟩

/-- Entrywise image under a ring map. -/
def Mat.map (φ : R →+* S) (p : Mat R) : Mat S := ⟨p.1, p.2.map φ⟩

/-- The identity matrix of size `n` (the trivial bundle of rank `n`). -/
def Mat.one (R : Type) [Ring R] (n : ℕ) : Mat R := ⟨n, 1⟩

/-- Murray–von Neumann equivalence (isomorphism of the projective modules). -/
def Mat.MvN (p q : Mat R) : Prop :=
  ∃ (a : Matrix (Fin q.1) (Fin p.1) R) (b : Matrix (Fin p.1) (Fin q.1) R),
    b * a = p.2 ∧ a * b = q.2

/-- The relations of `K₀`. -/
def K0Rel (R : Type) [Ring R] : AddSubgroup (FreeAbelianGroup (Mat R)) :=
  AddSubgroup.closure
    ({x | ∃ p q : Mat R, p.IsIdem ∧ q.IsIdem ∧
        x = FreeAbelianGroup.of (p.sum q) - FreeAbelianGroup.of p - FreeAbelianGroup.of q} ∪
     {x | ∃ p q : Mat R, p.IsIdem ∧ q.IsIdem ∧ p.MvN q ∧
        x = FreeAbelianGroup.of p - FreeAbelianGroup.of q} ∪
     {x | ∃ p : Mat R, ¬ p.IsIdem ∧ x = FreeAbelianGroup.of p})

/-- `K₀` of a ring. -/
abbrev K0 (R : Type) [Ring R] : Type := FreeAbelianGroup (Mat R) ⧸ K0Rel R

/-- The class of a matrix (zero unless the matrix is idempotent). -/
def cls (p : Mat R) : K0 R := QuotientAddGroup.mk (FreeAbelianGroup.of p)

open Classical in
/-- Value of `K₀(φ)` on a generator. -/
def mapCls (φ : R →+* S) (p : Mat R) : K0 S := if p.IsIdem then cls (p.map φ) else 0

/-- Functoriality of `K₀` along a ring homomorphism. -/
def K0.map (φ : R →+* S) : K0 R →+ K0 S :=
  QuotientAddGroup.lift (K0Rel R) (FreeAbelianGroup.lift (mapCls φ)) (by
    have idem_map : ∀ {p : Mat R}, p.IsIdem → (p.map φ).IsIdem := by
      intro p hp
      unfold Mat.IsIdem Mat.map at *
      simp only
      rw [← Matrix.map_mul, hp]
    have idem_sum : ∀ {p q : Mat R}, p.IsIdem → q.IsIdem → (p.sum q).IsIdem := by
      intro p q hp hq
      unfold Mat.IsIdem Mat.sum at *
      simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply,
        Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, hp, hq]
    have sum_map : ∀ p q : Mat R, (p.sum q).map φ = (p.map φ).sum (q.map φ) := by
      intro p q
      unfold Mat.sum Mat.map
      simp only [Sigma.mk.injEq, heq_eq_eq, true_and]
      ext i j
      simp only [Matrix.map_apply, Matrix.reindex_apply, Matrix.submatrix_apply]
      rcases finSumFinEquiv.symm i with a | a <;> rcases finSumFinEquiv.symm j with b | b <;> simp
    have cls_eq : ∀ {p q : Mat S},
        FreeAbelianGroup.of p - FreeAbelianGroup.of q ∈ K0Rel S → cls p = cls q := by
      intro p q h
      unfold cls
      rw [← sub_eq_zero, ← QuotientAddGroup.mk_sub, QuotientAddGroup.eq_zero_iff]
      exact h
    rw [K0Rel, AddSubgroup.closure_le]
    rintro x ((⟨p, q, hp, hq, rfl⟩ | ⟨p, q, hp, hq, ⟨a, b, hba, hab⟩, rfl⟩) | ⟨p, hp, rfl⟩)
    · simp only [SetLike.mem_coe, AddMonoidHom.mem_ker, map_sub, FreeAbelianGroup.lift_apply_of,
        mapCls, if_pos hp, if_pos hq, if_pos (idem_sum hp hq), sum_map]
      have hmem : FreeAbelianGroup.of ((p.map φ).sum (q.map φ)) - FreeAbelianGroup.of (p.map φ)
          - FreeAbelianGroup.of (q.map φ) ∈ K0Rel S :=
        AddSubgroup.subset_closure (Or.inl (Or.inl ⟨_, _, idem_map hp, idem_map hq, rfl⟩))
      unfold cls
      rw [← QuotientAddGroup.mk_sub, ← QuotientAddGroup.mk_sub, QuotientAddGroup.eq_zero_iff]
      exact hmem
    · simp only [SetLike.mem_coe, AddMonoidHom.mem_ker, map_sub, FreeAbelianGroup.lift_apply_of,
        mapCls, if_pos hp, if_pos hq]
      rw [sub_eq_zero]
      apply cls_eq
      refine AddSubgroup.subset_closure (Or.inl (Or.inr ⟨_, _, idem_map hp, idem_map hq,
        ⟨a.map φ, b.map φ, ?_, ?_⟩, rfl⟩))
      · show b.map φ * a.map φ = p.2.map φ
        rw [← hba]; exact (Matrix.map_mul).symm
      · show a.map φ * b.map φ = q.2.map φ
        rw [← hab]; exact (Matrix.map_mul).symm
    · simp [mapCls, hp])

/-- `K₀` along an algebra homomorphism. -/
abbrev K0.mapA {A B : Type} [Ring A] [Ring B] [Algebra ℂ A] [Algebra ℂ B]
    (φ : A →ₐ[ℂ] B) : K0 A →+ K0 B :=
  K0.map φ.toRingHom

/-! ## Products and Adams operations -/

section Comm

variable {A : Type} [Ring A]

/-- Kronecker product of square matrices, reindexed to `Fin (n * k)`. -/
def kronMat {n k : ℕ} (M : Matrix (Fin n) (Fin n) A) (N : Matrix (Fin k) (Fin k) A) :
    Matrix (Fin (n * k)) (Fin (n * k)) A :=
  Matrix.reindex finProdFinEquiv finProdFinEquiv (Matrix.kroneckerMap (· * ·) M N)

/-- Kronecker product `p ⊗ q` (tensor product of bundles). -/
def Mat.kron (p q : Mat A) : Mat A := ⟨p.1 * q.1, kronMat p.2 q.2⟩

open Classical in
/-- Value of the ring product of `K₀` on two generators. -/
def mulCls (p q : Mat A) : K0 A := if p.IsIdem ∧ q.IsIdem then cls (p.kron q) else 0

/-- `μ` is the ring multiplication of `K₀ A` (it is determined by this property). -/
def IsK0Mul (μ : K0 A →+ K0 A →+ K0 A) : Prop := ∀ p q : Mat A, μ (cls p) (cls q) = mulCls p q

/-- The swap `(i, j) ↦ (j, i)` of `Fin n × Fin n`, transported to `Fin (n * n)`. -/
def swapPerm (n : ℕ) : Equiv.Perm (Fin (n * n)) :=
  (finProdFinEquiv.symm.trans (Equiv.prodComm (Fin n) (Fin n))).trans finProdFinEquiv

/-- The cyclic permutation `((i, j), k) ↦ ((k, i), j)` of `(Fin n × Fin n) × Fin n`, transported
to `Fin (n * n * n)`. -/
def cycPerm (n : ℕ) : Equiv.Perm (Fin (n * n * n)) :=
  let c : (Fin n × Fin n) × Fin n ≃ (Fin n × Fin n) × Fin n :=
    { toFun := fun x => ((x.2, x.1.1), x.1.2)
      invFun := fun x => ((x.1.2, x.2), x.1.1)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let e : Fin (n * n * n) ≃ (Fin n × Fin n) × Fin n :=
    finProdFinEquiv.symm.trans (Equiv.prodCongr finProdFinEquiv.symm (Equiv.refl _))
  (e.trans c).trans e.symm

variable [Algebra ℂ A]

/-- `p ⊗ p` cut down by `(1 + ε·swap)/2`: `ε = 1` gives `Sym² p`, `ε = -1` gives `Λ² p`. -/
def sq2Part (ε : ℂ) (p : Mat A) : Mat A :=
  ⟨p.1 * p.1, kronMat p.2 p.2 *
    (algebraMap ℂ A (1 / 2) • (1 + algebraMap ℂ A ε • (swapPerm p.1).permMatrix A))⟩

/-- A primitive cube root of unity. -/
def omega : ℂ := Complex.exp (2 * Real.pi * Complex.I / 3)

/-- `p ⊗ p ⊗ p` cut down by the spectral projector `(1 + λ⁻¹ c + λ⁻² c²)/3` of the cyclic
permutation `c` for the eigenvalue `λ` (`λ³ = 1`). -/
def cubePart (lam : ℂ) (p : Mat A) : Mat A :=
  ⟨p.1 * p.1 * p.1,
    kronMat (kronMat p.2 p.2) p.2 *
    (algebraMap ℂ A (1 / 3) • (1 + algebraMap ℂ A lam⁻¹ • (cycPerm p.1).permMatrix A +
      algebraMap ℂ A (lam⁻¹ ^ 2) • ((cycPerm p.1).permMatrix A * (cycPerm p.1).permMatrix A)))⟩

open Classical in
/-- `ψ²` on a generator: `[Sym² p] − [Λ² p]`. -/
def psi2Cls (p : Mat A) : K0 A :=
  if p.IsIdem then cls (sq2Part 1 p) - cls (sq2Part (-1) p) else 0

open Classical in
/-- `ψ³` on a generator: `[V₁] − [V_ω]`, eigenspaces of the cyclic permutation on `p⊗p⊗p`
(the `ω` and `ω²` eigenspaces are isomorphic, and `1 + ω + ω² = 0`). -/
def psi3Cls (p : Mat A) : K0 A :=
  if p.IsIdem then cls (cubePart 1 p) - cls (cubePart omega p) else 0

/-- `ψ` is the Adams operation `ψ²` on `K₀ A`. -/
def IsPsi2 (ψ : K0 A →+ K0 A) : Prop := ∀ p : Mat A, ψ (cls p) = psi2Cls p

/-- `ψ` is the Adams operation `ψ³` on `K₀ A`. -/
def IsPsi3 (ψ : K0 A →+ K0 A) : Prop := ∀ p : Mat A, ψ (cls p) = psi3Cls p

end Comm

/-! ## Function algebras -/

/-- Functions constant on `A`: the algebra `C(X/A, ℂ)` (for `A` nonempty). -/
def constOn (X : Type) [TopologicalSpace X] (A : Set X) : Subalgebra ℂ C(X, ℂ) where
  carrier := {g | ∀ a ∈ A, ∀ a' ∈ A, g a = g a'}
  mul_mem' := by
    intro f g hf hg a ha a' ha'
    simp only [ContinuousMap.mul_apply, hf a ha a' ha', hg a ha a' ha']
  add_mem' := by
    intro f g hf hg a ha a' ha'
    simp only [ContinuousMap.add_apply, hf a ha a' ha', hg a ha a' ha']
  algebraMap_mem' := by
    intro c a _ a' _
    rfl

/-- Evaluation at a point, as a character of `C(X, ℂ)`. -/
abbrev evalC {X : Type} [TopologicalSpace X] (x : X) : C(X, ℂ) →ₐ[ℂ] ℂ :=
  ContinuousMap.evalAlgHom ℂ ℂ x

/-- The closed unit ball of `V`, as a type. -/
abbrev Ball (V : Type) [NormedAddCommGroup V] : Type := Metric.closedBall (0 : V) 1

/-- The unit sphere of `V`, as a type. -/
abbrev Sph (V : Type) [NormedAddCommGroup V] : Type := Metric.sphere (0 : V) 1

/-- The boundary sphere inside the ball. -/
def bdry (V : Type) [NormedAddCommGroup V] : Set (Ball V) := {y | ‖(y : V)‖ = 1}

/-- `C(D_V / S_V) = C(S^{dim V})`: functions on the ball constant on the boundary sphere. -/
abbrev Kpair (V : Type) [NormedAddCommGroup V] : Subalgebra ℂ C(Ball V, ℂ) :=
  constOn (Ball V) (bdry V)

/-- Augmentation of `Kpair V`: evaluation at a point `y0` (taken on the boundary). -/
def augPair (V : Type) [NormedAddCommGroup V] (y0 : Ball V) : Kpair V →ₐ[ℂ] ℂ :=
  (evalC y0).comp (Kpair V).val

/-- Pull-back of functions along a continuous map, as an algebra homomorphism. -/
abbrev pullAlg {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (g : C(X, Y)) :
    C(Y, ℂ) →ₐ[ℂ] C(X, ℂ) :=
  (ContinuousMap.compStarAlgHom' ℂ ℂ g).toAlgHom

/-- Restriction of a function on `X × [0,1]` to the slice `X × {t}`. -/
def sliceAt {X : Type} [TopologicalSpace X] (t : unitInterval) :
    C(X × unitInterval, ℂ) →ₐ[ℂ] C(X, ℂ) :=
  pullAlg ⟨fun x => (x, t), by fun_prop⟩

/-- `K¹(X) = K¹(pt)`: every invertible matrix over `C(X)`, after adding an identity block, is
homotopic through invertible matrices to a constant matrix. -/
def GLStablyTrivial (X : Type) [TopologicalSpace X] : Prop :=
  ∀ (n : ℕ) (u : Matrix (Fin n) (Fin n) C(X, ℂ)), IsUnit u →
    ∃ (k : ℕ) (H : Matrix (Fin (n + k)) (Fin (n + k)) C(X × unitInterval, ℂ)), IsUnit H ∧
      H.map (sliceAt 0) = Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks u 0 0 1) ∧
      ∃ c : Matrix (Fin (n + k)) (Fin (n + k)) ℂ, H.map (sliceAt 1) = c.map (algebraMap ℂ C(X, ℂ))

/-! ## The mapping cone -/

section Cone

variable {V : Type} [NormedAddCommGroup V] {T : Type} [TopologicalSpace T]

/-- `C(C_f)` for `f : S_V → T`: pairs `(g, h) ∈ C(T) × C(D_V)` with `h = g ∘ f` on `S_V`. -/
def coneAlg (f : C(Sph V, T)) : Subalgebra ℂ (C(T, ℂ) × C(Ball V, ℂ)) where
  carrier := {z | ∀ (y : Ball V) (hy : ‖(y : V)‖ = 1),
    z.2 y = z.1 (f ⟨(y : V), mem_sphere_zero_iff_norm.mpr hy⟩)}
  mul_mem' := by
    intro z w hz hw y hy
    simp only [Prod.fst_mul, Prod.snd_mul, ContinuousMap.mul_apply, hz y hy, hw y hy]
  add_mem' := by
    intro z w hz hw y hy
    simp only [Prod.fst_add, Prod.snd_add, ContinuousMap.add_apply, hz y hy, hw y hy]
  algebraMap_mem' := by
    intro c y hy
    rfl

/-- Restriction `C(C_f) → C(T)` to the bottom space. -/
def coneToT (f : C(Sph V, T)) : coneAlg f →ₐ[ℂ] C(T, ℂ) :=
  (AlgHom.fst ℂ C(T, ℂ) C(Ball V, ℂ)).comp (coneAlg f).val

/-- Augmentation of `C(C_f)`: evaluation at a point `t0 ∈ T`. -/
def augCone (f : C(Sph V, T)) (t0 : T) : coneAlg f →ₐ[ℂ] ℂ :=
  (evalC t0).comp (coneToT f)

/-- `C(C_f / T) = C(D_V / S_V) → C(C_f)` (collapse of the bottom space; `y0` on the boundary). -/
def relToCone (f : C(Sph V, T)) (y0 : Ball V) (hy0 : y0 ∈ bdry V) : Kpair V →ₐ[ℂ] coneAlg f :=
  AlgHom.codRestrict
    (AlgHom.prod ((Algebra.ofId ℂ C(T, ℂ)).comp (augPair V y0)) (Kpair V).val) (coneAlg f)
    (by
      intro h y hy
      have h1 := h.2 y hy y0 hy0
      simp only [AlgHom.prod_apply, AlgHom.comp_apply, Subalgebra.coe_val]
      rw [h1]
      rfl)

end Cone

/-! ## Products of ball pairs -/

section Prod

variable (V W : Type) [NormedAddCommGroup V] [NormedAddCommGroup W]

/-- The first projection `D_{V×W} = D_V × D_W → D_V` (sup norm on `V × W`). -/
def prFst : C(Ball (V × W), Ball V) :=
  ⟨fun z => ⟨(z : V × W).1, by
      have h := mem_closedBall_zero_iff.mp z.2
      exact mem_closedBall_zero_iff.mpr ((norm_fst_le _).trans h)⟩,
    by fun_prop⟩

/-- The second projection `D_{V×W} → D_W`. -/
def prSnd : C(Ball (V × W), Ball W) :=
  ⟨fun z => ⟨(z : V × W).2, by
      have h := mem_closedBall_zero_iff.mp z.2
      exact mem_closedBall_zero_iff.mpr ((norm_snd_le _).trans h)⟩,
    by fun_prop⟩

/-- `C((D_V/S_V) × (D_W/S_W)) = C(S^a × S^b)`: functions on `D_V × D_W` whose value at `(x, y)`
does not depend on `x` when `x ∈ S_V`, nor on `y` when `y ∈ S_W`. -/
def prodAlg : Subalgebra ℂ C(Ball (V × W), ℂ) where
  carrier := {F | (∀ z z' : Ball (V × W), ‖(z : V × W).1‖ = 1 → ‖(z' : V × W).1‖ = 1 →
      (z : V × W).2 = (z' : V × W).2 → F z = F z') ∧
    (∀ z z' : Ball (V × W), ‖(z : V × W).2‖ = 1 → ‖(z' : V × W).2‖ = 1 →
      (z : V × W).1 = (z' : V × W).1 → F z = F z')}
  mul_mem' := by
    rintro F G ⟨hF1, hF2⟩ ⟨hG1, hG2⟩
    refine ⟨fun z z' h1 h2 h3 => ?_, fun z z' h1 h2 h3 => ?_⟩
    · simp only [ContinuousMap.mul_apply, hF1 z z' h1 h2 h3, hG1 z z' h1 h2 h3]
    · simp only [ContinuousMap.mul_apply, hF2 z z' h1 h2 h3, hG2 z z' h1 h2 h3]
  add_mem' := by
    rintro F G ⟨hF1, hF2⟩ ⟨hG1, hG2⟩
    refine ⟨fun z z' h1 h2 h3 => ?_, fun z z' h1 h2 h3 => ?_⟩
    · simp only [ContinuousMap.add_apply, hF1 z z' h1 h2 h3, hG1 z z' h1 h2 h3]
    · simp only [ContinuousMap.add_apply, hF2 z z' h1 h2 h3, hG2 z z' h1 h2 h3]
  algebraMap_mem' := fun _ => ⟨fun _ _ _ _ _ => rfl, fun _ _ _ _ _ => rfl⟩

/-- Pull back along the first projection: `C(D_V/S_V) → C((D_V/S_V) × (D_W/S_W))`. -/
def pullFst : Kpair V →ₐ[ℂ] prodAlg V W :=
  AlgHom.codRestrict
    ((ContinuousMap.compStarAlgHom' ℂ ℂ (prFst V W)).toAlgHom.comp (Kpair V).val) (prodAlg V W)
    (by
      intro g
      refine ⟨fun z z' h1 h2 _ => ?_, fun z z' _ _ h3 => ?_⟩
      · exact g.2 (prFst V W z) h1 (prFst V W z') h2
      · have : prFst V W z = prFst V W z' := Subtype.ext h3
        simp only [AlgHom.comp_apply, StarAlgHom.coe_toAlgHom,
          ContinuousMap.compStarAlgHom'_apply, ContinuousMap.comp_apply, this])

/-- Pull back along the second projection. -/
def pullSnd : Kpair W →ₐ[ℂ] prodAlg V W :=
  AlgHom.codRestrict
    ((ContinuousMap.compStarAlgHom' ℂ ℂ (prSnd V W)).toAlgHom.comp (Kpair W).val) (prodAlg V W)
    (by
      intro g
      refine ⟨fun z z' _ _ h3 => ?_, fun z z' h1 h2 _ => ?_⟩
      · have : prSnd V W z = prSnd V W z' := Subtype.ext h3
        simp only [AlgHom.comp_apply, StarAlgHom.coe_toAlgHom,
          ContinuousMap.compStarAlgHom'_apply, ContinuousMap.comp_apply, this]
      · exact g.2 (prSnd V W z) h1 (prSnd V W z') h2)

/-- `C(S^a ∧ S^b) ⊆ C(S^a × S^b)`: functions constant on the whole boundary of `D_V × D_W`. -/
def smashIncl : Kpair (V × W) →ₐ[ℂ] prodAlg V W :=
  AlgHom.codRestrict (Kpair (V × W)).val (prodAlg V W)
    (by
      intro g
      have key : ∀ z : Ball (V × W), (‖(z : V × W).1‖ = 1 ∨ ‖(z : V × W).2‖ = 1) → z ∈ bdry (V × W) := by
        intro z hz
        have hz1 := mem_closedBall_zero_iff.mp z.2
        show ‖(z : V × W)‖ = 1
        rcases hz with h | h
        · exact le_antisymm hz1 (h.symm.le.trans (norm_fst_le _))
        · exact le_antisymm hz1 (h.symm.le.trans (norm_snd_le _))
      have hg : ∀ z z' : Ball (V × W), z ∈ bdry (V × W) → z' ∈ bdry (V × W) →
          (g : C(Ball (V × W), ℂ)) z = (g : C(Ball (V × W), ℂ)) z' :=
        fun z z' hz hz' => g.2 z hz z' hz'
      refine ⟨fun z z' h1 h2 _ => ?_, fun z z' h1 h2 _ => ?_⟩
      · exact hg z z' (key z (Or.inl h1)) (key z' (Or.inl h2))
      · exact hg z z' (key z (Or.inr h1)) (key z' (Or.inr h2)))

/-- `μx` is the reduced external product `K̃(S^a) × K̃(S^b) → K̃(S^a ∧ S^b)`, characterised by its
image in `K₀(C(S^a × S^b))`. -/
def IsExtProd (y0V : Ball V) (y0W : Ball W) (y0 : Ball (V × W))
    (μx : K0 (Kpair V) →+ K0 (Kpair W) →+ K0 (Kpair (V × W))) : Prop :=
  ∀ (s : K0 (Kpair V)) (t : K0 (Kpair W)), K0.mapA (augPair V y0V) s = 0 → K0.mapA (augPair W y0W) t = 0 →
    K0.mapA (augPair (V × W) y0) (μx s t) = 0 ∧
    ∀ μ : K0 (prodAlg V W) →+ K0 (prodAlg V W) →+ K0 (prodAlg V W), IsK0Mul μ →
      K0.mapA (smashIncl V W) (μx s t) = μ (K0.mapA (pullFst V W) s) (K0.mapA (pullSnd V W) t)

end Prod

/-! ## The Hopf invariant in K-theory -/

/-- `ℝ^{2m}`. -/
abbrev Eu (m : ℕ) : Type := EuclideanSpace ℝ (Fin (2 * m))

/-- `S^{2m} ⊂ ℝ^{2m+1}`. -/
abbrev Tgt (m : ℕ) : Type := Sph (EuclideanSpace ℝ (Fin (2 * m + 1)))

/-- **`f : S^{4m-1} → S^{2m}` has odd Hopf invariant in K-theory.**  Here `S^{4m-1}` is the
boundary of `D^{2m} × D^{2m}` (the unit sphere of `ℝ^{2m} × ℝ^{2m}` with the sup norm).  There is a
reduced class `a ∈ K̃(C_f)` and a generator `β` of `K̃(C_f / S^{2m}) = K̃(S^{4m})` with
`a² = h · β` in `K(C_f)` for an odd integer `h`. -/
def HopfOddK (m : ℕ) (f : C(Sph (Eu m × Eu m), Tgt m)) : Prop :=
  ∃ (t0 : Tgt m) (y0 : Ball (Eu m × Eu m)) (hy0 : y0 ∈ bdry (Eu m × Eu m))
    (a : K0 (coneAlg f)) (β : K0 (Kpair (Eu m × Eu m))) (h : ℤ),
    Odd h ∧ K0.mapA (augCone f t0) a = 0 ∧ K0.mapA (augPair (Eu m × Eu m) y0) β = 0 ∧
    (∀ w, K0.mapA (augPair (Eu m × Eu m) y0) w = 0 → ∃ k : ℤ, w = k • β) ∧
    ∀ μ : K0 (coneAlg f) →+ K0 (coneAlg f) →+ K0 (coneAlg f), IsK0Mul μ →
      μ a a = h • K0.mapA (relToCone f y0 hy0) β

/-! ## The Bott class on `S² ⊂ ℝ³` -/

/-- The round sphere `S² ⊂ ℝ³`. -/
abbrev S2 : Type := Sph (EuclideanSpace ℝ (Fin 3))

/-- The `i`-th coordinate on the unit sphere of `ℝ^d`, as a complex function. -/
def coordC (d : ℕ) (i : Fin d) : C(Sph (EuclideanSpace ℝ (Fin d)), ℂ) :=
  ⟨fun x => (((x : EuclideanSpace ℝ (Fin d)) i : ℝ) : ℂ), by fun_prop⟩

/-- The tautological (Hopf) line bundle on `S² = ℂP¹`: the rank-one projection
`(1 + x₀σ₁ + x₁σ₂ + x₂σ₃)/2` (Pauli matrices). -/
def hopfIdem : Mat C(S2, ℂ) :=
  ⟨2, algebraMap ℂ C(S2, ℂ) (1 / 2) •
    !![1 + coordC 3 2, coordC 3 0 - algebraMap ℂ C(S2, ℂ) Complex.I * coordC 3 1;
       coordC 3 0 + algebraMap ℂ C(S2, ℂ) Complex.I * coordC 3 1, 1 - coordC 3 2]⟩

end

end Work.KT
