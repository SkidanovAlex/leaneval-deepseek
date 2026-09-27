import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.Basic
import Submission.Work.KT.Fund.Basic
import Submission.Work.KT.mvN_additive
import Submission.Work.KT.mvN_comm
import Submission.Work.KT.mvN_assoc

/-!
# `Work.KT.bott_aux` — `K₀` algebra used by `Work.KT.bott_susp`

Self-contained preparation for the Bott suspension lemma:

* functoriality of `K0.mapA` and of algebra isomorphisms;
* existence of a product `μ` on `K₀` with `IsK0Mul μ` (the existence half of conjunct 1 of the node
  `k0_basic`), so that the multiplicativity hypothesis of `IsExtProd` can be instantiated without
  the (still open) node `k0_basic`;
* naturality of the product (`k0_basic` conjunct 2), proved directly, and the resulting transport
  identity for products along an algebra isomorphism.
-/

namespace Work.KT

open Matrix

noncomputable section

/-! ## Functoriality of `K₀` -/

section Functoriality

variable {A B C : Type} [Ring A] [Ring B] [Ring C] [Algebra ℂ A] [Algebra ℂ B] [Algebra ℂ C]

lemma ba_mapA_comp (φ : A →ₐ[ℂ] B) (ψ : B →ₐ[ℂ] C) :
    K0.mapA (ψ.comp φ) = (K0.mapA ψ).comp (K0.mapA φ) := by
  show K0.map (ψ.comp φ).toRingHom = (K0.map ψ.toRingHom).comp (K0.map φ.toRingHom)
  rw [show (ψ.comp φ).toRingHom = ψ.toRingHom.comp φ.toRingHom from rfl]
  exact K0.map_comp φ.toRingHom ψ.toRingHom

lemma ba_mapA_comp_apply (φ : A →ₐ[ℂ] B) (ψ : B →ₐ[ℂ] C) (x : K0 A) :
    K0.mapA ψ (K0.mapA φ x) = K0.mapA (ψ.comp φ) x := by
  rw [ba_mapA_comp, AddMonoidHom.comp_apply]

lemma ba_mapA_id : K0.mapA (AlgHom.id ℂ A) = AddMonoidHom.id (K0 A) := by
  show K0.map (RingHom.id A) = AddMonoidHom.id (K0 A)
  exact K0.map_id

lemma ba_mapA_id_apply (x : K0 A) : K0.mapA (AlgHom.id ℂ A) x = x := by
  rw [ba_mapA_id]; rfl

lemma ba_mapA_cls (φ : A →ₐ[ℂ] B) {p : Mat A} (hp : p.IsIdem) :
    K0.mapA φ (cls p) = cls (p.map φ.toRingHom) :=
  K0.map_cls φ.toRingHom hp

lemma ba_mapA_cls_mapCls (φ : A →ₐ[ℂ] B) (p : Mat A) :
    K0.mapA φ (cls p) = mapCls φ.toRingHom p :=
  K0.map_cls' φ.toRingHom p

lemma ba_mapA_symm_apply (Φ : A ≃ₐ[ℂ] B) (x : K0 A) :
    K0.mapA (Φ.symm : B →ₐ[ℂ] A) (K0.mapA (Φ : A →ₐ[ℂ] B) x) = x := by
  have hcomp : (Φ.symm : B →ₐ[ℂ] A).comp (Φ : A →ₐ[ℂ] B) = AlgHom.id ℂ A := by
    ext y; simp
  have h2 : (K0.mapA (Φ.symm : B →ₐ[ℂ] A)).comp (K0.mapA (Φ : A →ₐ[ℂ] B)) =
      AddMonoidHom.id (K0 A) := by
    rw [← ba_mapA_comp (Φ : A →ₐ[ℂ] B) (Φ.symm : B →ₐ[ℂ] A), hcomp, ba_mapA_id]
  exact congrFun (congrArg DFunLike.coe h2) x

lemma ba_mapA_apply_symm (Φ : A ≃ₐ[ℂ] B) (x : K0 B) :
    K0.mapA (Φ : A →ₐ[ℂ] B) (K0.mapA (Φ.symm : B →ₐ[ℂ] A) x) = x := by
  have hcomp : (Φ : A →ₐ[ℂ] B).comp (Φ.symm : B →ₐ[ℂ] A) = AlgHom.id ℂ B := by
    ext y; simp
  have h2 : (K0.mapA (Φ : A →ₐ[ℂ] B)).comp (K0.mapA (Φ.symm : B →ₐ[ℂ] A)) =
      AddMonoidHom.id (K0 B) := by
    rw [← ba_mapA_comp (Φ.symm : B →ₐ[ℂ] A) (Φ : A →ₐ[ℂ] B), hcomp, ba_mapA_id]
  exact congrFun (congrArg DFunLike.coe h2) x

lemma ba_mapA_injective (Φ : A ≃ₐ[ℂ] B) : Function.Injective (K0.mapA (Φ : A →ₐ[ℂ] B)) := by
  intro x y h
  rw [← ba_mapA_symm_apply Φ x, ← ba_mapA_symm_apply Φ y, h]

end Functoriality

/-! ## Products on `K₀` -/

section Product

variable {R : Type} [Ring R]

/-- On generators, `mulCls p q` is additive in the second variable. -/
lemma ba_mulCls_sum_right (hcR : ∀ x y : R, x * y = y * x) (p : Mat R) {q q' : Mat R}
    (hq : q.IsIdem) (hq' : q'.IsIdem) :
    mulCls p (q.sum q') = mulCls p q + mulCls p q' := by
  by_cases hp : p.IsIdem
  · have hsum : (q.sum q').IsIdem := Mat.sum_idem hq hq'
    have h1 : mulCls p (q.sum q') = cls (p.kron (q.sum q')) := by
      unfold mulCls; rw [if_pos ⟨hp, hsum⟩]
    have h2 : mulCls p q = cls (p.kron q) := by
      unfold mulCls; rw [if_pos ⟨hp, hq⟩]
    have h3 : mulCls p q' = cls (p.kron q') := by
      unfold mulCls; rw [if_pos ⟨hp, hq'⟩]
    have hk1 : (p.kron q).IsIdem := Mat.kron_idem hcR hp hq
    have hk2 : (p.kron q').IsIdem := Mat.kron_idem hcR hp hq'
    rw [h1, h2, h3,
      cls_eq_of_mvn (Mat.kron_idem hcR hp hsum) (Mat.sum_idem hk1 hk2)
        (mvN_additive.1 R p q q'), cls_sum hk1 hk2]
  · have h0 : mulCls p (q.sum q') = 0 := by
      unfold mulCls; rw [if_neg (fun h => hp h.1)]
    have h0a : mulCls p q = 0 := by unfold mulCls; rw [if_neg (fun h => hp h.1)]
    have h0b : mulCls p q' = 0 := by unfold mulCls; rw [if_neg (fun h => hp h.1)]
    rw [h0, h0a, h0b, add_zero]

/-- On generators, `mulCls p q` is additive in the first variable. -/
lemma ba_mulCls_sum_left (hcR : ∀ x y : R, x * y = y * x) {p p' : Mat R} (q : Mat R)
    (hp : p.IsIdem) (hp' : p'.IsIdem) :
    mulCls (p.sum p') q = mulCls p q + mulCls p' q := by
  by_cases hq : q.IsIdem
  · have hsum : (p.sum p').IsIdem := Mat.sum_idem hp hp'
    have h1 : mulCls (p.sum p') q = cls ((p.sum p').kron q) := by
      unfold mulCls; rw [if_pos ⟨hsum, hq⟩]
    have h2 : mulCls p q = cls (p.kron q) := by
      unfold mulCls; rw [if_pos ⟨hp, hq⟩]
    have h3 : mulCls p' q = cls (p'.kron q) := by
      unfold mulCls; rw [if_pos ⟨hp', hq⟩]
    have hk1 : (p.kron q).IsIdem := Mat.kron_idem hcR hp hq
    have hk2 : (p'.kron q).IsIdem := Mat.kron_idem hcR hp' hq
    rw [h1, h2, h3,
      cls_eq_of_mvn (Mat.kron_idem hcR hsum hq) (Mat.sum_idem hk1 hk2)
        (mvN_additive.2 R p p' q), cls_sum hk1 hk2]
  · have h0 : mulCls (p.sum p') q = 0 := by
      unfold mulCls; rw [if_neg (fun h => hq h.2)]
    have h0a : mulCls p q = 0 := by unfold mulCls; rw [if_neg (fun h => hq h.2)]
    have h0b : mulCls p' q = 0 := by unfold mulCls; rw [if_neg (fun h => hq h.2)]
    rw [h0, h0a, h0b, add_zero]

/-- On generators, `mulCls p q` only depends on the `MvN` class of the second variable. -/
lemma ba_mulCls_mvN_right (hcR : ∀ x y : R, x * y = y * x) (p : Mat R) {q q' : Mat R}
    (hq : q.IsIdem) (hq' : q'.IsIdem) (hmv : q.MvN q') :
    mulCls p q = mulCls p q' := by
  by_cases hp : p.IsIdem
  · have h2 : mulCls p q = cls (p.kron q) := by unfold mulCls; rw [if_pos ⟨hp, hq⟩]
    have h3 : mulCls p q' = cls (p.kron q') := by unfold mulCls; rw [if_pos ⟨hp, hq'⟩]
    rw [h2, h3,
      cls_eq_of_mvn (Mat.kron_idem hcR hp hq) (Mat.kron_idem hcR hp hq')
        (mvN_kron_right hcR hmv hp)]
  · have h0 : mulCls p q = 0 := by unfold mulCls; rw [if_neg (fun h => hp h.1)]
    have h0b : mulCls p q' = 0 := by unfold mulCls; rw [if_neg (fun h => hp h.1)]
    rw [h0, h0b]

/-- On generators, `mulCls p q` only depends on the `MvN` class of the first variable. -/
lemma ba_mulCls_mvN_left (hcR : ∀ x y : R, x * y = y * x) {p p' : Mat R} (q : Mat R)
    (hp : p.IsIdem) (hp' : p'.IsIdem) (hmv : p.MvN p') :
    mulCls p q = mulCls p' q := by
  by_cases hq : q.IsIdem
  · have h2 : mulCls p q = cls (p.kron q) := by unfold mulCls; rw [if_pos ⟨hp, hq⟩]
    have h3 : mulCls p' q = cls (p'.kron q) := by unfold mulCls; rw [if_pos ⟨hp', hq⟩]
    rw [h2, h3,
      cls_eq_of_mvn (Mat.kron_idem hcR hp hq) (Mat.kron_idem hcR hp' hq)
        (mvN_kron_left hcR hmv hq)]
  · have h0 : mulCls p q = 0 := by unfold mulCls; rw [if_neg (fun h => hq h.2)]
    have h0b : mulCls p' q = 0 := by unfold mulCls; rw [if_neg (fun h => hq h.2)]
    rw [h0, h0b]

/-- The kernel condition for the descent of `q ↦ mulCls p q`. -/
lemma baMulQ_ker (hcR : ∀ x y : R, x * y = y * x) (p : Mat R) :
    K0Rel R ≤ (FreeAbelianGroup.lift (fun q : Mat R => mulCls p q)).ker := by
  unfold K0Rel
  rw [AddSubgroup.closure_le]
  rintro x ((⟨q, q', hq, hq', rfl⟩ | ⟨q, q', hq, hq', hmv, rfl⟩) | ⟨q, hq, rfl⟩)
  · show (FreeAbelianGroup.lift (fun q : Mat R => mulCls p q))
        (FreeAbelianGroup.of (q.sum q') - FreeAbelianGroup.of q - FreeAbelianGroup.of q') = 0
    rw [map_sub, map_sub, FreeAbelianGroup.lift_apply_of, FreeAbelianGroup.lift_apply_of,
      FreeAbelianGroup.lift_apply_of, ba_mulCls_sum_right hcR p hq hq']
    abel
  · show (FreeAbelianGroup.lift (fun q : Mat R => mulCls p q))
        (FreeAbelianGroup.of q - FreeAbelianGroup.of q') = 0
    rw [map_sub, FreeAbelianGroup.lift_apply_of, FreeAbelianGroup.lift_apply_of,
      ba_mulCls_mvN_right hcR p hq hq' hmv]
    abel
  · show (FreeAbelianGroup.lift (fun q : Mat R => mulCls p q)) (FreeAbelianGroup.of q) = 0
    rw [FreeAbelianGroup.lift_apply_of]
    unfold mulCls
    rw [if_neg (fun h => hq h.2)]

/-- For fixed `p`, the map `q ↦ mulCls p q` descends to `K₀`. -/
def baMulQ (hcR : ∀ x y : R, x * y = y * x) (p : Mat R) : K0 R →+ K0 R :=
  QuotientAddGroup.lift (K0Rel R) (FreeAbelianGroup.lift (fun q : Mat R => mulCls p q))
    (baMulQ_ker hcR p)

lemma baMulQ_cls (hcR : ∀ x y : R, x * y = y * x) (p q : Mat R) :
    baMulQ hcR p (cls q) = mulCls p q := by
  change QuotientAddGroup.lift (K0Rel R) (FreeAbelianGroup.lift (fun q : Mat R => mulCls p q))
    (baMulQ_ker hcR p) (QuotientAddGroup.mk (FreeAbelianGroup.of q)) = mulCls p q
  rw [QuotientAddGroup.lift_mk, FreeAbelianGroup.lift_apply_of]

/-- The kernel condition for the descent of `p ↦ baMulQ hcR p`. -/
lemma baMulOuter_ker (hcR : ∀ x y : R, x * y = y * x) :
    K0Rel R ≤ (FreeAbelianGroup.lift (baMulQ hcR)).ker := by
  unfold K0Rel
  rw [AddSubgroup.closure_le]
  rintro x ((⟨p, p', hp, hp', rfl⟩ | ⟨p, p', hp, hp', hmv, rfl⟩) | ⟨p, hp, rfl⟩)
  · have h : baMulQ hcR (p.sum p') = baMulQ hcR p + baMulQ hcR p' := by
      refine K0.addHom_ext (fun q => ?_)
      rw [baMulQ_cls, AddMonoidHom.add_apply, baMulQ_cls, baMulQ_cls,
        ba_mulCls_sum_left hcR q hp hp']
    show (FreeAbelianGroup.lift (baMulQ hcR))
        (FreeAbelianGroup.of (p.sum p') - FreeAbelianGroup.of p - FreeAbelianGroup.of p') = 0
    rw [map_sub, map_sub, FreeAbelianGroup.lift_apply_of, FreeAbelianGroup.lift_apply_of,
      FreeAbelianGroup.lift_apply_of, h]
    abel
  · have h : baMulQ hcR p = baMulQ hcR p' := by
      refine K0.addHom_ext (fun q => ?_)
      rw [baMulQ_cls, baMulQ_cls, ba_mulCls_mvN_left hcR q hp hp' hmv]
    show (FreeAbelianGroup.lift (baMulQ hcR))
        (FreeAbelianGroup.of p - FreeAbelianGroup.of p') = 0
    rw [map_sub, FreeAbelianGroup.lift_apply_of, FreeAbelianGroup.lift_apply_of, h]
    abel
  · have h : baMulQ hcR p = 0 := by
      refine K0.addHom_ext (fun q => ?_)
      rw [baMulQ_cls]
      unfold mulCls
      rw [if_neg (fun hh => hp hh.1), AddMonoidHom.zero_apply]
    show (FreeAbelianGroup.lift (baMulQ hcR)) (FreeAbelianGroup.of p) = 0
    rw [FreeAbelianGroup.lift_apply_of, h]

/-- **Existence of the product on `K₀`**: for a commutative ring `A` there is a product
`μ : K₀ A →+ K₀ A →+ K₀ A` with `IsK0Mul μ`. -/
theorem ba_exists_isK0Mul (A : Type) [Ring A] (hcA : ∀ x y : A, x * y = y * x) :
    ∃ μ : K0 A →+ K0 A →+ K0 A, IsK0Mul μ := by
  let F : FreeAbelianGroup (Mat A) →+ (K0 A →+ K0 A) :=
    FreeAbelianGroup.lift (fun p : Mat A => baMulQ hcA p)
  have hF : K0Rel A ≤ F.ker := baMulOuter_ker hcA
  let μ : K0 A →+ K0 A →+ K0 A := QuotientAddGroup.lift (K0Rel A) F hF
  refine ⟨μ, ?_⟩
  intro p q
  have h1 : μ (cls p) = baMulQ hcA p := by
    change QuotientAddGroup.lift (K0Rel A) F hF
      (QuotientAddGroup.mk (FreeAbelianGroup.of p)) = baMulQ hcA p
    rw [QuotientAddGroup.lift_mk]
    show F (FreeAbelianGroup.of p) = baMulQ hcA p
    rw [show F = FreeAbelianGroup.lift (fun p : Mat A => baMulQ hcA p) from rfl,
      FreeAbelianGroup.lift_apply_of]
  rw [h1, baMulQ_cls]

end Product

/-! ## Naturality of the product, and its transport along an algebra isomorphism -/

/-- Conjunct 2 of `k0_basic`, proved directly: the product on `K₀` is natural. -/
theorem ba_k0_mul_natural (A B : Type) [Ring A] [Ring B] (φ : A →+* B)
    (μA : K0 A →+ K0 A →+ K0 A) (μB : K0 B →+ K0 B →+ K0 B)
    (hcA : ∀ x y : A, x * y = y * x) (hA : IsK0Mul μA) (hB : IsK0Mul μB) :
    ∀ a b, K0.map φ (μA a b) = μB (K0.map φ a) (K0.map φ b) := by
  have hmap : ∀ p : Mat A, K0.map φ (cls p) = mapCls φ p := by
    intro p
    simp only [K0.map, cls, QuotientAddGroup.lift_mk, FreeAbelianGroup.lift_apply_of]
  have hkron : ∀ p q : Mat A, (p.kron q).map φ = (p.map φ).kron (q.map φ) :=
    fun p q => Mat.map_kron φ p q
  have hidem : ∀ p : Mat A, p.IsIdem → (p.map φ).IsIdem := fun p hp => Mat.IsIdem.map φ hp
  have hkidem : ∀ p q : Mat A, p.IsIdem → q.IsIdem → (p.kron q).IsIdem := by
    intro p q hp hq
    let _ : CommRing A := { ‹Ring A› with mul_comm := hcA }
    unfold Mat.IsIdem Mat.kron kronMat at *
    simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv]
    rw [← Matrix.mul_kronecker_mul, hp, hq]
  have gen : ∀ p q : Mat A, K0.map φ (μA (cls p) (cls q)) =
      μB (K0.map φ (cls p)) (K0.map φ (cls q)) := by
    intro p q
    rw [hA, hmap, hmap]
    by_cases hp : p.IsIdem
    · by_cases hq : q.IsIdem
      · simp only [mulCls, mapCls, if_pos (And.intro hp hq), if_pos hp, if_pos hq]
        rw [hmap, mapCls, if_pos (hkidem p q hp hq), hB, mulCls,
          if_pos (And.intro (hidem p hp) (hidem q hq)), hkron]
      · simp [mulCls, mapCls, hp, hq]
    · simp [mulCls, mapCls, hp]
  intro a b
  induction a using QuotientAddGroup.induction_on with
  | H x =>
  induction b using QuotientAddGroup.induction_on with
  | H y =>
  induction x using FreeAbelianGroup.induction_on with
  | zero => simp
  | of p =>
    induction y using FreeAbelianGroup.induction_on with
    | zero => simp
    | of q => exact gen p q
    | neg q ih => simpa using ih
    | add q r ih1 ih2 => simp only [QuotientAddGroup.mk_add, map_add] at ih1 ih2 ⊢; rw [ih1, ih2]
  | neg p ih => simp only [QuotientAddGroup.mk_neg, map_neg, AddMonoidHom.neg_apply] at ih ⊢; rw [ih]
  | add p r ih1 ih2 =>
    simp only [QuotientAddGroup.mk_add, map_add, AddMonoidHom.add_apply] at ih1 ih2 ⊢; rw [ih1, ih2]

section Transport

variable {A B : Type} [Ring A] [Ring B] [Algebra ℂ A] [Algebra ℂ B]

/-- **Transport of a product along an algebra isomorphism**: the products on `K₀ A` and `K₀ B`
correspond to one another under the equivalence induced by `A ≃ₐ[ℂ] B`. -/
lemma ba_conjMul_eq (Φ : A ≃ₐ[ℂ] B) (hcA : ∀ x y : A, x * y = y * x)
    (μA : K0 A →+ K0 A →+ K0 A) (hA : IsK0Mul μA)
    (μB : K0 B →+ K0 B →+ K0 B) (hB : IsK0Mul μB) (x y : K0 A) :
    μA x y = K0.mapA (Φ.symm : B →ₐ[ℂ] A)
      (μB (K0.mapA (Φ : A →ₐ[ℂ] B) x) (K0.mapA (Φ : A →ₐ[ℂ] B) y)) := by
  have key : ∀ u v : K0 B, μA (K0.mapA (Φ.symm : B →ₐ[ℂ] A) u)
        (K0.mapA (Φ.symm : B →ₐ[ℂ] A) v) =
      K0.mapA (Φ.symm : B →ₐ[ℂ] A) (μB u v) := by
    intro u v
    have h := ba_k0_mul_natural A B (Φ : A →ₐ[ℂ] B).toRingHom μA μB hcA hA hB
      (K0.mapA (Φ.symm : B →ₐ[ℂ] A) u) (K0.mapA (Φ.symm : B →ₐ[ℂ] A) v)
    rw [ba_mapA_apply_symm, ba_mapA_apply_symm] at h
    have h2 := congrArg (K0.mapA (Φ.symm : B →ₐ[ℂ] A)) h
    rwa [ba_mapA_symm_apply] at h2
  have h4 := key (K0.mapA (Φ : A →ₐ[ℂ] B) x) (K0.mapA (Φ : A →ₐ[ℂ] B) y)
  rwa [ba_mapA_symm_apply, ba_mapA_symm_apply] at h4

end Transport

end

end Work.KT

namespace Work.KT

open Matrix

section ConstHelpers

variable {A B : Type} [Ring A] [Ring B] [Algebra ℂ A] [Algebra ℂ B]

/-- The classes of the constant functions are natural. -/
lemma ba_const_natural (φ : A →ₐ[ℂ] B) (x : K0 ℂ) :
    K0.mapA φ (K0.mapA (Algebra.ofId ℂ A) x) = K0.mapA (Algebra.ofId ℂ B) x := by
  have hcomp : φ.comp (Algebra.ofId ℂ A) = Algebra.ofId ℂ B :=
    AlgHom.ext (fun c => by simp)
  rw [ba_mapA_comp_apply (Algebra.ofId ℂ A) φ, hcomp]

/-- The augmentation of a constant class is the class itself. -/
lemma ba_mapA_aug_ofId (χ : A →ₐ[ℂ] ℂ) (x : K0 ℂ) :
    K0.mapA χ (K0.mapA (Algebra.ofId ℂ A) x) = x := by
  have hcomp : χ.comp (Algebra.ofId ℂ A) = AlgHom.id ℂ ℂ :=
    AlgHom.ext (fun c => by simp)
  rw [ba_mapA_comp_apply (Algebra.ofId ℂ A) χ, hcomp]
  exact ba_mapA_id_apply x

/-- Subtracting the constant class of the augmentation gives a reduced class. -/
lemma ba_reduced_sub_const (χ : A →ₐ[ℂ] ℂ) (x : K0 A) :
    K0.mapA χ (x - K0.mapA (Algebra.ofId ℂ A) (K0.mapA χ x)) = 0 := by
  rw [map_sub, ba_mapA_aug_ofId, sub_self]

end ConstHelpers

end Work.KT
