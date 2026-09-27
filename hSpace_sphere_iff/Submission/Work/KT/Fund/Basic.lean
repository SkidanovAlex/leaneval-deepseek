import Mathlib
import Submission.Work.KT.Defs

/-!
# `Work.KT.Fund.Basic` — elementary calculus in the idempotent model of `K₀`

Facts about `cls`, Murray–von Neumann equivalence, block sums, the Kronecker product and
functoriality of `K0.map` that the Bott periodicity proof (`fund_product`) rests on.
-/

namespace Work.KT

open Matrix

noncomputable section

variable {R S T : Type}

section Kernel

variable [Ring R]

/-- `cls p = 0` iff `of p` lies in the relation subgroup. -/
lemma cls_eq_zero_iff (p : Mat R) : cls p = 0 ↔ FreeAbelianGroup.of p ∈ K0Rel R := by
  rw [show cls p = QuotientAddGroup.mk (FreeAbelianGroup.of p) from rfl]
  exact QuotientAddGroup.eq_zero_iff _

/-- `cls p = cls q` iff `of p - of q` lies in the relation subgroup. -/
lemma cls_sub_eq_zero_iff (p q : Mat R) :
    cls p - cls q = 0 ↔ FreeAbelianGroup.of p - FreeAbelianGroup.of q ∈ K0Rel R := by
  show (QuotientAddGroup.mk (FreeAbelianGroup.of p) : K0 R) -
      QuotientAddGroup.mk (FreeAbelianGroup.of q) = 0 ↔ _
  rw [← QuotientAddGroup.mk_sub, QuotientAddGroup.eq_zero_iff]

lemma cls_eq_of_mem {p q : Mat R}
    (h : FreeAbelianGroup.of p - FreeAbelianGroup.of q ∈ K0Rel R) : cls p = cls q := by
  have h' : cls p - cls q = 0 := by
    show (QuotientAddGroup.mk (FreeAbelianGroup.of p) : K0 R) -
        QuotientAddGroup.mk (FreeAbelianGroup.of q) = 0
    rw [← QuotientAddGroup.mk_sub, QuotientAddGroup.eq_zero_iff]
    exact h
  exact sub_eq_zero.mp h'

lemma cls_congr {p q : Mat R} (h : p = q) : cls p = cls q := by subst h; rfl

/-- Non-idempotent generators are zero. -/
lemma cls_eq_zero_of_not_idem (p : Mat R) (hp : ¬ p.IsIdem) : cls p = 0 := by
  rw [show cls p = QuotientAddGroup.mk (FreeAbelianGroup.of p) from rfl,
    QuotientAddGroup.eq_zero_iff]
  exact AddSubgroup.subset_closure (Or.inr ⟨p, hp, rfl⟩)

/-- Murray–von Neumann equivalent idempotents have the same class. -/
lemma cls_eq_of_mvn {p q : Mat R} (hp : p.IsIdem) (hq : q.IsIdem) (h : p.MvN q) :
    cls p = cls q :=
  cls_eq_of_mem (AddSubgroup.subset_closure (Or.inl (Or.inr ⟨p, q, hp, hq, h, rfl⟩)))

/-- The square of the block sum. -/
lemma Mat.sum_mul_self (p q : Mat R) :
    (p.sum q).2 * (p.sum q).2 = Matrix.reindex finSumFinEquiv finSumFinEquiv
      (Matrix.fromBlocks (p.2 * p.2) 0 0 (q.2 * q.2)) := by
  unfold Mat.sum
  simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply,
    Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]

/-- A block sum of matrices is idempotent iff both blocks are. -/
lemma Mat.sum_isIdem_iff {p q : Mat R} : (p.sum q).IsIdem ↔ p.IsIdem ∧ q.IsIdem := by
  have key : (p.sum q).2 * (p.sum q).2 = Matrix.reindex finSumFinEquiv finSumFinEquiv
      (Matrix.fromBlocks (p.2 * p.2) 0 0 (q.2 * q.2)) := Mat.sum_mul_self p q
  have key2 : (p.sum q).2 = Matrix.reindex finSumFinEquiv finSumFinEquiv
      (Matrix.fromBlocks p.2 0 0 q.2) := rfl
  constructor
  · intro h
    unfold Mat.IsIdem at h
    rw [key, key2] at h
    have h2 : Matrix.fromBlocks (p.2 * p.2) 0 0 (q.2 * q.2)
        = Matrix.fromBlocks p.2 0 0 q.2 :=
      (Matrix.reindex finSumFinEquiv finSumFinEquiv).injective h
    rw [Matrix.fromBlocks_inj] at h2
    exact ⟨h2.1, h2.2.2.2⟩
  · rintro ⟨hp, hq⟩
    unfold Mat.IsIdem
    rw [key, key2, hp, hq]

lemma Mat.sum_isIdem {p q : Mat R} (hp : p.IsIdem) (hq : q.IsIdem) : (p.sum q).IsIdem :=
  Mat.sum_isIdem_iff.mpr ⟨hp, hq⟩

/-- Additivity of `cls` on block sums of idempotents. -/
lemma cls_sum {p q : Mat R} (hp : p.IsIdem) (hq : q.IsIdem) :
    cls (p.sum q) = cls p + cls q := by
  have hmem : FreeAbelianGroup.of (p.sum q) - FreeAbelianGroup.of p
      - FreeAbelianGroup.of q ∈ K0Rel R :=
    AddSubgroup.subset_closure (Or.inl (Or.inl ⟨p, q, hp, hq, rfl⟩))
  have h : cls (p.sum q) - cls p - cls q = 0 := by
    show (QuotientAddGroup.mk (FreeAbelianGroup.of (p.sum q)) : K0 R)
        - QuotientAddGroup.mk (FreeAbelianGroup.of p)
        - QuotientAddGroup.mk (FreeAbelianGroup.of q) = 0
    rw [← QuotientAddGroup.mk_sub, ← QuotientAddGroup.mk_sub,
      QuotientAddGroup.eq_zero_iff]
    exact hmem
  have h1 : cls (p.sum q) - cls p = cls q := sub_eq_zero.mp h
  have h2 : cls (p.sum q) = cls p + cls q := by
    rw [← h1]; abel
  exact h2

lemma cls_sum_comm {p q : Mat R} (hp : p.IsIdem) (hq : q.IsIdem) :
    cls (p.sum q) = cls (q.sum p) := by
  rw [cls_sum hp hq, cls_sum hq hp, add_comm]

lemma Mat.MvN_symm {p q : Mat R} (h : p.MvN q) : q.MvN p := by
  obtain ⟨a, b, h1, h2⟩ := h
  exact ⟨b, a, h2, h1⟩

lemma Mat.MvN_refl {p : Mat R} (hp : p.IsIdem) : p.MvN p := ⟨p.2, p.2, hp, hp⟩

lemma Mat.one_isIdem (n : ℕ) : (Mat.one R n).IsIdem := by
  unfold Mat.IsIdem Mat.one
  exact Matrix.one_mul 1

end Kernel

section MapCalc

variable [Ring R] [Ring S] [Ring T]

/-- Matrix multiplication commutes with entrywise application of a ring map. -/
lemma Matrix.map_mul' {α β : Type} [Ring α] [Ring β] (φ : α →+* β)
    {l m n : Type} [Fintype m] (M : Matrix l m α) (N : Matrix m n α) :
    M.map φ * N.map φ = (M * N).map φ := by
  ext i j
  simp [Matrix.mul_apply, map_sum, map_mul]

lemma Mat.map_id (p : Mat R) : p.map (RingHom.id R) = p := rfl

lemma Mat.map_comp (φ : R →+* S) (ψ : S →+* T) (p : Mat R) :
    p.map (ψ.comp φ) = (p.map φ).map ψ := by
  obtain ⟨n, M⟩ := p
  refine Sigma.ext rfl ?_
  show HEq (M.map (ψ.comp φ)) ((M.map φ).map ψ)
  refine heq_of_eq ?_
  ext i j
  rfl

lemma Mat.IsIdem.map {p : Mat R} (φ : R →+* S) (hp : p.IsIdem) : (p.map φ).IsIdem := by
  have hp' : p.2 * p.2 = p.2 := hp
  show p.2.map φ * p.2.map φ = p.2.map φ
  rw [Matrix.map_mul', hp']

/-- Murray–von Neumann equivalence is preserved by ring maps. -/
lemma Mat.MvN_map {p q : Mat R} (φ : R →+* S) (h : p.MvN q) :
    (p.map φ).MvN (q.map φ) := by
  obtain ⟨a, b, h1, h2⟩ := h
  refine ⟨a.map φ, b.map φ, ?_, ?_⟩
  · show b.map φ * a.map φ = p.2.map φ
    rw [Matrix.map_mul', h1]
  · show a.map φ * b.map φ = q.2.map φ
    rw [Matrix.map_mul', h2]

lemma mapCls_of_idem (φ : R →+* S) {p : Mat R} (hp : p.IsIdem) :
    mapCls φ p = cls (p.map φ) := by
  unfold mapCls
  rw [if_pos hp]

lemma K0.map_cls' (φ : R →+* S) (p : Mat R) : K0.map φ (cls p) = mapCls φ p := by
  unfold cls K0.map
  rw [QuotientAddGroup.lift_mk, FreeAbelianGroup.lift_apply_of]

/-- `K0.map` on the class of an idempotent matrix. -/
lemma K0.map_cls (φ : R →+* S) {p : Mat R} (hp : p.IsIdem) :
    K0.map φ (cls p) = cls (p.map φ) := by
  rw [K0.map_cls', mapCls_of_idem φ hp]

lemma K0.map_id_apply (x : K0 R) : K0.map (RingHom.id R) x = x := by
  induction x using QuotientAddGroup.induction_on with
  | _ z =>
    induction z using FreeAbelianGroup.induction_on with
    | zero => simp
    | of p =>
      change K0.map (RingHom.id R) (cls p) = cls p
      rw [K0.map_cls']
      by_cases hp : p.IsIdem
      · rw [mapCls_of_idem _ hp, Mat.map_id]
      · rw [show mapCls (RingHom.id R) p = 0 from by
              unfold mapCls; rw [if_neg hp]]
        exact (cls_eq_zero_of_not_idem p hp).symm
    | neg p ih => rw [QuotientAddGroup.mk_neg, map_neg, ih]
    | add p q ihp ihq => rw [QuotientAddGroup.mk_add, map_add, ihp, ihq]

lemma K0.map_id : K0.map (RingHom.id R) = AddMonoidHom.id (K0 R) :=
  AddMonoidHom.ext K0.map_id_apply

lemma K0.map_comp_apply (φ : R →+* S) (ψ : S →+* T) (x : K0 R) :
    K0.map (ψ.comp φ) x = K0.map ψ (K0.map φ x) := by
  induction x using QuotientAddGroup.induction_on with
  | _ z =>
    induction z using FreeAbelianGroup.induction_on with
    | zero => simp
    | of p =>
      change K0.map (ψ.comp φ) (cls p) = K0.map ψ (K0.map φ (cls p))
      rw [K0.map_cls' (ψ.comp φ) p, K0.map_cls' φ p]
      by_cases hp : p.IsIdem
      · rw [mapCls_of_idem (ψ.comp φ) hp, mapCls_of_idem φ hp,
          K0.map_cls ψ (Mat.IsIdem.map φ hp), Mat.map_comp]
      · rw [show mapCls φ p = 0 from by unfold mapCls; rw [if_neg hp],
            show mapCls (ψ.comp φ) p = 0 from by unfold mapCls; rw [if_neg hp],
            map_zero]
    | neg p ih =>
      rw [QuotientAddGroup.mk_neg]
      simp only [map_neg, ih]
    | add p q ihp ihq =>
      rw [QuotientAddGroup.mk_add]
      simp only [map_add, ihp, ihq]

lemma K0.map_comp (φ : R →+* S) (ψ : S →+* T) :
    K0.map (ψ.comp φ) = (K0.map ψ).comp (K0.map φ) :=
  AddMonoidHom.ext (K0.map_comp_apply φ ψ)

/-- Two homomorphisms out of `K₀` agreeing on generators agree. -/
lemma K0.addHom_ext {M : Type} [AddCommGroup M] {f g : K0 R →+ M}
    (h : ∀ p : Mat R, f (cls p) = g (cls p)) : f = g := by
  refine AddMonoidHom.ext (fun x => ?_)
  induction x using QuotientAddGroup.induction_on with
  | _ z =>
    induction z using FreeAbelianGroup.induction_on with
    | zero =>
      rw [show ((0 : FreeAbelianGroup (Mat R)) : K0 R) = 0 from rfl, map_zero, map_zero]
    | of p => change f (cls p) = g (cls p); exact h p
    | neg p ih =>
      rw [QuotientAddGroup.mk_neg, map_neg]
      simp only [map_neg, ih]
    | add p q ihp ihq =>
      rw [QuotientAddGroup.mk_add, map_add]
      simp only [map_add, ihp, ihq]

end MapCalc

section Product

variable [Ring R]

/-- Value of the ring product of `K₀` on the classes of two idempotents. -/
lemma mulCls_of_idem {p q : Mat R} (hp : p.IsIdem) (hq : q.IsIdem) :
    mulCls p q = cls (p.kron q) := by
  unfold mulCls
  rw [if_pos ⟨hp, hq⟩]

/-- Any `IsK0Mul` product is given by the Kronecker product on generators. -/
lemma IsK0Mul_cls {μ : K0 R →+ K0 R →+ K0 R} (hμ : IsK0Mul μ) {p q : Mat R}
    (hp : p.IsIdem) (hq : q.IsIdem) : μ (cls p) (cls q) = cls (p.kron q) := by
  rw [hμ p q, mulCls_of_idem hp hq]

end Product

end

end Work.KT
