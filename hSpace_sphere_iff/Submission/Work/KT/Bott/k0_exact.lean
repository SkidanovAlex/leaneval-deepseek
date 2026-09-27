import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.Basic
import Submission.Work.KT.cls_eq_stable_mvN
import Submission.Work.KT.k0_rep
import Submission.Work.KT.rel_cancel
import Submission.Work.KT.sum_mvN_congr
import Submission.Work.KT.sum_mvN_assoc
import Submission.Work.KT.Bott.patch_idem_dim
import Submission.Work.KT.Bott.k0_mv_inj

/-!
# Exactness of `K₀` (algebraic, Milnor)

Assembly of `Work.KT.Bott.k0_exact` from

* `Work.KT.cls_eq_stable_mvN` — equal classes are stable Murray–von Neumann equivalence,
* `Work.KT.k0_rep` — normal form of elements of `K₀`,
* `Work.KT.Bott.patch_idem_dim` — Milnor patching of idempotents (Mayer–Vietoris surjectivity),
* `Work.KT.Bott.k0_mv_inj` — the injectivity half of Mayer–Vietoris under stable lifting.

Conjuncts (1)(a) and (1)(b) are the instantiations of the general Mayer–Vietoris statements at the
cartesian square `U → ℂ`, `U → A`, `ℂ → B`, `A → B`; conjunct (3) is the general statement.
-/

namespace Work.KT.Bott

open Matrix

noncomputable section

/-! ## Elementary lemmas about `cls`, `Mat.map` and identity blocks -/

section Elementary

variable {R S : Type} [Ring R] [Ring S]

/-- `K₀.map` on the class of an idempotent. -/
lemma map_cls (φ : R →+* S) (p : Mat R) (hp : p.IsIdem) :
    K0.map φ (cls p) = cls (p.map φ) := by
  have h : K0.map φ (cls p) = mapCls φ p := by
    rw [show K0.map φ = QuotientAddGroup.lift (K0Rel R) (FreeAbelianGroup.lift (mapCls φ)) _
        from rfl]
    rw [show cls p = QuotientAddGroup.mk (FreeAbelianGroup.of p) from rfl]
    rw [QuotientAddGroup.lift_mk, FreeAbelianGroup.lift_apply_of]
  rw [h, mapCls, if_pos hp]

/-- The identity matrix maps to the identity matrix. -/
lemma mat_map_one (φ : R →+* S) (k : ℕ) : (Mat.one R k).map φ = Mat.one S k := by
  unfold Mat.one Mat.map
  simp

/-- `Mat.map` commutes with block sums. -/
lemma mat_map_sum (φ : R →+* S) (p q : Mat R) :
    (p.sum q).map φ = (p.map φ).sum (q.map φ) := by
  obtain ⟨m, M⟩ := p
  obtain ⟨n, N⟩ := q
  refine Sigma.ext rfl ?_
  simp only [Mat.map, Mat.sum, heq_eq_eq]
  ext i j
  rcases hi : finSumFinEquiv.symm i with a | a <;> rcases hj : finSumFinEquiv.symm j with b | b <;>
    simp [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.map_apply, Matrix.fromBlocks,
      hi, hj]

/-- `Mat.map` commutes with reindexing. -/
lemma map_reindex_h (φ : R →+* S) {m n : Type} (e : m ≃ n) (M : Matrix m m R) :
    (Matrix.reindex e e M).map φ = Matrix.reindex e e (M.map φ) := by
  ext i j
  simp [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.map_apply]

/-- `Mat.map` commutes with the block diagonal of a matrix and an identity. -/
lemma mat_map_fromBlocks_one (φ : R →+* S) {m n : Type} [DecidableEq m] [DecidableEq n]
    [Fintype m] [Fintype n] (M : Matrix m m R) :
    (Matrix.fromBlocks M 0 0 (1 : Matrix n n R)).map φ =
      Matrix.fromBlocks (M.map φ) 0 0 (1 : Matrix n n S) := by
  ext i j
  rcases i with a | a <;> rcases j with b | b <;>
    simp [Matrix.fromBlocks, Matrix.map_apply, Matrix.one_apply, map_one, map_zero]

/-- Entrywise image of a matrix stabilised by identity blocks (on the underlying matrices). -/
lemma mat_sum_map_snd (φ : R →+* S) (p : Mat R) (k : ℕ) :
    (p.sum (Mat.one R k)).2.map φ = ((p.map φ).sum (Mat.one S k)).2 := by
  show (Matrix.reindex finSumFinEquiv finSumFinEquiv
      (Matrix.fromBlocks p.2 0 0 (1 : Matrix (Fin k) (Fin k) R))).map φ =
    Matrix.reindex finSumFinEquiv finSumFinEquiv
      (Matrix.fromBlocks (p.2.map φ) 0 0 (1 : Matrix (Fin k) (Fin k) S))
  rw [map_reindex_h, mat_map_fromBlocks_one]

/-- The identity matrix is idempotent. -/
lemma one_idem (k : ℕ) : (Mat.one R k).IsIdem := by
  unfold Mat.IsIdem Mat.one
  simp

/-- A block sum of identity matrices is an identity matrix. -/
lemma one_sum (m n : ℕ) : (Mat.one R m).sum (Mat.one R n) = Mat.one R (m + n) := by
  have hfb : Matrix.fromBlocks (1 : Matrix (Fin m) (Fin m) R) 0 0
      (1 : Matrix (Fin n) (Fin n) R) = 1 := Matrix.fromBlocks_one
  have hri : Matrix.reindex finSumFinEquiv finSumFinEquiv
      (1 : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) R) = 1 := by
    ext i j
    rw [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.one_apply, Matrix.one_apply]
    by_cases h : i = j
    · subst h; simp
    · have h' : finSumFinEquiv.symm i ≠ finSumFinEquiv.symm j :=
        fun hh => h (finSumFinEquiv.symm.injective hh)
      simp [h, h']
  unfold Mat.one Mat.sum
  rw [hfb, hri]

/-- Classes of identity matrices are additive. -/
lemma cls_one_add (m n : ℕ) :
    cls (Mat.one R (m + n)) = cls (Mat.one R m) + cls (Mat.one R n) := by
  rw [← one_sum m n, cls_sum (one_idem m) (one_idem n)]

/-- Shifting a normal form by identity blocks. -/
lemma shift_rep {F : Mat R} {n m : ℕ} (hF : F.IsIdem) :
    cls F - cls (Mat.one R n) = cls (F.sum (Mat.one R m)) - cls (Mat.one R (n + m)) := by
  rw [cls_sum hF (one_idem m), cls_one_add n m]
  abel

end Elementary

/-! ## Mayer–Vietoris surjectivity -/

/-- **Surjectivity onto the fibre product** for a cartesian square with `σ₂` surjective. -/
lemma mv_surj {P P₁ P₂ Q : Type} [Ring P] [Ring P₁] [Ring P₂] [Ring Q]
    (ρ₁ : P →+* P₁) (ρ₂ : P →+* P₂) (σ₁ : P₁ →+* Q) (σ₂ : P₂ →+* Q)
    (hs : Function.Surjective σ₂) (hcomm : σ₁.comp ρ₁ = σ₂.comp ρ₂)
    (hpb : ∀ x₁ x₂, σ₁ x₁ = σ₂ x₂ → ∃! x, ρ₁ x = x₁ ∧ ρ₂ x = x₂) :
    ∀ z₁ z₂, K0.map σ₁ z₁ = K0.map σ₂ z₂ → ∃ z, K0.map ρ₁ z = z₁ ∧ K0.map ρ₂ z = z₂ := by
  intro z₁ z₂ hz
  obtain ⟨F₁, n₁, hid₁, hz₁⟩ := k0_rep z₁
  obtain ⟨F₂, n₂, hid₂, hz₂⟩ := k0_rep z₂
  -- shift so that both negative parts are the identity of size `n₁ + n₂`
  have hz₁' : z₁ = cls (F₁.sum (Mat.one P₁ n₂)) - cls (Mat.one P₁ (n₁ + n₂)) := by
    rw [hz₁, shift_rep (R := P₁) (n := n₁) hid₁ (m := n₂)]
  have hz₂' : z₂ = cls (F₂.sum (Mat.one P₂ n₁)) - cls (Mat.one P₂ (n₁ + n₂)) := by
    have h := shift_rep (R := P₂) (n := n₂) hid₂ (m := n₁)
    rw [hz₂, h, Nat.add_comm n₂ n₁]
  -- the stabilised idempotents
  set E₁ : Mat P₁ := F₁.sum (Mat.one P₁ n₂) with hE₁
  set E₂ : Mat P₂ := F₂.sum (Mat.one P₂ n₁) with hE₂
  have hidE₁ : E₁.IsIdem := Mat.sum_idem hid₁ (one_idem n₂)
  have hidE₂ : E₂.IsIdem := Mat.sum_idem hid₂ (one_idem n₁)
  -- the class condition after stabilising
  have hz' : K0.map σ₁ (cls E₁ - cls (Mat.one P₁ (n₁ + n₂))) =
      K0.map σ₂ (cls E₂ - cls (Mat.one P₂ (n₁ + n₂))) := by
    rw [← hz₁', ← hz₂']
    exact hz
  have hcls1 : K0.map σ₁ (cls E₁ - cls (Mat.one P₁ (n₁ + n₂))) =
      cls (E₁.map σ₁) - cls (Mat.one Q (n₁ + n₂)) := by
    rw [map_sub, map_cls σ₁ E₁ hidE₁, map_cls σ₁ (Mat.one P₁ (n₁ + n₂)) (one_idem _),
      mat_map_one]
  have hcls2 : K0.map σ₂ (cls E₂ - cls (Mat.one P₂ (n₁ + n₂))) =
      cls (E₂.map σ₂) - cls (Mat.one Q (n₁ + n₂)) := by
    rw [map_sub, map_cls σ₂ E₂ hidE₂, map_cls σ₂ (Mat.one P₂ (n₁ + n₂)) (one_idem _),
      mat_map_one]
  have hcl : cls (E₁.map σ₁) = cls (E₂.map σ₂) := by
    rw [hcls1, hcls2] at hz'
    have h := congrArg (fun x => x + cls (Mat.one Q (n₁ + n₂))) hz'
    simpa using h
  -- stable Murray–von Neumann data over `Q`
  obtain ⟨s, S, T, hTS, hST⟩ :=
    (cls_eq_stable_mvN (E₁.map σ₁) (E₂.map σ₂) (Mat.map_idem σ₁ hidE₁)
      (Mat.map_idem σ₂ hidE₂)).mp hcl
  -- the glueing
  have hmat₁ : (E₁.sum (Mat.one P₁ s)).2.map σ₁ = ((E₁.map σ₁).sum (Mat.one Q s)).2 :=
    mat_sum_map_snd σ₁ E₁ s
  have hmat₂ : (E₂.sum (Mat.one P₂ s)).2.map σ₂ = ((E₂.map σ₂).sum (Mat.one Q s)).2 :=
    mat_sum_map_snd σ₂ E₂ s
  have hTS' : T * S = ((E₁.sum (Mat.one P₁ s)).map σ₁).2 := hTS.trans hmat₁.symm
  have hST' : S * T = ((E₂.sum (Mat.one P₂ s)).map σ₂).2 := hST.trans hmat₂.symm
  obtain ⟨Ê, hidÊ, hÊ₁, hÊ₂⟩ :=
    patch_idem_dim (ρ₁ := ρ₁) (ρ₂ := ρ₂) (σ₁ := σ₁) (σ₂ := σ₂) hs hcomm hpb
      (e₁ := (E₁.sum (Mat.one P₁ s)).2) (e₂ := (E₂.sum (Mat.one P₂ s)).2)
      (Mat.sum_idem hidE₁ (one_idem s)) (Mat.sum_idem hidE₂ (one_idem s)) S T hST' hTS'
  have hÊ₁' : cls (Ê.map ρ₁) = cls (E₁.sum (Mat.one P₁ s)) := hÊ₁
  have hÊ₂' : cls (Ê.map ρ₂) = cls (E₂.sum (Mat.one P₂ s)) := hÊ₂
  refine ⟨cls Ê - cls (Mat.one P (n₁ + n₂ + s)), ?_, ?_⟩
  · rw [map_sub, map_cls ρ₁ Ê hidÊ, map_cls ρ₁ (Mat.one P (n₁ + n₂ + s)) (one_idem _), mat_map_one,
      hÊ₁', cls_sum hidE₁ (one_idem s), cls_one_add (n₁ + n₂) s]
    rw [hz₁']
    abel
  · rw [map_sub, map_cls ρ₂ Ê hidÊ, map_cls ρ₂ (Mat.one P (n₁ + n₂ + s)) (one_idem _), mat_map_one,
      hÊ₂', cls_sum hidE₂ (one_idem s), cls_one_add (n₁ + n₂) s]
    rw [hz₂']
    abel

/-! ## The cartesian square attached to a surjection with `U = ℂ·1 + ker π` -/

/-- Commutativity of the square `U → ℂ`, `U → A`, `ℂ → B`, `A → B`. -/
lemma square_comm {A B : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B]
    (π : A →ₐ[ℂ] B) (U : Subalgebra ℂ A) (ε : U →ₐ[ℂ] ℂ)
    (hε : ∀ u : U, π u = algebraMap ℂ B (ε u)) :
    (algebraMap ℂ B).comp ε.toRingHom = π.toRingHom.comp U.val.toRingHom := by
  ext u
  exact (hε u).symm

/-- The square `U → ℂ`, `U → A`, `ℂ → B`, `A → B` is cartesian. -/
lemma square_pull {A B : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] [Nontrivial B]
    (π : A →ₐ[ℂ] B) (U : Subalgebra ℂ A)
    (hU : ∀ r : A, r ∈ U ↔ ∃ c : ℂ, π r = algebraMap ℂ B c)
    (ε : U →ₐ[ℂ] ℂ) (hε : ∀ u : U, π u = algebraMap ℂ B (ε u)) :
    ∀ x₁ : ℂ, ∀ x₂ : A, algebraMap ℂ B x₁ = π x₂ →
      ∃! u : U, ε u = x₁ ∧ U.val u = x₂ := by
  have hinj : Function.Injective (algebraMap ℂ B) := by
    intro a b hab
    by_contra hne
    have hne' : a - b ≠ 0 := sub_ne_zero.mpr hne
    have h : algebraMap ℂ B (a - b) = 0 := by rw [map_sub, hab, sub_self]
    have hz : algebraMap ℂ B ((a - b)⁻¹) * algebraMap ℂ B (a - b) = 1 := by
      rw [← map_mul, inv_mul_cancel₀ hne', map_one]
    rw [h, mul_zero] at hz
    exact zero_ne_one hz
  intro x₁ x₂ h
  have hmem : x₂ ∈ U := (hU x₂).mpr ⟨x₁, h.symm⟩
  refine ⟨⟨x₂, hmem⟩, ⟨?_, rfl⟩, ?_⟩
  · have h1 : π (⟨x₂, hmem⟩ : U) = algebraMap ℂ B (ε ⟨x₂, hmem⟩) := hε _
    have h2 : π x₂ = algebraMap ℂ B x₁ := h.symm
    exact hinj (h1.symm.trans h2)
  · intro u hu
    exact Subtype.ext hu.2

/-! ## The theorem -/

/-- Exactness of `K₀` (algebraic, Milnor): (1) for a surjection `π : A → B` with `U = ℂ·1 + ker π`,
`K₀(ker π) → K₀(A) → K₀(B)` is exact in the middle; (2) if every invertible matrix over `B`
stably lifts to an invertible matrix over `A`, then `K₀(ker π) → K₀(A)` is injective; (3) the
Mayer–Vietoris property of `K₀` for a Milnor square (pull-back with one surjective leg). -/
theorem k0_exact :
    (∀ (A B : Type) [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] [Nontrivial B]
      (π : A →ₐ[ℂ] B), Function.Surjective π →
      ∀ (U : Subalgebra ℂ A), (∀ r : A, r ∈ U ↔ ∃ c : ℂ, π r = algebraMap ℂ B c) →
      ∀ (ε : U →ₐ[ℂ] ℂ), (∀ u : U, π u = algebraMap ℂ B (ε u)) →
      (∀ z : K0 A, K0.mapA π z = 0 →
        ∃ w : K0 U, K0.mapA ε w = 0 ∧ K0.mapA U.val w = z) ∧
      ((∀ (n : ℕ) (u : Matrix (Fin n) (Fin n) B), IsUnit u →
          ∃ (k : ℕ) (v : Matrix (Fin (n + k)) (Fin (n + k)) A), IsUnit v ∧
            v.map π = Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks u 0 0 1)) →
        ∀ w : K0 U, K0.mapA ε w = 0 → K0.mapA U.val w = 0 → w = 0)) ∧
    ∀ (P P₁ P₂ Q : Type) [Ring P] [Ring P₁] [Ring P₂] [Ring Q] (ρ₁ : P →+* P₁) (ρ₂ : P →+* P₂)
      (σ₁ : P₁ →+* Q) (σ₂ : P₂ →+* Q), Function.Surjective σ₂ → σ₁.comp ρ₁ = σ₂.comp ρ₂ →
      (∀ x₁ x₂, σ₁ x₁ = σ₂ x₂ → ∃! x, ρ₁ x = x₁ ∧ ρ₂ x = x₂) →
      ∀ z₁ z₂, K0.map σ₁ z₁ = K0.map σ₂ z₂ → ∃ z, K0.map ρ₁ z = z₁ ∧ K0.map ρ₂ z = z₂ := by
  constructor
  · intro A B _ _ _ _ _ π hπ U hU ε hε
    constructor
    · -- middle exactness: the general Mayer–Vietoris surjectivity at the square `U → ℂ`, `U → A`
      intro z hz
      exact mv_surj (ε.toRingHom) (U.val.toRingHom) (algebraMap ℂ B) (π.toRingHom) hπ
        (square_comm π U ε hε) (square_pull π U hU ε hε) 0 z hz.symm
    · -- injectivity under stable lifting: the general injectivity at that square
      intro hlift w hw1 hw2
      exact k0_mv_inj (ε.toRingHom) (U.val.toRingHom) (algebraMap ℂ B) (π.toRingHom) hπ
        (square_comm π U ε hε) (square_pull π U hU ε hε) hlift w hw1 hw2
  · -- the general Milnor square: Mayer–Vietoris surjectivity
    intro P P₁ P₂ Q _ _ _ _ ρ₁ ρ₂ σ₁ σ₂ hs hcomm hpb z₁ z₂ hz
    exact mv_surj ρ₁ ρ₂ σ₁ σ₂ hs hcomm hpb z₁ z₂ hz

end

end Work.KT.Bott
