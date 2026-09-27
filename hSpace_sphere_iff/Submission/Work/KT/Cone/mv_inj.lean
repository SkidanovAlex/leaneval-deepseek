import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.Basic
import Submission.Work.KT.cls_eq_stable_mvN
import Submission.Work.KT.k0_rep

/-!
# `Work.KT.Cone.mv_inj` — Mayer–Vietoris injectivity for `K₀`

Proof of `Work.KT.Cone.mv_inj`.  The argument is Milnor's glueing of projective modules:

* `mvinj_pb_ext`, `mvinj_mat_ext`, `mvinj_mat_lift`: the pull-back square `P → P₁, P → P₂` of rings gives an
  entrywise "glueing" of matrices over `P` from compatible matrices over `P₁` and `P₂`.
* `mvinj_mvN_glue`: **Milnor's glueing lemma.**  If an idempotent `e` over `P` becomes free of rank `N`
  over both `P₁` and `P₂` (via trivialisations `A_i, B_i`), and the resulting transition unit
  `A₁^{σ₁} · B₂^{σ₂}` over `Q` lifts to an invertible matrix `D` over `P₂`, then `e` is free of
  rank `N` over `P`.  `mvinj_isUnit_glue` supplies the unit used for the stable lifting hypothesis.
* `mvinj_stable_free`: an idempotent of `P` with stably free base changes of the same rank `N` is free
  of rank `N`, using `cls_eq_stable_mvN` to pass from equal `K₀`-classes to stable Murray–von
  Neumann equivalence and stabilising by a large enough free block.
* `mv_inj`: writing an element of `K₀ P` as `[F] - [1_n]` (`k0_rep`), the two vanishings force
  `[F] = [1_n]` after base change, hence `[F] = [1_n]` over `P` by `mvinj_stable_free`.

Nothing here needs the surjectivity of `σ₂`; it is kept because it is part of the stated
hypotheses of the Mayer–Vietoris square.
-/

namespace Work.KT.Cone

noncomputable section

open Matrix

theorem mvinj_pb_ext {P P₁ P₂ Q : Type} [Ring P] [Ring P₁] [Ring P₂] [Ring Q]
    (ρ₁ : P →+* P₁) (ρ₂ : P →+* P₂) (σ₁ : P₁ →+* Q) (σ₂ : P₂ →+* Q)
    (hcomm : σ₁.comp ρ₁ = σ₂.comp ρ₂)
    (hpb : ∀ x₁ x₂, σ₁ x₁ = σ₂ x₂ → ∃! x, ρ₁ x = x₁ ∧ ρ₂ x = x₂)
    (x y : P) (h1 : ρ₁ x = ρ₁ y) (h2 : ρ₂ x = ρ₂ y) : x = y := by
  have hc : σ₁ (ρ₁ x) = σ₂ (ρ₂ x) := by
    have h := RingHom.congr_fun hcomm x; simpa using h
  obtain ⟨w, hw, huniq⟩ := hpb (ρ₁ x) (ρ₂ x) hc
  exact (huniq x ⟨rfl, rfl⟩).trans (huniq y ⟨h1.symm, h2.symm⟩).symm

theorem mvinj_mat_ext {P P₁ P₂ Q : Type} [Ring P] [Ring P₁] [Ring P₂] [Ring Q]
    (ρ₁ : P →+* P₁) (ρ₂ : P →+* P₂) (σ₁ : P₁ →+* Q) (σ₂ : P₂ →+* Q)
    (hcomm : σ₁.comp ρ₁ = σ₂.comp ρ₂)
    (hpb : ∀ x₁ x₂, σ₁ x₁ = σ₂ x₂ → ∃! x, ρ₁ x = x₁ ∧ ρ₂ x = x₂)
    {ι κ : Type} (X Y : Matrix ι κ P)
    (h1 : X.map ρ₁ = Y.map ρ₁) (h2 : X.map ρ₂ = Y.map ρ₂) : X = Y := by
  ext i j
  refine mvinj_pb_ext ρ₁ ρ₂ σ₁ σ₂ hcomm hpb _ _ ?_ ?_
  · have hh := congrFun (congrFun h1 i) j; simpa [Matrix.map_apply] using hh
  · have hh := congrFun (congrFun h2 i) j; simpa [Matrix.map_apply] using hh

theorem mvinj_mat_lift {P P₁ P₂ Q : Type} [Ring P] [Ring P₁] [Ring P₂] [Ring Q]
    (ρ₁ : P →+* P₁) (ρ₂ : P →+* P₂) (σ₁ : P₁ →+* Q) (σ₂ : P₂ →+* Q)
    (hpb : ∀ x₁ x₂, σ₁ x₁ = σ₂ x₂ → ∃! x, ρ₁ x = x₁ ∧ ρ₂ x = x₂)
    {ι κ : Type} (X₁ : Matrix ι κ P₁) (X₂ : Matrix ι κ P₂)
    (h : X₁.map σ₁ = X₂.map σ₂) : ∃ X : Matrix ι κ P, X.map ρ₁ = X₁ ∧ X.map ρ₂ = X₂ := by
  have key : ∀ i j, ∃! x : P, ρ₁ x = X₁ i j ∧ ρ₂ x = X₂ i j := fun i j => hpb _ _ (by
    have hh := congrFun (congrFun h i) j; simpa [Matrix.map_apply] using hh)
  refine ⟨fun i j => (key i j).choose, ?_, ?_⟩
  · ext i j
    show ρ₁ ((key i j).choose) = X₁ i j
    exact ((key i j).choose_spec).1.1
  · ext i j
    show ρ₂ ((key i j).choose) = X₂ i j
    exact ((key i j).choose_spec).1.2

lemma mvinj_map_fromBlocksSum {R S : Type} [Ring R] [Ring S] (φ : R →+* S)
    {n n' m m' : ℕ} (a : Matrix (Fin n) (Fin n') R) (b : Matrix (Fin m) (Fin m') R) :
    (fromBlocksSum a b).map φ = fromBlocksSum (a.map φ) (b.map φ) := by
  ext i j
  simp only [fromBlocksSum, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.map_apply]
  rcases finSumFinEquiv.symm i with a' | a' <;> rcases finSumFinEquiv.symm j with b' | b' <;>
    simp [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂]

lemma mvinj_map_one {R S : Type} [Ring R] [Ring S] (φ : R →+* S) (n : ℕ) :
    (Mat.one R n).map φ = Mat.one S n := by
  unfold Mat.one Mat.map
  simp only [Sigma.mk.injEq, heq_eq_eq, true_and]
  ext i j
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

lemma mvinj_fromBlocksSum_one (R : Type) [Ring R] (m n : ℕ) :
    fromBlocksSum (1 : Matrix (Fin m) (Fin m) R) (1 : Matrix (Fin n) (Fin n) R) =
      (1 : Matrix (Fin (m + n)) (Fin (m + n)) R) := by
  rw [fromBlocksSum, Matrix.fromBlocks_one]
  ext i j
  rw [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.one_apply, Matrix.one_apply]
  by_cases h : i = j
  · subst h; simp
  · have h' : finSumFinEquiv.symm i ≠ finSumFinEquiv.symm j :=
      fun hh => h (finSumFinEquiv.symm.injective hh)
    simp [h, h']

lemma mvinj_cls_one_add {R : Type} [Ring R] (m k : ℕ) :
    cls (Mat.one R (m + k)) = cls (Mat.one R m) + cls (Mat.one R k) := by
  rw [← k2_one_sum_one R m k, cls_sum (Mat.one_isIdem R m) (Mat.one_isIdem R k)]

lemma mvinj_map_cls {R S : Type} [Ring R] [Ring S] (φ : R →+* S) (p : Mat R) (hp : p.IsIdem) :
    K0.map φ (cls p) = cls (p.map φ) := by
  have h : K0.map φ (cls p) = mapCls φ p := by
    rw [show K0.map φ = QuotientAddGroup.lift (K0Rel R) (FreeAbelianGroup.lift (mapCls φ)) _
        from rfl]
    rw [show cls p = QuotientAddGroup.mk (FreeAbelianGroup.of p) from rfl]
    rw [QuotientAddGroup.lift_mk, FreeAbelianGroup.lift_apply_of]
  rw [h, mapCls, if_pos hp]

lemma mvinj_mvN_of_cls_eq {R : Type} [Ring R] {p q : Mat R} (hp : p.IsIdem) (hq : q.IsIdem)
    (h : cls p = cls q) : ∃ k : ℕ, Mat.MvN (p.sum (Mat.one R k)) (q.sum (Mat.one R k)) :=
  (cls_eq_stable_mvN p q hp hq).mp h

lemma mvinj_mvN_sum_one_add {R : Type} [Ring R] {p q : Mat R} (hp : p.IsIdem) (hq : q.IsIdem)
    (a t : ℕ) (h : Mat.MvN (p.sum (Mat.one R a)) (q.sum (Mat.one R a))) :
    Mat.MvN (p.sum (Mat.one R (a + t))) (q.sum (Mat.one R (a + t))) :=
  k2_mvN_add_one_right hp hq h t

lemma mvinj_isUnit_glue {P P₁ P₂ Q : Type} [Ring P] [Ring P₁] [Ring P₂] [Ring Q]
    (ρ₁ : P →+* P₁) (ρ₂ : P →+* P₂) (σ₁ : P₁ →+* Q) (σ₂ : P₂ →+* Q)
    (hcomm : σ₁.comp ρ₁ = σ₂.comp ρ₂)
    {n N : ℕ} (e : Matrix (Fin n) (Fin n) P) (A₁ : Matrix (Fin N) (Fin n) P₁)
    (B₁ : Matrix (Fin n) (Fin N) P₁) (A₂ : Matrix (Fin N) (Fin n) P₂)
    (B₂ : Matrix (Fin n) (Fin N) P₂)
    (h₁ : B₁ * A₁ = e.map ρ₁) (h₂ : A₁ * B₁ = 1)
    (h₃ : B₂ * A₂ = e.map ρ₂) (h₄ : A₂ * B₂ = 1) :
    IsUnit ((A₁.map σ₁) * (B₂.map σ₂)) := by
  have he₁ : A₁ * (e.map ρ₁) = A₁ := by rw [← h₁, ← Matrix.mul_assoc, h₂, Matrix.one_mul]
  have he₂ : A₂ * (e.map ρ₂) = A₂ := by rw [← h₃, ← Matrix.mul_assoc, h₄, Matrix.one_mul]
  have heqρ : (e.map ρ₂).map σ₂ = (e.map ρ₁).map σ₁ := by
    ext i j
    simp only [Matrix.map_apply]
    exact (RingHom.congr_fun hcomm (e i j)).symm
  refine ⟨⟨(A₁.map σ₁) * (B₂.map σ₂), (A₂.map σ₂) * (B₁.map σ₁), ?_, ?_⟩, rfl⟩
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc (B₂.map σ₂) (A₂.map σ₂) (B₁.map σ₁),
      ← Matrix.map_mul (f := σ₂) (L := B₂) (M := A₂), h₃, heqρ,
      ← Matrix.mul_assoc (A₁.map σ₁) ((e.map ρ₁).map σ₁) (B₁.map σ₁),
      ← Matrix.map_mul (f := σ₁) (L := A₁) (M := e.map ρ₁), he₁,
      ← Matrix.map_mul (f := σ₁) (L := A₁) (M := B₁), h₂,
      Matrix.map_one (⇑σ₁) (map_zero σ₁) (map_one σ₁)]
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc (B₁.map σ₁) (A₁.map σ₁) (B₂.map σ₂),
      ← Matrix.map_mul (f := σ₁) (L := B₁) (M := A₁), h₁, ← heqρ,
      ← Matrix.mul_assoc (A₂.map σ₂) ((e.map ρ₂).map σ₂) (B₂.map σ₂),
      ← Matrix.map_mul (f := σ₂) (L := A₂) (M := e.map ρ₂), he₂,
      ← Matrix.map_mul (f := σ₂) (L := A₂) (M := B₂), h₄,
      Matrix.map_one (⇑σ₂) (map_zero σ₂) (map_one σ₂)]

theorem mvinj_mvN_glue {P P₁ P₂ Q : Type} [Ring P] [Ring P₁] [Ring P₂] [Ring Q]
    (ρ₁ : P →+* P₁) (ρ₂ : P →+* P₂) (σ₁ : P₁ →+* Q) (σ₂ : P₂ →+* Q)
    (hcomm : σ₁.comp ρ₁ = σ₂.comp ρ₂)
    (hpb : ∀ x₁ x₂, σ₁ x₁ = σ₂ x₂ → ∃! x, ρ₁ x = x₁ ∧ ρ₂ x = x₂)
    {n N : ℕ} (e : Matrix (Fin n) (Fin n) P) (A₁ : Matrix (Fin N) (Fin n) P₁)
    (B₁ : Matrix (Fin n) (Fin N) P₁) (A₂ : Matrix (Fin N) (Fin n) P₂)
    (B₂ : Matrix (Fin n) (Fin N) P₂)
    (h₁ : B₁ * A₁ = e.map ρ₁) (h₂ : A₁ * B₁ = 1)
    (h₃ : B₂ * A₂ = e.map ρ₂) (h₄ : A₂ * B₂ = 1)
    (D : Matrix (Fin N) (Fin N) P₂) (hD : IsUnit D)
    (hDσ : D.map σ₂ = (A₁.map σ₁) * (B₂.map σ₂)) :
    Mat.MvN ⟨n, e⟩ (Mat.one P N) := by
  have he₁ : A₁ * (e.map ρ₁) = A₁ := by rw [← h₁, ← Matrix.mul_assoc, h₂, Matrix.one_mul]
  have he₁' : (e.map ρ₁) * B₁ = B₁ := by rw [← h₁, Matrix.mul_assoc, h₂, Matrix.mul_one]
  have he₂ : A₂ * (e.map ρ₂) = A₂ := by rw [← h₃, ← Matrix.mul_assoc, h₄, Matrix.one_mul]
  have heqρ : (e.map ρ₂).map σ₂ = (e.map ρ₁).map σ₁ := by
    ext i j
    simp only [Matrix.map_apply]
    exact (RingHom.congr_fun hcomm (e i j)).symm
  let Dinv : Matrix (Fin N) (Fin N) P₂ := ↑hD.unit⁻¹
  have hDDinv : D * Dinv = 1 := hD.mul_val_inv
  have hDinvD : Dinv * D = 1 := hD.val_inv_mul
  have hW'W : ((A₂.map σ₂) * (B₁.map σ₁)) * ((A₁.map σ₁) * (B₂.map σ₂)) = 1 := by
    rw [Matrix.mul_assoc,
      ← Matrix.mul_assoc (B₁.map σ₁) (A₁.map σ₁) (B₂.map σ₂),
      ← Matrix.map_mul (f := σ₁) (L := B₁) (M := A₁), h₁,
      ← heqρ,
      ← Matrix.mul_assoc (A₂.map σ₂) ((e.map ρ₂).map σ₂) (B₂.map σ₂),
      ← Matrix.map_mul (f := σ₂) (L := A₂) (M := e.map ρ₂), he₂,
      ← Matrix.map_mul (f := σ₂) (L := A₂) (M := B₂), h₄,
      Matrix.map_one (⇑σ₂) (map_zero σ₂) (map_one σ₂)]
  have hDinvσ_mul : (D.map σ₂) * (Dinv.map σ₂) = 1 := by
    rw [← Matrix.map_mul (f := σ₂) (L := D) (M := Dinv), hDDinv,
      Matrix.map_one (⇑σ₂) (map_zero σ₂) (map_one σ₂)]
  have hDinvσ : Dinv.map σ₂ = (A₂.map σ₂) * (B₁.map σ₁) := by
    calc Dinv.map σ₂ = 1 * (Dinv.map σ₂) := by rw [one_mul]
      _ = (((A₂.map σ₂) * (B₁.map σ₁)) * ((A₁.map σ₁) * (B₂.map σ₂))) * (Dinv.map σ₂) := by rw [hW'W]
      _ = ((A₂.map σ₂) * (B₁.map σ₁)) * (((A₁.map σ₁) * (B₂.map σ₂)) * (Dinv.map σ₂)) := by rw [Matrix.mul_assoc]
      _ = ((A₂.map σ₂) * (B₁.map σ₁)) * ((D.map σ₂) * (Dinv.map σ₂)) := by rw [← hDσ]
      _ = ((A₂.map σ₂) * (B₁.map σ₁)) * 1 := by rw [hDinvσ_mul]
      _ = (A₂.map σ₂) * (B₁.map σ₁) := by rw [mul_one]
  have hAmap : (D * A₂).map σ₂ = A₁.map σ₁ := by
    rw [Matrix.map_mul (f := σ₂) (L := D) (M := A₂), hDσ,
      Matrix.mul_assoc, ← Matrix.map_mul (f := σ₂) (L := B₂) (M := A₂), h₃, heqρ,
      ← Matrix.map_mul (f := σ₁) (L := A₁) (M := e.map ρ₁), he₁]
  have hBmap : (B₂ * Dinv).map σ₂ = B₁.map σ₁ := by
    rw [Matrix.map_mul (f := σ₂) (L := B₂) (M := Dinv), hDinvσ,
      ← Matrix.mul_assoc, ← Matrix.map_mul (f := σ₂) (L := B₂) (M := A₂), h₃, heqρ,
      ← Matrix.map_mul (f := σ₁) (L := e.map ρ₁) (M := B₁), he₁']
  obtain ⟨a, ha₁, ha₂⟩ := mvinj_mat_lift ρ₁ ρ₂ σ₁ σ₂ hpb A₁ (D * A₂) hAmap.symm
  obtain ⟨b, hb₁, hb₂⟩ := mvinj_mat_lift ρ₁ ρ₂ σ₁ σ₂ hpb B₁ (B₂ * Dinv) hBmap.symm
  refine ⟨a, b, ?_, ?_⟩
  · show b * a = e
    apply mvinj_mat_ext ρ₁ ρ₂ σ₁ σ₂ hcomm hpb
    · rw [Matrix.map_mul (f := ρ₁) (L := b) (M := a), hb₁, ha₁]; exact h₁
    · rw [Matrix.map_mul (f := ρ₂) (L := b) (M := a), hb₂, ha₂]
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc Dinv D A₂, hDinvD, Matrix.one_mul, h₃]
  · show a * b = 1
    apply mvinj_mat_ext ρ₁ ρ₂ σ₁ σ₂ hcomm hpb
    · rw [Matrix.map_mul (f := ρ₁) (L := a) (M := b), ha₁, hb₁, h₂,
        Matrix.map_one (⇑ρ₁) (map_zero ρ₁) (map_one ρ₁)]
    · rw [Matrix.map_mul (f := ρ₂) (L := a) (M := b), ha₂, hb₂]
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc A₂ B₂ Dinv, h₄, Matrix.one_mul, hDDinv,
        Matrix.map_one (⇑ρ₂) (map_zero ρ₂) (map_one ρ₂)]

theorem mvinj_stable_free {P P₁ P₂ Q : Type} [Ring P] [Ring P₁] [Ring P₂] [Ring Q]
    (ρ₁ : P →+* P₁) (ρ₂ : P →+* P₂) (σ₁ : P₁ →+* Q) (σ₂ : P₂ →+* Q)
    (hs : Function.Surjective σ₂) (hcomm : σ₁.comp ρ₁ = σ₂.comp ρ₂)
    (hpb : ∀ x₁ x₂, σ₁ x₁ = σ₂ x₂ → ∃! x, ρ₁ x = x₁ ∧ ρ₂ x = x₂)
    (hlift : ∀ (n : ℕ) (u : Matrix (Fin n) (Fin n) Q), IsUnit u →
        ∃ (k : ℕ) (v : Matrix (Fin (n + k)) (Fin (n + k)) P₂), IsUnit v ∧
          v.map σ₂ = Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks u 0 0 1))
    {E : Mat P} (hE : E.IsIdem) (N : ℕ)
    (h₁ : cls (E.map ρ₁) = cls (Mat.one P₁ N)) (h₂ : cls (E.map ρ₂) = cls (Mat.one P₂ N)) :
    cls E = cls (Mat.one P N) := by
  obtain ⟨a₁, ha₁⟩ := mvinj_mvN_of_cls_eq (Mat.map_idem ρ₁ hE) (Mat.one_isIdem P₁ N) h₁
  obtain ⟨a₂, ha₂⟩ := mvinj_mvN_of_cls_eq (Mat.map_idem ρ₂ hE) (Mat.one_isIdem P₂ N) h₂
  let a : ℕ := max a₁ a₂
  have hsub₁ : a₁ + (a - a₁) = a := Nat.add_sub_of_le (le_max_left a₁ a₂)
  have hsub₂ : a₂ + (a - a₂) = a := Nat.add_sub_of_le (le_max_right a₁ a₂)
  let eE : Matrix (Fin (E.1 + a)) (Fin (E.1 + a)) P := fromBlocksSum E.2 (1 : Matrix (Fin a) (Fin a) P)
  have heEσ₁ : eE.map ρ₁ = fromBlocksSum (E.2.map ρ₁) (1 : Matrix (Fin a) (Fin a) P₁) := by
    rw [show eE = fromBlocksSum E.2 (1 : Matrix (Fin a) (Fin a) P) from rfl,
      mvinj_map_fromBlocksSum, Matrix.map_one (⇑ρ₁) (map_zero ρ₁) (map_one ρ₁)]
  have heEσ₂ : eE.map ρ₂ = fromBlocksSum (E.2.map ρ₂) (1 : Matrix (Fin a) (Fin a) P₂) := by
    rw [show eE = fromBlocksSum E.2 (1 : Matrix (Fin a) (Fin a) P) from rfl,
      mvinj_map_fromBlocksSum, Matrix.map_one (⇑ρ₂) (map_zero ρ₂) (map_one ρ₂)]
  have heE : Mat.IsIdem (⟨E.1 + a, eE⟩ : Mat P) := Mat.sum_idem hE (Mat.one_isIdem P a)
  have hF₁ : Mat.MvN
      (⟨E.1 + a, fromBlocksSum (E.2.map ρ₁) (1 : Matrix (Fin a) (Fin a) P₁)⟩ : Mat P₁)
      (⟨N + a, 1⟩ : Mat P₁) := by
    have h := mvinj_mvN_sum_one_add (Mat.map_idem ρ₁ hE) (Mat.one_isIdem P₁ N) a₁ (a - a₁) ha₁
    rw [hsub₁, k2_one_sum_one P₁ N a] at h
    exact h
  have hF₂ : Mat.MvN
      (⟨E.1 + a, fromBlocksSum (E.2.map ρ₂) (1 : Matrix (Fin a) (Fin a) P₂)⟩ : Mat P₂)
      (⟨N + a, 1⟩ : Mat P₂) := by
    have h := mvinj_mvN_sum_one_add (Mat.map_idem ρ₂ hE) (Mat.one_isIdem P₂ N) a₂ (a - a₂) ha₂
    rw [hsub₂, k2_one_sum_one P₂ N a] at h
    exact h
  obtain ⟨A₁, B₁, hB₁A₁, hA₁B₁⟩ := hF₁
  obtain ⟨A₂, B₂, hB₂A₂, hA₂B₂⟩ := hF₂
  have hWunit : IsUnit ((A₁.map σ₁) * (B₂.map σ₂)) :=
    mvinj_isUnit_glue ρ₁ ρ₂ σ₁ σ₂ hcomm eE A₁ B₁ A₂ B₂
      (by rw [heEσ₁]; exact hB₁A₁) (by rw [hA₁B₁])
      (by rw [heEσ₂]; exact hB₂A₂) (by rw [hA₂B₂])
  obtain ⟨k, D, hDunit, hD⟩ := hlift (N + a) ((A₁.map σ₁) * (B₂.map σ₂)) hWunit
  let ePm : Matrix (Fin (E.1 + a + k)) (Fin (E.1 + a + k)) P :=
    fromBlocksSum eE (1 : Matrix (Fin k) (Fin k) P)
  have hePmunf : ePm = fromBlocksSum eE (1 : Matrix (Fin k) (Fin k) P) := rfl
  have heP : Mat.IsIdem (⟨E.1 + a + k, ePm⟩ : Mat P) := Mat.sum_idem heE (Mat.one_isIdem P k)
  have hA1sig : (fromBlocksSum A₁ (1 : Matrix (Fin k) (Fin k) P₁)).map σ₁ =
      fromBlocksSum (A₁.map σ₁) (1 : Matrix (Fin k) (Fin k) Q) := by
    rw [mvinj_map_fromBlocksSum, Matrix.map_one (⇑σ₁) (map_zero σ₁) (map_one σ₁)]
  have hB2sig : (fromBlocksSum B₂ (1 : Matrix (Fin k) (Fin k) P₂)).map σ₂ =
      fromBlocksSum (B₂.map σ₂) (1 : Matrix (Fin k) (Fin k) Q) := by
    rw [mvinj_map_fromBlocksSum, Matrix.map_one (⇑σ₂) (map_zero σ₂) (map_one σ₂)]
  have hpk₁ : (fromBlocksSum B₁ (1 : Matrix (Fin k) (Fin k) P₁)) *
      (fromBlocksSum A₁ (1 : Matrix (Fin k) (Fin k) P₁)) = ePm.map ρ₁ := by
    rw [fromBlocksSum_mul, hB₁A₁, one_mul, hePmunf, mvinj_map_fromBlocksSum, heEσ₁,
      Matrix.map_one (⇑ρ₁) (map_zero ρ₁) (map_one ρ₁)]
  have hpk₂ : (fromBlocksSum A₁ (1 : Matrix (Fin k) (Fin k) P₁)) *
      (fromBlocksSum B₁ (1 : Matrix (Fin k) (Fin k) P₁)) = 1 := by
    rw [fromBlocksSum_mul, hA₁B₁, one_mul]
    exact mvinj_fromBlocksSum_one P₁ (N + a) k
  have hpk₃ : (fromBlocksSum B₂ (1 : Matrix (Fin k) (Fin k) P₂)) *
      (fromBlocksSum A₂ (1 : Matrix (Fin k) (Fin k) P₂)) = ePm.map ρ₂ := by
    rw [fromBlocksSum_mul, hB₂A₂, one_mul, hePmunf, mvinj_map_fromBlocksSum, heEσ₂,
      Matrix.map_one (⇑ρ₂) (map_zero ρ₂) (map_one ρ₂)]
  have hpk₄ : (fromBlocksSum A₂ (1 : Matrix (Fin k) (Fin k) P₂)) *
      (fromBlocksSum B₂ (1 : Matrix (Fin k) (Fin k) P₂)) = 1 := by
    rw [fromBlocksSum_mul, hA₂B₂, one_mul]
    exact mvinj_fromBlocksSum_one P₂ (N + a) k
  have hpk₅ : D.map σ₂ =
      (fromBlocksSum A₁ (1 : Matrix (Fin k) (Fin k) P₁)).map σ₁ *
      (fromBlocksSum B₂ (1 : Matrix (Fin k) (Fin k) P₂)).map σ₂ := by
    rw [hA1sig, hB2sig, fromBlocksSum_mul, one_mul, hD]
    rfl
  have hcrit : Mat.MvN ⟨E.1 + a + k, ePm⟩ (Mat.one P (N + a + k)) :=
    mvinj_mvN_glue ρ₁ ρ₂ σ₁ σ₂ hcomm hpb ePm
      (fromBlocksSum A₁ (1 : Matrix (Fin k) (Fin k) P₁))
      (fromBlocksSum B₁ (1 : Matrix (Fin k) (Fin k) P₁))
      (fromBlocksSum A₂ (1 : Matrix (Fin k) (Fin k) P₂))
      (fromBlocksSum B₂ (1 : Matrix (Fin k) (Fin k) P₂))
      hpk₁ hpk₂ hpk₃ hpk₄ D hDunit hpk₅
  have hcls : cls (⟨E.1 + a + k, ePm⟩ : Mat P) = cls (Mat.one P (N + a + k)) :=
    cls_eq_of_mvN heP (Mat.one_isIdem P (N + a + k)) hcrit
  have heq1 : (⟨E.1 + a + k, ePm⟩ : Mat P) = (E.sum (Mat.one P a)).sum (Mat.one P k) := rfl
  have hsplit : cls (⟨E.1 + a + k, ePm⟩ : Mat P) =
      cls E + cls (Mat.one P a) + cls (Mat.one P k) := by
    rw [heq1, cls_sum (Mat.sum_idem hE (Mat.one_isIdem P a)) (Mat.one_isIdem P k),
      cls_sum hE (Mat.one_isIdem P a)]
  have hrhs : cls (Mat.one P (N + a + k)) =
      cls (Mat.one P N) + cls (Mat.one P a) + cls (Mat.one P k) := by
    rw [mvinj_cls_one_add (R := P) (N + a) k, mvinj_cls_one_add (R := P) N a]
  rw [hsplit, hrhs] at hcls
  exact add_right_cancel (add_right_cancel hcls)

/-- **Mayer–Vietoris injectivity for `K₀`.**  In a cartesian square of rings
`ρ₁ : P → P₁`, `ρ₂ : P → P₂`, `σ₁ : P₁ → Q`, `σ₂ : P₂ → Q` with `σ₂` surjective, if every
invertible matrix over `Q` lifts stably to an invertible matrix over `P₂`, then the map
`K₀ P → K₀ P₁ × K₀ P₂` is injective.

Route (Milnor; see M. Land, *Algebraic K-theory*, §4.3, results 4.56 and 4.57): the connecting
map `∂ : K₁(Q) → K₀(P)` has image the kernel of `K₀ P → K₀ P₁ × K₀ P₂`; the stable lifting
hypothesis makes `GL(P₂) → GL(Q)` surjective on the relevant stable groups, so `∂ = 0` and the
kernel vanishes. -/
theorem mv_inj {P P₁ P₂ Q : Type} [Ring P] [Ring P₁] [Ring P₂] [Ring Q]
    (ρ₁ : P →+* P₁) (ρ₂ : P →+* P₂) (σ₁ : P₁ →+* Q) (σ₂ : P₂ →+* Q)
    (hs : Function.Surjective σ₂) (hcomm : σ₁.comp ρ₁ = σ₂.comp ρ₂)
    (hpb : ∀ x₁ x₂, σ₁ x₁ = σ₂ x₂ → ∃! x, ρ₁ x = x₁ ∧ ρ₂ x = x₂)
    (hlift : ∀ (n : ℕ) (u : Matrix (Fin n) (Fin n) Q), IsUnit u →
        ∃ (k : ℕ) (v : Matrix (Fin (n + k)) (Fin (n + k)) P₂), IsUnit v ∧
          v.map σ₂ = Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks u 0 0 1)) :
    ∀ w : K0 P, K0.map ρ₁ w = 0 → K0.map ρ₂ w = 0 → w = 0 := by
  intro w hw₁ hw₂
  obtain ⟨F, n, hF, hw⟩ := k0_rep w
  have h₁ : cls (F.map ρ₁) = cls (Mat.one P₁ n) := by
    have h : K0.map ρ₁ (cls F - cls (Mat.one P n)) = 0 := by rw [← hw]; exact hw₁
    rw [map_sub, mvinj_map_cls ρ₁ F hF,
      mvinj_map_cls (R := P) (S := P₁) ρ₁ (Mat.one P n) (Mat.one_isIdem P n), mvinj_map_one ρ₁ n] at h
    exact sub_eq_zero.mp h
  have h₂ : cls (F.map ρ₂) = cls (Mat.one P₂ n) := by
    have h : K0.map ρ₂ (cls F - cls (Mat.one P n)) = 0 := by rw [← hw]; exact hw₂
    rw [map_sub, mvinj_map_cls ρ₂ F hF,
      mvinj_map_cls (R := P) (S := P₂) ρ₂ (Mat.one P n) (Mat.one_isIdem P n), mvinj_map_one ρ₂ n] at h
    exact sub_eq_zero.mp h
  have hfree := mvinj_stable_free ρ₁ ρ₂ σ₁ σ₂ hs hcomm hpb hlift hF n h₁ h₂
  rw [hw, hfree, sub_self]

end
end Work.KT.Cone
