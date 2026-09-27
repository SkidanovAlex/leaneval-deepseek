import Mathlib
import Submission.Work.KT.Bott.GlueAux
import Submission.Work.KT.cls_eq_stable_mvN

/-!
# `Work.KT.Bott.mvN_glue`

Glueing of Murray–von Neumann equivalences along a cartesian square of rings.

The square

```
P --ρ₁--> P₁
|          |
ρ₂         σ₁
v          v
P₂ --σ₂--> Q
```

is cartesian (`hpb`).  Given matrices `A_i`, `B_i` over `P_i` with `A_i * B_i = 1` and
`B_i * A_i = E_i`, and `E₁` and `E₂` agreeing after mapping to `Q`, we glue `E₁`, `E₂` into a
matrix `e` over `P` and then glue the (possibly non-matching) maps `A_i`, `B_i`: after enlarging
the matrices by an identity block (using the lifting hypothesis `hlift` to fix the `Q`-images),
they become compatible and hence lift to `X`, `Y` over `P` with `X * Y = 1` and
`Y * X = blk t E_i` after the two projections.

* `mat_lift_eq` — matrix-equality form of `mat_lift`;
* `isUnit_mulMap_prod` — the product `A₁.map σ₁ * B₂.map σ₂` is invertible;
* `mvN_glue_aux` — the glueing step given the invertible correction `D` over `P₂`;
* `mvN_glue` — the requested statement, where `D` is produced by `hlift`.
-/

namespace Work.KT.Bott

open Matrix

noncomputable section

/-- Matrix-equality form of `mat_lift` (whose hypothesis is pointwise). -/
lemma mat_lift_eq {P P₁ P₂ Q : Type} [Ring P] [Ring P₁] [Ring P₂] [Ring Q]
    (ρ₁ : P →+* P₁) (ρ₂ : P →+* P₂) (σ₁ : P₁ →+* Q) (σ₂ : P₂ →+* Q)
    (hpb : ∀ x₁ x₂, σ₁ x₁ = σ₂ x₂ → ∃! x, ρ₁ x = x₁ ∧ ρ₂ x = x₂)
    {m l : ℕ} (N₁ : Matrix (Fin m) (Fin l) P₁) (N₂ : Matrix (Fin m) (Fin l) P₂)
    (h : N₁.map σ₁ = N₂.map σ₂) :
    ∃ Ê : Matrix (Fin m) (Fin l) P, Ê.map ρ₁ = N₁ ∧ Ê.map ρ₂ = N₂ := by
  refine mat_lift ρ₁ ρ₂ σ₁ σ₂ hpb N₁ N₂ ?_
  intro i j
  have hh := congrFun (congrFun h i) j
  simpa [Matrix.map_apply] using hh

/-- If `B_i * A_i = E_i` and `A_i * B_i = 1` for `i = 1, 2` and the `E_i` are the two images of a
matrix `e` over `P`, then `A₁.map σ₁ * B₂.map σ₂` is invertible over `Q`. -/
lemma isUnit_mulMap_prod {P P₁ P₂ Q : Type} [Ring P] [Ring P₁] [Ring P₂] [Ring Q]
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

/-- The core glueing step: a compatible pair of Murray–von Neumann equivalences `E_i ~ 1` over
`P₁`, `P₂`, together with an invertible correction `D` over `P₂` matching the `Q`-images, glues to
an equivalence `e ~ 1` over `P`. -/
lemma mvN_glue_aux {P P₁ P₂ Q : Type} [Ring P] [Ring P₁] [Ring P₂] [Ring Q]
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
    ∃ (X : Matrix (Fin N) (Fin n) P) (Y : Matrix (Fin n) (Fin N) P), X * Y = 1 ∧ Y * X = e := by
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
  obtain ⟨a, ha₁, ha₂⟩ := mat_lift_eq ρ₁ ρ₂ σ₁ σ₂ hpb A₁ (D * A₂) hAmap.symm
  obtain ⟨b, hb₁, hb₂⟩ := mat_lift_eq ρ₁ ρ₂ σ₁ σ₂ hpb B₁ (B₂ * Dinv) hBmap.symm
  refine ⟨a, b, ?_, ?_⟩
  · show a * b = 1
    apply mat_ext_of_maps ρ₁ ρ₂ σ₁ σ₂ hcomm hpb
    · rw [Matrix.map_mul (f := ρ₁) (L := a) (M := b), ha₁, hb₁, h₂,
        Matrix.map_one (⇑ρ₁) (map_zero ρ₁) (map_one ρ₁)]
    · rw [Matrix.map_mul (f := ρ₂) (L := a) (M := b), ha₂, hb₂]
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc A₂ B₂ Dinv, h₄, Matrix.one_mul, hDDinv,
        Matrix.map_one (⇑ρ₂) (map_zero ρ₂) (map_one ρ₂)]
  · show b * a = e
    apply mat_ext_of_maps ρ₁ ρ₂ σ₁ σ₂ hcomm hpb
    · rw [Matrix.map_mul (f := ρ₁) (L := b) (M := a), hb₁, ha₁]; exact h₁
    · rw [Matrix.map_mul (f := ρ₂) (L := b) (M := a), hb₂, ha₂]
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc Dinv D A₂, hDinvD, Matrix.one_mul, h₃]

theorem mvN_glue {P P₁ P₂ Q : Type} [Ring P] [Ring P₁] [Ring P₂] [Ring Q]
    (ρ₁ : P →+* P₁) (ρ₂ : P →+* P₂) (σ₁ : P₁ →+* Q) (σ₂ : P₂ →+* Q)
    (hcomm : σ₁.comp ρ₁ = σ₂.comp ρ₂)
    (hpb : ∀ x₁ x₂, σ₁ x₁ = σ₂ x₂ → ∃! x, ρ₁ x = x₁ ∧ ρ₂ x = x₂)
    (hlift : ∀ (n : ℕ) (u : Matrix (Fin n) (Fin n) Q), IsUnit u →
        ∃ (k : ℕ) (v : Matrix (Fin (n + k)) (Fin (n + k)) P₂), IsUnit v ∧
          v.map σ₂ = Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks u 0 0 1))
    {nq nF : ℕ}
    {A₁ : Matrix (Fin nq) (Fin nF) P₁} {B₁ : Matrix (Fin nF) (Fin nq) P₁}
    {E₁ : Matrix (Fin nF) (Fin nF) P₁}
    {A₂ : Matrix (Fin nq) (Fin nF) P₂} {B₂ : Matrix (Fin nF) (Fin nq) P₂}
    {E₂ : Matrix (Fin nF) (Fin nF) P₂}
    (hA₁ : A₁ * B₁ = 1) (hB₁ : B₁ * A₁ = E₁)
    (hA₂ : A₂ * B₂ = 1) (hB₂ : B₂ * A₂ = E₂)
    (hE : E₁.map σ₁ = E₂.map σ₂) :
    ∃ (t : ℕ) (X : Matrix (Fin (nq + t)) (Fin (nF + t)) P)
             (Y : Matrix (Fin (nF + t)) (Fin (nq + t)) P),
      X * Y = 1 ∧ (Y * X).map ρ₁ = Work.KT.Bott.blk t E₁ ∧
        (Y * X).map ρ₂ = Work.KT.Bott.blk t E₂ := by
  -- glue `E₁`, `E₂` into `e` over `P`
  have hEpt : ∀ i j, σ₁ (E₁ i j) = σ₂ (E₂ i j) := fun i j => by
    have h := congrFun (congrFun hE i) j
    simpa [Matrix.map_apply] using h
  obtain ⟨e, he₁, he₂⟩ := mat_lift ρ₁ ρ₂ σ₁ σ₂ hpb E₁ E₂ hEpt
  -- the correction `D` produced by `hlift`
  have hW : IsUnit ((A₁.map σ₁) * (B₂.map σ₂)) :=
    isUnit_mulMap_prod ρ₁ ρ₂ σ₁ σ₂ hcomm e A₁ B₁ A₂ B₂
      (by rw [he₁]; exact hB₁) hA₁ (by rw [he₂]; exact hB₂) hA₂
  obtain ⟨k, D, hDunit, hD⟩ := hlift nq ((A₁.map σ₁) * (B₂.map σ₂)) hW
  -- block everything with an identity of size `k`
  have hblk₁ : blk k B₁ * blk k A₁ = (blk k e).map ρ₁ := by
    rw [blk_mul, hB₁, blk_map, he₁]
  have hblk₂ : blk k A₁ * blk k B₁ = 1 := by
    rw [blk_mul, hA₁, blk_one]
  have hblk₃ : blk k B₂ * blk k A₂ = (blk k e).map ρ₂ := by
    rw [blk_mul, hB₂, blk_map, he₂]
  have hblk₄ : blk k A₂ * blk k B₂ = 1 := by
    rw [blk_mul, hA₂, blk_one]
  have hblk₅ : D.map σ₂ = (blk k A₁).map σ₁ * (blk k B₂).map σ₂ := by
    calc D.map σ₂ = blk k ((A₁.map σ₁) * (B₂.map σ₂)) := hD
      _ = (blk k A₁).map σ₁ * (blk k B₂).map σ₂ := by
            rw [blk_map, blk_map, blk_mul]
  obtain ⟨X, Y, hXY, hYX⟩ := mvN_glue_aux ρ₁ ρ₂ σ₁ σ₂ hcomm hpb (blk k e)
    (blk k A₁) (blk k B₁) (blk k A₂) (blk k B₂) hblk₁ hblk₂ hblk₃ hblk₄ D hDunit hblk₅
  refine ⟨k, X, Y, hXY, ?_, ?_⟩
  · rw [hYX, blk_map, he₁]
  · rw [hYX, blk_map, he₂]

end

end Work.KT.Bott
