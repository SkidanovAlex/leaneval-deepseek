/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import Submission.Work.Subdivision.Subdiv

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The cone identity for the subdivision differential

`PolyCW.coneLM P e k` appends a new top vertex `e` to every simplex all of whose
vertices are `< e`.  Its interaction with the order-complex differential `D` is
the classical cone identity

`∂ (cone_e x) = cone_e (∂ x) + (-1)^{k+1} x`

for a chain `x` supported below `e`; this is what drives the cone recursion
`subdivCell_succ` for the subdivision chain map.

The argument reduces to the basis vectors `Finsupp.single σ 1` with all vertices
of `σ` strictly below `e` (these span `PolyCW.belowSub P e (k+1)`), where the
identity is a direct computation with the face maps: deleting the last vertex of
`Simplex.snoc σ e` gives back `σ`, and deleting the `j`-th vertex gives
`Simplex.snoc (Simplex.face j σ) e`.  Both are `Simplex.face_last_snoc'` and
`Simplex.face_castSucc_snoc` below.
-/

namespace Work.Subdivision

universe u

namespace Simplex

variable {α : Type u} [Preorder α]

/-- Deleting the `j`-th vertex of `snoc σ e` (for `j` not the last index) gives
the cone on the `j`-th face of `σ`.  Stated with an arbitrary proof `h'` of the
side condition, since `Simplex` is independent of the proof (proof
irrelevance); this avoids a definitional-equality mismatch in rewriting. -/
theorem face_castSucc_snoc' {k : ℕ} (σ : Simplex α (k+1)) (e : α) (h : ∀ i, σ i < e)
    (j : Fin (k + 2)) (h' : ∀ i, (Simplex.face j σ) i < e) :
    Simplex.face j.castSucc (Simplex.snoc σ e h)
      = Simplex.snoc (Simplex.face j σ) e h' := by
  ext t
  rcases Fin.eq_castSucc_or_eq_last t with ⟨t', rfl⟩ | rfl
  · simp only [Simplex.face_apply, Fin.castSucc_succAbove_castSucc, Simplex.snoc_apply_castSucc]
  · rw [Simplex.face_apply, Fin.succAbove_ne_last_last (Fin.ne_of_lt (Fin.castSucc_lt_last j)),
      Simplex.snoc_apply_last, Simplex.snoc_apply_last]

/-- Deleting the last vertex of `snoc σ e` returns `σ`. -/
theorem face_last_snoc' {k : ℕ} (σ : Simplex α (k+1)) (e : α) (h : ∀ i, σ i < e) :
    Simplex.face (Fin.last (k + 2)) (Simplex.snoc σ e h) = σ := by
  ext t
  simp

/-- The concrete form of `face_castSucc_snoc'` with the canonical proof. -/
theorem face_castSucc_snoc {k : ℕ} (σ : Simplex α (k+1)) (e : α) (h : ∀ i, σ i < e)
    (j : Fin (k + 2)) :
    Simplex.face j.castSucc (Simplex.snoc σ e h)
      = Simplex.snoc (Simplex.face j σ) e (fun i => h (j.succAbove i)) :=
  face_castSucc_snoc' σ e h j (fun i => h (j.succAbove i))

end Simplex

set_option maxHeartbeats 2000000 in
theorem D_coneLM (P : PolyCW) (e : P.Cell) (m : ℕ) (x : chainMod P.Cell (m + 1))
    (hx : x ∈ PolyCW.belowSub P e (m + 1)) :
    D (α := P.Cell) (m + 1) (PolyCW.coneLM P e (m + 1) x)
      = PolyCW.coneLM P e m (D (α := P.Cell) m x) + (-1 : ℤ) ^ (m + 2) • x := by
  -- The basis computation: the identity on `single σ 1` for simplices supported below `e`.
  have hgen : ∀ (σ : Simplex P.Cell (m + 1)) (hσ : ∀ i, σ i < e),
      D (α := P.Cell) (m + 1) (PolyCW.coneLM P e (m + 1) (Finsupp.single σ 1))
        = PolyCW.coneLM P e m (D (α := P.Cell) m (Finsupp.single σ 1))
          + (-1 : ℤ) ^ (m + 2) • Finsupp.single σ 1 := by
    intro σ hσ
    rw [PolyCW.coneLM_single P e (m + 1) σ hσ]
    -- `∂ (snoc σ e)` splits into the sum over the proper faces of `σ` (coned with `e`)
    -- plus the single term `σ` coming from deleting the apex.
    have hL : D (α := P.Cell) (m + 1) (Finsupp.single (Simplex.snoc σ e hσ) 1)
        = (∑ j : Fin (m + 2), (-1 : ℤ) ^ (j : ℕ) •
              Finsupp.single (Simplex.snoc (Simplex.face j σ) e (fun i => hσ (j.succAbove i))) 1)
            + (-1 : ℤ) ^ (m + 2) • Finsupp.single σ 1 := by
      rw [D_single, Fin.sum_univ_castSucc]
      congr 1
      · apply Finset.sum_congr rfl
        intro j _
        rw [Simplex.face_castSucc_snoc]
        simp
      · rw [Simplex.face_last_snoc']
        simp
    -- `cone_e (∂ σ)` is the same sum, and `cone` is linear.
    have hR : PolyCW.coneLM P e m (D (α := P.Cell) m (Finsupp.single σ 1))
        = ∑ j : Fin (m + 2), (-1 : ℤ) ^ (j : ℕ) •
              Finsupp.single (Simplex.snoc (Simplex.face j σ) e (fun i => hσ (j.succAbove i))) 1 := by
      rw [D_single, map_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [map_smul, PolyCW.coneLM_single P e m (Simplex.face j σ) (fun i => hσ (j.succAbove i))]
    rw [hL, hR]
  -- Both sides are linear in `x`, so it suffices to check the identity on the generators
  -- of `belowSub P e (m+1)`, which is exactly `hgen`.
  have hker : PolyCW.belowSub P e (m + 1) ≤ LinearMap.ker
      ((D (α := P.Cell) (m + 1)).comp (PolyCW.coneLM P e (m + 1))
        - (PolyCW.coneLM P e m).comp (D (α := P.Cell) m)
        - (-1 : ℤ) ^ (m + 2) •
            (LinearMap.id : chainMod P.Cell (m + 1) →ₗ[ℤ] chainMod P.Cell (m + 1))) := by
    rw [PolyCW.belowSub_le_iff]
    intro σ hσ
    rw [LinearMap.mem_ker]
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply]
    rw [hgen σ hσ]
    abel
  have hx' := hker hx
  rw [LinearMap.mem_ker] at hx'
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply] at hx'
  rw [← sub_eq_zero, ← sub_sub]
  exact hx'

end Work.Subdivision
