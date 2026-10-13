import Mathlib
import Submission.Work.WilE9.Ift.OneShotDefs

namespace Work.WilE9.Ift.OneShot

open WilkiesDesign WilkiesDesign.E

/-! ## Degree bookkeeping for the one-shot construction

The one-shot set `oneShotSet c F L Y` is built by reindexing the polynomials of `Y` along the
injection `oneShotInj n m` (`Work.WilE8.Basic.extend`), viewing them on the left factor of the
concatenated chain (`Work.WilE7.Basic.inl`) and conjoining the single new equation
(`Work.WilE7.Basic.inr (oneShotBasic c F L)`).  None of these operations changes the degree of a
basic condition, so the degree of the result is `Y.deg + Y.basics.length * (oneShotBasic …).deg`.

Below we collect the `atomDeg`/`Basic.deg` invariance of `EAPoly.inl` and `EAPoly.inr`
(the concatenation reindexings) and then assemble the statement. -/

/-- Reindexing an EA polynomial to the left factor of a concatenated chain preserves the atom
degree: `EAPoly.inl` is a `rename` along the injective map `Sum.map id (Fin.castAdd r₂)`. -/
theorem atomDeg_inl {k r₁ r₂ : ℕ} (Q : EAPoly k r₁) :
    atomDeg (Work.WilE7.EAPoly.inl (r₂ := r₂) Q) = atomDeg Q := by
  have hinj : Function.Injective
      (Sum.map id (Fin.castAdd r₂) : Fin k ⊕ Fin r₁ → Fin k ⊕ Fin (r₁ + r₂)) :=
    Sum.map_injective.mpr ⟨Function.injective_id, Fin.castAdd_injective r₁ r₂⟩
  simp only [atomDeg, Work.WilE7.EAPoly.inl]
  rw [Work.WilE8.Extend.totalDegree_rename_of_injective _ hinj Q]

/-- Reindexing an EA polynomial to the right factor of a concatenated chain preserves the atom
degree: `EAPoly.inr` is a `rename` along the injective map `Sum.map id (Fin.natAdd r₁)`. -/
theorem atomDeg_inr {k r₁ r₂ : ℕ} (Q : EAPoly k r₂) :
    atomDeg (Work.WilE7.EAPoly.inr (r₁ := r₁) Q) = atomDeg Q := by
  have hinj : Function.Injective
      (Sum.map id (Fin.natAdd r₁) : Fin k ⊕ Fin r₂ → Fin k ⊕ Fin (r₁ + r₂)) :=
    Sum.map_injective.mpr ⟨Function.injective_id, Fin.natAdd_injective r₂ r₁⟩
  simp only [atomDeg, Work.WilE7.EAPoly.inr]
  rw [Work.WilE8.Extend.totalDegree_rename_of_injective _ hinj Q]

/-- Reindexing a basic condition to the left factor of a concatenated chain preserves its
degree. -/
theorem basic_deg_inl {k r₁ r₂ : ℕ} (B : Basic k r₁) :
    (Work.WilE7.Basic.inl (r₂ := r₂) B).deg = B.deg := by
  have key : ∀ l : List (EAPoly k r₁),
      ((l.map (Work.WilE7.EAPoly.inl (r₂ := r₂))).map atomDeg).sum = (l.map atomDeg).sum := by
    intro l
    congr 1
    rw [List.map_map]
    apply List.map_congr_left
    intro Q _
    exact atomDeg_inl Q
  simp only [Basic.deg, Work.WilE7.Basic.inl, List.map_append, List.sum_append]
  rw [key B.eqs, key B.pos]

/-- Reindexing a basic condition to the right factor of a concatenated chain preserves its
degree. -/
theorem basic_deg_inr {k r₁ r₂ : ℕ} (B : Basic k r₂) :
    (Work.WilE7.Basic.inr (r₁ := r₁) B).deg = B.deg := by
  have key : ∀ l : List (EAPoly k r₂),
      ((l.map (Work.WilE7.EAPoly.inr (r₁ := r₁))).map atomDeg).sum = (l.map atomDeg).sum := by
    intro l
    congr 1
    rw [List.map_map]
    apply List.map_congr_left
    intro Q _
    exact atomDeg_inr Q
  simp only [Basic.deg, Work.WilE7.Basic.inr, List.map_append, List.sum_append]
  rw [key B.eqs, key B.pos]

/-- Distributing a sum of a constant over a list: `∑ (f a + D) = ∑ f a + |l| * D`. -/
theorem sum_map_add_const {α : Type*} (l : List α) (f : α → ℕ) (D : ℕ) :
    (l.map (fun a => f a + D)).sum = (l.map f).sum + l.length * D := by
  rw [List.sum_map_add]
  congr 1
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    rw [ih, Nat.succ_mul]; ring

/-- The degree of the semi-Pfaffian set of the one-shot construction: the degree of `Y` plus,
for every disjunct of `Y`, one copy of the degree of the new equation. -/
theorem oneShotSet_deg_le {n m r : ℕ} (c : WilkiesDesign.E.EAChain (n + (1 + m)) r)
    (F : Fin (1 + m) → WilkiesDesign.E.EAPoly (n + (1 + m)) r) (L : List (Fin n))
    (Y : WilkiesDesign.E.SemiPf (n + (1 + m))) :
    (Work.WilE9.Ift.oneShotSet c F L Y).deg ≤
      Y.deg + Y.basics.length * (Work.WilE9.Ift.oneShotBasic c F L).deg := by
  have hinj := Work.WilE9.Ift.oneShotInj_injective n m
  have hstep : ∀ B : Basic (n + (1 + m)) Y.r,
      (Work.WilE5.conj
        (Work.WilE7.Basic.inl (Work.WilE8.Basic.extend (Work.WilE9.Ift.oneShotInj n m) B))
        (Work.WilE7.Basic.inr (Work.WilE9.Ift.oneShotBasic c F L))).deg
      = B.deg + (Work.WilE9.Ift.oneShotBasic c F L).deg := by
    intro B
    rw [Work.WilE5.conj_deg, basic_deg_inl, Work.WilE8.Extend.basic_deg_extend hinj B,
      basic_deg_inr]
  have hsum : ((Y.basics.map (fun B => Work.WilE5.conj
        (Work.WilE7.Basic.inl (Work.WilE8.Basic.extend (Work.WilE9.Ift.oneShotInj n m) B))
        (Work.WilE7.Basic.inr (Work.WilE9.Ift.oneShotBasic c F L)))).map Basic.deg).sum
      = (Y.basics.map (fun B => B.deg + (Work.WilE9.Ift.oneShotBasic c F L).deg)).sum := by
    congr 1
    rw [List.map_map]
    apply List.map_congr_left
    intro B _
    exact hstep B
  show ((Y.basics.map (fun B => Work.WilE5.conj
        (Work.WilE7.Basic.inl (Work.WilE8.Basic.extend (Work.WilE9.Ift.oneShotInj n m) B))
        (Work.WilE7.Basic.inr (Work.WilE9.Ift.oneShotBasic c F L)))).map Basic.deg).sum
      ≤ Y.deg + Y.basics.length * (Work.WilE9.Ift.oneShotBasic c F L).deg
  rw [hsum, sum_map_add_const]
  exact le_of_eq rfl

end Work.WilE9.Ift.OneShot
