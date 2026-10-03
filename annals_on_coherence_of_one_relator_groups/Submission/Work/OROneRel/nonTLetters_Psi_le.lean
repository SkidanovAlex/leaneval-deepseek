import Mathlib
import Submission.Work.OROneRel.psiSubstDefs
import Submission.Work.OROneRel.ntDefs

/-!
# The Magnus/Putman substitution does not increase the number of non-`t` letters

The main result `nonTLetters_Psi_le` is the combinatorial step of the "all exponent sums nonzero"
case of the Freiheitssatz: the substitution `Psi r t x` (`t ↦ t ^ σ_x(r)`, `x ↦ x * t ^ (-σ_t(r))`,
all other generators fixed) applied to the relator `r` produces a word whose reduced form has no more
letters different from `t` than `r` itself.

The proof goes through the letter count `nt` of `Submission.Work.OROneRel.ntDefs` (the number of
letters of a word different from `t`, i.e. the length of the Magnus rewriting): `nonTLetters t w` is
by definition `nt t w.toWord`, `nt` is subadditive under products (`nt_prod_le`), and each generator
image under `Psi` contributes at most one non-`t` letter, while `of t ^ k` contributes none
(`nt_of_zpow`).
-/

namespace Work.OROneRel

universe u

variable {α : Type u}

attribute [local instance] Classical.propDecidable

/-- `nonTLetters t w` is exactly the `nt`-count of the reduced word of `w`. -/
theorem nonTLetters_eq_nt {α : Type*} (t : α) (w : FreeGroup α) :
    nonTLetters t w = nt t (FreeGroup.toWord w) := by
  classical
  rw [nt_eq_countP]
  simp only [nonTLetters]

/-- Summing a function over a doubly-mapped list. -/
theorem sum_map_map {β γ : Type*} (f : γ → ℕ) (g : β → γ) (l : List β) :
    ((l.map g).map f).sum = (l.map (fun b => f (g b))).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    calc (((a :: l).map g).map f).sum
        = f (g a) + ((l.map g).map f).sum := rfl
      _ = f (g a) + ((l.map (fun b => f (g b))).sum) := by rw [ih]
      _ = ((a :: l).map (fun b => f (g b))).sum := rfl

/-- A sum of pointwise bounds against the indicators of a predicate is bounded by the `countP` of
that predicate. -/
theorem sum_map_le_countP {β : Type*} (q : β → Bool) (f : β → ℕ) (l : List β)
    (h : ∀ b ∈ l, f b ≤ if q b then 1 else 0) :
    (l.map f).sum ≤ l.countP q := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ha : f a ≤ if q a then 1 else 0 := h a (by simp)
    have hl : ∀ b ∈ l, f b ≤ if q b then 1 else 0 := fun b hb => h b (by simp [hb])
    rw [List.map_cons, List.sum_cons, List.countP_cons]
    exact le_trans (Nat.add_le_add ha (ih hl)) (le_of_eq (Nat.add_comm _ _))

/-- The image of `of t` under `Psi` is a power of `of t`, hence contributes no non-`t` letter. -/
theorem nt_Psi_of_eq_t {r : FreeGroup α} (t x : α) :
    nt t (Psi r t x (FreeGroup.of t)).toWord = 0 := by
  classical
  rw [Psi_of_eq_t, nt_of_zpow]

/-- Each generator image under `Psi` contributes at most one non-`t` letter. -/
theorem nt_Psi_of_le {r : FreeGroup α} {t x : α} (htx : x ≠ t) (a : α) :
    nt t (Psi r t x (FreeGroup.of a)).toWord ≤ if decide (a ≠ t) then 1 else 0 := by
  classical
  by_cases ha : a = t
  · have h0 : (if decide (a ≠ t) then (1 : ℕ) else 0) = 0 := by simp [ha]
    have h1 : Psi r t x (FreeGroup.of a) = FreeGroup.of t ^ (sigma x r).toAdd := by
      rw [ha, Psi_of_eq_t]
    calc nt t (Psi r t x (FreeGroup.of a)).toWord
        = nt t (FreeGroup.of t ^ (sigma x r).toAdd).toWord := by rw [h1]
      _ = 0 := nt_of_zpow t _
      _ ≤ (if decide (a ≠ t) then (1 : ℕ) else 0) := le_of_eq h0.symm
  · have h0 : (if decide (a ≠ t) then (1 : ℕ) else 0) = 1 := by simp [ha]
    by_cases hax : a = x
    · have hxt : x ≠ t := fun h => ha (hax.trans h)
      have h1 : Psi r t x (FreeGroup.of a)
          = FreeGroup.of x * FreeGroup.of t ^ (-(sigma t r).toAdd) := by
        rw [hax, Psi_of_eq_x htx]
      calc nt t (Psi r t x (FreeGroup.of a)).toWord
          = nt t (FreeGroup.of x * FreeGroup.of t ^ (-(sigma t r).toAdd)).toWord := by rw [h1]
        _ ≤ nt t (FreeGroup.of x).toWord
              + nt t ((FreeGroup.of t : FreeGroup α) ^ (-(sigma t r).toAdd)).toWord :=
              nt_mul_le t _ _
        _ = 1 := by
              rw [nt_of_zpow, FreeGroup.toWord_of, nt_singleton]
              simp [hxt]
        _ ≤ (if decide (a ≠ t) then (1 : ℕ) else 0) := le_of_eq h0.symm
    · have h1 : Psi r t x (FreeGroup.of a) = FreeGroup.of a := Psi_of_ne ha hax
      calc nt t (Psi r t x (FreeGroup.of a)).toWord
          = nt t (FreeGroup.of a).toWord := by rw [h1]
        _ = 1 := by
              rw [FreeGroup.toWord_of, nt_singleton]
              simp [ha]
        _ ≤ (if decide (a ≠ t) then (1 : ℕ) else 0) := le_of_eq h0.symm

/-- `PsiFun` is `Psi` on generators, so the letter estimates transfer to the `bif`-form in which
`FreeGroup.lift_mk` presents the images. -/
theorem nt_bif_le {r : FreeGroup α} {t x : α} (htx : x ≠ t) (a : α) (b : Bool) :
    nt t (bif b then PsiFun r t x a else (PsiFun r t x a)⁻¹).toWord
      ≤ if decide (a ≠ t) then 1 else 0 := by
  classical
  have hkey : PsiFun r t x a = Psi r t x (FreeGroup.of a) :=
    (FreeGroup.lift_apply_of (f := PsiFun r t x) (x := a)).symm
  cases b
  · show nt t ((PsiFun r t x a)⁻¹).toWord ≤ if decide (a ≠ t) then 1 else 0
    rw [nt_inv, hkey]
    exact nt_Psi_of_le htx a
  · show nt t (PsiFun r t x a).toWord ≤ if decide (a ≠ t) then 1 else 0
    rw [hkey]
    exact nt_Psi_of_le htx a

/-- **The Magnus/Putman substitution does not increase the number of non-`t` letters.** -/
theorem nonTLetters_Psi_le {α : Type*} (r : FreeGroup α) (t x : α) (htx : x ≠ t) :
    Work.OROneRel.nonTLetters t (Work.OROneRel.Psi r t x r) ≤ Work.OROneRel.nonTLetters t r := by
  classical
  obtain ⟨F, hF⟩ : ∃ F : α × Bool → FreeGroup α,
      F = fun p => bif p.2 then PsiFun r t x p.1 else (PsiFun r t x p.1)⁻¹ := ⟨_, rfl⟩
  have hL : Psi r t x r = (List.map F (FreeGroup.toWord r)).prod := by
    have h1 : Psi r t x r =
        FreeGroup.lift (PsiFun r t x) (FreeGroup.mk (FreeGroup.toWord r)) := by
      rw [FreeGroup.mk_toWord]
      rfl
    rw [h1, hF]
    exact FreeGroup.lift_mk
  calc nonTLetters t (Psi r t x r)
      = nt t (Psi r t x r).toWord := nonTLetters_eq_nt t _
    _ = nt t ((List.map F (FreeGroup.toWord r)).prod).toWord := by rw [hL]
    _ ≤ (List.map (fun y : FreeGroup α => nt t y.toWord)
          (List.map F (FreeGroup.toWord r))).sum := nt_prod_le t _
    _ = (List.map (fun p : α × Bool => nt t (F p).toWord) (FreeGroup.toWord r)).sum :=
          sum_map_map _ _ _
    _ ≤ (FreeGroup.toWord r).countP (fun p : α × Bool => decide (p.1 ≠ t)) :=
          sum_map_le_countP _ _ _ (fun p _ => by
            rw [hF]
            exact nt_bif_le htx p.1 p.2)
    _ = nt t (FreeGroup.toWord r) := (nt_eq_countP t (FreeGroup.toWord r)).symm
    _ = nonTLetters t r := (nonTLetters_eq_nt t r).symm

end Work.OROneRel
