import Mathlib
import Submission.Work.OROneRel.mrslExp

universe u

namespace Work.OROneRel

/-!  Auxiliary lemmas computing `FreeGroup.mk` on the elementary words used by the expansion. -/

private theorem mk_singleton_aux {α : Type u} (a : α) (b : Bool) :
    FreeGroup.mk [(a, b)] = (FreeGroup.of a) ^ (if b then (1 : ℤ) else -1) := by
  cases b
  · rw [show (if (false : Bool) then (1 : ℤ) else -1) = (-1 : ℤ) from rfl, zpow_neg_one]
    simp only [FreeGroup.of, FreeGroup.inv_mk]
    rfl
  · rw [show (if (true : Bool) then (1 : ℤ) else -1) = (1 : ℤ) from rfl, zpow_one]
    rfl

private theorem mk_cons_aux {α : Type u} (p : α × Bool) (L : List (α × Bool)) :
    FreeGroup.mk (p :: L) =
      (FreeGroup.of p.1) ^ (if p.2 then (1 : ℤ) else -1) * FreeGroup.mk L := by
  rw [← List.singleton_append, ← FreeGroup.mul_mk, mk_singleton_aux]

/-- `FreeGroup.mk` of a list of signed letters is the product of the corresponding powers. -/
private theorem mk_eq_prod_map {α : Type u} (L : List (α × Bool)) :
    FreeGroup.mk L =
      (L.map (fun p => if p.2 then FreeGroup.of p.1 else (FreeGroup.of p.1)⁻¹)).prod := by
  have h : FreeGroup.lift (FreeGroup.of : α → FreeGroup α) = MonoidHom.id (FreeGroup α) := by
    ext x; simp
  have key : FreeGroup.mk L = (FreeGroup.lift (FreeGroup.of : α → FreeGroup α)) (FreeGroup.mk L) := by
    rw [h]; rfl
  rw [key, FreeGroup.lift_mk]
  congr 1
  apply List.map_congr_left
  intro x _; cases x.2 <;> rfl

private theorem mk_replicate_true {α : Type u} (a : α) (k : ℕ) :
    FreeGroup.mk (List.replicate k (a, true)) = (FreeGroup.of a) ^ (k : ℤ) := by
  rw [mk_eq_prod_map, List.map_replicate, List.prod_replicate, zpow_natCast]
  rfl

private theorem mk_replicate_false {α : Type u} (a : α) (k : ℕ) :
    FreeGroup.mk (List.replicate k (a, false)) = ((FreeGroup.of a) ^ (k : ℤ))⁻¹ := by
  rw [mk_eq_prod_map, List.map_replicate, List.prod_replicate, zpow_natCast, ← inv_pow]
  rfl

/-- `FreeGroup.mk` of the signed run `a ^ n` is the power `of a ^ n`. -/
theorem mrsl_mk_runLetters {α : Type u} (a : α) (n : ℤ) :
    FreeGroup.mk (Work.OROneRel.runLetters a n) = (FreeGroup.of a) ^ n := by
  rw [Work.OROneRel.runLetters]
  cases n with
  | ofNat k =>
    cases k with
    | zero => simp [FreeGroup.one_eq_mk]
    | succ k =>
      have h1 : (Int.ofNat (k + 1)).natAbs = k + 1 := Int.natAbs_natCast _
      have h2 : decide (0 < (Int.ofNat (k + 1))) = true := by simp
      rw [h1, h2, mk_replicate_true]
      norm_cast
  | negSucc k =>
    have h1 : (Int.negSucc k).natAbs = k + 1 := Int.natAbs_negSucc k
    have h2 : decide (0 < (Int.negSucc k)) = false := by rw [decide_eq_false_iff_not]; omega
    rw [h1, h2, mk_replicate_false, zpow_negSucc]
    rfl

/-- The expansion of a single decorated letter `((c,i),b)` is the conjugate `t^i * c^b * t^{-i}`. -/
private theorem expandLetter_pair_aux {α : Type u} (t : α) (c : {x : α // x ≠ t}) (i : ℤ)
    (b : Bool) :
    Work.OROneRel.expandLetter t ((c, i), b) =
      (FreeGroup.of t) ^ i * (FreeGroup.of (c : α)) ^ (if b then (1 : ℤ) else -1) *
        (FreeGroup.of t) ^ (-i) := rfl

theorem mrsl_expAux_mk {β : Type u} (t : β) (a : ℤ) (D : List (({x : β // x ≠ t} × ℤ) × Bool)) :
    FreeGroup.mk (Work.OROneRel.expAux t a D) =
      (FreeGroup.of t) ^ (-a) * (D.map (Work.OROneRel.expandLetter t)).prod := by
  induction D generalizing a with
  | nil =>
    rw [Work.OROneRel.expAux_nil, List.map_nil, List.prod_nil, mul_one]
    exact mrsl_mk_runLetters t (-a)
  | cons p rest ih =>
    obtain ⟨⟨c, i⟩, b⟩ := p
    rw [Work.OROneRel.expAux_cons, List.map_cons, List.prod_cons, ← FreeGroup.mul_mk,
      mrsl_mk_runLetters, mk_cons_aux, ih i, expandLetter_pair_aux,
      show i - a = -a + i from by ring, zpow_add]
    simp only [mul_assoc]

end Work.OROneRel
