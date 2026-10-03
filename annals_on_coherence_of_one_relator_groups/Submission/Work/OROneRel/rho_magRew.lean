import Mathlib
import Submission.Work.OROneRel.MagnusRewrite

namespace Work.OROneRel

set_option linter.unnecessarySeqFocus false

universe u

variable {α : Type u}

/-- The image in `FreeGroup α` of the letter `(x, i)` of the Magnus rewriting:
the conjugate `t ^ i * x * t ^ (-i)`.  This is the function whose free-group lift is
`rho t`. -/
private noncomputable def inn (t : α) (p : {x : α // x ≠ t} × ℤ) : FreeGroup α :=
  FreeGroup.of t ^ p.2 * FreeGroup.of (p.1 : α) * FreeGroup.of t ^ (-p.2)

/-- The contribution of a single letter to the exponent sum of `t`. -/
private noncomputable def letterEps (t : α) (p : α × Bool) : ℤ := by
  classical exact if p.1 = t then (if p.2 then (1 : ℤ) else -1) else 0

private lemma magRew_cons_eq (t : α) (acc : ℤ) (hd : α × Bool) (tl : List (α × Bool))
    (h : hd.1 = t) :
    magRew t acc (hd :: tl) = magRew t (acc + (if hd.2 then (1 : ℤ) else -1)) tl := by
  rw [magRew.eq_def, magRew.eq_def]
  cases hd with
  | mk a b => simp only at h; subst h; cases b <;> simp

private lemma magRew_cons_ne (t : α) (acc : ℤ) (hd : α × Bool) (tl : List (α × Bool))
    (h : hd.1 ≠ t) :
    magRew t acc (hd :: tl) = ((⟨hd.1, h⟩, acc), hd.2) :: magRew t acc tl := by
  rw [magRew.eq_def, magRew.eq_def]
  cases hd with
  | mk a b => simp only at h ⊢; simp [h]

private lemma wordEps_cons (t : α) (hd : α × Bool) (tl : List (α × Bool)) :
    wordEps t (hd :: tl) = letterEps t hd + wordEps t tl := by
  unfold wordEps letterEps; simp

private lemma letterEps_eq (t : α) (hd : α × Bool) (h : hd.1 = t) :
    letterEps t hd = (if hd.2 then (1 : ℤ) else -1) := by
  unfold letterEps; simp [h]

private lemma letterEps_eq_ne (t : α) (hd : α × Bool) (h : hd.1 ≠ t) :
    letterEps t hd = 0 := by
  unfold letterEps; simp [h]

private lemma cond_of_eq (t : α) (hd : α × Bool) (h : hd.1 = t) :
    cond hd.2 (FreeGroup.of hd.1) (FreeGroup.of hd.1)⁻¹ =
      FreeGroup.of t ^ (if hd.2 then (1 : ℤ) else -1) := by
  cases hd with
  | mk a b => simp only at h; subst h; cases b <;> simp

private lemma cond_inn (t : α) (hd : α × Bool) (acc : ℤ) (h : hd.1 ≠ t) :
    cond hd.2 (inn t (⟨hd.1, h⟩, acc)) (inn t (⟨hd.1, h⟩, acc))⁻¹ =
      FreeGroup.of t ^ acc * (cond hd.2 (FreeGroup.of hd.1) (FreeGroup.of hd.1)⁻¹) *
        FreeGroup.of t ^ (-acc) := by
  cases hd with
  | mk a b => cases b <;> simp [inn] <;> group

/-- The Magnus rewriting `magRew` intertwines the free-group product of the source word with the
free-group product of the rewritten word: the rewriting adds the frame `t ^ acc ... t ^ (-acc - ε)`,
where `ε` is the exponent sum of `t` in the remaining part of the word. -/
private lemma aux (t : α) (acc : ℤ) (L : List (α × Bool)) :
    List.prod ((magRew t acc L).map (fun x => cond x.2 (inn t x.1) (inn t x.1)⁻¹)) =
      FreeGroup.of t ^ acc *
        List.prod (L.map fun x => cond x.2 (FreeGroup.of x.1) (FreeGroup.of x.1)⁻¹) *
        FreeGroup.of t ^ (-(acc + wordEps t L)) := by
  induction L generalizing acc with
  | nil => simp [magRew, wordEps]
  | cons hd tl ih =>
    rw [wordEps_cons]
    by_cases h : hd.1 = t
    · rw [letterEps_eq t hd h]
      rw [magRew_cons_eq t acc hd tl h]
      rw [ih (acc + (if hd.2 then (1 : ℤ) else -1))]
      simp only [List.map_cons, List.prod_cons]
      rw [cond_of_eq t hd h]
      group
    · rw [letterEps_eq_ne t hd h]
      rw [magRew_cons_ne t acc hd tl h]
      simp only [List.map_cons, List.prod_cons]
      rw [ih acc]
      rw [cond_inn t hd acc h]
      group

theorem rho_magRew {α : Type u} (t : α) (acc : ℤ) (L : List (α × Bool)) :
    Work.OROneRel.rho t (FreeGroup.mk (Work.OROneRel.magRew t acc L)) =
      FreeGroup.of t ^ acc * FreeGroup.mk L *
        FreeGroup.of t ^ (-(acc + Work.OROneRel.wordEps t L)) := by
  have h1 : rho t (FreeGroup.mk (magRew t acc L)) =
      List.prod ((magRew t acc L).map (fun x => cond x.2 (inn t x.1) (inn t x.1)⁻¹)) := by
    simp only [rho, FreeGroup.lift_mk, inn]
  rw [h1]
  rw [show FreeGroup.mk L =
      List.prod (L.map fun x => cond x.2 (FreeGroup.of x.1) (FreeGroup.of x.1)⁻¹) from by
    rw [← FreeGroup.lift_of_apply (FreeGroup.mk L), FreeGroup.lift_mk]]
  exact aux t acc L

end Work.OROneRel
