/-
  WilE5 / Strat — the pivot minor of a child is the determinant defining `detOp`.

  The child's system is `childB c σ t = σ.B ++ [(peelVal c σ t, t.l)]`: the parent's equations
  with one extra equation (`peelVal`, whose pivot direction is `t.l`).  Hence

  * `hFun (childB c σ t)` is `Fin.lastCases (peelVal c σ t) (hFun σ.B)`, and
  * `pivFun (childB c σ t)` is `Fin.lastCases (yDir p t.l) (pivFun σ.B)`

  (up to the description of the index type by `List.get`).  Substituting these into the minor
  `(eaD (pivFun childB b) (hFun childB a))` therefore gives exactly the `(j+1) × (j+1)` matrix
  that defines `detOp c (hFun σ.B) (pivFun σ.B) (yDir p t.l) (peelVal c σ t)`, and `eaEval_detOp`
  identifies the two determinants.

  The one technical point is that `Fin (B ++ [x]).length` is not *definitionally* `Fin (B.length+1)`
  (because `List.length` does not unfold on a variable list), so the two determinants live over
  propositionally equal index types; the comparison is made through `Fin.cast` and
  `Matrix.det_submatrix_equiv_self`.
-/
import Mathlib
import Submission.Work.WilE5.Sys

namespace Work.WilE5.Strat
open Work.WilE5 WilkiesDesign WilkiesDesign.E

/-! ## §1. Reading the last element of `B ++ [x]` -/

/-- The first component of the `j`-th element of `B ++ [x]`: the last element for `j = B.length`
and the `j`-th element of `B` otherwise. -/
lemma hFun_append {p q r : ℕ} (B : List (EAPoly (p + q) r × Fin q))
    (x : EAPoly (p + q) r × Fin q)
    (hlen : (B ++ [x]).length = B.length + 1) (j : Fin (B.length + 1)) :
    hFun (B ++ [x]) (Fin.cast hlen.symm j) = Fin.lastCases x.1 (hFun B) j := by
  rcases Fin.eq_castSucc_or_eq_last j with ⟨i, rfl⟩ | h
  · rw [Fin.lastCases_castSucc]
    simp only [hFun, List.get_eq_getElem, Fin.val_cast, Fin.val_castSucc]
    exact congrArg Prod.fst (List.getElem_append_left i.isLt)
  · subst h
    rw [Fin.lastCases_last]
    simp only [hFun, List.get_eq_getElem, Fin.val_last, Fin.val_cast]
    exact congrArg Prod.fst (List.getElem_concat_length rfl _)

/-- The pivot direction of the `j`-th element of `B ++ [x]` (see `hFun_append`). -/
lemma pivFun_append {p q r : ℕ} (B : List (EAPoly (p + q) r × Fin q))
    (x : EAPoly (p + q) r × Fin q)
    (hlen : (B ++ [x]).length = B.length + 1) (j : Fin (B.length + 1)) :
    pivFun (B ++ [x]) (Fin.cast hlen.symm j) = Fin.lastCases (yDir p x.2) (pivFun B) j := by
  rcases Fin.eq_castSucc_or_eq_last j with ⟨i, rfl⟩ | h
  · rw [Fin.lastCases_castSucc]
    simp only [pivFun, List.get_eq_getElem, Fin.val_cast, Fin.val_castSucc]
    exact congrArg (fun y : EAPoly (p + q) r × Fin q => yDir p y.2)
      (List.getElem_append_left i.isLt)
  · subst h
    rw [Fin.lastCases_last]
    simp only [pivFun, List.get_eq_getElem, Fin.val_last, Fin.val_cast]
    exact congrArg (fun y : EAPoly (p + q) r × Fin q => yDir p y.2)
      (List.getElem_concat_length rfl _)

/-! ## §2. The determinant identity for `B ++ [x]` -/

/-- The pivot minor of `B ++ [x]` is the `detOp` determinant of the peeled operator `x`. -/
theorem det_eq_of_append {p q r : ℕ} (c : EAChain (p + q) r)
    (B : List (EAPoly (p + q) r × Fin q)) (x : EAPoly (p + q) r × Fin q)
    (z : Fin (p + q) → ℝ) :
    (Matrix.of fun (a b : Fin (B ++ [x]).length) =>
        eaEval c (eaD c (pivFun (B ++ [x]) b) (hFun (B ++ [x]) a)) z).det
      = eaEval c (detOp c (hFun B) (pivFun B) (yDir p x.2) x.1) z := by
  rw [eaEval_detOp]
  have hlen : (B ++ [x]).length = B.length + 1 := by simp
  have hsurj : Function.Surjective (Fin.cast hlen) := fun y =>
    ⟨Fin.cast hlen.symm y, by simp [Fin.cast_cast]⟩
  have hbij : Function.Bijective (Fin.cast hlen) := ⟨Fin.cast_injective hlen, hsurj⟩
  set A : Matrix (Fin (B.length + 1)) (Fin (B.length + 1)) ℝ :=
    Matrix.of fun a b =>
      eaEval c (eaD c (Fin.lastCases (yDir p x.2) (pivFun B) b)
        (Fin.lastCases x.1 (hFun B) a)) z with hA
  set e : Fin (B ++ [x]).length ≃ Fin (B.length + 1) :=
    Equiv.ofBijective (Fin.cast hlen) hbij with hee
  have heapp : ∀ m : Fin (B ++ [x]).length, e m = Fin.cast hlen m := fun m => by
    rw [hee, Equiv.ofBijective_apply]
  have hmat : (Matrix.of fun (a b : Fin (B ++ [x]).length) =>
        eaEval c (eaD c (pivFun (B ++ [x]) b) (hFun (B ++ [x]) a)) z) = A.submatrix e e := by
    ext a b
    rw [Matrix.submatrix_apply, hA, Matrix.of_apply, Matrix.of_apply]
    show eaEval c (eaD c (pivFun (B ++ [x]) b) (hFun (B ++ [x]) a)) z =
      eaEval c (eaD c (Fin.lastCases (yDir p x.2) (pivFun B) (e b))
        (Fin.lastCases x.1 (hFun B) (e a))) z
    rw [heapp a, heapp b]
    have hfa : hFun (B ++ [x]) a = Fin.lastCases x.1 (hFun B) (Fin.cast hlen a) := by
      have h := hFun_append B x hlen (Fin.cast hlen a)
      have hidx : Fin.cast hlen.symm (Fin.cast hlen a) = a := Fin.ext (by simp)
      rwa [hidx] at h
    have hpb : pivFun (B ++ [x]) b = Fin.lastCases (yDir p x.2) (pivFun B) (Fin.cast hlen b) := by
      have h := pivFun_append B x hlen (Fin.cast hlen b)
      have hidx : Fin.cast hlen.symm (Fin.cast hlen b) = b := Fin.ext (by simp)
      rwa [hidx] at h
    rw [hfa, hpb]
  rw [hmat, Matrix.det_submatrix_equiv_self e]

/-! ## §3. The requested lemma -/

theorem childB_det_eq {p q : ℕ} (X : WilkiesDesign.E.SemiPf (p + q)) (σ : Work.WilE5.St p q X.r)
    (t : Work.WilE5.Test q) (z : Fin (p + q) → ℝ) :
    (Matrix.of fun (a b : Fin (Work.WilE5.childB X.c σ t).length) =>
        WilkiesDesign.E.eaEval X.c (WilkiesDesign.E.eaD X.c
          (Work.WilE5.pivFun (Work.WilE5.childB X.c σ t) b)
          (Work.WilE5.hFun (Work.WilE5.childB X.c σ t) a)) z).det
      = WilkiesDesign.E.eaEval X.c
          (WilkiesDesign.E.detOp X.c (Work.WilE5.hFun σ.B) (Work.WilE5.pivFun σ.B)
            (Work.WilE5.yDir p t.l) (Work.WilE5.peelVal X.c σ t)) z := by
  exact det_eq_of_append X.c σ.B (Work.WilE5.peelVal X.c σ t, t.l) z

end Work.WilE5.Strat
