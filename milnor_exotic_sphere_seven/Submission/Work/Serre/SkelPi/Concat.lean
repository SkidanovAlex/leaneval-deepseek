import Mathlib
import Submission.Work.Serre.SkelPi.Basic

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Iterated composition of a sequence of composable paths, at the level of homotopy classes

`Path.concat` composes a sequence of composable paths; this file provides the corresponding
operation `qconcat` on the quotients `Path.Homotopic.Quotient` (the fundamental groupoid), together
with the compatibility `qconcat_mk` with `Path.concat`.
-/

open scoped Topology unitInterval

namespace Work.Serre.SkelPi

noncomputable section

/-- **The iterated composition of a sequence of composable quotient paths.** -/
def qconcat {X : Type} [TopologicalSpace X] : {n : ℕ} → (p : Fin (n + 1) → X) →
    ((k : Fin n) → Path.Homotopic.Quotient (p k.castSucc) (p k.succ)) →
    Path.Homotopic.Quotient (p 0) (p (Fin.last n))
  | 0, p, _ => Path.Homotopic.Quotient.refl (p 0)
  | (n + 1), p, F =>
      (qconcat (n := n) (fun k : Fin (n + 1) => p k.castSucc) (fun k => F k.castSucc)).trans
        (F (Fin.last n))

@[simp] theorem qconcat_zero {X : Type} [TopologicalSpace X] (p : Fin 1 → X)
    (F : (k : Fin 0) → Path.Homotopic.Quotient (p k.castSucc) (p k.succ)) :
    qconcat p F = Path.Homotopic.Quotient.refl (p 0) := rfl

theorem qconcat_succ {X : Type} [TopologicalSpace X] {n : ℕ} (p : Fin (n + 2) → X)
    (F : (k : Fin (n + 1)) → Path.Homotopic.Quotient (p k.castSucc) (p k.succ)) :
    qconcat p F = (qconcat (fun k : Fin (n + 1) => p k.castSucc) (fun k => F k.castSucc)).trans
      (F (Fin.last n)) := rfl

end

end Work.Serre.SkelPi

namespace Work.Serre.SkelPi

noncomputable section

/-- **`qconcat` is the class of `Path.concat`.** -/
theorem qconcat_mk {X : Type} [TopologicalSpace X] : ∀ {n : ℕ} (p : Fin (n + 1) → X)
    (F : (k : Fin n) → Path (p k.castSucc) (p k.succ)),
    Path.Homotopic.Quotient.mk (Path.concat p F)
      = qconcat p (fun k => Path.Homotopic.Quotient.mk (F k)) := by
  intro n
  induction n with
  | zero =>
    intro p F
    rw [Path.concat_zero, qconcat_zero]
    rfl
  | succ n ih =>
    intro p F
    rw [Path.concat_succ, qconcat_succ]
    exact (Path.Homotopic.Quotient.mk_trans _ _).trans
      (congrArg₂ Path.Homotopic.Quotient.trans (ih _ _) rfl)

/-- The path-level cast of a concatenation. -/
theorem Path_cast_trans {Z : Type} [TopologicalSpace Z] {a b c a' c' : Z} (p : Path a b)
    (q : Path b c) (hx : a' = a) (hy : c' = c) :
    (p.trans q).cast hx hy = (p.cast hx rfl).trans (q.cast rfl hy) :=
  Path.ext rfl

/-- The path-level cast of an inverted path. -/
theorem Path_cast_symm {Z : Type} [TopologicalSpace Z] {a b a' b' : Z} (p : Path a b)
    (hx : a' = a) (hy : b' = b) : (p.symm).cast hy hx = (p.cast hx hy).symm :=
  Path.ext rfl

/-- The quotient-level cast of a concatenation. -/
theorem Quotient_cast_trans {Z : Type} [TopologicalSpace Z] {x y z x' z' : Z}
    (P : Path.Homotopic.Quotient x y) (Q : Path.Homotopic.Quotient y z)
    (hx : x' = x) (hy : z' = z) :
    (P.trans Q).cast hx hy = (P.cast hx rfl).trans (Q.cast rfl hy) := by
  induction P using Quotient.inductionOn with
  | h p =>
    induction Q using Quotient.inductionOn with
    | h q =>
      erw [← Path.Homotopic.Quotient.mk_trans p q,
        ← Path.Homotopic.Quotient.mk_cast (p.trans q) hx hy,
        ← Path.Homotopic.Quotient.mk_cast p hx rfl,
        ← Path.Homotopic.Quotient.mk_cast q rfl hy,
        ← Path.Homotopic.Quotient.mk_trans (p.cast hx rfl) (q.cast rfl hy),
        Path_cast_trans p q hx hy]

/-- The quotient-level cast of an inverted path. -/
theorem Quotient_cast_symm {Z : Type} [TopologicalSpace Z] {x y x' y' : Z}
    (P : Path.Homotopic.Quotient x y) (hx : x' = x) (hy : y' = y) :
    (P.symm).cast hy hx = (P.cast hx hy).symm := by
  induction P using Quotient.inductionOn with
  | h p =>
    erw [← Path.Homotopic.Quotient.mk_symm p,
      ← Path.Homotopic.Quotient.mk_cast (p.symm) hy hx,
      ← Path.Homotopic.Quotient.mk_cast p hx hy,
      ← Path.Homotopic.Quotient.mk_symm (p.cast hx hy),
      Path_cast_symm p hx hy]

end

end Work.Serre.SkelPi
