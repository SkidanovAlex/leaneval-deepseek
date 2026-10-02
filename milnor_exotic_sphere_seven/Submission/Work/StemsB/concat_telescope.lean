import Mathlib

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Telescoping a concatenation of paths

`Path.concat` concatenates a finite sequence of paths with compatible endpoints.  If each factor
`F k` is homotopic (relative to endpoints) to the path `δ k ≫ δ (k+1)⁻¹` determined by a family of
paths `δ k : p k → c` ending at a common point `c`, then the concatenation telescopes: it is
homotopic to `δ 0 ≫ δ n⁻¹`.
-/

open scoped Topology

namespace Work.StemsB

/-- Cancellation of a "sandwich" of paths ending at a common point `c`: the outer factor `j` of the
middle path and the first factor of the right path cancel.  This is the algebraic heart of the
telescoping argument, isolated so that no `Fin`-index bookkeeping is involved. -/
private lemma trans_symm_sandwich {X : Type*} [TopologicalSpace X] {a b e c : X} (i : Path a c)
    (j : Path b c) (k : Path e c) :
    ((i.trans j.symm).trans (j.trans k.symm)).Homotopic (i.trans k.symm) :=
  (Path.Homotopic.trans_assoc i j.symm (j.trans k.symm)).trans
    ((Path.Homotopic.hcomp (Path.Homotopic.refl i)
        (Path.Homotopic.trans_assoc j.symm j k.symm).symm).trans
      ((Path.Homotopic.hcomp (Path.Homotopic.refl i)
          (Path.Homotopic.hcomp (Path.Homotopic.symm_trans j)
            (Path.Homotopic.refl k.symm))).trans
        (Path.Homotopic.hcomp (Path.Homotopic.refl i)
          (Path.Homotopic.refl_trans k.symm))))

/-- The telescoping statement for the concatenation of the paths `δ k ≫ δ (k+1)⁻¹`. -/
private lemma concat_telescope_aux {X : Type*} [TopologicalSpace X] (n : ℕ) :
    ∀ (p : Fin (n + 1) → X) (c : X) (δ : (k : Fin (n + 1)) → Path (p k) c),
      (Path.concat p (fun k => (δ k.castSucc).trans ((δ k.succ).symm))).Homotopic
        ((δ 0).trans ((δ (Fin.last n)).symm)) := by
  induction n with
  | zero =>
    intro p c δ
    rw [Path.concat_zero]
    exact (Path.Homotopic.trans_symm (δ 0)).symm
  | succ n ih =>
    intro p c δ
    rw [Path.concat_succ]
    simp only [Fin.succ_castSucc]
    have hIH := ih (p ∘ Fin.castSucc) c (fun k : Fin (n + 1) => δ (Fin.castSucc k))
    refine (Path.Homotopic.hcomp hIH (Path.Homotopic.refl _)).trans ?_
    simp only [Fin.succ_last, Fin.castSucc_zero]
    exact trans_symm_sandwich (δ 0) (δ ((Fin.last n).castSucc)) (δ (Fin.last (n + 1)))

/-- **Telescoping of a concatenation.**  If `F k` is homotopic to `(δ k).trans ((δ (k+1)).symm)`
for every `k`, then `Path.concat p F` is homotopic to `(δ 0).trans ((δ (last n)).symm)`. -/
theorem concat_telescope {X : Type*} [TopologicalSpace X] (n : ℕ) {p : Fin (n + 1) → X}
    (F : (k : Fin n) → Path (p k.castSucc) (p k.succ)) (c : X)
    (δ : (k : Fin (n + 1)) → Path (p k) c)
    (h : ∀ k : Fin n, (F k).Homotopic ((δ k.castSucc).trans ((δ k.succ).symm))) :
    (Path.concat p F).Homotopic ((δ 0).trans ((δ (Fin.last n)).symm)) :=
  (Path.Homotopic.concat_hcomp p F (fun k => (δ k.castSucc).trans ((δ k.succ).symm)) h).trans
    (concat_telescope_aux n p c δ)

end Work.StemsB
