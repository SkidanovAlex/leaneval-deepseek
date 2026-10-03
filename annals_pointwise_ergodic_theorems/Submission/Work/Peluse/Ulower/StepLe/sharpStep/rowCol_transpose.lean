import Mathlib
import Submission.Work.Peluse.Ulower.StepLe.ddiSharp.Defs

/-!
# Exchanging the row and column decompositions of `□_σ(H)`

This is the purely combinatorial transposition behind Peluse's Lemma 7.4 at level `σ + 1`.

Writing `Θ_σ(K) = ThetaSet σ D K` and
`Bσ = thetaBox σ D ×ˢ (thetaBox σ D ×ˢ thetaBox σ D)`, the level-`σ` cube set of a set of shift
pairs `K` satisfies `Θ_σ(K) ⊆ Bσ` (`thetasubset`), while

* the *row* fibre of a level-`(σ+1)` set `H` at the first coordinates `(a,b)` is
  `rowFibre H a b = {(u,v) ∈ θBox × θBox | (Fin.cons a u, Fin.cons b v) ∈ H}`, and
* the *column* fibre at a level-`σ` triple `q` is
  `colFibre H q = {ab ∈ B1 | q ∈ Θ_σ(rowFibre H (ab.1 0) (ab.2 0))}`.

Both sides of the identity therefore sum `f (ab, q)` over the *same* set of pairs
`{(ab, q) | ab ∈ B1, q ∈ Θ_σ(rowFibre H (ab.1 0) (ab.2 0))}`, once by rows and once by columns;
the equality is `Finset.sum_comm` together with the two `Finset.sum_filter` presentations
(`sum_eq_sum_ite`).
-/

namespace Work.Peluse.Ulower.StepLe.sharpStep

/-- The level-`σ` cube set of any shift-pair set is contained in the level-`σ` box
`Bσ = thetaBox σ D ×ˢ (thetaBox σ D ×ˢ thetaBox σ D)`. -/
private lemma thetasubset {σ D : ℕ} (H' : Finset ((Fin σ → ℤ) × (Fin σ → ℤ))) :
    Work.Peluse.Ulower.ThetaSet σ D H' ⊆
      Work.Peluse.Ulower.thetaBox σ D ×ˢ
        (Work.Peluse.Ulower.thetaBox σ D ×ˢ Work.Peluse.Ulower.thetaBox σ D) := by
  intro k hk
  simp only [Work.Peluse.Ulower.ThetaSet, Finset.mem_filter] at hk
  exact hk.1

/-- Rewriting a sum over `s ⊆ t` as a sum over `t` of the indicator of `s`. -/
private lemma sum_eq_sum_ite {α M : Type*} [DecidableEq α] [AddCommMonoid M]
    (s t : Finset α) (h : s ⊆ t) (f : α → M) :
    (∑ x ∈ s, f x) = ∑ x ∈ t, if x ∈ s then f x else 0 := by
  have hEq : t.filter (fun x => x ∈ s) = s := by
    ext x; simp only [Finset.mem_filter]
    exact ⟨fun hx => hx.2, fun hx => ⟨h hx, hx⟩⟩
  rw [← Finset.sum_filter, hEq]

theorem rowCol_transpose {σ D : ℕ}
    (H : Finset ((Fin (σ+1) → ℤ) × (Fin (σ+1) → ℤ)))
    {M : Type*} [AddCommMonoid M]
    (f : ((Fin 1 → ℤ) × (Fin 1 → ℤ)) ×
          ((Fin σ → ℤ) × (Fin σ → ℤ) × (Fin σ → ℤ)) → M) :
    (∑ ab ∈ (Work.Peluse.Ulower.thetaBox 1 D ×ˢ Work.Peluse.Ulower.thetaBox 1 D),
        ∑ q ∈ Work.Peluse.Ulower.ThetaSet σ D
              (Work.Peluse.Ulower.StepLe.rowFibre σ D H (ab.1 0) (ab.2 0)), f (ab, q))
      = ∑ q ∈ (Work.Peluse.Ulower.thetaBox σ D ×ˢ (Work.Peluse.Ulower.thetaBox σ D ×ˢ
              Work.Peluse.Ulower.thetaBox σ D)),
          ∑ ab ∈ Work.Peluse.Ulower.StepLe.colFibre σ D H q, f (ab, q) := by
  classical
  -- Present the left-hand side as a sum over the box `Bσ`, using `Θ_σ(rowFibre H ab) ⊆ Bσ`.
  have hL : (∑ ab ∈ (Work.Peluse.Ulower.thetaBox 1 D ×ˢ Work.Peluse.Ulower.thetaBox 1 D),
        ∑ q ∈ Work.Peluse.Ulower.ThetaSet σ D
              (Work.Peluse.Ulower.StepLe.rowFibre σ D H (ab.1 0) (ab.2 0)), f (ab, q))
      = ∑ ab ∈ (Work.Peluse.Ulower.thetaBox 1 D ×ˢ Work.Peluse.Ulower.thetaBox 1 D),
          ∑ q ∈ (Work.Peluse.Ulower.thetaBox σ D ×ˢ (Work.Peluse.Ulower.thetaBox σ D ×ˢ
              Work.Peluse.Ulower.thetaBox σ D)),
            (if q ∈ Work.Peluse.Ulower.ThetaSet σ D
              (Work.Peluse.Ulower.StepLe.rowFibre σ D H (ab.1 0) (ab.2 0))
              then f (ab, q) else 0) := by
    refine Finset.sum_congr rfl (fun ab _ => ?_)
    exact sum_eq_sum_ite _ _ (thetasubset _) _
  -- Present the right-hand side in the same form, using the definition of `colFibre`.
  have hR : (∑ q ∈ (Work.Peluse.Ulower.thetaBox σ D ×ˢ (Work.Peluse.Ulower.thetaBox σ D ×ˢ
              Work.Peluse.Ulower.thetaBox σ D)),
          ∑ ab ∈ Work.Peluse.Ulower.StepLe.colFibre σ D H q, f (ab, q))
      = ∑ q ∈ (Work.Peluse.Ulower.thetaBox σ D ×ˢ (Work.Peluse.Ulower.thetaBox σ D ×ˢ
              Work.Peluse.Ulower.thetaBox σ D)),
          ∑ ab ∈ (Work.Peluse.Ulower.thetaBox 1 D ×ˢ Work.Peluse.Ulower.thetaBox 1 D),
            (if q ∈ Work.Peluse.Ulower.ThetaSet σ D
              (Work.Peluse.Ulower.StepLe.rowFibre σ D H (ab.1 0) (ab.2 0))
              then f (ab, q) else 0) := by
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [Work.Peluse.Ulower.StepLe.colFibre, Finset.sum_filter]
  rw [hL, hR, Finset.sum_comm]

end Work.Peluse.Ulower.StepLe.sharpStep
