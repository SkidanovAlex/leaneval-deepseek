import Mathlib
import Submission.Work.Diff.STE.FlatPDE
import Submission.Work.Diff.STE.flat.TowerDefs
import Submission.Work.Diff.STE.flat.limit_prep
import Submission.Work.Diff.STE.flat.limit_assembly
import Submission.Work.Diff.STE.flat.exists_limit_coeff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The limit of the Galerkin solutions solves the flat DeTurck problem

`Work.Diff.STE.flat.limit_solves`: the target of this file.  The Arzelà–Ascoli step
(`exists_limit_coeff`) produces the limit coefficient family `cinf`; the assembly
`Work.Diff.STE.flat.solvesOn_of_limit` (in `flat/limit_assembly.lean`) turns its properties into a
solution of `∂_t u = Φ (·, jet u)` on `[0, τ)`.

The only missing remark is the *shape* of the decay hypothesis: `exists_limit_coeff` produces
`‖cinf t k i j‖ * ⟨k⟩^M ≤ C * (1 + Blim (2M))`, while the assembly wants the constant to be
`t`-independent and of the plain form `≤ C`; this is a one-line weakening.
-/

namespace Work.Diff.STE.flat

open Work.Diff.STE.Flat
open scoped BigOperators
open Filter Set

noncomputable section

variable {n : ℕ}

theorem limit_solves {n : ℕ} (hn : 1 ≤ n)
    (Φ : (Fin n → ℝ) × Work.Diff.STE.Flat.Jet n → Work.Diff.STE.Flat.MatC n)
    (hshape : Work.Diff.STE.Flat.IsDeTurckNonlin Φ)
    (k : ℕ) (hk : Fintype.card (Fin n) + 4 < 2 * k)
    (τ : ℝ) (hτ : 0 < τ) (lam : ℝ) (hlam : 0 < lam)
    (Blim : ℕ → ℝ) (hBlim : ∀ j : ℕ, 0 ≤ Blim j)
    (u₀ : Work.Diff.STE.Flat.Torus n)
    (hu₀ : ContDiff ℝ (⊤ : ℕ∞) u₀) (hper₀ : Work.Diff.STE.Periodic1 u₀)
    (Nb : ℕ → ℕ) (hNb : Filter.Tendsto Nb Filter.atTop Filter.atTop)
    (c : ℕ → ℝ → (Fin n → ℤ) → Work.Diff.STE.Flat.MatC n)
    (hsol : ∀ m, ∀ t ∈ Set.Ico (0 : ℝ) τ, ∀ k' ∈ Work.Diff.STE.Flat.box n (Nb m),
      ∀ (i j : Fin n),
      HasDerivAt (fun s => c m s k' i j)
        (Work.Diff.STE.fourierCoeff (fun x =>
          Φ (x, Work.Diff.STE.Flat.jetM (Work.Diff.STE.Flat.seriesFunM (c m t)) x) i j) k') t)
    (hell : ∀ m, ∀ t ∈ Set.Ico (0 : ℝ) τ, ∀ (x : Fin n → ℝ) (v : Fin n → ℝ),
      lam * ∑ i, (v i) ^ 2 ≤ ∑ i, ∑ j,
        Work.Diff.STE.Flat.reMat (Work.Diff.STE.Flat.seriesFunM (c m t) x) i j * v i * v j)
    (hsym : ∀ m, ∀ t ∈ Set.Ico (0 : ℝ) τ, ∀ (x : Fin n → ℝ) (i j : Fin n),
      Work.Diff.STE.Flat.reMat (Work.Diff.STE.Flat.seriesFunM (c m t) x) i j
        = Work.Diff.STE.Flat.reMat (Work.Diff.STE.Flat.seriesFunM (c m t) x) j i)
    (hsupp : ∀ (m : ℕ) (t : ℝ) (k' : Fin n → ℤ), k' ∉ Work.Diff.STE.Flat.box n (Nb m) →
      c m t k' = 0)
    (hbdd : ∀ m, ∀ t ∈ Set.Ico (0 : ℝ) τ, ∀ j : ℕ,
      Work.Diff.STE.Flat.ENormSqFull j (Work.Diff.STE.Flat.seriesFunM (c m t)) ≤ Blim j)
    (hinit : ∀ x : Fin n → ℝ,
      Filter.Tendsto (fun m => Work.Diff.STE.Flat.seriesFunM (c m 0) x) Filter.atTop
        (nhds (u₀ x))) :
    ∃ u : ℝ → Work.Diff.STE.Flat.Torus n,
      Work.Diff.STE.Flat.SolvesOn Φ τ u ∧ (∀ x, u 0 x = u₀ x) ∧
      (∀ t ∈ Set.Ico (0 : ℝ) τ, ∀ x, Work.Diff.STE.Flat.PosDefM (u t x)) := by
  obtain ⟨cinf, h0, hper, hpd, hdec0, hpde0⟩ :=
    exists_limit_coeff Φ hshape τ hτ lam hlam Blim hBlim u₀ Nb hNb c hsol hell hsym hsupp hbdd
      hinit
  -- the decay bound in the form required by the assembly
  have hdec : ∀ M : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Ico (0 : ℝ) τ,
      ∀ (k' : Fin n → ℤ) (a b : Fin n), ‖cinf t k' a b‖ * (wt k') ^ M ≤ C := by
    intro M
    obtain ⟨C, hC, hCb⟩ := hdec0 M
    refine ⟨C * (1 + Blim (2 * M)), mul_nonneg hC (by linarith [hBlim (2 * M)]), ?_⟩
    intro t ht k' a b
    exact (hCb t ht k' a b).trans (le_of_eq (by ring))
  -- the level-one equation, in the form of the tower
  have hpde : ∀ t ∈ Set.Ico (0 : ℝ) τ, ∀ (k' : Fin n → ℤ) (a b : Fin n),
      HasDerivWithinAt (fun s : ℝ => dd Φ cinf 0 s k' a b)
        (dd Φ cinf 1 t k' a b) (Set.Ico (0 : ℝ) τ) t := by
    intro t ht k' a b
    rw [dd_one_apply]
    exact hpde0 t ht k' a b
  obtain ⟨hsol, hpdW⟩ := solvesOn_of_limit Φ hshape k hk hτ cinf hdec hper hpd hpde
  exact ⟨fun t => seriesFunM (cinf t), hsol, fun x => h0 x, hpdW⟩

end

end Work.Diff.STE.flat
