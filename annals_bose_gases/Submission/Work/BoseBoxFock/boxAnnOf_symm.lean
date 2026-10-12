import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseDict.Defs2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.boxAnnOf_symm` — the box annihilation of a superposition is symmetric

The box annihilation of the superposition `η_w = Σ_l w_l e_l` on the `k`-particle space is

    (boxAnnOf e w k Θ)(y) = √(k+1) ∫_z conj(η_w z) · Θ (z, y)

(`Work.BoseDict.boxAnnOf`).  If `Θ` is a symmetric `(k+1)`-particle function — invariance under
every permutation of the particle labels, which is exactly the hypothesis `hΘsym` of the box ↔
model dictionary — then `boxAnnOf e w k Θ` is a **symmetric** `k`-particle function.

The only content is the pointwise identity of the `(k+1)`-particle arguments:
for every `z ∈ ℝ³` the configurations `(z, y ∘ σ)` and `(z, y)` differ by a permutation of the
particle labels *fixing the first slot*, namely

    τ := Equiv.Perm.decomposeFin.symm (0, σ) : Equiv.Perm (Fin (k+1)),
    τ 0 = 0 ,   τ (i.succ) = (σ i).succ .

Hence `Fin.cons z (y ∘ σ) = (Fin.cons z y) ∘ τ` (`Fin.cases` + the two `decomposeFin` evaluation
lemmas) and `hΘsym τ` gives `Θ (Fin.cons z (y ∘ σ)) = Θ (Fin.cons z y)`; the integrands are then
equal, so the integrals are equal.

Everything is `sorry`-free and rests only on Mathlib.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

open Work.BoseDict

set_option autoImplicit false

/-- **Symmetry of the box annihilation**: for a symmetric `(k+1)`-particle function `Θ` the box
annihilation of the superposition `η_w` is a symmetric `k`-particle function. -/
theorem boxAnnOf_symm {m k : ℕ} {e : Fin m → Work.BoseDict.Sp → ℂ} (w : Fin m → ℝ)
    (Θ : Work.BoseDict.Xn (k + 1) → ℂ)
    (hΘsym : ∀ σ : Equiv.Perm (Fin (k + 1)), ∀ x : Work.BoseDict.Xn (k + 1), Θ (x ∘ ⇑σ) = Θ x) :
    ∀ σ : Equiv.Perm (Fin k), ∀ y : Work.BoseDict.Xn k,
      Work.BoseDict.boxAnnOf e w k Θ (y ∘ ⇑σ) = Work.BoseDict.boxAnnOf e w k Θ y := by
  intro σ y
  -- the `(k+1)`-particle arguments agree after the permutation `τ = decomposeFin.symm (0, σ)`
  have hkey : ∀ z : Sp, Θ (Fin.cons z (y ∘ ⇑σ)) = Θ (Fin.cons z y) := by
    intro z
    have hcomp : (Fin.cons z (y ∘ ⇑σ) : Xn (k + 1))
        = (Fin.cons z y) ∘ ⇑(Equiv.Perm.decomposeFin.symm ((0 : Fin (k + 1)), σ)) := by
      funext j
      refine Fin.cases ?_ ?_ j <;> simp [Equiv.Perm.decomposeFin_symm_apply_zero,
        Equiv.Perm.decomposeFin_symm_apply_succ]
    rw [hcomp]
    exact hΘsym _ _
  -- hence the two integrands are the same function of `z`
  have hfun : (fun z : Sp => (starRingEnd ℂ) (etaOf e w z) * Θ (Fin.cons z (y ∘ ⇑σ)))
      = fun z : Sp => (starRingEnd ℂ) (etaOf e w z) * Θ (Fin.cons z y) := by
    funext z
    rw [hkey z]
  simp only [Work.BoseDict.boxAnnOf, hfun]

end Work.BoseBoxFock
