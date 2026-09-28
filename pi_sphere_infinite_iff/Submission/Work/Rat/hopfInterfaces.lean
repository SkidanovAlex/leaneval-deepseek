import Mathlib
import Submission.Work.Serre.Models
import Submission.Work.StemsB.SphLoopModel
import Submission.Work.RatHurewicz.RelHomotopy
import Submission.Work.StemsB.Fibrations
import Submission.Work.StemsB.HurewiczFibration

/-!
# Interfaces for the even-sphere analysis (area RATIONAL)

This module fixes the two objects the even-`n` analysis of `π_{2n-1}(Sⁿ)` works with:

* `Work.Rat.coverProj` — the projection of the homotopy fibre of a map `f : Sⁿ → X`, transported
  to the sphere model `SphModel n` along a homeomorphism `SphModel n ≃ₜ Sⁿ` (the Wang sequence of
  `Submission/Work/StemsB/WangSphereHomology` is stated for fibrations over `SphModel n`);
* `Work.Rat.coverFibreData` — the rational homology of the fibre of that projection over `∞`: it is
  the rational homology of `ΩX`, i.e. (for `n` even and `X` a range model of `K(ℤ,n)`) that of
  `S^{n-1}` in the range below `2n`.

Nothing here is specific to the target theorem; the statements are the interface of the two
lemmas of the even-`n` analysis.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology

namespace Work.Rat

noncomputable section

/-- **The projection of the homotopy fibre, transported to the sphere model.**

For a homeomorphism `e : SphModel n ≃ₜ Sⁿ` and a map `f : Sⁿ → X` with base point `s₀`, this is
the map `(e.symm) ∘ (homotopyFibreFst f s₀) : hofib(f) → SphModel n`.  Its fibre over `∞` is the
fibre of the homotopy-fibre projection over `e ∞`, a space homotopy equivalent to `Ω_{f s₀}X`. -/
def coverProj {n : ℕ} {X : Type} [TopologicalSpace X]
    (e : Work.StemsB.SphModel n ≃ₜ Work.Serre.Sph n)
    (f : C(Work.Serre.Sph n, X)) (s₀ : Work.Serre.Sph n) :
    C(Work.RatHurewicz.homotopyFibre f s₀, Work.StemsB.SphModel n) :=
  (⟨e.symm, e.symm.continuous⟩ : C(Work.Serre.Sph n, Work.StemsB.SphModel n)).comp
    (Work.RatHurewicz.homotopyFibreFst f s₀)

/-- The fibre of `coverProj` over `∞`, as a type. -/
abbrev coverFibre {n : ℕ} {X : Type} [TopologicalSpace X]
    (e : Work.StemsB.SphModel n ≃ₜ Work.Serre.Sph n)
    (f : C(Work.Serre.Sph n, X)) (s₀ : Work.Serre.Sph n) : Type :=
  ↥((coverProj e f s₀) ⁻¹' ({OnePoint.infty} : Set (Work.StemsB.SphModel n)))

end

end Work.Rat
