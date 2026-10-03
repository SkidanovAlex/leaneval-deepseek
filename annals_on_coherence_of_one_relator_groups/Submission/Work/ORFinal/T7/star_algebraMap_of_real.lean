import Mathlib
import Submission.Work.ORVonNeumann.Envelope
import Submission.Work.ORBridgeLinnell.Bridge
import Submission.Work.ORDivLoc.Closure.star_toUK_complex

namespace Work.ORFinal.T7

open Work.ORVonNeumann

-- the `letI` in the statement is a genuine instance, needed to elaborate `algebraMap K E.U`;
-- the style linter's suggestion of `let` does not apply here.
set_option linter.style.haveILetI false

/-- The `K`-algebra structure on `U(G)` induced by a real-valued character `ψ : K →+* ℝ`
(via `ℝ ↪ ℂ`) has *real* scalars: the image of `ψ` in `ℂ` is fixed by complex conjugation,
and the involution of `U(G)` conjugates the complex scalars
(`Work.ORDivLoc.Closure.star_algebraMap_envelope`).  Hence every `K`-scalar in `U(G)` — which is
`algebraMap ℂ E.U ((algebraMap ℝ ℂ) (ψ k))` by definition of
`Work.ORBridgeLinnell.kAlgebra` — is fixed by `star`. -/
theorem star_algebraMap_of_real {G : Type} [Group G]
    (E : Work.ORVonNeumann.StarRegularEnvelope G) {K : Type} [Field K] (ψ : K →+* ℝ) (k : K) :
    letI := Work.ORBridgeLinnell.kAlgebra E ((algebraMap ℝ ℂ).comp ψ)
    star (algebraMap K E.U k) = algebraMap K E.U k := by
  letI := Work.ORBridgeLinnell.kAlgebra E ((algebraMap ℝ ℂ).comp ψ)
  -- `kAlgebra E φK` is `Algebra.compHom E.U φK`, so the `K`-scalar is the `ℂ`-scalar at `φK k`.
  have h1 : algebraMap K E.U k = algebraMap ℂ E.U ((algebraMap ℝ ℂ) (ψ k)) := rfl
  rw [h1, Work.ORDivLoc.Closure.star_algebraMap_envelope E ((algebraMap ℝ ℂ) (ψ k))]
  -- it remains only that the real scalar `(ψ k : ℂ)` is fixed by `star = conj`.
  congr 1
  simp

end Work.ORFinal.T7
