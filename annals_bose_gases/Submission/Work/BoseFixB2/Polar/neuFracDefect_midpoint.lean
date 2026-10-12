import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Submission.Work.BoseFixB2.Polar.neuFracSmulAddDef
import Submission.Work.BoseFixB2.Polar.neuFrac_parallelogram
import Submission.Work.BoseKinLoc.NeuFrac.neuFrac_const_mul
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB2.Polar.neuFracDefect_midpoint`

**The midpoint (second-difference) identity for the `t`-parametrised `neuFrac` defect.**

With `Q = Work.BoseKinLoc.neuFrac ℓ a² u`, `Φ_t = t·f + g` (`smulAdd`) and

`R t = neuFracDefect ℓ a² u f g t = Q(Φ_t) − t²·Q(f) − Q(g)`,

the claim is `R (s+t) + R (s−t) = 2·R s`.  Expanding,

`R (s+t) + R (s−t) = [Q(Φ_{s+t}) + Q(Φ_{s−t})] − ((s+t)² + (s−t)²)·Q(f) − 2·Q(g)`,

and the bracket is exactly the parallelogram law `neuFrac_parallelogram` applied to the pair

* `A = Φ_s = s·f + g`, `B = t·f` (the states whose sum/difference are `Φ_{s+t}` and `Φ_{s−t}`):

`Q(Φ_{s+t}) + Q(Φ_{s−t}) = 2·Q(Φ_s) + 2·Q(B)`.

`Q(B) = Q(t·f) = t²·Q(f)` by the `2`-homogeneity `neuFrac_const_mul`, so

`R (s+t) + R (s−t) = 2·Q(Φ_s) + 2t²·Q(f) − (2s² + 2t²)·Q(f) − 2·Q(g)
                 = 2·(Q(Φ_s) − s²·Q(f) − Q(g)) = 2·R s`.

Both states `A` and `B` are again smooth when `f, g` are, so the parallelogram law applies.
Note that the identity does **not** use additivity of `R` itself (`R t` need not vanish):
the `t`-dependence inside the bracket cancels against the `t²` in the homogeneity term.
-/

namespace Work.BoseFixB2.Polar

theorem neuFracDefect_midpoint {ℓ a2 : ℝ} (hℓ : 0 < ℓ) (ha2 : 0 < a2) (u : EuclideanSpace ℝ (Fin 3)) {f g : EuclideanSpace ℝ (Fin 3) → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (s t : ℝ) : neuFracDefect ℓ a2 u f g (s + t) + neuFracDefect ℓ a2 u f g (s - t) = 2 * neuFracDefect ℓ a2 u f g s := by
  have ha2le : (0 : ℝ) ≤ a2 := le_of_lt ha2
  -- smoothness of the two states to which the parallelogram law is applied
  have hA : ContDiff ℝ (⊤ : ℕ∞) (smulAdd s f g) := by
    change ContDiff ℝ (⊤ : ℕ∞) (fun z : EuclideanSpace ℝ (Fin 3) => s * f z + g z)
    exact (contDiff_const.mul hf).add hg
  have hB : ContDiff ℝ (⊤ : ℕ∞) (fun z : EuclideanSpace ℝ (Fin 3) => t * f z) := by
    simpa using contDiff_const.mul hf
  -- the parallelogram law for the pair `(s·f + g, t·f)`
  have hpar := neuFrac_parallelogram hℓ ha2 u hA hB
  -- `2`-homogeneity of `neuFrac` in the defect state
  have hhom : Work.BoseKinLoc.neuFrac ℓ a2 u (fun z : EuclideanSpace ℝ (Fin 3) => t * f z)
      = t ^ 2 * Work.BoseKinLoc.neuFrac ℓ a2 u f :=
    Work.BoseKinLoc.NeuFrac.neuFrac_const_mul ha2le u f
  -- `(s·f + g) ± t·f = (s ± t)·f + g`
  have h1 : (fun z : EuclideanSpace ℝ (Fin 3) => smulAdd s f g z + t * f z)
      = smulAdd (s + t) f g := by
    funext z
    simp only [smulAdd]
    ring
  have h2 : (fun z : EuclideanSpace ℝ (Fin 3) => smulAdd s f g z - t * f z)
      = smulAdd (s - t) f g := by
    funext z
    simp only [smulAdd]
    ring
  rw [h1, h2, hhom] at hpar
  simp only [neuFracDefect] at *
  linarith

end Work.BoseFixB2.Polar
