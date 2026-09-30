import Mathlib
import Submission.Work.BW.subIdealDefs
import Submission.Work.BW.charEval_sum
import Submission.Work.BW.mono_char_linearIndependent

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Separation by the evaluation maps `EV a x`

`RingA m = (Laur m)[u] = (ℂ[ℤ^m])[u]` is the ring in which the restrictions of the
multihomogeneous polynomials to the closure `G'` live (see `Submission.Work.BW.subIdealDefs`):
`Laur m = ℂ[ℤ^m]` are the Laurent polynomials in the torus coordinates and `u` is the `G_a`
coordinate.  The evaluation maps
`EV a x : RingA m →+* ℂ`, `p ↦ p(u := a)(t_j := x_j)`,
for a point `a : ℂ` of the affine line and a torus point `x : Fin m → ℂˣ`, jointly separate
elements of `RingA m`: this is the lemma `EV_sep` below.

The proof has two halves.

* **Halving off the `u`-degree.**  Fix the torus point `x`.  The function
  `a ↦ EV a x b` is the value at `a` of the polynomial `b.map (charEval x) : ℂ[X]`, whose
  `n`-th coefficient is `charEval x (b.coeff n)`.  Since it vanishes at every `a : ℂ` and `ℂ` is
  infinite, `b.map (charEval x) = 0` (Mathlib: `Polynomial.funext`), hence
  `charEval x (b.coeff n) = 0` for every `n`.

* **Separating Laurent polynomials.**  The characters `ψ_w : x ↦ ∏_j (x_j)^{w_j}`
  (`w : Fin m → ℤ`) of the torus `(ℂˣ)^m` are distinct monoid homomorphisms into `ℂ`, hence
  linearly independent by Dedekind's theorem (Mathlib: `linearIndependent_monoidHom`); see
  `mono_char_linearIndependent`.  Together with the evaluation formula for `charEval`
  (`charEval_sum`) this shows `b.coeff n = 0` for all `n`, so `b = 0`.
-/

namespace Work.BW

/-- The evaluation maps `EV a x` (`a : ℂ`, `x : Fin m → ℂˣ`) separate the points of
`RingA m = (Laur m)[u]`: the only element killed by all of them is `0`. -/
lemma EV_sep {m : ℕ} (b : RingA m) (h : ∀ (a : ℂ) (x : Fin m → ℂˣ), EV a x b = 0) : b = 0 := by
  apply Polynomial.ext
  intro n
  -- For every torus point `x`, the `n`-th coefficient of `b` is killed by `charEval x`.
  have hq : ∀ x : Fin m → ℂˣ, charEval x (b.coeff n) = 0 := by
    intro x
    have key : Polynomial.map (charEval x : Laur m →+* ℂ) b = 0 := by
      apply Polynomial.funext
      intro a
      rw [Polynomial.eval_zero]
      have hr : ((charEval x : Laur m →+* ℂ)) (algebraMap ℂ (Laur m) a) = a := by
        rw [show ((charEval x : Laur m →+* ℂ)) (algebraMap ℂ (Laur m) a)
            = (charEval x) (algebraMap ℂ (Laur m) a) from rfl]
        rw [AlgHom.commutes]; simp
      have hstep : Polynomial.eval a (Polynomial.map (charEval x : Laur m →+* ℂ) b)
          = EV a x b := by
        rw [Polynomial.eval_map]
        conv_lhs => rw [← hr]
        rw [Polynomial.eval₂_at_apply]
        simp only [Work.BW.EV, RingHom.comp_apply, Polynomial.coe_evalRingHom]
      rw [hstep, h a x]
    have hcc := congrArg (fun p : Polynomial ℂ => p.coeff n) key
    simp only [Polynomial.coeff_map, Polynomial.coeff_zero] at hcc
    exact hcc
  -- Linear independence of the torus characters upgrades this to `b.coeff n = 0`.
  have hLI := mono_char_linearIndependent (s := (b.coeff n).coeff.support)
    (c := fun w => (b.coeff n).coeff w)
    (fun x => by rw [← charEval_sum x (b.coeff n)]; exact hq x)
  apply AddMonoidAlgebra.ext
  show (b.coeff n).coeff = (0 : Laur m).coeff
  rw [AddMonoidAlgebra.coeff_zero]
  refine Finsupp.ext (fun w => ?_)
  by_cases hw : w ∈ (b.coeff n).coeff.support
  · simpa using hLI w hw
  · simpa using Finsupp.notMem_support_iff.mp hw

end Work.BW
