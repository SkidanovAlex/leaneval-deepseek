import Mathlib
import Submission.Work.SSSR.serreE1Snd
import Submission.Work.SSSR.iotaTLin_boundary
import Submission.Work.SSSR.Filtration
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

namespace Work.SSSR

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial Topology
/-- The degree equality `next (s+1+t) = s+t` at the two explicit degrees. -/
lemma iotaTLin_next_eq (s t : ℕ) :
    (ComplexShape.down ℕ).next ((s+1)+t) = s + t := by
  rw [Work.SSSR.down_next_eq]
  omega

/-- **The boundary formula for `iotaTLin`, with the differential written at the two explicit
degrees.**  `Work.SSSR.iotaTLin_boundary` states
`eqToHom (h : next (s+1+t) = s+t) (d (s+1+t) (next (s+1+t)) (iotaTLin)) = ∑ i, (-1)^i • iotaTLinFace i`,
with the differential at the *`next`* degree and a transport `eqToHom` along the degree equation.
This variant eliminates the transport, so that the differential can be evaluated directly at the
reachable index `s+t` (the form needed by `Work.SSSR.kF_eq_of_lift`).

It is a two-line corollary of `Work.SSSR.iotaTLin_boundary`: `Work.SSSR.iotaTLinD_cast`
(in the same module) says precisely that for `h : j' = j` the transport
`eqToHom (congrArg (fun k => K.X k) h)` conjugates `K.d i j'` into `K.d i j`; the equation
`next (s+1+t) = s+t` is available from `Work.SSSR.down_next_eq` plus `omega`, and the `eqToHom` in
`iotaTLin_boundary` may be replaced by any other proof of the same (propositional) equation,
e.g. via `congrArg eqToHom (Subsingleton.elim _ _)`. -/
theorem iotaTLin_boundary_explicit {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hfib : Work.SSSR.StemsB.IsSerreFibration p)
    (s t : ℕ) (b : B)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (s + 1)) : SSet.{0}) ⟶ Work.SSSR.sSing B)
    (h : Work.SSSR.sigmaVert σ = b) (z : (Work.SSSR.fibreCC p b).X t)
    (hz : (ModuleCat.Hom.hom ((Work.SSSR.fibreCC p b).d t ((ComplexShape.down ℕ).next t))) z = 0) :
    (ModuleCat.Hom.hom ((Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)).d (s+1+t) (s+t)))
        (Work.SSSR.iotaTLin p hfib s t b σ h z)
      = ∑ i : Fin (s + 2), (-1 : ℤ) ^ (i : ℕ) •
          Work.SSSR.iotaTLinFace p hfib s t b σ h i z := by
  have h' : (ComplexShape.down ℕ).next ((s+1)+t) = s + t := iotaTLin_next_eq s t
  rw [← Work.SSSR.iotaTLinD_cast
        (K := Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ))
        (i := (s+1)+t) (j := s+t) (j' := (ComplexShape.down ℕ).next ((s+1)+t)) h'
        (Work.SSSR.iotaTLin p hfib s t b σ h z)]
  exact Work.SSSR.iotaTLin_boundary p hfib s t b σ h z hz

end Work.SSSR
