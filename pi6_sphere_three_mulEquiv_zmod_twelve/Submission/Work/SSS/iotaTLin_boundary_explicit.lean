import Mathlib
import Submission.Work.SSS.serreE1Snd
import Submission.Work.SSS.iotaTLin_boundary
import Submission.Work.SSS.Filtration

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SSS

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial Topology

/-- The degree equality `next (s+1+t) = s+t` at the two explicit degrees. -/
lemma iotaTLin_next_eq (s t : ℕ) :
    (ComplexShape.down ℕ).next ((s+1)+t) = s + t := by
  rw [Work.SSS.down_next_eq]
  omega

/-- The two transports `eqToHom (congrArg X h₁)` and `eqToHom (congrArg X h₂)` along two proofs of
the same degree equation agree. -/
lemma eqToHom_congrArg_subsingleton {K : ChainComplex (ModuleCat ℤ) ℕ} {j j' : ℕ}
    (h₁ h₂ : j' = j) :
    eqToHom (congrArg (fun k : ℕ => K.X k) h₁) = eqToHom (congrArg (fun k : ℕ => K.X k) h₂) :=
  congrArg (fun e : j' = j => eqToHom (congrArg (fun k : ℕ => K.X k) e)) (Subsingleton.elim h₁ h₂)

/-- **The boundary formula for `iotaTLin`, with the differential written at the two explicit
degrees.**  `Work.SSS.iotaTLin_boundary` states
`eqToHom (h : next (s+1+t) = s+t) (d (s+1+t) (next (s+1+t)) (iotaTLin)) = ∑ i, (-1)^i • iotaTLinFace i`,
with the differential at the *`next`* degree and a transport `eqToHom` along the degree equation.
This variant eliminates the transport, so that the differential can be evaluated directly at the
reachable index `s+t` (the form needed by `Work.SSS.kF_eq_of_lift`).

It is a two-line corollary of `Work.SSS.iotaTLin_boundary`: `Work.SSS.iotaTLinD_cast`
(in the same module) says precisely that for `h : j' = j` the transport
`eqToHom (congrArg (fun k => K.X k) h)` conjugates `K.d i j'` into `K.d i j`; the equation
`next (s+1+t) = s+t` is available from `Work.SSS.down_next_eq` plus `omega`, and the `eqToHom` in
`iotaTLin_boundary` may be replaced by any other proof of the same (propositional) equation,
e.g. via `congrArg eqToHom (Subsingleton.elim _ _)`. -/
theorem iotaTLin_boundary_explicit {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hfib : Work.StemsB.IsSerreFibration p)
    (s t : ℕ) (b : B)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (s + 1)) : SSet.{0}) ⟶ Work.SSS.sSing B)
    (h : Work.SSS.sigmaVert σ = b) (z : (Work.SSS.fibreCC p b).X t)
    (hz : (ModuleCat.Hom.hom ((Work.SSS.fibreCC p b).d t ((ComplexShape.down ℕ).next t))) z = 0) :
    (ModuleCat.Hom.hom ((Work.SSS.sCC (Work.SSS.pullAlong (Work.SSS.sSingP p) σ)).d (s+1+t) (s+t)))
        (Work.SSS.iotaTLin p hfib s t b σ h z)
      = ∑ i : Fin (s + 2), (-1 : ℤ) ^ (i : ℕ) •
          Work.SSS.iotaTLinFace p hfib s t b σ h i z := by
  have h' : (ComplexShape.down ℕ).next ((s+1)+t) = s + t := iotaTLin_next_eq s t
  rw [← Work.SSS.iotaTLinD_cast
        (K := Work.SSS.sCC (Work.SSS.pullAlong (Work.SSS.sSingP p) σ))
        (i := (s+1)+t) (j := s+t) (j' := (ComplexShape.down ℕ).next ((s+1)+t)) h'
        (Work.SSS.iotaTLin p hfib s t b σ h z)]
  exact Work.SSS.iotaTLin_boundary p hfib s t b σ h z hz

end Work.SSS
