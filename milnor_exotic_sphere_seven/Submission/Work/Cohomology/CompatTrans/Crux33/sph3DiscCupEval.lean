import Mathlib
import Submission.Work.Cohomology.CompatTrans.Crux33.sphCupEvalAux

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Cohomology.Crux33

/-- **The Künneth/external-product evaluation for `A = S³ × S³` (`PairAT`).**

There are `3`-cocycles `β` on the first sphere `Sph3T` and `β'` on the second sphere
`TopCat.of (sphereInUnit 4)`, and a `6`-cycle `Δ` of `A = PairAT = S³ × S³`, such that the
Alexander–Whitney cup product of the pullbacks of `β` (along the first projection `pj1A`) and of
`β'` (along the second projection `pj2A`) evaluates non-trivially on `Δ`.

Equivalently: the external product `H³(S³) ⊗ H³(S³) → H⁶(S³ × S³) ≅ ℤ` is non-zero (this is the
`(3,3)` Künneth statement for the product of two `3`-spheres, the crux of the Milnor exotic sphere
project).  It implies `Work.Cohomology.prodSph33_cup_ne_zero_compat` and
`Work.Cohomology.Crux33.prodSph33_cap_ne_zero`.

Suggested route (classical Eilenberg–Zilber shuffle, chain level):
take `σ` a `3`-simplex of `Sph3T` constant on `∂Δ³` (e.g. the collapse `Δ³ → Δ³/∂Δ³ ≅ S³`
composed with a degree-`1` self-map of `S³`) and `τ` a `3`-simplex of `sphereInUnit 4` constant on
`∂Δ³`.  Such a simplex is automatically a cycle: `∂σ = Σ_{i=0}^{3}(-1)^i (constant simplex) = 0`.
Let `Δ := Σ_{cells z of the prism} ±_z (σ ∘ z₁, τ ∘ z₂)`, the image of the triangulation of the
prism `Δ³ × Δ³` (the maximal simplices of `Δ[3] ⊗ Δ[3]`, i.e. the lattice paths with `3` E- and
`3` N-steps, with the shuffle signs).  Then

* `Δ` is a cycle, since `(σ × τ)_*` is a chain map and `∂σ = ∂τ = 0`;
* the only cell whose front `3`-face is `σ` **and** whose back `3`-face is `τ` is the cell `EEENNN`
  (for every other cell at least one of the two faces is constant, and a cocycle in *odd* degree
  vanishes on constant simplices: `dα = 0` applied to the constant `(n+1)`-simplex, whose boundary
  is the constant `n`-simplex with coefficient `±1`, gives `α(constant n-simplex) = 0` for `n` odd),
  so the evaluation is `± β(σ)β'(τ)`;
* choose `β`, `β'` with `β(σ) = 1`, `β'(τ) = 1` using the non-degeneracy of the Kronecker pairing
  (`Work.Cohomology.kronH_isIso` together with `Work.Cohomology.sphereHomologyTop`: `H₃(S³) ≅ ℤ`
  is free, so `H³(S³) → Hom(H₃(S³),ℤ)` is onto and `∃ cycle c, cocycle β` with `β(c) = 1`).

The interior faces of the prism triangulation cancel; that cancellation (equivalently: `∂` of the
prism chain is the "product of the boundaries", the chain-map property of the Eilenberg–Zilber
shuffle map) is the only genuine combinatorial content. -/
theorem sph3DiscCupEval :
    ∃ (β : Work.Cohomology.Cochain ℤ (TopCat.toSSet.obj Work.Cohomology.Sph3T) 3)
      (β' : Work.Cohomology.Cochain ℤ
        (TopCat.toSSet.obj (TopCat.of (Work.Cohomology.sphereInUnit 4))) 3)
      (Δ : (Work.Cohomology.singularChains ℤ (TopCat.of Work.Cohomology.PairAT)).X 6),
      Work.Cohomology.cochainDiff ℤ (TopCat.toSSet.obj Work.Cohomology.Sph3T) β = 0
      ∧ Work.Cohomology.cochainDiff ℤ
          (TopCat.toSSet.obj (TopCat.of (Work.Cohomology.sphereInUnit 4))) β' = 0
      ∧ (Work.Cohomology.singularChains ℤ (TopCat.of Work.Cohomology.PairAT)).d 6 5 Δ = 0
      ∧ Work.Cohomology.kronecker ℤ (TopCat.toSSet.obj (TopCat.of Work.Cohomology.PairAT))
          (Work.Cohomology.cup ℤ (TopCat.toSSet.obj (TopCat.of Work.Cohomology.PairAT))
            ((Work.Cohomology.cochainPullbackHom ℤ (TopCat.of Work.Cohomology.PairAT)
              Work.Cohomology.Sph3T Work.Cohomology.pj1A 3).hom β)
            ((Work.Cohomology.cochainPullbackHom ℤ (TopCat.of Work.Cohomology.PairAT)
              (TopCat.of (Work.Cohomology.sphereInUnit 4)) Work.Cohomology.pj2A 3).hom β'))
          Δ ≠ 0 := scTargetWitness

end Work.Cohomology.Crux33
