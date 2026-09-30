import Mathlib
import Submission.Work.Serre.E3aDefs
import Submission.Work.Serre.serreE2d
import Submission.Work.Serre.serreE2b
import Submission.Work.StemsB.RelChainsR
import Submission.Work.Serre.csrAssembly
import Submission.Work.Serre.csrMid
import Submission.Work.Serre.csrUnionStep

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Serre

/-- The cell step of the cellular proof of E3(a): for `Z` obtained from `Y` by attaching
`(n+2)`-cells and a Serre fibration `q : E → Z` with rationally acyclic fibres below `N`, the
relative homology map induced by `q` on the pairs `(E, q⁻¹Y) → (Z, Y)` is an isomorphism in degrees
`≤ N`.

Proof route (excision and compression, no spectral sequence): let `V ⊆ E` be the preimage of
`Z` minus the centres of the attached cells.  The inclusion `q⁻¹Y ↪ V` is a homology isomorphism
(lift the radial deformation of `D^{n+2} ∖ 0` onto `S^{n+1}`, cube by cube, by the cube HLP, and
apply the compression criterion `Work.Serre.serreE2b`, or directly
`Work.RatHurewicz.compressRel_*`); then excision identifies
`H_*(E, q⁻¹Y)` with `H_*(E, V)` and further with the direct sum over the cells
`α` of `H_*(q⁻¹(D_α), q⁻¹(D_α ∖ 0))`, which by `Work.Serre.SerreE2d`/`SerreE2c` (already proved, in
the cube form: `H_{k+m}(τ^*E, τ^*E|_{∂I^m}) ≅ H_k(F)`; the disc `D^{n+2}` is the cube `I^{n+2}`)
is `⊕_α H_{*-(n+2)}(F_α;ℚ)`.  The same argument for the identity fibration on `Z` (fibres a point)
gives `H_*(Z,Y;ℚ) ≅ ⊕_α ℚ[-(n+2)]`.  The map between the two sums is `⊕ (F_α → pt)_*`, an
isomorphism in the range because the fibres are rationally acyclic and rationally connected
(`H_0(F) ≅ ℚ` together with `Work.Serre.serreFibration_fibre_homology_iso` for the transport).

The statement is over ℚ (`Work.StemsB.relChainsR ℚ`, whose short exact sequence and long exact
sequence `relChainsR_exact₁/₂/₃`, `relChainsRδ` are available); over ℤ it is false in general
(the fibres need only be rationally acyclic, e.g. `ℝP²`). -/
theorem cellStepRelHomologyIso (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) {E : Type} [TopologicalSpace E]
    (q : C(E, Work.RatHurewicz.attachCells n Y ι f))
    (hq : Work.StemsB.IsSerreFibration q) (N : ℕ)
    (hacyc : ∀ z : Work.RatHurewicz.attachCells n Y ι f,
      (∀ k : ℕ, 0 < k → k ≤ N → CategoryTheory.Limits.IsZero ((Work.Cohomology.singularChains ℚ
        (TopCat.of (Work.StemsB.fibre q z))).homology k)) ∧
      Nonempty ((Work.Cohomology.singularChains ℚ
        (TopCat.of (Work.StemsB.fibre q z))).homology 0 ≅ ModuleCat.of ℚ ℚ))
    (i : ℕ) (hi : i ≤ N) :
    CategoryTheory.IsIso (HomologicalComplex.homologyMap (Work.Serre.cellStepMap n ι f q) i) :=
  csrAssembly n Y ι f q hq N
    (fun m hm => csrMidIso n Y ι f q hq N
      (fun k hk => csrUnionStep n Y ι f q hq N hacyc k hk) m hm) i hi

end Work.Serre
