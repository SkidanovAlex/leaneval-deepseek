import Mathlib
import Submission.Work.Induction.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Induction

/-- **Every finite-dimensional complex representation comes from an `FDRep`.**

For a group `G` (in any universe) and a finite-dimensional `ℂ`-module `M` (in any universe),
carrying a representation `ρ : Representation ℂ G M`, there is a bundled finite-dimensional
complex representation `W : FDRep ℂ G` whose character is that of `ρ`.

The point is that `FDRep ℂ G` is the category of finitely generated `ℂ`-modules in the
universe of `ℂ` (universe `0`), while `M` may live in a larger universe; we transport `ρ`
across a linear isomorphism `M ≃ₗ[ℂ] (Fin (finrank ℂ M) → ℂ)` onto a standard Type-`0` model.
Characters are unchanged by this transport because the trace is invariant under conjugation
(`LinearMap.trace_conj'`). -/
theorem exists_fdRep_of_representation {G : Type*} [Group G] {M : Type*} [AddCommGroup M]
    [Module ℂ M] [Module.Finite ℂ M] (ρ : Representation ℂ G M) :
    ∃ W : FDRep ℂ G, W.character = ρ.character := by
  classical
  -- A concrete Type-`0` model of `M`: `Fin (finrank ℂ M) → ℂ`.
  let n := Module.finrank ℂ M
  let b := Module.finBasis ℂ M
  let e : M ≃ₗ[ℂ] (Fin n → ℂ) := b.equivFun
  -- Transport `ρ` to this model by conjugation with `e`.
  let ρ' : Representation ℂ G (Fin n → ℂ) := e.conjRingEquiv.toMonoidHom.comp ρ
  refine ⟨FDRep.of ρ', ?_⟩
  ext g
  show LinearMap.trace ℂ (FDRep.of ρ') ((FDRep.of ρ').ρ g) = LinearMap.trace ℂ M (ρ g)
  rw [FDRep.of_ρ']
  rw [show (e.conjRingEquiv.toMonoidHom.comp ρ) g = e.conj (ρ g) from rfl]
  exact LinearMap.trace_conj' (ρ g) e

end Work.Induction
