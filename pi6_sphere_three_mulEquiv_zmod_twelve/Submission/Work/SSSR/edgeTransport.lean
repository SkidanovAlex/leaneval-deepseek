import Mathlib
import Submission.Work.Cohomology.SingBridge
import Submission.Work.Stems.PerSimplex.prismChainBoundary
import Submission.Work.SSSR.serreE1Transport
import Submission.Work.SSSR.Serre.simpHomPrism
import Submission.Work.SSSR.RatHurewicz.Bridge.Defs
import Submission.Work.SSSR.Cohomology.HomologyPairSequence
import Submission.Work.SSSR.Stems.hurewiczMapN_surjective
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

set_option autoImplicit false
set_option maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits
open scoped Topology unitInterval Simplicial
namespace Work.SSSR

noncomputable section

/-- The standard `n`-simplex `Δ_n` (as a topological space), named locally. -/
abbrev edgeSimp (n : ℕ) : Type := ↥(stdSimplex ℝ (Fin (n + 1)))

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-- **A coherent family of lifts of the fibre over a path.**  For a map `p : E → B` and a path
`γ : b₀ → b₁`, this is the data of, for every continuous map `τ : Δ_t → p⁻¹(b₀)`, a lift
`G t τ : Δ_t × I → E` of the base homotopy `(z,s) ↦ γ s`, whose bottom is `τ` and whose
restrictions to the faces of `τ` are the lifts of those faces.  This is the coherence of
`REFS/NOTES_LEAD_SSS.md` §1(b). -/
structure LiftFam (p : C(E, B)) {b₀ b₁ : B} (γ : Path b₀ b₁) where
  /-- the lifted homotopies, one for every simplex of the fibre over `b₀` -/
  G : (t : ℕ) → C(edgeSimp t, (Work.SSSR.StemsB.fibre p b₀)) → C(edgeSimp t × I, E)
  /-- the lift lies over the path -/
  hbase : ∀ (t : ℕ) (τ : C(edgeSimp t, (Work.SSSR.StemsB.fibre p b₀))) (z : edgeSimp t) (s : I),
    p (G t τ (z, s)) = γ s
  /-- the bottom of the homotopy is the simplex itself -/
  hbot : ∀ (t : ℕ) (τ : C(edgeSimp t, (Work.SSSR.StemsB.fibre p b₀))) (z : edgeSimp t),
    G t τ (z, 0) = (τ z).1
  /-- the restriction to a face of the simplex is the lift of that face -/
  hside : ∀ (t : ℕ) (τ : C(edgeSimp (t + 1), (Work.SSSR.StemsB.fibre p b₀))) (i : Fin (t + 2)),
    (G (t + 1) τ).comp
        ((Work.SSSR.RatHurewicz.Bridge.coface t i).prodMap (ContinuousMap.id I))
      = G t (τ.comp (Work.SSSR.RatHurewicz.Bridge.coface t i))

/-! ## The inclusions of the two end fibres into the pullback -/

/-- The inclusion of the fibre over the source of the path into the pullback of `p` along `γ`. -/
def inclSource (p : C(E, B)) {b₀ b₁ : B} (γ : Path b₀ b₁) :
    C((Work.SSSR.StemsB.fibre p b₀), Work.SSSR.StemsB.Pullback p γ.toContinuousMap) where
  toFun e := ⟨((e.1 : E), 0), by
    have h : p e.1 = γ 0 := e.2.trans γ.source.symm
    simpa using h⟩
  continuous_toFun := Continuous.subtype_mk (continuous_subtype_val.prodMk continuous_const)
    (fun e => by
      have h : p e.1 = γ 0 := e.2.trans γ.source.symm
      simpa using h)

/-- The inclusion of the fibre over the target of the path into the pullback of `p` along `γ`. -/
def inclTarget (p : C(E, B)) {b₀ b₁ : B} (γ : Path b₀ b₁) :
    C((Work.SSSR.StemsB.fibre p b₁), Work.SSSR.StemsB.Pullback p γ.toContinuousMap) where
  toFun e := ⟨((e.1 : E), 1), by
    have h : p e.1 = γ 1 := e.2.trans γ.target.symm
    simpa using h⟩
  continuous_toFun := Continuous.subtype_mk (continuous_subtype_val.prodMk continuous_const)
    (fun e => by
      have h : p e.1 = γ 1 := e.2.trans γ.target.symm
      simpa using h)

/-- The chain map of the inclusion of the source fibre into the pullback. -/
def sourceChainMap (p : C(E, B)) {b₀ b₁ : B} (γ : Path b₀ b₁) :
    Work.SSSR.Stems.hChain (R := R) (Work.SSSR.StemsB.fibre p b₀) ⟶
      Work.SSSR.Stems.hChain (Work.SSSR.StemsB.Pullback p γ.toContinuousMap) :=
  Work.SSSR.Cohomology.chainMap R _ _ (TopCat.ofHom (inclSource p γ))

/-- The chain map of the inclusion of the target fibre into the pullback. -/
def targetChainMap (p : C(E, B)) {b₀ b₁ : B} (γ : Path b₀ b₁) :
    Work.SSSR.Stems.hChain (R := R) (Work.SSSR.StemsB.fibre p b₁) ⟶
      Work.SSSR.Stems.hChain (Work.SSSR.StemsB.Pullback p γ.toContinuousMap) :=
  Work.SSSR.Cohomology.chainMap R _ _ (TopCat.ofHom (inclTarget p γ))

namespace LiftFam

variable {p : C(E, B)} {b₀ b₁ : B} {γ : Path b₀ b₁}

end LiftFam

end

end Work.SSSR
