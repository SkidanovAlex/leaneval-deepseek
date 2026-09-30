import Mathlib
import Submission.Work.SSSR.PiS.Interfaces
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

namespace Work.SSSR

open scoped Topology unitInterval
open CategoryTheory CategoryTheory.Limits
/-- **Trivialisation of the local system of fibre homologies.**  Let `T` be a transport assignment
on the fibre homologies of a map `p : E → B` (an isomorphism `H_j(p⁻¹b) ≅ H_j(p⁻¹b')` for each path
`γ : Path b b'` in the base), assumed compatible with concatenation of paths and constant on paths
with the same endpoints that are homotopic rel endpoints.  If `B` is path connected and any two
paths with the same endpoints are homotopic (the case for a path connected, simply connected base:
`Work.SSSR.pathsHomotopicOfSimplyConn` together with the triviality of `π₀`), then the local system
`b ↦ H_j(p⁻¹ b)` is trivial: there is a family of isomorphisms `θ b : H_j(p⁻¹b) ≅ H_j(p⁻¹b₀)`
compatible with the transports, `T γ ≪≫ θ b' = θ b` for every path `γ` from `b` to `b'`.  This is
the input that identifies the coefficients of the E¹ page of the Serre spectral sequence with the
fixed module `H_j(p⁻¹(p e₀))`. -/
theorem fibreTransportTrivialization {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (j : ℕ) (b₀ : B)
    (T : ∀ {b b' : B}, Path b b' →
        ((Work.SSSR.PiS.HZ R (Work.SSSR.StemsB.fibre p b) j) ≅ (Work.SSSR.PiS.HZ R (Work.SSSR.StemsB.fibre p b') j)))
    (htrans : ∀ {b b' b'' : B} (γ : Path b b') (δ : Path b' b''), T (γ.trans δ) = T γ ≪≫ T δ)
    (hhom : ∀ {b b' : B} (γ γ' : Path b b'), Path.Homotopic γ γ' → T γ = T γ')
    (hpc : ∀ b : B, Nonempty (Path b b₀))
    (hpath : ∀ {b b' : B} (γ γ' : Path b b'), Path.Homotopic γ γ') :
    ∃ θ : ∀ b : B,
        ((Work.SSSR.PiS.HZ R (Work.SSSR.StemsB.fibre p b) j) ≅ (Work.SSSR.PiS.HZ R (Work.SSSR.StemsB.fibre p b₀) j)),
      ∀ {b b' : B} (γ : Path b b'), T γ ≪≫ θ b' = θ b := by
  classical
  -- Pick, for every `b`, an auxiliary path `σ b : Path b b₀` (using path connectedness),
  -- and set `θ b := T (σ b)`: the transport along `σ b` back to the base point.
  refine ⟨fun b => T (Classical.choice (hpc b)), ?_⟩
  intro b b' γ
  -- `T` is a functor on the path groupoid: transport along the concatenation `γ * σ b'`
  -- equals `T γ ≫ T (σ b')`.
  have h1 := htrans γ (Classical.choice (hpc b'))
  -- The two paths `γ * σ b'` and `σ b` have the same endpoints `b b₀`, hence are homotopic,
  -- so `T` takes the same value on them.
  have h2 := hhom (γ.trans (Classical.choice (hpc b'))) (Classical.choice (hpc b)) (hpath _ _)
  exact h1.symm.trans h2

end Work.SSSR
