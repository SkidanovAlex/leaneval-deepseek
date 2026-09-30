import Mathlib
import Submission.Work.SSS.fibreTransportTrivialization
import Submission.Work.SSS.pathsHomotopicOfSimplyConn

/-!
# Trivialising the local system of fibre homologies over a simply connected base

`Work.SSS.fibreTransportTrivialization` produces a trivialisation `θ b : H_j(p⁻¹b) ≅ H_j(p⁻¹b₀)`
of the local system `b ↦ H_j(p⁻¹ b)` from a *coherent* transport assignment on paths (compatible
with concatenation and with homotopies of paths rel endpoints).  `Work.SSS.pathsHomotopicOfSimplyConn`
supplies the last ingredient: over a path connected, simply connected base, any two paths with the
same endpoints are homotopic.

The present file is the resulting interface, in the form in which the identification of the
coefficients of the E¹ page of the Serre spectral sequence with the fixed module `H_j(p⁻¹(p e₀))`
consumes it: given `hc : Work.PiS.SimplyConn B b₀` and a coherent transport `T`, one gets `θ`.

For the E¹ page of the Serre filtration of a Serre fibration `p` over a simply connected base, the
remaining obligation is therefore only to show that the *specific* edge maps coming from the
σ-piece decomposition of the graded pieces of the filtration (the `i = 0` component of `d¹`) form
such a coherent transport: that is a statement about the explicit chain-level construction (the
coherent lift families `Φ_τ`), not about the present file.
-/

set_option autoImplicit false

open scoped Topology unitInterval
open CategoryTheory CategoryTheory.Limits

namespace Work.SSS

noncomputable section

/-- If `π₀ B` is trivial at some point then `B` is path connected. -/
theorem pathConnectedSpace_of_subsingleton_pi0 {B : Type} [TopologicalSpace B] (b₀ : B)
    (hb : Subsingleton (HomotopyGroup.Pi 0 B b₀)) : PathConnectedSpace B := by
  have hZ : Subsingleton (ZerothHomotopy B) :=
    ⟨fun a b => (HomotopyGroup.pi0EquivZerothHomotopy (X := B) (x := b₀)).symm.injective
      (Subsingleton.elim _ _)⟩
  exact pathConnectedSpace_iff_zerothHomotopy.mpr ⟨⟨ZerothHomotopy.mk b₀⟩, hZ⟩

/-- **Trivialisation of the local system of fibre homologies over a simply connected base.**
Let `T` be a transport assignment on the fibre homologies of a map `p : E → B` (an isomorphism
`H_j(p⁻¹b) ≅ H_j(p⁻¹b')` for each path `γ : Path b b'`), compatible with concatenation and constant
on homotopic paths rel endpoints.  If `B` is path connected and simply connected at `b₀`
(`Work.PiS.SimplyConn B b₀`), then there is a family of isomorphisms `θ b : H_j(p⁻¹b) ≅ H_j(p⁻¹b₀)`
with `T γ ≪≫ θ b' = θ b` for every path `γ` from `b` to `b'`.  This trivialises the coefficient
system `b ↦ H_j(p⁻¹b)` appearing in the E¹ page of the Serre spectral sequence. -/
theorem fibreTrivializationOfSimplyConn {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (b₀ : B) (j : ℕ)
    (T : ∀ {b b' : B}, Path b b' →
        ((Work.PiS.HZ (Work.StemsB.fibre p b) j) ≅ (Work.PiS.HZ (Work.StemsB.fibre p b') j)))
    (htrans : ∀ {b b' b'' : B} (γ : Path b b') (δ : Path b' b''), T (γ.trans δ) = T γ ≪≫ T δ)
    (hhom : ∀ {b b' : B} (γ γ' : Path b b'), Path.Homotopic γ γ' → T γ = T γ')
    (hc : Work.PiS.SimplyConn B b₀) :
    ∃ θ : ∀ b : B,
        ((Work.PiS.HZ (Work.StemsB.fibre p b) j) ≅ (Work.PiS.HZ (Work.StemsB.fibre p b₀) j)),
      ∀ {b b' : B} (γ : Path b b'), T γ ≪≫ θ b' = θ b := by
  haveI : PathConnectedSpace B := pathConnectedSpace_of_subsingleton_pi0 b₀ hc.1
  exact fibreTransportTrivialization p j b₀ T htrans hhom
    (fun b => PathConnectedSpace.joined b b₀)
    (fun γ γ' => pathsHomotopicOfSimplyConn b₀ hc γ γ')

end

end Work.SSS
