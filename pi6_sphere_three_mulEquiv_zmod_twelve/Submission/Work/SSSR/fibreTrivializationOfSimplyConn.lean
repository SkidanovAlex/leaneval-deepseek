import Mathlib
import Submission.Work.SSSR.fibreTransportTrivialization
import Submission.Work.SSSR.pathsHomotopicOfSimplyConn
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

set_option autoImplicit false

open scoped Topology unitInterval
open CategoryTheory CategoryTheory.Limits
namespace Work.SSSR

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
        ((Work.SSSR.PiS.HZ R (Work.SSSR.StemsB.fibre p b) j) ≅ (Work.SSSR.PiS.HZ R (Work.SSSR.StemsB.fibre p b') j)))
    (htrans : ∀ {b b' b'' : B} (γ : Path b b') (δ : Path b' b''), T (γ.trans δ) = T γ ≪≫ T δ)
    (hhom : ∀ {b b' : B} (γ γ' : Path b b'), Path.Homotopic γ γ' → T γ = T γ')
    (hc : Work.SSSR.PiS.SimplyConn B b₀) :
    ∃ θ : ∀ b : B,
        ((Work.SSSR.PiS.HZ R (Work.SSSR.StemsB.fibre p b) j) ≅ (Work.SSSR.PiS.HZ R (Work.SSSR.StemsB.fibre p b₀) j)),
      ∀ {b b' : B} (γ : Path b b'), T γ ≪≫ θ b' = θ b := by
  haveI : PathConnectedSpace B := pathConnectedSpace_of_subsingleton_pi0 b₀ hc.1
  exact fibreTransportTrivialization p j b₀ T htrans hhom
    (fun b => PathConnectedSpace.joined b b₀)
    (fun γ γ' => pathsHomotopicOfSimplyConn b₀ hc γ γ')

end

end Work.SSSR
