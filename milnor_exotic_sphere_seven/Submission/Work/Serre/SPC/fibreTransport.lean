import Mathlib
import Submission.Work.Serre.SPC.Defs
import Submission.Work.Serre.serreFibration_fibre_homology_iso
import Submission.Work.Serre.cubeRelIso
import Submission.Work.Serre.Assembly.fibreConnectivityTransfer

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Serre.SPC

/-- **Transport of the connectivity data of the fibre of a Serre fibration along a path in the
base.**

For a Serre fibration `q : X → Γ`, a path `γ : I → Γ` from `x₀` to `x₁`, and a natural number `φ`,
the fibre connectivity data at `x₀` — vanishing of the reduced homology
`H_j(q⁻¹{x₀}; ℤ)` for `0 < j < φ`, and the augmentation `H₀(q⁻¹{x₀}; ℤ) ⟶ ℤ` being an
isomorphism (i.e. `q⁻¹{x₀}` nonempty and path connected) — transfers to the fibre at `x₁`.

This is the assembly step `Work.Serre.Assembly.fibreConnectivityTransfer` of the pair comparison:
the homology statement is
`Work.Serre.serreFibration_fibre_homology_iso` combined with the isomorphism-invariance of
`IsZero`; the degree-`0` statement is the naturality of the augmentation
(`Work.Cohomology.epsilonNaturality`) applied to the two inclusions of the fibres of the pullback
`I ×_Γ X` of `q` along `γ`, whose relative homology vanishes because the base `I` is contractible
(`Work.Serre.isZero_relChains_fibre_of_contraction`). -/
theorem fibreTransport : Work.Serre.SPC.FibreTransport := by
  intro X Γ _ _ q hq φ x₀ x₁ γ hγ0 hγ1 hfib h0
  exact Work.Serre.Assembly.fibreConnectivityTransfer q hq φ x₀ x₁ γ hγ0 hγ1 hfib h0

end Work.Serre.SPC
