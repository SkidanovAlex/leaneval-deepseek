import Mathlib
import Submission.Work.Smooth.SphereJordan.Defs
import Submission.Work.Smooth.SphereJordan.janiszewskiChain.SphereJaniszewskiOfSimplyConnected
import Submission.Work.Smooth.SphereJordan.janiszewskiChain.IsPreconnectedComplComponentInSphere
import Submission.Work.Smooth.SphereJordan.isSimplyConnected_of_isPreconnected_compl
/-! # Copy of `Submission/Work/Smooth/SphereJordan/janiszewski_sphere.lean` under the namespace `Work.Smooth.SphereJordan.Chain`

Duplicate of the team module `Submission/Work/Smooth/SphereJordan/janiszewski_sphere.lean`, with the import of
`Submission.Work.Smooth.SphereJordan.janiszewskiConnectedInter` replaced by the
namespace-local `...janiszewskiChain.DisjointPlane`, so that the chain can be imported
by `janiszewskiConnectedInter.lean` itself without an import cycle. -/


namespace Work.Smooth.SphereJordan.Chain

/-- **Janiszewski's theorem on the Riemann sphere** (Pardon's classical Jordan-separation input).

If `A₁ A₂ ⊆ ℂ ∪ {∞}` are closed with `A₁ ∩ A₂` non-empty and preconnected, and `a, b ∉ A₁ ∪ A₂`
lie in the same connected component both of `A₁ᶜ` and of `A₂ᶜ`, then they lie in the same connected
component of `(A₁ ∪ A₂)ᶜ`. -/
theorem janiszewski_sphere {A₁ A₂ : Set (OnePoint ℂ)} (h₁ : IsClosed A₁) (h₂ : IsClosed A₂)
    (hne : (A₁ ∩ A₂).Nonempty) (hcon : IsPreconnected (A₁ ∩ A₂)) {a b : OnePoint ℂ} (hab : a ≠ b)
    (ha : a ∉ A₁ ∪ A₂) (hb : b ∉ A₁ ∪ A₂)
    (h₁' : b ∈ connectedComponentIn A₁ᶜ a) (h₂' : b ∈ connectedComponentIn A₂ᶜ a) :
    b ∈ connectedComponentIn (A₁ ∪ A₂)ᶜ a := by
  exact Work.Smooth.SphereJordan.Chain.janiszewski_of_simplyConnected
    (fun D hDo hDne hDp hDc => Work.Smooth.SphereJordan.isSimplyConnected_of_isPreconnected_compl hDo hDne hDp hDc)
    (fun {K} hK hKne hKp {x} hx =>
      Work.Smooth.SphereJordan.Chain.isPreconnected_compl_componentIn_sphere hK hKne hKp hx)
    Work.Smooth.JordanSeparation.onePoint_locallyPathConnected
    h₁ h₂ hne hcon ha hb h₁' h₂'

end Work.Smooth.SphereJordan.Chain
