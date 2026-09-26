import Mathlib
import Submission.Work.Smooth.JordanSeparation.janiszewskiConnectedInterCompact

/-!
# Janiszewski's theorem in the plane, for two compact sets with preconnected intersection

`Work.Smooth.JordanSeparation.janiszewski_connectedInter_plane`: if `K₁ K₂ ⊆ ℂ` are compact, their
intersection is non-empty and preconnected, and `x y ∉ K₁ ∪ K₂` lie in the same connected component
both of `K₁ᶜ` and of `K₂ᶜ`, then they lie in the same connected component of `(K₁ ∪ K₂)ᶜ`.

This is the plane form of Janiszewski's theorem (Z. Janiszewski, *Sur les continus irréductibles
entre deux points*, J. École Polytech. (2) 16 (1911), 79–170).  It is the topological input used in
Pardon's argument; the work is done in the sibling file
`Submission.Work.Smooth.JordanSeparation.janiszewskiConnectedInterCompact`, which reduces the plane
statement to the Riemann-sphere form `Work.Smooth.SphereJordan.janiszewski_sphere`.
-/

namespace Work.Smooth.JordanSeparation

open Set

theorem janiszewski_connectedInter_plane {K₁ K₂ : Set ℂ} (h₁ : IsCompact K₁) (h₂ : IsCompact K₂)
    (hne : (K₁ ∩ K₂).Nonempty) (hcon : IsPreconnected (K₁ ∩ K₂)) {x y : ℂ}
    (hx : x ∉ K₁ ∪ K₂) (hy : y ∉ K₁ ∪ K₂)
    (hc₁ : y ∈ connectedComponentIn K₁ᶜ x) (hc₂ : y ∈ connectedComponentIn K₂ᶜ x) :
    y ∈ connectedComponentIn (K₁ ∪ K₂)ᶜ x :=
  janiszewskiConnectedInterCompact h₁ h₂ hne hcon hx hy hc₁ hc₂

end Work.Smooth.JordanSeparation
