import Mathlib
import Submission.Work.Mostow.geomFiniteDefs

/-!
# Shimizu exponents of the cusps of a lattice

For a discrete subgroup `Γ ≤ PO n 1` (the case of interest: a lattice `Γ` in `ℍⁿ`, `n ≥ 2`) and a
boundary point `ξ`, the *Shimizu exponent* of the cusp at `ξ` is the infimum of the Shimizu
distortions

`(1 - ⟪ξ, bd γ ξ⟫) · exp (-(bCocy γ ξ))`   (γ ∈ Γ with `bd γ ξ ≠ ξ`),

where `bd γ ξ` is the boundary image, `1 - ⟪ξ,η⟫ = ‖ξ-η‖²/2` is (half) the square of the chordal
distance and `bCocy γ ξ` is the Busemann cocycle. The content of Shimizu's lemma for lattices is
that this infimum is *positive* (`Work.Mostow.cuspShimizu_pos`), which is exactly the statement
that the horoballs at `ξ` and at `bd γ ξ` are disjoint at the level `(1/2) log (cuspShimizu Γ ξ)`.

Two further facts about this quantity, proved in this development, are

* `cuspShimizu`.
* its equivariance `cuspShimizu (bd γ ξ) = exp (2 * bCocy γ ξ) * cuspShimizu ξ`, which makes the
  level function `ξ ↦ (1/2) log (cuspShimizu Γ ξ)` a `Γ`-equivariant height on `parFixed Γ`
  (`Work.Mostow.IsEquivHeight`), and
* the separation statement `Work.Mostow.cuspShimizu_separation`: for two distinct cusp classes the
  quantity `(1 - ⟪ξ,η⟫) / sqrt (cuspShimizu ξ * cuspShimizu η)` is bounded away from `0` uniformly.

Together these give an equivariant height on `parFixed Γ` whose horoballs are pairwise disjoint.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity Classical

noncomputable section

variable {n : ℕ}

/-- The set of Shimizu distortions of the elements of `Γ` at `ξ`: those `γ` which do not fix `ξ`
and the value `(1 - ⟪ξ, bd γ ξ⟫) exp (-(bCocy γ ξ))`. -/
def cuspShimizuSet (Γ : Subgroup (PO n 1)) (ξ : E n) : Set ℝ :=
  {r : ℝ | ∃ ν : Γ, bd (ν : PO n 1) ξ ≠ ξ ∧
    r = (1 - inner ℝ ξ (bd (ν : PO n 1) ξ)) * Real.exp (-(bCocy (ν : PO n 1) ξ))}

/-- The Shimizu exponent of the cusp at `ξ`: the infimum of the Shimizu distortions over the
elements of `Γ` not fixing `ξ` (junk value `1` when every element of `Γ` fixes `ξ`). -/
def cuspShimizu (Γ : Subgroup (PO n 1)) (ξ : E n) : ℝ :=
  if _ : ∃ ν : Γ, bd (ν : PO n 1) ξ ≠ ξ then sInf (cuspShimizuSet Γ ξ) else 1

lemma cuspShimizu_eq_sInf (Γ : Subgroup (PO n 1)) (ξ : E n)
    (h : ∃ ν : Γ, bd (ν : PO n 1) ξ ≠ ξ) : cuspShimizu Γ ξ = sInf (cuspShimizuSet Γ ξ) :=
  dif_pos h

lemma cuspShimizu_eq_one (Γ : Subgroup (PO n 1)) (ξ : E n)
    (h : ¬ ∃ ν : Γ, bd (ν : PO n 1) ξ ≠ ξ) : cuspShimizu Γ ξ = 1 :=
  dif_neg h

lemma mem_cuspShimizuSet (Γ : Subgroup (PO n 1)) (ξ : E n) (ν : Γ)
    (hν : bd (ν : PO n 1) ξ ≠ ξ) :
    (1 - inner ℝ ξ (bd (ν : PO n 1) ξ)) * Real.exp (-(bCocy (ν : PO n 1) ξ))
      ∈ cuspShimizuSet Γ ξ :=
  ⟨ν, hν, rfl⟩

end

end Work.Mostow
