import Mathlib
import Submission.Work.CharCore.Basic
import Submission.Work.CharCore.star_Irr
import Submission.Work.Clifford.CharPair

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.CharCore.irr_orthonormal`

The first orthogonality relation for the irreducible complex characters
`Work.CharCore.Irr G` of a finite group `G`: for `χ, ψ ∈ Irr G` the normalised inner
product `Work.CharCore.cfInner` is `1` if `χ = ψ` and `0` otherwise.

The computation is carried out for the bilinear companion
`Work.Clifford.charPair f g = |G|⁻¹ ∑_x f x * g x⁻¹` of `cfInner` in
`Work.Clifford.CharPair` (`Work.Clifford.charPair_eq_ite_of_mem_Irr`), using that a
χ ∈ Irr G is the character of a simple submodule of the regular module, so that
`Work.Clifford.submoduleRep_isIrreducible` makes Mathlib's `Representation.char_orthonormal`
available.  The two pairings differ only by the fact that the character of a finite
dimensional complex representation takes the complex conjugate at `x⁻¹`, which is
`Work.CharCore.star_Irr`.
-/

noncomputable section

open Classical

namespace Work.CharCore

theorem irr_orthonormal {G : Type*} [Group G] [Fintype G] (χ ψ : G → ℂ) (hχ : χ ∈ Irr G)
    (hψ : ψ ∈ Irr G) : cfInner χ ψ = if χ = ψ then 1 else 0 := by
  have hsum : (∑ x : G, χ x * starRingEnd ℂ (ψ x)) = ∑ x : G, χ x * ψ x⁻¹ :=
    Finset.sum_congr rfl fun x _ => by rw [star_Irr ψ hψ x]
  rw [cfInner, Fintype.card_eq_nat_card, hsum]
  exact Work.Clifford.charPair_eq_ite_of_mem_Irr hχ hψ

end Work.CharCore
