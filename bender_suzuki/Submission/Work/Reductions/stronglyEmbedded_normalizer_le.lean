import Mathlib
import Submission.Work.Reductions.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Reductions

/-- If `H` is strongly embedded in `G`, then any subgroup `X ≤ H` of even order has its
`G`-normalizer contained in `H`.  Indeed, if `g ∈ N_G(X)` lay outside `H`, then
`X ≤ H ⊓ H^g` would force the order of `H ⊓ H^g` to be even (it is a multiple of the even
number `Nat.card X`), contradicting strong embeddedness, which says `H ⊓ H^g` has odd order
for every `g ∉ H`. -/
theorem stronglyEmbedded_normalizer_le {G : Type} [Group G] {H X : Subgroup G}
    (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H) (hX : X ≤ H) (heven : Even (Nat.card X)) :
    Subgroup.normalizer X ≤ H := by
  intro g hg
  by_contra hgH
  obtain ⟨_, _, hodd⟩ := hH
  have hoddg := hodd g hgH
  -- `g ∈ N_G(X)` makes `X` invariant under conjugation by `g`, so `X ≤ H ⊓ H^g`.
  have hXle : X ≤ H ⊓ H.map (MulAut.conj g).toMonoidHom := by
    refine le_inf hX ?_
    intro x hx
    rw [Subgroup.mem_map]
    refine ⟨g⁻¹ * x * g, hX ((Subgroup.mem_normalizer_iff''.mp hg x).mp hx), ?_⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  -- Lagrange: the order of the intersection is a multiple of the even number `Nat.card X`.
  have hdvd : Nat.card X ∣ Nat.card ↥(H ⊓ H.map (MulAut.conj g).toMonoidHom) :=
    Subgroup.card_dvd_of_le hXle
  obtain ⟨k, hk⟩ := hdvd
  have hev : Even (Nat.card ↥(H ⊓ H.map (MulAut.conj g).toMonoidHom)) := by
    rw [hk]
    exact heven.mul_right k
  exact (Nat.not_even_iff_odd.mpr hoddg) hev

end Work.Reductions
