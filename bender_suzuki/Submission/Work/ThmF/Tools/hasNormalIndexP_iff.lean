import Mathlib
import Submission.Work.ThmF.Setup
import Submission.Work.Grun.pResidual

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThmF.Tools

set_option linter.style.haveILetI false

open LeanEval.GroupTheory.Defs Submission.Blueprint Work.ThmF

/-- `G` has a normal subgroup of index `p` (`p` prime) if and only if `G` admits a nontrivial
homomorphism into the cyclic group `ℤ/p` written multiplicatively.

Forward: a normal `N` of index `p` gives `G ⧸ N` of order `p`, and any two groups of prime order
are isomorphic, so composing `G →* G ⧸ N` with `G ⧸ N ≃* Multiplicative (ZMod p)` is a nontrivial
homomorphism.

Backward: a nontrivial `θ : G →* Multiplicative (ZMod p)` has `G ⧸ θ.ker ≃* θ.range`, and
`θ.range` is a nontrivial subgroup of a group of prime order `p`, hence has `p` elements; so
`θ.ker` is normal of index `p`. -/
theorem hasNormalIndexP_iff {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] : HasNormalIndexP p G ↔ ¬ (∀ θ : G →* Multiplicative (ZMod p), θ = 1) := by
  have hp : p.Prime := Fact.out
  have hcardtgt : Nat.card (Multiplicative (ZMod p)) = p := by
    rw [← Nat.card_congr (Multiplicative.ofAdd (α := ZMod p)), Nat.card_zmod]
  constructor
  · -- a normal subgroup of prime index gives a nontrivial homomorphism onto `ℤ/p`
    rintro ⟨N, hNnormal, hNindex⟩ hall
    haveI : N.Normal := hNnormal
    have hcardquot : Nat.card (G ⧸ N) = p := by
      rw [← Subgroup.index_eq_card N, hNindex]
    let e : G ⧸ N ≃* Multiplicative (ZMod p) := mulEquivOfPrimeCardEq hcardquot hcardtgt
    -- `N` is proper, so pick `g ∉ N`
    have hNne : N ≠ ⊤ := by
      intro htop
      rw [htop, Subgroup.index_top] at hNindex
      exact hp.ne_one hNindex.symm
    obtain ⟨g, hg⟩ : ∃ g, g ∉ N := by
      by_contra hc
      push Not at hc
      exact hNne ((Subgroup.eq_top_iff' N).mpr hc)
    have hq1 : QuotientGroup.mk' N g ≠ 1 := by
      rw [QuotientGroup.mk'_apply]
      exact fun hh => hg ((QuotientGroup.eq_one_iff g).mp hh)
    -- but `hall` forces this composite to be trivial, hence `↑g = 1`, a contradiction
    have hthis : e (QuotientGroup.mk' N g) = 1 := by
      have h1 := congrArg (fun f : G →* Multiplicative (ZMod p) => f g)
        (hall (e.toMonoidHom.comp (QuotientGroup.mk' N)))
      simpa only [MonoidHom.comp_apply, MonoidHom.one_apply, MulEquiv.coe_toMonoidHom] using h1
    exact hq1 (e.injective (by rw [hthis, map_one]))
  · -- a nontrivial homomorphism gives a normal subgroup of prime index
    intro h
    simp only [not_forall] at h
    obtain ⟨θ, hθ⟩ := h
    refine ⟨θ.ker, MonoidHom.normal_ker θ, ?_⟩
    rw [Subgroup.index_eq_card, Nat.card_congr (QuotientGroup.quotientKerEquivRange θ).toEquiv]
    have hdvd : Nat.card ↥θ.range ∣ p := by
      have := Subgroup.card_subgroup_dvd_card θ.range
      rwa [hcardtgt] at this
    rcases hp.eq_one_or_self_of_dvd _ hdvd with h1 | hp'
    · exact absurd (MonoidHom.range_eq_bot_iff.mp (Subgroup.card_eq_one.mp h1)) hθ
    · exact hp'

end Work.ThmF.Tools
