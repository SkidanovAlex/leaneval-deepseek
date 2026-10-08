import Mathlib
import Submission.Work.BSHallW.Defs
import Submission.Work.Grun.forall_hom_eq_one_iff_closure_pPrime_eq_top

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.BSHallW.SylowReduction` — the easy half of Hall–Wielandt

Let `S` be a Sylow `p`-subgroup of a finite group `G` and `H ≥ S` a subgroup.  If `H` has no
quotient of order `p` (equivalently, if every homomorphism `H →* Multiplicative (ZMod p)` is
trivial), then neither does `G`.

Proof.  Suppose `θ : G →* Multiplicative (ZMod p)` is nontrivial.  Then `θ.ker ⊴ G` has index `p`
(its index is the order of the image, a nontrivial subgroup of the group of order `p`;
`index_ker_eq_prime`), and `θ` vanishes on `H` by hypothesis, so `H ≤ θ.ker`.  Hence
`S ≤ θ.ker`, and then `p` divides `[G : S] = [θ.ker : S]·[G : θ.ker]`, contradicting
`Sylow.not_dvd_index`.

This is the direction in which Hall–Wielandt is *not* needed; it is recorded as a lemma because
Hall–Wielandt is applied to `H = N_G(A) ≥ S`, and the two directions together give the
`↔` of `Work.BSHallW.HallWielandtOddProp`.
-/

set_option autoImplicit false

namespace Work.BSHallW

/-- **The kernel of a nontrivial homomorphism into `ℤ/p` has index `p`.** -/
theorem index_ker_eq_prime {G : Type} [Group G] {p : ℕ} [Fact p.Prime]
    (θ : G →* Multiplicative (ZMod p)) (hθ : θ ≠ 1) : θ.ker.index = p := by
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩
  rw [Subgroup.index_eq_card, Nat.card_congr (QuotientGroup.quotientKerEquivRange θ).toEquiv]
  have hdvd : Nat.card ↥θ.range ∣ p := by
    have h1 : Nat.card ↥θ.range ∣ Nat.card (Multiplicative (ZMod p)) :=
      Subgroup.card_subgroup_dvd_card θ.range
    rwa [Work.Grun.card_multiplicative_zmod p] at h1
  have hne : Nat.card ↥θ.range ≠ 1 := by
    intro h1
    exact hθ (MonoidHom.range_eq_bot_iff.mp (Subgroup.card_eq_one.mp h1))
  rcases hp.eq_one_or_self_of_dvd _ hdvd with h1 | h1
  · exact absurd h1 hne
  · exact h1

/-- **If every homomorphism `H →* ℤ/p` is trivial and `S ≤ H` for a Sylow `p`-subgroup `S`, then
every homomorphism `G →* ℤ/p` is trivial.** -/
theorem forall_hom_eq_one_of_sylow_le {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (S : Sylow p G) {H : Subgroup G} (hSH : (S : Subgroup G) ≤ H)
    (hH : ∀ θ : ↥H →* Multiplicative (ZMod p), θ = 1) :
    ∀ θ : G →* Multiplicative (ZMod p), θ = 1 := by
  intro θ
  by_contra hθ
  have hker : θ.ker.index = p := index_ker_eq_prime θ hθ
  -- `θ` vanishes on `H`
  have hHle : H ≤ θ.ker := by
    intro h hh
    refine MonoidHom.mem_ker.mpr ?_
    have h1 : (θ.comp H.subtype) ⟨h, hh⟩ = 1 := by
      rw [hH (θ.comp H.subtype), MonoidHom.one_apply]
    simpa using h1
  -- hence on `S ≤ H`
  have hSK : (S : Subgroup G) ≤ θ.ker := hSH.trans hHle
  have hp_dvd : p ∣ (S : Subgroup G).index := by
    have h := Subgroup.index_dvd_of_le hSK
    rwa [hker] at h
  exact Sylow.not_dvd_index S hp_dvd

end Work.BSHallW
