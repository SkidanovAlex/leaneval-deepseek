import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Kahn.UsedColoursSetup
import Submission.Work.Deep.Conc.BruhnJoos.reed_adapter
import Submission.Work.Deep.Reed.Prob.pi_uniform_prob_box

/-!
# Box probabilities on the round space, and the law of `keptEvidence`

This module proves the two probabilistic identities on which the `usedColours`
estimate rests, for the uniform measure of `Work.Deep.Conc` on the product
space `Round.Space K 𝓗 L = ∀ f : 𝓗, Fin K × Fin (L f).card`:

* `box_prob` -- the probability of a *box* `{ξ | ∀ i ∈ S, ξ i ∈ A i}` is the
  product of the marginals (transported from the `FinProb` layer, where it is
  `Work.Deep.Reed.Prob.pi_prob_box_finset`);
* `prob_keptEvidence` -- for a colour `γ ∈ L e`, the probability that `γ` is
  *used* at `e` (i.e. belongs to `keptEvidence K e ·`) is exactly
  `1 - (1 - 1/(KΛ)) ^ (colWit e γ).card`.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open scoped BigOperators
open Finset

namespace Work.Deep.Kahn

open ErdosFaberLovaszConjecture

noncomputable section

/-- **Box probabilities** for the uniform measure of `Work.Deep.Conc` on a product space. -/
theorem box_prob {ι : Type*} [Fintype ι] [DecidableEq ι] {π : ι → Type*} [∀ i, Fintype (π i)]
    (hne : ∀ i, Nonempty (π i)) (S : Finset ι) (A : ∀ i, Finset (π i)) :
    Work.Deep.Conc.prob {ξ : ∀ i, π i | ∀ i ∈ S, ξ i ∈ A i}
      = ∏ i ∈ S, ((A i).card : ℝ) / (Fintype.card (π i) : ℝ) := by
  haveI : ∀ i, Nonempty (π i) := hne
  rw [← Work.Deep.Conc.BruhnJoos.pi_uniform_prob_eq hne]
  rw [Work.Deep.Reed.Prob.pi_prob_box_finset]
  exact Finset.prod_congr rfl (fun i _ => Work.Deep.Reed.Prob.uniform_prob_mem (A i))

variable {n c : ℕ} {𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)} [Fintype 𝓗]
  {L : 𝓗 → Finset (Fin c)} {K : ℕ} [NeZero K]

/-- The coordinates of `f` that are *activated and name `γ`*. -/
def badIndex (f : 𝓗) (γ : Fin c) : Finset (Fin K × Fin (L f).card) := by
  classical
  exact Finset.univ.filter (fun p => p.1 = 0 ∧ idxColour L f p.2 = γ)

lemma mem_badIndex {f : 𝓗} {γ : Fin c} {p : Fin K × Fin (L f).card} :
    p ∈ badIndex (L := L) (K := K) f γ ↔ p.1 = 0 ∧ idxColour L f p.2 = γ := by
  classical
  simp [badIndex]

/-- The number of coordinates of `f` activated and naming `γ` is `1` when `γ ∈ L f` and `0`
otherwise. -/
lemma card_badIndex (f : 𝓗) (γ : Fin c) :
    (badIndex (L := L) (K := K) f γ).card = if γ ∈ L f then 1 else 0 := by
  classical
  by_cases h : γ ∈ L f
  · rw [if_pos h]
    refine Finset.card_eq_one.mpr
      ⟨(0, (Finset.equivFin (L f)) ⟨γ, h⟩), ?_⟩
    ext p
    rw [mem_badIndex, Finset.mem_singleton]
    constructor
    · rintro ⟨h1, h2⟩
      refine Prod.ext h1 ?_
      apply idxColour_injective L f
      rw [h2]
      simp [idxColour]
    · rintro rfl
      exact ⟨rfl, by simp [idxColour]⟩
  · rw [if_neg h, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro p hp
    rw [mem_badIndex] at hp
    exact h (hp.2 ▸ idxColour_mem L f p.2)

end

end Work.Deep.Kahn
