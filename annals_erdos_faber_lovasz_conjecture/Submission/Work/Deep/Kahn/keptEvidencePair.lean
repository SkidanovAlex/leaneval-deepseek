import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Kahn.keptEvidenceLaw

#check @Finset.prod_le_prod₀
#check @Finset.prod_pow_eq_pow_sum
#check @Finset.inter_eq_right
#check @Finset.filter_mem_eq_inter
#check @Finset.sum_add_distrib
#check @Finset.card_filter

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
open scoped BigOperators
open Finset

namespace Work.Deep.Kahn

open ErdosFaberLovaszConjecture

noncomputable section

variable {n c : ℕ} {𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)} [Fintype 𝓗]
  {L : 𝓗 → Finset (Fin c)} {K : ℕ} [NeZero K]

/-- The coordinates of `f` that are neither activated-naming-`γ` nor activated-naming-`γ'`. -/
def goodIndex2 (f : 𝓗) (γ γ' : Fin c) : Finset (Fin K × Fin (L f).card) :=
  Finset.univ \ (badIndex (L := L) (K := K) f γ ∪ badIndex (L := L) (K := K) f γ')

lemma mem_goodIndex2 {f : 𝓗} {γ γ' : Fin c} {p : Fin K × Fin (L f).card} :
    p ∈ goodIndex2 (L := L) (K := K) f γ γ' ↔
      ¬(p.1 = 0 ∧ idxColour L f p.2 = γ) ∧ ¬(p.1 = 0 ∧ idxColour L f p.2 = γ') := by
  classical
  simp only [goodIndex2, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union,
    mem_badIndex, not_or]

lemma badIndex_disjoint {f : 𝓗} {γ γ' : Fin c} (hne : γ ≠ γ') :
    Disjoint (badIndex (L := L) (K := K) f γ) (badIndex (L := L) (K := K) f γ') := by
  rw [Finset.disjoint_left]
  intro p hp hq
  rw [mem_badIndex] at hp hq
  exact hne (hp.2.symm.trans hq.2)

lemma card_goodIndex2 {f : 𝓗} {γ γ' : Fin c} (hne : γ ≠ γ') :
    (goodIndex2 (L := L) (K := K) f γ γ').card
      = Fintype.card (Fin K × Fin (L f).card)
        - ((badIndex (L := L) (K := K) f γ).card
            + (badIndex (L := L) (K := K) f γ').card) := by
  classical
  unfold goodIndex2
  rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ,
    Finset.card_union_of_disjoint (badIndex_disjoint (K := K) hne)]

/-- Bernoulli: `1 - k q ≤ (1-q)^k`. -/
lemma one_sub_mul_le_pow {q : ℝ} (hq : q ≤ 2) (k : ℕ) : 1 - (k : ℝ) * q ≤ (1 - q) ^ k := by
  have h := one_add_mul_le_pow (a := -q) (by linarith : (-2 : ℝ) ≤ -q) k
  simpa [mul_neg, sub_eq_add_neg] using h

/-- **The complement of "both `γ` and `γ'` are used at `e`" is a box.** -/
lemma box_notMem_pair {e : 𝓗} {γ γ' : Fin c} (hne : γ ≠ γ') (hγ : γ ∈ L e)
    (hγ' : γ' ∈ L e) :
    {ω : Round.Space K 𝓗 L | γ ∉ keptEvidence K e ω ∧ γ' ∉ keptEvidence K e ω}
      = {ω : Round.Space K 𝓗 L | ∀ f ∈ colWit (L := L) e γ ∪ colWit (L := L) e γ',
          ω f ∈ goodIndex2 (L := L) (K := K) f γ γ'} := by
  classical
  ext ω
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h1, h2⟩ f hf
    have hfe : f ≠ e := by
      rcases Finset.mem_union.mp hf with h | h
      · exact (mem_colWit.mp h).1
      · exact (mem_colWit.mp h).1
    have hmeet : ((f : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty := by
      rcases Finset.mem_union.mp hf with h | h
      · exact (mem_colWit.mp h).2.1
      · exact (mem_colWit.mp h).2.1
    rw [mem_goodIndex2]
    constructor
    · rintro ⟨hc, hi⟩
      by_cases hfγ : f ∈ colWit (L := L) e γ
      · exact h1 (mem_classEvidence.mpr ⟨hγ, f, hfe, hmeet, hc, hi⟩)
      · exact (fun hmem => hfγ (mem_colWit.mpr ⟨hfe, hmeet, hmem⟩))
          (hi ▸ idxColour_mem L f (idxOf ω f))
    · rintro ⟨hc, hi⟩
      by_cases hfγ : f ∈ colWit (L := L) e γ'
      · exact h2 (mem_classEvidence.mpr ⟨hγ', f, hfe, hmeet, hc, hi⟩)
      · exact (fun hmem => hfγ (mem_colWit.mpr ⟨hfe, hmeet, hmem⟩))
          (hi ▸ idxColour_mem L f (idxOf ω f))
  · intro h
    refine ⟨?_, ?_⟩
    · intro hmem
      obtain ⟨-, f, hfe, hmeet, hcls, hidx⟩ := mem_classEvidence.mp hmem
      have hf : f ∈ colWit (L := L) e γ ∪ colWit (L := L) e γ' :=
        Finset.mem_union_left _ (mem_colWit.mpr ⟨hfe, hmeet, hidx ▸ idxColour_mem L f (idxOf ω f)⟩)
      have hg := h f hf
      rw [mem_goodIndex2] at hg
      exact hg.1 ⟨hcls, hidx⟩
    · intro hmem
      obtain ⟨-, f, hfe, hmeet, hcls, hidx⟩ := mem_classEvidence.mp hmem
      have hf : f ∈ colWit (L := L) e γ ∪ colWit (L := L) e γ' :=
        Finset.mem_union_right _ (mem_colWit.mpr ⟨hfe, hmeet, hidx ▸ idxColour_mem L f (idxOf ω f)⟩)
      have hg := h f hf
      rw [mem_goodIndex2] at hg
      exact hg.2 ⟨hcls, hidx⟩

/-- **Negative correlation of the used-colour events.**  For two distinct colours `γ ≠ γ'` of
`L e`, the probability that neither is used is at most the product of the individual
probabilities `(1-q)^{C(D-1)}`; equivalently the events `B_γ` and `B_γ'` are negatively
correlated. -/
lemma prob_notMem_pair {C D Λ : ℕ}
    (hlin : 𝓗.IsLinear)
    (hsize : ∀ e : 𝓗, ErdosFaberLovaszConjecture.edgeSize (e : Set (Fin n)) = C)
    (hdeg : ∀ x : Fin n, ∀ γ : Fin c, (∃ e : 𝓗, x ∈ (e : Set (Fin n)) ∧ γ ∈ L e) →
      Nat.card {e : 𝓗 // x ∈ (e : Set (Fin n)) ∧ γ ∈ L e} = D)
    (hlist : ∀ e : 𝓗, (L e).card = Λ) {e : 𝓗} {γ γ' : Fin c} (hne : γ ≠ γ')
    (hγ : γ ∈ L e) (hγ' : γ' ∈ L e) :
    Work.Deep.Conc.prob {ω : Round.Space K 𝓗 L |
        γ ∉ keptEvidence K e ω ∧ γ' ∉ keptEvidence K e ω}
      ≤ (1 - 1 / ((K : ℝ) * (Λ : ℝ))) ^ (C * (D - 1))
          * (1 - 1 / ((K : ℝ) * (Λ : ℝ))) ^ (C * (D - 1)) := by
  classical
  have hΛ1 : 1 ≤ Λ := by rw [← hlist e]; exact Finset.card_pos.mpr ⟨γ, hγ⟩
  have hΛpos : 0 < Λ := lt_of_lt_of_le Nat.zero_lt_one hΛ1
  have hKpos : (0 : ℝ) < (K : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne K)
  have hΛposR : (0 : ℝ) < (Λ : ℝ) := by exact_mod_cast hΛpos
  have hK1R : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne K)
  have hΛ1R : (1 : ℝ) ≤ (Λ : ℝ) := by exact_mod_cast hΛ1
  have hqpos : (0 : ℝ) < 1 / ((K : ℝ) * (Λ : ℝ)) := by positivity
  have hqle : 1 / ((K : ℝ) * (Λ : ℝ)) ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith
  have hneπ : ∀ f : 𝓗, Nonempty (Round.Coord K 𝓗 L f) := fun f =>
    ⟨(0, ⟨0, by rw [hlist f]; exact hΛpos⟩)⟩
  have hcard : ∀ f : 𝓗, Fintype.card (Round.Coord K 𝓗 L f) = K * Λ := by
    intro f
    rw [Fintype.card_prod, Fintype.card_fin, hlist f, Fintype.card_fin]
  set S := colWit (L := L) e γ ∪ colWit (L := L) e γ' with hS
  rw [box_notMem_pair (K := K) hne hγ hγ']
  rw [box_prob (π := fun f : 𝓗 => Round.Coord K 𝓗 L f) hneπ S
    (fun f => goodIndex2 (L := L) (K := K) f γ γ')]
  -- the two sums of "bad" coordinate counts
  have hsum1 : ∑ f ∈ S, (badIndex (L := L) (K := K) f γ).card = (colWit (L := L) e γ).card := by
    have h1 : ∀ f ∈ S, (badIndex (L := L) (K := K) f γ).card
        = if f ∈ colWit (L := L) e γ then 1 else 0 := by
      intro f hf
      rw [card_badIndex]
      rcases Finset.mem_union.mp hf with hfγ | hfγ'
      · have hfe := (mem_colWit.mp hfγ).1
        have hmeet := (mem_colWit.mp hfγ).2.1
        by_cases hc : γ ∈ L f
        · rw [if_pos hc, if_pos (mem_colWit.mpr ⟨hfe, hmeet, hc⟩)]
        · rw [if_neg hc, if_neg (fun hmem => hc (mem_colWit.mp hmem).2.2)]
      · have hfe := (mem_colWit.mp hfγ').1
        have hmeet := (mem_colWit.mp hfγ').2.1
        by_cases hc : γ ∈ L f
        · rw [if_pos hc, if_pos (mem_colWit.mpr ⟨hfe, hmeet, hc⟩)]
        · rw [if_neg hc, if_neg (fun hmem => hc (mem_colWit.mp hmem).2.2)]
    rw [Finset.sum_congr rfl h1, ← Finset.card_filter]
    congr 1
    rw [Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr Finset.subset_union_left]
  have hsum2 : ∑ f ∈ S, (badIndex (L := L) (K := K) f γ').card = (colWit (L := L) e γ').card := by
    have h1 : ∀ f ∈ S, (badIndex (L := L) (K := K) f γ').card
        = if f ∈ colWit (L := L) e γ' then 1 else 0 := by
      intro f hf
      rw [card_badIndex]
      rcases Finset.mem_union.mp hf with hfγ | hfγ'
      · have hfe := (mem_colWit.mp hfγ).1
        have hmeet := (mem_colWit.mp hfγ).2.1
        by_cases hc : γ' ∈ L f
        · rw [if_pos hc, if_pos (mem_colWit.mpr ⟨hfe, hmeet, hc⟩)]
        · rw [if_neg hc, if_neg (fun hmem => hc (mem_colWit.mp hmem).2.2)]
      · have hfe := (mem_colWit.mp hfγ').1
        have hmeet := (mem_colWit.mp hfγ').2.1
        by_cases hc : γ' ∈ L f
        · rw [if_pos hc, if_pos (mem_colWit.mpr ⟨hfe, hmeet, hc⟩)]
        · rw [if_neg hc, if_neg (fun hmem => hc (mem_colWit.mp hmem).2.2)]
    rw [Finset.sum_congr rfl h1, ← Finset.card_filter]
    congr 1
    rw [Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr Finset.subset_union_right]
  have hExp : (colWit (L := L) e γ).card + (colWit (L := L) e γ').card
      = ∑ f ∈ S, ((badIndex (L := L) (K := K) f γ).card
          + (badIndex (L := L) (K := K) f γ').card) := by
    rw [Finset.sum_add_distrib, hsum1, hsum2]
  -- the per-factor comparison
  have hfac : ∀ f ∈ S,
      ((goodIndex2 (L := L) (K := K) f γ γ').card : ℝ)
          / (Fintype.card (Round.Coord K 𝓗 L f) : ℝ)
        ≤ (1 - 1 / ((K : ℝ) * (Λ : ℝ)))
            ^ ((badIndex (L := L) (K := K) f γ).card
                + (badIndex (L := L) (K := K) f γ').card) := by
    intro f hf
    have hcf : Fintype.card (Fin K × Fin (L f).card) = K * Λ := by
      rw [Fintype.card_prod, Fintype.card_fin, hlist f, Fintype.card_fin]
    have hle : (badIndex (L := L) (K := K) f γ).card
        + (badIndex (L := L) (K := K) f γ').card ≤ K * Λ := by
      rw [← hcf]
      calc (badIndex (L := L) (K := K) f γ).card
            + (badIndex (L := L) (K := K) f γ').card
          = ((badIndex (L := L) (K := K) f γ)
              ∪ (badIndex (L := L) (K := K) f γ')).card :=
            (Finset.card_union_of_disjoint (badIndex_disjoint (K := K) hne)).symm
        _ ≤ (Finset.univ : Finset (Fin K × Fin (L f).card)).card :=
            Finset.card_le_card (Finset.subset_univ _)
        _ = Fintype.card (Fin K × Fin (L f).card) := Finset.card_univ
    have hne0 : ((K : ℝ) * (Λ : ℝ)) ≠ 0 := ne_of_gt (by positivity)
    have hval : ((goodIndex2 (L := L) (K := K) f γ γ').card : ℝ)
          / (Fintype.card (Round.Coord K 𝓗 L f) : ℝ)
        = 1 - (((badIndex (L := L) (K := K) f γ).card
              + (badIndex (L := L) (K := K) f γ').card : ℕ) : ℝ)
            * (1 / ((K : ℝ) * (Λ : ℝ))) := by
      rw [card_goodIndex2 hne, hcf]
      rw [Nat.cast_sub hle]
      push_cast
      rw [div_eq_iff hne0, sub_mul, one_mul, mul_assoc, one_div, inv_mul_cancel₀ hne0,
        mul_one]
    rw [hval]
    exact one_sub_mul_le_pow (by linarith [hqle]) _
  calc ∏ f ∈ S, ((goodIndex2 (L := L) (K := K) f γ γ').card : ℝ)
          / (Fintype.card (Round.Coord K 𝓗 L f) : ℝ)
      ≤ ∏ f ∈ S, (1 - 1 / ((K : ℝ) * (Λ : ℝ)))
          ^ ((badIndex (L := L) (K := K) f γ).card
              + (badIndex (L := L) (K := K) f γ').card) :=
        Finset.prod_le_prod₀
          (fun f hf => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hfac
    _ = (1 - 1 / ((K : ℝ) * (Λ : ℝ)))
          ^ (∑ f ∈ S, ((badIndex (L := L) (K := K) f γ).card
              + (badIndex (L := L) (K := K) f γ').card)) :=
        Finset.prod_pow_eq_pow_sum S _ _
    _ = (1 - 1 / ((K : ℝ) * (Λ : ℝ)))
          ^ ((colWit (L := L) e γ).card + (colWit (L := L) e γ').card) := by rw [hExp]
    _ = (1 - 1 / ((K : ℝ) * (Λ : ℝ))) ^ (C * (D - 1))
          * (1 - 1 / ((K : ℝ) * (Λ : ℝ))) ^ (C * (D - 1)) := by
        rw [card_colWit hlin hsize hdeg e hγ, card_colWit hlin hsize hdeg e hγ', pow_add]

end

end Work.Deep.Kahn
