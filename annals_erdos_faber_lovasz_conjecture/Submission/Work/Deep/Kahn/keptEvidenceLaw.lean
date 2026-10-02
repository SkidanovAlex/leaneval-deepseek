import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Kahn.boxProb

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

/-- The coordinates of `f` that are *not* activated-and-naming `γ`. -/
def goodIndex (f : 𝓗) (γ : Fin c) : Finset (Fin K × Fin (L f).card) :=
  Finset.univ \ badIndex (L := L) (K := K) f γ

lemma mem_goodIndex {f : 𝓗} {γ : Fin c} {p : Fin K × Fin (L f).card} :
    p ∈ goodIndex (L := L) (K := K) f γ ↔ ¬(p.1 = 0 ∧ idxColour L f p.2 = γ) := by
  classical
  simp [goodIndex, mem_badIndex]

lemma card_goodIndex (f : 𝓗) (γ : Fin c) :
    (goodIndex (L := L) (K := K) f γ).card
      = Fintype.card (Fin K × Fin (L f).card) - (if γ ∈ L f then 1 else 0) := by
  classical
  unfold goodIndex
  rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, card_badIndex]

/-- The complement of "`γ` is used at `e`" is the box where every witness edge of `γ`
avoids its activated-naming-`γ` coordinate. -/
lemma box_notMem_keptEvidence {e : 𝓗} {γ : Fin c} (hγ : γ ∈ L e) :
    {ω : Round.Space K 𝓗 L | γ ∉ keptEvidence K e ω}
      = {ω : Round.Space K 𝓗 L |
          ∀ f ∈ colWit (L := L) e γ, ω f ∈ goodIndex (L := L) (K := K) f γ} := by
  classical
  ext ω
  simp only [Set.mem_ofPred_eq]
  constructor
  · intro h f hf
    rw [mem_goodIndex]
    rintro ⟨h1, h2⟩
    obtain ⟨hfe, hmeet, -⟩ := mem_colWit.mp hf
    exact h (mem_classEvidence.mpr
      ⟨hγ, f, hfe, hmeet, h1, h2⟩)
  · intro h hmem
    obtain ⟨-, f, hfe, hmeet, hcls, hidx⟩ := mem_classEvidence.mp hmem
    have hf : f ∈ colWit (L := L) e γ :=
      mem_colWit.mpr ⟨hfe, hmeet, hidx ▸ idxColour_mem L f (idxOf ω f)⟩
    have hg := h f hf
    rw [mem_goodIndex] at hg
    exact hg ⟨hcls, hidx⟩

/-- **The law of a colour, complement form.**  For `γ ∈ L e` the probability that `γ` is *not*
used at `e` is `(1 - 1/(KΛ))^{C(D-1)}`: every one of the `C(D-1)` witness edges of `γ` must
avoid its own activated-naming-`γ` coordinate. -/
lemma prob_notMem_keptEvidence {C D Λ : ℕ}
    (hlin : 𝓗.IsLinear)
    (hsize : ∀ e : 𝓗, ErdosFaberLovaszConjecture.edgeSize (e : Set (Fin n)) = C)
    (hdeg : ∀ x : Fin n, ∀ γ : Fin c, (∃ e : 𝓗, x ∈ (e : Set (Fin n)) ∧ γ ∈ L e) →
      Nat.card {e : 𝓗 // x ∈ (e : Set (Fin n)) ∧ γ ∈ L e} = D)
    (hlist : ∀ e : 𝓗, (L e).card = Λ) {e : 𝓗} {γ : Fin c} (hγ : γ ∈ L e) :
    Work.Deep.Conc.prob {ω : Round.Space K 𝓗 L | γ ∉ keptEvidence K e ω}
      = (1 - 1 / ((K : ℝ) * (Λ : ℝ))) ^ (C * (D - 1)) := by
  classical
  have hΛ1 : 1 ≤ Λ := by rw [← hlist e]; exact Finset.card_pos.mpr ⟨γ, hγ⟩
  have hΛpos : 0 < Λ := lt_of_lt_of_le Nat.zero_lt_one hΛ1
  have hne : ∀ f : 𝓗, Nonempty (Round.Coord K 𝓗 L f) := fun f =>
    ⟨(0, ⟨0, by rw [hlist f]; exact hΛpos⟩)⟩
  have hbox := box_prob (π := fun f : 𝓗 => Round.Coord K 𝓗 L f) hne
    (colWit (L := L) e γ) (fun f => goodIndex (L := L) (K := K) f γ)
  have hfac : ∀ f ∈ colWit (L := L) e γ,
      ((goodIndex (L := L) (K := K) f γ).card : ℝ)
        / (Fintype.card (Round.Coord K 𝓗 L f) : ℝ)
      = 1 - 1 / ((K : ℝ) * (Λ : ℝ)) := by
    intro f hf
    obtain ⟨-, -, hγf⟩ := mem_colWit.mp hf
    have hcf : Fintype.card (Fin K × Fin (L f).card) = K * Λ := by
      rw [Fintype.card_prod, Fintype.card_fin, hlist f, Fintype.card_fin]
    have h1 : (1 : ℕ) ≤ K * Λ := by
      rw [← hcf]; exact Fintype.card_pos_iff.mpr (hne f)
    have hKp : (0 : ℝ) < (K : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne K)
    have hLp : (0 : ℝ) < (Λ : ℝ) := by exact_mod_cast hΛpos
    have hne0 : ((K : ℝ) * (Λ : ℝ)) ≠ 0 := ne_of_gt (by positivity)
    rw [card_goodIndex, if_pos hγf, hcf, Nat.cast_sub h1]
    push_cast
    rw [div_eq_iff hne0, sub_mul, one_mul, div_mul_cancel₀ _ hne0]
  rw [box_notMem_keptEvidence (L := L) (K := K) hγ, hbox,
    Finset.prod_congr rfl hfac, Finset.prod_const,
    card_colWit hlin hsize hdeg e hγ]

/-- **The law of a single colour.**  For `γ ∈ L e` the probability that `γ` is *used* at `e`
is `1 - (1 - 1/(KΛ))^{C(D-1)}`. -/
lemma prob_mem_keptEvidence {C D Λ : ℕ}
    (hlin : 𝓗.IsLinear)
    (hsize : ∀ e : 𝓗, ErdosFaberLovaszConjecture.edgeSize (e : Set (Fin n)) = C)
    (hdeg : ∀ x : Fin n, ∀ γ : Fin c, (∃ e : 𝓗, x ∈ (e : Set (Fin n)) ∧ γ ∈ L e) →
      Nat.card {e : 𝓗 // x ∈ (e : Set (Fin n)) ∧ γ ∈ L e} = D)
    (hlist : ∀ e : 𝓗, (L e).card = Λ) {e : 𝓗} {γ : Fin c} (hγ : γ ∈ L e) :
    Work.Deep.Conc.prob {ω : Round.Space K 𝓗 L | γ ∈ keptEvidence K e ω}
      = 1 - (1 - 1 / ((K : ℝ) * (Λ : ℝ))) ^ (C * (D - 1)) := by
  classical
  have hΛ1 : 1 ≤ Λ := by rw [← hlist e]; exact Finset.card_pos.mpr ⟨γ, hγ⟩
  have hΛpos : 0 < Λ := lt_of_lt_of_le Nat.zero_lt_one hΛ1
  have hne : ∀ f : 𝓗, Nonempty (Round.Coord K 𝓗 L f) := fun f =>
    ⟨(0, ⟨0, by rw [hlist f]; exact hΛpos⟩)⟩
  haveI : Nonempty (Round.Space K 𝓗 L) := ⟨fun f => Classical.choice (hne f)⟩
  have h1 := prob_notMem_keptEvidence (K := K) (L := L) (𝓗 := 𝓗) hlin hsize hdeg hlist hγ
  have h2 := Work.Deep.Conc.prob_compl
    {ω : Round.Space K 𝓗 L | γ ∈ keptEvidence K e ω}
  rw [Set.compl_ofPred] at h2
  have h3 : Work.Deep.Conc.prob {ω : Round.Space K 𝓗 L | γ ∉ keptEvidence K e ω}
      = 1 - Work.Deep.Conc.prob {ω : Round.Space K 𝓗 L | γ ∈ keptEvidence K e ω} := h2
  rw [h1] at h3
  linarith

end

end Work.Deep.Kahn
