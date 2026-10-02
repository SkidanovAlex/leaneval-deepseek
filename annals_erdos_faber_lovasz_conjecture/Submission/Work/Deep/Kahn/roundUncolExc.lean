import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Kahn.roundUncolMean

/-!
# `Work.Deep.Kahn.Round.roundUncolExc`

The probability of the **exceptional set** of the certificate argument for `uncolActCount`:
the union bound

  `prob (excSet x γ ℓ) ≤ D · Λ · (1/32)^ℓ`.

For a fixed colour `δ` of the `γ`-edges through `x`, the event `ℓ ≤ conflictAt ω x γ δ` means
that `ℓ` of the at most `D` eligible edges through `x` are activated with colour `δ`; by the
union bound over the `ℓ`-subsets this has probability at most
`C(D,ℓ) (1/(KΛ))^ℓ ≤ (D/(KΛ))^ℓ ≤ (1/32)^ℓ`, using `D/Λ ≤ 1/(1+ε)` and `16C ≤ (1+ε)K`.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open scoped BigOperators
open Finset

namespace Work.Deep.Kahn

open ErdosFaberLovaszConjecture

noncomputable section

open Work.Deep.Conc

namespace Round

variable {n c : ℕ} {𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)} [Fintype 𝓗]
  {L : 𝓗 → Finset (Fin c)} {K D : ℕ} {x : Fin n} {γ : Fin c}

/-- The eligible edges of the colour degree of `(x,γ)` at the colour `δ`. -/
def elig (x : Fin n) (γ δ : Fin c) : Finset 𝓗 := by
  classical
  exact (colThru (L := L) x γ).filter (fun e : 𝓗 => δ ∈ L e)

lemma mem_elig {x : Fin n} {γ δ : Fin c} {e : 𝓗} :
    e ∈ elig (L := L) x γ δ ↔ x ∈ (e : Set (Fin n)) ∧ γ ∈ L e ∧ δ ∈ L e := by
  classical
  rw [elig, Finset.mem_filter, mem_colThru]
  tauto

/-- **A single colour is the colour of `ℓ` activated `γ`-edges through `x` only with
probability at most `(1/32)^ℓ`.** -/
theorem prob_conflictAt_le [NeZero K] {Λ : ℕ} (hΛ : ∀ e : 𝓗, (L e).card = Λ)
    (hΛ1 : 1 ≤ Λ) (hD : (D : ℝ) / ((K : ℝ) * (Λ : ℝ)) ≤ 1 / 32)
    (hcol : (colThru (L := L) x γ).card ≤ D)
    (δ : Fin c) (ℓ : ℕ) :
    Work.Deep.Conc.prob {ω : Space K 𝓗 L | ℓ ≤ conflictAt (L := L) ω x γ δ}
      ≤ (1 / 32 : ℝ) ^ ℓ := by
  classical
  have hne : ∀ i : 𝓗, Nonempty (Coord K 𝓗 L i) :=
    fun i => ⟨(0, ⟨0, by rw [hΛ i]; omega⟩)⟩
  haveI : Nonempty (Space K 𝓗 L) := ⟨fun i => Classical.choice (hne i)⟩
  set N : Finset 𝓗 := elig (L := L) x γ δ with hN
  set v : ∀ i : 𝓗, Coord K 𝓗 L i := actCoord (K := K) (Classical.arbitrary (Space K 𝓗 L)) δ
    with hv
  have hNsub : N ⊆ colThru (L := L) x γ := by
    rw [hN]; exact Finset.filter_subset _ _
  -- the event is contained in the union over the `ℓ`-subsets of `N`
  have hsub : {ω : Space K 𝓗 L | ℓ ≤ conflictAt (L := L) ω x γ δ} ⊆
      ⋃ S : ↥(N.powersetCard ℓ), {ω : Space K 𝓗 L | ∀ e ∈ (S : Finset 𝓗), ω e = v e} := by
    intro ω hω
    have hcard : ℓ ≤ (N.filter (fun e : 𝓗 => active ω e ∧ colour ω e = δ)).card := by
      have h1 : conflictAt (L := L) ω x γ δ
          = (N.filter (fun e : 𝓗 => active ω e ∧ colour ω e = δ)).card := by
        rw [conflictAt, hN, elig, Finset.filter_filter]
      have h2 : ℓ ≤ conflictAt (L := L) ω x γ δ := hω
      rwa [h1] at h2
    obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq hcard
    have hSN : S ∈ N.powersetCard ℓ :=
      Finset.mem_powersetCard.mpr ⟨hSsub.trans (Finset.filter_subset _ _), hScard⟩
    refine Set.mem_iUnion.mpr ⟨⟨S, hSN⟩, ?_⟩
    intro e he
    have he' : active ω e ∧ colour ω e = δ := (Finset.mem_filter.mp (hSsub he)).2
    have heN : e ∈ N := (Finset.mem_powersetCard.mp hSN).1 he
    have heδ : δ ∈ L e := by
      rw [hN] at heN
      exact (mem_elig.mp heN).2.2
    exact (eq_actCoord_iff (K := K) heδ).mpr he'
  refine le_trans (Work.Deep.Conc.prob_mono hsub) ?_
  refine le_trans (Work.Deep.Conc.prob_iUnion_le _) ?_
  -- each `ℓ`-subset has probability `(1/(KΛ))^ℓ`
  have hone : ∀ S : ↥(N.powersetCard ℓ),
      Work.Deep.Conc.prob {ω : Space K 𝓗 L | ∀ e ∈ (S : Finset 𝓗), ω e = v e}
        = (1 / ((K : ℝ) * (Λ : ℝ))) ^ ℓ := by
    intro S
    have hScard : (S : Finset 𝓗).card = ℓ := (Finset.mem_powersetCard.mp S.property).2
    rw [Work.Deep.Conc.prob_all_eq (S : Finset 𝓗) v hne]
    have hfac : ∀ e ∈ (S : Finset 𝓗),
        1 / (Fintype.card (Coord K 𝓗 L e) : ℝ) = 1 / ((K : ℝ) * (Λ : ℝ)) := by
      intro e _
      rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, hΛ e, Nat.cast_mul]
    rw [Finset.prod_congr rfl hfac, Finset.prod_const, hScard]
  refine le_trans (Finset.sum_le_sum fun S _ => le_of_eq (hone S)) ?_
  rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_coe,
    Finset.card_powersetCard]
  have hNcard : N.card ≤ D := le_trans (Finset.card_le_card hNsub) hcol
  calc ((N.card.choose ℓ : ℕ) : ℝ) * (1 / ((K : ℝ) * (Λ : ℝ))) ^ ℓ
      ≤ ((N.card : ℝ) ^ ℓ) * (1 / ((K : ℝ) * (Λ : ℝ))) ^ ℓ := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact_mod_cast Nat.choose_le_pow N.card ℓ
    _ = ((N.card : ℝ) / ((K : ℝ) * (Λ : ℝ))) ^ ℓ := by
        rw [← mul_pow]; ring_nf
    _ ≤ ((D : ℝ) / ((K : ℝ) * (Λ : ℝ))) ^ ℓ := by
        refine pow_le_pow_left₀ (by positivity) ?_ ℓ
        exact div_le_div_of_nonneg_right (by exact_mod_cast hNcard) (by positivity)
    _ ≤ (1 / 32 : ℝ) ^ ℓ :=
        pow_le_pow_left₀ (by positivity) hD ℓ

/-- **The probability of the exceptional set.** -/
theorem roundUncolExc {n c C D Λ K : ℕ}
    {𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)} [Fintype 𝓗] [NeZero K]
    {L : 𝓗 → Finset (Fin c)} {ε : ℝ}
    (hC : 2 ≤ C) (hΛ : ∀ e : 𝓗, (L e).card = Λ)
    (hdeg : ∀ y : Fin n, ∀ δ : Fin c,
      (∃ e : 𝓗, y ∈ (e : Set (Fin n)) ∧ δ ∈ L e) →
      Nat.card {e : 𝓗 // y ∈ (e : Set (Fin n)) ∧ δ ∈ L e} = D)
    (h16 : (16 : ℝ) * C ≤ (1 + ε) * K) (hεΛ : (1 + ε) * (D : ℝ) ≤ (Λ : ℝ))
    (x : Fin n) (γ : Fin c)
    (hxγ : ∃ e : 𝓗, x ∈ (e : Set (Fin n)) ∧ γ ∈ L e) (ℓ : ℕ) :
    Work.Deep.Conc.prob (excSet (K := K) (L := L) x γ ℓ)
      ≤ (D : ℝ) * (Λ : ℝ) * ((1 / 32 : ℝ) ^ ℓ) := by
  classical
  have hex := hxγ
  obtain ⟨e₀, he₀, hγ₀⟩ := hex
  have hΛ1 : 1 ≤ Λ := by
    rw [← hΛ e₀]
    exact Finset.card_pos.mpr ⟨γ, hγ₀⟩
  have hcol : (colThru (L := L) x γ).card = D := by
    have h := hdeg x γ hxγ
    rw [← h] 
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    rfl
  -- the ratio `D/(KΛ) ≤ 1/32`
  have hD32 : (D : ℝ) / ((K : ℝ) * (Λ : ℝ)) ≤ 1 / 32 := by
    have hKpos : (0 : ℝ) < (K : ℝ) := by
      have : 0 < K := Nat.pos_of_ne_zero (NeZero.ne K)
      exact_mod_cast this
    have hΛpos : (0 : ℝ) < (Λ : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hΛ1)
    have hεpos : (0 : ℝ) < 1 + ε := by
      have h16' : (16 : ℝ) * (C : ℝ) ≤ (1 + ε) * (K : ℝ) := h16
      have hC2 : (2 : ℝ) ≤ (C : ℝ) := by exact_mod_cast hC
      by_contra hcon
      push Not at hcon
      have hpos : (1 + ε) * (K : ℝ) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hcon hKpos.le
      nlinarith [h16', hC2, hpos]
    have h1 : (D : ℝ) / (Λ : ℝ) ≤ 1 / (1 + ε) := by
      rw [div_le_div_iff₀ hΛpos hεpos]
      nlinarith [hεΛ]
    have h32 : (32 : ℝ) ≤ (1 + ε) * (K : ℝ) := by
      have h16' : (16 : ℝ) * (C : ℝ) ≤ (1 + ε) * (K : ℝ) := h16
      have hC2 : (2 : ℝ) ≤ (C : ℝ) := by exact_mod_cast hC
      nlinarith
    calc (D : ℝ) / ((K : ℝ) * (Λ : ℝ)) = ((D : ℝ) / (Λ : ℝ)) / (K : ℝ) := by ring
      _ ≤ (1 / (1 + ε)) / (K : ℝ) := div_le_div_of_nonneg_right h1 hKpos.le
      _ = 1 / ((1 + ε) * (K : ℝ)) := by rw [div_div]
      _ ≤ 1 / 32 := one_div_le_one_div_of_le (by norm_num) h32
  -- the union bound over the colours of `colThruCols`
  have hsub : excSet (K := K) (L := L) x γ ℓ ⊆
      ⋃ δ : {δ : Fin c // δ ∈ colThruCols (L := L) x γ},
        {ω : Space K 𝓗 L | ℓ ≤ conflictAt (L := L) ω x γ δ.1} := by
    intro ω hω
    obtain ⟨δ, hδ, hle⟩ := (mem_excSet_iff (K := K) (L := L) (x := x) (γ := γ) (ℓ := ℓ)).mp hω
    exact Set.mem_iUnion.mpr ⟨⟨δ, hδ⟩, hle⟩
  have hcolcols : (colThruCols (L := L) x γ).card ≤ D * Λ := by
    rw [colThruCols]
    refine le_trans Finset.card_biUnion_le ?_
    have h1 : ∀ e ∈ colThru (L := L) x γ, (L e).card ≤ Λ := fun e _ => le_of_eq (hΛ e)
    refine le_trans (Finset.sum_le_sum h1) ?_
    rw [Finset.sum_const, nsmul_eq_mul, hcol]
    simp
  refine le_trans (Work.Deep.Conc.prob_mono hsub) ?_
  refine le_trans (Work.Deep.Conc.prob_iUnion_le _) ?_
  have hstep : ∀ δ : {δ : Fin c // δ ∈ colThruCols (L := L) x γ},
      Work.Deep.Conc.prob {ω : Space K 𝓗 L | ℓ ≤ conflictAt (L := L) ω x γ δ.1}
        ≤ (1 / 32 : ℝ) ^ ℓ :=
    fun δ => prob_conflictAt_le (K := K) (L := L) (x := x) (γ := γ) (D := D)
      hΛ hΛ1 hD32 (le_of_eq hcol) δ.1 ℓ
  refine le_trans (Finset.sum_le_sum fun δ _ => hstep δ) ?_
  rw [← Finset.sum_subtype (colThruCols (L := L) x γ) (fun δ => Iff.rfl)
    (fun _ : Fin c => (1 / 32 : ℝ) ^ ℓ)]
  rw [Finset.sum_const, nsmul_eq_mul]
  have hcast : ((colThruCols (L := L) x γ).card : ℝ) ≤ (D : ℝ) * (Λ : ℝ) := by
    exact_mod_cast hcolcols
  calc ((colThruCols (L := L) x γ).card : ℝ) * (1 / 32 : ℝ) ^ ℓ
      ≤ ((D : ℝ) * (Λ : ℝ)) * (1 / 32 : ℝ) ^ ℓ :=
        mul_le_mul_of_nonneg_right hcast (by positivity)
    _ = (D : ℝ) * (Λ : ℝ) * (1 / 32 : ℝ) ^ ℓ := by ring

end Round

end

end Work.Deep.Kahn
