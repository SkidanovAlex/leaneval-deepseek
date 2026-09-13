import Mathlib
import Submission.Grassmann.Levels

/-!
# The first step of the KMS argument: `Φ` controls the second moment

For `S ⊆ Gr k ℓ` with `f = 1_S - ρ` (where `ρ = #S / N` is the density) one has

  `⟨A f, f⟩ = d · #S · (1 - ρ - Φ(S))`,

where `d = (2^ℓ-1)(2^(k-ℓ+1)-2)` is the degree.  This file contains the combinatorial core:
the number of *ordered* adjacent pairs inside `S` plus the number of crossing ordered pairs
equals `d · #S`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

open PseudorandomGrassmann
open Module Finset Filter
open Classical

local notation "𝔽₂" => ZMod 2

namespace Submission.Grassmann
namespace F2

noncomputable section

variable {k ℓ : ℕ}

-- We resolve decidability through the classical instances so that terms such as `Sᶜ`
-- are elaborated exactly as in the body of `Φ` (whose `DecidableEq` came from
-- `Classical.propDecidable`).
attribute [-instance] Subtype.instDecidableEq

/-- The indicator function of a finite set of vertices, as a `ℚ`-valued function. -/
def ind (S : Finset (GrVertex k ℓ)) : GrVertex k ℓ → ℚ := fun L => if L ∈ S then 1 else 0

lemma ind_apply (S : Finset (GrVertex k ℓ)) (L : GrVertex k ℓ) :
    ind S L = if L ∈ S then 1 else 0 := rfl

/-- The neighbours of `L` lying in `S`. -/
def nbrIn (L : GrVertex k ℓ) (S : Finset (GrVertex k ℓ)) : Finset (GrVertex k ℓ) :=
  (Finset.univ.filter (fun M => (Gr k ℓ).Adj L M)).filter (fun M => M ∈ S)

lemma mem_nbrIn {L : GrVertex k ℓ} {S : Finset (GrVertex k ℓ)} {M : GrVertex k ℓ} :
    M ∈ nbrIn L S ↔ (Gr k ℓ).Adj L M ∧ M ∈ S := by
  simp [nbrIn, and_comm]

lemma nbrIn_univ (L : GrVertex k ℓ) :
    (nbrIn L Finset.univ).card = (Gr k ℓ).degree L := by
  rw [nbrIn, Finset.filter_true_of_mem (fun M _ => Finset.mem_univ M),
    card_adjFinset_eq_degree]

/-- The cardinality of `nbrIn` as a sum of indicators. -/
lemma card_nbrIn_eq (S : Finset (GrVertex k ℓ)) (L : GrVertex k ℓ) :
    (nbrIn L S).card = ∑ M ∈ S, (if (Gr k ℓ).Adj L M then 1 else 0) := by
  classical
  rw [Finset.sum_boole]
  congr 1
  ext M
  simp only [nbrIn, Finset.mem_filter, Finset.mem_univ, true_and]
  exact and_comm

/-- **The ordered adjacent pairs with first vertex in `S` and second in `T`.** -/
lemma card_interedges_eq_sum (S T : Finset (GrVertex k ℓ)) :
    ((Gr k ℓ).interedges S T).card
      = ∑ L ∈ S, ∑ M ∈ T, (if (Gr k ℓ).Adj L M then 1 else 0) := by
  classical
  rw [SimpleGraph.interedges, Rel.interedges, Finset.card_filter, Finset.sum_product]

/-- `adjOp` of an indicator is the number of neighbours in that set. -/
lemma adjOp_ind (S : Finset (GrVertex k ℓ)) (L : GrVertex k ℓ) :
    adjOp (ind S) L = ((nbrIn L S).card : ℚ) := by
  classical
  rw [adjOp, nbrIn]
  rw [Finset.sum_congr rfl (fun M _ => ind_apply S M)]
  rw [Finset.sum_boole]

/-- **Ordered adjacent pairs, as a sum of `adjOp`s.** -/
lemma sum_adjOp_ind (S T : Finset (GrVertex k ℓ)) :
    ∑ L ∈ S, adjOp (ind T) L = (((Gr k ℓ).interedges S T).card : ℚ) := by
  classical
  rw [card_interedges_eq_sum]
  push_cast
  refine Finset.sum_congr rfl (fun L _ => ?_)
  rw [adjOp_ind, card_nbrIn_eq]
  push_cast
  rfl

/-- The neighbours of a vertex split according to whether they lie in `S`. -/
lemma card_nbrIn_add (S : Finset (GrVertex k ℓ)) (L : GrVertex k ℓ) :
    (nbrIn L S).card + (nbrIn L Sᶜ).card = (Gr k ℓ).degree L := by
  classical
  rw [← nbrIn_univ L, ← Finset.card_union_of_disjoint]
  · congr 1
    ext M
    simp only [mem_nbrIn, Finset.mem_union, Finset.mem_compl, Finset.mem_univ, and_true]
    tauto
  · rw [Finset.disjoint_left]
    intro M hM hM'
    rw [mem_nbrIn] at hM hM'
    exact (Finset.mem_compl.mp hM'.2) hM.2

/-- **The key identity**: the number of ordered adjacent pairs inside `S`, plus the number of
crossing ordered pairs, is `d · #S`. -/
lemma card_interedges_self_add (hℓ : 1 ≤ ℓ) (S : Finset (GrVertex k ℓ)) :
    (((Gr k ℓ).interedges S S).card : ℚ) + (((Gr k ℓ).interedges S Sᶜ).card : ℚ)
      = (((2 ^ ℓ - 1) * (2 ^ (k - ℓ + 1) - 2)) : ℚ) * (S.card : ℚ) := by
  classical
  rw [← sum_adjOp_ind (k := k) (ℓ := ℓ) S S,
    ← sum_adjOp_ind (k := k) (ℓ := ℓ) S Sᶜ,
    ← Finset.sum_add_distrib]
  have h1 : ∀ L ∈ S, adjOp (ind S) L + adjOp (ind Sᶜ) L
      = (((2 ^ ℓ - 1) * (2 ^ (k - ℓ + 1) - 2) : ℕ) : ℚ) := by
    intro L _
    rw [adjOp_ind, adjOp_ind, ← Nat.cast_add, card_nbrIn_add, Gr_degree_eq_value hℓ L]
  rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul]
  have h2 : 2 ≤ 2 ^ (k - ℓ + 1) := by
    have := Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega : 1 ≤ k - ℓ + 1)
    simpa using this
  have hD : (((2 ^ ℓ - 1) * (2 ^ (k - ℓ + 1) - 2) : ℕ) : ℚ)
      = ((2 : ℚ) ^ ℓ - 1) * ((2 : ℚ) ^ (k - ℓ + 1) - 2) := by
    push_cast [Nat.cast_sub (Nat.one_le_two_pow (n := ℓ)), Nat.cast_sub h2]
    ring
  rw [hD]
  ring

/-! ## The inner product identity -/

lemma ind_mul_ind (S : Finset (GrVertex k ℓ)) (L : GrVertex k ℓ) :
    ind S L * ind S L = if L ∈ S then 1 else 0 := by
  rw [ind_apply]
  by_cases h : L ∈ S <;> simp [h]

lemma ind_mul_one (S : Finset (GrVertex k ℓ)) (L : GrVertex k ℓ) :
    ind S L * 1 = if L ∈ S then 1 else 0 := by
  rw [ind_apply]
  by_cases h : L ∈ S <;> simp [h]

lemma sum_ind_eq (S : Finset (GrVertex k ℓ)) :
    (∑ L, (if L ∈ S then (1 : ℚ) else 0)) = (S.card : ℚ) := by
  rw [← Finset.sum_filter,
    show Finset.univ.filter (fun L => L ∈ S) = S from by ext L; simp,
    Finset.sum_const, nsmul_eq_mul, mul_one]

lemma stdInner_ind_self (S : Finset (GrVertex k ℓ)) :
    stdInner k ℓ (ind S) (ind S) = (S.card : ℚ) := by
  rw [stdInner_apply, Finset.sum_congr rfl (fun L _ => ind_mul_ind S L), sum_ind_eq]

lemma stdInner_ind_one (S : Finset (GrVertex k ℓ)) :
    stdInner k ℓ (ind S) (fun _ => (1 : ℚ)) = (S.card : ℚ) := by
  rw [stdInner_apply, Finset.sum_congr rfl (fun L _ => ind_mul_one S L), sum_ind_eq]

lemma stdInner_one_one (k ℓ : ℕ) :
    stdInner k ℓ (fun _ => (1 : ℚ)) (fun _ => (1 : ℚ))
      = (Fintype.card (GrVertex k ℓ) : ℚ) := by
  rw [stdInner_apply, Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  ring

lemma stdInner_adjOpLM_ind (S : Finset (GrVertex k ℓ)) :
    stdInner k ℓ (adjOpLM (k := k) (ℓ := ℓ) (ind S)) (ind S)
      = (((Gr k ℓ).interedges S S).card : ℚ) := by
  have h1 : ∀ L, adjOpLM (k := k) (ℓ := ℓ) (ind S) L * ind S L
      = if L ∈ S then adjOp (ind S) L else 0 := by
    intro L
    rw [adjOpLM_apply, ind_apply]
    by_cases h : L ∈ S <;> simp [h]
  rw [stdInner_apply, Finset.sum_congr rfl (fun L _ => h1 L), ← Finset.sum_filter,
    show Finset.univ.filter (fun L => L ∈ S) = S from by ext L; simp]
  exact sum_adjOp_ind S S

/-- **`Φ` in terms of the crossing edges.** -/
lemma Phi_Gr_eq (hℓ : 1 ≤ ℓ) (S : Finset (GrVertex k ℓ)) (hS : S.Nonempty) :
    Φ (Gr k ℓ) S hS
      = ((#((Gr k ℓ).interedges S Sᶜ) : ℚ))
        / (((2 ^ ℓ - 1) * (2 ^ (k - ℓ + 1) - 2) : ℕ) * #S) := by
  rw [Φ, Gr_degree_eq_value hℓ hS.choose, Nat.cast_mul]

/-! ## Density and the second-moment identity -/

/-- The density `#S / N` of a set of vertices, as a rational number. -/
noncomputable def dens (S : Finset (GrVertex k ℓ)) : ℚ :=
  (S.card : ℚ) / (Fintype.card (GrVertex k ℓ) : ℚ)

lemma sum_ind_eq' (S : Finset (GrVertex k ℓ)) : ∑ L, ind S L = (S.card : ℚ) := by
  rw [Finset.sum_congr rfl (fun L _ => ind_apply S L), sum_ind_eq]

lemma dens_mul_card (S : Finset (GrVertex k ℓ)) (hS : S.Nonempty) :
    dens S * (Fintype.card (GrVertex k ℓ) : ℚ) = (S.card : ℚ) := by
  have h1 : S.card ≤ Fintype.card (GrVertex k ℓ) := Finset.card_le_univ S
  have h2 : 0 < S.card := Finset.card_pos.mpr hS
  have h3 : Fintype.card (GrVertex k ℓ) ≠ 0 :=
    Nat.pos_iff_ne_zero.mp (lt_of_lt_of_le h2 h1)
  rw [dens, div_mul_cancel₀]
  exact Nat.cast_ne_zero.mpr h3

lemma dens_mul_card' (S : Finset (GrVertex k ℓ)) :
    dens S * (Fintype.card (GrVertex k ℓ) : ℚ) = (S.card : ℚ) := by
  rcases S.eq_empty_or_nonempty with h | h
  · subst h
    simp [dens]
  · exact dens_mul_card S h

lemma sum_adjOp_ind_univ (hℓ : 1 ≤ ℓ) (S : Finset (GrVertex k ℓ)) :
    ∑ L, adjOp (ind S) L
      = ((((2 ^ ℓ - 1) * (2 ^ (k - ℓ + 1) - 2)) : ℕ) : ℚ) * (S.card : ℚ) := by
  have h := adjOp_comm (k := k) (ℓ := ℓ) (ind S) (fun _ => (1 : ℚ))
  simp only [mul_one] at h
  rw [← h]
  have h2 : ∀ L : GrVertex k ℓ, ind S L * adjOp (fun _ => (1 : ℚ)) L
      = ind S L * ((((2 ^ ℓ - 1) * (2 ^ (k - ℓ + 1) - 2)) : ℕ) : ℚ) := by
    intro L
    rw [adjOp_const' hℓ]
    ring
  rw [Finset.sum_congr rfl (fun L _ => h2 L), ← Finset.sum_mul, sum_ind_eq', mul_comm]

lemma sum_adjOp_mul_ind (S : Finset (GrVertex k ℓ)) :
    ∑ L, adjOp (ind S) L * ind S L = (((Gr k ℓ).interedges S S).card : ℚ) := by
  have h := stdInner_adjOpLM_ind (k := k) (ℓ := ℓ) S
  rw [stdInner_apply] at h
  rw [Finset.sum_congr rfl (fun L (_ : L ∈ Finset.univ) => by rw [adjOpLM_apply])] at h
  exact h


/-- The common degree `d = (2^ℓ-1)(2^(k-ℓ+1)-2)` of `Gr k ℓ`, as a rational number. -/
def degQ (k ℓ : ℕ) : ℚ := ((2 ^ ℓ - 1) * (2 ^ (k - ℓ + 1) - 2) : ℚ)

lemma degQ_eq_nat (k ℓ : ℕ) :
    degQ k ℓ = ((((2 ^ ℓ - 1) * (2 ^ (k - ℓ + 1) - 2)) : ℕ) : ℚ) := by
  have h1 : 1 ≤ 2 ^ ℓ := Nat.one_le_two_pow
  have h2 : 2 ≤ 2 ^ (k - ℓ + 1) := by
    have := Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega : 1 ≤ k - ℓ + 1)
    simpa using this
  rw [degQ, Nat.cast_mul, Nat.cast_sub h1, Nat.cast_sub h2]
  push_cast
  ring

lemma sum_adjOp_ind_univ' (hℓ : 1 ≤ ℓ) (S : Finset (GrVertex k ℓ)) :
    ∑ L, adjOp (ind S) L = degQ k ℓ * (S.card : ℚ) := by
  rw [sum_adjOp_ind_univ hℓ S, degQ_eq_nat]

lemma degQ_mul_card (S : Finset (GrVertex k ℓ)) :
    degQ k ℓ * (S.card : ℚ) = ((((2 ^ ℓ - 1) * (2 ^ (k - ℓ + 1) - 2)) : ℕ) : ℚ) * (S.card : ℚ) := by
  rw [degQ_eq_nat]

lemma Phi_Gr_eq' (hℓ : 1 ≤ ℓ) (S : Finset (GrVertex k ℓ)) (hS : S.Nonempty) :
    Φ (Gr k ℓ) S hS
      = (((Gr k ℓ).interedges S Sᶜ).card : ℚ) / (degQ k ℓ * (S.card : ℚ)) := by
  rw [Phi_Gr_eq hℓ S hS, ← degQ_mul_card S]

/-- **`Φ` controls the crossing-edge count.** -/
lemma Phi_mul_deg (hℓ : 1 ≤ ℓ) (S : Finset (GrVertex k ℓ)) (hS : S.Nonempty) :
    Φ (Gr k ℓ) S hS * degQ k ℓ * (S.card : ℚ)
      = (((Gr k ℓ).interedges S Sᶜ).card : ℚ) := by
  by_cases hD : degQ k ℓ * (S.card : ℚ) = 0
  · have hcs := card_interedges_self_add hℓ S
    simp only [degQ] at hD ⊢
    have hE : (((Gr k ℓ).interedges S Sᶜ).card : ℚ) = 0 := by
      have h1 : (0 : ℚ) ≤ (((Gr k ℓ).interedges S S).card : ℚ) := Nat.cast_nonneg _
      linarith
    rw [hE, mul_assoc, hD, mul_zero]
  · rw [Phi_Gr_eq' hℓ S hS, mul_assoc,
      div_mul_cancel₀ _ (show degQ k ℓ * (S.card : ℚ) ≠ 0 from hD)]

/-- **The second-moment identity, edge-count form.** -/
lemma inner_self_identity (hℓ : 1 ≤ ℓ) (S : Finset (GrVertex k ℓ)) (hS : S.Nonempty) :
    (((Gr k ℓ).interedges S S).card : ℚ) - dens S * degQ k ℓ * (S.card : ℚ)
      = degQ k ℓ * (S.card : ℚ) * (1 - Φ (Gr k ℓ) S hS - dens S) := by
  have hcs := card_interedges_self_add hℓ S
  have hcs' : (((Gr k ℓ).interedges S S).card : ℚ)
      + (((Gr k ℓ).interedges S Sᶜ).card : ℚ) = degQ k ℓ * (S.card : ℚ) := hcs
  have hphi := Phi_mul_deg hℓ S hS
  have hself : (((Gr k ℓ).interedges S S).card : ℚ)
      = degQ k ℓ * (S.card : ℚ) - (((Gr k ℓ).interedges S Sᶜ).card : ℚ) := by linarith
  rw [hself, ← hphi]
  ring

/-- The adjacency operator commutes with subtraction (pointwise). -/
lemma adjOp_sub (f g : GrVertex k ℓ → ℚ) (L : GrVertex k ℓ) :
    adjOp (f - g) L = adjOp f L - adjOp g L := by
  rw [adjOp_apply, adjOp_apply, adjOp_apply, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun L' _ => by simp)

/-- Scaling (pointwise). -/
lemma adjOp_smul' (c : ℚ) (f : GrVertex k ℓ → ℚ) (L : GrVertex k ℓ) :
    adjOp (c • f) L = c * adjOp f L := by
  rw [adjOp_apply, adjOp_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun L' _ => by simp)

/-- **The KMS second-moment identity**: for `f = 1_S - ρ` with `ρ = #S/N`,
`⟨A f, f⟩ = d · #S · (1 - ρ - Φ(S))`. -/
lemma inner_adjOp_centered (hℓ : 1 ≤ ℓ) (S : Finset (GrVertex k ℓ)) (hS : S.Nonempty) :
    stdInner k ℓ (adjOpLM (k := k) (ℓ := ℓ) (fun L => ind S L - dens S))
      (fun L => ind S L - dens S)
      = degQ k ℓ * (S.card : ℚ) * (1 - Φ (Gr k ℓ) S hS - dens S) := by
  have hAf : ∀ L, adjOpLM (k := k) (ℓ := ℓ) (fun M => ind S M - dens S) L
      = adjOp (ind S) L - dens S * degQ k ℓ := by
    intro L
    have hf : (fun M => ind S M - dens S)
        = ind S - dens S • (fun _ : GrVertex k ℓ => (1 : ℚ)) := by
      funext M; simp
    rw [hf, adjOpLM_apply, adjOp_sub, adjOp_smul', adjOp_const' hℓ, degQ_eq_nat]
    ring
  rw [stdInner_apply]
  have hterm : ∀ L : GrVertex k ℓ,
      adjOpLM (k := k) (ℓ := ℓ) (fun M => ind S M - dens S) L * (ind S L - dens S)
        = (adjOp (ind S) L - dens S * degQ k ℓ) * (ind S L - dens S) := by
    intro L; rw [hAf L]
  rw [Finset.sum_congr rfl (fun L (_ : L ∈ Finset.univ) => hterm L)]
  have hterm2 : ∀ L : GrVertex k ℓ,
      (adjOp (ind S) L - dens S * degQ k ℓ) * (ind S L - dens S)
        = adjOp (ind S) L * ind S L - dens S * degQ k ℓ * ind S L
          - dens S * adjOp (ind S) L + dens S * degQ k ℓ * dens S := by
    intro L; ring
  rw [Finset.sum_congr rfl (fun L (_ : L ∈ Finset.univ) => hterm2 L)]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [sum_adjOp_mul_ind, ← Finset.mul_sum, sum_ind_eq', ← Finset.mul_sum,
    sum_adjOp_ind_univ' hℓ S, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← inner_self_identity hℓ S hS]
  rw [show (Fintype.card (GrVertex k ℓ) : ℚ) * (dens S * degQ k ℓ * dens S)
      = dens S * degQ k ℓ * (dens S * (Fintype.card (GrVertex k ℓ) : ℚ)) by ring,
    dens_mul_card S hS]
  ring

lemma sum_ind_mul_ind (S : Finset (GrVertex k ℓ)) :
    ∑ L, ind S L * ind S L = (S.card : ℚ) := by
  have h := stdInner_ind_self (k := k) (ℓ := ℓ) S
  rwa [stdInner_apply] at h

/-- **The centred indicator has the right norm**: `‖1_S - ρ‖² = #S (1 - ρ)`. -/
lemma stdInner_center_self (S : Finset (GrVertex k ℓ)) (hS : S.Nonempty) :
    stdInner k ℓ (fun L => ind S L - dens S) (fun L => ind S L - dens S)
      = (S.card : ℚ) * (1 - dens S) := by
  rw [stdInner_apply]
  have hterm : ∀ L : GrVertex k ℓ, (ind S L - dens S) * (ind S L - dens S)
      = ind S L * ind S L - (2 * dens S) * ind S L + dens S * dens S := by
    intro L; ring
  rw [Finset.sum_congr rfl (fun L (_ : L ∈ Finset.univ) => hterm L)]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [sum_ind_mul_ind, ← Finset.mul_sum, sum_ind_eq', Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]
  rw [show (Fintype.card (GrVertex k ℓ) : ℚ) * (dens S * dens S)
      = dens S * (dens S * (Fintype.card (GrVertex k ℓ) : ℚ)) by ring, dens_mul_card S hS]
  ring

/-- `0 ≤ degQ`. -/
lemma degQ_nonneg (hℓ : 1 ≤ ℓ) (S : Finset (GrVertex k ℓ)) (hS : S.Nonempty) :
    0 ≤ degQ k ℓ := by
  have hle : ℓ ≤ k := by
    have h1 : 0 < Fintype.card (GrVertex k ℓ) :=
      lt_of_lt_of_le (Finset.card_pos.mpr hS) (Finset.card_le_univ S)
    exact card_GrVertex_pos_iff_le.mp h1
  have h2 : (2 : ℚ) ≤ (2 : ℚ) ^ ℓ := by
    simpa using pow_le_pow_right₀ (by norm_num : (1 : ℚ) ≤ 2) hℓ
  have h3 : (2 : ℚ) ≤ (2 : ℚ) ^ (k - ℓ + 1) := by
    simpa using pow_le_pow_right₀ (by norm_num : (1 : ℚ) ≤ 2) (by omega : 1 ≤ k - ℓ + 1)
  rw [degQ]
  have h4 : (0 : ℚ) ≤ (2 : ℚ) ^ ℓ - 1 := by linarith
  have h5 : (0 : ℚ) ≤ (2 : ℚ) ^ (k - ℓ + 1) - 2 := by linarith
  exact mul_nonneg h4 h5

/-- **Second moment lower bound**: if `Φ(S) ≤ α` then `⟨A f, f⟩ ≥ d · #S · (1 - α - ρ)`
for `f = 1_S - ρ`. -/
lemma inner_adjOp_centered_ge (hℓ : 1 ≤ ℓ) (S : Finset (GrVertex k ℓ)) (hS : S.Nonempty)
    {α : ℚ} (hα : Φ (Gr k ℓ) S hS ≤ α) :
    degQ k ℓ * (S.card : ℚ) * (1 - α - dens S)
      ≤ stdInner k ℓ (adjOpLM (k := k) (ℓ := ℓ) (fun L => ind S L - dens S))
          (fun L => ind S L - dens S) := by
  rw [inner_adjOp_centered hℓ S hS]
  have hdeg : 0 ≤ degQ k ℓ * (S.card : ℚ) :=
    mul_nonneg (degQ_nonneg hℓ S hS) (Nat.cast_nonneg _)
  have hle : 1 - α - dens S ≤ 1 - Φ (Gr k ℓ) S hS - dens S := by linarith
  exact mul_le_mul_of_nonneg_left hle hdeg


end

end F2
end Submission.Grassmann
