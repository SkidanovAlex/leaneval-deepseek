import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Kahn.roundUncolExc
import Submission.Work.Deep.Kahn.roundUncolCert
import Submission.Work.Deep.Kahn.roundUncolNum
import Submission.Work.Deep.Kahn.colourNeighbours_card
import Submission.Work.Deep.Conc.BruhnJoos.bruhn_joos_talagrand

/-!
# `Work.Deep.Kahn.roundUncolAct`

The concentration of the *activated but blocked* colour-degree count `uncolActCount ω x γ`
(the paper's `uncolActivatedNbrsRV`; Kang--Kelly--Kühn--Methuku--Osthus, arXiv:2109.11438,
Lemma `lemma:concentrations`), in the form consumed by the one-round nibble:

  `prob (badUncolSet C D Λ η x γ) ≤ exp (-D^{1/4}) / 2`.

The three ingredients are the first-moment bound `roundUncolMean`, the certificate condition
`uncolAct_cert` and the probability of the exceptional set `roundUncolExc` (with `ℓ = ⌈D^{1/4}⌉`),
combined by the Bruhn--Joos concentration inequality `BruhnJoos.bruhn_joos_talagrand` applied to
the statistic `D - uncolActCount`, whose *increase* is bounded off the exceptional set.  The
numeric side conditions are `num_eta` and `num_exc`.
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

open Work.Deep.Kahn.Round

/-- The number of `γ`-edges through `x` is `D`. -/
lemma colThru_card {n c D : ℕ} {𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)} [Fintype 𝓗]
    {L : 𝓗 → Finset (Fin c)}
    (hdeg : ∀ y : Fin n, ∀ δ : Fin c,
      (∃ e : 𝓗, y ∈ (e : Set (Fin n)) ∧ δ ∈ L e) →
      Nat.card {e : 𝓗 // y ∈ (e : Set (Fin n)) ∧ δ ∈ L e} = D)
    {x : Fin n} {γ : Fin c} (hxγ : ∃ e : 𝓗, x ∈ (e : Set (Fin n)) ∧ γ ∈ L e) :
    (colThru (L := L) x γ).card = D := by
  classical
  rw [← hdeg x γ hxγ, Nat.card_eq_fintype_card, Fintype.card_subtype]
  rfl

/-- The blocker count of `blkOf` is `C (D-1)`. -/
lemma blkOf_card_le {n c C D : ℕ}
    {𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)} [Fintype 𝓗]
    {L : 𝓗 → Finset (Fin c)}
    (hlin : 𝓗.IsLinear)
    (hsize : ∀ e : 𝓗, ErdosFaberLovaszConjecture.edgeSize (e : Set (Fin n)) = C)
    (hdeg : ∀ y : Fin n, ∀ δ : Fin c,
      (∃ e : 𝓗, y ∈ (e : Set (Fin n)) ∧ δ ∈ L e) →
      Nat.card {e : 𝓗 // y ∈ (e : Set (Fin n)) ∧ δ ∈ L e} = D)
    (e : 𝓗) (δ : Fin c) (hδ : δ ∈ L e) :
    (blkOf (L := L) e δ).card ≤ C * (D - 1) := by
  classical
  have h1 := Work.Deep.Kahn.colourNeighbours_card 𝓗 L hlin hsize hdeg e δ hδ
  rw [← h1]
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rfl

/-- The maximum of the blocker multiplicity off the exceptional set. -/
lemma uncolActCount_le_colThru {n c K : ℕ}
    {𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)} [Fintype 𝓗] [NeZero K]
    {L : 𝓗 → Finset (Fin c)} (ω : Space K 𝓗 L) (x : Fin n) (γ : Fin c) :
    uncolActCount (K := K) (L := L) ω x γ ≤ (colThru (L := L) x γ).card := by
  classical
  rw [← uncolActSet_card (K := K) (L := L) ω x γ]
  exact Finset.card_le_card (uncolActSet_subset_colThru ω x γ)

theorem roundUncolAct {C : ℕ} (hC : 2 ≤ C) (ε η : ℝ) (hε : 0 < ε) (hη : 0 < η) :
    ∃ Dmin : ℝ, 0 < Dmin ∧
    Dmin ≤ ((C : ℝ) + η⁻¹ + ε⁻¹ + 1) ^ (1000 : ℕ) + 10 ^ (1000 : ℕ) ∧
    ∀ (n c : ℕ)
      (𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)) [Fintype 𝓗]
      (L : 𝓗 → Finset (Fin c)) (D Λ K : ℕ) [NeZero K],
      1 ≤ D → 1 ≤ Λ → 2 ≤ K → η * (K : ℝ) ≤ 1 →
      (16 : ℝ) * (C : ℝ) ≤ (1 + ε) * (K : ℝ) →
      𝓗.IsLinear →
      (∀ e : 𝓗, ErdosFaberLovaszConjecture.edgeSize (e : Set (Fin n)) = C) →
      (∀ e : 𝓗, (L e).card = Λ) →
      (∀ x : Fin n, ∀ γ : Fin c, (∃ e : 𝓗, x ∈ (e : Set (Fin n)) ∧ γ ∈ L e) →
        Nat.card {e : 𝓗 // x ∈ (e : Set (Fin n)) ∧ γ ∈ L e} = D) →
      (1 + ε) * (D : ℝ) ≤ (Λ : ℝ) → (Λ : ℝ) ≤ 10 * (C : ℝ) * (D : ℝ) →
      Dmin ≤ (D : ℝ) →
      Real.log (D : ℝ) ≤ (K : ℝ) → (K : ℝ) ≤ (Real.log (D : ℝ)) ^ 2 →
      ((C : ℝ) + (K : ℝ) + η⁻¹) ≤ (D : ℝ) ^ ((1 : ℝ) / 9) →
      ∀ x : Fin n, ∀ γ : Fin c, (∃ e : 𝓗, x ∈ (e : Set (Fin n)) ∧ γ ∈ L e) →
        Work.Deep.Conc.prob (Work.Deep.Kahn.Round.badUncolSet (K := K) (L := L) C D Λ η x γ)
          ≤ Real.exp (-(D : ℝ) ^ ((1 : ℝ) / 4)) / 2 := by
  refine ⟨(10 : ℝ) ^ 1000, by positivity, ?_, ?_⟩
  · exact le_add_of_nonneg_left (by positivity :
      (0 : ℝ) ≤ ((C : ℝ) + η⁻¹ + ε⁻¹ + 1) ^ (1000 : ℕ))
  · intro n c 𝓗 _instF L D Λ K _instK hD1 hΛ1 hK2 hηK h16C hlin hsize hlist hdeg hDΛ hΛD
      hDmin hlogK hKlog hCKη x γ hxγ
    classical
    have hDpos : (0 : ℝ) < (D : ℝ) :=
      lt_of_lt_of_le (by positivity : (0 : ℝ) < (10 : ℝ) ^ 1000) hDmin
    have hD1' : (1 : ℝ) ≤ (D : ℝ) :=
      le_trans (one_le_pow₀ (a := (10 : ℝ)) (by norm_num) (n := 1000)) hDmin
    have hKpos : (0 : ℝ) < (K : ℝ) := by
      have : 0 < K := Nat.pos_of_ne_zero (NeZero.ne K)
      exact_mod_cast this
    have hne : ∀ e : 𝓗, Nonempty (Coord K 𝓗 L e) :=
      fun e => ⟨(0, ⟨0, by rw [hlist e]; omega⟩)⟩
    haveI : Nonempty (Space K 𝓗 L) := ⟨fun i => Classical.choice (hne i)⟩
    -- the threshold parameters
    set ℓ : ℕ := ⌈(D : ℝ) ^ ((1 : ℝ) / 4)⌉₊ with hℓdef
    have hℓ : (D : ℝ) ^ ((1 : ℝ) / 4) ≤ (ℓ : ℝ) := Nat.le_ceil _
    have hℓu : (ℓ : ℝ) ≤ (D : ℝ) ^ ((1 : ℝ) / 4) + 1 := by
      rw [hℓdef]
      exact le_of_lt (Nat.ceil_lt_add_one (by positivity))
    set cst : ℝ := (C : ℝ) + (ℓ : ℝ) + 2 with hcstdef
    have hcst1 : (1 : ℝ) ≤ cst := by
      rw [hcstdef]
      have h2 : (0 : ℝ) ≤ (C : ℝ) + (ℓ : ℝ) := by positivity
      calc (1 : ℝ) = 1 + 0 := by ring
        _ ≤ 1 + ((C : ℝ) + (ℓ : ℝ)) := add_le_add le_rfl h2
        _ = ((C : ℝ) + (ℓ : ℝ)) + 1 := by ring
        _ ≤ ((C : ℝ) + (ℓ : ℝ)) + 2 := add_le_add le_rfl (by norm_num)
    -- `C ≤ D^{1/9}` and `cst ≤ 3 D^{1/4}`
    have hCD : (C : ℝ) ≤ (D : ℝ) ^ ((1 : ℝ) / 9) := by
      have h1 : (C : ℝ) ≤ (C : ℝ) + (K : ℝ) := le_add_of_nonneg_right hKpos.le
      have h2 : (C : ℝ) + (K : ℝ) ≤ (C : ℝ) + (K : ℝ) + η⁻¹ :=
        le_add_of_nonneg_right (by positivity : (0 : ℝ) ≤ η⁻¹)
      exact le_trans (le_trans h1 h2) hCKη
    have hD14ge : (3 : ℝ) ≤ (D : ℝ) ^ ((1 : ℝ) / 4) := by
      refine rpow_ge_of_ten (c := (1 : ℝ) / 4) (by norm_num) hDmin ?_
      have h2 : 1000 * ((1 : ℝ) / 4) = (250 : ℝ) := by norm_num
      rw [h2]
      refine le_trans (by norm_num : (3 : ℝ) ≤ 10) ?_
      have h5 : (10 : ℝ) ^ (1 : ℝ) ≤ (10 : ℝ) ^ (250 : ℝ) :=
        (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 10)).mpr (by norm_num)
      rwa [Real.rpow_one] at h5
    have hcu : cst ≤ 3 * (D : ℝ) ^ ((1 : ℝ) / 4) := by
      have hDgt : (1 : ℝ) < (D : ℝ) :=
        lt_of_lt_of_le (by norm_num : (1 : ℝ) < 10)
          (le_trans (le_self_pow₀ (a := (10 : ℝ)) (by norm_num) (n := 1000) (by norm_num)) hDmin)
      have h1 : (D : ℝ) ^ ((1 : ℝ) / 9) ≤ (D : ℝ) ^ ((1 : ℝ) / 4) :=
        (Real.rpow_le_rpow_left_iff hDgt).mpr (by norm_num)
      have h2 : (C : ℝ) + (ℓ : ℝ) + 2
          ≤ ((D : ℝ) ^ ((1 : ℝ) / 4) + ((D : ℝ) ^ ((1 : ℝ) / 4) + 1)) + 2 :=
        add_le_add (add_le_add (le_trans hCD h1) hℓu) le_rfl
      rw [hcstdef]
      refine le_trans h2 ?_
      calc ((D : ℝ) ^ ((1 : ℝ) / 4) + ((D : ℝ) ^ ((1 : ℝ) / 4) + 1)) + 2
          = 2 * (D : ℝ) ^ ((1 : ℝ) / 4) + 3 := by ring
        _ ≤ 2 * (D : ℝ) ^ ((1 : ℝ) / 4) + (D : ℝ) ^ ((1 : ℝ) / 4) :=
            add_le_add le_rfl hD14ge
        _ = 3 * (D : ℝ) ^ ((1 : ℝ) / 4) := by ring
    -- the numeric inputs
    obtain ⟨ht, hexp_le⟩ := num_eta (C := C) (D := D) (K := K) (ℓ := ℓ) (η := η)
      hC hη hK2 hηK hDmin hlogK hKlog hCKη hcu hℓ
    have hcol : (colThru (L := L) x γ).card = D := colThru_card (L := L) hdeg hxγ
    set Ω : Set (Space K 𝓗 L) := excSet (K := K) (L := L) x γ ℓ with hΩdef
    have hExc : Work.Deep.Conc.prob Ω ≤ (D : ℝ) * (Λ : ℝ) * ((1 / 32 : ℝ) ^ ℓ) :=
      roundUncolExc (K := K) (L := L) hC hlist hdeg h16C hDΛ x γ hxγ ℓ
    obtain ⟨hnExc, hnExc2⟩ := num_exc (C := C) (D := D) (Λ := Λ) (ℓ := ℓ) hC hΛ1 hΛD hDmin hCD hℓ
    have hExc2 : Work.Deep.Conc.prob Ω ≤ Real.exp (-((D : ℝ) ^ ((1 : ℝ) / 4))) / 16 :=
      le_trans hExc hnExc
    have hexc : Work.Deep.Conc.prob Ω ≤ 1 / (D : ℝ) ^ 2 := le_trans hExc2 hnExc2
    clear hDmin
    -- the certificate
    have hcert : ∀ (u : ℝ), 0 < u → ∀ ω : Space K 𝓗 L, ω ∉ Ω →
        ∃ I : Finset 𝓗, I.card ≤ 4 * D ∧
          ∀ ω' : Space K 𝓗 L, ω' ∉ Ω →
            ((I.filter (fun i : 𝓗 => ω i ≠ ω' i)).card : ℝ) < u / cst →
              ((D : ℝ) - (uncolActCount (K := K) (L := L) ω' x γ : ℝ))
                < ((D : ℝ) - (uncolActCount (K := K) (L := L) ω x γ : ℝ)) + u := by
      intro u hu ω hω
      obtain ⟨I, hIcard, hI⟩ := uncolAct_cert (K := K) (L := L) hlin hsize ℓ x γ u hu ω hω
      refine ⟨I, ?_, ?_⟩
      · have h2 : I.card ≤ 2 * D := by
          rw [hcol] at hIcard
          omega
        omega
      · intro ω' hω' hdis
        have h1 := hI ω' hω' hdis
        linarith
    -- the mean bound
    have hblk : ∀ e ∈ colThru (L := L) x γ, ∀ δ ∈ L e,
        (blkOf (L := L) e δ).card ≤ C * (D - 1) :=
      fun e _ δ hδ => blkOf_card_le (L := L) hlin hsize hdeg e δ hδ
    have hmeanX : Work.Deep.Conc.expect
        (fun ω : Space K 𝓗 L => (uncolActCount (K := K) (L := L) ω x γ : ℝ))
        ≤ (1 / (K : ℝ)) * (1 - retention Λ C D K) * (D : ℝ) :=
      roundUncolMean (K := K) (L := L) (x := x) (γ := γ) hΛ1 (by omega) hlist hblk
        (le_of_eq hcol)
    -- the Bruhn--Joos input
    have hM1 : (1 : ℝ) ≤ (D : ℝ) := hD1'
    have hsup : ∀ ω : Space K 𝓗 L,
        |(D : ℝ) - (uncolActCount (K := K) (L := L) ω x γ : ℝ)| ≤ (D : ℝ) := by
      intro ω
      have h1 := uncolActCount_le_colThru (K := K) (L := L) ω x γ
      have h3 : (uncolActCount (K := K) (L := L) ω x γ : ℝ) ≤ (D : ℝ) := by
        rw [← hcol]
        exact_mod_cast h1
      have h4 : (0 : ℝ) ≤ (uncolActCount (K := K) (L := L) ω x γ : ℝ) := by positivity
      rw [abs_le]
      constructor <;> linarith
    have ht' : 50 * cst * Real.sqrt ((4 * D : ℕ) : ℝ) < η * (D : ℝ) / 4 := by
      have h1 : ((4 * D : ℕ) : ℝ) = 4 * (D : ℝ) := by push_cast; ring
      rw [h1, hcstdef]
      exact ht
    have hbj := Work.Deep.Conc.BruhnJoos.bruhn_joos_talagrand (ι := 𝓗)
      (π := fun e : 𝓗 => Coord K 𝓗 L e) hne
      (fun ω : Space K 𝓗 L => (D : ℝ) - (uncolActCount (K := K) (L := L) ω x γ : ℝ))
      (D : ℝ) hM1 hsup cst hcst1 (4 * D) (by omega) Ω hexc hcert (η * (D : ℝ) / 4) ht'
    -- the mean bound in terms of the statistic
    have hEX : Work.Deep.Conc.expect
        (fun ω : Space K 𝓗 L => (D : ℝ) - (uncolActCount (K := K) (L := L) ω x γ : ℝ))
        = (D : ℝ) - Work.Deep.Conc.expect
          (fun ω : Space K 𝓗 L => (uncolActCount (K := K) (L := L) ω x γ : ℝ)) := by
      have h1 : (fun ω : Space K 𝓗 L => (D : ℝ) - (uncolActCount (K := K) (L := L) ω x γ : ℝ))
          = (fun _ : Space K 𝓗 L => (D : ℝ))
            - (fun ω : Space K 𝓗 L => (uncolActCount (K := K) (L := L) ω x γ : ℝ)) := rfl
      rw [h1, Work.Deep.Conc.expect_sub, Work.Deep.Conc.expect_const]
    have hmono : Work.Deep.Kahn.Round.badUncolSet (K := K) (L := L) C D Λ η x γ
        ⊆ {ω : Space K 𝓗 L |
            η * (D : ℝ) / 4 ≤ |((D : ℝ) - (uncolActCount (K := K) (L := L) ω x γ : ℝ))
              - Work.Deep.Conc.expect
                (fun ω : Space K 𝓗 L =>
                  (D : ℝ) - (uncolActCount (K := K) (L := L) ω x γ : ℝ))|} := by
      intro ω hω
      rw [badUncolSet, Set.mem_ofPred_eq] at hω
      have h1 : (1 / (K : ℝ)) * (1 - retention Λ C D K) * (D : ℝ) + η * (D : ℝ) / 4
          < (uncolActCount (K := K) (L := L) ω x γ : ℝ) := hω
      have h2 : Work.Deep.Conc.expect
          (fun ω : Space K 𝓗 L => (uncolActCount (K := K) (L := L) ω x γ : ℝ))
          ≤ (1 / (K : ℝ)) * (1 - retention Λ C D K) * (D : ℝ) := hmeanX
      have h3 : η * (D : ℝ) / 4
          ≤ (uncolActCount (K := K) (L := L) ω x γ : ℝ)
            - Work.Deep.Conc.expect
              (fun ω : Space K 𝓗 L => (uncolActCount (K := K) (L := L) ω x γ : ℝ)) := by
        linarith
      have h4 : ((D : ℝ) - (uncolActCount (K := K) (L := L) ω x γ : ℝ))
            - Work.Deep.Conc.expect
              (fun ω : Space K 𝓗 L =>
                (D : ℝ) - (uncolActCount (K := K) (L := L) ω x γ : ℝ))
          = Work.Deep.Conc.expect
              (fun ω : Space K 𝓗 L => (uncolActCount (K := K) (L := L) ω x γ : ℝ))
            - (uncolActCount (K := K) (L := L) ω x γ : ℝ) := by
        rw [hEX]
        ring
      rw [Set.mem_ofPred_eq, h4, abs_sub_comm]
      exact le_trans h3 (le_abs_self _)
    -- the exponent comparison
    have hexp : 4 * Real.exp (-(η * (D : ℝ) / 4) ^ 2
          / (16 * ((C : ℝ) + (ℓ : ℝ) + 2) ^ 2 * (4 * (D : ℝ))))
        + 4 * Work.Deep.Conc.prob Ω
        ≤ Real.exp (-((D : ℝ) ^ ((1 : ℝ) / 4))) / 2 := by
      have hden : (0 : ℝ) < 16 * ((C : ℝ) + (ℓ : ℝ) + 2) ^ 2 * (4 * (D : ℝ)) := by positivity
      have h1 : Real.exp (-(η * (D : ℝ) / 4) ^ 2
            / (16 * ((C : ℝ) + (ℓ : ℝ) + 2) ^ 2 * (4 * (D : ℝ))))
          ≤ Real.exp (-((D : ℝ) ^ ((1 : ℝ) / 4))) / 16 := by
        have harg : -(η * (D : ℝ) / 4) ^ 2
              / (16 * ((C : ℝ) + (ℓ : ℝ) + 2) ^ 2 * (4 * (D : ℝ)))
            ≤ -((D : ℝ) ^ ((1 : ℝ) / 4) + Real.log 16) := by
          have h2 : (D : ℝ) ^ ((1 : ℝ) / 4) + Real.log 16
              ≤ (η * (D : ℝ) / 4) ^ 2
                / (16 * ((C : ℝ) + (ℓ : ℝ) + 2) ^ 2 * (4 * (D : ℝ))) := hexp_le
          calc -(η * (D : ℝ) / 4) ^ 2
                / (16 * ((C : ℝ) + (ℓ : ℝ) + 2) ^ 2 * (4 * (D : ℝ)))
              = -((η * (D : ℝ) / 4) ^ 2
                  / (16 * ((C : ℝ) + (ℓ : ℝ) + 2) ^ 2 * (4 * (D : ℝ)))) := by
                rw [neg_div]
            _ ≤ -((D : ℝ) ^ ((1 : ℝ) / 4) + Real.log 16) := neg_le_neg h2
        refine le_trans (Real.exp_le_exp.mpr harg) (le_of_eq ?_)
        rw [neg_add_rev, Real.exp_add, Real.exp_neg,
          Real.exp_log (by norm_num : (0 : ℝ) < 16)]
        ring
      have h2 : 4 * Work.Deep.Conc.prob Ω
          ≤ Real.exp (-((D : ℝ) ^ ((1 : ℝ) / 4))) / 4 := by
        have h3 : 4 * Work.Deep.Conc.prob Ω
            ≤ 4 * (Real.exp (-((D : ℝ) ^ ((1 : ℝ) / 4))) / 16) :=
          mul_le_mul_of_nonneg_left hExc2 (by norm_num)
        linarith
      have h4 : 4 * Real.exp (-(η * (D : ℝ) / 4) ^ 2
            / (16 * ((C : ℝ) + (ℓ : ℝ) + 2) ^ 2 * (4 * (D : ℝ))))
          ≤ Real.exp (-((D : ℝ) ^ ((1 : ℝ) / 4))) / 4 := by
        have h5 : 4 * Real.exp (-(η * (D : ℝ) / 4) ^ 2
              / (16 * ((C : ℝ) + (ℓ : ℝ) + 2) ^ 2 * (4 * (D : ℝ))))
            ≤ 4 * (Real.exp (-((D : ℝ) ^ ((1 : ℝ) / 4))) / 16) :=
          mul_le_mul_of_nonneg_left h1 (by norm_num)
        linarith
      linarith
    calc Work.Deep.Conc.prob (Work.Deep.Kahn.Round.badUncolSet (K := K) (L := L) C D Λ η x γ)
        ≤ Work.Deep.Conc.prob {ω : Space K 𝓗 L |
            η * (D : ℝ) / 4 ≤ |((D : ℝ) - (uncolActCount (K := K) (L := L) ω x γ : ℝ))
              - Work.Deep.Conc.expect
                (fun ω : Space K 𝓗 L =>
                  (D : ℝ) - (uncolActCount (K := K) (L := L) ω x γ : ℝ))|} :=
          Work.Deep.Conc.prob_mono hmono
      _ ≤ 4 * Real.exp (-(η * (D : ℝ) / 4) ^ 2 / (16 * cst ^ 2 * ((4 * D : ℕ) : ℝ)))
            + 4 * Work.Deep.Conc.prob Ω := hbj
      _ ≤ Real.exp (-((D : ℝ) ^ ((1 : ℝ) / 4))) / 2 := by
          have h1 : ((4 * D : ℕ) : ℝ) = 4 * (D : ℝ) := by push_cast; ring
          have h2 : cst = (C : ℝ) + (ℓ : ℝ) + 2 := hcstdef
          rw [h1, h2]
          exact hexp

end

end Work.Deep.Kahn
