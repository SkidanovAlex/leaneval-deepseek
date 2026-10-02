import Submission.Work.Deep.Nibble.sparseMatchingStatement_of_EGJStatement

/-!
# The interface of the family nibble, and `cor:sparse_egj` from it

`Work.Deep.Nibble.sparseMatchingStatement_of_EGJStatement` proves the cone's
`SparseMatchingStatement` (`cor:sparse_egj`) from `EGJStatement`, and in that proof the
*only* input taken from `EGJStatement` is a matching `M₀` covering all but a `3κ`-fraction
of every family member (the hypothesis `hlower` there).  This module isolates that input
as `RelCoverStatement` — exactly the output of the family nibble of this chapter
(`nibble_round2_fam_asm` + the iteration) — and reproves the corollary from it.

So the whole remaining mathematical obligation of `Deep/Nibble` is
`RelCoverStatement`; everything downstream of it is proved here.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.Deep.Nibble

open ErdosFaberLovaszConjecture

/-- **The output of the family nibble** (`cor:sparse_egj`'s "near-perfect" step): for every
`r`-uniform linear `n`-vertex hypergraph with degrees `(1 ± κ)D`, `D ≥ n^{1/100}`, and every
family `𝓕` of at most `n^{2 log n}` vertex sets, there is a matching covering all but a
`3κ`-fraction of every member of `𝓕` of size at least `D^{1/20}`. -/
def RelCoverStatement : Prop :=
  ∀ r : ℕ, 2 ≤ r → ∀ κ : ℝ, 0 < κ → κ < 1 / 4 →
    ∃ n₀ : ℝ, 0 < n₀ ∧ ∀ n : ℕ, n₀ ≤ (n : ℝ) → ∀ D : ℝ, (n : ℝ) ^ ((1 : ℝ) / 100) ≤ D →
      ∀ 𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n), 𝓗.IsLinear →
      (∀ e ∈ 𝓗, ErdosFaberLovaszConjecture.edgeSize e = r) →
      (∀ v : Fin n, |((ErdosFaberLovaszConjecture.hypergraphDegree 𝓗 v : ℝ)) - D|
        ≤ κ * D) →
      ∀ 𝓕 : Set (Set (Fin n)), (𝓕.ncard : ℝ) ≤ (n : ℝ) ^ (2 * Real.log n) →
        ∃ M₀ : Set 𝓗, ErdosFaberLovaszConjecture.IsMatching 𝓗 M₀ ∧
          ∀ S ∈ 𝓕, D ^ ((1 : ℝ) / 20) ≤ (S.ncard : ℝ) →
            (1 - 3 * κ) * (S.ncard : ℝ) ≤
              ((S ∩ ErdosFaberLovaszConjecture.matchVert M₀).ncard : ℝ)

/-- **`cor:sparse_egj` from the family nibble.**  The proof is that of
`sparseMatchingStatement_of_EGJStatement` with the `EGJStatement` call replaced by
`RelCoverStatement`: thin the near-perfect matching of `RelCoverStatement` with
`Work.Deep.Nibble.thinning`. -/
theorem sparseMatchingStatement_of_relCover (h : RelCoverStatement) :
    SparseMatchingStatement := by
  classical
  intro r hr κ γ hκ0 hκ1 hγ0 hγ1
  by_cases hκbig : (1 : ℝ) / 4 ≤ κ
  · refine ⟨1, one_pos, fun n hn D hD 𝓗 hlin hunif hdeg 𝓕 h𝓕 => ?_⟩
    refine ⟨∅, isMatching_empty 𝓗, fun S hS hbig => ?_⟩
    have h1 : (S \ matchVert (∅ : Set 𝓗)).ncard = S.ncard := by
      simp [matchVert]
    rw [h1]
    have hs : (0 : ℝ) ≤ (S.ncard : ℝ) := Nat.cast_nonneg _
    have hγ : (0 : ℝ) ≤ 1 - γ := by linarith
    rw [show ((S.ncard : ℝ) - γ * (S.ncard : ℝ)) = (1 - γ) * (S.ncard : ℝ) by ring]
    rw [abs_of_nonneg (mul_nonneg hγ hs)]
    nlinarith [hs, hκbig, hγ]
  · push Not at hκbig
    obtain ⟨n₀R, hn₀Rpos, hR⟩ := h r hr κ hκ0 hκbig
    obtain ⟨n₀, hn₀pos, hn₀⟩ := exists_threshold hr hκ0 hκbig (by norm_num : (0 : ℝ) < 1)
    refine ⟨max n₀R n₀, lt_max_of_lt_left hn₀Rpos,
      fun n hn D hD 𝓗 hlin hunif hdeg 𝓕 h𝓕 => ?_⟩
    have hnR : n₀R ≤ (n : ℝ) := le_trans (le_max_left _ _) hn
    have hnE : n₀ ≤ (n : ℝ) := le_trans (le_max_right _ _) hn
    obtain ⟨hD1, -, -, -, -, -, hc6⟩ := hn₀ n hnE D hD
    obtain ⟨M₀, hM₀match, hM₀cov⟩ := hR n hnR D hD 𝓗 hlin hunif hdeg 𝓕 h𝓕
    set 𝓕₀ : Set (Set (Fin n)) := {S | S ∈ 𝓕 ∧ D ^ ((1 : ℝ) / 20) ≤ (S.ncard : ℝ)} with h𝓕₀def
    have hlower : ∀ S ∈ 𝓕₀,
        (1 - 3 * κ) * (S.ncard : ℝ) ≤ ((S ∩ matchVert M₀).ncard : ℝ) :=
      fun S hS => hM₀cov S hS.1 hS.2
    have hcard𝓕₀le : (Fintype.card ↥𝓕₀ : ℝ) ≤ (n : ℝ) ^ (2 * Real.log n) := by
      have h1 : Fintype.card ↥𝓕₀ = 𝓕₀.ncard := by
        rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
      rw [h1]
      have hsub : 𝓕₀ ⊆ 𝓕 := fun S hS => hS.1
      have hmono : 𝓕₀.ncard ≤ 𝓕.ncard := Set.ncard_mono hsub
      exact le_trans (by exact_mod_cast hmono) h𝓕
    have hunion : 2 * (Fintype.card ↥𝓕₀ : ℝ) *
        Real.exp (-(3 / 8 * κ ^ 2 * D ^ ((1 : ℝ) / 20) / r)) < 1 := by
      have h2 : (Fintype.card ↥𝓕₀ : ℝ) * 2 ≤ (n : ℝ) ^ (2 * Real.log n) * 2 :=
        mul_le_mul_of_nonneg_right hcard𝓕₀le (by norm_num)
      have hE : (0 : ℝ) ≤ Real.exp (-(3 / 8 * κ ^ 2 * D ^ ((1 : ℝ) / 20) / r)) :=
        Real.exp_nonneg _
      have h3 : 2 * (Fintype.card ↥𝓕₀ : ℝ) *
          Real.exp (-(3 / 8 * κ ^ 2 * D ^ ((1 : ℝ) / 20) / r)) ≤
          2 * (n : ℝ) ^ (2 * Real.log n) *
            Real.exp (-(3 / 8 * κ ^ 2 * D ^ ((1 : ℝ) / 20) / r)) := by nlinarith
      exact lt_of_le_of_lt h3 hc6
    have hthin : ∃ M : Set 𝓗, M ⊆ M₀ ∧ IsMatching 𝓗 M ∧
        ∀ a : 𝓕₀, |((((a : Set (Fin n))) \ matchVert M).ncard : ℝ)
          - γ * (((a : Set (Fin n))).ncard : ℝ)| ≤
            4 * κ * (((a : Set (Fin n))).ncard : ℝ) := by
      exact thinning (n := n) (𝓗 := 𝓗) (M₀ := M₀) (σ := 𝓕₀)
        (S := fun a => (a : Set (Fin n))) (r := (r : ℝ))
        (hM₀ := hM₀match) (hκ0 := hκ0) (hκ := hκbig) (hγ0 := le_of_lt hγ0)
        (hγ1 := hγ1) (hr := by exact_mod_cast (show 0 < r by omega)) (hD1 := hD1)
        (hsize := fun e _ => by rw [hunif (e : Set (Fin n)) e.2])
        (hbig := fun a => a.2.2) (hlower := fun a => hlower a.1 a.2) (hunion := hunion)
    obtain ⟨M, _hMsub, hMmatch, hMprop⟩ := hthin
    exact ⟨M, hMmatch, fun S hS hbig => hMprop ⟨S, hS, hbig⟩⟩

end Work.Deep.Nibble
