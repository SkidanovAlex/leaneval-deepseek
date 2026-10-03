import Mathlib
import Submission.Work.FIArea1.QboxDefs

set_option maxHeartbeats 1000000

namespace Work.FIArea1

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- Summation over an image, with the multiplicity dropped: for `g ≥ 0` on `φ '' s`,
`∑_{y ∈ s.image φ} g y ≤ ∑_{x ∈ s} g (φ x)`. -/
lemma sum_image_le' {α β : Type*} [DecidableEq β] (s : Finset α) (φ : α → β) (g : β → ℝ)
    (h : ∀ x ∈ s, 0 ≤ g (φ x)) : ∑ y ∈ s.image φ, g y ≤ ∑ x ∈ s, g (φ x) := by
  rw [Finset.sum_comp (f := g) (g := φ)]
  refine Finset.sum_le_sum fun b hb => ?_
  rw [Finset.mem_image] at hb
  obtain ⟨a, ha, rfl⟩ := hb
  have h1 : 1 ≤ ({x ∈ s | φ x = φ a} : Finset α).card := by
    rw [Finset.one_le_card]
    exact ⟨a, by rw [Finset.mem_filter]; exact ⟨ha, rfl⟩⟩
  have h2 : 0 ≤ g (φ a) := h a ha
  have h3 : (1 : ℝ) ≤ (({x ∈ s | φ x = φ a} : Finset α).card : ℝ) := by
    exact_mod_cast h1
  calc g (φ a) = 1 * g (φ a) := (one_mul _).symm
    _ ≤ (({x ∈ s | φ x = φ a} : Finset α).card : ℝ) * g (φ a) :=
        mul_le_mul_of_nonneg_right h3 h2
    _ = ({x ∈ s | φ x = φ a} : Finset α).card • g (φ a) := by rw [nsmul_eq_mul]

/-- **Squares in an interval.**  A finite set `U` of integers whose squares all lie in a real
interval `[lo,hi]` has at most `2√(hi-lo)+2` elements: at most `√(hi-lo)+1` positive square
values fit into an interval of length `hi-lo` (the `k`-th smallest non-negative square is
`(k-1)²`), and each value has at most two roots. -/
lemma card_sq_interval_le {U : Finset ℤ} {lo hi : ℝ} (hlh : lo ≤ hi)
    (h : ∀ c ∈ U, lo ≤ (c : ℝ) ^ 2 ∧ (c : ℝ) ^ 2 ≤ hi) :
    (U.card : ℝ) ≤ 2 * Real.sqrt (hi - lo) + 2 := by
  classical
  set V : Finset ℕ := U.image (fun c : ℤ => c.natAbs) with hV
  have hcast : ∀ c : ℤ, (((c.natAbs : ℕ) : ℝ)) = |(c : ℝ)| := by
    intro c
    rw [Nat.cast_natAbs, Int.cast_abs]
  have hsq : ∀ v ∈ V, lo ≤ (v : ℝ) ^ 2 ∧ (v : ℝ) ^ 2 ≤ hi := by
    intro v hv
    rw [hV, Finset.mem_image] at hv
    obtain ⟨c, hc, rfl⟩ := hv
    rw [hcast c, sq_abs]
    exact h c hc
  have hVcard : ((V.card : ℕ) : ℝ) ≤ Real.sqrt (hi - lo) + 1 := by
    rcases V.eq_empty_or_nonempty with hE | hne
    · rw [hE]; simp only [Finset.card_empty, Nat.cast_zero]
      have : (0:ℝ) ≤ Real.sqrt (hi - lo) := Real.sqrt_nonneg _
      linarith
    · set a : ℕ := V.min' hne with hadef
      set b : ℕ := V.max' hne with hbdef
      have hmem_a : a ∈ V := hadef ▸ V.min'_mem hne
      have hmem_b : b ∈ V := hbdef ▸ V.max'_mem hne
      have ha := hsq a hmem_a
      have hb := hsq b hmem_b
      have hsub : V ⊆ Finset.Icc a b := by
        intro v hv
        refine Finset.mem_Icc.mpr ⟨?_, ?_⟩
        · rw [hadef]; exact V.min'_le v hv
        · rw [hbdef]; exact V.le_max' v hv
      have hcard : V.card ≤ b + 1 - a := by
        calc V.card ≤ (Finset.Icc a b).card := Finset.card_le_card hsub
          _ = b + 1 - a := Nat.card_Icc a b
      have hba : a ≤ b := by
        rw [hadef, hbdef]
        exact V.min'_le b hmem_b
      have hdiff : (((b - a : ℕ) : ℝ)) ^ 2 ≤ hi - lo := by
        have h1 : ((b : ℝ)) ^ 2 - ((a : ℝ)) ^ 2 ≤ hi - lo := by linarith [ha.1, hb.2]
        have hc2 : (((b - a : ℕ) : ℝ)) = (b : ℝ) - (a : ℝ) := Nat.cast_sub hba
        have h2 : (((b - a : ℕ) : ℝ)) ^ 2 ≤ ((b : ℝ)) ^ 2 - ((a : ℝ)) ^ 2 := by
          rw [hc2]
          have ha0 : (0:ℝ) ≤ (a:ℝ) := Nat.cast_nonneg a
          have hb0 : (0:ℝ) ≤ (b:ℝ) := Nat.cast_nonneg b
          have hba' : (a:ℝ) ≤ (b:ℝ) := by exact_mod_cast hba
          nlinarith
        linarith
      have hbda : (((b - a : ℕ) : ℝ)) ≤ Real.sqrt (hi - lo) := by
        have h0 : (0:ℝ) ≤ ((b - a : ℕ) : ℝ) := Nat.cast_nonneg _
        rw [← Real.sqrt_sq h0]
        exact Real.sqrt_le_sqrt hdiff
      have hcardR : ((V.card : ℕ) : ℝ) ≤ ((b + 1 - a : ℕ) : ℝ) := by exact_mod_cast hcard
      have hcast2 : (((b + 1 - a : ℕ) : ℝ)) = (((b - a : ℕ) : ℝ)) + 1 := by
        have h1 : b + 1 - a = (b - a) + 1 := by omega
        rw [h1]; push_cast; ring
      rw [hcast2] at hcardR
      linarith [hcardR, hbda]
  have hUcard : ((U.card : ℕ) : ℝ) ≤ 2 * ((V.card : ℕ) : ℝ) := by
    have hsplit : U.card
        = (U.filter (fun c : ℤ => 0 ≤ c)).card + (U.filter (fun c : ℤ => c < 0)).card := by
      rw [← Finset.card_filter_add_card_filter_not (s := U) (p := fun c : ℤ => 0 ≤ c)]
      congr 1
      rw [Finset.filter_congr (fun c (_ : c ∈ U) => not_le)]
    rw [hsplit]
    have h1 : (U.filter (fun c : ℤ => 0 ≤ c)).card ≤ V.card := by
      have hinj : Set.InjOn (fun c : ℤ => c.natAbs)
          (↑(U.filter (fun c : ℤ => 0 ≤ c)) : Set ℤ) := by
        intro p hp q hq hpq
        simp only [Finset.mem_coe, Finset.mem_filter] at hp hq
        have hpq' : p.natAbs = q.natAbs := hpq
        rw [← Int.natAbs_of_nonneg hp.2, ← Int.natAbs_of_nonneg hq.2, hpq']
      calc (U.filter (fun c : ℤ => 0 ≤ c)).card
          = ((U.filter (fun c : ℤ => 0 ≤ c)).image (fun c : ℤ => c.natAbs)).card :=
            (Finset.card_image_of_injOn hinj).symm
        _ ≤ V.card := by
            rw [hV]
            exact Finset.card_le_card (Finset.image_subset_image (Finset.filter_subset _ _))
    have h2 : (U.filter (fun c : ℤ => c < 0)).card ≤ V.card := by
      have hinj : Set.InjOn (fun c : ℤ => c.natAbs)
          (↑(U.filter (fun c : ℤ => c < 0)) : Set ℤ) := by
        intro p hp q hq hpq
        simp only [Finset.mem_coe, Finset.mem_filter] at hp hq
        have hp' : ((p.natAbs : ℕ) : ℤ) = -p := by
          rw [Int.natCast_natAbs, abs_of_neg hp.2]
        have hq' : ((q.natAbs : ℕ) : ℤ) = -q := by
          rw [Int.natCast_natAbs, abs_of_neg hq.2]
        have hpq' : p.natAbs = q.natAbs := hpq
        have hthis : ((p.natAbs : ℕ) : ℤ) = ((q.natAbs : ℕ) : ℤ) := by rw [hpq']
        linarith [hp', hq', hthis]
      calc (U.filter (fun c : ℤ => c < 0)).card
          = ((U.filter (fun c : ℤ => c < 0)).image (fun c : ℤ => c.natAbs)).card :=
            (Finset.card_image_of_injOn hinj).symm
        _ ≤ V.card := by
            rw [hV]
            exact Finset.card_le_card (Finset.image_subset_image (Finset.filter_subset _ _))
    have h4 : (U.filter (fun c : ℤ => 0 ≤ c)).card + (U.filter (fun c : ℤ => c < 0)).card
        ≤ V.card + V.card := Nat.add_le_add h1 h2
    have h3 : ((U.filter (fun c : ℤ => 0 ≤ c)).card : ℝ)
        + ((U.filter (fun c : ℤ => c < 0)).card : ℝ) ≤ 2 * ((V.card : ℕ) : ℝ) := by
      have h4R : (((U.filter (fun c : ℤ => 0 ≤ c)).card
            + (U.filter (fun c : ℤ => c < 0)).card : ℕ) : ℝ)
          ≤ ((V.card + V.card : ℕ) : ℝ) := by exact_mod_cast h4
      push_cast at h4R
      linarith [h4R]
    push_cast
    exact h3
  have hmain : ((U.card : ℕ) : ℝ) ≤ 2 * (Real.sqrt (hi - lo) + 1) := by
    have h2 : (0:ℝ) ≤ ((V.card : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith [hUcard, hVcard]
  linarith [hmain]

end

end Work.FIArea1
