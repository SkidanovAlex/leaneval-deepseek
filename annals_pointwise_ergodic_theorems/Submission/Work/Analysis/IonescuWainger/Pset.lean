/-
Copyright (c) 2026 The AnnalsChallenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AnnalsChallenge team
-/
import Submission.Work.Analysis.IonescuWainger.Basic

/-!
# Elementary structure of the Ionescu–Wainger denominator sets

Basic membership and positivity facts for the sets `W_{≤l}`, `P_{≤l}` and `(ℚ/ℤ)_{≤l}` of
Appendix A of Krause–Mirek–Tao.  The deeper arithmetic (the inclusion `[2^l] ⊆ P_{≤l}`,
monotonicity of `P_{≤l}`, the element/cardinality bounds and the separation of `(ℚ/ℤ)_{≤l}`)
is proved in the sibling modules `PsetContains`, `PsetMono`, `PsetElementLe`,
`ArithFreqsCard` and `ArithFreqsSeparated`.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Analysis.IonescuWainger

/-- The product `∏_{p ∈ (N_0^{(l)}, 2^l], p prime} p^{D_ρ}`. -/
noncomputable def iwProd (ρ : ℝ) (l : ℕ) : ℕ := ∏ p ∈ iwPrimeRange ρ l, p ^ iwD ρ

theorem iwProd_ne_zero (ρ : ℝ) (l : ℕ) : iwProd ρ l ≠ 0 := by
  rw [iwProd, Finset.prod_ne_zero_iff]
  intro p hp
  exact pow_ne_zero _ (Nat.Prime.ne_zero ((Finset.mem_filter.mp hp).2))

theorem iwQ0_ne_zero (ρ : ℝ) (l : ℕ) : iwQ0 ρ l ≠ 0 :=
  pow_ne_zero _ (Nat.factorial_ne_zero _)

theorem iwW_eq (ρ : ℝ) (l : ℕ) : iwW ρ l =
    (Nat.divisors (iwProd ρ l)).filter (fun w => w.factorization.support.card ≤ iwD ρ) := rfl

theorem mem_iwW {ρ : ℝ} {l w : ℕ} :
    w ∈ iwW ρ l ↔ w ∣ iwProd ρ l ∧ w.factorization.support.card ≤ iwD ρ := by
  rw [iwW_eq, Finset.mem_filter, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨hdvd, _⟩, hc⟩; exact ⟨hdvd, hc⟩
  · rintro ⟨hdvd, hc⟩; exact ⟨⟨hdvd, iwProd_ne_zero ρ l⟩, hc⟩

theorem one_mem_iwW (ρ : ℝ) (l : ℕ) : 1 ∈ iwW ρ l := by
  rw [mem_iwW]
  refine ⟨one_dvd _, ?_⟩
  simp

theorem pos_of_mem_iwW {ρ : ℝ} {l w : ℕ} (h : w ∈ iwW ρ l) : 0 < w :=
  Nat.pos_of_dvd_of_pos (mem_iwW.mp h).1 (Nat.pos_of_ne_zero (iwProd_ne_zero ρ l))

theorem mem_iwPconcrete {ρ : ℝ} {l q : ℕ} :
    q ∈ iwPconcrete ρ l ↔ ∃ Q ∈ (iwQ0 ρ l).divisors, ∃ w ∈ iwW ρ l, q = Q * w := by
  simp only [iwPconcrete, Finset.mem_biUnion, Finset.mem_image]
  exact ⟨fun ⟨Q, hQ, w, hw, h⟩ => ⟨Q, hQ, w, hw, h.symm⟩,
         fun ⟨Q, hQ, w, hw, h⟩ => ⟨Q, hQ, w, hw, h.symm⟩⟩

theorem mem_iwP {ρ : ℝ} {l q : ℕ} :
    q ∈ iwP ρ l ↔ (l ≤ iwC0 ρ ∧ 1 ≤ q ∧ q ≤ 2 ^ l) ∨ (iwC0 ρ < l ∧ q ∈ iwPconcrete ρ l) := by
  unfold iwP
  split_ifs with h
  · rw [Finset.mem_Icc]
    constructor
    · exact fun hq => Or.inl ⟨h, hq.1, hq.2⟩
    · rintro (⟨-, h1, h2⟩ | ⟨hlt, -⟩)
      · exact ⟨h1, h2⟩
      · exact absurd h (not_le_of_gt hlt)
  · constructor
    · exact fun hq => Or.inr ⟨not_le.mp h, hq⟩
    · rintro (⟨hle, -⟩ | ⟨hlt, hq⟩)
      · exact absurd hle (not_le_of_gt (not_le.mp h))
      · exact hq

theorem one_mem_iwP (ρ : ℝ) (l : ℕ) : 1 ∈ iwP ρ l := by
  rw [mem_iwP]
  by_cases h : l ≤ iwC0 ρ
  · exact Or.inl ⟨h, le_refl 1, Nat.one_le_two_pow⟩
  · refine Or.inr ⟨not_le.mp h, ?_⟩
    rw [mem_iwPconcrete]
    exact ⟨1, Nat.mem_divisors.mpr ⟨one_dvd _, iwQ0_ne_zero ρ l⟩, 1, one_mem_iwW ρ l, (one_mul 1).symm⟩

theorem pos_of_mem_iwP {ρ : ℝ} {l q : ℕ} (h : q ∈ iwP ρ l) : 0 < q := by
  rw [mem_iwP] at h
  rcases h with ⟨-, h1, -⟩ | ⟨-, hq⟩
  · exact h1
  · rw [mem_iwPconcrete] at hq
    obtain ⟨Q, hQ, w, hw, rfl⟩ := hq
    exact Nat.mul_pos (Nat.pos_of_mem_divisors hQ) (pos_of_mem_iwW hw)

theorem ne_zero_of_mem_iwP {ρ : ℝ} {l q : ℕ} (h : q ∈ iwP ρ l) : q ≠ 0 :=
  (pos_of_mem_iwP h).ne'

/-- An integer, viewed in `ℝ/ℤ`, is zero. -/
theorem coe_natCast_eq_zero (a : ℕ) : ((a : ℝ) : Circle) = 0 := by
  rw [AddCircle.coe_eq_zero_iff]
  exact ⟨(a : ℤ), by simp⟩

/-- The arithmetic frequency `a/q` is killed by multiplication by `q`. -/
theorem nsmul_div_eq_zero {q a : ℕ} (hq : 0 < q) :
    q • (((a : ℝ) / (q : ℝ)) : Circle) = 0 := by
  rw [← AddCircle.coe_nsmul]
  have h : (q : ℕ) • ((a : ℝ) / (q : ℝ)) = (a : ℝ) := by
    rw [nsmul_eq_mul]
    field_simp
  rw [h, coe_natCast_eq_zero]

/-- Every element of `ℝ/ℤ` of order dividing `q > 0` is of the form `a/q`, `0 ≤ a < q`. -/
theorem eq_div_of_nsmul_eq_zero {q : ℕ} (hq : 0 < q) {α : Circle} (h : q • α = 0) :
    ∃ a ∈ Finset.range q, ((a : ℝ) / (q : ℝ) : Circle) = α := by
  have ho : addOrderOf α ∣ q := addOrderOf_dvd_iff_nsmul_eq_zero.mpr h
  have ho0 : 0 < addOrderOf α := Nat.pos_of_dvd_of_pos ho hq
  have hfin : IsOfFinAddOrder α := addOrderOf_pos_iff.mp ho0
  obtain ⟨m, -, hm, hcoe⟩ := AddCircle.exists_gcd_eq_one_of_isOfFinAddOrder
    (𝕜 := ℝ) (p := (1 : ℝ)) hfin
  -- `hcoe : ↑(↑m / ↑(addOrderOf α) * 1) = α`
  set o := addOrderOf α with ho_def
  have hqo : o * (q / o) = q := Nat.mul_div_cancel' ho
  refine ⟨m * (q / o), Finset.mem_range.mpr ?_, ?_⟩
  · calc m * (q / o) < o * (q / o) :=
        Nat.mul_lt_mul_of_pos_right hm (Nat.div_pos (Nat.le_of_dvd hq ho) ho0)
      _ = q := hqo
  · have hqo' : (q : ℝ) = (o : ℝ) * ((q / o : ℕ) : ℝ) := by
      have hcast := congrArg (fun n : ℕ => (n : ℝ)) hqo
      push_cast at hcast
      linarith [hcast]
    have hqo_ne : ((q / o : ℕ) : ℝ) ≠ 0 := by
      have : 0 < q / o := Nat.div_pos (Nat.le_of_dvd hq ho) ho0
      exact_mod_cast this.ne'
    have : ((m * (q / o) : ℕ) : ℝ) / (q : ℝ) = (m : ℝ) / (o : ℝ) := by
      rw [hqo', Nat.cast_mul]
      field_simp
    rw [this]
    simpa using hcoe

/-- Membership in `(ℚ/ℤ)_{≤l}`: `α ∈ iwArithFreqs ρ l` iff `α` is killed by some `q ∈ P_{≤l}`. -/
theorem mem_iwArithFreqs {ρ : ℝ} {l : ℕ} {α : Circle} :
    α ∈ iwArithFreqs ρ l ↔ ∃ q ∈ iwP ρ l, q • α = 0 := by
  rw [iwArithFreqs, Finset.mem_biUnion]
  constructor
  · rintro ⟨q, hq, hα⟩
    rw [Finset.mem_image] at hα
    obtain ⟨a, -, rfl⟩ := hα
    exact ⟨q, hq, nsmul_div_eq_zero (pos_of_mem_iwP hq)⟩
  · rintro ⟨q, hq, hα⟩
    exact ⟨q, hq, Finset.mem_image.mpr
      (eq_div_of_nsmul_eq_zero (pos_of_mem_iwP hq) hα)⟩

/-- The common denominator `Q_{≤l} = lcm(P_{≤l})` of the IW arithmetic frequency set. -/
noncomputable def iwQl (ρ : ℝ) (l : ℕ) : ℕ := (iwP ρ l).lcm id

theorem iwQl_pos {ρ : ℝ} {l : ℕ} : 0 < iwQl ρ l := by
  rw [iwQl, Nat.pos_iff_ne_zero]
  intro h
  obtain ⟨q, hq, hq0⟩ := Finset.lcm_eq_zero_iff.mp h
  exact ne_zero_of_mem_iwP hq hq0

/-- `(ℚ/ℤ)_{≤l}` is contained in the `iwQl ρ l`-torsion subgroup of `ℝ/ℤ`. -/
theorem iwQl_nsmul_eq_zero {ρ : ℝ} {l : ℕ} {α : Circle} (h : α ∈ iwArithFreqs ρ l) :
    iwQl ρ l • α = 0 := by
  obtain ⟨q, hq, hqα⟩ := mem_iwArithFreqs.mp h
  have hdvd : q ∣ iwQl ρ l := by
    rw [iwQl]; exact Finset.dvd_lcm hq
  obtain ⟨k, hk⟩ := hdvd
  rw [hk, mul_nsmul, hqα, smul_zero]

end Work.Analysis.IonescuWainger
