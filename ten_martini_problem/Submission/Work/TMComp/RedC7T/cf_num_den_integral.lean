import Mathlib

namespace Work.TMComp.RedC7T

open GenContFract

/-- For the (regular) continued fraction of a real number `v`, every partial quotient
`⟨a, b⟩` that occurs has numerator `a = 1` and denominator `b` an integer `c ≥ 1`.
(The proof of `c ≥ 1` uses that the fractional parts of `IntFractPair.stream v` lie in
`[0,1)` and are non-zero, which is exactly what the hypothesis that no `s.get? n` is
`none` supplies.) -/
lemma of_get?_eq_some_cast {v : ℝ} {n : ℕ} {gp : GenContFract.Pair ℝ}
    (h : (GenContFract.of v).s.get? n = some gp) :
    ∃ c : ℤ, gp = ⟨1, (c : ℝ)⟩ ∧ 1 ≤ c := by
  obtain ⟨ifp, hstream, _hb⟩ :=
    GenContFract.IntFractPair.exists_succ_get?_stream_of_gcf_of_get?_eq_some h
  have h1 : (GenContFract.of v).s.get? n = some ⟨1, ((ifp.b : ℤ) : ℝ)⟩ :=
    GenContFract.get?_of_eq_some_of_succ_get?_intFractPair_stream hstream
  have hgp : gp = ⟨1, ((ifp.b : ℤ) : ℝ)⟩ := by
    rw [h] at h1
    exact (Option.some.injEq _ _).mp h1
  refine ⟨ifp.b, hgp, ?_⟩
  obtain ⟨ifp_n, hn, hfrne, heq⟩ := IntFractPair.succ_nth_stream_eq_some_iff.mp hstream
  have hbeq : ifp.b = ⌊ifp_n.fr⁻¹⌋ := by rw [← heq]; rfl
  have hbnd := IntFractPair.nth_stream_fr_nonneg_lt_one hn
  have hpos : 0 < ifp_n.fr := lt_of_le_of_ne hbnd.1 (Ne.symm hfrne)
  have hle : ((1 : ℤ) : ℝ) ≤ ifp_n.fr⁻¹ := by
    push_cast
    exact (one_le_inv₀ hpos).mpr (le_of_lt hbnd.2)
  rw [hbeq]
  exact Int.le_floor.mpr hle

theorem cf_num_den_integral (v : ℝ) (hv : ∀ n, ¬ (GenContFract.of v).TerminatedAt n) :
    ∃ (A : ℕ → ℤ) (B : ℕ → ℕ),
      (∀ n, (GenContFract.of v).nums n = (A n : ℝ)) ∧
      (∀ n, (GenContFract.of v).dens n = (B n : ℝ)) ∧
      (∀ n, 1 ≤ B n) := by
  -- Non-termination means every partial quotient exists.
  have hget : ∀ n, ∃ gp : GenContFract.Pair ℝ, (GenContFract.of v).s.get? n = some gp := by
    intro n
    have h : (GenContFract.of v).s.get? n ≠ none := fun hnone =>
      hv n (GenContFract.terminatedAt_iff_s_none.mpr hnone)
    exact Option.ne_none_iff_exists'.mp h
  -- ... and then it has numerator `1` and an integer denominator `≥ 1`.
  have hstep : ∀ n, ∃ c : ℤ, 1 ≤ c ∧ (GenContFract.of v).s.get? n = some ⟨1, (c : ℝ)⟩ := by
    intro n
    obtain ⟨gp, hgp⟩ := hget n
    obtain ⟨c, hgpc, hc⟩ := of_get?_eq_some_cast hgp
    refine ⟨c, hc, ?_⟩
    rw [hgp, hgpc]
  -- The continuants `contsAux n` of `of v` are integer pairs, and their second
  -- component is non-negative (positive as soon as `n ≥ 1`), by the two-step recurrence.
  have hP : ∀ n, ∃ A B : ℤ, (GenContFract.of v).contsAux n = ⟨(A : ℝ), (B : ℝ)⟩ ∧
      0 ≤ B ∧ (1 ≤ n → 1 ≤ B) := by
    apply Nat.twoStepInduction
    · refine ⟨1, 0, ?_, by norm_num, by omega⟩
      simp [GenContFract.contsAux]
    · refine ⟨⌊v⌋, 1, ?_, by norm_num, by omega⟩
      simp [GenContFract.contsAux]
    · intro n hn hn1
      obtain ⟨An, Bn, hAn, hBn0, hBn1⟩ := hn
      obtain ⟨An1, Bn1, hAn1, hBn10, hBn11⟩ := hn1
      obtain ⟨c, hc1, hcn⟩ := hstep n
      have hrec := GenContFract.contsAux_recurrence (g := GenContFract.of v) (n := n)
        hcn hAn hAn1
      refine ⟨c * An1 + An, c * Bn1 + Bn, ?_, ?_, ?_⟩
      · rw [hrec]
        simp only [Pair.mk.injEq]
        constructor <;> push_cast <;> ring
      · have h1 : 1 ≤ Bn1 := hBn11 (by omega)
        have hmul : 1 ≤ c * Bn1 := by
          have := mul_le_mul hc1 h1 (show (0:ℤ) ≤ 1 by norm_num) (show (0:ℤ) ≤ c by omega)
          simpa using this
        omega
      · intro _
        have h1 : 1 ≤ Bn1 := hBn11 (by omega)
        have hmul : 1 ≤ c * Bn1 := by
          have := mul_le_mul hc1 h1 (show (0:ℤ) ≤ 1 by norm_num) (show (0:ℤ) ≤ c by omega)
          simpa using this
        omega
  choose A B hAB using hP
  refine ⟨fun n => A (n+1), fun n => (B (n+1)).toNat, ?_, ?_, ?_⟩
  · intro n
    have h := (hAB (n+1)).1
    show (GenContFract.of v).nums n = (A (n+1) : ℝ)
    simp only [GenContFract.num_eq_conts_a, GenContFract.conts, Stream'.tail, Stream'.get]
    rw [h]
  · intro n
    have h := (hAB (n+1)).1
    have hnonneg : 0 ≤ B (n+1) := (hAB (n+1)).2.1
    have htoNat : ((B (n+1)).toNat : ℝ) = (B (n+1) : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg hnonneg
    show (GenContFract.of v).dens n = ((B (n+1)).toNat : ℝ)
    simp only [GenContFract.den_eq_conts_b, GenContFract.conts, Stream'.tail, Stream'.get]
    rw [h, htoNat]
  · intro n
    have hone : 1 ≤ B (n+1) := (hAB (n+1)).2.2 (by omega)
    show 1 ≤ (B (n+1)).toNat
    omega

end Work.TMComp.RedC7T
