import Mathlib
import Submission.Work.KMTAreas.A4.expSum_Icc_bound
import Submission.Work.KMTAreas.A4.denseMultiples_et
import Submission.Work.KMTAreas.A4.finalArithmetic

namespace Work.KMTAreas.A4

open scoped BigOperators

/-- Krause--Mirek--Tao / Green--Tao "recurrent linear functions are major arc" (Green--Tao,
*Quadratic uniformity of the Möbius function*, Lemma 3.1(i)):  a set `T` of lattice points in
`[-N,N]` of density at least `ρ`, all of whose multiples `α n` are within `δ ≤ ρ/4` of an integer,
forces `α` to be within `2^8/(ρ^2(2N+1))` of a rational with denominator at most `8/ρ`. -/
theorem denseMultiples_engine (α : ℝ) (δ : ℝ) (hδ : 0 < δ) (N : ℕ) (hN : 1 ≤ N) (T : Finset ℤ) (hT : ∀ n ∈ T, -(N : ℤ) ≤ n ∧ n ≤ (N : ℤ)) (hgood : ∀ n ∈ T, ∃ m : ℤ, |α * (n : ℝ) - (m : ℝ)| ≤ δ) (ρ : ℝ) (hρ : 0 < ρ) (hρδ : 4 * δ ≤ ρ) (hcard : ρ * (2 * (N : ℝ) + 1) ≤ (T.card : ℝ)) : ∃ q : ℕ, 1 ≤ q ∧ (q : ℝ) ≤ 8 / ρ ∧ ∃ a : ℤ, |α - (a : ℝ) / (q : ℝ)| ≤ 2 ^ 8 / (ρ ^ 2 * (2 * (N : ℝ) + 1)) := by
  have hTsub : T ⊆ Finset.Icc (-(N:ℤ)) (N:ℤ) := fun x hx => Finset.mem_Icc.mpr (hT x hx)
  have hcard_le : T.card ≤ 2*N+1 := by
    calc T.card ≤ (Finset.Icc (-(N:ℤ)) (N:ℤ)).card := Finset.card_le_card hTsub
      _ = 2*N+1 := by
        rw [Int.card_Icc]
        have h : (N:ℤ) + 1 - (-(N:ℤ)) = ((2*N+1 : ℕ) : ℤ) := by push_cast; ring
        rw [h, Int.toNat_natCast]
  have hcardR : (T.card : ℝ) ≤ 2*(N:ℝ)+1 := by exact_mod_cast hcard_le
  have hρ1 : ρ ≤ 1 := by nlinarith [hcard, hcardR]
  have hMpos : (0:ℝ) < 2*(N:ℝ)+1 := by positivity
  set Q : ℕ := ⌊8/ρ⌋₊ with hQdef
  have hQle : (Q:ℝ) ≤ 8/ρ := Nat.floor_le (by positivity)
  have hQlt : 8/ρ < (Q:ℝ)+1 := Nat.lt_floor_add_one _
  have hQlow : 7/ρ ≤ (Q:ℝ) := by
    have h2 : (8:ℝ)/ρ - 1 < (Q:ℝ) := by linarith [hQlt]
    have h3 : (7:ℝ)/ρ = 7*(1/ρ) := by ring
    have h4 : (8:ℝ)/ρ = 8*(1/ρ) := by ring
    have h1 : (1:ℝ) ≤ 1/ρ := by rw [le_div_iff₀ hρ]; linarith
    nlinarith [h2, h3, h4, h1]
  have hQ2 : 2 ≤ Q := by
    have h1 : (1:ℝ) ≤ 1/ρ := by rw [le_div_iff₀ hρ]; linarith
    have h7 : (7:ℝ) ≤ 7/ρ := by
      have h3 : (7:ℝ)/ρ = 7*(1/ρ) := by ring
      nlinarith [h3, h1]
    have : (2:ℝ) ≤ (Q:ℝ) := by linarith
    exact_mod_cast this
  have hQ1 : 1 ≤ Q := by omega
  have hgoodn : ∀ n ∈ T, nDist (α*(n:ℝ)) ≤ δ := by
    intro n hn
    obtain ⟨m, hm⟩ := hgood n hn
    exact (nDist_le_abs_sub_int (α*(n:ℝ)) m).trans hm
  set cQ : ℝ := ∫ x in (-(1/(2*(Q:ℝ))))..(1/(2*(Q:ℝ))), fejerKern (Q-1) x with hcQdef
  have hcast : (((Q-1:ℕ):ℝ) + 1) = (Q:ℝ) := by
    rw [Nat.cast_sub hQ1]; ring
  have hcQlow : (3:ℝ)/4 ≤ cQ := by
    rw [hcQdef]
    convert fejerKern_mass (Q-1) using 2 <;> rw [hcast]
  have hcQpos : 0 < cQ := by linarith
  set S : ℕ → ℂ := fun q => ∑ l ∈ Finset.Icc (-(N:ℤ)) (N:ℤ), Complex.exp (2*Real.pi*Complex.I*(q:ℂ)*(α:ℂ)*(l:ℂ)) with hSdef
  by_cases hzero : ∃ q ∈ Finset.Icc 1 (Q-1), nDist ((q:ℝ)*α) = 0
  · obtain ⟨q, hq, hq0⟩ := hzero
    have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
    have hqQ : (q:ℝ) ≤ 8/ρ := by
      have hqle : q ≤ Q-1 := (Finset.mem_Icc.mp hq).2
      have h1 : (q:ℝ) ≤ ((Q-1:ℕ):ℝ) := by exact_mod_cast hqle
      have h2 : ((Q-1:ℕ):ℝ) = (Q:ℝ) - 1 := by rw [Nat.cast_sub hQ1]; norm_num
      linarith [hQle]
    refine ⟨q, hq1, hqQ, ⟨round ((q:ℝ)*α), ?_⟩⟩
    have hx : (q:ℝ)*α = (round ((q:ℝ)*α) : ℝ) := by
      have h0 : |(q:ℝ)*α - (round ((q:ℝ)*α) : ℝ)| = 0 := by simpa [nDist] using hq0
      linarith [(abs_eq_zero.mp h0)]
    have hα : α - (round ((q:ℝ)*α) : ℝ) / (q:ℝ) = 0 := by
      have hqne : (q:ℝ) ≠ 0 := by positivity
      rw [sub_eq_zero, eq_div_iff hqne]
      linarith [hx]
    rw [hα, abs_zero]
    positivity
  · push Not at hzero
    have hS : ∀ q ∈ Finset.Icc 1 (Q-1), ‖S q‖ ≤ 1/(2*nDist ((q:ℝ)*α)) := by
      intro q hq
      have h := expSum_Icc_bound N ((q:ℝ)*α) (hzero q hq)
      rw [hSdef]
      simpa [mul_assoc, mul_comm, mul_left_comm] using h
    have hET := denseMultiples_et_engine Q N hQ1 α δ (le_of_lt hδ) T hT hgoodn
    have hX : (T.card : ℝ) ≤ (1/cQ) * (2*(δ + 1/(2*(Q:ℝ))) * (2*(N:ℝ)+1) + (2/Real.pi) * ∑ q ∈ Finset.Icc 1 (Q-1), (1/(q:ℝ)) * ‖S q‖) := hET
    have hpi : (0:ℝ) < 2/Real.pi := by positivity
    have hbound : (cQ*ρ - 2*δ - 1/(Q:ℝ)) * (2*(N:ℝ)+1) ≤ (2/Real.pi) * ∑ q ∈ Finset.Icc 1 (Q-1), (1/(q:ℝ)) * (1/(2*nDist ((q:ℝ)*α))) := by
      have h2 : cQ * (ρ * (2*(N:ℝ)+1)) ≤ cQ * (T.card:ℝ) := mul_le_mul_of_nonneg_left hcard hcQpos.le
      have h3 : cQ * (T.card:ℝ) ≤ 2*(δ + 1/(2*(Q:ℝ))) * (2*(N:ℝ)+1) + (2/Real.pi) * ∑ q ∈ Finset.Icc 1 (Q-1), (1/(q:ℝ)) * ‖S q‖ := by
        have h := mul_le_mul_of_nonneg_left hX hcQpos.le
        have h4 : cQ * ((1/cQ) * (2*(δ + 1/(2*(Q:ℝ))) * (2*(N:ℝ)+1) + (2/Real.pi) * ∑ q ∈ Finset.Icc 1 (Q-1), (1/(q:ℝ)) * ‖S q‖)) = 2*(δ + 1/(2*(Q:ℝ))) * (2*(N:ℝ)+1) + (2/Real.pi) * ∑ q ∈ Finset.Icc 1 (Q-1), (1/(q:ℝ)) * ‖S q‖ := by
          rw [← mul_assoc, mul_one_div_cancel hcQpos.ne', one_mul]
        linarith [h, h4.symm.le, h4.le]
      have h4 : ∑ q ∈ Finset.Icc 1 (Q-1), (1/(q:ℝ)) * ‖S q‖ ≤ ∑ q ∈ Finset.Icc 1 (Q-1), (1/(q:ℝ)) * (1/(2*nDist ((q:ℝ)*α))) := by
        apply Finset.sum_le_sum
        intro q hq
        have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
        have hqpos : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq1
        exact mul_le_mul_of_nonneg_left (hS q hq) (by positivity)
      have h5 : 2*(δ + 1/(2*(Q:ℝ))) = 2*δ + 1/(Q:ℝ) := by
        have hQne : (Q:ℝ) ≠ 0 := by positivity
        field_simp
      nlinarith [h2, h3, h4, h5, hpi, hcQpos]
    exact finalArithmetic Q N hQ2 hN α δ ρ cQ hρ hδ hρδ hcQlow hQlow hQle hbound


end Work.KMTAreas.A4
