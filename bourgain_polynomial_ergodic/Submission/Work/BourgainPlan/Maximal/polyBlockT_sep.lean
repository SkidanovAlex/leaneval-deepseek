import Mathlib
import Submission.Work.BourgainPlan.Maximal.poly_block_core_defs

namespace Work.BourgainPlan.Maximal

open Finset
open Commons.Analysis.ExponentialSums

/-- **The frequencies of a dyadic block are separated.**  For `c = P.leadingCoeff > 0`, any two distinct elements `p ≠ q` of the (frequency, weight) family `polyBlockT P m` are at circle distance at least `1/(c² · 4^{m+1})`: for every integer `l`, `1/(c²·4^{m+1}) ≤ |p.1 - q.1 + l|`.

Unfold `polyBlockT` (`Finset.mem_image`), write the two frequencies as `(a + s·q)/(q·c)` and `(a' + s'·q')/(q'·c)` with `(q,a), (q',a') ∈ blockPair m`, `s, s' < c`, and argue as in the pure-power analogue `Commons.Analysis.ExponentialSums.powBlockT_sep` (use `frac_eq_of_coprime` for the case `a/q = a'/q'` and the integer numerator `(a+sq)q' - (a'+s'q')q + l c q q'` otherwise, plus `q q' < 4^{m+1}`). -/
theorem polyBlockT_sep (P : Polynomial ℤ) (hc : 0 < P.leadingCoeff) (m : ℕ) :
    ∀ p ∈ polyBlockT P m, ∀ q ∈ polyBlockT P m, p ≠ q → ∀ l : ℤ,
      (1 : ℝ) / ((P.leadingCoeff : ℝ)^2 * (4:ℝ)^(m+1)) ≤ |p.1 - q.1 + (l:ℝ)| := by
  intro p hp q hq hpq l
  rw [polyBlockT, Finset.mem_image] at hp hq
  obtain ⟨t₁, ht₁, ht₁p⟩ := hp
  obtain ⟨t₂, ht₂, ht₂q⟩ := hq
  obtain ⟨⟨q₁, a₁⟩, s₁⟩ := t₁
  obtain ⟨⟨q₂, a₂⟩, s₂⟩ := t₂
  obtain ⟨hb₁, hs₁⟩ := Finset.mem_product.mp ht₁
  obtain ⟨hb₂, hs₂⟩ := Finset.mem_product.mp ht₂
  rw [Finset.mem_range] at hs₁ hs₂
  obtain ⟨h1, h2, h3, h4⟩ := mem_blockPair.mp hb₁
  obtain ⟨h1', h2', h3', h4'⟩ := mem_blockPair.mp hb₂
  have hq₁ : 0 < q₁ := lt_of_lt_of_le (Nat.two_pow_pos m) h1
  have hq₂ : 0 < q₂ := lt_of_lt_of_le (Nat.two_pow_pos m) h1'
  have hq₁R : (0:ℝ) < (q₁:ℝ) := by exact_mod_cast hq₁
  have hq₂R : (0:ℝ) < (q₂:ℝ) := by exact_mod_cast hq₂
  have hcpos : (0:ℝ) < (P.leadingCoeff : ℝ) := by exact_mod_cast hc
  have hCne : (P.leadingCoeff:ℝ) ≠ 0 := ne_of_gt hcpos
  have hc1z : (1:ℤ) ≤ P.leadingCoeff := by omega
  have hc1 : (1:ℝ) ≤ (P.leadingCoeff : ℝ) := by exact_mod_cast hc1z
  have hCnatZ : ((P.leadingCoeff.toNat : ℕ) : ℤ) = P.leadingCoeff :=
    Int.toNat_of_nonneg (le_of_lt hc)
  have hf₁ : ((a₁:ℝ) + (s₁:ℝ)*(q₁:ℝ)) / ((q₁:ℝ)*(P.leadingCoeff:ℝ)) = p.1 := by
    simpa using congrArg Prod.fst ht₁p
  have hf₂ : ((a₂:ℝ) + (s₂:ℝ)*(q₂:ℝ)) / ((q₂:ℝ)*(P.leadingCoeff:ℝ)) = q.1 := by
    simpa using congrArg Prod.fst ht₂q
  have ht_ne : ((q₁,a₁),s₁) ≠ ((q₂,a₂),s₂) := by
    intro ht
    exact hpq (ht₁p.symm.trans (by rw [ht]; exact ht₂q))
  rw [← hf₁, ← hf₂]
  -- The two frequencies are distinct.
  have hfreq_ne : ((a₁:ℝ) + (s₁:ℝ)*(q₁:ℝ))/((q₁:ℝ)*(P.leadingCoeff:ℝ))
      - ((a₂:ℝ) + (s₂:ℝ)*(q₂:ℝ))/((q₂:ℝ)*(P.leadingCoeff:ℝ)) + (l:ℝ) ≠ 0 := by
    intro hzero
    have hA : ((a₁:ℝ) + (s₁:ℝ)*(q₁:ℝ))/((q₁:ℝ)*(P.leadingCoeff:ℝ))
        = ((a₁:ℝ)/q₁ + (s₁:ℝ))/(P.leadingCoeff:ℝ) := by field_simp
    have hB : ((a₂:ℝ) + (s₂:ℝ)*(q₂:ℝ))/((q₂:ℝ)*(P.leadingCoeff:ℝ))
        = ((a₂:ℝ)/q₂ + (s₂:ℝ))/(P.leadingCoeff:ℝ) := by field_simp
    have hmul : (a₁:ℝ)/q₁ - (a₂:ℝ)/q₂ + ((s₁:ℝ) - (s₂:ℝ))
        + (l:ℝ)*(P.leadingCoeff:ℝ) = 0 := by
      have h := hzero
      rw [hA, hB] at h
      have hdist : (((a₁:ℝ)/q₁ + (s₁:ℝ))/(P.leadingCoeff:ℝ)
            - ((a₂:ℝ)/q₂ + (s₂:ℝ))/(P.leadingCoeff:ℝ) + (l:ℝ)) * (P.leadingCoeff:ℝ)
          = (a₁:ℝ)/q₁ - (a₂:ℝ)/q₂ + ((s₁:ℝ) - (s₂:ℝ))
            + (l:ℝ)*(P.leadingCoeff:ℝ) := by
        rw [add_mul, sub_mul, div_mul_cancel₀ _ hCne, div_mul_cancel₀ _ hCne]
        ring
      have hc := congrArg (fun t : ℝ => t * (P.leadingCoeff:ℝ)) h
      rw [zero_mul] at hc
      rw [hdist] at hc
      exact hc
    have heqR : (a₁:ℝ)/q₁ - (a₂:ℝ)/q₂
        = ((((s₂:ℤ) - (s₁:ℤ) - l * P.leadingCoeff : ℤ)) : ℝ) := by
      push_cast
      linarith [hmul]
    have hbnd : |(a₁:ℝ)/q₁ - (a₂:ℝ)/q₂| < 1 := by
      rw [abs_lt]
      constructor
      · have hlt : (a₂:ℝ)/q₂ < 1 := by rw [div_lt_one hq₂R]; exact_mod_cast h3'
        have hnn : (0:ℝ) ≤ (a₁:ℝ)/q₁ := by positivity
        linarith
      · have hlt : (a₁:ℝ)/q₁ < 1 := by rw [div_lt_one hq₁R]; exact_mod_cast h3
        have hnn : (0:ℝ) ≤ (a₂:ℝ)/q₂ := by positivity
        linarith
    have hz0 : (s₂:ℤ) - (s₁:ℤ) - l * P.leadingCoeff = 0 := by
      have hz : |(s₂:ℤ) - (s₁:ℤ) - l * P.leadingCoeff| < (1:ℤ) := by
        have h1'' : |((((s₂:ℤ) - (s₁:ℤ) - l * P.leadingCoeff : ℤ)) : ℝ)| < (1:ℝ) := by
          rw [← heqR]; exact hbnd
        rw [← Int.cast_abs] at h1''
        exact_mod_cast h1''
      rw [abs_lt] at hz
      omega
    have haeq : (a₁:ℝ)/q₁ = (a₂:ℝ)/q₂ := by
      have h0 : (a₁:ℝ)/q₁ - (a₂:ℝ)/q₂ = 0 := by rw [heqR, hz0]; simp
      linarith
    obtain ⟨hqeq, haeq'⟩ := frac_eq_of_coprime hq₁ hq₂
      (Nat.coprime_iff_gcd_eq_one.mpr h4) (Nat.coprime_iff_gcd_eq_one.mpr h4') h3 h3' haeq
    have hs₁z : (s₁:ℤ) < P.leadingCoeff := by
      have : (s₁:ℤ) < (P.leadingCoeff.toNat : ℤ) := by exact_mod_cast hs₁
      rwa [hCnatZ] at this
    have hs₂z : (s₂:ℤ) < P.leadingCoeff := by
      have : (s₂:ℤ) < (P.leadingCoeff.toNat : ℤ) := by exact_mod_cast hs₂
      rwa [hCnatZ] at this
    have hs₁n : (0:ℤ) ≤ (s₁:ℤ) := by exact_mod_cast Nat.zero_le s₁
    have hs₂n : (0:ℤ) ≤ (s₂:ℤ) := by exact_mod_cast Nat.zero_le s₂
    have hsabs : |(s₂:ℤ) - (s₁:ℤ)| < P.leadingCoeff := by
      rw [abs_lt]; constructor <;> omega
    have hl0 : l = 0 := by
      have hs : (s₂:ℤ) - (s₁:ℤ) = l * P.leadingCoeff := by linarith [hz0]
      have hlt : |l * P.leadingCoeff| < P.leadingCoeff := by rw [← hs]; exact hsabs
      rw [abs_mul, abs_of_pos hc] at hlt
      have h1c : |l| * P.leadingCoeff < 1 * P.leadingCoeff := by rw [one_mul]; exact hlt
      have : |l| < (1:ℤ) := lt_of_mul_lt_mul_right h1c (le_of_lt hc)
      rw [abs_lt] at this; omega
    have hs12 : s₁ = s₂ := by
      have hs : (s₂:ℤ) - (s₁:ℤ) = l * P.leadingCoeff := by linarith [hz0]
      rw [hl0] at hs
      simp at hs
      omega
    exact ht_ne (Prod.ext (Prod.ext hqeq haeq') hs12)
  -- The shifted rationals are distinct.
  have hshift_ne : (a₁:ℝ)/q₁ + ((((s₁:ℤ) + l * P.leadingCoeff : ℤ)) : ℝ)
      ≠ (a₂:ℝ)/q₂ + ((s₂:ℤ):ℝ) := by
    intro hh
    apply hfreq_ne
    have hrel : ((a₁:ℝ) + (s₁:ℝ)*(q₁:ℝ))/((q₁:ℝ)*(P.leadingCoeff:ℝ))
        - ((a₂:ℝ) + (s₂:ℝ)*(q₂:ℝ))/((q₂:ℝ)*(P.leadingCoeff:ℝ)) + (l:ℝ)
        = ((a₁:ℝ)/q₁ + ((((s₁:ℤ) + l * P.leadingCoeff : ℤ)) : ℝ)
            - ((a₂:ℝ)/q₂ + ((s₂:ℤ):ℝ)))/(P.leadingCoeff:ℝ) := by
      push_cast
      field_simp [hq₁R.ne', hq₂R.ne', hCne]
      ring
    rw [hrel, hh]; simp
  have hsep := majorArc_shift_sep (q₁ := q₁) (q₂ := q₂) (a₁ := a₁) (a₂ := a₂)
      (l₁ := (s₁:ℤ) + l * P.leadingCoeff) (l₂ := (s₂:ℤ)) hq₁ hq₂ hshift_ne
  have hCmul : (a₁:ℝ)/q₁ + ((((s₁:ℤ) + l * P.leadingCoeff : ℤ)) : ℝ)
        - ((a₂:ℝ)/q₂ + ((s₂:ℤ):ℝ))
      = (P.leadingCoeff:ℝ) * (((a₁:ℝ) + (s₁:ℝ)*(q₁:ℝ))/((q₁:ℝ)*(P.leadingCoeff:ℝ))
          - ((a₂:ℝ) + (s₂:ℝ)*(q₂:ℝ))/((q₂:ℝ)*(P.leadingCoeff:ℝ)) + (l:ℝ)) := by
    have hrel : ((a₁:ℝ) + (s₁:ℝ)*(q₁:ℝ))/((q₁:ℝ)*(P.leadingCoeff:ℝ))
        - ((a₂:ℝ) + (s₂:ℝ)*(q₂:ℝ))/((q₂:ℝ)*(P.leadingCoeff:ℝ)) + (l:ℝ)
        = ((a₁:ℝ)/q₁ + ((((s₁:ℤ) + l * P.leadingCoeff : ℤ)) : ℝ)
            - ((a₂:ℝ)/q₂ + ((s₂:ℤ):ℝ)))/(P.leadingCoeff:ℝ) := by
      push_cast
      field_simp [hq₁R.ne', hq₂R.ne', hCne]
      ring
    rw [hrel]; field_simp [hCne]
  have hsep' := hsep
  rw [hCmul, abs_mul, abs_of_pos hcpos] at hsep'
  -- Assemble.
  have hprod : (q₁:ℝ)*(q₂:ℝ) ≤ (4:ℝ)^(m+1) := by
    have h₁ : (q₁:ℝ) < (2:ℝ)^(m+1) := by exact_mod_cast h2
    have h₂ : (q₂:ℝ) < (2:ℝ)^(m+1) := by exact_mod_cast h2'
    calc (q₁:ℝ)*(q₂:ℝ) ≤ (2:ℝ)^(m+1) * (2:ℝ)^(m+1) :=
          mul_le_mul h₁.le h₂.le (by positivity) (by positivity)
      _ = (4:ℝ)^(m+1) := by rw [← mul_pow]; norm_num
  have hkey : ((q₁:ℝ)*(q₂:ℝ))⁻¹ / (P.leadingCoeff:ℝ)
      ≤ |((a₁:ℝ) + (s₁:ℝ)*(q₁:ℝ))/((q₁:ℝ)*(P.leadingCoeff:ℝ))
          - ((a₂:ℝ) + (s₂:ℝ)*(q₂:ℝ))/((q₂:ℝ)*(P.leadingCoeff:ℝ)) + (l:ℝ)| := by
    rw [div_le_iff₀ hcpos]
    linarith [hsep', mul_comm (P.leadingCoeff:ℝ)
      |((a₁:ℝ) + (s₁:ℝ)*(q₁:ℝ))/((q₁:ℝ)*(P.leadingCoeff:ℝ))
          - ((a₂:ℝ) + (s₂:ℝ)*(q₂:ℝ))/((q₂:ℝ)*(P.leadingCoeff:ℝ)) + (l:ℝ)|]
  have hCq : (P.leadingCoeff:ℝ) * ((q₁:ℝ)*(q₂:ℝ)) ≤ (P.leadingCoeff:ℝ)^2 * (4:ℝ)^(m+1) := by
    have h1 : (P.leadingCoeff:ℝ) * ((q₁:ℝ)*(q₂:ℝ)) ≤ (P.leadingCoeff:ℝ) * (4:ℝ)^(m+1) :=
      mul_le_mul_of_nonneg_left hprod (le_of_lt hcpos)
    have h2 : (P.leadingCoeff:ℝ) * (4:ℝ)^(m+1) ≤ (P.leadingCoeff:ℝ)^2 * (4:ℝ)^(m+1) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      nlinarith [hc1]
    linarith [h1, h2]
  have hle : (1:ℝ)/((P.leadingCoeff:ℝ)^2 * (4:ℝ)^(m+1))
      ≤ ((q₁:ℝ)*(q₂:ℝ))⁻¹ / (P.leadingCoeff:ℝ) := by
    have hthis := one_div_le_one_div_of_le
      (by positivity : (0:ℝ) < (P.leadingCoeff:ℝ) * ((q₁:ℝ)*(q₂:ℝ))) hCq
    calc (1:ℝ)/((P.leadingCoeff:ℝ)^2*(4:ℝ)^(m+1))
          ≤ 1/((P.leadingCoeff:ℝ)*((q₁:ℝ)*(q₂:ℝ))) := hthis
      _ = ((q₁:ℝ)*(q₂:ℝ))⁻¹ / (P.leadingCoeff:ℝ) := by field_simp
  exact le_trans hle hkey

end Work.BourgainPlan.Maximal
