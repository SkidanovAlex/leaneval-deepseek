import Mathlib
import Submission.Work.ClassFieldTower.WitnessField

namespace Work.ClassFieldTower

open NumberField

/-- **The ramified prime ideals of `ℚ(√-d)`, `d = 30030`, satisfy `P_p² = (p)`.**

`P_p := (p, scR)`.  Hints: `P_p ^ 2 = span {p * p, p * scR, scR * scR} = span {p*p, p*scR, -dWit}`
using `scR_sq`, and since `p ∣ dWit` and `p ∤ dWit / p` the ideal is `span {p}`: the reverse
inclusion holds because `span {p*p, dWit} ∋ p` via Bézout for the coprime integers `p` and
`dWit / p` (`Nat.Coprime`, `Nat.coprime_iff_gcd_eq_one`), and `dWit = p * (dWit / p)`
(`Nat.mul_div_cancel'`). -/
theorem span_pair_sq (i : Fin 5) :
    Ideal.span ({(Work.ClassFieldTower.certPrime i : NumberField.RingOfIntegers Work.ClassFieldTower.Kc),
        Work.ClassFieldTower.scR} : Set (NumberField.RingOfIntegers Work.ClassFieldTower.Kc)) ^ 2
      = Ideal.span {(Work.ClassFieldTower.certPrime i :
          NumberField.RingOfIntegers Work.ClassFieldTower.Kc)} := by
  have hpP : (certPrime i : 𝓞 Kc) ∈ Ideal.span ({(certPrime i : 𝓞 Kc), scR} : Set (𝓞 Kc)) :=
    Ideal.subset_span (Set.mem_insert _ _)
  have hscP : scR ∈ Ideal.span ({(certPrime i : 𝓞 Kc), scR} : Set (𝓞 Kc)) :=
    Ideal.subset_span (Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton scR)))
  have hp1 : (certPrime i : 𝓞 Kc) ∈ Ideal.span ({(certPrime i : 𝓞 Kc)} : Set (𝓞 Kc)) :=
    Ideal.subset_span (Set.mem_singleton _)
  -- `p` divides `dWit` in the ring of integers
  have hdvdR : (certPrime i : 𝓞 Kc) ∣ (dWit : 𝓞 Kc) := by
    obtain ⟨c, hc⟩ := certPrime_dvd i
    exact ⟨(c : 𝓞 Kc), by rw [hc, Nat.cast_mul]⟩
  -- `scR ^ 2 = -dWit`
  have hdWit_eq : (dWit : 𝓞 Kc) = -(scR * scR) := by rw [scR_sq]; ring
  -- Bézout for the coprime integers `p` and `dWit / p`
  have hcop : (certPrime i).Coprime (dWit / certPrime i) := by fin_cases i <;> decide
  obtain ⟨a, b, hab⟩ : ∃ a b : ℤ,
      (certPrime i : ℤ) * a + ((dWit / certPrime i : ℕ) : ℤ) * b = 1 := by
    have h := Nat.gcd_eq_gcd_ab (certPrime i) (dWit / certPrime i)
    rw [Nat.coprime_iff_gcd_eq_one.mp hcop, Nat.cast_one] at h
    exact ⟨_, _, h.symm⟩
  -- `p = a * p * p + b * dWit` in `ℤ` ...
  have h1 : (certPrime i : ℤ) = a * (certPrime i : ℤ) * (certPrime i : ℤ) + b * (dWit : ℤ) := by
    have hqp : ((dWit / certPrime i : ℕ) : ℤ) * (certPrime i : ℤ) = (dWit : ℤ) := by
      have h : (certPrime i : ℕ) * (dWit / certPrime i) = dWit :=
        Nat.mul_div_cancel' (certPrime_dvd i)
      calc ((dWit / certPrime i : ℕ) : ℤ) * (certPrime i : ℤ)
          = ((certPrime i * (dWit / certPrime i) : ℕ) : ℤ) := by push_cast; ring
        _ = (dWit : ℤ) := by rw [h]
    calc (certPrime i : ℤ) = 1 * (certPrime i : ℤ) := by ring
      _ = ((certPrime i : ℤ) * a + ((dWit / certPrime i : ℕ) : ℤ) * b) * (certPrime i : ℤ) := by
            rw [hab]
      _ = a * (certPrime i : ℤ) * (certPrime i : ℤ)
            + b * (((dWit / certPrime i : ℕ) : ℤ) * (certPrime i : ℤ)) := by ring_nf
      _ = a * (certPrime i : ℤ) * (certPrime i : ℤ) + b * (dWit : ℤ) := by rw [hqp]
  -- ... hence in the ring of integers
  have hcast : (certPrime i : 𝓞 Kc) = (a : 𝓞 Kc) * (certPrime i : 𝓞 Kc) * (certPrime i : 𝓞 Kc)
      + (b : 𝓞 Kc) * (dWit : 𝓞 Kc) := by
    have h2 := congrArg (fun z : ℤ => (z : 𝓞 Kc)) h1
    push_cast at h2
    exact h2
  -- `p` is an explicit combination of `p * p` and `scR * scR`
  have hbez : (a : 𝓞 Kc) * ((certPrime i : 𝓞 Kc) * (certPrime i : 𝓞 Kc))
      + (b : 𝓞 Kc) * (-(scR * scR)) = (certPrime i : 𝓞 Kc) := by
    rw [← hdWit_eq, ← mul_assoc]
    exact hcast.symm
  refine le_antisymm ?_ ?_
  · -- `(p, scR) ^ 2 ≤ (p)`
    rw [pow_two, Ideal.span_pair_mul_span_pair]
    apply Ideal.span_le.mpr
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with h | h | h | h
    · rw [h]; exact Ideal.mul_mem_right _ _ hp1
    · rw [h]; exact Ideal.mul_mem_right scR _ hp1
    · rw [h]; exact Ideal.mul_mem_left _ scR hp1
    · rw [h]
      have hsr : scR * scR = -(dWit : 𝓞 Kc) := by rw [hdWit_eq]; ring
      rw [hsr]
      obtain ⟨c, hc⟩ := hdvdR
      rw [hc]
      exact neg_mem (Ideal.mul_mem_right c _ hp1)
  · -- `(p) ≤ (p, scR) ^ 2`, via Bézout
    have hp2mem : (certPrime i : 𝓞 Kc) * (certPrime i : 𝓞 Kc) ∈
        Ideal.span ({(certPrime i : 𝓞 Kc), scR} : Set (𝓞 Kc)) ^ 2 := by
      rw [pow_two]
      exact Ideal.mul_mem_mul hpP hpP
    have hsc2mem : scR * scR ∈ Ideal.span ({(certPrime i : 𝓞 Kc), scR} : Set (𝓞 Kc)) ^ 2 := by
      rw [pow_two]
      exact Ideal.mul_mem_mul hscP hscP
    have hmem : (a : 𝓞 Kc) * ((certPrime i : 𝓞 Kc) * (certPrime i : 𝓞 Kc))
        + (b : 𝓞 Kc) * (-(scR * scR))
        ∈ Ideal.span ({(certPrime i : 𝓞 Kc), scR} : Set (𝓞 Kc)) ^ 2 :=
      Ideal.add_mem _ (Ideal.mul_mem_left _ _ hp2mem) (Ideal.mul_mem_left _ _ (neg_mem hsc2mem))
    have hspan : Ideal.span {(certPrime i : 𝓞 Kc)} = Ideal.span
        ({((a : 𝓞 Kc) * ((certPrime i : 𝓞 Kc) * (certPrime i : 𝓞 Kc))
          + (b : 𝓞 Kc) * (-(scR * scR)))} : Set (𝓞 Kc)) := by
      rw [hbez]
    rw [hspan]
    exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hmem)

end Work.ClassFieldTower
