import Mathlib
import Submission.Work.HP.PFDefs
import Submission.Work.HP.eNorm_veronese_bounds

namespace Work.HP.HP2

/-- If `W` is coprime to `k` and `W ∣ k * m`, then `W ∣ m`.  (Characteristic-zero form of the
standard coprime-cancellation fact, in `ℤ`.) -/
private lemma dvd_of_coprime_mul {W k : ℕ} (hcop : Nat.Coprime k W) {m : ℤ}
    (h : (W : ℤ) ∣ (k : ℤ) * m) : (W : ℤ) ∣ m := by
  have hc : IsCoprime (W : ℤ) (k : ℤ) := Nat.isCoprime_iff_coprime.mpr hcop.symm
  exact hc.dvd_of_dvd_mul_left h

/-- Membership of an integer point in the cone region, rewritten so that the cone condition is
expressed through `Cgam (toR (veronese d n x))` and the radius bound through `eNorm`. -/
private lemma mem_coneRegion_toR_iff {d n : ℕ} {a : Mon d n → ℤ} {α T : ℝ}
    {x : Fin (n + 1) → ℤ} :
    toR x ∈ coneRegion d n a α T ↔
      eNorm x ≤ T ∧ toR a ∈ Cgam (toR (veronese d n x)) α := by
  rw [coneRegion, Set.mem_ofPred_eq]
  have h1 : rNorm (toR x) = eNorm x := rfl
  have h2 : veronese d n (toR x) = toR (veronese d n x) := (toR_veronese d n x).symm
  rw [h1, h2]

/-- **The integer points of a coset are the Möbius count set.**  Let `W k : ℕ` with `k` coprime to
`W`, let `b c : Fin (n+1) → ℤ` with `(W : ℤ) ∣ (k : ℤ) * c i - b i` for all `i` (so `c` represents
`k⁻¹ b` modulo `W`), and suppose `b` is *not* coordinatewise divisible by `W`.

Then the integer points `v` of the coset `c mod W` whose image `toR v` lies in the cone region
`coneRegion d n a α T` are exactly the nonzero `z` with `(k : ℤ) * z i ≡ b i (mod W)`, `eNorm z ≤ T`
and `toR a ∈ Cgam (toR (veronese d n z)) α`.

Steps: (i) `toR v ∈ coneRegion d n a α T ↔ eNorm v ≤ T ∧ toR a ∈ Cgam (toR (veronese d n v)) α`,
via `eNorm_eq_rNorm_toR` and `toR_veronese`; (ii) `W ∣ v i - c i ↔ W ∣ k * v i - b i`, using
`(k : ℤ) * (v i - c i) = ((k : ℤ) * v i - b i) - ((k : ℤ) * c i - b i)` and
`IsCoprime (W : ℤ) (k : ℤ)` (from `Nat.isCoprime_iff_coprime`, plus `.symm`);
(iii) `0` lies in the coset `c mod W` exactly when `W ∣ c i` for all `i`, which forces `W ∣ b i`
for all `i`; the hypothesis on `b` therefore removes the origin, the only point at which the two
sets can differ (`mobiusCount` excludes `z = 0` but this set does not exclude `0`). -/
lemma coset_eq_mobiusSet {d n : ℕ} (a : Work.HP.Mon d n → ℤ) (b c : Fin (n + 1) → ℤ)
    (W k : ℕ) (α T : ℝ)
    (hc : ∀ i, (W : ℤ) ∣ (k : ℤ) * c i - b i) (hcop : Nat.Coprime k W)
    (hb : ¬ ∀ i, (W : ℤ) ∣ b i) :
    ({v : Fin (n + 1) → ℤ | (∀ i, (W : ℤ) ∣ v i - c i) ∧
        Work.HP.toR v ∈ Work.HP.coneRegion d n a α T} : Set (Fin (n + 1) → ℤ))
      = {z : Fin (n + 1) → ℤ | z ≠ 0 ∧ (∀ i, (W : ℤ) ∣ (k : ℤ) * z i - b i) ∧
        Work.HP.eNorm z ≤ T ∧
        Work.HP.toR a ∈ Work.HP.Cgam (Work.HP.toR (Work.HP.veronese d n z)) α} := by
  ext x
  simp only [Set.mem_ofPred_eq]
  rw [mem_coneRegion_toR_iff]
  constructor
  · -- `v` in the coset: the congruence transfers to `k v ≡ b`, and `v ≠ 0` because `0` in the
    -- coset forces `W ∣ b i` for all `i`.
    rintro ⟨hcoset, hnorm, hcone⟩
    refine ⟨?_, ?_, hnorm, hcone⟩
    · intro hx0
      apply hb
      intro i
      have hci : (W : ℤ) ∣ c i := by
        have hh := hcoset i
        rw [hx0] at hh
        simpa using hh
      have h1 : (W : ℤ) ∣ (k : ℤ) * c i := dvd_mul_of_dvd_right hci k
      have h2 := hc i
      have h3 : b i = (k : ℤ) * c i - ((k : ℤ) * c i - b i) := by ring
      rw [h3]
      exact dvd_sub h1 h2
    · intro i
      have hxi := hcoset i
      have hki := hc i
      have heq : (k : ℤ) * x i - b i
          = (k : ℤ) * (x i - c i) + ((k : ℤ) * c i - b i) := by ring
      rw [heq]
      exact dvd_add (dvd_mul_of_dvd_right hxi k) hki
  · -- Conversely `k v ≡ b` implies `v ≡ c` by cancelling the unit `k` modulo `W`.
    rintro ⟨hxne, hcong, hnorm, hcone⟩
    refine ⟨?_, hnorm, hcone⟩
    intro i
    have h1 := hcong i
    have h2 := hc i
    refine dvd_of_coprime_mul hcop ?_
    have heq : (k : ℤ) * (x i - c i)
        = ((k : ℤ) * x i - b i) - ((k : ℤ) * c i - b i) := by ring
    rw [heq]
    exact dvd_sub h1 h2

end Work.HP.HP2
