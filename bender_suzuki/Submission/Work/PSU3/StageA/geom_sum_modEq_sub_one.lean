import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PSU3.StageA

/-- `A ≡ 1` modulo `A - 1` whenever `A ≥ 1`. -/
private lemma self_modEq_one (A : ℕ) (hA : 1 ≤ A) : A ≡ 1 [MOD A - 1] :=
  (Nat.modEq_iff_dvd' hA).mpr (dvd_refl (A - 1)) |>.symm

/-- Every power of `A` is congruent to `1` modulo `A - 1`. -/
private lemma pow_modEq_one (A : ℕ) (hA : 1 ≤ A) (i : ℕ) : A ^ i ≡ 1 [MOD A - 1] := by
  simpa using Nat.ModEq.pow i (self_modEq_one A hA)

/-- A geometric sum `∑_{i < p} A ^ i` is congruent to `p` modulo `A - 1`:
base reduction `A ≡ 1` turns every summand into `1`. -/
theorem geom_sum_modEq_sub_one {A p : ℕ} (hA : 1 ≤ A) :
    Nat.ModEq (A - 1) (∑ i ∈ Finset.range p, A ^ i) p := by
  have h : (∑ i ∈ Finset.range p, A ^ i) ≡ (∑ i ∈ Finset.range p, (1 : ℕ)) [MOD A - 1] :=
    Nat.ModEq.sum (fun i _ => pow_modEq_one A hA i)
  have h' : (∑ i ∈ Finset.range p, (1 : ℕ)) = p := by
    rw [Finset.sum_const, Finset.card_range]
    simp
  rwa [h'] at h

end Work.PSU3.StageA
