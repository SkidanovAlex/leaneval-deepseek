import Mathlib
import Submission.Work.ORHughesFree.Section6.Reduce

namespace Work.Section6

theorem unitsTimesSubgroup_conj_of_conj {K : Type} [Monoid K] {H : Type} [Group H]
    (N : Subgroup H) (t : H)
    (hconj : ∀ (k : ℤ) (n : N), t ^ k * (n : H) * t ^ (-k) ∈ N) :
    ∀ (k : ℤ) (n : Kˣ × H), n ∈ Work.ORHughesFree.unitsTimesSubgroup (K := K) N →
      (((1 : Kˣ), t) : Kˣ × H) ^ k * n * (((1 : Kˣ), t) : Kˣ × H) ^ (-k) ∈
        Work.ORHughesFree.unitsTimesSubgroup (K := K) N := by
  intro k n hn
  -- Membership in `unitsTimesSubgroup N` only constrains the second coordinate.
  rw [Work.ORHughesFree.mem_unitsTimesSubgroup] at hn ⊢
  -- The powers of `(1, t)` act componentwise.
  have hpow : (((1 : Kˣ), t) : Kˣ × H) ^ k = ((1 : Kˣ), t ^ k) := by ext <;> simp
  have hpow' : (((1 : Kˣ), t) : Kˣ × H) ^ (-k) = ((1 : Kˣ), t ^ (-k)) := by ext <;> simp
  rw [hpow, hpow']
  simpa using hconj k ⟨n.2, hn⟩

end Work.Section6
