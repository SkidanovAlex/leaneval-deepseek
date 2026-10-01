import Mathlib
import Submission.Work.LinnikAreas.Density4.ShiftedDefs

namespace Work.LinnikAreas.Density4

/-- The divisors of `p * m`, for `p` prime and coprime to `m`, are exactly the divisors of `m`
together with `p` times the divisors of `m`. -/
theorem divisors_prime_mul {p m : ℕ} (hp : p.Prime) :
    (p * m).divisors = m.divisors ∪ m.divisors.image (fun d => p * d) := by
  rw [Nat.divisors_mul, hp.divisors]
  ext x
  simp only [Finset.mem_mul, Finset.mem_union, Finset.mem_image, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro ⟨y, hy, z, hz, hyz⟩
    rcases hy with rfl | rfl
    · left; rw [one_mul] at hyz; exact hyz ▸ hz
    · right; exact ⟨z, hz, hyz⟩
  · rintro (hx | ⟨a, ha, hax⟩)
    · exact ⟨1, Or.inl rfl, x, hx, by rw [one_mul]⟩
    · exact ⟨p, Or.inr rfl, a, ha, hax⟩

theorem sum_divisors_prime_mul {p m : ℕ} (hp : p.Prime) (hm : p.Coprime m) (h : ℕ → ℝ) :
    ∑ d ∈ (p * m).divisors, h d
      = (∑ d ∈ m.divisors, h d) + ∑ d ∈ m.divisors, h (p * d) := by
  have hset := divisors_prime_mul (m := m) hp
  have hdisj : Disjoint m.divisors (m.divisors.image (fun d => p * d)) := by
    rw [Finset.disjoint_left]
    intro x hx hxim
    rw [Finset.mem_image] at hxim
    obtain ⟨d, hd, rfl⟩ := hxim
    exact (hp.coprime_iff_not_dvd.mp hm)
      (dvd_trans (dvd_mul_right p d) (Nat.mem_divisors.mp hx).1)
  have hinj : Set.InjOn (fun d => p * d) (↑m.divisors : Set ℕ) := by
    intro a _ b _ hab
    exact Nat.mul_left_cancel hp.pos hab
  rw [hset, Finset.sum_union hdisj, Finset.sum_image hinj]

end Work.LinnikAreas.Density4
