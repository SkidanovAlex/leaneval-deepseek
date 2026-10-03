import Mathlib
import Submission.Work.KMTAreas.ADev.Defs

namespace Work.A7Hi2

theorem tsum_bSign_conv {t : Finset ℤ} {g : ℤ → ℂ} (hg : ∀ x : ℤ, x ∉ t → g x = 0)
    (k : ℕ → ℤ → ℂ) (F : Finset ℕ) (ω : ℕ → Bool) (n : ℤ) :
    (∑' y : ℤ, (∑ l ∈ F, Work.KMTAreas.ADev.bSign ω l * k l y) * g (n - y))
      = ∑ l ∈ F, Work.KMTAreas.ADev.bSign ω l * (∑' y : ℤ, k l y * g (n - y)) := by
  -- `g` is supported on the finite set `t`, so both series are really finite sums over
  -- `S = t.image (fun x => n - x)`, the set of `y` with `g (n - y) ≠ 0`.
  set S : Finset ℤ := t.image (fun x : ℤ => n - x) with hS
  have hmem : ∀ y : ℤ, y ∈ S ↔ n - y ∈ t := by
    intro y
    rw [hS, Finset.mem_image]
    constructor
    · rintro ⟨x, hx, hxy⟩
      rw [← hxy]
      simpa using hx
    · intro hy
      exact ⟨n - y, hy, by ring⟩
  have hsup1 : ∀ y ∉ S, (∑ l ∈ F, Work.KMTAreas.ADev.bSign ω l * k l y) * g (n - y) = 0 := by
    intro y hy
    have hn : n - y ∉ t := fun h => hy ((hmem y).mpr h)
    rw [hg (n - y) hn, mul_zero]
  have hsup2 : ∀ l : ℕ, ∀ y ∉ S, k l y * g (n - y) = 0 := by
    intro l y hy
    have hn : n - y ∉ t := fun h => hy ((hmem y).mpr h)
    rw [hg (n - y) hn, mul_zero]
  calc (∑' y : ℤ, (∑ l ∈ F, Work.KMTAreas.ADev.bSign ω l * k l y) * g (n - y))
      = ∑ y ∈ S, (∑ l ∈ F, Work.KMTAreas.ADev.bSign ω l * k l y) * g (n - y) :=
        tsum_eq_sum (s := S) hsup1
    _ = ∑ y ∈ S, ∑ l ∈ F, (Work.KMTAreas.ADev.bSign ω l * k l y) * g (n - y) := by
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [Finset.sum_mul]
    _ = ∑ l ∈ F, ∑ y ∈ S, (Work.KMTAreas.ADev.bSign ω l * k l y) * g (n - y) :=
        Finset.sum_comm
    _ = ∑ l ∈ F, Work.KMTAreas.ADev.bSign ω l * ∑ y ∈ S, k l y * g (n - y) := by
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun y _ => by ring
    _ = ∑ l ∈ F, Work.KMTAreas.ADev.bSign ω l * (∑' y : ℤ, k l y * g (n - y)) := by
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [tsum_eq_sum (s := S) (hsup2 l)]

end Work.A7Hi2
