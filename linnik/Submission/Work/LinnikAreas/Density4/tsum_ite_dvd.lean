import Mathlib

namespace Work.LinnikAreas.Density4

/-- Reindex a `tsum` over the multiples of a positive `l`: summing `g n` over those
`n` divisible by `l` is the same as summing `g (l * m)` over all `m`.

The map `m ↦ l * m` is injective when `l > 0` and its range is exactly the support
of `n ↦ if l ∣ n then g n else 0`, so `Function.Injective.tsum_eq` applies. -/
theorem tsum_ite_dvd {l : ℕ} (hl : 0 < l) (g : ℕ → ℂ) :
    (∑' n : ℕ, if l ∣ n then g n else 0) = ∑' m : ℕ, g (l * m) := by
  have hmain : (∑' m : ℕ, (fun n : ℕ => if l ∣ n then g n else 0) (l * m))
      = ∑' n : ℕ, (fun n : ℕ => if l ∣ n then g n else 0) n :=
    Function.Injective.tsum_eq (f := fun n : ℕ => if l ∣ n then g n else 0)
      (g := fun m : ℕ => l * m) (fun a b hab => Nat.mul_left_cancel hl hab) (by
        intro n hn
        rw [Set.mem_range]
        by_cases hd : l ∣ n
        · obtain ⟨k, hk⟩ := hd
          exact ⟨k, hk.symm⟩
        · simp [Function.mem_support, hd] at hn)
  have hL : (∑' m : ℕ, (fun n : ℕ => if l ∣ n then g n else 0) (l * m))
      = ∑' m : ℕ, g (l * m) := by
    refine tsum_congr (fun m => ?_)
    simp
  rw [← hmain, hL]

end Work.LinnikAreas.Density4
