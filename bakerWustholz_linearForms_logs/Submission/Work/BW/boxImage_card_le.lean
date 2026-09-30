import Mathlib
import Submission.Work.BW.subgroup_rayDegAux

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- Counting bound: if on the box `∏ᵢ [0, mᵢ]` the `c`-th coordinate of `Ψ` is bounded in absolute value by `K c · sup m`, then the number of distinct values of `Ψ` on the box is at most `∏_c (2 (K c · sup m) + 1)` (the values lie in a product of intervals holding that many integers). -/
theorem boxImage_card_le {N ρ : ℕ} (m : Fin N → ℕ)
    (Ψ : (Fin N → ℤ) →ₗ[ℤ] (Fin (N - ρ) → ℤ)) (K : Fin (N - ρ) → ℕ)
    (h : ∀ b ∈ boxPts N m, ∀ c, |(Ψ b) c| ≤ (K c : ℤ) * ((Finset.univ.sup m : ℕ) : ℤ)) :
    ((boxPts N m).image Ψ).card ≤ ∏ c, (2 * (K c * Finset.univ.sup m) + 1) := by
  classical
  -- Abbreviate `S = sup m`, the side length controlling the coordinate bounds.
  set S : ℕ := Finset.univ.sup m with hS
  -- Each coordinate of `Ψ b` is bounded by `↑(K c * S)`.
  have hbound : ∀ b ∈ boxPts N m, ∀ c, |(Ψ b) c| ≤ ((K c * S : ℕ) : ℤ) := by
    intro b hb c
    have h1 := h b hb c
    simpa [Nat.cast_mul] using h1
  -- Hence the image of the box under `Ψ` lies in the product of the integer intervals
  -- `[-(K c · S), K c · S]`, each holding `2 (K c · S) + 1` integers.
  have hsub : (boxPts N m).image Ψ ⊆
      Fintype.piFinset (fun c => Finset.Icc (-(((K c * S : ℕ) : ℤ))) ((K c * S : ℕ) : ℤ)) := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨b, hb, rfl⟩ := hx
    rw [Fintype.mem_piFinset]
    intro c
    rw [Finset.mem_Icc]
    exact abs_le.mp (hbound b hb c)
  calc ((boxPts N m).image Ψ).card
      ≤ (Fintype.piFinset (fun c => Finset.Icc (-(((K c * S : ℕ) : ℤ))) ((K c * S : ℕ) : ℤ))).card :=
        Finset.card_le_card hsub
    _ = ∏ c, (Finset.Icc (-(((K c * S : ℕ) : ℤ))) ((K c * S : ℕ) : ℤ)).card :=
        Fintype.card_piFinset _
    _ = ∏ c, (2 * (K c * S) + 1) := by
        apply Finset.prod_congr rfl
        intro c _
        rw [Int.card_Icc]
        have : (↑(K c * S) + 1 - -(↑(K c * S)) : ℤ) = ((2 * (K c * S) + 1 : ℕ) : ℤ) := by
          push_cast; ring
        rw [this, Int.toNat_natCast]

end Work.BW
