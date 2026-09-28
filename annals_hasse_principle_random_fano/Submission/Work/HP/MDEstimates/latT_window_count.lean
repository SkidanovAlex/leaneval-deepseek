import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.Sig2.num_lattices_of

namespace Work.HP.MDEstimates

/-- The number of primitive rank-three sublattices `L ≤ ℤ^5` whose first two successive minima
are bounded by `2^i`, `2^j` and whose third successive minimum is bounded by
`max 1 (4 Kmk (Δ+1)/(2^i 2^j))` is `≪_Kmk 2^{7i} 2^{5j} (max 1 (4 Kmk (Δ+1)/(2^i 2^j)))^3`.

This is the `ι = Fin 5`, `r = 3` instance of the paper's "number of lattices" bound
(`Work.HP.Sig2.num_lattices_of`), whose product `∏_j s_j^{N+r+1-2j}` evaluates in rank three
over `ℤ^5` (`N = 5`) to `s_1^7 s_2^5 s_3^3`. -/
theorem latT_window_count (Kmk : ℝ) (hKmk : 1 ≤ Kmk)
    (hmink : ∀ L : Submodule ℤ (Fin 5 → ℤ),
      (∏ j ∈ Finset.range (rk L), lam L (j + 1)) ≤ Kmk * detL L) :
    ∃ Kq : ℝ, 0 < Kq ∧ ∀ (i j : ℕ) (Δ : ℝ), 1 ≤ Δ →
      (({L : Submodule ℤ (Fin 5 → ℤ) | IsPrimLat L ∧ rk L = 3 ∧ lam L 1 ≤ (2:ℝ) ^ i ∧
          lam L 2 ≤ (2:ℝ) ^ j ∧
          lam L 3 ≤ max 1 (4 * Kmk * (Δ + 1) / ((2:ℝ) ^ i * (2:ℝ) ^ j))} :
          Set (Submodule ℤ (Fin 5 → ℤ))).ncard : ℝ)
        ≤ Kq * (2:ℝ) ^ (7 * i) * (2:ℝ) ^ (5 * j)
            * (max 1 (4 * Kmk * (Δ + 1) / ((2:ℝ) ^ i * (2:ℝ) ^ j))) ^ 3 := by
  obtain ⟨K, hKpos, hK⟩ :=
    Work.HP.Sig2.num_lattices_of (ι := Fin 5) Kmk (le_trans zero_le_one hKmk) hmink
  refine ⟨K, hKpos, fun i j Δ hΔ => ?_⟩
  set s : Fin 3 → ℝ :=
    ![ (2:ℝ)^i, (2:ℝ)^j, max 1 (4 * Kmk * (Δ + 1) / ((2:ℝ)^i * (2:ℝ)^j)) ] with hs
  -- The two set descriptions agree: a bound for each of the three successive minima.
  have hset : ({L : Submodule ℤ (Fin 5 → ℤ) | IsPrimLat L ∧ rk L = 3 ∧ lam L 1 ≤ (2:ℝ) ^ i ∧
        lam L 2 ≤ (2:ℝ) ^ j ∧
        lam L 3 ≤ max 1 (4 * Kmk * (Δ + 1) / ((2:ℝ) ^ i * (2:ℝ) ^ j))} :
        Set (Submodule ℤ (Fin 5 → ℤ)))
      = {L : Submodule ℤ (Fin 5 → ℤ) |
          IsPrimLat L ∧ rk L = 3 ∧ ∀ j : Fin 3, lam L (j.1 + 1) ≤ s j} := by
    ext L
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hp, hr, h1, h2, h3⟩
      refine ⟨hp, hr, ?_⟩
      intro k
      fin_cases k <;> simp [hs, h1, h2, h3]
    · rintro ⟨hp, hr, hf⟩
      refine ⟨hp, hr, ?_, ?_, ?_⟩
      · simpa [hs] using hf 0
      · simpa [hs] using hf 1
      · simpa [hs] using hf 2
  rw [hset]
  have hsge : ∀ k : Fin 3, 1 ≤ s k := by
    intro k
    rw [hs]
    fin_cases k <;> simp <;> exact one_le_pow₀ (by norm_num)
  have hb := hK 3 s hsge
  refine hb.trans (le_of_eq ?_)
  -- The product `∏_{j<3} s_j^{5+3+1-2(j+1)} = s_1^7 s_2^5 s_3^3`.
  have hp : (∏ j : Fin 3, s j ^ (Fintype.card (Fin 5) + 3 + 1 - 2 * (j.1 + 1)))
      = (2:ℝ)^(7*i) * (2:ℝ)^(5*j)
        * (max 1 (4 * Kmk * (Δ + 1) / ((2:ℝ)^i * (2:ℝ)^j)))^3 := by
    have hs0 : s 0 = (2:ℝ)^i := by simp [hs]
    have hs1 : s 1 = (2:ℝ)^j := by simp [hs]
    have hs2 : s 2 = max 1 (4 * Kmk * (Δ + 1) / ((2:ℝ)^i * (2:ℝ)^j)) := by simp [hs]
    rw [Fin.prod_univ_three]
    simp only [Fintype.card_fin, Fin.val_zero, Fin.val_one, Fin.val_two]
    norm_num
    simp only [hs0, hs1, hs2]
    rw [← pow_mul, ← pow_mul]
    rw [show i * 7 = 7 * i from by ring, show j * 5 = 5 * j from by ring]
  rw [hp]
  ring

end Work.HP.MDEstimates
