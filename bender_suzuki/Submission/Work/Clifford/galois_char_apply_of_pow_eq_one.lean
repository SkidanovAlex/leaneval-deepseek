import Mathlib
import Submission.Work.Clifford.galois_char_apply

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Clifford

/-- **Galois action on character values, governed by the order of the element.**

Let `ζ` be a primitive `n`-th root of unity and `σ : ℂ ≃+* ℂ` a ring automorphism with
`σ ζ = ζ ^ k`.  If `g ^ n = 1`, then `σ (χ g) = χ (g ^ k)` for every irreducible character
`χ`.  This is `Work.Clifford.galois_char_apply` with the hypothesis `Nat.card G ∣ n` replaced by
the weaker `g ^ n = 1`; the proof mirrors it, using `Work.Clifford.galois_trace_aux n n k`. -/
theorem galois_char_apply_of_pow_eq_one {G : Type*} [Group G] {n : ℕ} (hn : 0 < n)
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ n) (σ : ℂ ≃+* ℂ) {k : ℕ} (hσ : σ ζ = ζ ^ k)
    {χ : G → ℂ} (hχ : χ ∈ Work.Clifford.Irr G) {g : G} (hg : g ^ n = 1) :
    σ (χ g) = χ (g ^ k) := by
  obtain ⟨V, _hVsimple, hVχ⟩ := (Work.Clifford.mem_Irr (G := G) (χ := χ)).mp hχ
  -- `g ^ n = 1` makes `V.ρ g` an endomorphism whose `n`-th power is `1`
  have hT : (V.ρ g) ^ n = 1 := by
    rw [← map_pow, hg, map_one]
  have hmain := galois_trace_aux n n k hn hζ (dvd_refl n) σ hσ
    (Module.finrank ℂ V) V rfl (V.ρ g) hT
  rw [← hVχ]
  show σ (LinearMap.trace ℂ V (V.ρ g)) = LinearMap.trace ℂ V (V.ρ (g ^ k))
  rw [map_pow]
  exact hmain

end Work.Clifford
