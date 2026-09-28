import Mathlib

namespace Work.HP.HP2

/-- Given `k` coprime to `W`, every vector `b` has a "pre-image" modulo `W`: there is
`c : Fin m → ℤ` with `(W : ℤ) ∣ (k : ℤ) * c i - b i` for every `i`.  Equivalently, `c` is any
representative of the residue class `k⁻¹ b mod W`; this is the change of variable `z = c + W y`
in the Möbius count of the product-factors bound.  (No positivity of `W`, and no positivity of
`k`, is needed: `Nat.Coprime k W` alone suffices.) -/
lemma exists_coset_rep {m : ℕ} (W k : ℕ) (b : Fin m → ℤ) (h : Nat.Coprime k W) :
    ∃ c : Fin m → ℤ, ∀ i, (W : ℤ) ∣ (k : ℤ) * c i - b i := by
  -- Bézout relation coming from `gcd k W = 1`: `k * gcdA + W * gcdB = 1` over `ℤ`.
  have hbez : (1 : ℤ) = (k : ℤ) * Nat.gcdA k W + (W : ℤ) * Nat.gcdB k W := by
    have hh := Nat.gcd_eq_gcd_ab k W
    rw [h.gcd_eq_one] at hh
    simpa using hh
  -- `c i := gcdA k W * b i` is the representative of `k⁻¹ b mod W`.
  refine ⟨fun i => Nat.gcdA k W * b i, fun i => ?_⟩
  have key : (k : ℤ) * Nat.gcdA k W = 1 - (W : ℤ) * Nat.gcdB k W := by linarith [hbez]
  refine ⟨-(Nat.gcdB k W * b i), ?_⟩
  calc (k : ℤ) * (Nat.gcdA k W * b i) - b i
      = ((k : ℤ) * Nat.gcdA k W) * b i - b i := by ring
    _ = (1 - (W : ℤ) * Nat.gcdB k W) * b i - b i := by rw [key]
    _ = (W : ℤ) * (-(Nat.gcdB k W * b i)) := by ring

end Work.HP.HP2
