import Mathlib
import Submission.Work.Peluse.Nodes

namespace Work.Peluse.Ulower

/-- **Peluse's `U²`-inverse theorem at an arithmetic-progression shift scale.**

This is the form of `Work.Peluse.PeluseU2Inverse` used in the §9/degree-lowering chain: the shift
set is the arithmetic progression `arithIcc 1 D` (so the shift parameter is `δ' = D / L`) and the
uniformity hypothesis is stated for the *`2^2`-th power* `uNormPow 2` of the `U²`-norm (the power
that is actually produced by the peeling/box-sum arguments) rather than for the norm itself.

Since `uNormPow 2 Q S f = (uNorm 2 Q S f)^4`, the inverse theorem with `δ` replaced by
`δ^{1/4}` transfers verbatim; the exponents `4` on `δ` and the resulting `δ^{3K/4}` loss are
absorbed into the constant `C₀` and the exponent `K₀` (indeed one may take `C₀ := C'`,
`K₀ := K`). -/
theorem u2inverse_arithIcc (h1 : Work.Peluse.PeluseU2Inverse) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∃ K₀ : ℕ, 1 ≤ K₀ ∧
      ∀ (L D : ℕ) (g : ℤ → ℂ) (δ : ℝ),
        1 ≤ L → 1 ≤ D → (D : ℝ) ≤ (L : ℝ) →
        Work.Peluse.SupportIn g L → (∀ x : ℤ, ‖g x‖ ≤ 1) → 0 < δ → δ ≤ 1 →
        δ ≤ Work.Peluse.uNormPow 2 (Work.Peluse.arithIcc 1 D) (Work.Peluse.symIcc L) g →
        ∃ β : ℝ, C₀ * δ ^ K₀ * ((D : ℝ) / (L : ℝ)) ^ K₀ * (L : ℝ) ≤
          ‖∑' x : ℤ, g x * Complex.exp (2 * Real.pi * Complex.I * β * x)‖ := by
  obtain ⟨C', hC', K, hK, hbody⟩ := h1
  refine ⟨C', hC', K, hK, ?_⟩
  intro L D g δ hL hD hDL hsupp hbdd hδ0 hδ1 hnorm
  have hLpos : (0:ℝ) < (L:ℝ) := by exact_mod_cast hL
  have hDpos : (0:ℝ) < (D:ℝ) := by exact_mod_cast hD
  -- the shift parameter of `PeluseU2Inverse` that produces the shift set `[D]`
  set s : ℝ := (D:ℝ)/(L:ℝ) with hs
  have hs0 : 0 < s := by rw [hs]; exact div_pos hDpos hLpos
  have hs1 : s ≤ 1 := by rw [hs, div_le_one hLpos]; exact hDL
  have hfloor : (⌊s * (L:ℝ)⌋).toNat = D := by
    have hmul : s * (L:ℝ) = (D:ℝ) := by rw [hs]; field_simp
    rw [hmul, Int.floor_natCast, Int.toNat_natCast]
  -- `δ ≤ uNormPow 2 …` is `δ^{1/4} ≤ uNorm 2 …`
  have hδ14pos : 0 < δ ^ (1/4:ℝ) := Real.rpow_pos_of_pos hδ0 _
  have hδ14le : δ ^ (1/4:ℝ) ≤ 1 := Real.rpow_le_one hδ0.le hδ1 (by norm_num)
  have hu : δ ^ (1/4:ℝ) ≤
      Work.Peluse.uNorm 2 (Work.Peluse.arithIcc 1 D) (Work.Peluse.symIcc L) g := by
    have h := Real.rpow_le_rpow hδ0.le hnorm (by norm_num : (0:ℝ) ≤ 1/4)
    have h2 : Work.Peluse.uNorm 2 (Work.Peluse.arithIcc 1 D) (Work.Peluse.symIcc L) g
        = (Work.Peluse.uNormPow 2 (Work.Peluse.arithIcc 1 D) (Work.Peluse.symIcc L) g)
            ^ (1/4:ℝ) := by
      rw [Work.Peluse.uNorm]
      congr 1
      norm_num
    rw [h2]
    exact h
  obtain ⟨β, hβ⟩ := hbody L (δ ^ (1/4:ℝ)) s g hL hδ14pos hδ14le hs0 hs1 hsupp hbdd
    (by rw [hfloor]; exact hu)
  refine ⟨β, le_trans ?_ hβ⟩
  -- numerical comparison: `δ^K s^K ≤ (δ^{1/4} s)^K` because `0 < δ ≤ 1`
  have hpow : δ ^ K ≤ (δ ^ (1/4:ℝ)) ^ K := by
    have hle : δ ≤ δ ^ (1/4:ℝ) := by
      have h := Real.rpow_le_rpow_of_exponent_ge hδ0 hδ1 (by norm_num : (1/4:ℝ) ≤ 1)
      simpa using h
    exact pow_le_pow_left₀ hδ0.le hle K
  have h2 : δ ^ K * s ^ K ≤ (δ ^ (1/4:ℝ) * s) ^ K := by
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right hpow (pow_nonneg hs0.le K)
  calc C' * δ ^ K * s ^ K * (L:ℝ)
      = C' * (L:ℝ) * (δ ^ K * s ^ K) := by ring
    _ ≤ C' * (L:ℝ) * ((δ ^ (1/4:ℝ) * s) ^ K) :=
        mul_le_mul_of_nonneg_left h2 (mul_nonneg hC'.le (by positivity))
    _ = C' * (δ ^ (1/4:ℝ) * s) ^ K * (L:ℝ) := by ring

end Work.Peluse.Ulower
