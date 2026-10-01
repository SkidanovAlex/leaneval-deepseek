/-
# ZeroFreeTables/P9/SigmaP3L_conj_eq

The conjugation (Schwarz-reflection) symmetry of the smoothing functional `SigmaP3L`:

`SigmaP3L χ s a λ₁ = SigmaP3L χ⁻¹ (conj s) a λ₁`.

Since `Lambda` is real and the weight `hbWL` is real, this reduces to the pointwise identity

`Re (χ⁻¹(n) · n^{-conj s}) = Re (χ(n) · n^{-s})`,

which follows from `conj (χ(n)) = χ⁻¹(n)` — the pointwise conjugation of a Dirichlet character
with values in `ℂ` is its group inverse (`MulChar.star_apply'`, a character takes values in the
roots of unity) — and from `conj (n^s) = n^{conj s}` for a natural base.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.P3.DefsL

open Complex

namespace Work.ZeroFreeTables.P9

/-- `conj (n ^ w) = n ^ (conj w)` for a natural base `n` (the degenerate case `n = 0` included:
`Complex.natCast_arg` gives `arg 0 = 0 ≠ π`). -/
lemma star_natCast_cpow (n : ℕ) (w : ℂ) : star ((n : ℂ) ^ w) = (n : ℂ) ^ (starRingEnd ℂ w) := by
  have harg : ((n : ℂ)).arg ≠ Real.pi := by
    rw [Complex.natCast_arg]; exact fun h => Real.pi_ne_zero h.symm
  have h := Complex.conj_cpow (n : ℂ) (starRingEnd ℂ w) harg
  simpa using h.symm

/-- The real part of the `n`-th summand of the twisted von Mangoldt series is invariant under
`χ ↦ χ⁻¹`, `s ↦ conj s`. -/
lemma chiTwistRe_inv_conj {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ) (n : ℕ) :
    (χ⁻¹ (n : ZMod N) / (n : ℂ) ^ (starRingEnd ℂ s)).re = (χ (n : ZMod N) / (n : ℂ) ^ s).re := by
  rw [← MulChar.star_apply' χ (n : ZMod N), ← star_natCast_cpow n s, RCLike.star_def,
    ← map_div₀ (starRingEnd ℂ) (χ ↑n) (↑n ^ s)]
  exact Complex.conj_re _

/-- `SigmaP3L` is invariant under `χ ↦ χ⁻¹`, `s ↦ conj s`: the real part of every summand is
unchanged, and the (real) weight and the von Mangoldt factor are untouched. -/
theorem SigmaP3L_conj_eq {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (L : ℝ) (s : ℂ)
    (a lam₁ : ℝ) :
    Work.ZeroFreeTables.SigmaP3L N L χ s a lam₁
      = Work.ZeroFreeTables.SigmaP3L N L χ⁻¹ (starRingEnd ℂ s) a lam₁ := by
  rw [Work.ZeroFreeTables.SigmaP3L_eq_tsum, Work.ZeroFreeTables.SigmaP3L_eq_tsum]
  congr 1
  exact tsum_congr fun n => by rw [← chiTwistRe_inv_conj χ s n]

end Work.ZeroFreeTables.P9
