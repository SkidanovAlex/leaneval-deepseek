import Mathlib

/-!
# Definitions for the Turán–Fejér lower bound

Spectral factorisation used below:

  r^{|m|} e^{imθ} - c·δ_{m0} = (r(1-r)/(1+r)) · Σ_p a(p+m) a(p) · e^{imθ} ,
  where c = (1-r)/(1+r),   a(0) = 1,   a(n+1) = (1+r) r^n ,

exhibits the Toeplitz symbol of `P_r - c` (Poisson kernel minus its minimum)
as a sum of squares.  Together with the Fejér kernel this gives `turanFejerLower`.
-/

namespace Work.LinnikAreas

/-- The coefficient sequence `a 0 = 1`, `a (n+1) = (1 + r) * r ^ n`. -/
def aSeq (r : ℝ) : ℕ → ℝ
  | 0 => 1
  | (n + 1) => (1 + r) * r ^ n

/-- `ℤ`-indexed extension of `aSeq`, equal to `0` on the negative integers. -/
def aZ (r : ℝ) (n : ℤ) : ℝ := if 0 ≤ n then aSeq r n.toNat else 0

@[simp] lemma aZ_ofNat (r : ℝ) (n : ℕ) : aZ r (n : ℤ) = aSeq r n := by
  rw [aZ, if_pos (by exact_mod_cast Nat.zero_le n)]
  simp

@[simp] lemma aSeq_zero (r : ℝ) : aSeq r 0 = 1 := rfl

lemma aSeq_succ (r : ℝ) (n : ℕ) : aSeq r (n + 1) = (1 + r) * r ^ n := rfl

lemma aZ_eq_zero_of_neg (r : ℝ) {n : ℤ} (hn : n < 0) : aZ r n = 0 := by
  rw [aZ, if_neg (by omega)]

lemma aZ_neg_succ (r : ℝ) (n : ℕ) : aZ r (-((n : ℤ) + 1)) = 0 :=
  aZ_eq_zero_of_neg r (by omega)

/-- The Fejér kernel `K_N(θ) = Σ_{|m|<N} (1-|m|/N) r^{|m|} e^{imθ}` (real form). -/
noncomputable def Kfun (r θ : ℝ) (N : ℕ) : ℝ :=
  1 + 2 * ∑ m ∈ Finset.Icc 1 (N - 1), (1 - (m : ℝ) / N) * r ^ m * Real.cos ((m : ℝ) * θ)

/-- The summand whose double sum computes `N * (Kfun r θ N - (1-r)/(1+r))`. -/
noncomputable def tildea (r θ : ℝ) (m : ℤ) : ℝ :=
  r ^ m.natAbs * Real.cos ((m : ℝ) * θ) - if m = 0 then (1 - r) / (1 + r) else 0

/-- Autocorrelation `Σ_p a(p+m) a(p)` of `aZ`. -/
noncomputable def Az (r : ℝ) (m : ℤ) : ℝ := ∑' p : ℤ, aZ r (p + m) * aZ r p

/-- Real part of `Σ_k a(p+k) e^{ikθ}`. -/
noncomputable def Cf (r θ : ℝ) (N : ℕ) (p : ℤ) : ℝ :=
  ∑ k ∈ Finset.range N, aZ r (p + k) * Real.cos ((k : ℝ) * θ)

/-- Imaginary part of `Σ_k a(p+k) e^{ikθ}`. -/
noncomputable def Sf (r θ : ℝ) (N : ℕ) (p : ℤ) : ℝ :=
  ∑ k ∈ Finset.range N, aZ r (p + k) * Real.sin ((k : ℝ) * θ)

end Work.LinnikAreas
