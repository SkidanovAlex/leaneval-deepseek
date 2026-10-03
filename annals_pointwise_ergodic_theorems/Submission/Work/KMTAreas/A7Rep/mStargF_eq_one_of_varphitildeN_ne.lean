import Mathlib
import Submission.Work.KMTAreas.A7.cut_discharge

namespace Work.KMTAreas.A7Rep

/-- Monotonicity of `x ↦ 2^x` on `ℝ`. -/
private lemma two_rpow_mono {a b : ℝ} (h : a ≤ b) : (2 : ℝ) ^ a ≤ (2 : ℝ) ^ b :=
  (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mpr h

/-- **The `g`-side bump `φ̃_N` of §6 is supported inside the plateau of the cutoff `m̃_* = η_{≤-2dU}`.**

The bump `φ̃_N = η(2^{d(Log N-k₂)}·) - η(2^{d(Log N-k₂+1)}·)` is a difference of two rescalings of
the cutoff `η`, whose support is the open unit ball; hence a nonzero value at `θ` forces
`|θ| ≤ 2^{d(k₂ - Log N)}`.  The hypothesis `k₂ + 1 + 2U ≤ Log N` (plus `d = P.natDegree ≥ 1`)
turns this into `|θ| ≤ 2^{-2dU-1} = 2^{-2dU}/2`, which is exactly the plateau
`mStargF_eq_one_of_abs_le` of `Work.KMTAreas.A7.cut_discharge` for the cutoff `η_{≤ -2dU}`. -/
theorem mStargF_eq_one_of_varphitildeN_ne (P : Polynomial ℤ) (hdeg : 2 ≤ P.natDegree) (N k₂ U : ℕ)
    (h : (k₂ : ℤ) + 1 + 2 * (U : ℤ) ≤ Work.Analysis.EndVar.logN N) :
    ∀ θ : ℝ, Work.KMTAreas.A7.varphitildeN P.natDegree N k₂ θ ≠ 0 →
      Work.KMTAreas.A7.mStargF P.natDegree U θ = 1 := by
  intro θ hθ
  set d := P.natDegree with hd
  have hd1 : 1 ≤ d := le_trans (by norm_num) hdeg
  -- the support bound for `φ̃_N` (the modulation `e(P(Nt)·)` is nowhere zero, but here
  -- we simply use the same statement for the modulated bump at `t = 0`)
  have hnt : Work.KMTAreas.A7.varphitildeNt P d N k₂ 0 θ ≠ 0 := by
    rw [Work.KMTAreas.A7.varphitildeNt]
    exact mul_ne_zero hθ (by simp [Work.KMTAreas.A7.ee, Complex.exp_ne_zero])
  have hband : |θ| ≤ (2 : ℝ) ^ ((d : ℝ) * ((k₂ : ℝ) - (Work.Analysis.EndVar.logN N : ℝ))) :=
    Work.KMTAreas.A7.varphitildeNt_support_all P d N k₂ 0 θ hnt
  -- the regime hypothesis, in `ℝ`
  have hreal : (k₂ : ℝ) + 1 + 2 * (U : ℝ) ≤ (Work.Analysis.EndVar.logN N : ℝ) := by
    exact_mod_cast h
  -- the exponent comparison `d(k₂ - Log N) ≤ -2dU - 1`
  have hexp : (d : ℝ) * ((k₂ : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)) ≤
      ((-((d : ℤ) * 2 * (U : ℤ)) - 1 : ℤ) : ℝ) := by
    have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    have h1 : (k₂ : ℝ) - (Work.Analysis.EndVar.logN N : ℝ) ≤ -1 - 2 * (U : ℝ) := by linarith
    have h2 := mul_le_mul_of_nonneg_left h1 hd0
    have h3 : (d : ℝ) * (-1 - 2 * (U : ℝ)) ≤
        ((-((d : ℤ) * 2 * (U : ℤ)) - 1 : ℤ) : ℝ) := by
      have hd1' : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd1
      push_cast
      nlinarith
    linarith
  have hfin : |θ| ≤ (2 : ℝ) ^ (-((d : ℤ) * 2 * (U : ℤ)) - 1) := by
    calc |θ| ≤ (2 : ℝ) ^ ((d : ℝ) * ((k₂ : ℝ) - (Work.Analysis.EndVar.logN N : ℝ))) := hband
      _ ≤ (2 : ℝ) ^ (((-((d : ℤ) * 2 * (U : ℤ)) - 1 : ℤ)) : ℝ) := two_rpow_mono hexp
      _ = (2 : ℝ) ^ (-((d : ℤ) * 2 * (U : ℤ)) - 1) := Real.rpow_intCast 2 _
  -- `2^{-2dU-1} = 2^{-2dU}/2`, the hypothesis of the plateau lemma
  have hsplit : (2 : ℝ) ^ (-((d : ℤ) * 2 * (U : ℤ)) - 1) =
      (2 : ℝ) ^ (-((d : ℤ) * 2 * (U : ℤ))) / 2 := by
    rw [show -((d : ℤ) * 2 * (U : ℤ)) - 1 = (-((d : ℤ) * 2 * (U : ℤ))) - 1 from by ring,
      zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one]
  refine Work.KMTAreas.A7.mStargF_eq_one_of_abs_le ?_
  linarith [hfin, hsplit]

end Work.KMTAreas.A7Rep
