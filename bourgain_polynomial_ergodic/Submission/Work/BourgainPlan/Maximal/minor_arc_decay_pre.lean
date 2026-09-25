import Mathlib
import Submission.Work.BourgainPlan.Maximal.l2_defs
import Submission.Commons.Analysis.ExponentialSums.weyl_minor_arc_decay

namespace Work.BourgainPlan.Maximal

open Polynomial

/-! ## Elementary facts about the realification `toRealPoly` of an integer polynomial -/

/-- Evaluation of `toRealPoly P` at a natural number cast. -/
lemma eval_toRealPoly_natCast (P : Polynomial ℤ) (x : ℕ) :
    (toRealPoly P).eval (x : ℝ) = ((P.eval (x : ℤ) : ℤ) : ℝ) := by
  rw [toRealPoly, Polynomial.eval_map]
  exact Polynomial.eval₂_at_natCast _ x

/-- The realification of an integer polynomial has the same degree. -/
lemma natDegree_toRealPoly (P : Polynomial ℤ) :
    (toRealPoly P).natDegree = P.natDegree := by
  rw [toRealPoly]
  exact Polynomial.natDegree_map_eq_of_injective (f := Int.castRingHom ℝ) Int.cast_injective P

/-- The leading coefficient of `θ · (toRealPoly P)` for `θ ≠ 0`. -/
lemma leadingCoeff_C_toRealPoly (P : Polynomial ℤ) (θ : ℝ) (hθ : θ ≠ 0) :
    (Polynomial.C θ * toRealPoly P).leadingCoeff = θ * (P.leadingCoeff : ℝ) := by
  have hcoeff_toReal : (toRealPoly P).coeff (toRealPoly P).natDegree
      = ((P.leadingCoeff : ℤ) : ℝ) := by
    unfold toRealPoly
    rw [Polynomial.coeff_map,
      Polynomial.natDegree_map_eq_of_injective (f := Int.castRingHom ℝ) Int.cast_injective P]
    rfl
  rw [Polynomial.leadingCoeff, Polynomial.coeff_C_mul, Polynomial.natDegree_C_mul hθ,
    hcoeff_toReal]

/-- **Minor-arc decay of the polynomial Weyl kernel (non-monic form).**  For an integer polynomial
`P` of degree `d ≥ 2` with `c = P.leadingCoeff > 0`, if the scaled frequency `c·θ` is far from every
rational `a/q` with `q ≤ N^{1/4}`, then the Weyl kernel decays like a power of `N`:

`‖N⁻¹ ∑_{n<N} e(θ P n)‖ ≤ C N^{-ν}`.

This is a thin wrapper around `Commons.Analysis.ExponentialSums.weyl_minor_arc_decay` applied to
the real polynomial `θ • P` (whose leading coefficient is `θ·c`): the hypothesis is exactly the
minor-arc hypothesis of that lemma, and `θ ≠ 0` follows from it (take `q = 1`, `a = 0`, using
`hc`). -/
theorem minor_arc_decay_pre (P : Polynomial ℤ) (hc : 0 < P.leadingCoeff) (hd : 2 ≤ P.natDegree) :
    ∃ ν C : ℝ, 0 < ν ∧ 0 < C ∧ ∀ (N : ℕ) (θ : ℝ), 3 ≤ N → 0 ≤ θ → θ ≤ 1 →
      (∀ (q : ℕ) (a : ℤ), 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ)/4) →
        (N : ℝ) ^ (-((P.natDegree : ℝ) - (1 : ℝ)/4))
            < |(P.leadingCoeff : ℝ) * θ - (a : ℝ) / (q : ℝ)|) →
      ‖Work.BourgainPlan.Maximal.polyWeylKernel P N θ‖ ≤ C * (N : ℝ) ^ (-ν) := by
  obtain ⟨C, ν, hC0, hν0, hdecay⟩ :=
    Commons.Analysis.ExponentialSums.weyl_minor_arc_decay P.natDegree hd ((1 : ℝ)/4)
      (by norm_num) (by norm_num)
  refine ⟨ν, C, hν0, hC0, ?_⟩
  intro N θ hN hθ0 hθ1 hminor
  -- `hc` is not needed for the argument; record the positivity of the real leading coefficient.
  have _hc : (0 : ℝ) < (P.leadingCoeff : ℝ) := by exact_mod_cast hc
  have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : 1 ≤ N)
  -- `θ ≠ 0`: otherwise the minor-arc hypothesis at `q = 1`, `a = 0` would give
  -- `N^{-(d-1/4)} < 0`.
  have hθne : θ ≠ 0 := by
    intro h0
    have hle : ((1 : ℕ) : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ)/4) := by
      have h1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : 1 ≤ N)
      simpa using Real.one_le_rpow h1 (by norm_num : (0 : ℝ) ≤ (1 : ℝ)/4)
    have h := hminor 1 0 le_rfl hle
    rw [h0] at h
    simp only [mul_zero, Int.cast_zero, zero_div, sub_zero, abs_zero] at h
    have hpos : (0 : ℝ) < (N : ℝ) ^ (-((P.natDegree : ℝ) - (1 : ℝ)/4)) :=
      Real.rpow_pos_of_pos hNr _
    linarith
  -- the real polynomial `θ • P` still has degree `P.natDegree`
  have hfdeg : (Polynomial.C θ * toRealPoly P).natDegree = P.natDegree := by
    rw [Polynomial.natDegree_C_mul hθne, natDegree_toRealPoly]
  have hlead : (Polynomial.C θ * toRealPoly P).leadingCoeff = θ * (P.leadingCoeff : ℝ) :=
    leadingCoeff_C_toRealPoly P θ hθne
  -- translate the minor-arc hypothesis in `ℕ`/leading-coefficient form into the form
  -- required by `weyl_minor_arc_decay` (`ℤ` denominators, `|f.leadingCoeff - a/q|`)
  have hminor' : ∀ (q : ℤ) (a : ℤ), 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ)/4) →
      (N : ℝ) ^ (-(P.natDegree : ℝ) + (1 : ℝ)/4)
        < |(Polynomial.C θ * toRealPoly P).leadingCoeff - (a : ℝ) / (q : ℝ)| := by
    intro q a hq hqle
    have hq0 : (0 : ℤ) ≤ q := by omega
    have hqnatZ : (q.toNat : ℤ) = q := Int.toNat_of_nonneg hq0
    have hqnat : (q.toNat : ℝ) = (q : ℝ) := by exact_mod_cast hqnatZ
    have hq1 : 1 ≤ q.toNat := by omega
    have hle' : (q.toNat : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ)/4) := by rw [hqnat]; exact hqle
    have h := hminor q.toNat a hq1 hle'
    rw [hlead, ← hqnat]
    have hexp : -((P.natDegree : ℝ)) + (1 : ℝ)/4
        = -((P.natDegree : ℝ) - (1 : ℝ)/4) := by ring
    rw [hexp, mul_comm]
    exact h
  have hW := hdecay N (Polynomial.C θ * toRealPoly P) hfdeg (by omega : 2 ≤ N) hminor'
  -- identify the Weyl kernel with the normalized Weyl sum of `θ • P`
  have hker : polyWeylKernel P N θ = (N : ℂ)⁻¹ * ∑ x ∈ Finset.range N,
      Complex.exp (2 * Real.pi * Complex.I *
        ((Polynomial.eval (x : ℝ) (Polynomial.C θ * toRealPoly P) : ℝ) : ℂ)) := by
    unfold polyWeylKernel
    rw [show ((N : ℝ)⁻¹ : ℂ) = (N : ℂ)⁻¹ by push_cast; ring]
    congr 1
    apply Finset.sum_congr rfl
    intro x _
    have he : Polynomial.eval (x : ℝ) (Polynomial.C θ * toRealPoly P)
        = θ * ((P.eval (x : ℤ) : ℤ) : ℝ) := by
      rw [Polynomial.eval_C_mul, eval_toRealPoly_natCast]
    rw [he]
  rw [hker]
  exact hW

end Work.BourgainPlan.Maximal
