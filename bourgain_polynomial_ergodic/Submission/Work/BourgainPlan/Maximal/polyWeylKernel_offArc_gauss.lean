import Mathlib
import Submission.Work.BourgainPlan.Maximal.model_pre
import Submission.Work.BourgainPlan.Maximal.polyWeight_cap_modulus
import Submission.Work.BourgainPlan.Maximal.major_arc_bound_pre
import Submission.Work.BourgainPlan.Maximal.poly_kernel_minor_arc

/-!
# Decay of the polynomial Weyl kernel off the `2^m`-arcs

This file proves `Work.BourgainPlan.Maximal.polyWeylKernel_offArc_gauss`: for an integer polynomial
`P : ℤ[X]` of degree `d ≥ 2` with leading coefficient `c = P.leadingCoeff > 0` there are constants
`A, σ, C, c₀ > 0` such that for every pair of scales `m, N`, every `θ` at distance
`> N^{-(d-1/4)}` from every arc centre `a/q + l` with `1 ≤ q < 2^m`, `0 ≤ a < q`, `gcd a q = 1`,
`l ∈ [-1, c]`, the Weyl kernel of `P` obeys

`‖polyWeylKernel P N θ‖ ≤ A · 2^{−mσ} + C · N^{−c₀}`.

The proof is a two-case split on whether `θ` lies on one of the *major arcs of the level `1/4`*
(radius `N^{-(d-1/4)}`, denominator `q ≤ N^{1/4}`):

* **On an arc** `a/q + l` of level `1/4`: the off-arc hypothesis (applied with this same `a`, `q`,
  `l`) forces `q ≥ 2^m` — for `q < 2^m` the hypothesis would give the distance `> N^{-(d-1/4)}`,
  contradicting the arc membership.  Then the single-arc major-arc approximation
  `major_arc_bound_pre` (Bourgain (1989), (6.10)) gives
  `‖kernel − polyWeight P (q·c) (a + l·q) · polyProfile P N (…)‖ ≤ C₁ N^{−c₁}`, and the Gauss-sum
  cap `polyWeight_cap_modulus` (Bourgain (1989), (6.18)) turns `q ≥ 2^m` into
  `‖polyWeight P (q·c) (a + l·q)‖ ≤ A 2^{−mσ}` with `σ = 2^{−(d+1)}`; `‖polyProfile‖ ≤ 1` finishes.

* **Off the level-`1/4` arcs**: the off-arc hypothesis is not needed at all — this is exactly the
  minor-arc hypothesis of `poly_kernel_minor_arc`, which gives the power decay
  `‖kernel‖ ≤ C₂ N^{−ν}`.

Both cases are dominated by `A · 2^{−mσ} + (C₁ + C₂) · N^{−min c₁ ν}`, so the constants
`A, σ, C₁ + C₂, min c₁ ν` work.
-/

namespace Work.BourgainPlan.Maximal

open Finset
open scoped BigOperators

set_option autoImplicit false

/-- **Decay of the polynomial Weyl kernel off the `2^m`-arcs.**  Let `P : ℤ[X]` have degree
`d ≥ 2` and leading coefficient `c = P.leadingCoeff > 0`.  There are `A, σ, C, c₀ > 0` such that
for all `m, N : ℕ` and `θ : ℝ` with `3 ≤ N`, `0 ≤ θ ≤ 1`, if `c·θ` is at distance
`> N^{-(d-1/4)}` from every `a/q + l` with `1 ≤ q < 2^m`, `0 ≤ a < q`, `gcd a q = 1` and
`l ∈ [-1, c]`, then `‖polyWeylKernel P N θ‖ ≤ A · 2^{−mσ} + C · N^{−c₀}`. -/
theorem polyWeylKernel_offArc_gauss (P : Polynomial ℤ) (hc : 0 < P.leadingCoeff)
    (hd : 2 ≤ P.natDegree) :
    ∃ A σ C c₀ : ℝ, 0 < A ∧ 0 < σ ∧ 0 < C ∧ 0 < c₀ ∧
      ∀ (m N : ℕ) (θ : ℝ), 3 ≤ N → 0 ≤ θ → θ ≤ 1 →
        (∀ (q a : ℕ) (l : ℤ), 1 ≤ q → q < 2 ^ m → a < q → Nat.gcd a q = 1 →
          l ∈ Finset.Icc (-1 : ℤ) P.leadingCoeff →
          (N : ℝ) ^ (-((P.natDegree : ℝ) - (1 : ℝ)/4))
            < |(P.leadingCoeff : ℝ) * θ - (a : ℝ) / (q : ℝ) - (l : ℝ)|) →
        ‖Work.BourgainPlan.Maximal.polyWeylKernel P N θ‖
          ≤ A * (2 : ℝ) ^ (-(m : ℝ) * σ) + C * (N : ℝ) ^ (-c₀) := by
  obtain ⟨A, hApos, hcap⟩ := polyWeight_cap_modulus P hc hd
  obtain ⟨c₁, C₁, hc₁pos, hC₁pos, hmaj⟩ := major_arc_bound_pre P hc hd
  obtain ⟨ν, C₂, hνpos, hC₂pos, hmin⟩ := poly_kernel_minor_arc P hc hd
  refine ⟨A, (2 : ℝ) ^ (-((P.natDegree : ℝ) + 1)), C₁ + C₂, min c₁ ν, hApos,
    Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 2) _, by linarith, lt_min hc₁pos hνpos, ?_⟩
  intro m N θ hN3 hθ0 hθ1 hoff
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : 1 ≤ N)
  have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  -- monotonicity of `N ↦ N^{-t}` in the exponent
  have hNpow₁ : (N : ℝ) ^ (-c₁) ≤ (N : ℝ) ^ (-(min c₁ ν)) := by
    apply Real.rpow_le_rpow_of_exponent_le hN1
    have := min_le_left c₁ ν
    linarith
  have hNpow₂ : (N : ℝ) ^ (-ν) ≤ (N : ℝ) ^ (-(min c₁ ν)) := by
    apply Real.rpow_le_rpow_of_exponent_le hN1
    have := min_le_right c₁ ν
    linarith
  have hC12 : (0 : ℝ) ≤ C₁ + C₂ := by linarith
  by_cases harc : ∃ (q a : ℕ) (l : ℤ), 1 ≤ q ∧ q ≤ Nat.floor ((N:ℝ)^((1:ℝ)/4)) ∧ a < q ∧
      Nat.gcd a q = 1 ∧ l ∈ Finset.Icc (-1:ℤ) P.leadingCoeff ∧
      |(P.leadingCoeff:ℝ)*θ - (a:ℝ)/(q:ℝ) - (l:ℝ)|
        ≤ (N:ℝ)^(-((P.natDegree:ℝ) - (1:ℝ)/4))
  · -- ### Case 1: `θ` lies on a major arc of level `1/4`
    obtain ⟨q, a, l, hq1, hqQ, haq, hgcd, hl, hdist⟩ := harc
    -- the off-arc hypothesis forces `2^m ≤ q`
    have hqm : 2 ^ m ≤ q := by
      by_contra hcon
      rw [not_le] at hcon
      have h := hoff q a l hq1 hcon haq hgcd hl
      linarith
    have hqN : (q:ℝ) ≤ (N:ℝ)^((1:ℝ)/4) := by
      have h1 : (q:ℝ) ≤ (Nat.floor ((N:ℝ)^((1:ℝ)/4)) : ℝ) := by exact_mod_cast hqQ
      have h2 : ((Nat.floor ((N:ℝ)^((1:ℝ)/4)) : ℕ) : ℝ) ≤ (N:ℝ)^((1:ℝ)/4) :=
        Nat.floor_le (Real.rpow_nonneg hNr.le _)
      linarith
    have hgcdZ : Int.gcd (a:ℤ) (q:ℤ) = 1 := by
      rw [Int.gcd_eq_natAbs, Int.natAbs_natCast, Int.natAbs_natCast]
      exact hgcd
    -- the Gauss-sum cap for the arc's complete sum
    have hw := hcap q (a:ℤ) l m hqm hgcdZ
    -- the arc's model term is the cap times the profile, which has norm `≤ 1`
    have hmt : ‖polyModelTermPre P N q a l θ‖
        ≤ A * (2:ℝ) ^ (-(m:ℝ) * ((2:ℝ)^(-((P.natDegree:ℝ)+1)))) := by
      rw [polyModelTermPre, norm_mul]
      have hprof := norm_polyProfile_le_one P N
        (θ - (((a:ℝ)/(q:ℝ) + (l:ℝ)) / (P.leadingCoeff:ℝ)))
      calc ‖polyWeight P (q * P.leadingCoeff.toNat) (a + l * q)‖
              * ‖polyProfile P N (θ - (((a:ℝ)/(q:ℝ) + (l:ℝ)) / (P.leadingCoeff:ℝ)))‖
          ≤ ‖polyWeight P (q * P.leadingCoeff.toNat) (a + l * q)‖ * 1 :=
            mul_le_mul_of_nonneg_left hprof (norm_nonneg _)
        _ = ‖polyWeight P (q * P.leadingCoeff.toNat) (a + l * q)‖ := mul_one _
        _ ≤ A * (2:ℝ) ^ (-(m:ℝ) * ((2:ℝ)^(-((P.natDegree:ℝ)+1)))) := hw
    have hmain := hmaj N q a l θ hq1 hqN haq hgcd hdist
    have hC1le : C₁ * (N:ℝ)^(-c₁) ≤ (C₁ + C₂) * (N:ℝ)^(-(min c₁ ν)) :=
      mul_le_mul (by linarith) hNpow₁ (Real.rpow_nonneg hNr.le _) hC12
    calc ‖polyWeylKernel P N θ‖
        = ‖(polyWeylKernel P N θ - polyModelTermPre P N q a l θ)
            + polyModelTermPre P N q a l θ‖ := by rw [sub_add_cancel]
      _ ≤ ‖polyWeylKernel P N θ - polyModelTermPre P N q a l θ‖
            + ‖polyModelTermPre P N q a l θ‖ := norm_add_le _ _
      _ ≤ C₁ * (N:ℝ)^(-c₁) + A * (2:ℝ) ^ (-(m:ℝ) * ((2:ℝ)^(-((P.natDegree:ℝ)+1)))) :=
          add_le_add hmain hmt
      _ ≤ (C₁ + C₂) * (N:ℝ)^(-(min c₁ ν))
            + A * (2:ℝ) ^ (-(m:ℝ) * ((2:ℝ)^(-((P.natDegree:ℝ)+1)))) := by
          linarith [hC1le]
      _ = A * (2:ℝ) ^ (-(m:ℝ) * ((2:ℝ)^(-((P.natDegree:ℝ)+1))))
            + (C₁ + C₂) * (N:ℝ)^(-(min c₁ ν)) := by ring
  · -- ### Case 2: `θ` is off every level-`1/4` arc: pure minor-arc decay
    push_neg at harc
    have hkey := hmin N hN3 θ hθ0 hθ1 harc
    have hC2le : C₂ * (N:ℝ)^(-ν) ≤ (C₁ + C₂) * (N:ℝ)^(-(min c₁ ν)) :=
      mul_le_mul (by linarith) hNpow₂ (Real.rpow_nonneg hNr.le _) hC12
    calc ‖polyWeylKernel P N θ‖ ≤ C₂ * (N:ℝ)^(-ν) := hkey
      _ ≤ (C₁ + C₂) * (N:ℝ)^(-(min c₁ ν)) := hC2le
      _ ≤ A * (2:ℝ) ^ (-(m:ℝ) * ((2:ℝ)^(-((P.natDegree:ℝ)+1))))
            + (C₁ + C₂) * (N:ℝ)^(-(min c₁ ν)) :=
          le_add_of_nonneg_left
            (mul_nonneg hApos.le (Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 2) _).le)

end Work.BourgainPlan.Maximal
