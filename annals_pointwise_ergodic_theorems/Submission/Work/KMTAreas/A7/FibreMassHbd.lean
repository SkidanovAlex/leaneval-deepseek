/-
# The corrected derivative `∫`-bound for the fibre symbol

For the symbol `σ = φ_N ⊗ φ̃_N · weylAvg P N α₁ α₂` and `i₁,i₂ ≤ 2`,

`∫_{ℝ²} ‖∂₁^{i₁}∂₂^{i₂} σ‖ ≤ fibHbdC P N q k₁ k₂ · (N⁻¹)^{1-i₁} · fibR₂(P,N,k₂)^{1-i₂}`

with `fibR₂ = min (N^{-d}) λ₂` (`λ₂ = 2^{dk₂}/2^{d Log N}`) and
`fibHbdC = 64 · M₀ · Cφ · Cψ · q²(1+S²/N) · λ₁ · max (λ₂N^d) 1`.

The two-frequency bookkeeping is the point: for `N ≥ 2` one has `λ₂ N^d ≥ 1` and the bound is the
"physical" one (`r₂ = N^{-d}`), while at `N = 1` (`2 > N`) the bump scale `λ₂` can fall below
`N^{-d}`, and then the frequency radius `r₂` must be reduced to `λ₂` — exactly the `(1+B)^j ≤ 2^j
B^j` dichotomy of the sharp `L¹`-computation of the `φ̃`-derivatives.

The proof is Leibniz expansion (`dp_symbol_eq_leibniz`) + the sharp symbol bound
(`pointwise_weighted_bound`) + the `L¹`-bounds for the bumps (`fibBumpCφ_bound`,
`fibBumpCψ_bound`) + the binomial sums `fibreMass_sumA`/`fibreMass_sumB` + the arithmetic
(`fibreMass_arith_core`).
-/
import Mathlib
import Submission.Work.KMTAreas.A7.fibreMass_pointwise
import Submission.Work.KMTAreas.A7.fibreMass_sumA
import Submission.Work.KMTAreas.A7.fibreMass_sumB
import Submission.Work.KMTAreas.A7.fibreMass_arith_core
import Submission.Work.KMTAreas.A7.fibreMass_const_compare

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.IonescuWainger

/-! ## The product integral identity -/

/-- The `ℝ²`-integral of a product `f(z.1)·g(z.2)` factorises. -/
theorem fibreMass_prodIntegral (P : Polynomial ℤ) (N k₁ k₂ a b : ℕ) (_ha : a ≤ 2) (_hb : b ≤ 2) :
    (∫ z : ℝ × ℝ, ‖iteratedDeriv a (varphiN N k₁) z.1‖
        * ‖iteratedDeriv b (varphitildeN P.natDegree N k₂) z.2‖)
      = (∫ ξ : ℝ, ‖iteratedDeriv a (varphiN N k₁) ξ‖)
        * (∫ η : ℝ, ‖iteratedDeriv b (varphitildeN P.natDegree N k₂) η‖) := by
  rw [MeasureTheory.Measure.volume_eq_prod ℝ ℝ]
  exact MeasureTheory.integral_prod_mul (fun ξ : ℝ => ‖iteratedDeriv a (varphiN N k₁) ξ‖)
    (fun η : ℝ => ‖iteratedDeriv b (varphitildeN P.natDegree N k₂) η‖)

/-! ## The main `∫`-bound -/

theorem fibreMass_hbd (P : Polynomial ℤ) (N q k₁ k₂ : ℕ)
    (α₁ α₂ : Work.Analysis.IonescuWainger.Circle)
    (hmZ : mZ P q α₁ α₂ = 0) (hN : 1 ≤ N) (hq : 0 < q) (hs₁ : q • α₁ = 0) (hs₂ : q • α₂ = 0)
    (i₁ i₂ : ℕ) (hi₁ : i₁ ≤ 2) (hi₂ : i₂ ≤ 2) :
    (∫ z : ℝ × ℝ, ‖Work.KMTPlan.A6.dp i₁ i₂ (fun a b => varphiN N k₁ a
        * varphitildeN P.natDegree N k₂ b * weylAvg P N α₁ α₂ a b) z.1 z.2‖)
      ≤ fibHbdC P N q k₁ k₂ * ((N : ℝ)⁻¹) ^ ((1 : ℝ) - (i₁ : ℝ))
          * (fibR₂ P N k₂) ^ ((1 : ℝ) - (i₂ : ℝ)) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  -- exponent bookkeeping: convert the real-power radii into integer powers
  have hpow₁ : ((N : ℝ)⁻¹) ^ ((1 : ℝ) - (i₁ : ℝ)) = (N : ℝ) ^ ((i₁ : ℤ) - 1) := by
    rw [Real.inv_rpow hNpos.le, ← Real.rpow_neg hNpos.le]
    rw [show -((1 : ℝ) - (i₁ : ℝ)) = (((i₁ : ℤ) - 1 : ℤ) : ℝ) by push_cast; ring]
    rw [Real.rpow_intCast]
  have hpow₂ : (fibR₂ P N k₂) ^ ((1 : ℝ) - (i₂ : ℝ))
      = (fibR₂ P N k₂) ^ ((1 : ℤ) - (i₂ : ℤ)) := by
    rw [show (1 : ℝ) - (i₂ : ℝ) = (((1 : ℤ) - (i₂ : ℤ) : ℤ) : ℝ) by push_cast; ring]
    rw [Real.rpow_intCast]
  rw [hpow₁, hpow₂]
  -- the two one-dimensional weight sums
  set F1 : ℝ → ℝ := fun x => ∑ a' ∈ Finset.range (i₁ + 1),
    (i₁.choose a' : ℝ) * ((N : ℝ) ^ (a' : ℤ))⁻¹ * ‖iteratedDeriv a' (varphiN N k₁) x‖ with hF1
  set F2 : ℝ → ℝ := fun y => ∑ b' ∈ Finset.range (i₂ + 1),
    (i₂.choose b' : ℝ) * (N : ℝ) ^ ((P.natDegree : ℤ) * (b' : ℤ))
      * ‖iteratedDeriv (i₂ - b') (varphitildeN P.natDegree N k₂) y‖ with hF2
  set Kc : ℝ := fibM0C P * (q : ℝ) ^ 2 * (1 + (Work.A7.Sval P k₁ k₂) ^ 2 / (N : ℝ))
      * (N : ℝ) ^ ((i₁ : ℤ) - 1) with hKc
  -- 1. the pointwise bound
  have hpt : ∀ z : ℝ × ℝ, ‖Work.KMTPlan.A6.dp i₁ i₂ (fun a b => varphiN N k₁ a
      * varphitildeN P.natDegree N k₂ b * weylAvg P N α₁ α₂ a b) z.1 z.2‖
      ≤ Kc * (F1 z.1 * F2 z.2) := by
    intro z
    rw [hKc, hF1, hF2]
    exact fibreMass_pointwise P N q k₁ k₂ α₁ α₂ hmZ hN hq hs₁ hs₂ i₁ i₂ hi₁ hi₂ z.1 z.2
  -- 2. integrability
  have htermA : ∀ a' ∈ Finset.range (i₁ + 1), Integrable (fun x : ℝ =>
      (i₁.choose a' : ℝ) * ((N : ℝ) ^ (a' : ℤ))⁻¹ * ‖iteratedDeriv a' (varphiN N k₁) x‖) := by
    intro a' ha'
    have ha2 : a' ≤ 2 := by
      have := Finset.mem_range.mp ha'
      omega
    exact (integrable_iteratedDeriv_varphiN N k₁ a' ha2).const_mul _
  have hF1int : Integrable F1 := by
    rw [hF1]
    exact integrable_finsetSum (Finset.range (i₁ + 1)) htermA
  have htermB : ∀ b' ∈ Finset.range (i₂ + 1), Integrable (fun y : ℝ =>
      (i₂.choose b' : ℝ) * (N : ℝ) ^ ((P.natDegree : ℤ) * (b' : ℤ))
        * ‖iteratedDeriv (i₂ - b') (varphitildeN P.natDegree N k₂) y‖) := by
    intro b' hb'
    have hb2 : i₂ - b' ≤ 2 := by
      have := Finset.mem_range.mp hb'
      omega
    have hcont : Continuous (iteratedDeriv (i₂ - b') (varphitildeN P.natDegree N k₂)) :=
      (contDiff_varphitildeN P.natDegree N k₂).continuous_iteratedDeriv (i₂ - b')
        (by exact_mod_cast hb2)
    exact ((hcont.integrable_of_hasCompactSupport
      (hcs_iteratedDeriv_varphitildeN P.natDegree N k₂ (i₂ - b') hb2)).norm).const_mul _
  have hF2int : Integrable F2 := by
    rw [hF2]
    exact integrable_finsetSum (Finset.range (i₂ + 1)) htermB
  have hF2nonneg : ∀ y : ℝ, 0 ≤ F2 y := by
    intro y
    rw [hF2]
    refine Finset.sum_nonneg (fun b' hb' => ?_)
    have h1 : (0 : ℝ) ≤ (i₂.choose b' : ℝ) := by positivity
    have h2 : (0 : ℝ) ≤ (N : ℝ) ^ ((P.natDegree : ℤ) * (b' : ℤ)) :=
      zpow_nonneg hNpos.le _
    exact mul_nonneg (mul_nonneg h1 h2) (norm_nonneg _)
  have hprodint : Integrable (fun z : ℝ × ℝ => F1 z.1 * F2 z.2) := by
    rw [MeasureTheory.Measure.volume_eq_prod ℝ ℝ]
    exact hF1int.mul_prod hF2int
  have hmajint : Integrable (fun z : ℝ × ℝ => Kc * (F1 z.1 * F2 z.2)) :=
    hprodint.const_mul _
  obtain ⟨hsm, hc⟩ := contDiff_hasCompactSupport_fibreSymbol P N k₁ k₂ α₁ α₂
  have hlhsint : Integrable (fun z : ℝ × ℝ => ‖Work.KMTPlan.A6.dp i₁ i₂ (fun a b =>
      varphiN N k₁ a * varphitildeN P.natDegree N k₂ b * weylAvg P N α₁ α₂ a b) z.1 z.2‖) :=
    (integrable_dp _ i₁ i₂ (hsm.of_le (by exact_mod_cast (by omega : i₁ + i₂ ≤ 4))) hc).norm
  -- 3. the integral estimate
  have h1 : (∫ z : ℝ × ℝ, ‖Work.KMTPlan.A6.dp i₁ i₂ (fun a b => varphiN N k₁ a
      * varphitildeN P.natDegree N k₂ b * weylAvg P N α₁ α₂ a b) z.1 z.2‖)
      ≤ ∫ z : ℝ × ℝ, Kc * (F1 z.1 * F2 z.2) :=
    MeasureTheory.integral_mono hlhsint hmajint hpt
  have hInt : (∫ z : ℝ × ℝ, Kc * (F1 z.1 * F2 z.2))
      = Kc * ((∫ x : ℝ, F1 x) * (∫ y : ℝ, F2 y)) := by
    rw [MeasureTheory.integral_const_mul]
    congr 1
    rw [MeasureTheory.Measure.volume_eq_prod ℝ ℝ]
    exact MeasureTheory.integral_prod_mul F1 F2
  -- 4. the two one-dimensional integrals
  have hIA : (∫ x : ℝ, F1 x) = ∑ a' ∈ Finset.range (i₁ + 1),
      (i₁.choose a' : ℝ) * ((N : ℝ) ^ (a' : ℤ))⁻¹
        * (∫ ξ : ℝ, ‖iteratedDeriv a' (varphiN N k₁) ξ‖) := by
    rw [hF1]
    rw [integral_finsetSum (Finset.range (i₁ + 1)) htermA]
    refine Finset.sum_congr rfl (fun a' ha' => ?_)
    rw [MeasureTheory.integral_const_mul]
  have hIB : (∫ y : ℝ, F2 y) = ∑ b' ∈ Finset.range (i₂ + 1),
      (i₂.choose b' : ℝ) * (N : ℝ) ^ ((P.natDegree : ℤ) * (b' : ℤ))
        * (∫ η : ℝ, ‖iteratedDeriv (i₂ - b') (varphitildeN P.natDegree N k₂) η‖) := by
    rw [hF2]
    rw [integral_finsetSum (Finset.range (i₂ + 1)) htermB]
    refine Finset.sum_congr rfl (fun b' hb' => ?_)
    rw [MeasureTheory.integral_const_mul]
  -- 5. the bounds for the two sums
  set P1 : ℝ := fibBumpCφ P * fibLam₁ N k₁
      * (1 + 1 / (fibLam₁ N k₁ * (N : ℝ))) ^ i₁ with hP1
  set P2 : ℝ := fibBumpCψ P * (fibLam₂ P N k₂) ^ ((1 : ℤ) - (i₂ : ℤ))
      * (1 + fibLam₂ P N k₂ * (N : ℝ) ^ P.natDegree) ^ i₂ with hP2
  set Bx : ℝ := fibLam₂ P N k₂ * (N : ℝ) ^ P.natDegree with hBx
  set Lam2z : ℝ := (fibLam₂ P N k₂) ^ ((1 : ℤ) - (i₂ : ℤ)) with hLam2z
  set Rz : ℝ := (fibR₂ P N k₂) ^ ((1 : ℤ) - (i₂ : ℤ)) with hRz
  have hA' : (∫ x : ℝ, F1 x) ≤ P1 := by
    rw [hIA, hP1]
    exact fibreMass_sumA P N k₁ i₁ hi₁
  have hB' : (∫ y : ℝ, F2 y) ≤ P2 := by
    rw [hIB, hP2, hLam2z, hBx]
    exact fibreMass_sumB P N k₂ i₂ hi₂
  have hAB : (∫ x : ℝ, F1 x) * (∫ y : ℝ, F2 y) ≤ P1 * P2 := by
    refine mul_le_mul hA' hB' (MeasureTheory.integral_nonneg hF2nonneg) ?_
    rw [hP1]
    have h1 := (fibBumpCφ_pos P).le
    have h2 := (fibLam₁_pos N k₁).le
    positivity
  have har : (1 + 1 / (fibLam₁ N k₁ * (N : ℝ))) ^ i₁
      * (1 + Bx) ^ i₂ * Lam2z ≤ 64 * max Bx 1 * Rz := by
    rw [hBx, hLam2z, hRz]
    exact fibreMass_arith_core P N k₁ k₂ hN i₁ i₂ hi₁ hi₂
  -- 6. the final arithmetic
  have hKcnonneg : 0 ≤ Kc := by
    rw [hKc]
    have h1 := (fibM0C_pos P).le
    have h2 : (0 : ℝ) ≤ (N : ℝ) ^ ((i₁ : ℤ) - 1) := zpow_nonneg hNpos.le _
    have h3 : (0 : ℝ) ≤ (1 + (Work.A7.Sval P k₁ k₂) ^ 2 / (N : ℝ)) := by positivity
    exact mul_nonneg (mul_nonneg (mul_nonneg h1 (sq_nonneg _)) h3) h2
  set Dc : ℝ := (q : ℝ) ^ 2 * (1 + (Work.A7.Sval P k₁ k₂) ^ 2 / (N : ℝ)) with hDc
  set Cn : ℝ := fibM0C P * fibBumpCφ P * fibBumpCψ P * fibLam₁ N k₁
      * (N : ℝ) ^ ((i₁ : ℤ) - 1) with hCn
  have hDcnonneg : 0 ≤ Dc := by
    rw [hDc]
    have : (0 : ℝ) ≤ 1 + (Work.A7.Sval P k₁ k₂) ^ 2 / (N : ℝ) := by positivity
    positivity
  have hCnnonneg : 0 ≤ Cn := by
    rw [hCn]
    have h1 := (fibM0C_pos P).le
    have h2 := (fibBumpCφ_pos P).le
    have h3 := (fibBumpCψ_pos P).le
    have h4 := (fibLam₁_pos N k₁).le
    have h5 : (0 : ℝ) ≤ (N : ℝ) ^ ((i₁ : ℤ) - 1) := zpow_nonneg hNpos.le _
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg h1 h2) h3) h4) h5
  have hkey : Cn * (Dc * ((1 + 1 / (fibLam₁ N k₁ * (N : ℝ))) ^ i₁ * (1 + Bx) ^ i₂ * Lam2z))
      ≤ Cn * (Dc * (64 * max Bx 1 * Rz)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left har hDcnonneg) hCnnonneg
  have hleft : Kc * (P1 * P2)
      = Cn * (Dc * ((1 + 1 / (fibLam₁ N k₁ * (N : ℝ))) ^ i₁ * (1 + Bx) ^ i₂ * Lam2z)) := by
    rw [hKc, hCn, hDc, hP1, hP2, hBx, hLam2z]
    ring
  have hright : fibHbdC P N q k₁ k₂ * (N : ℝ) ^ ((i₁ : ℤ) - 1) * Rz
      = Cn * (Dc * (64 * max Bx 1 * Rz)) := by
    rw [hCn, hDc, hBx, hRz, fibHbdC]
    ring
  calc (∫ z : ℝ × ℝ, ‖Work.KMTPlan.A6.dp i₁ i₂ (fun a b => varphiN N k₁ a
        * varphitildeN P.natDegree N k₂ b * weylAvg P N α₁ α₂ a b) z.1 z.2‖)
      ≤ ∫ z : ℝ × ℝ, Kc * (F1 z.1 * F2 z.2) := h1
    _ = Kc * ((∫ x : ℝ, F1 x) * (∫ y : ℝ, F2 y)) := hInt
    _ ≤ Kc * (P1 * P2) := mul_le_mul_of_nonneg_left hAB hKcnonneg
    _ = Cn * (Dc * ((1 + 1 / (fibLam₁ N k₁ * (N : ℝ))) ^ i₁ * (1 + Bx) ^ i₂ * Lam2z)) := hleft
    _ ≤ Cn * (Dc * (64 * max Bx 1 * Rz)) := hkey
    _ = fibHbdC P N q k₁ k₂ * (N : ℝ) ^ ((i₁ : ℤ) - 1) * Rz := hright.symm

end

end Work.KMTAreas.A7
