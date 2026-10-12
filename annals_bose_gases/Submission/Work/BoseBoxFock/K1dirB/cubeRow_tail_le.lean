import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBoxFock.K1dirBDefs
import Submission.Work.BoseBoxFock.L1Tails.kernelTail
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.K1dirB.cubeRow_tail_le`

The **cube-row tail bound**: the lattice sum over the cube `[-N,N]³` of the cut-off kernel row
`(1 − ζ_{Λ_N}(κ_n))·Ŵ(κ_n)·Ȟ_n` is bounded by the Cauchy–Schwarz product

    √(τb ℓ³) · √(ℓ⁶ D)

of the two budgets supplied by the caller: `τb` controls the Coulomb tail of `Ŵ` above the
threshold `Λ` (`(ℓ³)⁻¹ Σ ‖Ŵ(κ_n)‖²/‖κ_n‖² ≤ τb` on every finset of labels above `Λ`) and `D`
controls the sharp lattice budget `Σ ‖κ_n‖²‖Ȟ_n‖² ≤ ℓ⁶ D`.

## Proof

The cut-off `ζ_Λ(k) = f_u(‖k‖/Λ)` equals `1` on the ball of radius `Λ`, so the coefficient
`1 − ζ_{Λ_N}(κ_n)` vanishes for every cube label with `‖κ_n‖ < Λ` — and also at the origin
(`‖κ_0‖ = 0`, since `Λ ≤ uvRad ℓ N` and `ζ(0) = 1`).  Hence the sum over the cube is the sum over
the finset `T` of labels with `Λ ≤ ‖κ_n‖` and `n ≠ 0`.  On `T` the momentum is nonzero, so the
pointwise identity `(‖Ŵ‖/‖κ‖)·(‖κ‖‖Ȟ‖) = ‖Ŵ‖‖Ȟ‖` holds, and Cauchy–Schwarz
(`Finset.sum_mul_sq_le_sq_mul_sq`) with the two granted budgets gives the claim.
-/

namespace Work.BoseBoxFock.K1dirB

open scoped BigOperators

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The norm of a real number seen in `ℂ` is its absolute value. -/
lemma cubeRowTail_norm_ofReal (x : ℝ) : ‖((x : ℝ) : ℂ)‖ = |x| := by
  simp

/-- The cut-off radius `uvRad ℓ N` is nonnegative. -/
lemma cubeRowTail_uvRad_nonneg {ℓ : ℝ} (hℓ : 0 < ℓ) (N : ℕ) :
    0 ≤ Work.BoseBoxFock.uvRad ℓ N := by
  rw [Work.BoseBoxFock.uvRad]
  positivity

/-- `uvCut` at the radius `uvRad ℓ N` equals `1` on the closed ball of that radius (for every
sign of the radius). -/
lemma cubeRowTail_uvCut_eq_one {ℓ : ℝ} (fu : Work.BoseBoxFix.LowCut) {N : ℕ} {k : E3}
    (hk : ‖k‖ ≤ Work.BoseBoxFock.uvRad ℓ N) :
    Work.BoseBoxFock.uvCut fu (Work.BoseBoxFock.uvRad ℓ N) k = 1 := by
  rw [Work.BoseBoxFock.uvCut]
  refine fu.one _ ?_
  rcases lt_trichotomy (Work.BoseBoxFock.uvRad ℓ N) 0 with h | h | h
  · rw [show ‖k‖ = 0 from le_antisymm (le_trans hk h.le) (norm_nonneg _), zero_div]
    norm_num
  · rw [h, div_zero]
    norm_num
  · exact (div_le_one h).mpr hk

/-- **Cauchy–Schwarz on a zero-free finset**: the `Λ`-free core of the cube-row tail bound.  From
the two granted budgets on `T` (with every momentum of `T` nonzero) the product sum is bounded by
`√(τ ℓ³)·√(ℓ⁶ D)`. -/
lemma cubeRowTail_tailCS {ℓ τ D : ℝ} (hℓ : 0 < ℓ)
    {W : E3 → ℝ} {H : E3 → E3 → ℂ} {T : Finset (Fin 3 → ℤ)}
    (hτ : (ℓ ^ 3)⁻¹ * ∑ n ∈ T,
        ‖Submission.BoseGases.kinFT (fun y => ((W y : ℝ) : ℂ))
          (Work.BoseBoxFock.kmomInt ℓ n)‖ ^ 2
          / ‖Work.BoseBoxFock.kmomInt ℓ n‖ ^ 2 ≤ τ)
    (hD : ∑ n ∈ T, ‖Work.BoseBoxFock.kmomInt ℓ n‖ ^ 2
        * ‖Work.BoseBoxFock.L1Tails.hPair ℓ H n‖ ^ 2 ≤ ℓ ^ 6 * D)
    (h0 : ∀ n ∈ T, n ≠ 0) :
    ∑ n ∈ T, ‖Submission.BoseGases.kinFT (fun y => ((W y : ℝ) : ℂ))
          (Work.BoseBoxFock.kmomInt ℓ n)‖
        * ‖Work.BoseBoxFock.L1Tails.hPair ℓ H n‖
      ≤ Real.sqrt (τ * ℓ ^ 3) * Real.sqrt (ℓ ^ 6 * D) := by
  have hne : ∀ n ∈ T, ‖Work.BoseBoxFock.kmomInt ℓ n‖ ≠ 0 :=
    fun n hn => ne_of_gt (Work.BoseBoxFock.L1Tails.norm_kappaL_pos hℓ (h0 n hn))
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq T
    (fun n => ‖Submission.BoseGases.kinFT (fun y => ((W y : ℝ) : ℂ))
        (Work.BoseBoxFock.kmomInt ℓ n)‖ / ‖Work.BoseBoxFock.kmomInt ℓ n‖)
    (fun n => ‖Work.BoseBoxFock.kmomInt ℓ n‖
        * ‖Work.BoseBoxFock.L1Tails.hPair ℓ H n‖)
  have hpt : ∀ n ∈ T, ‖Submission.BoseGases.kinFT (fun y => ((W y : ℝ) : ℂ))
        (Work.BoseBoxFock.kmomInt ℓ n)‖ / ‖Work.BoseBoxFock.kmomInt ℓ n‖
        * (‖Work.BoseBoxFock.kmomInt ℓ n‖ * ‖Work.BoseBoxFock.L1Tails.hPair ℓ H n‖)
      = ‖Submission.BoseGases.kinFT (fun y => ((W y : ℝ) : ℂ))
          (Work.BoseBoxFock.kmomInt ℓ n)‖ * ‖Work.BoseBoxFock.L1Tails.hPair ℓ H n‖ := by
    intro n hn
    have hk : ‖Work.BoseBoxFock.kmomInt ℓ n‖ ≠ 0 := hne n hn
    field_simp
  have hu : ∑ n ∈ T, (‖Submission.BoseGases.kinFT (fun y => ((W y : ℝ) : ℂ))
        (Work.BoseBoxFock.kmomInt ℓ n)‖ / ‖Work.BoseBoxFock.kmomInt ℓ n‖) ^ 2
      ≤ τ * ℓ ^ 3 := by
    have h := hτ
    rw [inv_mul_le_iff₀ (pow_pos hℓ 3), mul_comm (ℓ ^ 3) τ] at h
    simpa only [div_pow] using h
  have hv : ∑ n ∈ T, (‖Work.BoseBoxFock.kmomInt ℓ n‖
        * ‖Work.BoseBoxFock.L1Tails.hPair ℓ H n‖) ^ 2 ≤ ℓ ^ 6 * D := by
    simpa only [mul_pow] using hD
  have hX : 0 ≤ ∑ n ∈ T, ‖Submission.BoseGases.kinFT (fun y => ((W y : ℝ) : ℂ))
      (Work.BoseBoxFock.kmomInt ℓ n)‖ ^ 2 / ‖Work.BoseBoxFock.kmomInt ℓ n‖ ^ 2 :=
    Finset.sum_nonneg (fun n _ => div_nonneg (sq_nonneg _) (sq_nonneg _))
  have hτ0 : 0 ≤ τ := le_trans (mul_nonneg (inv_nonneg.mpr (pow_nonneg hℓ.le 3)) hX) hτ
  have hτℓ3 : 0 ≤ τ * ℓ ^ 3 := mul_nonneg hτ0 (pow_nonneg hℓ.le 3)
  have hsq : (∑ n ∈ T, ‖Submission.BoseGases.kinFT (fun y => ((W y : ℝ) : ℂ))
          (Work.BoseBoxFock.kmomInt ℓ n)‖
        * ‖Work.BoseBoxFock.L1Tails.hPair ℓ H n‖) ^ 2
      ≤ (τ * ℓ ^ 3) * (ℓ ^ 6 * D) := by
    have h₁ : ∑ n ∈ T, ‖Submission.BoseGases.kinFT (fun y => ((W y : ℝ) : ℂ))
          (Work.BoseBoxFock.kmomInt ℓ n)‖ / ‖Work.BoseBoxFock.kmomInt ℓ n‖
          * (‖Work.BoseBoxFock.kmomInt ℓ n‖ * ‖Work.BoseBoxFock.L1Tails.hPair ℓ H n‖)
        = ∑ n ∈ T, ‖Submission.BoseGases.kinFT (fun y => ((W y : ℝ) : ℂ))
            (Work.BoseBoxFock.kmomInt ℓ n)‖ * ‖Work.BoseBoxFock.L1Tails.hPair ℓ H n‖ :=
      Finset.sum_congr rfl (fun n hn => hpt n hn)
    rw [← h₁]
    refine le_trans hcs ?_
    exact mul_le_mul hu hv (Finset.sum_nonneg (fun n _ => sq_nonneg _)) hτℓ3
  calc ∑ n ∈ T, ‖Submission.BoseGases.kinFT (fun y => ((W y : ℝ) : ℂ))
          (Work.BoseBoxFock.kmomInt ℓ n)‖ * ‖Work.BoseBoxFock.L1Tails.hPair ℓ H n‖
      ≤ Real.sqrt ((τ * ℓ ^ 3) * (ℓ ^ 6 * D)) := Real.le_sqrt_of_sq_le hsq
    _ = Real.sqrt (τ * ℓ ^ 3) * Real.sqrt (ℓ ^ 6 * D) := Real.sqrt_mul hτℓ3 _

theorem cubeRow_tail_le {ℓ : ℝ} (hℓ : 0 < ℓ) (fu : Work.BoseBoxFix.LowCut) {N : ℕ} (hN : 1 ≤ N)
    {Λ τb D : ℝ} (hΛ : Λ ≤ Work.BoseBoxFock.uvRad ℓ N)
    {Wb : EuclideanSpace ℝ (Fin 3) → ℝ}
    {H : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℂ}
    (hτb : ∀ S : Finset (Fin 3 → ℤ),
      (∀ n ∈ S, Λ ≤ ‖Work.BoseBoxFock.kmomInt ℓ n‖) →
      ((ℓ) ^ 3)⁻¹ * ∑ n ∈ S,
        ‖Submission.BoseGases.kinFT (fun y => ((Wb y : ℝ) : ℂ))
          (Work.BoseBoxFock.kmomInt ℓ n)‖ ^ 2
          / ‖Work.BoseBoxFock.kmomInt ℓ n‖ ^ 2 ≤ τb)
    (hD : ∀ T : Finset (Fin 3 → ℤ),
      ∑ n ∈ T, ‖Work.BoseBoxFock.kmomInt ℓ n‖ ^ 2
        * ‖Work.BoseBoxFock.L1Tails.hPair ℓ H n‖ ^ 2 ≤ ℓ ^ 6 * D) :
    ‖∑ n ∈ Work.BoseRowQ2.cube N,
        ((1 - Work.BoseBoxFock.uvCut fu (Work.BoseBoxFock.uvRad ℓ N)
            (Work.BoseBoxFock.kmomInt ℓ n) : ℝ) : ℂ)
          * Submission.BoseGases.kinFT (fun y => ((Wb y : ℝ) : ℂ))
              (Work.BoseBoxFock.kmomInt ℓ n)
          * Work.BoseBoxFock.L1Tails.hPair ℓ H n‖
      ≤ Real.sqrt (τb * ℓ ^ 3) * Real.sqrt (ℓ ^ 6 * D) := by
  classical
  let kin : (Fin 3 → ℤ) → ℂ := fun n =>
    Submission.BoseGases.kinFT (fun y => ((Wb y : ℝ) : ℂ)) (Work.BoseBoxFock.kmomInt ℓ n)
  let hp : (Fin 3 → ℤ) → ℂ := fun n => Work.BoseBoxFock.L1Tails.hPair ℓ H n
  let cf : (Fin 3 → ℤ) → ℂ := fun n =>
    (((1 - Work.BoseBoxFock.uvCut fu (Work.BoseBoxFock.uvRad ℓ N)
      (Work.BoseBoxFock.kmomInt ℓ n) : ℝ)) : ℂ)
  change ‖∑ n ∈ Work.BoseRowQ2.cube N, cf n * kin n * hp n‖
      ≤ Real.sqrt (τb * ℓ ^ 3) * Real.sqrt (ℓ ^ 6 * D)
  -- the surviving labels: cube labels above the threshold and away from the origin
  set S : Finset (Fin 3 → ℤ) :=
    (Work.BoseRowQ2.cube N).filter (fun n => Λ ≤ ‖Work.BoseBoxFock.kmomInt ℓ n‖) with hSdef
  set T : Finset (Fin 3 → ℤ) := S.filter (fun n => n ≠ 0) with hTdef
  have hSsub : ∀ n ∈ S, Λ ≤ ‖Work.BoseBoxFock.kmomInt ℓ n‖ := by
    intro n hn
    rw [hSdef, Finset.mem_filter] at hn
    exact hn.2
  have hTmem : ∀ n ∈ T, n ∈ S ∧ n ≠ 0 := by
    intro n hn
    rw [hTdef, Finset.mem_filter] at hn
    exact hn
  -- the cut-off coefficient vanishes below the cut-off radius
  have hcoeff : ∀ n ∈ Work.BoseRowQ2.cube N, ¬ (Λ ≤ ‖Work.BoseBoxFock.kmomInt ℓ n‖) →
      cf n = 0 := by
    intro n _ hn
    have hkn : ‖Work.BoseBoxFock.kmomInt ℓ n‖ ≤ Work.BoseBoxFock.uvRad ℓ N :=
      le_trans (lt_of_not_ge hn).le hΛ
    dsimp only [cf]
    rw [cubeRowTail_uvCut_eq_one fu hkn]
    norm_num
  -- the cut-off coefficient also vanishes at the origin
  have hcoeff0 : cf 0 = 0 := by
    dsimp only [cf]
    have hroot : Work.BoseBoxFock.kmomInt ℓ (0 : Fin 3 → ℤ) = 0 :=
      (Work.BoseBoxFock.L1Tails.kappaL_eq_zero_iff (ne_of_gt hℓ) 0).mpr rfl
    rw [cubeRowTail_uvCut_eq_one fu
      (by rw [hroot, norm_zero]; exact cubeRowTail_uvRad_nonneg hℓ N)]
    norm_num
  -- the sum over the cube is the sum over `S`
  have hSum1 : ∑ n ∈ Work.BoseRowQ2.cube N, cf n * kin n * hp n
      = ∑ n ∈ S, cf n * kin n * hp n := by
    rw [hSdef, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun n hn => ?_)
    by_cases h : Λ ≤ ‖Work.BoseBoxFock.kmomInt ℓ n‖
    · rw [if_pos h]
    · rw [if_neg h, hcoeff n hn h, zero_mul, zero_mul]
  -- and the origin contributes nothing, so `S` can be replaced by `T`
  have hSum2 : ∑ n ∈ S, cf n * kin n * hp n = ∑ n ∈ T, cf n * kin n * hp n := by
    rw [hTdef]
    conv_rhs => rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun n hn => ?_)
    by_cases h : n = 0
    · rw [h, if_neg (by simp), hcoeff0]
      ring
    · rw [if_pos h]
  -- the coefficient is bounded by `1`, so the summand is dominated by `‖Ŵ‖‖Ȟ‖`
  have hnorm : ‖∑ n ∈ T, cf n * kin n * hp n‖ ≤ ∑ n ∈ T, ‖kin n‖ * ‖hp n‖ := by
    refine le_trans (norm_sum_le T (fun n => cf n * kin n * hp n))
      (Finset.sum_le_sum (fun n _ => ?_))
    have hc : ‖cf n‖ ≤ 1 := by
      have hcn : ‖cf n‖ = |(1 - Work.BoseBoxFock.uvCut fu (Work.BoseBoxFock.uvRad ℓ N)
          (Work.BoseBoxFock.kmomInt ℓ n) : ℝ)| := by
        dsimp only [cf]
        exact cubeRowTail_norm_ofReal _
      rw [hcn, abs_le]
      refine ⟨?_, ?_⟩
      · have h1 := Work.BoseBoxFix.LowCut.le_one fu
          (‖Work.BoseBoxFock.kmomInt ℓ n‖ / Work.BoseBoxFock.uvRad ℓ N)
        rw [Work.BoseBoxFock.uvCut]
        linarith
      · have h1 := Work.BoseBoxFix.LowCut.nonneg fu
          (‖Work.BoseBoxFock.kmomInt ℓ n‖ / Work.BoseBoxFock.uvRad ℓ N)
        rw [Work.BoseBoxFock.uvCut]
        linarith
    calc ‖cf n * kin n * hp n‖ = ‖cf n‖ * (‖kin n‖ * ‖hp n‖) := by
          rw [norm_mul, norm_mul]; ring
      _ ≤ 1 * (‖kin n‖ * ‖hp n‖) := mul_le_mul_of_nonneg_right hc (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ = ‖kin n‖ * ‖hp n‖ := one_mul _
  -- the two budgets, restricted to `T`
  have hτT : (ℓ ^ 3)⁻¹ * ∑ n ∈ T, ‖kin n‖ ^ 2 / ‖Work.BoseBoxFock.kmomInt ℓ n‖ ^ 2 ≤ τb := by
    refine le_trans ?_ (hτb S hSsub)
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr (pow_nonneg hℓ.le 3))
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun n hn => (hTmem n hn).1) ?_
    intro n _ _
    exact div_nonneg (sq_nonneg _) (sq_nonneg _)
  have hCS : ∑ n ∈ T, ‖kin n‖ * ‖hp n‖
      ≤ Real.sqrt (τb * ℓ ^ 3) * Real.sqrt (ℓ ^ 6 * D) :=
    cubeRowTail_tailCS hℓ hτT (hD T) (fun n hn => (hTmem n hn).2)
  -- assembly
  calc ‖∑ n ∈ Work.BoseRowQ2.cube N, cf n * kin n * hp n‖
      = ‖∑ n ∈ T, cf n * kin n * hp n‖ := by rw [hSum1, hSum2]
    _ ≤ ∑ n ∈ T, ‖kin n‖ * ‖hp n‖ := hnorm
    _ ≤ Real.sqrt (τb * ℓ ^ 3) * Real.sqrt (ℓ ^ 6 * D) := hCS

end Work.BoseBoxFock.K1dirB
