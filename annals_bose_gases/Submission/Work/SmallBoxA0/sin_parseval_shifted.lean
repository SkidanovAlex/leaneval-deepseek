import Mathlib.Analysis.Fourier.AddCircle
import Submission.Work.SmallBoxA0.fourierCoeff_oddExt
import Submission.Work.SmallBoxA0.memLp_oddExt
import Submission.Work.SmallBoxA0.oddExt_sq_integral
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The shifted sine (Dirichlet) Parseval identity

`Work.SmallBoxA0.sin_parseval_shifted`:

    ∫_{−ℓ/2}^{ℓ/2} F² = ∑_{k≥0} (2/ℓ) (∫_{−ℓ/2}^{ℓ/2} F(x)·sin ((kπ/ℓ)(x + ℓ/2)) dx)² .

This is the completeness of the Dirichlet (sine) basis `sin ((kπ/ℓ)(· + ℓ/2))`,
`k ≥ 1`, of `L²[−ℓ/2, ℓ/2]` — the sine companion of the corpus's Neumann/cosine
Parseval `BoseGases.boxNeumann_parseval`.

Proof route (mirroring `Commons.Analysis.Fourier.cos_basis_parseval`, which used an
*even* extension and the circle Parseval `tsum_sq_fourierCoeffOn`): the *odd*
extension `oddExt F` of `F` (see `SinParsevalDefs`) is an `L²` function on the
period-`2` interval `[−1,1]` whose `n`-th circle Fourier coefficient is
`−I · ∫_{−1/2}^{1/2} F(x)·sin (nπ(x+1/2)) dx` (`fourierCoeff_oddExt`).
Parseval's identity `tsum_sq_fourierCoeffOn` applied to `oddExt F` then gives the
unit-interval (`ℓ = 1`) identity `sin_parseval_unit`, which is rescaled to
arbitrary `ℓ` exactly as `SmallBoxModeParseval.cos_parseval_scaled` rescales the
cosine identity.
-/

set_option autoImplicit false

namespace Work.SmallBoxA0

open MeasureTheory

/-- **The unit sine Parseval identity** on `[−1/2, 1/2]` (the `ℓ = 1` case). -/
theorem sin_parseval_unit {F : ℝ → ℝ} (hF : Continuous F) :
    (∫ x in (-(1 / 2))..(1 / 2), (F x) ^ 2)
      = ∑' k : ℕ, 2 * (∫ x in (-(1 / 2))..(1 / 2),
            F x * Real.sin ((k : ℝ) * Real.pi * (x + 1 / 2))) ^ 2 := by
  have h02 : (-1 : ℝ) < 1 := by norm_num
  have hmemLp : MemLp (fun v : ℝ => ((oddExt F v : ℝ) : ℂ)) 2
      (volume.restrict (Set.Ioc (-1) 1)) := memLp_oddExt hF
  have hpar := tsum_sq_fourierCoeffOn h02 hmemLp
  set c : ℤ → ℝ :=
    fun n => ∫ x in (-(1 / 2))..(1 / 2), F x * Real.sin ((n : ℝ) * Real.pi * (x + 1 / 2))
    with hc
  have hinteq : ∀ i : ℤ, (∫ x in (-(1 / 2))..(1 / 2),
        ((F x : ℂ) * (Real.sin ((i : ℝ) * Real.pi * (x + 1 / 2)) : ℂ))) = ((c i : ℝ) : ℂ) := by
    intro i
    rw [hc]; simp only
    rw [← intervalIntegral.integral_ofReal]
    apply intervalIntegral.integral_congr
    intro x _
    simp only [Complex.ofReal_mul]
  have hLHS : (∑' i : ℤ, ‖fourierCoeffOn h02 (fun v : ℝ => ((oddExt F v : ℝ) : ℂ)) i‖ ^ 2)
      = ∑' i : ℤ, (c i) ^ 2 := by
    apply tsum_congr
    intro i
    rw [fourierCoeff_oddExt hF i, hinteq i, Complex.sq_norm, Complex.normSq_mul,
        Complex.normSq_neg, Complex.normSq_I, one_mul, Complex.normSq_ofReal]
    ring
  have hRHS : ((1 : ℝ) - (-1))⁻¹ • ∫ x in (-1)..1, ‖((oddExt F x : ℝ) : ℂ)‖ ^ 2
      = ∫ x in (-(1 / 2))..(1 / 2), (F x) ^ 2 := by
    rw [show (1 : ℝ) - (-1) = 2 by norm_num]
    have hb : (∫ x in (-1)..1, ‖((oddExt F x : ℝ) : ℂ)‖ ^ 2)
        = ∫ x in (-1)..1, (oddExt F x) ^ 2 := by
      apply intervalIntegral.integral_congr
      intro x _
      simp only []
      rw [Complex.sq_norm, Complex.normSq_ofReal]
      ring
    rw [hb, smul_eq_mul, show (2 : ℝ)⁻¹ = 1 / 2 by norm_num, oddExt_sq_integral hF]
    ring
  have hmain : (∫ x in (-(1 / 2))..(1 / 2), (F x) ^ 2) = ∑' i : ℤ, (c i) ^ 2 := by
    rw [← hRHS, ← hLHS]
    exact hpar.symm
  have hneg : ∀ i : ℤ, c (-i) = -(c i) := by
    intro i
    rw [hc]; simp only
    rw [show (∫ x in (-(1 / 2))..(1 / 2),
            F x * Real.sin (((↑(-i) : ℝ) * Real.pi * (x + 1 / 2))))
          = ∫ x in (-(1 / 2))..(1 / 2),
              -(F x * Real.sin ((↑i : ℝ) * Real.pi * (x + 1 / 2))) from by
        apply intervalIntegral.integral_congr
        intro x _
        simp only []
        rw [show ((↑(-i) : ℝ) * Real.pi * (x + 1 / 2))
              = -((↑i : ℝ) * Real.pi * (x + 1 / 2)) by push_cast; ring, Real.sin_neg]
        ring]
    rw [intervalIntegral.integral_neg]
  have heven : Function.Even (fun i : ℤ => (c i) ^ 2) := by
    intro i
    show (c (-i)) ^ 2 = (c i) ^ 2
    rw [hneg i]; ring
  have hsummable : Summable (fun i : ℤ => (c i) ^ 2) := by
    have h0 : Summable (fun i : ℤ =>
        ‖fourierCoeffOn h02 (fun v : ℝ => ((oddExt F v : ℝ) : ℂ)) i‖ ^ 2) :=
      (hasSum_sq_fourierCoeffOn h02 hmemLp).summable
    refine h0.congr ?_
    intro i
    rw [fourierCoeff_oddExt hF i, hinteq i, Complex.sq_norm, Complex.normSq_mul,
        Complex.normSq_neg, Complex.normSq_I, one_mul, Complex.normSq_ofReal]
    ring
  have hreindex : (∑' i : ℤ, (c i) ^ 2) = (c 0) ^ 2 + 2 * ∑' k : ℕ, (c ((k : ℤ) + 1)) ^ 2 := by
    rw [tsum_int_eq_zero_add_two_mul_tsum_pnat heven hsummable]
    have hpnat : (∑' (n : ℕ+), (c (↑n : ℤ)) ^ 2) = ∑' k : ℕ, (c ((k : ℤ) + 1)) ^ 2 := by
      rw [tsum_pnat_eq_tsum_succ (f := fun m : ℕ => (c (m : ℤ)) ^ 2)]
      simp only [Nat.cast_add, Nat.cast_one]
    rw [hpnat, nsmul_eq_mul]
    ring
  have hc0 : c 0 = 0 := by
    rw [hc]; simp only
    simp [Real.sin_zero]
  have htnat : (∑' k : ℕ, (c k) ^ 2) = ∑' k : ℕ, (c ((k : ℤ) + 1)) ^ 2 := by
    have hs : Summable (fun k : ℕ => (c (k : ℤ)) ^ 2) :=
      hsummable.comp_injective Nat.cast_injective
    rw [hs.tsum_eq_zero_add]
    rw [show ((0 : ℕ) : ℤ) = 0 by norm_num, hc0]
    simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_add]
    apply tsum_congr
    intro k
    simp only [Nat.cast_add, Nat.cast_one]
  have hintnat : (∑' k : ℕ, (∫ x in (-(1 / 2))..(1 / 2),
        F x * Real.sin ((k : ℝ) * Real.pi * (x + 1 / 2))) ^ 2) = ∑' k : ℕ, (c k) ^ 2 := by
    apply tsum_congr
    intro k
    rw [hc]; simp only; push_cast; rfl
  have hfinal : (∑' k : ℕ, 2 * (∫ x in (-(1 / 2))..(1 / 2),
        F x * Real.sin ((k : ℝ) * Real.pi * (x + 1 / 2))) ^ 2)
      = 2 * ∑' k : ℕ, (c ((k : ℤ) + 1)) ^ 2 := by
    rw [tsum_mul_left, hintnat, htnat]
  rw [hmain, hreindex, hc0]
  simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_add]
  exact hfinal.symm

/-- **The shifted sine Parseval identity** (the requested lemma): the Dirichlet
(sine) basis `sin ((kπ/ℓ)(· + ℓ/2))`, `k ≥ 1`, is complete in `L²[−ℓ/2, ℓ/2]`. -/
lemma sin_parseval_shifted {ℓ : ℝ} (hℓ : 0 < ℓ) {F : ℝ → ℝ} (hF : Continuous F) :
    (∫ x in (-(ℓ / 2))..(ℓ / 2), (F x) ^ 2)
      = ∑' k : ℕ, (2 / ℓ) *
          (∫ x in (-(ℓ / 2))..(ℓ / 2),
            F x * Real.sin (((k : ℝ) * Real.pi / ℓ) * (x + ℓ / 2))) ^ 2 := by
  have hne : ℓ ≠ 0 := ne_of_gt hℓ
  have hbase := sin_parseval_unit (F := fun y : ℝ => F (ℓ * y))
    (hF.comp (continuous_const.mul continuous_id))
  have hL : (∫ y in (-(1 / 2))..(1 / 2), (F (ℓ * y)) ^ 2)
      = ℓ⁻¹ * ∫ x in (-(ℓ / 2))..(ℓ / 2), (F x) ^ 2 := by
    have h := intervalIntegral.integral_comp_mul_left (fun x : ℝ => (F x) ^ 2) hne
      (a := -(1 / 2)) (b := 1 / 2) (c := ℓ)
    simp only [smul_eq_mul] at h
    rw [h]
    congr 2 <;> ring
  have hB : ∀ k : ℕ,
      (∫ y in (-(1 / 2))..(1 / 2), F (ℓ * y) * Real.sin ((k : ℝ) * Real.pi * (y + 1 / 2)))
        = ℓ⁻¹ * ∫ x in (-(ℓ / 2))..(ℓ / 2),
            F x * Real.sin (((k : ℝ) * Real.pi / ℓ) * (x + ℓ / 2)) := by
    intro k
    have hpt : (fun y : ℝ => F (ℓ * y) * Real.sin ((k : ℝ) * Real.pi * (y + 1 / 2)))
        = fun y : ℝ => (fun x : ℝ =>
            F x * Real.sin (((k : ℝ) * Real.pi / ℓ) * (x + ℓ / 2))) (ℓ * y) := by
      funext y
      simp only
      congr 1
      have h : (ℓ * y + ℓ / 2) = ℓ * (y + 1 / 2) := by ring
      rw [h]
      field_simp
    rw [hpt]
    have h := intervalIntegral.integral_comp_mul_left
      (fun x : ℝ => F x * Real.sin (((k : ℝ) * Real.pi / ℓ) * (x + ℓ / 2))) hne
      (a := -(1 / 2)) (b := 1 / 2) (c := ℓ)
    simp only [smul_eq_mul] at h
    rw [h]
    congr 2 <;> ring
  have htsum : (∑' k : ℕ, 2 * (∫ y in (-(1 / 2))..(1 / 2),
        F (ℓ * y) * Real.sin ((k : ℝ) * Real.pi * (y + 1 / 2))) ^ 2)
      = (2 / ℓ ^ 2) * ∑' k : ℕ,
          (∫ x in (-(ℓ / 2))..(ℓ / 2),
            F x * Real.sin (((k : ℝ) * Real.pi / ℓ) * (x + ℓ / 2))) ^ 2 := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro k
    rw [hB k]
    ring
  rw [hL] at hbase
  rw [htsum] at hbase
  rw [tsum_mul_left]
  set A : ℝ := ∫ x in (-(ℓ / 2))..(ℓ / 2), (F x) ^ 2 with hA
  set S : ℝ := ∑' k : ℕ, (∫ x in (-(ℓ / 2))..(ℓ / 2),
      F x * Real.sin (((k : ℝ) * Real.pi / ℓ) * (x + ℓ / 2))) ^ 2 with hS
  have key : A = (2 / ℓ) * S := by
    have h1 : ℓ * (ℓ⁻¹ * A) = ℓ * ((2 / ℓ ^ 2) * S) := by rw [hbase]
    have h2 : ℓ * (ℓ⁻¹ * A) = A := by field_simp
    have h3 : ℓ * ((2 / ℓ ^ 2) * S) = (2 / ℓ) * S := by field_simp
    rw [h2, h3] at h1
    exact h1
  exact key

end Work.SmallBoxA0
