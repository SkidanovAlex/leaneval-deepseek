/-
Copyright: work module for the Elgindi finite-time singularity project.

# The angular machinery of the open-quadrant estimate, under a private namespace

The open-quadrant statement `Fstar_Hk_le_open` must not import
`Submission.Work.FTS.EllipticEst.Fstar_Hk_le`: that module and
`Submission.Work.FTS.EllipticEst.OpenQDefs` both define
`Work.FTS.EllipticEst.integrableOn_zSummand_nbhd` (the closed- resp. open-quadrant versions of one
lemma), so the two modules cannot be imported together.

The few *purely angular* pieces of `Fstar_Hk_le` which the open-quadrant proof needs are
therefore restated here under the namespace `Work.FTS.EllipticEst.FstarHkOpen`:

* `sin_two_nonneg`, `sin_two_le_one`, `abs_sinCos2_le_one` : elementary bounds on `Iθ`;
* `sinProf_eq_zero_of_sin_eq_zero`, `smoothSlice_sinProf`, `sinProf_sq_mul_rpow_le`,
  `angK`, `angK_pos`, `angK_bound` : `(D_θ^i (sin 2θ))² sin(2θ)^{-γ} ≤ angK i` on `Iθ`
  for `γ ∈ [1,2]` (from `Work.Elliptic.SinSliceBounds`);
* `zTerm_eq_on`, `mixedTerm_eq_on` : the pointwise evaluation of the summands of the
  `H^k`-integrand of `F_*(F)·sin 2θ`;
* `Uj`, `angKsum`, `hkConst` and their elementary properties : the constants of the estimate.

The proofs are those of `Fstar_Hk_le`.  Everything here is `sorry`-free.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.SmoothCompact_Aux
import Submission.Work.Elliptic.Defs
import Submission.Work.Elliptic.SinSliceBounds
import Submission.Work.FTS.EllipticEst.FstarHkAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst

namespace FstarHkOpen

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

/-! ## Elementary angular facts -/

/-- `sin(2θ) ≥ 0` on `Iθ = [0,π/2]`. -/
theorem sin_two_nonneg {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- `sin(2θ) ≤ 1`. -/
theorem sin_two_le_one (θ : ℝ) : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _

/-- The measure of `Iθ` is `π/2`. -/
theorem integral_Iθ_one : ∫ θ in Work.Spaces.Iθ, (1 : ℝ) = π / 2 := by
  rw [MeasureTheory.setIntegral_const]
  simp only [smul_eq_mul, mul_one]
  rw [MeasureTheory.measureReal_def, Work.Spaces.Iθ, Real.volume_Icc,
    ENNReal.toReal_ofReal (by linarith [Real.pi_pos])]
  ring

/-- A function on `Iθ` bounded by a constant is integrable there. -/
theorem integrableOn_Iθ_of_abs_le {f : ℝ → ℝ}
    (hm : AEStronglyMeasurable f (volume.restrict Work.Spaces.Iθ)) {C : ℝ}
    (h : ∀ θ ∈ Work.Spaces.Iθ, |f θ| ≤ C) : IntegrableOn f Work.Spaces.Iθ := by
  refine Integrable.mono'
    (MeasureTheory.integrableOn_const (s := Work.Spaces.Iθ) (C := C)
      (by rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top)) hm ?_
  rw [Work.Spaces.Iθ, ae_restrict_iff' measurableSet_Icc]
  exact Eventually.of_forall fun θ hθ => by simpa [Real.norm_eq_abs] using h θ hθ

/-- `sinθ cos²θ` vanishes wherever `sin 2θ` does. -/
theorem sinCos2_eq_zero_of_sin_two_eq_zero {θ : ℝ} (h : Real.sin (2 * θ) = 0) :
    Work.Elliptic.sinCos2 θ = 0 := by
  have h2 : Real.sin θ * Real.cos θ = 0 := by
    have h3 : 2 * (Real.sin θ * Real.cos θ) = 0 := by
      rw [← h, Real.sin_two_mul]; ring
    exact (mul_eq_zero.mp h3).resolve_left (by norm_num)
  rcases mul_eq_zero.mp h2 with h3 | h3
  · simp [Work.Elliptic.sinCos2, h3]
  · simp [Work.Elliptic.sinCos2, h3]


/-- `sinProf i` vanishes wherever `sin 2θ` does. -/
theorem sinProf_eq_zero_of_sin_eq_zero (i : ℕ) {θ : ℝ} (h : Real.sin (2 * θ) = 0) :
    sinProf i θ = 0 := by
  induction i with
  | zero => simpa [sinProf] using h
  | succ n _ =>
      show Work.Spaces.DthIter (n + 1) (fun _ θ' => Real.sin (2 * θ')) 0 θ = 0
      rw [Work.Spaces.DthIter_succ]
      simp only [Work.Spaces.Dth, Work.Spaces.pth]
      rw [h, zero_mul]

/-- `sinProf i` is a smooth function of the angle on a neighbourhood of `[0,π/2]`. -/
theorem smoothSlice_sinProf (i : ℕ) : Work.Elliptic.SmoothSlice (fun θ => sinProf i θ) := by
  have hbase : Work.Spaces.SmoothNbhd (fun z θ => Real.sin (2 * θ)) := by
    rw [Work.Spaces.SmoothNbhd]
    fun_prop
  have hsm := Work.Spaces.smoothNbhd_DthIter hbase i
  rw [Work.Elliptic.SmoothSlice]
  have hmap : Set.MapsTo (fun θ : ℝ => ((0 : ℝ), θ)) (Set.Ioo (-1) (π / 2 + 1))
      (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (π / 2 + 1)) := fun θ hθ => ⟨by norm_num, hθ⟩
  have hcomp := hsm.comp ((contDiffOn_const (c := (0 : ℝ))).prodMk contDiffOn_id) hmap
  simpa [sinProf, Function.uncurry, Function.comp_def] using hcomp

/-- **The angular bound.**  `(D_θ^i (sin 2θ))² sin(2θ)^{-γ}` is bounded on `Iθ` by a
constant depending only on `i`, uniformly in `γ ∈ [1,2]`. -/
theorem sinProf_sq_mul_rpow_le (i : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (γ : ℝ), 1 ≤ γ → γ ≤ 2 → ∀ θ ∈ Work.Spaces.Iθ,
      (sinProf i θ) ^ 2 * (Real.sin (2 * θ)) ^ (-γ) ≤ K := by
  obtain ⟨C, hCpos, hC, -, -, -⟩ :=
    Work.Elliptic.SinSliceBounds (fun θ => sinProf i θ) (smoothSlice_sinProf i)
      (sinProf_eq_zero_of_sin_eq_zero i (by norm_num))
      (sinProf_eq_zero_of_sin_eq_zero i (by rw [show 2 * (π / 2) = π by ring, Real.sin_pi]))
  refine ⟨max 1 (C ^ 2), lt_max_of_lt_left one_pos, ?_⟩
  intro γ hγ1 hγ2 θ hθ
  have hs0 : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg hθ
  have hs1 : Real.sin (2 * θ) ≤ 1 := sin_two_le_one θ
  have h2γ : 0 ≤ 2 - γ := by linarith
  have hsle : Real.sin (2 * θ) ^ (2 - γ) ≤ 1 := Real.rpow_le_one hs0 hs1 h2γ
  have hpow : 0 ≤ (Real.sin (2 * θ)) ^ (-γ) := Real.rpow_nonneg hs0 _
  by_cases hzero : Real.sin (2 * θ) = 0
  · rw [sinProf_eq_zero_of_sin_eq_zero i hzero, hzero,
      Real.zero_rpow (by linarith : (-γ) ≠ 0)]
    rw [zero_pow (by norm_num : 2 ≠ 0), zero_mul]
    linarith [le_max_left (1 : ℝ) (C ^ 2)]
  · have hspos : 0 < Real.sin (2 * θ) := lt_of_le_of_ne hs0 (Ne.symm hzero)
    have hθ0 : 0 < θ := by
      rcases eq_or_lt_of_le hθ.1 with h | h
      · exact absurd (by rw [← h]; norm_num) hzero
      · exact h
    have hθπ : θ < π / 2 := by
      rcases lt_or_eq_of_le hθ.2 with h | h
      · exact h
      · exact absurd (by rw [h]; rw [show 2 * (π / 2) = π by ring, Real.sin_pi]) hzero
    have hb := hC θ ⟨hθ0, hθπ⟩
    have hsq : (sinProf i θ) ^ 2 ≤ (C * Real.sin (2 * θ)) ^ 2 := by
      have h1 : |sinProf i θ| ^ 2 ≤ (C * Real.sin (2 * θ)) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) hb 2
      rwa [sq_abs] at h1
    have hstep : (sinProf i θ) ^ 2 * (Real.sin (2 * θ)) ^ (-γ)
        ≤ (C * Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-γ) :=
      mul_le_mul_of_nonneg_right hsq hpow
    have hmain : (C * Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-γ) ≤ C ^ 2 := by
      have hsplit : (Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-γ)
          = (Real.sin (2 * θ)) ^ (2 - γ) := by
        have hcast : (Real.sin (2 * θ)) ^ (2 : ℝ) = (Real.sin (2 * θ)) ^ 2 :=
          Real.rpow_natCast (Real.sin (2 * θ)) 2
        rw [← hcast, ← Real.rpow_add hspos (2 : ℝ) (-γ)]
        congr 1
      calc (C * Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-γ)
          = C ^ 2 * ((Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-γ)) := by ring
        _ = C ^ 2 * (Real.sin (2 * θ)) ^ (2 - γ) := by rw [hsplit]
        _ ≤ C ^ 2 * 1 := mul_le_mul_of_nonneg_left hsle (sq_nonneg C)
        _ = C ^ 2 := by ring
    exact le_trans hstep (le_trans hmain (le_max_right 1 (C ^ 2)))

/-- The angular constant of the estimate: `angK i` bounds
`(D_θ^i (sin 2θ))² sin(2θ)^{-γ}` on `Iθ` for every `γ ∈ [1,2]`. -/
noncomputable def angK (i : ℕ) : ℝ := Classical.choose (sinProf_sq_mul_rpow_le i)

theorem angK_pos (i : ℕ) : 0 < angK i := (Classical.choose_spec (sinProf_sq_mul_rpow_le i)).1

theorem angK_bound (i : ℕ) (γ : ℝ) (h1 : 1 ≤ γ) (h2 : γ ≤ 2) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    (sinProf i θ) ^ 2 * (Real.sin (2 * θ)) ^ (-γ) ≤ angK i :=
  (Classical.choose_spec (sinProf_sq_mul_rpow_le i)).2 γ h1 h2 θ hθ

theorem abs_sinCos2_le_one {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Elliptic.sinCos2 θ| ≤ 1 := by
  have hsin : |Real.sin θ| ≤ 1 := abs_le.mpr ⟨Real.neg_one_le_sin θ, Real.sin_le_one θ⟩
  have hcos : |Real.cos θ| ≤ 1 := abs_le.mpr ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩
  have hcos2 : Real.cos θ ^ 2 ≤ 1 := by
    have h := pow_le_pow_left₀ (abs_nonneg (Real.cos θ)) hcos 2
    rw [sq_abs] at h
    simpa using h
  have hcos2nn : 0 ≤ Real.cos θ ^ 2 := sq_nonneg _
  calc |Work.Elliptic.sinCos2 θ| = |Real.sin θ| * Real.cos θ ^ 2 := by
        rw [Work.Elliptic.sinCos2, abs_mul, abs_of_nonneg hcos2nn]
    _ ≤ 1 := by nlinarith [hsin, hcos2, abs_nonneg (Real.sin θ)]


/-- The pure `D_z`-summand of the `H^k`-integrand of `F_*·sin 2θ`. -/
theorem zTerm_eq_on (Ψ : ℝ) (z : ℝ) : ∀ θ ∈ Work.Spaces.Iθ,
    (Ψ * Real.sin (2 * θ) * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      = Ψ ^ 2 * (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.eta) := by
  intro θ hθ
  have hs0 : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg hθ
  have he : Work.Spaces.eta / 2 ≠ 0 := by rw [Work.Spaces.eta]; norm_num
  have he2 : 2 - Work.Spaces.eta ≠ 0 := by rw [Work.Spaces.eta]; norm_num
  by_cases hs : Real.sin (2 * θ) = 0
  · rw [hs, Real.zero_rpow he, div_zero, Real.zero_rpow he2]
    ring
  · have hspos : 0 < Real.sin (2 * θ) := lt_of_le_of_ne hs0 (Ne.symm hs)
    have h1 : ((Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
        = (Real.sin (2 * θ)) ^ Work.Spaces.eta := by
      rw [pow_two, ← Real.rpow_add hspos (Work.Spaces.eta / 2) (Work.Spaces.eta / 2)]
      congr 1
      ring
    have h2 : (Real.sin (2 * θ)) ^ 2 / (Real.sin (2 * θ)) ^ Work.Spaces.eta
        = (Real.sin (2 * θ)) ^ (2 - Work.Spaces.eta) := by
      have hcast : (Real.sin (2 * θ)) ^ (2 : ℝ) = (Real.sin (2 * θ)) ^ 2 :=
        Real.rpow_natCast (Real.sin (2 * θ)) 2
      rw [← hcast, ← Real.rpow_sub hspos (2 : ℝ) Work.Spaces.eta]
    calc (Ψ * Real.sin (2 * θ)
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        = Ψ ^ 2 * (Real.sin (2 * θ)) ^ 2
            * ((Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by ring
      _ = Ψ ^ 2 * (Real.sin (2 * θ)) ^ 2
            * ((Work.Spaces.w z) ^ 2 / ((Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2) := by
          rw [div_pow]
      _ = Ψ ^ 2 * (Work.Spaces.w z) ^ 2
            * ((Real.sin (2 * θ)) ^ 2 / (Real.sin (2 * θ)) ^ Work.Spaces.eta) := by
          rw [h1]; ring
      _ = Ψ ^ 2 * (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.eta) := by
          rw [h2]

/-- The mixed summand of the `H^k`-integrand of `F_*·sin 2θ`. -/
theorem mixedTerm_eq_on (α : ℝ) (Ψ z : ℝ) (u : ℝ → ℝ) : ∀ θ ∈ Work.Spaces.Iθ,
    (Ψ * u θ * Work.Spaces.Wt α z θ) ^ 2
      = Ψ ^ 2 * (Work.Spaces.w z) ^ 2
        * ((u θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by
  intro θ hθ
  have hs0 : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg hθ
  have h1 : ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ 2
      = (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
    rw [← Real.rpow_natCast ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) 2,
      ← Real.rpow_mul hs0]
    congr 1
    ring
  simp only [Work.Spaces.Wt, Work.Spaces.wTheta]
  rw [show (Ψ * u θ * (Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2)))) ^ 2
      = Ψ ^ 2 * (u θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ 2 from by ring,
    h1]
  ring

/-! ## The constants of the estimate -/

/-- The `j`-th pure `D_z`-summand of the `H^k`-integrand of `F`, integrated over the angle. -/
def Uj (F : ℝ → ℝ → ℝ) (z : ℝ) (j : ℕ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter j F z θ
    * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2

theorem Uj_nonneg (F : ℝ → ℝ → ℝ) (z : ℝ) (j : ℕ) : 0 ≤ Uj F z j :=
  integral_nonneg fun θ => sq_nonneg _

/-- The sum of the angular constants `angK i`, `i ≤ k`. -/
noncomputable def angKsum (k : ℕ) : ℝ := ∑ i ∈ Finset.range (k + 1), angK i

theorem angKsum_nonneg (k : ℕ) : 0 ≤ angKsum k :=
  Finset.sum_nonneg fun i _ => (angK_pos i).le

/-- The constant of the `H^k`-slice estimate. -/
noncomputable def hkConst (k : ℕ) : ℝ :=
  (π / 2) ^ 2 * (1 + (k + 1)) * (1 + angKsum k) + 1

theorem hkConst_pos (k : ℕ) : 0 < hkConst k := by
  have hK := angKsum_nonneg k
  have hk : (0 : ℝ) ≤ 1 + (k + 1) := by positivity
  have h1 : (0 : ℝ) ≤ 1 + angKsum k := by linarith
  have h2 : (0 : ℝ) ≤ (π / 2) ^ 2 * (1 + (k + 1)) :=
    mul_nonneg (sq_nonneg _) hk
  have h3 : (0 : ℝ) ≤ (π / 2) ^ 2 * (1 + (k + 1)) * (1 + angKsum k) :=
    mul_nonneg h2 h1
  rw [hkConst]
  linarith

end FstarHkOpen

end Work.FTS.EllipticEst
