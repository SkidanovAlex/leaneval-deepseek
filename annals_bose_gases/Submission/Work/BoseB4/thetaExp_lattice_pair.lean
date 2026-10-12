import Mathlib.Tactic.Have
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Submission.Work.BoseB4.thetaExp_lattice
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB4.thetaExp_lattice_pair` — the general θ-mode orthogonality

The general-pair version of `Work.BoseB4.realIP_thetaExp_thetaFun_of_cell`: for a
`BoxData` on FS's unit cube and dual-lattice momenta `ℓ⁻¹•2πn`, `ℓ⁻¹•2πm`,

    `⟨e^{isx}θ, e^{itx}θ⟩ = ℓ³ δ_{st}`,

i.e. `ℓ³` when `n = m` and `0` otherwise — the hypothesis `horth` of
`Work.BoseB4.exists_gram_jointKernel`.  The proof is the change of variables
`x = ℓy` and the unit-cube Fourier orthogonality, exactly as in the `t = 0` case,
after rewriting `vec m − vec n = vec (m − n)`.
-/

noncomputable section

open scoped BigOperators Pointwise
open MeasureTheory Classical

namespace Work.BoseB4

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

lemma vec_sub (n m : Fin 3 → ℤ) : vec m - vec n = vec (fun i => m i - n i) := by
  ext i
  simp only [vec, PiLp.sub_apply, WithLp.ofLp_toLp]
  push_cast
  ring

lemma vec_injective : Function.Injective vec := by
  intro n m h
  funext i
  have hi : (vec n : ℝ³) i = (vec m : ℝ³) i := by rw [h]
  simp only [vec, WithLp.ofLp_toLp] at hi
  have h2 : (n i : ℝ) = (m i : ℝ) := by
    have := mul_left_cancel₀ (by positivity : (2 * Real.pi : ℝ) ≠ 0) hi
    simpa using this
  exact_mod_cast h2

/-- **The θ-mode orthogonality at lattice momenta, general pair.** -/
theorem realIP_thetaExp_thetaExp_of_cell (B : BoxData) (hcell : B.cell = unitCell)
    {ℓ : ℝ} (hℓ : 0 < ℓ) (n m : Fin 3 → ℤ) :
    B.realIP (B.thetaExp ℓ (ℓ⁻¹ • vec n)) (B.thetaExp ℓ (ℓ⁻¹ • vec m))
      = if n = m then ℓ ^ 3 else 0 := by
  have hℓ0 : ℓ ≠ 0 := ne_of_gt hℓ
  rw [BoxData.realIP_apply,
    show (fun x : ℝ³ =>
        ((starRingEnd ℂ) (B.thetaExp ℓ (ℓ⁻¹ • vec n) x) * B.thetaExp ℓ (ℓ⁻¹ • vec m) x).re)
        = fun x : ℝ³ => Set.indicator (B.boxL ℓ)
            (fun x : ℝ³ => Real.cos (inner ℝ (vec (fun i => m i - n i)) (ℓ⁻¹ • x))) x from
      funext fun x => by
        rw [B.conj_thetaExp_mul_thetaExp_re]
        by_cases hx : x ∈ B.boxL ℓ
        · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
          congr 1
          rw [← vec_sub n m, ← smul_sub, real_inner_smul_left, real_inner_smul_right]
        · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx],
    MeasureTheory.integral_indicator (B.boxL_measurableSet ℓ), BoxData.boxL, hcell]
  have hsc := MeasureTheory.Measure.setIntegral_comp_smul_of_pos (μ := volume)
    (f := fun x : ℝ³ => Real.cos (inner ℝ (vec (fun i => m i - n i)) (ℓ⁻¹ • x))) (s := unitCell) hℓ
  rw [finrank_euclideanSpace_fin] at hsc
  calc ∫ x in ℓ • unitCell,
        Real.cos (inner ℝ (vec (fun i => m i - n i)) (ℓ⁻¹ • x))
      = ℓ ^ 3 * ∫ x in unitCell,
          Real.cos (inner ℝ (vec (fun i => m i - n i)) (ℓ⁻¹ • (ℓ • x))) := by
        rw [hsc, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero 3 hℓ0), one_mul]
    _ = ℓ ^ 3 * ∫ x in unitCell, Real.cos (inner ℝ (vec (fun i => m i - n i)) x) := by
        congr 1
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        show Real.cos (inner ℝ (vec (fun i => m i - n i)) (ℓ⁻¹ • (ℓ • x)))
          = Real.cos (inner ℝ (vec (fun i => m i - n i)) x)
        congr 1
        rw [inv_smul_smul₀ hℓ0]
    _ = ℓ ^ 3 * (if (fun i => m i - n i) = 0 then 1 else 0) := by
        simp only [vec]
        rw [integral_unitCell_cos_lattice (fun i => m i - n i)]
    _ = if n = m then ℓ ^ 3 else 0 := by
        have hiff : ((fun i => m i - n i) = 0) ↔ n = m := by
          constructor
          · intro h
            funext i
            have := congrFun h i
            simpa using (sub_eq_zero.mp this).symm
          · intro h
            rw [h]
            funext i
            simp
        by_cases hnm : n = m
        · rw [if_pos (hiff.mpr hnm), if_pos hnm, mul_one]
        · rw [if_neg (fun h => hnm (hiff.mp h)), if_neg hnm, mul_zero]

end Work.BoseB4
