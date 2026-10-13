/-
Copyright: work module for the Elgindi finite-time singularity project.

# The pointwise `ℋⁿ`-slot bound for `Ê₂` on the open class

Support module for `EpsE4Thr/E2hat_HkSq_le_uniform_O.lean`.  For `α > 0`, `f` of class
`SmoothOpen` and `(z,θ)` in the open quadrant,

`HkIntegrand α n (Ê₂ f) z θ ≤ Cn · (HkIntegrand α n f z θ + HkIntegrand α n (D_θ f) z θ)`

with `Cn` depending only on `n` — in particular *not* on `α`.  The proof splits
`Ê₂ f = 2·(φ·f) + 3·(φ·D_θ f)` (`φ(z) = z/(1+z)²`) with the open-class subadditivity
`GalFields.HkSum.HkIntegrand_add_le_open` and the homogeneity
`LocData.HkIntegrand_const_mul`, and contracts each of the two pieces with the `α`-free
multiplier estimate `E2hatOAux.HkIntegrand_zmul_SO`.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongEps.EpsE4Thr.E2hatOAux.ZmulBound
import Submission.Work.FTS.GalFields.RHS.HkSum
import Submission.Work.FTS.LocData.HkIntegrand_const_mul
import Submission.Work.FTS.CoercivityFix.E2Bound.E2hat_HkIntegrand_le_uniform
import Submission.Work.FTS.CoercivityFix.E2Bound.SlotMul.Zop_iterate_phiZ_bound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.E2hatOAux

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- **The `ℋⁿ`-slot bound for the `D_z`-commutator defect, on the open class.**  For `α > 0`,
`f` of class `SmoothOpen` and `(z,θ)` in the open quadrant,

`HkIntegrand α n (Ê₂ f) z θ ≤ Cn·(HkIntegrand α n f z θ + HkIntegrand α n (D_θ f) z θ)`

with `Cn` depending only on `n`. -/
theorem E2hat_HkIntegrand_le_uniform_pt (n : ℕ) :
    ∃ Cn : ℝ, 0 < Cn ∧ ∀ (α : ℝ) (f : ℝ → ℝ → ℝ), 0 < α →
      Work.FTS.EllipticEst.SmoothOpen f →
      ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        Work.Spaces.HkIntegrand α n (Work.FTS.CoercivityFix.E2hat f) z θ
          ≤ Cn * (Work.Spaces.HkIntegrand α n f z θ
              + Work.Spaces.HkIntegrand α n (Work.Spaces.Dth f) z θ) := by
  obtain ⟨K, hK0, hKb⟩ :=
    Work.FTS.CoercivityFix.E2Bound.SlotMul.Zop_iterate_phiZ_bound n
  refine ⟨18 * zmulC n * (1 + K) ^ 2 + 1, ?_, ?_⟩
  · have h : 0 ≤ zmulC n * (1 + K) ^ 2 := mul_nonneg (zmulC_pos n).le (sq_nonneg _)
    linarith
  · intro α f hα hf z hz θ hθ
    have hzIz : z ∈ Work.Spaces.Iz := Set.mem_Ici.mpr (le_of_lt hz)
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    have hDth : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dth f) := by
      simpa using hf.DthIter 1
    have hphi : ∀ m : ℕ, ContDiffOn ℝ m (fun z : ℝ => z / (1 + z) ^ 2) (Set.Ioi 0) :=
      phiZ_contDiffOn
    have hA : Work.FTS.EllipticEst.SmoothOpen
        (fun z θ : ℝ => 2 * ((z / (1 + z) ^ 2) * f z θ)) :=
      smoothOpen_const_mul 2 (smoothOpen_mul (smoothOpen_zOnly hphi) hf)
    have hB : Work.FTS.EllipticEst.SmoothOpen
        (fun z θ : ℝ => 3 * ((z / (1 + z) ^ 2) * (Work.Spaces.Dth f) z θ)) :=
      smoothOpen_const_mul 3 (smoothOpen_mul (smoothOpen_zOnly hphi) hDth)
    rw [Work.FTS.CoercivityFix.E2Bound.E2hat_eq_zmul f]
    have h1 := Work.FTS.GalFields.RHS.HkIntegrand_add_le_open α n hα hA hB z hzIz θ hθI
    have h1' : Work.Spaces.HkIntegrand α n
          (fun z θ : ℝ => 2 * ((z / (1 + z) ^ 2) * f z θ)
            + 3 * ((z / (1 + z) ^ 2) * (Work.Spaces.Dth f) z θ)) z θ
        ≤ 2 * (Work.Spaces.HkIntegrand α n
            (fun z θ : ℝ => 2 * ((z / (1 + z) ^ 2) * f z θ)) z θ
          + Work.Spaces.HkIntegrand α n
              (fun z θ : ℝ => 3 * ((z / (1 + z) ^ 2) * (Work.Spaces.Dth f) z θ)) z θ) := by
      simpa only [Pi.add_apply] using h1
    have h2 := Work.FTS.LocData.HkIntegrand_const_mul α n 2
      (fun z θ : ℝ => (z / (1 + z) ^ 2) * f z θ) z θ
    have h3 := Work.FTS.LocData.HkIntegrand_const_mul α n 3
      (fun z θ : ℝ => (z / (1 + z) ^ 2) * (Work.Spaces.Dth f) z θ) z θ
    have h2' : Work.Spaces.HkIntegrand α n
          (fun z θ : ℝ => 2 * ((z / (1 + z) ^ 2) * f z θ)) z θ
        = 4 * Work.Spaces.HkIntegrand α n
            (fun z θ : ℝ => (z / (1 + z) ^ 2) * f z θ) z θ := by
      rw [h2]; norm_num
    have h3' : Work.Spaces.HkIntegrand α n
          (fun z θ : ℝ => 3 * ((z / (1 + z) ^ 2) * (Work.Spaces.Dth f) z θ)) z θ
        = 9 * Work.Spaces.HkIntegrand α n
            (fun z θ : ℝ => (z / (1 + z) ^ 2) * (Work.Spaces.Dth f) z θ) z θ := by
      rw [h3]; norm_num
    have h4 := HkIntegrand_zmul_SO α n (fun z : ℝ => z / (1 + z) ^ 2) K hK0 hKb hphi f hf
      z hz θ hθ
    have h5 := HkIntegrand_zmul_SO α n (fun z : ℝ => z / (1 + z) ^ 2) K hK0 hKb hphi
      (Work.Spaces.Dth f) hDth z hz θ hθ
    have hX : 0 ≤ Work.Spaces.HkIntegrand α n f z θ :=
      Work.Spaces.HkIntegrand_nonneg α n f z θ
    have hY : 0 ≤ Work.Spaces.HkIntegrand α n (Work.Spaces.Dth f) z θ :=
      Work.Spaces.HkIntegrand_nonneg α n (Work.Spaces.Dth f) z θ
    have hK1 : (0 : ℝ) ≤ (1 + K) ^ 2 := by positivity
    have hC0 : 0 ≤ zmulC n * (1 + K) ^ 2 := mul_nonneg (zmulC_pos n).le hK1
    have hCX : 0 ≤ zmulC n * (1 + K) ^ 2 * Work.Spaces.HkIntegrand α n f z θ :=
      mul_nonneg hC0 hX
    have hCY : 0 ≤ zmulC n * (1 + K) ^ 2 * Work.Spaces.HkIntegrand α n (Work.Spaces.Dth f) z θ :=
      mul_nonneg hC0 hY
    nlinarith [h1', h2', h3', h4, h5, hX, hY, hCX, hCY]

end Work.FTS.StrongEps.EpsE4Thr.E2hatOAux
