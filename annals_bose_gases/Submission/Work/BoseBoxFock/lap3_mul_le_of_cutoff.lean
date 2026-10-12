import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Submission.Work.BoseBoxFock.lap3_decay_aux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.lap3_mul_le_of_cutoff`

The pointwise Leibniz bound for `Δ³ (θ_R · g)`:

    ‖Δ³ (θ_R · g) x‖ ≤ 27 · ∑_{i ≤ 6} C(6,i) · C i · ‖D^{6-i} g x‖

whenever `‖D^i (θ_R : ℂ) x‖ ≤ C i` for every `i ≤ 6` and every `R ≥ 1`.

The proof is the two-step composition of the two bounds already available in the chapter:

* `norm_lap3_apply_le` (in `NormSymAux`) bounds `Δ³` pointwise by `27 · ‖D⁶‖`;
* `norm_iteratedFDeriv_smul_le` (Mathlib, `ContDiff/Bounds.lean`) is the `n`-th order
  Leibniz bound `‖D^n (f • g)‖ ≤ ∑_{i ≤ n} C(n,i) ‖D^i f‖ ‖D^{n-i} g‖` for the scalar
  multiplication of `ℂ` on `ℂ`, which is complex multiplication;

followed by the pointwise comparison of each summand with the hypothesis `hC`.  Note that the
constant `27` of the statement is exactly the `27 = 3³` of `norm_lap3_apply_le`, and the sum runs
over `Finset.range 7 = {0,…,6}` matching `n = 6`.
-/

open MeasureTheory
open scoped Real BigOperators

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem lap3_mul_le_of_cutoff {θ : ℝ → EuclideanSpace ℝ (Fin 3) → ℝ}
    (hθ : Work.BoseBoxFock.CutoffHyp θ)
    {g : EuclideanSpace ℝ (Fin 3) → ℂ} (hg : ContDiff ℝ (⊤ : ENat) g)
    {C : ℕ → ℝ} (hC : ∀ k ≤ 6, ∀ R, 1 ≤ R → ∀ x,
      ‖iteratedFDeriv ℝ k (fun y => ((θ R y : ℝ) : ℂ)) x‖ ≤ C k)
    {R : ℝ} (hR : 1 ≤ R) (x : EuclideanSpace ℝ (Fin 3)) :
    ‖Work.BoseBoxFock.lap3 (fun y => ((θ R y : ℝ) : ℂ) * g y) x‖
      ≤ 27 * ∑ i ∈ Finset.range 7, ((6 : ℕ).choose i : ℝ) * C i * ‖iteratedFDeriv ℝ (6 - i) g x‖ := by
  -- the complex cutoff `(θ R : ℂ)` is smooth, being a linear isometry applied to the smooth
  -- real cutoff `θ R`
  have hθR : ContDiff ℝ (⊤ : ENat) (fun y : E3 => ((θ R y : ℝ) : ℂ)) := by
    have h : (fun y : E3 => ((θ R y : ℝ) : ℂ)) = ⇑(Complex.ofRealCLM) ∘ θ R := rfl
    rw [h]
    exact (Complex.ofRealCLM).contDiff.comp (hθ.contDiff R)
  have hF : ContDiff ℝ (⊤ : ENat) (fun y : E3 => ((θ R y : ℝ) : ℂ) * g y) := hθR.mul hg
  -- step 1: `Δ³` against the sixth derivative, with the constant `27`
  have h1 := norm_lap3_apply_le (fun y : E3 => ((θ R y : ℝ) : ℂ) * g y) hF x
  -- step 2: the sixth-order Leibniz bound (`•` on `ℂ` is multiplication)
  have hsmul : ‖iteratedFDeriv ℝ 6 (fun y : E3 => ((θ R y : ℝ) : ℂ) * g y) x‖
      ≤ ∑ i ∈ Finset.range 7, ((6 : ℕ).choose i : ℝ)
          * ‖iteratedFDeriv ℝ i (fun y : E3 => ((θ R y : ℝ) : ℂ)) x‖
          * ‖iteratedFDeriv ℝ (6 - i) g x‖ := by
    have := norm_iteratedFDeriv_smul_le (𝕜 := ℝ) (f := fun y : E3 => ((θ R y : ℝ) : ℂ))
      (g := g) hθR hg x (n := 6) (WithTop.coe_le_coe.mpr le_top)
    simpa only [smul_eq_mul] using this
  -- step 3: replace each `‖D^i (θ R : ℂ) x‖` by `C i`
  have hbound : (∑ i ∈ Finset.range 7, ((6 : ℕ).choose i : ℝ)
          * ‖iteratedFDeriv ℝ i (fun y : E3 => ((θ R y : ℝ) : ℂ)) x‖
          * ‖iteratedFDeriv ℝ (6 - i) g x‖)
      ≤ ∑ i ∈ Finset.range 7, ((6 : ℕ).choose i : ℝ) * C i * ‖iteratedFDeriv ℝ (6 - i) g x‖ := by
    refine Finset.sum_le_sum (fun i hi => ?_)
    have hi6 : i ≤ 6 := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    have hb := hC i hi6 R hR x
    have hnn : (0 : ℝ) ≤ ((6 : ℕ).choose i : ℝ) := by positivity
    have hgn : (0 : ℝ) ≤ ‖iteratedFDeriv ℝ (6 - i) g x‖ := norm_nonneg _
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb hnn) hgn
  calc ‖Work.BoseBoxFock.lap3 (fun y => ((θ R y : ℝ) : ℂ) * g y) x‖
      ≤ 27 * ‖iteratedFDeriv ℝ 6 (fun y => ((θ R y : ℝ) : ℂ) * g y) x‖ := h1
    _ ≤ 27 * ∑ i ∈ Finset.range 7, ((6 : ℕ).choose i : ℝ) * C i
          * ‖iteratedFDeriv ℝ (6 - i) g x‖ :=
        mul_le_mul_of_nonneg_left (hsmul.trans hbound) (by norm_num)

end Work.BoseBoxFock
