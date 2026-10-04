import Mathlib
import Submission.Work.Diff.EXT.ConnCov.aTowerMovingDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Sharpening the monotone slot bound for homogeneous slot families

The *monotone* slot bound `Work.Diff.EXT.ConnCov.AMB.Bnd1 G t τ C` bounds an `N`-slot family `τ`
by `C ∏_j (1 + ‖F_j(x)‖_{G t})` on arbitrary smooth tuples `F`, whereas the *sharp* (product)
bound is `C ∏_j ‖F_j(x)‖_{G t}`.  For a family that is **homogeneous of degree `N`** in its slots,
`τ (r • F) x = r^N τ F x`, the two are equivalent: the monotone bound is obtained from the sharp
one by `∏ √a_j ≤ ∏ (1 + √a_j)`, and the sharp one is recovered from the monotone one by scaling the
tuple by `r` and letting `r → ∞`:

  `r^N |τ F x| ≤ C ∏_j (1 + r s_j)`  (from `Bnd1` applied to `r • F`, `s_j = ‖F_j(x)‖`),

divide by `r^N` and use `(1 + r s)/r = 1/r + s`:

  `|τ F x| ≤ C ∏_j (1/r + s_j)`  for every `r > 0`,

then let `r → ∞` along `Filter.atTop` (`1/r → 0`).  Note that no hypothesis on the *sign* of `C` is
needed for this direction: dividing by the positive number `r^N` and passing to the limit are both
sign-blind.  (The `hC : 0 ≤ C` hypothesis of the statement is therefore redundant here; it is kept
because it is harmless and is needed in the converse direction, `bnd1_of_valBound`.)

This is the contract `Work.Diff.EXT.ConnCov.sharp_of_bnd1_homog`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.EXT.ConnCov

theorem sharp_of_bnd1_homog
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    (G : ℝ → Submission.Diff.SMet I M) (t : ℝ) {N : ℕ}
    (τ : Work.Diff.EXT.ConnCov.AMB.Fam (I := I) (M := M) N) {C : ℝ} (hC : 0 ≤ C)
    (h : Work.Diff.EXT.ConnCov.AMB.Bnd1 G t τ C)
    (hhom : ∀ (r : ℝ) (F : Fin N → Work.Diff.EXT.ConnCov.AMB.TF (I := I) (M := M)) (x : M),
      τ (fun j => r • F j) x = r ^ N * τ F x) :
    ∀ (F : Fin N → Work.Diff.EXT.ConnCov.AMB.TF (I := I) (M := M)) (x : M),
      (∀ j, Work.Diff.EXT.ATower.SmE I M (F j)) →
      |τ F x| ≤ C * ∏ j, Real.sqrt ((G t).inner x (F j x) (F j x)) := by
  intro F x hF
  -- The `G t`-self pairing is nonnegative (it is the squared norm of the slot value).
  have hinner_nonneg : ∀ v : TangentSpace I x, 0 ≤ (G t).inner x v v := by
    intro v
    rcases eq_or_ne v 0 with hv | hv
    · subst hv
      simp
    · exact le_of_lt ((G t).pos x v hv)
  -- Scaling a vector by `r` scales the self pairing by `r ^ 2`.
  have hsmul_inner : ∀ (r : ℝ) (v : TangentSpace I x),
      (G t).inner x (r • v) (r • v) = r ^ 2 * ((G t).inner x v v) := by
    intro r v
    simp only [ContinuousLinearMap.map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  -- Hence the square root of a scaled self pairing is `r` times the square root.
  have hsqrt_smul : ∀ (r : ℝ) (v : TangentSpace I x), 0 < r →
      Real.sqrt ((G t).inner x (r • v) (r • v))
        = r * Real.sqrt ((G t).inner x v v) := by
    intro r v hr
    rw [hsmul_inner r v, Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq_eq_abs, abs_of_pos hr]
  -- **The scaled bound**: `Bnd1` on `r • F` plus homogeneity.
  have key : ∀ r : ℝ, 0 < r → r ^ N * |τ F x| ≤
      C * ∏ j : Fin N, (1 + r * Real.sqrt ((G t).inner x (F j x) (F j x))) := by
    intro r hr
    have hFsm : ∀ j : Fin N, Work.Diff.EXT.ATower.SmE I M (fun y : M => r • F j y) :=
      fun j => ContMDiff.smul_section (contMDiff_const (c := r)) (hF j)
    have hb := h (fun j : Fin N => fun y : M => r • F j y) x hFsm
    have hhom' : τ (fun j : Fin N => fun y : M => r • F j y) x = r ^ N * τ F x := by
      rw [show (fun j : Fin N => fun y : M => r • F j y) = (fun j : Fin N => r • F j) from
        funext fun j => rfl, hhom r F x]
    rw [hhom', abs_mul, abs_of_nonneg (pow_nonneg hr.le N)] at hb
    rw [show (∏ j : Fin N, (1 + Real.sqrt ((G t).inner x
            ((fun j : Fin N => fun y : M => r • F j y) j x)
            ((fun j : Fin N => fun y : M => r • F j y) j x))))
        = ∏ j : Fin N, (1 + r * Real.sqrt ((G t).inner x (F j x) (F j x))) from by
      apply Finset.prod_congr rfl
      intro j _
      change 1 + Real.sqrt ((G t).inner x (r • F j x) (r • F j x))
        = 1 + r * Real.sqrt ((G t).inner x (F j x) (F j x))
      rw [hsqrt_smul r (F j x) hr]] at hb
    exact hb
  -- Divide by `r ^ N` and rewrite `(1 + r s)/r = 1/r + s`.
  have hbound : ∀ r : ℝ, 0 < r → |τ F x| ≤
      C * ∏ j : Fin N, ((1 : ℝ) / r + Real.sqrt ((G t).inner x (F j x) (F j x))) := by
    intro r hr
    have hrN : r ^ N ≠ 0 := pow_ne_zero N (ne_of_gt hr)
    have hident : (∏ j : Fin N, (1 + r * Real.sqrt ((G t).inner x (F j x) (F j x))))
        = r ^ N * ∏ j : Fin N,
            ((1 : ℝ) / r + Real.sqrt ((G t).inner x (F j x) (F j x))) := by
      have h1 : ∀ j : Fin N, (1 + r * Real.sqrt ((G t).inner x (F j x) (F j x)))
          = r * ((1 : ℝ) / r + Real.sqrt ((G t).inner x (F j x) (F j x))) := by
        intro j
        have hr' : r ≠ 0 := ne_of_gt hr
        field_simp
      rw [Finset.prod_congr rfl (fun j _ => h1 j), Finset.prod_mul_distrib]
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    calc |τ F x| = (r ^ N * |τ F x|) / r ^ N := by rw [mul_div_cancel_left₀ _ hrN]
      _ ≤ (C * ∏ j : Fin N, (1 + r * Real.sqrt ((G t).inner x (F j x) (F j x)))) / r ^ N :=
          div_le_div_of_nonneg_right (key r hr) (pow_nonneg hr.le N)
      _ = C * ((∏ j : Fin N, (1 + r * Real.sqrt ((G t).inner x (F j x) (F j x)))) / r ^ N) := by
          rw [mul_div_assoc]
      _ = C * ∏ j : Fin N, ((1 : ℝ) / r + Real.sqrt ((G t).inner x (F j x) (F j x))) := by
          rw [hident, mul_div_cancel_left₀ _ hrN]
  -- Finally let `r → ∞`.
  have htend : Tendsto (fun r : ℝ => C * ∏ j : Fin N,
        ((1 : ℝ) / r + Real.sqrt ((G t).inner x (F j x) (F j x))))
      atTop (𝓝 (C * ∏ j : Fin N, Real.sqrt ((G t).inner x (F j x) (F j x)))) := by
    refine Tendsto.const_mul C ?_
    refine tendsto_finsetProd (Finset.univ : Finset (Fin N)) (fun j _ => ?_)
    have h1 : Tendsto (fun r : ℝ => (1 : ℝ) / r) atTop (𝓝 0) := by
      simpa [one_div] using (tendsto_inv_atTop_zero (𝕜 := ℝ))
    simpa using h1.add tendsto_const_nhds
  refine le_of_tendsto_of_tendsto tendsto_const_nhds htend ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  exact hbound r hr

end Work.Diff.EXT.ConnCov
