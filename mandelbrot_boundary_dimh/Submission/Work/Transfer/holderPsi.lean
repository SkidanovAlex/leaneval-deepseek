import Mathlib
import Submission.Work.Transfer.Setup

/-!
# Hölder continuity of `c ↦ phi c₁ (codeOf m phi c)` on the hit set

This file proves `Work.Transfer.holderPsi`, one of the five pieces of the area-transfer
argument (Shishikura, *Hausdorff dimension of the boundary of the Mandelbrot set and Julia
sets*, Ann. of Math. 147 (1998), Lemma 3.2; compare MSS Lemma III.2).

The mathematical content is the following.  The holomorphic motion of the IFS produced by
`MandelDim.MotionStatement` carries, for every `c` in the ball `ball c₀ ρ`, a bijection
`ω ↦ phi c ω` onto the limit set at `c`; `MotionData.holder` says that up to the factor `C`
the distance between the limit points of two codes is *larger at the base parameter* than at
any other parameter, raised to the power `a`:

`‖phi c ω - phi c ω'‖ ≤ C * ‖phi c' ω - phi c' ω'‖ ^ a`,

and `MotionData.lipschitz` says that the motion is `L`-Lipschitz in the parameter.

If `c` and `c'` are parameters at which the critical value `critOrbit m c` hits the limit set
(with codes `w`, `w'`), then `phi c w = critOrbit m c` and `phi c' w' = critOrbit m c'`, so
comparing the two displayed inequalities for the pairs `(c, w)`, `(c, w')` bounds
`‖phi c w - phi c w'‖` by `(D + L) ‖c - c'‖`, where `D` is the Lipschitz constant of the
critical orbit on the ball.  Feeding this back into the first inequality gives the Hölder
bound with constant `C * (D + L) ^ a` and exponent `a` for the map
`c ↦ phi c₁ (codeOf m phi c)` on the set of hitting parameters.
-/

open LeanEval.Dynamics.MandelbrotBoundary
open Set Metric Filter Topology
open scoped NNReal ENNReal
open Classical

noncomputable section

namespace Work.Transfer

/-- `c ↦ phi c₁ (codeOf m phi c)`, the map which sends a parameter at which the critical value
`critOrbit m c` hits the limit set to the corresponding limit point, is Hölder continuous with
exponent `a` on the set of hitting parameters `HitSet m c₁ ρ₁ phi W`.

Both the motion (`MotionData.lipschitz`) and its "reverse Hölder" property
(`MotionData.holder`) are used, the latter via the Lipschitz bound `D` for the critical orbit
on `ball c₀ ρ`. -/
theorem holderPsi {N : ℕ} [NeZero N] {c₀ : ℂ} {τ : Fin N → ℂ → ℂ} {n : Fin N → ℕ} {p : ℂ}
    {ρ a : ℝ} {phi : ℂ → (ℕ → Fin N) → ℂ} (hρ : 0 < ρ)
    (hMD : Work.Transfer.MotionData c₀ N τ n p ρ a phi) (ha0 : 0 < a) (ha1 : a ≤ 1) (m : ℕ)
    {c₁ : ℂ} (hc₁ : c₁ ∈ Metric.ball c₀ ρ) {ρ₁ : ℝ} (hρ₁ : 0 < ρ₁)
    (hsub : Metric.ball c₁ ρ₁ ⊆ Metric.ball c₀ ρ) (W : Set (ℕ → Fin N)) :
    ∃ K : NNReal, HolderOnWith K (Real.toNNReal a)
      (fun c => phi c₁ (Work.Transfer.codeOf m phi c)) (Work.Transfer.HitSet m c₁ ρ₁ phi W) := by
  obtain ⟨L, hL⟩ := hMD.lipschitz
  obtain ⟨C, hC⟩ := hMD.holder
  obtain ⟨-, D, -, hD, -, hlip⟩ := Work.Transfer.critOrbit_bound_lip (c₀ := c₀) hρ m
  set L' : ℝ := max L 0 with hL'_def
  set C' : ℝ := max C 0 with hC'_def
  have hC'0 : 0 ≤ C' := by rw [hC'_def]; exact le_max_right _ _
  have hCle : C ≤ C' := by rw [hC'_def]; exact le_max_left _ _
  have hLle : L ≤ L' := by rw [hL'_def]; exact le_max_left _ _
  have hDL0 : 0 ≤ D + L' := by rw [hL'_def]; linarith [le_max_right L (0 : ℝ)]
  have hval0 : 0 ≤ C' * (D + L') ^ a := mul_nonneg hC'0 (Real.rpow_nonneg hDL0 a)
  set K : NNReal := ⟨C' * (D + L') ^ a, hval0⟩ with hK_def
  refine ⟨K, ?_⟩
  intro x hx y hy
  -- `x` and `y` are hitting parameters: their critical values are realised by the limit set.
  obtain ⟨hxb1, w, -, hxw⟩ := hx
  obtain ⟨hyb1, w', -, hyw⟩ := hy
  have hxbal : x ∈ Metric.ball c₀ ρ := hsub hxb1
  have hybal : y ∈ Metric.ball c₀ ρ := hsub hyb1
  have hcodex : Work.Transfer.critOrbit m x = phi x (Work.Transfer.codeOf m phi x) :=
    Work.Transfer.codeOf_spec m phi x ⟨w, hxw⟩
  have hcodey : Work.Transfer.critOrbit m y = phi y (Work.Transfer.codeOf m phi y) :=
    Work.Transfer.codeOf_spec m phi y ⟨w', hyw⟩
  -- Step 1: the two limit points `phi x w`, `phi x w'` are within `(D + L') ‖x - y‖` at `x`.
  have hX : ‖phi x (Work.Transfer.codeOf m phi x) - phi x (Work.Transfer.codeOf m phi y)‖
      ≤ (D + L') * ‖x - y‖ := by
    have htri : ‖phi x (Work.Transfer.codeOf m phi x) - phi x (Work.Transfer.codeOf m phi y)‖
        = ‖Work.Transfer.critOrbit m x - phi x (Work.Transfer.codeOf m phi y)‖ := by rw [hcodex]
    rw [htri]
    have h2 : ‖Work.Transfer.critOrbit m x - Work.Transfer.critOrbit m y‖ ≤ D * ‖x - y‖ :=
      hlip x hxbal y hybal
    have h3 : ‖Work.Transfer.critOrbit m y - phi x (Work.Transfer.codeOf m phi y)‖
        ≤ L' * ‖x - y‖ := by
      rw [hcodey]
      calc ‖phi y (Work.Transfer.codeOf m phi y) - phi x (Work.Transfer.codeOf m phi y)‖
          ≤ L * ‖y - x‖ := hL y hybal x hxbal _
        _ ≤ L' * ‖y - x‖ := mul_le_mul_of_nonneg_right hLle (norm_nonneg _)
        _ = L' * ‖x - y‖ := by rw [norm_sub_rev y x]
    calc ‖Work.Transfer.critOrbit m x - phi x (Work.Transfer.codeOf m phi y)‖
        ≤ ‖Work.Transfer.critOrbit m x - Work.Transfer.critOrbit m y‖
          + ‖Work.Transfer.critOrbit m y - phi x (Work.Transfer.codeOf m phi y)‖ := by
          simpa [dist_eq_norm, norm_sub_rev] using dist_triangle (Work.Transfer.critOrbit m x)
            (Work.Transfer.critOrbit m y) (phi x (Work.Transfer.codeOf m phi y))
      _ ≤ D * ‖x - y‖ + L' * ‖x - y‖ := add_le_add h2 h3
      _ = (D + L') * ‖x - y‖ := by ring
  -- Step 2: transfer the bound at `x` back to the base parameter `c₁` using the Hölder field.
  have hkey : ‖phi c₁ (Work.Transfer.codeOf m phi x) - phi c₁ (Work.Transfer.codeOf m phi y)‖
      ≤ (C' * (D + L') ^ a) * ‖x - y‖ ^ a := by
    have hX0 : 0 ≤ ‖phi x (Work.Transfer.codeOf m phi x)
        - phi x (Work.Transfer.codeOf m phi y)‖ := norm_nonneg _
    have h1 : ‖phi c₁ (Work.Transfer.codeOf m phi x) - phi c₁ (Work.Transfer.codeOf m phi y)‖
        ≤ C * ‖phi x (Work.Transfer.codeOf m phi x)
            - phi x (Work.Transfer.codeOf m phi y)‖ ^ a := hC c₁ hc₁ x hxbal _ _
    refine h1.trans ?_
    have hZ : 0 ≤ ‖phi x (Work.Transfer.codeOf m phi x)
        - phi x (Work.Transfer.codeOf m phi y)‖ ^ a := Real.rpow_nonneg hX0 a
    calc C * ‖phi x (Work.Transfer.codeOf m phi x)
            - phi x (Work.Transfer.codeOf m phi y)‖ ^ a
        ≤ C' * ‖phi x (Work.Transfer.codeOf m phi x)
            - phi x (Work.Transfer.codeOf m phi y)‖ ^ a := mul_le_mul_of_nonneg_right hCle hZ
      _ ≤ C' * ((D + L') * ‖x - y‖) ^ a := by
          refine mul_le_mul_of_nonneg_left ?_ hC'0
          exact Real.rpow_le_rpow hX0 hX ha0.le
      _ = (C' * (D + L') ^ a) * ‖x - y‖ ^ a := by
          rw [Real.mul_rpow hDL0 (norm_nonneg _)]
          ring
  -- Step 3: rewrite the `ℝ≥0∞`-valued goal as the real inequality just proved.
  have hKcoe : (K : ℝ) = C' * (D + L') ^ a := by rw [hK_def]; rfl
  have hright : (K : ℝ≥0∞) * edist x y ^ ((Real.toNNReal a : ℝ≥0) : ℝ)
      = ENNReal.ofReal ((C' * (D + L') ^ a) * ‖x - y‖ ^ a) := by
    rw [ENNReal.coe_nnreal_eq, hKcoe, edist_dist, dist_eq_norm, Real.coe_toNNReal a ha0.le,
      ENNReal.ofReal_rpow_of_nonneg (norm_nonneg (x - y)) ha0.le,
      ← ENNReal.ofReal_mul hval0]
  rw [show edist (phi c₁ (Work.Transfer.codeOf m phi x)) (phi c₁ (Work.Transfer.codeOf m phi y))
      = ENNReal.ofReal ‖phi c₁ (Work.Transfer.codeOf m phi x)
          - phi c₁ (Work.Transfer.codeOf m phi y)‖ from by rw [edist_dist, dist_eq_norm]]
  rw [hright]
  exact ENNReal.ofReal_le_ofReal hkey

end Work.Transfer
