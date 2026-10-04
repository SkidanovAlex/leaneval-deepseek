import Mathlib
import Submission.Work.Diff.Alg.q2p_defs
import Submission.Work.Diff.Alg.Q2PB.on_pair_norm_b

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.Alg.Q2PF

open Submission.Diff.Alg

/-!
# Normalising an orthogonal four-frame gives an orthonormal four-frame

Given four mutually orthogonal nonzero vectors `x y z w` of `ℝⁿ`, the four vectors obtained by
dividing each of them by its norm `√⟪u,u⟫` (i.e. `(√⟪u,u⟫)⁻¹ • u`) form an orthonormal four-frame
`IsON4`. This is the reduction used when one wants to apply a statement phrased for orthonormal
frames to an arbitrary orthogonal (nonzero) four-tuple.

`dot` is homogeneous: `⟪t • u, s • v⟫ = t s ⟪u,v⟫`, so cross terms stay `0`, while on the diagonal
`⟪c⁻¹ • u, c⁻¹ • u⟫ = c⁻² * ⟪u,u⟫ = (c⁻¹ c)² = 1` because `c = √⟪u,u⟫` satisfies `c * c = ⟪u,u⟫`
and `c ≠ 0` (the pairing `⟪u,u⟫ = ∑ uᵢ²` is `> 0` when `u ≠ 0`).
-/

variable {n : ℕ}

/-! ## Elementary API for the Euclidean pairing `dot` -/

theorem dot_smul_left' (t : ℝ) (u v : Fin n → ℝ) : dot (t • u) v = t * dot u v := by
  simp only [dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem dot_smul_right' (t : ℝ) (u v : Fin n → ℝ) : dot u (t • v) = t * dot u v := by
  simp only [dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- `dot` is bilinear with respect to scalar multiplication in both slots. -/
theorem dot_smul_smul (t s : ℝ) (u v : Fin n → ℝ) :
    dot (t • u) (s • v) = t * s * dot u v := by
  rw [dot_smul_left', dot_smul_right']
  ring

theorem dot_self_nonneg' (u : Fin n → ℝ) : 0 ≤ dot u u :=
  Finset.sum_nonneg fun _ _ => mul_self_nonneg _

theorem dot_self_eq_zero' {u : Fin n → ℝ} : dot u u = 0 ↔ u = 0 := by
  rw [dot, Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => mul_self_nonneg _)]
  constructor
  · intro h
    funext i
    exact mul_self_eq_zero.mp (h i (Finset.mem_univ i))
  · intro h i _
    rw [h]
    simp

theorem dot_self_pos' {u : Fin n → ℝ} (hu : u ≠ 0) : 0 < dot u u :=
  lt_of_le_of_ne (dot_self_nonneg' u) fun h0 => hu (dot_self_eq_zero'.mp h0.symm)

/-! ## The two normalisation computations -/

/-- Normalising a nonzero vector makes it a unit vector. -/
theorem dot_norm_self {u : Fin n → ℝ} (hu : u ≠ 0) :
    dot ((Real.sqrt (dot u u))⁻¹ • u) ((Real.sqrt (dot u u))⁻¹ • u) = 1 := by
  set c := Real.sqrt (dot u u) with hc
  have hcc : c * c = dot u u := by
    rw [hc, ← sq]
    exact Real.sq_sqrt (dot_self_nonneg' u)
  have hcne : c ≠ 0 := by
    rw [hc]
    exact ne_of_gt (Real.sqrt_pos.mpr (dot_self_pos' hu))
  rw [dot_smul_smul, ← hcc]
  have h1 : c⁻¹ * c = 1 := inv_mul_cancel₀ hcne
  calc c⁻¹ * c⁻¹ * (c * c) = (c⁻¹ * c) * (c⁻¹ * c) := by ring
    _ = 1 := by rw [h1]; ring

/-- Normalising two orthogonal vectors keeps them orthogonal. -/
theorem dot_norm_orth {u v : Fin n → ℝ} (h : dot u v = 0) :
    dot ((Real.sqrt (dot u u))⁻¹ • u) ((Real.sqrt (dot v v))⁻¹ • v) = 0 := by
  rw [dot_smul_smul, h]
  ring

/-! ## The main statement -/

theorem norm_on4 {n : ℕ} {x y z w : Fin n → ℝ}
    (h : Work.Diff.Alg.Q2P.PairwiseOrth x y z w)
    (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) (hw : w ≠ 0) :
    Work.Diff.Alg.Q2P.IsON4 ((Real.sqrt (Submission.Diff.Alg.dot x x))⁻¹ • x)
      ((Real.sqrt (Submission.Diff.Alg.dot y y))⁻¹ • y)
      ((Real.sqrt (Submission.Diff.Alg.dot z z))⁻¹ • z)
      ((Real.sqrt (Submission.Diff.Alg.dot w w))⁻¹ • w) := by
  obtain ⟨hxy, hxz, hxw, hyz, hyw, hzw⟩ := h
  refine ⟨dot_norm_self hx, dot_norm_self hy, dot_norm_self hz, dot_norm_self hw,
    dot_norm_orth hxy, dot_norm_orth hxz, dot_norm_orth hxw, dot_norm_orth hyz,
    dot_norm_orth hyw, dot_norm_orth hzw⟩

end Work.Diff.Alg.Q2PF
