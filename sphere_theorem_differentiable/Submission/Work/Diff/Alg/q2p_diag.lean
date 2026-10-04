import Mathlib
import Submission.Work.Diff.Alg.q2p_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The diagonal (normalized) form of the lower sectional-curvature bound

If every sectional curvature `secK R u v` of an orthonormal pair `(u, v)` is at least `a`, then for
*arbitrary* orthogonal vectors `u ⊥ v` one has

`a * (⟪u,u⟫ * ⟪v,v⟫) ≤ R4 R u v u v`,

i.e. the bound extends from orthonormal pairs to orthogonal pairs after rescaling. This is the
"diagonal" form of the pinching lower bound: the quartic form `(u,v) ↦ R4 R u v u v` is homogeneous
of degree `2` in each argument, so dividing `u` and `v` by `√⟪u,u⟫` and `√⟪v,v⟫` reduces the claim
to an orthonormal pair, to which the hypothesis `ha` applies; multiplying back by the (positive)
norms squared yields the statement. No symmetry of `R` is used, only the multilinearity of `R4`.

Degenerate cases: if `⟪u,u⟫ = 0` then `u = 0` (a sum of squares vanishes), and both sides are `0`;
likewise for `v`.
-/

namespace Work.Diff.Alg

open Submission.Diff.Alg

variable {n : ℕ}

/-! ## Elementary API for the Euclidean pairing `dot` used below

(These are self-contained copies of the standard bilinearity/positivity lemmas for
`Submission.Diff.Alg.dot`; they are kept local to this file so that the proof depends only on
`q2p_defs`.) -/

theorem q2pd_dot_smul_left (t : ℝ) (u v : Fin n → ℝ) : dot (t • u) v = t * dot u v := by
  simp only [dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem q2pd_dot_smul_right (t : ℝ) (u v : Fin n → ℝ) : dot u (t • v) = t * dot u v := by
  simp only [dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- `dot` is homogeneous of degree `2` on the diagonal. -/
theorem q2pd_dot_smul_self (t : ℝ) (u : Fin n → ℝ) : dot (t • u) (t • u) = t ^ 2 * dot u u := by
  rw [q2pd_dot_smul_left, q2pd_dot_smul_right]; ring

theorem q2pd_dot_self_nonneg (u : Fin n → ℝ) : 0 ≤ dot u u :=
  Finset.sum_nonneg fun _ _ => mul_self_nonneg _

theorem q2pd_dot_self_eq_zero {u : Fin n → ℝ} : dot u u = 0 ↔ u = 0 := by
  rw [dot, Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => mul_self_nonneg _)]
  constructor
  · intro h
    funext i
    exact mul_self_eq_zero.mp (h i (Finset.mem_univ i))
  · intro h i _
    rw [h]
    simp

theorem q2p_diag {n : ℕ} (R : Submission.Diff.Alg.Curv4 n) {a : ℝ}
    (ha : ∀ u v : Fin n → ℝ, Submission.Diff.Alg.IsONPair u v →
      a ≤ Submission.Diff.Alg.secK R u v)
    {u v : Fin n → ℝ} (huv : Submission.Diff.Alg.dot u v = 0) :
    a * (Submission.Diff.Alg.dot u u * Submission.Diff.Alg.dot v v) ≤
      Submission.Diff.Alg.R4 R u v u v := by
  by_cases hu : dot u u = 0
  · -- `u = 0`, so both sides vanish
    rw [q2pd_dot_self_eq_zero.mp hu]
    simp [dot, R4]
  by_cases hv : dot v v = 0
  · -- `v = 0`, so both sides vanish
    rw [q2pd_dot_self_eq_zero.mp hv]
    simp [dot, R4]
  -- nondegenerate case: rescale to the orthonormal pair `(u/|u|, v/|v|)`
  have htupos : 0 < dot u u := lt_of_le_of_ne (q2pd_dot_self_nonneg u) (Ne.symm hu)
  have htvpos : 0 < dot v v := lt_of_le_of_ne (q2pd_dot_self_nonneg v) (Ne.symm hv)
  set c := Real.sqrt (dot u u) with hcdef
  set d := Real.sqrt (dot v v) with hddef
  have hcpos : 0 < c := by rw [hcdef]; exact Real.sqrt_pos.mpr htupos
  have hdpos : 0 < d := by rw [hddef]; exact Real.sqrt_pos.mpr htvpos
  have hcc : c * c = dot u u := by rw [hcdef, ← sq]; exact Real.sq_sqrt htupos.le
  have hdd : d * d = dot v v := by rw [hddef, ← sq]; exact Real.sq_sqrt htvpos.le
  have hcne : c ≠ 0 := ne_of_gt hcpos
  have hdne : d ≠ 0 := ne_of_gt hdpos
  have hU : dot (c⁻¹ • u) (c⁻¹ • u) = 1 := by
    rw [q2pd_dot_smul_self, ← hcc]
    have h1 : c⁻¹ * c = 1 := inv_mul_cancel₀ hcne
    calc c⁻¹ ^ 2 * (c * c) = (c⁻¹ * c) * (c⁻¹ * c) := by ring
      _ = 1 := by rw [h1]; ring
  have hV : dot (d⁻¹ • v) (d⁻¹ • v) = 1 := by
    rw [q2pd_dot_smul_self, ← hdd]
    have h1 : d⁻¹ * d = 1 := inv_mul_cancel₀ hdne
    calc d⁻¹ ^ 2 * (d * d) = (d⁻¹ * d) * (d⁻¹ * d) := by ring
      _ = 1 := by rw [h1]; ring
  have hUV0 : dot (c⁻¹ • u) (d⁻¹ • v) = 0 := by
    rw [q2pd_dot_smul_left, q2pd_dot_smul_right, huv]; ring
  have hpair : IsONPair (c⁻¹ • u) (d⁻¹ • v) := ⟨hU, hV, hUV0⟩
  have hsec := ha (c⁻¹ • u) (d⁻¹ • v) hpair
  -- expand the sectional curvature of the rescaled pair
  have hsecK : secK R (c⁻¹ • u) (d⁻¹ • v)
      = (c⁻¹ * c⁻¹) * (d⁻¹ * d⁻¹) * R4 R u v u v := by
    simp only [secK, Work.Diff.Alg.Q2P.R4_smul₁, Work.Diff.Alg.Q2P.R4_smul₂,
      Work.Diff.Alg.Q2P.R4_smul₃, Work.Diff.Alg.Q2P.R4_smul₄]
    ring
  rw [hsecK] at hsec
  have hts : dot u u * dot v v = (c * c) * (d * d) := by rw [← hcc, ← hdd]
  rw [hts]
  have hnn : 0 ≤ (c * c) * (d * d) := by positivity
  have hid : ((c⁻¹ * c⁻¹) * (d⁻¹ * d⁻¹) * R4 R u v u v) * ((c * c) * (d * d))
      = R4 R u v u v := by
    have h1 : c⁻¹ * c = 1 := inv_mul_cancel₀ hcne
    have h2 : d⁻¹ * d = 1 := inv_mul_cancel₀ hdne
    calc ((c⁻¹ * c⁻¹) * (d⁻¹ * d⁻¹) * R4 R u v u v) * ((c * c) * (d * d))
        = ((c⁻¹ * c) * (c⁻¹ * c)) * ((d⁻¹ * d) * (d⁻¹ * d)) * R4 R u v u v := by ring
      _ = R4 R u v u v := by rw [h1, h2]; ring
  calc a * ((c * c) * (d * d))
      ≤ ((c⁻¹ * c⁻¹) * (d⁻¹ * d⁻¹) * R4 R u v u v) * ((c * c) * (d * d)) :=
        mul_le_mul_of_nonneg_right hsec hnn
    _ = R4 R u v u v := hid

end Work.Diff.Alg
