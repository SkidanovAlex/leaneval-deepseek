import Mathlib
import Submission.Work.Mostow.ellipticDefs

/-!
# `hdist (linBlk k m R u) (linBlk k m R v) = hdist u v`

`linBlk k m R` keeps the first `k` coordinates of `u : E (k+m)` and applies the linear isometry
`R` to the last `m` ones.  On the hyperboloid it corresponds to the block matrix
`diag(1_k, R, 1)`, which preserves the Minkowski form; here we check the resulting statement
directly in the chart: `linBlk` preserves both the Euclidean norm and the Euclidean inner
product, hence `tpart` and `hdist`.

The computation is a `Fin.append` decomposition of the inner product (as for `inner_fermi`):
`Fin.sum_univ_add` splits the coordinate sum over `Fin (k + m)` into the sums over `Fin k`
and `Fin m`, and on the second part `R.inner_map_map` replaces `R` by the identity.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity

noncomputable section

/-- The Euclidean inner product as a coordinate sum. -/
private lemma inner_eq_sum_coord {n : ℕ} (x y : E n) :
    inner ℝ x y = ∑ i, x.ofLp i * y.ofLp i := by
  rw [PiLp.inner_apply]
  exact Finset.sum_congr rfl fun i _ => Real.inner_apply (x.ofLp i) (y.ofLp i)

/-- The coordinate sum as the Euclidean inner product. -/
private lemma sum_mul_ofLp_eq_inner {n : ℕ} (x y : E n) :
    (∑ i, x.ofLp i * y.ofLp i) = inner ℝ x y := by
  rw [inner_eq_sum_coord]

/-- `linBlk` preserves the Euclidean inner product (it is the block diagonal of `1` and `R`). -/
lemma inner_linBlk (k m : ℕ) (R : E m ≃ₗᵢ[ℝ] E m) (u v : E (k + m)) :
    inner ℝ (linBlk k m R u) (linBlk k m R v) = inner ℝ u v := by
  rw [inner_eq_sum_coord (linBlk k m R u) (linBlk k m R v), inner_eq_sum_coord u v]
  rw [Fin.sum_univ_add, Fin.sum_univ_add]
  simp only [linBlk, PiLp.toLp_apply, Fin.append_left, Fin.append_right]
  have h2 : (∑ x : Fin m,
        (R (WithLp.toLp 2 fun j' => u.ofLp (Fin.natAdd k j'))).ofLp x *
          (R (WithLp.toLp 2 fun j' => v.ofLp (Fin.natAdd k j'))).ofLp x)
      = ∑ x : Fin m, u.ofLp (Fin.natAdd k x) * v.ofLp (Fin.natAdd k x) := by
    rw [sum_mul_ofLp_eq_inner
          (R (WithLp.toLp 2 fun j' => u.ofLp (Fin.natAdd k j')))
          (R (WithLp.toLp 2 fun j' => v.ofLp (Fin.natAdd k j'))),
        R.inner_map_map,
        ← inner_eq_sum_coord (WithLp.toLp 2 fun j' => u.ofLp (Fin.natAdd k j'))
          (WithLp.toLp 2 fun j' => v.ofLp (Fin.natAdd k j'))]
  rw [h2]

/-- `linBlk` preserves the Euclidean norm. -/
lemma norm_linBlk (k m : ℕ) (R : E m ≃ₗᵢ[ℝ] E m) (u : E (k + m)) :
    ‖linBlk k m R u‖ = ‖u‖ := by
  have hsq : ‖linBlk k m R u‖ ^ 2 = ‖u‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq (linBlk k m R u), ← real_inner_self_eq_norm_sq u,
      inner_linBlk]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
  · exact h
  · linarith [norm_nonneg (linBlk k m R u), norm_nonneg u]

/-- `linBlk` preserves the time coordinate `tpart`. -/
lemma tpart_linBlk (k m : ℕ) (R : E m ≃ₗᵢ[ℝ] E m) (u : E (k + m)) :
    tpart (linBlk k m R u) = tpart u := by
  rw [tpart, tpart, norm_linBlk]

theorem hdist_linBlk (k m : ℕ) (R : Submission.Mostow.E m ≃ₗᵢ[ℝ] Submission.Mostow.E m)
    (u v : Submission.Mostow.E (k + m)) :
    Submission.Mostow.hdist (Work.Mostow.linBlk k m R u) (Work.Mostow.linBlk k m R v)
      = Submission.Mostow.hdist u v := by
  rw [hdist, hdist, tpart_linBlk, tpart_linBlk, inner_linBlk]

end

end Work.Mostow
