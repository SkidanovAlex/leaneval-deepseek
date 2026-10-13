/-
  Subproject WilE9G, Sard — the fibre Jacobian of an *ambient* `Good` stratum is surjective.

  `Stratum.Good` for `S : Stratum 0 q` (the ambient case `p = 0`) says that at every point
  `z` of `S.X.set` the equations `S.h` vanish and the `S.j × q` matrix of symbolic derivatives
  `eaEval S.X.c (eaD S.X.c (Fin.natAdd 0 l) (S.h a)) z` has rank `S.j`.  Since the number of
  rows of that matrix is `S.j`, the corresponding Fréchet differential
  `d_z (h_a)_a : ℝ^{0+q} → ℝ^{S.j}` is surjective.  This is the elementary linear-algebra
  consequence of `Good` that every chart/implicit-function step in the construction uses: `Good`
  makes `h` a submersion.

  The proof runs through the bridge `Work.WilE5.Strat.fderiv_pi_eaEval`, which identifies
  `fderiv ℝ (fun w a => eaEval c (h a) w) z` with the `ContinuousLinearMap.pi` of the rows
  `∑ i, eaEval c (eaD c i (h a)) z • proj i`, and then the general lemma below: a matrix with
  `rank = #rows` gives a surjective `mulVecLin`.
-/
import Mathlib
import Submission.Work.WilE9G.Amb
import Submission.Work.WilE5.Strat.flatConormalTools

namespace Work.WilE9G.Sard

open WilkiesDesign WilkiesDesign.E
open Work.WilE9G

/-- A matrix whose rank equals its number of rows has surjective `mulVecLin`.  Stated for the row
form `ContinuousLinearMap.pi (fun a => ∑ i, cs a i • proj i)` that the `fderiv` of a tuple of
`eaEval`s takes. -/
theorem pi_surjective_of_rank_eq_card {m n : ℕ} (cs : Fin m → Fin n → ℝ)
    (hr : (Matrix.of cs).rank = m) :
    Function.Surjective (ContinuousLinearMap.pi (fun a : Fin m =>
      ∑ i : Fin n, cs a i • (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ))) := by
  have hpoint : ∀ v : Fin n → ℝ, (ContinuousLinearMap.pi (fun a : Fin m =>
      ∑ i : Fin n, cs a i • (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ))) v
      = (Matrix.of cs).mulVecLin v := by
    intro v
    funext a
    rw [ContinuousLinearMap.pi_apply, sum_apply,
      Matrix.mulVecLin_apply, Matrix.mulVec_apply_eq_sum]
    exact Finset.sum_congr rfl fun i _ => by simp [smul_eq_mul]
  have hfin : Module.finrank ℝ (LinearMap.range (Matrix.of cs).mulVecLin)
      = Module.finrank ℝ (Fin m → ℝ) := by
    rw [Module.finrank_pi, Fintype.card_fin]
    exact hr
  have htop : LinearMap.range (Matrix.of cs).mulVecLin = ⊤ := Submodule.eq_top_of_finrank_eq hfin
  have hsurj : Function.Surjective ((Matrix.of cs).mulVecLin) := LinearMap.range_eq_top.mp htop
  intro y
  obtain ⟨v, hv⟩ := hsurj y
  exact ⟨v, by rw [hpoint]; exact hv⟩

theorem goodFDerivSurjective {q : ℕ} (S : Stratum 0 q) (hS : S.Good) {z : Fin (0 + q) → ℝ}
    (hz : z ∈ S.X.set) :
    Function.Surjective
      (fderiv ℝ (fun z : Fin (0 + q) → ℝ => fun a : Fin S.j => eaEval S.X.c (S.h a) z) z) := by
  -- the `Good` rank hypothesis, over the columns `Fin q`
  have hrank0 := (hS z hz).2.1
  -- the same matrix with the columns indexed by `Fin (0 + q)` instead of `Fin q`
  set M : Matrix (Fin S.j) (Fin (0 + q)) ℝ :=
    Matrix.of fun a i => eaEval S.X.c (eaD S.X.c i (S.h a)) z with hM
  have hsub : (Matrix.of fun (a : Fin S.j) (l : Fin q) =>
        eaEval S.X.c (eaD S.X.c (Fin.natAdd 0 l) (S.h a)) z)
      = M.submatrix id (Fin.natAdd 0) := by
    ext a l; simp [M]
  rw [hsub] at hrank0
  have hle : (M.submatrix id (Fin.natAdd 0)).rank ≤ M.rank :=
    Matrix.rank_submatrix_le M id (Fin.natAdd 0)
  have hht : M.rank ≤ S.j := Matrix.rank_le_height M
  have hrank : M.rank = S.j := by omega
  -- the derivative is the `pi` of the rows of `M`
  rw [Work.WilE5.Strat.fderiv_pi_eaEval]
  exact pi_surjective_of_rank_eq_card (fun a i => eaEval S.X.c (eaD S.X.c i (S.h a)) z)
    (by rw [← hM]; exact hrank)

end Work.WilE9G.Sard
