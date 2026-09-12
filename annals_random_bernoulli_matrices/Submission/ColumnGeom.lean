import Mathlib
import Submission.GeoBridge
import Submission.NormalVectorMatrix
import Submission.Commons.LinearAlgebra.Net.incompressible_spread

set_option autoImplicit false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
open MeasureTheory InnerProductSpace
open scoped BigOperators

noncomputable section

/-!
# Geometry of the random normal (item (2) of the incompressible side)

For a unit vector `y` orthogonal to a subspace `V` and any `x`,
`|⟪x, y⟫| ≤ dist x V`.  We phrase the distance through the orthogonal
projection (`‖x − V.starProjection x‖`), which is what the events will use.
The deterministic inclusion of the σ_min-decomposition then reads: if
`f` has a large coordinate `|f_i|`, the distance of column `i` to the span
of the other columns is bounded by `‖A f‖ / |f_i|`.
-/

namespace Submission.ColumnGeom

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ## Abstract orthogonal-geometry facts -/

/-- For unit `y ∈ Vᵗ`, the inner product with `x` is bounded by the norm of
the orthogonal component of `x` (equivalently `dist x V`). -/
lemma abs_inner_le_norm_perp_component (V : Submodule ℝ E) [V.HasOrthogonalProjection]
    {x y : E} (hy_unit : ‖y‖ = 1) (hyV : y ∈ Vᗮ) :
    |inner ℝ x y| ≤ ‖x - V.starProjection x‖ := by
  let u : E := V.starProjection x
  let w : E := x - V.starProjection x
  have huV : u ∈ V := by
    dsimp [u]
    exact V.starProjection_apply_mem x
  have hwV : w ∈ Vᗮ := by
    dsimp [w]
    exact V.sub_starProjection_mem_orthogonal x
  -- x = u + w
  have hx : x = u + w := by
    dsimp [u, w]
    abel
  -- ⟪u, y⟫ = 0 since u ∈ V and y ∈ Vᗮ
  have huin : inner ℝ u y = 0 := by
    have hyu : inner ℝ y u = 0 := (V.mem_orthogonal' y).1 hyV u huV
    exact inner_eq_zero_symm.mp hyu
  have hwperp : inner ℝ w y = inner ℝ (x - V.starProjection x) y := by rfl
  calc
    |inner ℝ x y| = |inner ℝ (u + w) y| := by rw [hx]
    _ = |inner ℝ u y + inner ℝ w y| := by rw [inner_add_left]
    _ = |inner ℝ w y| := by simp [huin]
    _ ≤ ‖w‖ * ‖y‖ := by
      -- |⟪w, y⟫| ≤ ‖w‖‖y‖ : via norm_inner_le_norm (real norm = abs)
      simpa using (norm_inner_le_norm (𝕜 := ℝ) w y)
    _ = ‖w‖ := by simp [hy_unit]
    _ = ‖x - V.starProjection x‖ := by rfl

/-- Adding a vector of `V` to `w ∈ Vᵗ` can only increase the norm of `w`
(Pythagoras). -/
lemma norm_perp_le_norm_add (V : Submodule ℝ E) [V.HasOrthogonalProjection]
    {v w : E} (hv : v ∈ V) (hw : w ∈ Vᗮ) :
    ‖w‖ ≤ ‖v + w‖ := by
  -- ‖v + w‖² = ‖v‖² + ‖w‖² ≥ ‖w‖², then take roots
  have hin : inner ℝ v w = 0 := by
    have hwv : inner ℝ w v = 0 := (V.mem_orthogonal' w).1 hw v hv
    exact inner_eq_zero_symm.mp hwv
  have hsq : ‖v + w‖ ^ 2 = ‖v‖ ^ 2 + ‖w‖ ^ 2 := by
    calc
      ‖v + w‖ ^ 2 = inner ℝ (v + w) (v + w) := by
        simpa using (inner_self_eq_norm_sq (𝕜 := ℝ) (v + w)).symm
      _ = inner ℝ v v + inner ℝ v w + inner ℝ w v + inner ℝ w w := by
        rw [inner_add_left, inner_add_right, inner_add_right]
        ring
      _ = inner ℝ v v + inner ℝ w w := by simp [hin, inner_eq_zero_symm.mpr hin]
      _ = ‖v‖ ^ 2 + ‖w‖ ^ 2 := by
        simp [inner_self_eq_norm_sq]
  have hnonneg : 0 ≤ ‖v + w‖ := norm_nonneg _
  have hge : ‖w‖ ^ 2 ≤ ‖v + w‖ ^ 2 := by
    rw [hsq]
    nlinarith [sq_nonneg ‖v‖]
  -- from ‖w‖² ≤ ‖v+w‖² and both ≥ 0
  have h1 : |‖w‖| ≤ |‖v + w‖| := (sq_le_sq.mp hge)
  simpa [abs_of_nonneg (norm_nonneg w), abs_of_nonneg (norm_nonneg (v + w))] using h1


/-! ## Deterministic inclusion for matrices -/

open Submission.NormalVectorMatrix (colVec)

/-- The span of all columns of `M` except the `i`-th. -/
def othersSpan {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    Submodule ℝ (Submission.GeoBridge.E n) :=
  Submodule.span ℝ (Set.range (fun k : {j : Fin n // j ≠ i} => colVec M (k : Fin n)))

/-- `Σ_j f_j • col_j = M f` (column decomposition of the matrix action). -/
lemma sum_cols_eq_toEuclideanLin {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (f : Fin n → ℝ) :
    M.toEuclideanLin (WithLp.toLp 2 f : Submission.GeoBridge.E n) = ∑ j : Fin n, f j • colVec M j := by
  have hfun : (fun a : Fin n => (M.toEuclideanLin (WithLp.toLp 2 f : Submission.GeoBridge.E n)).ofLp a) =
      fun a : Fin n => (∑ j : Fin n, f j • colVec M j).ofLp a := by
    funext a
    calc
      (M.toEuclideanLin (WithLp.toLp 2 f : Submission.GeoBridge.E n)).ofLp a = ∑ j : Fin n, M a j * f j := by
        exact Submission.GeoBridge.coeff_toEuclideanLin M (WithLp.toLp 2 f) a
      _ = ∑ j : Fin n, (f j • colVec M j).ofLp a := by
        apply Finset.sum_congr rfl
        intro j hj
        simp [colVec]
        ring
      _ = (∑ j : Fin n, f j • colVec M j).ofLp a := by
        simp
  calc
    M.toEuclideanLin (WithLp.toLp 2 f : Submission.GeoBridge.E n)
        = (WithLp.toLp 2 ((M.toEuclideanLin (WithLp.toLp 2 f : Submission.GeoBridge.E n)).ofLp) : Submission.GeoBridge.E n) := by
            rfl
    _ = (WithLp.toLp 2 ((∑ j : Fin n, f j • colVec M j).ofLp) : Submission.GeoBridge.E n) := by
            exact congrArg (fun g : Fin n → ℝ => (WithLp.toLp 2 g : Submission.GeoBridge.E n)) hfun
    _ = ∑ j : Fin n, f j • colVec M j := by rfl

/-- Deterministic inclusion: if `f` is a vector with `|f_i| > 0`, the distance
of column `i` to the span of the other columns is at most `‖M f‖ / |f_i|`. -/
theorem colDist_mul_coord_le_normAct {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (i : Fin n)
    (f : Fin n → ℝ) :
    ‖colVec M i - (othersSpan M i).starProjection (colVec M i)‖ * |f i| ≤
      ‖M.toEuclideanLin (WithLp.toLp 2 f : Submission.GeoBridge.E n)‖ := by
  let S : Submodule ℝ (Submission.GeoBridge.E n) := othersSpan M i
  let c : Fin n → Submission.GeoBridge.E n := colVec M
  let w : Submission.GeoBridge.E n := c i - S.starProjection (c i)
  have hwS : w ∈ Sᗮ := by
    dsimp [w]
    exact S.sub_starProjection_mem_orthogonal (c i)
  have hprojS : S.starProjection (c i) ∈ S := by
    exact S.starProjection_apply_mem (c i)
  -- the "V part" of M f
  let v : Submission.GeoBridge.E n := (∑ j ∈ (Finset.univ.erase i : Finset (Fin n)), f j • c j) + f i • S.starProjection (c i)
  have hc_mem : ∀ j : Fin n, j ≠ i → c j ∈ S := by
    intro j hj
    dsimp [S, othersSpan]
    exact Submodule.subset_span ⟨⟨j, hj⟩, rfl⟩
  have hsumS : (∑ j ∈ (Finset.univ.erase i : Finset (Fin n)), f j • c j) ∈ S := by
    refine S.sum_mem ?_
    intro j hj
    exact S.smul_mem (f j) (hc_mem j (Finset.mem_erase.mp hj).1)
  have hvS : v ∈ S := by
    dsimp [v]
    exact S.add_mem hsumS (S.smul_mem (f i) hprojS)
  -- decomposition: v + f_i • w = Σ_j f_j • c_j
  have hdecomp : v + f i • w = ∑ j : Fin n, f j • c j := by
    dsimp [v, w]
    -- Σ over erase i plus f_i c_i = Σ over univ; and f_i c_i = f_i proj + f_i (c_i − proj)
    have hsplit : (∑ j ∈ (Finset.univ.erase i : Finset (Fin n)), f j • c j) + f i • c i =
        ∑ j : Fin n, f j • c j := by
      -- (∑ j ∈ univ.erase i, g j) + g i = ∑ j ∈ univ, g j
      have hsum := Finset.sum_erase_add (s := (Finset.univ : Finset (Fin n))) (f := fun j => f j • c j) (a := i) (by simp)
      simpa using hsum
    have hcsub : f i • c i = f i • S.starProjection (c i) + f i • (c i - S.starProjection (c i)) := by
      rw [← smul_add]
      congr 1
      abel
    calc
      (∑ j ∈ (Finset.univ.erase i : Finset (Fin n)), f j • c j)
          + f i • S.starProjection (c i) + f i • (c i - S.starProjection (c i))
          = (∑ j ∈ (Finset.univ.erase i : Finset (Fin n)), f j • c j) + f i • c i := by
              rw [hcsub]
              abel
      _ = ∑ j : Fin n, f j • c j := hsplit
  -- main estimate
  calc
    ‖colVec M i - (othersSpan M i).starProjection (colVec M i)‖ * |f i|
        = ‖(f i) • w‖ := by
            dsimp [w, c]
            rw [norm_smul]
            simp [Real.norm_eq_abs]
            ring
    _ ≤ ‖v + f i • w‖ := norm_perp_le_norm_add S hvS (by
        exact Sᗮ.smul_mem (f i) hwS)
    _ = ‖∑ j : Fin n, f j • colVec M j‖ := by
            rw [← hdecomp]
    _ = ‖M.toEuclideanLin (WithLp.toLp 2 f : Submission.GeoBridge.E n)‖ := by
            rw [sum_cols_eq_toEuclideanLin M f]


/-! ## Counting over column-distance events

For an incompressible unit vector `f` with `‖M f‖ ≤ u`, the spread lemma gives
at least `(1/2)·ν²·δ·n` coordinates `i` with `|f_i| ≥ ν/(2√n)`, and for each
of them the deterministic inclusion gives `dist(col_i, V_i) ≤ 2u√n/ν`.  So
the number of `i` with small column-distance is at least that many. -/

/-- The distance of column `i` from the span of the other columns (as a
projection norm). -/
noncomputable def colDist {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) : ℝ :=
  ‖colVec M i - (othersSpan M i).starProjection (colVec M i)‖

/-- The number of columns whose distance to the span of the others is at most
`r`. -/
noncomputable def cntDist {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (r : ℝ) : ℕ := by
  classical
  exact (Finset.univ.filter (fun i : Fin n => colDist M i ≤ r)).card

/-- If every element of `σ` satisfies `P`, the size of `σ` is at most the
number of elements of the ambient type satisfying `P`. -/
lemma card_le_filter_card {n : ℕ} (σ : Finset (Fin n)) {P : Fin n → Prop}
    [DecidablePred P] (hP : ∀ i : Fin n, i ∈ σ → P i) :
    σ.card ≤ (Finset.univ.filter P).card := by
  exact Finset.card_le_card (by
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hP i hi⟩)

/-- Deterministic inclusion: an incompressible unit vector `f` with small
image under `M` forces many columns to be close to the span of the others. -/
theorem incomp_count_colDist_ge {n : ℕ} (hn : 1 ≤ n)
    (M : Matrix (Fin n) (Fin n) ℝ) {δ ν u : ℝ} (hδ0 : 0 < δ) (hν0 : 0 < ν)
    (hu : 0 ≤ u) {f : Fin n → ℝ} (hf : Commons.LinearAlgebra.Net.sqNorm f = 1)
    (hnot : ∀ z : Fin n → ℝ, Commons.LinearAlgebra.Net.sqNorm (f - z) ≤ ν ^ 2 →
        ¬ (((Finset.univ.filter (fun i => z i ≠ 0)).card : ℝ) ≤ δ * (n : ℝ)))
    (hMf : ‖M.toEuclideanLin (WithLp.toLp 2 f : Submission.GeoBridge.E n)‖ ≤ u) :
    (1 / 2) * ν ^ 2 * δ * (n : ℝ) ≤ (cntDist M (2 * u * Real.sqrt (n : ℝ) / ν) : ℝ) := by
  classical
  rcases Commons.LinearAlgebra.Net.incompressible_spread hn hδ0 hν0 f hf hnot with
    ⟨σ, hσcard, hσcoord⟩
  let r : ℝ := 2 * u * Real.sqrt (n : ℝ) / ν
  have hle_card : (σ.card : ℝ) ≤ (cntDist M r : ℝ) := by
    dsimp [cntDist]
    exact_mod_cast (card_le_filter_card σ (P := fun i : Fin n => colDist M i ≤ r) (by
      intro i hi
      have hfge : ν / (2 * Real.sqrt (n : ℝ)) ≤ |f i| := hσcoord i hi
      have hpos1 : 0 < ν / (2 * Real.sqrt (n : ℝ)) := by positivity
      have hfi_pos : 0 < |f i| := lt_of_lt_of_le hpos1 hfge
      have hineq1 : colDist M i ≤ u / |f i| := by
        have hmul := colDist_mul_coord_le_normAct M i f
        exact (le_div_iff₀ hfi_pos).2 (le_trans hmul hMf)
      have hineq2 : u / |f i| ≤ r := by
        dsimp [r]
        have hstep : u / |f i| ≤ u / (ν / (2 * Real.sqrt (n : ℝ))) := by
          exact div_le_div_of_nonneg_left hu hpos1 hfge
        have heq : u / (ν / (2 * Real.sqrt (n : ℝ))) =
            2 * u * Real.sqrt (n : ℝ) / ν := by
          field_simp [show ν / (2 * Real.sqrt (n : ℝ)) ≠ 0 by positivity, hν0.ne']
        rw [heq] at hstep
        exact hstep
      exact le_trans hineq1 hineq2))
  exact le_trans hσcard hle_card


/-- Orthogonal projections onto equal submodules are equal (instance-safe
version: the value is recovered from the membership/orthogonality properties,
independent of the `HasOrthogonalProjection` witnesses). -/
lemma starProjection_eq_of_submodule_eq (V W : Submodule ℝ E) [V.HasOrthogonalProjection]
    [W.HasOrthogonalProjection] (h : V = W) (x : E) :
    V.starProjection x = W.starProjection x := by
  have hmem : V.starProjection x ∈ W := by
    have := V.starProjection_apply_mem x
    simpa [h] using this
  have horth : x - V.starProjection x ∈ Wᗮ := by
    have hperp : Vᗮ = Wᗮ := congrArg (fun U : Submodule ℝ E => Uᗮ) h
    simpa [hperp] using (V.sub_starProjection_mem_orthogonal x)
  exact (Submodule.eq_starProjection_of_mem_orthogonal (K := W) (u := x)
    (v := V.starProjection x) hmem horth).symm

end Submission.ColumnGeom
