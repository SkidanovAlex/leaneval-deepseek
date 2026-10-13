import Mathlib
import Submission.Work.WilkiesH.Norm.Defs
import Submission.Work.WilkiesH.Omega.omega_poly_le
import Submission.Work.WilkiesH.Omega.omega_poly_lt
import Submission.Work.WilG5.Basic
import Submission.Work.WilG0.API

/-!
# `normPiece σ` is `Ω`-definable

The normalisation piece `normPiece σ = {x : ℝⁿ | ∀ i, x i ∈ shapeSet (σ i)}` is the
intersection over the coordinates of the four elementary half-space regions
`[0,1]`, `[-1,0]`, `(1,∞)`, `(-∞,-1)`.  Each of those is a finite intersection of
(at most two) elementary `Ω`-sets, so `normPiece σ` is `Ω`-definable with a format
and degree depending only on `n`:

* a single half-space `{x | c ≤ x i}`, `{x | x i ≤ c}`, `{x | c < x i}`, `{x | x i < c}`
  and the whole space lie in `S.Ω (4n+20) 8 n` (`Work.WilG5.leSet_mem`, `geSet_mem`,
  `ltSet_mem`, `gtSet_mem`, `univ_mem`);
* by the `SOMin.inter` axiom, an intersection of two such lies in `S.Ω (4n+21) 16 n`;
* intersecting over the `n` coordinates (again `SOMin.inter`) gives
  `normPiece σ ∈ S.Ω (4n+22) (∑ _ : Fin n, 16) n`.
-/

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilkiesH.Norm

open WilkiesDesign WilkiesConjecture

/-- `{x : ℝⁿ | c ≤ x i}` lies in `S.Ω (4n+20) 8 n` (uniformly in `i` and `c`). -/
private theorem halfspace_le_mem (S : SOMin) {n : ℕ} (i : Fin n) (c : ℝ) :
    {x : Fin n → ℝ | c ≤ x i} ∈ S.Ω (4 * n + 20) 8 n :=
  Work.WilG5.mem_mono (Work.WilG5.leSet_mem (S := S) i c) (4 * n + 20) 8
    (by omega) (by omega)

/-- `{x : ℝⁿ | x i ≤ c}` lies in `S.Ω (4n+20) 8 n` (uniformly in `i` and `c`). -/
private theorem halfspace_ge_mem (S : SOMin) {n : ℕ} (i : Fin n) (c : ℝ) :
    {x : Fin n → ℝ | x i ≤ c} ∈ S.Ω (4 * n + 20) 8 n :=
  Work.WilG5.mem_mono (Work.WilG5.geSet_mem (S := S) i c) (4 * n + 20) 8
    (by omega) (by omega)

/-- `{x : ℝⁿ | c < x i}` lies in `S.Ω (4n+20) 8 n` (uniformly in `i` and `c`). -/
private theorem halfspace_lt_mem (S : SOMin) {n : ℕ} (i : Fin n) (c : ℝ) :
    {x : Fin n → ℝ | c < x i} ∈ S.Ω (4 * n + 20) 8 n :=
  Work.WilG5.ltSet_mem (S := S) i c

/-- `{x : ℝⁿ | x i < c}` lies in `S.Ω (4n+20) 8 n` (uniformly in `i` and `c`). -/
private theorem halfspace_gt_mem (S : SOMin) {n : ℕ} (i : Fin n) (c : ℝ) :
    {x : Fin n → ℝ | x i < c} ∈ S.Ω (4 * n + 20) 8 n :=
  Work.WilG5.gtSet_mem (S := S) i c

/-- The whole space lies in `S.Ω (4n+20) 8 n`. -/
private theorem univ_mem' (S : SOMin) {n : ℕ} :
    (Set.univ : Set (Fin n → ℝ)) ∈ S.Ω (4 * n + 20) 8 n :=
  Work.WilG5.mem_mono (Work.WilG5.univ_mem (S := S) (n := n)) (4 * n + 20) 8
    (by omega) (by omega)

/-- Intersecting two sets in `S.Ω (4n+20) 8 n` costs one format and doubles the degree. -/
private theorem inter2_mem (S : SOMin) {n : ℕ} {A B : Set (Fin n → ℝ)}
    (hA : A ∈ S.Ω (4 * n + 20) 8 n) (hB : B ∈ S.Ω (4 * n + 20) 8 n) :
    A ∩ B ∈ S.Ω (4 * n + 21) 16 n :=
  Work.WilG5.mem_mono (Work.WilG0.Omega_inter2 (S := S) hA hB) (4 * n + 21) 16
    (by omega) (by omega)

/-- The coordinate condition `{x : ℝⁿ | x i ∈ shapeSet s}` lies in `S.Ω (4n+21) 16 n`
uniformly in `i` and `s`. -/
private theorem coordShape_mem (S : SOMin) {n : ℕ} (i : Fin n) (s : NormShape) :
    {x : Fin n → ℝ | x i ∈ shapeSet s} ∈ S.Ω (4 * n + 21) 16 n := by
  cases s
  · show {x : Fin n → ℝ | x i ∈ Set.Icc (0 : ℝ) 1} ∈ S.Ω (4 * n + 21) 16 n
    have h := inter2_mem (S := S) (A := {x : Fin n → ℝ | (0 : ℝ) ≤ x i})
      (B := {x : Fin n → ℝ | x i ≤ (1 : ℝ)}) (halfspace_le_mem S i 0)
      (halfspace_ge_mem S i 1)
    have he : {x : Fin n → ℝ | x i ∈ Set.Icc (0 : ℝ) 1} =
        {x : Fin n → ℝ | (0 : ℝ) ≤ x i} ∩ {x : Fin n → ℝ | x i ≤ (1 : ℝ)} := by
      ext x; simp [Set.mem_Icc]
    rw [he]; exact h
  · show {x : Fin n → ℝ | x i ∈ Set.Icc (-1 : ℝ) 0} ∈ S.Ω (4 * n + 21) 16 n
    have h := inter2_mem (S := S) (A := {x : Fin n → ℝ | (-1 : ℝ) ≤ x i})
      (B := {x : Fin n → ℝ | x i ≤ (0 : ℝ)}) (halfspace_le_mem S i (-1))
      (halfspace_ge_mem S i 0)
    have he : {x : Fin n → ℝ | x i ∈ Set.Icc (-1 : ℝ) 0} =
        {x : Fin n → ℝ | (-1 : ℝ) ≤ x i} ∩ {x : Fin n → ℝ | x i ≤ (0 : ℝ)} := by
      ext x; simp [Set.mem_Icc]
    rw [he]; exact h
  · show {x : Fin n → ℝ | x i ∈ Set.Ioi (1 : ℝ)} ∈ S.Ω (4 * n + 21) 16 n
    have h := inter2_mem (S := S) (A := {x : Fin n → ℝ | (1 : ℝ) < x i})
      (B := (Set.univ : Set (Fin n → ℝ))) (halfspace_lt_mem S i 1) (univ_mem' S)
    have he : {x : Fin n → ℝ | x i ∈ Set.Ioi (1 : ℝ)} =
        {x : Fin n → ℝ | (1 : ℝ) < x i} ∩ Set.univ := by
      ext x; simp [Set.mem_Ioi]
    rw [he]; exact h
  · show {x : Fin n → ℝ | x i ∈ Set.Iio (-1 : ℝ)} ∈ S.Ω (4 * n + 21) 16 n
    have h := inter2_mem (S := S) (A := {x : Fin n → ℝ | x i < (-1 : ℝ)})
      (B := (Set.univ : Set (Fin n → ℝ))) (halfspace_gt_mem S i (-1)) (univ_mem' S)
    have he : {x : Fin n → ℝ | x i ∈ Set.Iio (-1 : ℝ)} =
        {x : Fin n → ℝ | x i < (-1 : ℝ)} ∩ Set.univ := by
      ext x; simp [Set.mem_Iio]
    rw [he]; exact h

theorem normPiece_mem_alt {n : ℕ} (σ : Fin n → Work.WilkiesH.Norm.NormShape) :
    ∃ a b : ℕ, ∀ S : WilkiesDesign.SOMin, Work.WilkiesH.Norm.normPiece σ ∈ S.Ω a b n := by
  refine ⟨4 * n + 22, ∑ _ : Fin n, 16, fun S => ?_⟩
  have hsingle : ∀ i : Fin n,
      {x : Fin n → ℝ | x i ∈ shapeSet (σ i)} ∈ S.Ω (4 * n + 21) 16 n :=
    fun i => coordShape_mem S i (σ i)
  have h := S.inter (fun _ : Fin n => 16)
    (fun i : Fin n => {x : Fin n → ℝ | x i ∈ shapeSet (σ i)}) hsingle
  have he : (⋂ i : Fin n, {x : Fin n → ℝ | x i ∈ shapeSet (σ i)}) = normPiece σ := by
    ext x; simp [normPiece]
  rw [he] at h
  exact Work.WilG5.mem_mono h (4 * n + 22) (∑ _ : Fin n, 16) (by omega) le_rfl

end Work.WilkiesH.Norm
