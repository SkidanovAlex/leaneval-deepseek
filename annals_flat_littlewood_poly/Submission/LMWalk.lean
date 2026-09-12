import Mathlib
import Submission.LMAux

/-!
The Lovett--Meka partial-colouring walk.

We define a discrete Gaussian walk in `EuclideanSpace ℝ (Fin n)` which freezes (a) a variable
coordinate `i` once `|x i| ≥ 1 - δ` and (b) a discrepancy constraint `j` once
`|⟪x - x0, v j⟫| ≥ (c j - δ) * ‖v j‖`.  The walk steps orthogonally to all frozen constraints.
-/

open scoped BigOperators RealInnerProductSpace
open MeasureTheory ProbabilityTheory

noncomputable section

namespace Submission.Discrepancy

/-- Free coordinates: those not yet frozen. -/
def frozenVars {n : ℕ} (δ : ℝ) (x : Vec n) : Finset (Fin n) :=
  Finset.univ.filter (fun i : Fin n => 1 - δ ≤ |x i|)

/-- Frozen discrepancy rows. -/
def frozenRows {n : ℕ} {ι : Type*} [Fintype ι] (δ : ℝ) (x0 : Vec n) (v : ι → Vec n) (c : ι → ℝ)
    (x : Vec n) : Finset ι :=
  Finset.univ.filter (fun j : ι => (c j - δ) * ‖v j‖ ≤ |vin (x - x0) (v j)|)

/-- The span of the frozen constraint vectors. -/
def Wspan {n : ℕ} {ι : Type*} [Fintype ι] (v : ι → Vec n) (A : Finset (Fin n)) (B : Finset ι) :
    Submodule ℝ (Vec n) :=
  Submodule.span ℝ (((A.image (fun i : Fin n => basis n i)) : Set (Vec n)) ∪ (B.image v : Set (Vec n)))

/-- Projection onto the orthogonal complement of the frozen constraints. -/
def walkProj {n : ℕ} {ι : Type*} [Fintype ι] (v : ι → Vec n) (A : Finset (Fin n)) (B : Finset ι)
    (g : Vec n) : Vec n :=
  ((Wspan v A B)ᗮ).starProjection g

/-- One step of the walk. -/
def walkStep {n : ℕ} {ι : Type*} [Fintype ι] (δ γ : ℝ) (x0 : Vec n) (v : ι → Vec n) (c : ι → ℝ)
    (x : Vec n) (g : Vec n) : Vec n :=
  x + γ • walkProj v (frozenVars δ x) (frozenRows δ x0 v c x) g

/-- Trajectory of the walk with an oracle of Gaussians indexed by ℕ. -/
def xseq {n : ℕ} {ι : Type*} [Fintype ι] (δ γ : ℝ) (x0 : Vec n) (v : ι → Vec n) (c : ι → ℝ)
    (g : ℕ → Vec n) : ℕ → Vec n
  | 0 => x0
  | t + 1 => walkStep δ γ x0 v c (xseq δ γ x0 v c g t) (g t)

/-- Step increments. -/
def sinc {n : ℕ} {ι : Type*} [Fintype ι] (δ γ : ℝ) (x0 : Vec n) (v : ι → Vec n) (c : ι → ℝ)
    (g : ℕ → Vec n) (t : ℕ) : Vec n :=
  walkProj v (frozenVars δ (xseq δ γ x0 v c g t)) (frozenRows δ x0 v c (xseq δ γ x0 v c g t)) (g t)

@[simp] lemma xseq_succ {n : ℕ} {ι : Type*} [Fintype ι] (δ γ : ℝ) (x0 : Vec n) (v : ι → Vec n)
    (c : ι → ℝ) (g : ℕ → Vec n) (t : ℕ) :
    xseq δ γ x0 v c g (t + 1) = xseq δ γ x0 v c g t + γ • sinc δ γ x0 v c g t := rfl

@[simp] lemma xseq_zero {n : ℕ} {ι : Type*} [Fintype ι] (δ γ : ℝ) (x0 : Vec n) (v : ι → Vec n)
    (c : ι → ℝ) (g : ℕ → Vec n) : xseq δ γ x0 v c g 0 = x0 := rfl

/-- Telescoping: `xseq T - x0 = γ • Σ sinc t`. -/
lemma xseq_sub_eq_sum {n : ℕ} {ι : Type*} [Fintype ι] (δ γ : ℝ) (x0 : Vec n) (v : ι → Vec n)
    (c : ι → ℝ) (g : ℕ → Vec n) (T : ℕ) :
    xseq δ γ x0 v c g T - x0 = γ • ∑ t ∈ Finset.range T, sinc δ γ x0 v c g t := by
  induction T with
  | zero => simp [xseq]
  | succ T ih =>
      calc xseq δ γ x0 v c g (T + 1) - x0
          = (xseq δ γ x0 v c g T + γ • sinc δ γ x0 v c g T) - x0 := by rw [xseq_succ]
      _ = (xseq δ γ x0 v c g T - x0) + γ • sinc δ γ x0 v c g T := by abel
      _ = γ • ∑ t ∈ Finset.range T, sinc δ γ x0 v c g t + γ • sinc δ γ x0 v c g T := by
          rw [ih]
      _ = γ • (∑ t ∈ Finset.range T, sinc δ γ x0 v c g t + sinc δ γ x0 v c g T) := by
          rw [smul_add]
      _ = γ • ∑ t ∈ Finset.range (T + 1), sinc δ γ x0 v c g t := by
          rw [Finset.sum_range_succ]

/-- Projection kills frozen coordinates. -/
lemma walkProj_coord_zero {n : ℕ} {ι : Type*} [Fintype ι] (v : ι → Vec n) (A : Finset (Fin n))
    (B : Finset ι) (g : Vec n) {i : Fin n} (hi : i ∈ A) :
    (walkProj v A B g) i = 0 := by
  have hmem : walkProj v A B g ∈ (Wspan v A B)ᗮ := Submodule.starProjection_apply_mem _ _
  have hb : basis n i ∈ (Wspan v A B : Set (Vec n)) := by
    exact Submodule.subset_span (by
      left
      exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨i, hi, rfl⟩))
  have horth : vin (basis n i) (walkProj v A B g) = 0 :=
    ((Submodule.mem_orthogonal (K := Wspan v A B) (walkProj v A B g)).1 hmem) (basis n i) hb
  simpa [vin_basis] using horth

/-- Projection kills frozen rows. -/
lemma walkProj_row_zero {n : ℕ} {ι : Type*} [Fintype ι] (v : ι → Vec n) (A : Finset (Fin n))
    (B : Finset ι) (g : Vec n) {j : ι} (hj : j ∈ B) :
    vin (walkProj v A B g) (v j) = 0 := by
  have hmem : walkProj v A B g ∈ (Wspan v A B)ᗮ := Submodule.starProjection_apply_mem _ _
  have hb : v j ∈ (Wspan v A B : Set (Vec n)) := by
    exact Submodule.subset_span (by
      right
      exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨j, hj, rfl⟩))
  have hz0 : ⟪v j, walkProj v A B g⟫ = 0 :=
    ((Submodule.mem_orthogonal (K := Wspan v A B) (walkProj v A B g)).1 hmem) (v j) hb
  have hc := real_inner_comm (x := walkProj v A B g) (y := v j)
  simpa [vin] using hc.symm.trans hz0

/-- A frozen coordinate stays frozen. -/
lemma frozenVars_mono {n : ℕ} {ι : Type*} [Fintype ι] (δ γ : ℝ) (x0 : Vec n) (v : ι → Vec n)
    (c : ι → ℝ) (g : ℕ → Vec n) (t : ℕ) : frozenVars δ (xseq δ γ x0 v c g t) ⊆
    frozenVars δ (xseq δ γ x0 v c g (t + 1)) := by
  intro i hi
  have hstep : (xseq δ γ x0 v c g (t + 1)) i = (xseq δ γ x0 v c g t) i := by
    rw [xseq_succ]
    have hz : (sinc δ γ x0 v c g t) i = 0 := by
      simpa [sinc] using (walkProj_coord_zero v (frozenVars δ (xseq δ γ x0 v c g t))
        (frozenRows δ x0 v c (xseq δ γ x0 v c g t)) (g t) hi)
    simp [hz]
  unfold frozenVars at hi ⊢
  simp only [Finset.mem_univ, Finset.mem_filter, true_and] at hi ⊢
  rw [hstep]
  exact hi

/-- A frozen row stays frozen. -/
lemma frozenRows_mono {n : ℕ} {ι : Type*} [Fintype ι] (δ γ : ℝ) (x0 : Vec n) (v : ι → Vec n)
    (c : ι → ℝ) (g : ℕ → Vec n) (t : ℕ) : frozenRows δ x0 v c (xseq δ γ x0 v c g t) ⊆
    frozenRows δ x0 v c (xseq δ γ x0 v c g (t + 1)) := by
  intro j hj
  have hz : vin (sinc δ γ x0 v c g t) (v j) = 0 := by
    simpa [sinc] using (walkProj_row_zero v (frozenVars δ (xseq δ γ x0 v c g t))
      (frozenRows δ x0 v c (xseq δ γ x0 v c g t)) (g t) hj)
  have hx : vin (xseq δ γ x0 v c g (t + 1) - x0) (v j) =
      vin (xseq δ γ x0 v c g t - x0) (v j) := by
    rw [xseq_succ]
    have hbil : vin (xseq δ γ x0 v c g t + γ • sinc δ γ x0 v c g t - x0) (v j)
        = vin (xseq δ γ x0 v c g t - x0) (v j) + γ * vin (sinc δ γ x0 v c g t) (v j) := by
      simp [vin, inner_add_left, inner_smul_left, inner_sub_left, inner_sub_right,
        inner_add_right]
      ring
    rw [hbil, hz, mul_zero, add_zero]
  unfold frozenRows at hj ⊢
  simp only [Finset.mem_univ, Finset.mem_filter, true_and] at hj ⊢
  rw [hx]
  exact hj

/-- Frozen coordinate sets grow with the trajectory. -/
lemma frozenVars_subset_of_le {n : ℕ} {ι : Type*} [Fintype ι] (δ γ : ℝ) (x0 : Vec n) (v : ι → Vec n)
    (c : ι → ℝ) (g : ℕ → Vec n) {s t : ℕ} (hst : s ≤ t) :
    frozenVars δ (xseq δ γ x0 v c g s) ⊆ frozenVars δ (xseq δ γ x0 v c g t) := by
  refine Nat.le_induction ?_ ?_ t hst
  · intro x hx; exact hx
  · intro t hst ih i hi
    exact frozenVars_mono δ γ x0 v c g t (ih hi)

/-- Frozen row sets grow with the trajectory. -/
lemma frozenRows_subset_of_le {n : ℕ} {ι : Type*} [Fintype ι] (δ γ : ℝ) (x0 : Vec n) (v : ι → Vec n)
    (c : ι → ℝ) (g : ℕ → Vec n) {s t : ℕ} (hst : s ≤ t) :
    frozenRows δ x0 v c (xseq δ γ x0 v c g s) ⊆ frozenRows δ x0 v c (xseq δ γ x0 v c g t) := by
  refine Nat.le_induction ?_ ?_ t hst
  · intro x hx; exact hx
  · intro t hst ih i hi
    exact frozenRows_mono δ γ x0 v c g t (ih hi)

end Discrepancy

end Submission
