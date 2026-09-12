import Mathlib
import Submission.Commons.Analysis.InnerProductSpace.norm_iMulti_orthonormal
import Submission.Commons.Analysis.InnerProductSpace.normSq_sum_swap_one
import Submission.Commons.Analysis.InnerProductSpace.orthonormal_normSq_sum_smul
import Submission.GeometryOfNumbers.ProjectionDistance

/-!
# Graph over an arbitrary orthonormal k-plane inside a reference plane (M2/M3 core)

Context: `E` a real finite-dimensional inner product space, `x : Submodule ℝ E` a
reference plane, `e : Fin k → E` an orthonormal family with each `e j ∈ x`, and
`c : Fin k → E` with each `c j ∈ xᗮ` (the "graph offsets").  The graph family is
`u j = e j + c j`, `V = span (range u)`, and the graph wedge `w = ιMulti u`.

**Block decomposition (M2)**: expanding `w` by multilinearity over `u = e + c` groups the
terms by the number of `c`-factors: block-0 (no `c`) is the unit vector `ιMulti e`
(`‖block0‖ = 1`), block-1 (one `c`) is the sum of the swap wedges
`Σ_j ιMulti (σ_j)` (`σ_j` = `e` with the `j`-th slot replaced by `c j`), whose
squared norm is `Σ_j ‖c j‖²` (commons `normSq_sum_swap_one`).

**Residual bound (M3, the generic part of E1(b))**: the orthogonal projection onto `x` fixes
each `e j` and kills each `c j`, so for `v = Σ_j α_j u_j ∈ V` we get
`π_x v = Σ_j α_j e_j`, `v - π_x v = Σ_j α_j c_j`, Pythagoras gives
`Σ_j α_j² ≤ ‖v‖²`, and Cauchy–Schwarz gives
`‖v - π_x v‖ ≤ √(Σ_j ‖c j‖²) · ‖v‖`, i.e. every unit vector of `V`
has residual at most `‖block1‖`.  Hence `planeResidual V x ≤ ‖block1‖` (E1(b) for the
ON-graph, with `‖block0‖ = 1`).

All results here are Mathlib-only.
-/

noncomputable section

open Module exteriorPower InnerProductGeometry Real
open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Submission.Bridge.ONGraph

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The graph family `u j = e j + c j`. -/
def graphVec {k : ℕ} (e c : Fin k → E) : Fin k → E := fun j => e j + c j

/-- The graph wedge `w = ιMulti u`. -/
def graphWedge {k : ℕ} (e c : Fin k → E) : ⋀[ℝ]^k E :=
  exteriorPower.ιMulti ℝ k (graphVec e c)

/-- The graph subspace `V = span (range u)`. -/
def graphSubspace {k : ℕ} (e c : Fin k → E) : Submodule ℝ E :=
  Submodule.span ℝ (Set.range (graphVec e c))

/-- Block-0 of the graph wedge: the wedge of the orthonormal base `e` alone. -/
def block0 {k : ℕ} (e : Fin k → E) : ⋀[ℝ]^k E := exteriorPower.ιMulti ℝ k e

/-- The `j`-th swap family: `e` with the slot `j` replaced by `c j`. -/
def swap {k : ℕ} (e c : Fin k → E) (j : Fin k) : Fin k → E :=
  fun r => if r = j then c j else e r

/-- Block-1 of the graph wedge: the sum of the one-`c` swap terms. -/
def block1 {k : ℕ} (e c : Fin k → E) : ⋀[ℝ]^k E :=
  (Finset.univ : Finset (Fin k)).sum (fun j : Fin k => exteriorPower.ιMulti ℝ k (swap e c j))

/-- `c j ∈ xᗮ` and `e i ∈ x` imply `⟨e i, c j⟩ = 0`. -/
lemma inner_e_c_zero {x : Submodule ℝ E} {k : ℕ} (e c : Fin k → E)
    (he_mem : ∀ j, e j ∈ x) (hc_orth : ∀ j, c j ∈ xᗮ) (i j : Fin k) :
    inner ℝ (e i) (c j) = 0 :=
  (Submodule.mem_orthogonal x (c j)).mp (hc_orth j) (e i) (he_mem i)

/-- **M2, block-0**: the wedge of the orthonormal base `e` is a unit vector. -/
lemma block0_norm_one {k : ℕ} (e : Fin k → E) (he : Orthonormal ℝ e) (hk : 0 < k) :
    ‖block0 e‖ = 1 :=
  Commons.Analysis.InnerProductSpace.norm_iMulti_orthonormal e he hk

/-- **M2, block-1**: the squared norm of the one-`c` swap sum is `Σ_j ‖c j‖²`. -/
lemma block1_normSq {x : Submodule ℝ E} {k : ℕ} (e c : Fin k → E)
    (he : Orthonormal ℝ e) (he_mem : ∀ j, e j ∈ x)
    (hc_orth : ∀ j, c j ∈ xᗮ) :
    ‖block1 e c‖ ^ 2 = (Finset.univ : Finset (Fin k)).sum (fun j : Fin k => ‖c j‖ ^ 2) :=
  Commons.Analysis.InnerProductSpace.normSq_sum_swap_one e c he
    (inner_e_c_zero (x := x) e c he_mem hc_orth)

/-- `π_x (e j + c j) = e j` for `e j ∈ x`, `c j ∈ xᗮ`. -/
lemma starProj_graphVec {x : Submodule ℝ E} {k : ℕ} (e c : Fin k → E)
    (he_mem : ∀ j, e j ∈ x) (hc_orth : ∀ j, c j ∈ xᗮ) (j : Fin k) :
    x.starProjection (graphVec e c j) = e j := by
  have hfix : x.starProjection (e j) = e j := by
    exact Submodule.starProjection_eq_self_iff.mpr (he_mem j)
  have hkill : x.starProjection (c j) = 0 := by
    exact Submodule.eq_starProjection_of_mem_orthogonal (K := x) (u := c j) (v := 0)
      (by simp) (by simpa using hc_orth j)
  unfold graphVec
  rw [map_add, hfix, hkill, add_zero]

/-- `π_x (Σ_j α_j • u j) = Σ_j α_j • e j`. -/
lemma starProj_sum {x : Submodule ℝ E} {k : ℕ} (e c : Fin k → E)
    (he_mem : ∀ j, e j ∈ x) (hc_orth : ∀ j, c j ∈ xᗮ) (α : Fin k → ℝ) :
    x.starProjection (Finset.univ.sum (fun j : Fin k => α j • graphVec e c j)) =
      Finset.univ.sum (fun j : Fin k => α j • e j) := by
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [map_smul]
  rw [starProj_graphVec (x := x) e c he_mem hc_orth j]

/-- The residual of a combination is the combination of the `c j`'s:
`(Σ α_j u_j) − π_x(Σ α_j u_j) = Σ α_j c_j`. -/
lemma residual_sum_eq {x : Submodule ℝ E} {k : ℕ} (e c : Fin k → E)
    (he_mem : ∀ j, e j ∈ x) (hc_orth : ∀ j, c j ∈ xᗮ) (α : Fin k → ℝ) :
    (Finset.univ.sum (fun j : Fin k => α j • graphVec e c j)) -
        x.starProjection (Finset.univ.sum (fun j : Fin k => α j • graphVec e c j)) =
      Finset.univ.sum (fun j : Fin k => α j • c j) := by
  rw [starProj_sum (x := x) e c he_mem hc_orth α]
  calc
    (Finset.univ.sum (fun j : Fin k => α j • graphVec e c j)) -
        Finset.univ.sum (fun j : Fin k => α j • e j)
        = Finset.univ.sum (fun j : Fin k =>
            (α j • graphVec e c j) - (α j • e j)) := by
            rw [Finset.sum_sub_distrib]
    _ = Finset.univ.sum (fun j : Fin k => α j • c j) := by
          apply Finset.sum_congr rfl
          intro j hj
          unfold graphVec
          simp [smul_add]

/-- Pythagoras + projection: `Σ_j α_j² ≤ ‖Σ_j α_j u_j‖²`. -/
lemma sum_coeff_sq_le_normSq {x : Submodule ℝ E} {k : ℕ} (e c : Fin k → E)
    (he : Orthonormal ℝ e) (he_mem : ∀ j, e j ∈ x) (hc_orth : ∀ j, c j ∈ xᗮ)
    (α : Fin k → ℝ) :
    (Finset.univ.sum (fun j : Fin k => (α j) ^ 2)) ≤
      ‖Finset.univ.sum (fun j : Fin k => α j • graphVec e c j)‖ ^ 2 := by
  let v : E := Finset.univ.sum (fun j : Fin k => α j • graphVec e c j)
  have hsplit : ‖v‖ ^ 2 = ‖x.starProjection v‖ ^ 2 + ‖(xᗮ).starProjection v‖ ^ 2 := by
    exact Submodule.norm_sq_eq_add_norm_sq_starProjection v x
  have hproj : ‖x.starProjection v‖ ^ 2 = Finset.univ.sum (fun j : Fin k => (α j) ^ 2) := by
    calc
      ‖x.starProjection v‖ ^ 2 =
          ‖Finset.univ.sum (fun j : Fin k => α j • e j)‖ ^ 2 := by
            rw [starProj_sum (x := x) e c he_mem hc_orth α]
      _ = Finset.univ.sum (fun j : Fin k => (α j) ^ 2) := by
            exact Commons.Analysis.InnerProductSpace.orthonormal_normSq_sum_smul e he α
  rw [hproj] at hsplit
  nlinarith

/-- Squared residual bound (Cauchy–Schwarz): `‖v − π_x v‖² ≤ (Σ‖c j‖²) · ‖v‖²`. -/
lemma residual_normSq_le {x : Submodule ℝ E} {k : ℕ} (e c : Fin k → E)
    (he : Orthonormal ℝ e) (he_mem : ∀ j, e j ∈ x) (hc_orth : ∀ j, c j ∈ xᗮ)
    (α : Fin k → ℝ) :
    ‖(Finset.univ.sum (fun j : Fin k => α j • graphVec e c j)) -
        x.starProjection (Finset.univ.sum (fun j : Fin k => α j • graphVec e c j))‖ ^ 2 ≤
      (Finset.univ.sum (fun j : Fin k => ‖c j‖ ^ 2)) *
        ‖Finset.univ.sum (fun j : Fin k => α j • graphVec e c j)‖ ^ 2 := by
  have hcs := Submission.ProjectionDistance.cs_comb_normSq α c
  have hres : ‖(Finset.univ.sum (fun j : Fin k => α j • graphVec e c j)) -
      x.starProjection (Finset.univ.sum (fun j : Fin k => α j • graphVec e c j))‖ ^ 2 =
      ‖Finset.univ.sum (fun j : Fin k => α j • c j)‖ ^ 2 := by
    rw [residual_sum_eq (x := x) e c he_mem hc_orth α]
  calc
    ‖(Finset.univ.sum (fun j : Fin k => α j • graphVec e c j)) -
        x.starProjection (Finset.univ.sum (fun j : Fin k => α j • graphVec e c j))‖ ^ 2
        = ‖Finset.univ.sum (fun j : Fin k => α j • c j)‖ ^ 2 := hres
    _ ≤ (Finset.univ.sum (fun j : Fin k => (α j) ^ 2)) *
          (Finset.univ.sum (fun j : Fin k => ‖c j‖ ^ 2)) := hcs
    _ ≤ (Finset.univ.sum (fun j : Fin k => ‖c j‖ ^ 2)) *
          ‖Finset.univ.sum (fun j : Fin k => α j • graphVec e c j)‖ ^ 2 := by
          have hsum := sum_coeff_sq_le_normSq (x := x) e c he he_mem hc_orth α
          have hcs_nonneg : 0 ≤ Finset.univ.sum (fun j : Fin k => ‖c j‖ ^ 2) :=
            Finset.sum_nonneg (fun j hj => sq_nonneg _)
          nlinarith


/-- Membership in the graph subspace is equivalent to a `Fin k`-indexed representation. -/
lemma graph_mem_span_iff {k : ℕ} (e c : Fin k → E) (v : E) :
    v ∈ graphSubspace e c ↔ ∃ a : Fin k → ℝ,
      (Finset.univ.sum (fun j : Fin k => a j • graphVec e c j)) = v := by
  unfold graphSubspace
  exact (Submodule.mem_span_range_iff_exists_fun (R := ℝ) (M := E)
    (v := graphVec e c) (x := v))

/-- **M3, vector form**: for every `v ∈ V = span (range u)`, the residual from `x` is at
most `‖block1‖ · ‖v‖`. -/
lemma residual_le_block1 {x : Submodule ℝ E} {k : ℕ} (e c : Fin k → E)
    (he : Orthonormal ℝ e) (he_mem : ∀ j, e j ∈ x) (hc_orth : ∀ j, c j ∈ xᗮ) :
    ∀ ⦃v : E⦄, v ∈ graphSubspace e c →
      ‖v - x.starProjection v‖ ≤ ‖block1 e c‖ * ‖v‖ := by
  intro v hv
  rcases (graph_mem_span_iff e c v).mp hv with ⟨a, ha⟩
  have hb := residual_normSq_le (x := x) e c he he_mem hc_orth a
  have hb1 : ‖block1 e c‖ ^ 2 = Finset.univ.sum (fun j : Fin k => ‖c j‖ ^ 2) :=
    block1_normSq (x := x) e c he he_mem hc_orth
  have hb2 : ‖(Finset.univ.sum (fun j : Fin k => a j • graphVec e c j)) -
        x.starProjection (Finset.univ.sum (fun j : Fin k => a j • graphVec e c j))‖ ≤
      ‖block1 e c‖ * ‖(Finset.univ.sum (fun j : Fin k => a j • graphVec e c j))‖ := by
    have hnonneg : 0 ≤ ‖block1 e c‖ * ‖(Finset.univ.sum (fun j : Fin k => a j • graphVec e c j))‖ :=
      mul_nonneg (norm_nonneg _) (norm_nonneg _)
    rw [← hb1] at hb
    rw [← mul_pow] at hb
    exact (sq_le_sq₀ (norm_nonneg _) hnonneg).mp hb
  simpa [ha] using hb2

/-- **M3, unit form**: every unit vector of `V` has residual at most `‖block1‖`. -/
lemma unit_residual_le_block1 {x : Submodule ℝ E} {k : ℕ} (e c : Fin k → E)
    (he : Orthonormal ℝ e) (he_mem : ∀ j, e j ∈ x) (hc_orth : ∀ j, c j ∈ xᗮ) :
    ∀ ⦃v : E⦄, v ∈ graphSubspace e c → ‖v‖ = 1 →
      ‖v - x.starProjection v‖ ≤ ‖block1 e c‖ := by
  intro v hv hv1
  have h := residual_le_block1 (x := x) e c he he_mem hc_orth hv
  simpa [hv1] using h

/-- Pythagoras for the graph vector: `‖u j‖² = 1 + ‖c j‖²` (`e ᗮ c`). -/
lemma graphVec_normSq {x : Submodule ℝ E} {k : ℕ} (e c : Fin k → E)
    (he : Orthonormal ℝ e) (he_mem : ∀ j, e j ∈ x) (hc_orth : ∀ j, c j ∈ xᗮ) (j : Fin k) :
    ‖graphVec e c j‖ ^ 2 = 1 + ‖c j‖ ^ 2 := by
  have hec : inner ℝ (e j) (c j) = 0 := inner_e_c_zero (x := x) e c he_mem hc_orth j j
  have hce : inner ℝ (c j) (e j) = 0 := inner_eq_zero_symm.mp hec
  have hnorm_e : ‖e j‖ ^ 2 = 1 := by
    have h1 : ‖e j‖ = 1 := he.norm_eq_one j
    nlinarith [sq_nonneg (‖e j‖)]
  unfold graphVec
  calc
    ‖e j + c j‖ ^ 2 = inner ℝ (e j + c j) (e j + c j) := by
          exact (inner_self_eq_norm_sq_to_K (e j + c j)).symm
    _ = 1 + ‖c j‖ ^ 2 := by
          simp only [inner_add_left, inner_add_right, hec, hce]
          simp [hnorm_e]

/-- The graph vector `u j` is nonzero. -/
lemma graphVec_ne_zero {x : Submodule ℝ E} {k : ℕ} (e c : Fin k → E)
    (he : Orthonormal ℝ e) (he_mem : ∀ j, e j ∈ x) (hc_orth : ∀ j, c j ∈ xᗮ) (j : Fin k) :
    graphVec e c j ≠ 0 := by
  intro h
  have hs := graphVec_normSq (x := x) e c he he_mem hc_orth j
  rw [h] at hs
  have hs0 : (0 : ℝ) = 1 + ‖c j‖ ^ 2 := by simpa using hs
  nlinarith [sq_nonneg (‖c j‖)]

/-- **M3, operator form**: the distance from the graph subspace `V` to `x` is at most
`‖block1‖` (E1(b) for the ON-graph, since `‖block0‖ = 1`). -/
lemma planeResidual_le_block1 {x : Submodule ℝ E} {k : ℕ} (hk : 0 < k)
    (e c : Fin k → E) (he : Orthonormal ℝ e) (he_mem : ∀ j, e j ∈ x)
    (hc_orth : ∀ j, c j ∈ xᗮ) :
    Submission.ProjectionDistance.planeResidual (graphSubspace e c) x ≤ ‖block1 e c‖ := by
  classical
  let V : Submodule ℝ E := graphSubspace e c
  let S : Set ℝ := {r : ℝ | ∃ v : E, v ∈ V ∧ ‖v‖ = 1 ∧
    ‖v - ((x.orthogonalProjectionOnto v : E))‖ = r}
  have hnonempty : S.Nonempty := by
    let i₀ : Fin k := ⟨0, hk⟩
    let u₀ : E := graphVec e c i₀
    let v₀ : E := (1 / ‖u₀‖) • u₀
    refine ⟨‖v₀ - ((x.orthogonalProjectionOnto v₀ : E))‖, ?_⟩
    refine ⟨v₀, ?hvV, ?hv1, rfl⟩
    · have hu₀ : u₀ ∈ V := by
        refine Submodule.subset_span ?_
        exact Set.mem_range.mpr ⟨i₀, rfl⟩
      exact Submodule.smul_mem _ _ hu₀
    · have hpos : 0 < ‖u₀‖ := by
        exact norm_pos_iff.mpr (graphVec_ne_zero (x := x) e c he he_mem hc_orth i₀)
      simp [v₀, norm_smul, hpos.ne']
  refine csSup_le hnonempty ?_
  intro r hr
  rcases hr with ⟨v, hvV, hv1, rfl⟩
  have h := unit_residual_le_block1 (x := x) e c he he_mem hc_orth hvV hv1
  simpa using h

end Submission.Bridge.ONGraph
