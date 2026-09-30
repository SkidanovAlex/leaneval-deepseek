import Mathlib
import Submission.Work.Cohomology.Mesh

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The mesh of `affComp v w` for a bary-nested vertex family `w`

This file proves the metric estimate behind the "small simplices" theorem: if `w` is a
bary-nested family of points of `Δⁿ` (each `w j` is the uniform average of a nonempty subset
`S j ⊆ Fin (n+1)` of the vertices, the subsets forming a *decreasing* chain in `j`), then

`meshVF (affComp v w) ≤ (n / (n+1)) * meshVF v`

for any vertex family `v`.  Since `affComp v w i = affineSimplex v (w i)` is the centroid of the
vertices `{v l : l ∈ S i}`, and `S j ⊆ S i` whenever `i ≤ j`, the whole vertex set of `affComp v w`
has diameter at most `(1 - 1/(n+1)) · diam (range v)`: subtracting the centroid of the *larger*
subset, the components indexed by the larger subset cancel, leaving `|S i \ S j| / |S i|` terms of
the identity.  This is the geometric heart of the proof that barycentric subdivision shrinks mesh.

## Main results

* `dist_centerMass_le` — a point is within `D` of the uniform average of a family all of whose
  members are within `D` of it (triangle inequality for convex combinations);
* `centroid_sub_eq` — the exact algebraic identity
  `centroid(B) - centroid(S) = 1/|B| • ∑_{B∖S} (x l - centroid(S))` for `S ⊆ B`;
* `dist_centroid_subset_le` — the resulting sharp diameter estimate between two nested centroids;
* `diam_affComp_le` — the requested theorem.
-/

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

/-! ### The ambient coordinates of `affineSimplex v (baryOf A hA)` -/

/-- The affine simplex with vertices `v`, evaluated at the barycentre of the vertex subset `A`, is
the uniform average of the vertices `v l`, `l ∈ A` (in the ambient vector space `Fin (N+1) → ℝ`). -/
theorem affineSimplex_baryOf_coe {N : ℕ} (v : Fin (N + 1) → stdSimplex ℝ (Fin (N + 1)))
    (A : Finset (Fin (N + 1))) (hA : A.Nonempty) :
    Subtype.val (affineSimplex v (baryOf A hA))
      = ∑ l ∈ A, ((A.card : ℝ))⁻¹ • Subtype.val (v l) := by
  ext c
  change ((affineSimplex v (baryOf A hA) : stdSimplex ℝ (Fin (N + 1))) : Fin (N + 1) → ℝ) c
      = (∑ l ∈ A, ((A.card : ℝ))⁻¹ • Subtype.val (v l)) c
  rw [affineSimplex_apply]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, baryOf_apply, ite_mul, zero_mul]
  rw [Finset.sum_ite_mem, Finset.univ_inter]
  exact Finset.sum_congr rfl fun x _ => rfl

/-! ### Metric estimate for a single uniform average -/

/-- Weighted triangle inequality: the distance from a "convex" combination `∑ aₗ • xₗ` to the
point `(∑ aₗ) • y` is at most `∑ aₗ ‖xₗ - y‖` (for nonnegative weights). -/
theorem dist_sum_smul_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type*} (s : Finset ι) (a : ι → ℝ) (ha : ∀ l ∈ s, 0 ≤ a l) (x : ι → E) (y : E) :
    ‖(∑ l ∈ s, a l • x l) - (∑ l ∈ s, a l) • y‖ ≤ ∑ l ∈ s, a l * ‖x l - y‖ := by
  have h : (∑ l ∈ s, a l • x l) - (∑ l ∈ s, a l) • y = ∑ l ∈ s, a l • (x l - y) := by
    rw [Finset.sum_smul, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun l _ => (smul_sub _ _ _).symm
  rw [h]
  calc ‖∑ l ∈ s, a l • (x l - y)‖ ≤ ∑ l ∈ s, ‖a l • (x l - y)‖ := norm_sum_le _ _
    _ = ∑ l ∈ s, a l * ‖x l - y‖ := by
        apply Finset.sum_congr rfl; intro l hl
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (ha l hl)]

/-- A point `y` is within `D` of the uniform average of a nonempty family, provided it is within
`D` of every member. -/
theorem dist_centerMass_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (x : ι → E) (y : E) (D : ℝ)
    (hD : ∀ l ∈ s, dist (x l) y ≤ D) :
    dist (∑ l ∈ s, ((s.card : ℝ))⁻¹ • x l) y ≤ D := by
  have hcard : (s.card : ℝ) ≠ 0 := by exact_mod_cast Finset.card_ne_zero.mpr hs
  have hsum : ∑ l ∈ s, ((s.card : ℝ))⁻¹ = 1 := by
    rw [Finset.sum_const, nsmul_eq_mul, mul_inv_cancel₀ hcard]
  have hkey := dist_sum_smul_le s (fun _ : ι => ((s.card : ℝ))⁻¹) (fun l _ => by positivity) x y
  rw [hsum, one_smul] at hkey
  rw [dist_eq_norm]
  refine le_trans hkey ?_
  calc ∑ l ∈ s, ((s.card : ℝ))⁻¹ * ‖x l - y‖
      = ∑ l ∈ s, ((s.card : ℝ))⁻¹ * dist (x l) y := by
        apply Finset.sum_congr rfl; intro l _; rw [dist_eq_norm]
    _ ≤ ∑ l ∈ s, ((s.card : ℝ))⁻¹ * D := by
        refine Finset.sum_le_sum fun l hl => ?_
        exact mul_le_mul_of_nonneg_left (hD l hl) (by positivity)
    _ = D := by rw [← Finset.sum_mul, hsum, one_mul]

/-! ### The exact algebraic identity between nested centroids -/

/-- For `A ⊆ B`, the difference of the two uniform averages equals the uniform average over
`B \ A` of the differences to the average over `A`. -/
theorem centroid_sub_eq {E : Type*} [AddCommGroup E] [Module ℝ E] {ι : Type*} [DecidableEq ι]
    (A B : Finset ι) (hA : A.Nonempty) (hAB : A ⊆ B) (x : ι → E) :
    (∑ l ∈ B, ((B.card:ℝ))⁻¹ • x l) - (∑ l ∈ A, ((A.card:ℝ))⁻¹ • x l)
      = ((B.card:ℝ))⁻¹ • ∑ l ∈ B \ A, (x l - (∑ k ∈ A, ((A.card:ℝ))⁻¹ • x k)) := by
  set p : E := ∑ k ∈ A, ((A.card:ℝ))⁻¹ • x k with hp
  have hAne : (A.card : ℝ) ≠ 0 := by exact_mod_cast Finset.card_ne_zero.mpr hA
  have hBne : (B.card : ℝ) ≠ 0 := by exact_mod_cast Finset.card_ne_zero.mpr (hA.mono hAB)
  have hcA : (A.card : ℝ) * ((A.card : ℝ))⁻¹ = 1 := mul_inv_cancel₀ hAne
  have hcB : (B.card : ℝ) * ((B.card : ℝ))⁻¹ = 1 := mul_inv_cancel₀ hBne
  have hsumA : ∑ k ∈ A, x k = (A.card : ℝ) • p := by
    rw [hp, Finset.smul_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [smul_smul, hcA, one_smul]
  have h1 : ∑ l ∈ B, ((B.card:ℝ))⁻¹ • (x l - p) = (∑ l ∈ B, ((B.card:ℝ))⁻¹ • x l) - p := by
    simp_rw [smul_sub]
    rw [Finset.sum_sub_distrib]
    congr 1
    rw [← Finset.sum_smul, Finset.sum_const, nsmul_eq_mul, hcB, one_smul]
  have h2 : ∑ l ∈ A, ((B.card:ℝ))⁻¹ • (x l - p) = 0 := by
    rw [← Finset.smul_sum, Finset.sum_sub_distrib, hsumA, Finset.sum_const,
        ← Nat.cast_smul_eq_nsmul ℝ A.card p, sub_self, smul_zero]
  rw [← h1, ← Finset.sum_sdiff hAB, h2, add_zero, Finset.smul_sum]

/-- **The nested-centroid diameter estimate.**  For nonempty `A ⊆ B`, the uniform averages of the
families `(x l)_{l ∈ A}` and `(x l)_{l ∈ B}` are at most `|B \ A| / |B| · D` apart, where `D`
bounds the diameter of `(x l)_{l ∈ B}`. -/
theorem dist_centroid_subset_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type*} [DecidableEq ι] (A B : Finset ι) (hA : A.Nonempty) (hAB : A ⊆ B)
    (x : ι → E) (D : ℝ)
    (hD : ∀ l ∈ B, ∀ k ∈ B, dist (x l) (x k) ≤ D) :
    dist (∑ l ∈ A, ((A.card:ℝ))⁻¹ • x l) (∑ l ∈ B, ((B.card:ℝ))⁻¹ • x l)
      ≤ (((B \ A).card : ℝ) / (B.card : ℝ)) * D := by
  set p : E := ∑ l ∈ A, ((A.card:ℝ))⁻¹ • x l with hp
  have hp_bound : ∀ l ∈ B, dist (x l) p ≤ D := by
    intro l hl
    rw [hp, dist_comm]
    refine dist_centerMass_le A hA x (x l) D fun k hk => ?_
    exact hD k (hAB hk) l hl
  have key : (∑ l ∈ B, ((B.card:ℝ))⁻¹ • x l) - p = ((B.card:ℝ))⁻¹ • ∑ l ∈ B \ A, (x l - p) := by
    rw [hp]; exact centroid_sub_eq A B hA hAB x
  rw [dist_eq_norm, norm_sub_rev, key, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hnorm : ‖∑ l ∈ B \ A, (x l - p)‖ ≤ ((B \ A).card : ℝ) * D := by
    calc ‖∑ l ∈ B \ A, (x l - p)‖ ≤ ∑ l ∈ B \ A, ‖x l - p‖ := norm_sum_le _ _
      _ ≤ ∑ l ∈ B \ A, D := by
          refine Finset.sum_le_sum fun l hl => ?_
          simpa only [dist_eq_norm] using hp_bound l (Finset.mem_sdiff.mp hl).1
      _ = ((B \ A).card : ℝ) * D := by rw [Finset.sum_const, nsmul_eq_mul]
  calc ((B.card:ℝ))⁻¹ * ‖∑ l ∈ B \ A, (x l - p)‖
      ≤ ((B.card:ℝ))⁻¹ * (((B\A).card : ℝ) * D) :=
        mul_le_mul_of_nonneg_left hnorm (by positivity)
    _ = ((B\A).card : ℝ) / (B.card:ℝ) * D := by rw [div_eq_mul_inv]; ring

/-! ### Arithmetic of the cardinality ratio -/

/-- `(A - B)/A ≤ n/(n+1)` for `1 ≤ B ≤ A ≤ n+1`. -/
theorem card_sub_div_le (n A B : ℕ) (hB : 1 ≤ B) (hBA : B ≤ A) (hAn : A ≤ n + 1) :
    ((A - B : ℕ) : ℝ) / (A : ℝ) ≤ (n : ℝ) / (n + 1) := by
  have hApos : (0 : ℝ) < A := by
    have h : 0 < A := lt_of_lt_of_le hB hBA
    exact_mod_cast h
  have hcast : ((A - B : ℕ) : ℝ) = (A : ℝ) - (B : ℝ) := by rw [Nat.cast_sub hBA]
  rw [hcast]
  have h1B : (1 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB
  have hAle : (A : ℝ) ≤ (n : ℝ) + 1 := by
    have h : (A : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast hAn
    push_cast at h ⊢; linarith
  have hkey : (A : ℝ) ≤ ((n : ℝ) + 1) * (B : ℝ) := by
    calc (A : ℝ) ≤ (n : ℝ) + 1 := hAle
      _ = ((n : ℝ) + 1) * 1 := by ring
      _ ≤ ((n : ℝ) + 1) * (B : ℝ) := by
          exact mul_le_mul_of_nonneg_left h1B (by positivity)
  rw [div_le_iff₀ hApos, div_mul_eq_mul_div, le_div_iff₀ (by positivity : (0:ℝ) < (n:ℝ) + 1)]
  nlinarith [hkey]

/-! ### The main theorem -/

/-- **Mesh shrinks under `affComp` with a bary-nested family.**  If `w` is bary-nested then the
diameter of the vertex set of `affComp v w` is at most `n/(n+1)` times the diameter of the vertex
set of `v`. -/
theorem diam_affComp_le (n : ℕ) (v w : Fin (n + 1) → stdSimplex ℝ (Fin (n + 1)))
    (hw : IsBaryNested w) :
    meshVF (affComp v w) ≤ ((n : ℝ) / (n + 1)) * meshVF v := by
  obtain ⟨S, hS, hmono, hwj⟩ := hw
  set X : Fin (n + 1) → (Fin (n + 1) → ℝ) := fun l => Subtype.val (v l) with hX
  have hbdd : Bornology.IsBounded (Set.range v) := (Set.finite_range v).isBounded
  have hDv : ∀ l k : Fin (n + 1), dist (X l) (X k) ≤ meshVF v := by
    intro l k
    rw [hX, ← Subtype.dist_eq]
    exact Metric.dist_le_diam_of_mem hbdd (Set.mem_range_self l) (Set.mem_range_self k)
  have hcoe : ∀ (A : Finset (Fin (n + 1))) (hA : A.Nonempty),
      Subtype.val (affineSimplex v (baryOf A hA)) = ∑ l ∈ A, ((A.card : ℝ))⁻¹ • X l := by
    intro A hA
    rw [affineSimplex_baryOf_coe, hX]
  -- reduce to a pairwise distance estimate on the vertex set
  refine Metric.diam_le_of_forall_dist_le ?_ ?_
  · exact mul_nonneg (div_nonneg (Nat.cast_nonneg n) (by positivity)) Metric.diam_nonneg
  · intro x hx y hy
    rcases hx with ⟨i, rfl⟩
    rcases hy with ⟨j, rfl⟩
    rcases le_total i j with hij | hji
    · -- `i ≤ j`, so `S j ⊆ S i`; the centroid of the smaller set `S j` is compared with `S i`
      have hstep := dist_centroid_subset_le (S j) (S i) (hS j) (hmono i j hij) X (meshVF v)
        (fun l _ k _ => hDv l k)
      have hcoef : (((S i \ S j).card : ℝ) / ((S i).card : ℝ)) ≤ (n : ℝ) / (n + 1) := by
        rw [Finset.card_sdiff_of_subset (hmono i j hij)]
        exact card_sub_div_le n ((S i).card) ((S j).card) (Finset.card_pos.mpr (hS j))
          (Finset.card_le_card (hmono i j hij))
          (by simpa [Fintype.card_fin] using Finset.card_le_univ (S i))
      rw [affComp, affComp, hwj i, hwj j, Subtype.dist_eq, dist_comm,
        hcoe (S i) (hS i), hcoe (S j) (hS j)]
      exact le_trans hstep (mul_le_mul_of_nonneg_right hcoef Metric.diam_nonneg)
    · -- `j ≤ i`, so `S i ⊆ S j`
      have hstep := dist_centroid_subset_le (S i) (S j) (hS i) (hmono j i hji) X (meshVF v)
        (fun l _ k _ => hDv l k)
      have hcoef : (((S j \ S i).card : ℝ) / ((S j).card : ℝ)) ≤ (n : ℝ) / (n + 1) := by
        rw [Finset.card_sdiff_of_subset (hmono j i hji)]
        exact card_sub_div_le n ((S j).card) ((S i).card) (Finset.card_pos.mpr (hS i))
          (Finset.card_le_card (hmono j i hji))
          (by simpa [Fintype.card_fin] using Finset.card_le_univ (S j))
      rw [affComp, affComp, hwj i, hwj j, Subtype.dist_eq,
        hcoe (S i) (hS i), hcoe (S j) (hS j)]
      exact le_trans hstep (mul_le_mul_of_nonneg_right hcoef Metric.diam_nonneg)

end

end Work.Cohomology
