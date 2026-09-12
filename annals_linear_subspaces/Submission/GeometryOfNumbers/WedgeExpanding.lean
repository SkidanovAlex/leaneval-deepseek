import Mathlib
import Submission.GeometryOfNumbers.WedgeContract
import Submission.GeometryOfNumbers.LargeBlockCovering
import Submission.Commons.Analysis.InnerProductSpace.norm_iMulti_orthonormal
import Submission.Commons.Analysis.InnerProductSpace.exteriorPower_norm_wedge_le_prod
import Submission.Commons.Analysis.Real.sum_log_norm_annulus
import Submission.Commons.Analysis.Real.sum_log_norm_interval

/-!
# Wedges of directions inside the expanding block: the `∧^k x₀ᗮ`-decomposition

Model setting: `x₀ = modelX ℓ` is the coordinate `ℓ`-plane (the real span of the
contracting block); its orthogonal complement `x₀ᗮ` is the real span of the **expanding**
block (`LargeBlockCovering.largeSpan ℓ`: `Span {(B d) j | j.val ≥ ℓ}`, dimension `d − ℓ`).
This module is the mirror of `WedgeContract` on the expanding side: for a family
`u : Fin k → ℝᵈ` of vectors inside `x₀ᗮ`,

* the wedge `ιMulti u` is its own block-`k` component: `blockElem (ιMulti u) k = ιMulti u`
  (the degree-`k` block — subsets with all `k` indices `≥ ℓ` — is `∧^k x₀ᗮ`, and the
  projection `π₁ := ⋀^k (1 − P₀)` onto it acts as the identity);
* `π₁` is the orthogonal projection onto the degree-`k` block: `pi1_apply`:
  `π₁ w = blockElem w k` (`blockElem_k_eq_map_modelProjComp`), so it is bounded
  (`norm_pi1_le`), idempotent (`pi1_idempotent`), fixes wedges of families inside
  `x₀ᗮ`/the expanding block (`pi1_ιMulti_of_mem_largeSpan`), and preserves unit norms
  there (`norm_pi1_ιMulti_of_orthonormal`);
* the `π₁`-perturbation lower-bound chain: for an orthonormal `u` inside `x₀ᗮ` and a unit
  family `v` within `1/5` of `u` pointwise, `1 − k/5 ≤ ‖π₁(ιMulti v)‖`
  (`norm_pi1_ιMulti_ge_sub_one_fifth_of_largeSpan`); scaled by `∏ᵢ‖v i‖` for a nonzero
  annulus family (`norm_pi1_ιMulti_ge_mul_sub_one_fifth_of_largeSpan`);
* the block-annulus assembly mirroring `WedgeContract`'s contracting-block lock, fed by
  `LargeBlockCovering.exists_largeFamily_annulus`: for an ON family `u` of unit directions
  in `largeSpan` and an annulus family `v : Fin k → largeFlow a b ℓ` around
  `11·(d−ℓ:ℝ)b·u` per index, the two-sided `π₁`-sandwich
  `(∏ᵢ‖v i‖)·(1 − k/5) ≤ ‖π₁(ιMulti v)‖ ≤ ∏ᵢ‖v i‖` (`wedgeLarge_blockAnnulus_twoSided`)
  and its log forms (`wedgeLarge_blockAnnulus_log_twoSided`), with the exponential-flow
  instances (`a = e^{−t/ℓ}`, `b = e^{t/(d−ℓ)}` — suffix `_exp`).

All results are Mathlib-only (besides the Submission geometry modules).
-/

noncomputable section

open Module exteriorPower InnerProductGeometry Real
open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

open Submission.ExteriorCoordinates
open Submission.DiagonalFlow
open Submission.WedgeBlocks
open Submission.WedgeBlockZero

namespace Submission.WedgeExpanding

variable {d k : ℕ}

/-- The orthogonal projection onto the complement `x₀ᗮ` of the model plane: `1 − P₀` (the
projection onto `x₀` kills exactly the orthogonal complement, since the ambient space is
the orthogonal sum `x₀ ⊕ x₀ᗮ`). -/
def modelProjComp (ℓ : ℕ) : RD d →ₗ[ℝ] RD d :=
  (1 : RD d →ₗ[ℝ] RD d) - modelProj (d := d) ℓ

/-- The complement projection subtracts the `x₀`-projection: `(1 − P₀) v = v − P₀ v`. -/
lemma modelProjComp_apply (ℓ : ℕ) (v : RD d) :
    modelProjComp ℓ v = v - modelProj (d := d) ℓ v := rfl

/-- The complement projection kills the low standard vectors (those of `x₀`). -/
lemma modelProjComp_std_low (ℓ : ℕ) (j : Fin d) (hj : j.val < ℓ) :
    modelProjComp ℓ ((B d) j) = 0 := by
  rw [modelProjComp_apply, modelProj_std_low (d := d) ℓ j hj]
  simp

/-- The complement projection fixes the high standard vectors (those of `x₀ᗮ`). -/
lemma modelProjComp_std_high (ℓ : ℕ) (j : Fin d) (hj : ℓ ≤ j.val) :
    modelProjComp ℓ ((B d) j) = (B d) j := by
  rw [modelProjComp_apply, modelProj_std_high (d := d) ℓ j hj]
  simp

/-- **Block-`k` = `⋀^k(1 − P₀)`**: the degree-`k` block component of a `k`-vector (subsets
with all `k` indices `≥ ℓ`, i.e. the `∧^k x₀ᗮ` part) equals the image under the induced
exterior-power map of the complement projection `1 − P₀`. -/
lemma blockElem_k_eq_map_modelProjComp (ℓ : ℕ) (w : WK d k) :
    blockElem (d := d) (k := k) (ℓ := ℓ) w k =
      exteriorPower.map k (modelProjComp ℓ) w := by
  classical
  let cnt : IDX d k → ℕ := fun s =>
    ((s : Finset (Fin d)).filter (fun i : Fin d => ℓ ≤ i.val)).card
  have hbasis : ∀ s : IDX d k,
      exteriorPower.map k (modelProjComp ℓ) ((Bk d k) s : WK d k) =
        if cnt s = k then ((Bk d k) s : WK d k) else 0 := by
    intro s
    let σ : Fin k → Fin d := Set.powersetCard.ofFinEmbEquiv.symm s
    have hb : ((Bk d k) s : WK d k) =
        exteriorPower.ιMulti ℝ k (fun r : Fin k => (B d) (σ r)) :=
      basisWedge_eq_enumWedge (d := d) (k := k) s
    by_cases hs : cnt s = k
    · rw [if_pos hs]
      have hsubf : (s : Finset (Fin d)).filter (fun i : Fin d => ℓ ≤ i.val) ⊆ s :=
        Finset.filter_subset _ _
      have hfeq : (s : Finset (Fin d)).filter (fun i : Fin d => ℓ ≤ i.val) = s := by
        refine Finset.eq_of_subset_of_card_le hsubf ?_
        have h1 : (s : Finset (Fin d)).card = k := s.2
        have h2 : cnt s = k := hs
        dsimp [cnt] at h2
        omega
      have hσge : ∀ r : Fin k, ℓ ≤ (σ r).val := by
        intro r
        have hmem : σ r ∈ (s : Finset (Fin d)) := by
          exact (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem (s := s) (i := σ r)).mp
            (Set.mem_range.mpr ⟨r, rfl⟩)
        have hf : σ r ∈ (s : Finset (Fin d)).filter (fun i : Fin d => ℓ ≤ i.val) := by
          rw [hfeq]
          exact hmem
        exact (Finset.mem_filter.mp hf).2
      calc
        exteriorPower.map k (modelProjComp ℓ) ((Bk d k) s : WK d k)
            = exteriorPower.map k (modelProjComp ℓ)
                (exteriorPower.ιMulti ℝ k (fun r : Fin k => (B d) (σ r))) := by rw [hb]
        _ = exteriorPower.ιMulti ℝ k (fun r : Fin k => modelProjComp ℓ ((B d) (σ r))) := by
              rw [exteriorPower.map_apply_ιMulti]
              rfl
        _ = exteriorPower.ιMulti ℝ k (fun r : Fin k => (B d) (σ r)) := by
              apply congrArg (exteriorPower.ιMulti ℝ k)
              funext r
              exact modelProjComp_std_high (d := d) ℓ (σ r) (hσge r)
        _ = ((Bk d k) s : WK d k) := by rw [← hb]
    · rw [if_neg hs]
      have hsome : ∃ r : Fin k, (σ r).val < ℓ := by
        by_contra hnone
        have hall : ∀ r : Fin k, ℓ ≤ (σ r).val := fun r => le_of_not_gt (by
          intro h
          exact hnone ⟨r, h⟩)
        have hfeq : (s : Finset (Fin d)).filter (fun i : Fin d => ℓ ≤ i.val) = s := by
          ext x
          constructor
          · intro hx
            exact (Finset.mem_filter.mp hx).1
          · intro hx
            refine Finset.mem_filter.mpr ⟨hx, ?_⟩
            have hxr : x ∈ Set.range σ :=
              (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem (s := s) (i := x)).mpr hx
            rcases (Set.mem_range.mp hxr) with ⟨r, hr⟩
            rw [← hr]
            exact hall r
        have hc : cnt s = k := by
          dsimp [cnt]
          rw [hfeq, s.2]
        exact hs hc
      rcases hsome with ⟨r, hrlt⟩
      have hzero : modelProjComp ℓ ((B d) (σ r)) = 0 :=
        modelProjComp_std_low (d := d) ℓ (σ r) hrlt
      calc
        exteriorPower.map k (modelProjComp ℓ) ((Bk d k) s : WK d k)
            = exteriorPower.map k (modelProjComp ℓ)
                (exteriorPower.ιMulti ℝ k (fun r : Fin k => (B d) (σ r))) := by rw [hb]
        _ = exteriorPower.ιMulti ℝ k (fun r : Fin k => modelProjComp ℓ ((B d) (σ r))) := by
              rw [exteriorPower.map_apply_ιMulti]
              rfl
        _ = 0 := by
              have hf : (fun r : Fin k => modelProjComp ℓ ((B d) (σ r))) r = 0 := by
                simpa using hzero
              exact AlternatingMap.map_coord_zero (exteriorPower.ιMulti ℝ k) r hf
  -- expand w in the standard basis and push the exterior-power map through the sum
  calc
    blockElem (d := d) (k := k) (ℓ := ℓ) w k
        = (blockFinset (d := d) (k := k) (ℓ := ℓ) k).sum (fun s =>
            wcoord (d := d) (k := k) w s • ((Bk d k) s : WK d k)) := by rfl
    _ = ((Finset.univ : Finset (IDX d k)).filter
          (fun s : IDX d k => cnt s = k)).sum (fun s =>
            wcoord (d := d) (k := k) w s • ((Bk d k) s : WK d k)) := by
          simp [blockFinset, cnt]
    _ = (Finset.univ : Finset (IDX d k)).sum (fun s =>
          if cnt s = k
          then wcoord (d := d) (k := k) w s • ((Bk d k) s : WK d k) else 0) := by
          rw [Finset.sum_filter]
    _ = (Finset.univ : Finset (IDX d k)).sum (fun s =>
          wcoord (d := d) (k := k) w s •
            (exteriorPower.map k (modelProjComp ℓ) ((Bk d k) s : WK d k))) := by
          apply Finset.sum_congr rfl
          intro s hs
          by_cases hc : cnt s = k
          · simp [hc, hbasis s]
          · simp [hc, hbasis s]
    _ = exteriorPower.map k (modelProjComp ℓ)
          ((Finset.univ : Finset (IDX d k)).sum (fun s =>
            wcoord (d := d) (k := k) w s • ((Bk d k) s : WK d k))) := by
          rw [map_sum]
          apply Finset.sum_congr rfl
          intro s hs
          rw [map_smul]
    _ = exteriorPower.map k (modelProjComp ℓ) w := by
          rw [sum_wcoord_smul_basis (d := d) (k := k) w]

/-- The orthogonal projection `π₁` onto `∧^k x₀ᗮ` (the degree-`k` block of the exterior
decomposition along `x₀ ⊕ x₀ᗮ`), as a linear map.  It equals `w ↦ blockElem w k`
(`pi1_apply`). -/
def pi1 (ℓ : ℕ) : WK d k →ₗ[ℝ] WK d k :=
  exteriorPower.map k (modelProjComp ℓ)

/-- `π₁` acts as the degree-`k` block component `w ↦ blockElem w k`. -/
lemma pi1_apply (ℓ : ℕ) (w : WK d k) :
    pi1 (d := d) (k := k) ℓ w = blockElem (d := d) (k := k) (ℓ := ℓ) w k := by
  unfold pi1
  exact (blockElem_k_eq_map_modelProjComp (d := d) (k := k) ℓ w).symm

/-- `π₁` is bounded with norm at most `1`: projecting onto the degree-`k` block cannot
increase the norm. -/
lemma norm_pi1_le (ℓ : ℕ) (w : WK d k) : ‖pi1 (d := d) (k := k) ℓ w‖ ≤ ‖w‖ := by
  rw [pi1_apply]
  have hle0 : ‖blockElem (d := d) (k := k) (ℓ := ℓ) w k‖ ^ 2 ≤
      (Finset.range (k + 1)).sum (fun r : ℕ =>
        ‖blockElem (d := d) (k := k) (ℓ := ℓ) w r‖ ^ 2) := by
    exact Finset.single_le_sum (s := Finset.range (k + 1))
      (f := fun r : ℕ => ‖blockElem (d := d) (k := k) (ℓ := ℓ) w r‖ ^ 2)
      (by intro r hr; exact sq_nonneg _) (a := k) (Finset.mem_range.mpr (by omega))
  have hle : ‖blockElem (d := d) (k := k) (ℓ := ℓ) w k‖ ^ 2 ≤ ‖w‖ ^ 2 := by
    rw [← sum_normSq_blockElem (d := d) (k := k) (ℓ := ℓ) w]
    exact hle0
  have habs : |‖blockElem (d := d) (k := k) (ℓ := ℓ) w k‖| ≤ |‖w‖| := sq_le_sq.mp hle
  have hb : 0 ≤ ‖blockElem (d := d) (k := k) (ℓ := ℓ) w k‖ := norm_nonneg _
  have hw : 0 ≤ ‖w‖ := norm_nonneg _
  simpa [abs_of_nonneg hb, abs_of_nonneg hw] using habs

/-- The real span of the expanding block is contained in `x₀ᗮ`. -/
lemma largeSpan_le_modelX_orth (ℓ : ℕ) :
    Submission.LargeBlockCovering.largeSpan (d := d) ℓ ≤ (modelX (d := d) ℓ)ᗮ := by
  change Submodule.span ℝ (Set.range (fun j : {j : Fin d // ℓ ≤ j.val} =>
    (B d) j.1)) ≤ (modelX (d := d) ℓ)ᗮ
  apply Submodule.span_le.mpr
  rintro x ⟨j, rfl⟩
  exact std_mem_modelX_orth (d := d) ℓ j.1 j.2

/-- The complement projection kills the vectors of `x₀`: `(1 − P₀) v = 0` for `v ∈ x₀`. -/
lemma modelProjComp_eq_zero_of_mem_modelX (ℓ : ℕ) {v : RD d} (hv : v ∈ modelX (d := d) ℓ) :
    modelProjComp ℓ v = 0 := by
  rw [modelProjComp_apply]
  rw [Submission.WedgeContract.modelProj_apply_of_mem_modelX (d := d) ℓ hv]
  simp

/-- The complement projection fixes the vectors of `x₀ᗮ`: `(1 − P₀) v = v` for
`v ∈ x₀ᗮ`. -/
lemma modelProjComp_eq_self_of_mem_orth (ℓ : ℕ) {v : RD d} (hv : v ∈ (modelX (d := d) ℓ)ᗮ) :
    modelProjComp ℓ v = v := by
  rw [modelProjComp_apply]
  unfold modelProj
  rw [Submission.WedgeGeneralE1.projMap_apply]
  have hz : (modelX (d := d) ℓ).starProjection v = 0 :=
    (Submission.WedgeGeneralE1.starProjection_eq_zero_iff_orthogonal (modelX (d := d) ℓ) v).mpr hv
  rw [hz]
  simp


/-! ### `π₁` on wedges of families in the expanding block, and the perturbation lower bound

The mirror of the `π₀`-perturbation chain of `WedgeContract`: `π₁` fixes wedges of
families inside the expanding block's real span, preserves unit norms of wedges of
orthonormal families there, is 1-Lipschitz, and — via the (generic, `E`-typed)
one-slot/telescoping machinery of `WedgeContract` — an orthonormal family `u` inside
`largeSpan` with a unit family `v` within `1/5` of `u` pointwise satisfies
`1 − k/5 ≤ ‖π₁(ιMulti v)‖`; scaling by `∏ᵢ‖v i‖` (normalisation `v̂ i = ‖v i‖⁻¹ • v i`)
gives `(∏ᵢ‖v i‖)·(1 − k/5) ≤ ‖π₁(ιMulti v)‖` for any nonzero annulus family `v`. -/

/-- `π₁` is the identity on wedges of families inside the real span of the expanding block
(the `largeFlow` setting): for `u i ∈ largeSpan ℓ` (⊆ `x₀ᗮ`), `π₁(ιMulti u) = ιMulti u`. -/
lemma pi1_ιMulti_of_mem_largeSpan (ℓ : ℕ) (u : Fin k → RD d)
    (hu : ∀ i, u i ∈ Submission.LargeBlockCovering.largeSpan (d := d) ℓ) :
    pi1 (d := d) (k := k) ℓ (exteriorPower.ιMulti ℝ k u) = exteriorPower.ιMulti ℝ k u := by
  have hfix : ∀ i, modelProjComp (d := d) ℓ (u i) = u i := by
    intro i
    exact modelProjComp_eq_self_of_mem_orth (d := d) ℓ
      ((largeSpan_le_modelX_orth (d := d) ℓ) (hu i))
  unfold pi1
  rw [exteriorPower.map_apply_ιMulti]
  apply congrArg (exteriorPower.ιMulti ℝ k)
  funext i
  exact hfix i

/-- `π₁` preserves the unit norm of wedges of orthonormal families inside `largeSpan`:
`‖π₁(ιMulti u)‖ = 1`. -/
lemma norm_pi1_ιMulti_of_orthonormal (ℓ : ℕ) (u : Fin k → RD d)
    (hu : ∀ i, u i ∈ Submission.LargeBlockCovering.largeSpan (d := d) ℓ)
    (huON : Orthonormal ℝ u) (hk : 0 < k) :
    ‖pi1 (d := d) (k := k) ℓ (exteriorPower.ιMulti ℝ k u)‖ = 1 := by
  rw [pi1_ιMulti_of_mem_largeSpan (d := d) (k := k) ℓ u hu]
  exact Commons.Analysis.InnerProductSpace.norm_iMulti_orthonormal (E := RD d) u huON hk

/-- `π₁` is 1-Lipschitz: `‖π₁ x − π₁ y‖ ≤ ‖x − y‖`. -/
lemma norm_pi1_sub_le (ℓ : ℕ) (x y : WK d k) :
    ‖pi1 (d := d) (k := k) ℓ x - pi1 (d := d) (k := k) ℓ y‖ ≤ ‖x - y‖ := by
  have hlin : pi1 (d := d) (k := k) ℓ (x - y) =
      pi1 (d := d) (k := k) ℓ x - pi1 (d := d) (k := k) ℓ y := by
    exact map_sub (pi1 (d := d) (k := k) ℓ) x y
  rw [← hlin]
  exact norm_pi1_le (d := d) (k := k) ℓ (x - y)

/-- **Reverse triangle for `π₁`**: if `π₁` fixes a unit vector `w` and `z` is within `ε` of
`w`, then `‖π₁ z‖ ≥ 1 − ε`. -/
lemma norm_pi1_ge_sub_of_unit_fixed (ℓ : ℕ) (w z : WK d k) (hw1 : ‖w‖ = 1)
    (hfix : pi1 (d := d) (k := k) ℓ w = w) {ε : ℝ} (hε : ‖z - w‖ ≤ ε) :
    1 - ε ≤ ‖pi1 (d := d) (k := k) ℓ z‖ := by
  have hfixnorm : ‖pi1 (d := d) (k := k) ℓ w‖ = 1 := by
    rw [hfix, hw1]
  have h₀ : ‖pi1 (d := d) (k := k) ℓ w‖ ≤ ‖pi1 (d := d) (k := k) ℓ w - pi1 (d := d) (k := k) ℓ z‖ +
      ‖pi1 (d := d) (k := k) ℓ z‖ := by
    have hveq : (pi1 (d := d) (k := k) ℓ w - pi1 (d := d) (k := k) ℓ z) +
        pi1 (d := d) (k := k) ℓ z = pi1 (d := d) (k := k) ℓ w := by abel
    have hmain := norm_add_le (pi1 (d := d) (k := k) ℓ w - pi1 (d := d) (k := k) ℓ z)
      (pi1 (d := d) (k := k) ℓ z)
    simpa [hveq] using hmain
  have hd : ‖pi1 (d := d) (k := k) ℓ w - pi1 (d := d) (k := k) ℓ z‖ ≤ ε := by
    have h1 := norm_pi1_sub_le (d := d) (k := k) ℓ w z
    have h2 : ‖w - z‖ ≤ ε := by simpa [norm_sub_rev] using hε
    exact le_trans h1 h2
  have h₁ : (1 : ℝ) ≤ ‖pi1 (d := d) (k := k) ℓ w - pi1 (d := d) (k := k) ℓ z‖ +
      ‖pi1 (d := d) (k := k) ℓ z‖ := by
    simpa [hfixnorm] using h₀
  linarith

/-- **`π₁`-lower bound on a unit family**: for an orthonormal family `u : Fin k → ℝᵈ` of
unit directions inside the expanding block's real span (`u i ∈ largeSpan ℓ`) and a **unit**
family `v` within `1/5` of `u` pointwise, `1 − k/5 ≤ ‖π₁(ιMulti v)‖`. -/
lemma norm_pi1_ιMulti_ge_sub_one_fifth_of_largeSpan (ℓ : ℕ) (u v : Fin k → RD d)
    (hu_mem : ∀ i, u i ∈ Submission.LargeBlockCovering.largeSpan (d := d) ℓ)
    (huON : Orthonormal ℝ u) (hk : 0 < k)
    (hv1 : ∀ i, ‖v i‖ = 1) (hclose : ∀ i, ‖v i - u i‖ ≤ (1 / 5 : ℝ)) :
    1 - (k : ℝ) / 5 ≤ ‖pi1 (d := d) (k := k) ℓ (exteriorPower.ιMulti ℝ k v)‖ := by
  let w : WK d k := exteriorPower.ιMulti ℝ k u
  let z : WK d k := exteriorPower.ιMulti ℝ k v
  have hw1 : ‖w‖ = 1 := by
    dsimp [w]
    exact Commons.Analysis.InnerProductSpace.norm_iMulti_orthonormal (E := RD d) u huON hk
  have hfix : pi1 (d := d) (k := k) ℓ w = w := by
    dsimp [w]
    exact pi1_ιMulti_of_mem_largeSpan (d := d) (k := k) ℓ u hu_mem
  have hb : ‖z - w‖ ≤ (k : ℝ) / 5 := by
    dsimp [w, z]
    exact Submission.WedgeContract.norm_ιMulti_sub_le_of_one_fifth (m := k) (u := u) (v := v)
      (fun j => huON.1 j) hv1 hclose
  have hgoal := norm_pi1_ge_sub_of_unit_fixed (d := d) (k := k) ℓ w z hw1 hfix
    (ε := (k : ℝ) / 5) hb
  simpa [w, z] using hgoal

/-- **`π₁`-scaling identity**: with `v̂ i := ‖v i‖⁻¹ • v i` (`v i ≠ 0`),
`‖π₁(ιMulti v)‖ = (∏ᵢ ‖v i‖) · ‖π₁(ιMulti v̂)‖`. -/
lemma norm_pi1_ιMulti_mul_normed (ℓ : ℕ) (v : Fin k → RD d) (hv0 : ∀ i, v i ≠ 0) :
    ‖pi1 (d := d) (k := k) ℓ (exteriorPower.ιMulti ℝ k v)‖ =
      (∏ i : Fin k, ‖v i‖) *
        ‖pi1 (d := d) (k := k) ℓ
          (exteriorPower.ιMulti ℝ k (fun i : Fin k => (‖v i‖⁻¹) • v i))‖ := by
  have hvi : ∀ i, ‖v i‖ • ((‖v i‖⁻¹) • v i) = v i := by
    intro i
    rw [smul_smul]
    rw [mul_inv_cancel₀ (norm_ne_zero_iff.mpr (hv0 i))]
    simp
  have hmain : exteriorPower.ιMulti ℝ k v =
      (∏ i : Fin k, ‖v i‖) •
        exteriorPower.ιMulti ℝ k (fun i : Fin k => (‖v i‖⁻¹) • v i) := by
    calc
      exteriorPower.ιMulti ℝ k v
          = exteriorPower.ιMulti ℝ k (fun i : Fin k => ‖v i‖ • ((‖v i‖⁻¹) • v i)) := by
              apply congrArg (exteriorPower.ιMulti ℝ k)
              funext i
              exact (hvi i).symm
      _ = (∏ i : Fin k, ‖v i‖) •
            exteriorPower.ιMulti ℝ k (fun i : Fin k => (‖v i‖⁻¹) • v i) := by
            exact DiagonalFlow.ιMulti_smul_univ (fun i : Fin k => ‖v i‖)
              (fun i : Fin k => (‖v i‖⁻¹) • v i)
  have hpi : pi1 (d := d) (k := k) ℓ (exteriorPower.ιMulti ℝ k v) =
      (∏ i : Fin k, ‖v i‖) •
        pi1 (d := d) (k := k) ℓ
          (exteriorPower.ιMulti ℝ k (fun i : Fin k => (‖v i‖⁻¹) • v i)) := by
    rw [hmain]
    rw [map_smul]
  have hnn : 0 ≤ (∏ i : Fin k, ‖v i‖) := Finset.prod_nonneg (fun i hi => norm_nonneg _)
  calc
    ‖pi1 (d := d) (k := k) ℓ (exteriorPower.ιMulti ℝ k v)‖
        = ‖(∏ i : Fin k, ‖v i‖) •
            pi1 (d := d) (k := k) ℓ
              (exteriorPower.ιMulti ℝ k (fun i : Fin k => (‖v i‖⁻¹) • v i))‖ := by rw [hpi]
    _ = (∏ i : Fin k, ‖v i‖) *
          ‖pi1 (d := d) (k := k) ℓ
            (exteriorPower.ιMulti ℝ k (fun i : Fin k => (‖v i‖⁻¹) • v i))‖ := by
          rw [norm_smul]
          rw [Real.norm_eq_abs]
          rw [abs_of_nonneg hnn]

/-- **`π₁`-lower bound with the `Π‖vᵢ‖` scaling**: for an orthonormal `u` of unit
directions inside the expanding block (`u i ∈ largeSpan ℓ`) and a nonzero annulus family
`v` whose normalisation `v̂ i = ‖v i‖⁻¹ • v i` is within `1/5` of `u` pointwise,
`(∏ᵢ ‖v i‖) · (1 − k/5) ≤ ‖π₁(ιMulti v)‖`. -/
theorem norm_pi1_ιMulti_ge_mul_sub_one_fifth_of_largeSpan (ℓ : ℕ) (u v : Fin k → RD d)
    (hu_mem : ∀ i, u i ∈ Submission.LargeBlockCovering.largeSpan (d := d) ℓ)
    (huON : Orthonormal ℝ u) (hk : 0 < k) (hv0 : ∀ i, v i ≠ 0)
    (hclose : ∀ i, ‖(‖v i‖⁻¹) • v i - u i‖ ≤ (1 / 5 : ℝ)) :
    (∏ i : Fin k, ‖v i‖) * (1 - (k : ℝ) / 5) ≤
      ‖pi1 (d := d) (k := k) ℓ (exteriorPower.ιMulti ℝ k v)‖ := by
  classical
  let vn : Fin k → RD d := fun i => (‖v i‖⁻¹) • v i
  have hv1 : ∀ i, ‖vn i‖ = 1 := by
    intro i
    dsimp [vn]
    exact Submission.WedgeContract.norm_smul_inv_eq_one (v i) (hv0 i)
  have hclose' : ∀ i, ‖vn i - u i‖ ≤ (1 / 5 : ℝ) := by
    intro i
    simpa [vn] using hclose i
  have hlow := norm_pi1_ιMulti_ge_sub_one_fifth_of_largeSpan (d := d) (k := k) ℓ u vn
    hu_mem huON hk hv1 hclose'
  have hprod0 : 0 ≤ (∏ i : Fin k, ‖v i‖) := Finset.prod_nonneg (fun i hi => norm_nonneg _)
  have hmul : (∏ i : Fin k, ‖v i‖) * (1 - (k : ℝ) / 5) ≤
      (∏ i : Fin k, ‖v i‖) * ‖pi1 (d := d) (k := k) ℓ
        (exteriorPower.ιMulti ℝ k vn)‖ := by
    exact mul_le_mul_of_nonneg_left hlow hprod0
  have heq : ‖pi1 (d := d) (k := k) ℓ (exteriorPower.ιMulti ℝ k v)‖ =
      (∏ i : Fin k, ‖v i‖) * ‖pi1 (d := d) (k := k) ℓ
        (exteriorPower.ιMulti ℝ k vn)‖ := by
    simpa [vn] using (norm_pi1_ιMulti_mul_normed (d := d) (k := k) ℓ v hv0)
  exact le_trans hmul (le_of_eq heq.symm)


/-- **`π₁`-lower bound on a unit family, general `k`**: for an orthonormal family
`u : Fin k → ℝᵈ` of unit directions in `largeSpan ℓ` and a **unit** family `v` whose
per-direction error is `≤ 2/(11k−1)` (the `k`-dependent normalisation of
`norm_smul_inv_sub_le_of_annulus_k`), `1 − 2k/(11k−1) ≤ ‖π₁(ιMulti v)‖` — the wedge loss
`2k/(11k−1) ≤ 2/10 < 1` is bounded INDEPENDENTLY of `k` (`k ≥ 1`), so no `k ≤ 4`
restriction is needed. -/
lemma norm_pi1_ιMulti_ge_sub_k_of_largeSpan (ℓ : ℕ) (u v : Fin k → RD d)
    (hu_mem : ∀ i, u i ∈ Submission.LargeBlockCovering.largeSpan (d := d) ℓ)
    (huON : Orthonormal ℝ u) (hk : 0 < k)
    (hv1 : ∀ i, ‖v i‖ = 1)
    (hclose : ∀ i, ‖v i - u i‖ ≤ 2 / ((11 : ℝ) * (k : ℝ) - 1)) :
    1 - (2 * (k : ℝ)) / ((11 : ℝ) * (k : ℝ) - 1) ≤
      ‖pi1 (d := d) (k := k) ℓ (exteriorPower.ιMulti ℝ k v)‖ := by
  let w : WK d k := exteriorPower.ιMulti ℝ k u
  let z : WK d k := exteriorPower.ιMulti ℝ k v
  have hw1 : ‖w‖ = 1 := by
    dsimp [w]
    exact Commons.Analysis.InnerProductSpace.norm_iMulti_orthonormal (E := RD d) u huON hk
  have hfix : pi1 (d := d) (k := k) ℓ w = w := by
    dsimp [w]
    exact pi1_ιMulti_of_mem_largeSpan (d := d) (k := k) ℓ u hu_mem
  have hsum : ‖z - w‖ ≤ (2 * (k : ℝ)) / ((11 : ℝ) * (k : ℝ) - 1) := by
    dsimp [w, z]
    have hsum0 : ‖exteriorPower.ιMulti ℝ k v - exteriorPower.ιMulti ℝ k u‖ ≤
        (∑ i : Fin k, ‖v i - u i‖) :=
      Submission.WedgeContract.norm_ιMulti_sub_le_sum (m := k) (u := u) (v := v)
        (fun j => huON.1 j) hv1
    have hsumle : (∑ i : Fin k, ‖v i - u i‖) ≤
        (2 * (k : ℝ)) / ((11 : ℝ) * (k : ℝ) - 1) := by
      calc
        (∑ i : Fin k, ‖v i - u i‖)
            ≤ (∑ _ : Fin k, (2 / ((11 : ℝ) * (k : ℝ) - 1))) := by
              apply Finset.sum_le_sum
              intro i hi
              exact hclose i
        _ = (k : ℝ) * (2 / ((11 : ℝ) * (k : ℝ) - 1)) := by
              simp [Finset.sum_const, Fintype.card_fin]
        _ = (2 * (k : ℝ)) / ((11 : ℝ) * (k : ℝ) - 1) := by ring
    exact le_trans hsum0 hsumle
  have hgoal := norm_pi1_ge_sub_of_unit_fixed (d := d) (k := k) ℓ w z hw1 hfix
    (ε := (2 * (k : ℝ)) / ((11 : ℝ) * (k : ℝ) - 1)) hsum
  simpa [w, z] using hgoal

/-- **`π₁`-lower bound with the `Π‖vᵢ‖` scaling, general `k`**: for an orthonormal `u` of
unit directions in the expanding block and a nonzero family `v` whose normalisation
`v̂ i = ‖v i‖⁻¹ • v i` is within `2/(11k−1)` of `u` pointwise,
`(∏ᵢ ‖v i‖) · (1 − 2k/(11k−1)) ≤ ‖π₁(ιMulti v)‖`. -/
theorem norm_pi1_ιMulti_ge_mul_sub_k_of_largeSpan (ℓ : ℕ) (u v : Fin k → RD d)
    (hu_mem : ∀ i, u i ∈ Submission.LargeBlockCovering.largeSpan (d := d) ℓ)
    (huON : Orthonormal ℝ u) (hk : 0 < k) (hv0 : ∀ i, v i ≠ 0)
    (hclose : ∀ i, ‖(‖v i‖⁻¹) • v i - u i‖ ≤ 2 / ((11 : ℝ) * (k : ℝ) - 1)) :
    (∏ i : Fin k, ‖v i‖) * (1 - (2 * (k : ℝ)) / ((11 : ℝ) * (k : ℝ) - 1)) ≤
      ‖pi1 (d := d) (k := k) ℓ (exteriorPower.ιMulti ℝ k v)‖ := by
  classical
  let vn : Fin k → RD d := fun i => (‖v i‖⁻¹) • v i
  have hv1 : ∀ i, ‖vn i‖ = 1 := by
    intro i
    dsimp [vn]
    exact Submission.WedgeContract.norm_smul_inv_eq_one (v i) (hv0 i)
  have hclose' : ∀ i, ‖vn i - u i‖ ≤ 2 / ((11 : ℝ) * (k : ℝ) - 1) := by
    intro i
    simpa [vn] using hclose i
  have hlow := norm_pi1_ιMulti_ge_sub_k_of_largeSpan (d := d) (k := k) ℓ u vn
    hu_mem huON hk hv1 hclose'
  have hprod0 : 0 ≤ (∏ i : Fin k, ‖v i‖) := Finset.prod_nonneg (fun i hi => norm_nonneg _)
  have hmul : (∏ i : Fin k, ‖v i‖) * (1 - (2 * (k : ℝ)) / ((11 : ℝ) * (k : ℝ) - 1)) ≤
      (∏ i : Fin k, ‖v i‖) * ‖pi1 (d := d) (k := k) ℓ
        (exteriorPower.ιMulti ℝ k vn)‖ := by
    exact mul_le_mul_of_nonneg_left hlow hprod0
  have heq : ‖pi1 (d := d) (k := k) ℓ (exteriorPower.ιMulti ℝ k v)‖ =
      (∏ i : Fin k, ‖v i‖) * ‖pi1 (d := d) (k := k) ℓ
        (exteriorPower.ιMulti ℝ k vn)‖ := by
    simpa [vn] using (norm_pi1_ιMulti_mul_normed (d := d) (k := k) ℓ v hv0)
  exact le_trans hmul (le_of_eq heq.symm)

/-- The general-`k` wedge loss `2k/(11k−1)` is at most `1/5` for `k ≥ 1`, so the slack
`(1 − 2k/(11k−1))` stays at least `4/5` for every `k ≥ 1`. -/
lemma wedgeLoss_k_le_one_fifth (k : ℕ) (hk : 1 ≤ k) :
    (2 * (k : ℝ)) / ((11 : ℝ) * (k : ℝ) - 1) ≤ 1 / 5 := by
  have hdenpos : 0 < (11 : ℝ) * (k : ℝ) - 1 := by
    have hkR : 1 ≤ (k : ℝ) := by exact_mod_cast hk
    nlinarith
  rw [div_le_iff₀ hdenpos]
  have hkR : 1 ≤ (k : ℝ) := by exact_mod_cast hk
  nlinarith

/-- **Two-sided `π₁`-sandwich, general `k` (expanding block, `a b` flow)**: with an ON
family `u` of unit directions in `largeSpan ℓ` and an annulus family `v : Fin k → largeFlow
a b ℓ` around `(11k)·((d−ℓ:ℕ):ℝ)b·u` per index (`1 ≤ k`), the two-sided estimate
`(∏ᵢ‖v i‖)·(1 − 2k/(11k−1)) ≤ ‖π₁(ιMulti v)‖ ≤ ‖ιMulti v‖` holds — no `k ≤ 4`
restriction (the per-direction error `≤ 2/(11k−1)` shrinks like `1/k`). -/
theorem wedgeLarge_blockAnnulus_twoSided_k (ℓ : ℕ) (hℓd : ℓ < d) {a b : ℝ} (hb0 : 0 < b)
    (u : Fin k → RD d)
    (hu_mem : ∀ i, u i ∈ Submission.LargeBlockCovering.largeSpan (d := d) ℓ)
    (huON : Orthonormal ℝ u) (hk : 0 < k)
    (v : Fin k → Submission.LargeBlockMinima.largeFlow (d := d) a b ℓ)
    (hvann : ∀ i, ‖(v i : RD d) -
          (((11 : ℝ) * (k : ℝ)) * ((d - ℓ : ℕ) : ℝ) * b) • u i‖ ≤ ((d - ℓ : ℕ) : ℝ) * b ∧
        (((11 : ℝ) * (k : ℝ) - 1) * ((d - ℓ : ℕ) : ℝ)) * b ≤ ‖(v i : RD d)‖ ∧
        ‖(v i : RD d)‖ ≤ (((11 : ℝ) * (k : ℝ) + 1) * ((d - ℓ : ℕ) : ℝ)) * b) :
    (∏ i : Fin k, ‖(v i : RD d)‖) * (1 - (2 * (k : ℝ)) / ((11 : ℝ) * (k : ℝ) - 1)) ≤
        ‖pi1 (d := d) (k := k) ℓ
          (exteriorPower.ιMulti ℝ k (fun i : Fin k => (v i : RD d)))‖ ∧
      ‖pi1 (d := d) (k := k) ℓ
        (exteriorPower.ιMulti ℝ k (fun i : Fin k => (v i : RD d)))‖ ≤
        ‖exteriorPower.ιMulti ℝ k (fun i : Fin k => (v i : RD d))‖ := by
  classical
  have hv0 : ∀ i, (v i : RD d) ≠ 0 := by
    intro i
    rcases hvann i with ⟨hd, hlo, hhi⟩
    have hpos : 0 < (((11 : ℝ) * (k : ℝ) - 1) * ((d - ℓ : ℕ) : ℝ)) * b := by
      have hkR : 1 ≤ (k : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
      have hcpos : 0 < ((d - ℓ : ℕ) : ℝ) * b :=
        mul_pos (by exact_mod_cast (Nat.sub_pos_of_lt hℓd)) hb0
      nlinarith
    have hnormpos : 0 < ‖(v i : RD d)‖ := lt_of_lt_of_le hpos hlo
    exact norm_pos_iff.mp hnormpos
  have hclose : ∀ i, ‖(‖(v i : RD d)‖⁻¹) • (v i : RD d) - u i‖ ≤
      2 / ((11 : ℝ) * (k : ℝ) - 1) := by
    intro i
    rcases hvann i with ⟨hd, hlo, hhi⟩
    let C : ℝ := ((d - ℓ : ℕ) : ℝ) * b
    have hs1 : (((11 : ℝ) * (k : ℝ)) * ((d - ℓ : ℕ) : ℝ) * b) = ((11 : ℝ) * (k : ℝ)) * C := by
      dsimp [C]
      ring
    have hs2 : (((11 : ℝ) * (k : ℝ) - 1) * ((d - ℓ : ℕ) : ℝ)) * b = ((11 : ℝ) * (k : ℝ) - 1) * C := by
      dsimp [C]
      ring
    have hs3 : (((11 : ℝ) * (k : ℝ) + 1) * ((d - ℓ : ℕ) : ℝ)) * b = ((11 : ℝ) * (k : ℝ) + 1) * C := by
      dsimp [C]
      ring
    have hd' : ‖(v i : RD d) - (((11 : ℝ) * (k : ℝ)) * C) • u i‖ ≤ C := by
      rw [← hs1]
      simpa [C] using hd
    have hlo' : ((11 : ℝ) * (k : ℝ) - 1) * C ≤ ‖(v i : RD d)‖ := by
      rw [← hs2]
      exact hlo
    have hhi' : ‖(v i : RD d)‖ ≤ ((11 : ℝ) * (k : ℝ) + 1) * C := by
      rw [← hs3]
      exact hhi
    have hk1 : 1 ≤ k := lt_of_lt_of_le Nat.zero_lt_one hk
    exact Submission.WedgeContract.norm_smul_inv_sub_le_of_annulus_k (u := u i)
      (v := (v i : RD d)) (huON.1 i) (hv0 i) (C := C) hk1 hd' hlo' hhi'
  have hlow := norm_pi1_ιMulti_ge_mul_sub_k_of_largeSpan (d := d) (k := k) ℓ u
    (fun i : Fin k => (v i : RD d)) hu_mem huON hk hv0 hclose
  constructor
  · simpa using hlow
  · exact norm_pi1_le (d := d) (k := k) ℓ
      (exteriorPower.ιMulti ℝ k (fun i : Fin k => (v i : RD d)))

/-- **Log-form sandwich, expanding block, general `k`**: under the `(11k)`-anchored annulus
hypotheses and `1 ≤ k` (no `k ≤ 4` restriction), with the `k`-dependent wedge loss
`2k/(11k−1)`, `Σᵢ log‖v i‖ + log(1 − 2k/(11k−1)) ≤ log‖π₁(ιMulti v)‖ ≤ Σᵢ log‖v i‖`. -/
lemma wedgeLarge_blockAnnulus_log_twoSided_k (ℓ : ℕ) (hℓd : ℓ < d) {a b : ℝ} (hb0 : 0 < b)
    (u : Fin k → RD d)
    (hu_mem : ∀ i, u i ∈ Submission.LargeBlockCovering.largeSpan (d := d) ℓ)
    (huON : Orthonormal ℝ u) (hk : 0 < k)
    (v : Fin k → Submission.LargeBlockMinima.largeFlow (d := d) a b ℓ)
    (hvann : ∀ i, ‖(v i : RD d) -
          (((11 : ℝ) * (k : ℝ)) * ((d - ℓ : ℕ) : ℝ) * b) • u i‖ ≤ ((d - ℓ : ℕ) : ℝ) * b ∧
        (((11 : ℝ) * (k : ℝ) - 1) * ((d - ℓ : ℕ) : ℝ)) * b ≤ ‖(v i : RD d)‖ ∧
        ‖(v i : RD d)‖ ≤ (((11 : ℝ) * (k : ℝ) + 1) * ((d - ℓ : ℕ) : ℝ)) * b) :
    (∑ i : Fin k, Real.log ‖(v i : RD d)‖) +
        Real.log (1 - (2 * (k : ℝ)) / ((11 : ℝ) * (k : ℝ) - 1)) ≤
        Real.log ‖pi1 (d := d) (k := k) ℓ
          (exteriorPower.ιMulti ℝ k (fun i : Fin k => (v i : RD d)))‖ ∧
      Real.log ‖pi1 (d := d) (k := k) ℓ
        (exteriorPower.ιMulti ℝ k (fun i : Fin k => (v i : RD d)))‖ ≤
        (∑ i : Fin k, Real.log ‖(v i : RD d)‖) := by
  classical
  have htwo := wedgeLarge_blockAnnulus_twoSided_k (d := d) ℓ hℓd (a := a) (b := b) hb0 u
    hu_mem huON hk v hvann
  have hpos : ∀ i, 0 < ‖(v i : RD d)‖ := by
    intro i
    rcases hvann i with ⟨hd, hloi, hhii⟩
    have hposlo : 0 < (((11 : ℝ) * (k : ℝ) - 1) * ((d - ℓ : ℕ) : ℝ)) * b := by
      have hkR : 1 ≤ (k : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
      have hC : 0 < ((d - ℓ : ℕ) : ℝ) * b := by
        exact mul_pos (by exact_mod_cast (Nat.sub_pos_of_lt hℓd)) hb0
      nlinarith
    exact lt_of_lt_of_le hposlo hloi
  have hprod0 : 0 < (∏ i : Fin k, ‖(v i : RD d)‖) := Finset.prod_pos (fun i hi => hpos i)
  have hk1 : 1 ≤ k := lt_of_lt_of_le Nat.zero_lt_one hk
  have hloss : (2 * (k : ℝ)) / ((11 : ℝ) * (k : ℝ) - 1) ≤ 1 / 5 :=
    wedgeLoss_k_le_one_fifth k hk1
  have hlosslt1 : (2 * (k : ℝ)) / ((11 : ℝ) * (k : ℝ) - 1) < 1 := by
    exact lt_of_le_of_lt hloss (by norm_num)
  have h1m : 0 < 1 - (2 * (k : ℝ)) / ((11 : ℝ) * (k : ℝ) - 1) := by
    linarith
  have hpi0 : 0 < ‖pi1 (d := d) (k := k) ℓ
      (exteriorPower.ιMulti ℝ k (fun i : Fin k => (v i : RD d)))‖ :=
    lt_of_lt_of_le (mul_pos hprod0 h1m) htwo.1
  have hpl : Real.log (∏ i : Fin k, ‖(v i : RD d)‖) =
      (∑ i : Fin k, Real.log ‖(v i : RD d)‖) := by
    exact Real.log_prod (s := Finset.univ) (f := fun i : Fin k => ‖(v i : RD d)‖)
      (by intro i hi; exact ne_of_gt (hpos i))
  have hprod_le : ‖pi1 (d := d) (k := k) ℓ
        (exteriorPower.ιMulti ℝ k (fun i : Fin k => (v i : RD d)))‖ ≤
        (∏ i : Fin k, ‖(v i : RD d)‖) :=
      le_trans (norm_pi1_le (d := d) (k := k) ℓ
        (exteriorPower.ιMulti ℝ k (fun i : Fin k => (v i : RD d))))
        (Commons.Analysis.InnerProductSpace.exteriorPower_norm_wedge_le_prod
          (fun i : Fin k => (v i : RD d)))
  constructor
  · calc
      (∑ i : Fin k, Real.log ‖(v i : RD d)‖) +
            Real.log (1 - (2 * (k : ℝ)) / ((11 : ℝ) * (k : ℝ) - 1))
          = Real.log (∏ i : Fin k, ‖(v i : RD d)‖) +
            Real.log (1 - (2 * (k : ℝ)) / ((11 : ℝ) * (k : ℝ) - 1)) := by
              rw [← hpl]
      _ = Real.log ((∏ i : Fin k, ‖(v i : RD d)‖) *
            (1 - (2 * (k : ℝ)) / ((11 : ℝ) * (k : ℝ) - 1))) := by
              rw [Real.log_mul (ne_of_gt hprod0) (ne_of_gt h1m)]
      _ ≤ Real.log ‖pi1 (d := d) (k := k) ℓ
            (exteriorPower.ιMulti ℝ k (fun i : Fin k => (v i : RD d)))‖ :=
            Real.log_le_log (mul_pos hprod0 h1m) htwo.1
  · calc
      Real.log ‖pi1 (d := d) (k := k) ℓ
          (exteriorPower.ιMulti ℝ k (fun i : Fin k => (v i : RD d)))‖
          ≤ Real.log (∏ i : Fin k, ‖(v i : RD d)‖) := Real.log_le_log hpi0 hprod_le
      _ = (∑ i : Fin k, Real.log ‖(v i : RD d)‖) := hpl

/-- **Log-form sandwich in the exponential flow (expanding block), general `k`**: the
exp instance of `wedgeLarge_blockAnnulus_log_twoSided_k` — same sandwich
`Σᵢ log‖v i‖ + log(1 − 2k/(11k−1)) ≤ log‖π₁(ιMulti v)‖ ≤ Σᵢ log‖v i‖` for every `1 ≤ k`
(no `k ≤ 4` restriction). -/
lemma wedgeLarge_blockAnnulus_log_twoSided_k_exp (ℓ : ℕ) (hℓd : ℓ < d) {t : ℝ}
    (u : Fin k → RD d)
    (hu_mem : ∀ i, u i ∈ Submission.LargeBlockCovering.largeSpan (d := d) ℓ)
    (huON : Orthonormal ℝ u) (hk : 0 < k)
    (v : Fin k → Submission.LargeBlockMinima.largeFlow (d := d)
        (Real.exp (-t / (ℓ : ℝ))) (Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))) ℓ)
    (hvann : ∀ i, ‖(v i : RD d) -
          (((11 : ℝ) * (k : ℝ)) * ((d - ℓ : ℕ) : ℝ) *
            Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))) • u i‖ ≤
          ((d - ℓ : ℕ) : ℝ) * Real.exp (t / ((d : ℝ) - (ℓ : ℝ))) ∧
        (((11 : ℝ) * (k : ℝ) - 1) * ((d - ℓ : ℕ) : ℝ)) *
            Real.exp (t / ((d : ℝ) - (ℓ : ℝ))) ≤ ‖(v i : RD d)‖ ∧
        ‖(v i : RD d)‖ ≤ (((11 : ℝ) * (k : ℝ) + 1) * ((d - ℓ : ℕ) : ℝ)) *
            Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))) :
    (∑ i : Fin k, Real.log ‖(v i : RD d)‖) +
        Real.log (1 - (2 * (k : ℝ)) / ((11 : ℝ) * (k : ℝ) - 1)) ≤
        Real.log ‖pi1 (d := d) (k := k) ℓ
          (exteriorPower.ιMulti ℝ k (fun i : Fin k => (v i : RD d)))‖ ∧
      Real.log ‖pi1 (d := d) (k := k) ℓ
        (exteriorPower.ιMulti ℝ k (fun i : Fin k => (v i : RD d)))‖ ≤
        (∑ i : Fin k, Real.log ‖(v i : RD d)‖) := by
  exact wedgeLarge_blockAnnulus_log_twoSided_k (d := d) ℓ hℓd
    (a := Real.exp (-t / (ℓ : ℝ))) (b := Real.exp (t / ((d : ℝ) - (ℓ : ℝ))))
    (Real.exp_pos _) u hu_mem huON hk v hvann

/-- **Log-interval for the `(11k)`-annulus family (expanding block), general `k`**: from the
per-index annulus bounds (`C = ((d−ℓ:ℕ):ℝ)b > 0`),
`Σᵢ log‖v i‖ ∈ [k·log(((11k−1)·(d−ℓ:ℕ):ℝ)b), k·log(((11k+1)·(d−ℓ:ℕ):ℝ)b)]`. -/
lemma wedgeLarge_blockAnnulus_log_interval_k (ℓ : ℕ) (hℓd : ℓ < d) {a b : ℝ} (hb0 : 0 < b)
    (hk1 : 1 ≤ k)
    (v : Fin k → Submission.LargeBlockMinima.largeFlow (d := d) a b ℓ)
    (hlo : ∀ i, (((11 : ℝ) * (k : ℝ) - 1) * ((d - ℓ : ℕ) : ℝ)) * b ≤ ‖(v i : RD d)‖)
    (hhi : ∀ i, ‖(v i : RD d)‖ ≤ (((11 : ℝ) * (k : ℝ) + 1) * ((d - ℓ : ℕ) : ℝ)) * b) :
    (k : ℝ) * Real.log ((((11 : ℝ) * (k : ℝ) - 1) * ((d - ℓ : ℕ) : ℝ)) * b) ≤
        (∑ i : Fin k, Real.log ‖(v i : RD d)‖) ∧
      (∑ i : Fin k, Real.log ‖(v i : RD d)‖) ≤
        (k : ℝ) * Real.log ((((11 : ℝ) * (k : ℝ) + 1) * ((d - ℓ : ℕ) : ℝ)) * b) := by
  let C : ℝ := ((d - ℓ : ℕ) : ℝ) * b
  let c0 : ℝ := (11 : ℝ) * (k : ℝ) - 1
  let c1 : ℝ := (11 : ℝ) * (k : ℝ) + 1
  have hC0 : 0 < C := by
    dsimp [C]
    exact mul_pos (by exact_mod_cast (Nat.sub_pos_of_lt hℓd)) hb0
  have hc0 : 0 < c0 := by
    dsimp [c0]
    have hkR : 1 ≤ (k : ℝ) := by exact_mod_cast hk1
    nlinarith
  have hc1 : 0 < c1 := by
    dsimp [c1]
    have hkR0 : 0 ≤ (k : ℝ) := by exact_mod_cast (Nat.zero_le k)
    nlinarith
  have hlo' : ∀ i, (c0 * C) ≤ ‖(v i : RD d)‖ := by
    intro i
    have hs : c0 * C = (((11 : ℝ) * (k : ℝ) - 1) * ((d - ℓ : ℕ) : ℝ)) * b := by
      dsimp [C, c0]
      ring
    rw [hs]
    exact hlo i
  have hhi' : ∀ i, ‖(v i : RD d)‖ ≤ (c1 * C) := by
    intro i
    have hs : c1 * C = (((11 : ℝ) * (k : ℝ) + 1) * ((d - ℓ : ℕ) : ℝ)) * b := by
      dsimp [C, c1]
      ring
    rw [hs]
    exact hhi i
  have h := Commons.Analysis.Real.sum_log_norm_interval (E := RD d) k
    (fun i : Fin k => (v i : RD d)) c0 c1 C hc0 hc1 hC0 hlo' hhi'
  constructor
  · have hs0 : c0 * C = (((11 : ℝ) * (k : ℝ) - 1) * ((d - ℓ : ℕ) : ℝ)) * b := by
      dsimp [C, c0]
      ring
    rw [hs0] at h
    exact h.1
  · have hs1 : c1 * C = (((11 : ℝ) * (k : ℝ) + 1) * ((d - ℓ : ℕ) : ℝ)) * b := by
      dsimp [C, c1]
      ring
    rw [hs1] at h
    exact h.2





/-! ### The expanding-block annulus assembly (two-sided sandwich, log forms)

The mirror of `WedgeContract`'s contracting-block lock on the expanding side, fed by
`LargeBlockCovering.exists_largeFamily_annulus`: given an ON family `u` of unit directions
in the expanding block's real span (`u i ∈ largeSpan ℓ`) and an annulus family
`v : Fin k → largeFlow a b ℓ` around `11·((d−ℓ:ℕ):ℝ)b·u` per index, the two-sided
`π₁`-sandwich `(∏ᵢ‖v i‖)·(1 − k/5) ≤ ‖π₁(ιMulti v)‖ ≤ ∏ᵢ‖v i‖` holds
(`wedgeLarge_blockAnnulus_twoSided`), and so do its log forms
(`wedgeLarge_blockAnnulus_log_twoSided`).  The exponential-flow instances
(`a = e^{−t/ℓ}`, `b = e^{t/(d−ℓ)}` — suffix `_exp`) state the same estimates with
`C = ((d−ℓ:ℕ):ℝ)·e^{t/(d−ℓ)}`. -/

/-- **Annulus family → `π₁`-lower bound** (expanding block): with an ON family `u` of unit
directions in `largeSpan ℓ` and an annulus family `v : Fin k → largeFlow a b ℓ` around
`11·((d−ℓ:ℕ):ℝ)b·u` per index, `(∏ᵢ ‖v i‖)·(1 − k/5) ≤ ‖π₁(ιMulti (ambient v))‖`. -/
theorem wedgeLarge_blockAnnulus_lower (ℓ : ℕ) (hℓd : ℓ < d) {a b : ℝ} (hb0 : 0 < b)
    (u : Fin k → RD d)
    (hu_mem : ∀ i, u i ∈ Submission.LargeBlockCovering.largeSpan (d := d) ℓ)
    (huON : Orthonormal ℝ u) (hk : 0 < k)
    (v : Fin k → Submission.LargeBlockMinima.largeFlow (d := d) a b ℓ)
    (hvann : ∀ i, ‖(v i : RD d) - ((11 : ℝ) * ((d - ℓ : ℕ) : ℝ) * b) • u i‖ ≤
          ((d - ℓ : ℕ) : ℝ) * b ∧
        (10 : ℝ) * ((d - ℓ : ℕ) : ℝ) * b ≤ ‖(v i : RD d)‖ ∧
        ‖(v i : RD d)‖ ≤ (12 : ℝ) * ((d - ℓ : ℕ) : ℝ) * b) :
    (∏ i : Fin k, ‖(v i : RD d)‖) * (1 - (k : ℝ) / 5) ≤
      ‖pi1 (d := d) (k := k) ℓ
        (exteriorPower.ιMulti ℝ k (fun i : Fin k => (v i : RD d)))‖ := by
  classical
  have hv0 : ∀ i, (v i : RD d) ≠ 0 := by
    intro i
    rcases hvann i with ⟨hd, hlo, hhi⟩
    have hpos : 0 < ((d - ℓ : ℕ) : ℝ) * b := by
      exact mul_pos (by exact_mod_cast (Nat.sub_pos_of_lt hℓd)) hb0
    have hnormpos : 0 < ‖(v i : RD d)‖ := lt_of_lt_of_le (by nlinarith) hlo
    exact norm_pos_iff.mp hnormpos
  have hclose : ∀ i, ‖(‖(v i : RD d)‖⁻¹) • (v i : RD d) - u i‖ ≤ (1 / 5 : ℝ) := by
    intro i
    rcases hvann i with ⟨hd, hlo, hhi⟩
    have hs : (11 * (((d - ℓ : ℕ) : ℝ) * b)) = ((11 : ℝ) * ((d - ℓ : ℕ) : ℝ)) * b := by ring
    have hd' : ‖(v i : RD d) - (11 * (((d - ℓ : ℕ) : ℝ) * b)) • u i‖ ≤ ((d - ℓ : ℕ) : ℝ) * b := by
      rw [hs]
      exact hd
    have hlo' : (10 * (((d - ℓ : ℕ) : ℝ) * b)) ≤ ‖(v i : RD d)‖ := by
      rw [show (10 * (((d - ℓ : ℕ) : ℝ) * b)) = ((10 : ℝ) * ((d - ℓ : ℕ) : ℝ)) * b by ring]
      exact hlo
    have hhi' : ‖(v i : RD d)‖ ≤ (12 * (((d - ℓ : ℕ) : ℝ) * b)) := by
      rw [show (12 * (((d - ℓ : ℕ) : ℝ) * b)) = ((12 : ℝ) * ((d - ℓ : ℕ) : ℝ)) * b by ring]
      exact hhi
    exact Submission.WedgeContract.norm_smul_inv_sub_le_one_fifth (u := u i)
      (v := (v i : RD d)) (huON.1 i) (hv0 i) (C := ((d - ℓ : ℕ) : ℝ) * b) hd' hlo' hhi'
  exact norm_pi1_ιMulti_ge_mul_sub_one_fifth_of_largeSpan (d := d) (k := k) ℓ u
    (fun i : Fin k => (v i : RD d)) hu_mem huON hk hv0 hclose

/-- **Instantiation with the Lemma-5 directions (expanding block)**: for an orthonormal
family `u` of unit directions in the expanding block's real span (`0 < ℓ < d`, `0 < b`),
the annulus family exists (`LargeBlockCovering.exists_largeFamily_annulus`) and satisfies
the `π₁`-lower bound. -/
theorem exists_wedgeLarge_blockAnnulus_lower (ℓ : ℕ) (hℓd : ℓ < d) {a b : ℝ} (hb0 : 0 < b)
    (u : Fin k → RD d)
    (hu_mem : ∀ i, u i ∈ Submission.LargeBlockCovering.largeSpan (d := d) ℓ)
    (huON : Orthonormal ℝ u) (hk : 0 < k) :
    ∃ v : Fin k → Submission.LargeBlockMinima.largeFlow (d := d) a b ℓ,
      (∏ i : Fin k, ‖(v i : RD d)‖) * (1 - (k : ℝ) / 5) ≤
        ‖pi1 (d := d) (k := k) ℓ
          (exteriorPower.ιMulti ℝ k (fun i : Fin k => (v i : RD d)))‖ := by
  classical
  obtain ⟨v, hv⟩ := Submission.LargeBlockCovering.exists_largeFamily_annulus (d := d) ℓ
    (le_of_lt hℓd) (a := a) (b := b) hb0 (m := k) (u := u) hu_mem (fun i => huON.1 i)
  refine ⟨v, ?_⟩
  exact wedgeLarge_blockAnnulus_lower (d := d) ℓ hℓd (a := a) (b := b) hb0 u hu_mem huON hk v hv

/-- **Wedge-upper, expanding block**: for any family `v : Fin k → largeFlow a b ℓ` of block
lattice vectors, `‖π₁(ιMulti (ambient v))‖ ≤ ∏ᵢ ‖v i‖` (`norm_pi1_le` + the Commons product
bound). -/
theorem wedgeLarge_blockAnnulus_upper (ℓ : ℕ) {a b : ℝ}
    (v : Fin k → Submission.LargeBlockMinima.largeFlow (d := d) a b ℓ) :
    ‖pi1 (d := d) (k := k) ℓ
        (exteriorPower.ιMulti ℝ k (fun i : Fin k => (v i : RD d)))‖ ≤
      (∏ i : Fin k, ‖(v i : RD d)‖) := by
  have h1 := norm_pi1_le (d := d) (k := k) ℓ
    (exteriorPower.ιMulti ℝ k (fun i : Fin k => (v i : RD d)))
  have h2 := Commons.Analysis.InnerProductSpace.exteriorPower_norm_wedge_le_prod
    (fun i : Fin k => (v i : RD d))
  exact le_trans h1 h2

/-- **Two-sided sandwich, expanding block**: under the annulus hypotheses of
`wedgeLarge_blockAnnulus_lower`, the `π₁`-projection of the wedge satisfies
`(∏ᵢ ‖v i‖)·(1 − k/5) ≤ ‖π₁(ιMulti v)‖ ≤ ∏ᵢ ‖v i‖`. -/
theorem wedgeLarge_blockAnnulus_twoSided (ℓ : ℕ) (hℓd : ℓ < d) {a b : ℝ} (hb0 : 0 < b)
    (u : Fin k → RD d)
    (hu_mem : ∀ i, u i ∈ Submission.LargeBlockCovering.largeSpan (d := d) ℓ)
    (huON : Orthonormal ℝ u) (hk : 0 < k)
    (v : Fin k → Submission.LargeBlockMinima.largeFlow (d := d) a b ℓ)
    (hvann : ∀ i, ‖(v i : RD d) - ((11 : ℝ) * ((d - ℓ : ℕ) : ℝ) * b) • u i‖ ≤
          ((d - ℓ : ℕ) : ℝ) * b ∧
        (10 : ℝ) * ((d - ℓ : ℕ) : ℝ) * b ≤ ‖(v i : RD d)‖ ∧
        ‖(v i : RD d)‖ ≤ (12 : ℝ) * ((d - ℓ : ℕ) : ℝ) * b) :
    (∏ i : Fin k, ‖(v i : RD d)‖) * (1 - (k : ℝ) / 5) ≤
        ‖pi1 (d := d) (k := k) ℓ
          (exteriorPower.ιMulti ℝ k (fun i : Fin k => (v i : RD d)))‖ ∧
      ‖pi1 (d := d) (k := k) ℓ
        (exteriorPower.ιMulti ℝ k (fun i : Fin k => (v i : RD d)))‖ ≤
        (∏ i : Fin k, ‖(v i : RD d)‖) := by
  exact ⟨wedgeLarge_blockAnnulus_lower (d := d) ℓ hℓd (a := a) (b := b) hb0 u hu_mem huON hk v hvann,
    wedgeLarge_blockAnnulus_upper (d := d) ℓ (a := a) (b := b) v⟩

/-- **Log-interval for the expanding-block annulus family**: from the per-index annulus
bounds (`C = ((d−ℓ:ℕ):ℝ)b > 0`), `Σᵢ log‖v i‖ ∈ [k·log(10C), k·log(12C)]`. -/
lemma wedgeLarge_blockAnnulus_log_interval (ℓ : ℕ) (hℓd : ℓ < d) {a b : ℝ} (hb0 : 0 < b)
    (v : Fin k → Submission.LargeBlockMinima.largeFlow (d := d) a b ℓ)
    (hlo : ∀ i, (10 : ℝ) * ((d - ℓ : ℕ) : ℝ) * b ≤ ‖(v i : RD d)‖)
    (hhi : ∀ i, ‖(v i : RD d)‖ ≤ (12 : ℝ) * ((d - ℓ : ℕ) : ℝ) * b) :
    (k : ℝ) * Real.log ((10 : ℝ) * ((d - ℓ : ℕ) : ℝ) * b) ≤ (∑ i : Fin k, Real.log ‖(v i : RD d)‖) ∧
      (∑ i : Fin k, Real.log ‖(v i : RD d)‖) ≤ (k : ℝ) * Real.log ((12 : ℝ) * ((d - ℓ : ℕ) : ℝ) * b) := by
  have hC0 : 0 < ((d - ℓ : ℕ) : ℝ) * b := by
    exact mul_pos (by exact_mod_cast (Nat.sub_pos_of_lt hℓd)) hb0
  have hlo' : ∀ i, (10 * (((d - ℓ : ℕ) : ℝ) * b)) ≤ ‖(v i : RD d)‖ := by
    intro i
    rw [show (10 * (((d - ℓ : ℕ) : ℝ) * b)) = ((10 : ℝ) * ((d - ℓ : ℕ) : ℝ)) * b by ring]
    exact hlo i
  have hhi' : ∀ i, ‖(v i : RD d)‖ ≤ (12 * (((d - ℓ : ℕ) : ℝ) * b)) := by
    intro i
    rw [show (12 * (((d - ℓ : ℕ) : ℝ) * b)) = ((12 : ℝ) * ((d - ℓ : ℕ) : ℝ)) * b by ring]
    exact hhi i
  have h := Commons.Analysis.Real.sum_log_norm_annulus (E := RD d) k
    (fun i : Fin k => (v i : RD d)) (((d - ℓ : ℕ) : ℝ) * b) hC0 hlo' hhi'
  have hs10 : (10 * (((d - ℓ : ℕ) : ℝ) * b)) = ((10 : ℝ) * ((d - ℓ : ℕ) : ℝ)) * b := by ring
  have hs12 : (12 * (((d - ℓ : ℕ) : ℝ) * b)) = ((12 : ℝ) * ((d - ℓ : ℕ) : ℝ)) * b := by ring
  rwa [hs10, hs12] at h

/-- **Log-form sandwich, expanding block**: under the annulus hypotheses and `k ≤ 4`,
`Σᵢ log‖v i‖ + log(1 − k/5) ≤ log‖π₁(ιMulti v)‖ ≤ Σᵢ log‖v i‖`. -/
lemma wedgeLarge_blockAnnulus_log_twoSided (ℓ : ℕ) (hℓd : ℓ < d) {a b : ℝ} (hb0 : 0 < b)
    (hk4 : k ≤ 4) (u : Fin k → RD d)
    (hu_mem : ∀ i, u i ∈ Submission.LargeBlockCovering.largeSpan (d := d) ℓ)
    (huON : Orthonormal ℝ u) (hk : 0 < k)
    (v : Fin k → Submission.LargeBlockMinima.largeFlow (d := d) a b ℓ)
    (hvann : ∀ i, ‖(v i : RD d) - ((11 : ℝ) * ((d - ℓ : ℕ) : ℝ) * b) • u i‖ ≤
          ((d - ℓ : ℕ) : ℝ) * b ∧
        (10 : ℝ) * ((d - ℓ : ℕ) : ℝ) * b ≤ ‖(v i : RD d)‖ ∧
        ‖(v i : RD d)‖ ≤ (12 : ℝ) * ((d - ℓ : ℕ) : ℝ) * b) :
    (∑ i : Fin k, Real.log ‖(v i : RD d)‖) + Real.log (1 - (k : ℝ) / 5) ≤
        Real.log ‖pi1 (d := d) (k := k) ℓ
          (exteriorPower.ιMulti ℝ k (fun i : Fin k => (v i : RD d)))‖ ∧
      Real.log ‖pi1 (d := d) (k := k) ℓ
        (exteriorPower.ιMulti ℝ k (fun i : Fin k => (v i : RD d)))‖ ≤
        (∑ i : Fin k, Real.log ‖(v i : RD d)‖) := by
  classical
  have htwo := wedgeLarge_blockAnnulus_twoSided (d := d) ℓ hℓd (a := a) (b := b) hb0 u
    hu_mem huON hk v hvann
  have hpos : ∀ i, 0 < ‖(v i : RD d)‖ := by
    intro i
    rcases hvann i with ⟨hd, hloi, hhii⟩
    have hC : 0 < ((d - ℓ : ℕ) : ℝ) * b := by
      exact mul_pos (by exact_mod_cast (Nat.sub_pos_of_lt hℓd)) hb0
    have hpos10 : 0 < (10 : ℝ) * ((d - ℓ : ℕ) : ℝ) * b := by nlinarith
    exact lt_of_lt_of_le hpos10 hloi
  have hprod0 : 0 < (∏ i : Fin k, ‖(v i : RD d)‖) := Finset.prod_pos (fun i hi => hpos i)
  have hkR : (k : ℝ) ≤ 4 := by exact_mod_cast hk4
  have h1m : 0 < 1 - (k : ℝ) / 5 := by nlinarith
  have hpi0 : 0 < ‖pi1 (d := d) (k := k) ℓ
      (exteriorPower.ιMulti ℝ k (fun i : Fin k => (v i : RD d)))‖ :=
    lt_of_lt_of_le (mul_pos hprod0 h1m) htwo.1
  have hpl : Real.log (∏ i : Fin k, ‖(v i : RD d)‖) =
      (∑ i : Fin k, Real.log ‖(v i : RD d)‖) := by
    exact Real.log_prod (s := Finset.univ) (f := fun i : Fin k => ‖(v i : RD d)‖)
      (by intro i hi; exact ne_of_gt (hpos i))
  constructor
  · calc
      (∑ i : Fin k, Real.log ‖(v i : RD d)‖) + Real.log (1 - (k : ℝ) / 5)
          = Real.log (∏ i : Fin k, ‖(v i : RD d)‖) + Real.log (1 - (k : ℝ) / 5) := by
              rw [← hpl]
      _ = Real.log ((∏ i : Fin k, ‖(v i : RD d)‖) * (1 - (k : ℝ) / 5)) := by
              rw [Real.log_mul (ne_of_gt hprod0) (ne_of_gt h1m)]
      _ ≤ Real.log ‖pi1 (d := d) (k := k) ℓ
            (exteriorPower.ιMulti ℝ k (fun i : Fin k => (v i : RD d)))‖ :=
            Real.log_le_log (mul_pos hprod0 h1m) htwo.1
  · calc
      Real.log ‖pi1 (d := d) (k := k) ℓ
          (exteriorPower.ιMulti ℝ k (fun i : Fin k => (v i : RD d)))‖
          ≤ Real.log (∏ i : Fin k, ‖(v i : RD d)‖) := Real.log_le_log hpi0 htwo.2
      _ = (∑ i : Fin k, Real.log ‖(v i : RD d)‖) := hpl


/-! ### The exponential-length instance (step (b): `b = exp(t/(d−ℓ))`)

Specialising the expanding-block estimates to the exponential flow of the model
(`a = exp(−t/ℓ)`, `b = exp(t/(d−ℓ))`, so the expanding scale is `exp(t/(d−ℓ))`):

* `log_mul_annulus_exp_large`: endpoint log rewrite — `log(m·((d−ℓ:ℕ):ℝ)·exp(t/(d−ℓ))) =
  log(m·((d−ℓ:ℕ):ℝ)) + t/(d−ℓ)` (`Real.log_mul` + `Real.log_exp`);
* `wedgeLarge_blockAnnulus_log_twoSided_exp` / `wedgeLarge_blockAnnulus_log_exp_interval`
  and the assembled **`wedgeLarge_blockAnnulus_log_upper_exp`** /
  **`wedgeLarge_blockAnnulus_log_lower_exp`**: under the exp-annulus hypotheses and `k ≤ 4`,
  `log‖π₁(ιMulti v)‖ ≤ k·log(12·((d−ℓ:ℕ):ℝ)) + k·t/(d−ℓ)` and the matching lower with the
  `log(1 − k/5)` slack;
* **`exists_wedgeLarge_blockAnnulus_log_upper_exp`** /
  **`exists_wedgeLarge_blockAnnulus_log_lower_exp`**: the same as existence statements, fed
  by `LargeBlockCovering.exists_largeFamily_annulus_exp`;
* `wedgeLarge_blockAnnulus_log_upper_exp_slope`: the slope-visible form with coefficient
  `t·(k/(d−ℓ))` — the expanding-block slope sum.
-/

/-- Endpoint log rewrite in the exponential flow (expanding scale): `log (m·((d−ℓ:ℕ):ℝ)·
exp(t/(d−ℓ))) = log (m·((d−ℓ:ℕ):ℝ)) + t/(d−ℓ)` for `m ≠ 0`, `0 < ℓ < d`. -/
lemma log_mul_annulus_exp_large (m : ℝ) (hm : m ≠ 0) (ℓ : ℕ) (hℓd : ℓ < d) (t : ℝ) :
    Real.log (m * ((d - ℓ : ℕ) : ℝ) * Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))) =
      Real.log (m * ((d - ℓ : ℕ) : ℝ)) + t / ((d : ℝ) - (ℓ : ℝ)) := by
  have hdm : ((d - ℓ : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Nat.sub_pos_of_lt hℓd))
  have hmℓ : m * ((d - ℓ : ℕ) : ℝ) ≠ 0 := mul_ne_zero hm hdm
  rw [Real.log_mul hmℓ (Real.exp_ne_zero _)]
  rw [Real.log_exp]
/-- **Log-interval for the `(11k)`-annulus family in the exponential flow (expanding
block), general `k`**: from the per-index exp-annulus bounds,
`Σᵢ log‖v i‖ ∈ [k·(log(((11k−1)·(d−ℓ:ℕ):ℝ)) + t/(d−ℓ)),
k·(log(((11k+1)·(d−ℓ:ℕ):ℝ)) + t/(d−ℓ))]`. -/
lemma wedgeLarge_blockAnnulus_log_exp_interval_k (ℓ : ℕ) (hℓd : ℓ < d) {t : ℝ}
    (hk1 : 1 ≤ k)
    (v : Fin k → Submission.LargeBlockMinima.largeFlow (d := d)
        (Real.exp (-t / (ℓ : ℝ))) (Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))) ℓ)
    (hlo : ∀ i, (((11 : ℝ) * (k : ℝ) - 1) * ((d - ℓ : ℕ) : ℝ)) *
          Real.exp (t / ((d : ℝ) - (ℓ : ℝ))) ≤ ‖(v i : RD d)‖)
    (hhi : ∀ i, ‖(v i : RD d)‖ ≤ (((11 : ℝ) * (k : ℝ) + 1) * ((d - ℓ : ℕ) : ℝ)) *
          Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))) :
    (k : ℝ) * (Real.log (((11 : ℝ) * (k : ℝ) - 1) * ((d - ℓ : ℕ) : ℝ)) +
          t / ((d : ℝ) - (ℓ : ℝ))) ≤
        (∑ i : Fin k, Real.log ‖(v i : RD d)‖) ∧
      (∑ i : Fin k, Real.log ‖(v i : RD d)‖) ≤
        (k : ℝ) * (Real.log (((11 : ℝ) * (k : ℝ) + 1) * ((d - ℓ : ℕ) : ℝ)) +
          t / ((d : ℝ) - (ℓ : ℝ))) := by
  have hint := wedgeLarge_blockAnnulus_log_interval_k (d := d) ℓ hℓd
    (a := Real.exp (-t / (ℓ : ℝ))) (b := Real.exp (t / ((d : ℝ) - (ℓ : ℝ))))
    (Real.exp_pos _) hk1 v hlo hhi
  have hkR : 1 ≤ (k : ℝ) := by exact_mod_cast hk1
  have hm0 : (11 : ℝ) * (k : ℝ) - 1 ≠ 0 := by
    have : 0 < (11 : ℝ) * (k : ℝ) - 1 := by nlinarith
    exact ne_of_gt this
  have hm1 : (11 : ℝ) * (k : ℝ) + 1 ≠ 0 := by
    have : 0 < (11 : ℝ) * (k : ℝ) + 1 := by nlinarith
    exact ne_of_gt this
  constructor
  · calc
      (k : ℝ) * (Real.log (((11 : ℝ) * (k : ℝ) - 1) * ((d - ℓ : ℕ) : ℝ)) +
            t / ((d : ℝ) - (ℓ : ℝ)))
          = (k : ℝ) * Real.log ((((11 : ℝ) * (k : ℝ) - 1) * ((d - ℓ : ℕ) : ℝ)) *
              Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))) := by
              congr 1
              rw [log_mul_annulus_exp_large ((11 : ℝ) * (k : ℝ) - 1) hm0 ℓ hℓd t]
      _ ≤ (∑ i : Fin k, Real.log ‖(v i : RD d)‖) := hint.1
  · calc
      (∑ i : Fin k, Real.log ‖(v i : RD d)‖) ≤
          (k : ℝ) * Real.log ((((11 : ℝ) * (k : ℝ) + 1) * ((d - ℓ : ℕ) : ℝ)) *
              Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))) := hint.2
      _ = (k : ℝ) * (Real.log (((11 : ℝ) * (k : ℝ) + 1) * ((d - ℓ : ℕ) : ℝ)) +
            t / ((d : ℝ) - (ℓ : ℝ))) := by
            congr 1
            rw [log_mul_annulus_exp_large ((11 : ℝ) * (k : ℝ) + 1) hm1 ℓ hℓd t]


/-- **Log-form sandwich in the exponential flow (expanding block)**: under the exp-annulus
hypotheses and `k ≤ 4`, `Σᵢ log‖v i‖ + log(1 − k/5) ≤ log‖π₁(ιMulti v)‖ ≤ Σᵢ log‖v i‖`. -/
lemma wedgeLarge_blockAnnulus_log_twoSided_exp (ℓ : ℕ) (hℓd : ℓ < d) {t : ℝ} (hk4 : k ≤ 4)
    (u : Fin k → RD d)
    (hu_mem : ∀ i, u i ∈ Submission.LargeBlockCovering.largeSpan (d := d) ℓ)
    (huON : Orthonormal ℝ u) (hk : 0 < k)
    (v : Fin k → Submission.LargeBlockMinima.largeFlow (d := d)
        (Real.exp (-t / (ℓ : ℝ))) (Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))) ℓ)
    (hvann : ∀ i, ‖(v i : RD d) - ((11 : ℝ) * ((d - ℓ : ℕ) : ℝ) * Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))) • u i‖ ≤
          ((d - ℓ : ℕ) : ℝ) * Real.exp (t / ((d : ℝ) - (ℓ : ℝ))) ∧
        (10 : ℝ) * ((d - ℓ : ℕ) : ℝ) * Real.exp (t / ((d : ℝ) - (ℓ : ℝ))) ≤ ‖(v i : RD d)‖ ∧
        ‖(v i : RD d)‖ ≤ (12 : ℝ) * ((d - ℓ : ℕ) : ℝ) * Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))) :
    (∑ i : Fin k, Real.log ‖(v i : RD d)‖) + Real.log (1 - (k : ℝ) / 5) ≤
        Real.log ‖pi1 (d := d) (k := k) ℓ
          (exteriorPower.ιMulti ℝ k (fun i : Fin k => (v i : RD d)))‖ ∧
      Real.log ‖pi1 (d := d) (k := k) ℓ
        (exteriorPower.ιMulti ℝ k (fun i : Fin k => (v i : RD d)))‖ ≤
        (∑ i : Fin k, Real.log ‖(v i : RD d)‖) := by
  exact wedgeLarge_blockAnnulus_log_twoSided (d := d) ℓ hℓd
    (a := Real.exp (-t / (ℓ : ℝ))) (b := Real.exp (t / ((d : ℝ) - (ℓ : ℝ))))
    (Real.exp_pos _) hk4 u hu_mem huON hk v hvann

/-- **Exponential-length interval for the expanding-block annulus family**: under the
per-index exp-annulus bounds, `Σᵢ log‖v i‖ ∈ [k·log(10·((d−ℓ:ℕ):ℝ)) + k·t/(d−ℓ),
k·log(12·((d−ℓ:ℕ):ℝ)) + k·t/(d−ℓ)]`. -/
lemma wedgeLarge_blockAnnulus_log_exp_interval (ℓ : ℕ) (hℓd : ℓ < d) {t : ℝ}
    (v : Fin k → Submission.LargeBlockMinima.largeFlow (d := d)
        (Real.exp (-t / (ℓ : ℝ))) (Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))) ℓ)
    (hlo : ∀ i, (10 : ℝ) * ((d - ℓ : ℕ) : ℝ) * Real.exp (t / ((d : ℝ) - (ℓ : ℝ))) ≤ ‖(v i : RD d)‖)
    (hhi : ∀ i, ‖(v i : RD d)‖ ≤ (12 : ℝ) * ((d - ℓ : ℕ) : ℝ) * Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))) :
    (k : ℝ) * Real.log ((10 : ℝ) * ((d - ℓ : ℕ) : ℝ)) + (k : ℝ) * (t / ((d : ℝ) - (ℓ : ℝ))) ≤
        (∑ i : Fin k, Real.log ‖(v i : RD d)‖) ∧
      (∑ i : Fin k, Real.log ‖(v i : RD d)‖) ≤
        (k : ℝ) * Real.log ((12 : ℝ) * ((d - ℓ : ℕ) : ℝ)) + (k : ℝ) * (t / ((d : ℝ) - (ℓ : ℝ))) := by
  have hint := wedgeLarge_blockAnnulus_log_interval (d := d) ℓ hℓd
    (a := Real.exp (-t / (ℓ : ℝ))) (b := Real.exp (t / ((d : ℝ) - (ℓ : ℝ))))
    (Real.exp_pos _) v hlo hhi
  constructor
  · calc
      (k : ℝ) * Real.log ((10 : ℝ) * ((d - ℓ : ℕ) : ℝ)) + (k : ℝ) * (t / ((d : ℝ) - (ℓ : ℝ)))
          = (k : ℝ) * (Real.log ((10 : ℝ) * ((d - ℓ : ℕ) : ℝ)) + t / ((d : ℝ) - (ℓ : ℝ))) := by
              rw [mul_add]
      _ = (k : ℝ) * Real.log ((10 : ℝ) * ((d - ℓ : ℕ) : ℝ) * Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))) := by
              rw [log_mul_annulus_exp_large (10 : ℝ) (by norm_num) ℓ hℓd t]
      _ ≤ (∑ i : Fin k, Real.log ‖(v i : RD d)‖) := hint.1
  · calc
      (∑ i : Fin k, Real.log ‖(v i : RD d)‖) ≤
          (k : ℝ) * Real.log ((12 : ℝ) * ((d - ℓ : ℕ) : ℝ) * Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))) := hint.2
      _ = (k : ℝ) * (Real.log ((12 : ℝ) * ((d - ℓ : ℕ) : ℝ)) + t / ((d : ℝ) - (ℓ : ℝ))) := by
              rw [log_mul_annulus_exp_large (12 : ℝ) (by norm_num) ℓ hℓd t]
      _ = (k : ℝ) * Real.log ((12 : ℝ) * ((d - ℓ : ℕ) : ℝ)) + (k : ℝ) * (t / ((d : ℝ) - (ℓ : ℝ))) := by
              rw [mul_add]

/-- **Expanding-block upper estimate** (exponential flow): under the exp-annulus hypotheses
and `k ≤ 4`, `log‖π₁(ιMulti v)‖ ≤ k·log(12·((d−ℓ:ℕ):ℝ)) + k·t/(d−ℓ)`. -/
lemma wedgeLarge_blockAnnulus_log_upper_exp (ℓ : ℕ) (hℓd : ℓ < d) {t : ℝ} (hk4 : k ≤ 4)
    (u : Fin k → RD d)
    (hu_mem : ∀ i, u i ∈ Submission.LargeBlockCovering.largeSpan (d := d) ℓ)
    (huON : Orthonormal ℝ u) (hk : 0 < k)
    (v : Fin k → Submission.LargeBlockMinima.largeFlow (d := d)
        (Real.exp (-t / (ℓ : ℝ))) (Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))) ℓ)
    (hvann : ∀ i, ‖(v i : RD d) - ((11 : ℝ) * ((d - ℓ : ℕ) : ℝ) * Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))) • u i‖ ≤
          ((d - ℓ : ℕ) : ℝ) * Real.exp (t / ((d : ℝ) - (ℓ : ℝ))) ∧
        (10 : ℝ) * ((d - ℓ : ℕ) : ℝ) * Real.exp (t / ((d : ℝ) - (ℓ : ℝ))) ≤ ‖(v i : RD d)‖ ∧
        ‖(v i : RD d)‖ ≤ (12 : ℝ) * ((d - ℓ : ℕ) : ℝ) * Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))) :
    Real.log ‖pi1 (d := d) (k := k) ℓ
        (exteriorPower.ιMulti ℝ k (fun i : Fin k => (v i : RD d)))‖ ≤
      (k : ℝ) * Real.log ((12 : ℝ) * ((d - ℓ : ℕ) : ℝ)) + (k : ℝ) * (t / ((d : ℝ) - (ℓ : ℝ))) := by
  have hlo : ∀ i, (10 : ℝ) * ((d - ℓ : ℕ) : ℝ) * Real.exp (t / ((d : ℝ) - (ℓ : ℝ))) ≤ ‖(v i : RD d)‖ := by
    intro i
    exact (hvann i).2.1
  have hhi : ∀ i, ‖(v i : RD d)‖ ≤ (12 : ℝ) * ((d - ℓ : ℕ) : ℝ) * Real.exp (t / ((d : ℝ) - (ℓ : ℝ))) := by
    intro i
    exact (hvann i).2.2
  have hup := (wedgeLarge_blockAnnulus_log_twoSided_exp (d := d) ℓ hℓd (t := t) hk4 u
    hu_mem huON hk v hvann).2
  have hint := (wedgeLarge_blockAnnulus_log_exp_interval (d := d) ℓ hℓd (t := t) v
    hlo hhi).2
  exact le_trans hup hint

/-- **Expanding-block lower estimate** (exponential flow): under the exp-annulus hypotheses
and `k ≤ 4`, `k·log(10·((d−ℓ:ℕ):ℝ)) + k·t/(d−ℓ) + log(1 − k/5) ≤ log‖π₁(ιMulti v)‖`. -/
lemma wedgeLarge_blockAnnulus_log_lower_exp (ℓ : ℕ) (hℓd : ℓ < d) {t : ℝ} (hk4 : k ≤ 4)
    (u : Fin k → RD d)
    (hu_mem : ∀ i, u i ∈ Submission.LargeBlockCovering.largeSpan (d := d) ℓ)
    (huON : Orthonormal ℝ u) (hk : 0 < k)
    (v : Fin k → Submission.LargeBlockMinima.largeFlow (d := d)
        (Real.exp (-t / (ℓ : ℝ))) (Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))) ℓ)
    (hvann : ∀ i, ‖(v i : RD d) - ((11 : ℝ) * ((d - ℓ : ℕ) : ℝ) * Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))) • u i‖ ≤
          ((d - ℓ : ℕ) : ℝ) * Real.exp (t / ((d : ℝ) - (ℓ : ℝ))) ∧
        (10 : ℝ) * ((d - ℓ : ℕ) : ℝ) * Real.exp (t / ((d : ℝ) - (ℓ : ℝ))) ≤ ‖(v i : RD d)‖ ∧
        ‖(v i : RD d)‖ ≤ (12 : ℝ) * ((d - ℓ : ℕ) : ℝ) * Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))) :
    (k : ℝ) * Real.log ((10 : ℝ) * ((d - ℓ : ℕ) : ℝ)) + (k : ℝ) * (t / ((d : ℝ) - (ℓ : ℝ))) +
        Real.log (1 - (k : ℝ) / 5) ≤
      Real.log ‖pi1 (d := d) (k := k) ℓ
        (exteriorPower.ιMulti ℝ k (fun i : Fin k => (v i : RD d)))‖ := by
  have hlo : ∀ i, (10 : ℝ) * ((d - ℓ : ℕ) : ℝ) * Real.exp (t / ((d : ℝ) - (ℓ : ℝ))) ≤ ‖(v i : RD d)‖ := by
    intro i
    exact (hvann i).2.1
  have hhi : ∀ i, ‖(v i : RD d)‖ ≤ (12 : ℝ) * ((d - ℓ : ℕ) : ℝ) * Real.exp (t / ((d : ℝ) - (ℓ : ℝ))) := by
    intro i
    exact (hvann i).2.2
  have hlow0 := (wedgeLarge_blockAnnulus_log_exp_interval (d := d) ℓ hℓd (t := t) v
    hlo hhi).1
  have hlow1 := (wedgeLarge_blockAnnulus_log_twoSided_exp (d := d) ℓ hℓd (t := t) hk4 u
    hu_mem huON hk v hvann).1
  have hstep : (k : ℝ) * Real.log ((10 : ℝ) * ((d - ℓ : ℕ) : ℝ)) + (k : ℝ) * (t / ((d : ℝ) - (ℓ : ℝ))) +
        Real.log (1 - (k : ℝ) / 5) ≤
      (∑ i : Fin k, Real.log ‖(v i : RD d)‖) + Real.log (1 - (k : ℝ) / 5) :=
    add_le_add_left hlow0 (Real.log (1 - (k : ℝ) / 5))
  exact le_trans hstep hlow1

/-- **Expanding-block upper, existence form**: for ON directions `u` in the expanding
block's real span (`k ≤ 4`), there is an annulus family `v : Fin k → largeFlow` (exp flow)
whose `π₁`-wedge satisfies
`log‖π₁(ιMulti v)‖ ≤ k·log(12·((d−ℓ:ℕ):ℝ)) + k·t/(d−ℓ)`. -/
theorem exists_wedgeLarge_blockAnnulus_log_upper_exp (ℓ : ℕ) (hℓd : ℓ < d) {t : ℝ}
    (hk4 : k ≤ 4) (u : Fin k → RD d)
    (hu_mem : ∀ i, u i ∈ Submission.LargeBlockCovering.largeSpan (d := d) ℓ)
    (huON : Orthonormal ℝ u) (hk : 0 < k) :
    ∃ v : Fin k → Submission.LargeBlockMinima.largeFlow (d := d)
        (Real.exp (-t / (ℓ : ℝ))) (Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))) ℓ,
      Real.log ‖pi1 (d := d) (k := k) ℓ
        (exteriorPower.ιMulti ℝ k (fun i : Fin k => (v i : RD d)))‖ ≤
        (k : ℝ) * Real.log ((12 : ℝ) * ((d - ℓ : ℕ) : ℝ)) + (k : ℝ) * (t / ((d : ℝ) - (ℓ : ℝ))) := by
  classical
  obtain ⟨v, hv⟩ := Submission.LargeBlockCovering.exists_largeFamily_annulus_exp (d := d) ℓ
    hℓd (m := k) (u := u) hu_mem (fun i => huON.1 i)
  refine ⟨v, ?_⟩
  exact wedgeLarge_blockAnnulus_log_upper_exp (d := d) ℓ hℓd (t := t) hk4 u hu_mem huON hk v hv

/-- **Expanding-block lower, existence form**: for ON directions `u` in the expanding
block's real span (`k ≤ 4`), there is an annulus family `v : Fin k → largeFlow` (exp flow)
whose `π₁`-wedge satisfies
`k·log(10·((d−ℓ:ℕ):ℝ)) + k·t/(d−ℓ) + log(1 − k/5) ≤ log‖π₁(ιMulti v)‖`. -/
theorem exists_wedgeLarge_blockAnnulus_log_lower_exp (ℓ : ℕ) (hℓd : ℓ < d) {t : ℝ}
    (hk4 : k ≤ 4) (u : Fin k → RD d)
    (hu_mem : ∀ i, u i ∈ Submission.LargeBlockCovering.largeSpan (d := d) ℓ)
    (huON : Orthonormal ℝ u) (hk : 0 < k) :
    ∃ v : Fin k → Submission.LargeBlockMinima.largeFlow (d := d)
        (Real.exp (-t / (ℓ : ℝ))) (Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))) ℓ,
      (k : ℝ) * Real.log ((10 : ℝ) * ((d - ℓ : ℕ) : ℝ)) + (k : ℝ) * (t / ((d : ℝ) - (ℓ : ℝ))) +
          Real.log (1 - (k : ℝ) / 5) ≤
        Real.log ‖pi1 (d := d) (k := k) ℓ
          (exteriorPower.ιMulti ℝ k (fun i : Fin k => (v i : RD d)))‖ := by
  classical
  obtain ⟨v, hv⟩ := Submission.LargeBlockCovering.exists_largeFamily_annulus_exp (d := d) ℓ
    hℓd (m := k) (u := u) hu_mem (fun i => huON.1 i)
  refine ⟨v, ?_⟩
  exact wedgeLarge_blockAnnulus_log_lower_exp (d := d) ℓ hℓd (t := t) hk4 u hu_mem huON hk v hv

/-- **Expanding `k`-slope sum**: `k` expanding directions each of log-scale `t/(d−ℓ)` sum to
`t·(k/(d−ℓ))` — the slope-visible exponent of the expanding-block estimate. -/
lemma wedgeLarge_expBlock_slope_sum (ℓ : ℕ) {t : ℝ} (k : ℕ) :
    (∑ _ : Fin k, Real.log (Real.exp (t / ((d : ℝ) - (ℓ : ℝ))))) = t * ((k : ℝ) / ((d : ℝ) - (ℓ : ℝ))) := by
  calc
    (∑ _ : Fin k, Real.log (Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))))
        = (∑ _ : Fin k, (t / ((d : ℝ) - (ℓ : ℝ)))) := by
            simp [Real.log_exp]
    _ = (k : ℝ) * (t / ((d : ℝ) - (ℓ : ℝ))) := by simp [Finset.sum_const, Fintype.card_fin]
    _ = t * ((k : ℝ) / ((d : ℝ) - (ℓ : ℝ))) := by
            rw [div_eq_mul_inv]
            ring

/-- **Expanding-block upper bound, slope-visible form**: under the exp-annulus hypotheses and
`k ≤ 4`, `log‖π₁(ιMulti v)‖ ≤ k·log(12·((d−ℓ:ℕ):ℝ)) + t·(k/(d−ℓ))` — the exponent's
`t`-coefficient is the expanding slope-sum `k/(d−ℓ)` (cf. `wedgeLarge_expBlock_slope_sum`). -/
lemma wedgeLarge_blockAnnulus_log_upper_exp_slope (ℓ : ℕ) (hℓd : ℓ < d) {t : ℝ} (hk4 : k ≤ 4)
    (u : Fin k → RD d)
    (hu_mem : ∀ i, u i ∈ Submission.LargeBlockCovering.largeSpan (d := d) ℓ)
    (huON : Orthonormal ℝ u) (hk : 0 < k)
    (v : Fin k → Submission.LargeBlockMinima.largeFlow (d := d)
        (Real.exp (-t / (ℓ : ℝ))) (Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))) ℓ)
    (hvann : ∀ i, ‖(v i : RD d) - ((11 : ℝ) * ((d - ℓ : ℕ) : ℝ) * Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))) • u i‖ ≤
          ((d - ℓ : ℕ) : ℝ) * Real.exp (t / ((d : ℝ) - (ℓ : ℝ))) ∧
        (10 : ℝ) * ((d - ℓ : ℕ) : ℝ) * Real.exp (t / ((d : ℝ) - (ℓ : ℝ))) ≤ ‖(v i : RD d)‖ ∧
        ‖(v i : RD d)‖ ≤ (12 : ℝ) * ((d - ℓ : ℕ) : ℝ) * Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))) :
    Real.log ‖pi1 (d := d) (k := k) ℓ
        (exteriorPower.ιMulti ℝ k (fun i : Fin k => (v i : RD d)))‖ ≤
      (k : ℝ) * Real.log ((12 : ℝ) * ((d - ℓ : ℕ) : ℝ)) +
        t * ((k : ℝ) / ((d : ℝ) - (ℓ : ℝ))) := by
  have h := wedgeLarge_blockAnnulus_log_upper_exp (d := d) ℓ hℓd (t := t) hk4 u
    hu_mem huON hk v hvann
  have hs : (k : ℝ) * (t / ((d : ℝ) - (ℓ : ℝ))) = t * ((k : ℝ) / ((d : ℝ) - (ℓ : ℝ))) := by
    rw [div_eq_mul_inv]
    ring
  rwa [hs] at h

end Submission.WedgeExpanding
