import Mathlib
import Submission.GeometryOfNumbers.WedgeGeneralE1
import Submission.Commons.LinearAlgebra.ExteriorPower.iMulti_linearIndependent_of_ne_zero

/-!
# Block-0 of a pure tensor vs. the projected exterior power (bridge step (i), (ii))

Model: `RD d` with reference plane `x₀ = modelX ℓ` and `P = projMap (modelX ℓ)` the
orthogonal projection onto `x₀`.

* `blockElem_zero_eq_map_modelProj`: for every `k`-vector `w`, the block-0 component
  (`j = 0`: subsets with no index `≥ ℓ`) equals the image of `w` under the induced map
  `⋀^k P` on the exterior power.  Coordinate proof: `P` fixes the low standard vectors and
  kills the high ones, so on the standard exterior-power basis the `⋀^k P`-action is the
  identity on the block-0 basis vectors and zero on all others.

* `blockElem_zero_ιMulti`: hence for a pure tensor `ιMulti u`, `blockElem (ιMulti u) 0 =
  ιMulti (P ∘ u)` (`exteriorPower.map_apply_ιMulti`).

* `inj_modelX_of_block0_ne_zero` (bridge step (ii)): for a linearly independent family `u`,
  `blockElem (ιMulti u) 0 ≠ 0` implies `span(range u) ⊓ (modelX ℓ)ᗮ = ⊥`.  Contrapositive:
  a nonzero vector `v = Σ αⱼ uⱼ ∈ span(range u) ∩ x₀ᗮ` is projected to zero by `P`, so
  `Σ αⱼ • P uⱼ = 0` is a nontrivial linear dependence of `P ∘ u` (nontrivial since `α ≠ 0`
  by independence of `u` and `v ≠ 0`); hence `ιMulti (P ∘ u) = 0`
  (`AlternatingMap.map_linearDependent`), which is `block₀(ιMulti u) = 0` — contradiction.

All results here are Mathlib-only (besides the Submission geometry modules).
-/

noncomputable section

open Module exteriorPower InnerProductGeometry Real
open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false

open Submission.ExteriorCoordinates
open Submission.DiagonalFlow
open Submission.WedgeBlocks
open Submission.WedgeGeneralE1

namespace Submission.WedgeBlockZero

variable {d k : ℕ}

/-- The orthogonal projection onto the model plane `x₀ = modelX ℓ`, as a linear map. -/
def modelProj (ℓ : ℕ) : RD d →ₗ[ℝ] RD d :=
  Submission.WedgeGeneralE1.projMap (modelX ℓ)

/-- The projection onto `x₀` fixes the low standard vectors. -/
lemma modelProj_std_low (ℓ : ℕ) (j : Fin d) (hj : j.val < ℓ) :
    modelProj ℓ ((B d) j) = (B d) j := by
  unfold modelProj
  rw [projMap_apply]
  exact Submodule.starProjection_eq_self_iff.mpr (std_mem_modelX ℓ j hj)

/-- The projection onto `x₀` kills the high standard vectors. -/
lemma modelProj_std_high (ℓ : ℕ) (j : Fin d) (hj : ℓ ≤ j.val) :
    modelProj ℓ ((B d) j) = 0 := by
  unfold modelProj
  rw [projMap_apply]
  exact (starProjection_eq_zero_iff_orthogonal (modelX ℓ) ((B d) j)).mpr
    (std_mem_modelX_orth ℓ j hj)

/-- For a `k`-vector, the block-0 component equals the image under the induced exterior-power
map `⋀^k P` of the projection onto `x₀`. -/
lemma blockElem_zero_eq_map_modelProj (ℓ : ℕ) (w : WK d k) :
    blockElem (d := d) (k := k) (ℓ := ℓ) w 0 =
      exteriorPower.map k (modelProj ℓ) w := by
  classical
  -- first: the `⋀^k P`-image of the standard basis vector at `s` is the basis vector when
  -- `s` contains no index `≥ ℓ`, and is zero otherwise.
  have hbasis : ∀ s : IDX d k,
      exteriorPower.map k (modelProj ℓ) ((Bk d k) s : WK d k) =
        if ((s : Finset (Fin d)).filter (fun i : Fin d => ℓ ≤ i.val)).card = 0
        then ((Bk d k) s : WK d k) else 0 := by
    intro s
    let σ : Fin k → Fin d := Set.powersetCard.ofFinEmbEquiv.symm s
    have hb : ((Bk d k) s : WK d k) =
        exteriorPower.ιMulti ℝ k (fun r : Fin k => (B d) (σ r)) :=
      basisWedge_eq_enumWedge (d := d) (k := k) s
    by_cases hs : ((s : Finset (Fin d)).filter (fun i : Fin d => ℓ ≤ i.val)).card = 0
    · rw [if_pos hs]
      have hσlt : ∀ r : Fin k, (σ r).val < ℓ := by
        intro r
        have hmem : σ r ∈ (s : Finset (Fin d)) := by
          exact (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem (s := s) (i := σ r)).mp
            (Set.mem_range.mpr ⟨r, rfl⟩)
        by_contra hge
        have hge' : ℓ ≤ (σ r).val := le_of_not_gt hge
        have hfilter : (σ r) ∈ (s : Finset (Fin d)).filter (fun i : Fin d => ℓ ≤ i.val) :=
          Finset.mem_filter.mpr ⟨hmem, hge'⟩
        have hempty : (s : Finset (Fin d)).filter (fun i : Fin d => ℓ ≤ i.val) = ∅ :=
          Finset.card_eq_zero.mp hs
        have : σ r ∈ (∅ : Finset (Fin d)) := by simpa [hempty] using hfilter
        simpa using this
      calc
        exteriorPower.map k (modelProj ℓ) ((Bk d k) s : WK d k)
            = exteriorPower.map k (modelProj ℓ)
                (exteriorPower.ιMulti ℝ k (fun r : Fin k => (B d) (σ r))) := by rw [hb]
        _ = exteriorPower.ιMulti ℝ k (fun r : Fin k => modelProj ℓ ((B d) (σ r))) := by
              rw [exteriorPower.map_apply_ιMulti]
              rfl
        _ = exteriorPower.ιMulti ℝ k (fun r : Fin k => (B d) (σ r)) := by
              apply congrArg (exteriorPower.ιMulti ℝ k)
              funext r
              exact modelProj_std_low ℓ (σ r) (hσlt r)
        _ = ((Bk d k) s : WK d k) := by rw [← hb]
    · rw [if_neg hs]
      have hne : (s : Finset (Fin d)).filter (fun i : Fin d => ℓ ≤ i.val) ≠ ∅ := by
        intro hempty
        exact hs (Finset.card_eq_zero.mpr hempty)
      have hnonempty : ((s : Finset (Fin d)).filter (fun i : Fin d => ℓ ≤ i.val)).Nonempty :=
        Finset.card_pos.mp (Nat.pos_of_ne_zero (by
          intro hzero
          exact hs hzero))
      rcases (Finset.nonempty_iff_ne_empty.mpr hne) with ⟨j, hj⟩
      rcases (Finset.mem_filter.mp hj) with ⟨hjS, hjge⟩
      -- j ∈ s, write j = σ r
      have hjrange : j ∈ Set.range σ :=
        (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem (s := s) (i := j)).mpr hjS
      rcases (Set.mem_range.mp hjrange) with ⟨r, hr⟩
      have hzero : modelProj ℓ ((B d) j) = 0 := modelProj_std_high ℓ j hjge
      calc
        exteriorPower.map k (modelProj ℓ) ((Bk d k) s : WK d k)
            = exteriorPower.map k (modelProj ℓ)
                (exteriorPower.ιMulti ℝ k (fun r : Fin k => (B d) (σ r))) := by rw [hb]
        _ = exteriorPower.ιMulti ℝ k (fun r : Fin k => modelProj ℓ ((B d) (σ r))) := by
              rw [exteriorPower.map_apply_ιMulti]
              rfl
        _ = 0 := by
              have hf : (fun r : Fin k => modelProj ℓ ((B d) (σ r))) r = 0 := by
                simpa [hr] using hzero
              exact AlternatingMap.map_coord_zero (exteriorPower.ιMulti ℝ k) r hf
  -- expand w in the standard basis and push the exterior-power map through the sum
  calc
    blockElem (d := d) (k := k) (ℓ := ℓ) w 0
        = (blockFinset (d := d) (k := k) (ℓ := ℓ) 0).sum (fun s =>
            wcoord (d := d) (k := k) w s • ((Bk d k) s : WK d k)) := by rfl
    _ = ((Finset.univ : Finset (IDX d k)).filter
          (fun s : IDX d k => ((s : Finset (Fin d)).filter
            (fun i : Fin d => ℓ ≤ i.val)).card = 0)).sum (fun s =>
            wcoord (d := d) (k := k) w s • ((Bk d k) s : WK d k)) := by
          simp [blockFinset]
    _ = (Finset.univ : Finset (IDX d k)).sum (fun s =>
          if ((s : Finset (Fin d)).filter (fun i : Fin d => ℓ ≤ i.val)).card = 0
          then wcoord (d := d) (k := k) w s • ((Bk d k) s : WK d k) else 0) := by
          rw [Finset.sum_filter]
    _ = (Finset.univ : Finset (IDX d k)).sum (fun s =>
          wcoord (d := d) (k := k) w s •
            (exteriorPower.map k (modelProj ℓ) ((Bk d k) s : WK d k))) := by
          apply Finset.sum_congr rfl
          intro s hs
          by_cases hc : ((s : Finset (Fin d)).filter (fun i : Fin d => ℓ ≤ i.val)).card = 0
          · simp [hc, hbasis s]
          · simp [hc, hbasis s]
    _ = exteriorPower.map k (modelProj ℓ)
          ((Finset.univ : Finset (IDX d k)).sum (fun s =>
            wcoord (d := d) (k := k) w s • ((Bk d k) s : WK d k))) := by
          rw [map_sum]
          apply Finset.sum_congr rfl
          intro s hs
          rw [map_smul]
    _ = exteriorPower.map k (modelProj ℓ) w := by
          rw [sum_wcoord_smul_basis (d := d) (k := k) w]

/-- Block-0 of a pure tensor is the exterior power of the projected family. -/
lemma blockElem_zero_ιMulti (ℓ : ℕ) (u : Fin k → RD d) :
    blockElem (d := d) (k := k) (ℓ := ℓ) (exteriorPower.ιMulti ℝ k u) 0 =
      exteriorPower.ιMulti ℝ k (fun i => modelProj ℓ (u i)) := by
  rw [blockElem_zero_eq_map_modelProj ℓ (exteriorPower.ιMulti ℝ k u)]
  rw [exteriorPower.map_apply_ιMulti]
  rfl

/-- **Bridge step (ii)**: a nonzero block-0 forces `span(range u) ⊓ x₀ᗮ = ⊥` (the
orthogonal projection onto `x₀` is injective on the plane `span(range u)`). -/
lemma inj_modelX_of_block0_ne_zero (ℓ : ℕ) (u : Fin k → RD d)
    (hu : LinearIndependent ℝ u)
    (hblk : blockElem (d := d) (k := k) (ℓ := ℓ) (exteriorPower.ιMulti ℝ k u) 0 ≠ 0) :
    (Submodule.span ℝ (Set.range u)) ⊓ (modelX ℓ)ᗮ = ⊥ := by
  classical
  let P : RD d →ₗ[ℝ] RD d := modelProj ℓ
  rw [Submodule.eq_bot_iff]
  intro v hv
  by_contra hne
  rcases (Submodule.mem_inf.mp hv) with ⟨hvV, hvO⟩
  rcases (Submodule.mem_span_range_iff_exists_fun (R := ℝ) (v := u)).mp hvV with ⟨α, hα⟩
  -- hα : (∑ j, α j • u j) = v
  have hPv : P v = 0 := by
    dsimp [P]
    exact (starProjection_eq_zero_iff_orthogonal (modelX ℓ) v).mpr hvO
  have hsumP : (Finset.univ : Finset (Fin k)).sum (fun j => α j • P (u j)) = 0 := by
    have hαP : (Finset.univ : Finset (Fin k)).sum (fun j => α j • P (u j)) =
        P ((Finset.univ : Finset (Fin k)).sum (fun j => α j • u j)) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [map_smul]
    rw [hαP, hα, hPv]
  -- α is nontrivial (else v = 0)
  have hα_nonzero : ∃ j : Fin k, α j ≠ 0 := by
    by_contra h
    have hα0 : ∀ j : Fin k, α j = 0 := by
      intro j
      by_contra hj
      exact h ⟨j, hj⟩
    have hv0 : v = 0 := by
      calc
        v = (Finset.univ : Finset (Fin k)).sum (fun j => α j • u j) := hα.symm
        _ = 0 := by simp [hα0]
    exact hne hv0
  -- the projected family P ∘ u is linearly dependent
  have hdep : ¬ LinearIndependent ℝ (fun j => P (u j)) := by
    intro hli
    have hα0 : ∀ j : Fin k, α j = 0 :=
      (Fintype.linearIndependent_iffₛ.mp hli) α (fun _ : Fin k => (0 : ℝ)) (by simpa using hsumP)
    rcases hα_nonzero with ⟨j, hj⟩
    exact hj (hα0 j)
  -- hence its wedge vanishes
  have hw0 : exteriorPower.ιMulti ℝ k (fun j => P (u j)) = 0 := by
    exact AlternatingMap.map_linearDependent (f := exteriorPower.ιMulti ℝ k)
      (fun j => P (u j)) hdep
  -- but block-0 of ιMulti u is exactly that wedge
  have hb : blockElem (d := d) (k := k) (ℓ := ℓ) (exteriorPower.ιMulti ℝ k u) 0 = 0 := by
    have h' := blockElem_zero_ιMulti (d := d) (k := k) ℓ u
    rw [h']
    simpa [P] using hw0
  exact hblk hb

end Submission.WedgeBlockZero
