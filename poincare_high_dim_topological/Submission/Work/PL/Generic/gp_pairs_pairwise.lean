import Mathlib
import Submission.Work.PL.Defs
import Submission.Work.PL.Generic.Basic
import Submission.Work.PL.Generic.Hull
import Submission.Work.PL.Generic.mem_hullOf
import Submission.Work.PL.Generic.mem_union_of_sum_smul_eq_of_frozen
import Submission.Work.PL.Generic.affineSpan_eq_top_of_sum_smul_ne
import Submission.Work.PL.Generic.domDim_of_isBounded_subset_affineSubspace

open Set

namespace Work.PL.Generic

/-- The affine span of the images of a union of index sets is the sup of the two affine spans. -/
theorem affineSpan_image_union {n : ℕ} {ι : Type*} [DecidableEq ι]
    (y : ι → PL.E n) (σ₁ σ₂ : Finset ι) :
    affineSpan ℝ (y '' ((σ₁ ∪ σ₂ : Finset ι) : Set ι))
      = affineSpan ℝ (y '' (σ₁ : Set ι)) ⊔ affineSpan ℝ (y '' (σ₂ : Set ι)) := by
  rw [Finset.coe_union, Set.image_union, AffineSubspace.span_union]

/-- The pairwise conjunct of `Work.PL.Generic.gp_pairs`, pointwise and with the perturbation
abstracted into `hgp`.  Proof (as in `Submission/Work/NOTES_LEAD_poincare_engulf.md` §4.1):
for `x` in the intersection take barycentric representations on `σ₁` and `σ₂` (`mem_hullOf`).
Case split on `W := affineSpan ℝ (y '' (σ₁ ∪ σ₂)) = ⊤`:
* `W = ⊤`: then, writing `A = affineSpan ℝ (y '' σ₁)`, `B = affineSpan ℝ (y '' σ₂)` with `A ⊔ B = W`
  (via `AffineSubspace.direction_sup`), the dimension formula gives
  `finrank (A ⊓ B).direction ≤ |σ₁| + |σ₂| - 2 - n`; every common point lies in the bounded `A ⊓ B`,
  so `domDim_of_isBounded_subset_affineSubspace` applies with `D` = the intersection.
* `W ≠ ⊤`: `affineSpan_eq_top_of_sum_smul_ne` (contrapositive, using `hgp`) rules out representations
  whose free coefficients differ, so `mem_union_of_sum_smul_eq_of_frozen` applies and `D = ∅` works. -/
theorem gp_pairs_pairwise {n : ℕ} {ι : Type*} [DecidableEq ι]
    (fz : Finset ι) (y : ι → PL.E n) (σ₁ σ₂ : Finset ι)
    (hgp : ∀ u, u ∉ fz → ∀ T : Finset ι, T ⊆ σ₁ ∪ σ₂ → u ∉ T →
      y u ∈ (affineSpan ℝ (y '' (T : Set ι)) : Set (PL.E n)) →
        affineSpan ℝ (y '' (T : Set ι)) = ⊤)
    (hcol : ∀ z ∈ Work.PL.Generic.hullOf y (σ₁ ∩ fz) ∩ Work.PL.Generic.hullOf y (σ₂ ∩ fz),
      (∃ v ∈ σ₁ ∩ σ₂, v ∉ fz) → z ∈ Work.PL.Generic.hullOf y (σ₁ ∩ σ₂ ∩ fz)) :
    ∃ D : Set (PL.E n), PL.DomDim D ((σ₁.card : ℤ) + (σ₂.card : ℤ) - 2 - (n : ℤ)) ∧
      Work.PL.Generic.hullOf y σ₁ ∩ Work.PL.Generic.hullOf y σ₂ ⊆
        Work.PL.Generic.hullOf y (σ₁ ∩ σ₂) ∪
          (Work.PL.Generic.hullOf y (σ₁ ∩ fz) ∩ Work.PL.Generic.hullOf y (σ₂ ∩ fz)) ∪ D := by
  classical
  by_cases hW : affineSpan ℝ (y '' ((σ₁ ∪ σ₂ : Finset ι) : Set ι)) = ⊤
  · -- Case `W = ⊤`: the whole common hull is dominated by the intersection of the two spans.
    refine ⟨hullOf y σ₁ ∩ hullOf y σ₂, ?_, Set.subset_union_right⟩
    by_cases hne : (hullOf y σ₁ ∩ hullOf y σ₂).Nonempty
    · obtain ⟨x, hx⟩ := hne
      rw [Set.mem_inter_iff] at hx
      have hxA : x ∈ affineSpan ℝ (y '' (σ₁ : Set ι)) := hullOf_subset_affineSpan y σ₁ hx.1
      have hxB : x ∈ affineSpan ℝ (y '' (σ₂ : Set ι)) := hullOf_subset_affineSpan y σ₂ hx.2
      have hne1 : σ₁.Nonempty := by
        by_contra h
        rw [Finset.not_nonempty_iff_eq_empty] at h
        rw [h, hullOf_empty] at hx
        exact hx.1
      have hne2 : σ₂.Nonempty := by
        by_contra h
        rw [Finset.not_nonempty_iff_eq_empty] at h
        rw [h, hullOf_empty] at hx
        exact hx.2
      have hAB : affineSpan ℝ (y '' (σ₁ : Set ι)) ⊔ affineSpan ℝ (y '' (σ₂ : Set ι)) = ⊤ :=
        (affineSpan_image_union y σ₁ σ₂).symm.trans hW
      -- The two directions already span everything, using the common point `x`.
      have hUV : (affineSpan ℝ (y '' (σ₁ : Set ι))).direction ⊔
          (affineSpan ℝ (y '' (σ₂ : Set ι))).direction = ⊤ := by
        have h := AffineSubspace.direction_sup (k := ℝ) hxA hxB
        rw [hAB, AffineSubspace.direction_top, vsub_self, Submodule.span_zero_singleton,
          sup_bot_eq] at h
        exact h.symm
      have hdirinf : (affineSpan ℝ (y '' (σ₁ : Set ι)) ⊓
            affineSpan ℝ (y '' (σ₂ : Set ι))).direction
          = (affineSpan ℝ (y '' (σ₁ : Set ι))).direction ⊓
            (affineSpan ℝ (y '' (σ₂ : Set ι))).direction :=
        AffineSubspace.direction_inf_of_mem hxA hxB
      -- Dimension formula for the intersection of the two directions.
      have hsup : n + Module.finrank ℝ ↥((affineSpan ℝ (y '' (σ₁ : Set ι))).direction ⊓
            (affineSpan ℝ (y '' (σ₂ : Set ι))).direction)
          = Module.finrank ℝ ↥(affineSpan ℝ (y '' (σ₁ : Set ι))).direction
            + Module.finrank ℝ ↥(affineSpan ℝ (y '' (σ₂ : Set ι))).direction := by
        have h := Submodule.finrank_sup_add_finrank_inf_eq
          (affineSpan ℝ (y '' (σ₁ : Set ι))).direction
          (affineSpan ℝ (y '' (σ₂ : Set ι))).direction
        rw [hUV, finrank_top, finrank_euclideanSpace, Fintype.card_fin] at h
        exact h
      -- Each direction is spanned by `|σᵢ| - 1` vectors.
      have hU : (Module.finrank ℝ ↥(affineSpan ℝ (y '' (σ₁ : Set ι))).direction : ℤ)
          ≤ (σ₁.card : ℤ) - 1 := by
        have hc1 : σ₁.card = (σ₁.card - 1) + 1 := by
          have h1 : 0 < σ₁.card := Finset.card_pos.mpr hne1
          omega
        have hle := finrank_vectorSpan_image_finset_le (k := ℝ) y σ₁ hc1
        have hle' : Module.finrank ℝ ↥(affineSpan ℝ (y '' (σ₁ : Set ι))).direction
            ≤ σ₁.card - 1 := by
          rw [direction_affineSpan, ← Finset.coe_image]
          exact hle
        have h3 : (Module.finrank ℝ ↥(affineSpan ℝ (y '' (σ₁ : Set ι))).direction : ℤ)
            ≤ ((σ₁.card - 1 : ℕ) : ℤ) := by exact_mod_cast hle'
        have h2 : ((σ₁.card - 1 : ℕ) : ℤ) = (σ₁.card : ℤ) - 1 := by
          have h1 : (1 : ℕ) ≤ σ₁.card := Finset.card_pos.mpr hne1
          omega
        omega
      have hV : (Module.finrank ℝ ↥(affineSpan ℝ (y '' (σ₂ : Set ι))).direction : ℤ)
          ≤ (σ₂.card : ℤ) - 1 := by
        have hc2 : σ₂.card = (σ₂.card - 1) + 1 := by
          have h1 : 0 < σ₂.card := Finset.card_pos.mpr hne2
          omega
        have hle := finrank_vectorSpan_image_finset_le (k := ℝ) y σ₂ hc2
        have hle' : Module.finrank ℝ ↥(affineSpan ℝ (y '' (σ₂ : Set ι))).direction
            ≤ σ₂.card - 1 := by
          rw [direction_affineSpan, ← Finset.coe_image]
          exact hle
        have h3 : (Module.finrank ℝ ↥(affineSpan ℝ (y '' (σ₂ : Set ι))).direction : ℤ)
            ≤ ((σ₂.card - 1 : ℕ) : ℤ) := by exact_mod_cast hle'
        have h2 : ((σ₂.card - 1 : ℕ) : ℤ) = (σ₂.card : ℤ) - 1 := by
          have h1 : (1 : ℕ) ≤ σ₂.card := Finset.card_pos.mpr hne2
          omega
        omega
      refine domDim_of_isBounded_subset_affineSubspace
        (A := hullOf y σ₁ ∩ hullOf y σ₂)
        (d := (σ₁.card : ℤ) + (σ₂.card : ℤ) - 2 - (n : ℤ))
        (F := affineSpan ℝ (y '' (σ₁ : Set ι)) ⊓ affineSpan ℝ (y '' (σ₂ : Set ι)))
        (Bornology.IsBounded.subset (isBounded_hullOf y σ₁) Set.inter_subset_left) ?_ ?_
      · intro z hz
        rw [Set.mem_inter_iff] at hz
        rw [AffineSubspace.coe_inf]
        exact ⟨hullOf_subset_affineSpan y σ₁ hz.1, hullOf_subset_affineSpan y σ₂ hz.2⟩
      · rw [hdirinf]
        have hZ : (Module.finrank ℝ ↥((affineSpan ℝ (y '' (σ₁ : Set ι))).direction ⊓
              (affineSpan ℝ (y '' (σ₂ : Set ι))).direction) : ℤ)
            = (Module.finrank ℝ ↥(affineSpan ℝ (y '' (σ₁ : Set ι))).direction : ℤ)
              + (Module.finrank ℝ ↥(affineSpan ℝ (y '' (σ₂ : Set ι))).direction : ℤ) - n := by
          have hc : ((n : ℤ) + (Module.finrank ℝ ↥((affineSpan ℝ (y '' (σ₁ : Set ι))).direction ⊓
              (affineSpan ℝ (y '' (σ₂ : Set ι))).direction) : ℤ))
              = (Module.finrank ℝ ↥(affineSpan ℝ (y '' (σ₁ : Set ι))).direction : ℤ)
                + (Module.finrank ℝ ↥(affineSpan ℝ (y '' (σ₂ : Set ι))).direction : ℤ) := by
            exact_mod_cast hsup
          omega
        rw [hZ]
        omega
    · -- The common hull is empty.
      rw [Set.not_nonempty_iff_eq_empty] at hne
      rw [hne]
      exact PL.DomDim.empty _
  · -- Case `W ≠ ⊤`: the two barycentric representations agree on the free coefficients, and
    -- `mem_union_of_sum_smul_eq_of_frozen` applies with `D = ∅`.
    refine ⟨∅, PL.DomDim.empty _, ?_⟩
    rw [Set.union_empty]
    intro x hx
    rw [Set.mem_inter_iff] at hx
    obtain ⟨a, ha0, has, hay⟩ := (mem_hullOf y σ₁ x).mp hx.1
    obtain ⟨b, hb0, hbs, hby⟩ := (mem_hullOf y σ₂ x).mp hx.2
    have heq : ∑ v ∈ σ₁, a v • y v = ∑ v ∈ σ₂, b v • y v := by rw [hay, hby]
    have hfree : ∀ v, v ∉ fz → (if v ∈ σ₁ then a v else 0) = (if v ∈ σ₂ then b v else 0) := by
      intro v hv
      by_contra hne
      exact hW (affineSpan_eq_top_of_sum_smul_ne fz y has hbs heq ⟨v, hv, hne⟩ hgp)
    have := mem_union_of_sum_smul_eq_of_frozen fz y ha0 has hb0 hbs hfree hcol heq
    rw [hay] at this
    exact this

end Work.PL.Generic
