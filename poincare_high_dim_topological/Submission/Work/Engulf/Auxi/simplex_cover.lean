import Mathlib
import Submission.Work.PL.Defs

open Set

namespace Work.Engulf.Aux

/-- **`simplex_cover`** (contract §8, E2 step 2): if a simplex `PL.simp s` whose vertex set is nonempty and affinely independent is covered by the simplices of a finite family `T` of subsets of `s`, then already `s ∈ T`.  Equivalently: a simplex is not the union of finitely many proper sub-simplices.  Used to prove `BadCard k` for the subdivided complex in `E2`: a face of the fine subdivision lying in the union of the "good" and "small" faces is one of them.  Suggested proof: take a strictly positive convex combination `x` of the vertices of `s`; `x ∈ PL.simp t` for some `t ∈ T`; uniqueness of affine coordinates (`AffineIndependent.affineCombination_eq_iff_eq`, or `Set.Finite.isCompact_convexHull`-style relative interior) forces `s = t`. -/
theorem simplex_cover {N : ℕ} (s : Finset (PL.E N)) (T : Finset (Finset (PL.E N)))
    (hne : s.Nonempty) (hind : AffineIndependent ℝ (fun v : ↥s => (v : PL.E N)))
    (hsub : ∀ t ∈ T, t ⊆ s) (hcov : PL.simp s ⊆ ⋃ t ∈ T, PL.simp t) : s ∈ T := by
  classical
  -- The weights of the "barycentre" `x` of the vertices of `s`: all strictly positive, summing to `1`.
  have hcardpos : 0 < s.card := Finset.card_pos.2 hne
  have hcardR : (s.card : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.pos_iff_ne_zero.1 hcardpos)
  have hcpos : 0 < (s.card : ℝ)⁻¹ := inv_pos.2 (by exact_mod_cast hcardpos)
  have hsum : ∑ i : ↥s, (s.card : ℝ)⁻¹ = 1 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
    exact mul_inv_cancel₀ hcardR
  set x : PL.E N := ∑ v : ↥s, (s.card : ℝ)⁻¹ • (v : PL.E N) with hxdef
  -- `x` lies in the simplex on `s`.
  have hx_mem : x ∈ PL.simp s := by
    rw [hxdef]
    change (∑ v : ↥s, (s.card : ℝ)⁻¹ • (v : PL.E N)) ∈ convexHull ℝ (↑s : Set (PL.E N))
    refine Convex.sum_mem (convex_convexHull ℝ (↑s : Set (PL.E N))) ?_ hsum ?_
    · intro i _
      exact le_of_lt hcpos
    · intro i _
      exact subset_convexHull ℝ _ i.2
  -- hence `x` lies in `PL.simp t` for some `t ∈ T`, with `t ⊆ s`.
  obtain ⟨t, htT, hxt⟩ := Set.mem_iUnion₂.1 (hcov hx_mem)
  have hts : t ⊆ s := hsub t htT
  -- the vertex map from `↥s` restricted to the indices in `t` has image exactly `t`.
  have himg : (fun v : ↥s => (v : PL.E N)) '' {v : ↥s | (v : PL.E N) ∈ t} = (↑t : Set (PL.E N)) := by
    ext y
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact hv
    · intro hy
      exact ⟨⟨y, hts hy⟩, hy, rfl⟩
  -- `x` is the affine combination of the vertices of `s` with all weights `1/|s|`.
  have haff : Finset.univ.affineCombination ℝ (fun v : ↥s => (v : PL.E N))
      (fun _ => (s.card : ℝ)⁻¹) = x := by
    rw [Finset.affineCombination_eq_linear_combination _ _ _ hsum, ← hxdef]
  have hxaff : x ∈ affineSpan ℝ (↑t : Set (PL.E N)) :=
    convexHull_subset_affineSpan (𝕜 := ℝ) (t : Set (PL.E N)) hxt
  have hxspan : Finset.univ.affineCombination ℝ (fun v : ↥s => (v : PL.E N))
        (fun _ => (s.card : ℝ)⁻¹) ∈
      affineSpan ℝ ((fun v : ↥s => (v : PL.E N)) '' {v : ↥s | (v : PL.E N) ∈ t}) := by
    rw [haff, himg]
    exact hxaff
  -- uniqueness of affine coordinates: a positive weight forces the corresponding vertex into `t`.
  have hzero : ∀ v : ↥s, (v : PL.E N) ∉ t → (s.card : ℝ)⁻¹ = 0 := by
    intro v hv
    exact hind.eq_zero_of_affineCombination_mem_affineSpan (fs := Finset.univ)
      (w := fun _ : ↥s => (s.card : ℝ)⁻¹) hsum hxspan (Finset.mem_univ v) hv
  have hst : s ⊆ t := by
    intro v hv
    by_contra hvt
    exact absurd (hzero ⟨v, hv⟩ hvt) (ne_of_gt hcpos)
  have hts' : t = s := Finset.Subset.antisymm hts hst
  rwa [hts'] at htT

end Work.Engulf.Aux
