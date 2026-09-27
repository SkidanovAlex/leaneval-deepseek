import Mathlib
import Submission.Work.PL.Defs
import Submission.Work.PL.Generic.Basic
import Submission.Work.PL.Generic.Hull

namespace Work.PL.Generic

open Set

/-- A point which is an affine combination (weights summing to `1`) of the vertices `y v`, `v ∈ T`,
lies in the affine span of the vertex set `y '' T`.  (`Finset.affineCombination` evaluated with
weights that sum to `1` is `∑ v, w v • y v`, `affineCombination_mem_affineSpan_image`.) -/
theorem sum_smul_mem_affineSpan_image {n : ℕ} {ι : Type*} (T : Finset ι) (y : ι → PL.E n)
    {w : ι → ℝ} (hw : ∑ v ∈ T, w v = 1) :
    ∑ v ∈ T, w v • y v ∈ (affineSpan ℝ (y '' (T : Set ι)) : Set (PL.E n)) := by
  rw [← Finset.affineCombination_eq_linear_combination T y w hw]
  exact affineCombination_mem_affineSpan_image hw (fun i hi hi' => absurd hi hi') y

/-- Affine dependence of a finite vertex family: if `∑_{v ∈ S} c v = 0`,
`∑_{v ∈ S} c v • y v = 0` and `c u ≠ 0` for some `u ∈ S`, then `y u` lies in the affine span of
the *remaining* vertices `y '' (S.erase u)`.

With `T := S.erase u`, `∑_{v ∈ T} c v = -c u` and `∑_{v ∈ T} c v • y v = -c u • y u`, so `y u` is
the affine combination `∑_{v ∈ T} (-(c v / c u)) • y v` of the vertices in `T`. -/
theorem mem_affineSpan_erase_of_sum_smul_eq_zero {n : ℕ} {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (y : ι → PL.E n) {c : ι → ℝ} {u : ι}
    (huS : u ∈ S) (hcu : c u ≠ 0)
    (hc : ∑ v ∈ S, c v = 0) (hcy : ∑ v ∈ S, c v • y v = 0) :
    y u ∈ (affineSpan ℝ (y '' ((S.erase u : Finset ι) : Set ι)) : Set (PL.E n)) := by
  set T : Finset ι := S.erase u with hT
  have hTsum : ∑ v ∈ T, c v = - c u := by
    rw [hT, Finset.sum_erase_eq_sub (f := c) huS, hc, zero_sub]
  have hTy : ∑ v ∈ T, c v • y v = - (c u • y u) := by
    have h := Finset.sum_erase_add S (fun v => c v • y v) huS
    rw [← hT, hcy] at h
    exact eq_neg_of_add_eq_zero_left h
  set w : ι → ℝ := fun v => -(c v / c u) with hw
  have hwsum : ∑ v ∈ T, w v = 1 := by
    have h1 : ∑ v ∈ T, w v = -((∑ v ∈ T, c v) / c u) := by
      simp only [hw]
      rw [Finset.sum_neg_distrib, ← Finset.sum_div]
    rw [h1, hTsum, neg_div, div_self hcu, neg_neg]
  have hwy : ∑ v ∈ T, w v • y v = y u := by
    have hcoef : ∀ v, w v = -(c u)⁻¹ * c v := by
      intro v; simp only [hw, div_eq_mul_inv]; ring
    calc ∑ v ∈ T, w v • y v
        = ∑ v ∈ T, (-(c u)⁻¹ * c v) • y v :=
          Finset.sum_congr rfl (fun v _ => by rw [hcoef v])
      _ = ∑ v ∈ T, -(c u)⁻¹ • (c v • y v) :=
          Finset.sum_congr rfl (fun v _ => by rw [mul_smul])
      _ = -(c u)⁻¹ • ∑ v ∈ T, c v • y v := by rw [Finset.smul_sum]
      _ = -(c u)⁻¹ • (-(c u • y u)) := by rw [hTy]
      _ = y u := by
            rw [smul_neg, ← mul_smul]
            have h1 : -(c u)⁻¹ * c u = -1 := by
              rw [neg_mul, inv_mul_cancel₀ hcu]
            rw [h1, neg_one_smul, neg_neg]
  have hmem := sum_smul_mem_affineSpan_image T y hwsum
  rw [hwy] at hmem
  exact hmem

/-- Case A of the pointwise argument for `Work.PL.Generic.gp_pairs`: if a barycentric relation
`∑_{σ₁} a • y = ∑_{σ₂} b • y` has a nonzero "net" coefficient at a free index `u`, then the vertex
set already spans everything.  Proof: with `c v := (if v ∈ σ₁ then a v else 0) - (if v ∈ σ₂ then b v else 0)`
one has `∑ c v • y v = 0` and `∑ c v = 0`; `c u ≠ 0` expresses `y u` as an affine combination of
`y '' T` with `T = (σ₁ ∪ σ₂).erase u`, so `hgen` gives `affineSpan ℝ (y '' T) = ⊤`, and `T ⊆ σ₁ ∪ σ₂`. -/
theorem affineSpan_eq_top_of_sum_smul_ne {n : ℕ} {ι : Type*} [DecidableEq ι]
    (fz : Finset ι) (y : ι → PL.E n) {σ₁ σ₂ : Finset ι} {a b : ι → ℝ}
    (has : ∑ v ∈ σ₁, a v = 1) (hbs : ∑ v ∈ σ₂, b v = 1)
    (heq : ∑ v ∈ σ₁, a v • y v = ∑ v ∈ σ₂, b v • y v)
    (hA : ∃ u, u ∉ fz ∧ (if u ∈ σ₁ then a u else 0) ≠ (if u ∈ σ₂ then b u else 0))
    (hgen : ∀ u, u ∉ fz → ∀ T : Finset ι, T ⊆ σ₁ ∪ σ₂ → u ∉ T →
      y u ∈ (affineSpan ℝ (y '' (T : Set ι)) : Set (PL.E n)) →
        affineSpan ℝ (y '' (T : Set ι)) = ⊤) :
    affineSpan ℝ (y '' ((σ₁ ∪ σ₂ : Finset ι) : Set ι)) = ⊤ := by
  classical
  obtain ⟨u, hufz, hcu_ne⟩ := hA
  set c : ι → ℝ := fun v => (if v ∈ σ₁ then a v else 0) - (if v ∈ σ₂ then b v else 0) with hcdef
  -- the two "one-sided" masses are both `1`
  have hsu₁ : ∑ v ∈ σ₁ ∪ σ₂, (if v ∈ σ₁ then a v else 0) = 1 := by
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr Finset.subset_union_left, has]
  have hsu₂ : ∑ v ∈ σ₁ ∪ σ₂, (if v ∈ σ₂ then b v else 0) = 1 := by
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr Finset.subset_union_right, hbs]
  -- `∑ c v = 0`
  have hc : ∑ v ∈ σ₁ ∪ σ₂, c v = 0 := by
    have h : ∑ v ∈ σ₁ ∪ σ₂, c v
        = ∑ v ∈ σ₁ ∪ σ₂, ((if v ∈ σ₁ then a v else 0) - (if v ∈ σ₂ then b v else 0)) :=
      Finset.sum_congr rfl (fun v _ => by simp only [hcdef])
    rw [h, Finset.sum_sub_distrib, hsu₁, hsu₂, sub_self]
  -- the two "one-sided" vector sums
  have hsuy₁ : ∑ v ∈ σ₁ ∪ σ₂, (if v ∈ σ₁ then a v • y v else 0) = ∑ v ∈ σ₁, a v • y v := by
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr Finset.subset_union_left]
  have hsuy₂ : ∑ v ∈ σ₁ ∪ σ₂, (if v ∈ σ₂ then b v • y v else 0) = ∑ v ∈ σ₂, b v • y v := by
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr Finset.subset_union_right]
  -- `∑ c v • y v = 0`
  have hcy : ∑ v ∈ σ₁ ∪ σ₂, c v • y v = 0 := by
    have hnum : ∀ v, c v • y v
        = (if v ∈ σ₁ then a v • y v else 0) - (if v ∈ σ₂ then b v • y v else 0) := by
      intro v
      by_cases h1 : v ∈ σ₁ <;> by_cases h2 : v ∈ σ₂ <;>
        simp [hcdef, h1, h2, sub_smul]
    rw [Finset.sum_congr rfl (fun v _ => hnum v), Finset.sum_sub_distrib,
      hsuy₁, hsuy₂, heq, sub_self]
  have hcu : c u ≠ 0 := by
    simp only [hcdef]
    exact sub_ne_zero.mpr hcu_ne
  have huS : u ∈ σ₁ ∪ σ₂ := by
    by_contra h
    have h1 : u ∉ σ₁ := fun hu => h (Finset.mem_union_left _ hu)
    have h2 : u ∉ σ₂ := fun hu => h (Finset.mem_union_right _ hu)
    refine hcu ?_
    simp [hcdef, h1, h2]
  have hmu := mem_affineSpan_erase_of_sum_smul_eq_zero (σ₁ ∪ σ₂) y huS hcu hc hcy
  have htop := hgen u hufz ((σ₁ ∪ σ₂).erase u) (Finset.erase_subset u (σ₁ ∪ σ₂))
    (Finset.notMem_erase u (σ₁ ∪ σ₂)) hmu
  have hmono : affineSpan ℝ (y '' (((σ₁ ∪ σ₂).erase u : Finset ι) : Set ι))
      ≤ affineSpan ℝ (y '' ((σ₁ ∪ σ₂ : Finset ι) : Set ι)) :=
    affineSpan_mono ℝ (Set.image_mono (Finset.coe_subset.mpr (Finset.erase_subset u (σ₁ ∪ σ₂))))
  exact le_antisymm le_top (htop ▸ hmono)

end Work.PL.Generic
