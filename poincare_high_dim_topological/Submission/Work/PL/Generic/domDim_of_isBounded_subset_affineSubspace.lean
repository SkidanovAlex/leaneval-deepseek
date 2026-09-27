import Mathlib
import Submission.Work.PL.Defs
import Submission.Work.PL.Generic.Basic

namespace Work.PL.Generic

open Set Metric
open scoped Convex Pointwise

/-- A bounded subset of an affine subspace of dimension ≤ d is dominated by a single d-simplex.
Proof plan: if `F = ⊥` then `A = ∅`; otherwise pick `p ∈ F` and a basis `v₁…v_k` of `F.direction`
(`k = finrank ≤ d`), form the simplex `T = simp {p, p + λ v₁, …, p + λ v_k}` and note that for
`λ` large `T` contains `A` (use `Bornology.IsBounded` to bound `A` and the existence of a ball
around `p` inside `T` — e.g. scale the simplex spanned by an affine basis of `F` about its
centroid). Then `⟨{s}, …⟩` where `s` is the vertex set. -/
theorem domDim_of_isBounded_subset_affineSubspace {m : ℕ} {d : ℤ} {A : Set (PL.E m)}
    (hbd : Bornology.IsBounded A) {F : AffineSubspace ℝ (PL.E m)} (hAF : A ⊆ (F : Set (PL.E m)))
    (hd : (Module.finrank ℝ F.direction : ℤ) ≤ d) : PL.DomDim A d := by
  rcases (F : Set (PL.E m)).eq_empty_or_nonempty with hF | hne
  · -- `F` is empty, hence so is `A`.
    have hA : A = ∅ := Subset.antisymm (by rw [hF] at hAF; exact hAF) (Set.empty_subset _)
    rw [hA]
    exact PL.DomDim.empty d
  · obtain ⟨p, hp⟩ := hne
    -- An affine basis of the direction, whose convex hull is a simplex containing `0` in its
    -- interior (inside the direction subspace).
    obtain ⟨b, hb0, -⟩ := exists_mem_interior_convexHull_affineBasis
      (E := ↥(F.direction)) (x := 0) (s := Set.univ) Filter.univ_mem
    obtain ⟨ε, hεpos, hεsub⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hb0)
    -- A bound for `A` around `p`.
    obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_ball p).1 hbd
    set lam : ℝ := max 1 (r / ε + 1) with hlamdef
    have hlam1 : 1 ≤ lam := le_max_left _ _
    have hlampos : 0 < lam := lt_of_lt_of_le zero_lt_one hlam1
    have hrlam : r < lam * ε := by
      have h3 : r / ε < lam := lt_of_lt_of_le (lt_add_one _) (le_max_right _ _)
      calc r = r / ε * ε := by rw [div_mul_cancel₀ r hεpos.ne']
        _ < lam * ε := by nlinarith [hεpos]
    -- The homothety of ratio `lam` about `p`, restricted to the direction.
    set χ : ↥(F.direction) →ᵃ[ℝ] PL.E m :=
      (AffineMap.homothety p lam).comp
        ((AffineMap.const ℝ ↥(F.direction) p) +ᵥ (Submodule.subtype (F.direction)).toAffineMap)
      with hχdef
    have hχ : ∀ v, χ v = p +ᵥ lam • (v : PL.E m) := by
      intro v
      rw [hχdef, AffineMap.comp_apply, AffineMap.vadd_apply, AffineMap.const_apply,
        AffineMap.homothety_apply]
      simp [add_comm]
    -- The vertex set of the scaled simplex.
    set t : Finset (PL.E m) := Finset.univ.image (fun i => χ (b i)) with htdef
    have hcover : A ⊆ PL.simp t := by
      intro x hx
      have hxF : x ∈ (F : Set (PL.E m)) := hAF hx
      have hxr : dist x p < r := by
        have := hr hx
        rwa [mem_ball] at this
      -- The direction component of `x`, scaled down by `lam`, is inside the simplex.
      set w : ↥(F.direction) :=
        ⟨(1 / lam) • (x -ᵥ p), Submodule.smul_mem _ _ (AffineSubspace.vsub_mem_direction hxF hp)⟩
        with hwdef
      have hwnorm : ‖w‖ = (1 / lam) * dist x p := by
        rw [hwdef, ← Submodule.norm_coe, Submodule.coe_mk, norm_smul, Real.norm_eq_abs,
          abs_of_pos (one_div_pos.2 hlampos), dist_eq_norm_vsub]
      have hwball : w ∈ Metric.ball (0 : ↥(F.direction)) ε := by
        rw [mem_ball, dist_zero_right, hwnorm]
        calc (1 / lam) * dist x p < (1 / lam) * (lam * ε) :=
              mul_lt_mul_of_pos_left (by linarith) (one_div_pos.2 hlampos)
          _ = ε := by rw [one_div, ← mul_assoc, inv_mul_cancel₀ hlampos.ne', one_mul]
      have hwT : w ∈ convexHull ℝ (Set.range b) := hεsub hwball
      have hxχ : χ w = x := by
        rw [hχ w, hwdef, Submodule.coe_mk, one_div, smul_inv_smul₀ hlampos.ne']
        simp
      have hmem : x ∈ χ '' convexHull ℝ (Set.range b) := ⟨w, hwT, hxχ⟩
      have hmem2 : x ∈ convexHull ℝ (Set.range fun i => χ (b i)) := by
        rw [AffineMap.image_convexHull, ← Set.range_comp] at hmem
        exact hmem
      have htcoe : (t : Set (PL.E m)) = Set.range (fun i => χ (b i)) := by
        rw [htdef, Finset.coe_image, Finset.coe_univ, Set.image_univ]
      rw [PL.simp, htcoe]
      exact hmem2
    refine ⟨{t}, ?_, ?_⟩
    · intro s hs
      rw [Finset.mem_singleton] at hs
      rw [hs]
      have h1 : t.card ≤ Module.finrank ℝ ↥(F.direction) + 1 := by
        rw [htdef]
        calc (Finset.univ.image (fun i => χ (b i))).card
            ≤ (Finset.univ : Finset (Fin (Module.finrank ℝ ↥(F.direction) + 1))).card :=
              Finset.card_image_le
          _ = Module.finrank ℝ ↥(F.direction) + 1 := by simp
      have h2 : (Module.finrank ℝ ↥(F.direction) : ℤ) ≤ d := hd
      omega
    · intro x hx
      rw [PL.mem_iUnion_simp]
      exact ⟨t, Finset.mem_singleton_self t, hcover hx⟩

end Work.PL.Generic
