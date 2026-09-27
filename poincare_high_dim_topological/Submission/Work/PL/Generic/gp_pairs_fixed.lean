import Mathlib
import Submission.Work.PL.Defs
import Submission.Work.PL.Generic.Basic
import Submission.Work.PL.Generic.Hull
import Submission.Work.PL.Generic.domDim_join_step
import Submission.Work.PL.Generic.mem_hullOf
import Submission.Work.PL.Generic.eq_of_sum_smul_eq_of_affineIndependent

namespace Work.PL.Generic

open Set Metric

/-- Erasing a vertex `u ∈ σ` from the index set and re-adding its image gives back the image:
`(σ.erase u).image y ∪ {y u} = σ.image y`. -/
lemma image_erase_union_singleton {n : ℕ} {ι : Type*} [DecidableEq ι]
    (y : ι → PL.E n) {σ : Finset ι} {u : ι} (hu : u ∈ σ) :
    (σ.erase u).image y ∪ {y u} = σ.image y := by
  apply Finset.Subset.antisymm
  · intro z hz
    rw [Finset.mem_union] at hz
    rcases hz with hz | hz
    · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hz
      exact Finset.mem_image.2 ⟨v, (Finset.mem_erase.1 hv).2, rfl⟩
    · rw [Finset.mem_singleton] at hz
      exact Finset.mem_image.2 ⟨u, hu, hz.symm⟩
  · intro z hz
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hz
    rw [Finset.mem_union]
    by_cases hvu : v = u
    · subst hvu
      exact Or.inr (Finset.mem_singleton_self _)
    · exact Or.inl (Finset.mem_image.2 ⟨v, Finset.mem_erase.2 ⟨hvu, hv⟩, rfl⟩)

/-- An affinely independent family on `σ` has no point lying in the affine span of the remaining
points: in particular `y u ∉ affineSpan ℝ ((σ.erase u).image y)` for `u ∈ σ`
(here `((σ.erase u).image y : Finset (PL.E n))` coerces to the set `y '' ↑(σ.erase u)`). -/
lemma notMem_affineSpan_image_erase {n : ℕ} {ι : Type*} [DecidableEq ι]
    {y : ι → PL.E n} {σ : Finset ι} {u : ι}
    (hind : AffineIndependent ℝ (fun v : ↥σ => y v)) (hu : u ∈ σ) :
    y u ∉ (affineSpan ℝ (((σ.erase u).image y : Finset (PL.E n)) : Set (PL.E n)) :
      Set (PL.E n)) := by
  intro hmem
  rw [Finset.coe_image] at hmem
  have hset : y '' ((σ.erase u : Finset ι) : Set ι)
      = (fun v : ↥σ => y v) '' {v : ↥σ | (v : ι) ≠ u} := by
    ext z
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨⟨v, (Finset.mem_erase.1 hv).2⟩, (Finset.mem_erase.1 hv).1, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      exact ⟨v.1, Finset.mem_erase.2 ⟨hv, v.2⟩, rfl⟩
  rw [hset] at hmem
  exact (fun h => h rfl)
    ((AffineIndependent.mem_affineSpan_iff hind ⟨u, hu⟩ {v : ↥σ | (v : ι) ≠ u}).1 hmem)

/-- If `x` has a barycentric representation on the affinely independent family `y` on `σ` whose
`u`-th coefficient is strictly positive, then `x` does not lie in the hull of `y` over `σ.erase u`
(barycentric coordinates are unique). -/
lemma notMem_hullOf_erase_of_pos_weight {n : ℕ} {ι : Type*} [DecidableEq ι]
    {y : ι → PL.E n} {σ : Finset ι} {u : ι}
    (hind : AffineIndependent ℝ (fun v : ↥σ => y v))
    {x : PL.E n} {w : ι → ℝ} (_hw0 : ∀ v ∈ σ, 0 ≤ w v)
    (hw1 : ∑ v ∈ σ, w v = 1) (hw2 : ∑ v ∈ σ, w v • y v = x)
    (hu : u ∈ σ) (hpos : 0 < w u) : x ∉ hullOf y (σ.erase u) := by
  intro hx
  obtain ⟨w', hw'0, hw'1, hw'2⟩ := (mem_hullOf y (σ.erase u) x).1 hx
  have hsum : ∑ v ∈ σ, (if v ∈ σ.erase u then w' v else 0 : ℝ) = 1 := by
    rw [← Finset.sum_subset (Finset.erase_subset u σ) (fun v _ hv => by rw [ite_eq_right hv])]
    rw [Finset.sum_congr rfl (fun v hv => by rw [ite_eq_left hv]), hw'1]
  have hsmul : ∑ v ∈ σ, (if v ∈ σ.erase u then w' v else 0 : ℝ) • y v = x := by
    rw [← Finset.sum_subset (Finset.erase_subset u σ)
      (fun v _ hv => by rw [ite_eq_right hv, zero_smul])]
    rw [Finset.sum_congr rfl (fun v hv => by rw [ite_eq_left hv]), hw'2]
  have hwu : (if u ∈ σ.erase u then w' u else 0 : ℝ) = w u :=
    eq_of_sum_smul_eq_of_affineIndependent hind hsum hw1 (by rw [hsmul, hw2]) u hu
  have h0 : (if u ∈ σ.erase u then w' u else 0 : ℝ) = 0 := by
    rw [ite_eq_right (Finset.notMem_erase u σ)]
  rw [h0] at hwu
  exact absurd hwu.symm (ne_of_gt hpos)

/-- The dimension bound for one free vertex: for `u ∈ σ` free, the part of the simplex `hullOf y σ`
which uses `y u` with positive weight lies in the join step
`(simp ((σ.erase u).image y ∪ {y u}) \ simp ((σ.erase u).image y)) ∩ simp S`, whose dimension is
bounded by `|σ| + |S| - 2 - n`.  The hypotheses are exactly those of `domDim_join_step`, with `hy`
from `hind` and `hgen` from `hgpS` (applied to `T := σ.erase u`). -/
lemma domDim_erase_join {n : ℕ} {ι : Type*} [DecidableEq ι]
    (fz : Finset ι) (y : ι → PL.E n) (σ : Finset ι) (S : Finset (PL.E n))
    (hgpS : ∀ u, u ∉ fz → ∀ T : Finset ι, T ⊆ σ → u ∉ T →
      y u ∈ (affineSpan ℝ ((y '' (T : Set ι)) ∪ (S : Set (PL.E n))) : Set (PL.E n)) →
        affineSpan ℝ ((y '' (T : Set ι)) ∪ (S : Set (PL.E n))) = ⊤)
    (hind : AffineIndependent ℝ (fun v : ↥σ => y v))
    {u : ι} (huσ : u ∈ σ) (hufz : u ∉ fz) :
    PL.DomDim ((PL.simp ((σ.erase u).image y ∪ {y u}) \ PL.simp ((σ.erase u).image y)) ∩
        PL.simp S) ((σ.card : ℤ) + (S.card : ℤ) - 2 - (n : ℤ)) := by
  classical
  have hy : y u ∉ (affineSpan ℝ (((σ.erase u).image y : Finset (PL.E n)) : Set (PL.E n)) :
      Set (PL.E n)) := notMem_affineSpan_image_erase hind huσ
  have hgen : y u ∉ (affineSpan ℝ ((((σ.erase u).image y : Finset (PL.E n)) : Set (PL.E n)) ∪
        (S : Set (PL.E n))) : Set (PL.E n)) ∨
      affineSpan ℝ ((((σ.erase u).image y : Finset (PL.E n)) : Set (PL.E n)) ∪
        (S : Set (PL.E n))) = ⊤ := by
    by_cases h : y u ∈ (affineSpan ℝ ((((σ.erase u).image y : Finset (PL.E n)) : Set (PL.E n)) ∪
        (S : Set (PL.E n))) : Set (PL.E n))
    · refine Or.inr ?_
      have h' : y u ∈ (affineSpan ℝ ((y '' ((σ.erase u : Finset ι) : Set ι)) ∪
          (S : Set (PL.E n))) : Set (PL.E n)) := by
        simpa [Finset.coe_image] using h
      have hmain := hgpS u hufz (σ.erase u) (Finset.erase_subset u σ)
        (Finset.notMem_erase u σ) h'
      simpa [Finset.coe_image] using hmain
    · exact Or.inl h
  have hstep := domDim_join_step (s := (σ.erase u).image y) (σ := S) (y := y u) hy hgen
  refine PL.DomDim.mono_dim ?_ hstep
  rw [finrank_E]
  have hcard : (((σ.erase u).image y).card : ℤ) ≤ (σ.card : ℤ) - 1 := by
    have h1 : ((σ.erase u).image y).card ≤ (σ.erase u).card := Finset.card_image_le
    have h2 : (σ.erase u).card = σ.card - 1 := Finset.card_erase_of_mem huσ
    have h3 : 1 ≤ σ.card := Finset.card_pos.2 ⟨u, huσ⟩
    have h4 : (((σ.erase u).card : ℕ) : ℤ) = (σ.card : ℤ) - 1 := by
      rw [h2]
      omega
    have h5 : (((σ.erase u).image y).card : ℤ) ≤ ((σ.erase u).card : ℤ) := by
      exact_mod_cast h1
    omega
  omega

/-- The `Fixed` conjunct of `Work.PL.Generic.gp_pairs` for one pair and one fixed simplex `simp S`.
Proof: take `x ∈ hullOf y σ ∩ simp S`; if the barycentric coefficients of `x` on the affinely
independent `σ` (`hind`) all vanish on `σ ∖ fz`, then `x ∈ hullOf y (σ ∩ fz)`; otherwise pick a free
`u` with `a u > 0` and apply `domDim_join_step` with `s := (σ.erase u).image y` and `σ := S` (its `hy`
comes from `hind`, its `hgen` from `hgpS`), then union the finitely many pieces with `PL.DomDim.iUnion`. -/
theorem gp_pairs_fixed {n : ℕ} {ι : Type*} [DecidableEq ι]
    (fz : Finset ι) (y : ι → PL.E n) (σ : Finset ι) (S : Finset (PL.E n))
    (hgp : ∀ u, u ∉ fz → ∀ T : Finset ι, T ⊆ σ → u ∉ T →
      y u ∈ (affineSpan ℝ (y '' (T : Set ι)) : Set (PL.E n)) →
        affineSpan ℝ (y '' (T : Set ι)) = ⊤)
    (hgpS : ∀ u, u ∉ fz → ∀ T : Finset ι, T ⊆ σ → u ∉ T →
      y u ∈ (affineSpan ℝ ((y '' (T : Set ι)) ∪ (S : Set (PL.E n))) : Set (PL.E n)) →
        affineSpan ℝ ((y '' (T : Set ι)) ∪ (S : Set (PL.E n))) = ⊤)
    (hind : AffineIndependent ℝ (fun v : ↥σ => y v)) :
    ∃ D : Set (PL.E n), PL.DomDim D ((σ.card : ℤ) + (S.card : ℤ) - 2 - (n : ℤ)) ∧
      Work.PL.Generic.hullOf y σ ∩ PL.simp S ⊆ Work.PL.Generic.hullOf y (σ ∩ fz) ∪ D := by
  classical
  refine ⟨⋃ u ∈ σ \ fz,
      (PL.simp ((σ.erase u).image y ∪ {y u}) \ PL.simp ((σ.erase u).image y)) ∩ PL.simp S,
    ?_, ?_⟩
  · refine PL.DomDim.biUnion (u := σ \ fz)
      (A := fun u => (PL.simp ((σ.erase u).image y ∪ {y u}) \ PL.simp ((σ.erase u).image y)) ∩
        PL.simp S) ?_
    intro u hu
    exact domDim_erase_join fz y σ S hgpS hind (Finset.mem_sdiff.1 hu).1 (Finset.mem_sdiff.1 hu).2
  · intro x hx
    rcases hx with ⟨hxσ, hxS⟩
    by_cases hfz : x ∈ hullOf y (σ ∩ fz)
    · exact Or.inl hfz
    · refine Or.inr ?_
      obtain ⟨w, hw0, hw1, hw2⟩ := (mem_hullOf y σ x).1 hxσ
      have hfree : ∃ u ∈ σ, u ∉ fz ∧ 0 < w u := by
        by_contra hc
        have hzero : ∀ u ∈ σ, u ∉ fz → w u = 0 := by
          intro u huσ hufz
          by_contra hne
          exact hc ⟨u, huσ, hufz, lt_of_le_of_ne (hw0 u huσ) (Ne.symm hne)⟩
        have hzfz : ∀ v ∈ σ, v ∉ σ ∩ fz → w v = 0 := by
          intro v hv hv'
          exact hzero v hv (fun hvf => hv' (Finset.mem_inter.2 ⟨hv, hvf⟩))
        have hsum_fz : ∑ v ∈ σ ∩ fz, w v = 1 := by
          rw [Finset.sum_subset Finset.inter_subset_left hzfz, hw1]
        have hsmul_fz : ∑ v ∈ σ ∩ fz, w v • y v = x := by
          rw [Finset.sum_subset Finset.inter_subset_left
            (fun v hv hv' => by rw [hzfz v hv hv', zero_smul]), hw2]
        exact hfz ((mem_hullOf y (σ ∩ fz) x).2
          ⟨w, (fun v hv => hw0 v (Finset.mem_inter.1 hv).1), hsum_fz, hsmul_fz⟩)
      obtain ⟨u, huσ, hufz, hpos⟩ := hfree
      refine Set.mem_iUnion.2 ⟨u, Set.mem_iUnion.2
        ⟨Finset.mem_sdiff.2 ⟨huσ, hufz⟩, ?_⟩⟩
      refine ⟨⟨?_, ?_⟩, hxS⟩
      · rw [image_erase_union_singleton y huσ]
        simpa [hullOf_eq_simp] using hxσ
      · intro hxin
        exact notMem_hullOf_erase_of_pos_weight hind hw0 hw1 hw2 huσ hpos
          (by rw [hullOf_eq_simp]; exact hxin)

end Work.PL.Generic
