import Mathlib
import Submission.Work.Engulf.Tools
import Submission.Work.Engulf.Defs
import Submission.Work.PL.Defs
import Submission.Work.Geo.Prism.Convex.prism_convex_piece
import Submission.Work.PL.Subdiv.DomDim

namespace Work.Engulf.E4Aux

open Set Metric

/-- The affine map `(z,t) ↦ T.symm (0, z, t)`: the inclusion of the "base × height" plane
`{y = 0}` of the prism into `E n`, followed by the inverse of the affine equivalence `T`
furnished by `G2`. -/
noncomputable def piAff {n q : ℕ} (T : PL.E n ≃ᵃ[ℝ] Work.Engulf.Pr (n - q - 1) q) :
    (PL.E q × ℝ) →ᵃ[ℝ] PL.E n :=
  (T.symm : Work.Engulf.Pr (n - q - 1) q →ᵃ[ℝ] PL.E n).comp
    (AffineMap.prod (AffineMap.const ℝ (PL.E q × ℝ) (0 : PL.E (n - q - 1)))
      (AffineMap.id ℝ (PL.E q × ℝ)))

theorem piAff_apply {n q : ℕ} (T : PL.E n ≃ᵃ[ℝ] Work.Engulf.Pr (n - q - 1) q)
    (z : PL.E q) (t : ℝ) :
    piAff T (z, t) = T.symm ((0 : PL.E (n - q - 1)), z, t) := rfl

/-- **The prism over one simplex and one interval is covered by small simplices.**  For a
finite vertex set `s ⊆ E q` and reals `lo ≤ hi`, the box `conv(s) × [lo,hi]` is covered by the
convex hulls of the subsets `U` of `prismFinset s lo hi = {(v,lo),(v,hi) | v ∈ s}` with
`U.card ≤ s.card + 1` (Carathéodory inside the affine span of the `s.card + 1` points
`prismU s v₀ lo hi`). -/
theorem prism_cover {q : ℕ} (s : Finset (PL.E q)) {lo hi : ℝ} (hle : lo ≤ hi) :
    (convexHull ℝ (s : Set (PL.E q)) ×ˢ Set.Icc lo hi) ⊆
      ⋃ U ∈ (Work.Geo.Prism.Convex.prismFinset s lo hi).powerset.filter
        (fun U => U.card ≤ s.card + 1), convexHull ℝ (U : Set (PL.E q × ℝ)) := by
  intro p hp
  rcases Finset.eq_empty_or_nonempty s with h | hsne
  · rw [h] at hp
    simp only [Finset.coe_empty, convexHull_empty, Set.empty_prod,
      Set.mem_empty_iff_false] at hp
  · obtain ⟨v₀, hv₀⟩ := hsne
    have hmem : p ∈ convexHull ℝ
        (Work.Geo.Prism.Convex.prismFinset s lo hi : Set (PL.E q × ℝ)) := by
      rw [Work.Geo.Prism.Convex.convexHull_prismFinset s hle]
      exact hp
    have hUcard : (Work.Geo.Prism.Convex.prismU s v₀ lo hi).card ≤ s.card + 1 := by
      rw [Work.Geo.Prism.Convex.prismU]
      calc (insert (v₀, hi) (s.image (fun v => (v, lo)))).card
          ≤ (s.image (fun v => (v, lo))).card + 1 := Finset.card_insert_le _ _
        _ ≤ s.card + 1 := Nat.add_le_add_right Finset.card_image_le 1
    exact Work.Geo.Prism.Convex.cover_of_subset_affineSpan _ _ (s.card + 1)
      (Work.Geo.Prism.Convex.prismFinset_subset_affineSpan s hv₀ lo hi) hUcard hmem

/-- **The pieces cover the region over `J` (`E4c`)**.  Let `T : E n ≃ᵃ ℝ Pr (n-q-1) q` be the affine equivalence of G2, `J ⊆ F ⊆ E q` a `(q-2)`-dominated set (the projection of the exceptional set of the bad-set lemma), and `γ₀ ≤ γ₁` the floor/top functions of the prism, squeezed between `lo` and `hi`.  Then the part of the prism lying over `J` — which is `(q-1)`-dimensional — is covered by finitely many simplices of `E n` with at most `q` vertices, i.e. is a "bad set of card ≤ q" for the recursive `B q`.  (Proof: `PL.DomDim J (q-2)` gives a finite cover of `J` by simplices `simp P`, `P.card ≤ q-1`; the box `simp P × [lo,hi]` is the product of a simplex and an interval, whose triangulation has `P.card + 1 ≤ q` vertices per simplex; pull back by `T.symm`.) -/
theorem piece_cover {n q : ℕ} (hq : q + 1 ≤ n)
    (T : PL.E n ≃ᵃ[ℝ] Work.Engulf.Pr (n - q - 1) q)
    (F J : Set (PL.E q)) (hJF : J ⊆ F) (hJ : PL.DomDim J (q - 2))
    (γ₀ γ₁ : PL.E q → ℝ) (lo hi : ℝ)
    (hγ₀ : ∀ z ∈ F, lo ≤ γ₀ z) (hγ₁ : ∀ z ∈ F, γ₁ z ≤ hi) :
    ∃ S : Finset (Finset (PL.E n)), (∀ s ∈ S, s.card ≤ q) ∧
      (∀ z ∈ J, ∀ t ∈ Set.Icc (γ₀ z) (γ₁ z),
        T.symm ((0 : PL.E (n - q - 1)), z, t) ∈ ⋃ s ∈ S, PL.simp s) := by
  classical
  by_cases hle : lo ≤ hi
  · obtain ⟨Sc, hScard, hScov⟩ := hJ
    let Φ : (PL.E q × ℝ) →ᵃ[ℝ] PL.E n := piAff T
    refine ⟨Sc.biUnion (fun s =>
        ((Work.Geo.Prism.Convex.prismFinset s lo hi).powerset.filter
          (fun U => U.card ≤ s.card + 1)).image (fun U => U.image Φ)), ?_, ?_⟩
    · intro U' hU'
      rw [Finset.mem_biUnion] at hU'
      obtain ⟨s, hsS, hU'⟩ := hU'
      rw [Finset.mem_image] at hU'
      obtain ⟨U, hU, rfl⟩ := hU'
      rw [Finset.mem_filter] at hU
      have hsle : s.card + 1 ≤ q := by
        have hs := hScard s hsS
        have hcast : ((s.card + 1 : ℕ) : ℤ) ≤ (q : ℤ) := by
          push_cast
          linarith
        exact_mod_cast hcast
      calc (U.image Φ).card ≤ U.card := Finset.card_image_le
        _ ≤ s.card + 1 := hU.2
        _ ≤ q := hsle
    · intro z hz t ht
      rw [Set.mem_Icc] at ht
      obtain ⟨ht1, ht2⟩ := ht
      have hzF : z ∈ F := hJF hz
      obtain ⟨s, hsS, hzs⟩ := Set.mem_iUnion₂.mp (hScov hz)
      have htIcc : t ∈ Set.Icc lo hi :=
        ⟨le_trans (hγ₀ z hzF) ht1, le_trans ht2 (hγ₁ z hzF)⟩
      have hp : (z, t) ∈ convexHull ℝ (s : Set (PL.E q)) ×ˢ Set.Icc lo hi := ⟨hzs, htIcc⟩
      have hcov := prism_cover s hle hp
      simp only [Set.mem_iUnion] at hcov
      obtain ⟨U, hUmem, hzU⟩ := hcov
      refine Set.mem_iUnion₂.mpr ⟨U.image Φ, ?_, ?_⟩
      · rw [Finset.mem_biUnion]
        exact ⟨s, hsS, Finset.mem_image.mpr ⟨U, hUmem, rfl⟩⟩
      · show Φ (z, t) ∈ PL.simp (U.image Φ)
        have h1 : Φ (z, t) ∈ convexHull ℝ (Φ '' (U : Set (PL.E q × ℝ))) := by
          rw [← AffineMap.image_convexHull]
          exact ⟨(z, t), hzU, rfl⟩
        have h2 : PL.simp (U.image Φ) = convexHull ℝ (Φ '' (U : Set (PL.E q × ℝ))) := by
          rw [PL.simp, Finset.coe_image]
        rw [h2]; exact h1
  · refine ⟨∅, by simp, ?_⟩
    intro z hz t ht
    rw [Set.mem_Icc] at ht
    obtain ⟨ht1, ht2⟩ := ht
    have hzF : z ∈ F := hJF hz
    exact absurd (le_trans (le_trans (hγ₀ z hzF) (le_trans ht1 ht2)) (hγ₁ z hzF)) hle

end Work.Engulf.E4Aux
