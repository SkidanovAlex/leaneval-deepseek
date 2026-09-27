import Mathlib
import Submission.Work.Engulf.E4P.Defs
import Submission.Work.Engulf.E4alt.exists_pieces
import Submission.Work.Engulf.Auxi.exists_indep_cover

/-!
# `Work.Engulf.E4P.exists_pieces_list`

The list of chart simplices that the E4c piece loop of `piecesEngulfG` attaches one at a time.

`E4alt.exists_pieces` produces, for the *given* closed `(q-2)`-dominated `J` inside a compact convex
`F`, a finite family `S` of vertex sets with at most `q` vertices covering the region over `J` and
lying in the `δ`-neighbourhood of that region.  Choosing `δ` small enough that this neighbourhood
lands in the closed `11/16` cube (possible because the region over `J` is a subset of the *open*
`9/16` cube by `hsmall`, and `T.symm` is Lipschitz), and replacing every `s ∈ S` by the finitely
many affinely independent nonempty subsets of `s` (Carathéodory's theorem, `convexHull_eq_union`:
a simplex is the union of the simplices on its affinely independent subsets, `Auxi.exists_indep_cover`)
gives the required list of pieces: non-empty, affinely independent, of cardinality at most `q`, each
inside the closed `11/16` cube, and covering the region over `J`.
-/

open Set Metric PL

namespace Work.Engulf.E4P

set_option synthInstance.maxHeartbeats 400000

/-- The inverse of an affine equivalence `E n ≃ᵃ[ℝ] Pr (n-q-1) q` is Lipschitz, with the operator
norm of the linear part of the inverse as a constant.  (Both spaces are finite dimensional, so every
linear map is continuous.) -/
lemma exists_dist_symm_le {n q : ℕ} (T : PL.E n ≃ᵃ[ℝ] Work.Engulf.Pr (n - q - 1) q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u v : Work.Engulf.Pr (n - q - 1) q,
      dist (T.symm u) (T.symm v) ≤ C * dist u v := by
  let L : Work.Engulf.Pr (n - q - 1) q →ₗ[ℝ] PL.E n := T.symm.linear.toLinearMap
  let Φ : Work.Engulf.Pr (n - q - 1) q →L[ℝ] PL.E n := LinearMap.toContinuousLinearMap L
  refine ⟨‖Φ‖, norm_nonneg _, ?_⟩
  intro u v
  have h1 : T.symm u - T.symm v = Φ (u - v) := by
    have h := AffineMap.linearMap_vsub (T.symm : Work.Engulf.Pr (n - q - 1) q →ᵃ[ℝ] PL.E n) u v
    rw [vsub_eq_sub, vsub_eq_sub] at h
    exact h.symm
  rw [dist_eq_norm, dist_eq_norm, h1]
  exact ContinuousLinearMap.le_opNorm Φ (u - v)

theorem exists_pieces_list {n q : ℕ} (hn : q + 1 ≤ n)
    (T : PL.E n ≃ᵃ[ℝ] Work.Engulf.Pr (n - q - 1) q)
    {F : Set (PL.E q)} (hFc : IsCompact F) (hFconv : Convex ℝ F)
    {γ₀ γ₁ : PL.E q → ℝ} (hγ₀ : Continuous γ₀) (hγ₁ : Continuous γ₁)
    (hle : ∀ z ∈ F, γ₀ z ≤ γ₁ z)
    {J : Set (PL.E q)} (hJF : J ⊆ F) (hJd : PL.DomDim J ((q : ℤ) - 2)) (hJc : IsClosed J)
    (hsmall : ∀ z ∈ J, ∀ t ∈ Set.Icc (γ₀ z) (γ₁ z),
      T.symm ((0 : PL.E (n - q - 1)), z, t) ∈ PL.openCube (n := n) (9 / 16 : ℝ)) :
    ∃ pieces : List (Finset (PL.E n)),
      Work.Engulf.E4P.PiecesOk (q := q) pieces ∧
      Work.Engulf.E4P.CoversRegion T γ₀ γ₁ J pieces := by
  classical
  obtain ⟨C, hC0, hClip⟩ := exists_dist_symm_le T
  -- `δ` is small enough that `C * δ ≤ 1/16`, so that the `δ`-neighbourhood of the region over `J`
  -- lands in the closed `10/16` cube, hence in the closed `11/16` cube.
  set δ : ℝ := (1 / 16) / (C + 1) with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]; exact div_pos (by norm_num) (by linarith)
  have hCδ : C * δ ≤ 1 / 16 := by
    rw [hδdef, div_eq_mul_inv]
    rw [show C * ((1 / 16) * (C + 1)⁻¹) = (C / (C + 1)) * (1 / 16) by
      rw [div_eq_mul_inv]; ring]
    have h4 : C / (C + 1) ≤ 1 := (div_le_one (by linarith : (0:ℝ) < C + 1)).mpr (by linarith)
    exact mul_le_of_le_one_left (by norm_num) h4
  -- The family of vertex sets produced by `E4alt.exists_pieces`.
  obtain ⟨J', S, hJ'd, hJ'c, hJsub, hScard, hSclose, hScov⟩ :=
    Work.Engulf.E4alt.exists_pieces hn T F hFc hFconv γ₀ γ₁ hγ₀ hγ₁ hle J hJd hJF δ hδpos
  -- Every simplex of `S` lies in the closed `11/16` cube.
  have hcube : ∀ s ∈ S, PL.simp s ⊆ PL.closedCube (n := n) (11 / 16 : ℝ) := by
    intro s hs w hw
    obtain ⟨z₀, hz₀, z, hz, t, hTw, t₀, ht₀, hdist, htdist⟩ := hSclose s hs w hw
    have hw' : w = T.symm ((0 : PL.E (n - q - 1)), z, t) := by
      rw [← hTw]; exact (AffineEquiv.symm_apply_apply T w).symm
    have hY : T.symm ((0 : PL.E (n - q - 1)), z₀, t₀) ∈ PL.openCube (n := n) (9 / 16 : ℝ) :=
      hsmall z₀ hz₀ t₀ ht₀
    have hdu : dist ((0 : PL.E (n - q - 1)), z, t) ((0 : PL.E (n - q - 1)), z₀, t₀) < δ := by
      rw [Prod.dist_eq, Prod.dist_eq, dist_self, Real.dist_eq,
        max_eq_right (le_max_of_le_left dist_nonneg)]
      exact max_lt hdist htdist
    have hnorm : ‖w - T.symm ((0 : PL.E (n - q - 1)), z₀, t₀)‖ ≤ 1 / 16 := by
      rw [hw']
      calc ‖T.symm ((0 : PL.E (n - q - 1)), z, t)
              - T.symm ((0 : PL.E (n - q - 1)), z₀, t₀)‖
          ≤ C * dist ((0 : PL.E (n - q - 1)), z, t) ((0 : PL.E (n - q - 1)), z₀, t₀) := hClip _ _
        _ ≤ C * δ := mul_le_mul_of_nonneg_left (le_of_lt hdu) hC0
        _ ≤ 1 / 16 := hCδ
    intro i
    have hYi : |(T.symm ((0 : PL.E (n - q - 1)), z₀, t₀)) i| < 9 / 16 := hY i
    have h1 : |w i - (T.symm ((0 : PL.E (n - q - 1)), z₀, t₀)) i|
        ≤ ‖w - T.symm ((0 : PL.E (n - q - 1)), z₀, t₀)‖ := by
      have h := PiLp.norm_apply_le (p := 2) (w - T.symm ((0 : PL.E (n - q - 1)), z₀, t₀)) i
      rw [Real.norm_eq_abs] at h
      simpa using h
    calc |w i| = |(w i - (T.symm ((0 : PL.E (n - q - 1)), z₀, t₀)) i)
            + (T.symm ((0 : PL.E (n - q - 1)), z₀, t₀)) i| := by ring_nf
      _ ≤ |w i - (T.symm ((0 : PL.E (n - q - 1)), z₀, t₀)) i|
            + |(T.symm ((0 : PL.E (n - q - 1)), z₀, t₀)) i| := abs_add_le _ _
      _ ≤ 1 / 16 + 9 / 16 := by linarith [h1, hnorm, le_of_lt hYi]
      _ ≤ 11 / 16 := by norm_num
  -- Refine every `s ∈ S` into its affinely independent non-empty subsets.
  let piecesF : Finset (Finset (PL.E n)) := S.biUnion fun s =>
    s.powerset.filter (fun t => t.Nonempty ∧ AffineIndependent ℝ (fun v : ↥t => (v : PL.E n)))
  refine ⟨piecesF.toList, ?_, ?_⟩
  · intro s hsmem
    rw [Finset.mem_toList] at hsmem
    rw [Finset.mem_biUnion] at hsmem
    obtain ⟨s₀, hs₀, hsmem'⟩ := hsmem
    rw [Finset.mem_filter] at hsmem'
    obtain ⟨hspow, hne, haff⟩ := hsmem'
    rw [Finset.mem_powerset] at hspow
    exact ⟨hne, haff, le_trans (Finset.card_le_card hspow) (hScard s₀ hs₀),
      fun w hw => hcube s₀ hs₀ (Work.Engulf.simp_mono hspow hw)⟩
  · intro z hz t ht
    obtain ⟨s, hs, hpt⟩ := Set.mem_iUnion₂.mp (hScov z (hJsub hz) t ht)
    obtain ⟨t', ht's, hne', haff', hpt'⟩ := Work.Engulf.Auxi.exists_indep_cover s hpt
    refine Set.mem_iUnion.mpr ⟨t', Set.mem_iUnion.mpr ⟨?_, hpt'⟩⟩
    rw [Finset.mem_toList, Finset.mem_biUnion]
    exact ⟨s, hs, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr ht's, hne', haff'⟩⟩

end Work.Engulf.E4P
