import Mathlib
import Submission.Work.Engulf.Defs
import Submission.Work.Engulf.Tools
import Submission.Work.Engulf.Basic
import Submission.Work.Engulf.E4Aux.piece_cover
import Submission.Work.Engulf.E4alt.exists_fine_cover_domDim

/-!
# `Work.Engulf.E4alt.exists_pieces` (E4c)

Given the affine equivalence `T : E n ≃ᵃ ℝ Pr (n-q-1) q` of the prism decomposition `G2`, a
`(q-2)`-dominated set `J₀` inside a compact convex `F`, and continuous `γ₀ ≤ γ₁` on `F`, produce a
closed `(q-2)`-dominated `J ⊇ J₀` together with a finite family `S` of vertex sets with at most
`q` vertices which *covers the region over `J`* and each of whose simplices lies in the
`δ`-neighbourhood of the region over `J₀`.

Proof: refine the `DomDim` cover of `J₀` (`exists_fine_cover_domDim`) to simplices of diameter
`< η` each lying in the `η`-ball about a point `z_p ∈ J₀`; take `J` to be their union (so `J` is
closed and `(q-2)`-dominated and `J ⊆ B(J₀,η)`).  For each refined simplex `p` the pieces are the
images under `piAff T` of the prism triangulation (`prism_cover`) of `simp p × [γ₀ z_p - h, γ₁ z_p + 2h]`
with `h = δ/4`; a point of `simp p` has `γ`-values within `h` of those at `z_p` (uniform continuity
on a compact ball), which gives both the covering of the region over `J` (the tile is long enough)
and the `δ`-closeness to the region over `J₀` (the tile is short enough).
-/

open Set Metric PL

namespace Work.Engulf.E4alt
theorem exists_pieces {n q : ℕ} (hq : q + 1 ≤ n)
    (T : PL.E n ≃ᵃ[ℝ] Work.Engulf.Pr (n - q - 1) q)
    (F : Set (PL.E q)) (hFc : IsCompact F) (hFconv : Convex ℝ F)
    (γ₀ γ₁ : PL.E q → ℝ) (hγ₀ : Continuous γ₀) (hγ₁ : Continuous γ₁)
    (hle : ∀ z ∈ F, γ₀ z ≤ γ₁ z)
    (J₀ : Set (PL.E q)) (hJ₀ : PL.DomDim J₀ (q - 2)) (hJ₀F : J₀ ⊆ F)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ (J : Set (PL.E q)) (S : Finset (Finset (PL.E n))),
      PL.DomDim J (q - 2) ∧ IsClosed J ∧ J₀ ⊆ J ∧
      (∀ s ∈ S, s.card ≤ q) ∧
      (∀ s ∈ S, ∀ w ∈ PL.simp s, ∃ z₀ ∈ J₀, ∃ z ∈ J, ∃ t : ℝ,
        T w = ((0 : PL.E (n - q - 1)), z, t) ∧
        ∃ t₀ ∈ Set.Icc (γ₀ z₀) (γ₁ z₀), dist z z₀ < δ ∧ |t - t₀| < δ) ∧
      (∀ z ∈ J, ∀ t ∈ Set.Icc (γ₀ z) (γ₁ z),
        T.symm ((0 : PL.E (n - q - 1)), z, t) ∈ ⋃ s ∈ S, PL.simp s) := by
  classical
  have hJ₀' : PL.DomDim J₀ (q - 2) := hJ₀
  set h : ℝ := δ / 4 with hhdef
  have hhpos : 0 < h := by rw [hhdef]; linarith
  obtain ⟨Sc, hScard, hScov⟩ := hJ₀
  have hCcompact : IsCompact (⋃ s ∈ Sc, PL.simp s) :=
    Sc.finite_toSet.isCompact_biUnion (fun s _ => isCompact_simp s)
  obtain ⟨R₀, hR₀⟩ : ∃ R : ℝ, (⋃ s ∈ Sc, PL.simp s) ⊆ Metric.closedBall (0 : PL.E q) R :=
    (Metric.isBounded_iff_subset_closedBall (0 : PL.E q)).mp hCcompact.isBounded
  set Kc : Set (PL.E q) := Metric.closedBall (0 : PL.E q) (R₀ + 1) with hKcdef
  have hKccompact : IsCompact Kc := isCompact_closedBall _ _
  obtain ⟨η₀, hη₀pos, hη₀⟩ :
      ∃ η' > 0, ∀ x ∈ Kc, ∀ y ∈ Kc, dist x y < η' → dist (γ₀ x) (γ₀ y) < h :=
    (Metric.uniformContinuousOn_iff.mp
      (hKccompact.uniformContinuousOn_of_continuous hγ₀.continuousOn)) h hhpos
  obtain ⟨η₁, hη₁pos, hη₁⟩ :
      ∃ η' > 0, ∀ x ∈ Kc, ∀ y ∈ Kc, dist x y < η' → dist (γ₁ x) (γ₁ y) < h :=
    (Metric.uniformContinuousOn_iff.mp
      (hKccompact.uniformContinuousOn_of_continuous hγ₁.continuousOn)) h hhpos
  set η : ℝ := min (min η₀ η₁) (min (δ / 2) 1) with hηdef
  have hηpos : 0 < η := by
    rw [hηdef]
    exact lt_min (lt_min hη₀pos hη₁pos) (lt_min (by linarith) zero_lt_one)
  have hη_η₀ : η ≤ η₀ := le_trans (min_le_left _ _) (min_le_left _ _)
  have hη_η₁ : η ≤ η₁ := le_trans (min_le_left _ _) (min_le_right _ _)
  have hη_δ : η ≤ δ / 2 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hη_1 : η ≤ 1 := le_trans (min_le_right _ _) (min_le_right _ _)
  obtain ⟨P, hPcard, hPcov, hPball⟩ := exists_fine_cover_domDim hJ₀' η hηpos
  choose zp hzpmem hzpball using hPball
  have hzpF : ∀ (p : Finset (PL.E q)) (hp : p ∈ P), zp p hp ∈ F := fun p hp => hJ₀F (hzpmem p hp)
  have hle_zp : ∀ (p : Finset (PL.E q)) (hp : p ∈ P), γ₀ (zp p hp) ≤ γ₁ (zp p hp) := fun p hp => hle _ (hzpF p hp)
  have hzpnorm : ∀ (p : Finset (PL.E q)) (hp : p ∈ P), ‖zp p hp‖ ≤ R₀ := by
    intro p hp
    have h1 : zp p hp ∈ Metric.closedBall (0 : PL.E q) R₀ := hR₀ (hScov (hzpmem p hp))
    rwa [Metric.mem_closedBall, dist_zero_right] at h1
  have hzpK : ∀ (p : Finset (PL.E q)) (hp : p ∈ P), zp p hp ∈ Kc := by
    intro p hp
    rw [hKcdef, Metric.mem_closedBall, dist_zero_right]
    linarith [hzpnorm p hp]
  have hzK : ∀ (p : Finset (PL.E q)) (hp : p ∈ P) (y : PL.E q), y ∈ PL.simp p → y ∈ Kc := by
    intro p hp y hy
    have h1 : dist y (zp p hp) < 1 := lt_of_lt_of_le (hzpball p hp y hy) hη_1
    have h3 : ‖y - zp p hp‖ < 1 := by rwa [dist_eq_norm] at h1
    rw [hKcdef, Metric.mem_closedBall, dist_zero_right]
    calc ‖y‖ = ‖(y - zp p hp) + zp p hp‖ := by rw [sub_add_cancel]
      _ ≤ ‖y - zp p hp‖ + ‖zp p hp‖ := norm_add_le _ _
      _ ≤ R₀ + 1 := by linarith [hzpnorm p hp]
  have hosc₀ : ∀ (p : Finset (PL.E q)) (hp : p ∈ P) (y : PL.E q) (hy : y ∈ PL.simp p), dist (γ₀ y) (γ₀ (zp p hp)) < h :=
    fun p hp y hy => hη₀ y (hzK p hp y hy) (zp p hp) (hzpK p hp)
      (lt_of_lt_of_le (hzpball p hp y hy) hη_η₀)
  have hosc₁ : ∀ (p : Finset (PL.E q)) (hp : p ∈ P) (y : PL.E q) (hy : y ∈ PL.simp p), dist (γ₁ y) (γ₁ (zp p hp)) < h :=
    fun p hp y hy => hη₁ y (hzK p hp y hy) (zp p hp) (hzpK p hp)
      (lt_of_lt_of_le (hzpball p hp y hy) hη_η₁)
  let Φ : PL.E q × ℝ →ᵃ[ℝ] PL.E n := Work.Engulf.E4Aux.piAff T
  let lo : (p : Finset (PL.E q)) → p ∈ P → ℝ := fun p hp => γ₀ (zp p hp) - h
  let hi : (p : Finset (PL.E q)) → p ∈ P → ℝ := fun p hp => γ₁ (zp p hp) + 2 * h
  have hlohi : ∀ (p : Finset (PL.E q)) (hp : p ∈ P), lo p hp ≤ hi p hp := by
    intro p hp; have := hle_zp p hp; simp only [lo, hi]; linarith
  let Fam : {p // p ∈ P} → Finset (Finset (PL.E n)) := fun p =>
    ((Work.Geo.Prism.Convex.prismFinset p.1 (lo p.1 p.2) (hi p.1 p.2)).powerset.filter
      (fun U => U.card ≤ p.1.card + 1)).image (fun U => U.image Φ)
  let S : Finset (Finset (PL.E n)) := P.attach.biUnion Fam
  refine ⟨⋃ p ∈ P, PL.simp p, S, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨P, hPcard, Subset.rfl⟩
  · exact P.finite_toSet.isClosed_biUnion (fun p _ => (isCompact_simp p).isClosed)
  · exact hPcov
  · intro s hs
    rw [show S = P.attach.biUnion Fam from rfl, Finset.mem_biUnion] at hs
    obtain ⟨p, hp, hs⟩ := hs
    simp only [Fam, Finset.mem_image] at hs
    obtain ⟨U, hU, rfl⟩ := hs
    rw [Finset.mem_filter] at hU
    have h1 : (U.image Φ).card ≤ U.card := Finset.card_image_le
    have h3 : p.1.card + 1 ≤ q := by
      have hh : (p.1.card : ℤ) + 1 ≤ (q : ℤ) := by
        have := hPcard p.1 p.2; omega
      exact_mod_cast hh
    omega
  · intro s hs w hw
    rw [show S = P.attach.biUnion Fam from rfl, Finset.mem_biUnion] at hs
    obtain ⟨p, hp, hs⟩ := hs
    simp only [Fam, Finset.mem_image] at hs
    obtain ⟨U, hU, rfl⟩ := hs
    rw [Finset.mem_filter] at hU
    have hUsub : U ⊆ Work.Geo.Prism.Convex.prismFinset p.1 (lo p.1 p.2) (hi p.1 p.2) :=
      Finset.mem_powerset.mp hU.1
    have hw' : w ∈ Φ '' convexHull ℝ (U : Set (PL.E q × ℝ)) := by
      have hsimp : PL.simp (U.image Φ) = Φ '' convexHull ℝ (U : Set (PL.E q × ℝ)) := by
        rw [PL.simp, Finset.coe_image, ← AffineMap.image_convexHull]
      rw [hsimp] at hw; exact hw
    obtain ⟨u, hu, hwu⟩ := hw'
    obtain ⟨z, t⟩ := u
    have hmem : (z, t) ∈ convexHull ℝ (↑p.1 : Set (PL.E q)) ×ˢ
        Set.Icc (lo p.1 p.2) (hi p.1 p.2) := by
      rw [← Work.Geo.Prism.Convex.convexHull_prismFinset (p.1) (hlohi p.1 p.2)]
      exact convexHull_mono (Finset.coe_subset.mpr hUsub) hu
    obtain ⟨huz, hut⟩ := hmem
    rw [Set.mem_Icc] at hut
    simp only [lo, hi] at hut
    have hzJ : z ∈ ⋃ p ∈ P, PL.simp p := Set.mem_iUnion₂.mpr ⟨p.1, p.2, huz⟩
    have heq : T w = ((0 : PL.E (n - q - 1)), z, t) := by
      rw [← hwu]
      show T (Work.Engulf.E4Aux.piAff T (z, t)) = ((0 : PL.E (n - q - 1)), z, t)
      rw [Work.Engulf.E4Aux.piAff_apply, AffineEquiv.apply_symm_apply]
    have hdist : dist z (zp p.1 p.2) < δ := by
      have h1 := hzpball p.1 p.2 z huz
      linarith [hη_δ]
    have ht₀ : ∃ t₀ ∈ Set.Icc (γ₀ (zp p.1 p.2)) (γ₁ (zp p.1 p.2)), |t - t₀| < δ := by
      have hzp_le : γ₀ (zp p.1 p.2) ≤ γ₁ (zp p.1 p.2) := hle_zp p.1 p.2
      rcases le_or_gt t (γ₀ (zp p.1 p.2)) with h1 | h1
      · refine ⟨γ₀ (zp p.1 p.2), ⟨le_rfl, hzp_le⟩, ?_⟩
        rw [abs_of_nonpos (by linarith)]; linarith [hut.1]
      · rcases le_or_gt (γ₁ (zp p.1 p.2)) t with h2 | h2
        · refine ⟨γ₁ (zp p.1 p.2), ⟨hzp_le, le_rfl⟩, ?_⟩
          rw [abs_of_nonneg (by linarith)]; linarith [hut.2]
        · exact ⟨t, ⟨le_of_lt h1, le_of_lt h2⟩, by rw [sub_self, abs_zero]; exact hδ⟩
    obtain ⟨t₀, ht₀mem, ht₀val⟩ := ht₀
    exact ⟨zp p.1 p.2, hzpmem p.1 p.2, z, hzJ, t, heq, t₀, ht₀mem, hdist, ht₀val⟩
  · intro z hz t ht
    rw [Set.mem_iUnion₂] at hz
    obtain ⟨p, hp, hzp⟩ := hz
    rw [Set.mem_Icc] at ht
    have hcov := Work.Engulf.E4Aux.prism_cover p (hlohi p hp)
    have hmem : (z, t) ∈ convexHull ℝ (↑p : Set (PL.E q)) ×ˢ Set.Icc (lo p hp) (hi p hp) := by
      refine ⟨hzp, ?_⟩
      rw [Set.mem_Icc]
      constructor
      · have h1 := hosc₀ p hp z hzp
        have h2 : γ₀ (zp p hp) - h < γ₀ z := by
          have := abs_lt.mp (by rwa [Real.dist_eq] at h1)
          linarith [this.1]
        simp only [lo]
        linarith [ht.1]
      · have h1 := hosc₁ p hp z hzp
        have h2 : γ₁ z < γ₁ (zp p hp) + h := by
          have := abs_lt.mp (by rwa [Real.dist_eq] at h1)
          linarith [this.2]
        simp only [hi]
        linarith [ht.2]
    obtain ⟨U, hUS, hUt⟩ := Set.mem_iUnion₂.mp (hcov hmem)
    have hUmem : U ∈ (Work.Geo.Prism.Convex.prismFinset p (lo p hp) (hi p hp)).powerset.filter
        (fun U => U.card ≤ p.card + 1) := by simpa using hUS
    obtain ⟨hUpow, hUcard⟩ := Finset.mem_filter.mp hUmem
    refine Set.mem_iUnion₂.mpr ⟨U.image Φ, ?_, ?_⟩
    · rw [show S = P.attach.biUnion Fam from rfl, Finset.mem_biUnion]
      refine ⟨⟨p, hp⟩, Finset.mem_attach P _, ?_⟩
      simp only [Fam, Finset.mem_image]
      exact ⟨U, Finset.mem_filter.mpr ⟨hUpow, hUcard⟩, rfl⟩
    · show Work.Engulf.E4Aux.piAff T (z, t) ∈ PL.simp (U.image Φ)
      rw [PL.simp, Finset.coe_image, ← AffineMap.image_convexHull]
      exact ⟨(z, t), hUt, rfl⟩

end Work.Engulf.E4alt
