import Mathlib
import Submission.Work.HP.BCS.Defs
import Submission.Work.HP.BCS.CLAux

open MeasureTheory
open scoped Pointwise

namespace Work.HP.BCS

-- Lattice point counting from a boundary-layer bound.
-- Let `k ≥ 1` and let `Ψ : ℝ^k →ₗ[ℝ] ℝ^k` be injective, so that `Λ := Ψ '' ℤ^k` is a rank-`k`
-- lattice with half-open fundamental domain `F := Ψ '' [0,1)^k`, of volume `Ψ.normDet` and radius
-- `cellRad Ψ = ∑ i, ‖Ψ eᵢ‖`.  Let `K ⊆ ℝ^k` have finite volume and finite intersection with `Λ`,
-- let `R₀ ≥ cellRad Ψ` and suppose the `R₀`-boundary layer of `K` has volume `≤ M`.
-- Then `|#(Λ ∩ K) - vol K / Ψ.normDet| ≤ M / Ψ.normDet`.
--
-- ROUTE.  `F := Ψ '' [0,1)^k` is a half-open fundamental domain of `Λ`: the translates `s + F`,
-- `s ∈ Λ`, are pairwise disjoint with union `range Ψ ⊇ K` (use `Int.floor`/`Int.fract`
-- coordinatewise and transport by `Ψ`).  Hence with `N := #(Λ ∩ K)`:
--   * upper: `N * vol F = vol (⋃_{s ∈ Λ ∩ K} (s + F)) ≤ vol (K + B_{R₀})` because `F ⊆ B_{R₀}`
--     (`R₀ ≥ cellRad Ψ` uses `‖Ψ t‖ ≤ ∑ |tᵢ| ‖Ψ eᵢ‖` for `t` in the unit cube);
--   * lower: if `x ∈ erode K (B_{R₀}) ⊆ K` then `B_{R₀}(x) ⊆ K`; write `x = Ψ t` (`Ψ` surjective
--     onto its range, and `K ⊆ range Ψ`), put `c = ⌈t⌉` (`Int.ceil`, coordinatewise), so that
--     `t - c ∈ (-1,0]^k`, whence `x - Ψ c ∈ -F ⊆ B_{R₀}` and `Ψ c ∈ B_{R₀}(x) ⊆ K`; so
--     `x ∈ Ψ c + F` with `Ψ c ∈ Λ ∩ K`.  Thus `erode K (B_{R₀}) ⊆ ⋃_{s ∈ Λ ∩ K} (s + F)`.
-- Therefore `|N * vol F - vol K| ≤ vol(layer K R₀) ≤ M`, and `vol F = |det Ψ| = Ψ.normDet`
-- (`Measure.addHaar_image_linearMap` applied to the unit cube, whose volume is `1` since the
-- `MeasureSpace` instance on `ℝ^k` is the Haar measure attached to an orthonormal basis:
-- `Module.Basis.addHaar_parallelepiped`); `Ψ.normDet ≠ 0` by injectivity.
-- The resulting `C` is an absolute constant (indeed `C = 1` or `2` works).
theorem count_from_layer (k : ℕ) (hk : 1 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Ψ : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin k)),
      Function.Injective Ψ → ∀ (K : Set (EuclideanSpace ℝ (Fin k))) (R₀ M : ℝ),
      0 ≤ R₀ → 0 ≤ M → Work.HP.BCS.cellRad Ψ ≤ R₀ →
      (Work.HP.BCS.latImage Ψ ∩ K).Finite → MeasureTheory.volume K ≠ ⊤ →
      MeasureTheory.volume (Work.HP.BCS.layer K R₀) ≤ ENNReal.ofReal M →
      |(((Work.HP.BCS.latImage Ψ ∩ K).ncard : ℝ) - (MeasureTheory.volume K).toReal / Ψ.normDet)|
        ≤ C * M / Ψ.normDet := by
  refine ⟨1, one_pos, ?_⟩
  intro Ψ hΨ K R₀ M hR₀ hM hcell hfin hKne hlayer
  classical
  have hcellpos : 0 < cellRad Ψ := cellRad_pos_aux hk Ψ hΨ
  have hRpos : 0 < R₀ := lt_of_lt_of_le hcellpos hcell
  have hd : 0 < Ψ.normDet := normDet_pos_aux Ψ hΨ
  have hdne : Ψ.normDet ≠ 0 := ne_of_gt hd
  set S : Finset (EuclideanSpace ℝ (Fin k)) := hfin.toFinset with hSdef
  have hSmem : ∀ x : EuclideanSpace ℝ (Fin k), x ∈ S ↔ x ∈ latImage Ψ ∧ x ∈ K := by
    intro x
    rw [hSdef, Set.Finite.mem_toFinset, Set.mem_inter_iff]
  have hSsub : ∀ s ∈ S, s ∈ latImage Ψ := fun s hs => ((hSmem s).mp hs).1
  have hSK : ∀ s ∈ S, s ∈ K := fun s hs => ((hSmem s).mp hs).2
  -- measure of the (finite, disjoint) union of translates
  have h1 : (MeasureTheory.volume (⋃ s ∈ S, ({s} + fund Ψ))).toReal
      = (S.card : ℝ) * Ψ.normDet := volume_biUnion_fund_aux Ψ hΨ S hSsub
  -- the union sits in the thickening
  have hUT : MeasureTheory.volume (⋃ s ∈ S, ({s} + fund Ψ))
      ≤ MeasureTheory.volume (Metric.thickening R₀ K) := by
    apply measure_mono
    intro x hx
    obtain ⟨s, hs⟩ := Set.mem_iUnion.mp hx
    obtain ⟨hsS, hxs⟩ := Set.mem_iUnion.mp hs
    obtain ⟨a, ha, f, hf, haf⟩ := Set.mem_add.mp hxs
    rw [Set.mem_singleton_iff] at ha
    rw [ha] at haf
    obtain ⟨t, ht, rfl⟩ := hf
    refine Metric.mem_thickening_iff.mpr ⟨s, hSK s hsS, ?_⟩
    have hlt : ‖Ψ t‖ < R₀ := lt_of_lt_of_le (norm_lt_cellRad_aux hk Ψ hΨ ht) hcell
    rw [← haf, dist_eq_norm, add_sub_cancel_left]
    exact hlt
  -- the erosion sits in the union
  have hEU : MeasureTheory.volume (erode K (Metric.ball (0 : EuclideanSpace ℝ (Fin k)) R₀))
      ≤ MeasureTheory.volume (⋃ s ∈ S, ({s} + fund Ψ)) := by
    apply measure_mono
    intro x hx
    obtain ⟨c, hc, -⟩ := fund_cover_aux Ψ hΨ x
    obtain ⟨t, ht, htx⟩ := hc
    have hval : Ψ (toEk c) - x = -Ψ t := by rw [htx]; abel
    have hb : Ψ (toEk c) - x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin k)) R₀ := by
      rw [Metric.mem_ball, dist_eq_norm, sub_zero, hval, norm_neg]
      exact lt_of_lt_of_le (norm_lt_cellRad_aux hk Ψ hΨ ht) hcell
    have hmemK : Ψ (toEk c) ∈ K := by
      have h := hx (Ψ (toEk c) - x) hb
      rwa [show x + (Ψ (toEk c) - x) = Ψ (toEk c) by abel] at h
    have hS : Ψ (toEk c) ∈ S := (hSmem _).mpr ⟨⟨toEk c, ⟨c, rfl⟩, rfl⟩, hmemK⟩
    refine Set.mem_iUnion.mpr ⟨Ψ (toEk c), Set.mem_iUnion.mpr ⟨hS, ?_⟩⟩
    exact Set.mem_add.mpr ⟨Ψ (toEk c), rfl, x - Ψ (toEk c), ⟨t, ht, htx⟩, by abel⟩
  have hsplit : MeasureTheory.volume (Metric.thickening R₀ K)
      = MeasureTheory.volume (erode K (Metric.ball (0 : EuclideanSpace ℝ (Fin k)) R₀))
        + MeasureTheory.volume (layer K R₀) := thickening_erode_layer_aux (K := K) hRpos
  have hTK : MeasureTheory.volume K ≤ MeasureTheory.volume (Metric.thickening R₀ K) := by
    apply measure_mono
    intro x hx
    exact Metric.mem_thickening_iff.mpr ⟨x, hx, by simpa using hRpos⟩
  have hTL : MeasureTheory.volume (Metric.thickening R₀ K)
      ≤ MeasureTheory.volume K + MeasureTheory.volume (layer K R₀) := by
    refine le_trans (measure_mono ?_) (measure_union_le (K : Set _) (layer K R₀))
    intro x hx
    by_cases hxK : x ∈ K
    · exact Or.inl hxK
    · refine Or.inr ?_
      rw [layer, add_ball_eq_thickening]
      exact ⟨hx, fun hero => hxK (by simpa using erode_subset_self hRpos hero)⟩
  have hLne : MeasureTheory.volume (layer K R₀) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hlayer
  have hTne : MeasureTheory.volume (Metric.thickening R₀ K) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hKne, hLne⟩) hTL
  have hEne : MeasureTheory.volume (erode K (Metric.ball (0 : EuclideanSpace ℝ (Fin k)) R₀))
      ≠ ⊤ := ne_top_of_le_ne_top hTne (by rw [hsplit]; exact le_self_add)
  have hUne : MeasureTheory.volume (⋃ s ∈ S, ({s} + fund Ψ)) ≠ ⊤ :=
    ne_top_of_le_ne_top hTne hUT
  have h2 : (MeasureTheory.volume (⋃ s ∈ S, ({s} + fund Ψ))).toReal
      ≤ (MeasureTheory.volume (Metric.thickening R₀ K)).toReal := ENNReal.toReal_mono hTne hUT
  have h3 : (MeasureTheory.volume (erode K (Metric.ball (0 : EuclideanSpace ℝ (Fin k)) R₀))).toReal
      ≤ (MeasureTheory.volume (⋃ s ∈ S, ({s} + fund Ψ))).toReal := ENNReal.toReal_mono hUne hEU
  have h4 : (MeasureTheory.volume (Metric.thickening R₀ K)).toReal
      = (MeasureTheory.volume (erode K (Metric.ball (0 : EuclideanSpace ℝ (Fin k)) R₀))).toReal
        + (MeasureTheory.volume (layer K R₀)).toReal := by
    rw [hsplit, ENNReal.toReal_add hEne hLne]
  have h5 : (MeasureTheory.volume K).toReal
      ≤ (MeasureTheory.volume (Metric.thickening R₀ K)).toReal := ENNReal.toReal_mono hTne hTK
  have h6 : (MeasureTheory.volume (Metric.thickening R₀ K)).toReal
      ≤ (MeasureTheory.volume K).toReal + (MeasureTheory.volume (layer K R₀)).toReal := by
    rw [← ENNReal.toReal_add hKne hLne]
    exact ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hKne, hLne⟩) hTL
  have h7 : (MeasureTheory.volume (layer K R₀)).toReal ≤ M := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hlayer
    rwa [ENNReal.toReal_ofReal hM] at h
  have hmain : |(S.card : ℝ) * Ψ.normDet - (MeasureTheory.volume K).toReal| ≤ M := by
    have e1 : (S.card : ℝ) * Ψ.normDet - (MeasureTheory.volume K).toReal ≤ M := by
      linarith [h1, h2, h6, h7]
    have e2 : (MeasureTheory.volume K).toReal - (S.card : ℝ) * Ψ.normDet ≤ M := by
      linarith [h3, h4, h5, h7]
    rw [abs_sub_le_iff]
    exact ⟨e1, e2⟩
  have hcard : ((latImage Ψ ∩ K).ncard : ℝ) = (S.card : ℝ) := by
    rw [Set.ncard_eq_toFinset_card _ hfin, ← hSdef]
  rw [hcard]
  have hfinabs : |(S.card : ℝ) - (MeasureTheory.volume K).toReal / Ψ.normDet| * Ψ.normDet
      = |(S.card : ℝ) * Ψ.normDet - (MeasureTheory.volume K).toReal| := by
    have h1' : (S.card : ℝ) - (MeasureTheory.volume K).toReal / Ψ.normDet
        = ((S.card : ℝ) * Ψ.normDet - (MeasureTheory.volume K).toReal) / Ψ.normDet := by
      rw [eq_div_iff hdne, sub_mul, div_mul_cancel₀ _ hdne]
    rw [h1', abs_div, abs_of_pos hd, div_mul_cancel₀ _ hdne]
  rw [le_div_iff₀ hd, hfinabs]
  linarith [hmain]

end Work.HP.BCS
