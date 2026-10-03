import Mathlib
import Submission.Work.Pert.MaxDom

/-!
# `Work.Pert.pert2v2.EfFloorDiffV2.Prelim` — helpers for the floor-extension differentiability

Two elementary facts used by `EfFloorDiffV2`:

* `mem_nhds_image_of_deriv_ne_zero`: the image `Φ '' Q` of an open set under a holomorphic map
  with nowhere-vanishing derivative is a neighbourhood of the image of each of its points (local
  open mapping / inverse function theorem);
* `seedP_add_one_of_re_Ico`: the *window* form of the level-one structure `hlvl`: for a base point
  `u` whose real part lies in `[0,1)` (i.e. a canonical `⌊Re⌋`-representative) with `y ≤ Im u` and
  `u + 1` in the gate image, the seed value shifts by `1`.

These are the two inputs of the periodicity *germ* lemma `seedP_germ_add_one`.
-/

namespace Work.Pert.pert2v2.EfFloorDiffV2

open Complex Set Filter
open scoped Topology

noncomputable section

variable {Φm Φp : ℂ → ℂ} {Q : Set ℂ} {y : ℝ}

/-- **The gate image is a neighbourhood of each of its points.**  If `Q` is open, `Φ` is holomorphic
on `Q` and `deriv Φ ζ ≠ 0` at `ζ ∈ Q`, then `Φ '' Q ∈ 𝓝 (Φ ζ)`. -/
theorem mem_nhds_image_of_deriv_ne_zero {Φ : ℂ → ℂ} {Q : Set ℂ} (hQ : IsOpen Q)
    (hΦ : DifferentiableOn ℂ Φ Q) {ζ : ℂ} (hζ : ζ ∈ Q) (hder : deriv Φ ζ ≠ 0) :
    Φ '' Q ∈ 𝓝 (Φ ζ) := by
  have hana : AnalyticAt ℂ Φ ζ := hΦ.analyticAt (hQ.mem_nhds hζ)
  have hmap : Filter.map Φ (𝓝 ζ) = 𝓝 (Φ ζ) := hana.hasStrictDerivAt.map_nhds_eq hder
  rw [← hmap, Filter.mem_map]
  exact Filter.mem_of_superset (hQ.mem_nhds hζ) (fun x hx => ⟨x, hx, rfl⟩)

/-- **The window form of the level-one structure.**  If `u` has real part in `[0,1)` (so that
`u - ⌊Re u⌋ = u`), `y ≤ Im u` and `u + 1` lies in the gate image, then the *seed* values
(`Work.Pert.seedP Φp Φm Q = Φp ∘ invOn Φm Q`) shift by `1`. -/
theorem seedP_add_one_of_re_Ico {u : ℂ}
    (hlvl : ∀ w : ℂ, y ≤ w.im → w - (((Int.floor w.re : ℤ)) : ℂ) + 1 ∈ Φm '' Q →
      Φp (Work.Pert.invOn Φm Q (w - (((Int.floor w.re : ℤ)) : ℂ) + 1))
        = Φp (Work.Pert.invOn Φm Q (w - (((Int.floor w.re : ℤ)) : ℂ))) + 1)
    (him : y ≤ u.im) (hre : u.re ∈ Set.Ico 0 1) (hu1 : u + 1 ∈ Φm '' Q) :
    Work.Pert.seedP Φp Φm Q (u + 1) = Work.Pert.seedP Φp Φm Q u + 1 := by
  have hfloor : (⌊u.re⌋ : ℤ) = 0 := Int.floor_eq_zero_iff.mpr hre
  have hprem : u - (((Int.floor u.re : ℤ)) : ℂ) + 1 ∈ Φm '' Q := by
    rw [hfloor]; simpa using hu1
  have hmain := hlvl u him hprem
  rw [hfloor] at hmain
  simpa [Work.Pert.seedP] using hmain

/-- **A shift into the open window.**  If `Re u ∈ [0,1)` then for every `δ > 0` there is `τ` with
`‖τ‖ < δ`, `Re (u + τ) ∈ (0,1)` and `Im (u + τ) > Im u`.  This is the point at which the level-one
hypothesis bites (used to produce a non-empty set of points where the two branches of the
`⌊Re⌋`-extension agree). -/
theorem exists_shift_mem_window {u : ℂ} (hre : u.re ∈ Set.Ico 0 1) {δ : ℝ} (hδ : 0 < δ) :
    ∃ τ : ℂ, ‖τ‖ < δ ∧ (u + τ).re ∈ Set.Ioo 0 1 ∧ u.im < (u + τ).im := by
  set ρ : ℝ := min (δ / 4) ((1 - u.re) / 2) with hρ
  set η : ℝ := δ / 4 with hη
  have hρpos : 0 < ρ := lt_min (by linarith) (by linarith [hre.2])
  have hηpos : 0 < η := by rw [hη]; linarith
  have hρδ : ρ ≤ δ / 4 := min_le_left _ _
  have hρ1 : ρ < 1 - u.re := by
    have h := min_le_right (δ / 4) ((1 - u.re) / 2)
    have : (1 - u.re) / 2 < 1 - u.re := by linarith [hre.2]
    linarith
  refine ⟨(ρ : ℂ) + (η : ℂ) * Complex.I, ?_, ?_, ?_⟩
  · have h1 : ‖((ρ : ℝ) : ℂ)‖ = ρ := by simp [abs_of_pos hρpos]
    have h2 : ‖((η : ℝ) : ℂ) * Complex.I‖ = η := by
      rw [norm_mul, Complex.norm_I, mul_one]
      simp [abs_of_pos hηpos]
    calc ‖((ρ : ℝ) : ℂ) + ((η : ℝ) : ℂ) * Complex.I‖
        ≤ ‖((ρ : ℝ) : ℂ)‖ + ‖((η : ℝ) : ℂ) * Complex.I‖ := norm_add_le _ _
      _ = ρ + η := by rw [h1, h2]
      _ < δ := by rw [hη]; linarith
  · have hre' : (u + ((ρ : ℂ) + (η : ℂ) * Complex.I)).re = u.re + ρ := by simp
    rw [hre']
    exact ⟨by linarith [hre.1], by linarith⟩
  · have him' : (u + ((ρ : ℂ) + (η : ℂ) * Complex.I)).im = u.im + η := by simp
    rw [him']
    linarith

end

end Work.Pert.pert2v2.EfFloorDiffV2
