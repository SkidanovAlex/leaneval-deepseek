import Mathlib
import Submission.Work.Drive.Mono.FiberModel.Defs
import Submission.Work.Drive.Mono.FiberModel.height_basic
import Submission.Work.Drive.Mono.FiberModel.fibreCoord
import Submission.Work.Drive.Mono.fibreMax_continuous
import Submission.Work.Drive.Final.Trough.fibre_model

namespace Work.Drive.Mono.WindowCase

open LeanEval.KnotTheory.PardonDistortion Set

noncomputable section

/-- The closed box of the sweep is the closed box of the trough model. -/
theorem ClBox_eq_cbox {s : ℝ} (hs : 0 < s) (c : R3) (σ : Equiv.Perm (Fin 3)) :
    Work.Drive.Mono.FiberModel.ClBox s c σ = Work.Drive.Final.Trough.cbox s c σ := by
  rw [Work.Drive.Mono.FiberModel.ClBox, Work.Drive.Mono.closure_PBox_eq hs c σ]
  rfl

/-- The shadow of the closed box is the shadow of the trough model. -/
theorem boxShadow_eq_shadow {s : ℝ} (hs : 0 < s) (c : R3) (σ : Equiv.Perm (Fin 3))
    (v : R3) (ℓ : R3 →L[ℝ] ℝ) :
    Work.Drive.Mono.FiberModel.boxShadow s c σ v ℓ
      = Work.Drive.Final.Trough.shadow s c σ v ℓ := by
  have hfun : Work.Drive.Mono.FiberModel.levPair v ℓ = Work.Drive.Final.Trough.pair v ℓ := by
    funext y
    rw [Work.Drive.Final.Trough.pair_apply]
    rfl
  rw [Work.Drive.Mono.FiberModel.boxShadow, Work.Drive.Mono.FiberModel.shadow,
    Work.Drive.Final.Trough.shadow, ClBox_eq_cbox hs c σ, hfun]

/-- The fibre of the closed box over a plane point, in the `pair` language of the trough model. -/
theorem fibre_eq_pair {s : ℝ} (hs : 0 < s) (c : R3) (σ : Equiv.Perm (Fin 3))
    (v : R3) (ℓ : R3 →L[ℝ] ℝ) (X : ℝ × ℝ) :
    Work.Drive.Mono.FiberModel.fibre v ℓ s c σ X
      = {y : R3 | y ∈ Work.Drive.Final.Trough.cbox s c σ ∧
          Work.Drive.Final.Trough.pair v ℓ y = X} := by
  ext y
  simp only [Work.Drive.Mono.FiberModel.fibre, Set.mem_ofPred_eq,
    ClBox_eq_cbox hs c σ, Work.Drive.Final.Trough.pair_apply,
    Work.Drive.Mono.FiberModel.levPair]

/-- The fibre model of the closed box: a fibre coordinate, the fibre as an interval, the
regularity of the two heights, and non-degeneracy of the fibres over the interior of the shadow. -/
theorem tls_fibre_model
    (s : ℝ) (hs : 0 < s) (c : EuclideanSpace ℝ (Fin 3)) (σ : Equiv.Perm (Fin 3)) (h : ℝ)
    (v : EuclideanSpace ℝ (Fin 3))
    (ℓ : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ) (hh : 0 < h) (hℓv : ℓ v = 0) (hℓne : ℓ ≠ 0)
    (hv : v ≠ 0) :
    ∃ ζ : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ,
      Work.Drive.Mono.FiberModel.HasTrivKernel v ℓ ζ ∧
      (∀ X ∈ Work.Drive.Mono.FiberModel.boxShadow s c σ v ℓ,
        ζ '' Work.Drive.Mono.FiberModel.fibre v ℓ s c σ X
          = Set.Icc (Work.Drive.Mono.FiberModel.fMin ζ v ℓ s c σ X)
                    (Work.Drive.Mono.FiberModel.fMax ζ v ℓ s c σ X)) ∧
      (∀ X ∈ interior (Work.Drive.Mono.FiberModel.boxShadow s c σ v ℓ),
        Work.Drive.Mono.FiberModel.fMin ζ v ℓ s c σ X
          < Work.Drive.Mono.FiberModel.fMax ζ v ℓ s c σ X) ∧
      ContinuousOn (Work.Drive.Mono.FiberModel.fMax ζ v ℓ s c σ)
        (Work.Drive.Mono.FiberModel.boxShadow s c σ v ℓ) ∧
      ContinuousOn (Work.Drive.Mono.FiberModel.fMin ζ v ℓ s c σ)
        (Work.Drive.Mono.FiberModel.boxShadow s c σ v ℓ) ∧
      ConcaveOn ℝ (Work.Drive.Mono.FiberModel.boxShadow s c σ v ℓ)
        (Work.Drive.Mono.FiberModel.fMax ζ v ℓ s c σ) ∧
      ConvexOn ℝ (Work.Drive.Mono.FiberModel.boxShadow s c σ v ℓ)
        (Work.Drive.Mono.FiberModel.fMin ζ v ℓ s c σ) := by
  classical
  obtain ⟨ζ₀, hζ₀⟩ := Work.Drive.Mono.FiberModel.exists_fibreCoord hv hℓv hℓne
  have hζ₀pair : ∀ y : R3, Work.Drive.Final.Trough.pair v ℓ y = 0 → ζ₀ y = 0 → y = 0 := by
    intro y hy hzy
    rw [Work.Drive.Final.Trough.pair_apply] at hy
    exact hζ₀ y (by simpa using congrArg Prod.fst hy)
      (by simpa using congrArg Prod.snd hy) hzy
  have hfd0 : Work.Drive.Final.Trough.pair v ℓ (Work.Drive.Final.Trough.fibreDir v ℓ) = 0 :=
    Work.Drive.Final.Trough.pair_fibreDir hv hℓv hℓne
  have hfdne : Work.Drive.Final.Trough.fibreDir v ℓ ≠ 0 :=
    Work.Drive.Final.Trough.fibreDir_ne_zero hv hℓv hℓne
  have hκ : ζ₀ (Work.Drive.Final.Trough.fibreDir v ℓ) ≠ 0 :=
    fun hc => hfdne (hζ₀pair _ hfd0 hc)
  let ζ : R3 →L[ℝ] ℝ := (ζ₀ (Work.Drive.Final.Trough.fibreDir v ℓ))⁻¹ • ζ₀
  let g : ℝ × ℝ → ℝ := fun X => ζ (Work.Drive.Final.Trough.sectionL v ℓ X)
  have hζeq : ∀ y : R3, ζ y = (ζ₀ (Work.Drive.Final.Trough.fibreDir v ℓ))⁻¹ * ζ₀ y := by
    intro y
    simp only [ζ, smul_apply, smul_eq_mul]
  have hζfd : ζ (Work.Drive.Final.Trough.fibreDir v ℓ) = 1 := by
    rw [hζeq]
    exact inv_mul_cancel₀ hκ
  have hg_add : ∀ (a b : ℝ) (X Y : ℝ × ℝ),
      g (a • X + b • Y) = a * g X + b * g Y := by
    intro a b X Y
    simp only [g, map_add, map_smul, smul_eq_mul]
  have hkerζ : Work.Drive.Mono.FiberModel.HasTrivKernel v ℓ ζ := by
    intro y hy1 hy2 hzy
    have hpy : Work.Drive.Final.Trough.pair v ℓ y = 0 := by
      rw [Work.Drive.Final.Trough.pair_apply]
      exact Prod.ext hy1 hy2
    rw [hζeq] at hzy
    exact hζ₀pair y hpy ((mul_eq_zero.mp hzy).resolve_left (inv_ne_zero hκ))
  have hfib_img : ∀ X ∈ Work.Drive.Mono.FiberModel.boxShadow s c σ v ℓ,
      ζ '' Work.Drive.Mono.FiberModel.fibre v ℓ s c σ X
        = Set.Icc (g X + Work.Drive.Final.Trough.htl s c σ v ℓ X)
            (g X + Work.Drive.Final.Trough.hth s c σ v ℓ X) := by
    intro X hX
    have hXsh : X ∈ Work.Drive.Final.Trough.shadow s c σ v ℓ := by
      simpa [boxShadow_eq_shadow hs c σ v ℓ] using hX
    ext p
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [fibre_eq_pair hs c σ v ℓ X] at hy
      obtain ⟨hycbox, hypair⟩ := hy
      obtain ⟨t, ht⟩ := Work.Drive.Final.Trough.exists_fibre_coord hv hℓv hℓne y
      have hmem : Work.Drive.Final.Trough.sectionL v ℓ X + t • Work.Drive.Final.Trough.fibreDir v ℓ
          ∈ Work.Drive.Final.Trough.cbox s c σ := by
        rw [← hypair, ← ht]
        exact hycbox
      have hzy : ζ y = g X + t := by
        calc ζ y = ζ (Work.Drive.Final.Trough.sectionL v ℓ X
              + t • Work.Drive.Final.Trough.fibreDir v ℓ) := by rw [ht, hypair]
          _ = g X + t := by rw [map_add, map_smul, hζfd]; simp [g]
      rw [hzy]
      exact ⟨by linarith [Work.Drive.Final.Trough.htl_le_of_mem_cbox s c σ hv hℓv hℓne hmem],
        by linarith [Work.Drive.Final.Trough.le_hth_of_mem_cbox s c σ hv hℓv hℓne hmem]⟩
    · rintro ⟨h1, h2⟩
      refine ⟨Work.Drive.Final.Trough.sectionL v ℓ X
        + (p - g X) • Work.Drive.Final.Trough.fibreDir v ℓ, ?_, ?_⟩
      · rw [fibre_eq_pair hs c σ v ℓ X]
        refine ⟨?_, ?_⟩
        · exact Work.Drive.Final.Trough.mem_cbox_of_mem_shadow_of_between s c σ v ℓ hv hℓv hℓne
            hXsh (by linarith) (by linarith)
        · rw [map_add, map_smul, Work.Drive.Final.Trough.sectionL_spec hv hℓv hℓne,
            Work.Drive.Final.Trough.pair_fibreDir hv hℓv hℓne, smul_zero, add_zero]
      · calc ζ (Work.Drive.Final.Trough.sectionL v ℓ X
              + (p - g X) • Work.Drive.Final.Trough.fibreDir v ℓ)
            = g X + (p - g X) := by rw [map_add, map_smul, hζfd]; simp [g]
          _ = p := by ring
  have hfMax_eq : ∀ X ∈ Work.Drive.Mono.FiberModel.boxShadow s c σ v ℓ,
      Work.Drive.Mono.FiberModel.fMax ζ v ℓ s c σ X
        = g X + Work.Drive.Final.Trough.hth s c σ v ℓ X := by
    intro X hX
    have hXsh : X ∈ Work.Drive.Final.Trough.shadow s c σ v ℓ := by
      simpa [boxShadow_eq_shadow hs c σ v ℓ] using hX
    have hsup : Work.Drive.Mono.FiberModel.fMax ζ v ℓ s c σ X
        = sSup (ζ '' Work.Drive.Mono.FiberModel.fibre v ℓ s c σ X) := by
      rw [Work.Drive.Mono.FiberModel.fMax, Work.Drive.Mono.fibreMax,
        Work.Drive.Mono.FiberModel.fibre_eq_set]
      simp only [innerSL_apply_apply]
    have hle : g X + Work.Drive.Final.Trough.htl s c σ v ℓ X
        ≤ g X + Work.Drive.Final.Trough.hth s c σ v ℓ X := by
      linarith [Work.Drive.Final.Trough.htl_le_hth_of_mem_shadow s c σ v ℓ hv hℓv hℓne hXsh]
    rw [hsup, hfib_img X hX, csSup_Icc hle]
  have hfMin_eq : ∀ X ∈ Work.Drive.Mono.FiberModel.boxShadow s c σ v ℓ,
      Work.Drive.Mono.FiberModel.fMin ζ v ℓ s c σ X
        = g X + Work.Drive.Final.Trough.htl s c σ v ℓ X := by
    intro X hX
    have hXsh : X ∈ Work.Drive.Final.Trough.shadow s c σ v ℓ := by
      simpa [boxShadow_eq_shadow hs c σ v ℓ] using hX
    have hinf : Work.Drive.Mono.FiberModel.fMin ζ v ℓ s c σ X
        = sInf (ζ '' Work.Drive.Mono.FiberModel.fibre v ℓ s c σ X) := by
      rw [Work.Drive.Mono.FiberModel.fMin, Work.Drive.Mono.fibreMin,
        Work.Drive.Mono.FiberModel.fibre_eq_set]
      simp only [innerSL_apply_apply]
    have hle : g X + Work.Drive.Final.Trough.htl s c σ v ℓ X
        ≤ g X + Work.Drive.Final.Trough.hth s c σ v ℓ X := by
      linarith [Work.Drive.Final.Trough.htl_le_hth_of_mem_shadow s c σ v ℓ hv hℓv hℓne hXsh]
    rw [hinf, hfib_img X hX, csInf_Icc hle]
  refine ⟨ζ, hkerζ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro X hX
    rw [hfMin_eq X hX, hfMax_eq X hX]
    exact hfib_img X hX
  · intro X hX
    have hXbs : X ∈ Work.Drive.Mono.FiberModel.boxShadow s c σ v ℓ := interior_subset hX
    have hXint : X ∈ interior (Work.Drive.Final.Trough.shadow s c σ v ℓ) := by
      simpa [boxShadow_eq_shadow hs c σ v ℓ] using hX
    rw [hfMin_eq X hXbs, hfMax_eq X hXbs]
    linarith [Work.Drive.Final.Trough.htl_lt_hth_of_mem_interior s c σ hs hv hℓv hℓne hXint]
  · have hcont : Continuous (fun X : ℝ × ℝ =>
        g X + Work.Drive.Final.Trough.hth s c σ v ℓ X) :=
      ((ζ.continuous.comp
        (Work.Drive.Final.Trough.sectionL v ℓ).continuous_of_finiteDimensional)).add
        (Work.Drive.Final.Trough.continuous_hth s c σ v ℓ hv hℓv hℓne)
    exact hcont.continuousOn.congr (fun X hX => hfMax_eq X hX)
  · have hcont : Continuous (fun X : ℝ × ℝ =>
        g X + Work.Drive.Final.Trough.htl s c σ v ℓ X) :=
      ((ζ.continuous.comp
        (Work.Drive.Final.Trough.sectionL v ℓ).continuous_of_finiteDimensional)).add
        (Work.Drive.Final.Trough.continuous_htl s c σ v ℓ hv hℓv hℓne)
    exact hcont.continuousOn.congr (fun X hX => hfMin_eq X hX)
  · refine ⟨Work.Drive.Mono.FiberModel.convex_boxShadow s c σ v ℓ, ?_⟩
    intro X hX Y hY a b ha hb hab
    have hXY : a • X + b • Y ∈ Work.Drive.Mono.FiberModel.boxShadow s c σ v ℓ :=
      Work.Drive.Mono.FiberModel.convex_boxShadow s c σ v ℓ hX hY ha hb hab
    have hXs : X ∈ Work.Drive.Final.Trough.shadow s c σ v ℓ := by
      simpa [boxShadow_eq_shadow hs c σ v ℓ] using hX
    have hYs : Y ∈ Work.Drive.Final.Trough.shadow s c σ v ℓ := by
      simpa [boxShadow_eq_shadow hs c σ v ℓ] using hY
    have h1 : a * Work.Drive.Final.Trough.hth s c σ v ℓ X
        + b * Work.Drive.Final.Trough.hth s c σ v ℓ Y
        ≤ Work.Drive.Final.Trough.hth s c σ v ℓ (a • X + b • Y) := by
      have := (Work.Drive.Final.Trough.concaveOn_hth s c σ v ℓ hv hℓv hℓne).2 hXs hYs ha hb hab
      simpa only [smul_eq_mul] using this
    have h2 := hg_add a b X Y
    rw [hfMax_eq X hX, hfMax_eq Y hY, hfMax_eq (a • X + b • Y) hXY]
    simp only [smul_eq_mul]
    nlinarith [h1, h2]
  · refine ⟨Work.Drive.Mono.FiberModel.convex_boxShadow s c σ v ℓ, ?_⟩
    intro X hX Y hY a b ha hb hab
    have hXY : a • X + b • Y ∈ Work.Drive.Mono.FiberModel.boxShadow s c σ v ℓ :=
      Work.Drive.Mono.FiberModel.convex_boxShadow s c σ v ℓ hX hY ha hb hab
    have hXs : X ∈ Work.Drive.Final.Trough.shadow s c σ v ℓ := by
      simpa [boxShadow_eq_shadow hs c σ v ℓ] using hX
    have hYs : Y ∈ Work.Drive.Final.Trough.shadow s c σ v ℓ := by
      simpa [boxShadow_eq_shadow hs c σ v ℓ] using hY
    have h1 : Work.Drive.Final.Trough.htl s c σ v ℓ (a • X + b • Y)
        ≤ a * Work.Drive.Final.Trough.htl s c σ v ℓ X
          + b * Work.Drive.Final.Trough.htl s c σ v ℓ Y := by
      have := (Work.Drive.Final.Trough.convexOn_htl s c σ v ℓ hv hℓv hℓne).2 hXs hYs ha hb hab
      simpa only [smul_eq_mul] using this
    have h2 := hg_add a b X Y
    rw [hfMin_eq X hX, hfMin_eq Y hY, hfMin_eq (a • X + b • Y) hXY]
    simp only [smul_eq_mul]
    nlinarith [h1, h2]

end

end Work.Drive.Mono.WindowCase
