import Mathlib
import Submission.Work.Smooth.Plane.Slicing
import Submission.Work.InnermostDisk.All

namespace Work.Smooth.Plane.Slicing

open LeanEval.KnotTheory.PardonDistortion
open Set

noncomputable section

/-! ## Straight-line interpolation inside the arc `ArcInterval = [0,1]`

The homotopy of the main theorem moves a point `φ t` of the arc `ArcInterval = [0,1]` along the
straight segment joining it to the base point `φ 0`.  Since the homotopy parameter `s` ranges over
*all* of `ℝ` (a homotopy of closed curves of the torus is a map on `ℝ × ℝ`), it is first clamped
into `[0,1]`, so that the two weights `1 - s` and `s` are nonnegative and sum to `1`; convexity of
`[0,1]` then keeps the combination inside the arc. -/

/-- **The clamp of the line onto `[0,1]`**: `s ↦ min 1 (max 0 s)`.  It is continuous, takes the
values `0` at `0` and `1` at `1`, and its values lie in `[0,1]`. -/
def clampUnit (s : ℝ) : ℝ := min 1 (max 0 s)

theorem clampUnit_mem (s : ℝ) : clampUnit s ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨le_min zero_le_one (le_max_left 0 s), min_le_left 1 (max 0 s)⟩

@[simp] theorem clampUnit_zero : clampUnit 0 = 0 := by simp [clampUnit]

@[simp] theorem clampUnit_one : clampUnit 1 = 1 := by simp [clampUnit]

theorem continuous_clampUnit : Continuous clampUnit :=
  continuous_min.comp (continuous_const.prodMk
    (continuous_max.comp (continuous_const.prodMk continuous_id)))

/-- **The straight-line interpolation in the arc `ArcInterval = [0,1]`.**  `arcSeg φ s t` is the
convex combination of `φ t` and `φ 0` with weights `1 - clampUnit s` and `clampUnit s`; it lies in
the arc because the arc is convex. -/
def arcSeg (φ : ℝ → ArcInterval) (s t : ℝ) : ArcInterval :=
  ⟨(1 - clampUnit s) * (φ t : ℝ) + clampUnit s * (φ 0 : ℝ), by
    have hs := clampUnit_mem s
    have h1 : (0 : ℝ) ≤ 1 - clampUnit s := by linarith [hs.2]
    have h2 : (0 : ℝ) ≤ clampUnit s := hs.1
    have ht := (φ t).2
    have h0 := (φ 0).2
    refine ⟨?_, ?_⟩
    · have ha := mul_nonneg h1 ht.1
      have hb := mul_nonneg h2 h0.1
      linarith
    · have ha := mul_le_mul_of_nonneg_left ht.2 h1
      have hb := mul_le_mul_of_nonneg_left h0.2 h2
      nlinarith⟩

@[simp] theorem arcSeg_apply (φ : ℝ → ArcInterval) (s t : ℝ) :
    (arcSeg φ s t : ℝ) = (1 - clampUnit s) * (φ t : ℝ) + clampUnit s * (φ 0 : ℝ) := rfl

/-- The interpolation depends continuously on the two real parameters. -/
theorem continuous_arcSeg (φ : ℝ → ArcInterval) (hφ : Continuous φ) :
    Continuous fun p : ℝ × ℝ => arcSeg φ p.1 p.2 := by
  refine Continuous.subtype_mk ?_ _
  have hc : Continuous fun p : ℝ × ℝ => clampUnit p.1 :=
    continuous_clampUnit.comp continuous_fst
  have hφt : Continuous fun p : ℝ × ℝ => (φ p.2 : ℝ) :=
    continuous_subtype_val.comp (hφ.comp continuous_snd)
  have hφ0 : Continuous fun p : ℝ × ℝ => (φ 0 : ℝ) := continuous_const
  exact ((continuous_const.sub hc).mul hφt).add (hc.mul hφ0)

@[simp] theorem arcSeg_zero (φ : ℝ → ArcInterval) (t : ℝ) : arcSeg φ 0 t = φ t := by
  apply Subtype.ext
  simp [arcSeg_apply]

@[simp] theorem arcSeg_one (φ : ℝ → ArcInterval) (t : ℝ) : arcSeg φ 1 t = φ 0 := by
  apply Subtype.ext
  simp [arcSeg_apply]

/-- The interpolation is compatible with a periodic `φ`. -/
theorem arcSeg_periodic (φ : ℝ → ArcInterval) (hper : ∀ t : ℝ, φ (t + 2 * Real.pi) = φ t)
    (s t : ℝ) : arcSeg φ s (t + 2 * Real.pi) = arcSeg φ s t := by
  apply Subtype.ext
  simp [arcSeg_apply, hper t]

/-! ## The main theorem -/

/-- **A loop of the torus lying in an arc of the torus is inessential.**

Let `P` be a parametrised torus with surface `F = P.carrier`, let `a : ArcInterval → ℝ³` be an
embedded arc lying on `F`, and let `γ` be a closed curve of `F` whose image is contained in the
image of `a`.  Then `γ` has vanishing winding vector (it is null-homotopic in `F`), i.e. it is
inessential in the sense of `Work.CoreTopology.IsEssential`.

Intended proof: `a` is an injective continuous map from the compact interval `ArcInterval` into the
Hausdorff space `ℝ³`, so it is a homeomorphism onto its image
(`Continuous.homeoOfEquivCompactToT2`, as used in `Work.SurgeryInvariance.DiscRegion.not_isEssential`
for the disc); let `φ = a⁻¹ ∘ γ : ℝ → ArcInterval`, which is continuous and `2π`-periodic.  Then
`H (s,t) = a ((1-s) • φ t + s • φ 0)` is a homotopy (through loops in `F`, using `haP` and the
convexity of the interval) from `γ` to the constant loop of `F` at `γ 0`; hence `γ` is homotopic to
a constant curve of `F` and `Work.InnermostDisk.not_isEssential_iff_homotopic_const` applies. -/
theorem not_isEssential_of_range_subset_arc {P : Work.CoreTopology.ParamTorus}
    {a : C(Work.Smooth.Plane.ArcInterval, LeanEval.KnotTheory.PardonDistortion.R3)}
    (hinj : Function.Injective a)
    (haP : ∀ s : Work.Smooth.Plane.ArcInterval, a s ∈ P.carrier)
    {γ : Work.CoreTopology.ClosedCurve P} (hγ : ∀ t : ℝ, γ.γ t ∈ Set.range a) :
    ¬ Work.CoreTopology.IsEssential P γ := by
  -- `ArcInterval = [0,1]` is compact, so `a` is a homeomorphism onto its image
  -- `a` is a homeomorphism of the compact interval onto its image
  have he : Continuous (Equiv.ofInjective a hinj) :=
    a.continuous.subtype_mk fun s => Set.mem_range_self s
  let homeo : Work.Smooth.Plane.ArcInterval ≃ₜ Set.range a :=
    Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofInjective a hinj) he
  -- the reparametrisation `φ = a⁻¹ ∘ γ` of `γ` by points of the arc
  let φ : ℝ → Work.Smooth.Plane.ArcInterval := fun t => homeo.symm ⟨γ.γ t, hγ t⟩
  have hφcont : Continuous φ := homeo.symm.continuous.comp (γ.cont.subtype_mk _)
  have hφA : ∀ t : ℝ, a (φ t) = γ.γ t := by
    intro t
    have h := homeo.apply_symm_apply (⟨γ.γ t, hγ t⟩ : Set.range a)
    exact congrArg Subtype.val h
  have hφper : ∀ t : ℝ, φ (t + 2 * Real.pi) = φ t := by
    intro t
    apply hinj
    rw [hφA (t + 2 * Real.pi), hφA t, γ.periodic t]
  -- the straight-line homotopy in the arc contracts `γ` to the constant loop at `γ 0`
  refine (Work.InnermostDisk.not_isEssential_iff_homotopic_const P γ).mpr
    ⟨γ.γ 0, γ.mem 0, ?_⟩
  refine ⟨fun s t => a (arcSeg φ s t), ?_, ?_, ?_, ?_, ?_⟩
  · exact a.continuous.comp (continuous_arcSeg φ hφcont)
  · intro s t; exact haP _
  · intro t; show a (arcSeg φ 0 t) = γ.γ t; rw [arcSeg_zero, hφA t]
  · intro t; show a (arcSeg φ 1 t) = γ.γ 0; rw [arcSeg_one, hφA 0]
  · intro s t
    show a (arcSeg φ s (t + 2 * Real.pi)) = a (arcSeg φ s t)
    rw [arcSeg_periodic φ hφper s t]

end

end Work.Smooth.Plane.Slicing
