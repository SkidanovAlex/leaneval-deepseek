import Mathlib
import Submission.Work.RPB1a.Caratheodory.Polar.lintegral_eq_lintegral_circleMap
import Submission.Work.RPB1a.Caratheodory.Arc.mem_sphere_neg_one_inter_ball_iff
import Submission.Work.RPB1a.Caratheodory.Chord.dist_le_circleMap_chord
import Submission.Work.RPB1a.Caratheodory.CS.sq_lintegral_le_mul_lintegral_sq
import Submission.Work.RPB1a.Caratheodory.Area.lintegral_enorm_deriv_sq_ne_top
import Submission.Work.RPB1a.Caratheodory.Divergence.lintegral_ofReal_div_Ioo_eq_top

/-!
# The length–area estimate: arbitrarily small circular crosscuts at a boundary point

This file proves `Work.RPB1a.Caratheodory.exists_small_crosscut`: for a holomorphic injection `f`
of the unit disc with bounded image, every boundary point `ζ` of the disc has circular crosscuts
`sphere ζ r ∩ ball 0 1` of arbitrarily small image diameter and arbitrarily small radius.  The proof
is the classical **length–area method** (Pommerenke, *Boundary Behaviour of Conformal Maps*, §2.2;
Garnett–Marshall, *Harmonic Measure*, the proof of Carathéodory's theorem).  It never uses boundary
continuity of `f`; the only analytic input is that the Dirichlet integral of `f` over the disc is
finite.

The argument, in outline.  Write `U` for the unit disc.

* The area formula for a holomorphic injection (`Area`) gives
  `∫⁻ z in U, ‖deriv f z‖ₑ ^ 2 = volume (f '' U)`, which is finite because the image is bounded.
* The circular crosscuts are parametrised by angles.  Rotating the plane to the boundary point
  `-1`, the arc `sphere (-1) r ∩ U` is exactly `{circleMap (-1) r θ | r/2 < cos θ}`, an arc of
  angles (`Arc`).
* The fundamental theorem of calculus along that arc bounds the distance between the images of any
  two of its points by `r` times the angular integral of `‖deriv f‖` over the whole period: the
  **chord bound** (`Chord`).  Hence the diameter of the image of the crosscut is at most that
  integral (`Mint`).
* Cauchy–Schwarz over the circle of angles (`CS`) turns that bound on the first moment into a bound
  on the second moment `Qint`: if the crosscut at radius `r` has image diameter at least `ε`, then
  `∫⁻ θ, ... ‖deriv f‖² ≥ ε² / (2 π r²)`.
* The polar-coordinate formula for the plane integral (`Polar`) rewrites the Dirichlet integral as
  `∫⁻ r in Ioi 0, ENNReal.ofReal r * Qint f r`; substituting the lower bound for `Qint` on
  `(0, ρ₀)` and integrating `r ↦ ε² / (2 π r)` — which diverges at `0` (`Divergence`) — exhibits
  the Dirichlet integral as `⊤`, contradicting finiteness.

Together these give the required `∃ r`, and a rotation removes the normalisation of the boundary
point.
-/

namespace Work.RPB1a.Caratheodory

open Complex Set Metric MeasureTheory
open scoped ContDiff Real Topology ENNReal


private noncomputable def Mint (f : ℂ → ℂ) (ρ : ℝ) : ℝ≥0∞ :=
  ∫⁻ θ in Ioo (-π) π, (ball (0 : ℂ) 1).indicator (fun z => ‖deriv f z‖ₑ) (circleMap (-1 : ℂ) ρ θ)

private noncomputable def Qint (f : ℂ → ℂ) (ρ : ℝ) : ℝ≥0∞ :=
  ∫⁻ θ in Ioo (-π) π,
    ((ball (0 : ℂ) 1).indicator (fun z => ‖deriv f z‖ₑ) (circleMap (-1 : ℂ) ρ θ)) ^ 2

private lemma measurable_dens (f : ℂ → ℂ) :
    Measurable ((ball (0 : ℂ) 1).indicator fun z => ‖deriv f z‖ₑ) :=
  (measurable_deriv f).enorm.indicator measurableSet_ball

private lemma measurable_dens_circle (f : ℂ → ℂ) (ρ : ℝ) :
    Measurable fun θ : ℝ =>
      (ball (0 : ℂ) 1).indicator (fun z => ‖deriv f z‖ₑ) (circleMap (-1 : ℂ) ρ θ) :=
  (measurable_dens f).comp (continuous_circleMap (-1) ρ).measurable

private lemma dens_sq (f : ℂ → ℂ) (w : ℂ) :
    ((ball (0 : ℂ) 1).indicator (fun z => ‖deriv f z‖ₑ) w) ^ 2
      = (ball (0 : ℂ) 1).indicator (fun z => ‖deriv f z‖ₑ ^ 2) w := by
  by_cases hw : w ∈ ball (0 : ℂ) 1
  · rw [Set.indicator_of_mem hw, Set.indicator_of_mem hw]
  · rw [Set.indicator_of_notMem hw, Set.indicator_of_notMem hw]; simp

/-- The polar-coordinate identity for the Dirichlet integral of `f` over the unit disc, with the
angular integral written as `Qint`. -/
private lemma polar_ball (f : ℂ → ℂ) :
    ∫⁻ z in ball (0 : ℂ) 1, ‖deriv f z‖ₑ ^ 2
      = ∫⁻ ρ in Ioi (0 : ℝ), ENNReal.ofReal ρ * Qint f ρ := by
  have hmeas : Measurable ((ball (0 : ℂ) 1).indicator fun z => ‖deriv f z‖ₑ ^ 2) :=
    ((measurable_deriv f).enorm.pow_const 2).indicator measurableSet_ball
  rw [← lintegral_indicator measurableSet_ball (fun z => ‖deriv f z‖ₑ ^ 2),
    Polar.lintegral_eq_lintegral_circleMap (-1) _ hmeas]
  refine setLIntegral_congr_fun measurableSet_Ioi fun ρ _ => ?_
  congr 1
  exact setLIntegral_congr_fun measurableSet_Ioo fun θ _ => (dens_sq f _).symm

/-- **The diameter of the image of a crosscut arc is at most the length integral.** -/
private lemma ediam_le (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (ball (0 : ℂ) 1)) {ρ : ℝ}
    (hρ : 0 < ρ) :
    Metric.ediam (f '' (sphere (-1 : ℂ) ρ ∩ ball (0 : ℂ) 1)) ≤ ENNReal.ofReal ρ * Mint f ρ := by
  rw [Metric.ediam_le_iff]
  rintro _ ⟨z, hz, rfl⟩ _ ⟨w, hw, rfl⟩
  rw [edist_dist]
  obtain ⟨θ₁, hθ₁, hc₁, rfl⟩ := (Arc.mem_sphere_neg_one_inter_ball_iff hρ z).mp hz
  obtain ⟨θ₂, hθ₂, hc₂, rfl⟩ := (Arc.mem_sphere_neg_one_inter_ball_iff hρ w).mp hw
  rcases le_total θ₁ θ₂ with hle | hle
  · exact Chord.dist_le_circleMap_chord hf hρ hle hθ₁ hθ₂ hc₁ hc₂
  · rw [dist_comm]
    exact Chord.dist_le_circleMap_chord hf hρ hle hθ₂ hθ₁ hc₂ hc₁

/-- **The slice Cauchy–Schwarz bound on `Qint`.** -/
private lemma Qint_lower (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (ball (0 : ℂ) 1)) {ε η ρ₀ ρ : ℝ}
    (hε : 0 < ε) (hρ₀η : ρ₀ ≤ η)
    (hdiam : ∀ r : ℝ, 0 < r → r < η →
      ε ≤ Metric.diam (closure (f '' (sphere (-1 : ℂ) r ∩ ball (0 : ℂ) 1))))
    (hρ : ρ ∈ Ioo (0 : ℝ) ρ₀) :
    ENNReal.ofReal (ε ^ 2 / (2 * π * ρ ^ 2)) ≤ Qint f ρ := by
  have hρpos : 0 < ρ := hρ.1
  have hρη : ρ < η := lt_of_lt_of_le hρ.2 hρ₀η
  have hd : ε ≤ Metric.diam (f '' (sphere (-1 : ℂ) ρ ∩ ball (0 : ℂ) 1)) := by
    have h1 := hdiam ρ hρpos hρη
    rwa [Metric.diam_closure] at h1
  have hed : Metric.ediam (f '' (sphere (-1 : ℂ) ρ ∩ ball (0 : ℂ) 1)) ≠ ⊤ := by
    intro htop
    have : Metric.diam (f '' (sphere (-1 : ℂ) ρ ∩ ball (0 : ℂ) 1)) = 0 := by
      change (Metric.ediam (f '' (sphere (-1 : ℂ) ρ ∩ ball (0 : ℂ) 1))).toReal = 0
      rw [htop]; simp
    linarith
  have hεed : ENNReal.ofReal ε ≤ Metric.ediam (f '' (sphere (-1 : ℂ) ρ ∩ ball (0 : ℂ) 1)) := by
    rw [ENNReal.ofReal_le_iff_le_toReal hed]
    exact hd
  have hM : ENNReal.ofReal ε / ENNReal.ofReal ρ ≤ Mint f ρ := by
    rw [ENNReal.div_le_iff_le_mul (Or.inl (ne_of_gt (ENNReal.ofReal_pos.mpr hρpos)))
      (Or.inl ENNReal.ofReal_ne_top), mul_comm]
    exact hεed.trans (ediam_le f hf hρpos)
  rw [← ENNReal.ofReal_div_of_pos hρpos] at hM
  have hcs := CS.sq_lintegral_le_mul_lintegral_sq
    (g := fun θ : ℝ =>
      (ball (0 : ℂ) 1).indicator (fun z => ‖deriv f z‖ₑ) (circleMap (-1 : ℂ) ρ θ))
    (measurable_dens_circle f ρ).aemeasurable
  have hsq : ENNReal.ofReal (ε / ρ) ^ 2 ≤ ENNReal.ofReal (2 * π) * Qint f ρ :=
    (ENNReal.pow_le_pow_left hM).trans hcs
  have h2 : ENNReal.ofReal ((ε / ρ) ^ 2) ≤ ENNReal.ofReal (2 * π) * Qint f ρ := by
    rwa [← ENNReal.ofReal_pow (show (0 : ℝ) ≤ ε / ρ by positivity)] at hsq
  have h3 : ENNReal.ofReal ((ε / ρ) ^ 2) / ENNReal.ofReal (2 * π) ≤ Qint f ρ := by
    rw [ENNReal.div_le_iff_le_mul (Or.inl (ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity))))
      (Or.inl ENNReal.ofReal_ne_top), mul_comm]
    exact h2
  have hreal : ε ^ 2 / (2 * π * ρ ^ 2) = (ε / ρ) ^ 2 / (2 * π) := by
    field_simp
  have heq : ENNReal.ofReal (ε ^ 2 / (2 * π * ρ ^ 2))
      = ENNReal.ofReal ((ε / ρ) ^ 2) / ENNReal.ofReal (2 * π) := by
    rw [hreal, ← ENNReal.ofReal_div_of_pos (y := 2 * π) (show (0 : ℝ) < 2 * π by positivity)]
  rw [heq]
  exact h3

/-- **The key estimate for the crosscuts at `-1`.** -/
private theorem key_neg_one (ε η : ℝ) (hε : 0 < ε) (hη : 0 < η) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (ball (0 : ℂ) 1)) (hfi : InjOn f (ball (0 : ℂ) 1))
    (hb : Bornology.IsBounded (f '' ball (0 : ℂ) 1)) :
    ∃ r : ℝ, 0 < r ∧ r < η ∧
      Metric.diam (closure (f '' (sphere (-1 : ℂ) r ∩ ball (0 : ℂ) 1))) < ε := by
  have hfin : ∫⁻ z in ball (0 : ℂ) 1, ‖deriv f z‖ₑ ^ 2 ≠ ⊤ :=
    Area.lintegral_enorm_deriv_sq_ne_top isOpen_ball hf hfi hb
  set ρ₀ : ℝ := min η 1 / 2 with hρ₀def
  have hminpos : 0 < min η 1 := lt_min hη zero_lt_one
  have hρ₀pos : 0 < ρ₀ := by rw [hρ₀def]; linarith
  have hρ₀le_η : ρ₀ ≤ η := by
    have := min_le_left η (1 : ℝ); rw [hρ₀def]; linarith
  by_contra hcon
  have hdiam : ∀ r : ℝ, 0 < r → r < η →
      ε ≤ Metric.diam (closure (f '' (sphere (-1 : ℂ) r ∩ ball (0 : ℂ) 1))) := by
    intro r hr hrη
    by_contra hlt
    exact hcon ⟨r, hr, hrη, lt_of_not_ge hlt⟩
  -- the polar identity lower bounds the Dirichlet integral by a divergent one
  have hmain : ∫⁻ ρ in Ioo (0 : ℝ) ρ₀, ENNReal.ofReal (ε ^ 2 / (2 * π * ρ))
      ≤ ∫⁻ z in ball (0 : ℂ) 1, ‖deriv f z‖ₑ ^ 2 := by
    calc ∫⁻ ρ in Ioo (0 : ℝ) ρ₀, ENNReal.ofReal (ε ^ 2 / (2 * π * ρ))
        = ∫⁻ ρ in Ioi (0 : ℝ),
            (Ioo (0 : ℝ) ρ₀).indicator (fun ρ => ENNReal.ofReal (ε ^ 2 / (2 * π * ρ))) ρ := by
          rw [← lintegral_indicator measurableSet_Ioo,
            ← lintegral_indicator measurableSet_Ioi]
          refine lintegral_congr fun ρ => ?_
          by_cases h : ρ ∈ Ioo (0 : ℝ) ρ₀
          · rw [Set.indicator_of_mem h, Set.indicator_of_mem (mem_Ioi.mpr h.1),
              Set.indicator_of_mem h]
          · rw [Set.indicator_of_notMem h]
            by_cases h2 : ρ ∈ Ioi (0 : ℝ)
            · rw [Set.indicator_of_mem h2, Set.indicator_of_notMem h]
            · rw [Set.indicator_of_notMem h2]
      _ ≤ ∫⁻ ρ in Ioi (0 : ℝ), ENNReal.ofReal ρ * Qint f ρ := by
          refine lintegral_mono fun ρ => ?_
          by_cases h : ρ ∈ Ioo (0 : ℝ) ρ₀
          · rw [Set.indicator_of_mem h]
            calc ENNReal.ofReal (ε ^ 2 / (2 * π * ρ))
                = ENNReal.ofReal ρ * ENNReal.ofReal (ε ^ 2 / (2 * π * ρ ^ 2)) := by
                  rw [← ENNReal.ofReal_mul (le_of_lt h.1)]
                  congr 1
                  field_simp
              _ ≤ ENNReal.ofReal ρ * Qint f ρ := by
                  gcongr
                  exact Qint_lower f hf hε hρ₀le_η hdiam h
          · rw [Set.indicator_of_notMem h]; exact bot_le
      _ = ∫⁻ z in ball (0 : ℂ) 1, ‖deriv f z‖ₑ ^ 2 := (polar_ball f).symm

  have hdiv : (∫⁻ ρ in Ioo (0 : ℝ) ρ₀, ENNReal.ofReal (ε ^ 2 / (2 * π * ρ))) = ⊤ := by
    have hc : 0 < ε ^ 2 / (2 * π) := by positivity
    have hEE : (∫⁻ ρ in Ioo (0 : ℝ) ρ₀, ENNReal.ofReal (ε ^ 2 / (2 * π * ρ)))
        = ∫⁻ ρ in Ioo (0 : ℝ) ρ₀, ENNReal.ofReal ((ε ^ 2 / (2 * π)) / ρ) := by
      refine setLIntegral_congr_fun (μ := volume) measurableSet_Ioo fun ρ hρ => ?_
      congr 1
      field_simp
    rw [hEE]
    exact Divergence.lintegral_ofReal_div_Ioo_eq_top hc hρ₀pos
  have : (∫⁻ z in ball (0 : ℂ) 1, ‖deriv f z‖ₑ ^ 2) = ⊤ := by
    refine top_le_iff.mp ?_
    rw [← hdiv]
    exact hmain
  exact hfin this

/-- **The crosscuts at `-1` for an arbitrary conformal map.** -/
private theorem key_general {D : Set ℂ} (hDb : Bornology.IsBounded D) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (ball 0 1)) (hfi : InjOn f (ball 0 1)) (hfs : f '' ball 0 1 = D)
    (ζ : ℂ) (hζ : ζ ∈ sphere 0 1) (ε : ℝ) (hε : 0 < ε) (η : ℝ) (hη : 0 < η) :
    ∃ r : ℝ, 0 < r ∧ r < η ∧
      Metric.diam (closure (f '' (sphere ζ r ∩ ball 0 1))) < ε := by
  have hb : Bornology.IsBounded (f '' ball (0 : ℂ) 1) := by rw [hfs]; exact hDb
  have hζn : ‖ζ‖ = 1 := by simpa [Metric.mem_sphere, dist_eq_norm] using hζ
  have hζne : ζ ≠ 0 := by
    intro h; rw [h, norm_zero] at hζn; exact one_ne_zero hζn.symm
  set w : ℂ := -ζ with hw
  have hwnorm : ‖w‖ = 1 := by rw [hw, norm_neg, hζn]
  have hwne : w ≠ 0 := by
    intro h; rw [h, norm_zero] at hwnorm; exact absurd hwnorm (by norm_num)
  set g : ℂ → ℂ := fun z => f (w * z) with hg
  have hgmaps : ∀ z ∈ ball (0 : ℂ) 1, w * z ∈ ball (0 : ℂ) 1 := by
    intro z hz
    rw [Metric.mem_ball, dist_eq_norm, sub_zero] at hz ⊢
    rw [norm_mul, hwnorm, one_mul]
    exact hz
  have hgd : DifferentiableOn ℂ g (ball (0 : ℂ) 1) := by
    rw [hg]
    exact hf.comp ((differentiableOn_const w).mul differentiableOn_id) hgmaps
  have hgi : InjOn g (ball (0 : ℂ) 1) := by
    intro z hz z' hz' h
    rw [hg] at h
    exact mul_left_cancel₀ hwne (hfi (hgmaps z hz) (hgmaps z' hz') h)
  have hgb : Bornology.IsBounded (g '' ball (0 : ℂ) 1) := by
    have himg : g '' ball (0 : ℂ) 1 = f '' ball (0 : ℂ) 1 := by
      rw [hg, show (fun z : ℂ => f (w * z)) = f ∘ (fun z : ℂ => w * z) from rfl,
        Set.image_comp]
      congr 1
      ext z
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hgmaps y hy
      · intro hz
        refine ⟨w⁻¹ * z, ?_, ?_⟩
        · rw [Metric.mem_ball, dist_eq_norm, sub_zero] at hz ⊢
          rw [norm_mul, norm_inv, hwnorm, inv_one, one_mul]
          exact hz
        · show w * (w⁻¹ * z) = z
          rw [← mul_assoc, mul_inv_cancel₀ hwne, one_mul]
    rw [himg]; exact hb
  obtain ⟨r, hr0, hrη, hrd⟩ := key_neg_one ε η hε hη hgd hgi hgb
  refine ⟨r, hr0, hrη, ?_⟩
  have hset : g '' (sphere (-1 : ℂ) r ∩ ball (0 : ℂ) 1) = f '' (sphere ζ r ∩ ball (0 : ℂ) 1) := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨w * y, ⟨?_, hgmaps y hy.2⟩, rfl⟩
      rw [Metric.mem_sphere, dist_eq_norm]
      have : w * y - ζ = w * (y - (-1)) := by rw [hw]; ring
      rw [this, norm_mul, hwnorm, one_mul]
      have := Metric.mem_sphere.mp hy.1
      rwa [dist_eq_norm] at this
    · rintro ⟨y, hy, rfl⟩
      refine ⟨w⁻¹ * y, ⟨?_, ?_⟩, ?_⟩
      · rw [Metric.mem_sphere, dist_eq_norm]
        have hwz : w⁻¹ * ζ = -1 := by
          rw [hw, inv_neg, neg_mul, inv_mul_cancel₀ hζne]
        have h1 : w⁻¹ * y - (-1) = w⁻¹ * (y - ζ) := by
          rw [mul_sub, hwz]
        rw [h1, norm_mul, norm_inv, hwnorm, inv_one, one_mul]
        have := Metric.mem_sphere.mp hy.1
        rwa [dist_eq_norm] at this
      · rw [Metric.mem_ball, dist_eq_norm, sub_zero, norm_mul, norm_inv, hwnorm, inv_one,
          one_mul]
        have := Metric.mem_ball.mp hy.2
        rwa [dist_eq_norm, sub_zero] at this
      · show f (w * (w⁻¹ * y)) = f y
        rw [← mul_assoc, mul_inv_cancel₀ hwne, one_mul]
  rw [← hset]
  exact hrd

/-- The length-area estimate of the Garnett–Marshall proof of Carathéodory's theorem: for a
conformal map of the disc onto a bounded domain, arbitrarily close to any boundary point of the
disc there are circular crosscuts of arbitrarily small image diameter. -/
theorem exists_small_crosscut {D : Set ℂ} (hDb : Bornology.IsBounded D) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (ball 0 1)) (hfi : InjOn f (ball 0 1)) (hfs : f '' ball 0 1 = D)
    (ζ : ℂ) (hζ : ζ ∈ sphere 0 1) :
    ∀ ε > 0, ∀ η > 0, ∃ r : ℝ, 0 < r ∧ r < η ∧
      Metric.diam (closure (f '' (sphere ζ r ∩ ball 0 1))) < ε := by
  intro ε hε η hη
  exact key_general hDb hf hfi hfs ζ hζ ε hε η hη

end Work.RPB1a.Caratheodory
