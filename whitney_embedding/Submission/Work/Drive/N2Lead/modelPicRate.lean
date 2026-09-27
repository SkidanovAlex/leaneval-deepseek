import Mathlib
import Submission.Work.Drive.N2Lead.modelPicDefs
import Submission.Work.Drive.N2Lead.mobius_pushedStarIcc
import Submission.Work.Drive.N2Lead.mobiusArcSmooth
import Submission.Work.Drive.N2Lead.mobius_upperArcs
import Submission.Work.Drive.N2Lead.pinComplex
import Submission.Work.Drive.N2Lead.modelArc_cross_about_one

namespace Work.Drive.N2Lead

open scoped Manifold ContDiff Topology
open Set Filter


noncomputable section

/-! ## The level curve `u ↦ √(s + i u)`

The level `Re ζ² = s` is parametrised through a point `ζ` by `ζ = ε₀ * levelRho s w₀` with
`w₀ = (ζ²).im` and `ε₀ = ±1`; the tangent direction of the level at `ζ` is `I / (2ζ)`. -/

/-- The level curve `u ↦ √(s + i u)` of the level `Re ζ² = s`. -/
def levelRho (s : ℝ) (u : ℝ) : ℂ := Complex.sqrt ((s : ℂ) + (u : ℂ) * Complex.I)

lemma levelRho_def (s u : ℝ) :
    levelRho s u = Complex.sqrt ((s : ℂ) + (u : ℂ) * Complex.I) := rfl

lemma levelRho_sq (s u : ℝ) : (levelRho s u) ^ 2 = (s : ℂ) + (u : ℂ) * Complex.I :=
  Work.Drive.N2.complex_sqrt_sq _

lemma levelRho_ne_zero {s u : ℝ} (hs : 0 < s) : levelRho s u ≠ 0 := by
  intro h
  have h2 : (levelRho s u) ^ 2 = 0 := by rw [h]; ring
  rw [levelRho_sq] at h2
  have hre : ((s : ℂ) + (u : ℂ) * Complex.I).re = 0 := by rw [h2]; simp
  simp at hre
  linarith

/-- `saddlePhi` at the level point `s + i u` is the square of the model arc `mobiusRho`. -/
lemma saddlePhi_levelRho (η δ s u : ℝ) :
    Work.Drive.N2.saddlePhi η δ ((s : ℂ) + (u : ℂ) * Complex.I) = (mobiusRho η δ s u) ^ 2 := by
  rw [mobiusRho, Work.Drive.N2.complex_sqrt_sq]
  apply Complex.ext <;>
    simp [Work.Drive.N2.saddlePhi_re, Work.Drive.N2.saddlePhi_im, modelZeta, modelSigma]

/-- **The level law of `saddlePsi`**: on the level `Re ζ² = s`, the square of `Ψ` is the square of
the model arc. -/
lemma saddlePsi_levelRho_sq {η δ s ε₀ : ℝ} (hδ : 0 < δ) (hδ₂ : δ < 1 / 2)
    (hε₀ : ε₀ = 1 ∨ ε₀ = -1) (u : ℝ) :
    (Work.Drive.N2.saddlePsi η δ (ε₀ * levelRho s u)) ^ 2 = (mobiusRho η δ s u) ^ 2 := by
  have h2 : (0 : ℝ) ≤ 2 - 4 * δ := by linarith
  rw [Work.Drive.N2.saddlePsi_sq hδ h2]
  have hsq : (ε₀ * levelRho s u) ^ 2 = (s : ℂ) + (u : ℂ) * Complex.I := by
    rw [mul_pow, levelRho_sq]
    rcases hε₀ with rfl | rfl <;> norm_num
  rw [hsq, saddlePhi_levelRho]

/-- `mobiusRho` never vanishes. -/
lemma mobiusRho_ne_zero {η δ s : ℝ} (hδ : 0 < δ) (hδ₂ : δ < 1 / 2) (hs : 0 < s) (u : ℝ) :
    mobiusRho η δ s u ≠ 0 := by
  intro h0
  have hsq : (mobiusRho η δ s u) ^ 2 = modelZeta η δ s u := by
    rw [mobiusRho]; exact Work.Drive.N2.complex_sqrt_sq _
  have hz : modelZeta η δ s u = 0 := by rw [← hsq, h0]; ring
  have hmem := modelZeta_mem_slitPlane (η := η) hδ hδ₂ hs u
  rw [hz] at hmem
  rw [Complex.mem_slitPlane_iff] at hmem
  rcases hmem with h | h <;> simp at h

/-- **The derivative of the level curve** at `w₀`. -/
lemma hasDerivAt_levelRho {s : ℝ} (hs : 0 < s) (w₀ : ℝ) :
    HasDerivAt (levelRho s) (Complex.I / (2 * levelRho s w₀)) w₀ := by
  have hG : HasDerivAt (fun u : ℝ => (s : ℂ) + (u : ℂ) * Complex.I) Complex.I w₀ := by
    have h1 : HasDerivAt (fun u : ℝ => ((u : ℝ) : ℂ)) (1 : ℂ) w₀ := by
      simpa using (hasDerivAt_id w₀).ofReal_comp
    have h2 : HasDerivAt (fun u : ℝ => (u : ℂ) * Complex.I) ((1 : ℂ) * Complex.I) w₀ :=
      h1.mul_const Complex.I
    simpa using h2.const_add ((s : ℂ))
  have hz : ((s : ℂ) + (w₀ : ℂ) * Complex.I) ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    left
    simpa using hs
  have hcomp := (Complex.hasDerivAt_sqrt hz).comp w₀ hG
  have hval : ((s : ℂ) + (w₀ : ℂ) * Complex.I) ^ (-1 / 2 : ℂ) / 2 * Complex.I
      = Complex.I / (2 * levelRho s w₀) := by
    have h1 : ((s : ℂ) + (w₀ : ℂ) * Complex.I) ^ (-1 / 2 : ℂ)
        = (Complex.sqrt ((s : ℂ) + (w₀ : ℂ) * Complex.I))⁻¹ := by
      rw [show (-1 / 2 : ℂ) = -(2⁻¹ : ℂ) by norm_num, Complex.cpow_neg]
      rfl
    rw [h1, levelRho]
    field_simp
  rw [hval] at hcomp
  exact hcomp

/-- **Extraction of the level parametrisation**: every point `ζ ≠ 0` of the level `Re ζ² = s` is
`± √(s + i (Im ζ²))`. -/
lemma exists_levelRho_eq {s : ℝ} {ζ : ℂ} (hζ : ζ ≠ 0) (hre : (ζ ^ 2).re = s) :
    ∃ ε₀ : ℝ, (ε₀ = 1 ∨ ε₀ = -1) ∧ ζ = ε₀ * levelRho s ((ζ ^ 2).im) := by
  set w₀ : ℝ := (ζ ^ 2).im with hw₀
  have hz : ((s : ℂ) + (w₀ : ℂ) * Complex.I) = ζ ^ 2 := by
    rw [hw₀]
    apply Complex.ext <;> simp [hre]
  have hc : ((s : ℂ) + (w₀ : ℂ) * Complex.I) ≠ 0 := by
    rw [hz]; exact pow_ne_zero 2 hζ
  rcases sq_eq_sqrt_or hc (x := ζ) (by rw [hz]) with h | h
  · exact ⟨1, Or.inl rfl, by rw [h, levelRho]; simp⟩
  · exact ⟨-1, Or.inr rfl, by rw [h, levelRho]; simp⟩

/-- **The `±1`-valued quotient is locally constant**: along the level curve through `ζ`, the sign of
`Ψ` relative to the model arc is eventually constant near `w₀ = (ζ²).im`. -/
lemma saddlePsi_levelRho_eventuallyEq {η δ s ε₀ : ℝ} (hδ : 0 < δ) (hδ₂ : δ < 1 / 2)
    (hs : 0 < s) (hε₀ : ε₀ = 1 ∨ ε₀ = -1) (w₀ : ℝ) :
    ∃ σ : ℂ, (σ = 1 ∨ σ = -1) ∧
      ∀ᶠ u in 𝓝 w₀,
        Work.Drive.N2.saddlePsi η δ (ε₀ * levelRho s u) = σ * mobiusRho η δ s u := by
  have hne : ∀ u : ℝ, mobiusRho η δ s u ≠ 0 := fun u => mobiusRho_ne_zero hδ hδ₂ hs u
  set q : ℝ → ℂ := fun u => Work.Drive.N2.saddlePsi η δ (ε₀ * levelRho s u) / mobiusRho η δ s u
    with hq
  have hq2 : ∀ u : ℝ, q u = 1 ∨ q u = -1 := by
    intro u
    have hsq : (q u) ^ 2 = 1 := by
      rw [hq]
      simp only [div_pow]
      rw [saddlePsi_levelRho_sq hδ hδ₂ hε₀ u]
      exact div_self (pow_ne_zero 2 (hne u))
    exact sq_eq_one_iff.mp hsq
  have hcont : ContinuousAt q w₀ := by
    set F : ℝ → ℂ := fun u => (ε₀ : ℂ) * levelRho s u with hF
    have hinner : ContinuousAt F w₀ :=
      ((hasDerivAt_levelRho hs w₀).const_mul (ε₀ : ℂ)).continuousAt
    have houter : ContinuousAt (fun z : ℂ => Work.Drive.N2.saddlePsi η δ z) (F w₀) :=
      (Work.Drive.N2.contDiff_saddlePsi η δ hδ hδ₂).continuous.continuousAt
    have h1 : ContinuousAt (fun u : ℝ => Work.Drive.N2.saddlePsi η δ (F u)) w₀ :=
      houter.comp hinner
    have h2 : ContinuousAt (fun u : ℝ => mobiusRho η δ s u) w₀ :=
      (mobiusRho_contDiff (η := η) hδ hδ₂ hs).continuous.continuousAt
    exact h1.div h2 (hne w₀)
  refine ⟨q w₀, hq2 w₀, ?_⟩
  have hsp : ∀ u : ℝ,
      Work.Drive.N2.saddlePsi η δ (ε₀ * levelRho s u) = q u * mobiusRho η δ s u := by
    intro u; rw [hq]; exact (div_mul_cancel₀ _ (hne u)).symm
  have hev1 : ∀ᶠ u in 𝓝 w₀, ‖q u - q w₀‖ < 1 := by
    have hqt : ContinuousAt (fun u : ℝ => q u - q w₀) w₀ :=
      hcont.sub (continuousAt_const (y := q w₀))
    have htend : Tendsto (fun u : ℝ => q u - q w₀) (𝓝 w₀) (𝓝 0) := by
      have := hqt.tendsto
      simpa [sub_self] using this
    exact htend.norm.eventually (Iio_mem_nhds (by norm_num : ‖(0 : ℂ)‖ < 1))
  filter_upwards [hev1] with u hu
  rcases hq2 u with h | h <;> rcases hq2 w₀ with h0 | h0
  · rw [hsp u, h, h0]
  · rw [h, h0] at hu; norm_num at hu
  · rw [h, h0] at hu; norm_num at hu
  · rw [hsp u, h, h0]

end

/-- **The picture along the level is one of the two pushed arcs** (locally near `w₀`): the sign of
`Ψ` relative to the model arc determines which of the two pushed arcs the picture is. -/
lemma modelPic_level_local {η δ s a' ε Dp εp ε₀ w₀ : ℝ} (hδ : 0 < δ) (hδ₂ : δ < 1 / 2)
    (hs : 0 < s) (hε₀ : ε₀ = 1 ∨ ε₀ = -1) :
    ( (Work.Drive.N2.saddlePsi η δ (ε₀ * levelRho s w₀) = -(mobiusRho η δ s w₀)) ∧
      (∀ᶠ u in 𝓝 w₀, modelPic η δ a' ε Dp εp (ε₀ * levelRho s u)
        = proj2 (pushY Dp εp 1 (mobiusAlpha η δ s a' ε u))) )
    ∨ ( (Work.Drive.N2.saddlePsi η δ (ε₀ * levelRho s w₀) = mobiusRho η δ s w₀) ∧
      (∀ᶠ u in 𝓝 w₀, modelPic η δ a' ε Dp εp (ε₀ * levelRho s u)
        = proj2 (pushY Dp εp 1 (mobiusBeta η δ s a' ε u))) ) := by
  obtain ⟨σ, hσ, hev⟩ :=
    saddlePsi_levelRho_eventuallyEq (η := η) hδ hδ₂ hs hε₀ w₀
  rcases hσ with hσ1 | hσ1
  · right
    refine ⟨?_, ?_⟩
    · have h := Filter.EventuallyEq.eq_of_nhds hev
      rw [hσ1] at h
      simpa using h
    · filter_upwards [hev] with u hu
      rw [hσ1] at hu
      exact modelPic_of_saddlePsi_eq (by simpa using hu)
  · left
    refine ⟨?_, ?_⟩
    · have h := Filter.EventuallyEq.eq_of_nhds hev
      rw [hσ1] at h
      simpa using h
    · filter_upwards [hev] with u hu
      rw [hσ1] at hu
      exact modelPic_of_saddlePsi_eq_neg (by simpa using hu)

/-- **Real-independence from a non-vanishing determinant**: two complex numbers whose determinant
`a.re * b.im - a.im * b.re` does not vanish are `ℝ`-independent. -/
lemma not_realMultiple_of_det {a b : ℂ} (h : a.re * b.im - a.im * b.re ≠ 0) :
    ¬ ∃ t : ℝ, b = t • a := by
  rintro ⟨t, ht⟩
  apply h
  rw [ht]
  simp only [Complex.smul_re, Complex.smul_im]
  ring

/-- **The final rate step**: if the derivative of the picture at `ζ` in the direction `I / (2ζ)` is
the derivative of the pushed arc `proj2 (pushY Dp εp 1 (g ·))`, its value is that arc's value, and the
tangent direction is `w = μ • (I / (2ζ))` with `μ ≠ 0`, then the arc's rate row (its determinant is
non-zero) makes the derivative of the picture independent of its value. -/
lemma rate_step {η δ s a' ε Dp εp : ℝ} {ζ w : ℂ} {u₀ μ εs : ℝ} {g : ℝ → E3}
    (hg : HasDerivAt (fun u : ℝ => proj2 (pushY Dp εp 1 (g u)))
      ((fderiv ℝ (modelPic η δ a' ε Dp εp) ζ) (Complex.I / (2 * ζ))) u₀)
    (hval : modelPic η δ a' ε Dp εp ζ = proj2 (pushY Dp εp 1 (g u₀)))
    (hμ : μ ≠ 0) (hw : w = μ • (Complex.I / (2 * ζ)))
    (hrow : εs * ((pushY Dp εp 1 (g u₀)) 0 * deriv (fun u : ℝ => (pushY Dp εp 1 (g u)) 1) u₀
        - (pushY Dp εp 1 (g u₀)) 1 * deriv (fun u : ℝ => (pushY Dp εp 1 (g u)) 0) u₀) < 0)
    (hεs : εs = 1 ∨ εs = -1) :
    (modelPic η δ a' ε Dp εp ζ).re * ((fderiv ℝ (modelPic η δ a' ε Dp εp) ζ) w).im
      - (modelPic η δ a' ε Dp εp ζ).im * ((fderiv ℝ (modelPic η δ a' ε Dp εp) ζ) w).re ≠ 0 := by
  have hrow' : (pushY Dp εp 1 (g u₀)) 0 * deriv (fun u : ℝ => (pushY Dp εp 1 (g u)) 1) u₀
      - (pushY Dp εp 1 (g u₀)) 1 * deriv (fun u : ℝ => (pushY Dp εp 1 (g u)) 0) u₀ ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hrow
    exact lt_irrefl 0 hrow
  have hD : (fderiv ℝ (modelPic η δ a' ε Dp εp) ζ) w
      = μ • ((fderiv ℝ (modelPic η δ a' ε Dp εp) ζ) (Complex.I / (2 * ζ))) := by
    rw [hw, map_smul]
  have hre : (deriv (fun u : ℝ => proj2 (pushY Dp εp 1 (g u))) u₀).re
      = deriv (fun u : ℝ => (pushY Dp εp 1 (g u)) 0) u₀ := by
    have h := (Complex.reCLM.hasFDerivAt.comp_hasDerivAt u₀ hg).deriv
    rw [← hg.deriv] at h
    have hfun : (Complex.reCLM ∘ fun u : ℝ => proj2 (pushY Dp εp 1 (g u)))
        = fun u : ℝ => (pushY Dp εp 1 (g u)) 0 := by
      funext u
      rfl
    rw [hfun] at h
    exact h.symm
  have him : (deriv (fun u : ℝ => proj2 (pushY Dp εp 1 (g u))) u₀).im
      = deriv (fun u : ℝ => (pushY Dp εp 1 (g u)) 1) u₀ := by
    have h := (Complex.imCLM.hasFDerivAt.comp_hasDerivAt u₀ hg).deriv
    rw [← hg.deriv] at h
    have hfun : (Complex.imCLM ∘ fun u : ℝ => proj2 (pushY Dp εp 1 (g u)))
        = fun u : ℝ => (pushY Dp εp 1 (g u)) 1 := by
      funext u
      rfl
    rw [hfun] at h
    exact h.symm
  rw [hD, Complex.smul_im, Complex.smul_re, smul_eq_mul, smul_eq_mul, hval]
  simp only [proj2]
  rw [← hg.deriv, hre, him]
  intro h0
  rcases mul_eq_zero.mp (show μ * ((pushY Dp εp 1 (g u₀)) 0
        * deriv (fun u : ℝ => (pushY Dp εp 1 (g u)) 1) u₀
      - (pushY Dp εp 1 (g u₀)) 1 * deriv (fun u : ℝ => (pushY Dp εp 1 (g u)) 0) u₀) = 0 by
    rw [← h0]; ring) with h | h
  · exact hμ h
  · exact hrow' h

/-- **The plane-model rate row of the twisted Möbius upper picture.**  Let
`modelPic η δ a' ε Dp εp : ℂ → ℂ` be the plane model (`modelPicDefs.lean`, module docstring):
`modelPic η δ a' ε Dp εp ζ = proj2 (pushY Dp εp 1 (twistX ε (-1) (twistY a' (-1)
(cE3 (saddlePsi η δ ζ)))))`, and let `mobiusAlpha`/`mobiusBeta η δ s a' ε` be the two model arcs.
The six rows `hαsm … hβx` are exactly the rows of the arcs on `[-2,2]` supplied by
`Work.Drive.N2Lead.mobius_upperArcs` (smoothness, `y`-signs, positive `x`-derivative).

Claim: there is `εp₀ > 0` and, for every `εp ≤ εp₀`, a `D₀ ≥ 0` such that for every push size
`Dp ≥ D₀` and every point `ζ` of the level `Re ζ² = s` with `|Im ζ²| < 39/20`, the planar velocity of
the model picture along the level is never a real multiple of the value.

Full proof plan, all bricks named: `Submission/Work/Drive/N2Lead/NOTES_modelPicRate_route.md`.
Short form: parametrise the level through `ζ` as `ζ = ± ρ₀ w₀`, `ρ₀ u = √(s + I u)`; `saddlePsi`
sends it to the `mobiusRho η δ s`-curve up to a *locally constant* sign (because
`(saddlePsi η δ z)² = saddlePhi η δ (z²)` and `saddlePhi η δ (w²) = modelZeta η δ s (w².im)` on the
level), so the picture restricted to the level is one of the two pushed arcs; the level direction is
`μ • (I/(2ζ))` with `μ = (2ζw).im ≠ 0`; the chain rule gives the velocity as `μ` times the derivative
of that pushed arc; and both pushed arcs have non-vanishing `mobiusRate` on `[-2,2]` by
`Work.Drive.N2Lead.mobius_pushedStarIcc`.  The final step is the elementary fact that for complex
`a b`, real-dependence `∃ t, a = t • b` is `a.re * b.im - a.im * b.re = 0`. -/
theorem modelPicRate {η δ s a' ε : ℝ} (hη : 0 < η) (hδ : 0 < δ) (hδ₂ : δ < 1 / 2) (hs : 0 < s)
    (ha' : 0 < a') (hε : 0 < ε)
    (hαsm : ContDiff ℝ 1 (mobiusAlpha η δ s a' ε))
    (hβsm : ContDiff ℝ 1 (mobiusBeta η δ s a' ε))
    (hαy : ∀ w ∈ Set.Icc (-2) 2, 0 < (mobiusAlpha η δ s a' ε w) 1)
    (hβy : ∀ w ∈ Set.Icc (-2) 2, (mobiusBeta η δ s a' ε w) 1 < 0)
    (hαx : ∀ w ∈ Set.Icc (-2) 2, 0 < deriv (fun u : ℝ => (mobiusAlpha η δ s a' ε u) 0) w)
    (hβx : ∀ w ∈ Set.Icc (-2) 2, 0 < deriv (fun u : ℝ => (mobiusBeta η δ s a' ε u) 0) w) :
    ∃ εp₀ : ℝ, 0 < εp₀ ∧ ∀ εp : ℝ, 0 < εp → εp ≤ εp₀ →
      ∃ D₀ : ℝ, 0 ≤ D₀ ∧ ∀ Dp : ℝ, D₀ ≤ Dp →
        ∀ (ζ w : ℂ), ζ ≠ 0 → (ζ ^ 2).re = s → |(ζ ^ 2).im| < 39 / 20 →
          (2 * ζ * w).re = 0 → w ≠ 0 →
            ¬ (∃ t : ℝ, (fderiv ℝ (modelPic η δ a' ε Dp εp) ζ) w
                = t • (modelPic η δ a' ε Dp εp ζ)) := by
  -- Step 1: the rate rows of the two pushed arcs on `[-2,2]`
  obtain ⟨εpα, hεpα, hαrow⟩ :=
    mobius_pushedStarIcc (g := mobiusAlpha η δ s a' ε) (εs := (1 : ℝ)) (a := (-2 : ℝ)) (b := 2)
      hαsm (Or.inl rfl) (by norm_num) hαx (fun w hw => by simpa using hαy w hw)
  obtain ⟨εpβ, hεpβ, hβrow⟩ :=
    mobius_pushedStarIcc (g := mobiusBeta η δ s a' ε) (εs := (-1 : ℝ)) (a := (-2 : ℝ)) (b := 2)
      hβsm (Or.inr rfl) (by norm_num) hβx (fun w hw => by
        have h := hβy w hw
        simp only [neg_one_mul]
        linarith)
  refine ⟨min εpα εpβ, lt_min hεpα hεpβ, ?_⟩
  intro εp hεp hεple
  obtain ⟨Dα, hDα, hαall⟩ := hαrow εp hεp (le_trans hεple (min_le_left _ _))
  obtain ⟨Dβ, hDβ, hβall⟩ := hβrow εp hεp (le_trans hεple (min_le_right _ _))
  refine ⟨max Dα Dβ, le_of_lt (lt_max_of_lt_left hDα), ?_⟩
  intro Dp hDp
  intro ζ w hζ hre him hperp hw
  rintro ⟨t, ht⟩
  set w₀ : ℝ := (ζ ^ 2).im with hw₀
  set μ : ℝ := (2 * ζ * w).im with hμ
  have hw₀mem : w₀ ∈ Set.Icc (-2 : ℝ) 2 := by
    have h1 := abs_lt.mp (by rw [hw₀]; exact him : |w₀| < 39 / 20)
    constructor <;> linarith [h1.1, h1.2]
  obtain ⟨ε₀, hε₀, hζeq⟩ := exists_levelRho_eq hζ hre
  rw [← hw₀] at hζeq
  -- the tangent data
  have h2ζw : 2 * ζ * w = (μ : ℂ) * Complex.I := by
    apply Complex.ext
    · simpa using hperp
    · simp [hμ]
  have hμne : μ ≠ 0 := by
    intro h0
    have hzero : (2 : ℂ) * ζ * w = 0 := by rw [h2ζw, h0]; simp
    have h2ζne : (2 : ℂ) * ζ ≠ 0 := mul_ne_zero (by norm_num) hζ
    rcases mul_eq_zero.mp hzero with h | h
    · exact h2ζne h
    · exact hw h
  have hw_eq : w = μ • (Complex.I / (2 * ζ)) := by
    have h2ζne : (2 : ℂ) * ζ ≠ 0 := mul_ne_zero (by norm_num) hζ
    have hdiv : w = (μ : ℂ) * Complex.I / (2 * ζ) := by
      rw [eq_div_iff h2ζne]
      rw [← h2ζw]
      ring
    rw [hdiv, Complex.real_smul, mul_div_assoc']
  -- the differentiability of the picture
  have hdiff : DifferentiableAt ℝ (modelPic η δ a' ε Dp εp) ζ :=
    (contDiff_modelPic (η := η) (δ := δ) (a' := a') (ε := ε) (Dp := Dp) (εp := εp) hδ hδ₂)
      |>.differentiable (by simp) |>.differentiableAt
  rcases modelPic_level_local (η := η) (δ := δ) (s := s) (a' := a') (ε := ε) (Dp := Dp)
      (εp := εp) (ε₀ := ε₀) (w₀ := w₀) hδ hδ₂ hs hε₀ with ⟨hsp, hev⟩ | ⟨hsp, hev⟩
  · -- the `α` branch (the sign `-1`)
    have hval : modelPic η δ a' ε Dp εp ζ
        = proj2 (pushY Dp εp 1 (mobiusAlpha η δ s a' ε w₀)) := by
      rw [hζeq]
      exact modelPic_of_saddlePsi_eq_neg hsp
    have hchain : HasDerivAt (fun u : ℝ => modelPic η δ a' ε Dp εp (ε₀ * levelRho s u))
        ((fderiv ℝ (modelPic η δ a' ε Dp εp) ζ) (Complex.I / (2 * ζ))) w₀ := by
      have hρ' : HasDerivAt (fun u : ℝ => ε₀ * levelRho s u)
          (ε₀ * (Complex.I / (2 * levelRho s w₀))) w₀ :=
        (hasDerivAt_levelRho (s := s) hs w₀).const_mul (ε₀ : ℂ)
      have hfd : HasFDerivAt (modelPic η δ a' ε Dp εp)
          (fderiv ℝ (modelPic η δ a' ε Dp εp) ζ) (ε₀ * levelRho s w₀) := by
        rw [hζeq.symm]
        exact hdiff.hasFDerivAt
      have hc : Complex.I / (2 * ζ) = ε₀ * (Complex.I / (2 * levelRho s w₀)) := by
        have hx : levelRho s w₀ ≠ 0 := levelRho_ne_zero (u := w₀) hs
        have hesq : (ε₀ : ℂ) * (ε₀ : ℂ) = 1 := by
          rcases hε₀ with rfl | rfl <;> norm_num
        have hene : (ε₀ : ℂ) ≠ 0 := by
          rcases hε₀ with rfl | rfl <;> norm_num
        rw [hζeq]
        field_simp
        rw [pow_two]
        exact hesq.symm
      rw [hc]
      exact hfd.comp_hasDerivAt w₀ hρ'
    have hg : HasDerivAt (fun u : ℝ => proj2 (pushY Dp εp 1 (mobiusAlpha η δ s a' ε u)))
        ((fderiv ℝ (modelPic η δ a' ε Dp εp) ζ) (Complex.I / (2 * ζ))) w₀ :=
      hchain.congr_of_eventuallyEq (by
        filter_upwards [hev] with u hu
        exact hu.symm)
    exact not_realMultiple_of_det
      (rate_step (η := η) (δ := δ) (s := s) (a' := a') (ε := ε) (Dp := Dp) (εp := εp)
        (ζ := ζ) (w := w) (u₀ := w₀) (μ := μ) (g := mobiusAlpha η δ s a' ε) (εs := 1)
        hg hval hμne hw_eq ((hαall Dp (le_trans (le_max_left _ _) hDp)).2 w₀ hw₀mem) (Or.inl rfl)) ⟨t, ht⟩
  · -- the `β` branch (the sign `+1`)
    have hval : modelPic η δ a' ε Dp εp ζ
        = proj2 (pushY Dp εp 1 (mobiusBeta η δ s a' ε w₀)) := by
      rw [hζeq]
      exact modelPic_of_saddlePsi_eq hsp
    have hchain : HasDerivAt (fun u : ℝ => modelPic η δ a' ε Dp εp (ε₀ * levelRho s u))
        ((fderiv ℝ (modelPic η δ a' ε Dp εp) ζ) (Complex.I / (2 * ζ))) w₀ := by
      have hρ' : HasDerivAt (fun u : ℝ => ε₀ * levelRho s u)
          (ε₀ * (Complex.I / (2 * levelRho s w₀))) w₀ :=
        (hasDerivAt_levelRho (s := s) hs w₀).const_mul (ε₀ : ℂ)
      have hfd : HasFDerivAt (modelPic η δ a' ε Dp εp)
          (fderiv ℝ (modelPic η δ a' ε Dp εp) ζ) (ε₀ * levelRho s w₀) := by
        rw [hζeq.symm]
        exact hdiff.hasFDerivAt
      have hc : Complex.I / (2 * ζ) = ε₀ * (Complex.I / (2 * levelRho s w₀)) := by
        have hx : levelRho s w₀ ≠ 0 := levelRho_ne_zero (u := w₀) hs
        have hesq : (ε₀ : ℂ) * (ε₀ : ℂ) = 1 := by
          rcases hε₀ with rfl | rfl <;> norm_num
        have hene : (ε₀ : ℂ) ≠ 0 := by
          rcases hε₀ with rfl | rfl <;> norm_num
        rw [hζeq]
        field_simp
        rw [pow_two]
        exact hesq.symm
      rw [hc]
      exact hfd.comp_hasDerivAt w₀ hρ'
    have hg : HasDerivAt (fun u : ℝ => proj2 (pushY Dp εp 1 (mobiusBeta η δ s a' ε u)))
        ((fderiv ℝ (modelPic η δ a' ε Dp εp) ζ) (Complex.I / (2 * ζ))) w₀ :=
      hchain.congr_of_eventuallyEq (by
        filter_upwards [hev] with u hu
        exact hu.symm)
    exact not_realMultiple_of_det
      (rate_step (η := η) (δ := δ) (s := s) (a' := a') (ε := ε) (Dp := Dp) (εp := εp)
        (ζ := ζ) (w := w) (u₀ := w₀) (μ := μ) (g := mobiusBeta η δ s a' ε) (εs := -1)
        hg hval hμne hw_eq ((hβall Dp (le_trans (le_max_right _ _) hDp)).2 w₀ hw₀mem) (Or.inr rfl)) ⟨t, ht⟩


end Work.Drive.N2Lead
