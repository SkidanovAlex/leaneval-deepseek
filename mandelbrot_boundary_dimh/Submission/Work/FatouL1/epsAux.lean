import Mathlib
import Submission.Work.FatouL1.wideDerivSmall

/-!
# FATOU-L1: shared preliminaries for `epsDiameterLe`

Elementary facts about the "big strip" `x₀ - 1 < Re z < x₀ + 3` (which the hypotheses `h₁`, `h₂`
of `epsDiameterLe` place inside `Qreg b₁ b₂`), about the holomorphy of the displacement
`ε = F - id` there, and about its restrictions to the vertical and horizontal lines through a
point of the strip (with the fundamental theorem of calculus along segments).

These live in a separate module so that the analytic pieces of `Work.FatouL1.epsDiameterLe`
(line masses, Fubini, the end limits) can be stated and proved against a stable interface.
-/

open MandelDim Set MeasureTheory Filter
open scoped Topology

namespace Work.FatouL1

noncomputable section

variable {b₁ b₂ : Option ℂ} {F : ℂ → ℂ} {x₀ : ℝ}

/-- The **big strip** `x₀ - 1 < Re z < x₀ + 3` (width `4`): on every vertical line of it the `L¹`
bounds of `NearTranslationL1` are available. -/
def bigStrip (x₀ : ℝ) : Set ℂ := {z : ℂ | x₀ - 1 < z.re ∧ z.re < x₀ + 3}

lemma mem_bigStrip {x₀ : ℝ} {z : ℂ} : z ∈ bigStrip x₀ ↔ x₀ - 1 < z.re ∧ z.re < x₀ + 3 :=
  Iff.rfl

/-- `Qreg b₁ b₂` is open. -/
lemma isOpen_Qreg (b₁ b₂ : Option ℂ) : IsOpen (MandelDim.Qreg b₁ b₂) := by
  have h : MandelDim.Qreg b₁ b₂ =
      {z : ℂ | ∀ c ∈ b₁, -|(z - c).im| < (z - c).re} ∩
      {z : ℂ | ∀ c ∈ b₂, (z - c).re < |(z - c).im|} := rfl
  rw [h]
  refine IsOpen.inter ?_ ?_
  · rcases b₁ with _ | a
    · convert isOpen_univ using 1
      ext z; simp
    · have h' : {z : ℂ | ∀ c ∈ (some a : Option ℂ), -|(z - c).im| < (z - c).re} =
          {z : ℂ | -|(z - a).im| < (z - a).re} := by ext z; simp
      rw [h']
      exact isOpen_lt (by fun_prop) (by fun_prop)
  · rcases b₂ with _ | b
    · convert isOpen_univ using 1
      ext z; simp
    · have h' : {z : ℂ | ∀ c ∈ (some b : Option ℂ), (z - c).re < |(z - c).im|} =
          {z : ℂ | (z - b).re < |(z - b).im|} := by ext z; simp
      rw [h']
      exact isOpen_lt (by fun_prop) (by fun_prop)

/-- The big strip lies in `Qreg b₁ b₂`. -/
lemma bigStrip_subset_Qreg (h₁ : ∀ a ∈ b₁, a.re + 1 < x₀)
    (h₂ : ∀ b ∈ b₂, x₀ + 3 < b.re) : bigStrip x₀ ⊆ MandelDim.Qreg b₁ b₂ := by
  intro z hz
  have h := mem_openStrip_Qreg (b₁ := b₁) (b₂ := b₂) h₁ h₂ (x := z.re)
    (by linarith [hz.1]) (by linarith [hz.2]) z.im
  simpa using h

/-- A near-translation is analytic, so `deriv F` is continuous on `Qreg b₁ b₂`. -/
lemma continuousOn_deriv_Qreg (hF : MandelDim.NearTranslationL1 F (MandelDim.Qreg b₁ b₂)) :
    ContinuousOn (deriv F) (MandelDim.Qreg b₁ b₂) := by
  have hopen := isOpen_Qreg b₁ b₂
  have han : AnalyticOnNhd ℂ F (MandelDim.Qreg b₁ b₂) :=
    (Complex.analyticOnNhd_iff_differentiableOn hopen).2 hF.1.1
  exact (han.contDiffOn hopen.uniqueDiffOn).continuousOn_deriv_of_isOpen hopen le_rfl

/-- The displacement `ε = F - id` has derivative `deriv F - 1` at every point of `Qreg`. -/
lemma hasDerivAt_eps (hF : MandelDim.NearTranslationL1 F (MandelDim.Qreg b₁ b₂)) {z : ℂ}
    (hz : z ∈ MandelDim.Qreg b₁ b₂) :
    HasDerivAt (fun w : ℂ => F w - w) (deriv F z - 1) z := by
  have hFz : HasDerivAt F (deriv F z) z := hF.1.1.hasDerivAt ((isOpen_Qreg b₁ b₂).mem_nhds hz)
  exact hFz.sub (hasDerivAt_id z)

/-- Derivative of the displacement along a vertical line. -/
lemma hasDerivAt_eps_vert (hF : MandelDim.NearTranslationL1 F (MandelDim.Qreg b₁ b₂))
    {x η : ℝ} (hreg : ((x : ℂ) + η * Complex.I) ∈ MandelDim.Qreg b₁ b₂) :
    HasDerivAt (fun t : ℝ => F ((x : ℂ) + t * Complex.I) - ((x : ℂ) + t * Complex.I))
      ((deriv F ((x : ℂ) + η * Complex.I) - 1) * Complex.I) η := by
  have hinner : HasDerivAt (fun t : ℝ => (x : ℂ) + t * Complex.I) Complex.I η := by
    have h1 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 η := (hasDerivAt_id η).ofReal_comp
    have h2 : HasDerivAt (fun t : ℝ => (t : ℂ) * Complex.I) (1 * Complex.I) η := h1.mul_const Complex.I
    have h3 : HasDerivAt (fun t : ℝ => (x : ℂ) + (t : ℂ) * Complex.I) (1 * Complex.I) η := h2.const_add (x : ℂ)
    simpa using h3
  exact (hasDerivAt_eps hF hreg).comp η hinner

/-- Derivative of the displacement along a horizontal line. -/
lemma hasDerivAt_eps_horiz (hF : MandelDim.NearTranslationL1 F (MandelDim.Qreg b₁ b₂))
    {x η : ℝ} (hreg : ((x : ℂ) + η * Complex.I) ∈ MandelDim.Qreg b₁ b₂) :
    HasDerivAt (fun t : ℝ => F ((t : ℂ) + η * Complex.I) - ((t : ℂ) + η * Complex.I))
      (deriv F ((x : ℂ) + η * Complex.I) - 1) x := by
  have hinner : HasDerivAt (fun t : ℝ => (t : ℂ) + η * Complex.I) 1 x := by
    have h1 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 x := (hasDerivAt_id x).ofReal_comp
    simpa using h1.add_const (η * Complex.I)
  have hmain := (hasDerivAt_eps hF hreg).comp x hinner
  rw [mul_one] at hmain
  exact hmain

/-- Fundamental theorem of calculus along a vertical segment of the big strip. -/
lemma eps_vertical_ftc (hF : MandelDim.NearTranslationL1 F (MandelDim.Qreg b₁ b₂))
    {x y y' : ℝ} (hseg : ∀ t ∈ Set.uIcc y y', ((x : ℂ) + t * Complex.I) ∈ MandelDim.Qreg b₁ b₂) :
    (F ((x : ℂ) + y' * Complex.I) - ((x : ℂ) + y' * Complex.I)) -
        (F ((x : ℂ) + y * Complex.I) - ((x : ℂ) + y * Complex.I)) =
      ∫ t in y..y', (deriv F ((x : ℂ) + t * Complex.I) - 1) * Complex.I := by
  have hderiv : ∀ t ∈ Set.uIcc y y',
      HasDerivAt (fun s : ℝ => F ((x : ℂ) + s * Complex.I) - ((x : ℂ) + s * Complex.I))
        ((deriv F ((x : ℂ) + t * Complex.I) - 1) * Complex.I) t :=
    fun t ht => hasDerivAt_eps_vert hF (hseg t ht)
  have hcont : ContinuousOn (fun t : ℝ => (deriv F ((x : ℂ) + t * Complex.I) - 1) * Complex.I) (Set.uIcc y y') := by
    have h1 : Continuous fun t : ℝ => (x : ℂ) + t * Complex.I := by fun_prop
    have h2 : ContinuousOn (fun t : ℝ => deriv F ((x : ℂ) + t * Complex.I)) (Set.uIcc y y') :=
      (continuousOn_deriv_Qreg hF).comp h1.continuousOn (fun t _ => hseg t ‹_›)
    exact (h2.sub continuousOn_const).mul continuousOn_const
  exact (intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable).symm

/-- Fundamental theorem of calculus along a horizontal segment of the big strip. -/
lemma eps_horizontal_ftc (hF : MandelDim.NearTranslationL1 F (MandelDim.Qreg b₁ b₂))
    {x x' η : ℝ} (hseg : ∀ ξ ∈ Set.uIcc x x', ((ξ : ℂ) + η * Complex.I) ∈ MandelDim.Qreg b₁ b₂) :
    (F ((x' : ℂ) + η * Complex.I) - ((x' : ℂ) + η * Complex.I)) -
        (F ((x : ℂ) + η * Complex.I) - ((x : ℂ) + η * Complex.I)) =
      ∫ ξ in x..x', (deriv F ((ξ : ℂ) + η * Complex.I) - 1) := by
  have hderiv : ∀ ξ ∈ Set.uIcc x x',
      HasDerivAt (fun s : ℝ => F ((s : ℂ) + η * Complex.I) - ((s : ℂ) + η * Complex.I))
        (deriv F ((ξ : ℂ) + η * Complex.I) - 1) ξ :=
    fun ξ hξ => hasDerivAt_eps_horiz hF (hseg ξ hξ)
  have hcont : ContinuousOn (fun ξ : ℝ => deriv F ((ξ : ℂ) + η * Complex.I) - 1) (Set.uIcc x x') := by
    have h1 : Continuous fun ξ : ℝ => (ξ : ℂ) + η * Complex.I := by fun_prop
    have h2 : ContinuousOn (fun ξ : ℝ => deriv F ((ξ : ℂ) + η * Complex.I)) (Set.uIcc x x') :=
      (continuousOn_deriv_Qreg hF).comp h1.continuousOn (fun ξ _ => hseg ξ ‹_›)
    exact h2.sub continuousOn_const
  exact (intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable).symm

/-! ## Notation-free wrappers used to state the analytic lemmas of `epsDiameterLe` -/

/-- The displacement `ε = F - id` restricted to the vertical line through `x`. -/
noncomputable def vertEps (F : ℂ → ℂ) (x : ℝ) : ℝ → ℂ :=
  fun η => F ((x : ℂ) + η * Complex.I) - ((x : ℂ) + η * Complex.I)

/-- The derivative defect `F' - 1` restricted to the vertical line through `x`. -/
noncomputable def vertDefect (F : ℂ → ℂ) (x : ℝ) : ℝ → ℂ :=
  fun η => deriv F ((x : ℂ) + η * Complex.I) - 1

/-- The value at `+∞` of the displacement along the vertical line through `x`. -/
noncomputable def endTop (F : ℂ → ℂ) (x : ℝ) : ℂ := atTop.limUnder (vertEps F x)

/-- The value at `-∞` of the displacement along the vertical line through `x`. -/
noncomputable def endBot (F : ℂ → ℂ) (x : ℝ) : ℂ := atBot.limUnder (vertEps F x)

/-- The total vertical mass `∫ ‖F' - 1‖ dy` of the derivative defect on the line through `x`. -/
noncomputable def vertMass (F : ℂ → ℂ) (x : ℝ) : ℝ := ∫ η : ℝ, ‖vertDefect F x η‖

/-- The upper tail `∫_{y}^{∞} ‖F' - 1‖` of the vertical mass on the line through `x`. -/
noncomputable def tailTop (F : ℂ → ℂ) (x y : ℝ) : ℝ := ∫ η in Ioi y, ‖vertDefect F x η‖

/-- The lower tail `∫_{-∞}^{y} ‖F' - 1‖` of the vertical mass on the line through `x`. -/
noncomputable def tailBot (F : ℂ → ℂ) (x y : ℝ) : ℝ := ∫ η in Iic y, ‖vertDefect F x η‖

end

end Work.FatouL1
