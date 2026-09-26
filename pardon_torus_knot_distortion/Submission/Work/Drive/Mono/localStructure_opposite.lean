import Mathlib
import Submission.Work.Drive.Mono.OneEvBadAux

/-!
# `Work.Drive.Mono.localStructure_opposite`

Near an *opposite-sign* bad witness of the tilted sweep, the set of bad witnesses is contained in
the image of a `C¹` parametrisation `φ` of (an open piece of) `(τ, σ₂)`-space.

A witness `w = (u,h,τ,q,q')` is:
* `q = Ψ₁(τ,σ₁)` with `care₁ τ q` and `q' = Ψ₂(τ,σ₂)` with `care₂ τ q'`, where `Ψᵢ` are the event
  charts of the two event conditions (`EvChart`), and `σᵢ = ⟪v, par ψ ·⟫`;
* the slab heights satisfy `σ₁ = ⟪v,c⟫+u+η₁h` and `σ₂ = ⟪v,c⟫+u+η₂h`;
* the two sweep heights agree: `sH τ q = sH τ q'`.

Because `η₁+η₂ = 0`, the two slab equations are equivalent to
`u = (σ₁+σ₂)/2 - ⟪v,c⟫`, `h = η₁(σ₁-σ₂)/2`; and the level equation `L₁(τ,σ₁) = L₂(τ,σ₂)` (with
`Lᵢ = evLevel ψ a₀ b₀ Ψᵢ`) has nonvanishing `σ₁`-derivative at the base point (this is the chart
hypothesis `EvChart.hσ`), so by the implicit function theorem it can be solved locally for
`σ₁ = S(τ,σ₂)`.  The parametrisation is
`φ (τ,σ₂) = (u,h,τ, Ψ₁(τ,S(τ,σ₂)), Ψ₂(τ,σ₂))`.
-/

namespace Work.Drive.Mono

noncomputable section

open LeanEval.KnotTheory.PardonDistortion Set Filter
open scoped RealInnerProductSpace ENNReal

set_option maxHeartbeats 1000000

/-! ## Auxiliary maps and lemmas -/

/-- The projection `((τ,σ₂),σ₁) ↦ (τ,σ₁)`. -/
def P13 : ((ℝ × ℝ) × ℝ) →L[ℝ] (ℝ × ℝ) :=
  ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ)).prod
    (ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ)

@[simp] theorem P13_apply (z : (ℝ × ℝ) × ℝ) : P13 z = (z.1.1, z.2) := rfl

/-- The projection `((τ,σ₂),σ₁) ↦ (τ,σ₂)`. -/
def P12 : ((ℝ × ℝ) × ℝ) →L[ℝ] (ℝ × ℝ) := ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ

@[simp] theorem P12_apply (z : (ℝ × ℝ) × ℝ) : P12 z = z.1 := rfl

theorem contDiffAt_comp_P13 {A : ℝ × ℝ → ℝ} {τ σ₁ σ₂ : ℝ} (hA : ContDiffAt ℝ 1 A (τ,σ₁)) :
    ContDiffAt ℝ 1 (fun z : (ℝ × ℝ) × ℝ => A (P13 z)) ((τ,σ₂),σ₁) :=
  ContDiffWithinAt.comp_continuousLinearMap (x := ((τ,σ₂),σ₁)) P13 hA

theorem contDiffAt_comp_P12 {A : ℝ × ℝ → ℝ} {τ σ₁ σ₂ : ℝ} (hA : ContDiffAt ℝ 1 A (τ,σ₂)) :
    ContDiffAt ℝ 1 (fun z : (ℝ × ℝ) × ℝ => A (P12 z)) ((τ,σ₂),σ₁) :=
  ContDiffWithinAt.comp_continuousLinearMap (x := ((τ,σ₂),σ₁)) P12 hA

/-- `evLevel ψ a₀ b₀ Ψ` is `C¹` at every point of the (open) chart domain. -/
theorem contDiffAt_evLevel {ψ : Submission.Diffeo} {a₀ b₀ : R3} (ha : ‖a₀‖ = 1) (hb : ‖b₀‖ = 1)
    (hab : inner ℝ a₀ b₀ = 0) {Ψ : ℝ × ℝ → ℝ × ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (hΨ : ContDiffOn ℝ 1 Ψ V) {x : ℝ × ℝ} (hx : x ∈ V) :
    ContDiffAt ℝ 1 (evLevel ψ a₀ b₀ Ψ) x := by
  have hout : ContDiffAt ℝ 1 (Function.uncurry (sH ψ a₀ b₀)) (x.1, Ψ x) :=
    ((contDiff_sH_uncurry ha hb hab ψ).of_le (by norm_num)).contDiffAt
  have hin : ContDiffAt ℝ 1 (fun y : ℝ × ℝ => (y.1, Ψ y)) x :=
    ContDiffAt.prodMk contDiffAt_fst (hΨ.contDiffAt (hV.mem_nhds hx))
  have hmain := hout.comp x hin
  exact hmain.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => rfl)

theorem continuous_wU : Continuous wU := by unfold wU; fun_prop
theorem continuous_wH : Continuous wH := by unfold wH; fun_prop
theorem continuous_wT : Continuous wT := by unfold wT; fun_prop
theorem continuous_wQ : Continuous wQ := by unfold wQ; fun_prop
theorem continuous_wQ' : Continuous wQ' := by unfold wQ'; fun_prop

theorem continuous_hFn (ψ : Submission.Diffeo) (v : R3) : Continuous (hFn ψ v) :=
  (contDiff_hFn ψ v).continuous

/-- A nonzero continuous linear functional on `ℝ` is invertible. -/
theorem isInvertible_of_ne_zero {g : ℝ →L[ℝ] ℝ} (hg : g ≠ 0) : g.IsInvertible := by
  have hg_apply : ∀ x : ℝ, g x = x * g 1 := fun x => by
    simpa [smul_eq_mul] using map_smul g x (1 : ℝ)
  have hg1 : g 1 ≠ 0 := by
    intro h
    apply hg
    apply ContinuousLinearMap.ext
    intro x
    rw [hg_apply x, h, mul_zero]
    simp
  refine ContinuousLinearMap.IsInvertible.of_inverse (f := g)
    (g := ContinuousLinearMap.toSpanSingleton ℝ (g 1)⁻¹) ?_ ?_
  · apply ContinuousLinearMap.ext
    intro x
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul]
    rw [hg_apply, mul_assoc, inv_mul_cancel₀ hg1, mul_one]
  · apply ContinuousLinearMap.ext
    intro x
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul]
    rw [hg_apply, mul_assoc, mul_inv_cancel₀ hg1, mul_one]

/-- The `u`-coordinate is reconstructed from the two slab coordinates. -/
theorem half_sum_sub {η₁ η₂ h m : ℝ} (hη : η₁ + η₂ = 0) :
    ((m + η₁ * h) + (m + η₂ * h)) / 2 - m = 0 := by
  have hsum : η₁ * h + η₂ * h = 0 := by rw [← add_mul, hη, zero_mul]
  linarith

/-- The `h`-coordinate is reconstructed from the two slab coordinates. -/
theorem eta_mul_sub_half {η₁ η₂ h m : ℝ} (hη : η₁ + η₂ = 0) (hsq : η₁ * η₁ = 1) :
    η₁ * (((m + η₁ * h) - (m + η₂ * h)) / 2) = h := by
  have h2 : η₁ * ((m + η₁ * h - (m + η₂ * h)) / 2) = η₁ * (η₁ * h) := by
    rw [show η₂ = -η₁ by linarith]; ring
  rw [h2]
  calc η₁ * (η₁ * h) = (η₁ * η₁) * h := by ring
    _ = 1 * h := by rw [hsq]
    _ = h := by ring

/-! ## The local structure -/

theorem localStructure_opposite (ψ : Submission.Diffeo) (v a₀ b₀ : LeanEval.KnotTheory.PardonDistortion.R3) (c : LeanEval.KnotTheory.PardonDistortion.R3)
    (ha : ‖a₀‖ = 1) (hb : ‖b₀‖ = 1) (hab : inner ℝ a₀ b₀ = 0)
    (hva : inner ℝ v a₀ = 0) (hvb : inner ℝ v b₀ = 0)
    {care₁ care₂ : ℝ → ℝ × ℝ → Prop} {τ₀ σ₁₀ σ₂₀ : ℝ} {p₁ p₂ : ℝ × ℝ}
    (C₁ : Work.Drive.Mono.EvChart ψ v a₀ b₀ care₁ τ₀ σ₁₀ p₁) (C₂ : Work.Drive.Mono.EvChart ψ v a₀ b₀ care₂ τ₀ σ₂₀ p₂)
    (hc₁ : care₁ τ₀ p₁) (hc₂ : care₂ τ₀ p₂)
    {η₁ η₂ : ℝ} (hη₁ : η₁ = 1 ∨ η₁ = -1) (hη₂ : η₂ = 1 ∨ η₂ = -1) (hη : η₁ + η₂ = 0)
    (hlev : Work.Drive.Mono.sH ψ a₀ b₀ τ₀ p₁ = Work.Drive.Mono.sH ψ a₀ b₀ τ₀ p₂)
    {u₀ h₀ : ℝ}
    (hu₁ : Work.Drive.Mono.hFn ψ v p₁ = (inner ℝ v c + u₀) + η₁ * h₀)
    (hu₂ : Work.Drive.Mono.hFn ψ v p₂ = (inner ℝ v c + u₀) + η₂ * h₀) :
    ∃ (O : Set Work.Drive.Mono.Wit) (V : Set (ℝ × ℝ)) (φ : ℝ × ℝ → Work.Drive.Mono.Wit),
      IsOpen O ∧ Work.Drive.Mono.wit u₀ h₀ τ₀ p₁ p₂ ∈ O ∧ IsOpen V ∧ (τ₀, σ₂₀) ∈ V ∧
      ContDiffOn ℝ 1 φ V ∧
      {w : Work.Drive.Mono.Wit | care₁ (Work.Drive.Mono.wT w) (Work.Drive.Mono.wQ w) ∧ care₂ (Work.Drive.Mono.wT w) (Work.Drive.Mono.wQ' w) ∧
          Work.Drive.Mono.hFn ψ v (Work.Drive.Mono.wQ w) = (inner ℝ v c + Work.Drive.Mono.wU w) + η₁ * Work.Drive.Mono.wH w ∧
          Work.Drive.Mono.hFn ψ v (Work.Drive.Mono.wQ' w) = (inner ℝ v c + Work.Drive.Mono.wU w) + η₂ * Work.Drive.Mono.wH w ∧
          Work.Drive.Mono.sH ψ a₀ b₀ (Work.Drive.Mono.wT w) (Work.Drive.Mono.wQ w) = Work.Drive.Mono.sH ψ a₀ b₀ (Work.Drive.Mono.wT w) (Work.Drive.Mono.wQ' w)} ∩ O ⊆ φ '' V := by
  classical
  -- ## 0. the slab coordinates of the base point
  have hσ₁₀ : σ₁₀ = hFn ψ v p₁ := by
    rw [← C₁.hΨmem]
    exact (C₁.hg (τ₀, σ₁₀) C₁.hVmem).symm
  have hσ₂₀ : σ₂₀ = hFn ψ v p₂ := by
    rw [← C₂.hΨmem]
    exact (C₂.hg (τ₀, σ₂₀) C₂.hVmem).symm
  have hσ₁eq : σ₁₀ = (inner ℝ v c + u₀) + η₁ * h₀ := by rw [hσ₁₀, hu₁]
  have hσ₂eq : σ₂₀ = (inner ℝ v c + u₀) + η₂ * h₀ := by rw [hσ₂₀, hu₂]
  have hη₂' : η₂ = -η₁ := by linarith
  have hη₁sq : η₁ * η₁ = 1 := by rcases hη₁ with h | h <;> rw [h] <;> norm_num
  -- ## 1. the two level functions are `C¹` at the base point
  have hA₁cd : ContDiffAt ℝ 1 (evLevel ψ a₀ b₀ C₁.Ψ) (τ₀, σ₁₀) :=
    contDiffAt_evLevel ha hb hab C₁.hVopen C₁.hΨcd C₁.hVmem
  have hA₂cd : ContDiffAt ℝ 1 (evLevel ψ a₀ b₀ C₂.Ψ) (τ₀, σ₂₀) :=
    contDiffAt_evLevel ha hb hab C₂.hVopen C₂.hΨcd C₂.hVmem
  -- ## 2. the σ₁-derivative of the first level function does not vanish
  have hσ₁ne : (fderiv ℝ (evLevel ψ a₀ b₀ C₁.Ψ) (τ₀, σ₁₀)) (0, 1) ≠ 0 := by
    have h := C₁.hσ
    rwa [fderivWithin_of_isOpen C₁.hVopen C₁.hVmem] at h
  -- ## 3. the implicit equation
  set f : ((ℝ × ℝ) × ℝ) → ℝ :=
    fun z => evLevel ψ a₀ b₀ C₁.Ψ (P13 z) - evLevel ψ a₀ b₀ C₂.Ψ (P12 z) with hfdef
  have hf_apply : ∀ (y : ℝ × ℝ) (σ : ℝ),
      f (y, σ) = evLevel ψ a₀ b₀ C₁.Ψ (y.1, σ) - evLevel ψ a₀ b₀ C₂.Ψ y := by
    intro y σ
    rw [hfdef]
    rfl
  have hfcd : ContDiffAt ℝ 1 f ((τ₀, σ₂₀), σ₁₀) := by
    rw [hfdef]
    exact (contDiffAt_comp_P13 hA₁cd).sub (contDiffAt_comp_P12 hA₂cd)
  have hfu : f ((τ₀, σ₂₀), σ₁₀) = 0 := by
    rw [hf_apply]
    change sH ψ a₀ b₀ τ₀ (C₁.Ψ (τ₀, σ₁₀)) - sH ψ a₀ b₀ τ₀ (C₂.Ψ (τ₀, σ₂₀)) = 0
    rw [C₁.hΨmem, C₂.hΨmem]
    exact sub_eq_zero.mpr hlev
  -- ## 4. the σ₁-partial derivative of the implicit equation
  have hderivval : (fderiv ℝ f ((τ₀, σ₂₀), σ₁₀))
        (ContinuousLinearMap.inr ℝ (ℝ × ℝ) ℝ 1)
      = (fderiv ℝ (evLevel ψ a₀ b₀ C₁.Ψ) (τ₀, σ₁₀)) (0, 1) := by
    have hd₁ : HasFDerivAt (fun z : (ℝ × ℝ) × ℝ => evLevel ψ a₀ b₀ C₁.Ψ (P13 z))
        ((fderiv ℝ (evLevel ψ a₀ b₀ C₁.Ψ) (τ₀, σ₁₀)) ∘SL P13) ((τ₀, σ₂₀), σ₁₀) := by
      have h1 : HasFDerivAt (evLevel ψ a₀ b₀ C₁.Ψ)
          (fderiv ℝ (evLevel ψ a₀ b₀ C₁.Ψ) (τ₀, σ₁₀)) (τ₀, σ₁₀) :=
        (hA₁cd.differentiableAt (by norm_num)).hasFDerivAt
      have h2 := h1.comp (((τ₀, σ₂₀), σ₁₀)) P13.hasFDerivAt
      simpa [Function.comp_def] using h2
    have hd₂ : HasFDerivAt (fun z : (ℝ × ℝ) × ℝ => evLevel ψ a₀ b₀ C₂.Ψ (P12 z))
        ((fderiv ℝ (evLevel ψ a₀ b₀ C₂.Ψ) (τ₀, σ₂₀)) ∘SL P12) ((τ₀, σ₂₀), σ₁₀) := by
      have h1 : HasFDerivAt (evLevel ψ a₀ b₀ C₂.Ψ)
          (fderiv ℝ (evLevel ψ a₀ b₀ C₂.Ψ) (τ₀, σ₂₀)) (τ₀, σ₂₀) :=
        (hA₂cd.differentiableAt (by norm_num)).hasFDerivAt
      have h2 := h1.comp (((τ₀, σ₂₀), σ₁₀)) P12.hasFDerivAt
      simpa [Function.comp_def] using h2
    have hfd : fderiv ℝ f ((τ₀, σ₂₀), σ₁₀)
        = ((fderiv ℝ (evLevel ψ a₀ b₀ C₁.Ψ) (τ₀, σ₁₀)) ∘SL P13)
          - ((fderiv ℝ (evLevel ψ a₀ b₀ C₂.Ψ) (τ₀, σ₂₀)) ∘SL P12) := by
      rw [hfdef]
      exact (hd₁.sub hd₂).fderiv
    rw [hfd]
    simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]
  have hne : ((fderiv ℝ f ((τ₀, σ₂₀), σ₁₀)) ∘SL ContinuousLinearMap.inr ℝ (ℝ × ℝ) ℝ) ≠ 0 := by
    intro h0
    have h1 := congrArg (fun T : ℝ →L[ℝ] ℝ => T 1) h0
    simp only [ContinuousLinearMap.comp_apply, zero_apply] at h1
    rw [hderivval] at h1
    exact hσ₁ne h1
  have hinv : ((fderiv ℝ f ((τ₀, σ₂₀), σ₁₀)) ∘SL ContinuousLinearMap.inr ℝ (ℝ × ℝ) ℝ).IsInvertible :=
    isInvertible_of_ne_zero hne
  -- ## 5. the implicit function
  set ψi : ℝ × ℝ → ℝ := hfcd.implicitFunction (by norm_num) hinv with hψidef
  have hψi_cd : ContDiffAt ℝ 1 ψi (τ₀, σ₂₀) := by
    rw [hψidef]
    exact hfcd.contDiffAt_implicitFunction (by norm_num) hinv
  have hψi_self : ψi (τ₀, σ₂₀) = σ₁₀ := by
    rw [hψidef]
    exact hfcd.implicitFunction_apply_self (by norm_num) hinv
  have hψi_iff : ∀ᶠ x : (ℝ × ℝ) × ℝ in nhds ((τ₀, σ₂₀), σ₁₀),
      f x = f ((τ₀, σ₂₀), σ₁₀) ↔ ψi x.1 = x.2 := by
    rw [hψidef]
    exact hfcd.eventually_apply_eq_iff_implicitFunction (by norm_num) hinv
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hψi_iff
  have hiff : ∀ x : (ℝ × ℝ) × ℝ, dist x (((τ₀, σ₂₀), σ₁₀) : (ℝ × ℝ) × ℝ) < ε →
      (f x = f ((τ₀, σ₂₀), σ₁₀) ↔ ψi x.1 = x.2) := fun x hx =>
    hball (Metric.mem_ball.mpr hx)
  -- ## 6. an open neighbourhood of `(τ₀,σ₂₀)` on which `ψi` is `C¹` and lands in the charts
  have hV₀ex : ∃ V₀ ∈ nhds (τ₀, σ₂₀), ContDiffOn ℝ 1 ψi V₀ := by
    have h := (contDiffWithinAt_iff_contDiffOn_nhds (𝕜 := ℝ) (f := ψi) (s := Set.univ)
      (x := (τ₀, σ₂₀)) (n := 1) (by norm_num)).mp hψi_cd
    simpa using h
  obtain ⟨V₀, hV₀mem, hV₀cd⟩ := hV₀ex
  have hV₀mem' : V₀ ∈ nhds (τ₀, σ₂₀) := by simpa using hV₀mem
  obtain ⟨Vc, hVcsub, hVcopen, hVcmem⟩ := mem_nhds_iff.mp hV₀mem'
  have hVccd : ContDiffOn ℝ 1 ψi Vc := hV₀cd.mono hVcsub
  have hψi_cont : ContinuousAt ψi (τ₀, σ₂₀) :=
    (hψi_cd.differentiableAt (by norm_num)).continuousAt
  have hcont₃ : ContinuousAt (fun y : ℝ × ℝ => (y.1, ψi y)) (τ₀, σ₂₀) :=
    ContinuousAt.prodMk continuousAt_fst hψi_cont
  have hS₂ : (fun y : ℝ × ℝ => (y.1, ψi y)) ⁻¹' C₁.V ∈ nhds (τ₀, σ₂₀) :=
    hcont₃.preimage_mem_nhds (by simpa [hψi_self] using (C₁.hVopen.mem_nhds C₁.hVmem))
  have hS₃ : C₂.V ∈ nhds (τ₀, σ₂₀) := C₂.hVopen.mem_nhds C₂.hVmem
  have hSmem : Vc ∩ ((fun y : ℝ × ℝ => (y.1, ψi y)) ⁻¹' C₁.V) ∩ C₂.V ∈ nhds (τ₀, σ₂₀) :=
    Filter.inter_mem (Filter.inter_mem (hVcopen.mem_nhds hVcmem) hS₂) hS₃
  obtain ⟨V, hVsub, hVopen, hVmem⟩ := mem_nhds_iff.mp hSmem
  have hVcd : ContDiffOn ℝ 1 ψi V := hVccd.mono (fun y hy => (hVsub hy).1.1)
  have hVsub₂ : ∀ y ∈ V, (y.1, ψi y) ∈ C₁.V := fun y hy => (hVsub hy).1.2
  have hVsub₃ : ∀ y ∈ V, y ∈ C₂.V := fun y hy => (hVsub hy).2
  -- ## 7. the parametrisation
  set φ : ℝ × ℝ → Wit := fun y =>
    wit ((ψi y + y.2) / 2 - inner ℝ v c) (η₁ * ((ψi y - y.2) / 2)) y.1
      (C₁.Ψ (y.1, ψi y)) (C₂.Ψ (y.1, y.2)) with hφdef
  have hφcd : ContDiffOn ℝ 1 φ V := by
    rw [hφdef]
    have hf₁ : ContDiffOn ℝ 1 (fun y : ℝ × ℝ => (ψi y + y.2) / 2 - inner ℝ v c) V :=
      ((hVcd.add contDiff_snd.contDiffOn).div_const 2).sub contDiffOn_const
    have hf₂ : ContDiffOn ℝ 1 (fun y : ℝ × ℝ => η₁ * ((ψi y - y.2) / 2)) V :=
      contDiffOn_const.mul ((hVcd.sub contDiff_snd.contDiffOn).div_const 2)
    have hf₃ : ContDiffOn ℝ 1 (fun y : ℝ × ℝ => y.1) V := contDiff_fst.contDiffOn
    have hf₄ : ContDiffOn ℝ 1 (fun y : ℝ × ℝ => C₁.Ψ (y.1, ψi y)) V :=
      C₁.hΨcd.comp (contDiff_fst.contDiffOn.prodMk hVcd) hVsub₂
    have hf₅ : ContDiffOn ℝ 1 (fun y : ℝ × ℝ => C₂.Ψ (y.1, y.2)) V :=
      (C₂.hΨcd.mono hVsub₃).congr (fun y _ => by simp)
    exact hf₁.prodMk (hf₂.prodMk (hf₃.prodMk (hf₄.prodMk hf₅)))
  -- ## 8. the open set of witnesses
  set O : Set Wit :=
    (wQ ⁻¹' C₁.U) ∩ (wQ' ⁻¹' C₂.U) ∩
    ((fun w : Wit => (wT w, hFn ψ v (wQ w))) ⁻¹' C₁.V) ∩
    ((fun w : Wit => (wT w, hFn ψ v (wQ' w))) ⁻¹' C₂.V) ∩
    ((fun w : Wit => (wT w, hFn ψ v (wQ' w))) ⁻¹' V) ∩
    {w : Wit | dist (wT w, hFn ψ v (wQ' w)) (τ₀, σ₂₀) < ε / 2} ∩
    {w : Wit | dist (hFn ψ v (wQ w)) σ₁₀ < ε / 2} with hOdef
  have hOopen : IsOpen O := by
    have hcont₁ : Continuous (fun w : Wit => (wT w, hFn ψ v (wQ w))) :=
      continuous_wT.prodMk ((continuous_hFn ψ v).comp continuous_wQ)
    have hcont₂ : Continuous (fun w : Wit => (wT w, hFn ψ v (wQ' w))) :=
      continuous_wT.prodMk ((continuous_hFn ψ v).comp continuous_wQ')
    have hcont₄ : Continuous (fun w : Wit => dist (wT w, hFn ψ v (wQ' w)) (τ₀, σ₂₀)) :=
      continuous_dist.comp (hcont₂.prodMk continuous_const)
    have hcont₅ : Continuous (fun w : Wit => dist (hFn ψ v (wQ w)) σ₁₀) :=
      continuous_dist.comp (((continuous_hFn ψ v).comp continuous_wQ).prodMk continuous_const)
    have h1 : IsOpen (wQ ⁻¹' C₁.U) := C₁.hUopen.preimage continuous_wQ
    have h2 : IsOpen (wQ' ⁻¹' C₂.U) := C₂.hUopen.preimage continuous_wQ'
    have h3 : IsOpen ((fun w : Wit => (wT w, hFn ψ v (wQ w))) ⁻¹' C₁.V) :=
      C₁.hVopen.preimage hcont₁
    have h4 : IsOpen ((fun w : Wit => (wT w, hFn ψ v (wQ' w))) ⁻¹' C₂.V) :=
      C₂.hVopen.preimage hcont₂
    have h5 : IsOpen ((fun w : Wit => (wT w, hFn ψ v (wQ' w))) ⁻¹' V) :=
      hVopen.preimage hcont₂
    have h6 : IsOpen {w : Wit | dist (wT w, hFn ψ v (wQ' w)) (τ₀, σ₂₀) < ε / 2} :=
      isOpen_Iio.preimage hcont₄
    have h7 : IsOpen {w : Wit | dist (hFn ψ v (wQ w)) σ₁₀ < ε / 2} :=
      isOpen_Iio.preimage hcont₅
    rw [hOdef]
    exact (((((h1.inter h2).inter h3).inter h4).inter h5).inter h6).inter h7
  have hwit_mem : wit u₀ h₀ τ₀ p₁ p₂ ∈ O := by
    rw [hOdef]
    simp only [wQ_wit, wQ'_wit, wT_wit, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage]
    refine ⟨⟨⟨⟨⟨⟨C₁.hUmem, C₂.hUmem⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
    · have hpair : (τ₀, hFn ψ v p₁) = (τ₀, σ₁₀) := by rw [hσ₁₀]
      rw [hpair]; exact C₁.hVmem
    · have hpair : (τ₀, hFn ψ v p₂) = (τ₀, σ₂₀) := by rw [hσ₂₀]
      rw [hpair]; exact C₂.hVmem
    · have hpair : (τ₀, hFn ψ v p₂) = (τ₀, σ₂₀) := by rw [hσ₂₀]
      rw [hpair]; exact hVmem
    · rw [hσ₂₀, dist_self]; linarith
    · rw [hσ₁₀, dist_self]; linarith
  -- ## 9. the inclusion
  refine ⟨O, V, φ, hOopen, hwit_mem, hVopen, hVmem, hφcd, ?_⟩
  intro w hw
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq] at hw
  obtain ⟨⟨hc₁w, hc₂w, hh₁w, hh₂w, hlevw⟩, hwO⟩ := hw
  rw [hOdef] at hwO
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage] at hwO
  obtain ⟨⟨⟨⟨⟨⟨hQmem, hQ'mem⟩, hV₁mem⟩, hV₂mem⟩, hVmem'⟩, hdist₂⟩, hdist₁⟩ := hwO
  -- the two endpoint points are the chart values
  have hq : wQ w = C₁.Ψ (wT w, hFn ψ v (wQ w)) :=
    C₁.huniq (wT w) (hFn ψ v (wQ w)) (wQ w) hV₁mem hQmem hc₁w rfl
  have hq' : wQ' w = C₂.Ψ (wT w, hFn ψ v (wQ' w)) :=
    C₂.huniq (wT w) (hFn ψ v (wQ' w)) (wQ' w) hV₂mem hQ'mem hc₂w rfl
  -- the level equation
  have hlevw' : evLevel ψ a₀ b₀ C₁.Ψ (wT w, hFn ψ v (wQ w))
      = evLevel ψ a₀ b₀ C₂.Ψ (wT w, hFn ψ v (wQ' w)) := by
    change sH ψ a₀ b₀ (wT w) (C₁.Ψ (wT w, hFn ψ v (wQ w)))
      = sH ψ a₀ b₀ (wT w) (C₂.Ψ (wT w, hFn ψ v (wQ' w)))
    rw [← hq, ← hq']
    exact hlevw
  -- the implicit equation vanishes at the witness
  have hfval : f ((wT w, hFn ψ v (wQ' w)), hFn ψ v (wQ w)) = 0 := by
    rw [hf_apply]
    change evLevel ψ a₀ b₀ C₁.Ψ (wT w, hFn ψ v (wQ w))
      - evLevel ψ a₀ b₀ C₂.Ψ (wT w, hFn ψ v (wQ' w)) = 0
    rw [hlevw']
    ring
  -- the witness is close to the base point, so the implicit function applies
  have hclose : dist (((wT w, hFn ψ v (wQ' w)), hFn ψ v (wQ w)) : (ℝ × ℝ) × ℝ)
      (((τ₀, σ₂₀), σ₁₀) : (ℝ × ℝ) × ℝ) < ε := by
    have hA : dist (wT w, hFn ψ v (wQ' w)) (τ₀, σ₂₀) < ε := lt_of_lt_of_le hdist₂ (by linarith)
    have hB : dist (hFn ψ v (wQ w)) σ₁₀ < ε := lt_of_lt_of_le hdist₁ (by linarith)
    calc dist (((wT w, hFn ψ v (wQ' w)), hFn ψ v (wQ w)) : (ℝ × ℝ) × ℝ)
          (((τ₀, σ₂₀), σ₁₀) : (ℝ × ℝ) × ℝ)
        = max (dist (wT w, hFn ψ v (wQ' w)) (τ₀, σ₂₀)) (dist (hFn ψ v (wQ w)) σ₁₀) :=
          Prod.dist_eq
      _ < ε := max_lt hA hB
  have hψival : ψi (wT w, hFn ψ v (wQ' w)) = hFn ψ v (wQ w) :=
    (hiff (((wT w, hFn ψ v (wQ' w)), hFn ψ v (wQ w))) hclose).mp (by rw [hfval, hfu])
  -- the parameters are reconstructed
  have hu : (ψi (wT w, hFn ψ v (wQ' w)) + hFn ψ v (wQ' w)) / 2 - inner ℝ v c = wU w := by
    rw [hψival, hh₁w, hh₂w]
    linarith [half_sum_sub (η₁ := η₁) (η₂ := η₂) (h := wH w)
      (m := inner ℝ v c + wU w) hη]
  have hh : η₁ * ((ψi (wT w, hFn ψ v (wQ' w)) - hFn ψ v (wQ' w)) / 2) = wH w := by
    rw [hψival, hh₁w, hh₂w]
    exact eta_mul_sub_half (η₁ := η₁) (η₂ := η₂) (h := wH w)
      (m := inner ℝ v c + wU w) hη hη₁sq
  have hqa : C₁.Ψ (wT w, ψi (wT w, hFn ψ v (wQ' w))) = wQ w := by rw [hψival, ← hq]
  have hqb : C₂.Ψ (wT w, hFn ψ v (wQ' w)) = wQ' w := by rw [← hq']
  have hφval : φ (wT w, hFn ψ v (wQ' w)) = w := by
    have hφ1 : φ (wT w, hFn ψ v (wQ' w))
        = wit ((ψi (wT w, hFn ψ v (wQ' w)) + hFn ψ v (wQ' w)) / 2 - inner ℝ v c)
          (η₁ * ((ψi (wT w, hFn ψ v (wQ' w)) - hFn ψ v (wQ' w)) / 2)) (wT w)
          (C₁.Ψ (wT w, ψi (wT w, hFn ψ v (wQ' w)))) (C₂.Ψ (wT w, hFn ψ v (wQ' w))) := by
      rw [hφdef]
    rw [hφ1, hqa, hqb, hu, hh]
    obtain ⟨uu, hhh, tt, qq, qq'⟩ := w
    simp only [wit, wU, wH, wT, wQ, wQ']
  exact ⟨(wT w, hFn ψ v (wQ' w)), hVmem', hφval⟩

end

end Work.Drive.Mono
