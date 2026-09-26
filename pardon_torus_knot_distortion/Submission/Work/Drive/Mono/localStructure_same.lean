import Mathlib
import Submission.Work.Drive.Mono.OneEvBadAux
import Submission.Work.Drive.Mono.Band.BadFaceDefs
import Submission.Work.Drive.Mono.dirOfBasic

/-!
# `Work.Drive.Mono.localStructure_same`

Near a *same-sign* bad witness of the tilted sweep, the set of bad witnesses is contained in the
image of a `C¹` parametrisation `φ` of (an open piece of) `(σ, u)`-space.

A witness `w = (u,h,τ,q,q')` is:
* `q = Ψ₁(τ,σ)` with `care₁ τ q` and `q' = Ψ₂(τ,σ)` with `care₂ τ q'`, where `Ψᵢ` are the event
  charts of the two event conditions (`EvChart`), both read at the *same* slab coordinate
  `σ = ⟪v, par ψ ·⟫` (the "same sign" case: the two slab equations
  `σ = (⟪v,c⟫+u) + ηᵢ h` with `η₁ = η₂ = η` force `σ₁ = σ₂`);
* therefore `h = (σ - ⟪v,c⟫ - u)/η` and the two points are determined by `(τ,σ)`, while `u` is free;
* the two sweep heights agree: `sH τ q = sH τ q'`.

The level equation `L₁(τ,σ) = L₂(τ,σ)` (with `Lᵢ = evLevel ψ a₀ b₀ Ψᵢ`) is solved locally for `τ`,
which is legitimate because the envelope `τ`-derivative
`⟪deriv dirOf τ₀, par ψ p₁ - par ψ p₂⟫` does not vanish: the difference `x = par ψ p₁ - par ψ p₂`
is nonzero, orthogonal to `v` (equal slab coordinates) and to `dirOf τ₀` (equal sweep heights), and
for an orthonormal pair `(a₀,b₀)` with `v ⊥ a₀, v ⊥ b₀` this forces `x` to pair nontrivially with
the envelope derivative (`Work.Drive.Mono.dirOfBasic`).

The parametrisation is `φ (σ,u) = (u, (σ-⟪v,c⟫-u)/η, S(σ), Ψ₁(S(σ),σ), Ψ₂(S(σ),σ))` where
`S` is the implicit function.
-/

open LeanEval.KnotTheory.PardonDistortion Set Filter
open scoped RealInnerProductSpace ENNReal

namespace Work.Drive.Mono

noncomputable section

set_option linter.unusedVariables false

set_option maxHeartbeats 1000000


/-! ## Linear algebra -/

/-- If a nonzero `v` is orthogonal to the orthonormal pair `a₀, b₀`, then a vector orthogonal to
`a₀`, `b₀` and `v` is zero. -/
theorem lss_eq_zero_of_inner_eq_zero_orthonormal_pair {a₀ b₀ v X : R3}
    (ha : ‖a₀‖ = 1) (hb : ‖b₀‖ = 1) (hab : inner ℝ a₀ b₀ = 0)
    (hva : inner ℝ v a₀ = 0) (hvb : inner ℝ v b₀ = 0) (hv : v ≠ 0)
    (h1 : inner ℝ X a₀ = 0) (h2 : inner ℝ X b₀ = 0) (h3 : inner ℝ X v = 0) : X = 0 := by
  have hz : ‖Work.Drive.Generic.crossE a₀ b₀‖ = 1 :=
    Work.Drive.Mono.Band.norm_crossE ha hb hab
  have hXc : X = inner ℝ (Work.Drive.Generic.crossE a₀ b₀) X
      • Work.Drive.Generic.crossE a₀ b₀ := by
    have h := Work.Drive.Mono.Band.crossExpansion (v := a₀) (n := b₀) (X := X) ha hb hab
    rw [real_inner_comm X a₀, h1, real_inner_comm X b₀, h2] at h
    simpa using h.symm
  have hvc : v = inner ℝ (Work.Drive.Generic.crossE a₀ b₀) v
      • Work.Drive.Generic.crossE a₀ b₀ := by
    have h := Work.Drive.Mono.Band.crossExpansion (v := a₀) (n := b₀) (X := v) ha hb hab
    rw [real_inner_comm v a₀, hva, real_inner_comm v b₀, hvb] at h
    simpa using h.symm
  have hzv : inner ℝ (Work.Drive.Generic.crossE a₀ b₀) v ≠ 0 := by
    intro h
    rw [hvc, h, zero_smul] at hv
    exact hv rfl
  have hzX : inner ℝ (Work.Drive.Generic.crossE a₀ b₀) X = 0 := by
    have h3' := h3
    rw [hXc, hvc] at h3'
    rw [real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq, hz, one_pow,
      mul_one] at h3'
    rcases mul_eq_zero.mp h3' with h | h
    · exact h
    · exact absurd h hzv
  rw [hXc, hzX, zero_smul]

/-- **The envelope derivative at a point.**  If `X ≠ 0` is orthogonal to `v` and to `dirOf τ a₀ b₀`,
then the derivative of `dirOf` at `τ` pairs nontrivially with `X`. -/
theorem lss_deriv_dirOf_inner_ne_zero {a₀ b₀ v X : R3} (τ : ℝ)
    (ha : ‖a₀‖ = 1) (hb : ‖b₀‖ = 1) (hab : inner ℝ a₀ b₀ = 0)
    (hva : inner ℝ v a₀ = 0) (hvb : inner ℝ v b₀ = 0) (hv : v ≠ 0)
    (hX : X ≠ 0) (hXv : inner ℝ X v = 0)
    (hXd : inner ℝ X (Work.Drive.Mono.Band.dirOf τ a₀ b₀) = 0) :
    inner ℝ X (deriv (fun s : ℝ => Work.Drive.Mono.Band.dirOf s a₀ b₀) τ) ≠ 0 := by
  obtain ⟨-, -, hbasic, -⟩ := dirOfBasic (a₀ := a₀) (b₀ := b₀) ha hb hab
  intro hw0
  obtain ⟨ha0, hb0⟩ := hbasic τ X hXd hw0
  exact hX (lss_eq_zero_of_inner_eq_zero_orthonormal_pair ha hb hab hva hvb hv ha0 hb0 hXv)

/-! ## Generic chart helpers -/

/-- `evLevel` is `C¹` at every point of an open chart domain. -/
theorem lss_evLevel_cd {ψ : Submission.Diffeo} {a₀ b₀ : R3} (ha : ‖a₀‖ = 1) (hb : ‖b₀‖ = 1)
    (hab : inner ℝ a₀ b₀ = 0) {Ψ : ℝ × ℝ → ℝ × ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (hΨ : ContDiffOn ℝ 1 Ψ V) {x : ℝ × ℝ} (hx : x ∈ V) :
    ContDiffAt ℝ 1 (evLevel ψ a₀ b₀ Ψ) x := by
  have hout : ContDiffAt ℝ 1 (Function.uncurry (sH ψ a₀ b₀)) (x.1, Ψ x) :=
    ((contDiff_sH_uncurry ha hb hab ψ).of_le (by norm_num)).contDiffAt
  have hin : ContDiffAt ℝ 1 (fun y : ℝ × ℝ => (y.1, Ψ y)) x :=
    ContDiffAt.prodMk contDiffAt_fst (hΨ.contDiffAt (hV.mem_nhds hx))
  exact (hout.comp x hin).congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => rfl)

/-- A nonzero continuous linear functional on `ℝ` is invertible. -/
theorem lss_isInvertible_of_ne_zero {g : ℝ →L[ℝ] ℝ} (hg : g ≠ 0) : g.IsInvertible := by
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

theorem lss_continuous_wU : Continuous wU := by unfold wU; fun_prop
theorem lss_continuous_wH : Continuous wH := by unfold wH; fun_prop
theorem lss_continuous_wT : Continuous wT := by unfold wT; fun_prop
theorem lss_continuous_wQ : Continuous wQ := by unfold wQ; fun_prop
theorem lss_continuous_wQ' : Continuous wQ' := by unfold wQ'; fun_prop
theorem lss_continuous_hFn (ψ : Submission.Diffeo) (v : R3) : Continuous (hFn ψ v) :=
  (contDiff_hFn ψ v).continuous

/-- The witness rebuilt from its coordinates is itself. -/
theorem lss_wit_eta (w : Wit) : wit (wU w) (wH w) (wT w) (wQ w) (wQ' w) = w := by
  obtain ⟨uu, hhh, tt, qq, qq'⟩ := w
  rfl

/-! ## The local structure at a same-sign witness -/

theorem localStructure_same (ψ : Submission.Diffeo) (v a₀ b₀ : LeanEval.KnotTheory.PardonDistortion.R3) (c : LeanEval.KnotTheory.PardonDistortion.R3)
    (ha : ‖a₀‖ = 1) (hb : ‖b₀‖ = 1) (hab : inner ℝ a₀ b₀ = 0)
    (hva : inner ℝ v a₀ = 0) (hvb : inner ℝ v b₀ = 0)
    {care₁ care₂ : ℝ → ℝ × ℝ → Prop} {τ₀ σ₀ : ℝ} {p₁ p₂ : ℝ × ℝ}
    (C₁ : Work.Drive.Mono.EvChart ψ v a₀ b₀ care₁ τ₀ σ₀ p₁) (C₂ : Work.Drive.Mono.EvChart ψ v a₀ b₀ care₂ τ₀ σ₀ p₂)
    (hc₁ : care₁ τ₀ p₁) (hc₂ : care₂ τ₀ p₂)
    {η : ℝ} (hη : η = 1 ∨ η = -1)
    (hlev : Work.Drive.Mono.sH ψ a₀ b₀ τ₀ p₁ = Work.Drive.Mono.sH ψ a₀ b₀ τ₀ p₂)
    (hne : Work.BoxShrink.Pinch.par ψ p₁ ≠ Work.BoxShrink.Pinch.par ψ p₂)
    (hσ₀ : σ₀ = Work.Drive.Mono.hFn ψ v p₁) (hσ₀' : σ₀ = Work.Drive.Mono.hFn ψ v p₂)
    {u₀ h₀ : ℝ}
    (hu₁ : Work.Drive.Mono.hFn ψ v p₁ = (inner ℝ v c + u₀) + η * h₀)
    (hu₂ : Work.Drive.Mono.hFn ψ v p₂ = (inner ℝ v c + u₀) + η * h₀) :
    ∃ (O : Set Work.Drive.Mono.Wit) (V : Set (ℝ × ℝ)) (φ : ℝ × ℝ → Work.Drive.Mono.Wit),
      IsOpen O ∧ Work.Drive.Mono.wit u₀ h₀ τ₀ p₁ p₂ ∈ O ∧ IsOpen V ∧ (σ₀, u₀) ∈ V ∧
      ContDiffOn ℝ 1 φ V ∧
      {w : Work.Drive.Mono.Wit | care₁ (Work.Drive.Mono.wT w) (Work.Drive.Mono.wQ w) ∧ care₂ (Work.Drive.Mono.wT w) (Work.Drive.Mono.wQ' w) ∧
          Work.Drive.Mono.hFn ψ v (Work.Drive.Mono.wQ w) = Work.Drive.Mono.hFn ψ v (Work.Drive.Mono.wQ' w) ∧
          Work.Drive.Mono.hFn ψ v (Work.Drive.Mono.wQ w) = (inner ℝ v c + Work.Drive.Mono.wU w) + η * Work.Drive.Mono.wH w ∧
          Work.Drive.Mono.sH ψ a₀ b₀ (Work.Drive.Mono.wT w) (Work.Drive.Mono.wQ w) = Work.Drive.Mono.sH ψ a₀ b₀ (Work.Drive.Mono.wT w) (Work.Drive.Mono.wQ' w)} ∩ O ⊆ φ '' V := by
  classical
  have hηne : η ≠ 0 := by rcases hη with h | h <;> rw [h] <;> norm_num
  -- (0) the slab coordinate is nontrivial: `v ≠ 0`
  have hvne : v ≠ 0 := by
    intro hv0
    subst hv0
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (C₁.hVopen.mem_nhds C₁.hVmem)
    have h1 : σ₀ = 0 := by
      have hz := C₁.hg (τ₀, σ₀) (hball (by simp [Metric.mem_ball, hε]))
      simp only [hFn_apply, inner_zero_left] at hz
      exact hz.symm
    have h2 : σ₀ + ε / 2 = 0 := by
      have hz : hFn ψ 0 (C₁.Ψ (τ₀, σ₀ + ε / 2)) = σ₀ + ε / 2 := by
        have h := C₁.hg (τ₀, σ₀ + ε / 2) ?_
        · simpa using h
        · refine hball ?_
          rw [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq]
          simp only [sub_self, abs_zero]
          rw [add_sub_cancel_left, abs_of_pos (by linarith : (0:ℝ) < ε / 2),
            max_eq_right (by linarith : (0:ℝ) ≤ ε / 2)]
          linarith
      simp only [hFn_apply, inner_zero_left] at hz
      exact hz.symm
    linarith
  -- (1) the difference of the two parameter points
  have hx_v : inner ℝ v (Work.BoxShrink.Pinch.par ψ p₁ - Work.BoxShrink.Pinch.par ψ p₂) = 0 := by
    have h₁ : hFn ψ v p₁ = hFn ψ v p₂ := by rw [← hσ₀, hσ₀']
    rw [inner_sub_right]
    change hFn ψ v p₁ - hFn ψ v p₂ = 0
    rw [h₁, sub_self]
  have hx_d : inner ℝ (Work.Drive.Mono.Band.dirOf τ₀ a₀ b₀)
      (Work.BoxShrink.Pinch.par ψ p₁ - Work.BoxShrink.Pinch.par ψ p₂) = 0 := by
    rw [inner_sub_right]
    change sH ψ a₀ b₀ τ₀ p₁ - sH ψ a₀ b₀ τ₀ p₂ = 0
    rw [hlev, sub_self]
  have hxne : Work.BoxShrink.Pinch.par ψ p₁ - Work.BoxShrink.Pinch.par ψ p₂ ≠ 0 :=
    sub_ne_zero.mpr hne
  have hxv : inner ℝ (Work.BoxShrink.Pinch.par ψ p₁ - Work.BoxShrink.Pinch.par ψ p₂) v = 0 := by
    rw [real_inner_comm v (Work.BoxShrink.Pinch.par ψ p₁ - Work.BoxShrink.Pinch.par ψ p₂)]
    exact hx_v
  have hxd : inner ℝ (Work.BoxShrink.Pinch.par ψ p₁ - Work.BoxShrink.Pinch.par ψ p₂)
      (Work.Drive.Mono.Band.dirOf τ₀ a₀ b₀) = 0 := by
    rw [real_inner_comm (Work.Drive.Mono.Band.dirOf τ₀ a₀ b₀)
      (Work.BoxShrink.Pinch.par ψ p₁ - Work.BoxShrink.Pinch.par ψ p₂)]
    exact hx_d
  -- (2) the envelope derivative at `τ₀` is nonzero on the difference
  have hwx : inner ℝ (Work.BoxShrink.Pinch.par ψ p₁ - Work.BoxShrink.Pinch.par ψ p₂)
      (deriv (fun s : ℝ => Work.Drive.Mono.Band.dirOf s a₀ b₀) τ₀) ≠ 0 :=
    lss_deriv_dirOf_inner_ne_zero τ₀ ha hb hab hva hvb hvne hxne hxv hxd
  have hwx' : inner ℝ (deriv (fun s : ℝ => Work.Drive.Mono.Band.dirOf s a₀ b₀) τ₀)
      (Work.BoxShrink.Pinch.par ψ p₁ - Work.BoxShrink.Pinch.par ψ p₂) ≠ 0 := by
    rw [real_inner_comm (Work.BoxShrink.Pinch.par ψ p₁ - Work.BoxShrink.Pinch.par ψ p₂)
      (deriv (fun s : ℝ => Work.Drive.Mono.Band.dirOf s a₀ b₀) τ₀)]
    exact hwx
  -- (3) the level functions are `C¹` at the base point
  have hA₁cd : ContDiffAt ℝ 1 (evLevel ψ a₀ b₀ C₁.Ψ) (τ₀, σ₀) :=
    lss_evLevel_cd ha hb hab C₁.hVopen C₁.hΨcd C₁.hVmem
  have hA₂cd : ContDiffAt ℝ 1 (evLevel ψ a₀ b₀ C₂.Ψ) (τ₀, σ₀) :=
    lss_evLevel_cd ha hb hab C₂.hVopen C₂.hΨcd C₂.hVmem
  -- (4) the swap `(σ,τ) ↦ (τ,σ)`
  set P21 : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).prod (ContinuousLinearMap.fst ℝ ℝ ℝ) with hP21def
  have hP21 : ∀ z : ℝ × ℝ, P21 z = (z.2, z.1) := by
    intro z
    rw [hP21def, ContinuousLinearMap.prod_apply]
    rfl
  have hP21₀ : P21 (0, 1) = ((1 : ℝ), (0 : ℝ)) := by
    simp [hP21]
  -- (5) the implicit equation
  set f : ℝ × ℝ → ℝ :=
    fun z => evLevel ψ a₀ b₀ C₁.Ψ (P21 z) - evLevel ψ a₀ b₀ C₂.Ψ (P21 z) with hfdef
  have hf_apply : ∀ (σ τ : ℝ), f (σ, τ)
      = evLevel ψ a₀ b₀ C₁.Ψ (τ, σ) - evLevel ψ a₀ b₀ C₂.Ψ (τ, σ) := by
    intro σ τ
    simp only [hfdef, hP21]
  have hfcd : ContDiffAt ℝ 1 f (σ₀, τ₀) := by
    rw [hfdef]
    have h1 : ContDiffAt ℝ 1 (fun z : ℝ × ℝ => P21 z) (σ₀, τ₀) := P21.contDiff.contDiffAt
    exact (hA₁cd.comp (σ₀, τ₀) h1).sub (hA₂cd.comp (σ₀, τ₀) h1)
  have hfu : f (σ₀, τ₀) = 0 := by
    rw [hf_apply]
    change sH ψ a₀ b₀ τ₀ (C₁.Ψ (τ₀, σ₀)) - sH ψ a₀ b₀ τ₀ (C₂.Ψ (τ₀, σ₀)) = 0
    rw [C₁.hΨmem, C₂.hΨmem]
    exact sub_eq_zero.mpr hlev
  -- (6) the `τ`-derivative of `f` at the base point
  have hτ₁ : (fderiv ℝ (evLevel ψ a₀ b₀ C₁.Ψ) (τ₀, σ₀)) (1, 0)
      = inner ℝ (deriv (fun s : ℝ => Work.Drive.Mono.Band.dirOf s a₀ b₀) τ₀)
          (Work.BoxShrink.Pinch.par ψ p₁) := by
    rw [← fderivWithin_of_isOpen C₁.hVopen C₁.hVmem]
    exact C₁.hτ
  have hτ₂ : (fderiv ℝ (evLevel ψ a₀ b₀ C₂.Ψ) (τ₀, σ₀)) (1, 0)
      = inner ℝ (deriv (fun s : ℝ => Work.Drive.Mono.Band.dirOf s a₀ b₀) τ₀)
          (Work.BoxShrink.Pinch.par ψ p₂) := by
    rw [← fderivWithin_of_isOpen C₂.hVopen C₂.hVmem]
    exact C₂.hτ
  have hderivval : (fderiv ℝ f (σ₀, τ₀)) (0, 1)
      = inner ℝ (deriv (fun s : ℝ => Work.Drive.Mono.Band.dirOf s a₀ b₀) τ₀)
          (Work.BoxShrink.Pinch.par ψ p₁ - Work.BoxShrink.Pinch.par ψ p₂) := by
    have hd₁ : HasFDerivAt (fun z : ℝ × ℝ => evLevel ψ a₀ b₀ C₁.Ψ (P21 z))
        ((fderiv ℝ (evLevel ψ a₀ b₀ C₁.Ψ) (τ₀, σ₀)) ∘SL P21) (σ₀, τ₀) := by
      have h1 : HasFDerivAt (evLevel ψ a₀ b₀ C₁.Ψ)
          (fderiv ℝ (evLevel ψ a₀ b₀ C₁.Ψ) (τ₀, σ₀)) (τ₀, σ₀) :=
        (hA₁cd.differentiableAt (by norm_num)).hasFDerivAt
      have h2 := h1.comp (σ₀, τ₀) (ContinuousLinearMap.hasFDerivAt P21 (x := (σ₀, τ₀)))
      simpa [Function.comp_def] using h2
    have hd₂ : HasFDerivAt (fun z : ℝ × ℝ => evLevel ψ a₀ b₀ C₂.Ψ (P21 z))
        ((fderiv ℝ (evLevel ψ a₀ b₀ C₂.Ψ) (τ₀, σ₀)) ∘SL P21) (σ₀, τ₀) := by
      have h1 : HasFDerivAt (evLevel ψ a₀ b₀ C₂.Ψ)
          (fderiv ℝ (evLevel ψ a₀ b₀ C₂.Ψ) (τ₀, σ₀)) (τ₀, σ₀) :=
        (hA₂cd.differentiableAt (by norm_num)).hasFDerivAt
      have h2 := h1.comp (σ₀, τ₀) (ContinuousLinearMap.hasFDerivAt P21 (x := (σ₀, τ₀)))
      simpa [Function.comp_def] using h2
    have hfd : fderiv ℝ f (σ₀, τ₀)
        = ((fderiv ℝ (evLevel ψ a₀ b₀ C₁.Ψ) (τ₀, σ₀)) ∘SL P21)
          - ((fderiv ℝ (evLevel ψ a₀ b₀ C₂.Ψ) (τ₀, σ₀)) ∘SL P21) := by
      rw [hfdef]
      exact (hd₁.sub hd₂).fderiv
    rw [hfd]
    simp only [sub_apply, ContinuousLinearMap.comp_apply, hP21₀]
    rw [hτ₁, hτ₂, ← inner_sub_right]
  have hne0 : ((fderiv ℝ f (σ₀, τ₀)) ∘SL ContinuousLinearMap.inr ℝ ℝ ℝ) ≠ 0 := by
    intro h0
    have h1 : (fderiv ℝ f (σ₀, τ₀)) (ContinuousLinearMap.inr ℝ ℝ ℝ 1) = 0 := by
      have := congrArg (fun T : ℝ →L[ℝ] ℝ => T 1) h0
      simpa using this
    rw [ContinuousLinearMap.inr_apply] at h1
    rw [hderivval] at h1
    exact hwx' h1
  have hinv : ((fderiv ℝ f (σ₀, τ₀)) ∘SL ContinuousLinearMap.inr ℝ ℝ ℝ).IsInvertible :=
    lss_isInvertible_of_ne_zero hne0
  -- (7) the implicit function `σ ↦ τ`
  set S : ℝ → ℝ := hfcd.implicitFunction (by norm_num) hinv with hSdef
  have hS_cd : ContDiffAt ℝ 1 S σ₀ := by
    rw [hSdef]
    exact hfcd.contDiffAt_implicitFunction (by norm_num) hinv
  have hS_self : S σ₀ = τ₀ := by
    rw [hSdef]
    exact hfcd.implicitFunction_apply_self (by norm_num) hinv
  have hS_iff : ∀ᶠ y : ℝ × ℝ in nhds (σ₀, τ₀), f y = f (σ₀, τ₀) ↔ S y.1 = y.2 := by
    rw [hSdef]
    exact hfcd.eventually_apply_eq_iff_implicitFunction (by norm_num) hinv
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hS_iff
  have hiff : ∀ y : ℝ × ℝ, dist y (σ₀, τ₀) < ε → (f y = f (σ₀, τ₀) ↔ S y.1 = y.2) :=
    fun y hy => hball (Metric.mem_ball.mpr hy)
  -- (8) an open set of `σ` on which the charts are defined and `S` is `C¹`
  have hW₀ex : ∃ W ∈ nhds σ₀, ContDiffOn ℝ 1 S W := by
    have h := (contDiffWithinAt_iff_contDiffOn_nhds (𝕜 := ℝ) (f := S) (s := Set.univ) (x := σ₀)
      (n := 1) (by norm_num)).mp hS_cd
    simpa using h
  obtain ⟨W₀, hW₀mem, hW₀cd⟩ := hW₀ex
  obtain ⟨Wc, hWcsub, hWcopen, hWcmem⟩ := mem_nhds_iff.mp hW₀mem
  have hWccd : ContDiffOn ℝ 1 S Wc := hW₀cd.mono hWcsub
  have hS_cont : ContinuousAt S σ₀ := (hS_cd.differentiableAt (by norm_num)).continuousAt
  have hpair_cont : ContinuousAt (fun σ : ℝ => (S σ, σ)) σ₀ := hS_cont.prodMk continuousAt_id
  have hmem₁ : (fun σ : ℝ => (S σ, σ)) ⁻¹' C₁.V ∈ nhds σ₀ :=
    hpair_cont.preimage_mem_nhds (by simpa [hS_self] using C₁.hVopen.mem_nhds C₁.hVmem)
  have hmem₂ : (fun σ : ℝ => (S σ, σ)) ⁻¹' C₂.V ∈ nhds σ₀ :=
    hpair_cont.preimage_mem_nhds (by simpa [hS_self] using C₂.hVopen.mem_nhds C₂.hVmem)
  have hWσ_mem : Wc ∩ ((fun σ : ℝ => (S σ, σ)) ⁻¹' C₁.V) ∩ ((fun σ : ℝ => (S σ, σ)) ⁻¹' C₂.V)
      ∈ nhds σ₀ :=
    Filter.inter_mem (Filter.inter_mem (hWcopen.mem_nhds hWcmem) hmem₁) hmem₂
  obtain ⟨Wσ, hWσsub, hWσopen, hWσmem⟩ := mem_nhds_iff.mp hWσ_mem
  have hWσcd : ContDiffOn ℝ 1 S Wσ := hWccd.mono (fun σ hσ => (hWσsub hσ).1.1)
  have hWσV₁ : ∀ σ ∈ Wσ, (S σ, σ) ∈ C₁.V := fun σ hσ => (hWσsub hσ).1.2
  have hWσV₂ : ∀ σ ∈ Wσ, (S σ, σ) ∈ C₂.V := fun σ hσ => (hWσsub hσ).2
  -- (9) the neighbourhoods and the parametrisation
  set V : Set (ℝ × ℝ) := Wσ ×ˢ Set.univ with hVdef
  have hVopen : IsOpen V := by rw [hVdef]; exact hWσopen.prod isOpen_univ
  have hVmem : (σ₀, u₀) ∈ V := by rw [hVdef]; exact ⟨hWσmem, trivial⟩
  set φ : ℝ × ℝ → Wit := fun z =>
    wit z.2 ((z.1 - inner ℝ v c - z.2) / η) (S z.1)
      (C₁.Ψ (S z.1, z.1)) (C₂.Ψ (S z.1, z.1)) with hφdef
  have hφeq : ∀ (σ' u' : ℝ), φ (σ', u') = wit u' ((σ' - inner ℝ v c - u') / η) (S σ')
      (C₁.Ψ (S σ', σ')) (C₂.Ψ (S σ', σ')) := by
    intro σ' u'
    rw [hφdef]
  have hφcd : ContDiffOn ℝ 1 φ V := by
    rw [hφdef]
    have hf₁ : ContDiffOn ℝ 1 (fun z : ℝ × ℝ => z.2) V := contDiff_snd.contDiffOn
    have hf₂ : ContDiffOn ℝ 1 (fun z : ℝ × ℝ => (z.1 - inner ℝ v c - z.2) / η) V :=
      ((contDiff_fst.contDiffOn.sub contDiffOn_const).sub contDiff_snd.contDiffOn).div_const η
    have hf₃ : ContDiffOn ℝ 1 (fun z : ℝ × ℝ => S z.1) V :=
      hWσcd.comp contDiff_fst.contDiffOn (fun z hz => (by rw [hVdef] at hz; exact hz.1))
    have hf₄ : ContDiffOn ℝ 1 (fun z : ℝ × ℝ => C₁.Ψ (S z.1, z.1)) V :=
      C₁.hΨcd.comp (hf₃.prodMk contDiff_fst.contDiffOn)
        (fun z hz => (by rw [hVdef] at hz; exact hWσV₁ z.1 hz.1))
    have hf₅ : ContDiffOn ℝ 1 (fun z : ℝ × ℝ => C₂.Ψ (S z.1, z.1)) V :=
      C₂.hΨcd.comp (hf₃.prodMk contDiff_fst.contDiffOn)
        (fun z hz => (by rw [hVdef] at hz; exact hWσV₂ z.1 hz.1))
    exact hf₁.prodMk (hf₂.prodMk (hf₃.prodMk (hf₄.prodMk hf₅)))
  -- (10) the open neighbourhood of the witness
  set O : Set Wit :=
    (wQ ⁻¹' C₁.U) ∩ (wQ' ⁻¹' C₂.U) ∩
    ((fun w : Wit => (wT w, hFn ψ v (wQ w))) ⁻¹' C₁.V) ∩
    ((fun w : Wit => (wT w, hFn ψ v (wQ' w))) ⁻¹' C₂.V) ∩
    ((fun w : Wit => hFn ψ v (wQ w)) ⁻¹' Wσ) ∩
    ((fun w : Wit => dist (hFn ψ v (wQ w)) σ₀) ⁻¹' Set.Iio (ε / 2)) ∩
    ((fun w : Wit => dist (wT w) τ₀) ⁻¹' Set.Iio (ε / 2)) with hOdef
  have hOopen : IsOpen O := by
    have hcont₁ : Continuous (fun w : Wit => (wT w, hFn ψ v (wQ w))) :=
      lss_continuous_wT.prodMk ((lss_continuous_hFn ψ v).comp lss_continuous_wQ)
    have hcont₂ : Continuous (fun w : Wit => (wT w, hFn ψ v (wQ' w))) :=
      lss_continuous_wT.prodMk ((lss_continuous_hFn ψ v).comp lss_continuous_wQ')
    have hcont₃ : Continuous (fun w : Wit => hFn ψ v (wQ w)) :=
      (lss_continuous_hFn ψ v).comp lss_continuous_wQ
    have hcont₄ : Continuous (fun w : Wit => dist (hFn ψ v (wQ w)) σ₀) :=
      continuous_dist.comp (hcont₃.prodMk continuous_const)
    have hcont₅ : Continuous (fun w : Wit => dist (wT w) τ₀) :=
      continuous_dist.comp (lss_continuous_wT.prodMk continuous_const)
    have h1 : IsOpen (wQ ⁻¹' C₁.U) := C₁.hUopen.preimage lss_continuous_wQ
    have h2 : IsOpen (wQ' ⁻¹' C₂.U) := C₂.hUopen.preimage lss_continuous_wQ'
    have h3 : IsOpen ((fun w : Wit => (wT w, hFn ψ v (wQ w))) ⁻¹' C₁.V) :=
      C₁.hVopen.preimage hcont₁
    have h4 : IsOpen ((fun w : Wit => (wT w, hFn ψ v (wQ' w))) ⁻¹' C₂.V) :=
      C₂.hVopen.preimage hcont₂
    have h5 : IsOpen ((fun w : Wit => hFn ψ v (wQ w)) ⁻¹' Wσ) :=
      hWσopen.preimage hcont₃
    have h6 : IsOpen ((fun w : Wit => dist (hFn ψ v (wQ w)) σ₀) ⁻¹' Set.Iio (ε / 2)) :=
      isOpen_Iio.preimage hcont₄
    have h7 : IsOpen ((fun w : Wit => dist (wT w) τ₀) ⁻¹' Set.Iio (ε / 2)) :=
      isOpen_Iio.preimage hcont₅
    rw [hOdef]
    exact (((((h1.inter h2).inter h3).inter h4).inter h5).inter h6).inter h7
  have hwit_mem : wit u₀ h₀ τ₀ p₁ p₂ ∈ O := by
    rw [hOdef]
    simp only [wQ_wit, wQ'_wit, wT_wit, Set.mem_inter_iff, Set.mem_preimage, Set.mem_Iio]
    refine ⟨⟨⟨⟨⟨⟨C₁.hUmem, C₂.hUmem⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
    · have hpair : ((τ₀, hFn ψ v p₁) : ℝ × ℝ) = (τ₀, σ₀) := by rw [← hσ₀]
      rw [hpair]; exact C₁.hVmem
    · have hpair : ((τ₀, hFn ψ v p₂) : ℝ × ℝ) = (τ₀, σ₀) := by rw [← hσ₀']
      rw [hpair]; exact C₂.hVmem
    · rw [← hσ₀]; exact hWσmem
    · rw [← hσ₀, dist_self]; linarith
    · rw [dist_self]; linarith
  -- (11) the inclusion
  refine ⟨O, V, φ, hOopen, hwit_mem, hVopen, hVmem, hφcd, ?_⟩
  intro w hw
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq] at hw
  obtain ⟨hbad, hwO⟩ := hw
  obtain ⟨hc₁w, hc₂w, hσeq, hslab, hlevw⟩ := hbad
  rw [hOdef] at hwO
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Iio] at hwO
  obtain ⟨⟨⟨⟨⟨⟨hQmem, hQ'mem⟩, hV₁mem⟩, hV₂mem⟩, hσWσ⟩, hdist₁⟩, hdist₂⟩ := hwO
  set σ : ℝ := hFn ψ v (wQ w) with hσdef
  have hσWσ' : σ ∈ Wσ := by rw [hσdef]; exact hσWσ
  have hdist₁' : dist σ σ₀ < ε / 2 := by rw [hσdef]; exact hdist₁
  have hV₁mem' : (wT w, σ) ∈ C₁.V := by rw [hσdef]; exact hV₁mem
  have hσ' : hFn ψ v (wQ' w) = σ := by
    rw [hσdef]
    exact hσeq.symm
  have hV₂mem' : (wT w, σ) ∈ C₂.V := by rw [← hσ']; exact hV₂mem
  -- the two endpoints are the chart values
  have hq : wQ w = C₁.Ψ (wT w, σ) :=
    C₁.huniq (wT w) σ (wQ w) hV₁mem' hQmem hc₁w hσdef.symm
  have hq' : wQ' w = C₂.Ψ (wT w, σ) :=
    C₂.huniq (wT w) σ (wQ' w) hV₂mem' hQ'mem hc₂w hσ'
  -- the level equation
  have hlevw' : evLevel ψ a₀ b₀ C₁.Ψ (wT w, σ) = evLevel ψ a₀ b₀ C₂.Ψ (wT w, σ) := by
    change sH ψ a₀ b₀ (wT w) (C₁.Ψ (wT w, σ)) = sH ψ a₀ b₀ (wT w) (C₂.Ψ (wT w, σ))
    rw [← hq, ← hq']
    exact hlevw
  have hfval : f (σ, wT w) = 0 := by
    rw [hf_apply]
    rw [hlevw']
    ring
  have hclose : dist ((σ, wT w) : ℝ × ℝ) (σ₀, τ₀) < ε := by
    have hA : dist σ σ₀ < ε := lt_of_lt_of_le hdist₁' (by linarith)
    have hB : dist (wT w) τ₀ < ε := lt_of_lt_of_le hdist₂ (by linarith)
    calc dist ((σ, wT w) : ℝ × ℝ) (σ₀, τ₀)
        = max (dist σ σ₀) (dist (wT w) τ₀) := Prod.dist_eq
      _ < ε := max_lt hA hB
  have hSval : S σ = wT w := (hiff (σ, wT w) hclose).mp (by rw [hfval, hfu])
  -- the parameters are reconstructed
  have hwU : (σ - inner ℝ v c - wU w) / η = wH w := by
    have h : σ = inner ℝ v c + wU w + η * wH w := by rw [hσdef]; exact hslab
    rw [h]
    rw [show inner ℝ v c + wU w + η * wH w - inner ℝ v c - wU w = η * wH w from by ring]
    exact mul_div_cancel_left₀ (wH w) hηne
  have hφval : φ (σ, wU w) = w := by
    rw [hφeq, hwU, hSval, hq.symm, hq'.symm]
    exact lss_wit_eta w
  exact ⟨(σ, wU w), by rw [hVdef]; exact ⟨hσWσ', trivial⟩, hφval⟩

end

end Work.Drive.Mono
