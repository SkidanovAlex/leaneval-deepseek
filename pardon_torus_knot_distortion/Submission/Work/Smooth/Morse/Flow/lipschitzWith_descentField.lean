import Mathlib
import Submission.Work.Smooth.Morse.Defs

/-!
# The descent field is Lipschitz, bounded by `1`, and `2π`-periodic

The descent field of the chapter is

`descentField ψ g p = -((1 + (∂₁G p)² + (∂₂G p)²))⁻¹ • (∂₁G p, ∂₂G p)`,   `G = pullback ψ g`,

where `∂₁G`, `∂₂G` are the two coordinate derivatives of `G = g ∘ param ψ` in the parameter plane.
This file proves the bundle of analytic properties of that field which the construction of the
normalised gradient flow needs:

* it is globally Lipschitz;
* it is bounded by `1` in norm;
* it is `2π`-periodic in each parameter.

## The mechanism

`G` is `C²` (because `g` is `C²` and the parametrisation `param ψ` is `C^∞`) and **biperiodic**:
`G (x + 2πk, y + 2πl) = G (x, y)` for integers `k, l`.  This is a purely algebraic consequence of
the periodicity of `cos`/`sin` in the formula for `Work.Core.torusMap`.

Two consequences of biperiodicity are used repeatedly, and are proved here in abstract form:

* `fderiv_biperiodic`: the derivative of a biperiodic function is biperiodic (differentiate the
  identity `h ∘ (· + c) = h`, whose derivative at `p` is `fderiv h (p + c)` since the translation
  has derivative the identity);
* `exists_bound_biperiodic`: a continuous biperiodic function is bounded — reduce a point to the
  fundamental domain `[0, 2π] × [0, 2π]` with integer multiples of `2π` and use compactness.

Since `G` is `C²`, the map `p ↦ fderiv ℝ G p` is `C¹` and also biperiodic, so by the two facts
above its second derivative is bounded; the mean value inequality then makes `p ↦ fderiv ℝ G p`
Lipschitz, hence so are the coordinate derivatives `∂₁G`, `∂₂G` (they are obtained by evaluating
that derivative at the fixed vector `(1,0)` respectively `(0,1)`).

Finally the descent field itself is the composite of the `C¹` map `p ↦ (∂₁G p, ∂₂G p)` with the
smooth (rational) map `v ↦ -((1 + v₁² + v₂²))⁻¹ • v`, hence `C¹` and biperiodic; its derivative is
biperiodic and continuous, so bounded, and the mean value inequality gives Lipschitzness of the
descent field with the ceiling of that bound as constant.
-/

namespace Work.Smooth.Morse.Flow

open LeanEval.KnotTheory.PardonDistortion

noncomputable section

/-! ## Periodicity of the parametrisation and of the pull-back -/

/-- The parametrisation of the torus is `2π`-periodic in each variable, by integer multiples of
`2π`. -/
theorem torusMap_biperiodic (x y : ℝ) (k l : ℤ) :
    Work.Core.torusMap (x + k * (2 * Real.pi)) (y + l * (2 * Real.pi)) =
      Work.Core.torusMap x y := by
  have h2 : ∀ θ φ : ℝ, Work.Core.torusMap θ (φ + l * (2 * Real.pi)) =
      Work.Core.torusMap θ φ :=
    fun θ => (show Function.Periodic (fun φ : ℝ => Work.Core.torusMap θ φ) (2 * Real.pi) from
      fun φ => Work.Core.torusMap_add_two_pi_right θ φ).int_mul l
  have h1 : ∀ θ φ : ℝ, Work.Core.torusMap (θ + k * (2 * Real.pi)) φ =
      Work.Core.torusMap θ φ :=
    fun θ φ => (show Function.Periodic (fun θ : ℝ => Work.Core.torusMap θ φ) (2 * Real.pi) from
      fun θ => Work.Core.torusMap_add_two_pi_left θ φ).int_mul k θ
  rw [h2, h1]

/-- The pull-back `G = pullback ψ g = g ∘ param ψ` of a function on `ℝ³` to the parameter plane is
`2π`-biperiodic. -/
theorem pullback_biperiodic (ψ : Submission.Diffeo) (g : R3 → ℝ) (p : ℝ × ℝ) (k l : ℤ) :
    Work.Smooth.Morse.pullback ψ g (p.1 + k * (2 * Real.pi), p.2 + l * (2 * Real.pi)) =
      Work.Smooth.Morse.pullback ψ g p := by
  obtain ⟨a, b⟩ := p
  simp only [Work.Smooth.Morse.pullback_apply]
  rw [torusMap_biperiodic]

/-! ## Two consequences of biperiodicity -/

/-- **The derivative of a biperiodic function is biperiodic.**  `h ∘ (· + c) = h` for the
translation `c` by the period; differentiating at `p` and using that the translation has
derivative the identity gives `fderiv h (p + c) = fderiv h p`. -/
theorem fderiv_biperiodic {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {h : ℝ × ℝ → F} (hd : Differentiable ℝ h)
    (hper : ∀ (p : ℝ × ℝ) (k l : ℤ),
      h (p.1 + k * (2 * Real.pi), p.2 + l * (2 * Real.pi)) = h p)
    (p : ℝ × ℝ) (k l : ℤ) :
    fderiv ℝ h (p.1 + k * (2 * Real.pi), p.2 + l * (2 * Real.pi)) = fderiv ℝ h p := by
  set c : ℝ × ℝ := (k * (2 * Real.pi), l * (2 * Real.pi)) with hc
  have hτ : ∀ q : ℝ × ℝ, h (q + c) = h q := by
    intro q
    have : q + c = (q.1 + k * (2 * Real.pi), q.2 + l * (2 * Real.pi)) := by
      ext <;> simp [hc]
    rw [this, hper]
  have hcomp : h ∘ (fun q : ℝ × ℝ => q + c) = h := funext hτ
  have hdτ : DifferentiableAt ℝ (fun q : ℝ × ℝ => q + c) p := by fun_prop
  have hdh : DifferentiableAt ℝ h (p + c) := hd.differentiableAt
  have key : fderiv ℝ (h ∘ (fun q : ℝ × ℝ => q + c)) p
      = fderiv ℝ h (p + c) ∘SL fderiv ℝ (fun q : ℝ × ℝ => q + c) p :=
    fderiv_comp p hdh hdτ
  rw [hcomp] at key
  have hdτ_eq : fderiv ℝ (fun q : ℝ × ℝ => q + c) p = ContinuousLinearMap.id ℝ (ℝ × ℝ) := by
    have : (fun q : ℝ × ℝ => q + c) = fun q => id q + c := rfl
    rw [this, fderiv_add_const, fderiv_id]
  rw [hdτ_eq, ContinuousLinearMap.comp_id] at key
  have : p + c = (p.1 + k * (2 * Real.pi), p.2 + l * (2 * Real.pi)) := by
    ext <;> simp [hc]
  rw [this] at key
  exact key.symm

/-- **A biperiodic point can be moved to the fundamental domain.**  For every `p` there is
`q ∈ [0, 2π] × [0, 2π]` with `F p = F q`: subtract from each coordinate the appropriate integer
multiple of `2π`. -/
theorem exists_mem_box_biperiodic {α : Type*} {F : ℝ × ℝ → α}
    (hper : ∀ (p : ℝ × ℝ) (k l : ℤ),
      F (p.1 + k * (2 * Real.pi), p.2 + l * (2 * Real.pi)) = F p) (p : ℝ × ℝ) :
    ∃ q ∈ Set.Icc 0 (2 * Real.pi) ×ˢ Set.Icc 0 (2 * Real.pi), F p = F q := by
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  set k : ℤ := ⌊p.1 / (2 * Real.pi)⌋ with hk
  set l : ℤ := ⌊p.2 / (2 * Real.pi)⌋ with hl
  refine ⟨(p.1 - k * (2 * Real.pi), p.2 - l * (2 * Real.pi)), ?_, ?_⟩
  · have h1 : (0 : ℝ) ≤ p.1 - k * (2 * Real.pi) := by
      have h := Int.floor_le (p.1 / (2 * Real.pi))
      rw [← hk] at h
      have h2 : (k : ℝ) * (2 * Real.pi) ≤ (p.1 / (2 * Real.pi)) * (2 * Real.pi) :=
        mul_le_mul_of_nonneg_right h (le_of_lt hpi)
      rw [div_mul_cancel₀ _ (ne_of_gt hpi)] at h2
      linarith
    have h2 : p.1 - k * (2 * Real.pi) ≤ 2 * Real.pi := by
      have h := Int.lt_floor_add_one (p.1 / (2 * Real.pi))
      rw [← hk] at h
      have h3 : (p.1 / (2 * Real.pi)) * (2 * Real.pi) < ((k : ℝ) + 1) * (2 * Real.pi) :=
        mul_lt_mul_of_pos_right h hpi
      rw [div_mul_cancel₀ _ (ne_of_gt hpi)] at h3
      linarith
    have h3 : (0 : ℝ) ≤ p.2 - l * (2 * Real.pi) := by
      have h := Int.floor_le (p.2 / (2 * Real.pi))
      rw [← hl] at h
      have h4 : (l : ℝ) * (2 * Real.pi) ≤ (p.2 / (2 * Real.pi)) * (2 * Real.pi) :=
        mul_le_mul_of_nonneg_right h (le_of_lt hpi)
      rw [div_mul_cancel₀ _ (ne_of_gt hpi)] at h4
      linarith
    have h4 : p.2 - l * (2 * Real.pi) ≤ 2 * Real.pi := by
      have h := Int.lt_floor_add_one (p.2 / (2 * Real.pi))
      rw [← hl] at h
      have h5 : (p.2 / (2 * Real.pi)) * (2 * Real.pi) < ((l : ℝ) + 1) * (2 * Real.pi) :=
        mul_lt_mul_of_pos_right h hpi
      rw [div_mul_cancel₀ _ (ne_of_gt hpi)] at h5
      linarith
    exact ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
  · have hq := hper (p.1 - k * (2 * Real.pi), p.2 - l * (2 * Real.pi)) k l
    have harg : ((p.1 - k * (2 * Real.pi)) + (k : ℝ) * (2 * Real.pi),
        (p.2 - l * (2 * Real.pi)) + (l : ℝ) * (2 * Real.pi)) = p := by
      ext <;> ring
    rw [harg] at hq
    exact hq

/-- **A continuous biperiodic function is bounded.** -/
theorem exists_bound_biperiodic {E : Type*} [SeminormedAddGroup E] {h : ℝ × ℝ → E}
    (hc : Continuous h)
    (hper : ∀ (p : ℝ × ℝ) (k l : ℤ),
      h (p.1 + k * (2 * Real.pi), p.2 + l * (2 * Real.pi)) = h p) :
    ∃ C : ℝ, ∀ p : ℝ × ℝ, ‖h p‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc :
    IsCompact (Set.Icc (0 : ℝ) (2 * Real.pi) ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi))).exists_bound_of_continuousOn
      hc.continuousOn
  exact ⟨max C 0, fun p => by
    obtain ⟨q, hq, hpq⟩ := exists_mem_box_biperiodic hper p
    rw [hpq]
    exact le_trans (hC q hq) (le_max_left _ _)⟩

/-! ## The pull-back is `C²` and its coordinate derivatives are biperiodic -/

/-- The pull-back of a `C²` function to the parameter plane is `C²`. -/
theorem contDiff_pullback (ψ : Submission.Diffeo) {g : R3 → ℝ} (hg : ContDiff ℝ 2 g) :
    ContDiff ℝ 2 (Work.Smooth.Morse.pullback ψ g) := by
  have hpar : ContDiff ℝ 2 (Work.Smooth.Morse.param ψ) :=
    (Work.Smooth.Morse.param_contDiff ψ).of_le (WithTop.coe_le_coe.mpr le_top)
  exact hg.comp hpar

/-- The first coordinate derivative `∂₁G` of the pull-back is `2π`-biperiodic. -/
theorem partialD₁_biperiodic (ψ : Submission.Diffeo) {g : R3 → ℝ} (hg : ContDiff ℝ 2 g)
    (p : ℝ × ℝ) (k l : ℤ) :
    Work.Smooth.Morse.partialD₁ ψ g (p.1 + k * (2 * Real.pi), p.2 + l * (2 * Real.pi)) =
      Work.Smooth.Morse.partialD₁ ψ g p := by
  have hG := contDiff_pullback ψ hg
  have hd : Differentiable ℝ (Work.Smooth.Morse.pullback ψ g) := hG.differentiable (by norm_num)
  have h1 := fderiv_biperiodic hd (fun p k l => pullback_biperiodic ψ g p k l) p k l
  simpa only [Work.Smooth.Morse.partialD₁] using
    congrArg (fun L : (ℝ × ℝ) →L[ℝ] ℝ => L ((1 : ℝ), (0 : ℝ))) h1

/-- The second coordinate derivative `∂₂G` of the pull-back is `2π`-biperiodic. -/
theorem partialD₂_biperiodic (ψ : Submission.Diffeo) {g : R3 → ℝ} (hg : ContDiff ℝ 2 g)
    (p : ℝ × ℝ) (k l : ℤ) :
    Work.Smooth.Morse.partialD₂ ψ g (p.1 + k * (2 * Real.pi), p.2 + l * (2 * Real.pi)) =
      Work.Smooth.Morse.partialD₂ ψ g p := by
  have hG := contDiff_pullback ψ hg
  have hd : Differentiable ℝ (Work.Smooth.Morse.pullback ψ g) := hG.differentiable (by norm_num)
  have h1 := fderiv_biperiodic hd (fun p k l => pullback_biperiodic ψ g p k l) p k l
  simpa only [Work.Smooth.Morse.partialD₂] using
    congrArg (fun L : (ℝ × ℝ) →L[ℝ] ℝ => L ((0 : ℝ), (1 : ℝ))) h1

/-! ## The descent field is `C¹` and biperiodic -/

/-- **The descent field is `C¹`**: it is the composite of the `C¹` map
`p ↦ (∂₁G p, ∂₂G p)` with the smooth rational map `v ↦ -((1 + v₁² + v₂²))⁻¹ • v`. -/
theorem contDiff_descentField (ψ : Submission.Diffeo) {g : R3 → ℝ} (hg : ContDiff ℝ 2 g) :
    ContDiff ℝ 1 (Work.Smooth.Morse.descentField ψ g) := by
  have hG : ContDiff ℝ 2 (Work.Smooth.Morse.pullback ψ g) := contDiff_pullback ψ hg
  have hL : ContDiff ℝ 1 (fderiv ℝ (Work.Smooth.Morse.pullback ψ g)) := by
    have h := (contDiff_succ_iff_fderiv (𝕜 := ℝ) (f := Work.Smooth.Morse.pullback ψ g) (n := 1)).1 hG
    exact h.2.2
  have hA : ContDiff ℝ 1 (fun p : ℝ × ℝ => fderiv ℝ (Work.Smooth.Morse.pullback ψ g) p (1, 0)) := by
    have hev : ContDiff ℝ 1 (fun v : (ℝ × ℝ) →L[ℝ] ℝ => v ((1 : ℝ), (0 : ℝ))) :=
      ContinuousLinearMap.contDiff (ContinuousLinearMap.apply ℝ ℝ ((1 : ℝ), (0 : ℝ)))
    exact hev.comp hL
  have hB : ContDiff ℝ 1 (fun p : ℝ × ℝ => fderiv ℝ (Work.Smooth.Morse.pullback ψ g) p (0, 1)) := by
    have hev : ContDiff ℝ 1 (fun v : (ℝ × ℝ) →L[ℝ] ℝ => v ((0 : ℝ), (1 : ℝ))) :=
      ContinuousLinearMap.contDiff (ContinuousLinearMap.apply ℝ ℝ ((0 : ℝ), (1 : ℝ)))
    exact hev.comp hL
  have hF : ContDiff ℝ 1 (fun p : ℝ × ℝ =>
      (fderiv ℝ (Work.Smooth.Morse.pullback ψ g) p (1, 0),
       fderiv ℝ (Work.Smooth.Morse.pullback ψ g) p (0, 1))) := hA.prodMk hB
  have hψ₀ : ContDiff ℝ 1 (fun v : ℝ × ℝ => -((1 + v.1 ^ 2 + v.2 ^ 2 : ℝ)⁻¹) • v) := by
    have h1 : ContDiff ℝ 1 (fun v : ℝ × ℝ => (1 + v.1 ^ 2 + v.2 ^ 2 : ℝ)) := by fun_prop
    have h2 : ContDiff ℝ 1 (fun v : ℝ × ℝ => ((1 + v.1 ^ 2 + v.2 ^ 2 : ℝ))⁻¹) :=
      h1.inv (fun v => by positivity)
    exact h2.neg.smul contDiff_id
  exact hψ₀.comp hF

/-- The descent field is `2π`-biperiodic (each of its two ingredients `∂₁G`, `∂₂G` is). -/
theorem descentField_biperiodic (ψ : Submission.Diffeo) {g : R3 → ℝ} (hg : ContDiff ℝ 2 g)
    (p : ℝ × ℝ) (k l : ℤ) :
    Work.Smooth.Morse.descentField ψ g (p.1 + k * (2 * Real.pi), p.2 + l * (2 * Real.pi)) =
      Work.Smooth.Morse.descentField ψ g p := by
  unfold Work.Smooth.Morse.descentField
  rw [partialD₁_biperiodic ψ hg p k l, partialD₂_biperiodic ψ hg p k l]

/-- The descent field has norm at most one, with no differentiability hypothesis: writing
`a = ∂₁G p`, `b = ∂₂G p` and `c = (1 + a² + b²)⁻¹`, it is `-(c • (a, b))`, whose norm is
`c · max |a| |b| ≤ max |a| |b| / (1 + max |a| |b|²) ≤ 1`. -/
theorem norm_descentField_le_one (ψ : Submission.Diffeo) (g : R3 → ℝ) (q : ℝ × ℝ) :
    ‖Work.Smooth.Morse.descentField ψ g q‖ ≤ 1 := by
  set a := Work.Smooth.Morse.partialD₁ ψ g q with ha
  set b := Work.Smooth.Morse.partialD₂ ψ g q with hb
  set c := (1 + a ^ 2 + b ^ 2 : ℝ)⁻¹ with hc
  have hcpos : 0 < c := by rw [hc]; positivity
  have hEq : Work.Smooth.Morse.descentField ψ g q = -(c • (a, b)) := by
    rw [Work.Smooth.Morse.descentField, ← hc, ← ha, ← hb, neg_smul]
  rw [hEq, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hcpos, Prod.norm_def]
  simp only [Real.norm_eq_abs]
  have ht : max |a| |b| ≤ 1 + a ^ 2 + b ^ 2 := by
    have ha1 : |a| ≤ 1 + a ^ 2 := by nlinarith [sq_abs a, abs_nonneg a]
    have hb1 : |b| ≤ 1 + b ^ 2 := by nlinarith [sq_abs b, abs_nonneg b]
    exact max_le (by nlinarith) (by nlinarith)
  have hden : (0 : ℝ) < 1 + a ^ 2 + b ^ 2 := by positivity
  calc c * max |a| |b| = max |a| |b| / (1 + a ^ 2 + b ^ 2) := by rw [hc, inv_mul_eq_div]
    _ ≤ 1 := (div_le_one hden).mpr ht

/-! ## The descent field is Lipschitz -/

theorem lipschitzWith_descentField (ψ : Submission.Diffeo) {g : LeanEval.KnotTheory.PardonDistortion.R3 → ℝ} (hg : ContDiff ℝ 2 g) : ∃ K : NNReal, LipschitzWith K (Work.Smooth.Morse.descentField ψ g) ∧ (∀ q : ℝ × ℝ, ‖Work.Smooth.Morse.descentField ψ g q‖ ≤ 1) ∧ (∀ (q : ℝ × ℝ) (k l : ℤ), Work.Smooth.Morse.descentField ψ g (q.1 + (k : ℝ) * (2 * Real.pi), q.2 + (l : ℝ) * (2 * Real.pi)) = Work.Smooth.Morse.descentField ψ g q) := by
  have hC1 : ContDiff ℝ 1 (Work.Smooth.Morse.descentField ψ g) := contDiff_descentField ψ hg
  have hper : ∀ (p : ℝ × ℝ) (k l : ℤ),
      Work.Smooth.Morse.descentField ψ g (p.1 + k * (2 * Real.pi), p.2 + l * (2 * Real.pi)) =
        Work.Smooth.Morse.descentField ψ g p := fun p k l => descentField_biperiodic ψ hg p k l
  have hdiff : Differentiable ℝ (Work.Smooth.Morse.descentField ψ g) := hC1.differentiable (by norm_num)
  have hper' : ∀ (p : ℝ × ℝ) (k l : ℤ),
      fderiv ℝ (Work.Smooth.Morse.descentField ψ g) (p.1 + k * (2 * Real.pi), p.2 + l * (2 * Real.pi)) =
        fderiv ℝ (Work.Smooth.Morse.descentField ψ g) p :=
    fun p k l => fderiv_biperiodic hdiff hper p k l
  obtain ⟨C, hC⟩ := exists_bound_biperiodic (hC1.continuous_fderiv (by norm_num)) hper'
  refine ⟨⌈max C 0⌉₊, ?_, ?_, ?_⟩
  · apply lipschitzWith_of_nnnorm_fderiv_le hdiff
    intro p
    rw [← NNReal.coe_le_coe, coe_nnnorm]
    exact le_trans (hC p) (le_trans (le_max_left _ _) (Nat.le_ceil _))
  · intro q
    exact norm_descentField_le_one ψ g q
  · intro q k l
    exact descentField_biperiodic ψ hg q k l

end

end Work.Smooth.Morse.Flow
