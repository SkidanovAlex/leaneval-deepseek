/-
# The Fourier multiplier of the iterated forward difference

For `u : ℂ → ℂ` in `L²(ℂ)` and `h : ℂ`, the Fourier transform of the forward difference
`Δ_h u (x) = u (x + h) - u x` is the pointwise product of `𝓕u` with the phase factor
`ξ ↦ 𝐞(⟪h,ξ⟫) - 1`.  Iterating, `𝓕 (Δ_h^N u) = (𝐞(⟪h,·⟫) - 1)^N · 𝓕u`, so by Plancherel

  `‖ (𝐞(⟪h,·⟫) - 1)^N 𝓕u ‖_{L²} = ‖ Δ_h^N u ‖_{L²}`.

The file is organised as follows.

* `phase h ξ = 𝐞(⟪h,ξ⟫)`.
* `shiftAdd h` is the translation operator `G ↦ G(· + h)` on `L²(ℂ)` (a measure preserving
  transformation of the domain), `multFun h` is the pointwise multiplication by `phase h`.
* `fourier_shiftAdd` is the key multiplier identity `𝓕 (shiftAdd h G) = multFun h (𝓕 G)`, proved
  by density of the Schwartz functions: both sides are continuous in `G`, `𝓕` is additive, and
  for a Schwartz function `φ` the identity is
  `VectorFourier.fourierIntegral_comp_add_right` together with `SchwartzMap.toLp_fourier_eq`.
* `shiftOp h = shiftAdd h - 1` and `multOp h = multFun h - 1`; iterating the multiplier identity
  gives `𝓕 (shiftOp h^[N] G) = multOp h^[N] (𝓕 G)` (`fourier_shiftOp_iterate`), and on
  representatives `multOp h^[N] F = (phase h - 1)^N * F` (`coeFn_multOp_iterate`).
* `coeFn_shiftOp_iterate` identifies `shiftOp h^[N] G` with the `N`-th forward difference of the
  representative of `G`.
-/
import Mathlib

namespace Work.Beltrami

open MeasureTheory
open scoped FourierTransform ContDiff SchwartzMap
open SchwartzMap

noncomputable section

/-! ### The phase factor and the two basic operators on `L²(ℂ)` -/

/-- The phase factor `ξ ↦ 𝐞(⟪h,ξ⟫) = exp(2πi⟪h,ξ⟫)`. -/
def phase (h ξ : ℂ) : ℂ := (Real.fourierChar (inner ℝ h ξ) : ℂ)

@[simp] lemma phase_apply (h ξ : ℂ) : phase h ξ = (Real.fourierChar (inner ℝ h ξ) : ℂ) := rfl

lemma norm_phase (h ξ : ℂ) : ‖phase h ξ‖ = 1 := by simp [phase]

lemma continuous_phase (h : ℂ) : Continuous (phase h) := by unfold phase; fun_prop

theorem phase_ne_zero (h ξ : ℂ) : phase h ξ ≠ 0 := by
  intro hz
  have := norm_phase h ξ
  rw [hz, norm_zero] at this
  exact one_ne_zero this.symm

/-- `fun ξ => phase h ξ * G ξ` is in `L²`, as `phase h` has modulus one. -/
theorem multMemLp (h : ℂ) (G : Lp (α := ℂ) ℂ 2 volume) :
    MemLp (fun ξ => phase h ξ * ⇑G ξ) 2 volume :=
  (Lp.memLp G).of_le_mul (c := 1)
    ((continuous_phase h).aestronglyMeasurable.mul (Lp.aestronglyMeasurable G))
    (Filter.Eventually.of_forall fun ξ => by simp)

/-- Multiplication by the phase factor, as a map on `L²(ℂ)`. -/
def multFun (h : ℂ) (G : Lp (α := ℂ) ℂ 2 volume) : Lp (α := ℂ) ℂ 2 volume :=
  MemLp.toLp (fun ξ => phase h ξ * ⇑G ξ) (multMemLp h G)

lemma coeFn_multFun (h : ℂ) (G : Lp (α := ℂ) ℂ 2 volume) :
    ⇑(multFun h G) =ᵐ[volume] fun ξ => phase h ξ * ⇑G ξ :=
  MemLp.coeFn_toLp (multMemLp h G)

lemma multFun_add (h : ℂ) (G G' : Lp (α := ℂ) ℂ 2 volume) :
    multFun h (G + G') = multFun h G + multFun h G' := by
  rw [Lp.ext_iff]
  filter_upwards [coeFn_multFun h (G + G'), coeFn_multFun h G, coeFn_multFun h G',
      Lp.coeFn_add (multFun h G) (multFun h G'), Lp.coeFn_add G G'] with ξ h1 h2 h3 h4 h5
  simp only [Pi.add_apply] at h4 h5 ⊢
  rw [h1, h4, h2, h3, h5]
  ring

lemma multFun_smul (h : ℂ) (c : ℂ) (G : Lp (α := ℂ) ℂ 2 volume) :
    multFun h (c • G) = c • multFun h G := by
  rw [Lp.ext_iff]
  filter_upwards [coeFn_multFun h (c • G), coeFn_multFun h G,
      Lp.coeFn_smul c (multFun h G), Lp.coeFn_smul c G] with ξ h1 h2 h3 h4
  simp only [Pi.smul_apply] at h3 h4 ⊢
  rw [h1, h3, h2, h4]
  ring

lemma norm_multFun (h : ℂ) (G : Lp (α := ℂ) ℂ 2 volume) : ‖multFun h G‖ = ‖G‖ := by
  have h2 : eLpNorm (fun ξ : ℂ => phase h ξ * ⇑G ξ) 2 volume = eLpNorm (⇑G) 2 volume :=
    eLpNorm_congr_norm_ae (f := fun ξ : ℂ => phase h ξ * ⇑G ξ) (g := ⇑G)
      ((continuous_phase h).aestronglyMeasurable.mul (Lp.aestronglyMeasurable G))
      (Lp.aestronglyMeasurable G) (Filter.Eventually.of_forall fun ξ => by simp)
  rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (p := 2) (μ := volume) (coeFn_multFun h G), h2]

lemma isometry_multFun (h : ℂ) : Isometry (multFun h) := by
  refine Isometry.of_dist_eq fun G G' => ?_
  have hsub : multFun h G - multFun h G' = multFun h (G - G') := by
    rw [sub_eq_add_neg, sub_eq_add_neg, multFun_add]
    congr 1
    rw [← neg_one_smul ℂ G', multFun_smul, neg_smul, one_smul]
  rw [dist_eq_norm, dist_eq_norm, hsub, norm_multFun]

/-- The translation `G ↦ G(· + h)` on `L²(ℂ)`. -/
def shiftAdd (h : ℂ) : Lp (α := ℂ) ℂ 2 volume →+ Lp (α := ℂ) ℂ 2 volume :=
  Lp.compMeasurePreserving (fun x : ℂ => x + h) (measurePreserving_add_right volume h)

lemma coeFn_shiftAdd (h : ℂ) (G : Lp (α := ℂ) ℂ 2 volume) :
    ⇑(shiftAdd h G) =ᵐ[volume] ⇑G ∘ (fun x : ℂ => x + h) :=
  Lp.coeFn_compMeasurePreserving G (measurePreserving_add_right volume h)

lemma isometry_shiftAdd (h : ℂ) : Isometry (shiftAdd h) := by
  refine Isometry.of_dist_eq fun G G' => ?_
  rw [dist_eq_norm, dist_eq_norm, ← map_sub]
  show ‖(Lp.compMeasurePreserving (fun x : ℂ => x + h) (measurePreserving_add_right volume h))
      (G - G')‖ = ‖G - G'‖
  exact Lp.norm_compMeasurePreserving _ _

/-- The Fourier transform of a translated function is the translate of the Fourier transform. -/
lemma fourier_comp_add (h : ℂ) (f : ℂ → ℂ) :
    𝓕 (f ∘ fun x : ℂ => x + h) = fun ξ => phase h ξ * 𝓕 f ξ := by
  ext ξ
  change VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ ℂ) (f ∘ fun v : ℂ => v + h) ξ
    = phase h ξ * VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ ℂ) f ξ
  rw [VectorFourier.fourierIntegral_comp_add_right (𝕜 := ℝ) (V := ℂ) (W := ℂ) (E := ℂ)
     Real.fourierChar volume (innerₗ ℂ) f h]
  simp [phase, Circle.smul_def]

lemma coe_fourier_compSubConstCLM (h : ℂ) (φ : 𝓢(ℂ,ℂ)) (ξ : ℂ) :
    𝓕 (SchwartzMap.compSubConstCLM ℂ (-h) φ) ξ = phase h ξ * (𝓕 φ) ξ := by
  have hcoe : (SchwartzMap.compSubConstCLM ℂ (-h) φ : ℂ → ℂ) = fun x : ℂ => φ (x + h) := by
    funext x; rw [SchwartzMap.compSubConstCLM_apply]; simp
  rw [SchwartzMap.fourier_coe (SchwartzMap.compSubConstCLM ℂ (-h) φ), hcoe,
      SchwartzMap.fourier_coe φ]
  exact congrFun (fourier_comp_add h (φ : ℂ → ℂ)) ξ

/-- The multiplier identity for a Schwartz function. -/
lemma schwartz_step (h : ℂ) (φ : 𝓢(ℂ,ℂ)) :
    𝓕 (shiftAdd h (φ.toLp 2 volume)) = multFun h (𝓕 (φ.toLp 2 volume)) := by
  have hA : shiftAdd h (φ.toLp 2 volume)
      = (SchwartzMap.compSubConstCLM ℂ (-h) φ).toLp 2 volume := by
    have h1 := Lp.toLp_compMeasurePreserving (f := fun x : ℂ => x + h) (g := ⇑φ)
        (φ.memLp 2 volume) (measurePreserving_add_right volume h)
    rw [show shiftAdd h (φ.toLp 2 volume)
        = (Lp.compMeasurePreserving (fun x : ℂ => x + h) (measurePreserving_add_right volume h))
            (MemLp.toLp ⇑φ (φ.memLp 2 volume)) from rfl, h1]
    refine MemLp.toLp_congr _ _ (Filter.Eventually.of_forall fun x => ?_)
    simp [SchwartzMap.compSubConstCLM_apply]
  rw [hA, SchwartzMap.toLp_fourier_eq, SchwartzMap.toLp_fourier_eq]
  unfold multFun
  refine MemLp.toLp_congr _ _ ?_
  filter_upwards [SchwartzMap.coeFn_toLp (𝓕 φ) 2 volume] with ξ hξ
  rw [hξ, coe_fourier_compSubConstCLM h φ ξ]

/-- **The multiplier identity**: the Fourier transform intertwines translation of the argument
with multiplication by the phase factor `𝐞(⟪h,·⟫)`. -/
theorem fourier_shiftAdd (h : ℂ) (G : Lp (α := ℂ) ℂ 2 volume) :
    𝓕 (shiftAdd h G) = multFun h (𝓕 G) := by
  have hfun : (fun G : Lp (α := ℂ) ℂ 2 volume => 𝓕 (shiftAdd h G))
      = fun G => multFun h (𝓕 G) :=
    DenseRange.equalizer
      (SchwartzMap.denseRange_toLpCLM (E := ℂ) (F := ℂ) (p := 2) (μ := volume)
        ENNReal.ofNat_ne_top)
      ((Lp.fourierTransformₗᵢ ℂ ℂ).continuous.comp (isometry_shiftAdd h).continuous)
      ((isometry_multFun h).continuous.comp (Lp.fourierTransformₗᵢ ℂ ℂ).continuous)
      (by
        funext φ
        simp only [Function.comp_apply, SchwartzMap.toLpCLM_apply]
        exact schwartz_step h φ)
  exact congrFun hfun G

/-! ### The difference operators and their iterates -/

/-- The forward difference `Δ_h f (x) = f (x + h) - f x`. -/
def dd (h : ℂ) : (ℂ → ℂ) → (ℂ → ℂ) := fun f => fun x => f (x + h) - f x

@[simp] lemma dd_apply (h : ℂ) (f : ℂ → ℂ) (x : ℂ) : dd h f x = f (x + h) - f x := rfl

/-- `shiftOp h` is `shiftAdd h - 1`: the forward difference on `L²(ℂ)`. -/
def shiftOp (h : ℂ) : Lp (α := ℂ) ℂ 2 volume → Lp (α := ℂ) ℂ 2 volume :=
  fun G => shiftAdd h G - G

@[simp] lemma shiftOp_apply (h : ℂ) (G : Lp (α := ℂ) ℂ 2 volume) :
    shiftOp h G = shiftAdd h G - G := rfl

/-- `multOp h` is `multFun h - 1`. -/
def multOp (h : ℂ) : Lp (α := ℂ) ℂ 2 volume → Lp (α := ℂ) ℂ 2 volume :=
  fun F => multFun h F - F

@[simp] lemma multOp_apply (h : ℂ) (F : Lp (α := ℂ) ℂ 2 volume) :
    multOp h F = multFun h F - F := rfl

lemma fourier_shiftOp (h : ℂ) (G : Lp (α := ℂ) ℂ 2 volume) :
    𝓕 (shiftOp h G) = multOp h (𝓕 G) := by
  change (Lp.fourierTransformₗᵢ ℂ ℂ) (shiftAdd h G - G)
    = multFun h ((Lp.fourierTransformₗᵢ ℂ ℂ) G) - (Lp.fourierTransformₗᵢ ℂ ℂ) G
  rw [map_sub,
    show (Lp.fourierTransformₗᵢ ℂ ℂ) (shiftAdd h G)
        = multFun h ((Lp.fourierTransformₗᵢ ℂ ℂ) G) from fourier_shiftAdd h G]

/-- Iterated form of the multiplier identity. -/
theorem fourier_shiftOp_iterate (h : ℂ) (N : ℕ) (G : Lp (α := ℂ) ℂ 2 volume) :
    𝓕 ((shiftOp h)^[N] G) = (multOp h)^[N] (𝓕 G) := by
  induction N with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      fourier_shiftOp h, ih]

/-- On representatives, the iterated `multOp` is multiplication by `(phase h - 1)^N`. -/
theorem coeFn_multOp_iterate (h : ℂ) (N : ℕ) (F : Lp (α := ℂ) ℂ 2 volume) :
    ⇑((multOp h)^[N] F) =ᵐ[volume] fun ξ => (phase h ξ - 1) ^ N * ⇑F ξ := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    show ⇑(multFun h ((multOp h)^[n] F) - (multOp h)^[n] F)
        =ᵐ[volume] fun ξ => (phase h ξ - 1) ^ (n + 1) * ⇑F ξ
    filter_upwards [coeFn_multFun h ((multOp h)^[n] F), Lp.coeFn_sub
      (multFun h ((multOp h)^[n] F)) ((multOp h)^[n] F), ih] with ξ h1 h2 h3
    simp only [Pi.sub_apply] at h2 ⊢
    rw [h2, h1, h3, pow_succ]
    ring

/-- Two functions which agree almost everywhere have forward differences which agree almost
everywhere. -/
lemma dd_congr_ae (h : ℂ) {f g : ℂ → ℂ} (hf : f =ᵐ[volume] g) :
    dd h f =ᵐ[volume] dd h g := by
  have h1 : f ∘ (fun x : ℂ => x + h) =ᵐ[volume] g ∘ (fun x : ℂ => x + h) :=
    (measurePreserving_add_right volume h).quasiMeasurePreserving.ae_eq_comp hf
  filter_upwards [h1, hf] with x hx1 hx2
  simp only [Function.comp_apply] at hx1
  simp [dd, hx1, hx2]

lemma dd_iterate_congr_ae (h : ℂ) (N : ℕ) {f g : ℂ → ℂ} (hf : f =ᵐ[volume] g) :
    (dd h)^[N] f =ᵐ[volume] (dd h)^[N] g := by
  induction N with
  | zero => simpa using hf
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact dd_congr_ae h ih

/-- On representatives, the iterated `shiftOp` is the iterated forward difference. -/
theorem coeFn_shiftOp_iterate (h : ℂ) (N : ℕ) (G : Lp (α := ℂ) ℂ 2 volume) :
    ⇑((shiftOp h)^[N] G) =ᵐ[volume] (dd h)^[N] (⇑G) := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    show ⇑(shiftAdd h ((shiftOp h)^[n] G) - (shiftOp h)^[n] G)
        =ᵐ[volume] (dd h)^[n + 1] (⇑G)
    have h1 : ⇑(shiftAdd h ((shiftOp h)^[n] G))
        =ᵐ[volume] (⇑((shiftOp h)^[n] G)) ∘ (fun x : ℂ => x + h) :=
      coeFn_shiftAdd h _
    have h3 : (⇑((shiftOp h)^[n] G)) ∘ (fun x : ℂ => x + h)
        =ᵐ[volume] ((dd h)^[n] (⇑G)) ∘ (fun x : ℂ => x + h) :=
      (measurePreserving_add_right volume h).quasiMeasurePreserving.ae_eq_comp ih
    filter_upwards [coeFn_shiftAdd h ((shiftOp h)^[n] G), h3,
      Lp.coeFn_sub (shiftAdd h ((shiftOp h)^[n] G)) ((shiftOp h)^[n] G), ih] with x hx1 hx2 hx4 hx5
    simp only [Pi.sub_apply, Function.comp_apply] at hx1 hx2 hx4 hx5 ⊢
    rw [hx4, hx1, hx2, hx5]
    rw [Function.iterate_succ_apply']
    simp [dd]

/-! ### Plancherel in `eLpNorm` form -/

lemma eLpNorm_coeFn_eq_ofReal_norm (F : Lp (α := ℂ) ℂ 2 volume) :
    eLpNorm (⇑F) 2 volume = ENNReal.ofReal ‖F‖ := by
  rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.memLp F).eLpNorm_ne_top]

lemma eLpNorm_fourier (F : Lp (α := ℂ) ℂ 2 volume) :
    eLpNorm (⇑(𝓕 F : Lp (α := ℂ) ℂ 2 volume)) 2 volume = eLpNorm (⇑F) 2 volume := by
  rw [eLpNorm_coeFn_eq_ofReal_norm (𝓕 F), eLpNorm_coeFn_eq_ofReal_norm F, Lp.norm_fourier_eq]

/-! ### The main statement -/

/-- If the iterated forward differences of `u ∈ L²(ℂ)` satisfy `‖Δ_h^N u‖_{L²} ≤ C N ‖h‖^N`, then
the same bound holds for the function `ξ ↦ (e^{2πi⟪h,ξ⟫} - 1)^N · 𝓕u(ξ)`, where `𝓕u` is the `L²`
Fourier transform of (the `L²` class of) `u`. This is the identity `𝓕(Δ_h^N u) = (e^{i⟨h,·⟩}-1)^N 𝓕u`
together with Plancherel.

Suggested route: define `T_h : Lp ℂ 2 volume →+ Lp ℂ 2 volume` as
`Lp.compMeasurePreserving (· + h) (measurePreserving_add_right volume h)` (so `T_h F =ᵐ F ∘ (·+h)`)
and prove the multiplier identity `𝓕 (T_h F - F) = (char_h - 1) • 𝓕 F` on `Lp ℂ 2 volume` by
density: both sides are continuous (in `F`) and agree on the range of `SchwartzMap.toLpCLM`
(`SchwartzMap.denseRange_toLpCLM`), where `𝓕 (f ∘ (·+h)) = fun ξ => 𝐞 (⟪h,ξ⟫) • 𝓕 f` is
`VectorFourier.fourierIntegral_comp_add_right` (`= Real.fourier_eq`-based). Iterate, and use
`Lp.toLp_compMeasurePreserving` plus the identification of `(fun G => T_h G - G)^[N] (hu.toLp u)`
with `MemLp.toLp (((fun f => fun x => f (x + h) - f x)^[N]) u) (…)` and Plancherel
(`MeasureTheory.Lp.norm_fourier_eq`, `MeasureTheory.Lp.norm_def`). -/
theorem diffQuot_fourier_norm {u : ℂ → ℂ} (hu : MemLp u 2 volume) (C : ℕ → ℝ)
    (hC : ∀ (N : ℕ) (h : ℂ), eLpNorm (((fun f : ℂ → ℂ => fun x => f (x + h) - f x) ^[N]) u) 2 volume
        ≤ ENNReal.ofReal (C N * ‖h‖ ^ N)) :
    ∀ (N : ℕ) (h : ℂ),
      eLpNorm (fun ξ : ℂ => (((Real.fourierChar (inner ℝ h ξ) : Circle) : ℂ) - 1) ^ N
        * (𝓕 (hu.toLp u) : Lp ℂ 2 volume) ξ) 2 volume ≤ ENNReal.ofReal (C N * ‖h‖ ^ N) := by
  intro N h
  have h1 := coeFn_multOp_iterate h N (𝓕 (MemLp.toLp u hu))
  have h2 := fourier_shiftOp_iterate h N (MemLp.toLp u hu)
  have h3 := coeFn_shiftOp_iterate h N (MemLp.toLp u hu)
  have h4 := dd_iterate_congr_ae h N (MemLp.coeFn_toLp hu)
  calc eLpNorm (fun ξ : ℂ => (((Real.fourierChar (inner ℝ h ξ) : Circle) : ℂ) - 1) ^ N
        * (𝓕 (MemLp.toLp u hu) : Lp ℂ 2 volume) ξ) 2 volume
      = eLpNorm (⇑((multOp h)^[N] (𝓕 (MemLp.toLp u hu)))) 2 volume :=
        (eLpNorm_congr_ae h1).symm
    _ = eLpNorm (⇑(𝓕 ((shiftOp h)^[N] (MemLp.toLp u hu)) : Lp (α := ℂ) ℂ 2 volume)) 2 volume := by
        rw [h2]
    _ = eLpNorm (⇑((shiftOp h)^[N] (MemLp.toLp u hu))) 2 volume := eLpNorm_fourier _
    _ = eLpNorm ((dd h)^[N] (⇑(MemLp.toLp u hu))) 2 volume := eLpNorm_congr_ae h3
    _ = eLpNorm ((dd h)^[N] u) 2 volume := eLpNorm_congr_ae h4
    _ ≤ ENNReal.ofReal (C N * ‖h‖ ^ N) := hC N h

end

end Work.Beltrami
