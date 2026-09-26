import Mathlib
import Submission.Work.Asymptotics.contourLeftDefs
import Submission.Work.Asymptotics.rectInt_eq_residue
import Submission.Work.Asymptotics.kerFormDefs
import Submission.Work.Asymptotics.kerForm_edgeH
import Submission.Work.Asymptotics.continuousOn_Kfun_clean
import Submission.Work.Asymptotics.Kfun_principal_part_z_lip
import Submission.Work.Asymptotics.jInvariantFun_eq_smul_of_eq

set_option maxHeartbeats 4000000

noncomputable section

open UpperHalfPlane MeasureTheory Filter
open scoped Topology

namespace Work.Asymptotics

/-! ## Copies of the elementary lemmas of `kerFormAux`

`Submission/Work/Asymptotics/kerFormAux.lean` currently does not compile (a `field_simp`/`ring`
fragility in an unrelated residue computation), so the few elementary facts about `kerForm`
that are needed here are reproduced below under fresh names. -/

/-- `edgeV` is `i` times the complex-variable integrand `kerForm`. -/
theorem dlcc_edgeV_eq_kerForm (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (r : ℝ)
    (τ : UpperHalfPlane) (u v : ℝ) (hv : 0 < v) :
    edgeV ℓ d r τ u v
      = Complex.I * kerForm ℓ d r τ ((u : ℂ) + (v : ℂ) * Complex.I) := by
  rw [edgeV, kerForm, ofReImT_eq_ofComplex u v hv, kerExp_eq_phaseWeight_mul_gaussWeight]
  rw [mul_div_assoc', mul_div_cancel_left₀ _ Complex.I_ne_zero]

/-- **The horizontal edges of the left detour as oriented interval integrals.** -/
theorem dlcc_integral_edgeH_neg (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (r : ℝ)
    (τ : UpperHalfPlane) (ξ v : ℝ) (hξ : 0 < ξ) (hv : 0 < v) :
    (∫ u in Set.Ioo (0 : ℝ) ξ, edgeH ℓ d r τ (-u) v)
      = ∫ x : ℝ in (-ξ)..0, kerForm ℓ d r τ ((x : ℂ) + (v : ℂ) * Complex.I) := by
  have hL : (∫ u in Set.Ioo (0 : ℝ) ξ, edgeH ℓ d r τ (-u) v)
      = ∫ u : ℝ in (0 : ℝ)..ξ, edgeH ℓ d r τ (-u) v := by
    rw [intervalIntegral.integral_of_le hξ.le]
    exact MeasureTheory.setIntegral_congr_set MeasureTheory.Ioo_ae_eq_Ioc
  rw [hL]
  have hneg : (∫ x : ℝ in (0 : ℝ)..ξ,
        kerForm ℓ d r τ (((-x : ℝ) : ℂ) + (v : ℂ) * Complex.I))
      = ∫ x : ℝ in (-ξ)..((-0 : ℝ)), kerForm ℓ d r τ ((x : ℂ) + (v : ℂ) * Complex.I) :=
    intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := ξ)
      (f := fun x : ℝ => kerForm ℓ d r τ ((x : ℂ) + (v : ℂ) * Complex.I))
  simp only [neg_zero] at hneg
  rw [← hneg]
  refine intervalIntegral.integral_congr fun u _ => ?_
  exact kerForm_edgeH ℓ d r τ (-u) v hv

/-- **The vertical edge of the left detour as an oriented interval integral.** -/
theorem dlcc_integral_edgeV (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (r : ℝ)
    (τ : UpperHalfPlane) (x y₁ y₂ : ℝ) (hy₁ : 0 < y₁) (hy : y₁ < y₂) :
    (∫ v in Set.Ioo y₁ y₂, edgeV ℓ d r τ x v)
      = Complex.I * ∫ v : ℝ in y₁..y₂,
          kerForm ℓ d r τ ((x : ℂ) + (v : ℂ) * Complex.I) := by
  have hL : (∫ v in Set.Ioo y₁ y₂, edgeV ℓ d r τ x v)
      = ∫ v : ℝ in y₁..y₂, edgeV ℓ d r τ x v := by
    rw [intervalIntegral.integral_of_le hy.le,
      MeasureTheory.setIntegral_congr_set MeasureTheory.Ioo_ae_eq_Ioc]
  rw [hL, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun v hv' => ?_
  have hv0 : 0 < v := by
    have h : v ∈ Set.Icc y₁ y₂ := by rwa [Set.uIcc_of_le hy.le] at hv'
    linarith [h.1, hy₁]
  exact dlcc_edgeV_eq_kerForm ℓ d r τ x v hv0

/-- **The closed left rectangle is clean.**  If no point of the `SL(2,ℤ)`-orbit of `τ` lies in
the closed rectangle `[-ξ,0] × [c-A,c+A]`, then `j (ofComplex z) ≠ j τ` for every `z` of the
rectangle other than the (already absent) pole `τ - 1`. -/
theorem dlcc_clean (τ : UpperHalfPlane) (c A ξ : ℝ) (hcA : 0 < c - A)
    (hcl : ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (z : UpperHalfPlane),
        leftRect c A ξ z → (z ≠ γ • τ ∨ z = tauSubOne τ)) :
    ∀ z : ℂ, z ∈ leftRectℂ c A ξ → z ≠ poleℂ τ →
      Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (UpperHalfPlane.ofComplex z) := by
  intro z hz hzp hjeq
  have hzim : 0 < z.im := leftRectℂ_subset_im_pos hcA hz
  have hcoe : ((UpperHalfPlane.ofComplex z : UpperHalfPlane) : ℂ) = z := by
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos hzim, UpperHalfPlane.coe_mk]
  have hre : (UpperHalfPlane.ofComplex z).re = z.re := by
    rw [← UpperHalfPlane.coe_re, hcoe]
  have him : (UpperHalfPlane.ofComplex z).im = z.im := by
    rw [← UpperHalfPlane.coe_im, hcoe]
  have hleft : leftRect c A ξ (UpperHalfPlane.ofComplex z) := by
    simp only [leftRect, leftRectℂ, Set.mem_ofPred_eq] at hz ⊢
    rw [hre, him]
    exact hz
  obtain ⟨γ, hγ⟩ := jInvariantFun_eq_smul_of_eq
    (τ := UpperHalfPlane.ofComplex z) (w := τ) hjeq.symm
  rcases hcl γ (UpperHalfPlane.ofComplex z) hleft with h' | h'
  · exact h' hγ.symm
  · exact hzp (by rw [poleℂ, ← h', hcoe])

/-- The open left rectangle is open. -/
lemma isOpen_openLeftRectℂ' (c A ξ : ℝ) : IsOpen (openLeftRectℂ c A ξ) := by
  have h : openLeftRectℂ c A ξ = Set.Ioo (-ξ) 0 ×ℂ Set.Ioo (c - A) (c + A) := by
    ext z
    simp only [openLeftRectℂ, Complex.mem_reProdIm, Set.mem_Ioo, Set.mem_ofPred_eq]
    tauto
  rw [h]
  exact isOpen_Ioo.reProdIm isOpen_Ioo

/-- **`kerForm` is continuous on the closed rectangle minus the pole.** -/
theorem dlcc_continuousOn (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (r : ℝ) (τ : UpperHalfPlane) (c A ξ : ℝ) (hcA : 0 < c - A)
    (hclean : ∀ z : ℂ, z ∈ leftRectℂ c A ξ → z ≠ poleℂ τ →
      Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (UpperHalfPlane.ofComplex z)) :
    ContinuousOn (kerForm ℓ d r τ) (leftRectℂ c A ξ \ {poleℂ τ}) := by
  have hsub : (leftRectℂ c A ξ \ {poleℂ τ}) ⊆ {z : ℂ | 0 < z.im} :=
    fun z hz => leftRectℂ_subset_im_pos hcA hz.1
  have hof : ContinuousOn (fun z : ℂ => UpperHalfPlane.ofComplex z)
      (leftRectℂ c A ξ \ {poleℂ τ}) :=
    continuousOn_ofComplex_of_im_pos.mono hsub
  have hgc : ContinuousOn (fun z : ℂ => (τ, UpperHalfPlane.ofComplex z))
      (leftRectℂ c A ξ \ {poleℂ τ}) :=
    ContinuousOn.prodMk (f := fun _ : ℂ => τ) (g := fun z : ℂ => UpperHalfPlane.ofComplex z)
      continuousOn_const hof
  have hK := (continuousOn_Kfun_clean ℓ d hd).comp hgc (fun z hz => by
    have h := hclean z hz.1 (by simpa using hz.2)
    simpa using h)
  have hexp : ContinuousOn (fun z : ℂ => kerExp r z) (leftRectℂ c A ξ \ {poleℂ τ}) := by
    have hcont : Continuous fun z : ℂ => kerExp r z := by
      unfold kerExp; fun_prop
    exact hcont.continuousOn
  have hmain := (hK.mul hexp).div_const Complex.I
  refine hmain.congr (fun z hz => ?_)
  simp [kerForm, Function.comp]

/-- **`kerForm` is holomorphic on the open rectangle off the pole.** -/
theorem dlcc_differentiableAt (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (r : ℝ) (τ : UpperHalfPlane) (c A ξ : ℝ) (hcA : 0 < c - A)
    (hclean : ∀ z : ℂ, z ∈ leftRectℂ c A ξ → z ≠ poleℂ τ →
      Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (UpperHalfPlane.ofComplex z)) :
    ∀ z : ℂ, z ∈ openLeftRectℂ c A ξ → z ≠ poleℂ τ →
      DifferentiableAt ℂ (kerForm ℓ d r τ) z := by
  intro z hz hzp
  have hleft : z ∈ leftRectℂ c A ξ := openLeftRectℂ_subset_leftRectℂ c A ξ hz
  have hzim : 0 < z.im := leftRectℂ_subset_im_pos hcA hleft
  have hU : {w : ℂ | 0 < w.im} ∈ 𝓝 z :=
    (isOpen_lt continuous_const Complex.continuous_im).mem_nhds hzim
  have hne : Work.Kernels.jInvariantFun τ
      ≠ Work.Kernels.jInvariantFun (UpperHalfPlane.ofComplex z) := hclean z hleft hzp
  have hA : DifferentiableAt ℂ
      (fun w : ℂ => AfunFun ℓ d τ (UpperHalfPlane.ofComplex w)) z := by
    have hhol : DifferentiableOn ℂ
        (fun w : ℂ => AfunFun ℓ d τ (UpperHalfPlane.ofComplex w)) {w : ℂ | 0 < w.im} := by
      have h := (UpperHalfPlane.mdifferentiable_iff
        (f := fun w : UpperHalfPlane => AfunFun ℓ d τ w)).mp
        (mdifferentiable_AfunFun_snd ℓ d hd τ)
      simpa [Function.comp_def] using h
    exact hhol.differentiableAt hU
  have hJ : DifferentiableAt ℂ
      (fun w : ℂ => Work.Kernels.jInvariantFun (UpperHalfPlane.ofComplex w)) z := by
    have hhol : DifferentiableOn ℂ
        (fun w : ℂ => Work.Kernels.jInvariantFun (UpperHalfPlane.ofComplex w))
        {w : ℂ | 0 < w.im} := by
      have h := (UpperHalfPlane.mdifferentiable_iff
        (f := Work.Kernels.jInvariantFun)).mp mdifferentiable_jInvariantFun
      simpa [Function.comp_def] using h
    exact hhol.differentiableAt hU
  have hexp : DifferentiableAt ℂ (fun w : ℂ => kerExp r w) z := by
    simp only [kerExp]
    fun_prop
  have hΦ : DifferentiableAt ℂ (fun w : ℂ =>
      AfunFun ℓ d τ (UpperHalfPlane.ofComplex w)
        / (Work.Kernels.jInvariantFun τ
            - Work.Kernels.jInvariantFun (UpperHalfPlane.ofComplex w))
        * kerExp r w / Complex.I) z :=
    (((hA.div ((differentiableAt_const (c := Work.Kernels.jInvariantFun τ)).sub hJ)
      (sub_ne_zero.mpr hne)).mul hexp)).div_const Complex.I
  refine (Filter.EventuallyEq.differentiableAt_iff ?_).mpr hΦ
  have hmem : openLeftRectℂ c A ξ \ {poleℂ τ} ∈ 𝓝 z :=
    ((isOpen_openLeftRectℂ' c A ξ).inter isOpen_compl_singleton).mem_nhds ⟨hz, hzp⟩
  filter_upwards [hmem] with w hw
  have hwl : w ∈ leftRectℂ c A ξ := openLeftRectℂ_subset_leftRectℂ c A ξ hw.1
  have hwne : Work.Kernels.jInvariantFun τ
      ≠ Work.Kernels.jInvariantFun (UpperHalfPlane.ofComplex w) := hclean w hwl hw.2
  simp only [kerForm]
  rw [show Work.Kernels.Kfun ℓ d τ (UpperHalfPlane.ofComplex w)
      = AfunFun ℓ d τ (UpperHalfPlane.ofComplex w)
        / (Work.Kernels.jInvariantFun τ
            - Work.Kernels.jInvariantFun (UpperHalfPlane.ofComplex w)) by
    rw [eq_div_iff (sub_ne_zero.mpr hwne)]
    exact Kfun_mul_slope_eq_AfunFun ℓ d hd τ (UpperHalfPlane.ofComplex w) hwne]

/-! ## The pole `τ - 1` is in the orbit -/

/-- `T⁻¹` acts on `ℍ` as the translation by `-1`, so `τ - 1` is an `SL(2,ℤ)`-translate of `τ`. -/
lemma Tinv_smul_eq_tauSubOne' (τ : UpperHalfPlane) :
    (ModularGroup.T⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℤ) • τ = tauSubOne τ := by
  apply UpperHalfPlane.ext
  rw [show (ModularGroup.T⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ModularGroup.T ^ (-1 : ℤ)
      from by rw [zpow_neg_one],
    UpperHalfPlane.modular_T_zpow_smul, UpperHalfPlane.coe_vadd, tauSubOne_coe]
  push_cast
  ring

/-- **The pole `τ - 1` is not in a rectangle whose points avoid the orbit of `τ`.** -/
lemma poleℂ_notMem_leftRectℂ (τ : UpperHalfPlane) (c A ξ : ℝ) (hcA : 0 < c - A)
    (hcl : ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (z : UpperHalfPlane),
        leftRect c A ξ z → z ≠ γ • τ) :
    poleℂ τ ∉ leftRectℂ c A ξ := by
  intro hmem
  have hw : UpperHalfPlane.ofComplex (poleℂ τ) = tauSubOne τ := by
    rw [poleℂ, UpperHalfPlane.ofComplex_apply]
  have hcoe : ((UpperHalfPlane.ofComplex (poleℂ τ) : UpperHalfPlane) : ℂ) = poleℂ τ := by
    rw [hw, poleℂ]
  have hre : (UpperHalfPlane.ofComplex (poleℂ τ)).re = (poleℂ τ).re := by
    rw [← UpperHalfPlane.coe_re, hcoe]
  have him2 : (UpperHalfPlane.ofComplex (poleℂ τ)).im = (poleℂ τ).im := by
    rw [← UpperHalfPlane.coe_im, hcoe]
  have hleft : leftRect c A ξ (UpperHalfPlane.ofComplex (poleℂ τ)) := by
    simp only [leftRect, leftRectℂ, Set.mem_ofPred_eq] at hmem ⊢
    rw [hre, him2]
    exact hmem
  have hne := hcl (ModularGroup.T⁻¹) (UpperHalfPlane.ofComplex (poleℂ τ)) hleft
  rw [hw, Tinv_smul_eq_tauSubOne' τ] at hne
  exact hne rfl

/-- For `d ∉ {8,24}` the kernel `Kfun` vanishes identically (both `Υ_±^{(d)}` are `0`). -/
lemma Kfun_eq_zero_of_ne {d : ℕ} (h8 : d ≠ 8) (h24 : d ≠ 24)
    (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) :
    Work.Kernels.Kfun ℓ d τ z = 0 := by
  have hp : Work.Kernels.UpsilonPlus d τ z = 0 := by
    ext i j
    simp [Work.Kernels.UpsilonPlus, h8, h24]
  have hm : Work.Kernels.UpsilonMinus d τ z = 0 := by
    ext i j
    simp [Work.Kernels.UpsilonMinus, h8, h24]
  simp [Work.Kernels.Kfun, Work.Kernels.KPlus, Work.Kernels.KMinus, hp, hm]

/-! ## The main theorem -/

/-- **The left detour equals the replaced interval integral, pole-free case.** -/
theorem detourLeftC_eq_interval_of_clean (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    {r c A ξ ε t₀ : ℝ} (ht₀ : 0 < t₀) (hε : 0 < ε) (hA : 0 < A) (hξ : 0 < ξ) (hcA : 0 < c - A)
    (hcl : ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI t₀ ht₀) < ε → τ.re < 1 →
      ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (z : UpperHalfPlane),
        Work.Asymptotics.leftRect c A ξ z → z ≠ γ • τ) :
    ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI t₀ ht₀) < ε → τ.re < 1 →
      Work.Asymptotics.detourLeftC ℓ d r c A ξ τ
        = ∫ v in Set.Ioo (c - A) (c + A), Work.Asymptotics.edgeV ℓ d r τ 0 v := by
  intro τ hτball hτre
  by_cases hd : d = 8 ∨ d = 24
  · have hcl' : ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (z : UpperHalfPlane),
        leftRect c A ξ z → (z ≠ γ • τ ∨ z = tauSubOne τ) :=
      fun γ z hz => Or.inl (hcl τ hτball hτre γ z hz)
    have hcleanish := dlcc_clean τ c A ξ hcA hcl'
    have hPoleNotMem : poleℂ τ ∉ leftRectℂ c A ξ :=
      poleℂ_notMem_leftRectℂ τ c A ξ hcA (fun γ z hz => hcl τ hτball hτre γ z hz)
    have hcontRect : ContinuousOn (kerForm ℓ d r τ) (leftRectℂ c A ξ) := by
      have h := dlcc_continuousOn ℓ d hd r τ c A ξ hcA hcleanish
      rwa [Set.sdiff_singleton_eq_self hPoleNotMem] at h
    set z₀ : ℂ := ((-ξ / 2 : ℝ) : ℂ) + ((c : ℝ) : ℂ) * Complex.I with hz₀
    have hz₀re : z₀.re = -ξ / 2 := by rw [hz₀]; simp
    have hz₀im : z₀.im = c := by rw [hz₀]; simp
    have hz₀open : z₀ ∈ openLeftRectℂ c A ξ := by
      simp only [openLeftRectℂ, Set.mem_ofPred_eq]
      exact ⟨by rw [hz₀re]; linarith, by rw [hz₀re]; linarith,
        by rw [hz₀im]; linarith, by rw [hz₀im]; linarith⟩
    have hmem₀ : leftRectℂ c A ξ ∈ 𝓝 z₀ :=
      Filter.mem_of_superset ((isOpen_openLeftRectℂ' c A ξ).mem_nhds hz₀open)
        (openLeftRectℂ_subset_leftRectℂ c A ξ)
    have hcont : ContinuousOn (kerForm ℓ d r τ) (leftRectℂ c A ξ \ {z₀}) :=
      hcontRect.mono Set.sdiff_subset
    have hhol : ∀ z : ℂ, (-ξ) < z.re → z.re < 0 → c - A < z.im → z.im < c + A → z ≠ z₀ →
        DifferentiableAt ℂ (kerForm ℓ d r τ) z := by
      intro z h1 h2 h3 h4 _
      refine dlcc_differentiableAt ℓ d hd r τ c A ξ hcA hcleanish z ⟨h1, h2, h3, h4⟩ ?_
      intro hpe
      exact hPoleNotMem (hpe ▸ openLeftRectℂ_subset_leftRectℂ c A ξ ⟨h1, h2, h3, h4⟩)
    have hres : Filter.Tendsto (fun z : ℂ => (z - z₀) * kerForm ℓ d r τ z)
        (nhdsWithin z₀ {z₀}ᶜ) (nhds 0) := by
      have h1 : Filter.Tendsto (fun z : ℂ => z - z₀) (𝓝 z₀) (𝓝 0) := by
        have h : Filter.Tendsto (fun z : ℂ => z - z₀) (𝓝 z₀) (𝓝 (z₀ - z₀)) :=
          (continuous_id.sub continuous_const).tendsto z₀
        simpa using h
      have h2 : Filter.Tendsto (fun z : ℂ => kerForm ℓ d r τ z) (𝓝 z₀)
          (𝓝 (kerForm ℓ d r τ z₀)) := hcontRect.continuousAt hmem₀
      have h3 := h1.mul h2
      have h3' : Filter.Tendsto (fun z : ℂ => (z - z₀) * kerForm ℓ d r τ z) (𝓝 z₀)
          (𝓝 (0 * kerForm ℓ d r τ z₀)) := h3
      rw [zero_mul] at h3'
      exact h3'.mono_left nhdsWithin_le_nhds
    have hrect := rectInt_eq_residue (kerForm ℓ d r τ) z₀ 0 (-ξ) 0 (c - A) (c + A)
      (by rw [hz₀re]; linarith) (by rw [hz₀re]; linarith)
      (by rw [hz₀im]; linarith) (by rw [hz₀im]; linarith) hcont hhol hres
    rw [mul_zero] at hrect
    rw [dlcc_integral_edgeV ℓ d r τ 0 (c - A) (c + A) hcA (by linarith)]
    rw [detourLeftC,
      dlcc_integral_edgeH_neg ℓ d r τ ξ (c - A) hξ hcA,
      dlcc_integral_edgeV ℓ d r τ (-ξ) (c - A) (c + A) hcA (by linarith),
      dlcc_integral_edgeH_neg ℓ d r τ ξ (c + A) hξ (by linarith)]
    linear_combination -hrect
  · simp only [not_or] at hd
    have hK (w : UpperHalfPlane) : Work.Kernels.Kfun ℓ d τ w = 0 :=
      Kfun_eq_zero_of_ne hd.1 hd.2 ℓ τ w
    have hdet : detourLeftC ℓ d r c A ξ τ = 0 := by
      simp [detourLeftC, edgeH, edgeV, hK]
    have hint : (∫ v in Set.Ioo (c - A) (c + A), edgeV ℓ d r τ 0 v) = 0 := by
      simp [edgeV, hK]
    rw [hdet, hint]

end Work.Asymptotics
