import Mathlib
import Submission.Work.RPB.Defs
import Submission.Work.RPB.B5.kappaDefs
import Submission.Work.RPB.B5.kappaSmallAux
import Submission.Work.RPB.B4.periodic_reduce
import Submission.Work.RPB.B4.periodic_deriv
import Submission.Work.RPB.B5.chord_linear_bound
import Submission.Work.RPB.B5.pos_min_of_compact
import Submission.Work.RPB.B5.chart_uproj_close
import Submission.Work.RPB.B5.signedArea_scale_shift
import Submission.Work.RPB.B5.embedded_family_close
import Submission.Work.RPB.B5.contDiffOn_uproj_comp
import Submission.Work.RPB.B5.CI_family_bound
import Submission.Work.RPB.B5.kappa_uproj_W_zero
import Submission.Work.RPB.B5.kappa_chartSlice_contDiff
import Submission.Work.RPB.B5.signedArea_pos_of_close
import Submission.Work.RPB.B5.kshape_close

namespace Work.RPB.B5

open RectangularPegProblem
open Manifold Complex Real
open scoped ContDiff Topology Interval

/-! ## Small pieces about the `t`-dependence of the shape -/

/-- The slice `t ↦ ktarg δ k σ t` is `C¹` (it is `t ↦ krd σ · e^{i (t + kphc)}`). -/
theorem ksmall_contDiff_ktarg_slice (δ : ℝ) (k : ℤ) (σ : ℝ) :
    ContDiff ℝ 1 (fun t : ℝ => ktarg δ k σ t) := by
  unfold ktarg
  have h1 : ContDiff ℝ 1 (fun t : ℝ => (↑t : ℂ) + ↑(kphc δ k σ)) :=
    ((Complex.ofRealCLM.contDiff).comp contDiff_id).add contDiff_const
  have h : ContDiff ℝ 1 (fun t : ℝ => (↑t + ↑(kphc δ k σ)) * Complex.I) :=
    h1.mul contDiff_const
  exact contDiff_const.mul ((Complex.contDiff_exp (𝕜 := ℝ)).comp h)

/-- The slice `t ↦ kfsh CI δ k τ σ t` is `C¹`. -/
theorem ksmall_contDiff_kfsh_slice (CI : Work.RPV.CurveIsotopy) (δ : ℝ) (k : ℤ) (τ σ : ℝ) :
    ContDiff ℝ 1 (fun t : ℝ => kfsh CI δ k τ σ t) := by
  unfold kfsh
  have h1 : ContDiff ℝ 1 (fun z : ℝ × ℝ => CI.c z.1 z.2) := CI.smooth.of_le (by norm_num)
  have h2 : ContDiff ℝ 1 (fun t : ℝ => (krpf δ σ * τ, t + kphc δ k σ)) :=
    contDiff_const.prodMk (contDiff_id.add contDiff_const)
  have h3 := h1.comp h2
  simp only [Function.comp_def] at h3
  exact contDiff_const.mul h3

/-- `2π`-periodicity of the glued shape in `t`. -/
theorem ksmall_kshape_periodic (CI : Work.RPV.CurveIsotopy) (W : ℝ → ℝ → ℝ → Work.RPV.PS)
    (ρh : ℝ → ℝ → ℝ → ℝ) (δ : ℝ) (k : ℤ)
    (hWper : ∀ τ t ρ, W τ (t + 2 * Real.pi) ρ = Work.RPV.Tk 1 (W τ t ρ))
    (hρhper : ∀ τ t σ, ρh τ (t + 2 * Real.pi) σ = ρh τ t σ) :
    ∀ τ σ t, kshape CI W ρh δ k τ σ (t + 2 * Real.pi) = kshape CI W ρh δ k τ σ t := by
  intro τ σ t
  have huh : ∀ X : Work.RPV.PS,
      Work.RPV.uproj (Work.RPV.Tk 1 X) = Work.RPV.uproj X := by
    intro X; rw [Work.RPV.uproj_Tk]
  have hkn : ∀ τ' : ℝ, Work.RPV.uproj (W τ' (t + 2 * Real.pi) (ρh τ' (t + 2 * Real.pi) (kclamp δ σ)))
      = Work.RPV.uproj (W τ' t (ρh τ' t (kclamp δ σ))) := by
    intro τ'
    rw [hρhper τ' t (kclamp δ σ), hWper τ' t (ρh τ' t (kclamp δ σ)), huh]
  have hkt : ktarg δ k σ (t + 2 * Real.pi) = ktarg δ k σ t := by
    have harg : (↑(t + 2 * Real.pi) : ℂ) + ↑(kphc δ k σ)
        = (↑t + ↑(kphc δ k σ)) + 2 * (Real.pi : ℂ) := by
      push_cast; ring
    simp only [ktarg, harg]
    rw [add_mul, Complex.exp_periodic]
  have hkf : kfsh CI δ k τ σ (t + 2 * Real.pi) = kfsh CI δ k τ σ t := by
    unfold kfsh
    congr 1
    rw [show t + 2 * Real.pi + kphc δ k σ = (t + kphc δ k σ) + 2 * Real.pi by ring]
    exact CI.per (krpf δ σ * τ) (t + kphc δ k σ)
  have hnear : knear CI W ρh δ k τ σ (t + 2 * Real.pi) = knear CI W ρh δ k τ σ t := by
    unfold knear
    rw [hkn τ, hkn 0, hkt]
  unfold kshape
  rw [hnear, hkf]

/-- The `t`-slice of the shape is `C¹` as soon as the two chart slices appearing in `knear` are. -/
theorem ksmall_contDiff_kshape_slice (CI : Work.RPV.CurveIsotopy) (W : ℝ → ℝ → ℝ → Work.RPV.PS)
    (ρh : ℝ → ℝ → ℝ → ℝ) (δ : ℝ) (k : ℤ) (τ σ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) 1)
    (hcl : |kclamp δ σ| ≤ δ)
    (hslice : ∀ τ' ∈ Set.Icc (0 : ℝ) 1, ∀ σ' : ℝ, |σ'| ≤ δ →
      ContDiff ℝ 1 (fun t : ℝ => Work.RPV.uproj (W τ' t (ρh τ' t σ')))) :
    ContDiff ℝ 1 (fun t : ℝ => kshape CI W ρh δ k τ σ t) := by
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
  have h1 := hslice τ hτ (kclamp δ σ) hcl
  have h2 := hslice 0 h0 (kclamp δ σ) hcl
  have h3 := ksmall_contDiff_ktarg_slice δ k σ
  have h4 := ksmall_contDiff_kfsh_slice CI δ k τ σ
  unfold kshape knear
  fun_prop

/-- The signed area of the reference family `√2 • CI.c τ` is `2π`. -/
theorem ksmall_signedArea_kGam (CI : Work.RPV.CurveIsotopy) (τ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    Work.RPB.signedArea (fun t : ℝ => kGam CI τ t) = 2 * Real.pi := by
  have h := signedArea_scale_shift CI τ (Real.sqrt 2) 0 hτ
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)] at h
  simpa [kGam] using h

theorem kappa_shape_geom_small (CI : Work.RPV.CurveIsotopy) (a : ℝ → ℝ → ℝ → ℝ)
    (ha : Work.RPB.IsChordPhase CI.c a)
    (ρ₀ : ℝ) (hρ₀ : 0 < ρ₀) (W : ℝ → ℝ → ℝ → Work.RPV.PS) (ρh : ℝ → ℝ → ℝ → ℝ)
    (κ : ℝ) (hκ : 0 < κ)
    (hW : ContDiffOn ℝ 12 (fun z : ℝ × (ℝ × ℝ) => W z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-ρ₀) ρ₀))
    (hWchord : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ r ∈ Set.Ioc (0 : ℝ) (Real.pi / 2),
      W τ t (r ^ 2) = Work.RPB.chordSurf CI.c a τ t r)
    (hWper : ∀ τ t ρ, W τ (t + 2 * Real.pi) ρ = Work.RPV.Tk 1 (W τ t ρ))
    (hρh : ContDiffOn ℝ 12 (fun z : ℝ × (ℝ × ℝ) => ρh z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-κ) κ))
    (hρh0 : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ρh τ t 0 = 0)
    (hρhv : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ σ ∈ Set.Ioo (-κ) κ,
      ρh τ t σ ∈ Set.Ioo (-ρ₀) ρ₀)
    (hρhl : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ σ ∈ Set.Ioo (-κ) κ,
      Work.RPV.K0 (W τ t (ρh τ t σ)) + 1 = -σ)
    (hρhper : ∀ τ t σ, ρh τ (t + 2 * Real.pi) σ = ρh τ t σ)
    (k : ℤ) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ κ ∧
      ∀ δ ∈ Set.Ioo (0 : ℝ) δ₀, ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ σ ∈ Set.Icc (0 : ℝ) δ,
        0 < Work.RPB.B5.karS CI W ρh δ k τ σ ∧
        (∀ t : ℝ, deriv (fun s : ℝ => Work.RPB.B5.kshape CI W ρh δ k τ σ s) t ≠ 0) ∧
        (∀ t t' : ℝ, Work.RPB.B5.kshape CI W ρh δ k τ σ t
            = Work.RPB.B5.kshape CI W ρh δ k τ σ t' →
          ∃ m : ℤ, t' = t + 2 * Real.pi * m) := by
  -- ## Step 1: a uniform bound for the curve isotopy
  obtain ⟨M₀, hM₀pos, hM₀b⟩ := CI_family_bound CI
  set M : ℝ := max 1 (Real.sqrt 2 * M₀) with hMdef
  have hM1 : 1 ≤ M := le_max_left _ _
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM1
  have hMg₀ : M₀ ≤ M := by
    have h1 : (1 : ℝ) ≤ Real.sqrt 2 := Real.one_le_sqrt.mpr (by norm_num)
    have h2 : M₀ ≤ Real.sqrt 2 * M₀ := by nlinarith [hM₀pos.le, h1]
    exact le_trans h2 (le_max_right _ _)
  have hMg₂ : Real.sqrt 2 * M₀ ≤ M := le_max_right _ _
  have hbound : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ,
      ‖CI.c τ t‖ ≤ M ∧ ‖deriv (fun s : ℝ => CI.c τ s) t‖ ≤ M := by
    intro τ hτ t
    obtain ⟨h1, h2⟩ := hM₀b τ hτ t
    exact ⟨le_trans h1 hMg₀, le_trans h2 hMg₀⟩
  -- ## Step 2: the reference family `√2 • CI.c` is a family of embedded curves
  have hinj : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t t' : ℝ,
      kGam CI τ t = kGam CI τ t' → ∃ m : ℤ, t' = t + 2 * Real.pi * m := by
    intro τ hτ t t' h
    refine CI.inj τ hτ t t' ?_
    have hne : (Real.sqrt 2 : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
    exact mul_left_cancel₀ hne h
  have hderiv : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ,
      deriv (fun s : ℝ => kGam CI τ s) t ≠ 0 := fun τ hτ t => deriv_kGam_ne CI τ hτ t
  obtain ⟨δe, hδepos, hemb⟩ :=
    embedded_family_close (fun τ t => kGam CI τ t) (contDiff_kGam CI)
      (fun τ t => kGam_per CI τ t) hinj hderiv
  -- ## Step 3: uniform `C¹`-stability of positivity of the signed area
  have hbγ : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ‖kGam CI τ t‖ ≤ M := by
    intro τ hτ t
    have h1 : ‖kGam CI τ t‖ = Real.sqrt 2 * ‖CI.c τ t‖ := by
      rw [kGam_apply, norm_mul]
      congr 1
      simp
    rw [h1]
    exact le_trans (mul_le_mul_of_nonneg_left (hM₀b τ hτ t).1 (Real.sqrt_nonneg 2)) hMg₂
  have hbγ' : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ‖deriv (fun s : ℝ => kGam CI τ s) t‖ ≤ M := by
    intro τ hτ t
    rw [deriv_kGam, norm_mul]
    have h2 : ‖(Real.sqrt 2 : ℂ)‖ = Real.sqrt 2 := by simp
    rw [h2]
    exact le_trans (mul_le_mul_of_nonneg_left (hM₀b τ hτ t).2 (Real.sqrt_nonneg 2)) hMg₂
  have hpos : ∃ a : ℝ, 0 < a ∧ ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      a ≤ Work.RPB.signedArea (fun t : ℝ => kGam CI τ t) :=
    ⟨2 * Real.pi, by positivity, fun τ hτ => le_of_eq (ksmall_signedArea_kGam CI τ hτ).symm⟩
  obtain ⟨εa, hεapos, harea⟩ :=
    signedArea_pos_of_close (fun τ t => kGam CI τ t) M hMpos
      (fun τ _ => contDiff_kGam_slice CI τ) hbγ hbγ' hpos
  -- ## Step 4: the common smallness threshold
  set A : ℝ := min δe εa with hAdef
  have hApos : 0 < A := lt_min hδepos hεapos
  have hAleδe : A ≤ δe := min_le_left _ _
  have hAleεa : A ≤ εa := min_le_right _ _
  -- ## Step 5: the chart is `C¹`-close to `√2 • CI.c` for small levels
  set εκ : ℝ := min κ ρ₀ with hεκdef
  have hεκpos : 0 < εκ := lt_min hκ hρ₀
  have hWc : ContDiffOn ℝ 1 (fun z : ℝ × (ℝ × ℝ) => W z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-εκ) εκ) := by
    refine (hW.mono ?_).of_le (by norm_num)
    intro z hz
    obtain ⟨h1, h2, h3⟩ := hz
    exact ⟨h1, h2, ⟨by linarith [h3.1, min_le_right κ ρ₀],
      by linarith [h3.2, min_le_right κ ρ₀]⟩⟩
  have hρhc : ContDiffOn ℝ 1 (fun z : ℝ × (ℝ × ℝ) => ρh z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-εκ) εκ) := by
    refine (hρh.mono ?_).of_le (by norm_num)
    intro z hz
    obtain ⟨h1, h2, h3⟩ := hz
    exact ⟨h1, h2, ⟨by linarith [h3.1, min_le_left κ ρ₀],
      by linarith [h3.2, min_le_left κ ρ₀]⟩⟩
  have hW0 : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ,
      Work.RPV.uproj (W τ t (ρh τ t 0)) = (Real.sqrt 2 : ℂ) * CI.c τ t := by
    intro τ hτ t
    rw [hρh0 τ hτ t]
    exact kappa_uproj_W_zero CI a hρ₀ (hW.of_le (by norm_num)) hWchord τ hτ t
  obtain ⟨ε', hε'pos, hε'le, hchart0⟩ :=
    chart_uproj_close (CI := CI) (W := W) (rho := ρh) (ε := εκ) hεκpos hWc hρhc
      hρh0 hρhper hWper hW0 (A / 8) (by linarith)
  -- ## Step 6: smoothness of the chart slices
  set δ' : ℝ := εκ / 4 with hδ'def
  have hδ'pos : 0 < δ' := by rw [hδ'def]; linarith
  have hδ'κ : 2 * δ' ≤ κ := by rw [hδ'def]; linarith [min_le_left κ ρ₀]
  have hδ'ρ : 2 * δ' ≤ ρ₀ := by rw [hδ'def]; linarith [min_le_right κ ρ₀]
  have hsliceAll := kappa_chartSlice_contDiff W ρh hρ₀ hκ hW hρh hρhv (δ := δ')
    hδ'pos hδ'κ hδ'ρ
  -- ## Step 7: the threshold `δ₀`
  refine ⟨min δ' (min ε' (A / (8 * Real.sqrt 2 * M))), ?_, ?_, ?_⟩
  · have h1 : 0 < A / (8 * Real.sqrt 2 * M) := by positivity
    positivity
  · calc min δ' (min ε' (A / (8 * Real.sqrt 2 * M))) ≤ δ' := min_le_left _ _
      _ ≤ κ := by rw [hδ'def]; linarith [min_le_left κ ρ₀]
  · intro δ hδ τ hτ σ hσ
    rw [Set.mem_Ioo] at hδ
    obtain ⟨hδpos, hδlt⟩ := hδ
    have hδδ' : δ < δ' := lt_of_lt_of_le hδlt (min_le_left _ _)
    have hδε' : δ < ε' := lt_of_lt_of_le hδlt (le_trans (min_le_right _ _) (min_le_left _ _))
    have hδA : δ < A / (8 * Real.sqrt 2 * M) :=
      lt_of_lt_of_le hδlt (le_trans (min_le_right _ _) (min_le_right _ _))
    have hδM : Real.sqrt 2 * δ * M ≤ A / 8 := by
      have hclear : δ * (8 * Real.sqrt 2 * M) < A := by
        rw [lt_div_iff₀ (by positivity : (0 : ℝ) < 8 * Real.sqrt 2 * M)] at hδA
        exact hδA
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 8)]
      nlinarith [hclear]
    have hchartC : ∀ τ' ∈ Set.Icc (0 : ℝ) 1, ∀ σ' : ℝ, |σ'| ≤ δ → ∀ t : ℝ,
        ‖Work.RPV.uproj (W τ' t (ρh τ' t σ')) - (Real.sqrt 2 : ℂ) * CI.c τ' t‖ < A / 8 ∧
        ‖deriv (fun u : ℝ => Work.RPV.uproj (W τ' u (ρh τ' u σ'))) t
          - deriv (fun u : ℝ => (Real.sqrt 2 : ℂ) * CI.c τ' u) t‖ < A / 8 := by
      intro τ' hτ' σ' hσ' t
      exact hchart0 τ' hτ' σ' (le_of_lt (lt_of_le_of_lt hσ' hδε')) t
    have hsliceC : ∀ τ' ∈ Set.Icc (0 : ℝ) 1, ∀ σ' : ℝ, |σ'| ≤ δ →
        ContDiff ℝ 1 (fun t : ℝ => Work.RPV.uproj (W τ' t (ρh τ' t σ'))) := by
      intro τ' hτ' σ' hσ'
      have h1 : |σ'| < 2 * δ' := by linarith [hσ', hδδ', hδ'pos]
      exact hsliceAll τ' hτ' σ' (Set.mem_Ioo.mpr ⟨(abs_lt.mp h1).1, (abs_lt.mp h1).2⟩)
    have hcl := kshape_close CI W ρh δ k A hApos M hMpos hδpos hM1 hδM hchartC hsliceC hbound
    have hclτσ := hcl τ hτ σ hσ
    have hcs : ContDiff ℝ 1 (fun t : ℝ => Work.RPB.B5.kshape CI W ρh δ k τ σ t) :=
      ksmall_contDiff_kshape_slice CI W ρh δ k τ σ hτ (abs_kclamp_le hδpos) hsliceC
    -- the perturbation `η = kshape - √2 • CI.c`
    have hηper : ∀ t : ℝ,
        (fun u : ℝ => Work.RPB.B5.kshape CI W ρh δ k τ σ u - kGam CI τ u) (t + 2 * Real.pi)
          = (fun u : ℝ => Work.RPB.B5.kshape CI W ρh δ k τ σ u - kGam CI τ u) t := by
      intro t
      simp only []
      rw [ksmall_kshape_periodic CI W ρh δ k hWper hρhper τ σ t, kGam_per CI τ t]
    have hηcd : ContDiff ℝ 1
        (fun u : ℝ => Work.RPB.B5.kshape CI W ρh δ k τ σ u - kGam CI τ u) :=
      hcs.sub (contDiff_kGam_slice CI τ)
    have hηsup : ∀ u : ℝ,
        ‖Work.RPB.B5.kshape CI W ρh δ k τ σ u - kGam CI τ u‖ < δe := by
      intro u
      have h := (hclτσ u).1
      exact lt_of_lt_of_le (by simpa only [kGam] using h) hAleδe
    have hηder : ∀ u : ℝ,
        ‖deriv (fun s : ℝ => Work.RPB.B5.kshape CI W ρh δ k τ σ s - kGam CI τ s) u‖ < δe := by
      intro u
      have h := (hclτσ u).2
      have hfun : (fun s : ℝ => Work.RPB.B5.kshape CI W ρh δ k τ σ s - kGam CI τ s)
          = ((fun s : ℝ => Work.RPB.B5.kshape CI W ρh δ k τ σ s)
              - (fun s : ℝ => kGam CI τ s)) := rfl
      rw [hfun, deriv_sub (hcs.contDiffAt.differentiableAt (by norm_num))
        ((contDiff_kGam_slice CI τ).contDiffAt.differentiableAt (by norm_num))]
      exact lt_of_lt_of_le (by simpa only [kGam] using h) hAleδe
    obtain ⟨himm, hinj2⟩ := hemb τ hτ
      (fun u : ℝ => Work.RPB.B5.kshape CI W ρh δ k τ σ u - kGam CI τ u)
      hηper hηcd hηsup hηder
    refine ⟨?_, ?_, ?_⟩
    · show 0 < Work.RPB.signedArea (fun t : ℝ => Work.RPB.B5.kshape CI W ρh δ k τ σ t)
      refine harea τ hτ (fun t : ℝ => Work.RPB.B5.kshape CI W ρh δ k τ σ t) hcs ?_ ?_
      · intro t
        have h := (hclτσ t).1
        exact lt_of_lt_of_le (by simpa only [kGam] using h) hAleεa
      · intro t
        have h := (hclτσ t).2
        exact lt_of_lt_of_le (by simpa only [kGam] using h) hAleεa
    · intro t
      have hfun : (fun s : ℝ => (fun τ t => kGam CI τ t) τ s
            + (fun u : ℝ => Work.RPB.B5.kshape CI W ρh δ k τ σ u - kGam CI τ u) s)
          = (fun s : ℝ => Work.RPB.B5.kshape CI W ρh δ k τ σ s) := by
        funext s
        simp only []
        ring
      rw [hfun] at himm
      exact himm t
    · intro t t' h
      refine hinj2 t t' ?_
      have h2 : (fun τ t => kGam CI τ t) τ t
            + (Work.RPB.B5.kshape CI W ρh δ k τ σ t - kGam CI τ t)
          = (fun τ t => kGam CI τ t) τ t'
            + (Work.RPB.B5.kshape CI W ρh δ k τ σ t' - kGam CI τ t') := by
        rw [h]; ring
      exact h2

end Work.RPB.B5
