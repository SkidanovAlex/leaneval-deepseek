import Mathlib
import Submission.Work.Asymptotics.removable_vertical_line
import Submission.Work.Asymptotics.residue_rectangle

namespace Work.Asymptotics

open Filter MeasureTheory intervalIntegral Topology
open scoped Topology

/-- A point of the form `x + y·I` is different from `z₀` as soon as `y ≠ z₀.im`. -/
lemma add_ofReal_mul_I_ne_of_im {z₀ : ℂ} {y : ℝ} (hy : y ≠ z₀.im) (x : ℝ) :
    ((x : ℂ) + (y : ℂ) * Complex.I) ≠ z₀ := by
  intro h
  have h1 : ((x : ℂ) + (y : ℂ) * Complex.I).im = y := by simp
  have h2 : ((x : ℂ) + (y : ℂ) * Complex.I).im = z₀.im := by rw [h]
  exact hy (h1.symm.trans h2)

/-- A point of the form `x + y·I` is different from `z₀` as soon as `x ≠ z₀.re`. -/
lemma add_ofReal_mul_I_ne_of_re {z₀ : ℂ} {x : ℝ} (hx : x ≠ z₀.re) (y : ℝ) :
    ((x : ℂ) + (y : ℂ) * Complex.I) ≠ z₀ := by
  intro h
  have h1 : ((x : ℂ) + (y : ℂ) * Complex.I).re = x := by simp
  have h2 : ((x : ℂ) + (y : ℂ) * Complex.I).re = z₀.re := by rw [h]
  exact hx (h1.symm.trans h2)

/-- **The rectangle boundary integral for a single simple pole, with the residue given by a
limit.**  If `f` is continuous on the closed rectangle `[x₁,x₂] × [y₁,y₂]` except at the single
interior point `z₀`, complex differentiable on the open rectangle except at `z₀`, and
`(z - z₀) * f z → c` as `z → z₀` (so that `f` has at worst a simple pole of residue `c` there,
possibly removable), then the counterclockwise boundary integral of `f` over the rectangle
equals `2 π i c`.  This is `Work.Asymptotics.residue_rectangle` with the
`DifferentiableAt (fun z => f z - c/(z-z₀)) z₀` hypothesis replaced by the limit form, which is
what the proved `Work.Asymptotics.Kfun_principal_part_z_lip` supplies for the CKMRV kernel. -/
theorem rectInt_eq_residue (f : ℂ → ℂ) (z₀ c : ℂ) (x₁ x₂ y₁ y₂ : ℝ)
    (hx₁ : x₁ < z₀.re) (hx₂ : z₀.re < x₂) (hy₁ : y₁ < z₀.im) (hy₂ : z₀.im < y₂)
    (hcont : ContinuousOn f ({z : ℂ | x₁ ≤ z.re ∧ z.re ≤ x₂ ∧ y₁ ≤ z.im ∧ z.im ≤ y₂} \ {z₀}))
    (hhol : ∀ z : ℂ, x₁ < z.re → z.re < x₂ → y₁ < z.im → z.im < y₂ → z ≠ z₀ →
      DifferentiableAt ℂ f z)
    (hres : Filter.Tendsto (fun z : ℂ => (z - z₀) * f z) (nhdsWithin z₀ {z₀}ᶜ) (nhds c)) :
    (∫ x : ℝ in x₁..x₂, f ((x : ℂ) + (y₁ : ℂ) * Complex.I))
      - (∫ x : ℝ in x₁..x₂, f ((x : ℂ) + (y₂ : ℂ) * Complex.I))
      + Complex.I * (∫ y : ℝ in y₁..y₂, f ((x₂ : ℂ) + (y : ℂ) * Complex.I))
      - Complex.I * (∫ y : ℝ in y₁..y₂, f ((x₁ : ℂ) + (y : ℂ) * Complex.I))
      = 2 * (Real.pi : ℂ) * Complex.I * c := by
  -- The closed rectangle and the open rectangle.
  set R : Set ℂ := {z : ℂ | x₁ < z.re ∧ z.re < x₂ ∧ y₁ < z.im ∧ z.im < y₂} with hR
  have hRopen : IsOpen R := by
    rw [hR]
    have heq : {z : ℂ | x₁ < z.re ∧ z.re < x₂ ∧ y₁ < z.im ∧ z.im < y₂}
        = Set.Ioo x₁ x₂ ×ℂ Set.Ioo y₁ y₂ := by
      ext z
      simp only [Complex.mem_reProdIm, Set.mem_Ioo, Set.mem_ofPred_eq]
      tauto
    rw [heq]
    exact isOpen_Ioo.reProdIm isOpen_Ioo
  have hz₀R : z₀ ∈ R := by
    rw [hR]
    exact ⟨hx₁, hx₂, hy₁, hy₂⟩
  have hRnhds : R ∈ 𝓝 z₀ := hRopen.mem_nhds hz₀R
  -- The holomorphic part `g = f - c/(z - z₀)`, which is holomorphic on the punctured open
  -- rectangle with `(z - z₀) g z → 0`.
  set g : ℂ → ℂ := fun z => f z - c / (z - z₀) with hg
  set v : ℂ := (nhdsWithin z₀ {z₀}ᶜ).limUnder g with hv
  -- `(z - z₀) * f z - c → 0`, and it equals `(z - z₀) * g z` off `z₀`.
  have hψ : Tendsto (fun z : ℂ => (z - z₀) * f z - c) (nhdsWithin z₀ {z₀}ᶜ) (nhds 0) := by
    have h := hres.sub (tendsto_const_nhds (x := c) (f := nhdsWithin z₀ {z₀}ᶜ))
    simpa using h
  have hgz : ∀ z : ℂ, z ≠ z₀ → (z - z₀) * g z = (z - z₀) * f z - c := by
    intro z hz
    rw [hg]
    rw [mul_sub, mul_div_cancel₀ c (sub_ne_zero.mpr hz)]
  -- `g` is holomorphic on the punctured open rectangle.
  have hd : DifferentiableOn ℂ g (R \ {z₀}) := by
    intro z hz
    simp only [Set.mem_sdiff, Set.mem_singleton_iff] at hz
    obtain ⟨hzR, hzne⟩ := hz
    rw [hR] at hzR
    have hfz : DifferentiableAt ℂ f z := hhol z hzR.1 hzR.2.1 hzR.2.2.1 hzR.2.2.2 hzne
    have hdiv : DifferentiableAt ℂ (fun w : ℂ => c / (w - z₀)) z :=
      (differentiableAt_const c).div (differentiableAt_id.sub_const z₀) (sub_ne_zero.mpr hzne)
    have hsum := hfz.sub hdiv
    rw [hg]
    exact hsum.differentiableWithinAt
  -- `g - g z₀` is `o((z - z₀)⁻¹)` at `z₀`, so `g` has a removable singularity there.
  have ho : (fun z : ℂ => g z - g z₀) =o[nhdsWithin z₀ {z₀}ᶜ] fun z => (z - z₀)⁻¹ := by
    refine Asymptotics.IsLittleO.of_bound fun ε hε => ?_
    have hε2 : 0 < ε / 2 := by positivity
    have hA : ∀ᶠ z in nhdsWithin z₀ {z₀}ᶜ, ‖(z - z₀) * f z - c‖ ≤ ε / 2 := by
      have h := (Metric.tendsto_nhds.mp hψ) (ε / 2) hε2
      filter_upwards [h] with z hz
      rw [dist_zero_right] at hz
      exact le_of_lt hz
    have hB : ∀ᶠ z in nhdsWithin z₀ {z₀}ᶜ, ‖z - z₀‖ * ‖g z₀‖ ≤ ε / 2 := by
      have ht : Tendsto (fun z : ℂ => ‖z - z₀‖ * ‖g z₀‖) (nhds z₀) (nhds 0) := by
        have h1 : Continuous fun z : ℂ => ‖z - z₀‖ * ‖g z₀‖ :=
          (continuous_id.sub continuous_const).norm.mul continuous_const
        simpa using h1.tendsto z₀
      have h := ht.eventually (isOpen_Iio.mem_nhds hε2)
      filter_upwards [h.filter_mono (nhdsWithin_le_nhds (a := z₀) (s := {z₀}ᶜ))] with z hz
      exact le_of_lt hz
    have hne : ∀ᶠ z in nhdsWithin z₀ {z₀}ᶜ, z ≠ z₀ := by
      filter_upwards [self_mem_nhdsWithin] with z hz
      simpa using hz
    filter_upwards [hA, hB, hne] with z h1 h2 hz
    have hE : ‖g z - g z₀‖ * ‖z - z₀‖ ≤ ε := by
      have hexp : (g z - g z₀) * (z - z₀) = ((z - z₀) * f z - c) - (z - z₀) * g z₀ := by
        rw [← hgz z hz]
        ring
      rw [← norm_mul, hexp]
      calc ‖((z - z₀) * f z - c) - (z - z₀) * g z₀‖
          ≤ ‖(z - z₀) * f z - c‖ + ‖(z - z₀) * g z₀‖ := norm_sub_le _ _
        _ = ‖(z - z₀) * f z - c‖ + ‖z - z₀‖ * ‖g z₀‖ := by rw [norm_mul]
        _ ≤ ε / 2 + ε / 2 := add_le_add h1 h2
        _ = ε := by ring
    have hz0 : 0 < ‖z - z₀‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz)
    rw [norm_inv, ← div_eq_mul_inv, le_div_iff₀ hz0]
    exact hE
  -- Hence the `limUnder`-update of `g` is holomorphic on the open rectangle.
  have h_update : DifferentiableOn ℂ (Function.update g z₀ v) R :=
    Complex.differentiableOn_update_limUnder_of_isLittleO hRnhds hd ho
  -- Change the value of `f` at `z₀`; the boundary integrals are unaffected.
  set f' : ℂ → ℂ := Function.update f z₀ v with hf'
  have hkey : (fun z : ℂ => f' z - c / (z - z₀)) = Function.update g z₀ v := by
    funext z
    by_cases hz : z = z₀
    · subst hz
      simp [hf', hg]
    · rw [hf', Function.update_apply, if_neg hz, Function.update_apply, if_neg hz, hg]
  have hrem : DifferentiableAt ℂ (fun z : ℂ => f' z - c / (z - z₀)) z₀ := by
    rw [hkey]
    exact h_update.differentiableAt hRnhds
  have hcont' : ContinuousOn f'
      ({z : ℂ | x₁ ≤ z.re ∧ z.re ≤ x₂ ∧ y₁ ≤ z.im ∧ z.im ≤ y₂} \ {z₀}) := by
    refine hcont.congr fun z hz => ?_
    simp only [Set.mem_sdiff, Set.mem_singleton_iff] at hz
    rw [hf', Function.update_of_ne hz.2 v f]
  have hhol' : ∀ z : ℂ, x₁ < z.re → z.re < x₂ → y₁ < z.im → z.im < y₂ → z ≠ z₀ →
      DifferentiableAt ℂ f' z := by
    intro z h1 h2 h3 h4 hne
    have hfz : DifferentiableAt ℂ f z := hhol z h1 h2 h3 h4 hne
    refine (Filter.EventuallyEq.differentiableAt_iff ?_).mpr hfz
    have hmem : ({z₀}ᶜ : Set ℂ) ∈ 𝓝 z := isOpen_compl_singleton.mem_nhds (by simpa using hne)
    filter_upwards [hmem] with w hw
    rw [hf', Function.update_of_ne (by simpa using hw) v f]
  -- Apply the residue theorem for a rectangle to `f'`.
  have hfinal := residue_rectangle f' z₀ c x₁ x₂ y₁ y₂ hx₁ hx₂ hy₁ hy₂ hcont' hhol' hrem
  -- Transfer the boundary integrals back from `f'` to `f`.
  have hb : (∫ x : ℝ in x₁..x₂, f' ((x : ℂ) + (y₁ : ℂ) * Complex.I))
      = ∫ x : ℝ in x₁..x₂, f ((x : ℂ) + (y₁ : ℂ) * Complex.I) := by
    refine intervalIntegral.integral_congr fun x _ => ?_
    rw [hf', Function.update_of_ne (add_ofReal_mul_I_ne_of_im (ne_of_lt hy₁) x) v f]
  have ht : (∫ x : ℝ in x₁..x₂, f' ((x : ℂ) + (y₂ : ℂ) * Complex.I))
      = ∫ x : ℝ in x₁..x₂, f ((x : ℂ) + (y₂ : ℂ) * Complex.I) := by
    refine intervalIntegral.integral_congr fun x _ => ?_
    rw [hf', Function.update_of_ne (add_ofReal_mul_I_ne_of_im (ne_of_gt hy₂) x) v f]
  have hrr : (∫ y : ℝ in y₁..y₂, f' ((x₂ : ℂ) + (y : ℂ) * Complex.I))
      = ∫ y : ℝ in y₁..y₂, f ((x₂ : ℂ) + (y : ℂ) * Complex.I) := by
    refine intervalIntegral.integral_congr fun y _ => ?_
    rw [hf', Function.update_of_ne (add_ofReal_mul_I_ne_of_re (ne_of_gt hx₂) y) v f]
  have hl : (∫ y : ℝ in y₁..y₂, f' ((x₁ : ℂ) + (y : ℂ) * Complex.I))
      = ∫ y : ℝ in y₁..y₂, f ((x₁ : ℂ) + (y : ℂ) * Complex.I) := by
    refine intervalIntegral.integral_congr fun y _ => ?_
    rw [hf', Function.update_of_ne (add_ofReal_mul_I_ne_of_re (ne_of_lt hx₁) y) v f]
  rw [hb, ht, hrr, hl] at hfinal
  exact hfinal

end Work.Asymptotics
