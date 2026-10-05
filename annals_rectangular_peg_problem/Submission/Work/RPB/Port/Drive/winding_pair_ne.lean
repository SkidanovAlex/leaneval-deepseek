import Mathlib
import Submission.Work.RPB.Port.Drive.ratio_loop
import Submission.Work.RPB.Port.Drive.curve_normal_segment
import Submission.Work.RPB.Port.Drive.curve_ratio_local
import Submission.Work.RPB.Port.Drive.degree_eq_of_lift_on_Ioo
import Submission.Work.RPB.Port.Drive.smooth_jordan_separation

set_option autoImplicit false
noncomputable section

namespace Work.RPB.Port.Drive

open Filter

/-! ## A helper: `seg_rel_false` for a general closed curve

`Work.RPB.Port.Drive.seg_rel_false` is stated for a `Circle`-parametrised curve `curve γ`; the version below is
stated for an arbitrary `G : ℝ → ℝ × ℝ`, which is the shape in which the parametrisation
`x ↦ γ (x/2π)` of the target statement appears. -/

lemma seg_rel_false_of_curve {G : ℝ → ℝ × ℝ} {V : ℝ × ℝ} {ε : ℝ} (hε : 0 < ε)
    (hseg : ∀ x τ : ℝ, |τ| ≤ ε → G x = G 0 + τ • rot90 V →
      τ = 0 ∧ ∃ k : ℤ, x = 2 * Real.pi * k)
    {s : ℝ} (hs : s < 0) {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1)
    (hrel : cpx (G (2 * Real.pi * x) - (G 0 + ε • rot90 V))
      = (s : ℂ) * cpx (G (2 * Real.pi * x) - (G 0 - ε • rot90 V))) : False := by
  set w := G (2 * Real.pi * x) with hw
  set G0 := G 0 with hG0
  set a := rot90 V with ha
  have hs1 : (0:ℝ) < 1 - s := by linarith
  have h1 : w.1 - (G0.1 + ε * a.1) = s * (w.1 - (G0.1 - ε * a.1)) := by
    have hh := congrArg Complex.re hrel
    simp only [cpx, Prod.fst_sub, Prod.fst_add, Prod.smul_fst, smul_eq_mul, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hh
    exact hh
  have h2 : w.2 - (G0.2 + ε * a.2) = s * (w.2 - (G0.2 - ε * a.2)) := by
    have hh := congrArg Complex.im hrel
    simp only [cpx, Prod.snd_sub, Prod.snd_add, Prod.smul_snd, smul_eq_mul, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero] at hh
    exact hh
  set τ : ℝ := ε * (1 + s) / (1 - s) with hτ
  have hw_eq : w = G0 + τ • a := by
    have e1 : (w.1 - G0.1) * (1 - s) = ε * (1 + s) * a.1 := by
      have h := h1
      ring_nf at h ⊢
      linarith
    have e2 : (w.2 - G0.2) * (1 - s) = ε * (1 + s) * a.2 := by
      have h := h2
      ring_nf at h ⊢
      linarith
    have f1 : w.1 - G0.1 = τ * a.1 := by
      rw [hτ, div_mul_eq_mul_div, eq_div_iff (ne_of_gt hs1)]
      exact e1
    have f2 : w.2 - G0.2 = τ * a.2 := by
      rw [hτ, div_mul_eq_mul_div, eq_div_iff (ne_of_gt hs1)]
      exact e2
    exact Prod.ext
      (by simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]; linarith)
      (by simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]; linarith)
  have hτabs : |τ| ≤ ε := by
    have habs : |1 + s| ≤ 1 - s := by
      by_cases h : (-1:ℝ) ≤ s
      · rw [abs_of_nonneg (by linarith)]; linarith
      · rw [abs_of_neg (by linarith)]; linarith
    rw [hτ, abs_div, abs_mul, abs_of_pos hε, abs_of_pos hs1, div_le_iff₀ hs1]
    nlinarith [habs, hε]
  have hab : G (2 * Real.pi * x) = G 0 + τ • rot90 V := by
    rw [hw, hG0, ha] at hw_eq
    exact hw_eq
  obtain ⟨hτ0, k, hk⟩ := hseg (2 * Real.pi * x) τ hτabs hab
  have h2pi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hx2 : x = (k : ℝ) := by
    refine mul_left_cancel₀ h2pi ?_
    simpa [mul_assoc] using hk
  have hk0 : (0:ℤ) < k := by
    have h : (0:ℝ) < (k:ℝ) := by rw [← hx2]; exact hx0
    exact_mod_cast h
  have hk1 : k < (1:ℤ) := by
    have h : (k:ℝ) < 1 := by rw [← hx2]; exact hx1
    exact_mod_cast h
  omega

/-- **Two points on opposite sides of a regular point of a smooth embedded closed plane curve have
different winding numbers** (the `ℝ/ℤ`-parametrised, `C¹`-input form of
`Work.RPB.Port.Drive.windE_two_sided`).

`γ` is a continuous injective closed plane curve, and at the parameter `0` the rescaled
parametrisation `x ↦ γ (x / 2π)` has non-zero derivative `V`.  Then there are points `p`, `p'` off the
curve with different winding numbers; in fact one may take `p = γ 0 + ε • rot90 V` and
`p' = γ 0 - ε • rot90 V` for small `ε > 0`. -/
theorem winding_pair_ne (γ : UnitAddCircle → ℝ × ℝ) (hγ : Continuous γ)
    (hinj : Function.Injective γ) {V : ℝ × ℝ} (hV : V ≠ 0)
    (hder : HasDerivAt (fun x : ℝ => γ ((x / (2 * Real.pi) : ℝ) : UnitAddCircle)) V 0) :
    ∃ p : ℝ × ℝ, ∃ hp : p ∉ Set.range γ, ∃ p' : ℝ × ℝ, ∃ hp' : p' ∉ Set.range γ,
      Work.RPB.Port.Drive.winding γ hγ hp ≠ Work.RPB.Port.Drive.winding γ hγ hp' := by
  set S : ℝ → ℝ × ℝ := fun x => γ ((x / (2 * Real.pi) : ℝ) : UnitAddCircle) with hSdef
  have hSder : HasDerivAt S V 0 := by rw [hSdef]; exact hder
  have hSc : Continuous (fun x : ℝ => ((x / (2 * Real.pi) : ℝ) : UnitAddCircle)) :=
    (AddCircle.continuous_mk' (p := (1 : ℝ))).comp (continuous_id.div_const _)
  have hScont : Continuous S := by rw [hSdef]; exact hγ.comp hSc
  -- the fundamental identity `S (2π y) = γ y`
  have hS_apply : ∀ y : ℝ, S (2 * Real.pi * y) = γ (y : UnitAddCircle) := by
    intro y
    show γ ((2 * Real.pi * y / (2 * Real.pi) : ℝ) : UnitAddCircle) = γ (y : UnitAddCircle)
    have harg : 2 * Real.pi * y / (2 * Real.pi) = y := by field_simp
    rw [harg]
  -- `S` is periodic with period `2π`
  have hSper : ∀ t : ℝ, S (t + 2 * Real.pi) = S t := by
    intro t
    show γ (((t + 2 * Real.pi) / (2 * Real.pi) : ℝ) : UnitAddCircle)
      = γ ((t / (2 * Real.pi) : ℝ) : UnitAddCircle)
    have h1 : ((t + 2 * Real.pi) / (2 * Real.pi) : ℝ) = t / (2 * Real.pi) + 1 := by
      field_simp
    rw [h1, AddCircle.coe_add_period (p := (1 : ℝ))]
  -- `S` is injective modulo `2π`
  have hSinj : ∀ s t : ℝ, S s = S t → ∃ k : ℤ, s = t + 2 * Real.pi * k := by
    intro s t hst
    have h1 : ((s / (2 * Real.pi) : ℝ) : UnitAddCircle)
        = ((t / (2 * Real.pi) : ℝ) : UnitAddCircle) := by
      rw [hSdef] at hst
      exact hinj hst
    have h2 : (-(s / (2 * Real.pi)) + t / (2 * Real.pi)) ∈ AddSubgroup.zmultiples (1 : ℝ) :=
      QuotientAddGroup.eq.mp h1
    obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp h2
    have h2pi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    have hk' : (k : ℝ) * (2 * Real.pi) = -s + t := by
      rw [zsmul_eq_mul, mul_one] at hk
      field_simp at hk ⊢
      linarith
    refine ⟨-k, ?_⟩
    push_cast
    linarith
  obtain ⟨ε, hεpos, hseg⟩ := curve_normal_segment S hV hScont hSder hSper hSinj
  set p : ℝ × ℝ := S 0 + ε • rot90 V with hpdef
  set p' : ℝ × ℝ := S 0 - ε • rot90 V with hp'def
  -- `p` and `p'` are off the curve
  have hcurve_ne : ∀ x : ℝ, S x ≠ p ∧ S x ≠ p' := by
    intro x
    constructor
    · intro hx
      have h2 : S x = S 0 + ε • rot90 V := by rw [hx, hpdef]
      obtain ⟨hτ, -⟩ := hseg x ε (by simp [abs_of_pos hεpos]) h2
      exact hεpos.ne' hτ
    · intro hx
      have h2 : S x = S 0 + (-ε) • rot90 V := by
        rw [hx, hp'def, neg_smul]
        abel
      obtain ⟨hτ, -⟩ := hseg x (-ε) (by simp [abs_of_pos hεpos]) h2
      exact (neg_ne_zero.mpr hεpos.ne') hτ
  -- the range of `S` is the range of `γ`
  have hrange : Set.range S = Set.range γ := by
    refine Set.Subset.antisymm ?_ ?_
    · rintro - ⟨x, rfl⟩
      exact ⟨_, rfl⟩
    · rintro - ⟨u, rfl⟩
      obtain ⟨y, hy⟩ : ∃ y : ℝ, (y : UnitAddCircle) = u := by
        refine ⟨(AddCircle.equivIco (1 : ℝ) 0 u : ℝ), ?_⟩
        exact AddCircle.coe_equivIco (p := (1 : ℝ)) (a := 0) (y := u)
      exact ⟨2 * Real.pi * y, by rw [hS_apply y, hy]⟩
  have hp : p ∉ Set.range γ := by
    rw [← hrange]
    rintro ⟨x, hx⟩
    exact (hcurve_ne x).1 hx
  have hp' : p' ∉ Set.range γ := by
    rw [← hrange]
    rintro ⟨x, hx⟩
    exact (hcurve_ne x).2 hx
  -- the real ratio and its argument
  set R : ℝ → ℂ := fun x => ratioMap S p p' (2 * Real.pi * x) with hRdef
  have hRne : ∀ x : ℝ, R x ≠ 0 := by
    intro x
    rw [hRdef]
    exact div_ne_zero (by rw [cpx_ne_zero_iff, sub_ne_zero]; exact (hcurve_ne _).1)
      (by rw [cpx_ne_zero_iff, sub_ne_zero]; exact (hcurve_ne _).2)
  have hRslit : ∀ x ∈ Set.Ioo (0:ℝ) 1, R x ∈ Complex.slitPlane := by
    intro x hx
    rw [Complex.mem_slitPlane_iff_arg]
    refine ⟨?_, hRne x⟩
    intro harg
    have hre : (R x).re < 0 := (Complex.arg_eq_pi_iff.mp harg).1
    have him : (R x).im = 0 := (Complex.arg_eq_pi_iff.mp harg).2
    have hz : R x = ((R x).re : ℂ) := by
      apply Complex.ext <;> simp [him]
    have hrel : cpx (S (2 * Real.pi * x) - (S 0 + ε • rot90 V))
        = ((R x).re : ℂ) * cpx (S (2 * Real.pi * x) - (S 0 - ε • rot90 V)) := by
      have hden : cpx (S (2 * Real.pi * x) - p') ≠ 0 := by
        rw [cpx_ne_zero_iff, sub_ne_zero]
        exact (hcurve_ne _).2
      have h1 : cpx (S (2 * Real.pi * x) - p)
          = R x * cpx (S (2 * Real.pi * x) - p') := by
        rw [hRdef]
        simp only [ratioMap]
        rw [div_mul_cancel₀ _ hden]
      rw [hz] at h1
      rw [hpdef, hp'def] at h1
      exact h1
    exact seg_rel_false_of_curve hεpos hseg hre hx.1 hx.2 hrel
  set A : ℝ → ℝ := fun x => (R x).arg / Real.pi with hAdef
  have hRcont : Continuous R := by
    rw [hRdef]
    refine Continuous.div ?_ ?_ ?_
    · exact continuous_cpx.comp ((hScont.comp (continuous_const.mul continuous_id)).sub
        continuous_const)
    · exact continuous_cpx.comp ((hScont.comp (continuous_const.mul continuous_id)).sub
        continuous_const)
    · intro x
      rw [cpx_ne_zero_iff, sub_ne_zero]
      exact (hcurve_ne _).2
  have hAcont : ContinuousOn A (Set.Ioo (0:ℝ) 1) := by
    rw [hAdef]
    exact (Complex.continuousOn_arg.comp hRcont.continuousOn fun x hx => hRslit x hx).div_const
      Real.pi
  have hlift : ∀ x ∈ Set.Ioo (0:ℝ) 1,
      ((A x : ℝ) : UnitAddCircle) = ratioLoop γ p p' (x : UnitAddCircle) := by
    intro x hx
    have h1 : ((A x : ℝ) : UnitAddCircle) = dirZ (R x) := rfl
    have h2 : ratioLoop γ p p' (x : UnitAddCircle) = dirZ (R x) := by
      rw [ratioLoop_apply]
      congr 1
      simp only [hRdef, ratioMap]
      rw [hS_apply x]
    rw [h1, h2]
  -- the limits of the lift
  obtain ⟨δ, hδpos, himneg, himpos, hlimpos, hlimneg⟩ :=
    curve_ratio_local hV hSder hεpos
  have ha : Filter.Tendsto A (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds (-1)) := by
    have heq : A =ᶠ[nhdsWithin (0:ℝ) (Set.Ioi 0)]
        fun x => (ratioMap S p p' (2 * Real.pi * x)).arg / Real.pi := by
      filter_upwards with x
      rw [hAdef, hRdef]
    have harg : Filter.Tendsto (fun x : ℝ => 2 * Real.pi * x)
        (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhdsWithin (0:ℝ) (Set.Ioi 0)) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, ?_⟩
      · have h1 : Filter.Tendsto (fun x : ℝ => 2 * Real.pi * x) (nhds (0:ℝ))
            (nhds (2 * Real.pi * 0)) := tendsto_const_nhds.mul Filter.tendsto_id
        simpa using h1.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with x hx
        show (0:ℝ) < 2 * Real.pi * x
        have : (0:ℝ) < x := hx
        positivity
    have hlim := (hlimpos.comp harg).div_const Real.pi
    have h3 : (-Real.pi) / Real.pi = -1 := by
      rw [neg_div, div_self Real.pi_ne_zero]
    rw [h3] at hlim
    exact hlim.congr' heq.symm
  have hb : Filter.Tendsto A (nhdsWithin (1:ℝ) (Set.Iio 1)) (nhds 1) := by
    have hper2 : ∀ x : ℝ, S (2 * Real.pi * x) = S (2 * Real.pi * x - 2 * Real.pi) := by
      intro x
      have h := hSper (2 * Real.pi * x - 2 * Real.pi)
      rw [show 2 * Real.pi * x - 2 * Real.pi + 2 * Real.pi = 2 * Real.pi * x by ring] at h
      exact h
    have heq : A =ᶠ[nhdsWithin (1:ℝ) (Set.Iio 1)]
        fun x => (ratioMap S p p' (2 * Real.pi * x - 2 * Real.pi)).arg / Real.pi := by
      filter_upwards with x
      rw [hAdef, hRdef]
      simp only [ratioMap]
      rw [hper2 x]
    have harg : Filter.Tendsto (fun x : ℝ => 2 * Real.pi * x - 2 * Real.pi)
        (nhdsWithin (1:ℝ) (Set.Iio 1)) (nhdsWithin (0:ℝ) (Set.Iio 0)) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, ?_⟩
      · have h1 : Filter.Tendsto (fun x : ℝ => 2 * Real.pi * x - 2 * Real.pi) (nhds (1:ℝ))
            (nhds (2 * Real.pi * 1 - 2 * Real.pi)) :=
          (tendsto_const_nhds.mul Filter.tendsto_id).sub tendsto_const_nhds
        have h2 : 2 * Real.pi * 1 - 2 * Real.pi = 0 := by ring
        rw [h2] at h1
        exact h1.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with x hx
        show 2 * Real.pi * x - 2 * Real.pi < 0
        have hx1 : x < 1 := hx
        nlinarith [Real.pi_pos]
    have hlim := (hlimneg.comp harg).div_const Real.pi
    have h3 : Real.pi / Real.pi = 1 := div_self Real.pi_ne_zero
    rw [h3] at hlim
    exact hlim.congr' heq.symm
  obtain ⟨n, hn, hdeg⟩ :=
    degree_eq_of_lift_on_Ioo (continuous_ratioLoop γ hγ hp hp') hAcont hlift ha hb
  have hn2 : n = 2 := by
    have h : (n : ℝ) = 2 := by linarith
    exact_mod_cast h
  have hwind : winding γ hγ hp - winding γ hγ hp' = 2 := by
    rw [winding_sub_eq_degree_ratioLoop γ hγ hp hp', hdeg, hn2]
  refine ⟨p, hp, p', hp', ?_⟩
  intro h
  omega

end Work.RPB.Port.Drive
