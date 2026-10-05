import Mathlib
import Submission.Work.RPB.Port.Drive.SeparationBase
import Submission.Work.RPB.Port.Drive.curve_normal_segment
import Submission.Work.RPB.Port.Drive.degree_eq_of_lift_on_Ioo
import Submission.Work.RPB.Port.Drive.curve_ratio_local
import Submission.Work.RPB.Port.Drive.curve_localSep
import Submission.Work.RPB.Port.Drive.two_sided_decomposition

namespace Work.RPB.Port.Drive

open Manifold
open scoped ContDiff Topology

/-! ## Separation -/

theorem not_isPathConnected_compl_of_windG_ne (γ : Circle → ℝ × ℝ) (hγ : Continuous γ)
    {p p' : ℝ × ℝ} (hp : p ∉ Set.range γ) (hp' : p' ∉ Set.range γ)
    (hne : windG γ hγ hp ≠ windG γ hγ hp') : ¬ IsPathConnected ((Set.range γ)ᶜ) := by
  intro hpc
  obtain ⟨γp, hγp⟩ := hpc.joinedIn p hp p' hp'
  have hsub : Set.range γp ⊆ (Set.range γ)ᶜ := by
    rintro - ⟨t, rfl⟩
    exact hγp t
  have hpre : IsPreconnected (Set.range γp) := isPreconnected_range γp.continuous
  have hp1 : p ∈ Set.range γp := ⟨0, Path.source γp⟩
  have hp2 : p' ∈ Set.range γp := ⟨1, Path.target γp⟩
  refine hne ?_
  simpa using (windG_preconnected hγ hsub hpre (⟨p, hp1⟩ : ↥(Set.range γp))
    (⟨p', hp2⟩ : ↥(Set.range γp))).symm

/-! ## The core computation -/

lemma seg_rel_false {γ : Circle → ℝ × ℝ} {V : ℝ × ℝ} {ε : ℝ} (hε : 0 < ε)
    (hseg : ∀ x τ : ℝ, |τ| ≤ ε → curve γ x = curve γ 0 + τ • rot90 V →
      τ = 0 ∧ ∃ k : ℤ, x = 2 * Real.pi * k)
    {s : ℝ} (hs : s < 0) {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1)
    (hrel : cpx (curve γ (2 * Real.pi * x) - (curve γ 0 + ε • rot90 V))
      = (s : ℂ) * cpx (curve γ (2 * Real.pi * x) - (curve γ 0 - ε • rot90 V))) : False := by
  set w := curve γ (2 * Real.pi * x) with hw
  set G0 := curve γ 0 with hG0
  set a := rot90 V with ha
  have hs1 : (0:ℝ) < 1 - s := by linarith
  have h1 : w.1 - (G0.1 + ε * a.1) = s * (w.1 - (G0.1 - ε * a.1)) := by
    have hh := congrArg Complex.re hrel
    simp only [cpx, Prod.fst_sub, Prod.fst_add, Prod.smul_fst, smul_eq_mul, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, sub_zero] at hh
    exact hh
  have h2 : w.2 - (G0.2 + ε * a.2) = s * (w.2 - (G0.2 - ε * a.2)) := by
    have hh := congrArg Complex.im hrel
    simp only [cpx, Prod.snd_sub, Prod.snd_add, Prod.smul_snd, smul_eq_mul, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, zero_add, add_zero] at hh
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
  have hab : curve γ (2 * Real.pi * x) = curve γ 0 + τ • rot90 V := by
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

/-! ## The two-sided winding lemma -/

/-- **Two points on opposite sides of a point of the curve have different winding numbers.** -/
theorem windE_two_sided (γ : Circle → ℝ × ℝ)
    (hγ : Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) γ) :
    ∃ p : ℝ × ℝ, ∃ hp : p ∉ Set.range γ, ∃ p' : ℝ × ℝ, ∃ hp' : p' ∉ Set.range γ,
      windE γ hγ hp ≠ windE γ hγ hp' := by
  have hcont : Continuous γ := hγ.isEmbedding.continuous
  have hGcont : Continuous (curve γ) := (contDiff_curve γ hγ).continuous
  set V : ℝ × ℝ := deriv (curve γ) 0 with hVdef
  have hVne : V ≠ 0 := by rw [hVdef]; exact curve_deriv_ne_zero γ hγ 0
  have hder : HasDerivAt (curve γ) V 0 := by
    rw [hVdef]
    exact (((contDiff_curve γ hγ).differentiable (by norm_num)).differentiableAt).hasDerivAt
  obtain ⟨ε, hεpos, hseg⟩ := curve_normal_segment (curve γ) hVne hGcont hder (curve_periodic γ)
    (fun s t h => (curve_eq_iff γ hγ s t).mp h)
  set p : ℝ × ℝ := curve γ 0 + ε • rot90 V with hpdef
  set p' : ℝ × ℝ := curve γ 0 - ε • rot90 V with hp'def
  have hcurve_ne : ∀ x : ℝ, curve γ x ≠ p ∧ curve γ x ≠ p' := by
    intro x
    constructor
    · intro hx
      have h2 : curve γ x = curve γ 0 + ε • rot90 V := by rw [hx, hpdef]
      obtain ⟨hτ, -⟩ := hseg x ε (by simp [abs_of_pos hεpos]) h2
      exact hεpos.ne' hτ
    · intro hx
      have h2 : curve γ x = curve γ 0 + (-ε) • rot90 V := by
        rw [hx, hp'def, neg_smul]
        abel
      obtain ⟨hτ, -⟩ := hseg x (-ε) (by simp [abs_of_pos hεpos]) h2
      exact (neg_ne_zero.mpr hεpos.ne') hτ
  have hp : p ∉ Set.range γ := by
    rw [← range_curve γ]
    rintro ⟨x, hx⟩
    exact (hcurve_ne x).1 hx
  have hp' : p' ∉ Set.range γ := by
    rw [← range_curve γ]
    rintro ⟨x, hx⟩
    exact (hcurve_ne x).2 hx
  -- the ratio loop
  set F : UnitAddCircle → UnitAddCircle :=
    fun t => dirZ (cpx (gammaU γ t - p) / cpx (gammaU γ t - p')) with hFdef
  have Fcont : Continuous F := continuous_dirZ_ratio hcont hp hp'
  -- the real ratio and its argument
  set R : ℝ → ℂ := fun x => ratioMap (curve γ) p p' (2 * Real.pi * x) with hRdef
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
    have hrel : cpx (curve γ (2 * Real.pi * x) - (curve γ 0 + ε • rot90 V))
        = ((R x).re : ℂ) * cpx (curve γ (2 * Real.pi * x) - (curve γ 0 - ε • rot90 V)) := by
      have hden : cpx (curve γ (2 * Real.pi * x) - p') ≠ 0 := by
        rw [cpx_ne_zero_iff, sub_ne_zero]
        exact (hcurve_ne _).2
      have h1 : cpx (curve γ (2 * Real.pi * x) - p) = R x * cpx (curve γ (2 * Real.pi * x) - p') := by
        rw [hRdef]
        simp only [ratioMap]
        rw [div_mul_cancel₀ _ hden]
      rw [hz] at h1
      rw [hpdef, hp'def] at h1
      exact h1
    exact seg_rel_false hεpos hseg hre hx.1 hx.2 hrel
  set A : ℝ → ℝ := fun x => (R x).arg / Real.pi with hAdef
  have hRcont : Continuous R := by
    rw [hRdef]
    refine Continuous.div ?_ ?_ ?_
    · exact continuous_cpx.comp ((hGcont.comp (continuous_const.mul continuous_id)).sub
        continuous_const)
    · exact continuous_cpx.comp ((hGcont.comp (continuous_const.mul continuous_id)).sub
        continuous_const)
    · intro x
      rw [cpx_ne_zero_iff, sub_ne_zero]
      exact (hcurve_ne _).2
  have hAcont : ContinuousOn A (Set.Ioo (0:ℝ) 1) := by
    rw [hAdef]
    exact (Complex.continuousOn_arg.comp hRcont.continuousOn fun x hx => hRslit x hx).div_const
      Real.pi
  have hlift : ∀ x ∈ Set.Ioo (0:ℝ) 1,
      ((A x : ℝ) : UnitAddCircle) = F (x : UnitAddCircle) := by
    intro x hx
    have h1 : ((A x : ℝ) : UnitAddCircle) = dirZ (R x) := rfl
    have h2 : F (x : UnitAddCircle) = dirZ (R x) := by
      change dirZ (cpx (gammaU γ (x : UnitAddCircle) - p) / cpx (gammaU γ (x : UnitAddCircle) - p'))
        = dirZ (R x)
      rw [gammaU_apply_coe, hRdef]
      rfl
    rw [h1, h2]
  -- the limits of the lift
  obtain ⟨δ, hδpos, himneg, himpos, hlimpos, hlimneg⟩ :=
    curve_ratio_local hVne hder hεpos
  have ha : Filter.Tendsto A (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds (-1)) := by
    have heq : A =ᶠ[nhdsWithin (0:ℝ) (Set.Ioi 0)]
        fun x => (ratioMap (curve γ) p p' (2 * Real.pi * x)).arg / Real.pi := by
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
    have hper2 : ∀ x : ℝ, curve γ (2 * Real.pi * x) = curve γ (2 * Real.pi * x - 2 * Real.pi) := by
      intro x
      have h := curve_periodic γ (2 * Real.pi * x - 2 * Real.pi)
      rw [show 2 * Real.pi * x - 2 * Real.pi + 2 * Real.pi = 2 * Real.pi * x by ring] at h
      exact h
    have heq : A =ᶠ[nhdsWithin (1:ℝ) (Set.Iio 1)]
        fun x => (ratioMap (curve γ) p p' (2 * Real.pi * x - 2 * Real.pi)).arg / Real.pi := by
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
  obtain ⟨n, hn, hdeg⟩ := degree_eq_of_lift_on_Ioo Fcont hAcont hlift ha hb
  have hn2 : n = 2 := by
    have h : (n : ℝ) = 2 := by linarith
    exact_mod_cast h
  have hwind : windG γ hcont hp - windG γ hcont hp' = 2 := by
    rw [windG_sub_eq_degree γ hcont hp hp', hdeg, hn2]
  have hne : windE γ hγ hp ≠ windE γ hγ hp' := by
    intro h
    have h' : windG γ hcont hp = windG γ hcont hp' := h
    omega
  exact ⟨p, hp, p', hp', hne⟩


theorem smooth_jordan_separation (γ : Circle → ℝ × ℝ)
    (hγ : Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) γ) :
    ∃ ins out : Set (ℝ × ℝ),
      IsOpen ins ∧ IsOpen out ∧ IsPathConnected ins ∧ IsPathConnected out ∧
      Bornology.IsBounded ins ∧ ¬ Bornology.IsBounded out ∧
      ins.Nonempty ∧ out.Nonempty ∧ (Set.range γ)ᶜ = ins ∪ out ∧ Disjoint ins out ∧
      closure ins = ins ∪ Set.range γ ∧ closure out = out ∪ Set.range γ := by
  have hcont : Continuous γ := hγ.isEmbedding.continuous
  have hKclosed : IsClosed (Set.range γ) := (isCompact_range hcont).isClosed
  have hKconn : IsConnected (Set.range γ) :=
    ⟨⟨γ (Circle.exp 0), ⟨Circle.exp 0, rfl⟩⟩, isPreconnected_range hcont⟩
  have hKbdd : Bornology.IsBounded (Set.range γ) := (isCompact_range hcont).isBounded
  obtain ⟨p, hp, p', hp', hne⟩ := windE_two_sided γ hγ
  have hnot : ¬ IsPathConnected ((Set.range γ)ᶜ) :=
    not_isPathConnected_compl_of_windG_ne γ hcont hp hp' hne
  obtain ⟨P₁, P₂, -, hpc1, hpc2, hopen1, hopen2, hcover, hdisj, hbdd, hcl1, hcl2⟩ :=
    two_sided_decomposition hKclosed hKconn hKbdd (curve_localSep γ hγ) hnot
  rcases hbdd with ⟨hb1, hb2⟩ | ⟨hb2, hb1⟩
  · exact ⟨P₁, P₂, hopen1, hopen2, hpc1, hpc2, hb1, hb2, hpc1.nonempty, hpc2.nonempty,
      hcover, hdisj, hcl1, hcl2⟩
  · exact ⟨P₂, P₁, hopen2, hopen1, hpc2, hpc1, hb2, hb1, hpc2.nonempty, hpc1.nonempty,
      hcover.trans (Set.union_comm P₁ P₂), hdisj.symm, hcl2, hcl1⟩

end Work.RPB.Port.Drive
